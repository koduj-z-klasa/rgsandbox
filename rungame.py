import os
import sys
import random
import pwd
import imp
import traceback
import ast
import time
import resource
import pkg_resources
import multiprocessing as mp
import multiprocessing.queues as mpq
import multiprocessing.managers as mpm
###
import dbcon
import limitexec as le
import matchstate as ms
import shorten
from rgkit import game, rg
from rgkit.settings import settings
import tools

MAX_MS_PER_FIRST_ACT = 1500
MAX_MS_PER_ACT = 300
MAX_MS_PER_CALL = 2000

S_MATCH_REST = 4.0

TIME_RATE = 0.1
WIN_RATE = 0.05
SYMMETRIC = True

# load modules for the user to use
sys.modules['rg'] = sys.modules['rgkit.rg']
sys.modules['settings'] = sys.modules['rgkit.settings']
MAP_FILENAME = pkg_resources.resource_filename(
    'rgkit', 'maps/default.py')


def get_cpu_time(pid):
    clk_tck = float(os.sysconf(os.sysconf_names['SC_CLK_TCK']))
    with open("/proc/%d/stat" % (pid,)) as fpath:
        vals = fpath.read().split(' ')
        time = sum(
            int(f) / clk_tck for f in vals[13:15])
        return time


class TimeoutError(Exception): pass
class TimeoutCannotRecoverError(Exception): pass

class CPUTimeoutQueue(mpq.Queue):
    """
    A version of multiprocessing.Queue which uses CPU time of a specified
    process instead of real time to limit the get() time. This only works on
    systems which support /proc/$pid/stat and only for local processes which
    don't fork and CPUs which keep their speed at the same level.
    """
    MAX_RETRY = 5
    MIN_ERROR = 0.1
    ERROR_PERCENT = 1.1
    def __init__(self, *args, **kwargs):
        self.clk_tck = float(os.sysconf(os.sysconf_names['SC_CLK_TCK']))
        super(CPUTimeoutQueue, self).__init__(*args, **kwargs)
    def set_pid(self, pid):
        self.pid = pid
    def _get_raw_cpu_time(self):
        with open("/proc/%d/stat" % (self.pid,)) as fpath:
            vals = fpath.read().split(' ')
            time = sum(
                int(f) / self.clk_tck for f in vals[13:15])
            return time
    def get(self, block=True, timeout=None):
        assert block and timeout is not None, (
            '%s.get() may only be used with block=True and a timeout!'.format(
                self.__class__.__name__))
        assert self.pid is not None, (
            'you must call q.set_pid(pid) before calling get()!')
        current_timeout = timeout
        pre_used_time = self._get_raw_cpu_time()
        pre_real_time = time.time()
        attempt_limit = 0
        while current_timeout > 0 and attempt_limit < self.MAX_RETRY:
            try:
                # Add a buffer both absolute and percentage wide to reduce the
                # number of necessary repetition
                return super(CPUTimeoutQueue, self).get(
                    block,
                    current_timeout * self.ERROR_PERCENT + self.MIN_ERROR)
            except mpq.Empty:
                post_used_time = self._get_raw_cpu_time()
                current_timeout = timeout - post_used_time + pre_used_time
                if current_timeout < 0:
                    attempt_limit = self.MAX_RETRY
                print('#timeout was supposed to be', timeout,
                    ', but CPU time was', post_used_time - pre_used_time,
                    'while the real time was', time.time() - pre_real_time)
                attempt_limit += 1
        raise mpq.Empty()


class CPUManager(mpm.BaseManager):
    pass
CPUManager.register('CPUQueue', CPUTimeoutQueue)
CPUManager.register('Queue', mpq.Queue)


def load_map(map_file):
    map_data = ast.literal_eval(open(MAP_FILENAME).read())
    settings.init_map(map_data)

def calc_score(scores):
    if scores[0] == scores[1]:
        return 0.5
    return 1 if scores[0] > scores[1] else 0

def update_ratings(db, match, game_result):
    MINUTE = 60
    HOUR = 60 * MINUTE
    DAY = 24 * HOUR
    WEEK = 7 * DAY
    MONTH = 30 * DAY

    def get_k_factor(r1_rating, r2_rating, r1_update, r2_update):
        k_factor = min(tools.get_k_factor(r1_rating),
                       tools.get_k_factor(r2_rating))
        # Increase k_factor for recently updated bots.
        if (time.time() - r1_update < DAY or
                time.time() - r2_update < DAY):
            k_factor = int(k_factor * 2)
        elif (time.time() - r1_update < 3 * DAY or
                time.time() - r2_update < 3 * DAY):
            k_factor = int(k_factor * 1.5)
        return k_factor

    def new_rating(r1, r2, result, k_factor):
        expected = 1.0/(1 + pow(10.0, (r2 - r1)/400.0))
        return r1 + k_factor * (result - expected)

    def get_rating_and_update_time(rid):
        result = db.select('robots', what='rating, last_updated', where='id=$id', vars={'id': rid})
        if not result:
            return None, None
        robot = result[0]
        rating = robot['rating']
        last_updated = robot['last_updated']
        if rating is None:
            return tools.DEFAULT_RATING, last_updated
        return rating, last_updated

    def get_ranking(rating):
        query = '''
            select count(*) as ranking
            from robots r
            where compiled and passed and not disabled and
                  r.rating > $rating + 1e-5
        '''
        robot = db.query(query, vars={'rating': rating})
        return robot[0]['ranking']

    rating1, updated1 = get_rating_and_update_time(match['r1_id'])
    rating2, updated2 = get_rating_and_update_time(match['r2_id'])

    k_factor = get_k_factor(rating1, rating2, updated1, updated2)

    new_rating1 = new_rating(rating1, rating2, game_result, k_factor)
    new_rating2 = new_rating(rating2, rating1, 1 - game_result, k_factor)

    # ratings might have changed since the match was created
    ranking1 = get_ranking(rating1)
    ranking2 = get_ranking(rating2)
    db.update('matches', where='id=$id', vars={'id': match['id']},
              r1_rating=rating1, r2_rating=rating2,
              r1_ranking=ranking1, r2_ranking=ranking2,
              k_factor=k_factor)
    db.update('robots', where='id=$id', vars={'id': match['r1_id']},
              rating=new_rating1, last_opponent=match['r2_id'],
              last_match=int(time.time()))
    db.update('robots', where='id=$id', vars={'id': match['r2_id']},
              rating=new_rating2, last_opponent=match['r1_id'],
              last_match=int(time.time()))

def update_stats(db, match, r1_time, r2_time, score):
    if r1_time is not None:
        db.query('UPDATE robots SET time=time*(1-$r) + $t*$r WHERE id=$id',
                 vars={'id': match['r1_id'], 'r': TIME_RATE, 't': r1_time})
    if r2_time is not None:
        db.query('UPDATE robots SET time=time*(1-$r) + $t*$r WHERE id=$id',
                 vars={'id': match['r2_id'], 'r': TIME_RATE, 't': r2_time})
    db.query('UPDATE robots SET winrate=winrate*(1-$r) + $t*$r WHERE id=$id',
             vars={'id': match['r1_id'], 'r': WIN_RATE, 't': score})
    db.query('UPDATE robots SET winrate=winrate*(1-$r) + $t*$r WHERE id=$id',
             vars={'id': match['r2_id'], 'r': WIN_RATE, 't': 1 - score})

def proxy_process_routine(user_code, queue_in, queue_out, queue_output):
    start_time = time.time()

    class Logger:
        def write(self, data):
            queue_output.put(data)
        def flush(self):
            pass

    # Cannot use sys as drop_privileges will disable it
    out = sys.stdout = sys.stderr = Logger()
    trace_func = traceback.print_exc

    def limit_resources():
        MEM_LIMIT = (2 ** 20) * 1024 # MB
        for rsrc in ('DATA', 'RSS', 'AS'):
            resource.setrlimit(getattr(resource, 'RLIMIT_' + rsrc), (MEM_LIMIT, MEM_LIMIT))
        resource.setrlimit(resource.RLIMIT_NPROC, (10, 10))

    def disable_modules(*blacklist):
        '''Always disable sys.'''

        def disable_mod(mod):
            sys.modules[mod] = None
            globals()[mod] = None
            pass

        for mod_name in blacklist:
            disable_mod(mod_name)
        disable_mod('sys')

    # counting on iptables to restrict network access for `nobody`
    def drop_privileges(uid_name='nobody'):
        uid = pwd.getpwnam(uid_name).pw_uid
        limit_resources()

        os.chroot('jail')
        os.chdir('jail')
        os.setgroups([])
        os.umask(0)
        os.setuid(uid)
        os.nice(10)  # Lower priority

        disable_modules(
            'ctypes',
            'imp',
            'inspect',
            'multiprocessing',
            'os',
            'pdb',
            'posix',
            'dbcon')

        # No sleeping!
        time.sleep = lambda s: 0

    def make_user_robot(code, mod):
        global settings

        try:
            exec code in mod.__dict__
        except:
            trace_func(file=out)
        finally:
            cmp_time = time.time()
            out.write(
                'Compilation: {0:.4g}s\n'.format(cmp_time - start_time))
            if 'Robot' in mod.__dict__:
                bot = mod.__dict__['Robot']()
                ini_time = time.time()
                out.write(
                    'Initialization: {0:.4g}s\n'.format(ini_time - cmp_time))
                return bot
            return None

    robot = None
    try:
        load_map('rgkit/maps/default.py')
        mod = imp.new_module('usercode')
        drop_privileges()
        my_robot = make_user_robot(user_code, mod)
        robot = my_robot
    except:
        trace_func(file=out)

    for data in iter(queue_in.get, None):
        if 'query' in data:
            queue_out.put({'result': robot is not None})
            continue
        try:
            robot.__dict__.update(data['properties'])
            random.seed(data['game'].seed)
            with le.time_limit(data['timelimit']):
                action = robot.act(data['game'])
            queue_out.put({'result': 'ok', 'ret': action})
        except Exception as e:
            trace_func(file=out)
            queue_out.put({'result': 'error', 'error': e})

class ProxyProcess:
    def __init__(self, user_code):
        self._queue_data = mp.Queue()
        self._queue_action = CPUTimeoutQueue()
        self._queue_output = mp.Queue()

        self.process = mp.Process(target=proxy_process_routine,
            args=(user_code, self._queue_data, self._queue_action, self._queue_output))
        self.process.start()
        self._queue_action.set_pid(self.process.pid)
        self.pid = self.process.pid
        self._ignore = 0

    def get_response(self, data, ms_timelimit=MAX_MS_PER_ACT):
        s_timelimit = ms_timelimit * 0.001
        data['timelimit'] = s_timelimit
        self._queue_data.put(data)
        try:
            # 10% room for error
            for i in range(self._ignore):
                self._queue_action.get(timeout=s_timelimit * 1.1)
                self._ignore -= 1
            return self._queue_action.get(timeout=s_timelimit * 1.1)
        except mpq.Empty:
            self._ignore += 1
            if self._ignore == 1:
                raise TimeoutError()
            raise TimeoutCannotRecoverError()

    def get_output(self):
        def get_next_output():
            try:
                return self._queue_output.get_nowait()
            except mpq.Empty:
                return None
        return ''.join(iter(get_next_output, None))

    def alive(self):
        return self.process.is_alive()

    def cleanup(self):
        self._queue_data.close()
        self._queue_action.close()
        self._queue_output.close()

        self._queue_data.cancel_join_thread()
        self._queue_action.cancel_join_thread()
        self._queue_output.cancel_join_thread()

        self.process.terminate()

class ProxyBot:
    def __init__(self, process, output_file):
        self._process = process
        self._output_file = output_file
        self.skip = False
        self.errors = 0
        self.turn = None

    def act(self, game):
        global settings

        if self.skip:
            return ['suicide']

        data = {'game': game, 'properties': dict()}
        props = settings.exposed_properties + settings.player_only_properties
        for prop in props:
            data['properties'][prop] = getattr(self, prop)

        timelimit = MAX_MS_PER_ACT
        if self.turn != game.turn:
            self.turn = game.turn
            # Players who calculate all in first act per turn
            timelimit = MAX_MS_PER_FIRST_ACT

        error = False
        try:
            response = self._process.get_response(data, ms_timelimit=timelimit)
            if response['result'] == 'ok':
                return response['ret']
            else:
                error = True
            raise response['error']
        except (TimeoutError, TimeoutCannotRecoverError) as e:
            error = True
            raise e
        finally:
            if error:
                self._output_file.write(
                    'Error for bot {0}\n'.format(int(self.player_id) + 1))
                self.errors += 1
                if self.errors > 2:
                    self._output_file.write(
                        '\n\n3 or more errors, forfeiting bot ' +
                        '{0}.\n\n'.format(int(self.player_id) + 1))
                    self.skip = True
            self._output_file.write(self._process.get_output())

def make_player(proxy_proc, output_file):
    global settings

    robot = None
    try:
        result = proxy_proc.get_response({'query': 'Robot'}, MAX_MS_PER_CALL)
        if result['result']:
            robot = ProxyBot(proxy_proc, output_file)
    except Exception as e:
        traceback.print_exc(file=output_file)
    finally:
        output_file.write(proxy_proc.get_output())
        output_file.flush()

    if robot is None:
        return None
    return game.Player(robot=robot)

class ProxyDeadError(Exception): pass

def run_game(db, match, output_file):
    global settings

    proxy_process1, proxy_process2 = None, None
    try:
        load_map('rgkit/maps/default.py')

        output_file.write('---Starting Robot 1---\n')
        proxy_process1 = ProxyProcess(match['r1_code'])
        p1 = make_player(proxy_process1, output_file)
        if p1 is None:
            db.update('robots', passed=False,
                      where='id=$id', vars={'id': match['r1_id']})
            raise Exception('Robot 1 not able to be instantiated.')

        output_file.write('---Starting Robot 2---\n')
        proxy_process2 = ProxyProcess(match['r2_code'])
        p2 = make_player(proxy_process2, output_file)
        if p2 is None:
            db.update('robots', passed=False,
                      where='id=$id', vars={'id': match['r2_id']})
            raise Exception('Robot 2 not able to be instantiated.')

        if not (proxy_process1 is not None
                and proxy_process2 is not None
                and proxy_process1.alive()
                and proxy_process2.alive()):
            raise ProxyDeadError('the process is dead')
        g = game.Game([p1, p2], record_actions=False, record_history=True,
                      print_info=True, seed=match['seed'], symmetric=SYMMETRIC)
        g.run_all_turns()
        if not (proxy_process1 is not None
                and proxy_process2 is not None
                and proxy_process1.alive()
                and proxy_process2.alive()):
            raise ProxyDeadError('the process is dead')

        game_scores = g.get_scores()
        r1_score, r2_score = game_scores
        score = calc_score(game_scores)
        history = g.history
        match_data = shorten.dumps({'history': history, 'score': game_scores})
        winner = {1: match['r1_id'], 0: match['r2_id'], 0.5: 0}[score]

        output_file.write('---Time Taken---\n')
        r1_time = None
        r2_time = None
        try:
            r1_time = get_cpu_time(proxy_process1.pid)
            r2_time = get_cpu_time(proxy_process2.pid)
            output_file.write('R1: {0}\nR2: {1}\n'.format(r1_time, r2_time))
        except Exception:
            traceback.print_exc(file=output_file)

        # turn off printing here because the output for data is huge
        old_print = db.printing
        db.printing = False
        db.insert(
            'history',
            match_id=match['id'], data=match_data, timestamp=int(time.time()))
        db.update(
            'matches',
            where='id=$id', vars={'id': match['id']},
            winner=winner, state=ms.DONE,
            r1_score=r1_score, r2_score=r2_score,
            r1_time=r1_time, r2_time=r2_time,
            timestamp=int(time.time()))
        db.printing = old_print

        return score, r1_time, r2_time
    finally:
        if proxy_process1 is not None:
            proxy_process1.cleanup()
        if proxy_process2 is not None:
            proxy_process2.cleanup()

def run_match(db, match):
    sys.stdout.flush()
    sys.stderr.flush()
    with open('/var/log/robot/matches/%d' % match['id'], 'w+') as f:
        try:
            sys.stdout = sys.stderr = f
            db.update('matches', where='id=$id', vars={'id': match['id']},
                      state=ms.RUNNING)
            score, r1_time, r2_time = run_game(db, match, f)
            if match['ranked']:
                update_ratings(db, match, score)
                update_stats(db, match, r1_time, r2_time, score)
        except Exception as e:
            traceback.print_exc(file=f)
            db.update('matches', where='id=$id', state=ms.ERROR,
                      vars={'id': match['id']})
    sys.stdout = sys.__stdout__
    sys.stderr = sys.__stderr__
    time.sleep(S_MATCH_REST)

def get_match(db, mid):
    query = '''
        select
            matches.*,
            r1.compiled_code as r1_code, r2.compiled_code as r2_code,
            r1.rating as r1_rating, r2.rating as r2_rating,
            r1.name as r1_name, r2.name as r2_name
        from matches
            join robots r1 on r1.id = matches.r1_id
            join robots r2 on r2.id = matches.r2_id
        where matches.id = $id'''

    match = db.query(query, vars={'id': mid})
    return match[0] if match else None

if __name__ == '__main__':
    try:
        db = dbcon.connect_db()
        if len(sys.argv) > 1:
            match = get_match(db, int(sys.argv[1]))
            run_match(match)
    except Exception:
        traceback.print_exc(file=sys.stdout)

