'''
Run automatic and manual matches together, interleaved.
'''
import datetime
import multiprocessing
import os
import random
import sys
import time

import dbcon
import gamecron
import matchstate as ms
import rungame
import tools
from rgkit.settings import settings


def try_create_matches(db):
    E = 2.71828
    MATCHED_SKIP = True
    INSERT_BATCH = 25
    RATING_RANGE = 200
    M_INC = 0.01
    WINNING_RATE = 0.75

    def match_robots(bots):
        matches = []
        matched = set()
        # Filter out lower pri bots
        #print 'num bots before {0}'.format(len(bots))
        #bots = [bot for bot in bots if random.random() < bot['priority']]
        #print 'num bots after  {0}'.format(len(bots))
        random.shuffle(bots)
        #half = len(bots) / 2
        estimate = 0
        for bot in bots:
            if bot['last_match'] is None:
                continue
            elapsed = time.time() - bot['last_match']
            updated = time.time() - bot['last_updated']
            # number 1 bot by definition has a high win rate, should not have
            # bonus based on it.
            winning = bot['winrate'] > WINNING_RATE and bot['rating'] < 3600
            pri = bot['priority']
            if updated < tools.HOUR or winning:
                pri = 1.0
            bot['priority'] = max(0.0, min(1.0, pri))
        for bot in bots:
            # Match half of everyone at least
            #half -= 1
            #if ((bot['automatch'] or random.random() < bot['priority'])
            # Match everyone
            #if bot['id'] not in matched:
            if (random.random() < bot['priority']
                and bot['id'] not in matched):
                rating1 = bot['rating']
                def match_prob(rating2):
                    return E**(-((rating1-rating2)/RATING_RANGE)**2)
                prob_dist = {}
                num = 0
                total = 0.0
                for obot in bots:
                    # Only match unmatched bots and not last matched opponents
                    if (obot != bot
                            and obot['id'] not in matched
                            and obot['id'] != bot['last_opponent']
                            and obot['last_opponent'] != bot['id']
                            and not (bot['user_id'] == 1
                                     and obot['user_id'] == 1)):
                        p = match_prob(obot['rating']) * obot['priority']
                        num += 1
                    else:
                        p = 0
                    total += p
                    prob_dist[obot['id']] = p
                if num == 0:
                    continue
                r = random.uniform(0, total)
                upto = 0.0
                opp = None
                for obot in bots:
                    if upto + prob_dist[obot['id']] > r:
                        opp = obot
                        break
                    upto += prob_dist[obot['id']]
                assert opp is not None, 'No opponent found.'
                if MATCHED_SKIP:
                    matched.add(bot['id'])
                    matched.add(opp['id'])
                #print 'matched {0:.5g} {1:.5g}'.format(bot['rating'], opp['rating'])
                matches.append((bot, opp))
                estimate += bot['time'] + opp['time'] + rungame.S_MATCH_REST
        matched_ids = []
        for id in matched:
            matched_ids.append(str(id))
        if matched_ids:
            db.update('robots', where='id in (' + ','.join(matched_ids) + ')',
                      priority=0)
        db.query('''UPDATE robots SET priority=priority+$p
                    WHERE compiled and passed and not disabled''',
                    vars={'p': M_INC})
        print('Estimated ranked time: {0}s'.format(round(estimate, 3)))
        #matches.sort(key=lambda (a, b): a['rating'] + b['rating'])
        random.shuffle(matches)
        return matches

    def get_ready_robots():
        avg_rating = db.select('robots', what='AVG(rating)',
                where='passed and compiled and not disabled')[0]['avg']
        print('Avg rating: {}'.format(avg_rating))
        if avg_rating > tools.DEFAULT_RATING:
            robots = db.select('robots',
                what='''id, user_id, name, rating, automatch, last_opponent,
                        priority, time, last_match, winrate, last_updated,
                        disabled''',
                where='''((passed and compiled and not disabled) or
                          (user_id = 1 and disabled and not deleted))''')
        else:
            robots = db.select('robots',
                what='''id, user_id, name, rating, automatch, last_opponent,
                        priority, time, last_match, winrate, last_updated,
                        disabled''',
                where='''passed and compiled and not disabled''')
        all_bots = []
        for robot in robots:
            if robot.rating is not None:
                rating = robot.rating
            else:
                rating = tools.DEFAULT_RATING
            all_bots.append({
                'id': robot.id,
                'user_id': robot.user_id,
                'name': robot.name,
                'rating': rating,
                'automatch': robot.automatch,
                'last_opponent': robot.last_opponent,
                'priority': 1.0 if robot.user_id == 1 and robot.disabled else robot.priority,
                'time': robot.time,
                'last_match': robot.last_match,
                'winrate': robot.winrate,
                'last_updated': robot.last_updated,
            })
        return all_bots

    def num_automatch_robots():
        result = db.select('robots',
            what='count(*)',
            where=('automatch and passed and compiled and not disabled'))
        if not result:
            return 0
        return result[0]['count']

    def num_matches_to_run():
        result = db.select('matches',
            where='state = %d and ranked' % ms.WAITING,
            what='count(*)')
        if not result:
            return 0
        return result[0]['count']

    def last_ranked_timestamp():
        result = db.select('matches',
            where='state = %d and ranked' % ms.DONE,
            what='timestamp', order='timestamp desc', limit=1)
        if not result:
            return 0
        return result[0]['timestamp']

    def create_matches(pairs):
        seed = random.randint(1, settings.max_seed)
        to_insert = []
        def insert(r1, r2):
            to_insert.append({
                'r1_id': r1['id'],
                'r2_id': r2['id'],
                'ranked': True,
                'r1_rating': r1['rating'],
                'r2_rating': r2['rating'],
                'seed': seed,
                'k_factor': 0.0, # TBD
            })
            if len(to_insert) >= INSERT_BATCH:
                num = len(db.multiple_insert('matches', to_insert))
                to_insert[:] = []  # Must clear list reference
                return num
            return 0
        num_inserted = 0
        for r1, r2 in pairs:
            num_inserted += insert(r1, r2)
        if not rungame.SYMMETRIC:
            # Flipped
            # Eh... how about just random no flip...
            for r1, r2 in pairs:
                num_inserted += insert(r2, r1)
        if to_insert:
            num_inserted += len(db.multiple_insert('matches', to_insert))
        return num_inserted

    num = num_matches_to_run()
    num_robots = num_automatch_robots()
    last_ranked = last_ranked_timestamp()
    if num > 0:
        print('still {0} matches to run for {1} automatch robots'.format(
            num, num_robots))
    else:
        cur_time = int(time.time())

        robots = get_ready_robots()
        pairs = match_robots(robots)
        print 'generated %d matches' % len(pairs)

        num_inserted = create_matches(pairs)
        print 'inserted {0} matches'.format(num_inserted)


def get_matches(db, ranked=True, limit=1):
    query = '''
        select
            matches.*,
            r1.compiled_code as r1_code, r2.compiled_code as r2_code,
            r1.rating as r1_rating, r2.rating as r2_rating,
            r1.name as r1_name, r2.name as r2_name
        from matches
            join robots r1 on r1.id = matches.r1_id
            join robots r2 on r2.id = matches.r2_id
        where state = {0} and ranked = {1}
        order by matches.id asc
        limit {2}
        '''.format(ms.WAITING, ranked, limit)
    return db.query(query)


def sync_get_match(db, lock):
    lock.acquire()
    try:
        matches = get_matches(db, ranked=False, limit=1)
        if matches:
            match = matches[0]
            db.update('matches', where='id=$id', vars={'id': match['id']},
                      state=ms.RUNNING)
            return match
    finally:
        lock.release()
    return None


def run_unranked_match(lock):
    db = dbcon.connect_fresh_db()
    match = sync_get_match(db, lock)
    ret = 0
    if match:
        r1_rating = match.r1_rating or tools.DEFAULT_RATING
        r2_rating = match.r2_rating or tools.DEFAULT_RATING
        print('unranked {0:5}({1:.5g}) v {2:5}({3:.5g}) : m {4} s {5}'.format(
            match.r1_id, r1_rating, match.r2_id, r2_rating,
            match.id, match.seed))
        rungame.run_match(db, match)
        ret = 1
    db.ctx.db.close()
    return ret


def run_ranked_match(match):
    db = dbcon.connect_fresh_db()
    ret = 0
    if match:
        rungame.run_match(db, match)
        ret = 1
    db.ctx.db.close()
    return ret


t = 0
def main():
    BATCH = 1000
    REST = 60
    PER_REST = 5
    r_time = 0
    u_time = 0
    r_count = 0
    u_count = 0
    def lap():
        global t
        e = time.time() - t
        t = time.time()
        return e

    # Not necessary to be high priority
    os.nice(5)

    print('\nstarting matchmaker {0}'.format(datetime.datetime.today()))
    db = dbcon.connect_db()
    try_create_matches(db)
    cron = gamecron.Scheduler()
    lock = multiprocessing.Manager().Lock()

    ranked_matches = get_matches(db, ranked=True, limit=BATCH)
    n = 1
    for match in ranked_matches:
        lap()
        u_count += cron.schedule(run_unranked_match, lock)
        u_time += lap()
        r1_rating = match.r1_rating or tools.DEFAULT_RATING
        r2_rating = match.r2_rating or tools.DEFAULT_RATING
        print('{6:2} ranked {0:5}({1:.5g}) v {2:5}({3:.5g}) : m {4} s {5}'.format(
            match.r1_id, r1_rating, match.r2_id, r2_rating,
            match.id, match.seed, n))
        sys.stdout.flush()
        n += 1
        r_count += cron.schedule(run_ranked_match, match)
        r_time += lap()

    if r_count:
        print('R - avg {0:.3g}s {1} games in {2:.4g}s '.format(
            r_time / r_count, r_count, r_time))
    rest = REST
    rested = 0
    print('resting for {0}s'.format(rest))
    while rested < rest:
        rested += PER_REST
        sys.stdout.flush()
        time.sleep(PER_REST)
        lap()
        u_count += cron.schedule(run_unranked_match, lock)
        u_time += lap()
    if u_count:
        print('U - avg {0:.3g}s {1} games in {2:.4g}s '.format(
            u_time / u_count, u_count, u_time))
    print('rested for {0}s'.format(rested))
    cron.wait()
    os.system('python matchmaker.py &')


if __name__ == '__main__':
    main()
