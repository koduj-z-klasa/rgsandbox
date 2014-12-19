import multiprocessing
import multiprocessing.pool
import os

class NonDaemonProcess(multiprocessing.Process):
    def _get_daemon(self):
        return False
    def _set_daemon(self, val):
        pass
    daemon = property(_get_daemon, _set_daemon)

class NonDaemonPool(multiprocessing.pool.Pool):
    Process = NonDaemonProcess

MAX_PROCESSES = 1
MAX_TASKS = 100
class Scheduler:
    def __init__(self, procs=MAX_PROCESSES, max_tasks=MAX_TASKS):
        self._pool = NonDaemonPool(procs, maxtasksperchild=max_tasks)

    def schedule(self, match_func, *params):
        #self._pool.apply_async(match_func, params)
        return self._pool.apply(match_func, params)

    def wait(self):
        self._pool.close()
        self._pool.join()
