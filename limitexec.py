import signal
from contextlib import contextmanager
import time
import sys

class ProcessTimeoutError(Exception): pass

@contextmanager
def time_limit(seconds):
    def signal_handler(signum, frame):
        raise ProcessTimeoutError()

    signal.signal(signal.SIGPROF, signal_handler)
    signal.setitimer(signal.ITIMER_PROF, seconds)
    try:
        yield
    finally:
        signal.setitimer(signal.ITIMER_PROF, 0)
