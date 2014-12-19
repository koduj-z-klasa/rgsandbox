#!/usr/bin/env python

import dbcon
import matchstate as ms

if __name__ == '__main__':
    db = dbcon.connect_db()
    db.update('matches', where='state = %d' % ms.RUNNING, state=ms.WAITING)
