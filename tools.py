SECOND = 1
MINUTE = 60 * SECOND
HOUR = 60 * MINUTE
DAY = 24 * HOUR
WEEK = 7 * DAY
MONTH = 30 * DAY

DEFAULT_RATING = 1200.0

def get_k_factor(rating):
    if rating >= 4800:
        return 2
    elif rating >= 4200:
        return 3
    elif rating >= 3600:
        return 4
    elif rating >= 3000:
        return 6
    elif rating >= 2400:
        return 8
    elif rating >= 1800:
        return 12
    elif rating >= 1200:
        return 16
    elif rating >= 600:
        return 24
    else:
        return 32
