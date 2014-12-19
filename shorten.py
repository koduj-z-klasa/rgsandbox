import bz2
import zlib
import base64
import pickle

def dumps(obj):
    obj = pickle.dumps(obj)
    obj = zlib.compress(obj)
    obj = bz2.compress(obj)
    return base64.b64encode(obj)


def loads(s):
    s = base64.b64decode(s)
    s = bz2.decompress(s)
    s = zlib.decompress(s)
    return pickle.loads(s)
