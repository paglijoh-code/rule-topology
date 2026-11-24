import sys, time, json
from lib3 import chain, analyse
N = int(sys.argv[1])
for a in sys.argv[2:]:
    sets = [tuple(map(int, s.split(","))) for s in a.split(">")]
    t = time.time(); T = chain(N, sets); r, C = analyse(T)
    print(a, json.dumps(r, default=str), "%.1fs" % (time.time() - t))
