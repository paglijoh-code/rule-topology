"""Incremental symbolic run (fam version of an earlier tracker): shapes interned, rows advanced on demand."""
from . import shape3 as shape, stack3


class Run:
    def __init__(self, W, L, M, cf=2):
        self.W, self.P = W, shape.Norm(M, L, cf)
        self.sh = shape.Shape([[]], [], [], [0] * W.p, 0)
        self.start = shape.normalise(W, self.sh, self.P)      # initial normalisation moves (tpull ...)
        self.ids, self.keys = {}, []
        self.hist = []            # per row: (sid, counters, moves, delta, gamma, slack)
        self.prev_n = []
        self.failed = None        # (row, message)

    @property
    def n(self):
        return len(self.hist)

    def advance(self, target):
        W, P = self.W, self.P
        sh = self.sh
        while len(self.hist) < target and self.failed is None:
            n = len(self.hist)
            try:
                sh, dl, ga = shape.sstep(W, sh)
                slack = min([c - g for c, g in zip(self.prev_n, ga)] + [10 ** 9])
                c = list(sh.n)
                mv = shape.normalise(W, sh, P)
            except shape.Fail as e:
                self.failed = (n, str(e)); break
            for m_ in mv:
                if m_[0] in ('pull', 'rot'):
                    slack = min(slack, c[m_[1]] - 1); c[m_[1]] -= 1
                elif m_[0] == 'abs':
                    c[m_[1]] += 1
                elif m_[0] == 'fold':
                    c.insert(m_[1], m_[3])
                elif m_[0] == 'drop':
                    assert c[m_[1]] == 0; del c[m_[1]]
            assert c == sh.n
            self.prev_n = list(sh.n)
            k = sh.key(W)
            sid = self.ids.get(k)
            if sid is None:
                sid = self.ids[k] = len(self.keys); self.keys.append(k)
            self.hist.append((sid, tuple(sh.n), mv, tuple(dl), tuple(ga), slack))
        self.sh = sh

    def shape_at(self, n):
        """Shape after row n (index into hist) with its counters"""
        k = self.keys[self.hist[n][0]]
        return shape.Shape(k[0], k[1], self.hist[n][1], k[2], 0)
