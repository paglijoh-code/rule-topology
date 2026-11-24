"""Certificate JSON (m6-cert-1, see docs/certificate-format.md) from a closed symbolic run."""


def enc_moves(mv):
    out = []
    for m in mv:
        if m[0] in ('pull', 'abs'): out.append([m[0], m[1], m[2]])
        elif m[0] == 'fold': out.append(['fold', m[1], m[2], m[3], m[4]])
        else: out.append(list(m))
    return out


def fit_aff(js, vals):
    a = (vals[1] - vals[0]) // (js[1] - js[0]); b = vals[0] - a * js[0]
    assert all(a * j + b == v for j, v in zip(js, vals)), 'not affine'
    return [a, b]


def build_cert(run, tf, rounds, R, k0, Kmax, rec_wall, W, params, law, K=25):
    hist, keys = run.hist, run.keys
    gaps = [tf(k + 1) - tf(k) for k in range(Kmax)]
    alpha = gaps[1] - gaps[0]; beta = gaps[0]
    assert all(gaps[k + 1] - gaps[k] == alpha for k in range(Kmax - 1)), 'gap not affine'
    cert = dict(format='m6-cert-1',
                wall=dict(name=rec_wall['name'], S1=list(W.S1), gpre=list(W.gpre), gper=list(W.gper)),
                m=W.m, p=W.p, N=W.N, blockLen=params['L'], margin=params['M'], cf=params['cf'], R=R, k0=k0,
                law=dict(law, alpha=alpha, beta=beta), params=params)

    def shape_json(sid, cnt):
        k_ = keys[sid]
        return dict(b=[list(b) for b in k_[0]], y=[list(y) for y in k_[1]], z=list(k_[2]), cnt=cnt)

    cert['initial'] = dict(rows=tf(k0), start=enc_moves(run.start), steps=[enc_moves(h[2]) for h in hist[:tf(k0)]])
    ends = list(range(K, tf(k0), K)) + [tf(k0)]
    cert['initial']['K'] = K
    cert['initial']['checkpoints'] = [dict(rows=r, b=[list(b) for b in keys[hist[r - 1][0]][0]],
                                           y=[list(y) for y in keys[hist[r - 1][0]][1]],
                                           z=list(keys[hist[r - 1][0]][2]), cnt=list(hist[r - 1][1])) for r in ends]
    classes = []
    for i in range(R):
        ks = [k for k in range(k0, Kmax) if k % R == i]
        js = [k // R for k in ks]
        h0 = [hist[tf(k) - 1] for k in ks]
        assert len(set(h[0] for h in h0)) == 1, 'Init shape differs inside class'
        cnt = [fit_aff(js, [h[1][ci] for h in h0]) for ci in range(len(h0[0][1]))]
        toks = rounds[ks[0]]
        ph = []
        for ti, t in enumerate(toks):
            if t[0] == 's':
                ph.append(dict(kind='step', moves=enc_moves(hist[t[3]][2])))
            else:
                Pn = len(t[1]); cs = [rounds[k][ti][2] for k in ks]
                ph.append(dict(kind='cycle', len=Pn, count=fit_aff(js, cs),
                               steps=[enc_moves(hist[t[3] + q][2]) for q in range(Pn)]))
        classes.append(dict(i=i, j0=js[0], init=shape_json(h0[0][0], cnt), phases=ph,
                            rows=[alpha * R, alpha * i + beta]))
    cert['classes'] = classes
    return cert
