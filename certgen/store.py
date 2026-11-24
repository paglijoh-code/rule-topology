"""Certificates shipped in certificates/ (xz-compressed JSON)."""
import json, lzma, os

from . import walls

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CERTS = os.path.join(ROOT, 'certificates')


def names():
    """wall id -> Lean module name, for every wall with a certificate except A and B (their sources are in lean/Cert)"""
    return json.load(open(os.path.join(CERTS, 'names.json')))


def load(i):
    with lzma.open(os.path.join(CERTS, 'json', walls.safe_id(i) + '.json.xz'), 'rt') as f:
        return json.load(f)


def lean_walls():
    """ids of the 32 walls with status LEAN other than A and B"""
    return [w for w in json.load(open(os.path.join(CERTS, 'reference.json')))]


def select(ids, group):
    n = names()
    if ids: return [(i, n[i]) for i in ids]
    lw = set(lean_walls())
    return [(i, m) for i, m in n.items() if group == 'all' or i in lw]
