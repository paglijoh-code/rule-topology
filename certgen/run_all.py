"""Certify every distinct wall game (32 + 30) in parallel; resumable.

    python3 -m certgen.run_all > certgen/out/run.log 2>&1 &

Per game: a child process `python -m certgen.certify ID` with a hard timeout (30 min).  One line per game in
certgen/out/summary.jsonl (an id already in the file is skipped), certificate in OUT/certs/<id>.json.
"""
import json, os, signal, subprocess, sys, threading, time
from concurrent.futures import ThreadPoolExecutor

from . import walls, game3

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, 'out')
SUMMARY = os.path.join(OUT, 'summary.jsonl')
TIMEOUT = 1800
WORKERS = 1
lock = threading.Lock()


def done_ids():
    ids = set()
    if os.path.exists(SUMMARY):
        for line in open(SUMMARY):
            r = json.loads(line)
            ids.add(r['id']); ids.update(r.get('dup_ids', []))
    return ids


def record(summ):
    with lock:
        with open(SUMMARY, 'a') as f:
            f.write(json.dumps(summ) + '\n')
        print('%s [%s] %s %s %.0fs' % (time.strftime('%H:%M:%S'), summ['status'], summ['id'],
                                       summ.get('reason', '')[:120], summ.get('seconds', 0)), flush=True)


def job(rec, ids):
    t0 = time.time()
    rf = os.path.join(OUT, 'result_%s.json' % walls.safe_id(rec['id']))
    if os.path.exists(rf): os.unlink(rf)
    cmd = [sys.executable, '-m', 'certgen.certify', rec['id'], '--out', OUT]
    p = subprocess.Popen(cmd, cwd=os.path.dirname(HERE), start_new_session=True,
                         stdout=open(os.path.join(OUT, 'log_%s.txt' % walls.safe_id(rec['id'])), 'w'),
                         stderr=subprocess.STDOUT)
    try:
        p.wait(timeout=TIMEOUT)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL); p.wait()
        record(dict(id=rec['id'], source=rec['source'], dup_ids=[i for i in ids if i != rec['id']],
                    status='timeout', reason='killed after %d s' % TIMEOUT, N=len(rec['gpre']),
                    p=len(rec['gper']), m=max(rec['S1']), seconds=round(time.time() - t0, 1)))
        return
    if os.path.exists(rf):
        record(json.load(open(rf)))
    else:
        record(dict(id=rec['id'], source=rec['source'], dup_ids=[i for i in ids if i != rec['id']], status='error',
                    reason='child exit %s without result' % p.returncode, seconds=round(time.time() - t0, 1)))


def main():
    os.makedirs(OUT, exist_ok=True)
    game3._build()
    recs = walls.load_all()
    groups = walls.distinct(recs)
    seen = done_ids()
    todo = [(r, ids) for r, ids in groups if r['id'] not in seen]
    print('%d games, %d to do' % (len(groups), len(todo)), flush=True)
    for r, ids in groups:
        if len(ids) > 1: print('duplicates:', ids, flush=True)
    with ThreadPoolExecutor(WORKERS) as ex:
        list(ex.map(lambda a: job(*a), todo))
    print('finished', flush=True)


if __name__ == '__main__':
    main()
