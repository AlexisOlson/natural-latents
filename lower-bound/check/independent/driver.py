"""PACK-REPLAY-V4 driver: schedules proposer and checker subprocesses over families; resumable.

usage: python driver.py WORK_DIR FAMILIES [--workers=13] [--target=3000]
  FAMILIES: 'd0' (finished d0 families), 'rest' (all other finished families), 'all', or i,j,k
State lives in WORK_DIR: certs/<i>/<s>_<e>[_tag].jsonl.gz, results/<i>/<s>_<e>[_tag].json, results/kraft_<i>.json.
A job is done when its checker result exists.  Rejected leaves are retried one at a time: --deep, then --split=1,2,3.
The driver trusts nothing from these results; summarize.py (stdlib, python -I) assembles the per-family verdicts.
"""
import sys, os, json, gzip, time, subprocess, glob

HERE = os.path.dirname(os.path.abspath(__file__))
REPAIRS = [('deep', ['--deep']), ('split1', ['--split=1']), ('split2', ['--split=2']), ('split3', ['--split=3'])]


try:
    import psutil
except ImportError:
    psutil = None
MIN_FREE_GB = 5                                                    # launch nothing new below this much free memory


def log(W, msg):
    line = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()) + ' ' + msg
    with open(os.path.join(W, 'logs', 'driver.log'), 'a', newline='\n') as f:
        f.write(line + '\n')
    print(line, flush=True)


def clock(t):
    """local wall-clock time, e.g. '9:42 am'"""
    return time.strftime('%I:%M %p', time.localtime(t)).lstrip('0').lower()


def free_gb():
    return psutil.virtual_memory().available / 2**30 if psutil else float('inf')


def main():
    W = sys.argv[1]; which = sys.argv[2]
    opt = dict(a.split('=', 1) for a in sys.argv[3:] if '=' in a)
    NW = int(opt.get('--workers', 13)); TARGET = int(opt.get('--target', 3000))
    R = os.path.join(W, 'refreeze'); cov = os.path.join(R, 'cover', 'v4')
    law, price, tr = (os.path.join(R, p) for p in ('pb/law.json', 'price/price_v4.json', 'state/transfer.json'))
    fams = {}
    for f in glob.glob(os.path.join(cov, 'fam_*.json')):
        d = json.load(open(f)); fams[d['i']] = d
    if which == 'all':
        idx = sorted(fams)
    elif which in ('d0', 'rest'):
        idx = sorted(i for i in fams if (fams[i]['name'].startswith('d0_')) == (which == 'd0'))
    else:
        idx = [int(x) for x in which.split(',')]
    idx.sort(key=lambda i: -fams[i]['leaves'])                     # largest first, for load balance
    env = dict(os.environ, NUMBA_CACHE_DIR=os.path.join(W, 'numba_cache'), PYTHONPYCACHEPREFIX=os.path.join(W, 'pycache'))
    for d in ('certs', 'results', 'logs'):
        os.makedirs(os.path.join(W, d), exist_ok=True)

    queue = []                                                     # (priority, kind, payload)
    for i in idx:
        os.makedirs(os.path.join(W, 'certs', str(i)), exist_ok=True); os.makedirs(os.path.join(W, 'results', str(i)), exist_ok=True)
        leaves = os.path.join(cov, f'leaves_{i}.json.gz')
        if not os.path.exists(os.path.join(W, 'results', f'kraft_{i}.json')):
            queue.append((0, 'kraft', (i,)))
        L = fams[i]['leaves']; nj = max(1, round(L / TARGET))
        bounds = [L * t // nj for t in range(nj + 1)]
        for s, e in zip(bounds, bounds[1:]):
            queue.append((2, 'job', (i, s, e, '', [])))
    running = []
    t_start = time.time(); done_jobs = 0

    base = {(q[2][0], q[2][1], q[2][2]) for q in queue if q[1] == 'job'}           # every first-pass job range
    total_leaves = sum(e - s for _, s, e in base)
    finished = {j for j in base if os.path.exists(os.path.join(W, 'results', str(j[0]), f'{j[1]}_{j[2]}.json'))}
    n_before = len(finished); low_mem_noted = False
    print(f'{clock(time.time())}: {len(finished)} of {len(base)} jobs already done '
          f'({sum(e - s for _, s, e in finished):,} of {total_leaves:,} leaves); '
          f'{len(base) - len(finished)} to go on {NW} workers.', flush=True)

    def progress():
        k = len(finished); left = len(base) - k
        leaves = sum(e - s for _, s, e in finished)
        msg = f'    {clock(time.time())}  {k}/{len(base)} jobs  {leaves:,}/{total_leaves:,} leaves ({100 * leaves / total_leaves:.1f}%)'
        new = k - n_before; mins = (time.time() - t_start) / 60
        if new >= NW and left:                                     # rate from this run only, once every worker has finished one job
            rate = new / mins
            msg += f'  {rate:.1f} jobs/min  ETA {clock(time.time() + 60 * left / rate)}'
        print(msg + f'  free mem {free_gb():.0f} GB', flush=True)

    def paths(i, s, e, tag):
        nm = f'{s}_{e}' + (f'_{tag}' if tag else '')
        return (os.path.join(W, 'certs', str(i), nm + '.jsonl.gz'), os.path.join(W, 'results', str(i), nm + '.json'))

    def launch(kind, payload):
        if kind == 'kraft':
            (i,) = payload
            cmd = [sys.executable, '-I', os.path.join(HERE, 'checker.py'), 'kraft', str(i), os.path.join(cov, f'leaves_{i}.json.gz'),
                   os.path.join(W, 'results', f'kraft_{i}.json')]
        elif kind == 'prop':
            i, s, e, tag, extra = payload
            certf, _ = paths(i, s, e, tag)
            cmd = [sys.executable, os.path.join(HERE, 'proposer.py'), os.path.join(R, 'rf'), price, os.path.join(cov, f'leaves_{i}.json.gz'),
                   str(i), str(s), str(e), certf] + extra
        else:
            i, s, e, tag, extra = payload
            certf, resf = paths(i, s, e, tag)
            cmd = [sys.executable, '-I', os.path.join(HERE, 'checker.py'), 'chunk', law, price, tr, str(i),
                   os.path.join(cov, f'leaves_{i}.json.gz'), str(s), str(e), certf, resf]
        lf = open(os.path.join(W, 'logs', f'{kind}_{"_".join(str(p) for p in payload[:4])}.log'), 'a')
        return subprocess.Popen(cmd, stdout=lf, stderr=subprocess.STDOUT, env=env, cwd=W), lf

    while queue or running:
        # expand 'job' entries into their next step
        ready = []
        for pr, kind, payload in queue:
            if kind == 'job':
                i, s, e, tag, extra = payload
                certf, resf = paths(i, s, e, tag)
                if os.path.exists(resf):
                    res = json.load(open(resf)); done_jobs += 1
                    for rj in res['rejected']:
                        k = int(rj['idx']); step = [t for t, _ in REPAIRS].index(tag) + 1 if tag else 0
                        if step < len(REPAIRS) and not any(q[2][:3] == (i, k, k + 1) for q in ready if q[1] == 'job'):
                            ready.append((1, 'job', (i, k, k + 1, REPAIRS[step][0], REPAIRS[step][1])))
                            log(W, f'repair {fams[i]["name"]} leaf {k}: {rj["reason"]} margin {rj.get("margin_float")} -> {REPAIRS[step][0]}')
                        elif step >= len(REPAIRS):
                            log(W, f'UNCERTIFIED {fams[i]["name"]} leaf {k} after split3: {rj["reason"]} {rj.get("margin_float")}')
                    continue
                ready.append((pr, 'chk' if os.path.exists(certf) else 'prop', payload))
            else:
                ready.append((pr, kind, payload))
        queue = []; seen = set()
        for q in ready:
            key = (q[1], tuple(map(str, q[2][:4])))
            if key not in seen:
                seen.add(key); queue.append(q)
        busy = {(k, tuple(map(str, p[:4]))) for k, p, _, _ in running}
        queue.sort(key=lambda q: (q[0], 0 if q[1] == 'chk' else 1))
        nxt = []
        for q in queue:
            if (q[1], tuple(map(str, q[2][:4]))) in busy:
                continue
            if len(running) < NW and q[1] != 'job' and running and free_gb() < MIN_FREE_GB:
                if not low_mem_noted:
                    print(f'    {clock(time.time())}  holding new launches: {free_gb():.1f} GB free < {MIN_FREE_GB} GB', flush=True)
                    low_mem_noted = True
                nxt.append(q); continue
            if len(running) < NW and q[1] != 'job':
                low_mem_noted = False
                proc, lf = launch(q[1], q[2]); running.append((q[1], q[2], proc, lf))
                busy.add((q[1], tuple(map(str, q[2][:4]))))
            else:
                nxt.append(q)
        queue = [q for q in nxt]
        time.sleep(2)
        still = []
        for kind, payload, proc, lf in running:
            rc = proc.poll()
            if rc is None:
                still.append((kind, payload, proc, lf)); continue
            lf.close()
            if rc != 0:
                log(W, f'FAILED {kind} {payload[:4]} rc={rc}')
                continue
            if kind in ('prop', 'chk'):
                queue.append((1 if payload[3] else 2, 'job', payload))
            if kind == 'chk':
                res = json.load(open(paths(*payload[:4])[1]))
                log(W, f'checked {fams[payload[0]]["name"]} [{payload[1]},{payload[2]}){payload[3] and " " + payload[3]}: '
                       f'accepted {res["accepted"]}/{res["leaves"]} rejected {len(res["rejected"])} min {res.get("min_margin_float")} '
                       f'cpu {res["cpu_seconds"]:.0f}s; elapsed {time.time() - t_start:.0f}s')
                if not payload[3]:
                    finished.add(tuple(payload[:3])); progress()
            if kind == 'kraft':
                log(W, f'kraft {fams[payload[0]]["name"]} ok')
        running = still
    log(W, f'driver finished {which}')


if __name__ == '__main__':
    main()
