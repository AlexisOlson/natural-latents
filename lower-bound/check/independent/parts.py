"""PACK-REPLAY-V4: minimum margin over the accepted leaves of a job that contains a rejection.

A main job's receipt keeps one min_margin over all its nodes, so when a leaf is rejected the job's passing minimum is
lost (VAL-REPLAY-V4, `summarize.py:59-63`). This splits the job's stored certificate file into the maximal ranges that
avoid the rejected leaves and runs the unchanged checker on each, writing results/<i>/<s>_<e>_part.json.
summarize.py then takes the job's accepted minimum from its parts.

usage: python parts.py WORK_DIR   (stdlib only; runs up to 5 checkers at once)
"""
import sys, os, json, gzip, glob, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))


def main():
    W = sys.argv[1]
    R = os.path.join(W, 'refreeze'); cov = os.path.join(R, 'cover', 'v4')
    law, price, tr = (os.path.join(R, p) for p in ('pb/law.json', 'price/price_v4.json', 'state/transfer.json'))
    todo = []
    for f in sorted(glob.glob(os.path.join(W, 'results', '*', '*.json'))):
        nm = os.path.basename(f)[:-5].split('_')
        if len(nm) != 2:
            continue
        r = json.load(open(f))
        if not r['rejected']:
            continue
        i, s, e = r['family'], r['start'], r['end']
        bad = sorted({int(x['idx']) for x in r['rejected']})
        certs = {}
        for line in gzip.open(os.path.join(W, 'certs', str(i), f'{s}_{e}.jsonl.gz'), 'rt'):
            if line.strip():
                c = json.loads(line); certs.setdefault(c['idx'], []).append(line)
        cuts = [s] + [x for b in bad for x in (b, b + 1)] + [e]
        for a, b in zip(cuts[::2], cuts[1::2]):
            if a >= b:
                continue
            certf = os.path.join(W, 'certs', str(i), f'{a}_{b}_part.jsonl.gz')
            resf = os.path.join(W, 'results', str(i), f'{a}_{b}_part.json')
            if os.path.exists(resf):
                continue
            with gzip.open(certf + '.tmp', 'wt', compresslevel=3, newline='\n') as g:
                for k in range(a, b):
                    g.writelines(certs[k])
            os.replace(certf + '.tmp', certf)
            todo.append([sys.executable, '-I', os.path.join(HERE, 'checker.py'), 'chunk', law, price, tr, str(i),
                         os.path.join(cov, f'leaves_{i}.json.gz'), str(a), str(b), certf, resf])
            print(f'part {i} [{a},{b}) of job [{s},{e}) without {bad}', flush=True)
    running = []
    while todo or running:
        while todo and len(running) < 5:
            running.append(subprocess.Popen(todo.pop(0), stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True))
        p = running.pop(0)
        out = p.communicate()[0]
        print(f'rc={p.returncode} ' + out.splitlines()[0][:200] if out else f'rc={p.returncode}', flush=True)


if __name__ == '__main__':
    main()
