"""Re-check C >= R > 2.0012323023 from this folder alone.

usage:
  python verify.py            full: (a) manifest, (b) final.py over data/ including the Kraft pass, (c) scalar check, (d) R
  python verify.py --quick    as full, but (b) skips the Kraft pass (see QUICK below)
  python verify.py --mutate   self-test: flip one byte of a copy of one data file and confirm (a) fails on it
  python verify.py --leaves [--families LIST] [--start S] [--limit N] [--chunk K] [--workers W]
                              per-leaf mode: (a), then the independent checker over every leaf of the named families
                              (default all 912; LIST is indices, ranges and names, e.g. 0,10-12,d0_L2); --start/--limit
                              restrict each family to leaves S..S+N-1; --chunk is the leaves per job (default 3000);
                              --workers W runs W jobs at once (default 1). Fails on any uncertified leaf.

Exit status is 0 only if every step it ran passed.

(a) every file under data/ and check/ is hashed and compared with MANIFEST.sha256 (sha256sum format); a missing file, a
    changed file, or an extra unlisted file fails.
(b) check/refreeze/rf/final.py, unmodified, runs over a scratch copy of data/ laid out the way it expects (see
    check/run_final.py). The copy is hashed against the manifest before the run. It re-reads all 912 family files and
    leaf sets, checks each is complete with no violation and the price hash, Kraft-checks each leaf set as a complete
    binary prefix code, and recomputes Phi_0 and the conditional ratio R in exact rationals.
    Needs numpy and numba (its common.py imports them); everything else is the standard library.
(c) check/independent/scalar.py (standard library only, run as python -I) recomputes Phi_0 and R with its own DP.
(d) prints the exact R, requires R to equal the value from (b), (c), data/price_v4.json and the constant pinned below
    (RECORD_R), and requires R > 2.0012323023 by exact rational comparison.

QUICK mode does not check, per family, that leaves_<i>.json.gz is a complete binary prefix code (Kraft sum 1):
cover.kraft is replaced by a no-op. Every other check in final.py still runs, including the leaf-count match against
fam_<i>.json. Neither full nor --quick mode runs the independent leaf checker (check/independent/checker.py): they do not
re-check the 3,448,987 leaves one by one, and final.py itself does not re-run the per-leaf exact check (its docstring says
so). That is what --leaves does; see the comment above step_leaves. It takes tens of CPU-hours for all 912 families.
Per-leaf mode checks the Kraft sum itself (checker.py kraft) whenever its actual selected slice is the whole family,
including when --start/--limit happen to select that whole family.
"""
import gzip, hashlib, os, shutil, subprocess, sys, tempfile, time, json
from fractions import Fraction

ROOT = os.path.dirname(os.path.abspath(__file__))
PRICE_SHA256 = '7dc955f68376369b2727ecace4b247013087e9e573ef433f7cde8993bbd1a98a'
BOUND = Fraction('2.0012323023')
# conditional_ratio_lower printed by the original 912-family assembly run (that log is not included here), pinned so that
# a changed data file cannot move R unnoticed
RECORD_R = Fraction(
    102395331021410935836841843679114580027925957092193752396069619230740137245107404,
    51166139433434760740393189165888283730804952847474027374683157095605028939972369)
RECORD_COUNTS = dict(families_total=912, families_complete=912, total_nodes=6897062, total_leaves=3448987)
BELOW_NORMAL = 0x4000


SCRUB = []


def add_scrub(path, label):
    """Printed text never shows local absolute paths: this folder becomes '.', a scratch directory '<scratch>'."""
    path = os.path.abspath(path)
    for v, sep in ((path, os.sep), (path.replace('\\', '\\\\'), '\\\\'), (path.replace('\\', '/'), '/')):
        SCRUB.append((v + sep, '' if label == '.' else label + sep))
        SCRUB.append((v, label))


def scrub(s):
    for a, b in sorted(SCRUB, key=lambda t: -len(t[0])):
        s = s.replace(a, b)
    return s


def say(*a):
    print(scrub(' '.join(str(x) for x in a)), flush=True)


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for blk in iter(lambda: f.read(1 << 20), b''):
            h.update(blk)
    return h.hexdigest()


def set_below_normal():
    if os.name != 'nt':
        return
    import ctypes
    k = ctypes.windll.kernel32
    k.GetCurrentProcess.restype = ctypes.c_void_p
    k.SetPriorityClass.argtypes = [ctypes.c_void_p, ctypes.c_uint32]
    k.GetPriorityClass.argtypes = [ctypes.c_void_p]
    k.GetPriorityClass.restype = ctypes.c_uint32
    h = k.GetCurrentProcess()
    if not k.SetPriorityClass(h, BELOW_NORMAL) or k.GetPriorityClass(h) != BELOW_NORMAL:
        raise RuntimeError('BelowNormal priority not verified')
    say('priority: BelowNormal verified for verify.py (children inherit it)')


def read_manifest(root):
    entries = []
    with open(os.path.join(root, 'MANIFEST.sha256'), 'r', encoding='ascii', newline='') as f:
        for ln, line in enumerate(f.read().split('\n'), 1):
            if not line:
                continue
            h, sep, p = line.partition('  ')
            if sep != '  ' or len(h) != 64 or any(c not in '0123456789abcdef' for c in h):
                raise ValueError(f'MANIFEST.sha256 line {ln} is not "<sha256>  <path>"')
            entries.append((h, p))
    paths = [p for _, p in entries]
    if paths != sorted(paths) or len(set(paths)) != len(paths):
        raise ValueError('MANIFEST.sha256 is not sorted and unique by path')
    return entries


def walk_files(root):
    out = []
    for top in ('data', 'check'):
        for dp, dn, fn in os.walk(os.path.join(root, top)):
            for f in fn:
                out.append(os.path.relpath(os.path.join(dp, f), root).replace(os.sep, '/'))
    return sorted(out)


def check_manifest(root, entries, echo):
    """returns (problems, hashes by path)"""
    problems = []; got = {}
    listed = {p for _, p in entries}
    for h, p in entries:
        fp = os.path.join(root, *p.split('/'))
        if not os.path.isfile(fp):
            problems.append(f'MISSING {p}'); continue
        d = sha256_file(fp); got[p] = d
        if echo:
            say(f'{d}  {p}  ({os.path.getsize(fp)} bytes)')
        if d != h:
            problems.append(f'MISMATCH {p}: manifest {h}, file {d}')
    for p in walk_files(root):
        if p not in listed:
            problems.append(f'EXTRA (not in manifest) {p}')
    return problems, got


def step_a(root, label='real tree'):
    say(f'--- (a) manifest check, {label}')
    entries = read_manifest(root)
    say(f'MANIFEST.sha256 sha256 = {sha256_file(os.path.join(root, "MANIFEST.sha256"))}  ({len(entries)} entries)')
    problems, got = check_manifest(root, entries, echo=True)
    for p in problems:
        say('FAIL', p)
    say(f'(a) {"PASS" if not problems else "FAIL"}: {len(entries) - len([x for x in problems if x.startswith(("MISSING", "MISMATCH"))])}'
        f' of {len(entries)} files match, {len([x for x in problems if x.startswith("EXTRA")])} extra')
    return not problems, entries


def child_env():
    env = dict(os.environ)
    for k in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS', 'NUMBA_NUM_THREADS', 'NUMEXPR_NUM_THREADS'):
        env[k] = '2'
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    return env


def run_child(cmd, cwd):
    flags = BELOW_NORMAL if os.name == 'nt' else 0
    t0 = time.time()
    p = subprocess.run(cmd, cwd=cwd, env=child_env(), stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                       creationflags=flags, stdin=subprocess.DEVNULL)
    return p.returncode, p.stdout, p.stderr, time.time() - t0


def build_scratch(entries):
    """byte copies of the files final.py needs, laid out the way it expects; returns the scratch dir"""
    tmp = tempfile.mkdtemp(prefix='c2verify_')
    add_scrub(tmp, '<scratch>')
    out = os.path.join(tmp, 'out')
    mp = {
        'check/refreeze/rf/final.py': 'rf/final.py', 'check/refreeze/rf/common.py': 'rf/common.py',
        'check/refreeze/rf/cover.py': 'rf/cover.py', 'check/refreeze/pb/repair.py': 'pb/repair.py',
        'check/refreeze/pb/runtime.py': 'pb/runtime.py', 'check/refreeze/pb/baseline/roots.py': 'pb/baseline/roots.py',
        'data/law.json': 'pb/law.json', 'data/prices.json': 'pb/prices.json', 'data/price_v4.json': 'price/price_v4.json'}
    for p in sorted(x for _, x in entries):
        if p.startswith('data/cover/v4/'):
            mp[p] = 'cover/v4/' + p[len('data/cover/v4/'):]
    expect = dict((p, h) for h, p in entries)
    for src, dst in mp.items():
        d = os.path.join(out, *dst.split('/'))
        os.makedirs(os.path.dirname(d), exist_ok=True)
        shutil.copyfile(os.path.join(ROOT, *src.split('/')), d)
        if sha256_file(d) != expect[src]:
            raise RuntimeError(f'scratch copy of {src} does not match the manifest')
    say(f'scratch tree {out}: {len(mp)} byte copies, each re-hashed against MANIFEST.sha256 after copying')
    for src in ('check/refreeze/rf/final.py', 'check/refreeze/rf/common.py', 'check/refreeze/rf/cover.py',
                'check/refreeze/pb/repair.py', 'check/refreeze/pb/runtime.py', 'check/refreeze/pb/baseline/roots.py',
                'data/law.json', 'data/prices.json', 'data/price_v4.json'):
        say(f'  input read by final.py: {expect[src]}  {src}')
    say(f'  input read by final.py: all 912 data/cover/v4/fam_<i>.json and leaves_<i>.json.gz, hashed one by one in (a)')
    return tmp, out


def step_b(entries, quick):
    say(f'--- (b) final.py over data/{" (QUICK: Kraft pass skipped)" if quick else ""}')
    tmp, out = build_scratch(entries)
    try:
        cmd = [sys.executable, '-E', '-B', os.path.join(ROOT, 'check', 'run_final.py')] + (['--no-kraft'] if quick else []) + [
            out, os.path.join(out, 'price', 'price_v4.json'), os.path.join(out, 'cover', 'v4')]
        say('command:', ' '.join(cmd))
        rc, so, se, wall = run_child(cmd, os.path.join(out, 'rf'))
        say('final.py stdout:'); say(so.rstrip())
        say('final.py stderr:'); say(se.rstrip())
        peak = None
        for line in se.splitlines():
            if line.startswith('PEAK_WORKING_SET_BYTES='):
                peak = int(line.split('=')[1])
        say(f'(b) wall time {wall:.1f} s' + (f', peak working set {peak / 2**30:.2f} GiB' if peak else ''))
        if rc != 0:
            say(f'(b) FAIL: final.py exited {rc}'); return False, None
        res = json.loads(so)
        ok = res['verdict'] == 'ACCEPTED' and res['missing'] == [] and res['price_sha256'] == PRICE_SHA256
        for k, v in RECORD_COUNTS.items():
            if res[k] != v:
                say(f'(b) FAIL: {k} = {res[k]}, pinned value {v}'); ok = False
        R = Fraction(res['conditional_ratio_lower'])
        say(f'(b) {"PASS" if ok else "FAIL"}: verdict {res["verdict"]}, {res["families_complete"]}/{res["families_total"]} families,'
            f' {res["total_leaves"]} leaves, price sha256 {res["price_sha256"]}')
        return ok, R
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def step_c():
    say('--- (c) independent scalar check (check/independent/scalar.py, python -I)')
    cmd = [sys.executable, '-I', '-B', os.path.join(ROOT, 'check', 'independent', 'scalar.py'),
           os.path.join(ROOT, 'data', 'law.json'), os.path.join(ROOT, 'data', 'price_v4.json')]
    say('command:', ' '.join(cmd))
    rc, so, se, wall = run_child(cmd, ROOT)
    say(so.rstrip());
    if se.strip():
        say(se.rstrip())
    if rc != 0:
        say(f'(c) FAIL: scalar.py exited {rc}'); return False, None
    res = json.loads(so)
    ok = res['phi0_matches_price'] and res['ratio_matches_price'] and res['numerator_positive'] and res['ratio_gt_2']
    say(f'(c) {"PASS" if ok else "FAIL"} ({wall:.1f} s): Phi_0 = {res["phi0"]}, matches price {res["phi0_matches_price"]}, '
        f'R matches price {res["ratio_matches_price"]}, numerator positive {res["numerator_positive"]}')
    return ok, Fraction(res['ratio'])


def floor_decimal(x, digits):
    n = (x.numerator * 10 ** digits) // x.denominator
    s = str(n).rjust(digits + 1, '0')
    return s[:-digits] + '.' + s[-digits:]


def step_d(Rb, Rc):
    say('--- (d) the exact R')
    price = json.load(open(os.path.join(ROOT, 'data', 'price_v4.json')))
    Rp = Fraction(price['conditional_ratio_lower'])
    R = Rc
    say(f'R = {R.numerator}/{R.denominator}')
    say(f'R, truncated (floor) to 25 decimals: {floor_decimal(R, 25)}')
    say(f'bound = {BOUND.numerator}/{BOUND.denominator} (2.0012323023)')
    ok = True
    for name, v in (('final.py (b)', Rb), ('scalar.py (c)', Rc), ('data/price_v4.json', Rp), ('the constant pinned in verify.py (RECORD_R)', RECORD_R)):
        eq = v is not None and v == R
        say(f'  R equals the value from {name}: {eq}')
        ok = ok and eq
    gt = R > BOUND
    say(f'exact rational comparison R > 2.0012323023: {gt}; R > 2: {R > 2}')
    ok = ok and gt
    say(f'(d) {"PASS" if ok else "FAIL"}')
    return ok


def step_mutate(entries):
    say('--- --mutate: flip one byte of a copy of one data file; (a) must fail on it')
    victim = 'data/cover/v4/leaves_100.json.gz'
    tmp = tempfile.mkdtemp(prefix='c2mutate_')
    add_scrub(tmp, '<scratch>')
    try:
        for top in ('data', 'check'):
            shutil.copytree(os.path.join(ROOT, top), os.path.join(tmp, top))
        shutil.copyfile(os.path.join(ROOT, 'MANIFEST.sha256'), os.path.join(tmp, 'MANIFEST.sha256'))
        say('control: unmodified copy')
        problems, _ = check_manifest(tmp, entries, echo=False)
        control_ok = not problems
        say(f'  unmodified copy passes (a): {control_ok}')
        vp = os.path.join(tmp, *victim.split('/'))
        data = bytearray(open(vp, 'rb').read())
        i = len(data) // 2
        say(f'mutation: {victim} byte {i}: 0x{data[i]:02x} -> 0x{data[i] ^ 0x01:02x}')
        data[i] ^= 0x01
        open(vp, 'wb').write(bytes(data))
        problems, _ = check_manifest(tmp, entries, echo=False)
        for p in problems:
            say('  (a) reports:', p[:200])
        detected = len(problems) == 1 and problems[0].startswith('MISMATCH ' + victim)
        say(f'  (a) fails on exactly the mutated file: {detected}')
        untouched = sha256_file(os.path.join(ROOT, *victim.split('/'))) == dict((p, h) for h, p in entries)[victim]
        say(f'  the real {victim} is unchanged: {untouched}')
        ok = control_ok and detected and untouched
        say(f'--mutate {"PASS" if ok else "FAIL"}')
        return ok
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


# ---------------------------------------------------------------------------------------------------------------------
# --leaves: the independent checker over every leaf
#
# check/independent/checker.py (standard library only, run as python -I) certifies one leaf from a certificate (the greedy
# orders and weights of the exact bound). The certificates come from check/independent/proposer.py, which re-runs
# the original search code (check/refreeze/, numpy, numba); the proposer is untrusted and its output gets no credit: the checker rebuilds
# every node from the stored path itself and accepts a leaf only if its own exact bound is positive. A leaf the checker
# rejects is retried as the replay did (proposer --deep, then --split=1,2,3: split the leaf and certify the children,
# the checker confirming the children tile it). Unless the family is only partly run (--start/--limit), the checker also
# runs its own Kraft check on the family's leaf file.

REPAIRS = [('deep', ['--deep']), ('split1', ['--split=1']), ('split2', ['--split=2']), ('split3', ['--split=3'])]
LEAF_TARGET = 3000          # leaves per job (the replay's size)


def parse_families(spec, fams):
    """'3,10-12,d0_L2' -> sorted family indices; fams is {index: name}"""
    byname = {v: k for k, v in fams.items()}
    out = set()
    for tok in spec.split(','):
        tok = tok.strip()
        if not tok:
            continue
        if tok in byname:
            out.add(byname[tok])
        elif '-' in tok and all(x.strip().isdigit() for x in tok.split('-')):
            a, b = (int(x) for x in tok.split('-'))
            if a > b:
                raise SystemExit(f'--families: descending range {tok!r}')
            out.update(range(a, b + 1))
        elif tok.isdigit():
            out.add(int(tok))
        else:
            raise SystemExit(f'--families: unknown family {tok!r}')
    if not out:
        raise SystemExit('--families: empty selection')
    bad = sorted(out - set(fams))
    if bad:
        raise SystemExit(f'--families: no such family index {bad}')
    return sorted(out)


def build_scratch_leaves(entries):
    """byte copies of what the proposer needs, laid out the way rf/common.py expects; returns (tmp, out)"""
    tmp = tempfile.mkdtemp(prefix='c2leaves_')
    add_scrub(tmp, '<scratch>')
    out = os.path.join(tmp, 'out')
    mp = {'check/refreeze/rf/common.py': 'rf/common.py', 'check/refreeze/rf/cover.py': 'rf/cover.py',
          'check/refreeze/pb/baseline/roots.py': 'pb/baseline/roots.py', 'check/refreeze/pb/baseline/core.py': 'pb/baseline/core.py',
          'check/refreeze/pb/baseline/core2.py': 'pb/baseline/core2.py', 'check/refreeze/pb/baseline/pen.py': 'pb/baseline/pen.py',
          'data/law.json': 'pb/law.json'}
    expect = dict((p, h) for h, p in entries)
    for src, dst in mp.items():
        d = os.path.join(out, *dst.split('/'))
        os.makedirs(os.path.dirname(d), exist_ok=True)
        shutil.copyfile(os.path.join(ROOT, *src.split('/')), d)
        if sha256_file(d) != expect[src]:
            raise RuntimeError(f'scratch copy of {src} does not match the manifest')
        say(f'  proposer input: {expect[src]}  {src}')
    say(f'scratch tree {out}: {len(mp)} byte copies, each re-hashed against MANIFEST.sha256 after copying')
    return tmp, out


class LeafRun:
    def __init__(self, entries, tmp, out):
        self.expect = dict((p, h) for h, p in entries)
        self.tmp = tmp; self.out = out
        self.law = os.path.join(ROOT, 'data', 'law.json'); self.price = os.path.join(ROOT, 'data', 'price_v4.json')
        self.tr = os.path.join(ROOT, 'data', 'transfer.json')
        self.cov = os.path.join(ROOT, 'data', 'cover', 'v4')
        self.env = child_env(); self.env['NUMBA_CACHE_DIR'] = os.path.join(tmp, 'numba_cache')
        self.work = os.path.join(tmp, 'work'); os.makedirs(self.work)
        self.indep = os.path.join(ROOT, 'check', 'independent')

    def run(self, cmd, what):
        flags = BELOW_NORMAL if os.name == 'nt' else 0
        p = subprocess.run(cmd, cwd=self.work, env=self.env, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                           creationflags=flags, stdin=subprocess.DEVNULL)
        if p.returncode != 0:
            raise RuntimeError(f'{what} exited {p.returncode}: {(p.stderr or p.stdout)[-1500:]}')
        return p.stdout

    def propose(self, fi, s, e, certf, extra):
        self.run([sys.executable, '-E', '-B', os.path.join(self.indep, 'proposer.py'), os.path.join(self.out, 'rf'), self.price,
                  os.path.join(self.cov, f'leaves_{fi}.json.gz'), str(fi), str(s), str(e), certf] + extra,
                 f'proposer family {fi} [{s},{e}) {extra}')

    def check(self, fi, s, e, certf, resf):
        self.run([sys.executable, '-I', '-B', os.path.join(self.indep, 'checker.py'), 'chunk', self.law, self.price, self.tr,
                  str(fi), os.path.join(self.cov, f'leaves_{fi}.json.gz'), str(s), str(e), certf, resf],
                 f'checker family {fi} [{s},{e})')
        return json.load(open(resf))

    def job(self, fi, s, e, tag='', extra=()):
        """propose and check leaves s..e-1; returns (result dict, wall seconds). The certificate file is removed after."""
        nm = f'{fi}_{s}_{e}' + (f'_{tag}' if tag else '')
        certf = os.path.join(self.work, nm + '.jsonl.gz'); resf = os.path.join(self.work, nm + '.json')
        t0 = time.time()
        self.propose(fi, s, e, certf, list(extra))
        res = self.check(fi, s, e, certf, resf)
        parts = []
        if res['rejected']:
            # the job's minimum margin is lost when a leaf is rejected; recover the accepted leaves' minimum by re-running
            # the unchanged checker on the rejection-free ranges of the same certificates
            bad = sorted({int(x['idx']) for x in res['rejected']})
            certs = {}
            for line in gzip.open(certf, 'rt'):
                if line.strip():
                    certs.setdefault(json.loads(line)['idx'], []).append(line)
            cuts = [s] + [x for b in bad for x in (b, b + 1)] + [e]
            for a, b in zip(cuts[::2], cuts[1::2]):
                if a >= b:
                    continue
                pc = os.path.join(self.work, f'{nm}_part{a}_{b}.jsonl.gz')
                with gzip.open(pc, 'wt', compresslevel=3, newline='\n') as g:
                    for k in range(a, b):
                        g.writelines(certs[k])
                parts.append(self.check(fi, a, b, pc, os.path.join(self.work, f'{nm}_part{a}_{b}.json')))
                os.remove(pc)
        os.remove(certf)
        return res, parts, time.time() - t0


def run_family(L, fi, name, nleaves, start, stop, chunk, workers, log):
    """returns dict(accepted, uncertified, splits, min_margin (Fraction or None), kraft, jobs, wall)"""
    t0 = time.time()
    total = stop - start
    nj = max(1, round(total / chunk))
    bounds = [start + total * t // nj for t in range(nj + 1)]
    ranges = [(a, b) for a, b in zip(bounds, bounds[1:]) if a < b]
    out = dict(name=name, leaves=total, accepted=0, uncertified=[], splits=[], min_margin=None, kraft=None, repairs=0)

    def note_margin(m):
        if m is not None:
            m = Fraction(m)
            out['min_margin'] = m if out['min_margin'] is None else min(out['min_margin'], m)

    def one(rg):
        s, e = rg
        res, parts, wall = L.job(fi, s, e)
        return rg, res, parts, wall

    if workers > 1:
        from concurrent.futures import ThreadPoolExecutor
        with ThreadPoolExecutor(workers) as ex:
            results = list(ex.map(one, ranges))
    else:
        results = [one(rg) for rg in ranges]
    for (s, e), res, parts, wall in results:
        out['accepted'] += res['accepted']
        out['splits'] += [(x['idx'], x['children']) for x in res['split_leaves']]
        if not res['rejected']:
            note_margin(res['min_margin'])
        for pr in parts:
            note_margin(pr['min_margin'])
        for rj in sorted({int(x['idx']) for x in res['rejected']}):
            ok = False
            for tag, extra in REPAIRS:
                r2, p2, _ = L.job(fi, rj, rj + 1, tag, extra)
                out['repairs'] += 1
                if not r2['rejected'] and r2['accepted'] == 1:
                    note_margin(r2['min_margin']); out['accepted'] += 1; ok = True
                    out['splits'].append((rj, f'repair {tag}'))
                    break
            if not ok:
                out['uncertified'].append(rj)
        log(f'  family {fi} {name} [{s},{e}): accepted {res["accepted"]}/{res["leaves"]} first pass, '
            f'{len(res["rejected"])} rejected, job wall {wall:.1f} s')
    if start == 0 and stop == nleaves:
        kf = os.path.join(L.work, f'kraft_{fi}.json')
        L.run([sys.executable, '-I', '-B', os.path.join(L.indep, 'checker.py'), 'kraft', str(fi),
               os.path.join(L.cov, f'leaves_{fi}.json.gz'), kf], f'checker kraft family {fi}')
        k = json.load(open(kf))
        out['kraft'] = (k['leaves'] == nleaves and k['kraft'] == 'complete prefix code, sum 1')
    out['wall'] = time.time() - t0
    return out


def step_leaves(entries, fam_spec, start, limit, chunk, workers):
    say('--- --leaves: independent checker (check/independent/checker.py) over the leaves, certificates from proposer.py')
    fams = {}
    for _, p in entries:
        if p.startswith('data/cover/v4/fam_'):
            d = json.load(open(os.path.join(ROOT, *p.split('/'))))
            fams[d['i']] = (d['name'], d['leaves'])
    idx = parse_families(fam_spec, {i: v[0] for i, v in fams.items()}) if fam_spec is not None else sorted(fams)
    say(f'families: {len(idx)} of {len(fams)}' + (f'; leaves from {start}, at most {limit} per family' if (start or limit) else ''))
    tmp, out = build_scratch_leaves(entries)
    try:
        L = LeafRun(entries, tmp, out)
        say('checker constants (E_block against the checker\'s own 400-bit logarithms):')
        so = L.run([sys.executable, '-I', '-B', os.path.join(L.indep, 'checker.py'), 'consts', L.law, L.price, L.tr], 'checker consts')
        cj = json.loads(so)
        say(f'  stored error >= own upper bound: {cj["stored_ge_own"]}; law symmetric: {cj["p_symmetric"]}; {cj["independence"]}')
        t0 = time.time(); allok = cj['stored_ge_own']; tot_leaves = tot_acc = 0; mm = None
        for fi in idx:
            name, nleaves = fams[fi]
            a = min(start, nleaves); b = nleaves if limit is None else min(nleaves, a + limit)
            if a >= b:
                say(f'family {fi} {name}: nothing in range'); continue
            r = run_family(L, fi, name, nleaves, a, b, chunk, workers, say)
            ok = not r['uncertified'] and r['accepted'] == r['leaves'] and r['kraft'] is not False
            allok = allok and ok
            tot_leaves += r['leaves']; tot_acc += r['accepted']
            if r['min_margin'] is not None:
                mm = r['min_margin'] if mm is None else min(mm, r['min_margin'])
            kr = {True: 'complete prefix code (own Kraft check)', False: 'KRAFT FAIL', None: 'Kraft not run (family only partly covered)'}[r['kraft']]
            say(f'family {fi} {name}: {r["accepted"]}/{r["leaves"]} leaves certified, uncertified {r["uncertified"]}, '
                f'repairs/splits {r["splits"]}, min margin {float(r["min_margin"]) if r["min_margin"] is not None else None}, '
                f'{kr}, wall {r["wall"]:.1f} s -> {"ok" if ok else "FAIL"}')
        wall = time.time() - t0
        say(f'--leaves total: {tot_acc}/{tot_leaves} leaves certified, minimum exact margin '
            f'{float(mm) if mm is not None else None}, wall {wall:.1f} s' + (f' ({tot_leaves / wall:.1f} leaves/s)' if wall else ''))
        if tot_leaves == 0:
            say('--leaves FAIL: no leaves selected')
        ok = allok and tot_leaves > 0 and tot_acc == tot_leaves
        say(f'--leaves {"PASS" if ok else "FAIL"}')
        return ok
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def main():
    argv = sys.argv[1:]
    opts = {}; flags = set(); i = 0
    while i < len(argv):
        a = argv[i]
        if a in ('--quick', '--mutate', '--leaves'):
            flags.add(a)
        elif a.split('=')[0] in ('--families', '--limit', '--start', '--chunk', '--workers'):
            if '=' in a:
                k, v = a.split('=', 1)
            elif i + 1 < len(argv):
                k, v = a, argv[i + 1]; i += 1
            else:
                print(__doc__); return 2
            opts[k] = v
        else:
            print(__doc__); return 2
        i += 1
    if len(flags) > 1 or (opts and '--leaves' not in flags):
        print(__doc__); return 2
    try:
        limit = int(opts['--limit']) if '--limit' in opts else None
        start = int(opts.get('--start', 0)); chunk = int(opts.get('--chunk', LEAF_TARGET)); workers = int(opts.get('--workers', 1))
    except ValueError:
        print(__doc__); return 2
    if start < 0 or (limit is not None and limit <= 0) or chunk <= 0 or workers <= 0:
        say('invalid leaf options: require start >= 0 and positive limit, chunk and workers')
        return 2
    add_scrub(ROOT, '.'); add_scrub(sys.executable, 'python')
    mode = 'mutate' if '--mutate' in flags else 'quick' if '--quick' in flags else 'leaves' if '--leaves' in flags else 'full'
    say(f'verify.py mode: {mode}' + (f' {opts}' if opts else '') + f'; started {time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}; '
        f'python {sys.version.split()[0]} on {sys.platform}')
    say(f'verify.py sha256 = {sha256_file(os.path.abspath(__file__))}')
    set_below_normal()
    t0 = time.time()
    okA, entries = step_a(ROOT)
    if not okA:
        say('RESULT: FAIL (manifest)'); return 1
    if mode == 'leaves':
        ok = step_leaves(entries, opts.get('--families'), start, limit, chunk, workers)
        say(f'RESULT: {"PASS" if ok else "FAIL"} (leaves), total wall {time.time() - t0:.1f} s'); return 0 if ok else 1
    if mode == 'mutate':
        ok = step_mutate(entries)
        say(f'RESULT: {"PASS" if ok else "FAIL"} (mutate), wall {time.time() - t0:.1f} s'); return 0 if ok else 1
    okB, Rb = step_b(entries, quick=(mode == 'quick'))
    okC, Rc = step_c()
    okD = step_d(Rb, Rc) if (okB and okC) else False
    ok = okB and okC and okD
    if mode == 'quick':
        say('QUICK MODE did not check that each leaves_<i>.json.gz is a complete binary prefix code (Kraft). '
            'Full and quick modes do not recompute per-leaf exact bounds; --leaves does.')
    say(f'RESULT: {"PASS" if ok else "FAIL"} ({mode}), total wall {time.time() - t0:.1f} s')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
