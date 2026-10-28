"""Workspace-only execution, priority, durable logs, and input identities."""
import os
for key in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS', 'NUMEXPR_NUM_THREADS', 'NUMBA_NUM_THREADS'):
    os.environ[key] = '1'
os.environ['PYTHONDONTWRITEBYTECODE'] = '1'
os.environ['NUMBA_CACHE_DIR'] = str(__import__('pathlib').Path(__file__).resolve().parent / 'numba_cache')
import ctypes, datetime, hashlib, json, pathlib, sys, time
OUT = pathlib.Path(__file__).resolve().parent
ROOT = OUT.parent
if os.name == 'nt':
    kernel = ctypes.windll.kernel32
    kernel.GetCurrentProcess.restype = ctypes.c_void_p
    kernel.SetPriorityClass.argtypes = [ctypes.c_void_p, ctypes.c_uint32]
    kernel.GetPriorityClass.argtypes = [ctypes.c_void_p]
    kernel.GetPriorityClass.restype = ctypes.c_uint32
    handle = kernel.GetCurrentProcess()
    if not kernel.SetPriorityClass(handle, 0x4000) or kernel.GetPriorityClass(handle) != 0x4000:
        raise RuntimeError('BelowNormal priority not verified')
sys.path.insert(0, str(OUT / 'baseline'))
def log(message):
    line = datetime.datetime.now(datetime.timezone.utc).isoformat() + ' ' + str(message)
    with (ROOT / 'PROGRESS.log').open('a', encoding='utf-8') as f:
        f.write(line + '\n')
    print(line, flush=True)
def save(name, obj):
    path = OUT / name
    tmp = path.with_suffix(path.suffix + '.tmp')
    tmp.write_text(json.dumps(obj, indent=2, allow_nan=False), encoding='utf-8')
    tmp.replace(path)
def checkpoint(state, completed, next_step):
    (ROOT / 'CHECKPOINT.md').write_text(
        '# Checkpoint\n\nFirst start UTC: 2026-10-26T12:09:00Z\nMinimum finish UTC: 2026-10-26T14:39:00Z\n'
        '\nUpdated UTC: ' + datetime.datetime.now(datetime.timezone.utc).isoformat() +
        '\n\nState: ' + state + '\n\nCompleted: ' + completed + '\n\nNext: ' + next_step +
        '\n\nAll writes are inside D:\\std-val\\PACK-BOUND. Python workers verify BelowNormal priority; numerical threads capped at one. At most two heavy processes.\n', encoding='utf-8')
def hashes(paths):
    return {str(pathlib.Path(p).relative_to(ROOT)): hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest() for p in paths}

