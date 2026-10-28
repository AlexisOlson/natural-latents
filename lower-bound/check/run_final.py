"""Glue that runs the unmodified check/refreeze/rf/final.py against a staged tree.

usage: python -E -B run_final.py [--no-kraft] OUT_DIR PRICE COVERDIR

OUT_DIR  a directory laid out the way final.py expects (it locates law.json and prices.json as OUT_DIR/pb/..., and its
         modules as OUT_DIR/rf/, OUT_DIR/pb/ and OUT_DIR/pb/baseline/). verify.py builds it from byte copies of data/ and
         check/refreeze/ and checks those copies against MANIFEST.sha256 first.
PRICE    price file, COVERDIR  the cover directory (fam_<i>.json, leaves_<i>.json.gz).

final.py is not edited. It writes cover_summary.json into COVERDIR, which is why verify.py hands it a scratch copy of
data/cover/v4 and never data/ itself.

--no-kraft  replaces cover.kraft (the Kraft-sum check that each leaves_<i>.json.gz is a complete binary prefix code) with
            a no-op before final.py imports it. Everything else in final.py runs unchanged. This is verify.py --quick.

At exit it prints PEAK_WORKING_SET_BYTES and PEAK_PAGEFILE_BYTES for this process to stderr (Windows only).
"""
import os, sys, runpy


def peak_memory():
    if os.name != 'nt':
        return None
    import ctypes
    from ctypes import wintypes

    class PMC(ctypes.Structure):
        _fields_ = [('cb', wintypes.DWORD), ('PageFaultCount', wintypes.DWORD),
                    ('PeakWorkingSetSize', ctypes.c_size_t), ('WorkingSetSize', ctypes.c_size_t),
                    ('QuotaPeakPagedPoolUsage', ctypes.c_size_t), ('QuotaPagedPoolUsage', ctypes.c_size_t),
                    ('QuotaPeakNonPagedPoolUsage', ctypes.c_size_t), ('QuotaNonPagedPoolUsage', ctypes.c_size_t),
                    ('PagefileUsage', ctypes.c_size_t), ('PeakPagefileUsage', ctypes.c_size_t)]
    k32 = ctypes.windll.kernel32
    k32.GetCurrentProcess.restype = ctypes.c_void_p
    psapi = ctypes.windll.psapi
    psapi.GetProcessMemoryInfo.argtypes = [ctypes.c_void_p, ctypes.POINTER(PMC), wintypes.DWORD]
    pmc = PMC(); pmc.cb = ctypes.sizeof(PMC)
    if not psapi.GetProcessMemoryInfo(k32.GetCurrentProcess(), ctypes.byref(pmc), pmc.cb):
        return None
    return pmc.PeakWorkingSetSize, pmc.PeakPagefileUsage


def main():
    args = sys.argv[1:]
    no_kraft = False
    if args and args[0] == '--no-kraft':
        no_kraft = True; args = args[1:]
    out_dir, price, coverdir = args
    out_dir = os.path.abspath(out_dir)
    final = os.path.join(out_dir, 'rf', 'final.py')
    sys.path.insert(0, os.path.join(out_dir, 'rf'))
    if no_kraft:
        import cover
        cover.kraft = lambda leaves: None
        print('run_final: --no-kraft, cover.kraft replaced by a no-op', file=sys.stderr, flush=True)
    sys.argv = [final, price, coverdir]
    try:
        runpy.run_path(final, run_name='__main__')
    finally:
        pk = peak_memory()
        if pk:
            print(f'PEAK_WORKING_SET_BYTES={pk[0]}', file=sys.stderr)
            print(f'PEAK_PAGEFILE_BYTES={pk[1]}', file=sys.stderr, flush=True)


if __name__ == '__main__':
    main()
