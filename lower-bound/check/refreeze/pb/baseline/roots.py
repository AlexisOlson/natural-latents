"""Symmetry roots of the fibre cover (s = 0 laws; p(x,y) = g((x-y) mod n), g even).
Group used: diagonal translations (x,y)->(x+a,y+a) and transposition (x,y)->(y,x); both preserve p, c(U) and
orbit-constant prices.  Distance of a cell: min(k, n-k), k = (x-y) mod n.
Claim: every nonempty U has an image under the group in exactly one of the families below (at least one suffices).
  Let d = min distance of cells of U.  After a transposition if needed, U has a cell on the line
  Ld = {(t, t+d mod n)} (x - y = -d).  [d = 0: the diagonal; d = n/2: both offsets coincide.]
  * If U contains all n cells of Ld: family (d, ALL): Ld on, all cells of distance < d off.
  * Else U cap Ld is a nonempty proper subset of the cycle Ld; take a maximal cyclic run t0..t0+L-1 (1 <= L <= n-1)
    with t0-1, t0+L not in U, and translate by -t0: family (d, L): cells (t,t+d), t = 0..L-1 on; (L, L+d) and
    (n-1, n-1+d) off (they coincide when L = n-1); all cells of distance < d off.
"""
import numpy as np


def cell(n, x, y):
    return (x % n) * n + (y % n)


def roots_for(n):
    x = np.repeat(np.arange(n), n); y = np.tile(np.arange(n), n)
    k = (x - y) % n
    DIST = np.minimum(k, (n - k) % n)
    out = []
    for d in range(DIST.max(), -1, -1):
        base_off = set(np.nonzero(DIST < d)[0].tolist())
        line = [cell(n, t, t + d) for t in range(n)]
        out.append((f'd{d}_ALL', sorted(line), sorted(base_off)))
        for L in range(1, n):
            on = line[:L]
            off = set(base_off) | {line[L % n], line[n - 1]}
            assert not (set(on) & off)
            out.append((f'd{d}_L{L}', sorted(on), sorted(off)))
    return out


if __name__ == '__main__':
    import sys
    n = int(sys.argv[1])
    r = roots_for(n)
    print(len(r), 'roots;', r[-3][0], r[-3][1][:5], r[-3][2][:5])


# ---- longest-run refinement --------------------------------------------------------------------------------------
# Choosing a LONGEST maximal run in the claim above, family (d, L) may additionally require: every cyclic run of
# U cap Ld has length <= L.  So inside family (d, L) a node is vacuous if its forced-on cells of Ld contain a run
# longer than L, and a free cell of Ld must be off if switching it on would join forced-on cells into a run > L.

def propagate(on, off, line, L):
    """Returns (vacuous, off2).  on/off: boolean arrays over cells; line: list of the n cells of Ld in cyclic order."""
    n = len(line)
    if L >= n:
        return False, off
    ons = np.array([on[z] for z in line])
    if ons.all():
        return True, off
    # longest cyclic run of forced-on cells
    def runs_through(arr):
        m = len(arr)
        left = np.zeros(m, dtype=int); right = np.zeros(m, dtype=int)
        # cyclic: unroll twice
        a2 = np.concatenate([arr, arr])
        c = 0; lr = np.zeros(2 * m, dtype=int)
        for i in range(2 * m):
            c = c + 1 if a2[i] else 0
            lr[i] = c
        for i in range(m):
            left[i] = min(lr[i + m], m)
        c = 0; rr = np.zeros(2 * m, dtype=int)
        for i in range(2 * m - 1, -1, -1):
            c = c + 1 if a2[i] else 0
            rr[i] = c
        for i in range(m):
            right[i] = min(rr[i], m)
        return left, right
    left, right = runs_through(ons)
    if (left.max() if len(left) else 0) > L:
        return True, off
    off2 = off.copy()
    for t in range(n):
        z = line[t]
        if not on[z] and not off[z]:
            lt = left[(t - 1) % n]; rt = right[(t + 1) % n]
            if lt + 1 + rt > L:
                off2[z] = True
    return False, off2


def roots_for_lr(n):
    """Same families as roots_for, with the line and L carried for the longest-run refinement."""
    x = np.repeat(np.arange(n), n); y = np.tile(np.arange(n), n)
    k = (x - y) % n
    DIST = np.minimum(k, (n - k) % n)
    out = []
    for d in range(DIST.max(), -1, -1):
        base_off = set(np.nonzero(DIST < d)[0].tolist())
        line = [cell(n, t, t + d) for t in range(n)]
        out.append((f'd{d}_ALL', sorted(line), sorted(base_off), line, n))
        for L in range(1, n):
            on = line[:L]
            off = set(base_off) | {line[L % n], line[n - 1]}
            out.append((f'd{d}_L{L}', sorted(on), sorted(off), line, L))
    return out


# ---- gap refinement of the L = 1 families ---------------------------------------------------------------------
# In family (d, 1) every run of U cap Ld is a single cell.  Choose, among its points, one followed by a LONGEST gap
# G (maximal stretch of non-members): family (d, 1, G): cell 0 on, cells 1..G off, cell G+1 on if G+1 <= n-1
# (G = n-1: U cap Ld = {cell 0}), cell n-1 off; and every gap of U cap Ld has length <= G.
# Propagation adds: a stretch of forced-off cells longer than G is vacuous; a free cell whose forced-off
# neighbourhood would make a gap > G must be on (and its two neighbours off, runs <= 1).

def propagate2(on, off, line, L, G):
    """Like propagate, plus the gap rule when G is not None.  Returns (vacuous, on2, off2)."""
    vac, off2 = propagate(on, off, line, L)
    if vac or G is None:
        return vac, on, off2
    n = len(line)
    on2 = on.copy()
    changed = True
    while changed:
        changed = False
        ons = np.array([on2[z] for z in line]); offs = np.array([off2[z] for z in line])
        if (ons & offs).any():
            return True, on2, off2
        # forced-off stretch lengths ending at / starting at each index (cyclic, ons exist so stretches are finite)
        a2 = np.concatenate([offs, offs])
        lr = np.zeros(2 * n, dtype=int); c = 0
        for i in range(2 * n):
            c = c + 1 if a2[i] else 0
            lr[i] = c
        rr = np.zeros(2 * n, dtype=int); c = 0
        for i in range(2 * n - 1, -1, -1):
            c = c + 1 if a2[i] else 0
            rr[i] = c
        left = np.minimum(lr[n:], n); right = np.minimum(rr[:n], n)
        if left.max() > G:
            return True, on2, off2
        for t in range(n):
            z = line[t]
            if not on2[z] and not off2[z]:
                lo = left[(t - 1) % n]; ro = right[(t + 1) % n]
                if lo + 1 + ro > G:
                    if on2[line[(t - 1) % n]] or on2[line[(t + 1) % n]]:
                        return True, on2, off2
                    on2[z] = True
                    for nb in (line[(t - 1) % n], line[(t + 1) % n]):
                        if not off2[nb]:
                            off2[nb] = True
                    changed = True
                    break
    return False, on2, off2


def roots_for_gap(n):
    """Families of roots_for_lr with (d, 1) replaced by (d, 1, G), G = 1..n-1.  Entries: (name, on, off, line, L, G)."""
    out = []
    for (name, on, off, line, L) in roots_for_lr(n):
        if L != 1:
            out.append((name, on, off, line, L, None))
            continue
        for G in range(1, n):
            on_ = {line[0]}
            off_ = set(off) | {line[t] for t in range(1, G + 1)} | {line[n - 1]}
            if G + 1 <= n - 1:
                if line[G + 1] in off_:
                    continue          # G + 1 = n - 1 clashes with the forced-off cell n-1: empty family
                on_.add(line[G + 1])
            out.append((f'{name}_G{G}', sorted(on_), sorted(off_), line, 1, G))
    return out

