from sage.all import *
from time import perf_counter

from cert_bloch import certify_maxeig_below

# cert_away_0.py
#
# Lemma lem:h1:core:cert (ii): inequality (eqn:core:lmi:psd) on [13/40, 1/2] for
# T = L_{1,theta}^{fib} (shifted weight sqrt(1+|k+alpha|^2)), core m = 4,
# r = 11/10, gamma = (1/2)(1 + 3/m^2) (Lemma lem:tm:tail), X = 0:
#   [[2r I - Ac^T - Ac, M01], [M01^T, 2(r - gamma) I_2]] >= 0,
# built directly in ball arithmetic and checked with certify_maxeig_below
# (Lemma lem:core:lmi:s1 then gives the inequality on the whole fiber).

DEFAULT_M = 4
DEFAULT_BITS = 200
DEFAULT_OM = QQ(11) / 10
DEFAULT_B = QQ(13) / 40


def gamma_tail_shifted(s, N0):
    """gamma: (1/2)(1 + 3/N0^2) for s=1 (Lemma lem:tm:tail, shifted weight); 1/2 for s=2."""
    N0 = ZZ(N0)
    if N0 < 3:
        raise ValueError("gamma_tail_shifted needs N0 >= 3 (got %s)" % N0)
    if s == 2:
        return QQ(1) / 2
    if s == 1:
        return QQ(1) / 2 * (1 + QQ(3) / N0 ** 2)
    raise ValueError("s must be 1 or 2 (got %s)" % s)


def _alpha_ball(alpha_lo, alpha_hi, RB):
    """[alpha_lo, alpha_hi] as a RealBall; requires 0 < alpha_lo <= alpha_hi <= 1/2."""
    lo, hi = QQ(alpha_lo), QQ(alpha_hi)
    if not lo <= hi:
        raise ValueError("empty interval [%s, %s]" % (lo, hi))
    if not lo > 0:
        raise ValueError("cert_away_0 covers the region away from zero: alpha "
                         "must stay strictly positive (got lo=%s).  Near "
                         "alpha=0 the identity metric degenerates and "
                         "cert_near_0's rescaled homogeneous device is "
                         "the one to use." % lo)
    if not hi <= QQ(1) / 2:
        raise ValueError("alpha must lie in (0, 1/2]; fibers above 1/2 follow "
                         "by the conjugation alpha <-> 1-alpha (Lemma conj) "
                         "(got hi=%s)" % hi)
    mid, rad = (lo + hi) / 2, (hi - lo) / 2
    return RB(mid).add_error(RB(rad))


def _tridiag_entries(al, m, s, RB):
    """
    Entries {(row, col): RealBall} of W_s L_alpha W_s^{-1} on the modes
    -(m+1)..(m+1), shifted weight w_k = sqrt(1 + |k+alpha|^{2s}):
        A[k-1, k] = A_{k,alpha} w_{k-1}/w_k,   A[k+1, k] = B_{k,alpha} w_{k+1}/w_k.
    Raises if k + alpha straddles 0.
    """
    kv = list(range(-m - 1, m + 2))
    w = {k: (1 + (RB(k) + al).abs() ** (2 * s)).sqrt() for k in kv}
    ent = {}
    for k in kv:
        ka = RB(k) + al
        if ka.lower() > 0:
            sg = 1
        elif ka.upper() < 0:
            sg = -1
        else:
            raise ValueError("k+alpha straddles 0 at k=%d over the alpha-ball "
                             "(interval left (0, 1/2]?)" % k)
        A = (ka + 1) * (ka - sg) / (2 * ka)
        B = -(ka - 1) * (ka - sg) / (2 * ka)
        if k - 1 in w:
            ent[(k - 1, k)] = A * w[k - 1] / w[k]
        if k + 1 in w:
            ent[(k + 1, k)] = B * w[k + 1] / w[k]
    return ent


def certify_away_0_lmi(alpha_lo, alpha_hi, r=DEFAULT_OM, m=DEFAULT_M,
                        bits=DEFAULT_BITS, s=1, verbose=False):
    """
    Certify for all alpha in [alpha_lo, alpha_hi]
        [[ M00, M01 ], [ M01^T, tau I ]] >= 0,
        M00 = 2r I - Ac^T - Ac   on the core {|k| <= m},
        M01 = -(A^T + A) on core x {m+1, -(m+1)}  (two nonzero entries),
        tau = 2 (r - gamma_tail_shifted(s, m)).
    Returns (ok, min_pivot); ok=False means the piece must be split.
    The certificate uses s = 1.
    """
    t0 = perf_counter()
    RB = RealBallField(bits)
    m = ZZ(m)
    if m < 3:
        raise ValueError("core half-width m must be >= 3 (got %s): the tail "
                         "bound gamma_tail_shifted needs N0 = m >= 3" % m)
    r = QQ(r)
    gam = gamma_tail_shifted(s, m)
    tau = 2 * (r - gam)
    if not tau > 0:
        raise RuntimeError("tau <= 0: core m=%s too small for r=%s (tail bound "
                           "%s); raise m" % (m, r, gam))

    al = _alpha_ball(alpha_lo, alpha_hi, RB)
    ent = _tridiag_entries(al, m, s, RB)

    core = list(range(-m, m + 1))
    ci = {k: i for i, k in enumerate(core)}
    n = len(core)

    Ac = matrix(RB, n, n)
    for k in core:
        for kk in (k - 1, k + 1):
            if -m <= kk <= m:
                Ac[ci[kk], ci[k]] = ent[(kk, k)]

    M00 = RB(2 * r) * identity_matrix(RB, n) - Ac.transpose() - Ac

    # Coupling core <-> boundary modes m+1 and -(m+1).
    M01 = matrix(RB, n, 2)
    M01[ci[m], 0] = -ent[(m + 1, m)] - ent[(m, m + 1)]
    M01[ci[-m], 1] = -ent[(-m - 1, -m)] - ent[(-m, -m - 1)]

    full = block_matrix(RB, [[M00, M01],
                             [M01.transpose(), RB(tau) * identity_matrix(RB, 2)]],
                        subdivide=False)
    full = (full + full.transpose()) / 2

    ok, piv = certify_maxeig_below(-full, RB(0), RB)
    dt = perf_counter() - t0
    if verbose:
        lo, hi = QQ(alpha_lo), QQ(alpha_hi)
        print("  [away_0 H1 LMI] alpha=[%s, %s] s=%d r=%s m=%s tau=%s : %s "
              "(min pivot >= %s)  [%.2fs]"
              % (lo, hi, s, r, m, tau, "PASS" if ok else "FAIL", piv, dt))
    return ok, piv


# -----------------------------------------------------------------------------
# Adaptive covering
# -----------------------------------------------------------------------------


def cover_away_0_region(lo=DEFAULT_B, hi=QQ(1) / 2, r=DEFAULT_OM, m=DEFAULT_M,
                  bits=DEFAULT_BITS, s=1, min_width=QQ(1) / 2 ** 20,
                  max_pieces=2 ** 14, verbose=True):
    """
    certify_away_0_lmi on [lo, hi] by adaptive bisection.  Returns True once
    the accepted pieces tile [lo, hi]; raises below min_width.
    """
    lo, hi = QQ(lo), QQ(hi)
    accepted, pending = [], [(lo, hi)]
    t0 = perf_counter()
    if verbose:
        print("cover_away_0_region: s=%d r=%s m=%s, fresh adaptive bisection of [%s, %s]"
              % (s, QQ(r), m, lo, hi))
    evals = 0
    while pending:
        a_i, b_i = pending.pop()
        width = b_i - a_i
        if width < min_width:
            raise RuntimeError(
                "cover_away_0_region piece [%s, %s] too narrow (< %s): the identity "
                "metric is not admissible at r=%s here.  The plain shifted "
                "H^1 Hermitian part crosses r=11/10 at alpha ~ 0.3208, so a "
                "left endpoint at or below that cannot close -- use "
                "cert_near_0.cover_near_0_region on that part instead."
                % (a_i, b_i, min_width, QQ(r)))
        evals += 1
        ok, piv = certify_away_0_lmi(a_i, b_i, r=r, m=m, bits=bits, s=s,
                                      verbose=False)
        if ok:
            accepted.append((a_i, b_i))
            status = "accept"
        else:
            mid = (a_i + b_i) / 2
            pending.append((a_i, mid))
            pending.append((mid, b_i))
            status = "FAIL -> split"
        if len(accepted) + len(pending) > max_pieces:
            raise RuntimeError("too many pieces for cover_away_0_region (> %d)"
                               % max_pieces)
        if verbose:
            covered = sum((y - x for x, y in accepted), QQ(0))
            print("    [away_0 H1] cov %3d%% | acc %d pend %d | [%s, %s] | %s"
                  % (int(100 * covered / (hi - lo)), len(accepted), len(pending),
                     a_i, b_i, status))

    endpoint = lo
    for a_i, b_i in sorted(accepted):
        if a_i != endpoint or not b_i > a_i:
            raise RuntimeError("cover_away_0_region: accepted pieces do not tile [%s, %s]"
                               % (lo, hi))
        endpoint = b_i
    if endpoint != hi:
        raise RuntimeError("cover_away_0_region: accepted pieces do not tile [%s, %s]"
                           % (lo, hi))
    finest = max((_depth(x, y, lo, hi) for x, y in accepted), default=0)
    print("cover_away_0_region: certified on [%s, %s]  (%d pieces, %d evaluations "
          "this run, finest depth %d, exact tiling)  [%.1fs]"
          % (lo, hi, len(accepted), evals, finest, perf_counter() - t0))
    return True


def _depth(x, y, lo, hi):
    """Bisection depth of the piece [x, y] inside [lo, hi] (width ratio)."""
    w = (hi - lo) / (y - x)
    d = 0
    while w > 1:
        w /= 2
        d += 1
    return d


if __name__ == "__main__":
    print("cert_away_0: thin-point scan, s=1, r=%s, m=%s" % (DEFAULT_OM, DEFAULT_M))
    for a in [QQ(3) / 10, QQ(32) / 100, QQ(13) / 40, QQ(1) / 3, QQ(7) / 20,
              QQ(4) / 11, QQ(2) / 5, QQ(9) / 20, QQ(1) / 2]:
        ok, piv = certify_away_0_lmi(a, a, verbose=False)
        print("   alpha=%-8s %s  (min pivot >= %s)"
              % (a, "PASS" if ok else "FAIL", RealField(30)(piv)))
    print()
    cover_away_0_region(DEFAULT_B, QQ(1) / 2, DEFAULT_OM, verbose=False)
