from sage.all import *
from time import perf_counter

from cert_bloch import certify_maxeig_below

# cert_near_0.py
#
# Lemma lem:h1:core:cert (i): inequality (eqn:core:lmi:psd) on (0, 13/40] for
# T = L_{1,theta}^{fib Sigma} (Lemma lem:rescaled:fiber), core m = 8, r = 11/10,
# gamma = (1/2)(1 + 1/m^2) (Lemma lem:tm:tail:hom).
#
# Homogeneous weight |k+alpha|^s with mode 0 rescaled; the four entries touching
# mode 0 are given in closed form (_hatA_closed_exact).  The block matrix
#   [[2r(I+X) - Ac^T(I+X) - (I+X)Ac, M01], [M01^T, 2(r - gamma) I_2]]
# is built exactly over Frac(QQ[al]) and only then evaluated at the alpha-ball.
# The certificate uses X = 0 and s = 1 (run_h1_metrics.py).  The s = 2 path,
# certify_B_bounds and solve_robust_X (cvxpy) are not used by main.tex.

DEFAULT_BITS = 200
DEFAULT_M = 8


def _sgn_fixed(k):
    """Sign of k + alpha for integer k != 0 and alpha in [0, 1)."""
    return 1 if k > 0 else -1


def _raw_AB_exact(k, al):
    """Unweighted A_{k,alpha}, B_{k,alpha}, k != 0, in QQ(al)."""
    ka = k + al
    sg = _sgn_fixed(k)
    A = (ka + 1) * (ka - sg) / (2 * ka)
    B = -(ka - 1) * (ka - sg) / (2 * ka)
    return A, B


def _w_homog_exact(k, al, s):
    """|k+alpha|^s in QQ(al), k != 0."""
    ka = k + al
    sg = 1 if k > 0 else -1
    return (sg * ka) ** s


def _hatA_closed_exact(k_row, k_col, al, s):
    """The four rescaled entries touching mode 0, in QQ(al)."""
    if (k_row, k_col) == (-1, 0):
        return -(1 - al) ** (s + 1) * (1 + al) / 2
    if (k_row, k_col) == (1, 0):
        return -(1 + al) ** s * (1 - al) ** 2 / 2
    if (k_row, k_col) == (0, 1):
        return (2 + al) / (2 * (1 + al) ** (s + 1))
    if (k_row, k_col) == (0, -1):
        return -(2 - al) / (2 * (1 - al) ** (s + 1))
    raise ValueError("not one of the four mode-0 entries")


def _raw_entry_exact(row, col, al, s):
    """Entry (row, col), |row - col| = 1, away from mode 0, homogeneous weight, exact."""
    if row == col - 1:
        k = col
        A, _ = _raw_AB_exact(k, al)
        return A * _w_homog_exact(k - 1, al, s) / _w_homog_exact(k, al, s)
    if row == col + 1:
        k = col
        _, B = _raw_AB_exact(k, al)
        return B * _w_homog_exact(k + 1, al, s) / _w_homog_exact(k, al, s)
    raise ValueError("row, col not adjacent")


def core_matrix_exact(m, s, al):
    """Core block (modes -m..m) of the rescaled operator, tridiagonal, in QQ(al)."""
    kv = list(range(-m, m + 1))
    n = len(kv)
    idx = {k: i for i, k in enumerate(kv)}
    FF = al.parent()
    M = matrix(FF, n, n)
    for k in range(-m, m):
        row, col = k, k + 1
        if (row, col) == (-1, 0) or (row, col) == (0, 1):
            M[idx[row], idx[col]] = _hatA_closed_exact(row, col, al, s)
        else:
            M[idx[row], idx[col]] = _raw_entry_exact(row, col, al, s)
        crow, ccol = col, row
        if (crow, ccol) == (0, -1) or (crow, ccol) == (1, 0):
            M[idx[crow], idx[ccol]] = _hatA_closed_exact(crow, ccol, al, s)
        else:
            M[idx[crow], idx[ccol]] = _raw_entry_exact(crow, ccol, al, s)
    return M, idx


def interface_entries_exact(m, s, al):
    """
    Core/boundary entries (M[m+1,m], M[m,m+1], M[-(m+1),-m], M[-m,-(m+1)]),
    in QQ(al).
    """
    M_mp1_m       = _raw_entry_exact(m + 1, m, al, s)
    M_m_mp1       = _raw_entry_exact(m, m + 1, al, s)
    M_negmp1_negm = _raw_entry_exact(-(m + 1), -m, al, s)
    M_negm_negmp1 = _raw_entry_exact(-m, -(m + 1), al, s)
    return M_mp1_m, M_m_mp1, M_negmp1_negm, M_negm_negmp1


def gamma_tail(s, N0):
    """gamma: (1/2)(1 + 1/N0^2) for s=1 (Lemma lem:tm:tail:hom); 1/2 for s=2."""
    if s == 2:
        return QQ(1) / 2
    return QQ(1) / 2 * (1 + QQ(1) / N0 ** 2)


def _eval_at_ball(expr, alpha_ball, RB):
    """Evaluate an element of QQ(al) (or QQ) at a ball: numerator / denominator."""
    if expr in QQ:
        return RB(QQ(expr))
    num = expr.numerator()
    den = expr.denominator()
    return num(alpha_ball) / den(alpha_ball)


def _matrix_at_ball(M_exact, alpha_ball, RB):
    n, k = M_exact.nrows(), M_exact.ncols()
    return matrix(RB, n, k, lambda i, j: _eval_at_ball(M_exact[i, j], alpha_ball, RB))


def certify_near_0_lmi(alpha_lo, alpha_hi, X, r, s, m=DEFAULT_M, bits=DEFAULT_BITS,
                     verbose=False):
    """
    Certify [[M00(X), M01(X)], [M01(X)^T, tau I]] >= 0 for all alpha in
    [alpha_lo, alpha_hi], X a fixed symmetric (2m+1)x(2m+1) matrix,
    tau = 2(r - gamma_tail(s, m)).  Returns (ok, min_pivot).
    """
    t0 = perf_counter()
    RB = RealBallField(bits)
    lo, hi = QQ(alpha_lo), QQ(alpha_hi)
    mid, rad = (lo + hi) / 2, (hi - lo) / 2
    alpha_ball = RB(mid).add_error(RB(rad))
    n = 2 * m + 1

    R = PolynomialRing(QQ, 'al')
    FF = R.fraction_field()
    al = FF(R.gen())
    r = QQ(r)
    Xq = matrix(QQ, n, n, lambda i, j: QQ(float(X[i][j])))
    Xq = (Xq + Xq.transpose()) / 2

    Ac, idx = core_matrix_exact(m, s, al)
    I = identity_matrix(FF, n)
    Btil = I + Xq.change_ring(FF)
    M00 = FF(2 * r) * Btil - Ac.transpose() * Btil - Btil * Ac

    tau = 2 * (r - gamma_tail(s, m))
    if not (tau > 0):
        raise RuntimeError("tau <= 0: core m=%d too small for r=%s (raise m)" % (m, r))

    # M01 = -(A^T Btil + Btil A) on (core) x (modes m+1, -(m+1)).  For X = 0
    # only the rows m and -m are nonzero.
    Mmp1_m, Mm_mp1, Mnegmp1_negm, Mnegm_negmp1 = interface_entries_exact(m, s, al)
    M01 = matrix(FF, n, 2)
    for k in range(n):
        M01[k, 0] = -Btil[k, idx[m]] * Mm_mp1
        M01[k, 1] = -Btil[k, idx[-m]] * Mnegm_negmp1
    M01[idx[m], 0] -= Mmp1_m
    M01[idx[-m], 1] -= Mnegmp1_negm

    M00_ball = _matrix_at_ball(M00, alpha_ball, RB)
    M01_ball = _matrix_at_ball(M01, alpha_ball, RB)
    full = block_matrix(RB, [[M00_ball, M01_ball],
                            [M01_ball.transpose(), RB(tau) * identity_matrix(RB, 2)]],
                        subdivide=False)
    full = (full + full.transpose()) / 2
    ok, piv = certify_maxeig_below(-full, RB(0), RB)
    dt = perf_counter() - t0
    if verbose:
        print("  [near_0 LMI] alpha=[%s +/- %s] s=%d r=%.4f m=%d : %s (min pivot >= %s)  [%.1fs]"
              % (lo, rad, s, float(r), m, "PASS" if ok else "FAIL", piv, dt))
    return ok, piv


def _float_core(al, m, s):
    """Float version of core_matrix_exact and interface_entries_exact, for solve_robust_X."""
    import numpy as np

    def raw_AB(k, al):
        ka = k + al
        sg = 1.0 if k > 0 else -1.0
        A = (ka + 1) * (ka - sg) / (2 * ka)
        B = -(ka - 1) * (ka - sg) / (2 * ka)
        return A, B

    def w(k, al, s):
        return abs(k + al) ** s

    def hatA_closed(kr, kc, al, s):
        if (kr, kc) == (-1, 0):
            return -(1 - al) ** (s + 1) * (1 + al) / 2
        if (kr, kc) == (1, 0):
            return -(1 + al) ** s * (1 - al) ** 2 / 2
        if (kr, kc) == (0, 1):
            return (2 + al) / (2 * (1 + al) ** (s + 1))
        if (kr, kc) == (0, -1):
            return -(2 - al) / (2 * (1 - al) ** (s + 1))
        raise ValueError

    def raw_entry(row, col, al, s):
        if row == col - 1:
            A, _ = raw_AB(col, al)
            return A * w(col - 1, al, s) / w(col, al, s)
        A, B = raw_AB(col, al)
        return B * w(col + 1, al, s) / w(col, al, s)

    kv = list(range(-m, m + 1))
    n = len(kv)
    idx = {k: i for i, k in enumerate(kv)}
    M = np.zeros((n, n))
    for k in range(-m, m):
        row, col = k, k + 1
        M[idx[row], idx[col]] = (hatA_closed(row, col, al, s) if (row, col) in
                                 [(-1, 0), (0, 1)] else raw_entry(row, col, al, s))
        crow, ccol = col, row
        M[idx[crow], idx[ccol]] = (hatA_closed(crow, ccol, al, s) if (crow, ccol) in
                                   [(0, -1), (1, 0)] else raw_entry(crow, ccol, al, s))
    # Interface entries, as in interface_entries_exact.
    M_mp1_m       = raw_entry(m + 1, m, al, s)
    M_m_mp1       = raw_entry(m, m + 1, al, s)
    M_negmp1_negm = raw_entry(-(m + 1), -m, al, s)
    M_negm_negmp1 = raw_entry(-m, -(m + 1), al, s)
    return M, idx, M_mp1_m, M_m_mp1, M_negmp1_negm, M_negm_negmp1


def certify_B_bounds(X, bits=200, gran=QQ(1) / 10**6, verbose=False):
    """
    Rational c1, c2 > 0 with c1 I <= I+X <= c2 I, certified with
    certify_maxeig_below.  Not used by main.tex.
    """
    RB = RealBallField(bits)
    n = X.nrows() if hasattr(X, "nrows") else len(X)
    Xq = matrix(QQ, n, n, lambda i, j: QQ(float(X[i][j])))
    Xq = (Xq + Xq.transpose()) / 2
    IpX = identity_matrix(QQ, n) + Xq
    IpX_ball = matrix(RB, n, n, lambda i, j: RB(IpX[i, j]))

    # float estimate to pick candidate rationals, then certify rigorously
    IpX_float = matrix(RDF, n, n, lambda i, j: float(IpX[i, j]))
    evs = [e.real() for e in IpX_float.eigenvalues()]
    lo_f, hi_f = min(evs), max(evs)

    c2 = (QQ(hi_f) / gran).floor() * gran + gran
    ok2, piv2 = certify_maxeig_below(IpX_ball, RB(c2), RB)
    if not ok2:
        raise RuntimeError("c_2 upper bound NOT certified (min pivot %s); "
                           "raise bits or gran" % piv2)

    c1 = (QQ(lo_f) / gran).floor() * gran - gran  # STRICTLY below the true min
    ok1, piv1 = certify_maxeig_below(-IpX_ball, RB(-c1), RB)
    if not ok1:
        raise RuntimeError("c_1 lower bound NOT certified (min pivot %s); "
                           "raise bits or gran" % piv1)
    if not (c1 > 0):
        raise RuntimeError("I+X is not certified positive definite (c_1=%s <= 0); "
                           "the rescaled metric requires c_1>0" % c1)
    if verbose:
        print("  [B bounds] c_1=%s (~%.6f)  c_2=%s (~%.6f)  ratio c_2/c_1=%.4f"
              % (c1, float(c1), c2, float(c2), float(c2 / c1)))
    return c1, c2


def solve_robust_X(m, s, r, sample_pts, eps=1e-2, verbose=False):
    """
    Floating-point candidate X (cvxpy/SCS) satisfying the block LMI with margin
    eps at every alpha in sample_pts.  Not part of the certificate.
    """
    import numpy as np
    import cvxpy as cp

    n = 2 * m + 1
    X = cp.Variable((n, n), symmetric=True)
    gamma_m = float(gamma_tail(s, m))
    tau = 2 * (r - gamma_m)
    constraints = []
    for al in sample_pts:
        Ac, idx, Mmp1_m, Mm_mp1, Mnegmp1_negm, Mnegm_negmp1 = _float_core(al, m, s)
        Btil = np.eye(n) + X
        M00 = 2 * r * Btil - Ac.T @ Btil - Btil @ Ac
        # M01 as in certify_near_0_lmi.
        M01 = [[0] * 2 for _ in range(n)]
        for k in range(n):
            M01[k][0] = -Btil[k, idx[m]] * Mm_mp1
            M01[k][1] = -Btil[k, idx[-m]] * Mnegm_negmp1
        M01[idx[m]][0] = M01[idx[m]][0] - Mmp1_m
        M01[idx[-m]][1] = M01[idx[-m]][1] - Mnegmp1_negm
        M01 = cp.bmat(M01)
        full = cp.bmat([[M00, M01], [M01.T, tau * np.eye(2)]])
        constraints.append(full >> eps * np.eye(n + 2))
    prob = cp.Problem(cp.Minimize(cp.norm(X, "fro")), constraints)
    prob.solve(solver=cp.SCS, verbose=verbose)
    if prob.status not in ("optimal", "optimal_inaccurate"):
        raise RuntimeError("robust SDP infeasible/failed (status=%s) at m=%d, s=%d, "
                           "r=%s, eps=%s" % (prob.status, m, s, r, eps))
    return X.value


def cover_near_0_region(X, r, s, a=QQ(30) / 100, m=DEFAULT_M, bits=DEFAULT_BITS,
                     min_width=QQ(1) / 2 ** 24, max_pieces=2 ** 20, verbose=True):
    """
    certify_near_0_lmi on [0, a] by adaptive bisection (run_h1_metrics.py:
    X = 0, r = 11/10, s = 1, a = 13/40, m = 8).  Returns True or raises.
    """
    from collections import deque

    a = QQ(a)
    t0 = perf_counter()
    print("cover_near_0_region: s=%d r=%.4f m=%d, adaptive bisection of (0,%s]"
          % (s, float(r), m, a))
    work = deque([(QQ(0), a, 0)])
    accepted, covered, finest, step = 0, QQ(0), 0, 0
    while work:
        step += 1
        lo, hi, depth = work.pop()
        width = hi - lo
        if width < min_width:
            raise RuntimeError("near_0 piece [%s,%s] too narrow; the "
                               "margin does not survive interval evaluation here "
                               "at all -- re-solve X (larger core m, or a locally "
                               "tighter robust SDP near this alpha)" % (lo, hi))
        finest = max(finest, depth)
        ok, piv = certify_near_0_lmi(lo, hi, X, r, s, m=m, bits=bits, verbose=False)
        if ok:
            accepted += 1
            covered += width
            status = "accept"
        else:
            mid = (lo + hi) / 2
            work.append((lo, mid, depth + 1))
            work.append((mid, hi, depth + 1))
            status = "FAIL -> split"
        if accepted + len(work) > max_pieces:
            raise RuntimeError("too many pieces for near_0 region (> %d)" % max_pieces)
        if verbose and step % 200 == 0:
            pct = (100 * covered / a).floor()
            print("    [near_0] cov %3d%% | acc %d pend %d depth %d | [%s, %s] | %s"
                  % (pct, accepted, len(work), depth, lo, hi, status))
    print("cover_near_0_region: certified on (0,%s]  (%d pieces, finest depth %d)  [%.1fs]"
          % (a, accepted, finest, perf_counter() - t0))
    return True
