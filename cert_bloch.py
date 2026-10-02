from sage.all import *
from time import perf_counter

# cert_bloch.py
#
# Interval LDL^T test certify_maxeig_below, used by cert_near_0.py and
# cert_away_0.py (Lemma lem:h1:core:cert).  The other routines (truncated
# Bloch matrices, certify_A, certify_B, certify_eigenpair, certify_theta) are
# not used by the certificates of main.tex.
#
# Fiber operator, ka = k + alpha:
#   L e^{ikx} = A_{k,a} e^{i(k-1)x} + B_{k,a} e^{i(k+1)x},
#   A_{k,a} = (ka+1)(ka - sgn ka)/(2 ka),  B_{k,a} = -(ka-1)(ka - sgn ka)/(2 ka),
# with weight w_k = sqrt(1+|ka|^{2s}).


def _sgn(x):
    return 1 if x > 0 else -1


def _as_alpha(alpha, RB):
    """
    Returns (alpha_RB, thin, alpha_q): thin=True and alpha_q in QQ for a
    rational alpha; thin=False and alpha_q=None for a RealBall.
    """
    if alpha in QQ:
        q = QQ(alpha)
        return RB(q), True, q
    return RB(alpha), False, None


def _alpha_str(alpha):
    """Compact label for a fiber parameter (rational point or theta-ball)."""
    if alpha in QQ:
        return str(QQ(alpha))
    try:
        return "[%.6f +/- %.1e]" % (float(alpha.mid()), float(alpha.rad()))
    except Exception:
        return str(alpha)


def fiber_kvals(alpha, K):
    """Index set for fiber alpha, excluding the zero mode k+alpha=0."""
    alpha = QQ(alpha)
    return [k for k in range(-K, K + 1) if k + alpha != 0]


def bloch_full_ball(alpha, K, s, RB):
    """
    W_s L_alpha W_s^{-1} on the modes |k| <= K, as a RealBall matrix; alpha is
    a rational or a RealBall.  Raises if k + alpha straddles 0.
    """
    a_RB, thin, a_q = _as_alpha(alpha, RB)
    kv = fiber_kvals(a_q, K) if thin else list(range(-K, K + 1))
    n = len(kv)
    idx = {k: i for i, k in enumerate(kv)}
    w = [(1 + (RB(k) + a_RB).abs() ** (2 * s)).sqrt() for k in kv]

    M = matrix(RB, n, n)
    for c, k in enumerate(kv):
        if thin:
            ka = QQ(k) + a_q
            sg = _sgn(ka)
            A = RB((ka + 1) * (ka - sg) / (2 * ka))    # coeff of e^{i(k-1)x}, exact then enclosed
            B = RB(-(ka - 1) * (ka - sg) / (2 * ka))   # coeff of e^{i(k+1)x}
        else:
            ka = RB(k) + a_RB
            if ka.lower() > 0:
                sg = 1
            elif ka.upper() < 0:
                sg = -1
            else:
                raise ValueError("k+alpha straddles 0 at k=%d over the theta-ball "
                                 "(J left (1/3,1/2)?)" % k)
            A = (ka + 1) * (ka - sg) / (2 * ka)
            B = -(ka - 1) * (ka - sg) / (2 * ka)
        if (k - 1) in idx:
            M[idx[k - 1], c] += A * w[idx[k - 1]] / w[c]
        if (k + 1) in idx:
            M[idx[k + 1], c] += B * w[idx[k + 1]] / w[c]
    return M


def bloch_sym_ball(alpha, K, s, RB):
    """Hermitian part S = sym(W_s L_alpha W_s^{-1}) of the K-truncation."""
    M = bloch_full_ball(alpha, K, s, RB)
    return (M + M.transpose()) / 2


def certify_maxeig_below(S, mu, RB):
    """
    Certify max eig(S) < mu for a symmetric RealBall matrix S: interval LDL^T of
    mu*I - S with every pivot provably > 0.  Returns (ok, min_pivot_lower);
    ok=False if some pivot is not certified positive.
    """
    n = S.nrows()
    A = [[ (RB(mu) - S[i, j]) if i == j else (-S[i, j]) for j in range(n)]
         for i in range(n)]
    L = [[RB(0)] * n for _ in range(n)]
    d = [RB(0)] * n
    min_piv = None
    for j in range(n):
        s = A[j][j]
        for k in range(j):
            s = s - d[k] * L[j][k] ** 2
        # certified positivity of the pivot
        if not (s > 0):
            return False, s.lower()
        d[j] = s
        min_piv = s.lower() if min_piv is None else min(min_piv, s.lower())
        L[j][j] = RB(1)
        for i in range(j + 1, n):
            t = A[i][j]
            for k in range(j):
                t = t - d[k] * L[i][k] * L[j][k]
            L[i][j] = t / d[j]
    return True, min_piv


# -----------------------------------------------------------------------------
# Not used by the certificates of main.tex
# -----------------------------------------------------------------------------

def certify_A(alpha, lam=None, K=240, bits=200, mu_frac=None, verbose=False):
    """max eig(sym(W_1 L_alpha W_1^{-1})) < mu on |k| <= K; mu = 2*lam or mu_frac."""
    t = perf_counter()
    RB = RealBallField(bits)
    if mu_frac is not None:
        mu = QQ(mu_frac)
    elif lam is not None:
        mu = 2 * QQ(lam)
    else:
        raise ValueError("certify_A needs either lam or mu_frac")
    if verbose:
        print("    [Cert A] alpha=%s K=%d bits=%d mu=%.6f : building sym(W_1 L W_1^{-1}) ..."
              % (_alpha_str(alpha), K, bits, float(mu)))
    S = bloch_sym_ball(alpha, K, 1, RB)
    t_build = perf_counter() - t
    ok, piv = certify_maxeig_below(S, mu, RB)
    dt = perf_counter() - t
    if verbose:
        print("    [Cert A] build %.1fs, LDL^T %.1fs (dim %d)"
              % (t_build, dt - t_build, S.nrows()))
    print("  Cert A  alpha=%-12s K=%d  mu=2lam=%.6f : %s  (min pivot >= %s)  [%.1fs]"
          % (_alpha_str(alpha), K, float(mu), "PASS" if ok else "FAIL", piv, dt))
    return ok


# Krawczyk enclosure of a real eigenpair: F(v, mu) = (A v - mu v ; v_j - 1) = 0.

def _approx_eigpair(Amid, lam_target, left=False):
    """Floating eigenpair of Amid (or its transpose) nearest lam_target (real)."""
    M = (Amid.transpose() if left else Amid).change_ring(CDF)
    triples = M.eigenvectors_right()
    lam, vecs, _ = min(triples, key=lambda t: abs(CDF(t[0]) - lam_target))
    v = vector(RDF, [c.real() for c in vecs[0]])
    return RDF(lam.real()), v


def certify_eigenpair(A_ball, lam_target, RB, left=False, r0=1e-9, infl=8):
    """
    Krawczyk-certified real eigenpair (mu, v) of A_ball (or A_ball^T if left),
    near lam_target.  Returns (mu_encl RealBall, v_encl RealBall vector) or
    (None, None) if the inclusion could not be established.
    """
    n = A_ball.nrows()
    Aw = A_ball.transpose() if left else A_ball
    Amid = matrix(RDF, n, n, lambda i, j: RDF(A_ball[i, j].mid()))
    Amid_w = Amid.transpose() if left else Amid

    lam0, v0 = _approx_eigpair(Amid, lam_target, left=left)
    j = max(range(n), key=lambda i: abs(v0[i]))
    v0 = v0 / v0[j]                                    # normalize v0_j = 1

    DFmid = matrix(RDF, n + 1, n + 1)
    DFmid[:n, :n] = Amid_w - lam0 * identity_matrix(RDF, n)
    for i in range(n):
        DFmid[i, n] = -v0[i]
    DFmid[n, j] = 1
    YRB = DFmid.inverse().change_ring(RB)             # approx inverse Jacobian

    v0RB = vector(RB, [RB(v0[i]) for i in range(n)])
    lam0RB = RB(lam0)
    F = vector(RB, list(Aw * v0RB - lam0RB * v0RB) + [v0RB[j] - 1])

    r = RB(r0)
    Inp1 = identity_matrix(RB, n + 1)
    for _ in range(infl):
        Delta = vector(RB, [RB(0).add_error(r.mid()) for _ in range(n + 1)])
        lamX = lam0RB + Delta[n]
        vX = vector(RB, [v0RB[i] + Delta[i] for i in range(n)])
        DFX = matrix(RB, n + 1, n + 1)
        DFX[:n, :n] = Aw - lamX * identity_matrix(RB, n)
        for i in range(n):
            DFX[i, n] = -vX[i]
        DFX[n, j] = RB(1)
        Kx = -YRB * F + (Inp1 - YRB * DFX) * Delta     # K(X) - x_tilde
        if all(Kx[i].abs() < r for i in range(n + 1)):  # K(X) in int(X): certified
            v_encl = vector(RB, [v0RB[i] + Kx[i] for i in range(n)])
            return lam0RB + Kx[n], v_encl
        r = r * 8                                      # epsilon-inflation, retry
    return None, None


def complement_basis(u, RB):
    """Orthonormal basis (n x (n-1) RealBall matrix) of u^perp, by a Householder reflection."""
    n = len(u)
    nrm = sum(u[i] ** 2 for i in range(n)).sqrt()
    s = RB(1) if u[0].mid() >= 0 else RB(-1)
    w = vector(RB, [u[i] for i in range(n)])
    w[0] = w[0] + s * nrm
    wtw = sum(w[i] ** 2 for i in range(n))
    H = identity_matrix(RB, n) - (RB(2) / wtw) * w.column() * w.row()
    return H[:, 1:n]


def certify_B(alpha, lam=None, K=120, bits=200, mu_frac=None, lam_target=None,
              verbose=False):
    """
    max eig(sym(W_2 L_alpha W_2^{-1}) restricted to u^perp) < mu on |k| <= K,
    u the Krawczyk-enclosed left eigenvector near lam_target; mu = lam or mu_frac.
    """
    t = perf_counter()
    RB = RealBallField(bits)
    if mu_frac is not None:
        mu = QQ(mu_frac)
    elif lam is not None:
        mu = QQ(lam)
    else:
        raise ValueError("certify_B needs either lam or mu_frac")
    tgt = QQ(lam_target) if lam_target is not None else (QQ(lam) if lam is not None else mu)

    if verbose:
        print("    [Cert B] alpha=%s K=%d bits=%d mu=%.6f target=%.4f : building W_2 L W_2^{-1} ..."
              % (_alpha_str(alpha), K, bits, float(mu), float(tgt)))
    A = bloch_full_ball(alpha, K, 2, RB)
    S = (A + A.transpose()) / 2
    t_build = perf_counter() - t

    lam_u, u = certify_eigenpair(A, tgt, RB, left=True)
    if u is None:
        print("  Cert B  alpha=%-12s : left eigenvector NOT certified near %.4f "
              "(raise bits/K or refine the approximation)  [%.1fs]"
              % (_alpha_str(alpha), float(tgt), perf_counter() - t))
        return False
    if verbose:
        print("    [Cert B] left eigenpair certified: mu in %s  (Krawczyk %.1fs)"
              % (lam_u, perf_counter() - t - t_build))

    N = complement_basis(u, RB)
    Sc = N.transpose() * S * N
    Sc = (Sc + Sc.transpose()) / 2
    ok, piv = certify_maxeig_below(Sc, mu, RB)
    dt = perf_counter() - t
    if verbose:
        print("    [Cert B] complement dim %d, build %.1fs, total %.1fs"
              % (Sc.nrows(), t_build, dt))
    print("  Cert B  alpha=%-12s K=%d  mu=lam=%.6f : %s  (min pivot >= %s, "
          "left eig mu in %s)  [%.1fs]"
          % (_alpha_str(alpha), K, float(mu), "PASS" if ok else "FAIL", piv, lam_u, dt))
    return ok


def certify_theta(theta, lam, K=120, bits=200, verbose=False):
    """certify_A and certify_B at a rational theta."""
    t = perf_counter()
    print("theta = %s,  lambda = %.6f" % (QQ(theta), float(lam)))
    okA = certify_A(theta, lam, K=K, bits=bits, verbose=verbose)
    okB = certify_B(theta, lam, K=K, bits=bits, verbose=verbose)
    print("  => %s  (total %.1fs)" % ("PASS" if (okA and okB) else "FAILED",
                                       perf_counter() - t))
    return okA and okB
