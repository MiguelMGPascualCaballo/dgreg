from sage.all import *
# local_fuchs.py
#
# SageMath base routines: Frobenius solver, local expansions, matrix constructor,
# and residual computation for the computer-assisted proof.
#
# Everything here is exact over K = Frac(QQ[the, lam]) (or Frac(QQ[the]) when
# lambda is fixed). No ball arithmetic enters this file; that is deferred to
# cert_eval.py.
#
# Main entry points:
#   make_symbolic_context(N, lam_value=None)       -> exact context K[[x]]
#   symbolic_matrix_A(N, lam_value=None)           -> (Mcrit over K, ctx)
#   hom_sol_fro_const / construct_solutions_...     -> local Frobenius solutions


# -----------------------------------------------------------------------------
# Contexts
# -----------------------------------------------------------------------------

def make_symbolic_context(N, lam_value=None, the_value=None, ball=None, bits=200):
    # Working field K and power-series ring R = K[[x]] truncated at order N.
    #
    # ball = (theta_ball, lam_ball): route-A "balls + dual number" context.  theta is
    # an interval enclosing a theta-sub-ball of J, lambda = lam_ball + eps with
    # eps^2 = 0 (a dual number), over K = RealBall[[eps]]/(eps^2).  The recursion is
    # ring-generic (only +,-,*,/ and series ops, no numerator/gcd), so it runs over
    # this ring directly: the eps^1 coefficient of any output is its EXACT
    # d/dlambda enclosed over the whole lambda-interval (eps^2=0 is exact, so there is
    # no Taylor remainder to bound), and the eps^0 coefficient is the value.  Both
    # enclose over the theta-ball.  This is rigorous (interval enclosures) though
    # looser than the exact build; it is the only route that gives d/dlambda det over
    # a (theta,lambda) box without the bivariate-exact blow-up.
    #
    # lam_value=None keeps both theta and lambda symbolic, K = Frac(QQ[the, lam]).
    # Passing a rational lam_value fixes lambda and drops to the univariate field
    # K = Frac(QQ[the]); the Frobenius recursion then runs over univariate
    # fractions, which is markedly cheaper (smaller degrees, univariate gcds).
    # The residuals are independent of lambda only through these coefficients, so
    # fixing it and looping over {56/100, 60/100} costs two cheap passes instead
    # of one expensive bivariate pass.
    #
    # the_value (symmetric to lam_value): fixes THETA to a rational and keeps
    # LAMBDA symbolic, K = Frac(QQ[lam]).  This is the cheap univariate-in-lambda
    # pass used by the simplicity certificate (d/dlambda det at a fixed paper
    # theta), avoiding the bivariate blow-up.
    if ball is not None:
        theta_ball, lam_ball = ball
        RB = RealBallField(bits)
        # dual numbers over balls: RBF[eps]/(eps^2).  Use a QUOTIENT ring (not a
        # PowerSeriesRing): PSR over the field RBF lands in a class lacking
        # _pseudo_fraction_field, which Sage calls when an inexact division is not
        # recognized as exact (balls cannot confirm is_unit).  The quotient ring is
        # not a field, so the outer R = PSR(K,'x') is the generic class that has it.
        Bp = PolynomialRing(RB, names=("eps",))
        (epsp,) = Bp.gens()
        K = Bp.quotient(epsp**2, names=("eps",))
        eps = K.gen()
        B = K
        the_K, lam_K = K(RB(theta_ball)), K(RB(lam_ball)) + eps
    elif the_value is not None:
        B = PolynomialRing(QQ, names=("lam",))
        (lam,) = B.gens()
        K = FractionField(B)
        the_K, lam_K = K(QQ(the_value)), K(lam)
    elif lam_value is None:
        B = PolynomialRing(QQ, names=("the", "lam"))
        the, lam = B.gens()
        K = FractionField(B)
        the_K, lam_K = K(the), K(lam)
    else:
        B = PolynomialRing(QQ, names=("the",))
        (the,) = B.gens()
        K = FractionField(B)
        the_K, lam_K = K(the), K(QQ(lam_value))
    R = PowerSeriesRing(K, name="x", default_prec=N + 1)
    x = R.gen()
    return {
        "N": N,
        "B": B,
        "K": K,
        "R": R,
        "x": x,
        "the": the_K,
        "lam": lam_K,
        "lam_fixed": lam_value is not None,
        "the_fixed": the_value is not None,
        "ball": ball is not None,
    }



# -----------------------------------------------------------------------------
# Parameter matrices
# -----------------------------------------------------------------------------

def default_parameter_matrices(ctx):
    K = ctx["K"]       # Below, t denotes the and l lambda
    # Partial-fraction data of the operator of def:PQtl, in the PHYSICAL +lambda
    # convention: specialize_terms is called directly at lambda (no reflection).
    pp = matrix(K, [
    #     1   l   t
        [ 1,  0,  2],       # 1/z
        [-1,  1,  0],       # 1/(z-1)
        [-1, -1,  0],       # 1/(z+1)
    ])
    qq = matrix(K, [
    #     1   t t*l t^2
        [ 0,  0, -2,  0],   # 1/z
        [-1,  0,  0,  1],   # 1/z^2
        [ 1, -1,  1,  0],   # 1/(z-1)
        [-1,  1,  1,  0],   # 1/(z+1)
    ])
    # 1/z 1/z^2 1/(z-1) 1/(z+1) and 1 t t^2
    a1 = matrix(K, [[ 2], [ 0], [-1], [-1]]) \
        * matrix(K, [[0, 2, -1]]) * K(QQ(1)/QQ(2))
    a2 = matrix(K, [[ 0], [ 2], [-1], [ 1]]) \
        * matrix(K, [[1, 0, -1]]) * K(QQ(1)/QQ(2))
    return pp, qq, a1, a2


def specialize_terms(pp, qq, a1, a2, the, lam):
    K = parent(the)
    v_pp = vector(K, [1, lam, the])
    v_qq = vector(K, [1, the, lam * the, the**2])
    v_aa  = vector(K, [1, the, the**2])
    return pp * v_pp, qq * v_qq, a1 * v_aa, a2 * v_aa


# -----------------------------------------------------------------------------
# Formal local expansions
# -----------------------------------------------------------------------------

def trunc_series_from_expr(R, expr):
    return R(expr)


def coeffs(series, N):
    return [series[kk] for kk in range(N + 1)]


def local_coeffs_at_p1(ctx, term_pp, term_qq, term_a1, term_a2):
    R, x, N = ctx["R"], ctx["x"], ctx["N"]
    z = 1 + x

    # term_pp: [coeff_1/z, coeff_1/(z-1), coeff_1/(z+1)]
    # term_qq / term_a1 / term_a2: [coeff_1/z, coeff_1/z^2, coeff_1/(z-1), coeff_1/(z+1)]
    # Singular point z=+1: the local variable is (z-1)=x, so 1/(z-1) is the leading
    # (indicial) term; 1/z and 1/(z+1) are analytic here.  Mirror of local_coeffs_at_m1
    # under z -> -z (swap the roles of (z-1) and (z+1)).
    P = term_pp[1] + x * (term_pp[0] / z + term_pp[2] / (z + 1))
    Q = term_qq[2] * x + x**2 * (
        term_qq[0] / z + term_qq[1] / (z**2) + term_qq[3] / (z + 1)
    )
    A1 = term_a1[2] * x + x**2 * (
        term_a1[0] / z + term_a1[1] / (z**2) + term_a1[3] / (z + 1)
    )
    A2 = term_a2[2] * x + x**2 * (
        term_a2[0] / z + term_a2[1] / (z**2) + term_a2[3] / (z + 1)
    )

    P  = trunc_series_from_expr(R, P)
    Q  = trunc_series_from_expr(R, Q)
    A1 = trunc_series_from_expr(R, A1)
    A2 = trunc_series_from_expr(R, A2)
    return coeffs(P, N), coeffs(Q, N), coeffs(A1, N), coeffs(A2, N)


def local_coeffs_at_0p(ctx, term_pp, term_qq, term_a1, term_a2):
    R, x, N = ctx["R"], ctx["x"], ctx["N"]
    z = x

    # term_pp: [coeff_1/z, coeff_1/(z-1), coeff_1/(z+1)]
    # term_qq / term_a1 / term_a2: [coeff_1/z, coeff_1/z^2, coeff_1/(z-1), coeff_1/(z+1)]
    # Expansion at z=0 toward z=+1: the local variable is z=+x (no reflection), so
    # there is no d/dz=-d/dx sign flip downstream (cf. get_analytic_from_0p).
    P  = term_pp[0] + z * (
        term_pp[1] / (z - 1) + term_pp[2] / (z + 1)
    )
    Q  = term_qq[1] + z * term_qq[0] + z**2 * (
        term_qq[2] / (z - 1) + term_qq[3] / (z + 1)
    )
    A1 = term_a1[1] + z * term_a1[0] + z**2 * (
        term_a1[2] / (z - 1) + term_a1[3] / (z + 1)
    )
    A2 = term_a2[1] + z * term_a2[0] + z**2 * (
        term_a2[2] / (z - 1) + term_a2[3] / (z + 1)
    )

    P  = trunc_series_from_expr(R, P)
    Q  = trunc_series_from_expr(R, Q)
    A1 = trunc_series_from_expr(R, A1)
    A2 = trunc_series_from_expr(R, A2)
    return coeffs(P, N), coeffs(Q, N), coeffs(A1, N), coeffs(A2, N)


# -----------------------------------------------------------------------------
# Power-series helpers
# -----------------------------------------------------------------------------

def series_from_coeffs(ctx, a):
    R, x = ctx["R"], ctx["x"]
    n = min(len(a), ctx["N"] + 1)
    return sum(R.base_ring()(a[kk]) * x**kk for kk in range(n)) + O(x**n)


def integrate_regular(ctx, f):
    R, x, N = ctx["R"], ctx["x"], ctx["N"]
    return sum(f[kk] * x**(kk + 1) / (kk + 1) for kk in range(N)) + O(x**(N + 1))


def integ_factor_not_int(ctx, f, alpha):
    R, x, N = ctx["R"], ctx["x"], ctx["N"]
    return sum(f[kk] * x**kk / (kk - alpha) for kk in range(N + 1)) + O(x**(N + 1))


# -----------------------------------------------------------------------------
# Frobenius and particular solutions
# -----------------------------------------------------------------------------

def hom_sol_fro_const(ctx, r, P, Q, sol_order=None):
    # Frobenius series of the indicial root r, recurrence (rec:0)/(rec:1).
    #
    # sol_order=m computes only the coefficients 0..m-1 and leaves the rest zero.
    # This is the order-N0 truncation f_approx used by the matrix and the residual: the
    # residual of f_approx never reads coefficients beyond N0-1, so stopping the
    # recursion there is exact and avoids the costly high-order terms.
    K, R, x, N = ctx["K"], ctx["R"], ctx["x"], ctx["N"]
    top = N if sol_order is None else min(sol_order - 1, N)
    f  = [K(0)] * (N + 1)
    f[0] = K(1)
    p0 = P[0]
    q0 = Q[0]
    def next_term(ii):
        num = K(0)
        for jj in range(ii):
            k = ii - jj
            num += (P[k] * (r + jj) + Q[k]) * f[jj]
        ri  = r + ii
        den = ri * (ri - 1) + p0 * ri + q0
        return -num / den
    for ii in range(1, top + 1):
        f[ii] = next_term(ii)
    return series_from_coeffs(ctx, f)


def _contains_zero(ctx, val):
    # True if val is zero (exact mode) or its ball encloses zero (route-A mode).
    # Over balls val lives in K = RBF[eps]/(eps^2); contains_zero() is a RealBall
    # method, so we extract the eps^0 coefficient first.
    if ctx.get("ball"):
        try:
            return val.lift()[0].contains_zero()
        except Exception:
            try:
                return val.contains_zero()
            except Exception:
                return val == ctx["K"](0)
    return val == ctx["K"](0)


def particular_sol_recurrence(ctx, P, Q, G):
    # Holomorphic particular solution  f = sum_{n>=0} c_n x^n  of the inhomogeneous
    # Fuchsian normal form   x^2 f'' + x P(x) f' + Q(x) f = G(x),  built directly from
    # the Frobenius recurrence (rec:aff) of Proposition prop:aff:rec:
    #     I(n) c_n = g_n - sum_{j<n} (j p_{n-j} + q_{n-j}) c_j,   I(n) = n(n-1)+n p0+q0.
    # Here I(n) != 0 for every n >= 1 (theta, lambda are non-integers).  The only
    # resonant index is n=0 at z=+1, where q0 = I(0) = 0; there the normal-form forcing
    # has g_0 = 0 (the structural (z-1) factor in A1, A2), so the n=0 equation reads
    # 0 = 0 and we set c_0 := 0.  This reproduces, coefficient by coefficient, the
    # variation-of-constants solution it replaces (which also satisfies f(z_0) = 0).
    K, N = ctx["K"], ctx["N"]
    p0, q0 = P[0], Q[0]
    c = [K(0)] * (N + 1)
    for ii in range(N + 1):
        rhs = K(G[ii])
        for jj in range(ii):
            rhs -= (P[ii - jj] * jj + Q[ii - jj]) * c[jj]
        if ii == 0 and _contains_zero(ctx, q0):
            assert _contains_zero(ctx, rhs), (
                "resonant index n=0 requires the normal-form forcing to vanish at the "
                "base point (g_0 = 0)"
            )
            c[0] = K(0)
        else:
            c[ii] = rhs / (ii * (ii - 1) + p0 * ii + q0)
    return series_from_coeffs(ctx, c)


def construct_solutions_when_diff_is_integer_formal(ctx, r1, differ_of_r, P, Q, A1, A2,
                                                    sol_order=None):
    # Resonant case at z=0 (root difference 2): phi1 by Frobenius, phi2 by
    # reduction of order, and the two particular solutions by variation of
    # constants. sol_order only truncates the Frobenius series phi1; the
    # particular solutions inherit the truncation through phi1 and are read off
    # only up to N0-1 by the residual.
    R, x, N = ctx["R"], ctx["x"], ctx["N"]
    r2 = r1 - differ_of_r
    d  = differ_of_r
    phi1 = hom_sol_fro_const(ctx, r1, P, Q, sol_order=sol_order)
    P_series = series_from_coeffs(ctx, P)
    wi_P = (P_series - P[0]) / x
    analytic_term1 = -integrate_regular(ctx, wi_P)
    expo_analytic_term1 = analytic_term1.exp()
    psi  = expo_analytic_term1 / (phi1**2)
    primi = sum(
        (psi[kk] / (kk - d)) * x**kk
        for kk in range(N + 1)
        if kk != d
    ) + O(x**(N + 1))
    C    = psi[d]
    phi2 = primi * phi1
    phi1_phi1 = phi1 * phi1
    phi1_phi2 = phi1 * phi2
    corch = phi1 * phi2.derivative() - phi2 * phi1.derivative()
    psiW  = C * x**d * phi1_phi1 - d * phi1_phi2 + x * corch
    inv_psiW  = 1 / psiW
    A1_series = series_from_coeffs(ctx, A1)
    A2_series = series_from_coeffs(ctx, A2)
    def build_fp(A_series):
        aux_integrand = A_series * inv_psiW
        psi1_j  = aux_integrand * phi1
        psi2_j  = aux_integrand * phi2
        beta1   = integ_factor_not_int(ctx, psi1_j, r2)
        beta2   = integ_factor_not_int(ctx, psi2_j, r1)
        J       = integ_factor_not_int(ctx, beta1, r2)
        first   = C * x**d * phi1 * J
        second  = phi2 * beta1
        third   = phi1 * beta2
        return first + second - third
    fp1 = build_fp(A1_series)
    fp2 = build_fp(A2_series)
    return phi1, phi2, fp1, fp2, C


# -----------------------------------------------------------------------------
# Values and matrix construction
# -----------------------------------------------------------------------------

def analytic_value_and_derivative(ctx, f, x0):
    K, N = ctx["K"], ctx["N"]
    x0  = K(x0)
    val = sum(f[kk] * x0**kk for kk in range(N + 1))
    der = sum(kk * f[kk] * x0**(kk - 1) for kk in range(1, N + 1))
    return vector(K, [val, der])


def series_value_and_derivative(ctx, phi, x0):
    K, N = ctx["K"], ctx["N"]
    x0  = K(x0)
    phi_val = sum(phi[kk] * x0**kk for kk in range(N + 1))
    phi_der = sum(kk * phi[kk] * x0**(kk - 1) for kk in range(1, N + 1))
    return vector(K, [phi_val, phi_der])


def get_analytic_from_p1(ctx, th, term_pp, term_qq, term_a1, term_a2, z0=QQ(1)/2):
    K = ctx["K"]
    P, Q, A1, A2 = local_coeffs_at_p1(ctx, term_pp, term_qq, term_a1, term_a2)
    r1  = K(0)
    r2  = K(1) - P[0]                 # = 2 - lambda  (excluded singular exponent at z=+1)
    psi1 = hom_sol_fro_const(ctx, r1, P, Q)
    psi2 = hom_sol_fro_const(ctx, r2, P, Q)
    fp1  = particular_sol_recurrence(ctx, P, Q, A1)
    fp2  = particular_sol_recurrence(ctx, P, Q, A2)
    xp1  = K(z0) - K(1)              # local var x = z - 1 (z = 1 + x); d/dz = d/dx
    Fh1  = series_value_and_derivative(ctx, psi1, xp1)
    Ps2  = series_value_and_derivative(ctx, psi2, xp1)
    Fp1  = analytic_value_and_derivative(ctx, fp1, xp1)
    Fp2  = analytic_value_and_derivative(ctx, fp2, xp1)
    return Fh1, Ps2, Fp1, Fp2


def get_analytic_from_0p(ctx, the, term_pp, term_qq, term_a1, term_a2, z0=QQ(1)/2):
    K = ctx["K"]
    P, Q, A1, A2 = local_coeffs_at_0p(
        ctx, term_pp, term_qq, term_a1, term_a2
    )
    r_big        = K(1) - the
    differ_of_r  = ZZ(2)
    phi1, phi2, fp1, fp2, C = construct_solutions_when_diff_is_integer_formal(
        ctx, r_big, differ_of_r, P, Q, A1, A2
    )
    x00 = K(z0)                      # x = z (z = +x), so no d/dz = -d/dx sign flip
    Ps1 = series_value_and_derivative(ctx, phi1, x00)
    Ps2 = series_value_and_derivative(ctx, phi2, x00)
    Fp1 = analytic_value_and_derivative(ctx, fp1, x00)
    Fp2 = analytic_value_and_derivative(ctx, fp2, x00)
    return Ps1, Ps2, Fp1, Fp2


# -----------------------------------------------------------------------------
# Matrix constructor
# -----------------------------------------------------------------------------

def symbolic_matrix_A(N, z0=QQ(1)/2, lam_value=None, the_value=None, ball=None, bits=200):
    ctx = make_symbolic_context(N, lam_value=lam_value, the_value=the_value,
                                ball=ball, bits=bits)
    K   = ctx["K"]
    the = ctx["the"]
    lam = ctx["lam"]
    pp, qq, a1, a2 = default_parameter_matrices(ctx)
    eht = K(1) - the
    # Matching at the two physical singular points z=0 and z=+1, with the operator
    # of def:PQtl specialized directly at the physical +lambda.  At z=+1 the excluded
    # (singular) branch has exponent 2-lambda and is annulled -- only the holomorphic
    # branch and the particular solutions enter the matrix -- so the regularity is
    # dictated by the binding exponent 2+lambda at z=-1.
    term_pp_the, term_qq_the, term_a1_the, term_a2_the = specialize_terms(pp, qq, a1, a2, the, lam)
    term_pp_eht, term_qq_eht, term_a1_eht, term_a2_eht = specialize_terms(pp, qq, a1, a2, eht, lam)
    Fh1_p1_the, Fh2_p1_the, Fp1_p1_the, Fp2_p1_the = get_analytic_from_p1(
        ctx, the, term_pp_the, term_qq_the, term_a1_the, term_a2_the, z0=z0
    )
    Fh1_p1_eht, Fh2_p1_eht, Fp1_p1_eht, Fp2_p1_eht = get_analytic_from_p1(
        ctx, eht, term_pp_eht, term_qq_eht, term_a1_eht, term_a2_eht, z0=z0
    )
    Fh1_0p_the, Fh2_0p_the, Fp1_0p_the, Fp2_0p_the = get_analytic_from_0p(
        ctx, the, term_pp_the, term_qq_the, term_a1_the, term_a2_the, z0=z0
    )
    Fh1_0p_eht, Fh2_0p_eht, Fp1_0p_eht, Fp2_0p_eht = get_analytic_from_0p(
        ctx, eht, term_pp_eht, term_qq_eht, term_a1_eht, term_a2_eht, z0=z0
    )
    A_p1 = matrix(K, [
        [Fh1_p1_the[0], 0,              Fp1_p1_the[0], Fp2_p1_the[0]],
        [Fh1_p1_the[1], 0,              Fp1_p1_the[1], Fp2_p1_the[1]],
        [0,              Fh1_p1_eht[0], Fp2_p1_eht[0], Fp1_p1_eht[0]],
        [0,              Fh1_p1_eht[1], Fp2_p1_eht[1], Fp1_p1_eht[1]],
    ])
    A_0p = matrix(K, [
        [0, 0, Fp1_0p_the[0], Fp2_0p_the[0]],
        [0, 0, Fp1_0p_the[1], Fp2_0p_the[1]],
        [0, 0, Fp2_0p_eht[0], Fp1_0p_eht[0]],
        [0, 0, Fp2_0p_eht[1], Fp1_0p_eht[1]],
    ])
    return A_p1 - A_0p, ctx


# =============================================================================
# Residual computation
# =============================================================================
#
# R is defined via  x^2 R'' = D  (Lemma lem:sec_ord:LS, equation def:appB:R),
# so  R[k] = D[k] / (k*(k-1))  for k >= 2.
#
# D = G - L_r[f_approx]  where L_r is the (shifted) local operator.
# For analytic functions (r = 0): L_r = L directly.
# For Frobenius factors (r != 0): L_r[phi] = x^2 phi'' + (P+2r)x phi' + (I_r+rP+Q) phi.

def _apply_operator_r(ctx, f, r, P_coeffs, Q_coeffs, G_list=None):
    """
    Compute D = G - L_r[f] as a coefficient list.

    For r=0: L_r = L = x^2 f'' + xP f' + Qf.                   |
    For r!=0: L_r[f] = x^2 f'' + (P+2r)x f' + (r(r-1)+rP+Q) f. | <- This branch is currently unused in the proof script.
    """
    K = ctx["K"]
    x = ctx["x"]
    N = ctx["N"]
    r_K = K(r)

    if bool(r_K == K(0)):
        P_ser = series_from_coeffs(ctx, P_coeffs)
        Q_ser = series_from_coeffs(ctx, Q_coeffs)
        Lf = x**2 * f.derivative().derivative() + x * P_ser * f.derivative() + Q_ser * f
    else:
        raise NotImplementedError("r != 0 path is not part of the certified proof")

    if G_list is None:
        D_ser = -Lf
    else:
        G_ser = series_from_coeffs(ctx, G_list)
        D_ser = G_ser - Lf

    return [D_ser[kk] for kk in range(N + 1)]
