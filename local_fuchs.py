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

def make_symbolic_context(N, lam_value=None):
    # Working field K and power-series ring R = K[[x]] truncated at order N.
    #
    # lam_value=None keeps both theta and lambda symbolic, K = Frac(QQ[the, lam]).
    # Passing a rational lam_value fixes lambda and drops to the univariate field
    # K = Frac(QQ[the]); the Frobenius recursion then runs over univariate
    # fractions, which is markedly cheaper (smaller degrees, univariate gcds).
    # The residuals are independent of lambda only through these coefficients, so
    # fixing it and looping over {56/100, 60/100} costs two cheap passes instead
    # of one expensive bivariate pass.
    if lam_value is None:
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
    }



# -----------------------------------------------------------------------------
# Parameter matrices
# -----------------------------------------------------------------------------

def default_parameter_matrices(ctx):
    K = ctx["K"]       # Below, t denotes the and l lambda
    pp = matrix(K, [
    #     1   l   t
        [ 1,  0,  2],       # 1/z
        [-1, -1,  0],       # 1/(z-1)
        [-1,  1,  0],       # 1/(z+1)
    ])
    qq = matrix(K, [
    #     1   t t*l t^2
        [ 0,  0,  2,  0],   # 1/z
        [-1,  0,  0,  1],   # 1/z^2
        [ 1, -1, -1,  0],   # 1/(z-1)
        [-1,  1, -1,  0],   # 1/(z+1)
    ])
    # 1/z 1/z^2 1/(z-1) 1/(z+1) and 1 t t^2
    a1 = matrix(K, [[ 2], [ 0], [-1], [-1]]) \
        * matrix(K, [[0, 2, -1]]) * K(1)/K(2)
    a2 = matrix(K, [[ 0], [ 2], [-1], [ 1]]) \
        * matrix(K, [[1, 0, -1]]) * K(1)/K(2)
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


def local_coeffs_at_m1(ctx, term_pp, term_qq, term_a1, term_a2):
    R, x, N = ctx["R"], ctx["x"], ctx["N"]
    z = -1 + x

    # term_pp: [coeff_1/z, coeff_1/(z-1), coeff_1/(z+1)]
    # term_qq / term_a1 / term_a2: [coeff_1/z, coeff_1/z^2, coeff_1/(z-1), coeff_1/(z+1)]
    P = term_pp[2] + x * (term_pp[0] / z + term_pp[1] / (z - 1))
    Q = term_qq[3] * x + x**2 * (
        term_qq[0] / z + term_qq[1] / (z**2) + term_qq[2] / (z - 1)
    )
    A1 = term_a1[3] * x + x**2 * (
        term_a1[0] / z + term_a1[1] / (z**2) + term_a1[2] / (z - 1)
    )
    A2 = term_a2[3] * x + x**2 * (
        term_a2[0] / z + term_a2[1] / (z**2) + term_a2[2] / (z - 1)
    )

    P  = trunc_series_from_expr(R, P)
    Q  = trunc_series_from_expr(R, Q)
    A1 = trunc_series_from_expr(R, A1)
    A2 = trunc_series_from_expr(R, A2)
    return coeffs(P, N), coeffs(Q, N), coeffs(A1, N), coeffs(A2, N)


def local_coeffs_at_0m(ctx, term_pp, term_qq, term_a1, term_a2):
    R, x, N = ctx["R"], ctx["x"], ctx["N"]
    z = -x    
    
    # term_pp: [coeff_1/z, coeff_1/(z-1), coeff_1/(z+1)]
    # term_qq / term_a1 / term_a2: [coeff_1/z, coeff_1/z^2, coeff_1/(z-1), coeff_1/(z+1)]
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


def singular_integral(ctx, f, alpha):
    R, x, N = ctx["R"], ctx["x"], ctx["N"]
    return sum(f[kk] * x**(kk + 1) / (kk + 1 + alpha) for kk in range(N)) + O(x**(N + 1))


def particular_sol_r1_is_0(ctx, psi1, psi2, aff, r):
    K, R, x, N = ctx["K"], ctx["R"], ctx["x"], ctx["N"]
    term   = psi1 * psi2.derivative() - psi2 * psi1.derivative()
    psiW = r * psi1 * psi2 + x * term
    aff_series  = series_from_coeffs(ctx, aff)
    assert aff_series[0] == K(0), (
        "right-hand side must vanish at x=0 for the Wronskian formula to produce a holomorphic result"
    )
    aff_shift   = aff_series / x
    aff_inv_W   = aff_shift / psiW
    inte1 = psi1 * aff_inv_W
    inte2 = psi2 * aff_inv_W
    integral1 = singular_integral(ctx, inte1, -r)
    integral2 = integrate_regular(ctx, inte2)
    return psi2 * integral1 - psi1 * integral2


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


def get_analytic_from_m1(ctx, th, term_pp, term_qq, term_a1, term_a2, z0=QQ(-1)/2):
    K = ctx["K"]
    P, Q, A1, A2 = local_coeffs_at_m1(ctx, term_pp, term_qq, term_a1, term_a2)
    r1  = K(0)
    r2  = K(1) - P[0]
    psi1 = hom_sol_fro_const(ctx, r1, P, Q)
    psi2 = hom_sol_fro_const(ctx, r2, P, Q)
    fp1  = particular_sol_r1_is_0(ctx, psi1, psi2, A1, r2)
    fp2  = particular_sol_r1_is_0(ctx, psi1, psi2, A2, r2)
    xm1  = K(z0) + K(1)
    Fh1  = series_value_and_derivative(ctx, psi1, xm1)
    Ps2  = series_value_and_derivative(ctx, psi2, xm1)
    Fp1  = analytic_value_and_derivative(ctx, fp1, xm1)
    Fp2  = analytic_value_and_derivative(ctx, fp2, xm1)
    return Fh1, Ps2, Fp1, Fp2


def get_analytic_from_00(ctx, the, term_pp, term_qq, term_a1, term_a2, z0=QQ(-1)/2):
    K = ctx["K"]
    P, Q, A1, A2 = local_coeffs_at_0m(
        ctx, term_pp, term_qq, term_a1, term_a2
    )
    r_big        = K(1) - the
    differ_of_r  = ZZ(2)
    phi1, phi2, fp1, fp2, C = construct_solutions_when_diff_is_integer_formal(
        ctx, r_big, differ_of_r, P, Q, A1, A2
    )
    x00 = -K(z0)
    Ps1 = series_value_and_derivative(ctx, phi1, x00)
    Ps2 = series_value_and_derivative(ctx, phi2, x00)
    Fp1 = analytic_value_and_derivative(ctx, fp1, x00)
    Fp2 = analytic_value_and_derivative(ctx, fp2, x00)
    # Sign correction: x = -z, so d/dz = -d/dx
    Ps1 = vector(K, [Ps1[0], -Ps1[1]])
    Ps2 = vector(K, [Ps2[0], -Ps2[1]])
    Fp1 = vector(K, [Fp1[0], -Fp1[1]])
    Fp2 = vector(K, [Fp2[0], -Fp2[1]])
    return Ps1, Ps2, Fp1, Fp2


# -----------------------------------------------------------------------------
# Matrix constructor
# -----------------------------------------------------------------------------

def symbolic_matrix_A(N, z0=QQ(-1)/2, lam_value=None):
    ctx = make_symbolic_context(N, lam_value=lam_value)
    K   = ctx["K"]
    the = ctx["the"]
    lam = ctx["lam"]
    pp, qq, a1, a2 = default_parameter_matrices(ctx)
    eht = K(1) - the
    term_pp_the, term_qq_the, term_a1_the, term_a2_the = specialize_terms(pp, qq, a1, a2, the, lam)
    term_pp_eht, term_qq_eht, term_a1_eht, term_a2_eht = specialize_terms(pp, qq, a1, a2, eht, lam)
    Fh1_m1_the, Fh2_m1_the, Fp1_m1_the, Fp2_m1_the = get_analytic_from_m1(
        ctx, the, term_pp_the, term_qq_the, term_a1_the, term_a2_the, z0=z0
    )
    Fh1_m1_eht, Fh2_m1_eht, Fp1_m1_eht, Fp2_m1_eht = get_analytic_from_m1(
        ctx, eht, term_pp_eht, term_qq_eht, term_a1_eht, term_a2_eht, z0=z0
    )
    Fh1_00_the, Fh2_00_the, Fp1_00_the, Fp2_00_the = get_analytic_from_00(
        ctx, the, term_pp_the, term_qq_the, term_a1_the, term_a2_the, z0=z0
    )
    Fh1_00_eht, Fh2_00_eht, Fp1_00_eht, Fp2_00_eht = get_analytic_from_00(
        ctx, eht, term_pp_eht, term_qq_eht, term_a1_eht, term_a2_eht, z0=z0
    )
    A_m1 = matrix(K, [
        [Fh1_m1_the[0], 0,              Fp1_m1_the[0], Fp2_m1_the[0]],
        [Fh1_m1_the[1], 0,              Fp1_m1_the[1], Fp2_m1_the[1]],
        [0,              Fh1_m1_eht[0], Fp2_m1_eht[0], Fp1_m1_eht[0]],
        [0,              Fh1_m1_eht[1], Fp2_m1_eht[1], Fp1_m1_eht[1]],
    ])
    A_00 = matrix(K, [
        [0, 0, Fp1_00_the[0], Fp2_00_the[0]],
        [0, 0, Fp1_00_the[1], Fp2_00_the[1]],
        [0, 0, Fp2_00_eht[0], Fp1_00_eht[0]],
        [0, 0, Fp2_00_eht[1], Fp1_00_eht[1]],
    ])
    return A_m1 - A_00, ctx


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
