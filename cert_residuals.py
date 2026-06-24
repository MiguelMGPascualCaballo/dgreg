from sage.all import *

# cert_residuals.py
#
# Exact residual series xi(x, theta, lambda) for the functions that build Mcrit,
# computed over K = Frac(QQ[the, lam]) (or Frac(QQ[the]) when lambda is fixed).
# No ball arithmetic here; that is deferred to cert_eval.py.
#
# Orders.  The matrix uses the order-N0 truncation f^ap (coefficients 0..N0-1).
# The residual xi = double integral of (g - L[f^ap]) / x^2  (def:appB:R) is
# computed up to coefficient Nres > N0.  Since f_ap matches the exact solution to
# order N0, xi vanishes exactly for k < N0 and is supported on N0 <= k <= Nres.
#
# Besides xi, each block also stores the data the tail estimates of Appendix B
# need: the specialized coefficient vectors term_pp = (c^p_i), term_qq = (c^q_j)
# for M_p, M_q, and the N0 truncation coefficients f^ap_m of every function.

from local_fuchs import (
    make_symbolic_context,
    default_parameter_matrices,
    specialize_terms,
    local_coeffs_at_p1,
    local_coeffs_at_0p,
    hom_sol_fro_const,
    particular_sol_recurrence,
    construct_solutions_when_diff_is_integer_formal,
    _apply_operator_r,
)


def _truncate(ctx, f, N0):
    """Order-N0 Taylor truncation of f, kept exact at full Nres precision."""
    R, x, N = ctx["R"], ctx["x"], ctx["N"]
    top = min(N0, N + 1)
    # f^ap is a polynomial of degree < N0; the trailing O(x^{N+1}) keeps it living
    # at the residual precision Nres, so g - L[f^ap] is reliable up to Nres.
    return sum(f[i] * x**i for i in range(top)) + O(x**(N + 1))


def _fapprox(ctx, f, N0):
    """The N0 truncation coefficients f^ap_0, ..., f^ap_{N0-1} as a plain list."""
    return [f[m] for m in range(N0)]


def _residual_of(ctx, f_full, N0, P, Q, G_list=None):
    """Residual xi[k] = (g - L[f^ap])[k] / (k(k-1)) of the order-N0 truncation f^ap."""
    K, N = ctx["K"], ctx["N"]
    f_approx = _truncate(ctx, f_full, N0)
    D = _apply_operator_r(ctx, f_approx, K(0), P, Q, G_list=G_list)
    if ctx.get("ball"):
        # over balls the structural zeros become small balls; check containment
        def _rb_contains_zero(elem):
            try:
                return elem.lift()[0].contains_zero()
            except Exception:
                try:
                    return elem.contains_zero()
                except Exception:
                    return False
        assert _rb_contains_zero(D[0]) and _rb_contains_zero(D[1]), (
            "residual defect does not vanish at orders 0 and 1 -- matching condition violated"
        )
    else:
        assert D[0] == K(0) and D[1] == K(0), (
            "residual defect does not vanish at orders 0 and 1 -- matching condition violated"
        )
    xi = [K(0)] * (N + 1)
    for k in range(2, N + 1):
        xi[k] = D[k] / (K(k) * K(k - 1))
    return xi


def residuals_at_p1(ctx, term_pp, term_qq, term_a1, term_a2, N0, sol_order=None):
    """
    Functions at z=+1 entering Mcrit: the holomorphic Frobenius solution phi1
    (root r=0) and the two particular solutions fp1, fp2.  All are holomorphic,
    so the residual operator uses r=0.  (The singular branch, exponent 2-lambda,
    is the excluded one.)
    """
    K = ctx["K"]
    P, Q, A1, A2 = local_coeffs_at_p1(ctx, term_pp, term_qq, term_a1, term_a2)
    r1 = K(0)
    phi1 = hom_sol_fro_const(ctx, r1, P, Q, sol_order=sol_order)
    fp1 = particular_sol_recurrence(ctx, P, Q, A1)
    fp2 = particular_sol_recurrence(ctx, P, Q, A2)
    return {
        "phi1": _residual_of(ctx, phi1, N0, P, Q, G_list=None),
        "fp1":  _residual_of(ctx, fp1,  N0, P, Q, G_list=A1),
        "fp2":  _residual_of(ctx, fp2,  N0, P, Q, G_list=A2),
        "fapprox": {
            "phi1": _fapprox(ctx, phi1, N0),
            "fp1":  _fapprox(ctx, fp1,  N0),
            "fp2":  _fapprox(ctx, fp2,  N0),
        },
        "term_pp": term_pp,
        "term_qq": term_qq,
        "_P": P,
        "_Q": Q,
    }


def residuals_at_00(ctx, term_pp, term_qq, term_a1, term_a2, N0, th, sol_order=None):
    """
    Functions at z=0 entering Mcrit: fp1, fp2 (both holomorphic).  The dominant
    Frobenius solution phi1 ~ x^{1-theta} does not appear in the matrix, so only
    the particular solutions are needed.  Expansion toward z=+1 (z=+x, no flip).
    """
    K = ctx["K"]
    P, Q, A1, A2 = local_coeffs_at_0p(
        ctx, term_pp, term_qq, term_a1, term_a2
    )
    r1 = K(1) - th
    phi1, phi2, fp1, fp2, C = construct_solutions_when_diff_is_integer_formal(
        ctx, r1, ZZ(2), P, Q, A1, A2, sol_order=sol_order
    )
    return {
        "fp1": _residual_of(ctx, fp1, N0, P, Q, G_list=A1),
        "fp2": _residual_of(ctx, fp2, N0, P, Q, G_list=A2),
        "fapprox": {
            "fp1": _fapprox(ctx, fp1, N0),
            "fp2": _fapprox(ctx, fp2, N0),
        },
        "term_pp": term_pp,
        "term_qq": term_qq,
        "_P": P,
        "_Q": Q,
    }


# Functions whose residual enters each singular point, in matrix order.
MATRIX_FUNCS = {"p1": ["phi1", "fp1", "fp2"], "00": ["fp1", "fp2"]}


def all_res_sym(Nres, N0, lam_value=None, the_value=None, ball=None, bits=200):
    """
    Every matrix-relevant residual series, exact in (theta, lambda).

    lam_value : fix lambda to this rational (univariate, faster), or None to keep
                it symbolic.
    the_value : fix theta to this rational and keep lambda symbolic (univariate in
                lambda) -- the cheap pass for the simplicity gap, no bivariate OOM.
    ball      : (theta_ball, lam_ball) -> route-A dual-number-over-balls context
                (lambda = lam_ball + eps, eps^2=0); residual coefficients come out as
                duals whose eps^0 part is the value and eps^1 part the d/dlambda, both
                enclosed over the (theta,lambda) box.

    The Frobenius recursion is stopped at order N0 (sol_order=N0): the residual
    only reads f^ap up to N0-1, so this is exact and drops the costly high-order
    Frobenius coefficients.

    Returns {"p1": {"the": blk, "eht": blk}, "00": {...}, plus metadata}, where
    each blk maps a function name to its xi list and carries "fapprox", "term_pp",
    "term_qq", "_P", "_Q".
    """
    if not (Nres > N0):
        raise ValueError("Nres must be strictly greater than N0")
    ctx = make_symbolic_context(Nres, lam_value=lam_value, the_value=the_value,
                                ball=ball, bits=bits)
    K = ctx["K"]
    the, lam = ctx["the"], ctx["lam"]
    # Base matrices encode the operator of def:PQtl directly in +lambda (consistent
    # with local_fuchs.symbolic_matrix_A); specialize at the physical lambda.
    pp, qq, a1, a2 = default_parameter_matrices(ctx)
    sol_order = N0

    out = {
        "p1": {}, "00": {},
        "_ctx": ctx, "_N0": N0, "_Nres": Nres,
        "_lam_value": lam_value,
    }
    for branch, th in [("the", the), ("eht", K(1) - the)]:
        t_pp, t_qq, t_a1, t_a2 = specialize_terms(pp, qq, a1, a2, th, lam)
        out["p1"][branch] = residuals_at_p1(ctx, t_pp, t_qq, t_a1, t_a2, N0, sol_order=sol_order)
        out["00"][branch] = residuals_at_00(ctx, t_pp, t_qq, t_a1, t_a2, N0, th, sol_order=sol_order)
    return out
