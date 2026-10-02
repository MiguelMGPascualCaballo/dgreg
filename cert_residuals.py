from sage.all import *

# cert_residuals.py
#
# Exact residual series xi(x, theta, lambda) for the functions that build Mcrit,
# computed over K = Frac(QQ[the, lam]) (or Frac(QQ[the]) when lambda is fixed).
# No ball arithmetic here; that is deferred to cert_eval.py.
#
# Orders.  The matrix uses the order-N0 truncation f^ap (coefficients 0..N0-1).
# The residual xi = double integral of (g - L[f^ap]) / x^2  (def:appB:R) is
# in general an infinite series.  Since f^ap matches the exact solution to order
# N0, xi_k = 0 for k < N0.  Only the coefficients through Nres >= N0 are stored;
# the tail k > Nres is bounded by cert_eval.xi_tails (Lemma lem:tails:xi).
#
# Besides xi, each block also stores the data the tail estimates of Appendix B
# need: the specialized coefficient vectors term_pp = (c^p_i), term_qq = (c^q_j)
# for M_p, M_q, and the N0 truncation coefficients f^ap_m of every function.

from local_fuchs import (
    make_symbolic_context,
    default_parameter_matrices,
    specialize_terms,
    local_coeffs_at_p1,
    local_coeffs_at_0,
    hom_sol_fro_const,
    particular_sol_ordinary_direct,
    particular_sol_r1_is_0_direct,
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


def _defect_vanishes(ctx, z):
    """z == 0 (exact mode), or every ball component of z contains 0 (ball mode)."""
    if not ctx.get("ball"):
        return z == ctx["K"](0)
    try:
        L = z.lift().list()
    except AttributeError:
        L = [z]
    return all(c.contains_zero() for c in L) if L else True


def _residual_of(ctx, f_full, N0, P, Q, G_list=None):
    """
    xi[0..Nres] of the order-N0 truncation f^ap, xi[k] = (g - L[f^ap])[k] / (k(k-1)).
    The coefficients k > Nres are not zero in general; they are bounded separately.
    """
    K, N = ctx["K"], ctx["N"]
    f_approx = _truncate(ctx, f_full, N0)
    D = _apply_operator_r(ctx, f_approx, K(0), P, Q, G_list=G_list)
    assert _defect_vanishes(ctx, D[0]) and _defect_vanishes(ctx, D[1]), (
        "residual defect does not vanish at orders 0 and 1 -- matching condition violated"
    )
    xi = [K(0)] * (N + 1)
    for k in range(2, N + 1):
        xi[k] = D[k] / (K(k) * K(k - 1))
    return xi


def residuals_at_p1(ctx, term_pp, term_qq, term_a1, term_a2, N0, sol_order=None):
    """
    Functions at z=1 entering Mcrit: the holomorphic Frobenius solution phi1
    (root r=0) and the two particular solutions fp1, fp2.  All are holomorphic,
    so the residual operator uses r=0.  (The singular branch, exponent 2-lambda,
    is the excluded one.)
    """
    K = ctx["K"]
    P, Q, A1, A2 = local_coeffs_at_p1(ctx, term_pp, term_qq, term_a1, term_a2)
    r1 = K(0)
    phi1 = hom_sol_fro_const(ctx, r1, P, Q, sol_order=sol_order)
    # Only coefficients 0..N0-1 enter f^ap.
    top = ctx["N"] if sol_order is None else min(ctx["N"], sol_order - 1)
    fp1 = particular_sol_r1_is_0_direct(ctx, A1, P, Q, top)
    fp2 = particular_sol_r1_is_0_direct(ctx, A2, P, Q, top)
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
    the particular solutions are needed.  Local variable x = z (no flip).
    """
    P, Q, A1, A2 = local_coeffs_at_0(
        ctx, term_pp, term_qq, term_a1, term_a2
    )
    top = ctx["N"] if sol_order is None else min(ctx["N"], sol_order - 1)
    fp1 = particular_sol_ordinary_direct(ctx, A1, P, Q, top)
    fp2 = particular_sol_ordinary_direct(ctx, A2, P, Q, top)
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
    Coefficients 0..Nres of every matrix-relevant residual, exact in (theta, lambda).

    lam_value : fix lambda to this rational (univariate, faster), or None to keep
                it symbolic.
    the_value : fix theta to this rational and keep lambda symbolic.  Not used
                by the proof.
    ball      : (theta_ball, lam_ball) -> optional dual-number-over-balls context
                (see local_fuchs.make_symbolic_context).  Not used by the proof.

    The Frobenius recurrences are stopped at degree N0-1 (sol_order=N0): the
    residual only reads f^ap up to N0-1, so this is exact.

    Returns {"p1": {"the": blk, "eht": blk}, "00": {...}, plus metadata}, where
    each blk maps a function name to its xi list (indices 0..Nres) and carries
    "fapprox", "term_pp", "term_qq", "_P", "_Q".  The tail k > Nres is bounded
    when these data are evaluated (cert_eval.xi_tails).
    """
    if not (Nres >= N0):
        raise ValueError("Nres must be at least N0")
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
