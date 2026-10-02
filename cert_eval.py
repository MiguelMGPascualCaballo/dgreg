from sage.all import *

# cert_eval.py
#
# Bounds of Appendix sec:appendix:errors on ball inputs.  The exact residual data
# of cert_residuals are enclosed over a theta-ball by
# cert_det_post.eval_series_tight; this module turns those enclosures into the
# bounds delta, delta' of Lemma lem:delta-cert.
#
# The residual norms are a finite sum of the exact coefficients up to Nres
# (norm_AN0 / norm_deriv) plus the Cauchy tail k > Nres (xi_tails), which
# includes the normalized forcing bound M_g (forcing_M), following Lemmas
# lem:forcing:Mbound and lem:tails:xi.  The contraction constant ell comes from
# Lemmas lem:sup:00 and lem:sup:-1 (L_bound).
#
# make_balls, eval_coeff and eval_series are direct ball evaluations; the proof
# does not call them.


# -----------------------------------------------------------------------------
# Ball substitution
# -----------------------------------------------------------------------------

def make_balls(bits, theta_mid, theta_rad, lam_value, lam_rad):
    """RealBallField and the parameter balls; radius 0 gives a thin (point) ball."""
    RB = RealBallField(bits)
    the_b = RB(QQ(theta_mid))
    if theta_rad != 0:
        the_b = the_b.add_error(RB(QQ(theta_rad)))
    lam_b = RB(QQ(lam_value))
    if lam_rad != 0:
        lam_b = lam_b.add_error(RB(QQ(lam_rad)))
    return RB, the_b, lam_b


def _eval_poly(poly, the_b, lam_b, RB):
    """
    Evaluate a polynomial in QQ[the] or QQ[the, lam] at ball values.

    Uses Sage's polynomial evaluation instead of an explicit expanded
    term-by-term interval sum, in one variable uses Horner's rule.
    """
    if poly.parent().ngens() == 2:
        return RB(poly(the_b, lam_b))
    return RB(poly(the_b))


def eval_coeff(c, the_b, lam_b, RB, label=None):
    """
    Enclose one Frac(QQ[the, lam]) coefficient at the ball point.

    Raises if the denominator ball contains zero (RBF would otherwise return a
    non-finite ball).
    """
    nb = _eval_poly(c.numerator(), the_b, lam_b, RB)
    db = _eval_poly(c.denominator(), the_b, lam_b, RB)
    if db.contains_zero():
        where = "" if label is None else " (%s)" % label
        raise ValueError("denominator ball contains 0%s: subdivide theta" % where)
    return nb / db


def eval_series(coeffs, the_b, lam_b, RB, label=None):
    """Enclose a whole coefficient list (or Sage vector)."""
    return [eval_coeff(c, the_b, lam_b, RB, label=label) for c in coeffs]


# -----------------------------------------------------------------------------
# Contraction constant (Lemmas lem:sup:00, lem:sup:-1)
# -----------------------------------------------------------------------------

def L_bound(point, N0):
    """
    Contraction constant ell of (appB:L) from the analytic sup-bounds:
        z=0   ||p|| < 4,  ||x p' - p - q|| < 8   ->  ell <= 4/N0 + 8/(N0(N0-1))
        z=1   ||p|| <= 8, ||x p' - p - q|| <= 16 ->  ell <= 8/N0 + 16/(N0(N0-1)).
    Valid for theta in (0, 1) and lambda in {56/100, 60/100} only; there it is
    uniform, so it is an exact rational.
    """
    if point == "00":
        c1, c2 = QQ(4), QQ(8)       # valid for N0 >= 6
    elif point == "p1":
        c1, c2 = QQ(8), QQ(16)      # valid for N0 >= 10 (lem:sup:-1)
    else:
        raise ValueError("point must be '00' or 'p1'")
    return c1 / N0 + c2 / (N0 * (N0 - 1))


# -----------------------------------------------------------------------------
# Cauchy sup-bounds M_p(rho), M_q(rho)  (Lemmas lem:cau:Mbound:m1, lem:cau:Mbound:00)
# -----------------------------------------------------------------------------

def rational_M_p1(cp, cq, rho):
    """M_p(rho), M_q(rho) at z=1 from cp = (c^p_0, c^p_1, c^p_2), cq = (c^q_0..c^q_3)."""
    Mp = abs(cp[1]) + rho * (abs(cp[0]) / (1 - rho) + abs(cp[2]) / (2 - rho))
    Mq = (abs(cq[2]) * rho
          + rho**2 * (abs(cq[0]) / (1 - rho)
                      + abs(cq[1]) / (1 - rho)**2
                      + abs(cq[3]) / (2 - rho)))
    return Mp, Mq


def rational_M_00(cp, cq, rho):
    """M_p(rho), M_q(rho) at z=0 from cp = (c^p_0, c^p_1, c^p_2), cq = (c^q_0..c^q_3)."""
    Mp = abs(cp[0]) + rho * (abs(cp[1]) + abs(cp[2])) / (1 - rho)
    Mq = abs(cq[1]) + abs(cq[0]) * rho + rho**2 * (abs(cq[2]) + abs(cq[3])) / (1 - rho)
    return Mp, Mq


def forcing_M(point, fn, a, b, rho):
    """
    M_g(rho) of Lemma lem:forcing:Mbound, with a >= theta(2-theta) and
    b >= 1-theta^2 = (1-theta)(1+theta); M_g = 0 for phi1.
    """
    if fn == "phi1":
        return rho.parent()(0)
    if point == "00" and fn == "fp1":
        return a * rho / (1 - rho**2)
    if point == "00" and fn == "fp2":
        return b / (1 - rho**2)
    if point == "p1" and fn == "fp1":
        return a * rho / ((1 - rho) * (2 - rho))
    if point == "p1" and fn == "fp2":
        return b * rho / ((1 - rho)**2 * (2 - rho))
    raise ValueError("unknown local forcing: %s, %s" % (point, fn))


# -----------------------------------------------------------------------------
# Residual norms: finite part (up to Nres) + Cauchy tail (k > Nres)
# -----------------------------------------------------------------------------

def norm_AN0(xi_RB, N0, Nres, b0):
    """Finite part of ||xi||_{A_N0} = sup_{|x|<=b0} |xi(x)/x^N0|, over N0..Nres."""
    RB = b0.parent()
    s = RB(0)
    for k in range(N0, Nres + 1):
        s += abs(xi_RB[k]) * b0**(k - N0)
    return s


def norm_deriv(xi_RB, N0, Nres, b0):
    """Finite part of ||d/dx xi||_{Linf([-b0,b0])}, over N0..Nres."""
    RB = b0.parent()
    s = RB(0)
    for k in range(N0, Nres + 1):
        s += abs(RB(k) * xi_RB[k]) * b0**(k - 1)
    return s


def fapprox_norms(fapprox_RB, rho):
    """C_val = sum_m |f^ap_m| rho^m and C_der = sum_m m |f^ap_m| rho^m (Lemma lem:tails:xi)."""
    RB = rho.parent()
    C_val = RB(0)
    C_der = RB(0)
    for m, fm in enumerate(fapprox_RB):
        term = abs(fm) * rho**m
        C_val += term
        C_der += RB(m) * term
    return C_val, C_der


def xi_tails(Mp, Mq, Mg, C_val, C_der, N0, Nres, b0, rho):
    """
    Cauchy tails k > Nres of ||xi||_{A_N0} and ||d/dx xi||_{Linf} (Lemma lem:tails:xi):
        S = Mp C_der + Mq C_val + Mg,   r = b0/rho,
        tail_val = S / (Nres (Nres+1) b0^N0) * r^{Nres+1} / (1-r),
        tail_der = S / (Nres b0)             * r^{Nres+1} / (1-r).
    """
    defect_bound = Mp * C_der + Mq * C_val + Mg
    r = b0 / rho
    geom = r**(Nres + 1) / (1 - r)
    tail_val = defect_bound / (Nres * (Nres + 1) * b0**N0) * geom
    tail_der = defect_bound / (Nres * b0) * geom
    return tail_val, tail_der


# -----------------------------------------------------------------------------
# delta, delta' per function
# -----------------------------------------------------------------------------

def delta_block(point, xi_RB, fapprox_RB, Mp, Mq, Mg, N0, Nres, b0, rho):
    """Per-function (delta_val, delta_der, ell) from (appB:Linfbound)/(appB:Eprimebound), M=b0."""
    RB = b0.parent()
    ell = RB(L_bound(point, N0))
    if not (ell < 1):
        raise ValueError("contraction ell < 1 not certified at %s (N0=%d): ell = %s"
                         % (point, N0, ell))
    C_val, C_der = fapprox_norms(fapprox_RB, rho)
    tail_val, tail_der = xi_tails(Mp, Mq, Mg, C_val, C_der, N0, Nres, b0, rho)
    nR  = norm_AN0(xi_RB, N0, Nres, b0) + tail_val
    nRp = norm_deriv(xi_RB, N0, Nres, b0) + tail_der
    M = b0
    inv = RB(1) / (RB(1) - ell)
    delta_val = M**N0 * inv * nR
    delta_der = (RB(N0) * ell * M**(N0 - 1) * inv) * nR + nRp
    return delta_val, delta_der, ell
