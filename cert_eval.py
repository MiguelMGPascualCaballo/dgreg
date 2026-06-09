from sage.all import *

# cert_eval.py
#
# Numeric layer.  Takes the exact residual series of cert_residuals and substitutes
# (theta, lambda) as RealBallField elements, then assembles the certified bounds
# delta, delta' of Lemma lem:sec_ord:LS.  This is the ONLY place ball arithmetic
# enters.
#
# The residual norms are rigorous: a finite sum of the exact coefficients up to
# Nres (norm_AN0 / norm_deriv) plus the Cauchy tail k > Nres (xi_tails), following
# Lemma lem:tails:xi.  The contraction constant ell comes from the analytic
# sup-bounds of Lemmas lem:sup:00 and lem:sup:-1 (L_bound), so no tail is needed
# for ell.


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
    Enclose a polynomial in QQ[the] or QQ[the, lam] at (the_b, lam_b).

    Uses Sage's polynomial __call__, i.e. Horner's rule, which gives a much tighter
    interval enclosure than the expanded term-by-term sum (the powers the_b^e are
    nested instead of summed independently).  This is what keeps a denominator from
    spuriously straddling 0 over a theta-ball.
    """
    if poly.parent().ngens() == 2:
        return RB(poly(the_b, lam_b))
    return RB(poly(the_b))


def eval_coeff(c, the_b, lam_b, RB, label=None):
    """
    Enclose one Frac(QQ[the, lam]) coefficient at the ball point.

    A denominator ball that contains zero means the (theta, lambda) box straddles
    a pole of this coefficient; we raise so the caller can subdivide theta.  Note
    RBF would silently return a NaN/inf ball here and compare False later, so the
    explicit check is what keeps the bisection honest.
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
        z=-1  ||p|| <= 8, ||x p' - p - q|| <= 24 ->  ell <= 8/N0 + 24/(N0(N0-1)).
    Uniform in (theta, lambda), so this is an exact rational, no ball needed.
    """
    if point == "00":
        c1, c2 = QQ(4), QQ(8)       # valid for N0 >= 6
    elif point == "m1":
        c1, c2 = QQ(8), QQ(24)      # valid for N0 >= 11
    else:
        raise ValueError("point must be '00' or 'm1'")
    return c1 / N0 + c2 / (N0 * (N0 - 1))


# -----------------------------------------------------------------------------
# Cauchy sup-bounds M_p(rho), M_q(rho)  (Lemmas lem:sup:Mbound:m1, lem:tails:Mbound:00)
# -----------------------------------------------------------------------------

def rational_M_m1(cp, cq, rho):
    """M_p(rho), M_q(rho) at z=-1 from cp = (c^p_0, c^p_1, c^p_2), cq = (c^q_0..c^q_3)."""
    Mp = abs(cp[2]) + rho * (abs(cp[0]) / (1 - rho) + abs(cp[1]) / (2 - rho))
    Mq = (abs(cq[3]) * rho
          + rho**2 * (abs(cq[0]) / (1 - rho)
                      + abs(cq[1]) / (1 - rho)**2
                      + abs(cq[2]) / (2 - rho)))
    return Mp, Mq


def rational_M_00(cp, cq, rho):
    """M_p(rho), M_q(rho) at z=0 from cp = (c^p_0, c^p_1, c^p_2), cq = (c^q_0..c^q_3)."""
    Mp = abs(cp[0]) + rho * (abs(cp[1]) + abs(cp[2])) / (1 - rho)
    Mq = abs(cq[1]) + abs(cq[0]) * rho + rho**2 * (abs(cq[2]) + abs(cq[3])) / (1 - rho)
    return Mp, Mq


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


def ftilde_norms(ftilde_RB, rho):
    """C_val = sum_m |f~_m| rho^m and C_der = sum_m m |f~_m| rho^m (Lemma lem:tails:xi)."""
    RB = rho.parent()
    C_val = RB(0)
    C_der = RB(0)
    for m, fm in enumerate(ftilde_RB):
        term = abs(fm) * rho**m
        C_val += term
        C_der += RB(m) * term
    return C_val, C_der


def xi_tails(Mp, Mq, C_val, C_der, N0, Nres, b0, rho):
    """
    Cauchy tails k > Nres of ||xi||_{A_N0} and ||d/dx xi||_{Linf} (Lemma lem:tails:xi):
        S = Mp C_der + Mq C_val,   r = b0/rho,
        tail_val = S / b0^N0 * r^{Nres+1} / (1-r),
        tail_der = S / b0     * r^{Nres+1} / (1-r).
    """
    S = Mp * C_der + Mq * C_val
    r = b0 / rho
    geom = r**(Nres + 1) / (1 - r)
    tail_val = S / b0**N0 * geom
    tail_der = S / b0 * geom
    return tail_val, tail_der


# -----------------------------------------------------------------------------
# delta, delta' per function
# -----------------------------------------------------------------------------

def delta_block(point, xi_RB, ftilde_RB, Mp, Mq, N0, Nres, b0, rho):
    """Per-function (delta_val, delta_der, ell) from (appB:Linfbound)/(appB:Eprimebound), M=b0."""
    RB = b0.parent()
    ell = RB(L_bound(point, N0))
    if not (ell < 1):
        raise ValueError("contraction ell < 1 not certified at %s (N0=%d): ell = %s"
                         % (point, N0, ell))
    C_val, C_der = ftilde_norms(ftilde_RB, rho)
    tail_val, tail_der = xi_tails(Mp, Mq, C_val, C_der, N0, Nres, b0, rho)
    nR  = norm_AN0(xi_RB, N0, Nres, b0) + tail_val
    nRp = norm_deriv(xi_RB, N0, Nres, b0) + tail_der
    M = b0
    inv = RB(1) / (RB(1) - ell)
    delta_val = M**N0 * inv * nR
    delta_der = (RB(N0) * ell * M**(N0 - 1) * inv) * nR + nRp
    return delta_val, delta_der, ell

