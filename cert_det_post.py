from sage.all import *

# cert_det_post.py
#
# Certified enclosure of det(Mcrit) over a theta-ball using TAYLOR MODELS in
# t = theta - theta_mid, built from each entry's NUMERATOR and DENOMINATOR
# polynomials (not from the whole fraction).
#
# Why num/den and not the fraction directly:
#   * Differentiating m = N/D in theta raises the denominator to D^2, D^3, ...
#     (huge degree, wild interval blow-up).  Here D appears only to power 1.
#   * Evaluating N/D over the ball by Horner still wraps when N, D have large
#     cancelling coefficients -- and more bits does NOT fix that.  Here the Taylor
#     coefficients of m come from the EXACT power series N(c+t)/D(c+t) over QQ
#     (no intervals, no cancellation); intervals enter only at the very end.
#
# Entry Taylor model (order k) about theta = c, on |t| <= r:
#   coefficients a_0..a_k = series of N(c+t)/D(c+t) to order k  (exact, in QQ);
#   remainder  |m(c+t) - sum a_l t^l| <= r^{k+1} * sup|H| / inf|D|, with
#   H(t) = (N(c+t) - P(t) D(c+t)) / t^{k+1},  P = sum a_l t^l, all from exact
#   coefficients (sup|H| = sum|H_l| r^l, inf|D| = |D(c)| - sum_{l>=1}|D_l| r^l).
#
# The determinant is then formed by Taylor-model arithmetic, so its t^0, t^1
# coefficients (det and d/dtheta det) are tight -- the determinant cancellation is
# done in the polynomial product.  The truncation gap M~ -> M_true is added in
# magnitude (Hadamard, per-entry radii); no derivative of the true solution, hence
# no f_theta tail, is used.

from local_fuchs import symbolic_matrix_A
from cert_eval import rational_M_m1, rational_M_00, delta_block


# -----------------------------------------------------------------------------
# Taylor models in t over |t| <= r:  f(t) = sum_{l=0}^{order} a[l] t^l + I
# -----------------------------------------------------------------------------

def _tpow(r, l, RB):
    """Enclosure of t^l over |t| <= r: 1 for l=0, [-r^l, r^l] otherwise."""
    if l == 0:
        return RB(1)
    return RB(0).add_error((r**l).upper())


class TM:
    """Order-`order` Taylor model in t on |t| <= r, coefficients/remainder in RB."""

    def __init__(self, a, I, r, order):
        self.a = list(a)
        self.I = I
        self.r = r
        self.order = order

    def _poly_enc(self):
        res = self.a[0]
        for l in range(1, self.order + 1):
            res = res + self.a[l] * _tpow(self.r, l, self.I.parent())
        return res

    def enclose(self):
        return self._poly_enc() + self.I

    def __add__(self, other):
        return TM([self.a[l] + other.a[l] for l in range(self.order + 1)],
                  self.I + other.I, self.r, self.order)

    def __neg__(self):
        return TM([-x for x in self.a], -self.I, self.r, self.order)

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        RB = self.I.parent()
        k = self.order
        r = self.r
        a, b = self.a, other.a
        c = [RB(0)] * (k + 1)
        overflow = RB(0)
        for i in range(k + 1):
            for j in range(k + 1):
                if i + j <= k:
                    c[i + j] = c[i + j] + a[i] * b[j]
                else:
                    overflow = overflow + a[i] * b[j] * _tpow(r, i + j, RB)
        newI = (overflow
                + self._poly_enc() * other.I
                + self.I * other._poly_enc()
                + self.I * other.I)
        return TM(c, newI, r, k)


def _tm_zero(r, order, RB):
    return TM([RB(0)] * (order + 1), RB(0), r, order)


def _tm_det(mat, r, order, RB):
    """Determinant of an n x n matrix of TMs, by cofactor expansion (handles zeros)."""
    n = len(mat)
    if n == 1:
        return mat[0][0]
    acc = _tm_zero(r, order, RB)
    for j in range(n):
        minor = [[mat[i][jj] for jj in range(n) if jj != j] for i in range(1, n)]
        term = mat[0][j] * _tm_det(minor, r, order, RB)
        acc = acc + term if (j % 2 == 0) else acc - term
    return acc


# -----------------------------------------------------------------------------
# Entry Taylor model from numerator/denominator
# -----------------------------------------------------------------------------

def _shift(poly, c, lam_value, t):
    """Substitute theta = c + t (and lambda = lam_value if present); result in QQ[t]."""
    if poly.parent().ngens() == 2:
        return poly(c + t, lam_value)
    return poly(c + t)


def _entry_tm(entry, c, lam_value, RB, r, r_rat, order, Pt):
    """Order-`order` Taylor model of the truncated entry m = N/D about theta = c."""
    N = entry.numerator()
    D = entry.denominator()
    if r_rat == 0:                                  # point theta: only the constant term survives
        bivar = (N.parent().ngens() == 2)
        d0 = D(c, lam_value) if bivar else D(c)
        if d0 == 0:
            raise ValueError("denominator vanishes at theta_mid (pole)")
        n0 = N(c, lam_value) if bivar else N(c)
        return TM([RB(n0 / d0)] + [RB(0)] * order, RB(0), r, order)
    t = Pt.gen()
    Nct = Pt(_shift(N, c, lam_value, t))
    Dct = Pt(_shift(D, c, lam_value, t))
    d0 = Dct[0]
    if d0 == 0:
        raise ValueError("denominator vanishes at theta_mid (pole)")

    Ps = PowerSeriesRing(QQ, "t", default_prec=order + 1)
    mser = Ps(Nct) / Ps(Dct)
    a = [mser[l] for l in range(order + 1)]                 # exact QQ Taylor coeffs

    P = sum(a[l] * t**l for l in range(order + 1))
    H = (Nct - P * Dct).shift(-(order + 1))                 # exact: (N - P D)/t^{k+1}
    supH = sum(abs(H[l]) * r_rat**l for l in range(H.degree() + 1)) if H != 0 else QQ(0)
    infD = abs(d0) - sum(abs(Dct[l]) * r_rat**l for l in range(1, Dct.degree() + 1))
    if infD <= 0:
        raise ValueError("denominator may vanish over the ball")
    rem = r_rat**(order + 1) * supH / infD                  # exact rational remainder bound

    return TM([RB(a[l]) for l in range(order + 1)], RB(0).add_error(RB(rem).upper()), r, order)


# -----------------------------------------------------------------------------
# Truncation perturbation (per-function residual bounds, per-entry radii)
# -----------------------------------------------------------------------------

_RATIONAL_M = {"m1": rational_M_m1, "00": rational_M_00}
_FN_KEYS = {"m1": ["phi1", "fp1", "fp2"], "00": ["fp1", "fp2"]}


def _abs_over_ball(elem, c, lam_value, r_rat, Pt):
    """Tight upper bound on |elem(theta)| over |theta-c| <= r_rat, from exact num/den coeffs."""
    N = elem.numerator()
    D = elem.denominator()
    bivar = (N.parent().ngens() == 2)
    if r_rat == 0:                               # point theta: evaluate directly, no substitution
        d0 = D(c, lam_value) if bivar else D(c)
        if d0 == 0:
            raise ValueError("denominator vanishes at theta_mid")
        n0 = N(c, lam_value) if bivar else N(c)
        return abs(n0 / d0)
    t = Pt.gen()
    if bivar:
        Nct = Pt(N(c + t, lam_value)); Dct = Pt(D(c + t, lam_value))
    else:
        Nct = Pt(N(c + t)); Dct = Pt(D(c + t))
    num_sup = (sum(abs(Nct[l]) * r_rat**l for l in range(Nct.degree() + 1))
               if Nct != 0 else QQ(0))
    d0 = Dct[0]
    if d0 == 0:
        raise ValueError("denominator vanishes at theta_mid")
    den_inf = abs(d0) - sum(abs(Dct[l]) * r_rat**l for l in range(1, Dct.degree() + 1))
    if den_inf <= 0:
        raise ValueError("denominator may vanish over the ball")
    return num_sup / den_inf


def eval_series_tight(coeffs, c, lam_value, r_rat, RB, Pt):
    """
    Enclose each K-coefficient over the theta-ball by a centered ball of the tight
    magnitude |.|, from exact num/den coefficients (no eval_coeff, hence no
    wrapping).  Only magnitudes are used downstream, so a centered ball suffices.
    """
    return [RB(0).add_error(RB(_abs_over_ball(ck, c, lam_value, r_rat, Pt)).upper())
            for ck in coeffs]


def delta_per_function(all_res, bits, theta_mid, theta_rad, lam_value, lam_rad=0,
                       b0=QQ(1) / 2, rho=QQ(3) / 4):
    """
    Per-function value/derivative error bounds {(point, branch, fn): (dv, dd)}.

    The residual coefficients are enclosed over the theta-ball with the tight
    num/den bound (eval_series_tight), not eval_coeff: otherwise their interval
    wrapping grows like r and swamps delta* (whereas the true truncation error is
    tiny at large N0).
    """
    RB = RealBallField(bits)
    c = QQ(theta_mid)
    r_rat = QQ(theta_rad)
    Pt = PolynomialRing(QQ, "t")
    b0 = RB(QQ(b0))
    rho = RB(QQ(rho))
    N0, Nres = all_res["_N0"], all_res["_Nres"]
    out = {}
    for point in ["m1", "00"]:
        for branch in ["the", "eht"]:
            blk = all_res[point][branch]
            cp = eval_series_tight(blk["term_pp"], c, lam_value, r_rat, RB, Pt)
            cq = eval_series_tight(blk["term_qq"], c, lam_value, r_rat, RB, Pt)
            Mp, Mq = _RATIONAL_M[point](cp, cq, rho)
            for fn in _FN_KEYS[point]:
                xi_RB = eval_series_tight(blk[fn], c, lam_value, r_rat, RB, Pt)
                ft_RB = eval_series_tight(blk["ftilde"][fn], c, lam_value, r_rat, RB, Pt)
                dv, dd, _ = delta_block(point, xi_RB, ft_RB, Mp, Mq, N0, Nres, b0, rho)
                out[(point, branch, fn)] = (dv, dd)
    return out


def _radius_matrix(dpf, RB):
    """Per-entry radii r_ij, following symbolic_matrix_A's layout A = A_m1 - A_00."""
    v = lambda p, b, f: RB(dpf[(p, b, f)][0].upper())
    d = lambda p, b, f: RB(dpf[(p, b, f)][1].upper())
    Z = RB(0)
    return [
        [v("m1", "the", "phi1"), Z,
         v("m1", "the", "fp1") + v("00", "the", "fp1"),
         v("m1", "the", "fp2") + v("00", "the", "fp2")],
        [d("m1", "the", "phi1"), Z,
         d("m1", "the", "fp1") + d("00", "the", "fp1"),
         d("m1", "the", "fp2") + d("00", "the", "fp2")],
        [Z, v("m1", "eht", "phi1"),
         v("m1", "eht", "fp2") + v("00", "eht", "fp2"),
         v("m1", "eht", "fp1") + v("00", "eht", "fp1")],
        [Z, d("m1", "eht", "phi1"),
         d("m1", "eht", "fp2") + d("00", "eht", "fp2"),
         d("m1", "eht", "fp1") + d("00", "eht", "fp1")],
    ]


# -----------------------------------------------------------------------------
# Symbolic matrix and certified determinant
# -----------------------------------------------------------------------------

def build_post(N0, lam_value=None, order=1):
    """Truncated symbolic matrix M~; order is echoed for the downstream det layer."""
    Asym, _ = symbolic_matrix_A(N0 - 1, lam_value=lam_value)
    return Asym, order


def certified_det_post(Asym, order, dpf, bits, theta_mid, theta_rad, lam_value, lam_rad=0):
    """Certified RealBall enclosing det(Mcrit(theta)) for all theta in the ball."""
    RB = RealBallField(bits)
    c = QQ(theta_mid)
    r_rat = QQ(theta_rad)
    r = RB(r_rat)
    Pt = PolynomialRing(QQ, "t")
    n = Asym.nrows()

    TMmat = [[_entry_tm(Asym[i, j], c, lam_value, RB, r, r_rat, order, Pt)
              for j in range(n)] for i in range(n)]
    D_enc = _tm_det(TMmat, r, order, RB).enclose()

    rad = _radius_matrix(dpf, RB)
    S = [sum(abs(TMmat[i][j].enclose()) for j in range(n)) for i in range(n)]
    rho = [sum(rad[i][j] for j in range(n)) for i in range(n)]
    pert = (prod([S[i] + rho[i] for i in range(n)]) - prod([S[i] for i in range(n)])).upper()

    return D_enc.add_error(pert)
