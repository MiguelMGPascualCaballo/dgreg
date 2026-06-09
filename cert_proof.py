from sage.all import *
from collections import deque
from time import perf_counter

# cert_proof.py
#
# Top-level computer-assisted verification of Lemma lem:negposjump:
#
#     det(Mcrit) < 0  at lambda = 56/100   and   det(Mcrit) > 0  at lambda = 60/100,
#
# uniformly over theta in [1/3, 1/2].  The exact symbolic residuals and matrix are
# built once per lambda; theta is then certified by adaptive bisection, the only
# layer where ball arithmetic and subdivision happen.
#
# A single theta ball covering all of [1/3, 1/2] does not work: some coefficient
# denominators straddle a pole and eval_coeff raises.  That raise is the trigger
# to bisect, exactly as in BHTW's max_prev_esti (accept / reject / refine).

from cert_residuals import all_res_sym
from cert_eval import L_bound
from cert_det_post import build_post, delta_per_function, certified_det_post

DEFAULT_N0 = 31
DEFAULT_BITS = 200
DEFAULT_CENTER = QQ(5) / 12
DEFAULT_LAM_LOW = QQ(56) / 100
DEFAULT_LAM_UPP = QQ(60) / 100
DEFAULT_RHO = QQ(3) / 4
DEFAULT_B0 = QQ(1) / 2


def default_nres(N0):
    return 2 * N0


def _post_det(all_res, Asym, order, bits, theta_mid, theta_rad, lam_value,
              rho=QQ(3) / 4, b0=QQ(1) / 2):
    """det(Mcrit) over the theta-ball via the tight a-posteriori enclosure."""
    dpf = delta_per_function(all_res, bits, theta_mid, theta_rad, lam_value, 0,
                             b0=b0, rho=rho)
    return certified_det_post(Asym, order, dpf, bits, theta_mid, theta_rad,
                              lam_value, 0)


def verify_det_sign(sign, lam_value, all_res, Asym, order, N0, Nres, bits,
                    theta_lo=QQ(1) / 3, theta_hi=QQ(1) / 2,
                    rho=QQ(3) / 4, b0=QQ(1) / 2,
                    min_width=QQ(1) / 2**40, max_intervals=2**20,
                    print_every=16, verbose=False):
    """
    Certify sign * det(Mcrit) > 0 for all theta in [theta_lo, theta_hi] at the
    fixed lambda, by adaptive bisection.  sign = -1 asks for det < 0, +1 for > 0.

    Per subinterval: enclose delta* and det(Mcrit).  Accept if the det ball has
    the required sign; refine if the sign is undetermined or a denominator
    straddled a pole; raise if the wrong sign is proven or the interval gets too
    narrow (so a failure or an insufficient N0 is never silent).
    """
    # Contraction is theta-independent, so check it once: bisecting theta could
    # never repair a too-small N0, it would just refine down to min_width.
    for point in ["m1", "00"]:
        if not (L_bound(point, N0) < 1):
            raise ValueError("contraction not certified at %s for N0=%d "
                             "(need N0 >= 6 at z=0, N0 >= 11 at z=-1)" % (point, N0))

    # Pre-flight: probe det at a few point thetas (thin balls).  At a point theta
    # the only error left is delta*, so if det cannot be signed there, refining
    # the interval cannot help -- the residual floor is too high.  Fail fast with
    # "increase N0" instead of bisecting down to min_width.
    n_probe = 8
    for i in range(n_probe + 1):
        theta = QQ(theta_lo) + (QQ(theta_hi) - QQ(theta_lo)) * QQ(i) / n_probe
        try:
            det = _post_det(all_res, Asym, order, bits, theta, 0, lam_value, rho=rho, b0=b0)
        except ValueError:
            continue                      # pole exactly at this probe theta; the loop will handle it
        det_signed = det if sign > 0 else -det
        if det_signed < 0:
            raise RuntimeError("det has the wrong sign at theta=%s (lambda=%s)"
                               % (theta, lam_value))
        if not (det_signed > 0):
            raise RuntimeError("N0=%d too small: det cannot be signed at the point "
                               "theta=%s (delta* dominates); increase N0"
                               % (N0, theta))

    # Each work item carries its bisection depth.  "covered" is the total width
    # of accepted subintervals, so covered/total is the certified fraction of
    # [theta_lo, theta_hi] -- the natural progress bar for a depth-first sweep.
    total = QQ(theta_hi) - QQ(theta_lo)
    work = deque([(QQ(theta_lo), QQ(theta_hi), 0)])
    accepted = 0
    covered = QQ(0)
    finest_depth = 0
    step = 0
    while work:
        step += 1
        a, b, depth = work.pop()
        width = b - a
        if width < min_width:
            raise RuntimeError("interval [%s, %s] too narrow; increase N0 or bits" % (a, b))
        finest_depth = max(finest_depth, depth)
        theta_mid, theta_rad = (a + b) / 2, width / 2

        try:
            det = _post_det(all_res, Asym, order, bits, theta_mid, theta_rad,
                            lam_value, rho=rho, b0=b0)
            det_signed = det if sign > 0 else -det
        except ValueError:
            det, det_signed = None, None      # pole straddle: subdivide

        if det_signed is not None and det_signed > 0:
            accepted += 1
            covered += width
            status = "accept"
        elif det_signed is not None and det_signed < 0:
            raise RuntimeError("det has the wrong sign on theta in [%s, %s] (lambda=%s)"
                               % (a, b, lam_value))
        else:
            mid = (a + b) / 2
            work.append((a, mid, depth + 1))
            work.append((mid, b, depth + 1))
            status = "pole -> split" if det is None else "undecided -> split"

        if accepted + len(work) > max_intervals:
            raise RuntimeError("too many subdivisions (> %d)" % max_intervals)

        if verbose and step % print_every == 0:
            pct = (100 * covered / total).floor()        # exact integer percent, no floats
            msg = ("    cov %3d%% | acc %d  pend %d  depth %d | [%s, %s] | %s"
                   % (pct, accepted, len(work), depth, a, b, status))
            if det is not None:
                msg += "  det=%s" % det
            print(msg)

    print("    certified: 100%% coverage over %d subintervals (finest depth %d)"
          % (accepted, finest_depth))
    return True


def prove(N, N0=DEFAULT_N0, Nres=None, bits=DEFAULT_BITS, center=DEFAULT_CENTER,
          lam_low=DEFAULT_LAM_LOW, lam_upp=DEFAULT_LAM_UPP,
          rho=DEFAULT_RHO, b0=DEFAULT_B0, verbose=False):
    """
    Certify that every n-fold De Gregorio steady state (n >= 2) is linearly unstable.

    Prime-divisor reduction: it suffices to treat prime n.  If n = p*m with p prime,
    then theta = h/p = (h*m)/n is an unfold parameter of L_n (l = h*m), so an
    unstable theta = h/p in [1/3, 1/2] for the prime p makes L_n unstable too;
    composites come for free.  For each prime p we need one theta = h/p in [1/3,1/2]
    with lambda_theta in (56/100, 60/100), i.e. det(Mcrit) < 0 at 56/100 and > 0 at
    60/100.

    This splits the (infinitely many) primes at N, the only lever:
      * primes p < N (= prime_range(N)) are checked at a single point theta_p = h_p/p,
        with h_p the interior choice nearest `center`;
      * all primes p >= N are covered at once by certifying the sign of det on the
        interval J = [center - 1/(2q), center + 1/(2q)] of length 1/q, where q is the
        smallest prime >= N.  Since |J| = 1/q >= 1/p, the interval [p*center +/- 1/2]
        has length >= 1, so it contains an integer h, i.e. some h/p lies in J.

    Returns True; raises on the first failure (wrong sign, or N0 too small so that
    delta* dominates even at a point).
    """
    if Nres is None:
        Nres = default_nres(N0)
    order = 1                                     # det enclosure order (fixed; see cert_det_post)
    primes = list(prime_range(N))                 # primes p < N, handled as points
    q = next_prime(N - 1)                         # smallest prime >= N, the first one J must cover
    half = QQ(1) / (2 * q)
    a, b = center - half, center + half           # J, of length 1/q
    if a < QQ(1) / 3 or b > QQ(1) / 2:
        raise ValueError("J = [%s, %s] leaves [1/3, 1/2]; raise N or move center" % (a, b))

    def theta_of(p):
        lo, hi = (QQ(p) / 3).ceil(), (QQ(p) / 2).floor()
        h = (QQ(p) * center + QQ(1) / 2).floor()
        return QQ(max(lo, min(hi, h))) / p

    t_all = perf_counter()
    for lam, sign, want in [(lam_low, -1, "< 0"), (lam_upp, +1, "> 0")]:
        print("=" * 60)
        print("lambda = %s   (need det %s)" % (lam, want))
        t = perf_counter()
        all_res = all_res_sym(Nres, N0, lam_value=lam)
        Asym, _ = build_post(N0, lam, order=order)
        print("  residuals + matrix (N0=%d, Nres=%d) built in %.1fs"
              % (N0, Nres, perf_counter() - t))

        # (1) primes p < N, each at the point theta_p
        t = perf_counter()
        for p in primes:
            theta = theta_of(p)
            det = _post_det(all_res, Asym, order, bits, theta, 0, lam, rho=rho, b0=b0)
            det_signed = det if sign > 0 else -det
            if det_signed < 0:
                raise RuntimeError("wrong sign at prime p=%d (theta=%s, lambda=%s): det=%s"
                                   % (p, theta, lam, det))
            if not (det_signed > 0):
                raise RuntimeError("N0=%d too small at prime p=%d (theta=%s): det=%s"
                                   % (N0, p, theta, det))
            if verbose:
                print("    p=%-6d theta=%-10s det=%s" % (p, theta, det))
        print("  %d primes < %d signed at points in %.1fs"
              % (len(primes), N, perf_counter() - t))

        # (2) all primes p >= N at once, on the interval J
        t = perf_counter()
        print("  covering primes >= %d on J = [%s, %s] (length 1/%d) ..." % (N, a, b, q))
        verify_det_sign(sign, lam, all_res, Asym, order, N0, Nres, bits,
                        theta_lo=a, theta_hi=b, rho=rho, b0=b0, verbose=verbose)
        print("  J certified in %.1fs" % (perf_counter() - t))

    print("=" * 60)
    print("PASS: every n-fold steady state (n >= 2) is unstable  (total %.1fs)"
          % (perf_counter() - t_all))
    return True
