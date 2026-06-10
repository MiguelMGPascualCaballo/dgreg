from sage.all import *

# verify_residuals.py
#
# Sanity checks for the exact residual pipeline, in the spirit of BHTW's verify.py:
# fail loudly, never silently.  A truncated power series forgets its tail, so the
# point here is to confirm we really are carrying the intended number of terms of
# every approximate solution f_approx and of every residual xi.

from cert_residuals import all_res_sym

MATRIX_FUNCS = {"m1": ["phi1", "fp1", "fp2"], "00": ["fp1", "fp2"]}


def check_term_counts(all_res):
    """We compute exactly N0 terms of each f^ap, and the full N0..Nres band of xi."""
    N0, Nres = all_res["_N0"], all_res["_Nres"]

    for point in ["m1", "00"]:
        for branch in ["the", "eht"]:
            blk = all_res[point][branch]
            for fn in MATRIX_FUNCS[point]:
                ###################################
                # the residual list spans coefficients 0..Nres
                if len(blk[fn]) != Nres + 1:
                    raise ValueError(
                        "xi[%s/%s/%s] has %d entries, expected Nres+1=%d"
                        % (point, branch, fn, len(blk[fn]), Nres + 1)
                    )
                ###################################
                # exactly N0 stored truncation coefficients f^ap_0..f^ap_{N0-1}
                if len(blk["fapprox"][fn]) != N0:
                    raise ValueError(
                        "fapprox[%s/%s/%s] has %d terms, expected N0=%d"
                        % (point, branch, fn, len(blk["fapprox"][fn]), N0)
                    )

    print("OK  term counts: N0=%d terms of each f^ap, residual band N0..Nres = %d..%d"
          % (N0, N0, Nres))


def check_residual_support(all_res):
    """xi vanishes exactly (over the field) for k < N0; this fixes the matching order."""
    N0 = all_res["_N0"]

    for point in ["m1", "00"]:
        for branch in ["the", "eht"]:
            blk = all_res[point][branch]
            for fn in MATRIX_FUNCS[point]:
                xi = blk[fn]
                for k in range(N0):
                    if xi[k] != 0:
                        raise ValueError(
                            "xi[%d] != 0 at %s/%s/%s (should vanish below N0)"
                            % (k, point, branch, fn)
                        )

    print("OK  residual support: xi[k]=0 for k<N0 in every block (N0=%d)" % N0)


def check_truncation_stable(N0, Nres_low, Nres_high, lam_value=None):
    """
    Recompute with two residual orders and require the overlap to agree exactly.
    This is the real guard against a silently over-truncated series: if a tail had
    been dropped, the higher-order run would disagree on the shared coefficients.
    """
    if not (N0 < Nres_low < Nres_high):
        raise ValueError("need N0 < Nres_low < Nres_high")

    a = all_res_sym(Nres_low,  N0, lam_value=lam_value)
    b = all_res_sym(Nres_high, N0, lam_value=lam_value)
    for point in ["m1", "00"]:
        for branch in ["the", "eht"]:
            for fn in MATRIX_FUNCS[point]:
                xa, xb = a[point][branch][fn], b[point][branch][fn]
                for k in range(Nres_low + 1):
                    if xa[k] != xb[k]:
                        raise ValueError(
                            "xi mismatch at %s/%s/%s, k=%d between Nres=%d and Nres=%d"
                            % (point, branch, fn, k, Nres_low, Nres_high)
                        )

    print("OK  truncation stable: xi agrees up to k=%d across Nres in {%d, %d}"
          % (Nres_low, Nres_low, Nres_high))


def run(N0=6, Nres=None, lam_value=None):
    """All exact-layer sanity checks.  These probe the pipeline logic, which is
    N0-independent, so a small N0 keeps them cheap; scale N0 upward for the
    actual certified bounds."""
    if Nres is None:
        Nres = 2 * N0
    print("--- verify_residuals (N0=%d, Nres=%d, lam=%s) ---"
          % (N0, Nres, lam_value))
    all_res = all_res_sym(Nres, N0, lam_value=lam_value)
    check_term_counts(all_res)
    check_residual_support(all_res)
    check_truncation_stable(N0, N0 + 1, Nres, lam_value=lam_value)
    return all_res
