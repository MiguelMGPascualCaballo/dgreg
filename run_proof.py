from sage.all import *
from cert_proof import (
    DEFAULT_B0,
    DEFAULT_BITS,
    DEFAULT_CENTER,
    DEFAULT_LAM_LOW,
    DEFAULT_LAM_UPP,
    DEFAULT_N0,
    DEFAULT_RHO,
    default_nres,
    prove,
)
from verify_residuals import run as run_sanity

# run_proof.py
#
# Exact sanity checks (at lambda = 56/100 only), then the certificate of
# Lemma lem:negposjump at lambda = 56/100 and 60/100.


if __name__ == "__main__":
    N = 300          # prime threshold
    N0 = DEFAULT_N0
    Nres = default_nres(N0)
    run_sanity(N0=N0, Nres=Nres, lam_value=DEFAULT_LAM_LOW)
    prove(N=N,
          N0=N0,
          Nres=Nres,
          bits=DEFAULT_BITS,
          center=DEFAULT_CENTER,
          lam_low=DEFAULT_LAM_LOW,
          lam_upp=DEFAULT_LAM_UPP,
          rho=DEFAULT_RHO,
          b0=DEFAULT_B0)
