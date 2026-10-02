import sys
import os
from time import perf_counter

from sage.all import QQ

# run_h1_metrics.py
#
# Driver for Lemma lem:h1:core:cert, r = 11/10, 200 bits:
#   (i)  cert_near_0.cover_near_0_region, s=1, X=0, m=8, on (0, 13/40];
#   (ii) cert_away_0.cover_away_0_region, m=4, on [13/40, 1/2].
# Both coverings are recomputed on every run; no state is stored.
#
# Usage:
#     sage -python run_h1_metrics.py          # both full coverings, always fresh
#     sage -python run_h1_metrics.py --smoke  # compatibility alias: same full run

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import cert_near_0 as near_0
import cert_away_0 as away_0

BITS = 200
NEAR_0_M = 8              # m in part (i)
RATE = QQ(11) / 10        # r = omega, both parts
THETA_SPLIT = QQ(13) / 40

def matrix_zero(n):
    import numpy as np
    return np.zeros((n, n))


def run(verbose=True, smoke=False):
    t0 = perf_counter()
    print("=" * 64)
    print("H^1 metric certificates (Lemma lem:h1:core:cert)%s"
          % ("  [SMOKE]" if smoke else ""))

    print("-" * 64)
    print("cert_near_0.cover_near_0_region, s=1, om=%s, on (0, %s]"
          % (RATE, THETA_SPLIT))
    if not near_0.cover_near_0_region(matrix_zero(2 * NEAR_0_M + 1), RATE, 1,
                                      a=THETA_SPLIT, m=NEAR_0_M, bits=BITS,
                                      verbose=verbose):
        raise RuntimeError("near_0 H^1 covering was not certified")

    print("-" * 64)
    print("cert_away_0.cover_away_0_region, r=%s, on [%s, 1/2]" % (RATE, THETA_SPLIT))
    if not away_0.cover_away_0_region(THETA_SPLIT, QQ(1) / 2, r=RATE, m=4, bits=BITS,
                                  verbose=verbose):
        raise RuntimeError("away_0 H^1 covering was not certified")

    print("=" * 64)
    print("PASS: H^1 metric certified on (0, 1/2]  (total %.1fs)"
          % (perf_counter() - t0))


if __name__ == "__main__":
    run(smoke="--smoke" in sys.argv)
