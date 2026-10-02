# Supplementary code - *On the instability of De Gregorio excited states*

Computer-assisted proofs of two lemmas of `main.tex` (Appendix `sec:appendix:impl`):

1. **Lemma `lem:negposjump`.** The determinant of the matching matrix
   $M_{\lambda,\theta}$ (Definition `def:Mat`) satisfies
   $\det M_{\lambda,\theta}<0$ at $\lambda=\tfrac{56}{100}$ and
   $\det M_{\lambda,\theta}>0$ at $\lambda=\tfrac{60}{100}$, at
   $\theta_p=\lfloor p/2\rfloor/p$ for every prime $p<N=300$ and on
   $J=[\tfrac12-\tfrac1{600},\tfrac12]$ (Lemma `lem:cover`).
2. **Lemma `lem:h1:core:cert`.** Inequality (`eqn:core:lmi:psd`) with $r=\tfrac{11}{10}$:
   (i) on $(0,\tfrac{13}{40}]$ with $m=8$, (ii) on $[\tfrac{13}{40},\tfrac12]$ with $m=4$.

## Requirements and usage

[SageMath](https://www.sagemath.org/) (`RealBallField`, Arb ball arithmetic;
`numpy`, shipped with Sage, for the zero matrix in `run_h1_metrics.py`).
`cvxpy` is only needed by `cert_near_0.solve_robust_X`, which is not part
of the certificates.

```sh
python run_proof.py        # Lemma lem:negposjump (exact checks, then both signs)
python run_h1_metrics.py   # Lemma lem:h1:core:cert, parts (i) and (ii)
```

Both drivers recompute everything in memory; no state is read or written.

## Determinant certificate (Lemma `lem:negposjump`)

Conventions: keys `p1` and `00` denote $z=1$ and $z=0$, with local coordinates
$x=1-z$ and $x=z$; matching at $z=\tfrac12$, i.e. $x=\tfrac12$ in both charts;
$d/dz=-d/dx$ at `p1` and $d/dz=d/dx$ at `00`. Keys `the`, `eht` denote the
branches $\theta$ and $1-\theta$. $\lambda$ is always a rational point
($\tfrac{56}{100}$ or $\tfrac{60}{100}$).

| Module | Contents |
|---|---|
| `local_fuchs.py` | Exact layer over $K=\mathrm{Frac}(\mathbb{Q}[\theta])$: partial-fraction coefficients (`PQfracform`), local equations (`local_coeffs_at_p1`, `local_coeffs_at_0`), Frobenius recurrence `hom_sol_fro_const` (`rec:0`, `rec:1`), particular solutions `particular_sol_r1_is_0_direct` (Lemma `lem:loc:aff1`) and `particular_sol_ordinary_direct` (Lemma `lem:loc:aff0`), matrix `symbolic_matrix_A`, residual defect `_apply_operator_r`. |
| `cert_residuals.py` | `all_res_sym`: exact residual coefficients $\xi_0,\dots,\xi_{N_{\rm res}}$ (`def:appB:R`), with $\xi_k=0$ for $k<N_0$, plus $f^{\rm ap}$, `term_pp`, `term_qq`. |
| `cert_eval.py` | Bounds of Appendix `sec:appendix:errors`: `L_bound` (Lemmas `lem:sup:00`, `lem:sup:-1`), `rational_M_00`, `rational_M_p1` (Lemmas `lem:cau:Mbound:00`, `lem:cau:Mbound:m1`), `forcing_M` (Lemma `lem:forcing:Mbound`), `fapprox_norms`, `xi_tails` (Lemma `lem:tails:xi`), `norm_AN0`, `norm_deriv`, `delta_block` (Lemma `lem:delta-cert`). |
| `cert_det_post.py` | Ball enclosures: `eval_series_tight` (coefficients over a $\theta$-ball), `delta_per_function`, `_radius_matrix` (Corollary `cor:matrix-enclose`), Taylor models `TM`, `_entry_tm`, `_tm_det`, and `certified_det_post`: Taylor-model $\det M^{\rm ap}$ plus $\prod_j(S_j+\rho_j)-\prod_jS_j$. |
| `cert_proof.py` | `prove`: primes $p<N$ at $\theta_p$, then `verify_det_sign` on $J$ by adaptive bisection. |
| `verify_residuals.py` | Exact checks: term counts, $\xi_k=0$ for $k<N_0$, agreement across two values of $N_{\rm res}$. |
| `run_proof.py` | Runs `verify_residuals.run` at $\lambda=\tfrac{56}{100}$ only, then `prove`. |

Ball arithmetic enters only through `eval_series_tight` and the Taylor models
of `cert_det_post.py`; `make_balls`, `eval_coeff` and `eval_series` in
`cert_eval.py` are not used. The denominators of the matrix entries do not
vanish for $\theta\in(0,1)$; a subinterval is bisected when the determinant
sign is undecided or the lower bound of a denominator over the ball is not
positive.

`L_bound` gives $\ell\le\tfrac4{N_0}+\tfrac8{N_0(N_0-1)}$ at $z=0$ (valid for
$N_0\ge6$) and $\ell\le\tfrac8{N_0}+\tfrac{16}{N_0(N_0-1)}$ at $z=1$ (valid for
$N_0\ge10$), only for $\theta\in(0,1)$ and $\lambda\in\{0.56,0.6\}$.

Parameters (`cert_proof.py`, `run_proof.py`):

| Name | Value | Meaning |
|---|---|---|
| `N` | 300 | prime threshold |
| `N0` | 31 | number of Taylor coefficients of $f^{\rm ap}$ |
| `Nres` | 62 $=2N_0$ | last residual index computed exactly (code requires $N_{\rm res}\ge N_0$) |
| `bits` | 200 | `RealBallField` precision |
| `center` | $\tfrac12$ | gives $\theta_p=\lfloor p/2\rfloor/p$ and $J=[\tfrac{299}{600},\tfrac12]$ |
| `rho` | $\tfrac34$ | Cauchy radius, $b_0<\rho<1$ |
| `b0` | $\tfrac12$ | matching point in local coordinates |
| `lam_low`, `lam_upp` | $\tfrac{56}{100}$, $\tfrac{60}{100}$ | values of $\lambda$ |

## $H^1$ certificate (Lemma `lem:h1:core:cert`)

| Module | Contents |
|---|---|
| `cert_bloch.py` | `certify_maxeig_below`: interval $LDL^\top$ test for $\max\operatorname{eig}(S)<\mu$. The other routines (`certify_A`, `certify_B`, `certify_eigenpair`, `certify_theta`, ...) are not used. |
| `cert_near_0.py` | Part (i): `certify_near_0_lmi`, `cover_near_0_region`. Operator $L^{{\rm fib}\,\Sigma}_{1,\theta}$ of Lemma `lem:rescaled:fiber` (homogeneous weight, mode 0 rescaled), $\gamma=\tfrac12(1+\tfrac1{64})$ (Lemma `lem:tm:tail:hom`); entries built exactly over $\mathrm{Frac}(\mathbb{Q}[\alpha])$, then evaluated at the ball. |
| `cert_away_0.py` | Part (ii): `certify_away_0_lmi`, `cover_away_0_region`. Shifted weight $\sqrt{1+|k+\alpha|^2}$, $\gamma=\tfrac12(1+\tfrac3{16})$ (Lemma `lem:tm:tail`); entries built directly in ball arithmetic. |
| `run_h1_metrics.py` | Driver: $r=\tfrac{11}{10}$, 200 bits, $X=0$, $s=1$; $m=8$ on $(0,\tfrac{13}{40}]$, $m=4$ on $[\tfrac{13}{40},\tfrac12]$. `--smoke` runs the same full computation. |
| `precomputed_near_0_X.py` | Matrix $X$ for the $s=2$ path of `cert_near_0.py` ($m=8$); not imported and not used by the certificates. |

Each covering starts from the whole rational interval and accepts a subinterval
only when all pivots of the interval $LDL^\top$ factorization of the block
matrix $H$ of (`eqn:core:lmi:psd`) are certified positive
(`certify_maxeig_below(-H, 0)`).

## Status

Executed with SageMath 10.9 (conda environment, Python of that environment):
`run_proof.py` passes (N=300, 62 primes plus J, about 63 s) and
`run_h1_metrics.py` passes (about 2 s).
