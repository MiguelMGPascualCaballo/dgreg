# Supplementary code - linear instability of the De Gregorio steady states

Computer-assisted verification of Lemma `lem:negposjump`: the determinant of the
matching matrix $M_{\lambda,\theta}$ (Definition `def:Mat`) satisfies

$$\det M_{\lambda,\theta} < 0 \quad\text{at } \lambda=\tfrac{56}{100},
\qquad
\det M_{\lambda,\theta} > 0 \quad\text{at } \lambda=\tfrac{60}{100},$$

at the point $\theta_p=h_p/p$ for every prime $p<N=900$, and uniformly on

$$J=\Big[\tfrac5{12}-\tfrac1{2p^\ast},\ \tfrac5{12}+\tfrac1{2p^\ast}\Big],
\qquad p^\ast=907,$$

for the primes $p\ge N$ (Lemma `lem:cover`). The sign change yields, by the
intermediate value theorem, an eigenvalue $\lambda_\theta\in(0.56,0.60)$ of
$L_\theta$ (Corollary `cor:detzero` and Proposition `prop:eigte`), and hence the linear instability of every
excited state $-\sin(nx)$, $n\ge 2$ (Theorem `thm:eig`).

## Requirements

[SageMath](https://www.sagemath.org/). The certified bounds use Sage's
`RealBallField` (Arb interval arithmetic); the exact layer uses
`Frac(QQ[the])` at each fixed $\lambda$. No other dependencies.

Run with the Python interpreter of the Sage installation (inside the Sage
environment, `python run_proof.py`; with the classic Sage launcher,
`sage -python run_proof.py`):

```sh
python run_proof.py                  # sanity checks, then the certificate
```
```python
# or, interactively in `sage`:
from cert_proof import DEFAULT_LAM_LOW, DEFAULT_N0, default_nres, prove
from verify_residuals import run as run_sanity
run_sanity(N0=DEFAULT_N0, Nres=default_nres(DEFAULT_N0), lam_value=DEFAULT_LAM_LOW)
prove(900, N0=DEFAULT_N0)            # primes p < 900 at points, p >= 900 on J
```

## How the verification is organized

The labels `p1` and `00` refer to the singular points `z=1` and `z=0`, with
local coordinates `x=1-z` and `x=z`; the branches `the` and `eht` correspond to
`theta` and `1-theta`. Matching takes place at `z=1/2`, hence `x=1/2` in both
charts. The derivative conversion is `d/dz=-d/dx` at `p1` and `d/dz=d/dx` at
`00`.

1. **Exact symbolic layer** (`local_fuchs.py`, `cert_residuals.py`) - builds the
   truncated matrix entries and the residual coefficients
   $\xi_0,\dots,\xi_{N_{\rm res}}$ over $K=\mathrm{Frac}(\mathbb{Q}[\theta])$
   ($\lambda$ fixed). No intervals.
2. **Certified layer** (`cert_det_post.py`, `cert_eval.py`) - encloses the
   exact data over a $\theta$-ball: residual and approximation coefficients by
   `eval_series_tight`, matrix entries and determinant by Taylor models. The
   bounds of Appendix `sec:appendix:errors` are assembled in `cert_eval.py`.
3. **Driver** (`cert_proof.py`) - point checks for the primes $p<N$, then
   adaptive bisection on $J$.

$\lambda$ is never an interval: the two values $\tfrac{56}{100}$ and
$\tfrac{60}{100}$ are fixed rationals. Only $J$ is subdivided, when the sign is
undecided or an enclosure fails (a denominator lower bound that is not positive
on the ball).

### Dependency graph

```
local_fuchs.py      cert_eval.py
    |   |                |  |
    |   +------------+   |  |
    v                v   v  |
cert_residuals.py   cert_det_post.py
    |                    |
    +--------+-----------+
             v
        cert_proof.py
```

| Module | imports (internal) |
|---|---|
| `local_fuchs.py` | - |
| `cert_eval.py` | - |
| `cert_residuals.py` | `local_fuchs` |
| `cert_det_post.py` | `local_fuchs`, `cert_eval` |
| `cert_proof.py` | `cert_residuals`, `cert_eval`, `cert_det_post` |

## Files

### Certified proof (required)

**`local_fuchs.py`** - exact symbolic engine.
- `make_symbolic_context` - the field $K$ and ring $K[[x]]$.
- `default_parameter_matrices`, `specialize_terms` - the partial fraction
  coefficients `term_pp` $=(c^p_i)$, `term_qq` $=(c^q_j)$ and the affine terms
  (`PQfracform`).
- `local_coeffs_at_p1`, `local_coeffs_at_0` - the normalized local coefficients
  $p,q$ and forcings $g$ at $x=0$ in the charts $x=1-z$ (`eq:op-m1`) and $x=z$.
- `hom_sol_fro_const` - Frobenius series, recurrences `rec:0`/`rec:1`. The
  argument `sol_order=N0` stops the recursion at degree $N_0-1$.
- `particular_sol_r1_is_0_direct` - particular solution at $z=1$ from the
  recurrence `rec:aff`, with $f_0=0$ (Lemma `lem:loc:aff1`).
- `particular_sol_ordinary_direct` - particular solution at $z=0$ from
  `rec:aff`, starting at $k=0$; all coefficients are determined since the
  indicial roots $1-\theta$, $-1-\theta$ are not nonnegative integers
  (Lemma `lem:loc:aff0`).
- `get_analytic_from_p1`, `get_particular_from_00` - values and derivatives at
  the matching point.
- `symbolic_matrix_A` - assembles $M_{\lambda,\theta}=A_{1}-A_{0}$ (Definition
  `def:Mat`).
- `_apply_operator_r` - the defect $g-\mathcal L[f^{\rm ap}]$ behind the
  residual (`def:appB:R`).
- Kept for comparison, not used by the proof: `particular_sol_recurrence`,
  `homogeneous_resonant_factors`,
  `construct_solutions_when_diff_is_integer_formal` (variation of constants
  at $z=0$), `get_analytic_from_00`.

**`cert_residuals.py`** - exact residual data.
- `all_res_sym(Nres, N0, lam_value)` - for both singular points and both
  branches, the residual coefficients $\xi_0,\dots,\xi_{N_{\rm res}}$
  (`def:appB:R`) of each matrix function, $N_{\rm res}\ge N_0$. Since $f^{\rm ap}$
  matches the solution to order $N_0$, $\xi_k=0$ for $k<N_0$. The full residual
  is in general an infinite series; the tail $k>N_{\rm res}$ is bounded
  separately (`xi_tails`). Also stores `fapprox` (the $f^{\rm ap}_m$),
  `term_pp`, `term_qq`.

**`cert_eval.py`** - bounds of Appendix `sec:appendix:errors`.
- `L_bound` - the contraction constant $\ell$ from Lemmas `lem:sup:00`,
  `lem:sup:-1`: $\ell\le \tfrac4{N_0}+\tfrac8{N_0(N_0-1)}$ at $z=0$,
  $\ell\le \tfrac8{N_0}+\tfrac{16}{N_0(N_0-1)}$ at $z=1$ ($N_0\ge10$). Valid for
  $\theta\in(0,1)$ and $\lambda\in\{\tfrac{56}{100},\tfrac{60}{100}\}$ only.
- `rational_M_p1`, `rational_M_00` - $M_p(\rho),M_q(\rho)$
  (Lemmas `lem:cau:Mbound:m1`, `lem:cau:Mbound:00`).
- `forcing_M` - $M_g(\rho)$ of the normalized forcing
  (Lemma `lem:forcing:Mbound`); $M_g=0$ for $\phi_1$.
- `fapprox_norms` - $C_{\mathrm{val}}, C_{\mathrm{der}}$.
- `xi_tails` - the tails $k>N_{\rm res}$ (Lemma `lem:tails:xi`): with
  $S=M_pC_{\rm der}+M_qC_{\rm val}+M_g$ and $r=b_0/\rho$,
  $\dfrac{S}{N_{\rm res}(N_{\rm res}+1)b_0^{N_0}}\dfrac{r^{N_{\rm res}+1}}{1-r}$
  and $\dfrac{S}{N_{\rm res}b_0}\dfrac{r^{N_{\rm res}+1}}{1-r}$.
- `norm_AN0`, `norm_deriv` - the finite parts ($N_0\le k\le N_{\mathrm{res}}$).
- `delta_block` - the per-function $(\delta_f,\delta'_f)$ (Lemma
  `lem:delta-cert`).
- `make_balls`, `eval_coeff`, `eval_series` - direct ball evaluation; not used
  by the proof.

**`cert_det_post.py`** - certified enclosure of $\det M_{\lambda,\theta}$ over a
$\theta$-ball, via Taylor models of order one in $t=\theta-\theta_{\mathrm{mid}}$
built from each entry's exact numerator/denominator. The exact rational Taylor
coefficients are enclosed as balls before the determinant is expanded.
- `eval_series_tight` - centered balls of the magnitude of each coefficient over
  the $\theta$-ball, from exact num/den coefficients.
- `delta_per_function` - per-`(point, branch, fn)` bounds
  $(\delta_f,\delta'_f)$. Checks $0<b_0<\rho<1$ and that the branch parameter
  stays in $[0,1]$; bounds $\theta(2-\theta)$ and $1-\theta^2$ by monotonicity
  for `forcing_M`.
- `TM`, `_tm_det`, `_entry_tm` - the Taylor-model class, cofactor determinant,
  and per-entry model.
- `_radius_matrix` - per-entry radii, in the layout of `symbolic_matrix_A`.
- `build_post` - the truncated matrix $M^{\rm ap}$ ($=$
  `symbolic_matrix_A(N0-1)`).
- `certified_det_post` - the certified `RealBall` containing
  $\det M_{\lambda,\theta}$ on the ball: Taylor-model determinant plus
  $\prod_i(S_i+\rho_i)-\prod_i S_i$ for the truncation gap (entry radii:
  Corollary `cor:matrix-enclose`; bound on the determinant gap: proof of
  Lemma `lem:negposjump`).

**`cert_proof.py`** - driver.
- `verify_det_sign` - certifies $\mathrm{sign}\cdot\det M_{\lambda,\theta}>0$ on
  $[\theta_{\mathrm{lo}},\theta_{\mathrm{hi}}]$ by adaptive bisection (accept /
  refine on undecided sign or failed enclosure / raise on wrong sign or below the
  minimum width). Before that it checks $\ell<1$ in both charts and probes a few
  points; an undecided point raises an error naming `N0` and `bits`.
- `prove(N, ...)` - primes $p<N$ at $\theta_p=h_p/p$ (`theta_of`: $h_p$ nearest
  $p\cdot$`center`, clipped to $[\lceil p/3\rceil,\lfloor p/2\rfloor]$); primes
  $p\ge N$ on $J=[\texttt{center}\pm\tfrac1{2p^\ast}]$, of length $\tfrac1{p^\ast}$.

### Driver and sanity checks

`run_proof.py` is the entry point that reproduces the certificate; the proof
itself is `cert_proof.prove`.

| File | Purpose |
|---|---|
| `verify_residuals.py` | Exact-layer sanity checks: term counts, $\xi_k=0$ for $k<N_0$, and agreement of the stored coefficients across two values of $N_{\mathrm{res}}$. |
| `run_proof.py` | Runs `run_sanity` at $\lambda=\tfrac{56}{100}$ only, then `prove` at both values of $\lambda$. |

## Parameters

| Name | Meaning | Value in `run_proof.py` |
|---|---|---|
| `N` | prime threshold | `900`; $p^\ast=907$ is the smallest prime $\ge N$ (`next_prime(N-1)`) |
| `center` | target of $\theta_p$ and centre of $J$ | $\tfrac{5}{12}$ |
| `N0` | truncation order of $f^{\rm ap}$; $N_0\ge10$ | `31` |
| `Nres` | last stored residual index, $N_{\mathrm{res}}\ge N_0$ | $2N_0=62$ |
| `bits` | `RealBallField` precision | `200` |
| `rho` | Cauchy radius, $b_0<\rho<1$ | $\tfrac34$ |
| `b0` | matching point in the local coordinate | $\tfrac12$ |
| `lam_low`, `lam_upp` | the two values of $\lambda$ | $\tfrac{56}{100}$, $\tfrac{60}{100}$ |

With these values $J=[\tfrac{5}{12}-\tfrac1{1814},\tfrac{5}{12}+\tfrac1{1814}]$.

## Notes on rigor

* The exact layer carries no intervals. Balls enter in `eval_series_tight` and
  the Taylor models of `cert_det_post.py`; `cert_eval.py` combines them into
  $(\delta_f,\delta'_f)$.
* The residual bound is the exact finite sum up to $N_{\rm res}$ plus the
  Cauchy tail of Lemma `lem:tails:xi`, which includes the forcing term $M_g$.
* The contraction constant $\ell$ uses Lemmas `lem:sup:00` and `lem:sup:-1`,
  sup-bounds over $x\in\big[0,\tfrac12\big]$.

## Status

Executed with SageMath 10.9 (conda environment, Python of that environment):
`run_proof.py` passes (N=900, 154 primes plus J, about 32 s).
