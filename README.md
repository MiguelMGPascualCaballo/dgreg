# Supplementary code - *On the linear instability of De Gregorio steady states*

Computer-assisted verification of Lemma `lem:negposjump`: the determinant of the
matching matrix $M_{\lambda,\theta}$ (Definition `def:Mat`) is

$$\det M_{\lambda,\theta} < 0 \quad\text{at } \lambda=\tfrac{56}{100},
\qquad
\det M_{\lambda,\theta} > 0 \quad\text{at } \lambda=\tfrac{60}{100},$$

uniformly for $\theta\in\big[\tfrac13,\tfrac12\big]$. The sign change yields, by the
intermediate value theorem, an eigenvalue $\lambda_\theta\in(0.56,0.60)$ of
$L_\theta$ (Corollary `cor:detzero`), and hence the linear instability of every
excited state $-\sin(nx)$, $n\ge 2$ (Theorem `thm:eig`).

## Requirements

[SageMath](https://www.sagemath.org/). The certified bounds use Sage's
`RealBallField` (Arb interval arithmetic); the exact layer uses
`Frac(QQ[the, lam])`. No other dependencies.

Run inside a Sage session, or with `sage -python`:

```sh
sage -python run_proof.py            # run sanity checks, then certify the theorem
```
```python
# or, interactively in `sage`:
from cert_proof import DEFAULT_LAM_LOW, DEFAULT_N0, default_nres, prove
from verify_residuals import run as run_sanity
run_sanity(N0=DEFAULT_N0, Nres=default_nres(DEFAULT_N0), lam_value=DEFAULT_LAM_LOW)
prove(50, N0=DEFAULT_N0)             # full theorem: all primes via points + interval J
```

## How the verification is organized

The proof separates the **exact symbolic** computation from the single step
where **interval arithmetic** enters.

Internally, the labels `m1` and `00` refer to the singular points `z=-1` and
`z=0`, while the branches `the` and `eht` correspond to `theta` and `1-theta`.

1. **Exact symbolic layer** (`local_fuchs.py`, `cert_residuals.py`) - builds the
   matrix entries and the residual series of the truncated Frobenius solutions
   over $K=\mathrm{Frac}(\mathbb{Q}[\theta,\lambda])$ (or
   $\mathrm{Frac}(\mathbb{Q}[\theta])$ with $\lambda$ fixed). No intervals.
2. **Certified numeric layer** (`cert_eval.py`, `cert_det_post.py`) - substitutes
   $(\theta,\lambda)$ as balls and assembles the certified enclosure of
   $\det M_{\lambda,\theta}$.
3. **Drivers** (`cert_proof.py`) - first run the prime-by-prime reduction, then
   certify the remaining interval by adaptive bisection.

Two parameter conventions used throughout the certified layer:

* $\lambda$ is enclosed as a **thin** ball at each of the two endpoints
  $\tfrac{56}{100}, \tfrac{60}{100}$, never as an interval.
* $\theta$ is treated in two stages. First, for each prime $p<N$, the proof is
  checked at the single point $\theta_p=\tfrac{h_p}p$. Then the remaining primes are
  covered at once by the interval $J=\big[c\pm\tfrac1{2q}\big]$, where $q$ is the
  smallest prime $\ge N$. Only this interval step is **subdivided** by
  bisection, when a ball makes some coefficient denominator straddle a pole or
  leaves the sign undecided.

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
- `default_parameter_matrices`, `specialize_terms` - the specialized coefficient
  vectors `term_pp` $=(c^p_i)$, `term_qq` $=(c^q_j)$.
- `local_coeffs_at_m1`, `local_coeffs_at_00` - the Fuchsian normal-form
  coefficients $p,q$ and affine forcings $A_1,A_2$ at $z=-1$ and $z=0$
  (`eq:op-m1`, `eq:op-00`).
- `hom_sol_fro_const` - Frobenius series, recurrences `rec:0`/`rec:1`. The
  argument `sol_order=N0` stops the recursion at the truncation order (exact for
  the residual, which never reads past $N_0-1$).
- `particular_sol_r1_is_0` - particular solution at $z=-1$ by the Wronskian
  (Lemma `lem:loc:aff-1`, `def:Fphol-1`).
- `construct_solutions_when_diff_is_integer_formal` - the resonant case at $z=0$
  (root difference $2$): $\phi_1$, $\phi_2$ (reduction of order, log term), and
  the two particular solutions (Lemmas `lem:loc:0`, `lem:loc:aff0`,
  `def:Fphol0`).
- `symbolic_matrix_A` - assembles $M_{\lambda,\theta}=A_{-1}-A_{0}$ (Definition
  `def:Mat`).
- `_apply_operator_r` - the defect $D=G-\mathcal L_r[\tilde f]$ behind the
  residual (`def:appB:R`).

**`cert_residuals.py`** - exact residual series.
- `all_res_sym(Nres, N0, lam_value=None)` - for both singular points
  and both branches $\theta^\pm$, the residual coefficients $\xi_k$
  (`def:appB:R`) of each matrix function, exact in $(\theta,\lambda)$. Because
  $\tilde f$ matches the solution to order $N_0$, $\xi_k=0$ for $k<N_0$ and is
  supported on $N_0\le k\le N_{\mathrm{res}}$. Also stores `ftilde` (the
  $\tilde f_m$), `term_pp`, `term_qq`.

**`cert_eval.py`** - ball substitution and certified norms (the only place
intervals enter the norms).
- `make_balls`, `eval_coeff`, `eval_series` - enclose $K$-coefficients at the
  ball point, raising on a denominator that contains $0$ (so bisection stays
  honest).
- `L_bound` - the contraction constant $\ell$ from the **analytic** sup-bounds
  (Lemmas `lem:sup:00`, `lem:sup:-1`): $\ell\le \tfrac4{N_0}+\tfrac8{N_0(N_0-1)}$ at $z=0$,
  $\ell\le \tfrac8{N_0}+\tfrac{24}{N_0(N_0-1)}$ at $z=-1$. (No Cauchy tail is needed for
  $\ell$.)
- `rational_M_m1`, `rational_M_00` - the Cauchy sup-bounds $M_p(\rho),M_q(\rho)$
  (Lemmas `lem:sup:Mbound:m1`, `lem:tails:Mbound:00`).
- `ftilde_norms` - $C_{\mathrm{val}}, C_{\mathrm{der}}$ (Lemma `lem:tails:xi`).
- `xi_tails` - the $k>N_{\mathrm{res}}$ Cauchy tails of the residual norms
  (Lemma `lem:tails:xi`).
- `norm_AN0`, `norm_deriv` - the finite parts ($N_0\le k\le N_{\mathrm{res}}$) of
  the residual norms (Lemma `lem:sec_ord:LS`).
- `delta_block` - the per-function $(\delta_f,\delta'_f)$ from `appB:Linfbound` /
  `appB:Eprimebound`.
**`cert_det_post.py`** - certified enclosure of $\det M_{\lambda,\theta}$ over a
$\theta$-ball, via **Taylor models** in $t=\theta-\theta_{\mathrm{mid}}$ built
from each entry's exact numerator/denominator (so the determinant cancellation
happens in $\mathbb{Q}$, before intervals).
- `delta_per_function` - per-`(point, branch, fn)` truncation bounds
  $\big(\delta_f,\delta'_f\big)$, enclosed with the tight num/den magnitude
  (`eval_series_tight`) to avoid interval wrapping.
- `TM`, `_tm_det`, `_entry_tm` - the Taylor-model class, cofactor determinant,
  and per-entry model.
- `_radius_matrix` - per-entry truncation radii, in the layout of
  `symbolic_matrix_A`.
- `build_post` - the truncated symbolic matrix $M^{\rm ap}$ ($=$
  `symbolic_matrix_A(N0-1)`).
- `certified_det_post` - the certified `RealBall` containing
  $\det M_{\lambda,\theta}$ for all $\theta$ in the ball: Taylor-model
  determinant plus a Hadamard-style perturbation
  $\prod_i(S_i+\rho_i)-\prod_i S_i$ for the truncation gap.

**`cert_proof.py`** - top-level drivers.
- `verify_det_sign` - certifies $\mathrm{sign}\cdot\det M_{\lambda,\theta}>0$ for
  all $\theta\in[\theta_{\mathrm{lo}},\theta_{\mathrm{hi}}]$ by adaptive
  bisection (accept / refine on undecided sign or pole straddle / raise on wrong
  sign).
- `prove(N, ...)` - the full theorem. Prime-divisor reduction (it suffices to
  treat prime $n$): primes $p<N$ are checked at the single point
  $\theta_p=\tfrac{h_p}p$; all primes $p\ge N$ are covered at once on the interval
  $J=\big[c\pm\tfrac1{2q}\big]$ of length $\tfrac1q$, where $c$ is `center` and $q$ is the smallest prime
  $\ge N$.

### Auxiliary (not needed for the proof)

| File | Purpose |
|---|---|
| `verify_residuals.py` | Exact-layer sanity checks: term counts, residual support ($\xi_k=0$ for $k<N_0$), and truncation stability across $N_{\mathrm{res}}$. |
| `run_proof.py` | Convenience runner that first calls `run_sanity` at `lambda = DEFAULT_LAM_LOW`, then `prove`, with timings. |

## Parameters

| Name | Meaning | Default / constraint |
|---|---|---|
| `N0` | matching / truncation order of $f^{\rm ap}$ | $\ge 11$ (contraction needs $N_0\ge6$ at $z=0$, $N_0\ge11$ at $z=-1$) |
| `Nres` | residual order, $N_{\mathrm{res}}>N_0$ | $2N_0$ |
| `bits` | `RealBallField` precision | `200` |
| `rho` | Cauchy radius $\rho\in\big(\tfrac12,1\big)$ | $\tfrac34$ |
| `b0` | local evaluation point ($z=x_0=-\tfrac12 \leftrightarrow x=\tfrac12$) | $\tfrac12$ |

## Notes on rigor

* The exact layer carries no intervals; substitution to `RealBallField` is the
  single rigorous step, in `cert_eval.py` / `cert_det_post.py`.
* The proof uses the tight `certified_det_post` based on Taylor models and
  per-function bounds $(\delta_f,\delta'_f)$, propagated entry-wise to the
  matrix.
* The contraction constant $\ell$ uses the analytic sup-bounds of Lemmas
  `lem:sup:00` and `lem:sup:-1`, which are taken over the real interval
  $x\in\big[0,\tfrac12\big]$.
