# Certificate: an exact critical value of a septic CM Hecke L-function

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24504453.svg)](https://doi.org/10.5281/zenodo.24504453)

This repository holds the computer certificate and the manuscript for

> Ramanuja, *An exact critical value of a Hecke L-function over Q(ζ₇): removing the rational ambiguity in Deligne's period relation.*

Main theorem: let K = Q(ζ₇) and let Ψ be the conductor-(2) Hecke character of infinity type 2S, with S = {1,4,5}. Then

```
L_K(Ψ, 2) = (49/8) (I₀ I₁ I₂)²  =  π³/(8·7⁴) · ∏_{j=1}^{3} (Γ(j/7)/Γ(1/2 + j/7))²,
I_j = ∫₀¹ t^j (1 − t⁷)^{-1/2} dt.
```

The paper proves that q = L(2)/(343 (I₀I₁I₂)²) satisfies 1792·q ∈ ℤ (Propositions 4.1–4.2). The certificate then proves |1792·q − 32| < 1/100 with rigorous interval arithmetic. Together these force q = 1/56.

## Contents

| Path | Purpose |
|---|---|
| `certificate/certify.py` | The rigorous certificate. Uses only the Python standard library and no floating point. |
| `certificate/certificate_output.txt` | Recorded output of the certificate. |
| `checks/independent_float_check.py` | Independent double-precision check (needs NumPy and SciPy). It is not part of the proof. |
| `manuscript/` | LaTeX source and PDF of the manuscript. |

## Running

```bash
python3 certificate/certify.py                  # about 10 s, Python >= 3.8, no dependencies
python3 checks/independent_float_check.py       # about 20 s, needs numpy and scipy
```

The certificate exits with a nonzero status if any check fails.

## What the certificate checks

**Part A: exact identities in ℤ[ζ₇]** (Sections 2–5 of the paper)
- Unit invariance of Ψ: ν(ζ), P_S(ζ)², ν(1+ζ) and P_S(1+ζ)².
- Ψ((1−ζ)) = −7, the Euler factor at 7.
- Galois covariance of ν on all 49 residue units mod 2.
- The finite Fourier identity (19) on all 64 residues mod 2.
- ((ζ−1)(ζ²−1)(ζ³−1))² = −7ζ⁶, from eq. (7).
- The Galois multipliers in Proposition 4.1.
- The smoothing data of §4.2: N(a₂₉) = 29, N(a₄₃) = 43, A* = −4U, U a unit above 2, and the λ-adic expansion of U.
- The ten tensor coefficients at 7 (table in §4.4).

**Part B: exact Dirichlet coefficients** a_n for n ≤ 10⁴
- A generator is found for every prime ideal of norm ≤ 10⁴ (1234 in all). Each is *verified* by an exact norm computation: an element of norm p^f, with f the residue degree, generates a prime. So the search method does not matter for the proof.
- Local Euler factors are multiplied exactly in ℤ[ζ]. The program checks that each coefficient is a rational integer and that |a_n| ≤ n·d₆(n).

**Part C: rigorous evaluation** (Section 6)
- Every real number is enclosed in an interval with 320-bit fixed-point endpoints, rounded outward.
- π (Machin), log (atanh series), Euler's γ (Euler–Maclaurin), and √2, √7, 2^{−a} (integer roots) all come with explicit remainder bounds.
- The approximate functional equation (23) uses the kernel series (24), truncated at m = 89 with the bound of §6.2, and the outer tail bound (25) with N = 10⁴, t = 12.
- The periods I_j come from the half-interval series of Appendix A with 200 terms.
- Result: `1792·q ∈ [31.99990, 32.00010]`.

## Citation

If you use this code, please cite the paper above and the archived software release:

> Ramanuja, *Certificate for an exact critical value of a Hecke L-function over Q(ζ₇)*, v1.0, Zenodo, 2026. doi:[10.5281/zenodo.24504453](https://doi.org/10.5281/zenodo.24504453)
