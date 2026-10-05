/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.RationalDetuningReduction

/-!
# Spectrum of the cosine product-defect operator and the finite rational detuning
  (`lem:supp-exact-rational-detuning`, `eq:supp-exact-cosine-defect`,
  `eq:supp-exact-diagonal-source`, `eq:supp-exact-diagonal-margin`; emergent-spacetime
  manuscript, Appendix `supp:exact-action-audit`)

`Gravity/RationalDetuningReduction.lean` reduced the lemma to the spectral input
`CosineDefectSpectralInput N C`: `ker D_h = constants` and `Σ_{λ ≠ 0} 1/|λ| ≤ C N³` for the
cosine product-defect operator `D_h u = δ(fu) − f δu − (δf) u`, `f = cos 2πx`, on the odd grid
`N = 2m + 1`.  This file proves the spectral input with `C = 10` for every odd `N ≥ 3`
(`cosineDefect_spectralInput`) and closes the lemma for every odd `N > 40`
(`rational_detuning`).

Proof (all steps exact):
* **Fourier modes** (`psi`, `ex`): `δψ_l = iκ̃(l)ψ_l` (`phaseDeriv_psi`, with `κ̃ = kap`
  evaluated in `kap_of_le`, `kap_of_gt`, `kap_zero`), and for `l ≥ 1`
  `D_hψ_l = (i/2)[α(l+1)ψ_{l+1} − α(l)ψ_{l−1}]`, `α(l) = κ̃(l) − κ̃(l−1) − κ̃(1)`
  (`cosineDefect_psi`): in Fourier space `D_h` is the zero-diagonal Jacobi matrix on the path
  `1, …, 2m`, decoupled from the constant mode.
* **Edge weights** (`edge_eq`): `α(p+1) = −K ρ_p ρ_{p+1} g_p` with `K = 8N sin(π/2N)`,
  `ρ_p = sin(πp/2N)` (`p ≤ m`), `sin(π(N−p)/2N)` (`p > m`), `g_p = 1` except on the middle
  edge `p = m`, where `g_m = γ = (4N sin(πm/N) + 2N sin(π/N))/(K ρ_m²)` (trigonometric identity
  `trig_edge`).
* **Explicit inversion of the weighted skew path** (`pathEq_even`, `pathEq_odd`, general
  weights): forward/backward substitution with the products `Γ(q,p) = Π g_k^{±1}`.
* **Kernel** (`cosineDefect_ker`): the path equations with zero right side force all nonconstant
  Fourier coefficients to vanish; Fourier inversion (`fourier_inversion`).
* **Reciprocal-eigenvalue sum**: for an eigenvector `D_h v = μv`, `μ ≠ 0`, with Fourier
  coefficients `c` (`eigen_identity`):
  `N = Σ|c(p)|² = (−2iμ/K) Σ_{i≤j} Γ_{ij}/(ρρ) (c̄_e c_o − c̄_o c_e)`.  The straddling part is
  rank one (`aW`, `bW`), so `1/|μ| ≤ (2/KN)(2 Σ |c_o||c_e|/(ρρ) + 2|γ^{±1} − 1| |A||B|)`
  (`inv_abs_le`).  Summing over an orthonormal eigenbasis with Bessel's inequality for complex
  test vectors (`bessel`, `sum_norm_mul_le`) and the bounds `Σρ_p⁻² ≤ 4N²`
  (`sum_inv_rho_sq_le`), `(Σρ_p⁻¹)² ≤ 2m Σρ_p⁻²`, `K ≥ 8`, `|γ^{±1} − 1| ≤ 8N`
  gives `Σ_{λ≠0} 1/|λ| ≤ 10N³`.
-/

namespace RenewalGeometry
namespace CosineDefectSpectrum

open Finset

noncomputable section

/-! ## Explicit inversion of a weighted skew path -/

section Path

/-- `Γ(q,p) = ∏_{k ∈ [q,p)} g_k^{±1}` (`g_k` for even `k`, `g_k⁻¹` for odd `k`). -/
def pathGamma (g : ℕ → ℝ) (q p : ℕ) : ℝ :=
  ∏ k ∈ Finset.Ico q p, (if Even k then g k else (g k)⁻¹)

theorem pathGamma_succ_top (g : ℕ → ℝ) {q p : ℕ} (h : q ≤ p) :
    pathGamma g q (p + 1) = pathGamma g q p * (if Even p then g p else (g p)⁻¹) := by
  unfold pathGamma
  rw [Finset.prod_Ico_succ_top h]

theorem pathGamma_succ_bot (g : ℕ → ℝ) {q p : ℕ} (h : q < p) :
    pathGamma g q p = (if Even q then g q else (g q)⁻¹) * pathGamma g (q + 1) p := by
  unfold pathGamma
  rw [Finset.prod_eq_prod_Ico_succ_bot h]

theorem pathGamma_self (g : ℕ → ℝ) (q : ℕ) : pathGamma g q q = 1 := by
  simp [pathGamma]

/-- The node equations of the scaled skew path on the nodes `1, …, 2m`. -/
def PathEq (m : ℕ) (g : ℕ → ℝ) (d z : ℕ → ℂ) : Prop :=
  ∀ p, 1 ≤ p → p ≤ 2 * m →
    z p = (if p < 2 * m then (g p : ℂ) * d (p + 1) else 0)
      - (if 1 < p then (g (p - 1) : ℂ) * d (p - 1) else 0)

theorem even_two_mul_add_two (j : ℕ) : Even (2 * j + 2) := ⟨j + 1, by ring⟩
theorem not_even_two_mul_add_one (j : ℕ) : ¬ Even (2 * j + 1) := by
  rw [Nat.not_even_iff_odd]; exact ⟨j, rfl⟩

/-- Forward substitution: the even nodes. -/
theorem pathEq_even {m : ℕ} {g : ℕ → ℝ} (hg : ∀ k, g k ≠ 0) {d z : ℕ → ℂ}
    (h : PathEq m g d z) :
    ∀ j, j < m → d (2 * j + 2) =
      ∑ i ∈ Finset.range (j + 1), (pathGamma g (2 * i + 1) (2 * j + 2) : ℂ) * z (2 * i + 1) := by
  intro j
  induction j with
  | zero =>
    intro hm
    have h1 := h 1 le_rfl (by omega)
    rw [if_pos (by omega), if_neg (by omega), sub_zero] at h1
    simp only [Finset.range_one, Finset.sum_singleton, mul_zero, zero_add]
    rw [show (2 : ℕ) = 1 + 1 from rfl, pathGamma_succ_top g le_rfl, pathGamma_self,
      if_neg (by decide), h1]
    have : (g 1 : ℂ) ≠ 0 := by exact_mod_cast hg 1
    push_cast
    field_simp
  | succ j ih =>
    intro hm
    have hj := ih (by omega)
    have h1 := h (2 * j + 3) (by omega) (by omega)
    rw [if_pos (by omega), if_pos (by omega), show 2 * j + 3 - 1 = 2 * j + 2 by omega,
      show 2 * j + 3 + 1 = 2 * (j + 1) + 2 by omega] at h1
    have hg3 : (g (2 * j + 3) : ℂ) ≠ 0 := by exact_mod_cast hg _
    have hd : d (2 * (j + 1) + 2) = (z (2 * j + 3) + g (2 * j + 2) * d (2 * j + 2)) /
        g (2 * j + 3) := by
      rw [h1]; field_simp; ring
    have hG : ∀ i ∈ Finset.range (j + 1), pathGamma g (2 * i + 1) (2 * (j + 1) + 2)
        = pathGamma g (2 * i + 1) (2 * j + 2) * (g (2 * j + 2) * (g (2 * j + 3))⁻¹) := by
      intro i hi
      have hi' := Finset.mem_range.1 hi
      rw [show 2 * (j + 1) + 2 = 2 * j + 3 + 1 by ring, pathGamma_succ_top g (by omega),
        show 2 * j + 3 = 2 * j + 2 + 1 by ring, pathGamma_succ_top g (by omega),
        if_pos (even_two_mul_add_two j), show 2 * j + 2 + 1 = 2 * (j + 1) + 1 by ring,
        if_neg (not_even_two_mul_add_one _)]
      ring
    have hlast : pathGamma g (2 * (j + 1) + 1) (2 * (j + 1) + 2) = (g (2 * j + 3))⁻¹ := by
      rw [show 2 * (j + 1) + 2 = 2 * (j + 1) + 1 + 1 by ring, pathGamma_succ_top g le_rfl,
        pathGamma_self, if_neg (not_even_two_mul_add_one _), one_mul]
      rfl
    have hR : ∑ i ∈ Finset.range (j + 1 + 1),
        (pathGamma g (2 * i + 1) (2 * (j + 1) + 2) : ℂ) * z (2 * i + 1)
        = ((g (2 * j + 3))⁻¹ : ℂ) * z (2 * j + 3) + ((g (2 * j + 2) : ℂ) * (g (2 * j + 3))⁻¹) *
          ∑ i ∈ Finset.range (j + 1),
            (pathGamma g (2 * i + 1) (2 * j + 2) : ℂ) * z (2 * i + 1) := by
      have hs : ∑ i ∈ Finset.range (j + 1),
          (pathGamma g (2 * i + 1) (2 * (j + 1) + 2) : ℂ) * z (2 * i + 1)
          = ∑ i ∈ Finset.range (j + 1), ((g (2 * j + 2) : ℂ) * (g (2 * j + 3))⁻¹) *
            ((pathGamma g (2 * i + 1) (2 * j + 2) : ℂ) * z (2 * i + 1)) :=
        Finset.sum_congr rfl fun i hi => by rw [hG i hi]; push_cast; ring
      rw [Finset.sum_range_succ, hs, ← Finset.mul_sum, hlast,
        show 2 * (j + 1) + 1 = 2 * j + 3 by ring]
      push_cast; ring
    rw [hR, hd, hj]
    push_cast
    field_simp

theorem pathGamma_odd_step (g : ℕ → ℝ) {i j : ℕ} (h : i < j) :
    pathGamma g (2 * i + 1) (2 * j + 2)
      = (g (2 * i + 1))⁻¹ * (g (2 * i + 2) * pathGamma g (2 * i + 3) (2 * j + 2)) := by
  rw [pathGamma_succ_bot g (by omega), if_neg (not_even_two_mul_add_one i),
    pathGamma_succ_bot g (by omega), show 2 * i + 1 + 1 = 2 * i + 2 by ring,
    if_pos (even_two_mul_add_two i), show 2 * i + 2 + 1 = 2 * i + 3 by ring]

theorem pathGamma_odd_last (g : ℕ → ℝ) (i : ℕ) :
    pathGamma g (2 * i + 1) (2 * i + 2) = (g (2 * i + 1))⁻¹ := by
  rw [show 2 * i + 2 = 2 * i + 1 + 1 by ring, pathGamma_succ_top g le_rfl, pathGamma_self,
    if_neg (not_even_two_mul_add_one i), one_mul]

/-- Backward substitution: the odd nodes. -/
theorem pathEq_odd {m : ℕ} {g : ℕ → ℝ} (hg : ∀ k, g k ≠ 0) {d z : ℕ → ℂ}
    (h : PathEq m g d z) :
    ∀ i, i < m → d (2 * i + 1) =
      -∑ j ∈ Finset.Ico i m, (pathGamma g (2 * i + 1) (2 * j + 2) : ℂ) * z (2 * j + 2) := by
  suffices H : ∀ k i, i + k + 1 = m → d (2 * i + 1) =
      -∑ j ∈ Finset.Ico i m, (pathGamma g (2 * i + 1) (2 * j + 2) : ℂ) * z (2 * j + 2) by
    intro i hi
    exact H (m - i - 1) i (by omega)
  intro k
  induction k with
  | zero =>
    intro i hi
    have h1 := h (2 * m) (by omega) le_rfl
    rw [if_neg (lt_irrefl _), if_pos (by omega), zero_sub,
      show 2 * m - 1 = 2 * i + 1 by omega] at h1
    rw [show m = i + 1 by omega, Nat.Ico_succ_singleton, Finset.sum_singleton,
      pathGamma_odd_last, show 2 * i + 2 = 2 * m by omega, h1]
    have : (g (2 * i + 1) : ℂ) ≠ 0 := by exact_mod_cast hg _
    push_cast
    field_simp
  | succ k ih =>
    intro i hi
    have hi1 := ih (i + 1) (by omega)
    have h1 := h (2 * i + 2) (by omega) (by omega)
    rw [if_pos (by omega), if_pos (by omega), show 2 * i + 2 - 1 = 2 * i + 1 by omega,
      show 2 * i + 2 + 1 = 2 * (i + 1) + 1 by ring] at h1
    have hg1 : (g (2 * i + 1) : ℂ) ≠ 0 := by exact_mod_cast hg _
    have hd : d (2 * i + 1) = (g (2 * i + 2) * d (2 * (i + 1) + 1) - z (2 * i + 2)) /
        g (2 * i + 1) := by
      rw [h1]; field_simp; ring
    have hs : ∑ j ∈ Finset.Ico (i + 1) m,
        (pathGamma g (2 * i + 1) (2 * j + 2) : ℂ) * z (2 * j + 2)
        = ∑ j ∈ Finset.Ico (i + 1) m, ((g (2 * i + 1) : ℂ)⁻¹ * g (2 * i + 2)) *
          ((pathGamma g (2 * (i + 1) + 1) (2 * j + 2) : ℂ) * z (2 * j + 2)) :=
      Finset.sum_congr rfl fun j hj => by
        rw [pathGamma_odd_step g (by simp at hj; omega),
          show 2 * (i + 1) + 1 = 2 * i + 3 by ring]
        push_cast; ring
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega), hs, ← Finset.mul_sum, pathGamma_odd_last,
      hd, hi1]
    push_cast
    field_simp
    ring

end Path

/-! ## Discrete Fourier modes -/

section Fourier

variable {N : ℕ}

/-- `ex N t = exp(2π i t / N)`. -/
def ex (N : ℕ) (t : ℤ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t / N)

theorem ex_add (a b : ℤ) : ex N (a + b) = ex N a * ex N b := by
  unfold ex; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem ex_N_mul (hN : N ≠ 0) (t : ℤ) : ex N (N * t) = 1 := by
  unfold ex
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have : (2 * Real.pi * Complex.I * ((N * t : ℤ) : ℂ) / N) = t * (2 * Real.pi * Complex.I) := by
    push_cast; field_simp
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

theorem ex_pow (t : ℤ) (n : ℕ) : ex N t ^ n = ex N (t * n) := by
  unfold ex; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

theorem ex_zero : ex N 0 = 1 := by simp [ex]

theorem ex_neg (t : ℤ) : ex N (-t) = starRingEnd ℂ (ex N t) := by
  unfold ex
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal, map_div₀, map_ofNat]

theorem ex_dvd (hN : N ≠ 0) {a b : ℤ} (h : (N : ℤ) ∣ a - b) : ex N a = ex N b := by
  obtain ⟨t, ht⟩ := h
  rw [show a = b + N * t by linarith, ex_add, ex_N_mul hN, mul_one]

/-- Geometric sum of the `N`-th roots of unity. -/
theorem sum_ex (hN : N ≠ 0) (j : ℤ) :
    ∑ x : Fin N, ex N (j * ((x : ℕ) : ℤ)) = if (N : ℤ) ∣ j then (N : ℂ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun x => ex N (j * (x : ℤ)))]
  split_ifs with h
  · obtain ⟨t, rfl⟩ := h
    have : ∀ x : ℕ, ex N (N * t * x) = 1 := fun x => by rw [mul_assoc]; exact ex_N_mul hN _
    simp [this]
  · have hr : ex N j ≠ 1 := by
      intro h1
      unfold ex at h1
      rw [Complex.exp_eq_one_iff] at h1
      obtain ⟨n, hn⟩ := h1
      apply h
      refine ⟨n, ?_⟩
      have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
      have h2 : (2 * Real.pi * Complex.I) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have : (j : ℂ) = N * n := by
        rw [div_eq_iff hN'] at hn
        apply mul_left_cancel₀ h2
        linear_combination hn
      exact_mod_cast this
    have : ∀ x : ℕ, ex N (j * x) = ex N j ^ x := fun x => (ex_pow j x).symm
    simp_rw [this]
    rw [geom_sum_eq hr, ex_pow, mul_comm, ex_N_mul hN, sub_self, zero_div]

/-- The Fourier mode `ψ_l(x) = exp(2π i l x / N)`. -/
def psi (N : ℕ) (l : ℕ) (x : Fin N) : ℂ := ex N ((l : ℤ) * ((x : ℕ) : ℤ))

theorem ofReal_sin_ex (hN : N ≠ 0) (t : ℤ) :
    ((Real.sin (2 * Real.pi * t / N) : ℝ) : ℂ) = (ex N t - ex N (-t)) / (2 * Complex.I) := by
  rw [Complex.ofReal_sin, Complex.sin]
  unfold ex
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have e1 : -(((2 * Real.pi * t / N : ℝ)) : ℂ) * Complex.I
      = 2 * Real.pi * Complex.I * ((-t : ℤ) : ℂ) / N := by push_cast; ring
  have e2 : (((2 * Real.pi * t / N : ℝ)) : ℂ) * Complex.I
      = 2 * Real.pi * Complex.I * ((t : ℤ) : ℂ) / N := by push_cast; ring
  rw [e1, e2]
  field_simp
  rw [Complex.I_sq]
  ring

theorem ofReal_cos_ex (t : ℤ) :
    ((Real.cos (2 * Real.pi * t / N) : ℝ) : ℂ) = (ex N t + ex N (-t)) / 2 := by
  rw [Complex.ofReal_cos, Complex.cos]
  unfold ex
  have e1 : -(((2 * Real.pi * t / N : ℝ)) : ℂ) * Complex.I
      = 2 * Real.pi * Complex.I * ((-t : ℤ) : ℂ) / N := by push_cast; ring
  have e2 : (((2 * Real.pi * t / N : ℝ)) : ℂ) * Complex.I
      = 2 * Real.pi * Complex.I * ((t : ℤ) : ℂ) / N := by push_cast; ring
  rw [e1, e2]

end Fourier

/-! ## The cosine defect on Fourier modes -/

section Defect

open RationalDetuning Matrix

variable {N : ℕ}

/-- The Fourier multiplier `κ̃(l)` of the odd-grid phase derivative on the mode `ψ_l`
(`κ̃(l) = 2N sin(πl/N)` for `1 ≤ l ≤ m`, `-2N sin(π(N-l)/N)` for `m < l < N`). -/
def kap (N : ℕ) (l : ℕ) : ℝ :=
  2 * N * ∑ k ∈ Finset.Icc 1 ((N - 1) / 2), Real.sin (Real.pi * k / N) *
    ((if (N : ℤ) ∣ ((l : ℤ) - k) then 1 else 0) - (if (N : ℤ) ∣ ((l : ℤ) + k) then 1 else 0))

theorem sin_sum_psi (hN : N ≠ 0) (k l : ℕ) (x : Fin N) :
    ∑ y : Fin N, ((Real.sin (2 * Real.pi * k * ((x : ℝ) - y) / N) : ℝ) : ℂ) * psi N l y
      = (N / (2 * Complex.I)) * psi N l x *
        ((if (N : ℤ) ∣ ((l : ℤ) - k) then 1 else 0) -
          (if (N : ℤ) ∣ ((l : ℤ) + k) then 1 else 0)) := by
  have harg : ∀ y : Fin N, (2 * Real.pi * k * ((x : ℝ) - y) / N)
      = 2 * Real.pi * (((k : ℤ) * ((x : ℕ) : ℤ) - (k : ℤ) * ((y : ℕ) : ℤ) : ℤ) : ℝ) / N := by
    intro y; push_cast; ring
  simp_rw [harg, ofReal_sin_ex hN]
  have h1 : ∀ y : Fin N, ex N ((k : ℤ) * ((x : ℕ) : ℤ) - (k : ℤ) * ((y : ℕ) : ℤ)) * psi N l y
      = ex N ((k : ℤ) * ((x : ℕ) : ℤ)) * ex N (((l : ℤ) - k) * ((y : ℕ) : ℤ)) := by
    intro y; unfold psi; rw [← ex_add, ← ex_add]; congr 1; ring
  have h2 : ∀ y : Fin N, ex N (-((k : ℤ) * ((x : ℕ) : ℤ) - (k : ℤ) * ((y : ℕ) : ℤ))) * psi N l y
      = ex N (-((k : ℤ) * ((x : ℕ) : ℤ))) * ex N (((l : ℤ) + k) * ((y : ℕ) : ℤ)) := by
    intro y; unfold psi; rw [← ex_add, ← ex_add]; congr 1; ring
  have hs : ∀ y : Fin N, (ex N ((k : ℤ) * ((x : ℕ) : ℤ) - (k : ℤ) * ((y : ℕ) : ℤ))
      - ex N (-((k : ℤ) * ((x : ℕ) : ℤ) - (k : ℤ) * ((y : ℕ) : ℤ)))) / (2 * Complex.I)
      * psi N l y = (ex N ((k : ℤ) * ((x : ℕ) : ℤ)) * ex N (((l : ℤ) - k) * ((y : ℕ) : ℤ))
        - ex N (-((k : ℤ) * ((x : ℕ) : ℤ))) * ex N (((l : ℤ) + k) * ((y : ℕ) : ℤ)))
        / (2 * Complex.I) := by
    intro y; rw [div_mul_eq_mul_div, sub_mul, h1, h2]
  simp_rw [hs]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_ex hN, sum_ex hN]
  have e1 : (N : ℤ) ∣ (l : ℤ) - k → ex N ((k : ℤ) * ((x : ℕ) : ℤ)) = psi N l x := by
    intro hd; unfold psi; apply ex_dvd hN
    obtain ⟨t, ht⟩ := hd; exact ⟨-(t * (x : ℕ)), by linear_combination (-(x : ℕ) : ℤ) * ht⟩
  have e2 : (N : ℤ) ∣ (l : ℤ) + k → ex N (-((k : ℤ) * ((x : ℕ) : ℤ))) = psi N l x := by
    intro hd; unfold psi; apply ex_dvd hN
    obtain ⟨t, ht⟩ := hd; exact ⟨-(t * (x : ℕ)), by linear_combination (-(x : ℕ) : ℤ) * ht⟩
  by_cases ha : (N : ℤ) ∣ (l : ℤ) - k <;> by_cases hb : (N : ℤ) ∣ (l : ℤ) + k <;>
    simp only [ha, hb, if_true, if_false, e1, e2, mul_zero, sub_zero, zero_sub, sub_self,
      mul_one] <;> field_simp <;> ring


/-- The odd-grid phase derivative acts on `ψ_l` by `i κ̃(l)`. -/
theorem phaseDeriv_psi (hN : N ≠ 0) (l : ℕ) (x : Fin N) :
    ∑ y, ((phaseDeriv N x y : ℝ) : ℂ) * psi N l y = Complex.I * (kap N l : ℂ) * psi N l x := by
  have hentry : ∀ y : Fin N, ((phaseDeriv N x y : ℝ) : ℂ) = ∑ k ∈ Finset.Icc 1 ((N - 1) / 2),
      (-4 : ℂ) * ((Real.sin (Real.pi * k / N) : ℝ) : ℂ) *
        ((Real.sin (2 * Real.pi * k * ((x : ℝ) - y) / N) : ℝ) : ℂ) := by
    intro y
    simp only [phaseDeriv, Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_neg,
      Complex.ofReal_ofNat, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hk : ∀ k : ℕ, ∑ y : Fin N, (-4 : ℂ) * ((Real.sin (Real.pi * k / N) : ℝ) : ℂ) *
      ((Real.sin (2 * Real.pi * k * ((x : ℝ) - y) / N) : ℝ) : ℂ) * psi N l y
      = Complex.I * (2 * N * (((Real.sin (Real.pi * k / N) : ℝ) : ℂ) *
        ((if (N : ℤ) ∣ ((l : ℤ) - k) then 1 else 0) -
          (if (N : ℤ) ∣ ((l : ℤ) + k) then 1 else 0)))) * psi N l x := by
    intro k
    have : ∑ y : Fin N, (-4 : ℂ) * ((Real.sin (Real.pi * k / N) : ℝ) : ℂ) *
        ((Real.sin (2 * Real.pi * k * ((x : ℝ) - y) / N) : ℝ) : ℂ) * psi N l y
        = (-4 : ℂ) * ((Real.sin (Real.pi * k / N) : ℝ) : ℂ) * ∑ y : Fin N,
          ((Real.sin (2 * Real.pi * k * ((x : ℝ) - y) / N) : ℝ) : ℂ) * psi N l y := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
    rw [this, sin_sum_psi hN]
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    field_simp
    rw [Complex.I_sq]
    ring
  calc ∑ y, ((phaseDeriv N x y : ℝ) : ℂ) * psi N l y
      = ∑ y : Fin N, ∑ k ∈ Finset.Icc 1 ((N - 1) / 2), (-4 : ℂ) *
          ((Real.sin (Real.pi * k / N) : ℝ) : ℂ) *
          ((Real.sin (2 * Real.pi * k * ((x : ℝ) - y) / N) : ℝ) : ℂ) * psi N l y := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [hentry y, Finset.sum_mul]
    _ = ∑ k ∈ Finset.Icc 1 ((N - 1) / 2), Complex.I * (2 * N *
          (((Real.sin (Real.pi * k / N) : ℝ) : ℂ) *
          ((if (N : ℤ) ∣ ((l : ℤ) - k) then 1 else 0) -
            (if (N : ℤ) ∣ ((l : ℤ) + k) then 1 else 0)))) * psi N l x := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => hk k
    _ = Complex.I * (kap N l : ℂ) * psi N l x := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum]
        unfold kap
        congr 2
        push_cast
        refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
        split_ifs <;> simp

theorem psi_mul (a b : ℕ) (x : Fin N) : psi N a x * psi N b x = psi N (a + b) x := by
  unfold psi; rw [← ex_add]; congr 1; push_cast; ring

theorem psi_zero (x : Fin N) : psi N 0 x = 1 := by simp [psi, ex_zero]

theorem psi_N (hN : N ≠ 0) (x : Fin N) : psi N N x = 1 := by
  unfold psi; exact ex_N_mul hN _

theorem ex_neg_mul_psi {l : ℕ} (hl : 1 ≤ l) (x : Fin N) :
    ex N (-((x : ℕ) : ℤ)) * psi N l x = psi N (l - 1) x := by
  unfold psi; rw [← ex_add]; congr 1; push_cast [Nat.cast_sub hl]; ring

theorem ex_neg_eq_psi (hN : 1 ≤ N) (x : Fin N) : ex N (-((x : ℕ) : ℤ)) = psi N (N - 1) x := by
  unfold psi; apply ex_dvd (by omega)
  exact ⟨-((x : ℕ) : ℤ), by push_cast [Nat.cast_sub hN]; ring⟩

theorem psi_pred_mul (hN : 1 ≤ N) {l : ℕ} (hl : 1 ≤ l) (x : Fin N) :
    psi N (N - 1) x * psi N l x = psi N (l - 1) x := by
  rw [← ex_neg_eq_psi hN, ex_neg_mul_psi hl]

theorem gridCos_c (y : Fin N) :
    ((gridCos N y : ℝ) : ℂ) = (psi N 1 y + ex N (-((y : ℕ) : ℤ))) / 2 := by
  unfold gridCos
  have : 2 * Real.pi * ((y : ℕ) : ℝ) / N = 2 * Real.pi * ((((y : ℕ) : ℤ)) : ℝ) / N := by
    push_cast; ring
  rw [this, ofReal_cos_ex]
  simp [psi]

theorem cosineDefect_apply (x y : Fin N) :
    cosineDefect N x y = phaseDeriv N x y * gridCos N y - gridCos N x * phaseDeriv N x y
      - (if x = y then (phaseDeriv N *ᵥ gridCos N) x else 0) := by
  simp [cosineDefect, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.diagonal_apply]

/-- `δ f = (iκ̃(1) ψ_1 + iκ̃(N-1) ψ_{N-1})/2` for `f = cos 2πx`. -/
theorem phaseDeriv_gridCos (hN : 1 ≤ N) (x : Fin N) :
    (((phaseDeriv N *ᵥ gridCos N) x : ℝ) : ℂ)
      = (Complex.I * (kap N 1 : ℂ) * psi N 1 x
        + Complex.I * (kap N (N - 1) : ℂ) * psi N (N - 1) x) / 2 := by
  have hN0 : N ≠ 0 := by omega
  simp only [Matrix.mulVec, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul]
  simp_rw [gridCos_c, ex_neg_eq_psi hN]
  rw [← phaseDeriv_psi hN0, ← phaseDeriv_psi hN0, ← Finset.sum_add_distrib, Finset.sum_div]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- **The cosine defect on a Fourier mode**: for `l ≥ 1`,
`D_h ψ_l = (i/2)[(κ̃(l+1) − κ̃(l) − κ̃(1)) ψ_{l+1} + (κ̃(l−1) − κ̃(l) − κ̃(N−1)) ψ_{l−1}]`. -/
theorem cosineDefect_psi (hN : 1 ≤ N) {l : ℕ} (hl : 1 ≤ l) (x : Fin N) :
    ∑ y, ((cosineDefect N x y : ℝ) : ℂ) * psi N l y
      = (Complex.I / 2) * (((kap N (l + 1) - kap N l - kap N 1 : ℝ) : ℂ) * psi N (l + 1) x
        + ((kap N (l - 1) - kap N l - kap N (N - 1) : ℝ) : ℂ) * psi N (l - 1) x) := by
  have hN0 : N ≠ 0 := by omega
  have hsplit : ∀ y : Fin N, ((cosineDefect N x y : ℝ) : ℂ) * psi N l y
      = ((phaseDeriv N x y : ℝ) : ℂ) * ((psi N (l + 1) y + psi N (l - 1) y) / 2)
        - ((gridCos N x : ℝ) : ℂ) * (((phaseDeriv N x y : ℝ) : ℂ) * psi N l y)
        - (if x = y then (((phaseDeriv N *ᵥ gridCos N) x : ℝ) : ℂ) * psi N l x else 0) := by
    intro y
    rw [cosineDefect_apply]
    have hf : ((gridCos N y : ℝ) : ℂ) * psi N l y = (psi N (l + 1) y + psi N (l - 1) y) / 2 := by
      rw [gridCos_c, ← ex_neg_mul_psi hl y, show l + 1 = 1 + l by ring, ← psi_mul]
      ring
    split_ifs with hxy
    · subst hxy
      push_cast
      rw [← hf]; ring
    · push_cast
      rw [← hf]; ring
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, if_pos (Finset.mem_univ _),
    ← Finset.mul_sum]
  simp_rw [mul_div_assoc', mul_add, add_div, Finset.sum_add_distrib, ← Finset.sum_div]
  rw [phaseDeriv_psi hN0, phaseDeriv_psi hN0, phaseDeriv_psi hN0, phaseDeriv_gridCos hN,
    gridCos_c, ex_neg_eq_psi hN]
  have e1 : psi N 1 x * psi N l x = psi N (l + 1) x := by rw [psi_mul, add_comm]
  have e2 : psi N (N - 1) x * psi N (l - 1 + 1) x = psi N (l - 1) x := by
    rw [Nat.sub_add_cancel hl, psi_pred_mul hN hl]
  have e3 : psi N (l + 1) x = psi N 1 x * psi N l x := e1.symm
  have e4 : psi N (l - 1) x = psi N (N - 1) x * psi N l x := (psi_pred_mul hN hl x).symm
  rw [e3, e4]
  push_cast
  ring

/-! ### Values of the multiplier `κ̃` -/

theorem dvd_sub_iff {m l k : ℕ} (hN : N = 2 * m + 1) (hl : l ≤ N) (hk1 : 1 ≤ k) (hkm : k ≤ m) :
    (N : ℤ) ∣ ((l : ℤ) - k) ↔ k = l := by
  constructor
  · intro h
    have h0 := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> push_cast <;> omega)
    omega
  · rintro rfl; simp

theorem dvd_add_iff {m l k : ℕ} (hN : N = 2 * m + 1) (hl : l ≤ N) (hk1 : 1 ≤ k) (hkm : k ≤ m) :
    (N : ℤ) ∣ ((l : ℤ) + k) ↔ k = N - l := by
  constructor
  · intro h
    have h' : (N : ℤ) ∣ ((l : ℤ) + k - N) := by
      have := dvd_sub h (dvd_refl (N : ℤ)); exact this
    have h0 := Int.eq_zero_of_abs_lt_dvd h' (by rw [abs_lt]; constructor <;> push_cast <;> omega)
    omega
  · intro h
    refine ⟨1, ?_⟩
    have : (k : ℤ) = N - l := by rw [h]; push_cast [Nat.cast_sub hl]; ring
    rw [this]; ring

/-- Closed form of `κ̃` on `0 ≤ l ≤ N`. -/
theorem kap_eq {m l : ℕ} (hN : N = 2 * m + 1) (hl : l ≤ N) :
    kap N l = 2 * N * ((if l ∈ Finset.Icc 1 m then Real.sin (Real.pi * l / N) else 0)
      - (if N - l ∈ Finset.Icc 1 m then Real.sin (Real.pi * ((N - l : ℕ) : ℝ) / N) else 0)) := by
  unfold kap
  have hm : (N - 1) / 2 = m := by omega
  rw [hm]
  congr 1
  have : ∀ k ∈ Finset.Icc 1 m, Real.sin (Real.pi * k / N) *
      ((if (N : ℤ) ∣ ((l : ℤ) - k) then (1 : ℝ) else 0) -
        (if (N : ℤ) ∣ ((l : ℤ) + k) then 1 else 0))
      = (if l = k then Real.sin (Real.pi * k / N) else 0)
        - (if N - l = k then Real.sin (Real.pi * k / N) else 0) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [if_congr (dvd_sub_iff hN hl hk.1 hk.2) rfl rfl,
      if_congr (dvd_add_iff hN hl hk.1 hk.2) rfl rfl]
    by_cases h1 : k = l <;> by_cases h2 : k = N - l
    · rw [if_pos h1, if_pos h2, if_pos h1.symm, if_pos h2.symm]; ring
    · rw [if_pos h1, if_neg h2, if_pos h1.symm, if_neg (Ne.symm h2)]; ring
    · rw [if_neg h1, if_pos h2, if_neg (Ne.symm h1), if_pos h2.symm]; ring
    · rw [if_neg h1, if_neg h2, if_neg (Ne.symm h1), if_neg (Ne.symm h2)]; ring
  rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]

theorem kap_of_le {m l : ℕ} (hN : N = 2 * m + 1) (h1 : 1 ≤ l) (hlm : l ≤ m) :
    kap N l = 2 * N * Real.sin (Real.pi * l / N) := by
  rw [kap_eq hN (by omega), if_pos (Finset.mem_Icc.2 ⟨h1, hlm⟩),
    if_neg (by rw [Finset.mem_Icc]; omega), sub_zero]

theorem kap_of_gt {m l : ℕ} (hN : N = 2 * m + 1) (hlm : m < l) (hl : l ≤ N) :
    kap N l = -(2 * N * Real.sin (Real.pi * ((N - l : ℕ) : ℝ) / N)) := by
  rw [kap_eq hN hl, if_neg (by rw [Finset.mem_Icc]; omega)]
  by_cases h : l = N
  · subst h; simp
  · rw [if_pos (Finset.mem_Icc.2 ⟨by omega, by omega⟩)]; ring

theorem kap_zero {m : ℕ} (hN : N = 2 * m + 1) : kap N 0 = 0 := by
  rw [kap_eq hN (by omega), if_neg (by simp), if_neg (by rw [Finset.mem_Icc]; omega)]; ring

theorem kap_N_sub_one {m : ℕ} (hN : N = 2 * m + 1) (hm : 1 ≤ m) : kap N (N - 1) = -kap N 1 := by
  rw [kap_of_gt hN (by omega) (by omega), kap_of_le hN le_rfl hm,
    show N - (N - 1) = 1 by omega]

/-! ### The edge weights of the Fourier path -/

/-- `σ_k = sin(πk/(2N))`. -/
def sig (N k : ℕ) : ℝ := Real.sin (Real.pi * k / (2 * N))

/-- `K = 8N sin(π/(2N))`. -/
def Kc (N : ℕ) : ℝ := 8 * N * Real.sin (Real.pi / (2 * N))

/-- The node scaling `ρ_p = σ_p` for `p ≤ m`, `σ_{N-p}` for `p > m`. -/
def rho (N m p : ℕ) : ℝ := if p ≤ m then sig N p else sig N (N - p)

/-- The middle-edge factor `γ = (4N sin(πm/N) + 2N sin(π/N)) / (K σ_m²)`. -/
def gam (N m : ℕ) : ℝ :=
  (4 * N * Real.sin (Real.pi * m / N) + 2 * N * Real.sin (Real.pi / N)) / (Kc N * sig N m ^ 2)

/-- The edge factors: `γ` on the middle edge `m`, `1` elsewhere. -/
def gw (N m p : ℕ) : ℝ := if p = m then gam N m else 1

theorem trig_edge (a b : ℝ) :
    Real.sin (2 * a) - Real.sin (2 * a - 2 * b) - Real.sin (2 * b)
      = -4 * Real.sin a * Real.sin b * Real.sin (a - b) := by
  rw [Real.sin_sub, Real.sin_sub, Real.sin_two_mul, Real.sin_two_mul, Real.cos_two_mul,
    Real.cos_two_mul]
  linear_combination (-4 * Real.sin a * Real.cos a) * Real.sin_sq_add_cos_sq b
    + (4 * Real.sin b * Real.cos b) * Real.sin_sq_add_cos_sq a

theorem interior_edge (hN : N ≠ 0) (q : ℕ) :
    2 * N * (Real.sin (Real.pi * ((q + 1 : ℕ) : ℝ) / N) - Real.sin (Real.pi * (q : ℝ) / N)
      - Real.sin (Real.pi / N)) = -(Kc N * sig N q * sig N (q + 1)) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have := trig_edge (Real.pi * ((q + 1 : ℕ) : ℝ) / (2 * N)) (Real.pi / (2 * N))
  have e1 : 2 * (Real.pi * ((q + 1 : ℕ) : ℝ) / (2 * N)) = Real.pi * ((q + 1 : ℕ) : ℝ) / N := by
    field_simp
  have e2 : 2 * (Real.pi * ((q + 1 : ℕ) : ℝ) / (2 * N)) - 2 * (Real.pi / (2 * N))
      = Real.pi * (q : ℝ) / N := by push_cast; field_simp; ring
  have e3 : 2 * (Real.pi / (2 * N)) = Real.pi / N := by field_simp
  have e4 : Real.pi * ((q + 1 : ℕ) : ℝ) / (2 * N) - Real.pi / (2 * N)
      = Real.pi * (q : ℝ) / (2 * N) := by push_cast; field_simp; ring
  rw [e2, e1, e3, e4] at this
  rw [this]
  unfold Kc sig
  ring

/-- **Edge weights.** For `1 ≤ p ≤ 2m - 1`, `κ̃(p+1) − κ̃(p) − κ̃(1) = −K ρ_p ρ_{p+1} g_p`. -/
theorem edge_eq {m p : ℕ} (hN : N = 2 * m + 1) (h1 : 1 ≤ p) (h2 : p ≤ 2 * m - 1) :
    kap N (p + 1) - kap N p - kap N 1 = -(Kc N * rho N m p * rho N m (p + 1) * gw N m p) := by
  have hN0 : N ≠ 0 := by omega
  have hm : 1 ≤ m := by omega
  rw [kap_of_le hN le_rfl hm]
  rcases lt_trichotomy p m with hp | hp | hp
  · rw [kap_of_le hN (by omega) (by omega), kap_of_le hN h1 hp.le]
    unfold rho gw
    rw [if_pos hp.le, if_pos (by omega), if_neg hp.ne, mul_one]
    rw [← interior_edge hN0 p]
    push_cast; ring_nf
  · subst hp
    rw [kap_of_gt hN (by omega) (by omega), kap_of_le hN h1 le_rfl,
      show N - (p + 1) = p by omega]
    unfold rho gw gam
    rw [if_pos le_rfl, if_neg (by omega), if_pos rfl, show N - (p + 1) = p by omega]
    have hs : 0 < sig N p := by
      unfold sig
      apply Real.sin_pos_of_pos_of_lt_pi
      · have : (0 : ℝ) < p := by exact_mod_cast h1
        positivity
      · rw [div_lt_iff₀ (by positivity)]
        have : (p : ℝ) < 2 * N := by exact_mod_cast (show p < 2 * N by omega)
        nlinarith [Real.pi_pos]
    have hK : 0 < Kc N := by
      unfold Kc
      have : 0 < Real.sin (Real.pi / (2 * N)) := by
        apply Real.sin_pos_of_pos_of_lt_pi
        · have : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
          positivity
        · rw [div_lt_iff₀ (by positivity)]
          have : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hN0
          nlinarith [Real.pi_pos]
      positivity
    have hs' := hs.ne'
    have hK' := hK.ne'
    field_simp
    ring_nf
  · obtain ⟨q, hq⟩ : ∃ q, N - p = q + 1 := ⟨N - p - 1, by omega⟩
    rw [kap_of_gt hN (by omega) (by omega), kap_of_gt hN hp (by omega),
      show N - (p + 1) = q by omega, hq]
    unfold rho gw
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), mul_one,
      show N - (p + 1) = q by omega, hq]
    rw [show Kc N * sig N (q + 1) * sig N q = Kc N * sig N q * sig N (q + 1) by ring,
      ← interior_edge hN0 q]
    ring_nf

/-! ### Fourier coefficients of an eigenvector -/

/-- The Fourier coefficient `c(l) = Σ_x conj(ψ_l(x)) v(x)`. -/
def cf (N : ℕ) (v : Fin N → ℝ) (l : ℕ) : ℂ := ∑ x, starRingEnd ℂ (psi N l x) * v x

theorem cosineDefect_entry_symm (x y : Fin N) : cosineDefect N y x = cosineDefect N x y := by
  have := (cosineDefect_symm N).apply x y
  simpa using this

/-- **Three-term recurrence** for the Fourier coefficients of an eigenvector of `D_h`. -/
theorem coeff_recurrence {m : ℕ} (hN : N = 2 * m + 1) (hm : 1 ≤ m) (v : Fin N → ℝ) (μ : ℝ)
    (hv : cosineDefect N *ᵥ v = μ • v) {l : ℕ} (hl : 1 ≤ l) :
    2 * Complex.I * μ * cf N v l
      = ((kap N (l + 1) - kap N l - kap N 1 : ℝ) : ℂ) * cf N v (l + 1)
        - ((kap N (l - 1 + 1) - kap N (l - 1) - kap N 1 : ℝ) : ℂ) * cf N v (l - 1) := by
  have hN1 : 1 ≤ N := by omega
  have hmu : (μ : ℂ) * cf N v l = ∑ y, (v y : ℂ) *
      starRingEnd ℂ (∑ x, ((cosineDefect N y x : ℝ) : ℂ) * psi N l x) := by
    unfold cf
    rw [Finset.mul_sum]
    have h1 : ∀ x, (μ : ℂ) * (starRingEnd ℂ (psi N l x) * v x)
        = starRingEnd ℂ (psi N l x) * ∑ y, ((cosineDefect N x y : ℝ) : ℂ) * v y := by
      intro x
      have := congrFun hv x
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
      rw [show ∑ y, ((cosineDefect N x y : ℝ) : ℂ) * v y
          = ((∑ y, cosineDefect N x y * v y : ℝ) : ℂ) by push_cast; rfl, this]
      push_cast; ring
    rw [Finset.sum_congr rfl fun x _ => h1 x]
    simp_rw [Finset.mul_sum, map_sum, map_mul, Complex.conj_ofReal]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [cosineDefect_entry_symm]; ring
  simp_rw [cosineDefect_psi hN1 hl] at hmu
  simp only [map_mul, map_add, Complex.conj_ofReal, map_div₀, Complex.conj_I, map_ofNat] at hmu
  have hB : kap N (l - 1) - kap N l - kap N (N - 1)
      = -(kap N (l - 1 + 1) - kap N (l - 1) - kap N 1) := by
    rw [kap_N_sub_one hN hm, Nat.sub_add_cancel hl]; ring
  rw [hB] at hmu
  have hexp : ∑ y, (v y : ℂ) * (-Complex.I / 2 *
      (((kap N (l + 1) - kap N l - kap N 1 : ℝ) : ℂ) * starRingEnd ℂ (psi N (l + 1) y)
        + ((-(kap N (l - 1 + 1) - kap N (l - 1) - kap N 1) : ℝ) : ℂ) *
          starRingEnd ℂ (psi N (l - 1) y)))
      = -Complex.I / 2 * (((kap N (l + 1) - kap N l - kap N 1 : ℝ) : ℂ) * cf N v (l + 1)
        - ((kap N (l - 1 + 1) - kap N (l - 1) - kap N 1 : ℝ) : ℂ) * cf N v (l - 1)) := by
    unfold cf
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    push_cast; ring
  rw [hexp] at hmu
  calc 2 * Complex.I * μ * cf N v l = 2 * Complex.I * ((μ : ℂ) * cf N v l) := by ring
    _ = _ := by
      rw [hmu]
      have : 2 * Complex.I * (-Complex.I / 2) = 1 := by
        field_simp; rw [Complex.I_sq]; ring
      rw [← mul_assoc, this, one_mul]

/-! ### Positivity of the scalings -/

theorem sig_ge (hN : N ≠ 0) {k : ℕ} (hk : k ≤ N) : (k : ℝ) / N ≤ sig N k := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hkN : (k : ℝ) ≤ N := by exact_mod_cast hk
  unfold sig
  have h0 : 0 ≤ Real.pi * k / (2 * N) := by positivity
  have h1 : Real.pi * k / (2 * N) ≤ Real.pi / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [Real.pi_pos]
  have := Real.mul_le_sin h0 h1
  calc (k : ℝ) / N = 2 / Real.pi * (Real.pi * k / (2 * N)) := by
        field_simp
    _ ≤ _ := this

theorem sig_pos (hN : N ≠ 0) {k : ℕ} (h1 : 1 ≤ k) (hk : k ≤ N) : 0 < sig N k := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have : (0 : ℝ) < (k : ℝ) / N := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast h1
    positivity
  exact this.trans_le (sig_ge hN hk)

theorem Kc_eq (N : ℕ) : Kc N = 8 * N * sig N 1 := by
  unfold Kc sig; push_cast; ring_nf

theorem Kc_ge (hN : N ≠ 0) : 8 ≤ Kc N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  rw [Kc_eq]
  have := sig_ge hN (k := 1) (by omega)
  have : 8 * N * ((1 : ℕ) / (N : ℝ)) ≤ 8 * N * sig N 1 :=
    mul_le_mul_of_nonneg_left this (by positivity)
  calc (8 : ℝ) = 8 * N * ((1 : ℕ) / (N : ℝ)) := by push_cast; field_simp
    _ ≤ _ := this

theorem Kc_pos (hN : N ≠ 0) : 0 < Kc N := lt_of_lt_of_le (by norm_num) (Kc_ge hN)

theorem rho_pos {m p : ℕ} (hN : N = 2 * m + 1) (h1 : 1 ≤ p) (h2 : p ≤ 2 * m) :
    0 < rho N m p := by
  unfold rho
  split_ifs with h
  · exact sig_pos (by omega) h1 (by omega)
  · exact sig_pos (by omega) (by omega) (by omega)

theorem gam_pos {m : ℕ} (hN : N = 2 * m + 1) (hm : 1 ≤ m) : 0 < gam N m := by
  have hN0 : N ≠ 0 := by omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
  unfold gam
  have hs : 0 < sig N m := sig_pos hN0 hm (by omega)
  have hK := Kc_pos hN0
  have h1 : 0 < Real.sin (Real.pi * m / N) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · have : (0 : ℝ) < m := by exact_mod_cast hm
      positivity
    · rw [div_lt_iff₀ hN']
      have : (m : ℝ) < N := by exact_mod_cast (show m < N by omega)
      nlinarith [Real.pi_pos]
  have h2 : 0 < Real.sin (Real.pi / N) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · rw [div_lt_iff₀ hN']
      have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
      nlinarith [Real.pi_pos]
  positivity

theorem gw_ne_zero {m : ℕ} (hN : N = 2 * m + 1) (hm : 1 ≤ m) (p : ℕ) : gw N m p ≠ 0 := by
  unfold gw; split_ifs
  · exact (gam_pos hN hm).ne'
  · exact one_ne_zero

theorem kap_N {m : ℕ} (hN : N = 2 * m + 1) : kap N N = 0 := by
  rw [kap_of_gt hN (by omega) le_rfl]; simp

/-- The Fourier coefficients of an eigenvector satisfy the scaled path equations. -/
theorem pathEq_of_eigen {m : ℕ} (hN : N = 2 * m + 1) (hm : 1 ≤ m) (v : Fin N → ℝ) (μ : ℝ)
    (hv : cosineDefect N *ᵥ v = μ • v) :
    PathEq m (gw N m) (fun p => (rho N m p : ℂ) * cf N v p)
      (fun p => -(2 * Complex.I * μ * cf N v p) / ((Kc N * rho N m p : ℝ) : ℂ)) := by
  intro p h1 h2
  have hN0 : N ≠ 0 := by omega
  have hK := (Kc_pos hN0).ne'
  have hr := (rho_pos hN h1 h2).ne'
  have hK' : (Kc N : ℂ) ≠ 0 := by exact_mod_cast hK
  have hr' : (rho N m p : ℂ) ≠ 0 := by exact_mod_cast hr
  simp only
  rw [coeff_recurrence hN hm v μ hv h1]
  have hA : (kap N (p + 1) - kap N p - kap N 1 : ℝ)
      = if p < 2 * m then -(Kc N * rho N m p * rho N m (p + 1) * gw N m p) else 0 := by
    split_ifs with hp
    · exact edge_eq hN h1 (by omega)
    · have : p = N - 1 := by omega
      rw [this, Nat.sub_add_cancel (by omega), kap_N hN, kap_N_sub_one hN hm]; ring
  have hB : (kap N (p - 1 + 1) - kap N (p - 1) - kap N 1 : ℝ)
      = if 1 < p then -(Kc N * rho N m (p - 1) * rho N m p * gw N m (p - 1)) else 0 := by
    split_ifs with hp
    · have := edge_eq hN (p := p - 1) (by omega) (by omega)
      rwa [Nat.sub_add_cancel h1] at this ⊢
    · have : p = 1 := by omega
      subst this; rw [kap_zero hN]; ring
  rw [hA, hB]
  split_ifs <;> push_cast <;> field_simp <;> ring

/-! ### The eigenvalue identity -/

/-- The explicit path factors: `Γ(2i+1, 2j+2) = γ^{±1}` if the pair straddles the middle edge,
`1` otherwise. -/
def gamC (N m : ℕ) : ℝ := if Even m then gam N m else (gam N m)⁻¹

theorem pathGamma_gw {m : ℕ} (i j : ℕ) :
    pathGamma (gw N m) (2 * i + 1) (2 * j + 2)
      = if 2 * i + 1 ≤ m ∧ m < 2 * j + 2 then gamC N m else 1 := by
  unfold pathGamma
  split_ifs with h
  · rw [Finset.prod_eq_single_of_mem m (Finset.mem_Ico.2 h)]
    · unfold gw gamC; simp
    · intro k _ hk; unfold gw; simp [hk]
  · apply Finset.prod_eq_one
    intro k hk
    have : k ≠ m := by rintro rfl; exact h (Finset.mem_Ico.1 hk)
    unfold gw; simp [this]

theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ q ∈ Finset.range (2 * m), f (q + 1)
      = ∑ i ∈ Finset.range m, f (2 * i + 1) + ∑ j ∈ Finset.range m, f (2 * j + 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ, Finset.sum_range_succ]
    rw [show 2 * m + 1 + 1 = 2 * m + 2 by ring]
    abel

/-- **Eigenvalue identity.** For an eigenvector `D_h v = μ v`,
`Σ_{p=1}^{2m} |c(p)|² = (−2iμ/K) Σ_{i ≤ j < m} Γ_{ij}/(ρ_{2i+1}ρ_{2j+2})
  (conj c(2j+2) c(2i+1) − conj c(2i+1) c(2j+2))`. -/
theorem eigen_identity {m : ℕ} (hN : N = 2 * m + 1) (hm : 1 ≤ m) (v : Fin N → ℝ) (μ : ℝ)
    (hv : cosineDefect N *ᵥ v = μ • v) :
    ∑ q ∈ Finset.range (2 * m), starRingEnd ℂ (cf N v (q + 1)) * cf N v (q + 1)
      = (-2 * Complex.I * μ / Kc N) * ∑ j ∈ Finset.range m, ∑ i ∈ Finset.range (j + 1),
        ((pathGamma (gw N m) (2 * i + 1) (2 * j + 2) /
          (rho N m (2 * i + 1) * rho N m (2 * j + 2)) : ℝ) : ℂ) *
        (starRingEnd ℂ (cf N v (2 * j + 2)) * cf N v (2 * i + 1)
          - starRingEnd ℂ (cf N v (2 * i + 1)) * cf N v (2 * j + 2)) := by
  have hN0 : N ≠ 0 := by omega
  have hpe := pathEq_of_eigen hN hm v μ hv
  have hev := pathEq_even (fun k => gw_ne_zero hN hm k) hpe
  have hod := pathEq_odd (fun k => gw_ne_zero hN hm k) hpe
  have hK' : (Kc N : ℂ) ≠ 0 := by exact_mod_cast (Kc_pos hN0).ne'
  have hro : ∀ i, i < m → (rho N m (2 * i + 1) : ℂ) ≠ 0 := fun i hi => by
    exact_mod_cast (rho_pos hN (by omega) (by omega)).ne'
  have hre : ∀ j, j < m → (rho N m (2 * j + 2) : ℂ) ≠ 0 := fun j hj => by
    exact_mod_cast (rho_pos hN (by omega) (by omega)).ne'
  set c := cf N v
  -- even nodes
  have heven : ∀ j ∈ Finset.range m, starRingEnd ℂ (c (2 * j + 2)) * c (2 * j + 2)
      = (-2 * Complex.I * μ / Kc N) * ∑ i ∈ Finset.range (j + 1),
          ((pathGamma (gw N m) (2 * i + 1) (2 * j + 2) : ℝ) : ℂ) /
          ((rho N m (2 * i + 1) : ℂ) * (rho N m (2 * j + 2) : ℂ)) *
          (starRingEnd ℂ (c (2 * j + 2)) * c (2 * i + 1)) := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    have h := hev j hj'
    have hr := hre j hj'
    calc starRingEnd ℂ (c (2 * j + 2)) * c (2 * j + 2)
        = starRingEnd ℂ (c (2 * j + 2)) * (((rho N m (2 * j + 2) : ℂ) * c (2 * j + 2)) /
            (rho N m (2 * j + 2) : ℂ)) := by field_simp
      _ = _ := by
        rw [h, Finset.sum_div, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi' : i < m := by have := Finset.mem_range.1 hi; omega
        have := hro i hi'
        push_cast
        field_simp
  -- odd nodes
  have hodd : ∀ i ∈ Finset.range m, starRingEnd ℂ (c (2 * i + 1)) * c (2 * i + 1)
      = -((-2 * Complex.I * μ / Kc N) * ∑ j ∈ Finset.Ico i m,
          ((pathGamma (gw N m) (2 * i + 1) (2 * j + 2) : ℝ) : ℂ) /
          ((rho N m (2 * i + 1) : ℂ) * (rho N m (2 * j + 2) : ℂ)) *
          (starRingEnd ℂ (c (2 * i + 1)) * c (2 * j + 2))) := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have h := hod i hi'
    have hr := hro i hi'
    calc starRingEnd ℂ (c (2 * i + 1)) * c (2 * i + 1)
        = starRingEnd ℂ (c (2 * i + 1)) * (((rho N m (2 * i + 1) : ℂ) * c (2 * i + 1)) /
            (rho N m (2 * i + 1) : ℂ)) := by field_simp
      _ = _ := by
        rw [h, neg_div, Finset.sum_div, Finset.mul_sum, mul_neg, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj' : j < m := (Finset.mem_Ico.1 hj).2
        have := hre j hj'
        push_cast
        field_simp
  rw [sum_range_two_mul (fun p => starRingEnd ℂ (c p) * c p) m]
  rw [Finset.sum_congr rfl hodd, Finset.sum_congr rfl heven, Finset.sum_neg_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, Finset.range_eq_Ico,
    Finset.sum_Ico_Ico_comm 0 m (fun i j => ((pathGamma (gw N m) (2 * i + 1) (2 * j + 2) : ℝ) : ℂ) /
      ((rho N m (2 * i + 1) : ℂ) * (rho N m (2 * j + 2) : ℂ)) *
      (starRingEnd ℂ (c (2 * i + 1)) * c (2 * j + 2)))]
  rw [← Finset.range_eq_Ico]
  simp_rw [← Finset.range_eq_Ico]
  rw [neg_add_eq_sub, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

/-! ### Orthogonality, inversion, Parseval -/

theorem psi_orth (hN : N ≠ 0) {p q : ℕ} (hp : p < N) (hq : q < N) :
    ∑ x, starRingEnd ℂ (psi N p x) * psi N q x = if p = q then (N : ℂ) else 0 := by
  have : ∀ x : Fin N, starRingEnd ℂ (psi N p x) * psi N q x
      = ex N (((q : ℤ) - p) * ((x : ℕ) : ℤ)) := by
    intro x; unfold psi; rw [← ex_neg, ← ex_add]; congr 1; ring
  rw [Finset.sum_congr rfl fun x _ => this x, sum_ex hN]
  congr 1
  apply propext
  constructor
  · intro h
    have := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
    omega
  · intro h; subst h; simp

theorem normSq_psi (p : ℕ) (x : Fin N) : Complex.normSq (psi N p x) = 1 := by
  unfold psi ex
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
  have : (2 * Real.pi * Complex.I * ((p : ℤ) * ((x : ℕ) : ℤ) : ℤ) / N).re = 0 := by
    simp [Complex.div_re]
  rw [this]; simp

theorem sum_range_ex (hN : N ≠ 0) (x y : Fin N) :
    ∑ l ∈ Finset.range N, psi N l x * starRingEnd ℂ (psi N l y)
      = if x = y then (N : ℂ) else 0 := by
  have : ∀ l : ℕ, psi N l x * starRingEnd ℂ (psi N l y)
      = ex N ((((x : ℕ) : ℤ) - ((y : ℕ) : ℤ)) * (l : ℤ)) := by
    intro l; unfold psi; rw [← ex_neg, ← ex_add]; congr 1; ring
  simp_rw [this]
  rw [← Fin.sum_univ_eq_sum_range (fun l => ex N ((((x : ℕ) : ℤ) - ((y : ℕ) : ℤ)) * (l : ℤ))),
    sum_ex hN]
  congr 1
  apply propext
  constructor
  · intro h
    have := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
    exact Fin.ext (by omega)
  · intro h; subst h; simp

/-- Fourier inversion: `Σ_{l<N} c(l) ψ_l(x) = N v(x)`. -/
theorem fourier_inversion (hN : N ≠ 0) (v : Fin N → ℝ) (x : Fin N) :
    ∑ l ∈ Finset.range N, cf N v l * psi N l x = N * v x := by
  unfold cf
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ y : Fin N, ∑ l ∈ Finset.range N, starRingEnd ℂ (psi N l y) * (v y : ℂ) * psi N l x
      = (v y : ℂ) * ∑ l ∈ Finset.range N, psi N l x * starRingEnd ℂ (psi N l y) := by
    intro y; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
  rw [Finset.sum_congr rfl fun y _ => this y]
  simp_rw [sum_range_ex hN]
  simp [Finset.sum_ite_eq, mul_comm]

/-- Parseval: `Σ_{l<N} |c(l)|² = N Σ_x v(x)²`. -/
theorem parseval (hN : N ≠ 0) (v : Fin N → ℝ) :
    ∑ l ∈ Finset.range N, Complex.normSq (cf N v l) = N * ∑ x, v x ^ 2 := by
  have h : ∑ l ∈ Finset.range N, ((Complex.normSq (cf N v l) : ℝ) : ℂ)
      = ((N * ∑ x, v x ^ 2 : ℝ) : ℂ) := by
    simp_rw [Complex.normSq_eq_conj_mul_self]
    have : ∀ l, starRingEnd ℂ (cf N v l) * cf N v l
        = ∑ x, (v x : ℂ) * starRingEnd ℂ (cf N v l * psi N l x) := by
      intro l
      calc starRingEnd ℂ (cf N v l) * cf N v l
          = starRingEnd ℂ (cf N v l) * ∑ x, starRingEnd ℂ (psi N l x) * v x := rfl
        _ = _ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          simp only [map_mul]; ring
    simp_rw [this]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, ← map_sum, fourier_inversion hN]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_natCast]; ring
  exact_mod_cast h

theorem cf_zero (v : Fin N → ℝ) : cf N v 0 = ((∑ x, v x : ℝ) : ℂ) := by
  unfold cf; push_cast; simp [psi_zero]

/-- Constants are in the kernel of `D_h`. -/
theorem cosineDefect_const {m : ℕ} (hN : N = 2 * m + 1) :
    cosineDefect N *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  have hN0 : N ≠ 0 := by omega
  have hδ : ∀ x, ∑ y, phaseDeriv N x y = 0 := by
    intro x
    have := phaseDeriv_psi hN0 0 x
    rw [kap_zero hN] at this
    simp only [psi_zero, mul_one, Complex.ofReal_zero, mul_zero] at this
    exact_mod_cast this
  funext x
  simp only [Matrix.mulVec, dotProduct, mul_one, Pi.zero_apply]
  simp_rw [cosineDefect_apply]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, if_pos (Finset.mem_univ _),
    ← Finset.mul_sum, hδ x]
  simp [Matrix.mulVec, dotProduct]

/-- An eigenvector with nonzero eigenvalue has zero mean. -/
theorem sum_eq_zero_of_eigen {m : ℕ} (hN : N = 2 * m + 1) (v : Fin N → ℝ) (μ : ℝ)
    (hv : cosineDefect N *ᵥ v = μ • v) (hμ : μ ≠ 0) : ∑ x, v x = 0 := by
  have h1 : μ * ∑ x, v x = ∑ x, (cosineDefect N *ᵥ v) x := by
    rw [hv, Finset.mul_sum]; rfl
  have h2 : ∑ x, (cosineDefect N *ᵥ v) x = ∑ y, v y * (cosineDefect N *ᵥ (fun _ => (1 : ℝ))) y := by
    simp only [Matrix.mulVec, dotProduct, mul_one]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [cosineDefect_entry_symm]; ring
  rw [cosineDefect_const hN] at h2
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h2
  rw [h2] at h1
  exact (mul_eq_zero.1 h1).resolve_left hμ

/-- **Kernel of `D_h`**: on the odd grid `N = 2m + 1` (`m ≥ 1`), `D_h v = 0` forces `v`
constant. -/
theorem cosineDefect_ker {m : ℕ} (hN : N = 2 * m + 1) (hm : 1 ≤ m) (v : Fin N → ℝ)
    (hv : cosineDefect N *ᵥ v = 0) : ∃ c, v = fun _ => c := by
  have hN0 : N ≠ 0 := by omega
  have hv' : cosineDefect N *ᵥ v = (0 : ℝ) • v := by rw [hv, zero_smul]
  have hpe := pathEq_of_eigen hN hm v 0 hv'
  have hev := pathEq_even (fun k => gw_ne_zero hN hm k) hpe
  have hod := pathEq_odd (fun k => gw_ne_zero hN hm k) hpe
  have hc : ∀ p, 1 ≤ p → p ≤ 2 * m → cf N v p = 0 := by
    intro p h1 h2
    have hr : (rho N m p : ℂ) ≠ 0 := by exact_mod_cast (rho_pos hN h1 h2).ne'
    obtain ⟨j, rfl | rfl⟩ : ∃ j, p = 2 * j + 1 ∨ p = 2 * j + 2 := ⟨(p - 1) / 2, by omega⟩
    · have := hod j (by omega)
      simp only [Complex.ofReal_zero, mul_zero, zero_mul, neg_zero, zero_div,
        Finset.sum_const_zero] at this
      exact (mul_eq_zero.1 this).resolve_left hr
    · have := hev j (by omega)
      simp only [Complex.ofReal_zero, mul_zero, zero_mul, neg_zero, zero_div,
        Finset.sum_const_zero] at this
      exact (mul_eq_zero.1 this).resolve_left hr
  refine ⟨(∑ x, v x) / N, funext fun x => ?_⟩
  have hinv := fourier_inversion hN0 v x
  rw [show Finset.range N = Finset.range (2 * m + 1) by rw [hN], Finset.sum_range_succ'] at hinv
  rw [Finset.sum_eq_zero fun q hq => by
    rw [hc (q + 1) (by omega) (by simp at hq; omega), zero_mul]] at hinv
  rw [cf_zero, psi_zero, zero_add, mul_one] at hinv
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN0
  have : ((∑ x, v x : ℝ) : ℂ) = ((N * v x : ℝ) : ℂ) := by rw [hinv]; push_cast; ring
  have := Complex.ofReal_injective this
  field_simp
  linarith

/-! ### Bessel for a real orthonormal basis and complex test vectors -/

theorem bessel (b : OrthonormalBasis (Fin N) ℝ (EuclideanSpace ℝ (Fin N))) (φ : Fin N → ℂ) :
    ∑ a, Complex.normSq (∑ x, starRingEnd ℂ (φ x) * ((b a x : ℝ) : ℂ))
      = ∑ x, Complex.normSq (φ x) := by
  set u : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (fun x => (φ x).re)
  set w : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (fun x => (φ x).im)
  have hin : ∀ y : EuclideanSpace ℝ (Fin N), ∀ f : Fin N → ℝ,
      inner ℝ (WithLp.toLp 2 f : EuclideanSpace ℝ (Fin N)) y = ∑ x, f x * y x := by
    intro y f
    simp [PiLp.inner_apply, mul_comm]
  have hterm : ∀ a, Complex.normSq (∑ x, starRingEnd ℂ (φ x) * ((b a x : ℝ) : ℂ))
      = inner ℝ u (b a) ^ 2 + inner ℝ w (b a) ^ 2 := by
    intro a
    have : ∑ x, starRingEnd ℂ (φ x) * ((b a x : ℝ) : ℂ)
        = ((inner ℝ u (b a) : ℝ) : ℂ) - Complex.I * ((inner ℝ w (b a) : ℝ) : ℂ) := by
      rw [hin, hin]
      push_cast
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      conv_lhs => rw [← Complex.re_add_im (φ x)]
      simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
      ring
    rw [this, Complex.normSq_apply]
    simp
    ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  have hp : ∀ z : EuclideanSpace ℝ (Fin N), ∑ a, inner ℝ z (b a) ^ 2 = inner ℝ z z := by
    intro z
    rw [← b.sum_inner_mul_inner z z]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [real_inner_comm (b a) z]; ring
  rw [hp, hp, hin, hin, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.normSq_apply]

/-- `Σ_a |⟨φ, v_a⟩| |⟨φ', v_a⟩| ≤ (‖φ‖² + ‖φ'‖²)/2`. -/
theorem sum_norm_mul_le (b : OrthonormalBasis (Fin N) ℝ (EuclideanSpace ℝ (Fin N)))
    (φ φ' : Fin N → ℂ) :
    ∑ a, ‖∑ x, starRingEnd ℂ (φ x) * ((b a x : ℝ) : ℂ)‖ *
        ‖∑ x, starRingEnd ℂ (φ' x) * ((b a x : ℝ) : ℂ)‖
      ≤ (∑ x, Complex.normSq (φ x) + ∑ x, Complex.normSq (φ' x)) / 2 := by
  rw [← bessel b φ, ← bessel b φ', ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  nlinarith [sq_nonneg (‖∑ x, starRingEnd ℂ (φ x) * ((b a x : ℝ) : ℂ)‖
    - ‖∑ x, starRingEnd ℂ (φ' x) * ((b a x : ℝ) : ℂ)‖)]

/-! ### The per-eigenvector bound -/

/-- Weights of the rank-one straddling block. -/
def aW (N m j : ℕ) : ℝ := if m < 2 * j + 2 then 1 / rho N m (2 * j + 2) else 0
/-- Weights of the rank-one straddling block. -/
def bW (N m i : ℕ) : ℝ := if 2 * i + 1 ≤ m then 1 / rho N m (2 * i + 1) else 0

theorem path_weight_split {m : ℕ} (i j : ℕ) :
    pathGamma (gw N m) (2 * i + 1) (2 * j + 2) / (rho N m (2 * i + 1) * rho N m (2 * j + 2))
      = 1 / (rho N m (2 * i + 1) * rho N m (2 * j + 2))
        + (gamC N m - 1) * (aW N m j * bW N m i) := by
  rw [pathGamma_gw]
  unfold aW bW
  by_cases h1 : 2 * i + 1 ≤ m <;> by_cases h2 : m < 2 * j + 2
  · rw [if_pos ⟨h1, h2⟩, if_pos h2, if_pos h1]; field_simp; ring
  · rw [if_neg (fun h => h2 h.2), if_neg h2]; ring
  · rw [if_neg (fun h => h1 h.1), if_neg h1]; ring
  · rw [if_neg (fun h => h1 h.1), if_neg h1]; ring

theorem norm_cross_le (a b : ℂ) :
    ‖starRingEnd ℂ a * b - starRingEnd ℂ b * a‖ ≤ 2 * (‖a‖ * ‖b‖) := by
  refine (norm_sub_le _ _).trans ?_
  simp only [norm_mul, Complex.norm_conj]
  linarith

/-- **Per-eigenvector bound.** -/
theorem inv_abs_le {m : ℕ} (hN : N = 2 * m + 1) (hm : 1 ≤ m) (v : Fin N → ℝ) (μ : ℝ)
    (hv : cosineDefect N *ᵥ v = μ • v) (hμ : μ ≠ 0)
    (hnorm : ∑ q ∈ Finset.range (2 * m), Complex.normSq (cf N v (q + 1)) = N) :
    1 / |μ| ≤ 2 / (Kc N * N) * (2 * ∑ j ∈ Finset.range m, ∑ i ∈ Finset.range m,
        ‖cf N v (2 * i + 1)‖ * ‖cf N v (2 * j + 2)‖ /
          (rho N m (2 * i + 1) * rho N m (2 * j + 2))
      + 2 * |gamC N m - 1| * (‖∑ j ∈ Finset.range m, (aW N m j : ℂ) * cf N v (2 * j + 2)‖ *
          ‖∑ i ∈ Finset.range m, (bW N m i : ℂ) * cf N v (2 * i + 1)‖)) := by
  have hN0 : N ≠ 0 := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
  have hK := Kc_pos hN0
  have hid := eigen_identity hN hm v μ hv
  set c := cf N v
  set W := ∑ j ∈ Finset.range m, ∑ i ∈ Finset.range (j + 1),
        ((pathGamma (gw N m) (2 * i + 1) (2 * j + 2) /
          (rho N m (2 * i + 1) * rho N m (2 * j + 2)) : ℝ) : ℂ) *
        (starRingEnd ℂ (c (2 * j + 2)) * c (2 * i + 1)
          - starRingEnd ℂ (c (2 * i + 1)) * c (2 * j + 2)) with hW
  have hlhs : ∑ q ∈ Finset.range (2 * m), starRingEnd ℂ (c (q + 1)) * c (q + 1) = (N : ℂ) := by
    simp_rw [← Complex.normSq_eq_conj_mul_self]
    exact_mod_cast hnorm
  rw [hlhs] at hid
  have hnormW : (N : ℝ) = 2 * |μ| / Kc N * ‖W‖ := by
    have := congrArg (fun z : ℂ => ‖z‖) hid
    simp only [Complex.norm_natCast, norm_mul, norm_div, norm_neg, Complex.norm_ofNat,
      Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hK] at this
    rw [this]; ring
  have hμpos : 0 < |μ| := abs_pos.2 hμ
  have hW0 : ‖W‖ ≠ 0 := by
    intro h; rw [h, mul_zero] at hnormW; linarith
  have hinv : 1 / |μ| = 2 / (Kc N * N) * ‖W‖ := by
    rw [hnormW]; field_simp
  rw [hinv]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hsplit : W = ∑ j ∈ Finset.range m, ∑ i ∈ Finset.range (j + 1),
        ((1 / (rho N m (2 * i + 1) * rho N m (2 * j + 2)) : ℝ) : ℂ) *
        (starRingEnd ℂ (c (2 * j + 2)) * c (2 * i + 1)
          - starRingEnd ℂ (c (2 * i + 1)) * c (2 * j + 2))
      + ((gamC N m - 1 : ℝ) : ℂ) * ∑ j ∈ Finset.range m, ∑ i ∈ Finset.range m,
        ((aW N m j * bW N m i : ℝ) : ℂ) *
        (starRingEnd ℂ (c (2 * j + 2)) * c (2 * i + 1)
          - starRingEnd ℂ (c (2 * i + 1)) * c (2 * j + 2)) := by
    rw [hW, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    have hsub : ∑ i ∈ Finset.range (j + 1), ((aW N m j * bW N m i : ℝ) : ℂ) *
        (starRingEnd ℂ (c (2 * j + 2)) * c (2 * i + 1)
          - starRingEnd ℂ (c (2 * i + 1)) * c (2 * j + 2))
        = ∑ i ∈ Finset.range m, ((aW N m j * bW N m i : ℝ) : ℂ) *
        (starRingEnd ℂ (c (2 * j + 2)) * c (2 * i + 1)
          - starRingEnd ℂ (c (2 * i + 1)) * c (2 * j + 2)) := by
      apply Finset.sum_subset (Finset.range_subset_range.2 (by omega))
      intro i hi hni
      have hi2 : j + 1 ≤ i := by simpa using hni
      unfold aW bW
      by_cases h2 : m < 2 * j + 2
      · rw [if_neg (show ¬ (2 * i + 1 ≤ m) by omega)]; simp
      · rw [if_neg h2]; simp
    rw [← hsub, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ j := by have := Finset.mem_range.1 hi; omega
    rw [path_weight_split i j]
    push_cast; ring
  have hW2 : ∑ j ∈ Finset.range m, ∑ i ∈ Finset.range m,
        ((aW N m j * bW N m i : ℝ) : ℂ) *
        (starRingEnd ℂ (c (2 * j + 2)) * c (2 * i + 1)
          - starRingEnd ℂ (c (2 * i + 1)) * c (2 * j + 2))
      = starRingEnd ℂ (∑ j ∈ Finset.range m, (aW N m j : ℂ) * c (2 * j + 2))
          * (∑ i ∈ Finset.range m, (bW N m i : ℂ) * c (2 * i + 1))
        - starRingEnd ℂ (∑ i ∈ Finset.range m, (bW N m i : ℂ) * c (2 * i + 1))
          * (∑ j ∈ Finset.range m, (aW N m j : ℂ) * c (2 * j + 2)) := by
    simp only [map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul_sum]
    rw [Finset.sum_comm (s := Finset.range m) (t := Finset.range m)
      (f := fun i j => (bW N m i : ℂ) * starRingEnd ℂ (c (2 * i + 1)) *
        ((aW N m j : ℂ) * c (2 * j + 2)))]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast; ring
  rw [hsplit, hW2]
  set A := ∑ j ∈ Finset.range m, (aW N m j : ℂ) * c (2 * j + 2)
  set B := ∑ i ∈ Finset.range m, (bW N m i : ℂ) * c (2 * i + 1)
  have hfirst : ‖∑ j ∈ Finset.range m, ∑ i ∈ Finset.range (j + 1),
          ((1 / (rho N m (2 * i + 1) * rho N m (2 * j + 2)) : ℝ) : ℂ) *
          (starRingEnd ℂ (c (2 * j + 2)) * c (2 * i + 1)
            - starRingEnd ℂ (c (2 * i + 1)) * c (2 * j + 2))‖
      ≤ 2 * ∑ j ∈ Finset.range m, ∑ i ∈ Finset.range m,
          ‖c (2 * i + 1)‖ * ‖c (2 * j + 2)‖ / (rho N m (2 * i + 1) * rho N m (2 * j + 2)) := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    have hnn : ∀ i ∈ Finset.range m, 0 ≤ 2 * (‖c (2 * i + 1)‖ * ‖c (2 * j + 2)‖ /
        (rho N m (2 * i + 1) * rho N m (2 * j + 2))) := by
      intro i hi
      have hi' := Finset.mem_range.1 hi
      have h1 := rho_pos hN (p := 2 * i + 1) (by omega) (by omega)
      have h2 := rho_pos hN (p := 2 * j + 2) (by omega) (by omega)
      positivity
    refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.2 (show j + 1 ≤ m by omega)) fun i hi _ => hnn i hi)
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' : i < m := by have := Finset.mem_range.1 hi; omega
    have h1 := rho_pos hN (p := 2 * i + 1) (by omega) (by omega)
    have h2 := rho_pos hN (p := 2 * j + 2) (by omega) (by omega)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hX := norm_cross_le (c (2 * j + 2)) (c (2 * i + 1))
    calc 1 / (rho N m (2 * i + 1) * rho N m (2 * j + 2)) *
          ‖starRingEnd ℂ (c (2 * j + 2)) * c (2 * i + 1)
            - starRingEnd ℂ (c (2 * i + 1)) * c (2 * j + 2)‖
        ≤ 1 / (rho N m (2 * i + 1) * rho N m (2 * j + 2)) *
          (2 * (‖c (2 * j + 2)‖ * ‖c (2 * i + 1)‖)) := by gcongr
      _ = _ := by ring
  have hsecond : ‖((gamC N m - 1 : ℝ) : ℂ) * (starRingEnd ℂ A * B - starRingEnd ℂ B * A)‖
      ≤ 2 * |gamC N m - 1| * (‖A‖ * ‖B‖) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |gamC N m - 1| * ‖starRingEnd ℂ A * B - starRingEnd ℂ B * A‖
        ≤ |gamC N m - 1| * (2 * (‖A‖ * ‖B‖)) := by gcongr; exact norm_cross_le A B
      _ = _ := by ring
  exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)

/-! ### Numerical bounds on the scalings -/

theorem basel_le (n : ℕ) :
    ∑ q ∈ Finset.range (n + 1), 1 / ((q : ℝ) + 1) ^ 2 ≤ 2 - 1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have key : 1 / (((n + 1 : ℕ) : ℝ) + 1) ^ 2
        ≤ 1 / ((n : ℝ) + 1) - 1 / (((n + 1 : ℕ) : ℝ) + 1) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    linarith

theorem basel_le_two (n : ℕ) : ∑ q ∈ Finset.range n, 1 / ((q : ℝ) + 1) ^ 2 ≤ 2 := by
  rcases n with _ | n
  · simp
  · have := basel_le n
    have : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
    linarith

theorem inv_rho_sq_le {m p : ℕ} (hN : N = 2 * m + 1) (h1 : 1 ≤ p) (h2 : p ≤ 2 * m) :
    1 / rho N m p ^ 2 ≤ (N : ℝ) ^ 2 * (1 / (p : ℝ) ^ 2 + 1 / ((N - p : ℕ) : ℝ) ^ 2) := by
  have hN0 : N ≠ 0 := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast h1
  have hq : (1 : ℝ) ≤ ((N - p : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ N - p by omega)
  have key : ∀ k : ℕ, 1 ≤ k → k ≤ N → 1 / sig N k ^ 2 ≤ (N : ℝ) ^ 2 * (1 / (k : ℝ) ^ 2) := by
    intro k hk1 hk2
    have hk : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hs := sig_ge hN0 hk2
    have hpos : 0 < (k : ℝ) / N := by positivity
    calc 1 / sig N k ^ 2 ≤ 1 / ((k : ℝ) / N) ^ 2 := by
          apply one_div_le_one_div_of_le (by positivity)
          exact pow_le_pow_left₀ hpos.le hs 2
      _ = _ := by field_simp
  unfold rho
  split_ifs with h
  · have := key p h1 (by omega)
    have : (0 : ℝ) ≤ (N : ℝ) ^ 2 * (1 / ((N - p : ℕ) : ℝ) ^ 2) := by positivity
    nlinarith
  · have := key (N - p) (by omega) (by omega)
    have : (0 : ℝ) ≤ (N : ℝ) ^ 2 * (1 / (p : ℝ) ^ 2) := by positivity
    nlinarith

/-- `S₂ = Σ_{p=1}^{2m} ρ_p⁻² ≤ 4N²`. -/
theorem sum_inv_rho_sq_le {m : ℕ} (hN : N = 2 * m + 1) :
    ∑ q ∈ Finset.range (2 * m), 1 / rho N m (q + 1) ^ 2 ≤ 4 * (N : ℝ) ^ 2 := by
  have h1 : ∑ q ∈ Finset.range (2 * m), 1 / rho N m (q + 1) ^ 2
      ≤ ∑ q ∈ Finset.range (2 * m), (N : ℝ) ^ 2 *
        (1 / ((q + 1 : ℕ) : ℝ) ^ 2 + 1 / ((N - (q + 1) : ℕ) : ℝ) ^ 2) :=
    Finset.sum_le_sum fun q hq => inv_rho_sq_le hN (by omega) (by simp at hq; omega)
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at h1
  have h2 : ∑ q ∈ Finset.range (2 * m), 1 / ((N - (q + 1) : ℕ) : ℝ) ^ 2
      = ∑ q ∈ Finset.range (2 * m), 1 / ((q : ℝ) + 1) ^ 2 := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq' := Finset.mem_range.1 hq
    rw [show N - (2 * m - 1 - q + 1) = q + 1 by omega]
    push_cast; ring
  have h3 : ∑ q ∈ Finset.range (2 * m), 1 / ((q + 1 : ℕ) : ℝ) ^ 2
      = ∑ q ∈ Finset.range (2 * m), 1 / ((q : ℝ) + 1) ^ 2 := by push_cast; rfl
  rw [h2, h3] at h1
  have := basel_le_two (2 * m)
  have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
  nlinarith

/-- Cauchy–Schwarz: `S₁² ≤ 2m S₂`. -/
theorem sum_inv_rho_sq {m : ℕ} :
    (∑ q ∈ Finset.range (2 * m), 1 / rho N m (q + 1)) ^ 2
      ≤ (2 * m) * ∑ q ∈ Finset.range (2 * m), 1 / rho N m (q + 1) ^ 2 := by
  have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (2 * m)) (fun _ => (1 : ℝ))
    (fun q => 1 / rho N m (q + 1))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    div_pow] at this
  push_cast at this ⊢
  exact this

theorem gam_le {m : ℕ} (hN : N = 2 * m + 1) (hm : 1 ≤ m) : gam N m ≤ 7 * N := by
  have hN0 : N ≠ 0 := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
  have hK := Kc_ge hN0
  have hs := sig_ge hN0 (k := m) (by omega)
  have hm3 : (1 : ℝ) / 3 ≤ (m : ℝ) / N := by
    rw [div_le_div_iff₀ (by norm_num) hNpos]
    have : (N : ℝ) = 2 * m + 1 := by exact_mod_cast hN
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hden : (8 : ℝ) / 9 ≤ Kc N * sig N m ^ 2 := by
    have : (1 / 3 : ℝ) ^ 2 ≤ sig N m ^ 2 := pow_le_pow_left₀ (by norm_num) (hm3.trans hs) 2
    nlinarith
  have hnum : 4 * N * Real.sin (Real.pi * m / N) + 2 * N * Real.sin (Real.pi / N) ≤ 6 * N := by
    have := Real.sin_le_one (Real.pi * m / N)
    have := Real.sin_le_one (Real.pi / N)
    nlinarith
  unfold gam
  rw [div_le_iff₀ (by linarith)]
  nlinarith

theorem gam_inv_le {m : ℕ} (hN : N = 2 * m + 1) (hm : 1 ≤ m) : (gam N m)⁻¹ ≤ 4 := by
  have hN0 : N ≠ 0 := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by omega)
  have hg := gam_pos hN hm
  unfold gam at hg ⊢
  rw [inv_div]
  have hKle : Kc N ≤ 4 * Real.pi := by
    unfold Kc
    have := Real.sin_le (show 0 ≤ Real.pi / (2 * N) by positivity)
    have h : 8 * N * (Real.pi / (2 * N)) = 4 * Real.pi := by field_simp; ring
    nlinarith
  have hsig : sig N m ^ 2 ≤ 1 := by
    have h0 : 0 ≤ sig N m := (sig_pos hN0 hm (by omega)).le
    have h1 : sig N m ≤ 1 := Real.sin_le_one _
    nlinarith
  have hsin1 : 4 ≤ 2 * N * Real.sin (Real.pi / N) := by
    have h0 : 0 ≤ Real.pi / N := by positivity
    have h1 : Real.pi / N ≤ Real.pi / 2 := by
      apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hN2
    have := Real.mul_le_sin h0 h1
    have h : 2 / Real.pi * (Real.pi / N) = 2 / N := by field_simp
    rw [h] at this
    have : 2 * N * (2 / N) = (4 : ℝ) := by field_simp; ring
    nlinarith
  have hsinm : 0 ≤ 4 * N * Real.sin (Real.pi * m / N) := by
    have : 0 ≤ Real.sin (Real.pi * m / N) := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
      rw [div_le_iff₀ hNpos]
      have : (m : ℝ) ≤ N := by exact_mod_cast (show m ≤ N by omega)
      nlinarith [Real.pi_pos]
    positivity
  rw [div_le_iff₀ (by linarith)]
  have hK0 := (Kc_pos hN0).le
  have : Kc N * sig N m ^ 2 ≤ Kc N := by nlinarith
  nlinarith [Real.pi_lt_four]

theorem abs_gamC_sub_one_le {m : ℕ} (hN : N = 2 * m + 1) (hm : 1 ≤ m) :
    |gamC N m - 1| ≤ 8 * N := by
  have hNpos : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hg := gam_pos hN hm
  unfold gamC
  split_ifs
  · have := gam_le hN hm
    rw [abs_le]; constructor <;> linarith
  · have := gam_inv_le hN hm
    have : 0 < (gam N m)⁻¹ := inv_pos.2 hg
    rw [abs_le]; constructor <;> linarith

/-! ### Assembly: the spectral input -/

theorem normSq_sum_psi (hN : N ≠ 0) (s : Finset ℕ) (e : ℕ → ℕ) (he : ∀ j ∈ s, e j < N)
    (hinj : ∀ j ∈ s, ∀ k ∈ s, e j = e k → j = k) (a : ℕ → ℝ) :
    ∑ x, Complex.normSq (∑ j ∈ s, (a j : ℂ) * psi N (e j) x) = N * ∑ j ∈ s, a j ^ 2 := by
  have h : ∑ x, ((Complex.normSq (∑ j ∈ s, (a j : ℂ) * psi N (e j) x) : ℝ) : ℂ)
      = ((N * ∑ j ∈ s, a j ^ 2 : ℝ) : ℂ) := by
    simp_rw [Complex.normSq_eq_conj_mul_self, map_sum, map_mul, Complex.conj_ofReal,
      Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    have : ∀ j ∈ s, ∑ x, ∑ k ∈ s, (a j : ℂ) * starRingEnd ℂ (psi N (e j) x) *
        ((a k : ℂ) * psi N (e k) x) = (a j : ℂ) * (a j : ℂ) * N := by
      intro j hj
      rw [Finset.sum_comm]
      have : ∀ k ∈ s, ∑ x, (a j : ℂ) * starRingEnd ℂ (psi N (e j) x) *
          ((a k : ℂ) * psi N (e k) x)
          = (a j : ℂ) * (a k : ℂ) * (if j = k then (N : ℂ) else 0) := by
        intro k hk
        have hjk : (e j = e k) ↔ j = k := ⟨hinj j hj k hk, fun h => h ▸ rfl⟩
        rw [← if_congr hjk rfl rfl, ← psi_orth hN (he j hj) (he k hk), Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring
      rw [Finset.sum_congr rfl this]
      simp [Finset.sum_ite_eq, hj]
    rw [Finset.sum_congr rfl this]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  exact_mod_cast h

theorem normSq_psi_sum (p : ℕ) : ∑ x : Fin N, Complex.normSq (psi N p x) = N := by
  simp [normSq_psi]

/-- **The spectral input of `lem:supp-exact-rational-detuning`.**  For every odd cutoff
`N = 2m + 1 ≥ 3`, the cosine defect `D_h` has kernel the constants and
`Σ_{λ ≠ 0} 1/|λ| ≤ 10 N³` (with multiplicity), i.e. `CosineDefectSpectralInput N 10`. -/
theorem cosineDefect_spectralInput {m : ℕ} (hN : N = 2 * m + 1) (hm : 1 ≤ m) :
    CosineDefectSpectralInput N 10 := by
  have hN0 : N ≠ 0 := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
  refine ⟨fun v hv => cosineDefect_ker hN hm v hv, ?_⟩
  set hD := cosineDefect_symm N
  set b := hD.eigenvectorBasis
  set μ := hD.eigenvalues
  have hK8 := Kc_ge hN0
  have hK := Kc_pos hN0
  -- eigenvector data
  have hvec : ∀ a, cosineDefect N *ᵥ (fun x => b a x) = μ a • (fun x => b a x) :=
    fun a => hD.mulVec_eigenvectorBasis a
  have hunit : ∀ a, ∑ x, (b a x) ^ 2 = 1 := by
    intro a
    have := (orthonormal_iff_ite.1 b.orthonormal) a a
    rw [if_pos rfl, PiLp.inner_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [sq]
  have hnorm : ∀ a, μ a ≠ 0 →
      ∑ q ∈ Finset.range (2 * m), Complex.normSq (cf N (fun x => b a x) (q + 1)) = N := by
    intro a ha
    have hp := parseval hN0 (fun x => b a x)
    rw [show Finset.range N = Finset.range (2 * m + 1) by rw [hN], Finset.sum_range_succ',
      cf_zero, sum_eq_zero_of_eigen hN _ _ (hvec a) ha, hunit a] at hp
    simpa using hp
  -- abbreviations
  set S2 := ∑ q ∈ Finset.range (2 * m), 1 / rho N m (q + 1) ^ 2
  set S1 := ∑ q ∈ Finset.range (2 * m), 1 / rho N m (q + 1)
  have hS2 : S2 ≤ 4 * (N : ℝ) ^ 2 := sum_inv_rho_sq_le hN
  have hS1 : S1 ^ 2 ≤ (2 * m) * S2 := sum_inv_rho_sq
  have hγ := abs_gamC_sub_one_le hN hm
  have hro : ∀ i, i < m → 0 < rho N m (2 * i + 1) := fun i hi => rho_pos hN (by omega) (by omega)
  have hre : ∀ j, j < m → 0 < rho N m (2 * j + 2) := fun j hj => rho_pos hN (by omega) (by omega)
  -- the test vectors of the straddling block
  set ΦA : Fin N → ℂ := fun x => ∑ j ∈ Finset.range m, (aW N m j : ℂ) * psi N (2 * j + 2) x
  set ΦB : Fin N → ℂ := fun x => ∑ i ∈ Finset.range m, (bW N m i : ℂ) * psi N (2 * i + 1) x
  have hA : ∀ a, ∑ j ∈ Finset.range m, (aW N m j : ℂ) * cf N (fun x => b a x) (2 * j + 2)
      = ∑ x, starRingEnd ℂ (ΦA x) * ((b a x : ℝ) : ℂ) := by
    intro a
    simp only [ΦA, cf, map_sum, map_mul, Complex.conj_ofReal, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ => by ring
  have hB : ∀ a, ∑ i ∈ Finset.range m, (bW N m i : ℂ) * cf N (fun x => b a x) (2 * i + 1)
      = ∑ x, starRingEnd ℂ (ΦB x) * ((b a x : ℝ) : ℂ) := by
    intro a
    simp only [ΦB, cf, map_sum, map_mul, Complex.conj_ofReal, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ => by ring
  have hΦA : ∑ x, Complex.normSq (ΦA x) = N * ∑ j ∈ Finset.range m, aW N m j ^ 2 :=
    normSq_sum_psi hN0 _ (fun j => 2 * j + 2) (fun j hj => by simp at hj; omega)
      (fun j _ k _ h => by simp at h; omega) _
  have hΦB : ∑ x, Complex.normSq (ΦB x) = N * ∑ i ∈ Finset.range m, bW N m i ^ 2 :=
    normSq_sum_psi hN0 _ (fun i => 2 * i + 1) (fun j hj => by simp at hj; omega)
      (fun j _ k _ h => by simp at h; omega) _
  have haW : ∑ j ∈ Finset.range m, aW N m j ^ 2 + ∑ i ∈ Finset.range m, bW N m i ^ 2 ≤ S2 := by
    rw [show S2 = ∑ i ∈ Finset.range m, 1 / rho N m (2 * i + 1) ^ 2
        + ∑ j ∈ Finset.range m, 1 / rho N m (2 * j + 2) ^ 2 from
      sum_range_two_mul (fun p => 1 / rho N m p ^ 2) m, add_comm]
    gcongr with i hi j hj
    · unfold bW; split_ifs
      · rw [div_pow, one_pow]
      · have := hro i (Finset.mem_range.1 hi); rw [zero_pow two_ne_zero]; positivity
    · unfold aW; split_ifs
      · rw [div_pow, one_pow]
      · have := hre j (Finset.mem_range.1 hj); rw [zero_pow two_ne_zero]; positivity
  -- per-eigenvector bound, summed
  set T1 : Fin N → ℝ := fun a => ∑ j ∈ Finset.range m, ∑ i ∈ Finset.range m,
      ‖cf N (fun x => b a x) (2 * i + 1)‖ * ‖cf N (fun x => b a x) (2 * j + 2)‖ /
        (rho N m (2 * i + 1) * rho N m (2 * j + 2))
  set T2 : Fin N → ℝ := fun a =>
      ‖∑ j ∈ Finset.range m, (aW N m j : ℂ) * cf N (fun x => b a x) (2 * j + 2)‖ *
        ‖∑ i ∈ Finset.range m, (bW N m i : ℂ) * cf N (fun x => b a x) (2 * i + 1)‖
  have hT1nn : ∀ a, 0 ≤ T1 a := fun a => Finset.sum_nonneg fun j hj => Finset.sum_nonneg
    fun i hi => by
      have := hro i (Finset.mem_range.1 hi); have := hre j (Finset.mem_range.1 hj)
      positivity
  have hT2nn : ∀ a, 0 ≤ T2 a := fun a => by positivity
  have hstep : ∀ a, (if μ a = 0 then 0 else 1 / |μ a|)
      ≤ 2 / (Kc N * N) * (2 * T1 a + 2 * |gamC N m - 1| * T2 a) := by
    intro a
    split_ifs with ha
    · have := hT1nn a; have := hT2nn a; positivity
    · exact inv_abs_le hN hm _ _ (hvec a) ha (hnorm a ha)
  have hsumT1 : ∑ a, T1 a ≤ N * S1 ^ 2 := by
    simp only [T1]
    rw [Finset.sum_comm]
    have : ∀ j ∈ Finset.range m, ∑ a, ∑ i ∈ Finset.range m,
        ‖cf N (fun x => b a x) (2 * i + 1)‖ * ‖cf N (fun x => b a x) (2 * j + 2)‖ /
          (rho N m (2 * i + 1) * rho N m (2 * j + 2))
        ≤ ∑ i ∈ Finset.range m, N / (rho N m (2 * i + 1) * rho N m (2 * j + 2)) := by
      intro j hj
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum fun i hi => ?_
      have h1 := hro i (Finset.mem_range.1 hi)
      have h2 := hre j (Finset.mem_range.1 hj)
      rw [← Finset.sum_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have := sum_norm_mul_le b (psi N (2 * i + 1)) (psi N (2 * j + 2))
      rw [normSq_psi_sum, normSq_psi_sum] at this
      simpa [cf] using this.trans (le_of_eq (by ring))
    refine (Finset.sum_le_sum this).trans ?_
    have hsplit : S1 = ∑ i ∈ Finset.range m, 1 / rho N m (2 * i + 1)
        + ∑ j ∈ Finset.range m, 1 / rho N m (2 * j + 2) :=
      sum_range_two_mul (fun p => 1 / rho N m p) m
    have e : ∑ j ∈ Finset.range m, ∑ i ∈ Finset.range m,
        (N : ℝ) / (rho N m (2 * i + 1) * rho N m (2 * j + 2))
        = N * ((∑ i ∈ Finset.range m, 1 / rho N m (2 * i + 1)) *
          (∑ j ∈ Finset.range m, 1 / rho N m (2 * j + 2))) := by
      rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have h1 := (hro i (Finset.mem_range.1 hi)).ne'
      have h2 := (hre j (Finset.mem_range.1 hj)).ne'
      field_simp
    rw [e]
    apply mul_le_mul_of_nonneg_left _ hNpos.le
    have hx : 0 ≤ ∑ i ∈ Finset.range m, 1 / rho N m (2 * i + 1) :=
      Finset.sum_nonneg fun i hi => (one_div_pos.2 (hro i (Finset.mem_range.1 hi))).le
    have hy : 0 ≤ ∑ j ∈ Finset.range m, 1 / rho N m (2 * j + 2) :=
      Finset.sum_nonneg fun j hj => (one_div_pos.2 (hre j (Finset.mem_range.1 hj))).le
    rw [hsplit]; nlinarith
  have hsumT2 : ∑ a, T2 a ≤ N * S2 / 2 := by
    simp only [T2]
    simp_rw [hA, hB]
    refine (sum_norm_mul_le b ΦA ΦB).trans ?_
    rw [hΦA, hΦB]
    have : (0 : ℝ) ≤ N := hNpos.le
    nlinarith
  calc ∑ a, (if μ a = 0 then 0 else 1 / |μ a|)
      ≤ ∑ a, 2 / (Kc N * N) * (2 * T1 a + 2 * |gamC N m - 1| * T2 a) :=
        Finset.sum_le_sum fun a _ => hstep a
    _ = 2 / (Kc N * N) * (2 * ∑ a, T1 a + 2 * |gamC N m - 1| * ∑ a, T2 a) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 / (Kc N * N) * (2 * (N * S1 ^ 2) + 2 * (8 * N) * (N * S2 / 2)) := by
        gcongr
    _ ≤ 10 * (N : ℝ) ^ 3 := by
        have hm' : (2 * m : ℝ) ≤ N := by
          have : (N : ℝ) = 2 * m + 1 := by exact_mod_cast hN
          linarith
        have hS2nn : 0 ≤ S2 := Finset.sum_nonneg fun q hq => by positivity
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        have e1 : 2 * (2 * (N * S1 ^ 2) + 2 * (8 * N) * (N * S2 / 2))
            = (N : ℝ) * (4 * S1 ^ 2 + 16 * N * S2) := by ring
        rw [e1]
        have h1 : 4 * S1 ^ 2 + 16 * N * S2 ≤ 4 * (2 * m) * S2 + 16 * N * S2 := by linarith
        have h2 : 4 * (2 * m) * S2 + 16 * N * S2 ≤ 20 * N * S2 := by nlinarith
        have h3 : 20 * N * S2 ≤ 80 * (N : ℝ) ^ 3 := by nlinarith
        have h4 : 80 * (N : ℝ) ^ 3 ≤ 10 * N ^ 3 * Kc N := by nlinarith [pow_pos hNpos 3]
        have h5 : 4 * S1 ^ 2 + 16 * N * S2 ≤ 10 * N ^ 3 * Kc N := by linarith
        calc (N : ℝ) * (4 * S1 ^ 2 + 16 * N * S2) ≤ N * (10 * N ^ 3 * Kc N) :=
              mul_le_mul_of_nonneg_left h5 hNpos.le
          _ = 10 * (N : ℝ) ^ 3 * (Kc N * N) := by ring

/-- **`lem:supp-exact-rational-detuning` (Finite rational detuning).**  For every odd cutoff
`N = 2m + 1 > 40` (`h = 1/N`) there is a rational `θ_h` with `1 < θ_h < 1 + h` such that, for
`α_h = (1, θ_h, 1)`, the diagonal lapse source `𝒟_{h,α_h}` of `eq:supp-exact-diagonal-source`
(the cosine defect `D_h` of `eq:supp-exact-cosine-defect` acting along each axis) satisfies
`‖𝒟_{h,α_h} n‖² ≥ (h⁶)² ‖n‖²` for every mean-zero lapse `n` (`eq:supp-exact-diagonal-margin`
with `c = 1`; the grid weight `h³` of `‖·‖_h` cancels on both sides). -/
theorem rational_detuning {m : ℕ} (hN : N = 2 * m + 1) (hfine : 40 < N) :
    ∃ θ : ℚ, 1 < (θ : ℝ) ∧ (θ : ℝ) < 1 + 1 / N ∧
      ∀ n : (Fin N × Fin N) × Fin N → ℝ, ∑ p, n p = 0 →
        ((1 / (N : ℝ)) ^ 6) ^ 2 * (n ⬝ᵥ n) ≤ sourceNormSq (cosineDefect N) θ n := by
  have hm : 1 ≤ m := by omega
  have hN' : (40 : ℝ) < N := by exact_mod_cast hfine
  refine rational_detuning_of_spectralInput (by omega) (cosineDefect_spectralInput hN hm) ?_ ?_
  · linarith
  · have h1 : (1 : ℝ) ≤ N := by linarith
    have h2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have : (N : ℝ) ≤ (N : ℝ) ^ 3 := by
      calc (N : ℝ) = N * 1 := by ring
        _ ≤ N * N ^ 2 := by gcongr
        _ = N ^ 3 := by ring
    linarith

/-- Non-vacuity: the spectral input at the coarsest odd cutoff `N = 3`. -/
example : CosineDefectSpectralInput 3 10 := cosineDefect_spectralInput (m := 1) rfl le_rfl

/-- Non-vacuity: the detuning lemma at `N = 41`. -/
example : ∃ θ : ℚ, 1 < (θ : ℝ) ∧ (θ : ℝ) < 1 + 1 / (41 : ℕ) ∧
    ∀ n : (Fin 41 × Fin 41) × Fin 41 → ℝ, ∑ p, n p = 0 →
      ((1 / ((41 : ℕ) : ℝ)) ^ 6) ^ 2 * (n ⬝ᵥ n) ≤ sourceNormSq (cosineDefect 41) θ n :=
  rational_detuning (m := 20) rfl (by norm_num)

end Defect

end

end CosineDefectSpectrum
end RenewalGeometry
