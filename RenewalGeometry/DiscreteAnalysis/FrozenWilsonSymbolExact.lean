/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Frozen symbol of the doubled Wilson operator and its unique zero

Paper `predictive_spectral_geometry`, label `thm:supp-general-Wilson-ellipticity`,
finite clauses.

* Abstract Clifford square (`clifford_symbol_sq`): in any algebra with elements
  `c j` satisfying `c j * c k + c k * c j = 2 g j k` and an element `Γ` that
  anticommutes with every `c j` and squares to one, the square of
  `Σ a_j • c j + b • Γ` is the scalar `Σ_{jk} g_jk a_j a_k + b²`.
* `eq:supp-general-frozen-symbol` (`frozenWilson_planeWave`): the constant-coefficient
  (frozen, trivial spin transport) doubled Wilson operator on `ℤ^d`, built from
  ordinary shifts, symmetric differences `(T - T*)/(2ih)` and the Wilson term
  `(1/2h) Σ (2 - T - T*)`, acts on the plane wave `x ↦ e^{iθ·x} v` by the matrix
  `q_h(θ) = h⁻¹ [Σ_j ĉ^j sin θ_j + ϖ Γ_⊥ Σ_j (1 - cos θ_j)]` (`frozenSymbol`).
* `eq:supp-general-frozen-square` (`frozenSymbol_sq`): `q_h(θ)² = h⁻² [g^{jk} sin θ_j sin θ_k
  + ϖ² (Σ_j (1 - cos θ_j))²] I`.
* Unique zero (`frozenSymbol_eq_zero_iff`): for positive semidefinite `g`, `ϖ ≠ 0`,
  the symbol vanishes iff every `θ_j ∈ 2πℤ`, i.e. only at `θ = 0` on the Brillouin torus.
* Uniform ellipticity of the scalar symbol (`frozenSymbolScalar_bounds`,
  `eq:frozen-uniform-ellipticity`): `min(λ, ϖ²) ℓ_h(θ) ≤ scalar ≤ (Λ + d ϖ²) ℓ_h(θ)` with
  `ℓ_h(θ) = 2 h⁻² Σ_j (1 - cos θ_j)` when `λ |ξ|² ≤ ξᵀ g ξ ≤ Λ |ξ|²`.

The cutoff-independent discrete Gårding estimate `eq:supp-general-Garding` for
variable coefficients is not treated here.
-/

open Matrix Finset

namespace RenewalGeometry.FrozenWilsonSymbol

/-! ### Abstract Clifford square -/

section abstractClifford

variable {K R ι : Type*} [CommRing K] [Ring R] [Algebra K R] [Fintype ι]

/-- **Clifford square.** With `c j c k + c k c j = 2 g j k`, `Γ c j + c j Γ = 0`
and `Γ² = 1`, the square of `Σ a_j c_j + b Γ` is the scalar
`Σ_{jk} g_{jk} a_j a_k + b²`. -/
theorem clifford_symbol_sq (c : ι → R) (Γ : R) (g : ι → ι → K)
    (hcc : ∀ j k, c j * c k + c k * c j = algebraMap K R (2 * g j k))
    (hΓc : ∀ j, Γ * c j + c j * Γ = 0) (hΓΓ : Γ * Γ = 1)
    (a : ι → K) (b : K) (h2 : IsUnit (2 : K)) :
    (∑ j, a j • c j + b • Γ) * (∑ j, a j • c j + b • Γ) =
      algebraMap K R (∑ j, ∑ k, g j k * (a j * a k) + b * b) := by
  set A := ∑ j, a j • c j with hA
  have hAA : A * A = algebraMap K R (∑ j, ∑ k, g j k * (a j * a k)) := by
    have hS : A * A = ∑ j, ∑ k, (a j * a k) • (c j * c k) := by
      rw [hA, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      rw [smul_mul_smul_comm]
    have hS' : A * A = ∑ j, ∑ k, (a j * a k) • (c k * c j) := by
      rw [hS, Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      rw [mul_comm (a k)]
    have htwo : A * A + A * A = algebraMap K R (2 * ∑ j, ∑ k, g j k * (a j * a k)) := by
      nth_rw 1 [hS]
      rw [hS', ← Finset.sum_add_distrib]
      simp only [← Finset.sum_add_distrib, ← smul_add, hcc, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      rw [Algebra.smul_def, ← map_mul]
      congr 1
      ring
    obtain ⟨u, hu⟩ := h2
    have hhalf : (↑u⁻¹ : K) * 2 = 1 := by rw [← hu]; exact u.inv_mul
    calc A * A = (↑u⁻¹ : K) • (A * A + A * A) := by
          rw [← two_smul K (A * A), smul_smul, hhalf, one_smul]
      _ = algebraMap K R (∑ j, ∑ k, g j k * (a j * a k)) := by
          rw [htwo, Algebra.smul_def, ← map_mul, ← mul_assoc, hhalf, one_mul]
  have hcross : A * (b • Γ) + (b • Γ) * A = 0 := by
    rw [hA, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (a j) b, ← smul_add,
      add_comm (c j * Γ), hΓc j, smul_zero]
  have hΓsq : (b • Γ) * (b • Γ) = algebraMap K R (b * b) := by
    rw [smul_mul_smul_comm, hΓΓ, Algebra.smul_def, mul_one]
  calc (A + b • Γ) * (A + b • Γ)
      = A * A + (A * (b • Γ) + (b • Γ) * A) + (b • Γ) * (b • Γ) := by
        rw [add_mul, mul_add, mul_add]
        abel
    _ = algebraMap K R (∑ j, ∑ k, g j k * (a j * a k) + b * b) := by
      rw [hAA, hcross, hΓsq, add_zero, map_add]

end abstractClifford

/-! ### The frozen symbol on the Brillouin torus -/

variable {d N : ℕ}

/-- `s(θ) = Σ_j (1 - cos θ_j)`. -/
noncomputable def wilsonScalar (θ : Fin d → ℝ) : ℝ := ∑ j, (1 - Real.cos (θ j))

/-- The frozen symbol `q_{h,x₀}(θ)` of `eq:supp-general-frozen-symbol`, with the
Clifford coefficients `ĉ^j(x₀)` and the normal factor `Γ_⊥` given as matrices. -/
noncomputable def frozenSymbol (h ϖ : ℝ) (c : Fin d → Matrix (Fin N) (Fin N) ℂ)
    (Γ : Matrix (Fin N) (Fin N) ℂ) (θ : Fin d → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  ((h : ℂ)⁻¹) • (∑ j, (Real.sin (θ j) : ℂ) • c j + ((ϖ * wilsonScalar θ : ℝ) : ℂ) • Γ)

/-- The scalar `h⁻² [g^{jk} sin θ_j sin θ_k + ϖ² s(θ)²]` of
`eq:supp-general-frozen-square`. -/
noncomputable def frozenSymbolScalar (h ϖ : ℝ) (g : Matrix (Fin d) (Fin d) ℝ)
    (θ : Fin d → ℝ) : ℝ :=
  (h ^ 2)⁻¹ * (∑ j, ∑ k, g j k * (Real.sin (θ j) * Real.sin (θ k)) +
    ϖ ^ 2 * wilsonScalar θ ^ 2)

/-- Clifford relations of the doubled coefficients: `ĉ^j ĉ^k + ĉ^k ĉ^j = 2 g^{jk}`,
`Γ_⊥` anticommutes with every `ĉ^j`, and `Γ_⊥² = 1`. -/
structure DoubledCliffordData (c : Fin d → Matrix (Fin N) (Fin N) ℂ)
    (Γ : Matrix (Fin N) (Fin N) ℂ) (g : Matrix (Fin d) (Fin d) ℝ) : Prop where
  anticomm : ∀ j k, c j * c k + c k * c j = ((2 * g j k : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)
  normal_anticomm : ∀ j, Γ * c j + c j * Γ = 0
  normal_sq : Γ * Γ = 1

/-- **`eq:supp-general-frozen-square`.** The square of the frozen symbol is the
scalar `frozenSymbolScalar` times the identity. -/
theorem frozenSymbol_sq (h ϖ : ℝ) (c : Fin d → Matrix (Fin N) (Fin N) ℂ)
    (Γ : Matrix (Fin N) (Fin N) ℂ) (g : Matrix (Fin d) (Fin d) ℝ)
    (hc : DoubledCliffordData c Γ g) (θ : Fin d → ℝ) :
    frozenSymbol h ϖ c Γ θ * frozenSymbol h ϖ c Γ θ =
      ((frozenSymbolScalar h ϖ g θ : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
  have hcc : ∀ j k, c j * c k + c k * c j =
      algebraMap ℂ (Matrix (Fin N) (Fin N) ℂ) (2 * ((g j k : ℝ) : ℂ)) := by
    intro j k
    rw [hc.anticomm j k, Algebra.algebraMap_eq_smul_one]
    push_cast
    rfl
  have key := clifford_symbol_sq c Γ (fun j k => ((g j k : ℝ) : ℂ)) hcc hc.normal_anticomm
    hc.normal_sq (fun j => (Real.sin (θ j) : ℂ)) ((ϖ * wilsonScalar θ : ℝ) : ℂ)
    (isUnit_iff_ne_zero.mpr two_ne_zero)
  unfold frozenSymbol
  rw [smul_mul_smul_comm, key, Algebra.algebraMap_eq_smul_one, smul_smul, frozenSymbolScalar]
  congr 1
  push_cast
  field_simp

/-! ### Uniform ellipticity and the unique zero -/

theorem wilsonScalar_nonneg (θ : Fin d → ℝ) : 0 ≤ wilsonScalar θ :=
  Finset.sum_nonneg fun j _ => by linarith [Real.cos_le_one (θ j)]

theorem one_sub_cos_le_wilsonScalar (θ : Fin d → ℝ) (j : Fin d) :
    1 - Real.cos (θ j) ≤ wilsonScalar θ := by
  unfold wilsonScalar
  exact Finset.single_le_sum (f := fun k => 1 - Real.cos (θ k))
    (fun k _ => by linarith [Real.cos_le_one (θ k)]) (Finset.mem_univ j)

theorem wilsonScalar_le (θ : Fin d → ℝ) : wilsonScalar θ ≤ 2 * d := by
  unfold wilsonScalar
  calc ∑ j, (1 - Real.cos (θ j)) ≤ ∑ _j : Fin d, (2 : ℝ) :=
        Finset.sum_le_sum fun j _ => by linarith [Real.neg_one_le_cos (θ j)]
    _ = 2 * d := by simp [mul_comm]

/-- `Σ_j sin² θ_j ≤ 2 s(θ)`. -/
theorem sum_sin_sq_le (θ : Fin d → ℝ) :
    ∑ j, Real.sin (θ j) ^ 2 ≤ 2 * wilsonScalar θ := by
  unfold wilsonScalar
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have := Real.sin_sq_add_cos_sq (θ j)
  nlinarith [Real.cos_le_one (θ j)]

/-- The elementary identity of the paper's proof, in inequality form:
`Σ_j sin² θ_j + s(θ)² ≥ 2 s(θ)`. -/
theorem two_wilsonScalar_le (θ : Fin d → ℝ) :
    2 * wilsonScalar θ ≤ ∑ j, Real.sin (θ j) ^ 2 + wilsonScalar θ ^ 2 := by
  have hsq : ∑ j, (1 - Real.cos (θ j)) ^ 2 ≤ wilsonScalar θ ^ 2 := by
    calc ∑ j, (1 - Real.cos (θ j)) ^ 2 ≤ ∑ j, (1 - Real.cos (θ j)) * wilsonScalar θ :=
          Finset.sum_le_sum fun j _ => by
            rw [sq]
            exact mul_le_mul_of_nonneg_left (one_sub_cos_le_wilsonScalar θ j)
              (by linarith [Real.cos_le_one (θ j)])
      _ = wilsonScalar θ ^ 2 := by rw [← Finset.sum_mul, sq]; rfl
  have hsin : ∑ j, Real.sin (θ j) ^ 2 =
      2 * wilsonScalar θ - ∑ j, (1 - Real.cos (θ j)) ^ 2 := by
    unfold wilsonScalar
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := Real.sin_sq_add_cos_sq (θ j)
    nlinarith
  linarith

/-- **`eq:frozen-uniform-ellipticity`.** For `λ |ξ|² ≤ ξᵀ g ξ ≤ Λ |ξ|²` the scalar
symbol is comparable to `ℓ_h(θ) = 2 h⁻² s(θ)` with constants `min(λ, ϖ²)` and
`Λ + d ϖ²`, uniformly on the Brillouin torus. -/
theorem frozenSymbolScalar_bounds (h ϖ lam Lam : ℝ) (hh : h ≠ 0) (hlam : 0 ≤ lam)
    (hLam : 0 ≤ Lam) (g : Matrix (Fin d) (Fin d) ℝ)
    (hlow : ∀ ξ : Fin d → ℝ, lam * ∑ j, ξ j ^ 2 ≤ ∑ j, ∑ k, g j k * (ξ j * ξ k))
    (hup : ∀ ξ : Fin d → ℝ, ∑ j, ∑ k, g j k * (ξ j * ξ k) ≤ Lam * ∑ j, ξ j ^ 2)
    (θ : Fin d → ℝ) :
    min lam (ϖ ^ 2) * (2 * (h ^ 2)⁻¹ * wilsonScalar θ) ≤ frozenSymbolScalar h ϖ g θ ∧
      frozenSymbolScalar h ϖ g θ ≤ (Lam + d * ϖ ^ 2) * (2 * (h ^ 2)⁻¹ * wilsonScalar θ) := by
  have hinv : 0 < (h ^ 2)⁻¹ := inv_pos.mpr (by positivity)
  have hs := wilsonScalar_nonneg θ
  have hsd := wilsonScalar_le θ
  have hsinsq : ∑ j, Real.sin (θ j) ^ 2 ≤ 2 * wilsonScalar θ := sum_sin_sq_le θ
  have hsum : 2 * wilsonScalar θ ≤ ∑ j, Real.sin (θ j) ^ 2 + wilsonScalar θ ^ 2 :=
    two_wilsonScalar_le θ
  have hsin_nonneg : 0 ≤ ∑ j, Real.sin (θ j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hl := hlow fun j => Real.sin (θ j)
  have hu := hup fun j => Real.sin (θ j)
  have hmin1 : min lam (ϖ ^ 2) ≤ lam := min_le_left _ _
  have hmin2 : min lam (ϖ ^ 2) ≤ ϖ ^ 2 := min_le_right _ _
  unfold frozenSymbolScalar
  constructor
  · have hcore : min lam (ϖ ^ 2) * (2 * wilsonScalar θ) ≤
        ∑ j, ∑ k, g j k * (Real.sin (θ j) * Real.sin (θ k)) + ϖ ^ 2 * wilsonScalar θ ^ 2 := by
      calc min lam (ϖ ^ 2) * (2 * wilsonScalar θ)
          ≤ min lam (ϖ ^ 2) * (∑ j, Real.sin (θ j) ^ 2 + wilsonScalar θ ^ 2) :=
            mul_le_mul_of_nonneg_left hsum (le_min hlam (sq_nonneg _))
        _ = min lam (ϖ ^ 2) * ∑ j, Real.sin (θ j) ^ 2 + min lam (ϖ ^ 2) * wilsonScalar θ ^ 2 := by
            ring
        _ ≤ lam * ∑ j, Real.sin (θ j) ^ 2 + ϖ ^ 2 * wilsonScalar θ ^ 2 :=
            add_le_add (mul_le_mul_of_nonneg_right hmin1 hsin_nonneg)
              (mul_le_mul_of_nonneg_right hmin2 (sq_nonneg _))
        _ ≤ _ := by linarith
    calc min lam (ϖ ^ 2) * (2 * (h ^ 2)⁻¹ * wilsonScalar θ)
        = (h ^ 2)⁻¹ * (min lam (ϖ ^ 2) * (2 * wilsonScalar θ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcore hinv.le
  · have hcore : ∑ j, ∑ k, g j k * (Real.sin (θ j) * Real.sin (θ k)) + ϖ ^ 2 * wilsonScalar θ ^ 2
        ≤ (Lam + d * ϖ ^ 2) * (2 * wilsonScalar θ) := by
      have h1 : ∑ j, ∑ k, g j k * (Real.sin (θ j) * Real.sin (θ k)) ≤ Lam * (2 * wilsonScalar θ) := by
        exact hu.trans (mul_le_mul_of_nonneg_left hsinsq hLam)
      have h2 : ϖ ^ 2 * wilsonScalar θ ^ 2 ≤ d * ϖ ^ 2 * (2 * wilsonScalar θ) := by
        have : wilsonScalar θ ^ 2 ≤ 2 * d * wilsonScalar θ := by nlinarith
        nlinarith [sq_nonneg ϖ]
      nlinarith
    calc _ ≤ (h ^ 2)⁻¹ * ((Lam + d * ϖ ^ 2) * (2 * wilsonScalar θ)) :=
          mul_le_mul_of_nonneg_left hcore hinv.le
      _ = _ := by ring

/-- The scalar symbol vanishes only when every `cos θ_j = 1` (positive
semidefinite `g`, `ϖ ≠ 0`, `h ≠ 0`). -/
theorem frozenSymbolScalar_eq_zero_iff (h ϖ : ℝ) (hh : h ≠ 0) (hϖ : ϖ ≠ 0)
    (g : Matrix (Fin d) (Fin d) ℝ)
    (hg : ∀ ξ : Fin d → ℝ, 0 ≤ ∑ j, ∑ k, g j k * (ξ j * ξ k)) (θ : Fin d → ℝ) :
    frozenSymbolScalar h ϖ g θ = 0 ↔ ∀ j, Real.cos (θ j) = 1 := by
  have hinv : 0 < (h ^ 2)⁻¹ := inv_pos.mpr (by positivity)
  have hq := hg fun j => Real.sin (θ j)
  have hs := wilsonScalar_nonneg θ
  constructor
  · intro h0
    have hprod : ∑ j, ∑ k, g j k * (Real.sin (θ j) * Real.sin (θ k)) +
        ϖ ^ 2 * wilsonScalar θ ^ 2 = 0 := by
      unfold frozenSymbolScalar at h0
      rcases mul_eq_zero.mp h0 with h0 | h0
      · exact absurd h0 hinv.ne'
      · exact h0
    have hs0 : wilsonScalar θ = 0 := by
      have hϖ2 : 0 < ϖ ^ 2 := by positivity
      have : ϖ ^ 2 * wilsonScalar θ ^ 2 = 0 := by nlinarith [sq_nonneg (wilsonScalar θ)]
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' hϖ2.ne'
      · exact pow_eq_zero_iff two_ne_zero |>.mp h'
    intro j
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => by linarith [Real.cos_le_one (θ k)])).mp hs0 j (Finset.mem_univ j)
    linarith
  · intro hcos
    have hsin : ∀ j, Real.sin (θ j) = 0 := fun j => by
      have := Real.sin_sq_add_cos_sq (θ j)
      rw [hcos j] at this
      nlinarith [sq_nonneg (Real.sin (θ j))]
    have hs0 : wilsonScalar θ = 0 := by
      unfold wilsonScalar
      exact Finset.sum_eq_zero fun j _ => by rw [hcos j]; ring
    unfold frozenSymbolScalar
    rw [hs0]
    simp [hsin]

/-- **Unique zero on the Brillouin torus.** For positive semidefinite `g`,
`ϖ ≠ 0`, `h ≠ 0` and a nontrivial spin module, the frozen symbol vanishes
exactly when every `θ_j` lies in `2πℤ`, i.e. only at `θ = 0` on the torus. -/
theorem frozenSymbol_eq_zero_iff (h ϖ : ℝ) (hh : h ≠ 0) (hϖ : ϖ ≠ 0) [NeZero N]
    (c : Fin d → Matrix (Fin N) (Fin N) ℂ) (Γ : Matrix (Fin N) (Fin N) ℂ)
    (g : Matrix (Fin d) (Fin d) ℝ) (hc : DoubledCliffordData c Γ g)
    (hg : ∀ ξ : Fin d → ℝ, 0 ≤ ∑ j, ∑ k, g j k * (ξ j * ξ k)) (θ : Fin d → ℝ) :
    frozenSymbol h ϖ c Γ θ = 0 ↔ ∀ j, ∃ n : ℤ, θ j = n * (2 * Real.pi) := by
  have hcos : (∀ j, ∃ n : ℤ, θ j = n * (2 * Real.pi)) ↔ ∀ j, Real.cos (θ j) = 1 := by
    refine forall_congr' fun j => ?_
    rw [Real.cos_eq_one_iff]
    exact exists_congr fun n => eq_comm
  rw [hcos, ← frozenSymbolScalar_eq_zero_iff h ϖ hh hϖ g hg θ]
  constructor
  · intro h0
    have := frozenSymbol_sq h ϖ c Γ g hc θ
    rw [h0, mul_zero] at this
    have h1 : ((frozenSymbolScalar h ϖ g θ : ℝ) : ℂ) = 0 := by
      have := congrFun (congrFun this ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩)
        ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩
      simpa using this.symm
    exact_mod_cast h1
  · intro h0
    have hcos' := (frozenSymbolScalar_eq_zero_iff h ϖ hh hϖ g hg θ).mp h0
    have hsin : ∀ j, Real.sin (θ j) = 0 := fun j => by
      have := Real.sin_sq_add_cos_sq (θ j)
      rw [hcos' j] at this
      nlinarith [sq_nonneg (Real.sin (θ j))]
    have hs0 : wilsonScalar θ = 0 := by
      unfold wilsonScalar
      exact Finset.sum_eq_zero fun j _ => by rw [hcos' j]; ring
    unfold frozenSymbol
    rw [hs0]
    simp [hsin]

/-! ### The frozen lattice operator acts on plane waves by the symbol -/

/-- Lattice sections `ℤ^d → ℂ^N`. -/
abbrev LatticeSection (d N : ℕ) := (Fin d → ℤ) → (Fin N → ℂ)

/-- The coordinate shift `T_j ψ (x) = ψ(x + e_j)` (frozen spin transport is trivial). -/
def shift (j : Fin d) (ψ : LatticeSection d N) : LatticeSection d N :=
  fun x => ψ (x + Pi.single j 1)

/-- The adjoint shift `T_j^* ψ (x) = ψ(x - e_j)`. -/
def shiftAdj (j : Fin d) (ψ : LatticeSection d N) : LatticeSection d N :=
  fun x => ψ (x - Pi.single j 1)

/-- The symmetric difference `P_j = (T_j - T_j^*) / (2 i h)` of `eq:supp-covariant-differences`. -/
noncomputable def symmetricDifference (h : ℝ) (j : Fin d) (ψ : LatticeSection d N) :
    LatticeSection d N :=
  fun x => (2 * Complex.I * (h : ℂ))⁻¹ • (shift j ψ x - shiftAdj j ψ x)

/-- The Wilson term `W = (1/2h) Σ_j (2 - T_j - T_j^*)` of `eq:supp-covariant-differences`. -/
noncomputable def wilsonTerm (h : ℝ) (ψ : LatticeSection d N) : LatticeSection d N :=
  fun x => (2 * (h : ℂ))⁻¹ • ∑ j, ((2 : ℂ) • ψ x - shift j ψ x - shiftAdj j ψ x)

/-- Pointwise multiplication by a constant matrix. -/
def matMul (M : Matrix (Fin N) (Fin N) ℂ) (ψ : LatticeSection d N) : LatticeSection d N :=
  fun x => M *ᵥ ψ x

/-- The frozen (constant-coefficient) doubled Wilson operator of `eq:supp-general-Wilson`:
`½ Σ_j (M_{ĉ^j} P_j + P_j M_{ĉ^j}) + ϖ Γ_⊥ W`. -/
noncomputable def frozenWilson (h ϖ : ℝ) (c : Fin d → Matrix (Fin N) (Fin N) ℂ)
    (Γ : Matrix (Fin N) (Fin N) ℂ) (ψ : LatticeSection d N) : LatticeSection d N :=
  fun x => (2 : ℂ)⁻¹ • ∑ j, (matMul (c j) (symmetricDifference h j ψ) x +
      symmetricDifference h j (matMul (c j) ψ) x) +
    (ϖ : ℂ) • matMul Γ (wilsonTerm h ψ) x

/-- The plane wave `x ↦ e^{i θ·x} v`. -/
noncomputable def planeWave (θ : Fin d → ℝ) (v : Fin N → ℂ) : LatticeSection d N :=
  fun x => Complex.exp (Complex.I * ∑ j, (θ j : ℂ) * (x j : ℂ)) • v

theorem shift_planeWave (θ : Fin d → ℝ) (v : Fin N → ℂ) (j : Fin d) (x : Fin d → ℤ) :
    shift j (planeWave θ v) x = Complex.exp (Complex.I * (θ j : ℂ)) • planeWave θ v x := by
  unfold shift planeWave
  rw [smul_smul, ← Complex.exp_add]
  congr 2
  simp only [Pi.add_apply, Pi.single_apply, Int.cast_add, Int.cast_ite, Int.cast_one,
    Int.cast_zero, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

theorem shiftAdj_planeWave (θ : Fin d → ℝ) (v : Fin N → ℂ) (j : Fin d) (x : Fin d → ℤ) :
    shiftAdj j (planeWave θ v) x = Complex.exp (-(Complex.I * (θ j : ℂ))) • planeWave θ v x := by
  unfold shiftAdj planeWave
  rw [smul_smul, ← Complex.exp_add]
  congr 2
  simp only [Pi.sub_apply, Pi.single_apply, Int.cast_sub, Int.cast_ite, Int.cast_one,
    Int.cast_zero, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- `e^{iθ} - e^{-iθ} = 2 i sin θ`. -/
theorem exp_sub_exp_neg (θ : ℝ) :
    Complex.exp (Complex.I * (θ : ℂ)) - Complex.exp (-(Complex.I * (θ : ℂ))) =
      2 * Complex.I * (Real.sin θ : ℂ) := by
  rw [Complex.ofReal_sin]
  have := Complex.two_sin (θ : ℂ)
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have h1 : Complex.exp (Complex.I * (θ : ℂ)) = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [mul_comm]
  have h2 : Complex.exp (-(Complex.I * (θ : ℂ))) = Complex.exp (-(θ : ℂ) * Complex.I) := by
    rw [neg_mul, mul_comm]
  rw [h1, h2]
  linear_combination (-Complex.I) * this +
    (Complex.exp ((θ : ℂ) * Complex.I) - Complex.exp (-(θ : ℂ) * Complex.I)) * hI

/-- `2 - e^{iθ} - e^{-iθ} = 2 (1 - cos θ)`. -/
theorem two_sub_exp_sub_exp_neg (θ : ℝ) :
    (2 : ℂ) - Complex.exp (Complex.I * (θ : ℂ)) - Complex.exp (-(Complex.I * (θ : ℂ))) =
      2 * ((1 - Real.cos θ : ℝ) : ℂ) := by
  push_cast
  have := Complex.two_cos (θ : ℂ)
  have h1 : Complex.exp (Complex.I * (θ : ℂ)) = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [mul_comm]
  have h2 : Complex.exp (-(Complex.I * (θ : ℂ))) = Complex.exp (-(θ : ℂ) * Complex.I) := by
    rw [neg_mul, mul_comm]
  rw [h1, h2]
  linear_combination this

theorem symmetricDifference_planeWave (h : ℝ) (hh : h ≠ 0) (θ : Fin d → ℝ) (v : Fin N → ℂ)
    (j : Fin d) (x : Fin d → ℤ) :
    symmetricDifference h j (planeWave θ v) x =
      ((Real.sin (θ j) / h : ℝ) : ℂ) • planeWave θ v x := by
  unfold symmetricDifference
  rw [shift_planeWave, shiftAdj_planeWave, ← sub_smul, smul_smul, exp_sub_exp_neg]
  congr 1
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  push_cast
  field_simp

theorem wilsonTerm_planeWave (h : ℝ) (θ : Fin d → ℝ) (v : Fin N → ℂ) (x : Fin d → ℤ) :
    wilsonTerm h (planeWave θ v) x = ((wilsonScalar θ / h : ℝ) : ℂ) • planeWave θ v x := by
  unfold wilsonTerm
  simp only [shift_planeWave, shiftAdj_planeWave, ← sub_smul, ← Finset.sum_smul, smul_smul]
  congr 1
  simp only [two_sub_exp_sub_exp_neg, ← Finset.mul_sum, wilsonScalar]
  push_cast
  rcases eq_or_ne h 0 with h0 | h0
  · simp [h0]
  · field_simp

theorem matMul_planeWave (M : Matrix (Fin N) (Fin N) ℂ) (θ : Fin d → ℝ) (v : Fin N → ℂ) :
    matMul M (planeWave θ v) = planeWave θ (M *ᵥ v) := by
  funext x
  simp [matMul, planeWave, Matrix.mulVec_smul]

theorem symmetricDifference_matMul (h : ℝ) (j : Fin d) (M : Matrix (Fin N) (Fin N) ℂ)
    (ψ : LatticeSection d N) :
    symmetricDifference h j (matMul M ψ) = matMul M (symmetricDifference h j ψ) := by
  funext x
  simp [symmetricDifference, matMul, shift, shiftAdj, Matrix.mulVec_smul, Matrix.mulVec_sub,
    Matrix.mulVec_neg]

/-- **`eq:supp-general-frozen-symbol`.** The frozen doubled Wilson operator acts on
the plane wave `e^{iθ·x} v` by the matrix symbol `q_h(θ)`: the symbol of the
constant-coefficient operator is exactly `frozenSymbol`. -/
theorem frozenWilson_planeWave (h ϖ : ℝ) (hh : h ≠ 0)
    (c : Fin d → Matrix (Fin N) (Fin N) ℂ) (Γ : Matrix (Fin N) (Fin N) ℂ)
    (θ : Fin d → ℝ) (v : Fin N → ℂ) :
    frozenWilson h ϖ c Γ (planeWave θ v) = planeWave θ (frozenSymbol h ϖ c Γ θ *ᵥ v) := by
  funext x
  unfold frozenWilson
  simp only [matMul_planeWave, symmetricDifference_planeWave h hh,
    wilsonTerm_planeWave, matMul, Matrix.mulVec_smul]
  unfold planeWave frozenSymbol
  simp only [Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.sum_mulVec,
    Finset.smul_sum, smul_add, smul_smul]
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  simp only [smul_smul, ← two_smul ℂ]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    push_cast
    field_simp
    try ring
  · congr 1
    push_cast
    field_simp
    try ring

end RenewalGeometry.FrozenWilsonSymbol
