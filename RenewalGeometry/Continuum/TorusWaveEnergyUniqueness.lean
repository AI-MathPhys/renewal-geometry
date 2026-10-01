/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.TorusSobolevTransfer

/-!
# Energy uniqueness for linear second-order hyperbolic systems on `𝕋³`
  (infrastructure for `lem:supp-open-subsidiary` and the vacuum clause of
  `thm:supp-open-einstein`; emergent-spacetime manuscript)

Classical solutions on `[0, T] × 𝕋³` of a linear system with a scalar (diagonal) hyperbolic
principal part, in the normal form

`a ∂ₜ²u_b = 2 βⁱ ∂ᵢ∂ₜu_b + γ^{ij} ∂ᵢ∂ⱼu_b + L_b`,

with `a ≥ a₀ > 0`, `γ^{ij}` symmetric and uniformly positive (`γ^{ij}ξᵢξⱼ ≥ λ|ξ|²`), bounded
coefficient derivatives `∂ₜa`, `∂ᵢβⁱ`, `∂ₜγ^{ij}`, `∂ᵢγ^{ij}`, and a lower-order term with
`Σ_b L_b² ≤ M Σ_b (|∂ₜu_b|² + |∇u_b|² + u_b²)` (e.g. any linear combination of `u`, `∂u` with bounded
coefficients).  For the subsidiary system of the harmonic gauge, `a = -g^{00}`, `βⁱ = g^{0i}`,
`γ^{ij} = g^{ij}`.

* `integral_lineDeriv_eq_zero` — `∫_{𝕋³} ∂ᵢF = 0` for a continuous `F` with continuous classical
  derivative (the zero Fourier mode of `mFourierCoeff_of_isLineDeriv`); this is the
  integration-by-parts rule on the torus.
* `WaveData`, `WaveData.Solves` — the data and hypotheses (time derivatives on `(0, T)`, classical
  spatial derivatives, joint continuity on `ℝ × 𝕋³`).
* `WaveData.energy_deriv_le` — the energy `E(t) = ∫ Σ_b (a|∂ₜu_b|² + γ^{ij}∂ᵢu_b∂ⱼu_b + u_b²)`
  satisfies `E' ≤ K E` on `(0, T)`, with `K` depending only on `a₀, λ, M`.
* `WaveData.eq_zero_of_zero_data` (**uniqueness**): zero Cauchy data `u(0) = ∂ₜu(0) = 0` force
  `u ≡ 0` on `[0, T] × 𝕋³`.
-/

open MeasureTheory Filter Topology UnitAddTorus Set
open scoped BigOperators

namespace RenewalGeometry.TorusWaveEnergy

open TorusSobolevTransfer

/-! The Haar measure of `UnitAddCircle` (the instance used by `mFourierCoeff`). -/

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : MeasureTheory.IsProbabilityMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : MeasureTheory.Measure.IsAddHaarMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

noncomputable section

set_option linter.unusedSectionVars false

/-- The unit torus `𝕋³`. -/
abbrev T3 := UnitAddTorus (Fin 3)

theorem integrable_of_continuous {f : T3 → ℝ} (hf : Continuous f) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- **Integration by parts on `𝕋³`**: the integral of a continuous classical partial derivative
vanishes. -/
theorem integral_lineDeriv_eq_zero {i : Fin 3} {F F' : T3 → ℝ} (hF : Continuous F)
    (hF' : Continuous F') (h : IsLineDeriv i F F') : ∫ x, F' x = 0 := by
  have h1 := mFourierCoeff_of_isLineDeriv i ⟨fun x => (F x : ℂ), by fun_prop⟩
    ⟨fun x => (F' x : ℂ), by fun_prop⟩ h.ofReal 0
  simp only [mFourierCoeff, neg_zero, mFourier_zero, ContinuousMap.coe_mk, Pi.zero_apply,
    Int.cast_zero, mul_zero, zero_mul] at h1
  have h2 : ∫ x, (F' x : ℂ) = ((∫ x, F' x : ℝ) : ℂ) := integral_ofReal
  simp only [ContinuousMap.one_apply, one_smul] at h1
  have h3 : ((∫ x, F' x : ℝ) : ℂ) = 0 := by rw [← h2]; exact h1
  exact_mod_cast h3

/-! ### The data of a linear wave system -/

/-- Fields and coefficients of a linear second-order system on `ℝ × 𝕋³`: `u` with its time
derivatives `ut, utt`, spatial derivatives `ux i = ∂ᵢu`, `uxt i = ∂ᵢ∂ₜu`, `uxx i j = ∂ᵢ∂ⱼu`;
coefficients `a` (`∂ₜa = at'`), `β i` (`∂ᵢβⁱ = βdiv i`), `γ i j` (`∂ₜγ = γt`, `∂ᵢγ^{ij} = γx i j`);
the lower-order term `L`. -/
structure WaveData (ι : Type*) where
  u : ℝ → T3 → ι → ℝ
  ut : ℝ → T3 → ι → ℝ
  utt : ℝ → T3 → ι → ℝ
  ux : ℝ → Fin 3 → T3 → ι → ℝ
  uxt : ℝ → Fin 3 → T3 → ι → ℝ
  uxx : ℝ → Fin 3 → Fin 3 → T3 → ι → ℝ
  a : ℝ → T3 → ℝ
  at' : ℝ → T3 → ℝ
  β : ℝ → Fin 3 → T3 → ℝ
  βdiv : ℝ → Fin 3 → T3 → ℝ
  γ : ℝ → Fin 3 → Fin 3 → T3 → ℝ
  γt : ℝ → Fin 3 → Fin 3 → T3 → ℝ
  γx : ℝ → Fin 3 → Fin 3 → T3 → ℝ
  L : ℝ → T3 → ι → ℝ

variable {ι : Type*} [Fintype ι]

/-- The hypotheses: joint continuity, the derivative relations, the equation
`a utt = 2 βⁱ uxtᵢ + γ^{ij} uxxᵢⱼ + L` on `(0, T)`, coercivity and coefficient bounds on `[0, T]`. -/
structure WaveData.Solves (D : WaveData ι) (T a₀ lam M : ℝ) : Prop where
  cont_u : ∀ b, Continuous fun p : ℝ × T3 => D.u p.1 p.2 b
  cont_ut : ∀ b, Continuous fun p : ℝ × T3 => D.ut p.1 p.2 b
  cont_utt : ∀ b, Continuous fun p : ℝ × T3 => D.utt p.1 p.2 b
  cont_ux : ∀ i b, Continuous fun p : ℝ × T3 => D.ux p.1 i p.2 b
  cont_uxt : ∀ i b, Continuous fun p : ℝ × T3 => D.uxt p.1 i p.2 b
  cont_uxx : ∀ i j b, Continuous fun p : ℝ × T3 => D.uxx p.1 i j p.2 b
  cont_a : Continuous fun p : ℝ × T3 => D.a p.1 p.2
  cont_at : Continuous fun p : ℝ × T3 => D.at' p.1 p.2
  cont_β : ∀ i, Continuous fun p : ℝ × T3 => D.β p.1 i p.2
  cont_βdiv : ∀ i, Continuous fun p : ℝ × T3 => D.βdiv p.1 i p.2
  cont_γ : ∀ i j, Continuous fun p : ℝ × T3 => D.γ p.1 i j p.2
  cont_γt : ∀ i j, Continuous fun p : ℝ × T3 => D.γt p.1 i j p.2
  cont_γx : ∀ i j, Continuous fun p : ℝ × T3 => D.γx p.1 i j p.2
  cont_L : ∀ b, Continuous fun p : ℝ × T3 => D.L p.1 p.2 b
  dt_u : ∀ t ∈ Ioo 0 T, ∀ x b, HasDerivAt (fun s => D.u s x b) (D.ut t x b) t
  dt_ut : ∀ t ∈ Ioo 0 T, ∀ x b, HasDerivAt (fun s => D.ut s x b) (D.utt t x b) t
  dt_ux : ∀ t ∈ Ioo 0 T, ∀ i x b, HasDerivAt (fun s => D.ux s i x b) (D.uxt t i x b) t
  dt_a : ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun s => D.a s x) (D.at' t x) t
  dt_γ : ∀ t ∈ Ioo 0 T, ∀ i j x, HasDerivAt (fun s => D.γ s i j x) (D.γt t i j x) t
  dx_u : ∀ t ∈ Icc 0 T, ∀ i b, IsLineDeriv i (fun x => D.u t x b) (fun x => D.ux t i x b)
  dx_ut : ∀ t ∈ Ioo 0 T, ∀ i b, IsLineDeriv i (fun x => D.ut t x b) (fun x => D.uxt t i x b)
  dx_ux : ∀ t ∈ Ioo 0 T, ∀ i j b, IsLineDeriv i (fun x => D.ux t j x b) (fun x => D.uxx t i j x b)
  dx_β : ∀ t ∈ Ioo 0 T, ∀ i, IsLineDeriv i (D.β t i) (D.βdiv t i)
  dx_γ : ∀ t ∈ Ioo 0 T, ∀ i j, IsLineDeriv i (D.γ t i j) (D.γx t i j)
  γ_symm : ∀ t i j x, D.γ t i j x = D.γ t j i x
  eqn : ∀ t ∈ Ioo 0 T, ∀ x b, D.a t x * D.utt t x b =
    2 * ∑ i, D.β t i x * D.uxt t i x b + ∑ i, ∑ j, D.γ t i j x * D.uxx t i j x b + D.L t x b
  coer_a : ∀ t ∈ Icc 0 T, ∀ x, a₀ ≤ D.a t x
  coer_γ : ∀ t ∈ Icc 0 T, ∀ x (ξ : Fin 3 → ℝ),
    lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, D.γ t i j x * ξ i * ξ j
  bnd_at : ∀ t ∈ Icc 0 T, ∀ x, |D.at' t x| ≤ M
  bnd_βdiv : ∀ t ∈ Icc 0 T, ∀ i x, |D.βdiv t i x| ≤ M
  bnd_γt : ∀ t ∈ Icc 0 T, ∀ i j x, |D.γt t i j x| ≤ M
  bnd_γx : ∀ t ∈ Icc 0 T, ∀ i j x, |D.γx t i j x| ≤ M
  bnd_L : ∀ t ∈ Icc 0 T, ∀ x, ∑ b, D.L t x b ^ 2 ≤
    M * ∑ b, (D.ut t x b ^ 2 + ∑ i, D.ux t i x b ^ 2 + D.u t x b ^ 2)

namespace WaveData

variable (D : WaveData ι)

/-- The energy density `Σ_b (a|∂ₜu_b|² + γ^{ij}∂ᵢu_b∂ⱼu_b + u_b²)`. -/
def dens (t : ℝ) (x : T3) : ℝ :=
  ∑ b, (D.a t x * D.ut t x b ^ 2 + ∑ i, ∑ j, D.γ t i j x * D.ux t i x b * D.ux t j x b +
    D.u t x b ^ 2)

/-- The energy `E(t) = ∫ dens`. -/
def energy (t : ℝ) : ℝ := ∫ x, D.dens t x

/-- The time derivative of the density. -/
def densT (t : ℝ) (x : T3) : ℝ :=
  ∑ b, (D.at' t x * D.ut t x b ^ 2 + 2 * D.a t x * D.ut t x b * D.utt t x b +
    ∑ i, ∑ j, (D.γt t i j x * D.ux t i x b * D.ux t j x b +
      D.γ t i j x * D.uxt t i x b * D.ux t j x b + D.γ t i j x * D.ux t i x b * D.uxt t j x b) +
    2 * D.u t x b * D.ut t x b)

/-- The density derivative after the equation and the integrations by parts. -/
def densG (t : ℝ) (x : T3) : ℝ :=
  ∑ b, (D.at' t x * D.ut t x b ^ 2 - 2 * ∑ i, D.βdiv t i x * D.ut t x b ^ 2 -
    2 * ∑ i, ∑ j, D.γx t i j x * D.ut t x b * D.ux t j x b +
    ∑ i, ∑ j, D.γt t i j x * D.ux t i x b * D.ux t j x b +
    2 * D.u t x b * D.ut t x b + 2 * D.ut t x b * D.L t x b)

/-- The squared size `Σ_b (|∂ₜu_b|² + |∇u_b|² + u_b²)`. -/
def size (t : ℝ) (x : T3) : ℝ :=
  ∑ b, (D.ut t x b ^ 2 + ∑ i, D.ux t i x b ^ 2 + D.u t x b ^ 2)

variable {D} {T a₀ lam M : ℝ}

theorem continuous_dens (h : D.Solves T a₀ lam M) :
    Continuous fun p : ℝ × T3 => D.dens p.1 p.2 := by
  unfold dens
  have := h.cont_u; have := h.cont_ut; have := h.cont_ux; have := h.cont_a; have := h.cont_γ
  fun_prop

theorem continuous_densT (h : D.Solves T a₀ lam M) :
    Continuous fun p : ℝ × T3 => D.densT p.1 p.2 := by
  unfold densT
  have := h.cont_u; have := h.cont_ut; have := h.cont_ux; have := h.cont_a; have := h.cont_γ
  have := h.cont_at; have := h.cont_γt; have := h.cont_utt; have := h.cont_uxt
  fun_prop

theorem hasDerivAt_dens (h : D.Solves T a₀ lam M) {t : ℝ} (ht : t ∈ Ioo 0 T) (x : T3) :
    HasDerivAt (fun s => D.dens s x) (D.densT t x) t := by
  unfold dens densT
  refine HasDerivAt.fun_sum fun b _ => ?_
  have hu := h.dt_u t ht x b
  have hut := h.dt_ut t ht x b
  have ha := h.dt_a t ht x
  have h1 := ha.fun_mul (hut.fun_pow 2)
  have h3 := hu.fun_pow 2
  have h2 : HasDerivAt (fun s => ∑ i, ∑ j, D.γ s i j x * D.ux s i x b * D.ux s j x b)
      (∑ i, ∑ j, (D.γt t i j x * D.ux t i x b * D.ux t j x b +
        D.γ t i j x * D.uxt t i x b * D.ux t j x b +
        D.γ t i j x * D.ux t i x b * D.uxt t j x b)) t := by
    refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
    refine (((h.dt_γ t ht i j x).fun_mul (h.dt_ux t ht i x b)).fun_mul
      (h.dt_ux t ht j x b)).congr_deriv ?_
    ring
  refine ((h1.add h2).add h3).congr_deriv ?_
  simp only [Nat.cast_ofNat]
  ring

/-- Pointwise: `densT - densG` is a sum of spatial derivatives. -/
theorem densT_sub_densG (h : D.Solves T a₀ lam M) {t : ℝ} (ht : t ∈ Ioo 0 T) (x : T3) :
    D.densT t x - D.densG t x = ∑ b, (∑ i, 2 * (D.βdiv t i x * D.ut t x b ^ 2 +
        D.β t i x * (2 * D.ut t x b * D.uxt t i x b)) +
      ∑ i, ∑ j, 2 * (D.γx t i j x * D.ut t x b * D.ux t j x b +
        D.γ t i j x * D.uxt t i x b * D.ux t j x b +
        D.γ t i j x * D.ut t x b * D.uxx t i j x b)) := by
  unfold densT densG
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  have he := h.eqn t ht x b
  have g10 := h.γ_symm t 1 0 x
  have g20 := h.γ_symm t 2 0 x
  have g21 := h.γ_symm t 2 1 x
  simp only [Fin.sum_univ_three] at he ⊢
  rw [g10, g20, g21] at *
  linear_combination (2 * D.ut t x b) * he


/-! ### Integration by parts and the energy identity -/

theorem isLineDeriv_const_mul {i : Fin 3} {F F' : T3 → ℝ} (c : ℝ) (h : IsLineDeriv i F F') :
    IsLineDeriv i (fun x => c * F x) (fun x => c * F' x) := by
  intro x
  exact (h x).const_mul c

theorem continuous_slice {f : ℝ × T3 → ℝ} (hf : Continuous f) (t : ℝ) :
    Continuous fun x : T3 => f (t, x) :=
  hf.comp (Continuous.prodMk continuous_const continuous_id)

/-- **The energy identity**: `∫ densT = ∫ densG` on `(0, T)`. -/
theorem integral_densT_eq (h : D.Solves T a₀ lam M) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    ∫ x, D.densT t x = ∫ x, D.densG t x := by
  have cs := fun {f : ℝ × T3 → ℝ} (hf : Continuous f) => continuous_slice hf t
  -- the integrated spatial derivatives
  have hP : ∀ b i, ∫ x, 2 * (D.βdiv t i x * D.ut t x b ^ 2 +
      D.β t i x * (2 * D.ut t x b * D.uxt t i x b)) = 0 := by
    intro b i
    refine integral_lineDeriv_eq_zero (i := i) (F := fun x => 2 * (D.β t i x * D.ut t x b ^ 2))
      ?_ ?_ ?_
    · have := cs (h.cont_β i); have := cs (h.cont_ut b); fun_prop
    · have := cs (h.cont_β i); have := cs (h.cont_ut b); have := cs (h.cont_βdiv i)
      have := cs (h.cont_uxt i b); fun_prop
    · have h1 := (h.dx_β t ht i).mul ((h.dx_ut t ht i b).mul (h.dx_ut t ht i b))
      have h2 := isLineDeriv_const_mul 2 h1
      intro x
      have := h2 x
      simp only [] at this
      convert this using 1
      · funext s; ring
      · ring
  have hQ : ∀ b i j, ∫ x, 2 * (D.γx t i j x * D.ut t x b * D.ux t j x b +
      D.γ t i j x * D.uxt t i x b * D.ux t j x b +
      D.γ t i j x * D.ut t x b * D.uxx t i j x b) = 0 := by
    intro b i j
    refine integral_lineDeriv_eq_zero (i := i)
      (F := fun x => 2 * (D.γ t i j x * D.ut t x b * D.ux t j x b)) ?_ ?_ ?_
    · have := cs (h.cont_γ i j); have := cs (h.cont_ut b); have := cs (h.cont_ux j b); fun_prop
    · have := cs (h.cont_γ i j); have := cs (h.cont_ut b); have := cs (h.cont_ux j b)
      have := cs (h.cont_γx i j); have := cs (h.cont_uxt i b); have := cs (h.cont_uxx i j b)
      fun_prop
    · have h1 := ((h.dx_γ t ht i j).mul (h.dx_ut t ht i b)).mul (h.dx_ux t ht i j b)
      have h2 := isLineDeriv_const_mul 2 h1
      intro x
      convert h2 x using 1
      ring
  have hint : ∀ {f : T3 → ℝ}, Continuous f → Integrable f := fun hf => integrable_of_continuous hf
  have hT : Integrable fun x => D.densT t x := hint (cs (continuous_densT h))
  have hG : Integrable fun x => D.densG t x := by
    unfold densG
    have := fun b => cs (h.cont_u b); have := fun b => cs (h.cont_ut b)
    have := fun i b => cs (h.cont_ux i b); have := cs h.cont_at
    have := fun i => cs (h.cont_βdiv i); have := fun i j => cs (h.cont_γx i j)
    have := fun i j => cs (h.cont_γt i j); have := fun b => cs (h.cont_L b)
    exact hint (by fun_prop)
  have hPb : ∀ b, ∫ x, ∑ i, 2 * (D.βdiv t i x * D.ut t x b ^ 2 +
      D.β t i x * (2 * D.ut t x b * D.uxt t i x b)) = 0 := by
    intro b
    rw [integral_finsetSum _ fun i _ => ?_]
    · exact Finset.sum_eq_zero fun i _ => hP b i
    · have := cs (h.cont_β i); have := cs (h.cont_ut b); have := cs (h.cont_βdiv i)
      have := cs (h.cont_uxt i b)
      exact hint (by fun_prop)
  have hQb : ∀ b, ∫ x, ∑ i, ∑ j, 2 * (D.γx t i j x * D.ut t x b * D.ux t j x b +
      D.γ t i j x * D.uxt t i x b * D.ux t j x b +
      D.γ t i j x * D.ut t x b * D.uxx t i j x b) = 0 := by
    intro b
    rw [integral_finsetSum _ fun i _ => ?_]
    · refine Finset.sum_eq_zero fun i _ => ?_
      rw [integral_finsetSum _ fun j _ => ?_]
      · exact Finset.sum_eq_zero fun j _ => hQ b i j
      · have := cs (h.cont_γ i j); have := cs (h.cont_ut b); have := cs (h.cont_ux j b)
        have := cs (h.cont_γx i j); have := cs (h.cont_uxt i b); have := cs (h.cont_uxx i j b)
        exact hint (by fun_prop)
    · have := fun j => cs (h.cont_γ i j); have := cs (h.cont_ut b)
      have := fun j => cs (h.cont_ux j b)
      have := fun j => cs (h.cont_γx i j); have := cs (h.cont_uxt i b)
      have := fun j => cs (h.cont_uxx i j b)
      exact hint (by fun_prop)
  rw [← sub_eq_zero, ← integral_sub hT hG]
  simp only [densT_sub_densG h ht]
  rw [integral_finsetSum _ fun b _ => ?_]
  · refine Finset.sum_eq_zero fun b _ => ?_
    rw [integral_add, hPb, hQb, add_zero]
    · have := fun i => cs (h.cont_β i); have := cs (h.cont_ut b); have := fun i => cs (h.cont_βdiv i)
      have := fun i => cs (h.cont_uxt i b)
      exact hint (by fun_prop)
    · have := fun i j => cs (h.cont_γ i j); have := cs (h.cont_ut b)
      have := fun j => cs (h.cont_ux j b)
      have := fun i j => cs (h.cont_γx i j); have := fun i => cs (h.cont_uxt i b)
      have := fun i j => cs (h.cont_uxx i j b)
      exact hint (by fun_prop)
  · have := fun i => cs (h.cont_β i); have := cs (h.cont_ut b); have := fun i => cs (h.cont_βdiv i)
    have := fun i => cs (h.cont_uxt i b)
    have := fun i j => cs (h.cont_γ i j)
    have := fun j => cs (h.cont_ux j b)
    have := fun i j => cs (h.cont_γx i j)
    have := fun i j => cs (h.cont_uxx i j b)
    exact hint (by fun_prop)


/-! ### Differentiation of the energy and the energy inequality -/

theorem continuous_energy (h : D.Solves T a₀ lam M) : Continuous D.energy := by
  have := continuous_parametric_integral_of_continuous (μ := (volume : Measure T3))
    (f := fun t x => D.dens t x) (continuous_dens h) (s := Set.univ) isCompact_univ
  unfold energy
  simpa only [Measure.restrict_univ] using this

theorem hasDerivAt_energy (h : D.Solves T a₀ lam M) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt D.energy (∫ x, D.densT t x) t := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).prod (isCompact_univ (X := T3))
    |>.exists_bound_of_continuousOn (continuous_densT h).continuousOn
  have cs := fun {f : ℝ × T3 → ℝ} (hf : Continuous f) (s : ℝ) => continuous_slice hf s
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure T3))
    (F := fun s x => D.dens s x) (F' := fun s x => D.densT s x) (x₀ := t) (s := Ioo 0 T)
    (bound := fun _ => C) (isOpen_Ioo.mem_nhds ht)
    (Eventually.of_forall fun s => (cs (continuous_dens h) s).aestronglyMeasurable)
    (integrable_of_continuous (cs (continuous_dens h) t))
    (cs (continuous_densT h) t).aestronglyMeasurable
    (Eventually.of_forall fun x s hs => hC (s, x) ⟨Ioo_subset_Icc_self hs, Set.mem_univ _⟩)
    (integrable_const C)
    (Eventually.of_forall fun x s hs => hasDerivAt_dens h hs x)
  exact key.2

theorem abs_mul_le_half (c p q M : ℝ) (hc : |c| ≤ M) : c * p * q ≤ M * (p ^ 2 + q ^ 2) / 2 := by
  have hM : 0 ≤ M := (abs_nonneg c).trans hc
  have h1 : c * p * q ≤ |c| * (|p| * |q|) := by
    calc c * p * q ≤ |c * p * q| := le_abs_self _
      _ = |c| * (|p| * |q|) := by rw [abs_mul, abs_mul, mul_assoc]
  have h2 : |p| * |q| ≤ (p ^ 2 + q ^ 2) / 2 := by
    have := sq_nonneg (|p| - |q|)
    rw [← sq_abs p, ← sq_abs q]
    nlinarith
  calc c * p * q ≤ |c| * (|p| * |q|) := h1
    _ ≤ M * (|p| * |q|) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ ≤ M * ((p ^ 2 + q ^ 2) / 2) := mul_le_mul_of_nonneg_left h2 hM
    _ = M * (p ^ 2 + q ^ 2) / 2 := by ring

/-- The pointwise bound of one component of `densG`. -/
theorem densG_term_le (M at' ut u L : ℝ) (βd : Fin 3 → ℝ) (γx γt : Fin 3 → Fin 3 → ℝ)
    (ux : Fin 3 → ℝ) (hat : |at'| ≤ M) (hβ : ∀ i, |βd i| ≤ M) (hγx : ∀ i j, |γx i j| ≤ M)
    (hγt : ∀ i j, |γt i j| ≤ M) :
    at' * ut ^ 2 - 2 * ∑ i, βd i * ut ^ 2 - 2 * ∑ i, ∑ j, γx i j * ut * ux j +
      ∑ i, ∑ j, γt i j * ux i * ux j + 2 * u * ut + 2 * ut * L ≤
      (16 * M + 2) * (ut ^ 2 + ∑ i, ux i ^ 2 + u ^ 2) + L ^ 2 := by
  have hM : 0 ≤ M := (abs_nonneg _).trans hat
  have h1 : at' * ut ^ 2 ≤ M * ut ^ 2 :=
    mul_le_mul_of_nonneg_right ((le_abs_self _).trans hat) (sq_nonneg _)
  have h2 : ∀ i, -(βd i * ut ^ 2) ≤ M * ut ^ 2 := fun i => by
    rw [← neg_mul]
    exact mul_le_mul_of_nonneg_right ((neg_le_abs _).trans (hβ i)) (sq_nonneg _)
  have h3 : ∀ i j, -(γx i j * ut * ux j) ≤ M * (ut ^ 2 + ux j ^ 2) / 2 := fun i j => by
    rw [← neg_mul, ← neg_mul]
    exact abs_mul_le_half _ _ _ _ (by rw [abs_neg]; exact hγx i j)
  have h4 : ∀ i j, γt i j * ux i * ux j ≤ M * (ux i ^ 2 + ux j ^ 2) / 2 := fun i j =>
    abs_mul_le_half _ _ _ _ (hγt i j)
  have h5 : 2 * u * ut ≤ u ^ 2 + ut ^ 2 := by nlinarith [sq_nonneg (u - ut)]
  have h6 : 2 * ut * L ≤ ut ^ 2 + L ^ 2 := by nlinarith [sq_nonneg (ut - L)]
  have hux : 0 ≤ ∑ i, ux i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  simp only [Fin.sum_univ_three] at hux ⊢
  have := h2 0; have := h2 1; have := h2 2
  have := h3 0 0; have := h3 0 1; have := h3 0 2; have := h3 1 0; have := h3 1 1
  have := h3 1 2; have := h3 2 0; have := h3 2 1; have := h3 2 2
  have := h4 0 0; have := h4 0 1; have := h4 0 2; have := h4 1 0; have := h4 1 1
  have := h4 1 2; have := h4 2 0; have := h4 2 1; have := h4 2 2
  have := sq_nonneg u; have := sq_nonneg ut
  have := mul_nonneg hM (sq_nonneg u); have := mul_nonneg hM (sq_nonneg ut)
  have := mul_nonneg hM (sq_nonneg (ux 0)); have := mul_nonneg hM (sq_nonneg (ux 1))
  have := mul_nonneg hM (sq_nonneg (ux 2))
  nlinarith

theorem densG_le (h : D.Solves T a₀ lam M) {t : ℝ} (ht : t ∈ Icc 0 T) (x : T3) :
    D.densG t x ≤ (17 * M + 2) * D.size t x := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (h.bnd_at t ht x)
  have hsz : 0 ≤ D.size t x := Finset.sum_nonneg fun b _ => by positivity
  have hb : ∀ b, (D.at' t x * D.ut t x b ^ 2 - 2 * ∑ i, D.βdiv t i x * D.ut t x b ^ 2 -
      2 * ∑ i, ∑ j, D.γx t i j x * D.ut t x b * D.ux t j x b +
      ∑ i, ∑ j, D.γt t i j x * D.ux t i x b * D.ux t j x b +
      2 * D.u t x b * D.ut t x b + 2 * D.ut t x b * D.L t x b) ≤
      (16 * M + 2) * (D.ut t x b ^ 2 + ∑ i, D.ux t i x b ^ 2 + D.u t x b ^ 2) + D.L t x b ^ 2 :=
    fun b => densG_term_le M _ _ _ _ _ _ _ _ (h.bnd_at t ht x) (fun i => h.bnd_βdiv t ht i x)
      (fun i j => h.bnd_γx t ht i j x) (fun i j => h.bnd_γt t ht i j x)
  calc D.densG t x ≤ ∑ b, ((16 * M + 2) * (D.ut t x b ^ 2 + ∑ i, D.ux t i x b ^ 2 +
        D.u t x b ^ 2) + D.L t x b ^ 2) := Finset.sum_le_sum fun b _ => hb b
    _ = (16 * M + 2) * D.size t x + ∑ b, D.L t x b ^ 2 := by
        rw [Finset.sum_add_distrib, size, Finset.mul_sum]
    _ ≤ (16 * M + 2) * D.size t x + M * D.size t x := by
        have := h.bnd_L t ht x
        unfold size; linarith
    _ = (17 * M + 2) * D.size t x := by ring

theorem size_le_dens (h : D.Solves T a₀ lam M) {m : ℝ} (hm : m ≤ a₀) (hm' : m ≤ lam) (hm1 : m ≤ 1)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : T3) : m * D.size t x ≤ D.dens t x := by
  unfold size dens
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  have hc := h.coer_γ t ht x (fun i => D.ux t i x b)
  have ha := h.coer_a t ht x
  have h1 : m * D.ut t x b ^ 2 ≤ D.a t x * D.ut t x b ^ 2 :=
    mul_le_mul_of_nonneg_right (hm.trans ha) (sq_nonneg _)
  have h2 : m * ∑ i, D.ux t i x b ^ 2 ≤ lam * ∑ i, D.ux t i x b ^ 2 :=
    mul_le_mul_of_nonneg_right hm' (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have h3 : m * D.u t x b ^ 2 ≤ D.u t x b ^ 2 := by
    have := sq_nonneg (D.u t x b); nlinarith
  have hc' : ∑ i, ∑ j, D.γ t i j x * D.ux t i x b * D.ux t j x b =
      ∑ i, ∑ j, D.γ t i j x * (fun i => D.ux t i x b) i * (fun i => D.ux t i x b) j := rfl
  rw [hc']
  nlinarith

theorem dens_nonneg (h : D.Solves T a₀ lam M) (ha₀ : 0 < a₀) (hlam : 0 < lam) {t : ℝ}
    (ht : t ∈ Icc 0 T) (x : T3) : 0 ≤ D.dens t x := by
  have hsz : 0 ≤ D.size t x := Finset.sum_nonneg fun b _ => by positivity
  have := size_le_dens h (m := min a₀ (min lam 1)) (min_le_left _ _)
    ((min_le_right _ _).trans (min_le_left _ _)) ((min_le_right _ _).trans (min_le_right _ _))
    ht x
  have : 0 ≤ min a₀ (min lam 1) * D.size t x :=
    mul_nonneg (le_min ha₀.le (le_min hlam.le zero_le_one)) hsz
  linarith

/-- **The energy inequality** `E'(t) ≤ K E(t)` on `(0, T)`, with
`K = (17 M + 2) / min(a₀, λ, 1)`. -/
theorem energy_deriv_le (h : D.Solves T a₀ lam M) (ha₀ : 0 < a₀) (hlam : 0 < lam) {t : ℝ}
    (ht : t ∈ Ioo 0 T) :
    ∫ x, D.densT t x ≤ (17 * M + 2) / min a₀ (min lam 1) * D.energy t := by
  set m := min a₀ (min lam 1) with hmdef
  have hm0 : 0 < m := lt_min ha₀ (lt_min hlam one_pos)
  have htc : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
  have hM : 0 ≤ M := (abs_nonneg _).trans (h.bnd_at t htc (0 : T3))
  rw [integral_densT_eq h ht, energy, ← integral_const_mul]
  refine integral_mono ?_ ?_ fun x => ?_
  · have cs := fun {f : ℝ × T3 → ℝ} (hf : Continuous f) => continuous_slice hf t
    unfold densG
    have := fun b => cs (h.cont_u b); have := fun b => cs (h.cont_ut b)
    have := fun i b => cs (h.cont_ux i b); have := cs h.cont_at
    have := fun i => cs (h.cont_βdiv i); have := fun i j => cs (h.cont_γx i j)
    have := fun i j => cs (h.cont_γt i j); have := fun b => cs (h.cont_L b)
    exact integrable_of_continuous (by fun_prop)
  · exact (integrable_of_continuous (continuous_slice (continuous_dens h) t)).const_mul _
  · have h1 := densG_le h htc x
    have h2 := size_le_dens h (m := m) (min_le_left _ _)
      ((min_le_right _ _).trans (min_le_left _ _)) ((min_le_right _ _).trans (min_le_right _ _))
      htc x
    have hK : 0 ≤ (17 * M + 2) / m := by positivity
    calc D.densG t x ≤ (17 * M + 2) * D.size t x := h1
      _ = (17 * M + 2) / m * (m * D.size t x) := by field_simp
      _ ≤ (17 * M + 2) / m * D.dens t x := mul_le_mul_of_nonneg_left h2 hK

/-! ### Uniqueness -/

/-- **Energy uniqueness on `𝕋³`**: a classical solution of the linear system with zero Cauchy data
`u(0) = ∂ₜu(0) = 0` vanishes identically on `[0, T] × 𝕋³`. -/
theorem eq_zero_of_zero_data (h : D.Solves T a₀ lam M) (ha₀ : 0 < a₀) (hlam : 0 < lam)
    (hu0 : ∀ x b, D.u 0 x b = 0) (hut0 : ∀ x b, D.ut 0 x b = 0) :
    ∀ t ∈ Icc 0 T, ∀ x b, D.u t x b = 0 := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  have h0mem : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  set K := (17 * M + 2) / min a₀ (min lam 1)
  -- zero initial energy
  have hux0 : ∀ i x b, D.ux 0 i x b = 0 := by
    intro i x b
    have h1 := h.dx_u 0 h0mem i b x
    simp only [hu0] at h1
    exact h1.unique (hasDerivAt_const _ _)
  have hE0 : D.energy 0 = 0 := by
    unfold energy dens
    simp [hu0, hut0, hux0]
  -- `f(t) = e^{-Kt} E(t)` is antitone
  set f : ℝ → ℝ := fun s => Real.exp (-(K * s)) * D.energy s with hf
  have hfc : ContinuousOn f (Icc 0 T) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul
      (continuous_energy h)).continuousOn
  have hfd : ∀ s ∈ Ioo 0 T, HasDerivAt f (Real.exp (-(K * s)) *
      ((∫ x, D.densT s x) - K * D.energy s)) s := by
    intro s hs
    have h1 : HasDerivAt (fun s => Real.exp (-(K * s))) (Real.exp (-(K * s)) * (-K)) s := by
      have := ((hasDerivAt_id s).const_mul K).neg.exp
      simpa using this
    refine (h1.mul (hasDerivAt_energy h hs)).congr_deriv ?_
    ring
  have hanti : AntitoneOn f (Icc 0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hfc ?_ ?_
    · rw [interior_Icc]
      exact fun s hs => (hfd s hs).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro s hs
      rw [(hfd s hs).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        (sub_nonpos.mpr (energy_deriv_le h ha₀ hlam hs))
  have hft : f t ≤ f 0 := hanti h0mem ht ht.1
  have hf0 : f 0 = 0 := by simp [hf, hE0]
  have hEt : D.energy t ≤ 0 := by
    have : Real.exp (-(K * t)) * D.energy t ≤ 0 := hf0 ▸ hft
    by_contra hc
    have := mul_pos (Real.exp_pos (-(K * t))) (lt_of_not_ge hc)
    linarith
  -- vanishing of the energy forces `u = 0`
  intro x b
  by_contra hne
  have hpos : 0 < D.dens t x := by
    have hm0 : 0 < min a₀ (min lam 1) := lt_min ha₀ (lt_min hlam one_pos)
    have h1 := size_le_dens h (m := min a₀ (min lam 1)) (min_le_left _ _)
      ((min_le_right _ _).trans (min_le_left _ _)) ((min_le_right _ _).trans (min_le_right _ _))
      ht x
    have h2 : 0 < D.size t x := by
      unfold size
      refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun b => D.ut t x b ^ 2 +
        ∑ i, D.ux t i x b ^ 2 + D.u t x b ^ 2) (fun b _ => by positivity) (Finset.mem_univ b))
      have : 0 < D.u t x b ^ 2 := by positivity
      have : 0 ≤ ∑ i, D.ux t i x b ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      have : 0 ≤ D.ut t x b ^ 2 := sq_nonneg _
      linarith
    nlinarith
  have hint := integral_pos_of_integrable_nonneg_nonzero (μ := (volume : Measure T3))
    (continuous_slice (continuous_dens h) t)
    (integrable_of_continuous (continuous_slice (continuous_dens h) t))
    (fun y => dens_nonneg h ha₀ hlam ht y) hpos.ne'
  have : 0 < D.energy t := hint
  linarith


/-! ### Non-vacuity -/

theorem isLineDeriv_const (i : Fin 3) (c : ℝ) : IsLineDeriv i (fun _ : T3 => c) (fun _ => 0) :=
  fun _ => hasDerivAt_const _ _

/-- The flat scalar wave system `∂ₜ²u = Δu` with the zero solution. -/
def flatZero : WaveData Unit where
  u := fun _ _ _ => 0
  ut := fun _ _ _ => 0
  utt := fun _ _ _ => 0
  ux := fun _ _ _ _ => 0
  uxt := fun _ _ _ _ => 0
  uxx := fun _ _ _ _ _ => 0
  a := fun _ _ => 1
  at' := fun _ _ => 0
  β := fun _ _ _ => 0
  βdiv := fun _ _ _ => 0
  γ := fun _ i j _ => if i = j then 1 else 0
  γt := fun _ _ _ _ => 0
  γx := fun _ _ _ _ => 0
  L := fun _ _ _ => 0

theorem flatZero_solves (T : ℝ) : flatZero.Solves T 1 1 0 where
  cont_u := fun _ => continuous_const
  cont_ut := fun _ => continuous_const
  cont_utt := fun _ => continuous_const
  cont_ux := fun _ _ => continuous_const
  cont_uxt := fun _ _ => continuous_const
  cont_uxx := fun _ _ _ => continuous_const
  cont_a := continuous_const
  cont_at := continuous_const
  cont_β := fun _ => continuous_const
  cont_βdiv := fun _ => continuous_const
  cont_γ := fun _ _ => continuous_const
  cont_γt := fun _ _ => continuous_const
  cont_γx := fun _ _ => continuous_const
  cont_L := fun _ => continuous_const
  dt_u := fun _ _ _ _ => hasDerivAt_const _ _
  dt_ut := fun _ _ _ _ => hasDerivAt_const _ _
  dt_ux := fun _ _ _ _ _ => hasDerivAt_const _ _
  dt_a := fun _ _ _ => hasDerivAt_const _ _
  dt_γ := fun _ _ i j _ => hasDerivAt_const _ _
  dx_u := fun _ _ i _ => isLineDeriv_const i 0
  dx_ut := fun _ _ i _ => isLineDeriv_const i 0
  dx_ux := fun _ _ i _ _ => isLineDeriv_const i 0
  dx_β := fun _ _ i => isLineDeriv_const i 0
  dx_γ := fun _ _ i j => isLineDeriv_const i _
  γ_symm := fun _ i j _ => by simp only [flatZero, eq_comm]
  eqn := fun _ _ _ _ => by simp [flatZero]
  coer_a := fun _ _ _ => le_rfl
  coer_γ := fun _ _ _ ξ => by
    simp only [flatZero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp [sq]
  bnd_at := fun _ _ _ => by simp [flatZero]
  bnd_βdiv := fun _ _ _ _ => by simp [flatZero]
  bnd_γt := fun _ _ _ _ _ => by simp [flatZero]
  bnd_γx := fun _ _ _ _ _ => by simp [flatZero]
  bnd_L := fun _ _ _ => by simp [flatZero]

example (T : ℝ) : ∀ t ∈ Icc 0 T, ∀ x b, flatZero.u t x b = 0 :=
  eq_zero_of_zero_data (flatZero_solves T) one_pos one_pos (fun _ _ => rfl) (fun _ _ => rfl)

end WaveData

end

end RenewalGeometry.TorusWaveEnergy
