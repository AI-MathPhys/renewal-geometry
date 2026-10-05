/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.ActualJetSmoothness
import RenewalGeometry.Continuum.KatoConstantSymmetrizer
import RenewalGeometry.Continuum.KatoDataStability
import RenewalGeometry.Continuum.KatoGalerkinSharpRate
import RenewalGeometry.Continuum.KatoGalerkinCausal

/-!
# The actual-jet system as a quasilinear symmetric hyperbolic system in Euclidean coordinates

Einstein–Standard-Model action-closure manuscript, `app:generated-dynamics`:
"Let the coupled actual-jet system of `prop:actual-jet-writer` be written on its fixed chart as
`U_t + A^i(U)∂_iU = F(U)` (`eq:generated-symmetric-system`)", the instantiation needed by
`thm:generated-dynamics` and `lem:generated-physical-identification`.

The realified actual-jet state space `StateP` of `ActualJetSmooth` (metric variables `(g, p, q)`,
gauge algebra `gl(m, ℝ)`, finite-dimensional Higgs and spinor spaces) carries the block inner
product `ipState` of `prop:actual-jet-writer` built from positive-definite symmetric forms on the
gauge algebra, the Higgs space and the two spinor spaces (`ipP`).  We choose **Euclidean
coordinates** for it: a linear isomorphism `κ : StateP ≃ ℝ^n` with `ipP(κ⁻¹v, κ⁻¹w) = v ⬝ w`
(`coordOf`, from a basis, its Gram matrix and the square-root factor
`KatoSymm.exists_sqrt_factor`).  In these coordinates

* the principal matrices `A^j(v)_{ab} = ⟨e_a, κ 𝒜^j(g(v)) κ⁻¹ e_b⟩` are **symmetric** (from
  `ActualJetSystem.princ_symm`, the Clifford unitarity relations and the symmetry of the forms);
* they depend on the state only through the four frame coefficients
  `(β_j, N E_{1j}, N E_{2j}, N E_{3j})` of the adapted frame `frameU(g⁻¹)` (`princ_congr`), which
  are smooth on the Lorentzian chart (`ActualJetSmooth.ContDiffAt.frameU_*`);
* the forcing `F(v) = κ 𝓕(κ⁻¹ v)` is smooth on the chart (`ActualJetSmooth.Fsys_smooth`).

**`actual_jet_kato_realization`**: for theory data with smooth sources, positive forms with the
Clifford unitarity relations, and every compact set `K` of states in the Lorentzian chart, there
are globally smooth coefficient maps `A^j`, `F` on `ℝ^n` with `A^j(v)` symmetric, which coincide on
`κ(K)` with the actual-jet principal operators and forcing.  Consequently the generic theorems for
quasilinear symmetric hyperbolic systems on `𝕋³` (`KatoGalerkin.kato_local_existence`,
`galerkin_uniform`, `KatoCFL.midpoint_uniform_cfl`, `KatoRates.kato_sharp_rates`,
`KatoStab.kato_physical_identification`) apply to the actual-jet system, and every classical
solution with values in `κ(K)` solves the actual-jet system `∂_t𝒰 + Σ_j 𝒜^j(g)∂_j𝒰 = 𝓕(𝒰)`
(`genP_eq_actual_jet`).  Instantiations:

* **`actual_jet_generated_dynamics`** — Kato existence, spectral Galerkin limit with the sharp
  rates (`KatoRates.kato_sharp_rates`) and the CFL midpoint scheme with cutoff-uniform bounds
  (`KatoCFL.midpoint_uniform_cfl`) for the actual-jet system;
* **`actual_jet_midpoint_causal`** — discrete causal stability `eq:generated-causal` in `H^m`
  (`KatoCausal.midpoint_causal_Hm`);
* **`actual_jet_physical_identification`** — `lem:generated-physical-identification` modulo exactly
  the named analytic-core input `KatoStab.AnalyticCoreContinuation`;
* `exists_time_mem`, **`solves_actual_jet_on_margin`** — a classical solution whose initial values
  lie in `K₀` (with `cthickening δ K₀ ⊆ K`) solves the actual-jet system on a possibly smaller
  slab `[0, t₀] × 𝕋³`;
* non-vacuity: `unitaryForms_triv` (vanishing-coupling theory data, Frobenius forms) and the
  Minkowski state.

Disclosed rendering: `Σ = 𝕋³`; the coefficient maps are smooth extensions (cutoff) of the
chart coefficients from the compact set `K` (the paper's "fixed chart"); the evolved system is the
independent symmetric system `eq:generated-extension` (residual and gauge-defect terms of
`eq:actual-jet-writer` are absent, as in the manuscript's extension).
-/

open Finset Set Filter Topology
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.ActualJetKato

open ActualJetSystem ActualJetSmooth ActualJetWriter FrameCurvature
  TwistedHalfRicci

set_option linter.unusedSectionVars false

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

/-! ### The state as a point of `StateP` -/

/-- The coordinates of a state (inverse of `ActualJetSmooth.ofP`). -/
def toS (U : State (MatLie m) V S S') : StateP m V S S' :=
  ((U.g, U.p, U.q), (U.A, U.E, U.B, U.H, U.Pm, U.Q, U.ψ, U.X, U.ψb, U.Xb))

theorem ofP_toS (U : State (MatLie m) V S S') : ofP (toS U) = U := rfl

theorem toS_ofP (x : StateP m V S S') : toS (ofP x) = x := rfl

/-! ### The block inner product on `StateP` -/

variable (bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ) (bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  (bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ) (bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ)

/-- The block inner product `ipState` in the coordinates `StateP`. -/
def ipP (x y : StateP m V S S') : ℝ := ipState bG bV bS bS' (ofP x) (ofP y)

theorem ipP_add_left (x x' y : StateP m V S S') :
    ipP bG bV bS bS' (x + x') y = ipP bG bV bS bS' x y + ipP bG bV bS bS' x' y := by
  simp only [ipP, ipState, ofP, Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add,
    LinearMap.add_apply, add_mul, Finset.sum_add_distrib]
  ring

theorem ipP_smul_left (c : ℝ) (x y : StateP m V S S') :
    ipP bG bV bS bS' (c • x) y = c * ipP bG bV bS bS' x y := by
  simp only [ipP, ipState, ofP, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, mul_add]
  ring_nf

theorem ipP_add_right (x y y' : StateP m V S S') :
    ipP bG bV bS bS' x (y + y') = ipP bG bV bS bS' x y + ipP bG bV bS bS' x y' := by
  simp only [ipP, ipState, ofP, Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add,
    mul_add, Finset.sum_add_distrib]
  ring

theorem ipP_smul_right (c : ℝ) (x y : StateP m V S S') :
    ipP bG bV bS bS' x (c • y) = c * ipP bG bV bS bS' x y := by
  simp only [ipP, ipState, ofP, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, map_smul,
    smul_eq_mul, mul_left_comm _ c, Finset.mul_sum, mul_add]

/-- The block inner product as a bilinear map. -/
def ipB : StateP m V S S' →ₗ[ℝ] StateP m V S S' →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (ipP bG bV bS bS') (ipP_add_left bG bV bS bS') (ipP_smul_left bG bV bS bS')
    (ipP_add_right bG bV bS bS') (ipP_smul_right bG bV bS bS')

theorem ipB_apply (x y : StateP m V S S') : ipB bG bV bS bS' x y = ipP bG bV bS bS' x y := rfl


/-! ### Symmetry and positivity of the block inner product -/

section Positive

variable {bG bV bS bS'}

theorem ipP_symm (hG : ∀ x y, bG x y = bG y x) (hV : ∀ x y, bV x y = bV y x)
    (hS : ∀ x y, bS x y = bS y x) (hS' : ∀ x y, bS' x y = bS' y x) (x y : StateP m V S S') :
    ipP bG bV bS bS' x y = ipP bG bV bS bS' y x := by
  simp only [ipP, ipState, ofP, hG (x.2.1 _), hG (x.2.2.1 _), hG (x.2.2.2.1 _),
    hV x.2.2.2.2.1, hV x.2.2.2.2.2.1, hV (x.2.2.2.2.2.2.1 _), hS x.2.2.2.2.2.2.2.1,
    hS (x.2.2.2.2.2.2.2.2.1 _), hS' x.2.2.2.2.2.2.2.2.2.1, hS' (x.2.2.2.2.2.2.2.2.2.2 _),
    mul_comm (x.1.1 _ _), mul_comm (x.1.2.1 _ _), mul_comm (x.1.2.2 _ _ _)]

/-- A sum of a nonnegative functional over a finite family vanishes only on the zero family. -/
theorem eq_zero_of_sum_eq_zero {ι X : Type*} [Fintype ι] [Zero X] {φ : X → ℝ}
    (h0 : ∀ z, 0 ≤ φ z) (h1 : ∀ z, φ z = 0 → z = 0) {f : ι → X}
    (hf : ∑ i, φ (f i) = 0) : f = 0 := by
  funext i
  exact h1 _ ((Finset.sum_eq_zero_iff_of_nonneg fun i _ => h0 (f i)).1 hf i (Finset.mem_univ i))

theorem nonneg_of_pos {X : Type*} [Zero X] {φ : X → ℝ} (hφ0 : φ 0 = 0)
    (hφ : ∀ z, z ≠ 0 → 0 < φ z) (z : X) : 0 ≤ φ z := by
  by_cases h : z = 0
  · rw [h, hφ0]
  · exact (hφ z h).le

theorem eq_zero_of_pos {X : Type*} [Zero X] {φ : X → ℝ}
    (hφ : ∀ z, z ≠ 0 → 0 < φ z) (z : X) (h : φ z = 0) : z = 0 := by
  by_contra hz; have := hφ z hz; linarith

theorem sq_sum_nonneg {ι : Type*} [Fintype ι] (f : ι → ℝ) : 0 ≤ ∑ i, f i * f i :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg _

/-- **The block inner product is positive definite** when the four forms are. -/
theorem ipP_pos (hpG : ∀ z, z ≠ 0 → 0 < bG z z) (hpV : ∀ z, z ≠ 0 → 0 < bV z z)
    (hpS : ∀ z, z ≠ 0 → 0 < bS z z) (hpS' : ∀ z, z ≠ 0 → 0 < bS' z z)
    {x : StateP m V S S'} (hx : x ≠ 0) : 0 < ipP bG bV bS bS' x x := by
  have nG := nonneg_of_pos (φ := fun z => bG z z) (by simp) hpG
  have nV := nonneg_of_pos (φ := fun z => bV z z) (by simp) hpV
  have nS := nonneg_of_pos (φ := fun z => bS z z) (by simp) hpS
  have nS' := nonneg_of_pos (φ := fun z => bS' z z) (by simp) hpS'
  have zG := eq_zero_of_pos (φ := fun z => bG z z) hpG
  have zV := eq_zero_of_pos (φ := fun z => bV z z) hpV
  have zS := eq_zero_of_pos (φ := fun z => bS z z) hpS
  have zS' := eq_zero_of_pos (φ := fun z => bS' z z) hpS'
  obtain ⟨⟨g, p, q⟩, A, E, B, H, Pm, Q, ψ, X, ψb, Xb⟩ := x
  simp only [ipP, ipState, ofP]
  set t1 := ∑ μ : Fin 4, ∑ ν : Fin 4, (g μ ν * g μ ν + p μ ν * p μ ν +
    ∑ a : Fin 3, q a μ ν * q a μ ν) with ht1
  have h1 : 0 ≤ t1 := Finset.sum_nonneg fun μ _ => Finset.sum_nonneg fun ν _ => by
    have := sq_sum_nonneg (fun a : Fin 3 => q a μ ν)
    nlinarith [mul_self_nonneg (g μ ν), mul_self_nonneg (p μ ν)]
  have h2 : 0 ≤ ∑ a : Fin 3, (bG (A a) (A a) + bG (E a) (E a) + bG (B a) (B a)) :=
    Finset.sum_nonneg fun a _ => by linarith [nG (A a), nG (E a), nG (B a)]
  have hQ : 0 ≤ ∑ a : Fin 3, bV (Q a) (Q a) := Finset.sum_nonneg fun a _ => nV _
  have hX : 0 ≤ ∑ a : Fin 3, bS (X a) (X a) := Finset.sum_nonneg fun a _ => nS _
  have hXb : 0 ≤ ∑ a : Fin 3, bS' (Xb a) (Xb a) := Finset.sum_nonneg fun a _ => nS' _
  have h3 : 0 ≤ bV H H + bV Pm Pm + ∑ a : Fin 3, bV (Q a) (Q a) := by
    linarith [nV H, nV Pm]
  have h4 : 0 ≤ bS ψ ψ + ∑ a : Fin 3, bS (X a) (X a) := by linarith [nS ψ]
  have h5 : 0 ≤ bS' ψb ψb + ∑ a : Fin 3, bS' (Xb a) (Xb a) := by linarith [nS' ψb]
  refine lt_of_le_of_ne (by linarith) fun hsum => hx ?_
  have e1 : t1 = 0 := by linarith
  have e2 : ∑ a : Fin 3, (bG (A a) (A a) + bG (E a) (E a) + bG (B a) (B a)) = 0 := by linarith
  have e3 : bV H H + bV Pm Pm + ∑ a : Fin 3, bV (Q a) (Q a) = 0 := by linarith
  have e4 : bS ψ ψ + ∑ a : Fin 3, bS (X a) (X a) = 0 := by linarith
  have e5 : bS' ψb ψb + ∑ a : Fin 3, bS' (Xb a) (Xb a) = 0 := by linarith
  -- metric block
  have hrow : ∀ μ ν, g μ ν * g μ ν + p μ ν * p μ ν + ∑ a : Fin 3, q a μ ν * q a μ ν = 0 := by
    intro μ ν
    have hμ := (Finset.sum_eq_zero_iff_of_nonneg fun μ _ => Finset.sum_nonneg fun ν _ => by
      have := sq_sum_nonneg (fun a : Fin 3 => q a μ ν)
      nlinarith [mul_self_nonneg (g μ ν), mul_self_nonneg (p μ ν)]).1 e1 μ (Finset.mem_univ _)
    exact (Finset.sum_eq_zero_iff_of_nonneg fun ν _ => by
      have := sq_sum_nonneg (fun a : Fin 3 => q a μ ν)
      nlinarith [mul_self_nonneg (g μ ν), mul_self_nonneg (p μ ν)]).1 hμ ν (Finset.mem_univ _)
  have hg : g = 0 := by
    funext μ ν; have := hrow μ ν; have := sq_sum_nonneg (fun a : Fin 3 => q a μ ν)
    simp only [Pi.zero_apply]; nlinarith [mul_self_nonneg (g μ ν), mul_self_nonneg (p μ ν)]
  have hp : p = 0 := by
    funext μ ν; have := hrow μ ν; have := sq_sum_nonneg (fun a : Fin 3 => q a μ ν)
    simp only [Pi.zero_apply]; nlinarith [mul_self_nonneg (g μ ν), mul_self_nonneg (p μ ν)]
  have hq : q = 0 := by
    funext a μ ν
    have hs : ∑ a : Fin 3, q a μ ν * q a μ ν = 0 := by
      have := hrow μ ν; have := sq_sum_nonneg (fun a : Fin 3 => q a μ ν)
      nlinarith [mul_self_nonneg (g μ ν), mul_self_nonneg (p μ ν)]
    have := (Finset.sum_eq_zero_iff_of_nonneg fun a _ => mul_self_nonneg (q a μ ν)).1 hs a
      (Finset.mem_univ _)
    simpa using this
  -- gauge block
  have hgauge : ∀ a, bG (A a) (A a) + bG (E a) (E a) + bG (B a) (B a) = 0 := fun a =>
    (Finset.sum_eq_zero_iff_of_nonneg fun a _ => by
      linarith [nG (A a), nG (E a), nG (B a)]).1 e2 a (Finset.mem_univ _)
  have hA : A = 0 := funext fun a => zG _ (by
    have := hgauge a; linarith [nG (A a), nG (E a), nG (B a)])
  have hE : E = 0 := funext fun a => zG _ (by
    have := hgauge a; linarith [nG (A a), nG (E a), nG (B a)])
  have hB : B = 0 := funext fun a => zG _ (by
    have := hgauge a; linarith [nG (A a), nG (E a), nG (B a)])
  -- Higgs block
  have hH : H = 0 := zV _ (by linarith [nV H, nV Pm])
  have hPm : Pm = 0 := zV _ (by linarith [nV H, nV Pm])
  have hQ0 : Q = 0 := eq_zero_of_sum_eq_zero nV zV (by linarith [nV H, nV Pm])
  -- spinor blocks
  have hψ : ψ = 0 := zS _ (by linarith [nS ψ])
  have hX0 : X = 0 := eq_zero_of_sum_eq_zero nS zS (by linarith [nS ψ])
  have hψb : ψb = 0 := zS' _ (by linarith [nS' ψb])
  have hXb0 : Xb = 0 := eq_zero_of_sum_eq_zero nS' zS' (by linarith [nS' ψb])
  subst hg hp hq hA hE hB hH hPm hQ0 hψ hX0 hψb hXb0
  rfl

end Positive

/-! ### Euclidean coordinates for the block inner product -/

section Coordinates

open scoped Matrix

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

/-- **Euclidean coordinates for a positive-definite symmetric bilinear form** on a
finite-dimensional real space: a linear isomorphism `κ : E ≃ ℝ^n` (`n = dim E`) with
`B(κ⁻¹v, κ⁻¹w) = Σ_i v_i w_i` (Gram matrix of a basis and its square-root factor). -/
theorem exists_euclidean_coords (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀ x y, B x y = B y x)
    (hpos : ∀ x, x ≠ 0 → 0 < B x x) :
    ∃ κ : E ≃ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ),
      ∀ v w, B (κ.symm v) (κ.symm w) = ∑ i, v i * w i := by
  classical
  set b := Module.finBasis ℝ E with hb
  set M : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    Matrix.of fun i j => B (b i) (b j) with hM
  have hcomb : ∀ c c' : Fin (Module.finrank ℝ E) → ℝ,
      B (b.equivFun.symm c) (b.equivFun.symm c') = c ⬝ᵥ (M *ᵥ c') := by
    intro c c'
    simp only [Module.Basis.equivFun_symm_apply, map_sum, map_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, dotProduct, Matrix.mulVec, hM, Matrix.of_apply,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hMpd : M.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun c hc => ?_
    · ext i j; simp [hM, Matrix.conjTranspose_apply, hB]
    · rw [star_trivial, ← hcomb]
      refine hpos _ fun h => hc ?_
      have := congrArg b.equivFun h
      rwa [LinearEquiv.apply_symm_apply, map_zero] at this
  obtain ⟨S, Si, hSM, hSSi, hSiS⟩ := KatoSymm.exists_sqrt_factor hMpd
  let L : (Fin (Module.finrank ℝ E) → ℝ) ≃ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
    { toFun := fun c => S *ᵥ c
      invFun := fun v => Si *ᵥ v
      map_add' := fun c c' => Matrix.mulVec_add S c c'
      map_smul' := fun r c => Matrix.mulVec_smul S r c
      left_inv := fun c => by simp [Matrix.mulVec_mulVec, hSiS]
      right_inv := fun v => by simp [Matrix.mulVec_mulVec, hSSi] }
  refine ⟨b.equivFun.trans L, fun v w => ?_⟩
  have hsymm : ∀ u, (b.equivFun.trans L).symm u = b.equivFun.symm (Si *ᵥ u) := fun u => rfl
  rw [hsymm, hsymm, hcomb, ← hSM, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hSSi,
    Matrix.one_mulVec, Matrix.one_mulVec]
  rfl

/-- In Euclidean coordinates the coordinates are the form against the dual basis:
`(κ y)_a = B(κ⁻¹ e_a, y)`. -/
theorem coord_eq_form {n : ℕ} (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (κ : E ≃ₗ[ℝ] (Fin n → ℝ))
    (hκ : ∀ v w, B (κ.symm v) (κ.symm w) = ∑ i, v i * w i) (y : E) (a : Fin n) :
    κ y a = B (κ.symm (Pi.single a 1)) y := by
  have := hκ (Pi.single a 1) (κ y)
  rw [κ.symm_apply_apply] at this
  rw [this]
  simp [Pi.single_apply]

/-- The inverse coordinate map is a linear combination of the coordinate vectors. -/
theorem symm_eq_sum {n : ℕ} (κ : E ≃ₗ[ℝ] (Fin n → ℝ)) (w : Fin n → ℝ) :
    κ.symm w = ∑ b, w b • κ.symm (Pi.single b 1) := by
  conv_lhs => rw [show w = ∑ b, w b • (Pi.single b 1 : Fin n → ℝ) by
    ext i; simp [Pi.single_apply]]
  simp [map_sum, map_smul]

end Coordinates

/-! ### The actual-jet coefficient maps in Euclidean coordinates -/

variable (m V S S') in
/-- The dimension of the realified actual-jet state space. -/
abbrev dimS : ℕ := Module.finrank ℝ (StateP m V S S')

/-- **The positivity and unitarity hypotheses of `prop:actual-jet-writer`** ("symmetric in the
fixed positive component norm after realification"): symmetric positive-definite forms on the
gauge algebra, the Higgs space and the two spinor spaces, for which `c_0` is self-adjoint and the
spatial Clifford generators `c_i` are skew (both Dirac blocks). -/
structure UnitaryForms (SM : SMData (MatLie m) V S S') (bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ)
    (bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ) (bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ) : Prop where
  symG : ∀ x y, bG x y = bG y x
  symV : ∀ x y, bV x y = bV y x
  symS : ∀ x y, bS x y = bS y x
  symS' : ∀ x y, bS' x y = bS' y x
  posG : ∀ z, z ≠ 0 → 0 < bG z z
  posV : ∀ z, z ≠ 0 → 0 < bV z z
  posS : ∀ z, z ≠ 0 → 0 < bS z z
  posS' : ∀ z, z ≠ 0 → 0 < bS' z z
  c0 : ∀ x y, bS (SM.D.Fr.c 0 • x) y = bS x (SM.D.Fr.c 0 • y)
  ci : ∀ (i : Fin 3) x y, bS (SM.D.Fr.c i.succ • x) y = -bS x (SM.D.Fr.c i.succ • y)
  c0b : ∀ x y, bS' (SM.Db.Fr.c 0 • x) y = bS' x (SM.Db.Fr.c 0 • y)
  cib : ∀ (i : Fin 3) x y, bS' (SM.Db.Fr.c i.succ • x) y = -bS' x (SM.Db.Fr.c i.succ • y)

section Realization

variable {SM : SMData (MatLie m) V S S'} {bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ}
  {bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ} {bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ}

/-- The principal operators are symmetric for the block inner product (any adapted frame). -/
theorem ipState_princ_symm (hU : UnitaryForms SM bG bV bS bS') (AF : AdaptedFrame) (j : Fin 3)
    (W W' : State (MatLie m) V S S') :
    ipState bG bV bS bS' (princ AF SM.D.Fr SM.Db.Fr j W) W' =
      ipState bG bV bS bS' W (princ AF SM.D.Fr SM.Db.Fr j W') :=
  princ_symm AF SM.D.Fr SM.Db.Fr bG bV bS bS' hU.c0 hU.ci hU.c0b hU.cib j W W'

theorem ipState_comm (hU : UnitaryForms SM bG bV bS bS') (W W' : State (MatLie m) V S S') :
    ipState bG bV bS bS' W W' = ipState bG bV bS bS' W' W :=
  ipP_symm hU.symG hU.symV hU.symS hU.symS' (toS W) (toS W')

/-- **Euclidean coordinates of the block inner product** on the actual-jet state space. -/
theorem exists_state_coords (hU : UnitaryForms SM bG bV bS bS') :
    ∃ κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ),
      ∀ v w, ipP bG bV bS bS' (κ.symm v) (κ.symm w) = ∑ i, v i * w i :=
  exists_euclidean_coords (ipB bG bV bS bS') (ipP_symm hU.symG hU.symV hU.symS hU.symS')
    fun _ hx => ipP_pos hU.posG hU.posV hU.posS hU.posS' hx

/-- The Lorentzian chart of the state space (`det g ≠ 0`, `g⁻¹` in the chart of `frameOf`). -/
def chartSet : Set (StateP m V S S') := {x | MetChart x.1}

theorem contDiffAt_ginv_state {x0 : StateP m V S S'} (hx : MetChart x0.1) :
    ContDiffAt ℝ ∞ (fun x : StateP m V S S' => ginvOf x.1.1) x0 := by
  have h1 : ContDiffAt ℝ ∞ (fun x : StateP m V S S' => x.1.1) x0 := by fun_prop
  exact ContDiffAt.ginvOf_fun h1 hx.1

theorem isOpen_chartSet : IsOpen (chartSet (m := m) (V := V) (S := S) (S' := S')) := by
  rw [isOpen_iff_mem_nhds]
  intro x0 hx
  have hdet : ContinuousAt (fun x : StateP m V S S' => (Matrix.of x.1.1).det) x0 := by
    have : Continuous (fun x : StateP m V S S' => (Matrix.of x.1.1).det) :=
      (Continuous.matrix_det (continuous_id.comp (by fun_prop)))
    exact this.continuousAt
  have h1 : ∀ᶠ x in 𝓝 x0, (Matrix.of (x : StateP m V S S').1.1).det ≠ 0 :=
    hdet.eventually (isOpen_ne.mem_nhds hx.1)
  have h2 := eventually_chart (contDiffAt_ginv_state hx).continuousAt hx.2
  filter_upwards [h1, h2] with x hx1 hx2
  exact ⟨hx1, hx2⟩

/-- The lapse, shift and spatial frame of the state are smooth on the chart. -/
theorem contDiffAt_frame_state {x0 : StateP m V S S'} (hx : MetChart x0.1) :
    ContDiffAt ℝ ∞ (fun x : StateP m V S S' => (frameU (ginvOf x.1.1)).N) x0 ∧
    (∀ j, ContDiffAt ℝ ∞ (fun x : StateP m V S S' => (frameU (ginvOf x.1.1)).β j) x0) ∧
    (∀ a j, ContDiffAt ℝ ∞ (fun x : StateP m V S S' => (frameU (ginvOf x.1.1)).E a j) x0) :=
  ⟨ContDiffAt.frameU_N (contDiffAt_ginv_state hx) hx.2,
    fun j => ContDiffAt.frameU_β (contDiffAt_ginv_state hx) hx.2 j,
    fun a j => ContDiffAt.frameU_E (contDiffAt_ginv_state hx) hx.2 a j⟩

/-- The forcing `𝓕` is smooth on the chart as a `StateP`-valued map. -/
theorem contDiffAt_Fsys_state (hS : SMSmooth SM) {x0 : StateP m V S S'} (hx : MetChart x0.1) :
    ContDiffAt ℝ ∞ (fun x : StateP m V S S' => toS (Fsys SM (ofP x))) x0 := by
  obtain ⟨hg, hp, hq, hA, hE, hB, hH, hPm, hQ, hψ, hX, hψb, hXb⟩ := Fsys_smooth SM hS hx
  have pi2 : ∀ {f : StateP m V S S' → Fin 4 → Fin 4 → ℝ},
      (∀ μ ν, ContDiffAt ℝ ∞ (fun x => f x μ ν) x0) → ContDiffAt ℝ ∞ f x0 := by
    intro f h
    rw [contDiffAt_pi]; intro μ; rw [contDiffAt_pi]; intro ν; exact h μ ν
  have pi3 : ∀ {f : StateP m V S S' → Fin 3 → Fin 4 → Fin 4 → ℝ},
      (∀ a μ ν, ContDiffAt ℝ ∞ (fun x => f x a μ ν) x0) → ContDiffAt ℝ ∞ f x0 := by
    intro f h
    rw [contDiffAt_pi]; intro a; exact pi2 (h a)
  simp only [toS]
  exact ((pi2 hg).prodMk ((pi2 hp).prodMk (pi3 hq))).prodMk
    ((contDiffAt_pi.2 hA).prodMk ((contDiffAt_pi.2 hE).prodMk ((contDiffAt_pi.2 hB).prodMk
      (hH.prodMk (hPm.prodMk ((contDiffAt_pi.2 hQ).prodMk (hψ.prodMk
        ((contDiffAt_pi.2 hX).prodMk (hψb.prodMk (contDiffAt_pi.2 hXb))))))))))

/-- A linear map between finite-dimensional real spaces is smooth. -/
theorem contDiff_linearEquiv {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [FiniteDimensional ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    (L : E₁ →ₗ[ℝ] E₂) : ContDiff ℝ ∞ L :=
  (LinearMap.toContinuousLinearMap L).contDiff

/-- The principal matrix entry `⟨κ⁻¹e_a, 𝒜^j κ⁻¹e_b⟩` for an adapted frame. -/
def princEntry (SM : SMData (MatLie m) V S S') (bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ)
    (bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ) (bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ)
    (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ)) (AF : AdaptedFrame) (j : Fin 3)
    (a b : Fin (dimS m V S S')) : ℝ :=
  ipState bG bV bS bS' (ofP (κ.symm (Pi.single a 1)))
    (princ AF SM.D.Fr SM.Db.Fr j (ofP (κ.symm (Pi.single b 1))))

theorem princEntry_symm (hU : UnitaryForms SM bG bV bS bS')
    (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ)) (AF : AdaptedFrame) (j : Fin 3)
    (a b : Fin (dimS m V S S')) :
    princEntry SM bG bV bS bS' κ AF j a b = princEntry SM bG bV bS bS' κ AF j b a := by
  unfold princEntry
  rw [← ipState_princ_symm hU, ipState_comm hU]

/-- **The principal matrices represent the principal operators**: in Euclidean coordinates,
`Σ_b ⟨κ⁻¹e_a, 𝒜^j κ⁻¹e_b⟩ w_b = (κ 𝒜^j κ⁻¹ w)_a`. -/
theorem sum_princEntry (hU : UnitaryForms SM bG bV bS bS')
    {κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ)}
    (hκ : ∀ v w, ipP bG bV bS bS' (κ.symm v) (κ.symm w) = ∑ i, v i * w i) (AF : AdaptedFrame)
    (j : Fin 3) (a : Fin (dimS m V S S')) (w : Fin (dimS m V S S') → ℝ) :
    ∑ b, princEntry SM bG bV bS bS' κ AF j a b * w b =
      κ (toS (princ AF SM.D.Fr SM.Db.Fr j (ofP (κ.symm w)))) a := by
  rw [coord_eq_form (ipB bG bV bS bS') κ hκ, ipB_apply, ipP, ofP_toS,
    ← ipState_princ_symm hU]
  have e : ipState bG bV bS bS' (princ AF SM.D.Fr SM.Db.Fr j (ofP (κ.symm (Pi.single a 1))))
      (ofP (κ.symm w)) = ipB bG bV bS bS'
        (toS (princ AF SM.D.Fr SM.Db.Fr j (ofP (κ.symm (Pi.single a 1))))) (κ.symm w) := rfl
  rw [e, symm_eq_sum κ w, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm, princEntry, ← ipState_princ_symm hU]
  rfl

/-- An adapted frame from a lapse logarithm, a shift and a spatial frame. -/
def mkFrame (L : ℝ) (β : Fin 3 → ℝ) (E : Fin 3 → Fin 3 → ℝ) : AdaptedFrame :=
  ⟨Real.exp L, β, E, Real.exp_pos L⟩

theorem mkFrame_eq {AF : AdaptedFrame} {L : ℝ} {β : Fin 3 → ℝ} {E : Fin 3 → Fin 3 → ℝ}
    (hL : L = Real.log AF.N) (hβ : β = AF.β) (hE : E = AF.E) : mkFrame L β E = AF := by
  cases AF
  simp only [mkFrame, hL, hβ, hE, AdaptedFrame.mk.injEq, and_true]
  exact Real.exp_log (by assumption)

/-- The principal matrix entries are smooth in the frame data `(log N, β, E)`. -/
theorem contDiff_princEntry_mkFrame
    (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ)) {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {L : X → ℝ} {β : X → Fin 3 → ℝ} {E : X → Fin 3 → Fin 3 → ℝ}
    (hL : ContDiff ℝ ∞ L) (hβ : ∀ j, ContDiff ℝ ∞ fun x => β x j)
    (hE : ∀ a j, ContDiff ℝ ∞ fun x => E x a j) (j : Fin 3) (a b : Fin (dimS m V S S')) :
    ContDiff ℝ ∞ fun x => princEntry SM bG bV bS bS' κ (mkFrame (L x) (β x) (E x)) j a b := by
  have hN : ContDiff ℝ ∞ fun x => Real.exp (L x) := Real.contDiff_exp.comp hL
  have hβj := hβ j
  have hEj : ∀ a, ContDiff ℝ ∞ fun x => E x a j := fun a => hE a j
  simp only [princEntry, ipState, princ, mkFrame, diracP, map_add, map_sub, map_neg, map_smul,
    map_sum, map_zero, smul_eq_mul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.zero_apply]
  fun_prop

end Realization

/-! ### The realization theorem -/

section Main

variable {SM : SMData (MatLie m) V S S'} {bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ}
  {bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ} {bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ}

/-- A family of real functions, smooth on an open set, has global smooth extensions from a
compact subset. -/
theorem exists_contDiff_eqOn_family {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {O K : Set E} (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    {Φ : ι → E → ℝ} (hΦ : ∀ i, ContDiffOn ℝ ∞ (Φ i) O) :
    ∃ Φ' : ι → E → ℝ, (∀ i, ContDiff ℝ ∞ (Φ' i)) ∧ ∀ i, ∀ v ∈ K, Φ' i v = Φ i v := by
  have h := fun i => SlabMoser.exists_contDiff_eqOn hO hK hKO (hΦ i)
  choose Φ' hΦ' hΦ'K using h
  exact ⟨Φ', hΦ', hΦ'K⟩

/-- **The actual-jet system as a quasilinear symmetric hyperbolic system**
(`eq:generated-symmetric-system`; `prop:actual-jet-writer`).  For theory data with smooth
sources (`SMSmooth`) and forms satisfying the positivity and Clifford unitarity relations
(`UnitaryForms`) there are Euclidean coordinates `κ` of the realified actual-jet state space
(`ipState(κ⁻¹v, κ⁻¹w) = v ⬝ w`) such that for every compact set `K` of coordinate states in the
Lorentzian chart there are **globally smooth coefficient maps** `A^j(v)` (`j = 1, 2, 3`), `F(v)`
on `ℝ^n` with **symmetric** `A^j(v)`, which on `K` are the actual-jet principal operators and
forcing: `Σ_b A^j(v)_{ab} w_b = (κ 𝒜^j(g(v)) κ⁻¹ w)_a` with the adapted frame
`frameU(g(v)⁻¹)`, and `F(v) = κ 𝓕(κ⁻¹v)`. -/
theorem actual_jet_kato_realization (hS : SMSmooth SM) (hU : UnitaryForms SM bG bV bS bS') :
    ∃ κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ),
      (∀ v w, ipP bG bV bS bS' (κ.symm v) (κ.symm w) = ∑ i, v i * w i) ∧
      ∀ K : Set (Fin (dimS m V S S') → ℝ), IsCompact K → (∀ v ∈ K, MetChart (κ.symm v).1) →
      ∃ (A : Fin 3 → Fin (dimS m V S S') → Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ) (F : Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ),
        (∀ i a b, ContDiff ℝ ∞ (A i a b)) ∧ (∀ i a b v, A i a b v = A i b a v) ∧
        (∀ a, ContDiff ℝ ∞ (F a)) ∧
        (∀ v ∈ K, ∀ j a (w : Fin (dimS m V S S') → ℝ), ∑ b, A j a b v * w b =
          κ (toS (princ (frameU (ginvOf (κ.symm v).1.1)) SM.D.Fr SM.Db.Fr j
            (ofP (κ.symm w)))) a) ∧
        (∀ v ∈ K, ∀ a, F a v = κ (toS (Fsys SM (ofP (κ.symm v)))) a) := by
  obtain ⟨κ, hκ⟩ := exists_state_coords hU
  refine ⟨κ, hκ, fun K hK hKc => ?_⟩
  set O : Set (Fin (dimS m V S S') → ℝ) := κ.symm ⁻¹' chartSet with hOdef
  have hκc : Continuous κ.symm := (contDiff_linearEquiv κ.symm.toLinearMap).continuous
  have hO : IsOpen O := isOpen_chartSet.preimage hκc
  have hKO : K ⊆ O := fun v hv => hKc v hv
  have hκs : ContDiff ℝ ∞ κ.symm := contDiff_linearEquiv κ.symm.toLinearMap
  have hκf : ContDiff ℝ ∞ κ := contDiff_linearEquiv κ.toLinearMap
  -- the chart coefficient functions are smooth on `O`
  have hframe : ∀ v ∈ O, ContDiffAt ℝ ∞
      (fun v => (frameU (ginvOf (κ.symm v).1.1)).N) v ∧
      (∀ j, ContDiffAt ℝ ∞ (fun v => (frameU (ginvOf (κ.symm v).1.1)).β j) v) ∧
      (∀ a j, ContDiffAt ℝ ∞ (fun v => (frameU (ginvOf (κ.symm v).1.1)).E a j) v) := by
    intro v hv
    obtain ⟨h1, h2, h3⟩ := contDiffAt_frame_state (m := m) (V := V) (S := S) (S' := S') hv
    exact ⟨h1.comp v hκs.contDiffAt, fun j => (h2 j).comp v hκs.contDiffAt,
      fun a j => (h3 a j).comp v hκs.contDiffAt⟩
  have hL : ContDiffOn ℝ ∞ (fun v => Real.log (frameU (ginvOf (κ.symm v).1.1)).N) O :=
    fun v hv => ((hframe v hv).1.log (frameU _).N_pos.ne').contDiffWithinAt
  obtain ⟨L', hL's, hL'K⟩ := SlabMoser.exists_contDiff_eqOn hO hK hKO hL
  obtain ⟨β', hβ's, hβ'K⟩ := exists_contDiff_eqOn_family hO hK hKO
    (Φ := fun j v => (frameU (ginvOf (κ.symm v).1.1)).β j)
    fun j v hv => ((hframe v hv).2.1 j).contDiffWithinAt
  obtain ⟨E', hE's, hE'K⟩ := exists_contDiff_eqOn_family hO hK hKO
    (Φ := fun p : Fin 3 × Fin 3 => fun v => (frameU (ginvOf (κ.symm v).1.1)).E p.1 p.2)
    fun p v hv => ((hframe v hv).2.2 p.1 p.2).contDiffWithinAt
  obtain ⟨F', hF's, hF'K⟩ := exists_contDiff_eqOn_family hO hK hKO
    (Φ := fun a v => κ (toS (Fsys SM (ofP (κ.symm v)))) a)
    fun a v hv => by
      have h1 := (contDiffAt_Fsys_state hS hv).comp v hκs.contDiffAt
      have h2 := (hκf.contDiffAt (x := toS (Fsys SM (ofP (κ.symm v))))).comp v h1
      exact ((contDiffAt_pi.1 h2) a).contDiffWithinAt
  set AF' : (Fin (dimS m V S S') → ℝ) → AdaptedFrame := fun v =>
    mkFrame (L' v) (fun j => β' j v) (fun a j => E' (a, j) v) with hAF'
  have hAFK : ∀ v ∈ K, AF' v = frameU (ginvOf (κ.symm v).1.1) := fun v hv =>
    mkFrame_eq (hL'K v hv) (funext fun j => hβ'K j v hv) (funext fun a => funext fun j =>
      hE'K (a, j) v hv)
  refine ⟨fun j a b v => princEntry SM bG bV bS bS' κ (AF' v) j a b, F', fun j a b => ?_,
    fun j a b v => princEntry_symm hU κ (AF' v) j a b, hF's, fun v hv j a w => ?_,
    fun v hv a => hF'K a v hv⟩
  · exact contDiff_princEntry_mkFrame κ hL's (fun j => hβ's j) (fun a j => hE's (a, j)) j a b
  · rw [sum_princEntry hU hκ, hAFK v hv]

/-- **Classical solutions of the realized system with values in `K` solve the actual-jet
system** `∂_t𝒰 + Σ_j 𝒜^j(g)∂_j𝒰 = 𝓕(𝒰)` (`eq:generated-extension`, in the coordinates `κ`): the
generator `F(U) - Σ_j A^j(U)∂_jU` of the realized system is the actual-jet generator. -/
theorem genP_eq_actual_jet {κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ)}
    {K : Set (Fin (dimS m V S S') → ℝ)}
    {A : Fin 3 → Fin (dimS m V S S') → Fin (dimS m V S S') → (Fin (dimS m V S S') → ℝ) → ℝ}
    {F : Fin (dimS m V S S') → (Fin (dimS m V S S') → ℝ) → ℝ}
    (hAK : ∀ v ∈ K, ∀ j a (w : Fin (dimS m V S S') → ℝ), ∑ b, A j a b v * w b =
      κ (toS (princ (frameU (ginvOf (κ.symm v).1.1)) SM.D.Fr SM.Db.Fr j (ofP (κ.symm w)))) a)
    (hFK : ∀ v ∈ K, ∀ a, F a v = κ (toS (Fsys SM (ofP (κ.symm v)))) a)
    (U : Fin (dimS m V S S') → SlabWaveHk.ST 3 → ℝ)
    (P : Fin (dimS m V S S') → Fin 3 → SlabWaveHk.ST 3 → ℝ) (x : SlabWaveHk.ST 3)
    (hx : (fun c => U c x) ∈ K) (a : Fin (dimS m V S S')) :
    KatoGalerkin.genP A F U P a x =
      κ (toS (Fsys SM (ofP (κ.symm fun c => U c x)))) a -
        ∑ j, κ (toS (princ (frameU (ginvOf (κ.symm fun c => U c x).1.1)) SM.D.Fr SM.Db.Fr j
          (ofP (κ.symm fun c => P c j x)))) a := by
  unfold KatoGalerkin.genP
  rw [hFK _ hx a]
  congr 1
  exact Finset.sum_congr rfl fun j _ => hAK _ hx j a (fun c => P c j x)

end Main

/-! ### Kato, Galerkin, midpoint and physical identification for the actual-jet system -/

section Dynamics

open KatoGalerkin SlabWaveHk SymHypEnergy QLEnergy PeriodicCube

variable {SM : SMData (MatLie m) V S S'} {bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ}
  {bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ} {bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ}

/-- **The generated dynamics of the actual-jet system** (`thm:generated-dynamics` on
`eq:generated-symmetric-system`, `Σ = 𝕋³`): in the Euclidean coordinates `κ` of the block inner
product, for every compact set `K` of states in the Lorentzian chart there are smooth symmetric
coefficient maps `A^j`, `F` that **are** the actual-jet principal operators and forcing on `K`
(so the realized generator is the actual-jet generator at every point where the state lies in
`K`, `genP_eq_actual_jet`), and for every data radius `R₀`:
* (Kato, `eq:generated-Galerkin`, `eq:generated-Galerkin-rate` with `a = 0`) every smooth periodic
  datum with `‖U₀‖_{H^q} ≤ R₀` has a classical solution on `[0, T] × 𝕋³` which is the limit of the
  spectral Galerkin solutions, with the sharp coefficient rates of `KatoRates.kato_sharp_rates`;
* (`eq:generated-midpoint`, `eq:generated-CFL`, `eq:generated-uniform`) the fully finite implicit
  midpoint recursion exists on a common interval under `τ(N+1) ≤ c_*`, `τ ≤ τ_*`, with the
  cutoff-uniform bound `‖U^j‖_{H^q} ≤ R`. -/
theorem actual_jet_generated_dynamics (hS : SMSmooth SM) (hU : UnitaryForms SM bG bV bS bS')
    {mm r : ℕ} (hm : (3 : ℝ) / 2 < mm) (hq : 2 * mm ≤ r + 1) (hq2 : mm + 2 ≤ r + 1) :
    ∃ κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ),
      (∀ v w, ipP bG bV bS bS' (κ.symm v) (κ.symm w) = ∑ i, v i * w i) ∧
      ∀ K : Set (Fin (dimS m V S S') → ℝ), IsCompact K → (∀ v ∈ K, MetChart (κ.symm v).1) →
      ∃ (A : Fin 3 → Fin (dimS m V S S') → Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ) (F : Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ),
        (∀ v ∈ K, ∀ j a (w : Fin (dimS m V S S') → ℝ), ∑ b, A j a b v * w b =
          κ (toS (princ (frameU (ginvOf (κ.symm v).1.1)) SM.D.Fr SM.Db.Fr j
            (ofP (κ.symm w)))) a) ∧
        (∀ v ∈ K, ∀ a, F a v = κ (toS (Fsys SM (ofP (κ.symm v)))) a) ∧
        ∀ R₀ : ℝ, 0 ≤ R₀ →
        (∃ T > 0, ∃ R ≥ 0, ∃ C ≥ 0, ∀ U₀ : Fin (dimS m V S S') → ST 3 → ℝ,
          (∀ b, ContDiff ℝ ∞ (U₀ b)) → (∀ b, IsSPeriodic (U₀ b)) →
          energyQ (r + 1) U₀ 0 ≤ R₀ ^ 2 →
          ∃ (U : Fin (dimS m V S S') → ST 3 → ℝ) (P : Fin (dimS m V S S') → Fin 3 → ST 3 → ℝ),
            (∀ b, Continuous (U b)) ∧ (∀ b, IsSPeriodic (U b)) ∧
            (∀ b y, U b (Fin.cons 0 y) = U₀ b (Fin.cons 0 y)) ∧
            (∀ b (i : Fin 3) x, HasDerivAt (fun s : ℝ => U b (x + s • ev i.succ)) (P b i x) 0) ∧
            (∀ b, ∀ t ∈ Set.Icc 0 T, ∀ y, HasDerivWithinAt (fun s => U b (Fin.cons s y))
              (genP A F U P b (Fin.cons t y)) (Set.Icc 0 T) t) ∧
            (∀ t ∈ Set.Icc 0 T, ∀ S : Finset (Fin 3 → ℤ),
              ∑ b, ∑ k ∈ S, wq (r + 1) k * coef (U b) t k ^ 2 ≤ R ^ 2) ∧
            ∃ γ : (N : ℕ) → ℝ → GS 3 (dimS m V S S') N, GalerkinHyp A F (r + 1) U₀ T R γ ∧
              (∀ N, ∀ t ∈ Set.Icc 0 T, ∀ S : Finset (Fin 3 → ℤ),
                ∑ b, ∑ k ∈ S, (cf (r + 1) (γ N t) b k - coef (U b) t k) ^ 2 ≤
                  C / (2 * Real.pi * ((N : ℝ) + 1)) ^ (2 * r + 1)) ∧
              (∀ ρ ≤ r, ∀ N, ∀ t ∈ Set.Icc 0 T, ∀ S : Finset (Fin 3 → ℤ),
                ∑ b, ∑ k ∈ S, wq ρ k * (cf (r + 1) (γ N t) b k - coef (U b) t k) ^ 2 ≤
                  ((1 + 4 * Real.pi ^ 2 * ((3 : ℕ) : ℝ)) ^ ρ * C + R ^ 2) /
                    ((N : ℝ) + 1) ^ (2 * (r - ρ) + 1))) ∧
        (∃ T > 0, ∃ R ≥ 0, ∃ cstar > 0, ∃ τstar > 0, ∀ (N : ℕ) (τ : ℝ), 0 < τ →
          τ * ((N : ℝ) + 1) ≤ cstar → τ ≤ τstar → ∀ a₀ : GS 3 (dimS m V S S') N, ‖a₀‖ ≤ R₀ →
          ∃ U : ℕ → GS 3 (dimS m V S S') N, U 0 = a₀ ∧ ∀ j : ℕ, (j : ℝ) * τ ≤ T →
            ‖U j‖ ≤ R ∧ (((j : ℝ) + 1) * τ ≤ T →
              U (j + 1) = U j + τ • GN A F (r + 1) (SpectralGalerkin.mid (U j) (U (j + 1))))) := by
  obtain ⟨κ, hκ, hreal⟩ := actual_jet_kato_realization hS hU
  refine ⟨κ, hκ, fun K hK hKc => ?_⟩
  obtain ⟨A, F, hA, hsym, hF, hAK, hFK⟩ := hreal K hK hKc
  refine ⟨A, F, hAK, hFK, fun R₀ hR₀ => ⟨?_, ?_⟩⟩
  · obtain ⟨T, hT, R, hR, C, hC, h⟩ := KatoRates.kato_sharp_rates (d := 3) hm hq hq2 hA hsym hF
      hR₀
    refine ⟨T, hT, R, hR, C, hC, fun U₀ hU₀ hUp hE => ?_⟩
    obtain ⟨U, P, h1, h2, h3, h4, h5, h6, γ, hG, h7, h8⟩ := h U₀ hU₀ hUp hE
    exact ⟨U, P, h1, h2, h3, h4, fun b t ht y => h5 b t ht y, h6, γ, hG, h7, h8⟩
  · obtain ⟨T, hT, R, hR, cstar, hc, τstar, hτ, CM, -, h⟩ := KatoCFL.midpoint_uniform_cfl
      (d := 3) hm hq hA hsym hF hR₀
    exact ⟨T, hT, R, hR, cstar, hc, τstar, hτ, fun N τ hτ0 hcfl hτs a₀ ha₀ => by
      obtain ⟨U, hU0, hUj⟩ := h N τ hτ0 hcfl hτs a₀ ha₀
      exact ⟨U, hU0, fun j hj => ⟨(hUj j hj).1, fun hj1 => ((hUj j hj).2 hj1).1⟩⟩⟩

/-- **Physical identification for the actual-jet system, modulo the named analytic-core input**
(`lem:generated-physical-identification`, `Σ = 𝕋³`): with the realized coefficient maps of
`actual_jet_kato_realization` (Euclidean-symmetric, so `KatoStab.kato_physical_identification`
applies directly) and any continuous physical first-jet identities `Φ_j` (defining-jet
identities, Einstein/matter residuals, Gauss and harmonic constraints evaluated on the
reconstructed jets): for every radius `R₀` there is `T > 0` such that, **under
`KatoStab.AnalyticCoreContinuation`** (Cauchy–Kovalevskaya with Sobolev-controlled continuation
and density of the analytic core), there is `t₁ > 0` such that every constrained datum with
`‖U₀‖_{H^q} ≤ R₀` has a common two-sided Kato solution on `(-T, T)` satisfying all physical
identities on `[0, t₁]`; wherever its state lies in `K`, its generator is the actual-jet generator
(`genP_eq_actual_jet`). -/
theorem actual_jet_physical_identification (hS : SMSmooth SM) (hU : UnitaryForms SM bG bV bS bS')
    {mm r : ℕ} (hm : (3 : ℝ) / 2 < mm) (hq : 2 * mm ≤ r + 1) (hq2 : mm + 2 ≤ r + 1)
    {ι : Type*} :
    ∃ κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ),
      (∀ v w, ipP bG bV bS bS' (κ.symm v) (κ.symm w) = ∑ i, v i * w i) ∧
      ∀ K : Set (Fin (dimS m V S S') → ℝ), IsCompact K → (∀ v ∈ K, MetChart (κ.symm v).1) →
      ∃ (A : Fin 3 → Fin (dimS m V S S') → Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ) (F : Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ),
        (∀ v ∈ K, ∀ j a (w : Fin (dimS m V S S') → ℝ), ∑ b, A j a b v * w b =
          κ (toS (princ (frameU (ginvOf (κ.symm v).1.1)) SM.D.Fr SM.Db.Fr j
            (ofP (κ.symm w)))) a) ∧
        (∀ v ∈ K, ∀ a, F a v = κ (toS (Fsys SM (ofP (κ.symm v)))) a) ∧
        ∀ (Φ : ι → (Fin (dimS m V S S') → ℝ) × (Fin (3 + 1) → Fin (dimS m V S S') → ℝ) → ℝ),
          (∀ j, Continuous (Φ j)) → ∀ R₀ : ℝ, 0 ≤ R₀ →
          ∃ T > 0, ∀ Constrained Core : (Fin (dimS m V S S') → ST 3 → ℝ) → Prop,
            KatoStab.AnalyticCoreContinuation A F (r + 1) Constrained Core Φ →
            ∃ t₁ > 0, ∀ U₀ : Fin (dimS m V S S') → ST 3 → ℝ, Constrained U₀ →
              (∀ b, ContDiff ℝ ∞ (U₀ b)) → (∀ b, IsSPeriodic (U₀ b)) →
              energyQ (r + 1) U₀ 0 ≤ R₀ ^ 2 →
              ∃ (U : Fin (dimS m V S S') → ST 3 → ℝ)
                (P : Fin (dimS m V S S') → Fin 3 → ST 3 → ℝ),
                TwoSidedSol A F U₀ T U P ∧ KatoStab.PhysicalOn Φ U t₁ := by
  obtain ⟨κ, hκ, hreal⟩ := actual_jet_kato_realization hS hU
  refine ⟨κ, hκ, fun K hK hKc => ?_⟩
  obtain ⟨A, F, hA, hsym, hF, hAK, hFK⟩ := hreal K hK hKc
  exact ⟨A, F, hAK, hFK, fun Φ hΦ R₀ hR₀ =>
    KatoStab.kato_physical_identification (d := 3) hm hq hq2 hA hsym hF hΦ hR₀⟩

end Dynamics

section Causal

open KatoGalerkin SlabWaveHk SymHypEnergy QLEnergy

variable {SM : SMData (MatLie m) V S S'} {bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ}
  {bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ} {bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ}

/-- **Discrete causal stability (`eq:generated-causal`) for the actual-jet system**: with the
realized coefficient maps of `actual_jet_kato_realization` (`Σ = 𝕋³`, `m ≥ 1`, `m + 3 ≤ q`), for
every radius `R` there is `K` such that any two midpoint trajectories of the spectral scheme in the
`H^q` ball of radius `R`, one of them with forcing `r_j`, satisfy
`‖U^n - V^n‖_{H^m} ≤ e^{2Knτ}(‖U^0 - V^0‖_{H^m} + 2τ Σ_{j<n} ‖r_j‖_{H^m})` (`τK ≤ 1`), uniformly in
the cutoff `N` and the step `τ`. -/
theorem actual_jet_midpoint_causal (hS : SMSmooth SM) (hU : UnitaryForms SM bG bV bS bS')
    {mH q : ℕ} (hm1 : 1 ≤ mH) (hq : 2 + mH + 1 ≤ q) :
    ∃ κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ),
      (∀ v w, ipP bG bV bS bS' (κ.symm v) (κ.symm w) = ∑ i, v i * w i) ∧
      ∀ K : Set (Fin (dimS m V S S') → ℝ), IsCompact K → (∀ v ∈ K, MetChart (κ.symm v).1) →
      ∃ (A : Fin 3 → Fin (dimS m V S S') → Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ) (F : Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ),
        (∀ v ∈ K, ∀ j a (w : Fin (dimS m V S S') → ℝ), ∑ b, A j a b v * w b =
          κ (toS (princ (frameU (ginvOf (κ.symm v).1.1)) SM.D.Fr SM.Db.Fr j
            (ofP (κ.symm w)))) a) ∧
        (∀ v ∈ K, ∀ a, F a v = κ (toS (Fsys SM (ofP (κ.symm v)))) a) ∧
        ∀ R : ℝ, 0 ≤ R → ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ (N : ℕ) (τ : ℝ), 0 ≤ τ → τ * Kc ≤ 1 →
          ∀ (U W r : ℕ → GS 3 (dimS m V S S') N) (nn : ℕ), (∀ j ≤ nn, ‖U j‖ ≤ R) →
          (∀ j ≤ nn, ‖W j‖ ≤ R) →
          (∀ j < nn, U (j + 1) = U j + τ • GN A F q (SpectralGalerkin.mid (U j) (U (j + 1)))) →
          (∀ j < nn, W (j + 1) = W j + τ • (GN A F q (SpectralGalerkin.mid (W j) (W (j + 1))) +
            r j)) →
          ‖KatoCausal.hmS mH q (U nn) - KatoCausal.hmS mH q (W nn)‖ ≤
            Real.exp (2 * Kc * (nn * τ)) * (‖KatoCausal.hmS mH q (U 0) -
              KatoCausal.hmS mH q (W 0)‖ +
              2 * τ * ∑ j ∈ Finset.range nn, ‖KatoCausal.hmS mH q (r j)‖) := by
  obtain ⟨κ, hκ, hreal⟩ := actual_jet_kato_realization hS hU
  refine ⟨κ, hκ, fun K hK hKc => ?_⟩
  obtain ⟨A, F, hA, hsym, hF, hAK, hFK⟩ := hreal K hK hKc
  exact ⟨A, F, hAK, hFK, fun R hR =>
    KatoCausal.midpoint_causal_Hm (d := 3) (ms := 2) hA hsym hF (by norm_num) hm1 hq hR⟩

end Causal

/-! ### Persistence of the chart margin -/

section Margin

open SymHypEnergy PeriodicCube

/-- **The state stays in the chart for a short time**: a continuous spatially periodic field whose
initial values lie in `K₀` takes values in any set `K ⊇ cthickening δ K₀` (`δ > 0`) on a slab
`[0, t₀] × 𝕋^d`, `t₀ > 0` (uniform continuity on the period cell). -/
theorem exists_time_mem {d n : ℕ} {U : Fin n → (Fin (d + 1) → ℝ) → ℝ}
    (hU : ∀ b, Continuous (U b)) (hUp : ∀ b, IsSPeriodic (U b)) {K₀ K : Set (Fin n → ℝ)}
    {δ : ℝ} (hδ : 0 < δ) (hK : Metric.cthickening δ K₀ ⊆ K)
    (h0 : ∀ y, (fun c => U c (Fin.cons 0 y)) ∈ K₀) :
    ∃ t₀ > 0, ∀ t ∈ Set.Icc 0 t₀, ∀ y, (fun c => U c (Fin.cons t y)) ∈ K := by
  set W : (Fin (d + 1) → ℝ) → Fin n → ℝ := fun x c => U c x with hW
  have hWc : Continuous W := continuous_pi fun c => hU c
  have hcpt : IsCompact (Set.Icc (0 : Fin (d + 1) → ℝ) 1) := isCompact_Icc
  have huc := hcpt.uniformContinuousOn_of_continuous hWc.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨η, hη, hηW⟩ := huc δ hδ
  refine ⟨min (η / 2) 1, by positivity, fun t ht y => ?_⟩
  -- reduce to the period cell
  set y' : Fin d → ℝ := fun i => Int.fract (y i) with hy'
  have hper : ∀ s, W (Fin.cons s y) = W (Fin.cons s y') := by
    intro s
    funext c
    have h := (hUp c).slice s (fun i => ⌊y i⌋) y'
    have e : y' + zvec (fun i => ⌊y i⌋) = y := by
      funext i; simp [hy', zvec, Int.fract_add_floor]
    simp only [hW]
    rw [← e]
    exact h
  have hmem : ∀ s ∈ Set.Icc (0 : ℝ) 1, (Fin.cons s y' : Fin (d + 1) → ℝ) ∈
      Set.Icc (0 : Fin (d + 1) → ℝ) 1 := by
    intro s hs
    constructor
    · intro i
      induction i using Fin.cases with
      | zero => simpa using hs.1
      | succ i => simp [hy', Int.fract_nonneg]
    · intro i
      induction i using Fin.cases with
      | zero => simpa using hs.2
      | succ i => simp [hy', (Int.fract_lt_one _).le]
  have ht1 : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans (min_le_right _ _)⟩
  have hdist : dist (Fin.cons t y' : Fin (d + 1) → ℝ) (Fin.cons 0 y') < η := by
    rw [dist_eq_norm]
    refine (norm_cons_sub_time t 0 y').trans_lt ?_
    rw [sub_zero, abs_of_nonneg ht.1]
    have := ht.2.trans (min_le_left _ _)
    linarith
  have hclose := hηW _ (hmem t ht1) _ (hmem 0 ⟨le_rfl, zero_le_one⟩) hdist
  rw [← hper t, ← hper 0] at hclose
  refine hK (Metric.mem_cthickening_of_dist_le _ _ δ K₀ (h0 y) ?_)
  exact hclose.le

end Margin

section MarginSolve

variable {SM : SMData (MatLie m) V S S'}

/-- **The realized solution solves the actual-jet system on a possibly smaller slab**
(`lem:generated-physical-identification`, "on a possibly smaller interval"; `Σ = 𝕋³`): if the
realized coefficient maps agree with the actual-jet operators on `K ⊇ cthickening δ K₀` and a
classical solution of the realized system on `[0, T] × 𝕋³` has initial values in `K₀`, then there
is `t₀ > 0` such that on `[0, min t₀ T] × 𝕋³` its time derivative is the actual-jet generator
`κ 𝓕(𝒰) - Σ_j κ 𝒜^j(g)∂_j𝒰`. -/
theorem solves_actual_jet_on_margin {κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ)}
    {K₀ K : Set (Fin (dimS m V S S') → ℝ)} {δ : ℝ} (hδ : 0 < δ)
    (hK : Metric.cthickening δ K₀ ⊆ K)
    {A : Fin 3 → Fin (dimS m V S S') → Fin (dimS m V S S') → (Fin (dimS m V S S') → ℝ) → ℝ}
    {F : Fin (dimS m V S S') → (Fin (dimS m V S S') → ℝ) → ℝ}
    (hAK : ∀ v ∈ K, ∀ j a (w : Fin (dimS m V S S') → ℝ), ∑ b, A j a b v * w b =
      κ (toS (princ (frameU (ginvOf (κ.symm v).1.1)) SM.D.Fr SM.Db.Fr j (ofP (κ.symm w)))) a)
    (hFK : ∀ v ∈ K, ∀ a, F a v = κ (toS (Fsys SM (ofP (κ.symm v)))) a)
    {U : Fin (dimS m V S S') → SlabWaveHk.ST 3 → ℝ}
    {P : Fin (dimS m V S S') → Fin 3 → SlabWaveHk.ST 3 → ℝ} {T : ℝ}
    (hUc : ∀ b, Continuous (U b)) (hUp : ∀ b, SymHypEnergy.IsSPeriodic (U b))
    (hU0 : ∀ y, (fun c => U c (Fin.cons 0 y)) ∈ K₀)
    (htime : ∀ b, ∀ t ∈ Set.Icc 0 T, ∀ y, HasDerivWithinAt (fun s => U b (Fin.cons s y))
      (KatoGalerkin.genP A F U P b (Fin.cons t y)) (Set.Icc 0 T) t) :
    ∃ t₀ > 0, ∀ b, ∀ t ∈ Set.Icc 0 (min t₀ T), ∀ y,
      HasDerivWithinAt (fun s => U b (Fin.cons s y))
        (κ (toS (Fsys SM (ofP (κ.symm fun c => U c (Fin.cons t y))))) b -
          ∑ j, κ (toS (princ (frameU (ginvOf (κ.symm fun c => U c (Fin.cons t y)).1.1))
            SM.D.Fr SM.Db.Fr j (ofP (κ.symm fun c => P c j (Fin.cons t y))))) b)
        (Set.Icc 0 T) t := by
  obtain ⟨t₀, ht₀, hmem⟩ := exists_time_mem hUc hUp hδ hK hU0
  refine ⟨t₀, ht₀, fun b t ht y => ?_⟩
  have htT : t ∈ Set.Icc 0 T := ⟨ht.1, ht.2.trans (min_le_right _ _)⟩
  have htK : (fun c => U c (Fin.cons t y)) ∈ K :=
    hmem t ⟨ht.1, ht.2.trans (min_le_left _ _)⟩ y
  rw [← genP_eq_actual_jet hAK hFK U P (Fin.cons t y) htK b]
  exact htime b t htT y

end MarginSolve

/-! ### Non-vacuity -/

section NonVacuity

/-- The entries of a `gl(m)` element. -/
def toM {m : ℕ} (x : MatLie m) : Matrix (Fin m) (Fin m) ℝ := x

theorem toM_add {m : ℕ} (x y : MatLie m) : toM (x + y) = toM x + toM y := rfl

theorem toM_smul {m : ℕ} (c : ℝ) (x : MatLie m) : toM (c • x) = c • toM x := rfl

/-- The Frobenius form `⟨x, y⟩ = Σ_{ij} x_{ij} y_{ij}` on `gl(m, ℝ)`. -/
def frob (m : ℕ) : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ∑ i, ∑ j, toM x i j * toM y i j)
    (fun x x' y => by
      simp only [toM_add, Matrix.add_apply, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [toM_smul, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc])
    (fun x y y' => by
      simp only [toM_add, Matrix.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [toM_smul, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm c])

theorem frob_apply {m : ℕ} (x y : MatLie m) : frob m x y = ∑ i, ∑ j, toM x i j * toM y i j :=
  rfl

theorem frob_pos {m : ℕ} (z : MatLie m) (hz : z ≠ 0) : 0 < frob m z z := by
  rw [frob_apply]
  by_contra h
  push Not at h
  apply hz
  have h0 : ∀ i j, toM z i j * toM z i j = 0 := by
    intro i j
    have hnn : ∀ i, 0 ≤ ∑ j, toM z i j * toM z i j := fun i =>
      Finset.sum_nonneg fun j _ => mul_self_nonneg _
    have hsum : ∑ i, ∑ j, toM z i j * toM z i j = 0 :=
      le_antisymm h (Finset.sum_nonneg fun i _ => hnn i)
    have hi := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i).1 hsum i (Finset.mem_univ _)
    exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_self_nonneg (toM z i j)).1 hi j
      (Finset.mem_univ _)
  have : toM z = 0 := by
    ext i j; exact mul_self_eq_zero.1 (h0 i j)
  exact this

/-- **Non-vacuity of `UnitaryForms`**: the vanishing-coupling theory data `trivSMM` (gauge algebra
`gl(1)`, Higgs space `gl(1)`, zero spinor spaces) with the Frobenius forms. -/
theorem unitaryForms_triv : UnitaryForms trivSMM (frob 1) (frob 1) (0 : PUnit.{1} →ₗ[ℝ] PUnit.{1} →ₗ[ℝ] ℝ)
    (0 : PUnit.{1} →ₗ[ℝ] PUnit.{1} →ₗ[ℝ] ℝ) where
  symG x y := by simp only [frob_apply, mul_comm]
  symV x y := by simp only [frob_apply, mul_comm]
  symS _ _ := rfl
  symS' _ _ := rfl
  posG := frob_pos
  posV := frob_pos
  posS z hz := absurd (Subsingleton.elim z 0) hz
  posS' z hz := absurd (Subsingleton.elim z 0) hz
  c0 _ _ := rfl
  ci _ _ _ := by simp only [LinearMap.zero_apply, neg_zero]
  c0b _ _ := rfl
  cib _ _ _ := by simp only [LinearMap.zero_apply, neg_zero]

/-- **Non-vacuity of `actual_jet_generated_dynamics`**: for the Minkowski state (in the
Lorentzian chart) the realized coefficient maps exist, coincide there with the actual-jet
operators, and the Kato/Galerkin conclusions hold for every data radius. -/
example : ∃ κ : StateP 1 (MatLie 1) PUnit.{1} PUnit.{1} ≃ₗ[ℝ] (Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ℝ),
    ∃ (A : Fin 3 → Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) →
        (Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ℝ) → ℝ),
      ∀ j a (w : Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ℝ),
        ∑ b, A j a b (κ ((minkInv, 0, 0), 0)) * w b =
          κ (toS (princ (frameU (ginvOf minkInv)) trivSMM.D.Fr trivSMM.Db.Fr j
            (ofP (κ.symm w)))) a := by
  obtain ⟨κ, -, h⟩ := actual_jet_generated_dynamics trivSMM_smooth unitaryForms_triv
    (mm := 2) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨A, F, hAK, -, -⟩ := h {κ ((minkInv, 0, 0), 0)} isCompact_singleton (by
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    rw [LinearEquiv.symm_apply_apply]
    exact metChart_mink)
  refine ⟨κ, A, fun j a w => ?_⟩
  have := hAK _ (Set.mem_singleton _) j a w
  rwa [LinearEquiv.symm_apply_apply] at this

end NonVacuity
end RenewalGeometry.ActualJetKato
