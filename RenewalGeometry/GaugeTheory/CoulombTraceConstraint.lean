/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.GaugeTheory.FiniteCoulombNormalization

/-!
# Trace constraints along the Coulomb homotopy (gauge groups `S(U(3) × U(2))`, `SU(N)`)

The gauge group of the Einstein–SM action-closure manuscript is
`G_SM = S(U(3) × U(2))` (`eq:gauge-group`), whose Lie algebra is cut out of the skew-adjoint
elements of `𝔸 = M₃(ℂ) × M₂(ℂ)` by the trace condition `τ(X) = tr X₃ + tr X₂ = 0`.  This file
shows that the Coulomb homotopy of `thm:finite-Coulomb-normalization` respects any such
constraint: for a continuous real-linear map `τ : 𝔸 →L[ℝ] V` into a real inner product space with
the trace property `τ(XY) = τ(YX)`, if the seed satisfies `τ(B) = 0`, then along the homotopy
* the generators satisfy `τ(ξ_s) = 0` (`trace_genXi_eq_zero`), i.e. the gauge path is horizontal
  for the subgroup with Lie algebra `ker τ` (its endpoint lies in the connected subgroup, e.g.
  `S(U(3) × U(2))` or `SU(N)`), and
* the logarithmic links satisfy `τ(A_s) = 0` (`trace_linkA_of_solution`).

`finite_coulomb_normalization_trace` packages this with `FiniteCoulomb.finite_coulomb_normalization`.

Generic facts: a linear functional killing `Z` is fixed by `𝒥(Z)`, `𝒥(Z)⁻¹`, `e^Z` and
`𝒦(Z)` (`map_dexpJ_of_comp_eq_zero` …), and a mean-zero grid field with vanishing lattice
Laplacian vanishes (`eq_zero_of_codiff_fwd_eq_zero`).
-/

open NormedSpace Filter Topology Finset Set

namespace RenewalGeometry.CoulombTrace

open OperatorHalfCoth MatrixExpDerivative SeriesLogChart GridSobolev LogGaugeDifferential
  CoulombHomotopy CoulombApriori CurvatureSplit FiniteCoulomb

noncomputable section

/-! ### Functionals killing `Z` -/

section Functional

variable {𝔹 : Type*} [NormedAddCommGroup 𝔹] [NormedSpace ℝ 𝔹] [CompleteSpace 𝔹] [Nontrivial 𝔹]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem comp_pow_eq_zero (ℓ : 𝔹 →L[ℝ] V) (Z : 𝔹 →L[ℝ] 𝔹) (hZ : ∀ u, ℓ (Z u) = 0) (k : ℕ)
    (hk : k ≠ 0) (w : 𝔹) : ℓ ((Z ^ k) w) = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [pow_succ', ContinuousLinearMap.mul_apply, hZ]

/-- If `ℓ ∘ Z = 0`, then `ℓ ∘ 𝒥(Z) = ℓ` and `ℓ ∘ e^Z = ℓ`. -/
theorem map_series_of_comp_eq_zero (ℓ : 𝔹 →L[ℝ] V) (Z : 𝔹 →L[ℝ] 𝔹) (hZ : ∀ u, ℓ (Z u) = 0)
    (w : 𝔹) : ℓ (dexpJ Z w) = ℓ w ∧ ℓ (exp Z w) = ℓ w := by
  set Ψ : (𝔹 →L[ℝ] 𝔹) →L[ℝ] V :=
    (ContinuousLinearMap.apply ℝ V w).comp ((ContinuousLinearMap.compL ℝ 𝔹 𝔹 V) ℓ) with hΨ
  have hΨa : ∀ T : 𝔹 →L[ℝ] 𝔹, Ψ T = ℓ (T w) := fun T => rfl
  have hz : ∀ (c : ℕ → ℝ) (k : ℕ), k ≠ 0 → Ψ (c k • Z ^ k) = 0 := by
    intro c k hk
    rw [hΨa, ContinuousLinearMap.smul_apply, map_smul, comp_pow_eq_zero ℓ Z hZ k hk, smul_zero]
  have h0 : ∀ c : ℝ, Ψ (c • Z ^ 0) = c • ℓ w := by
    intro c
    rw [hΨa, pow_zero, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, map_smul]
  constructor
  · have h1 := (hasSum_dexpJ Z).mapL Ψ
    have h2 : HasSum (fun k => Ψ (jCoeff k • Z ^ k)) (ℓ w) := by
      have := hasSum_single (f := fun k => Ψ (jCoeff k • Z ^ k)) 0 (fun k hk => hz jCoeff k hk)
      rwa [h0, jCoeff_zero, one_smul] at this
    rw [← hΨa]
    exact h1.unique h2
  · have h1 := (exp_series_hasSum_exp' (𝕂 := ℝ) Z).mapL Ψ
    have h2 : HasSum (fun k => Ψ (((Nat.factorial k : ℝ)⁻¹) • Z ^ k)) (ℓ w) := by
      have := hasSum_single (f := fun k => Ψ (((Nat.factorial k : ℝ)⁻¹) • Z ^ k)) 0
        (fun k hk => hz (fun k => ((Nat.factorial k : ℝ)⁻¹)) k hk)
      rwa [h0, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul] at this
    rw [← hΨa]
    exact h1.unique h2

/-- If `ℓ ∘ Z = 0` and `𝒥(Z)` is invertible: `ℓ ∘ 𝒥(Z)⁻¹ = ℓ` and `ℓ ∘ 𝒦(Z) = ℓ`. -/
theorem map_inverse_halfCoth_of_comp_eq_zero (ℓ : 𝔹 →L[ℝ] V) (Z : 𝔹 →L[ℝ] 𝔹)
    (hZ : ∀ u, ℓ (Z u) = 0) (hJ : IsUnit (dexpJ Z)) (w : 𝔹) :
    ℓ (Ring.inverse (dexpJ Z) w) = ℓ w ∧ ℓ (halfCoth Z w) = ℓ w := by
  have hinv : ∀ w, ℓ (Ring.inverse (dexpJ Z) w) = ℓ w := by
    intro w
    have h1 := (map_series_of_comp_eq_zero ℓ Z hZ (Ring.inverse (dexpJ Z) w)).1
    have h2 : dexpJ Z (Ring.inverse (dexpJ Z) w) = w := by
      rw [← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ hJ]; rfl
    rw [h2] at h1
    exact h1.symm
  refine ⟨hinv w, ?_⟩
  rw [halfCoth, ContinuousLinearMap.mul_apply, hinv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.one_apply, map_smul, map_add, (map_series_of_comp_eq_zero ℓ Z hZ w).2]
  rw [← two_smul ℝ (ℓ w), smul_smul]; norm_num

end Functional

/-! ### The lattice Laplacian on mean-zero fields -/

section Laplacian

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A mean-zero grid field `φ` with `δ_h D^+ φ = 0` vanishes. -/
theorem eq_zero_of_codiff_fwd_eq_zero {h : ℝ} (hh : 0 < h) (φ : (ι → ZMod n) → V)
    (hφ : ∑ x, φ x = 0)
    (hΔ : periodicHodgeCodiff h gridStep (fun μ y => gridFwd h μ φ y) = 0) : φ = 0 := by
  have h1 := FaddeevPopov.sum_inner_codiff h (fun μ y => gridFwd h μ φ y) φ
  rw [hΔ] at h1
  simp only [Pi.zero_apply, inner_zero_left, sum_const_zero] at h1
  refine FaddeevPopov.eq_zero_of_dirSq_eq_zero hh φ hφ ?_
  unfold FaddeevPopov.dirSq
  have h2 : ∑ μ, ∑ x, ‖gridFwd h μ φ x‖ ^ 2 = 0 := by
    rw [h1]; simp only [real_inner_self_eq_norm_sq]
  have h3 : ∑ μ, periodicHodgeNormSq ι h (gridFwd h μ φ) =
      h ^ Fintype.card ι * ∑ μ, ∑ x, ‖gridFwd h μ φ x‖ ^ 2 := by
    simp only [periodicHodgeNormSq, mul_sum]
  rw [h3, h2, mul_zero]

end Laplacian

/-! ### Along the Coulomb homotopy -/

variable {𝔸 : Type*} [CStarAlgebra 𝔸] [Nontrivial 𝔸] [FiniteDimensional ℝ 𝔸]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nontrivial E]
  [FiniteDimensional ℝ E]
variable (toE : 𝔸 ≃L[ℝ] E)
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] {n : ℕ} [NeZero n]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable (τ : 𝔸 →L[ℝ] V)

theorem trace_adOp (htr : ∀ X Y, τ (X * Y) = τ (Y * X)) (a u : 𝔸) : τ (adOp a u) = 0 := by
  rw [adOp_apply, map_sub, htr, sub_self]

/-- `τ` read in `E`. -/
def tauE : E →L[ℝ] V := τ.comp (toE.symm : E →L[ℝ] 𝔸)

theorem tauE_brE (htr : ∀ X Y, τ (X * Y) = τ (Y * X)) (a v : E) :
    tauE toE τ (brE toE a v) = 0 := by
  simp only [tauE, ContinuousLinearMap.comp_apply, brE_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]
  exact trace_adOp τ htr _ _

/-- `τ` of the Faddeev–Popov flux is the forward difference of `τ ξ`. -/
theorem tauE_fpFlux (htr : ∀ X Y, τ (X * Y) = τ (Y * X)) {h : ℝ} (Ā : ι → (ι → ZMod n) → E)
    (η : (ι → ZMod n) → E) (μ : ι) (x : ι → ZMod n)
    (hU : IsUnit (dexpJ (h • brE toE (Ā μ x)))) :
    tauE toE τ (FaddeevPopov.fpFlux (brE toE) h Ā η μ x) =
      gridFwd h μ (fun y => tauE toE τ (η y)) x := by
  have hZ : ∀ u, tauE toE τ ((h • brE toE (Ā μ x)) u) = 0 := by
    intro u
    rw [ContinuousLinearMap.smul_apply, map_smul, tauE_brE toE τ htr, smul_zero]
  rw [FaddeevPopov.fpFlux, map_add,
    (map_inverse_halfCoth_of_comp_eq_zero (tauE toE τ) _ hZ hU _).2, tauE_brE toE τ htr, add_zero]
  simp [gridFwd, map_sub, map_smul]

theorem tauE_codiff {h : ℝ} (W : ι → (ι → ZMod n) → E) :
    (fun x => tauE toE τ (periodicHodgeCodiff h gridStep W x)) =
      periodicHodgeCodiff h gridStep (fun μ y => tauE toE τ (W μ y)) := by
  funext x
  simp [periodicHodgeCodiff, periodicHodgeBwd, map_neg, map_sum, map_smul, map_sub]

/-- **The transverse solution is `τ`-free** when the seed is: `τ(ξ_s) = 0`. -/
theorem tauE_solveFP_eq_zero (hι : Fintype.card ι = 4) (htr : ∀ X Y, τ (X * Y) = τ (Y * X))
    {h : ℝ} (hh : 0 < h) {B : ι → (ι → ZMod n) → 𝔸} (hτB : ∀ μ x, τ (B μ x) = 0) {s : ℝ}
    {q : (ι → ZMod n) → 𝔸} (hq : ∀ y, q y ∈ unitary 𝔸) (hp : (s, q) ∈ domO toE h B) :
    ∀ y, tauE toE τ (solveFP toE h B s q y) = 0 := by
  obtain ⟨h1, h2⟩ := solveFP_spec toE hι hh B hp
  have hU : ∀ μ x, IsUnit (dexpJ (h • brE toE (toE (linkA h B s q μ x)))) := fun μ x =>
    (dexpJ_isUnit_and_norm_inverse_le _ (FaddeevPopov.chart_of_small hι (brE toE) hh
      (fun μ y => toE (linkA h B s q μ y)) hp.2.2 μ x).le).1
  -- `τ(R) = τ(B) = 0`
  have hR : ∀ μ y, tauE toE τ (toE (linkR h B s q μ y)) = 0 := by
    intro μ y
    have hJ := isUnit_dexpJ_linkA hh.ne' B s q μ y ((hp.2.1 μ y).le.trans (by norm_num))
    have hZ : ∀ u, τ ((h • adOp (linkA h B s q μ y)) u) = 0 := by
      intro u; rw [ContinuousLinearMap.smul_apply, map_smul, trace_adOp τ htr, smul_zero]
    simp only [tauE, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply, linkR]
    rw [(map_inverse_halfCoth_of_comp_eq_zero τ _ hZ hJ _).1, htr, ← mul_assoc,
      Unitary.star_mul_self_of_mem (hq y), one_mul, hτB]
  -- apply `τ` to `M_A ξ = δ_h R`
  have hΔ := congrArg (fun f : (ι → ZMod n) → E => fun x => tauE toE τ (f x)) h2
  unfold FaddeevPopov.fpOp at hΔ
  rw [tauE_codiff, tauE_codiff] at hΔ
  have hfl : (fun μ y => tauE toE τ (FaddeevPopov.fpFlux (brE toE) h
      (fun ν z => toE (linkA h B s q ν z)) (solveFP toE h B s q) μ y)) =
      fun μ y => gridFwd h μ (fun z => tauE toE τ (solveFP toE h B s q z)) y := by
    funext μ y; exact tauE_fpFlux toE τ htr _ _ μ y (hU μ y)
  rw [hfl] at hΔ
  have hzero : periodicHodgeCodiff h gridStep (fun μ y => tauE toE τ (toE (linkR h B s q μ y))) =
      0 := by
    funext x; simp [periodicHodgeCodiff, periodicHodgeBwd, hR]
  rw [hzero] at hΔ
  have hsum : ∑ x, tauE toE τ (solveFP toE h B s q x) = 0 := by rw [← map_sum, h1, map_zero]
  have := eq_zero_of_codiff_fwd_eq_zero hh _ hsum hΔ
  exact fun y => congrFun this y

theorem trace_genXi_eq_zero (hι : Fintype.card ι = 4) (htr : ∀ X Y, τ (X * Y) = τ (Y * X))
    {h : ℝ} (hh : 0 < h) {B : ι → (ι → ZMod n) → 𝔸} (hB : ∀ μ x, star (B μ x) = -B μ x)
    (hτB : ∀ μ x, τ (B μ x) = 0) {s : ℝ} {q : (ι → ZMod n) → 𝔸} (hq : ∀ y, q y ∈ unitary 𝔸)
    (hp : (s, q) ∈ domO toE h B) (y : ι → ZMod n) : τ (genXi toE h B s q y) = 0 := by
  have h1 := toE_genXi toE hι hh hB hq hp y
  have h2 := tauE_solveFP_eq_zero toE τ hι htr hh hτB hq hp y
  rw [← h1] at h2
  simpa [tauE] using h2

/-- **`τ(A_s) = 0` along the homotopy** when `τ(B) = 0`. -/
theorem trace_linkA_of_solution (hι : Fintype.card ι = 4) (htr : ∀ X Y, τ (X * Y) = τ (Y * X))
    {h : ℝ} (hh : 0 < h) {B : ι → (ι → ZMod n) → 𝔸} (hB : ∀ μ x, star (B μ x) = -B μ x)
    (hτB : ∀ μ x, τ (B μ x) = 0) {T : ℝ} {γ : ℝ → (ι → ZMod n) → 𝔸} (hγ0 : γ 0 = fun _ => 1)
    (hO : ∀ t ∈ Icc 0 T, (t, γ t) ∈ domO toE h B)
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt γ (field toE h B t (γ t)) (Icc 0 T) t) :
    ∀ t ∈ Icc 0 T, ∀ μ x, τ (linkA h B t (γ t) μ x) = 0 := by
  have hu := unitary_of_solution toE B hγ0 hd
  intro t ht μ x
  have hcont : ContinuousOn (fun s => τ (linkA h B s (γ s) μ x)) (Icc 0 T) :=
    τ.continuous.comp_continuousOn (continuousOn_linkA_sol toE B hO hd μ x)
  have hder : ∀ s ∈ Ico 0 T, HasDerivWithinAt (fun s => τ (linkA h B s (γ s) μ x)) 0 (Ici s) s := by
    intro s hs
    have hs' := Ico_subset_Icc_self hs
    have h1 := τ.hasFDerivAt.comp_hasDerivWithinAt s
      (hasDerivWithinAt_linkA_of_solution toE hh.ne' B hO hd hu hs μ x)
    refine h1.congr_deriv ?_
    have hp := hO s hs'
    have hJ := isUnit_dexpJ_linkA hh.ne' B s (γ s) μ x ((hp.2.1 μ x).le.trans (by norm_num))
    have hZ : ∀ u, τ ((h • adOp (linkA h B s (γ s) μ x)) u) = 0 := by
      intro u; rw [ContinuousLinearMap.smul_apply, map_smul, trace_adOp τ htr, smul_zero]
    have hξ := trace_genXi_eq_zero toE τ hι htr hh hB hτB (hu s hs') hp
    change τ (linkR h B s (γ s) μ x - gaugeFlux h (linkA h B s (γ s)) (genXi toE h B s (γ s)) μ x)
      = 0
    simp only [linkR, gaugeFlux, map_sub, map_add]
    rw [(map_inverse_halfCoth_of_comp_eq_zero τ _ hZ hJ _).1,
      (map_inverse_halfCoth_of_comp_eq_zero τ _ hZ hJ _).2, trace_adOp τ htr, htr, ← mul_assoc,
      Unitary.star_mul_self_of_mem (hu s hs' x), one_mul, hτB]
    simp [gridFwd, map_sub, map_smul, hξ]
  have := constant_of_has_deriv_right_zero hcont hder t ht
  rw [this]
  simp [hγ0, linkA_one]

/-- **`thm:finite-Coulomb-normalization` with a trace constraint** (`G_SM = S(U(3) × U(2))`,
`SU(N)`): in addition to the conclusions of `FiniteCoulomb.finite_coulomb_normalization`, if the
seed satisfies `τ(B) = 0` then the Coulomb representative satisfies `τ(A) = 0` (it is
`ker τ`-valued, i.e. a connection of the constrained group), and the normalizing gauge is the
endpoint of a horizontal path of unitary gauges `q̇ = ξ q` with skew-adjoint generators
`τ(ξ) = 0` (so it lies in the connected subgroup with Lie algebra `ker τ`). -/
theorem finite_coulomb_normalization_trace (hι : Fintype.card ι = 4)
    (hM1 : ∀ U ∈ unitary 𝔸, ∀ X, ‖toE (U * X * star U)‖ = ‖toE X‖)
    (hM2 : ∀ a : 𝔸, star a = -a → ∀ u, inner ℝ (toE a) (toE (a * u - u * a)) = 0)
    (htr : ∀ X Y, τ (X * Y) = τ (Y * X)) {L : ℝ} (hL : 0 < L) {εstar : ℝ} (hεstar : 0 < εstar) :
    ∃ εc Cc : ℝ, 0 < εc ∧ 0 < Cc ∧ ∀ (m : ℕ) [NeZero m] (h : ℝ), 0 < h → (m : ℝ) * h = L →
      ∀ B : ι → (ι → ZMod m) → 𝔸, (∀ μ x, star (B μ x) = -B μ x) → (∀ μ x, τ (B μ x) = 0) →
      oneL4 h (toE : 𝔸 →L[ℝ] E) B + curvL2 h (toE : 𝔸 →L[ℝ] E) B ≤ εc →
      ∃ q : (ι → ZMod m) → 𝔸, (∀ x, q x ∈ unitary 𝔸) ∧
        (∀ μ x, linkA h B 1 q μ x =
          h⁻¹ • logChart (q x * exp (h • B μ x) * star (q (x + gridStep μ)))) ∧
        (∀ μ x, star (linkA h B 1 q μ x) = -linkA h B 1 q μ x) ∧
        (∀ μ x, τ (linkA h B 1 q μ x) = 0) ∧
        periodicHodgeCodiff h gridStep (bar (toE : 𝔸 →L[ℝ] E) (linkA h B 1 q)) = 0 ∧
        oneH1 h (toE : 𝔸 →L[ℝ] E) (linkA h B 1 q) + oneL4 h (toE : 𝔸 →L[ℝ] E) (linkA h B 1 q) ≤
          Cc * (oneL2 h (toE : 𝔸 →L[ℝ] E) B + curvL2 h (toE : 𝔸 →L[ℝ] E) B +
            oneL4 h (toE : 𝔸 →L[ℝ] E) B ^ 2) ∧
        oneL4 h (toE : 𝔸 →L[ℝ] E) (linkA h B 1 q) ≤ εstar ∧
        ∃ γ : ℝ → (ι → ZMod m) → 𝔸, γ 0 = (fun _ => 1) ∧ γ 1 = q ∧
          (∀ t ∈ Icc (0 : ℝ) 1, ∀ x, γ t x ∈ unitary 𝔸) ∧
          ∀ t ∈ Icc (0 : ℝ) 1, ∃ ξ : (ι → ZMod m) → 𝔸,
            (∀ x, star (ξ x) = -ξ x ∧ τ (ξ x) = 0) ∧
            HasDerivWithinAt γ (fun x => ξ x * γ t x) (Icc 0 1) t := by
  obtain ⟨εc, Cc, hεc, hCc, H⟩ := finite_coulomb_normalization toE hι hM1 hM2 hL hεstar
  refine ⟨εc, Cc, hεc, hCc, fun m _ h hh hmh B hB hτB hsmall => ?_⟩
  obtain ⟨q, hu, hlink, hskew, hcod, hest, hsmallA, γ, hγ0, hγ1, hO, hd⟩ :=
    H m h hh hmh B hB hsmall
  have huγ := unitary_of_solution toE B hγ0 hd
  have hτA := trace_linkA_of_solution toE τ hι htr hh hB hτB hγ0 hO hd 1 ⟨zero_le_one, le_rfl⟩
  rw [hγ1] at hτA
  refine ⟨q, hu, hlink, hskew, hτA, hcod, hest, hsmallA, γ, hγ0, hγ1, huγ, fun t ht =>
    ⟨genXi toE h B t (γ t), fun x => ⟨star_skewPart _,
      trace_genXi_eq_zero toE τ hι htr hh hB hτB (huγ t ht) (hO t ht) x⟩, hd t ht⟩⟩

end

end RenewalGeometry.CoulombTrace
