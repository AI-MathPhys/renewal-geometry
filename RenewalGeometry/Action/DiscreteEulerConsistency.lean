/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ShiftedJetActionHessianExact

/-!
# Consistency of discrete Euler rows of shifted-first-jet lattice actions

Generic infrastructure for `prop:native-consistency` (Einstein–Standard-Model action-closure
manuscript, Appendix `app:quantitative-residuals`): for a shifted-first-jet lattice action
`𝒜_h(y) = h⁴ Σ_x F(h, Ξ_h y(x))` on the periodic grid `(ℤ/n)⁴` (`ShiftedJetAction.action`), the
**discrete Euler row** of the samples of a smooth periodic field `Y` is `O(h)`-close to the
**continuum Euler–Lagrange expression** of the limiting first-order density
`L₀(w, p) = F(0, (w, …, w; p, …, p))`.

## Objects

* `pos h x = h · x̃` is the real position of the node `x` (`x̃ ∈ {0, …, n-1}⁴`), and
  `samp h Y x = Y(pos h x)` the nodal sample of a field `Y : ℝ⁴ → V` (`𝖲_h` of the paper).
  For a field of period `n h` in every coordinate (`IsPeriodic`), the samples at shifted nodes are
  the values at the shifted real points (`samp_add_castVec`).
* `eulerRow A h y x = h⁻⁴ ∂_{y(x)} A(y)`: the raw Euler row (the gradient of a lattice action with
  respect to the value at the node `x`, in the mass normalisation `h⁴`).
* `contEuler L Y z = ∂_w L(Y, ∂Y)(z) - Σ_μ ∂_μ[∂_{p_μ} L(Y, ∂Y)](z)`: the continuum Euler–Lagrange
  expression of a first-order density `L(w, p)`.
* `eulerRow_action_eq`: the explicit form of the raw Euler row of a shifted-first-jet action,
  `E_h(y)(x) = Σ_i D_{v_i}F(Ξ(x - σ_i)) + Σ_{i,μ} h⁻¹(D_{d_{iμ}}F(Ξ(x - σ_i - e_μ)) - D_{d_{iμ}}F(Ξ(x - σ_i)))`
  (exact discrete summation by parts).

## Main result

`norm_eulerRow_sub_contEuler_le`: let `P(h, ξ) = ∂_ξ F(h, ξ)` be differentiable on the balls of
radius `δ` around the points `(0, J¹Y(z))` with `‖DP‖ ≤ M₂`, `‖D²P‖ ≤ M₃` there, let `Y` be `C³`,
`(n h)`-periodic, with `‖DY‖ ≤ B₁`, `‖D²Y‖ ≤ B₂`, `‖D³Y‖ ≤ B₃`, and let the shifts be bounded by
`s`.  Then for `0 < h` with `h (1 + c₁) < δ` (`c₁` explicit in `B₁, B₂, s`),
`‖E_h(𝖲_h Y)(x) - E₀(Y)(pos h x)‖ ≤ C h` at **every** node, with the explicit constant
`C = card ι · (M₂(1 + c₁) + 4(M₃(1 + c₁)(B₁ + B₂) + M₂ c₂))`, independent of `h`, of the number of
nodes and of the field (beyond the bounds).  The proof is the paper's: Taylor expansion of the
shifted stencils (first differences `= ∂Y + O(h)`, shifted values `= Y + O(h)`) and of the
divided difference of `D_dF` (`= ∂_μ D_dF + O(h)`, using the symmetry of `D²Y`).

## Companions

* `exists_densityReg`: the regularity packet holds uniformly for a compact parameter family of
  densities that are `C³` at the points `(θ, 0, c)` (finite-dimensional fibres).
* `fieldBound_of_iteratedFDeriv`, `FieldBound.rescale`: field bounds from iterated-derivative
  bounds, and the amplitude-preserving rescaling `Ỹ(ξ) = Y(ξ/K)` of a growing-band field.
* `eulerRow_smul_action`, `contEuler_scale`: exact rescaling of discrete and continuum Euler rows.
* `MapReg.norm_value_sub_le`, `MapReg.norm_divDiff_sub_le`, `exists_C2_ball_bounds`: the same
  Taylor estimates for arbitrary vector-valued composite stencil quantities `P(h, Ξ_h)`.
-/

open Finset Filter Topology Metric Set
open scoped ContDiff

namespace RenewalGeometry.DiscreteEulerConsistency

open ShiftedJetAction (Grid unitVec stencil action)

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

/-- Real four-space with the sup norm. -/
abbrev R4 := Fin 4 → ℝ

/-- The coordinate unit vector `e_μ` of `ℝ⁴`. -/
def evec (μ : Fin 4) : R4 := Pi.single μ 1

theorem norm_evec (μ : Fin 4) : ‖evec μ‖ = 1 := by
  unfold evec
  rw [Pi.norm_single, norm_one]

/-- Shifted first jets: shifted values and normalised first differences. -/
abbrev Jet (ι V : Type*) := (ι → V) × (ι × Fin 4 → V)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Slot embeddings -/

/-- The value slot `i` of the jet space. -/
def ιv (i : ι) : V →L[ℝ] Jet ι V :=
  (ContinuousLinearMap.inl ℝ _ _).comp (ContinuousLinearMap.single ℝ (fun _ : ι => V) i)

/-- The difference slot `(i, μ)` of the jet space. -/
def ιd (p : ι × Fin 4) : V →L[ℝ] Jet ι V :=
  (ContinuousLinearMap.inr ℝ _ _).comp (ContinuousLinearMap.single ℝ (fun _ : ι × Fin 4 => V) p)

theorem ιv_apply (i : ι) (w : V) : (ιv i w : Jet ι V) = (Pi.single i w, 0) := rfl

theorem ιd_apply (p : ι × Fin 4) (w : V) : (ιd p w : Jet ι V) = (0, Pi.single p w) := rfl

theorem norm_ιv_le (i : ι) : ‖(ιv i : V →L[ℝ] Jet ι V)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
  rw [ιv_apply, one_mul, Prod.norm_def, Pi.norm_single, norm_zero]
  exact (max_le le_rfl (norm_nonneg w))

theorem norm_ιd_le (p : ι × Fin 4) : ‖(ιd p : V →L[ℝ] Jet ι V)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
  rw [ιd_apply, one_mul, Prod.norm_def, Pi.norm_single, norm_zero]
  exact (max_le (norm_nonneg w) le_rfl)

/-- Every jet is the sum of its slots. -/
theorem jet_eq_sum (ξ : Jet ι V) :
    ξ = ∑ i, ιv i (ξ.1 i) + ∑ p, ιd p (ξ.2 p) := by
  ext j
  · simp [ιv_apply, ιd_apply, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
  · simp [ιv_apply, ιd_apply, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]

/-! ### Sampling on the periodic grid -/

variable {n : ℕ} [NeZero n]

/-- The real position `h · x̃` of a node. -/
def pos (h : ℝ) (x : Grid n) : R4 := fun μ => h * ((x μ).val : ℝ)

/-- The nodal sample `𝖲_h Y`. -/
def samp (h : ℝ) (Y : R4 → V) : Grid n → V := fun x => Y (pos h x)

/-- An integer lattice vector as a node. -/
def castVec (m : Fin 4 → ℤ) : Grid n := fun μ => (m μ : ZMod n)

/-- An integer lattice vector as a real vector. -/
def realVec (m : Fin 4 → ℤ) : R4 := fun μ => (m μ : ℝ)

theorem castVec_add (m m' : Fin 4 → ℤ) : (castVec (m + m') : Grid n) = castVec m + castVec m' := by
  funext μ; simp [castVec]

theorem castVec_neg (m : Fin 4 → ℤ) : (castVec (-m) : Grid n) = -castVec m := by
  funext μ; simp [castVec]

theorem realVec_add (m m' : Fin 4 → ℤ) : realVec (m + m') = realVec m + realVec m' := by
  funext μ; simp [realVec]

theorem realVec_neg (m : Fin 4 → ℤ) : realVec (-m) = -realVec m := by
  funext μ; simp [realVec]

theorem castVec_single (μ : Fin 4) : (castVec (Pi.single μ 1) : Grid n) = unitVec n μ := by
  funext ν
  by_cases h : ν = μ
  · subst h; simp [castVec, unitVec]
  · simp [castVec, unitVec, Pi.single_apply, h]

theorem realVec_single (μ : Fin 4) : realVec (Pi.single μ 1) = evec μ := by
  funext ν
  by_cases h : ν = μ
  · subst h; simp [realVec, evec]
  · simp [realVec, evec, Pi.single_apply, h]

/-- Periodicity of a field with period `L` in every coordinate. -/
def IsPeriodic (L : ℝ) (Y : R4 → V) : Prop := ∀ z μ, Y (z + Pi.single μ L) = Y z

theorem IsPeriodic.int_mul {L : ℝ} {Y : R4 → V} (hY : IsPeriodic L Y) (μ : Fin 4) (k : ℤ)
    (z : R4) : Y (z + Pi.single μ (k * L)) = Y z := by
  have hp : Function.Periodic (fun t : ℝ => Y (z + Pi.single μ t)) L := by
    intro t
    have := hY (z + Pi.single μ t) μ
    simp only [Pi.single_add, ← add_assoc] at this ⊢
    exact this
  have := (hp.int_mul k) 0
  simpa using this

theorem IsPeriodic.add_intVec {L : ℝ} {Y : R4 → V} (hY : IsPeriodic L Y) (k : Fin 4 → ℤ)
    (z : R4) : Y (z + L • realVec k) = Y z := by
  have hdec : L • realVec k = ∑ μ, Pi.single μ (k μ * L) := by
    funext ν
    simp [realVec, Finset.sum_apply, Pi.single_apply, mul_comm]
  rw [hdec]
  have key : ∀ s : Finset (Fin 4), Y (z + ∑ μ ∈ s, Pi.single μ ((k μ : ℝ) * L)) = Y z := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, ← add_assoc, add_right_comm, hY.int_mul a (k a)]
      exact ih
  exact key univ

/-- The position of a shifted node differs from the shifted position by a lattice of periods. -/
theorem exists_pos_add_castVec (h : ℝ) (x : Grid n) (m : Fin 4 → ℤ) :
    ∃ k : Fin 4 → ℤ, pos h (x + castVec m) = pos h x + h • realVec m + ((n : ℝ) * h) • realVec k := by
  have hk : ∀ μ, ∃ k : ℤ, (((x μ + (m μ : ZMod n)).val : ℤ) : ℝ) =
      ((x μ).val : ℝ) + (m μ : ℝ) + (n : ℝ) * k := by
    intro μ
    have h1 : (((x μ + (m μ : ZMod n)).val : ℤ) : ZMod n) = (((x μ).val + m μ : ℤ) : ZMod n) := by
      push_cast
      simp []
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
    obtain ⟨k, hk⟩ := h1
    refine ⟨-k, ?_⟩
    have : ((((x μ).val + m μ : ℤ)) : ℝ) - (((x μ + (m μ : ZMod n)).val : ℤ) : ℝ) = (n : ℝ) * k := by
      exact_mod_cast hk
    push_cast at this ⊢
    linarith
  choose k hk using hk
  refine ⟨k, ?_⟩
  funext μ
  have := hk μ
  simp only [pos, castVec, Pi.add_apply, Pi.smul_apply, realVec, smul_eq_mul]
  push_cast at this
  rw [this]
  ring

/-- Samples at shifted nodes are values at shifted points. -/
theorem samp_add_castVec {h : ℝ} {Y : R4 → V} (hY : IsPeriodic ((n : ℝ) * h) Y) (x : Grid n)
    (m : Fin 4 → ℤ) : samp h Y (x + castVec m) = Y (pos h x + h • realVec m) := by
  obtain ⟨k, hk⟩ := exists_pos_add_castVec h x m
  rw [samp, hk, hY.add_intVec]

/-! ### The discrete jet of a smooth field -/

/-- The shifted first jet of the field `Y` at the real base point `a` with mesh `h`:
`(Y(a + hσ_i))_i, (h⁻¹(Y(a + hσ_i + he_μ) - Y(a + hσ_i)))_{i,μ}`. -/
def discJet (σZ : ι → Fin 4 → ℤ) (h : ℝ) (Y : R4 → V) (a : R4) : Jet ι V :=
  (fun i => Y (a + h • realVec (σZ i)),
    fun p => h⁻¹ • (Y (a + h • realVec (σZ p.1) + h • evec p.2) - Y (a + h • realVec (σZ p.1))))

/-- The stencil of the samples is the discrete jet at the node position. -/
theorem stencil_samp {h : ℝ} {Y : R4 → V} (hY : IsPeriodic ((n : ℝ) * h) Y)
    (σZ : ι → Fin 4 → ℤ) (x : Grid n) (m : Fin 4 → ℤ) :
    stencil h (fun i => castVec (σZ i)) (x + castVec m) (samp h Y) =
      discJet σZ h Y (pos h x + h • realVec m) := by
  rw [ShiftedJetAction.stencil_apply]
  unfold discJet ShiftedJetAction.fwdDiff
  congr 1
  · funext i
    rw [add_assoc, ← castVec_add, samp_add_castVec hY, realVec_add, smul_add, add_assoc]
  · funext p
    rw [← castVec_single]
    simp only [add_assoc, ← castVec_add]
    rw [samp_add_castVec hY, samp_add_castVec hY]
    simp only [realVec_add, realVec_single, smul_add, add_assoc]

theorem stencil_samp' {h : ℝ} {Y : R4 → V} (hY : IsPeriodic ((n : ℝ) * h) Y)
    (σZ : ι → Fin 4 → ℤ) (x : Grid n) :
    stencil h (fun i => castVec (σZ i)) x (samp h Y) = discJet σZ h Y (pos h x) := by
  have h0 : (castVec 0 : Grid n) = 0 := by funext μ; simp [castVec]
  have h1 : realVec 0 = 0 := by funext μ; simp [realVec]
  have := stencil_samp hY σZ x 0
  rwa [h0, add_zero, h1, smul_zero, add_zero] at this

/-! ### The raw Euler row -/

/-- The raw Euler row `E_h(y)(x) = h⁻⁴ ∂_{y(x)} A(y)` of a lattice action. -/
def eulerRow (A : (Grid n → V) → ℝ) (h : ℝ) (y : Grid n → V) (x : Grid n) : V →L[ℝ] ℝ :=
  (h ^ 4)⁻¹ • (fderiv ℝ A y).comp (ContinuousLinearMap.single ℝ (fun _ : Grid n => V) x)

/-- Decomposition of the stencil map into slots. -/
theorem stencil_eq_sum (h : ℝ) (σ : ι → Grid n) (z : Grid n) (u : Grid n → V) :
    stencil h σ z u = ∑ i, ιv i (u (z + σ i)) +
      ∑ p, ιd p (ShiftedJetAction.fwdDiff h p.2 u (z + σ p.1)) := by
  rw [jet_eq_sum (stencil h σ z u), ShiftedJetAction.stencil_apply]

theorem hasFDerivAt_action {F : Jet ι V → ℝ} {h : ℝ} {σ : ι → Grid n} {y : Grid n → V}
    (hF : ∀ z, DifferentiableAt ℝ F (stencil h σ z y)) :
    HasFDerivAt (action F h σ)
      (h ^ 4 • ∑ z, (fderiv ℝ F (stencil h σ z y)).comp (stencil h σ z)) y := by
  have : action F h σ = fun y => h ^ 4 • ∑ z, F (stencil h σ z y) := by
    funext y; simp [action]
  rw [this]
  have hs : HasFDerivAt (fun y : Grid n → V => ∑ z, F (stencil h σ z y))
      (∑ z, (fderiv ℝ F (stencil h σ z y)).comp (stencil h σ z)) y := by
    refine HasFDerivAt.fun_sum fun z _ => ?_
    exact (hF z).hasFDerivAt.comp y ((stencil h σ z).hasFDerivAt (x := y))
  exact hs.const_smul (h ^ 4)

/-- Collapse of a nodal sum against a point mass. -/
theorem sum_single_shift (f : Grid n → V →L[ℝ] ℝ) (x a : Grid n) (w : V) :
    ∑ z, f z ((Pi.single x w : Grid n → V) (z + a)) = f (x - a) w := by
  rw [Fintype.sum_eq_single (x - a)]
  · simp
  · intro z hz
    have : z + a ≠ x := fun h => hz (by rw [← h]; abel)
    simp [this]

/-- **The explicit raw Euler row of a shifted-first-jet action** (discrete summation by parts):
`E_h(y)(x) = Σ_i D_{v_i}F(Ξ(x - σ_i)) + h⁻¹ Σ_{i,μ} (D_{d_{iμ}}F(Ξ(x - σ_i - e_μ)) - D_{d_{iμ}}F(Ξ(x - σ_i)))`. -/
theorem eulerRow_action_eq {F : Jet ι V → ℝ} {h : ℝ} (hh : h ≠ 0) {σ : ι → Grid n}
    {y : Grid n → V} (hF : ∀ z, DifferentiableAt ℝ F (stencil h σ z y)) (x : Grid n) :
    eulerRow (action F h σ) h y x =
      ∑ i, (fderiv ℝ F (stencil h σ (x - σ i) y)).comp (ιv i) +
        h⁻¹ • ∑ p : ι × Fin 4,
          ((fderiv ℝ F (stencil h σ (x - σ p.1 - unitVec n p.2) y)).comp (ιd p) -
            (fderiv ℝ F (stencil h σ (x - σ p.1) y)).comp (ιd p)) := by
  unfold eulerRow
  rw [(hasFDerivAt_action hF).fderiv]
  ext w
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    _root_.sum_apply, add_apply, sub_apply, ContinuousLinearMap.single_apply, smul_eq_mul]
  simp only [stencil_eq_sum h σ _ (Pi.single x w : Grid n → V), map_add, map_sum, sum_add_distrib]
  have hv : ∀ i, ∑ z, (fderiv ℝ F (stencil h σ z y)) (ιv i ((Pi.single x w : Grid n → V) (z + σ i))) =
      (fderiv ℝ F (stencil h σ (x - σ i) y)) (ιv i w) := fun i =>
    sum_single_shift (fun z => (fderiv ℝ F (stencil h σ z y)).comp (ιv i)) x (σ i) w
  have hd : ∀ p : ι × Fin 4, ∑ z, (fderiv ℝ F (stencil h σ z y))
      (ιd p (ShiftedJetAction.fwdDiff h p.2 (Pi.single x w) (z + σ p.1))) =
      h⁻¹ * ((fderiv ℝ F (stencil h σ (x - σ p.1 - unitVec n p.2) y)) (ιd p w) -
        (fderiv ℝ F (stencil h σ (x - σ p.1) y)) (ιd p w)) := by
    intro p
    simp only [ShiftedJetAction.fwdDiff, map_smul, map_sub, smul_eq_mul, ← mul_sum, sum_sub_distrib]
    congr 1
    congr 1
    · have := sum_single_shift (fun z => (fderiv ℝ F (stencil h σ z y)).comp (ιd p)) x
        (σ p.1 + unitVec n p.2) w
      rw [show x - (σ p.1 + unitVec n p.2) = x - σ p.1 - unitVec n p.2 by abel] at this
      simpa [add_assoc] using this
    · exact sum_single_shift (fun z => (fderiv ℝ F (stencil h σ z y)).comp (ιd p)) x (σ p.1) w
  rw [sum_comm (s := univ) (t := univ), sum_comm (s := univ) (t := (univ : Finset (ι × Fin 4)))]
  simp only [hv, hd, ← mul_sum]
  field_simp

/-! ### The continuum Euler–Lagrange expression -/

/-- The constant-jet map `(w, p) ↦ ((w)_i, (p_μ)_{i,μ})`: all shifts collapse at `h = 0`. -/
def cmap : V × (Fin 4 → V) →L[ℝ] Jet ι V :=
  (ContinuousLinearMap.pi fun _ : ι => ContinuousLinearMap.fst ℝ V (Fin 4 → V)).prod
    (ContinuousLinearMap.pi fun q : ι × Fin 4 =>
      (ContinuousLinearMap.proj q.2).comp (ContinuousLinearMap.snd ℝ V (Fin 4 → V)))

theorem cmap_apply (wp : V × (Fin 4 → V)) :
    (cmap wp : Jet ι V) = (fun _ => wp.1, fun q => wp.2 q.2) := rfl

/-- The first jet `(Y(z), (∂_μ Y(z))_μ)` of a continuum field. -/
def jet1 (Y : R4 → V) (z : R4) : V × (Fin 4 → V) := (Y z, fun μ => fderiv ℝ Y z (evec μ))

/-- **The continuum Euler–Lagrange expression** of a first-order density `L(w, p)`:
`E₀(z) = ∂_w L(Y, ∂Y)(z) - Σ_μ ∂_μ[∂_{p_μ} L(Y, ∂Y)](z)`, a covector on field values. -/
def contEuler (L : V × (Fin 4 → V) → ℝ) (Y : R4 → V) (z : R4) : V →L[ℝ] ℝ :=
  (fderiv ℝ L (jet1 Y z)).comp (ContinuousLinearMap.inl ℝ V (Fin 4 → V)) -
    ∑ μ, fderiv ℝ (fun z' => (fderiv ℝ L (jet1 Y z')).comp
      ((ContinuousLinearMap.inr ℝ V (Fin 4 → V)).comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => V) μ))) z (evec μ)

/-- The limiting (continuum) first-order density `L₀(w, p) = F(0, cmap(w, p))` of a mesh-dependent
jet density `F(h, ξ)`. -/
def limDensity (F : ℝ × Jet ι V → ℝ) : V × (Fin 4 → V) → ℝ := fun wp => F (0, cmap wp)

/-- The partial derivative `∂_ξ F(h, ξ)` of a jet density in the jet variable. -/
def pJet (F : ℝ × Jet ι V → ℝ) (q : ℝ × Jet ι V) : Jet ι V →L[ℝ] ℝ :=
  (fderiv ℝ F q).comp (ContinuousLinearMap.inr ℝ ℝ (Jet ι V))

theorem cmap_comp_inl :
    (cmap : V × (Fin 4 → V) →L[ℝ] Jet ι V).comp (ContinuousLinearMap.inl ℝ V (Fin 4 → V)) =
      ∑ i, ιv i := by
  ext w : 1
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, cmap_apply,
    _root_.sum_apply, ιv_apply]
  ext j
  · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
  · simp [Prod.snd_sum, Finset.sum_apply]

theorem cmap_comp_inr_single (μ : Fin 4) :
    (cmap : V × (Fin 4 → V) →L[ℝ] Jet ι V).comp ((ContinuousLinearMap.inr ℝ V (Fin 4 → V)).comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => V) μ)) = ∑ i, ιd (i, μ) := by
  ext w : 1
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, cmap_apply,
    _root_.sum_apply, ιd_apply, ContinuousLinearMap.single_apply]
  ext j
  · simp [Prod.fst_sum, Finset.sum_apply]
  · simp only [Prod.snd_sum, Finset.sum_apply, Pi.single_apply, Prod.ext_iff]
    by_cases hj : j.2 = μ
    · subst hj; simp
    · simp [hj]

/-! ### Regularity packets -/

/-- **Regularity of the jet density near the continuum jets**: on the balls of radius `δ` around
the points `(0, c)`, `c ∈ S`, the density is differentiable, its jet derivative `P = ∂_ξ F` is
differentiable with `‖DP‖ ≤ M₂`, and `DP` is `M₃`-Lipschitz on each ball (third-order control). -/
structure DensityReg (F : ℝ × Jet ι V → ℝ) (S : Set (Jet ι V)) (δ M₂ M₃ : ℝ) : Prop where
  diff : ∀ c ∈ S, ∀ q ∈ ball ((0 : ℝ), c) δ, DifferentiableAt ℝ F q
  diffP : ∀ c ∈ S, ∀ q ∈ ball ((0 : ℝ), c) δ, DifferentiableAt ℝ (pJet F) q
  boundDP : ∀ c ∈ S, ∀ q ∈ ball ((0 : ℝ), c) δ, ‖fderiv ℝ (pJet F) q‖ ≤ M₂
  lipDP : ∀ c ∈ S, ∀ q ∈ ball ((0 : ℝ), c) δ, ∀ q' ∈ ball ((0 : ℝ), c) δ,
    ‖fderiv ℝ (pJet F) q - fderiv ℝ (pJet F) q'‖ ≤ M₃ * ‖q - q'‖
  M₂_nonneg : 0 ≤ M₂
  M₃_nonneg : 0 ≤ M₃

/-- **Derivative bounds of a smooth field**: `C²` with `‖DY‖ ≤ B₁`, `DY` `B₂`-Lipschitz and `D²Y`
`B₃`-Lipschitz (i.e. third-order control). -/
structure FieldBound (Y : R4 → V) (B₁ B₂ B₃ : ℝ) : Prop where
  smooth : ContDiff ℝ 2 Y
  b1 : ∀ z, ‖fderiv ℝ Y z‖ ≤ B₁
  lip1 : ∀ a b, ‖fderiv ℝ Y b - fderiv ℝ Y a‖ ≤ B₂ * ‖b - a‖
  lip2 : ∀ a b, ‖fderiv ℝ (fderiv ℝ Y) b - fderiv ℝ (fderiv ℝ Y) a‖ ≤ B₃ * ‖b - a‖
  B₁_nonneg : 0 ≤ B₁
  B₂_nonneg : 0 ≤ B₂
  B₃_nonneg : 0 ≤ B₃

section FieldBoundLemmas

variable {Y : R4 → V} {B₁ B₂ B₃ : ℝ}

theorem FieldBound.diff0 (hY : FieldBound Y B₁ B₂ B₃) : Differentiable ℝ Y :=
  hY.smooth.differentiable (by norm_num)

theorem FieldBound.diff1 (hY : FieldBound Y B₁ B₂ B₃) : Differentiable ℝ (fderiv ℝ Y) :=
  (hY.smooth.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)

theorem FieldBound.symm (hY : FieldBound Y B₁ B₂ B₃) (z v w : R4) :
    fderiv ℝ (fderiv ℝ Y) z v w = fderiv ℝ (fderiv ℝ Y) z w v :=
  (hY.smooth.contDiffAt.isSymmSndFDerivAt (by simp [minSmoothness])).eq v w

theorem FieldBound.lip0 (hY : FieldBound Y B₁ B₂ B₃) (a b : R4) : ‖Y b - Y a‖ ≤ B₁ * ‖b - a‖ :=
  convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hY.diff0 z) (fun z _ => hY.b1 z)
    (mem_univ a) (mem_univ b)

/-- First-order Taylor remainder from a Lipschitz derivative. -/
theorem taylor1_le {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {f : R4 → W} {L : ℝ}
    (hL0 : 0 ≤ L) (hf : Differentiable ℝ f)
    (hL : ∀ a b, ‖fderiv ℝ f b - fderiv ℝ f a‖ ≤ L * ‖b - a‖)
    (b v : R4) : ‖f (b + v) - f b - fderiv ℝ f b v‖ ≤ L * ‖v‖ ^ 2 := by
  have hc : Convex ℝ (closedBall b ‖v‖) := convex_closedBall b ‖v‖
  have hb : b ∈ closedBall b ‖v‖ := mem_closedBall_self (norm_nonneg v)
  have hbv : b + v ∈ closedBall b ‖v‖ := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
  have key := hc.norm_image_sub_le_of_norm_fderiv_le' (f := f) (φ := fderiv ℝ f b)
    (C := L * ‖v‖) (fun z _ => hf z) (fun z hz => ?_) hb hbv
  · rw [add_sub_cancel_left] at key
    calc _ ≤ L * ‖v‖ * ‖v‖ := key
      _ = L * ‖v‖ ^ 2 := by ring
  · calc ‖fderiv ℝ f z - fderiv ℝ f b‖ ≤ L * ‖z - b‖ := hL b z
      _ ≤ L * ‖v‖ := by
        gcongr
        rw [← dist_eq_norm]
        exact hz

end FieldBoundLemmas


/-! ### Taylor estimates for the discrete jet -/

section JetEstimates

variable {Y : R4 → V} {B₁ B₂ B₃ : ℝ}

theorem norm_realVec_le {m : Fin 4 → ℤ} {s : ℝ} (hs : ∀ μ, |(m μ : ℝ)| ≤ s) (hs0 : 0 ≤ s) :
    ‖realVec m‖ ≤ s := by
  rw [pi_norm_le_iff_of_nonneg hs0]
  intro μ
  rw [Real.norm_eq_abs]
  exact hs μ

/-- Taylor: `h⁻¹(Y(c + h e) - Y(c)) = DY(c) e + O(B₂ h)`. -/
theorem norm_divDiff_sub_le (hY : FieldBound Y B₁ B₂ B₃) {h : ℝ} (hh : 0 < h) (c : R4) (μ : Fin 4) :
    ‖h⁻¹ • (Y (c + h • evec μ) - Y c) - fderiv ℝ Y c (evec μ)‖ ≤ B₂ * h := by
  have key := taylor1_le hY.B₂_nonneg hY.diff0 hY.lip1 c (h • evec μ)
  rw [norm_smul, norm_evec, Real.norm_eq_abs, abs_of_pos hh, mul_one, map_smul] at key
  have e : h⁻¹ • (Y (c + h • evec μ) - Y c) - fderiv ℝ Y c (evec μ) =
      h⁻¹ • (Y (c + h • evec μ) - Y c - h • fderiv ℝ Y c (evec μ)) := by
    simp only [smul_sub, smul_smul, inv_mul_cancel₀ hh.ne', one_smul]
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh)]
  calc h⁻¹ * ‖Y (c + h • evec μ) - Y c - h • fderiv ℝ Y c (evec μ)‖ ≤ h⁻¹ * (B₂ * h ^ 2) := by
        gcongr
    _ = B₂ * h := by field_simp

/-- Taylor for the derivative: `h⁻¹(DY(c + h e) - DY(c)) = D²Y(c) e + O(B₃ h)`. -/
theorem norm_divDiff1_sub_le (hY : FieldBound Y B₁ B₂ B₃) {h : ℝ} (hh : 0 < h) (c : R4)
    (μ : Fin 4) :
    ‖h⁻¹ • (fderiv ℝ Y (c + h • evec μ) - fderiv ℝ Y c) - fderiv ℝ (fderiv ℝ Y) c (evec μ)‖ ≤
      B₃ * h := by
  have key := taylor1_le hY.B₃_nonneg hY.diff1 hY.lip2 c (h • evec μ)
  rw [norm_smul, norm_evec, Real.norm_eq_abs, abs_of_pos hh, mul_one, map_smul] at key
  have e : h⁻¹ • (fderiv ℝ Y (c + h • evec μ) - fderiv ℝ Y c) - fderiv ℝ (fderiv ℝ Y) c (evec μ) =
      h⁻¹ • (fderiv ℝ Y (c + h • evec μ) - fderiv ℝ Y c - h • fderiv ℝ (fderiv ℝ Y) c (evec μ)) := by
    simp only [smul_sub, smul_smul, inv_mul_cancel₀ hh.ne', one_smul]
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh)]
  calc h⁻¹ * ‖fderiv ℝ Y (c + h • evec μ) - fderiv ℝ Y c - h • fderiv ℝ (fderiv ℝ Y) c (evec μ)‖
      ≤ h⁻¹ * (B₃ * h ^ 2) := by gcongr
    _ = B₃ * h := by field_simp

/-- The constant `c₁` of the jet estimate. -/
def cJet (B₁ B₂ s : ℝ) : ℝ := B₁ * (2 * s + 1) + B₂ * (2 * s + 2)

/-- The constant `c₂` of the jet-derivative estimate. -/
def cJet' (B₂ B₃ s : ℝ) : ℝ := B₂ * (2 * s + 1) + B₃ * (2 * s + 2)

variable {σZ : ι → Fin 4 → ℤ} {s : ℝ}

theorem norm_shift_sub_le {h : ℝ} (hh : 0 < h) (hs0 : 0 ≤ s) (hs : ∀ i μ, |(σZ i μ : ℝ)| ≤ s)
    {b z : R4} (hb : ‖b - z‖ ≤ h * (s + 1)) (i : ι) :
    ‖b + h • realVec (σZ i) - z‖ ≤ h * (2 * s + 1) := by
  have h1 : ‖h • realVec (σZ i)‖ ≤ h * s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    exact mul_le_mul_of_nonneg_left (norm_realVec_le (hs i) hs0) hh.le
  calc ‖b + h • realVec (σZ i) - z‖ = ‖(b - z) + h • realVec (σZ i)‖ := by congr 1; abel
    _ ≤ ‖b - z‖ + ‖h • realVec (σZ i)‖ := norm_add_le _ _
    _ ≤ h * (s + 1) + h * s := add_le_add hb h1
    _ = h * (2 * s + 1) := by ring

/-- **The discrete jet is `O(h)`-close to the continuum jet**:
`‖Ξ_h(b) - J¹Y(z)‖ ≤ c₁ h` for `‖b - z‖ ≤ (s + 1) h`. -/
theorem norm_discJet_sub_le (hY : FieldBound Y B₁ B₂ B₃) {h : ℝ} (hh : 0 < h) (hs0 : 0 ≤ s)
    (hs : ∀ i μ, |(σZ i μ : ℝ)| ≤ s) {b z : R4} (hb : ‖b - z‖ ≤ h * (s + 1)) :
    ‖discJet σZ h Y b - cmap (jet1 Y z)‖ ≤ h * cJet B₁ B₂ s := by
  have hc : 0 ≤ h * cJet B₁ B₂ s := by
    unfold cJet; have := hY.B₁_nonneg; have := hY.B₂_nonneg; positivity
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · rw [pi_norm_le_iff_of_nonneg hc]
    intro i
    simp only [discJet, cmap_apply, jet1, Prod.fst_sub, Pi.sub_apply]
    calc ‖Y (b + h • realVec (σZ i)) - Y z‖ ≤ B₁ * ‖b + h • realVec (σZ i) - z‖ := hY.lip0 _ _
      _ ≤ B₁ * (h * (2 * s + 1)) :=
          mul_le_mul_of_nonneg_left (norm_shift_sub_le hh hs0 hs hb i) hY.B₁_nonneg
      _ ≤ h * cJet B₁ B₂ s := by
          unfold cJet; have := mul_nonneg (mul_nonneg hh.le hY.B₂_nonneg) (show (0:ℝ) ≤ 2 * s + 2 by linarith); nlinarith
  · rw [pi_norm_le_iff_of_nonneg hc]
    intro p
    simp only [discJet, cmap_apply, jet1, Prod.snd_sub, Pi.sub_apply]
    set c := b + h • realVec (σZ p.1)
    have hcz : ‖c - z‖ ≤ h * (2 * s + 1) := norm_shift_sub_le hh hs0 hs hb p.1
    calc ‖h⁻¹ • (Y (c + h • evec p.2) - Y c) - fderiv ℝ Y z (evec p.2)‖
        = ‖(h⁻¹ • (Y (c + h • evec p.2) - Y c) - fderiv ℝ Y c (evec p.2)) +
            (fderiv ℝ Y c - fderiv ℝ Y z) (evec p.2)‖ := by
          congr 1; simp only [ContinuousLinearMap.sub_apply]; abel
      _ ≤ B₂ * h + ‖fderiv ℝ Y c - fderiv ℝ Y z‖ * ‖evec p.2‖ :=
          (norm_add_le _ _).trans
            (add_le_add (norm_divDiff_sub_le hY hh c p.2) (ContinuousLinearMap.le_opNorm _ _))
      _ ≤ B₂ * h + B₂ * (h * (2 * s + 1)) * 1 := by
          rw [norm_evec]
          gcongr
          exact (hY.lip1 z c).trans (mul_le_mul_of_nonneg_left hcz hY.B₂_nonneg)
      _ ≤ h * cJet B₁ B₂ s := by
          unfold cJet; have := mul_nonneg (mul_nonneg hh.le hY.B₁_nonneg) (show (0:ℝ) ≤ 2 * s + 1 by linarith); nlinarith

/-- The derivative of the discrete jet in the base point. -/
def dDisc (σZ : ι → Fin 4 → ℤ) (h : ℝ) (Y : R4 → V) (b : R4) : R4 →L[ℝ] Jet ι V :=
  (ContinuousLinearMap.pi fun i => fderiv ℝ Y (b + h • realVec (σZ i))).prod
    (ContinuousLinearMap.pi fun p : ι × Fin 4 =>
      h⁻¹ • (fderiv ℝ Y (b + h • realVec (σZ p.1) + h • evec p.2) -
        fderiv ℝ Y (b + h • realVec (σZ p.1))))

theorem hasFDerivAt_discJet (hY : FieldBound Y B₁ B₂ B₃) (h : ℝ) (b : R4) :
    HasFDerivAt (discJet σZ h Y) (dDisc σZ h Y b) b := by
  unfold discJet dDisc
  refine HasFDerivAt.prodMk (hasFDerivAt_pi.mpr fun i => ?_) (hasFDerivAt_pi.mpr fun p => ?_)
  · exact (hY.diff0 _).hasFDerivAt.comp b ((hasFDerivAt_id b).add_const _)
  · refine HasFDerivAt.const_smul (HasFDerivAt.sub ?_ ?_) h⁻¹
    · exact (hY.diff0 _).hasFDerivAt.comp b (((hasFDerivAt_id b).add_const _).add_const _)
    · exact (hY.diff0 _).hasFDerivAt.comp b ((hasFDerivAt_id b).add_const _)

/-- The derivative of the continuum jet `z ↦ J¹Y(z)`. -/
def dJet (Y : R4 → V) (z : R4) : R4 →L[ℝ] Jet ι V :=
  (cmap : V × (Fin 4 → V) →L[ℝ] Jet ι V).comp ((fderiv ℝ Y z).prod
    (ContinuousLinearMap.pi fun μ =>
      (ContinuousLinearMap.apply ℝ V (evec μ)).comp (fderiv ℝ (fderiv ℝ Y) z)))

theorem hasFDerivAt_jet (hY : FieldBound Y B₁ B₂ B₃) (z : R4) :
    HasFDerivAt (fun z => (cmap (jet1 Y z) : Jet ι V)) (dJet Y z) z := by
  unfold dJet jet1
  refine ((cmap : V × (Fin 4 → V) →L[ℝ] Jet ι V).hasFDerivAt
    (x := (Y z, fun μ => fderiv ℝ Y z (evec μ)))).comp z
    (HasFDerivAt.prodMk (hY.diff0 z).hasFDerivAt (hasFDerivAt_pi.mpr fun μ => ?_))
  exact (ContinuousLinearMap.apply ℝ V (evec μ)).hasFDerivAt.comp z (hY.diff1 z).hasFDerivAt

theorem norm_dDisc_le (hY : FieldBound Y B₁ B₂ B₃) {h : ℝ} (hh : 0 < h) (b : R4) :
    ‖dDisc σZ h Y b‖ ≤ B₁ + B₂ := by
  have h0 : 0 ≤ B₁ + B₂ := add_nonneg hY.B₁_nonneg hY.B₂_nonneg
  refine ContinuousLinearMap.opNorm_le_bound _ h0 fun v => ?_
  simp only [dDisc, ContinuousLinearMap.prod_apply, ContinuousLinearMap.pi_apply]
  rw [Prod.norm_def]
  have hv := norm_nonneg v
  refine max_le ?_ ?_
  · rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    calc ‖fderiv ℝ Y (b + h • realVec (σZ i)) v‖ ≤ ‖fderiv ℝ Y (b + h • realVec (σZ i))‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (B₁ + B₂) * ‖v‖ := by
          gcongr
          linarith [hY.b1 (b + h • realVec (σZ i)), hY.B₂_nonneg]
  · rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro p
    set c := b + h • realVec (σZ p.1)
    calc ‖(h⁻¹ • (fderiv ℝ Y (c + h • evec p.2) - fderiv ℝ Y c)) v‖
        ≤ ‖h⁻¹ • (fderiv ℝ Y (c + h • evec p.2) - fderiv ℝ Y c)‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (B₁ + B₂) * ‖v‖ := by
          gcongr
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh)]
          have := hY.lip1 c (c + h • evec p.2)
          rw [add_sub_cancel_left, norm_smul, norm_evec, Real.norm_eq_abs, abs_of_pos hh,
            mul_one] at this
          calc h⁻¹ * ‖fderiv ℝ Y (c + h • evec p.2) - fderiv ℝ Y c‖ ≤ h⁻¹ * (B₂ * h) := by gcongr
            _ = B₂ := by field_simp
            _ ≤ B₁ + B₂ := by linarith [hY.B₁_nonneg]

/-- **The derivative of the discrete jet is `O(h)`-close to that of the continuum jet**
(uses the symmetry of `D²Y`). -/
theorem norm_dDisc_sub_le (hY : FieldBound Y B₁ B₂ B₃) {h : ℝ} (hh : 0 < h) (hs0 : 0 ≤ s)
    (hs : ∀ i μ, |(σZ i μ : ℝ)| ≤ s) {b z : R4} (hb : ‖b - z‖ ≤ h * (s + 1)) :
    ‖dDisc σZ h Y b - dJet Y z‖ ≤ h * cJet' B₂ B₃ s := by
  have hc : 0 ≤ h * cJet' B₂ B₃ s := by
    unfold cJet'; have := hY.B₂_nonneg; have := hY.B₃_nonneg; positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun v => ?_
  have hv := norm_nonneg v
  simp only [ContinuousLinearMap.sub_apply, dDisc, dJet, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply, cmap_apply,
    ContinuousLinearMap.apply_apply]
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    simp only [Prod.fst_sub, Pi.sub_apply]
    calc ‖fderiv ℝ Y (b + h • realVec (σZ i)) v - fderiv ℝ Y z v‖
        = ‖(fderiv ℝ Y (b + h • realVec (σZ i)) - fderiv ℝ Y z) v‖ := rfl
      _ ≤ ‖fderiv ℝ Y (b + h • realVec (σZ i)) - fderiv ℝ Y z‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (B₂ * (h * (2 * s + 1))) * ‖v‖ := by
          gcongr
          exact (hY.lip1 _ _).trans
            (mul_le_mul_of_nonneg_left (norm_shift_sub_le hh hs0 hs hb i) hY.B₂_nonneg)
      _ ≤ h * cJet' B₂ B₃ s * ‖v‖ := by
          refine mul_le_mul_of_nonneg_right ?_ hv
          unfold cJet'; have := mul_nonneg (mul_nonneg hh.le hY.B₃_nonneg) (show (0:ℝ) ≤ 2 * s + 2 by linarith); nlinarith
  · rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro p
    simp only [Prod.snd_sub, Pi.sub_apply]
    set c := b + h • realVec (σZ p.1)
    have hcz : ‖c - z‖ ≤ h * (2 * s + 1) := norm_shift_sub_le hh hs0 hs hb p.1
    have hsym : fderiv ℝ (fderiv ℝ Y) z v (evec p.2) = fderiv ℝ (fderiv ℝ Y) z (evec p.2) v :=
      hY.symm z v (evec p.2)
    rw [hsym]
    set T := h⁻¹ • (fderiv ℝ Y (c + h • evec p.2) - fderiv ℝ Y c)
    calc ‖T v - fderiv ℝ (fderiv ℝ Y) z (evec p.2) v‖
        = ‖((T - fderiv ℝ (fderiv ℝ Y) c (evec p.2)) +
            (fderiv ℝ (fderiv ℝ Y) c - fderiv ℝ (fderiv ℝ Y) z) (evec p.2)) v‖ := by
          congr 1; simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]; abel
      _ ≤ ‖(T - fderiv ℝ (fderiv ℝ Y) c (evec p.2)) +
            (fderiv ℝ (fderiv ℝ Y) c - fderiv ℝ (fderiv ℝ Y) z) (evec p.2)‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (B₃ * h + B₃ * (h * (2 * s + 1)) * 1) * ‖v‖ := by
          gcongr
          refine (norm_add_le _ _).trans (add_le_add (norm_divDiff1_sub_le hY hh c p.2) ?_)
          refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
          rw [norm_evec]
          gcongr
          exact (hY.lip2 z c).trans (mul_le_mul_of_nonneg_left hcz hY.B₃_nonneg)
      _ ≤ h * cJet' B₂ B₃ s * ‖v‖ := by
          refine mul_le_mul_of_nonneg_right ?_ hv
          unfold cJet'; have := mul_nonneg (mul_nonneg hh.le hY.B₂_nonneg) (show (0:ℝ) ≤ 2 * s + 1 by linarith); nlinarith

end JetEstimates


/-! ### The continuum row in slot form -/

section ContRow

variable {F : ℝ × Jet ι V → ℝ}

/-- The partial derivative of `ξ ↦ F(h, ξ)` is the jet derivative `pJet F (h, ξ)`. -/
theorem fderiv_slice {h : ℝ} {ξ : Jet ι V} (hF : DifferentiableAt ℝ F (h, ξ)) :
    fderiv ℝ (fun ξ => F (h, ξ)) ξ = pJet F (h, ξ) := by
  have hin : HasFDerivAt (fun ξ : Jet ι V => ((h, ξ) : ℝ × Jet ι V))
      (ContinuousLinearMap.inr ℝ ℝ (Jet ι V)) ξ := by
    have := ((ContinuousLinearMap.inr ℝ ℝ (Jet ι V)).hasFDerivAt (x := ξ)).const_add
      ((h, 0) : ℝ × Jet ι V)
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun ξ' => ?_)
    simp
  exact (hF.hasFDerivAt.comp ξ hin).fderiv

/-- The derivative of the limiting density at a constant jet. -/
theorem fderiv_limDensity {wp : V × (Fin 4 → V)} (hF : DifferentiableAt ℝ F (0, cmap wp)) :
    fderiv ℝ (limDensity F) wp = (pJet F (0, cmap wp)).comp cmap := by
  have hin : HasFDerivAt (fun wp : V × (Fin 4 → V) => ((0 : ℝ), (cmap wp : Jet ι V)))
      ((ContinuousLinearMap.inr ℝ ℝ (Jet ι V)).comp cmap) wp :=
    ((ContinuousLinearMap.inr ℝ ℝ (Jet ι V)).comp cmap).hasFDerivAt
  rw [show limDensity F = F ∘ fun wp : V × (Fin 4 → V) => ((0 : ℝ), (cmap wp : Jet ι V)) from rfl,
    (hF.hasFDerivAt.comp wp hin).fderiv, pJet, ContinuousLinearMap.comp_assoc]

variable {S : Set (Jet ι V)} {δ M₂ M₃ : ℝ} {Y : R4 → V} {B₁ B₂ B₃ : ℝ}

/-- The jet derivative along the continuum jet is differentiable. -/
theorem hasFDerivAt_pJet_jet (hF : DensityReg F S δ M₂ M₃) (hδ : 0 < δ)
    (hY : FieldBound Y B₁ B₂ B₃) (hS : ∀ z, cmap (jet1 Y z) ∈ S) (z : R4) :
    HasFDerivAt (fun z => pJet F (0, (cmap (jet1 Y z) : Jet ι V)))
      ((fderiv ℝ (pJet F) (0, cmap (jet1 Y z))).comp
        ((ContinuousLinearMap.inr ℝ ℝ (Jet ι V)).comp (dJet Y z))) z := by
  have hin : HasFDerivAt (fun z => ((0 : ℝ), (cmap (jet1 Y z) : Jet ι V)))
      ((ContinuousLinearMap.inr ℝ ℝ (Jet ι V)).comp (dJet Y z)) z :=
    ((ContinuousLinearMap.inr ℝ ℝ (Jet ι V)).hasFDerivAt (x := cmap (jet1 Y z))).comp z
      (hasFDerivAt_jet (ι := ι) hY z)
  exact (hF.diffP _ (hS z) _ (mem_ball_self hδ)).hasFDerivAt.comp z hin

/-- **The continuum Euler row in slot form**: for the limiting density,
`E₀(z) = Σ_i P(0, J z) ∘ ι_{v,i} - Σ_{i,μ} DP(0, J z)[(0, DJ(z) e_μ)] ∘ ι_{d,iμ}`. -/
theorem contEuler_limDensity_eq (hF : DensityReg F S δ M₂ M₃) (hδ : 0 < δ)
    (hY : FieldBound Y B₁ B₂ B₃) (hS : ∀ z, cmap (jet1 Y z) ∈ S) (z : R4) :
    contEuler (limDensity F) Y z =
      ∑ i, (pJet F (0, cmap (jet1 Y z))).comp (ιv i) -
        ∑ p : ι × Fin 4, ((fderiv ℝ (pJet F) (0, cmap (jet1 Y z))) (0, dJet Y z (evec p.2))).comp
          (ιd p) := by
  have hd : ∀ z', DifferentiableAt ℝ F (0, cmap (jet1 Y z')) := fun z' =>
    hF.diff _ (hS z') _ (mem_ball_self hδ)
  unfold contEuler
  have h1 : ∀ z', fderiv ℝ (limDensity F) (jet1 Y z') = (pJet F (0, cmap (jet1 Y z'))).comp cmap :=
    fun z' => fderiv_limDensity (hd z')
  have h2 : ∀ μ, (fun z' => (fderiv ℝ (limDensity F) (jet1 Y z')).comp
      ((ContinuousLinearMap.inr ℝ V (Fin 4 → V)).comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => V) μ))) =
      fun z' => ((ContinuousLinearMap.compL ℝ (V) (Jet ι V) ℝ).flip (∑ i, ιd (i, μ)))
        (pJet F (0, cmap (jet1 Y z'))) := by
    intro μ
    funext z'
    rw [h1, ContinuousLinearMap.comp_assoc, cmap_comp_inr_single]
    rfl
  simp only [h2]
  rw [h1, ContinuousLinearMap.comp_assoc, cmap_comp_inl, ContinuousLinearMap.comp_finset_sum]
  congr 1
  rw [← Finset.univ_product_univ, Finset.sum_product_right]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hD := (((ContinuousLinearMap.compL ℝ V (Jet ι V) ℝ).flip (∑ i, ιd (i, μ))).hasFDerivAt).comp z
    (hasFDerivAt_pJet_jet hF hδ hY hS z)
  rw [show (fun z' => ((ContinuousLinearMap.compL ℝ V (Jet ι V) ℝ).flip (∑ i, ιd (i, μ)))
      (pJet F (0, cmap (jet1 Y z')))) = _ ∘ _ from rfl, hD.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.inr_apply,
    ContinuousLinearMap.comp_finset_sum]

end ContRow

/-! ### The main estimate -/

/-- The constant of `norm_eulerRow_sub_contEuler_le`. -/
def eulerConst (M₂ M₃ B₁ B₂ B₃ s : ℝ) (N : ℕ) : ℝ :=
  N * (M₂ * (1 + cJet B₁ B₂ s) + 4 * (M₃ * (1 + cJet B₁ B₂ s) * (B₁ + B₂) + M₂ * cJet' B₂ B₃ s))

section Main

variable {F : ℝ × Jet ι V → ℝ} {S : Set (Jet ι V)} {δ M₂ M₃ : ℝ} {Y : R4 → V}
  {B₁ B₂ B₃ : ℝ} {σZ : ι → Fin 4 → ℤ} {s : ℝ}

theorem norm_comp_slot_le {X : Jet ι V →L[ℝ] ℝ} {ι' : V →L[ℝ] Jet ι V} (hι : ‖ι'‖ ≤ 1) :
    ‖X.comp ι'‖ ≤ ‖X‖ :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hι)

/-- The discrete jets near the continuum jet lie in the regularity ball. -/
theorem discJet_mem_ball (hY : FieldBound Y B₁ B₂ B₃) {h : ℝ} (hh : 0 < h) (hs0 : 0 ≤ s)
    (hs : ∀ i μ, |(σZ i μ : ℝ)| ≤ s) (hδ : h * (1 + cJet B₁ B₂ s) < δ) {b z : R4}
    (hb : ‖b - z‖ ≤ h * (s + 1)) :
    (h, discJet σZ h Y b) ∈ ball ((0 : ℝ), (cmap (jet1 Y z) : Jet ι V)) δ ∧
      ‖((h, discJet σZ h Y b) : ℝ × Jet ι V) - (0, cmap (jet1 Y z))‖ ≤ h * (1 + cJet B₁ B₂ s) := by
  have hJ := norm_discJet_sub_le (ι := ι) hY hh hs0 hs hb (σZ := σZ)
  have hc : 0 ≤ cJet B₁ B₂ s := by
    unfold cJet; have := hY.B₁_nonneg; have := hY.B₂_nonneg; positivity
  have hle : ‖((h, discJet σZ h Y b) : ℝ × Jet ι V) - (0, cmap (jet1 Y z))‖ ≤
      h * (1 + cJet B₁ B₂ s) := by
    rw [Prod.norm_def]
    simp only [Prod.fst_sub, Prod.snd_sub, sub_zero, Real.norm_eq_abs, abs_of_pos hh]
    refine max_le (by nlinarith) (hJ.trans (by nlinarith))
  exact ⟨by rw [mem_ball, dist_eq_norm]; exact hle.trans_lt hδ, hle⟩

/-- **Discrete-to-continuum Euler consistency for shifted-first-jet actions.**  Under the
regularity packet `DensityReg F S δ M₂ M₃` around the continuum jets of a `(n h)`-periodic field
`Y` with the bounds `FieldBound Y B₁ B₂ B₃`, and for a mesh `0 < h` with `h (1 + c₁) < δ`, the raw
Euler row of the lattice action `h⁴ Σ_x F(h, Ξ_h y(x))` at the samples `𝖲_h Y` is `O(h)`-close, at
every node, to the continuum Euler–Lagrange expression of the limiting density
`L₀(w, p) = F(0, (w; p))` at the node position:
`‖E_h(𝖲_h Y)(x) - E₀(Y)(h x̃)‖ ≤ eulerConst · h`. -/
theorem norm_eulerRow_sub_contEuler_le (hF : DensityReg F S δ M₂ M₃) (hY : FieldBound Y B₁ B₂ B₃)
    (hS : ∀ z, cmap (jet1 Y z) ∈ S) (hs0 : 0 ≤ s) (hs : ∀ i μ, |(σZ i μ : ℝ)| ≤ s) {h : ℝ}
    (hh : 0 < h) (hper : IsPeriodic ((n : ℝ) * h) Y) (hδ : h * (1 + cJet B₁ B₂ s) < δ)
    (x : Grid n) :
    ‖eulerRow (action (fun ξ => F (h, ξ)) h (fun i => castVec (σZ i))) h (samp h Y) x -
        contEuler (limDensity F) Y (pos h x)‖ ≤
      eulerConst M₂ M₃ B₁ B₂ B₃ s (Fintype.card ι) * h := by
  have hc1 : 0 ≤ cJet B₁ B₂ s := by
    unfold cJet; have := hY.B₁_nonneg; have := hY.B₂_nonneg; positivity
  have hδ0 : 0 < δ := lt_of_le_of_lt (by positivity) hδ
  set σ : ι → Grid n := fun i => castVec (σZ i) with hσ
  set z₀ := pos h x with hz₀
  set J : Jet ι V := cmap (jet1 Y z₀) with hJ
  set P := pJet F with hP
  -- differentiability at every stencil
  have hdiff : ∀ z, DifferentiableAt ℝ (fun ξ => F (h, ξ)) (stencil h σ z (samp h Y)) := by
    intro z
    rw [hσ, stencil_samp' hper]
    have hm := (discJet_mem_ball (ι := ι) (σZ := σZ) hY hh hs0 hs hδ
      (b := pos h z) (z := pos h z) (by simp; positivity)).1
    have hin := ((ContinuousLinearMap.inr ℝ ℝ (Jet ι V)).hasFDerivAt
      (x := discJet σZ h Y (pos h z))).const_add ((h, 0) : ℝ × Jet ι V)
    have hin' : DifferentiableAt ℝ (fun ξ : Jet ι V => ((h, ξ) : ℝ × Jet ι V))
        (discJet σZ h Y (pos h z)) :=
      (hin.congr_of_eventuallyEq (Eventually.of_forall fun ξ' => by simp)).differentiableAt
    exact (hF.diff _ (hS _) _ hm).comp _ hin'
  -- the shifted base points
  set a : ι → R4 := fun i => z₀ + h • realVec (-σZ i) with ha
  set a' : ι × Fin 4 → R4 := fun p => z₀ + h • realVec (-σZ p.1 - Pi.single p.2 1) with ha'
  have hnode : ∀ i, x - σ i = x + castVec (-σZ i) := fun i => by
    rw [castVec_neg, sub_eq_add_neg]
  have hnode' : ∀ p : ι × Fin 4, x - σ p.1 - unitVec n p.2 = x + castVec (-σZ p.1 - Pi.single p.2 1) :=
    fun p => by rw [sub_eq_add_neg (-σZ p.1), castVec_add, castVec_neg, castVec_neg, castVec_single]; abel
  have hst : ∀ i, stencil h σ (x - σ i) (samp h Y) = discJet σZ h Y (a i) := fun i => by
    rw [hnode, hσ, stencil_samp hper]
  have hst' : ∀ p : ι × Fin 4, stencil h σ (x - σ p.1 - unitVec n p.2) (samp h Y) =
      discJet σZ h Y (a' p) := fun p => by
    rw [hnode', hσ, stencil_samp hper]
  have hsi : ∀ i μ, |((-σZ i) μ : ℝ)| ≤ s := fun i μ => by
    simpa using hs i μ
  have ha_le : ∀ i, ‖a i - z₀‖ ≤ h * (s + 1) := fun i => by
    rw [ha]; simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    exact mul_le_mul_of_nonneg_left ((norm_realVec_le (hsi i) hs0).trans (by linarith)) hh.le
  have hsa : ∀ (p : ι × Fin 4) (μ : Fin 4),
      |(((-σZ p.1 - Pi.single p.2 1 : Fin 4 → ℤ) μ : ℤ) : ℝ)| ≤ s + 1 := by
    intro p μ
    have h1 := hs p.1 μ
    simp only [Pi.sub_apply, Pi.neg_apply, Int.cast_sub, Int.cast_neg]
    by_cases hμ : μ = p.2
    · subst hμ
      simp only [Pi.single_eq_same, Int.cast_one]
      calc |-(σZ p.1 p.2 : ℝ) - 1| ≤ |-(σZ p.1 p.2 : ℝ)| + |(1 : ℝ)| := abs_sub _ _
        _ ≤ s + 1 := by rw [abs_neg, abs_one]; linarith
    · simp only [Pi.single_eq_of_ne hμ, Int.cast_zero, sub_zero, abs_neg]; linarith
  have ha'_le : ∀ p : ι × Fin 4, ‖a' p - z₀‖ ≤ h * (s + 1) := fun p => by
    rw [ha']; simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    exact mul_le_mul_of_nonneg_left (norm_realVec_le (hsa p) (by linarith)) hh.le
  have hseg : ∀ p : ι × Fin 4, a p.1 - a' p = h • evec p.2 := fun p => by
    rw [ha, ha']
    simp only [add_sub_add_left_eq_sub, ← smul_sub]
    congr 1
    rw [sub_eq_add_neg (-σZ p.1), realVec_add, realVec_neg (Pi.single p.2 1), realVec_single]
    abel
  -- the two rows in slot form
  rw [eulerRow_action_eq hh.ne' hdiff x, contEuler_limDensity_eq hF hδ0 hY hS z₀]
  have hP1 : ∀ i, fderiv ℝ (fun ξ => F (h, ξ)) (stencil h σ (x - σ i) (samp h Y)) =
      P (h, discJet σZ h Y (a i)) := fun i => by
    rw [hst]
    exact fderiv_slice (hF.diff _ (hS z₀) _ (discJet_mem_ball hY hh hs0 hs hδ (ha_le i)).1)
  have hP2 : ∀ p : ι × Fin 4,
      fderiv ℝ (fun ξ => F (h, ξ)) (stencil h σ (x - σ p.1 - unitVec n p.2) (samp h Y)) =
        P (h, discJet σZ h Y (a' p)) := fun p => by
    rw [hst']
    exact fderiv_slice (hF.diff _ (hS z₀) _ (discJet_mem_ball hY hh hs0 hs hδ (ha'_le p)).1)
  simp only [hP1, hP2]
  set φ : R4 →L[ℝ] (Jet ι V →L[ℝ] ℝ) :=
    (fderiv ℝ P (0, J)).comp ((ContinuousLinearMap.inr ℝ ℝ (Jet ι V)).comp (dJet Y z₀)) with hφ
  have hrw : ∀ p : ι × Fin 4, (fderiv ℝ P (0, J)) (0, dJet Y z₀ (evec p.2)) = φ (evec p.2) :=
    fun p => rfl
  rw [← hP, ← hJ]
  simp only [hrw]
  -- algebraic rearrangement
  have hEq : (∑ i, (P (h, discJet σZ h Y (a i))).comp (ιv i) +
      h⁻¹ • ∑ p : ι × Fin 4, ((P (h, discJet σZ h Y (a' p))).comp (ιd p) -
        (P (h, discJet σZ h Y (a p.1))).comp (ιd p))) -
      (∑ i, (P (0, J)).comp (ιv i) - ∑ p : ι × Fin 4, (φ (evec p.2)).comp (ιd p)) =
      ∑ i, (P (h, discJet σZ h Y (a i)) - P (0, J)).comp (ιv i) +
        ∑ p : ι × Fin 4, (h⁻¹ • (P (h, discJet σZ h Y (a' p)) - P (h, discJet σZ h Y (a p.1))) +
          φ (evec p.2)).comp (ιd p) := by
    simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.add_comp,
      ContinuousLinearMap.smul_comp, Finset.smul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      smul_sub]
    abel
  rw [hEq]
  -- bounds
  set C₁ := cJet B₁ B₂ s
  set C₂ := cJet' B₂ B₃ s
  have hball : ∀ b, ‖b - z₀‖ ≤ h * (s + 1) →
      (h, discJet σZ h Y b) ∈ ball ((0 : ℝ), J) δ ∧
        ‖((h, discJet σZ h Y b) : ℝ × Jet ι V) - (0, J)‖ ≤ h * (1 + C₁) :=
    fun b hb => discJet_mem_ball hY hh hs0 hs hδ hb
  have hJmem : ((0 : ℝ), J) ∈ ball ((0 : ℝ), J) δ := mem_ball_self hδ0
  -- value terms
  have hval : ∀ i, ‖(P (h, discJet σZ h Y (a i)) - P (0, J)).comp (ιv i)‖ ≤ M₂ * (h * (1 + C₁)) := by
    intro i
    refine (norm_comp_slot_le (norm_ιv_le i)).trans ?_
    obtain ⟨hm, hd⟩ := hball (a i) (ha_le i)
    have := (convex_ball ((0 : ℝ), J) δ).norm_image_sub_le_of_norm_fderiv_le
      (fun q hq => hF.diffP _ (hS z₀) q hq) (fun q hq => hF.boundDP _ (hS z₀) q hq) hJmem hm
    exact this.trans (mul_le_mul_of_nonneg_left hd hF.M₂_nonneg)
  -- difference terms
  have hdif : ∀ p : ι × Fin 4, ‖(h⁻¹ • (P (h, discJet σZ h Y (a' p)) - P (h, discJet σZ h Y (a p.1))) +
      φ (evec p.2)).comp (ιd p)‖ ≤ h * (M₃ * (1 + C₁) * (B₁ + B₂) + M₂ * C₂) := by
    intro p
    refine (norm_comp_slot_le (norm_ιd_le p)).trans ?_
    set g : R4 → (Jet ι V →L[ℝ] ℝ) := fun b => P (h, discJet σZ h Y b) with hg
    -- the segment stays in the ball
    have hsegball : segment ℝ (a' p) (a p.1) ⊆ closedBall z₀ (h * (s + 1)) :=
      (convex_closedBall z₀ _).segment_subset (by rw [mem_closedBall, dist_eq_norm]; exact ha'_le p)
        (by rw [mem_closedBall, dist_eq_norm]; exact ha_le p.1)
    have hgd : ∀ b ∈ segment ℝ (a' p) (a p.1), HasFDerivAt g
        ((fderiv ℝ P (h, discJet σZ h Y b)).comp
          ((ContinuousLinearMap.inr ℝ ℝ (Jet ι V)).comp (dDisc σZ h Y b))) b := by
      intro b hb
      have hb' : ‖b - z₀‖ ≤ h * (s + 1) := by
        have := hsegball hb; rwa [mem_closedBall, dist_eq_norm] at this
      have hin : HasFDerivAt (fun b => ((h, discJet σZ h Y b) : ℝ × Jet ι V))
          ((ContinuousLinearMap.inr ℝ ℝ (Jet ι V)).comp (dDisc σZ h Y b)) b := by
        have := (((ContinuousLinearMap.inr ℝ ℝ (Jet ι V)).hasFDerivAt
          (x := discJet σZ h Y b)).comp b (hasFDerivAt_discJet (σZ := σZ) hY h b)).const_add
          ((h, 0) : ℝ × Jet ι V)
        refine this.congr_of_eventuallyEq (Eventually.of_forall fun b' => ?_)
        simp
      exact (hF.diffP _ (hS z₀) _ (hball b hb').1).hasFDerivAt.comp b hin
    have hgb : ∀ b ∈ segment ℝ (a' p) (a p.1), ‖fderiv ℝ g b - φ‖ ≤
        h * (M₃ * (1 + C₁) * (B₁ + B₂) + M₂ * C₂) := by
      intro b hb
      have hb' : ‖b - z₀‖ ≤ h * (s + 1) := by
        have := hsegball hb; rwa [mem_closedBall, dist_eq_norm] at this
      obtain ⟨hm, hd⟩ := hball b hb'
      rw [(hgd b hb).fderiv, hφ]
      set A := fderiv ℝ P (h, discJet σZ h Y b)
      set A₀ := fderiv ℝ P (0, J)
      set D := dDisc σZ h Y b
      set D₀ := (dJet Y z₀ : R4 →L[ℝ] Jet ι V)
      set ιr := ContinuousLinearMap.inr ℝ ℝ (Jet ι V)
      have hιr : ‖ιr‖ ≤ 1 := by
        refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
        simp [ιr, Prod.norm_def]
      have e : A.comp (ιr.comp D) - A₀.comp (ιr.comp D₀) =
          (A - A₀).comp (ιr.comp D) + A₀.comp (ιr.comp (D - D₀)) := by
        simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]; abel
      rw [e]
      have hAA : ‖A - A₀‖ ≤ M₃ * (h * (1 + C₁)) :=
        (hF.lipDP _ (hS z₀) _ hm _ hJmem).trans (mul_le_mul_of_nonneg_left hd hF.M₃_nonneg)
      have hDD : ‖D - D₀‖ ≤ h * C₂ := norm_dDisc_sub_le hY hh hs0 hs hb'
      have hD : ‖D‖ ≤ B₁ + B₂ := norm_dDisc_le hY hh b
      have hA₀ : ‖A₀‖ ≤ M₂ := hF.boundDP _ (hS z₀) _ hJmem
      calc ‖(A - A₀).comp (ιr.comp D) + A₀.comp (ιr.comp (D - D₀))‖
          ≤ ‖A - A₀‖ * (‖ιr‖ * ‖D‖) + ‖A₀‖ * (‖ιr‖ * ‖D - D₀‖) := by
            refine (norm_add_le ((A - A₀).comp (ιr.comp D)) (A₀.comp (ιr.comp (D - D₀)))).trans
              (add_le_add ?_ ?_)
            · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
                (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
                  (norm_nonneg (A - A₀)))
            · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
                (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
                  (norm_nonneg A₀))
        _ ≤ (M₃ * (h * (1 + C₁))) * (1 * (B₁ + B₂)) + M₂ * (1 * (h * C₂)) := by
            have hDn := norm_nonneg D
            have hDDn := norm_nonneg (D - D₀)
            have hm3 : 0 ≤ M₃ * (h * (1 + C₁)) := by have := hF.M₃_nonneg; positivity
            exact add_le_add
              (mul_le_mul hAA (mul_le_mul hιr hD hDn zero_le_one) (by positivity) hm3)
              (mul_le_mul hA₀ (mul_le_mul hιr hDD hDDn zero_le_one) (by positivity) hF.M₂_nonneg)
        _ = h * (M₃ * (1 + C₁) * (B₁ + B₂) + M₂ * C₂) := by ring
    have hmv := (convex_segment (a' p) (a p.1)).norm_image_sub_le_of_norm_fderiv_le'
      (f := g) (φ := φ) (fun b hb => (hgd b hb).differentiableAt) hgb
      (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
    rw [hseg p, norm_smul, norm_evec, Real.norm_eq_abs, abs_of_pos hh, mul_one] at hmv
    have e : h⁻¹ • (P (h, discJet σZ h Y (a' p)) - P (h, discJet σZ h Y (a p.1))) + φ (evec p.2) =
        -(h⁻¹ • (g (a p.1) - g (a' p) - φ (h • evec p.2))) := by
      rw [map_smul, hg]
      simp only [smul_sub, smul_smul, inv_mul_cancel₀ hh.ne', one_smul, neg_sub]
      abel
    rw [e, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh)]
    calc h⁻¹ * ‖g (a p.1) - g (a' p) - φ (h • evec p.2)‖
        ≤ h⁻¹ * (h * (M₃ * (1 + C₁) * (B₁ + B₂) + M₂ * C₂) * h) := by gcongr
      _ = h * (M₃ * (1 + C₁) * (B₁ + B₂) + M₂ * C₂) := by field_simp
  -- summation
  calc ‖∑ i, (P (h, discJet σZ h Y (a i)) - P (0, J)).comp (ιv i) +
        ∑ p : ι × Fin 4, (h⁻¹ • (P (h, discJet σZ h Y (a' p)) - P (h, discJet σZ h Y (a p.1))) +
          φ (evec p.2)).comp (ιd p)‖
      ≤ ∑ i : ι, M₂ * (h * (1 + C₁)) +
          ∑ p : ι × Fin 4, h * (M₃ * (1 + C₁) * (B₁ + B₂) + M₂ * C₂) :=
        (norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans (Finset.sum_le_sum
          fun i _ => hval i)) ((norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => hdif p)))
    _ = eulerConst M₂ M₃ B₁ B₂ B₃ s (Fintype.card ι) * h := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul, eulerConst]
        push_cast
        ring

end Main


/-! ### Second and third derivatives through `iteratedFDeriv` -/

section IterBounds

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup W]
  [NormedSpace ℝ W]

theorem norm_fderiv_fderiv_eq (f : E → W) (x : E) :
    ‖fderiv ℝ (fderiv ℝ f) x‖ = ‖iteratedFDeriv ℝ 2 f x‖ := by
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]

/-- The difference of second derivatives is controlled by that of the second iterated
derivatives. -/
theorem norm_fderiv_fderiv_sub_le (f : E → W) (a b : E) :
    ‖fderiv ℝ (fderiv ℝ f) b - fderiv ℝ (fderiv ℝ f) a‖ ≤
      ‖iteratedFDeriv ℝ 2 f b - iteratedFDeriv ℝ 2 f a‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  have h := (iteratedFDeriv ℝ 2 f b - iteratedFDeriv ℝ 2 f a).le_opNorm ![v, w]
  simp only [ContinuousMultilinearMap.sub_apply, iteratedFDeriv_two_apply, Fin.prod_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h
  simpa [mul_assoc] using h

/-- A `C³` field with `‖D²f‖ ≤ B₂` has a `B₂`-Lipschitz derivative. -/
theorem lipschitz_fderiv_of_iteratedFDeriv {f : E → W} (hf : ContDiff ℝ 3 f) {B₂ : ℝ}
    (hB : ∀ z, ‖iteratedFDeriv ℝ 2 f z‖ ≤ B₂) (a b : E) :
    ‖fderiv ℝ f b - fderiv ℝ f a‖ ≤ B₂ * ‖b - a‖ := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num)
  exact convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hd z)
    (fun z _ => by rw [norm_fderiv_fderiv_eq]; exact hB z) (mem_univ a) (mem_univ b)

/-- A `C³` field with `‖D³f‖ ≤ B₃` has a `B₃`-Lipschitz second derivative. -/
theorem lipschitz_fderiv_fderiv_of_iteratedFDeriv {f : E → W} (hf : ContDiff ℝ 3 f) {B₃ : ℝ}
    (hB : ∀ z, ‖iteratedFDeriv ℝ 3 f z‖ ≤ B₃) (a b : E) :
    ‖fderiv ℝ (fderiv ℝ f) b - fderiv ℝ (fderiv ℝ f) a‖ ≤ B₃ * ‖b - a‖ := by
  refine (norm_fderiv_fderiv_sub_le f a b).trans ?_
  have hd : Differentiable ℝ (iteratedFDeriv ℝ 2 f) :=
    hf.differentiable_iteratedFDeriv (by norm_num)
  exact convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hd z)
    (fun z _ => by rw [norm_fderiv_iteratedFDeriv]; exact hB z) (mem_univ a) (mem_univ b)

/-- **Field bounds from iterated-derivative bounds.** -/
theorem fieldBound_of_iteratedFDeriv {Y : R4 → V} (hY : ContDiff ℝ 3 Y) {B₁ B₂ B₃ : ℝ}
    (h1 : ∀ z, ‖iteratedFDeriv ℝ 1 Y z‖ ≤ B₁) (h2 : ∀ z, ‖iteratedFDeriv ℝ 2 Y z‖ ≤ B₂)
    (h3 : ∀ z, ‖iteratedFDeriv ℝ 3 Y z‖ ≤ B₃) : FieldBound Y B₁ B₂ B₃ where
  smooth := hY.of_le (by norm_num)
  b1 z := by rw [← norm_iteratedFDeriv_one]; exact h1 z
  lip1 := lipschitz_fderiv_of_iteratedFDeriv hY h2
  lip2 := lipschitz_fderiv_fderiv_of_iteratedFDeriv hY h3
  B₁_nonneg := (norm_nonneg _).trans (h1 0)
  B₂_nonneg := (norm_nonneg _).trans (h2 0)
  B₃_nonneg := (norm_nonneg _).trans (h3 0)

end IterBounds

/-! ### Uniform regularity packets from smoothness on compact sets -/

section UniformReg

variable {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]

/-- The insertion `q ↦ (θ, q)` of a parameter. -/
theorem hasFDerivAt_insert (θ : Θ) (q : ℝ × Jet ι V) :
    HasFDerivAt (fun q : ℝ × Jet ι V => ((θ, q) : Θ × (ℝ × Jet ι V)))
      (ContinuousLinearMap.inr ℝ Θ (ℝ × Jet ι V)) q := by
  have := ((ContinuousLinearMap.inr ℝ Θ (ℝ × Jet ι V)).hasFDerivAt (x := q)).const_add
    ((θ, 0) : Θ × (ℝ × Jet ι V))
  refine this.congr_of_eventuallyEq (Eventually.of_forall fun q' => ?_)
  simp

theorem norm_inr_le {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] : ‖ContinuousLinearMap.inr ℝ A B‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  simp [Prod.norm_def]

/-- **Uniform regularity packets.**  If a parameter family of jet densities `G(θ, h, ξ)` is `C³`
at every point `(θ, 0, c)` with `θ` in a compact parameter set `Λ` and `c` in a compact set `S`
of jets (finite-dimensional fibres), then there are `δ > 0` and `M₂, M₃` such that every member
`G(θ, ·)`, `θ ∈ Λ`, satisfies the regularity packet `DensityReg … S δ M₂ M₃`. -/
theorem exists_densityReg [FiniteDimensional ℝ Θ] [FiniteDimensional ℝ V]
    (G : Θ × (ℝ × Jet ι V) → ℝ) {Λ : Set Θ} (hΛ : IsCompact Λ) {S : Set (Jet ι V)}
    (hSc : IsCompact S) (hG : ∀ θ ∈ Λ, ∀ c ∈ S, ContDiffAt ℝ 3 G (θ, ((0 : ℝ), c))) :
    ∃ δ > 0, ∃ M₂ M₃ : ℝ, ∀ θ ∈ Λ, DensityReg (fun q => G (θ, q)) S δ M₂ M₃ := by
  set U := {p : Θ × (ℝ × Jet ι V) | ContDiffAt ℝ 3 G p} with hU
  have hUo : IsOpen U :=
    isOpen_iff_mem_nhds.mpr fun p hp => (show ContDiffAt ℝ 3 G p from hp).eventually (by simp)
  set K₀ := Λ ×ˢ (({(0 : ℝ)} : Set ℝ) ×ˢ S) with hK₀
  have hK₀c : IsCompact K₀ := hΛ.prod (isCompact_singleton.prod hSc)
  have hK₀U : K₀ ⊆ U := by
    rintro ⟨θ, h, c⟩ ⟨hθ, hh, hc⟩
    rw [mem_singleton_iff] at hh
    subst hh
    exact hG θ hθ c hc
  obtain ⟨δ, hδ, hδU⟩ := hK₀c.exists_cthickening_subset_open hUo hK₀U
  set K₁ := cthickening δ K₀
  have hK₁c : IsCompact K₁ := hK₀c.cthickening
  have hcont : ∀ k : ℕ, k ≤ 3 → ContinuousOn (iteratedFDeriv ℝ k G) U := by
    intro k hk
    have hcd : ContDiffOn ℝ 3 G U := fun p hp => (show ContDiffAt ℝ 3 G p from hp).contDiffWithinAt
    exact (hcd.continuousOn_iteratedFDerivWithin (by exact_mod_cast hk) hUo.uniqueDiffOn).congr
      (fun p hp => (iteratedFDerivWithin_of_isOpen k hUo hp).symm)
  obtain ⟨C₂, hC₂⟩ := hK₁c.exists_bound_of_continuousOn ((hcont 2 (by norm_num)).mono hδU)
  obtain ⟨C₃, hC₃⟩ := hK₁c.exists_bound_of_continuousOn ((hcont 3 (by norm_num)).mono hδU)
  refine ⟨δ, hδ, max C₂ 0, max C₃ 0, fun θ hθ => ?_⟩
  -- membership of `(θ, q)` in the compact neighbourhood
  have hmem : ∀ c ∈ S, ∀ q ∈ ball ((0 : ℝ), c) δ, ((θ, q) : Θ × (ℝ × Jet ι V)) ∈ K₁ := by
    intro c hc q hq
    refine mem_cthickening_of_dist_le _ (θ, ((0 : ℝ), c)) _ _ ⟨hθ, rfl, hc⟩ ?_
    rw [Prod.dist_eq, dist_self, mem_ball] at *
    exact max_le hδ.le hq.le
  have hU' : ∀ c ∈ S, ∀ q ∈ ball ((0 : ℝ), c) δ, ContDiffAt ℝ 3 G (θ, q) :=
    fun c hc q hq => hδU (hmem c hc q hq)
  -- the jet derivative of the slice
  set L : (Θ × (ℝ × Jet ι V) →L[ℝ] ℝ) →L[ℝ] (Jet ι V →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (Jet ι V) (Θ × (ℝ × Jet ι V)) ℝ).flip
      ((ContinuousLinearMap.inr ℝ Θ (ℝ × Jet ι V)).comp (ContinuousLinearMap.inr ℝ ℝ (Jet ι V)))
    with hL
  have hLn : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun T => ?_
    rw [one_mul]
    simp only [hL, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) ?_)
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    exact mul_le_one₀ norm_inr_le (norm_nonneg _) norm_inr_le
  have hslice : ∀ q, ContDiffAt ℝ 3 G (θ, q) →
      pJet (fun q => G (θ, q)) q = L (fderiv ℝ G (θ, q)) := by
    intro q hq
    unfold pJet
    have := ((hq.differentiableAt (by norm_num)).hasFDerivAt.comp q (hasFDerivAt_insert θ q)).fderiv
    rw [show (fun q => G (θ, q)) = G ∘ fun q => ((θ, q) : Θ × (ℝ × Jet ι V)) from rfl, this]
    rfl
  have hev : ∀ q, ContDiffAt ℝ 3 G (θ, q) →
      pJet (fun q => G (θ, q)) =ᶠ[𝓝 q] fun q' => L (fderiv ℝ G (θ, q')) := by
    intro q hq
    have hopen : IsOpen {q' : ℝ × Jet ι V | ((θ, q') : Θ × (ℝ × Jet ι V)) ∈ U} :=
      hUo.preimage (continuous_const.prodMk continuous_id)
    filter_upwards [hopen.mem_nhds hq] with q' hq'
    exact hslice q' hq'
  have hDG : ∀ q, ContDiffAt ℝ 3 G (θ, q) →
      HasFDerivAt (fun q' => fderiv ℝ G (θ, q'))
        ((fderiv ℝ (fderiv ℝ G) (θ, q)).comp (ContinuousLinearMap.inr ℝ Θ (ℝ × Jet ι V))) q := by
    intro q hq
    have h1 : DifferentiableAt ℝ (fderiv ℝ G) (θ, q) :=
      (hq.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
    exact h1.hasFDerivAt.comp q (hasFDerivAt_insert θ q)
  have hDP : ∀ q, ContDiffAt ℝ 3 G (θ, q) →
      HasFDerivAt (pJet (fun q => G (θ, q)))
        (L.comp ((fderiv ℝ (fderiv ℝ G) (θ, q)).comp
          (ContinuousLinearMap.inr ℝ Θ (ℝ × Jet ι V)))) q := by
    intro q hq
    exact (L.hasFDerivAt.comp q (hDG q hq)).congr_of_eventuallyEq (hev q hq)
  have hnormDP : ∀ q, ContDiffAt ℝ 3 G (θ, q) →
      ‖fderiv ℝ (pJet (fun q => G (θ, q))) q‖ ≤ ‖iteratedFDeriv ℝ 2 G (θ, q)‖ := by
    intro q hq
    rw [(hDP q hq).fderiv, ← norm_fderiv_fderiv_eq]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    refine (mul_le_of_le_one_left (norm_nonneg _) hLn).trans ?_
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    exact mul_le_of_le_one_right (norm_nonneg _) norm_inr_le
  refine ⟨fun c hc q hq => ?_, fun c hc q hq => (hDP q (hU' c hc q hq)).differentiableAt,
    fun c hc q hq => ?_, fun c hc q hq q' hq' => ?_, le_max_right _ _, le_max_right _ _⟩
  · exact ((hU' c hc q hq).differentiableAt (by norm_num)).comp q
      (hasFDerivAt_insert θ q).differentiableAt
  · exact (hnormDP q (hU' c hc q hq)).trans ((hC₂ _ (hmem c hc q hq)).trans (le_max_left _ _))
  · -- Lipschitz bound through the third iterated derivative
    rw [(hDP q (hU' c hc q hq)).fderiv, (hDP q' (hU' c hc q' hq')).fderiv, ← ContinuousLinearMap.comp_sub,
      ← ContinuousLinearMap.sub_comp]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    refine (mul_le_of_le_one_left (norm_nonneg _) hLn).trans ?_
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    refine (mul_le_of_le_one_right (norm_nonneg _) norm_inr_le).trans ?_
    refine (norm_fderiv_fderiv_sub_le G (θ, q') (θ, q)).trans ?_
    -- mean value along the slice
    have hd : ∀ t ∈ ball ((0 : ℝ), c) δ, HasFDerivAt (fun t => iteratedFDeriv ℝ 2 G (θ, t))
        ((fderiv ℝ (iteratedFDeriv ℝ 2 G) (θ, t)).comp (ContinuousLinearMap.inr ℝ Θ (ℝ × Jet ι V))) t := by
      intro t ht
      exact ((hU' c hc t ht).differentiableAt_iteratedFDeriv (by norm_num)).hasFDerivAt.comp t
        (hasFDerivAt_insert θ t)
    have hb : ∀ t ∈ ball ((0 : ℝ), c) δ,
        ‖(fderiv ℝ (iteratedFDeriv ℝ 2 G) (θ, t)).comp (ContinuousLinearMap.inr ℝ Θ (ℝ × Jet ι V))‖ ≤
          max C₃ 0 := by
      intro t ht
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      refine (mul_le_of_le_one_right (norm_nonneg _) norm_inr_le).trans ?_
      rw [norm_fderiv_iteratedFDeriv]
      exact (hC₃ _ (hmem c hc t ht)).trans (le_max_left _ _)
    exact (convex_ball ((0 : ℝ), c) δ).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun t ht => (hd t ht).hasFDerivWithinAt) hb hq' hq

end UniformReg

/-! ### Exact scaling of Euler rows -/

section Scaling

/-- Scaling of the raw Euler row under a constant multiple of the action. -/
theorem eulerRow_smul_action {A A' : (Grid n → V) → ℝ} {h ρ c : ℝ} (hA : ∀ y, A y = c * A' y)
    (y : Grid n → V) (x : Grid n) (hρ : ρ ≠ 0) (hh : h ≠ 0) :
    eulerRow A h y x = (c * ρ ^ 4 / h ^ 4) • eulerRow A' ρ y x := by
  have hfun : A = c • A' := funext fun y => by rw [hA, Pi.smul_apply, smul_eq_mul]
  unfold eulerRow
  by_cases hc : c = 0
  · subst hc
    have : A = fun _ => 0 := by rw [hfun, zero_smul]; rfl
    rw [this, fderiv_fun_const]
    simp
  · haveI := invertibleOfNonzero hc
    rw [hfun, fderiv_const_smul_of_invertible c, ContinuousLinearMap.smul_comp, smul_smul,
      smul_smul]
    congr 1
    field_simp

end Scaling


/-! ### Exact scaling of the continuum Euler expression -/

section ContScaling

variable (V) in
/-- The rescaling `(w, p) ↦ (w, c p)` of first jets. -/
def scaleP (c : ℝ) : V × (Fin 4 → V) →L[ℝ] V × (Fin 4 → V) :=
  (ContinuousLinearMap.fst ℝ V (Fin 4 → V)).prod (c • ContinuousLinearMap.snd ℝ V (Fin 4 → V))

theorem scaleP_apply (c : ℝ) (wp : V × (Fin 4 → V)) : scaleP V c wp = (wp.1, c • wp.2) := rfl

variable (V) in
/-- The rescaling as a continuous linear equivalence (`K ≠ 0`). -/
def scalePE {K : ℝ} (hK : K ≠ 0) : (V × (Fin 4 → V)) ≃L[ℝ] (V × (Fin 4 → V)) :=
  ContinuousLinearEquiv.equivOfInverse (scaleP V K⁻¹) (scaleP V K)
    (fun wp => by simp [scaleP_apply, smul_smul, mul_inv_cancel₀ hK])
    (fun wp => by simp [scaleP_apply, smul_smul, inv_mul_cancel₀ hK])

theorem scalePE_apply {K : ℝ} (hK : K ≠ 0) (wp : V × (Fin 4 → V)) :
    scalePE V hK wp = (wp.1, K⁻¹ • wp.2) := rfl

/-- **Scaling of the continuum Euler expression.**  If `L(w, p) = K² L'(w, K⁻¹ p)` and
`Y(z) = Ỹ(K z)`, then `E₀[L](Y)(z) = K² E₀[L'](Ỹ)(K z)` (no differentiability hypotheses: the
rescalings are linear equivalences). -/
theorem contEuler_scale {L L' : V × (Fin 4 → V) → ℝ} {K : ℝ} (hK : K ≠ 0)
    (hL : ∀ wp, L wp = K ^ 2 * L' (scalePE V hK wp)) (Yt : R4 → V) (z : R4) :
    contEuler L (fun z => Yt (K • z)) z = K ^ 2 • contEuler L' Yt (K • z) := by
  haveI : Invertible (K ^ 2) := invertibleOfNonzero (pow_ne_zero 2 hK)
  haveI : Invertible K := invertibleOfNonzero hK
  have hLf : L = (K ^ 2) • (L' ∘ scalePE V hK) := funext fun wp => by
    rw [hL, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
  have hfd : ∀ wp, fderiv ℝ L wp = K ^ 2 • (fderiv ℝ L' (scalePE V hK wp)).comp
      (scalePE V hK : V × (Fin 4 → V) →L[ℝ] V × (Fin 4 → V)) := fun wp => by
    rw [hLf, fderiv_const_smul_of_invertible, (scalePE V hK).comp_right_fderiv]
  have hY : ∀ z', fderiv ℝ (fun z => Yt (K • z)) z' = K • fderiv ℝ Yt (K • z') := fun z' =>
    fderiv_comp_smul (f := Yt) K
  have hjet : ∀ z', scalePE V hK (jet1 (fun z => Yt (K • z)) z') = jet1 Yt (K • z') := fun z' => by
    rw [scalePE_apply]
    simp only [jet1, hY, ContinuousLinearMap.smul_apply]
    congr 1
    funext μ
    simp [smul_smul, inv_mul_cancel₀ hK]
  have hinl : (scalePE V hK : V × (Fin 4 → V) →L[ℝ] V × (Fin 4 → V)).comp
      (ContinuousLinearMap.inl ℝ V (Fin 4 → V)) = ContinuousLinearMap.inl ℝ V (Fin 4 → V) := by
    ext w <;> simp [scalePE_apply]
  have hinr : ∀ μ, (scalePE V hK : V × (Fin 4 → V) →L[ℝ] V × (Fin 4 → V)).comp
      ((ContinuousLinearMap.inr ℝ V (Fin 4 → V)).comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => V) μ)) =
      K⁻¹ • ((ContinuousLinearMap.inr ℝ V (Fin 4 → V)).comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => V) μ)) := by
    intro μ
    ext w : 1
    simp [scalePE_apply]
  set Φ : Fin 4 → R4 → (V →L[ℝ] ℝ) := fun μ u => (fderiv ℝ L' (jet1 Yt u)).comp
    ((ContinuousLinearMap.inr ℝ V (Fin 4 → V)).comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => V) μ)) with hΦ
  have hterm : ∀ μ, (fun z' => (fderiv ℝ L (jet1 (fun z => Yt (K • z)) z')).comp
      ((ContinuousLinearMap.inr ℝ V (Fin 4 → V)).comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => V) μ))) =
      fun z' => K • Φ μ (K • z') := by
    intro μ
    funext z'
    rw [hfd, hjet, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_assoc, hinr,
      ContinuousLinearMap.comp_smul, smul_smul, hΦ]
    congr 1
    field_simp
  unfold contEuler
  simp only [hterm]
  rw [hfd, hjet, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_assoc, hinl, smul_sub,
    Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  have h1 : fderiv ℝ (fun z' => K • Φ μ (K • z')) z = K • (K • fderiv ℝ (Φ μ) (K • z)) := by
    rw [show (fun z' => K • Φ μ (K • z')) = K • (fun z' => Φ μ (K • z')) from rfl,
      fderiv_const_smul_of_invertible (𝕜 := ℝ) (f := fun z' => Φ μ (K • z')) K,
      fderiv_comp_smul (f := Φ μ) K]
  rw [h1]
  simp only [ContinuousLinearMap.smul_apply, smul_smul, sq]
  rfl

end ContScaling


/-! ### Rescaled fields -/

section Rescale

variable {Y : R4 → V}

theorem fderiv_rescale (K : ℝ) (z : R4) :
    fderiv ℝ (fun z => Y (K⁻¹ • z)) z = K⁻¹ • fderiv ℝ Y (K⁻¹ • z) :=
  fderiv_comp_smul (f := Y) K⁻¹

/-- **Amplitude-preserving rescaling of a growing-band field**: if `‖DY‖ ≤ BK`, `DY` is
`BK²`-Lipschitz and `D²Y` is `BK³`-Lipschitz, then `Ỹ(ξ) = Y(ξ/K)` has the `K`-independent
bounds `FieldBound Ỹ B B B` (no field amplitude is divided by `K`). -/
theorem FieldBound.rescale {B K : ℝ} (hY : FieldBound Y (B * K) (B * K ^ 2) (B * K ^ 3))
    (hK : 0 < K) (hB : 0 ≤ B) : FieldBound (fun z => Y (K⁻¹ • z)) B B B := by
  haveI : Invertible K⁻¹ := invertibleOfNonzero (inv_ne_zero hK.ne')
  have h1 : fderiv ℝ (fun z => Y (K⁻¹ • z)) = fun z => K⁻¹ • fderiv ℝ Y (K⁻¹ • z) :=
    funext (fderiv_rescale K)
  have h2 : ∀ z, fderiv ℝ (fderiv ℝ (fun z => Y (K⁻¹ • z))) z =
      K⁻¹ • (K⁻¹ • fderiv ℝ (fderiv ℝ Y) (K⁻¹ • z)) := by
    intro z
    rw [h1, show (fun z => K⁻¹ • fderiv ℝ Y (K⁻¹ • z)) = K⁻¹ • (fun z => fderiv ℝ Y (K⁻¹ • z))
      from rfl, fderiv_const_smul_of_invertible (𝕜 := ℝ) (f := fun z => fderiv ℝ Y (K⁻¹ • z)) K⁻¹,
      fderiv_comp_smul (f := fderiv ℝ Y) K⁻¹]
  have hKi : 0 < K⁻¹ := inv_pos.mpr hK
  have hsc : ∀ a b : R4, ‖K⁻¹ • b - K⁻¹ • a‖ = K⁻¹ * ‖b - a‖ := fun a b => by
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg hKi.le]
  refine ⟨hY.smooth.comp (contDiff_const_smul K⁻¹), fun z => ?_, fun a b => ?_, fun a b => ?_,
    hB, hB, hB⟩
  · rw [fderiv_rescale, norm_smul, Real.norm_of_nonneg hKi.le]
    calc K⁻¹ * ‖fderiv ℝ Y (K⁻¹ • z)‖ ≤ K⁻¹ * (B * K) := by gcongr; exact hY.b1 _
      _ = B := by field_simp
  · rw [fderiv_rescale, fderiv_rescale]
    have e : ‖K⁻¹ • fderiv ℝ Y (K⁻¹ • b) - K⁻¹ • fderiv ℝ Y (K⁻¹ • a)‖ =
        K⁻¹ * ‖fderiv ℝ Y (K⁻¹ • b) - fderiv ℝ Y (K⁻¹ • a)‖ := by
      rw [← norm_smul_of_nonneg hKi.le]; congr 1; module
    rw [e]
    calc K⁻¹ * ‖fderiv ℝ Y (K⁻¹ • b) - fderiv ℝ Y (K⁻¹ • a)‖
        ≤ K⁻¹ * (B * K ^ 2 * ‖K⁻¹ • b - K⁻¹ • a‖) := by gcongr; exact hY.lip1 _ _
      _ = B * ‖b - a‖ := by rw [hsc]; field_simp
  · rw [h2, h2]
    set X := fderiv ℝ (fderiv ℝ Y) (K⁻¹ • b)
    set X' := fderiv ℝ (fderiv ℝ Y) (K⁻¹ • a)
    have e : ‖K⁻¹ • K⁻¹ • X - K⁻¹ • K⁻¹ • X'‖ ≤ K⁻¹ * (K⁻¹ * ‖X - X'‖) := by
      rw [show K⁻¹ • K⁻¹ • X - K⁻¹ • K⁻¹ • X' = K⁻¹ • (K⁻¹ • (X - X')) by module]
      refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
      rw [Real.norm_of_nonneg hKi.le]
      gcongr
      refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
      rw [Real.norm_of_nonneg hKi.le]
    refine e.trans ?_
    calc K⁻¹ * (K⁻¹ * ‖X - X'‖)
        ≤ K⁻¹ * (K⁻¹ * (B * K ^ 3 * ‖K⁻¹ • b - K⁻¹ • a‖)) := by gcongr; exact hY.lip2 _ _
      _ = B * ‖b - a‖ := by rw [hsc]; field_simp

theorem IsPeriodic.rescale {L K : ℝ} (hY : IsPeriodic L Y) (hK : K ≠ 0) :
    IsPeriodic (K * L) (fun z => Y (K⁻¹ • z)) := by
  intro z μ
  have e : K⁻¹ • (z + Pi.single μ (K * L)) = K⁻¹ • z + Pi.single μ L := by
    rw [smul_add]
    congr 1
    funext ν
    by_cases h : ν = μ
    · subst h; simp; field_simp
    · simp [Pi.single_apply, h]
  simp only [e, hY _ μ]

theorem pos_mul (h K : ℝ) (x : Grid n) : pos (h * K) x = K • pos h x := by
  funext μ
  simp only [pos, Pi.smul_apply, smul_eq_mul]
  ring

theorem samp_rescale {h K : ℝ} (hK : K ≠ 0) :
    samp (h * K) (fun z => Y (K⁻¹ • z)) = (samp h Y : Grid n → V) := by
  funext x
  simp only [samp, pos_mul, smul_smul, inv_mul_cancel₀ hK, one_smul]

end Rescale


/-! ### Consistency of composite stencil quantities -/

section MapReg

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **Regularity of a jet map near the continuum jets**: on the balls of radius `δ` around the
points `(0, c)`, `c ∈ S`, the map `P(h, ξ)` is differentiable with `‖DP‖ ≤ M₂` and `DP` is
`M₃`-Lipschitz. -/
structure MapReg (P : ℝ × Jet ι V → W) (S : Set (Jet ι V)) (δ M₂ M₃ : ℝ) : Prop where
  diff : ∀ c ∈ S, ∀ q ∈ ball ((0 : ℝ), c) δ, DifferentiableAt ℝ P q
  bound : ∀ c ∈ S, ∀ q ∈ ball ((0 : ℝ), c) δ, ‖fderiv ℝ P q‖ ≤ M₂
  lip : ∀ c ∈ S, ∀ q ∈ ball ((0 : ℝ), c) δ, ∀ q' ∈ ball ((0 : ℝ), c) δ,
    ‖fderiv ℝ P q - fderiv ℝ P q'‖ ≤ M₃ * ‖q - q'‖
  M₂_nonneg : 0 ≤ M₂
  M₃_nonneg : 0 ≤ M₃

variable {P : ℝ × Jet ι V → W} {S : Set (Jet ι V)} {δ M₂ M₃ : ℝ} {Y : R4 → V}
  {B₁ B₂ B₃ : ℝ} {σZ : ι → Fin 4 → ℤ} {s : ℝ}

/-- Value consistency: `‖P(h, Ξ_h(a)) - P(0, J¹Y(z))‖ ≤ M₂ (1 + c₁) h`. -/
theorem MapReg.norm_value_sub_le (hP : MapReg P S δ M₂ M₃) (hY : FieldBound Y B₁ B₂ B₃)
    (hS : ∀ z, cmap (jet1 Y z) ∈ S) (hs0 : 0 ≤ s) (hs : ∀ i μ, |(σZ i μ : ℝ)| ≤ s) {h : ℝ}
    (hh : 0 < h) (hδ : h * (1 + cJet B₁ B₂ s) < δ) {a z : R4} (ha : ‖a - z‖ ≤ h * (s + 1)) :
    ‖P (h, discJet σZ h Y a) - P (0, cmap (jet1 Y z))‖ ≤ M₂ * (h * (1 + cJet B₁ B₂ s)) := by
  have hδ0 : 0 < δ := lt_of_le_of_lt (by
    have : 0 ≤ cJet B₁ B₂ s := by unfold cJet; have := hY.B₁_nonneg; have := hY.B₂_nonneg; positivity
    positivity) hδ
  obtain ⟨hm, hd⟩ := discJet_mem_ball (ι := ι) hY hh hs0 hs hδ ha (σZ := σZ)
  have := (convex_ball ((0 : ℝ), (cmap (jet1 Y z) : Jet ι V)) δ).norm_image_sub_le_of_norm_fderiv_le
    (fun q hq => hP.diff _ (hS z) q hq) (fun q hq => hP.bound _ (hS z) q hq)
    (mem_ball_self hδ0) hm
  exact this.trans (mul_le_mul_of_nonneg_left hd hP.M₂_nonneg)

/-- **Divided-difference consistency of a composite stencil quantity**: for base points
`a, a' = a - h e_μ` within `(s + 1) h` of `z`,
`‖h⁻¹(P(h, Ξ_h(a')) - P(h, Ξ_h(a))) + DP(0, J z)[(0, DJ(z) e_μ)]‖ ≤ C h`; equivalently the forward
difference of `P(h, Ξ_h(·))` is `O(h)`-close to the `μ`-derivative of `P(0, J¹Y(·))`. -/
theorem MapReg.norm_divDiff_sub_le (hP : MapReg P S δ M₂ M₃) (hY : FieldBound Y B₁ B₂ B₃)
    (hS : ∀ z, cmap (jet1 Y z) ∈ S) (hs0 : 0 ≤ s) (hs : ∀ i μ, |(σZ i μ : ℝ)| ≤ s) {h : ℝ}
    (hh : 0 < h) (hδ : h * (1 + cJet B₁ B₂ s) < δ) {a a' z : R4} (μ : Fin 4)
    (ha : ‖a - z‖ ≤ h * (s + 1)) (ha' : ‖a' - z‖ ≤ h * (s + 1)) (hseg : a - a' = h • evec μ) :
    ‖h⁻¹ • (P (h, discJet σZ h Y a') - P (h, discJet σZ h Y a)) +
        (fderiv ℝ P (0, cmap (jet1 Y z))) (0, dJet Y z (evec μ))‖ ≤
      h * (M₃ * (1 + cJet B₁ B₂ s) * (B₁ + B₂) + M₂ * cJet' B₂ B₃ s) := by
  set C₁ := cJet B₁ B₂ s
  set C₂ := cJet' B₂ B₃ s
  set J : Jet ι V := cmap (jet1 Y z)
  have hc1 : 0 ≤ C₁ := by unfold C₁ cJet; have := hY.B₁_nonneg; have := hY.B₂_nonneg; positivity
  have hδ0 : 0 < δ := lt_of_le_of_lt (by positivity) hδ
  have hJmem : ((0 : ℝ), J) ∈ ball ((0 : ℝ), J) δ := mem_ball_self hδ0
  set φ : R4 →L[ℝ] W :=
    (fderiv ℝ P (0, J)).comp ((ContinuousLinearMap.inr ℝ ℝ (Jet ι V)).comp (dJet Y z)) with hφ
  set g : R4 → W := fun b => P (h, discJet σZ h Y b) with hg
  have hsegball : segment ℝ a' a ⊆ closedBall z (h * (s + 1)) :=
    (convex_closedBall z _).segment_subset (by rw [mem_closedBall, dist_eq_norm]; exact ha')
      (by rw [mem_closedBall, dist_eq_norm]; exact ha)
  have hgd : ∀ b ∈ segment ℝ a' a, HasFDerivAt g
      ((fderiv ℝ P (h, discJet σZ h Y b)).comp
        ((ContinuousLinearMap.inr ℝ ℝ (Jet ι V)).comp (dDisc σZ h Y b))) b := by
    intro b hb
    have hb' : ‖b - z‖ ≤ h * (s + 1) := by
      have := hsegball hb; rwa [mem_closedBall, dist_eq_norm] at this
    have hin : HasFDerivAt (fun b => ((h, discJet σZ h Y b) : ℝ × Jet ι V))
        ((ContinuousLinearMap.inr ℝ ℝ (Jet ι V)).comp (dDisc σZ h Y b)) b := by
      have := (((ContinuousLinearMap.inr ℝ ℝ (Jet ι V)).hasFDerivAt
        (x := discJet σZ h Y b)).comp b (hasFDerivAt_discJet (σZ := σZ) hY h b)).const_add
        ((h, 0) : ℝ × Jet ι V)
      refine this.congr_of_eventuallyEq (Eventually.of_forall fun b' => ?_)
      simp
    exact (hP.diff _ (hS z) _ (discJet_mem_ball hY hh hs0 hs hδ hb').1).hasFDerivAt.comp b hin
  have hgb : ∀ b ∈ segment ℝ a' a, ‖fderiv ℝ g b - φ‖ ≤ h * (M₃ * (1 + C₁) * (B₁ + B₂) + M₂ * C₂) := by
    intro b hb
    have hb' : ‖b - z‖ ≤ h * (s + 1) := by
      have := hsegball hb; rwa [mem_closedBall, dist_eq_norm] at this
    obtain ⟨hm, hd⟩ := discJet_mem_ball hY hh hs0 hs hδ hb'
    rw [(hgd b hb).fderiv, hφ]
    set A := fderiv ℝ P (h, discJet σZ h Y b)
    set A₀ := fderiv ℝ P (0, J)
    set D := dDisc σZ h Y b
    set D₀ := (dJet Y z : R4 →L[ℝ] Jet ι V)
    set ιr := ContinuousLinearMap.inr ℝ ℝ (Jet ι V)
    have hιr : ‖ιr‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
      simp [ιr, Prod.norm_def]
    have e : A.comp (ιr.comp D) - A₀.comp (ιr.comp D₀) =
        (A - A₀).comp (ιr.comp D) + A₀.comp (ιr.comp (D - D₀)) := by
      simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]; abel
    rw [e]
    have hAA : ‖A - A₀‖ ≤ M₃ * (h * (1 + C₁)) :=
      (hP.lip _ (hS z) _ hm _ hJmem).trans (mul_le_mul_of_nonneg_left hd hP.M₃_nonneg)
    have hDD : ‖D - D₀‖ ≤ h * C₂ := norm_dDisc_sub_le hY hh hs0 hs hb'
    have hD : ‖D‖ ≤ B₁ + B₂ := norm_dDisc_le hY hh b
    have hA₀ : ‖A₀‖ ≤ M₂ := hP.bound _ (hS z) _ hJmem
    calc ‖(A - A₀).comp (ιr.comp D) + A₀.comp (ιr.comp (D - D₀))‖
        ≤ ‖A - A₀‖ * (‖ιr‖ * ‖D‖) + ‖A₀‖ * (‖ιr‖ * ‖D - D₀‖) := by
          refine (norm_add_le ((A - A₀).comp (ιr.comp D)) (A₀.comp (ιr.comp (D - D₀)))).trans
            (add_le_add ?_ ?_)
          · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
              (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
                (norm_nonneg (A - A₀)))
          · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
              (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
                (norm_nonneg A₀))
      _ ≤ (M₃ * (h * (1 + C₁))) * (1 * (B₁ + B₂)) + M₂ * (1 * (h * C₂)) := by
          have hDn := norm_nonneg D
          have hDDn := norm_nonneg (D - D₀)
          have hm3 : 0 ≤ M₃ * (h * (1 + C₁)) := by have := hP.M₃_nonneg; positivity
          exact add_le_add
            (mul_le_mul hAA (mul_le_mul hιr hD hDn zero_le_one) (by positivity) hm3)
            (mul_le_mul hA₀ (mul_le_mul hιr hDD hDDn zero_le_one) (by positivity) hP.M₂_nonneg)
      _ = h * (M₃ * (1 + C₁) * (B₁ + B₂) + M₂ * C₂) := by ring
  have hmv := (convex_segment a' a).norm_image_sub_le_of_norm_fderiv_le'
    (f := g) (φ := φ) (fun b hb => (hgd b hb).differentiableAt) hgb
    (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
  rw [hseg, norm_smul, norm_evec, Real.norm_eq_abs, abs_of_pos hh, mul_one] at hmv
  have e : h⁻¹ • (P (h, discJet σZ h Y a') - P (h, discJet σZ h Y a)) +
      (fderiv ℝ P (0, J)) (0, dJet Y z (evec μ)) = -(h⁻¹ • (g a - g a' - φ (h • evec μ))) := by
    rw [map_smul, hg, hφ]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, smul_sub, smul_smul,
      inv_mul_cancel₀ hh.ne', one_smul, neg_sub]
    abel
  rw [e, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh)]
  calc h⁻¹ * ‖g a - g a' - φ (h • evec μ)‖
      ≤ h⁻¹ * (h * (M₃ * (1 + C₁) * (B₁ + B₂) + M₂ * C₂) * h) := by gcongr
    _ = h * (M₃ * (1 + C₁) * (B₁ + B₂) + M₂ * C₂) := by field_simp

/-- The `μ`-derivative of `P(0, J¹Y(·))`. -/
theorem MapReg.hasFDerivAt_comp_jet (hP : MapReg P S δ M₂ M₃) (hδ0 : 0 < δ)
    (hY : FieldBound Y B₁ B₂ B₃) (hS : ∀ z, cmap (jet1 Y z) ∈ S) (z : R4) :
    HasFDerivAt (fun z => P (0, (cmap (jet1 Y z) : Jet ι V)))
      ((fderiv ℝ P (0, cmap (jet1 Y z))).comp
        ((ContinuousLinearMap.inr ℝ ℝ (Jet ι V)).comp (dJet Y z))) z := by
  have hin : HasFDerivAt (fun z => ((0 : ℝ), (cmap (jet1 Y z) : Jet ι V)))
      ((ContinuousLinearMap.inr ℝ ℝ (Jet ι V)).comp (dJet Y z)) z :=
    ((ContinuousLinearMap.inr ℝ ℝ (Jet ι V)).hasFDerivAt (x := cmap (jet1 Y z))).comp z
      (hasFDerivAt_jet (ι := ι) hY z)
  exact (hP.diff _ (hS z) _ (mem_ball_self hδ0)).hasFDerivAt.comp z hin

end MapReg

/-! ### Uniform `C²` bounds near a compact set -/

/-- If `f` is `C²` at every point of a compact set `K` of a finite-dimensional space, then there
are `δ > 0` and `M₂, M₃ ≥ 0` such that on every ball `B(c, δ)`, `c ∈ K`, `f` is differentiable,
`‖Df‖ ≤ M₂` and `Df` is `M₃`-Lipschitz. -/
theorem exists_C2_ball_bounds {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W] {f : E → W} {K : Set E}
    (hK : IsCompact K) (hf : ∀ c ∈ K, ContDiffAt ℝ 2 f c) :
    ∃ δ > 0, ∃ M₂ M₃ : ℝ, 0 ≤ M₂ ∧ 0 ≤ M₃ ∧ ∀ c ∈ K, ∀ q ∈ ball c δ,
      DifferentiableAt ℝ f q ∧ ‖fderiv ℝ f q‖ ≤ M₂ ∧
        ∀ q' ∈ ball c δ, ‖fderiv ℝ f q - fderiv ℝ f q'‖ ≤ M₃ * ‖q - q'‖ := by
  set U := {p : E | ContDiffAt ℝ 2 f p} with hU
  have hUo : IsOpen U :=
    isOpen_iff_mem_nhds.mpr fun p hp => (show ContDiffAt ℝ 2 f p from hp).eventually (by simp)
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hUo hf
  have hK₁c : IsCompact (cthickening δ K) := hK.cthickening
  have hcont : ∀ k : ℕ, k ≤ 2 → ContinuousOn (iteratedFDeriv ℝ k f) U := by
    intro k hk
    have hcd : ContDiffOn ℝ 2 f U := fun p hp => (show ContDiffAt ℝ 2 f p from hp).contDiffWithinAt
    exact (hcd.continuousOn_iteratedFDerivWithin (by exact_mod_cast hk) hUo.uniqueDiffOn).congr
      (fun p hp => (iteratedFDerivWithin_of_isOpen k hUo hp).symm)
  obtain ⟨C₁, hC₁⟩ := hK₁c.exists_bound_of_continuousOn ((hcont 1 (by norm_num)).mono hδU)
  obtain ⟨C₂, hC₂⟩ := hK₁c.exists_bound_of_continuousOn ((hcont 2 (by norm_num)).mono hδU)
  have hmem : ∀ c ∈ K, ∀ q ∈ ball c δ, q ∈ cthickening δ K := fun c hc q hq =>
    mem_cthickening_of_dist_le q c δ K hc (le_of_lt (mem_ball.mp hq))
  refine ⟨δ, hδ, max C₁ 0, max C₂ 0, le_max_right _ _, le_max_right _ _, fun c hc q hq => ?_⟩
  have hU' : ∀ q ∈ ball c δ, ContDiffAt ℝ 2 f q := fun q hq => hδU (hmem c hc q hq)
  refine ⟨(hU' q hq).differentiableAt (by norm_num), ?_, fun q' hq' => ?_⟩
  · rw [← norm_iteratedFDeriv_one]
    exact (hC₁ _ (hmem c hc q hq)).trans (le_max_left _ _)
  · have hd : ∀ t ∈ ball c δ, DifferentiableAt ℝ (fderiv ℝ f) t := fun t ht =>
      ((hU' t ht).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hb : ∀ t ∈ ball c δ, ‖fderiv ℝ (fderiv ℝ f) t‖ ≤ max C₂ 0 := fun t ht => by
      rw [norm_fderiv_fderiv_eq]
      exact (hC₂ t (hmem c hc t ht)).trans (le_max_left C₂ 0)
    exact (convex_ball c δ).norm_image_sub_le_of_norm_fderiv_le (f := fderiv ℝ f) hd hb hq' hq

end

end RenewalGeometry.DiscreteEulerConsistency
