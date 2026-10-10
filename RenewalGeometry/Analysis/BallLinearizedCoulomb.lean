/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallNeumannLaplacian
import RenewalGeometry.Analysis.CovariantGradientCompactness

/-!
# Critical Sobolev on `H¹(B)` and the linearised Coulomb operator on a ball
  (stage C5, weak form, of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `sobolev_H1B` (**critical Sobolev on `H¹(B)`**, `n ≥ 3`): the `C¹` inequality `sobolev_ball`
  passes to the closure `H¹(B)` by lower semicontinuity of the `L^{p'}` norm under `L²`
  convergence (Fatou along an a.e. convergent subsequence); `sobCLM`: the embedding
  `H¹₀(B) → L⁴(B)` (`n = 4`) as a continuous linear map.
* `mulCLM`: multiplication by `a ∈ L⁴(B)`, `L⁴(B) → L²(B)` (Hölder).
* `XiB c r N` (`N`-component mean-zero `H¹(B)` fields), the Dirichlet form `dirFormN`, the
  coupling `couplingN` (`p(ξ,η) = Σ ⟨a_ν^{kl} ξ_l, ∂_ν η_k⟩`) and
  `linearized_neumann_ball` (**the linearised Coulomb operator `ξ ↦ d^*(dξ + [a,ξ])` with the
  natural Neumann condition**): for `Σ‖a_ν^{kl}‖_{L⁴(B)} ≤ δ` and every continuous load `ℓ`
  there is a unique mean-zero solution of the weak problem
  `Σ_{k,ν} ⟨∂_νξ_k + Σ_l a_ν^{kl} ξ_l, ∂_ν η_k⟩ = ℓ(η)` (Lax–Milgram for a small perturbation of
  the coercive Dirichlet form).  For a Lie-algebra valued gauge parameter, `a_ν^{kl}` is the
  matrix of `ad a_ν` in a real basis of the Lie algebra.

Higher regularity (`H^{s+1}` bounds for `H^s` data, the Banach algebra `H^s(B)`) is **not**
proved here.
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

namespace RenewalGeometry.BallAnalysis

open SobolevOpen

set_option linter.unusedSectionVars false

variable {n : ℕ} [NeZero n]

/-! ### The critical Sobolev inequality on `H¹(B)` -/

theorem ofReal_norm_L2B {c : Fin n → ℝ} {r : ℝ} (g : L2B c r) :
    ENNReal.ofReal ‖g‖ = eLpNorm g 2 (volume.restrict (euclBall c r)) := by
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]

/-- Real version of `sobolev_ball`. -/
theorem sobolev_ball_real (hn : 2 < n) {p' : ℝ≥0} (hp' : (p' : ℝ)⁻¹ = (2 : ℝ)⁻¹ - (n : ℝ)⁻¹) :
    ∃ C : ℝ≥0, ∀ (c : Fin n → ℝ) (r : ℝ), 0 < r → ∀ u : (Fin n → ℝ) → ℝ, ContDiff ℝ 1 u →
      eLpNorm u p' (volume.restrict (euclBall c r)) ≤
        C * (∑ i, eLpNorm (pd u i) 2 (volume.restrict (euclBall c r)) +
          ENNReal.ofReal r⁻¹ * eLpNorm u 2 (volume.restrict (euclBall c r))) := by
  obtain ⟨C, hC⟩ := sobolev_ball hn hp'
  refine ⟨C, fun c r hr u hu => ?_⟩
  have hu' : ContDiff ℝ 1 (fun y => ((u y : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hu
  have h := hC c r hr _ hu'
  have e : ∀ (q : ℝ≥0∞) (g : (Fin n → ℝ) → ℝ), eLpNorm (fun y => ((g y : ℝ) : ℂ)) q
      (volume.restrict (euclBall c r)) = eLpNorm g q (volume.restrict (euclBall c r)) :=
    fun q g => eLpNorm_congr_norm_ae (Eventually.of_forall fun y => by simp)
  have hpd : ∀ i, pd (fun y => ((u y : ℝ) : ℂ)) i = fun x => ((pd u i x : ℝ) : ℂ) :=
    fun i => funext (pd_ofReal hu i)
  simp only [hpd, e] at h
  exact h

variable (c : Fin n → ℝ) (r : ℝ) [hr : Fact (0 < r)]

/-- **Critical Sobolev inequality on `H¹(B)`** (`n ≥ 3`, `1/p' = 1/2 - 1/n`): every element of
`H¹(B)` has its function component in `L^{p'}(B)` with
`‖x₀‖_{L^{p'}(B)} ≤ C (Σ_i ‖x_i‖_{L²(B)} + r⁻¹ ‖x₀‖_{L²(B)})`, `C` independent of the ball (by
lower semicontinuity of the `L^{p'}` norm under `L²` convergence, from the `C¹` case). -/
theorem sobolev_H1B (hn : 2 < n) {p' : ℝ≥0} (hp' : (p' : ℝ)⁻¹ = (2 : ℝ)⁻¹ - (n : ℝ)⁻¹) :
    ∃ C : ℝ≥0, ∀ (c : Fin n → ℝ) (r : ℝ) [Fact (0 < r)], ∀ x ∈ H1B c r,
      eLpNorm (x none : L2B c r) p' (volume.restrict (euclBall c r)) ≤
        C * (∑ i, ENNReal.ofReal ‖x (some i)‖ + ENNReal.ofReal r⁻¹ * ENNReal.ofReal ‖x none‖) := by
  obtain ⟨C, hC⟩ := sobolev_ball_real hn hp'
  refine ⟨C, fun c r _ => ?_⟩
  have hr' : (0 : ℝ) < r := Fact.out
  set R : H1Amb c r → ℝ≥0∞ := fun x =>
    C * (∑ i, ENNReal.ofReal ‖x (some i)‖ + ENNReal.ofReal r⁻¹ * ENNReal.ofReal ‖x none‖)
  have hRc : Continuous R := by
    refine ENNReal.continuous_const_mul ENNReal.coe_ne_top |>.comp ?_
    refine (continuous_finset_sum _ fun i _ => ENNReal.continuous_ofReal.comp
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin n) => L2B c r) (some i)).continuous.norm)).add
      ?_
    exact (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp
      (ENNReal.continuous_ofReal.comp
        ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin n) => L2B c r) none).continuous.norm))
  refine H1B_induction c r ?_ fun u => ?_
  · -- closedness by Fatou along an a.e. convergent subsequence
    refine IsSeqClosed.isClosed fun xs x hxs hlim => ?_
    have hg : Tendsto (fun k => (xs k) none) atTop (𝓝 (x none)) :=
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin n) => L2B c r) none).continuous.tendsto x).comp
        hlim
    have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at hg
    have hmeas := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num)
      (fun k => (Lp.aestronglyMeasurable ((xs k) none))) (Lp.aestronglyMeasurable (x none)) hg
    obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
    show _ ≤ R x
    refine (Lp.eLpNorm_lim_le_liminf_eLpNorm (fun k => Lp.aestronglyMeasurable ((xs (ns k)) none))
      _ hae).trans ?_
    have hR : Tendsto (fun k => R (xs (ns k))) atTop (𝓝 (R x)) :=
      (hRc.tendsto x).comp (hlim.comp hns.tendsto_atTop)
    rw [← hR.liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall fun k => hxs (ns k))
  · have hu := u.2
    show eLpNorm ((graphC1 c r u none : L2B c r) : (Fin n → ℝ) → ℝ) p'
        (volume.restrict (euclBall c r)) ≤ R (graphC1 c r u)
    simp only [R, ofReal_norm_L2B, graphC1_none, graphC1_some]
    rw [eLpNorm_congr_ae (memLp_ball_of_C1 c r hu).coeFn_toLp]
    simp only [eLpNorm_congr_ae (MemLp.coeFn_toLp _)]
    exact hC c r hr' _ hu


/-! ### The linearised Coulomb operator with the natural Neumann condition (`n = 4`) -/

section Linearized

variable (c : Fin 4 → ℝ) (r : ℝ) [hr : Fact (0 < r)]

/-- `L⁴(B)`. -/
abbrev L4B := Lp ℝ 4 (volume.restrict (euclBall c r))

theorem sobolev_H1B_four : ∃ C : ℝ≥0, ∀ (c : Fin 4 → ℝ) (r : ℝ) [Fact (0 < r)], ∀ x ∈ H1B c r,
    eLpNorm (x none : L2B c r) 4 (volume.restrict (euclBall c r)) ≤
      C * (∑ i, ENNReal.ofReal ‖x (some i)‖ + ENNReal.ofReal r⁻¹ * ENNReal.ofReal ‖x none‖) := by
  obtain ⟨C, hC⟩ := sobolev_H1B (n := 4) (by norm_num) (p' := 4) (by norm_num)
  exact ⟨C, fun c r _ x hx => by simpa using hC c r x hx⟩

/-- The constant of `sobolev_H1B_four`. -/
def sobC : ℝ≥0 := sobolev_H1B_four.choose

theorem sobC_spec (x : H1Amb c r) (hx : x ∈ H1B c r) :
    eLpNorm (x none : L2B c r) 4 (volume.restrict (euclBall c r)) ≤
      sobC * (∑ i, ENNReal.ofReal ‖x (some i)‖ + ENNReal.ofReal r⁻¹ * ENNReal.ofReal ‖x none‖) :=
  sobolev_H1B_four.choose_spec c r x hx

theorem memLp_four_H1B (x : H1B0 c r) :
    MemLp ((x : H1Amb c r) none : L2B c r) 4 (volume.restrict (euclBall c r)) := by
  refine ⟨Lp.aestronglyMeasurable _, (sobC_spec c r _ x.2.1).trans_lt ?_⟩
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.add_lt_top.mpr ⟨ENNReal.sum_lt_top.mpr
    fun i _ => ENNReal.ofReal_lt_top, ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      ENNReal.ofReal_lt_top⟩)

/-- The Sobolev embedding `H¹₀(B) → L⁴(B)`, `x ↦ x₀`, as a bounded linear map. -/
def sobLin : H1B0 c r →ₗ[ℝ] L4B c r where
  toFun x := (memLp_four_H1B c r x).toLp _
  map_add' x y := by
    rw [← MemLp.toLp_add]
    refine (MemLp.toLp_eq_toLp_iff _ _).mpr ?_
    show (((x + y : H1B0 c r) : H1Amb c r) none : L2B c r) =ᵐ[_] _
    have : ((x + y : H1B0 c r) : H1Amb c r) none =
        ((x : H1Amb c r) none) + ((y : H1Amb c r) none) := rfl
    rw [this]
    exact Lp.coeFn_add _ _
  map_smul' a x := by
    rw [← MemLp.toLp_const_smul]
    refine (MemLp.toLp_eq_toLp_iff _ _).mpr ?_
    have : ((a • x : H1B0 c r) : H1Amb c r) none = a • ((x : H1Amb c r) none) := rfl
    show (((a • x : H1B0 c r) : H1Amb c r) none : L2B c r) =ᵐ[_] _
    rw [this]
    exact Lp.coeFn_smul _ _

/-- The constant of the embedding `H¹(B) → L⁴(B)` (depends on `r` through `r⁻¹`). -/
def sobK : ℝ := (sobC : ℝ) * (4 + r⁻¹)

theorem norm_sobLin_le (x : H1B0 c r) : ‖sobLin c r x‖ ≤ sobK r * ‖x‖ := by
  have hx := sobC_spec c r _ x.2.1
  have hr0 : 0 < r := hr.out
  rw [Lp.norm_def, show sobLin c r x = (memLp_four_H1B c r x).toLp _ from rfl,
    eLpNorm_congr_ae (MemLp.coeFn_toLp _)]
  have hle : ∀ k, ‖(x : H1Amb c r) k‖ ≤ ‖x‖ := fun k => PiLp.norm_apply_le (x : H1Amb c r) k
  have hsum : ∑ i, ENNReal.ofReal ‖(x : H1Amb c r) (some i)‖ +
      ENNReal.ofReal r⁻¹ * ENNReal.ofReal ‖(x : H1Amb c r) none‖ ≤
      ENNReal.ofReal ((4 + r⁻¹) * ‖x‖) := by
    calc ∑ i, ENNReal.ofReal ‖(x : H1Amb c r) (some i)‖ +
          ENNReal.ofReal r⁻¹ * ENNReal.ofReal ‖(x : H1Amb c r) none‖
        ≤ ∑ _i : Fin 4, ENNReal.ofReal ‖x‖ + ENNReal.ofReal r⁻¹ * ENNReal.ofReal ‖x‖ := by
          gcongr with i
          · exact hle _
          · exact hle _
      _ = ENNReal.ofReal ((4 + r⁻¹) * ‖x‖) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
              (by positivity)]
          congr 1; push_cast; ring
  have hb : sobC * (∑ i, ENNReal.ofReal ‖(x : H1Amb c r) (some i)‖ +
      ENNReal.ofReal r⁻¹ * ENNReal.ofReal ‖(x : H1Amb c r) none‖) ≤
      ENNReal.ofReal (sobK r * ‖x‖) := by
    calc (sobC : ℝ≥0∞) * (∑ i, ENNReal.ofReal ‖(x : H1Amb c r) (some i)‖ +
          ENNReal.ofReal r⁻¹ * ENNReal.ofReal ‖(x : H1Amb c r) none‖)
        ≤ (sobC : ℝ≥0∞) * ENNReal.ofReal ((4 + r⁻¹) * ‖x‖) := by gcongr
      _ = ENNReal.ofReal (sobK r * ‖x‖) := by
          rw [sobK, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
  exact (ENNReal.toReal_le_of_le_ofReal (by unfold sobK; positivity) (hx.trans hb))

/-- The Sobolev embedding as a continuous linear map. -/
def sobCLM : H1B0 c r →L[ℝ] L4B c r :=
  (sobLin c r).mkContinuous (sobK r) (norm_sobLin_le c r)

/-- Multiplication by a fixed `a ∈ L⁴(B)`, `L⁴(B) → L²(B)` (Hölder). -/
def mulLin {a : (Fin 4 → ℝ) → ℝ} (ha : MemLp a 4 (volume.restrict (euclBall c r))) :
    L4B c r →ₗ[ℝ] L2B c r where
  toFun f := ((Lp.memLp f).mul' ha).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    refine (MemLp.toLp_eq_toLp_iff _ _).mpr ?_
    filter_upwards [Lp.coeFn_add f g] with x hx
    simp only [hx, Pi.add_apply]; ring
  map_smul' t f := by
    rw [← MemLp.toLp_const_smul]
    refine (MemLp.toLp_eq_toLp_iff _ _).mpr ?_
    filter_upwards [Lp.coeFn_smul t f] with x hx
    simp only [hx, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem norm_mulLin_le {a : (Fin 4 → ℝ) → ℝ} (ha : MemLp a 4 (volume.restrict (euclBall c r)))
    (f : L4B c r) :
    ‖mulLin c r ha f‖ ≤ (eLpNorm a 4 (volume.restrict (euclBall c r))).toReal * ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, show mulLin c r ha f = ((Lp.memLp f).mul' ha).toLp _ from rfl,
    eLpNorm_congr_ae (MemLp.coeFn_toLp _), ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top ha.eLpNorm_ne_top (Lp.eLpNorm_ne_top _)) ?_
  have := eLpNorm_smul_le_mul_eLpNorm (p := 4) (q := 4) (r := 2) (Lp.aestronglyMeasurable f)
    ha.1
  simp only [smul_eq_mul] at this
  exact this

/-- Multiplication by `a ∈ L⁴(B)` as a continuous linear map `L⁴(B) → L²(B)`. -/
def mulCLM {a : (Fin 4 → ℝ) → ℝ} (ha : MemLp a 4 (volume.restrict (euclBall c r))) :
    L4B c r →L[ℝ] L2B c r :=
  (mulLin c r ha).mkContinuous _ (norm_mulLin_le c r ha)

theorem norm_mulCLM_apply_le {a : (Fin 4 → ℝ) → ℝ}
    (ha : MemLp a 4 (volume.restrict (euclBall c r))) (f : L4B c r) :
    ‖mulCLM c r ha f‖ ≤ (eLpNorm a 4 (volume.restrict (euclBall c r))).toReal * ‖f‖ :=
  norm_mulLin_le c r ha f

end Linearized


section Coupled

variable (c : Fin 4 → ℝ) (r : ℝ) [hr : Fact (0 < r)] (N : ℕ)

/-- `N`-component mean-zero `H¹(B)` fields. -/
abbrev XiB := PiLp 2 (fun _ : Fin N => H1B0 c r)

set_option synthInstance.maxHeartbeats 200000 in
instance instInnerXiB : InnerProductSpace ℝ (XiB c r N) := PiLp.innerProductSpace _

set_option synthInstance.maxHeartbeats 200000 in
instance instCompleteXiB : CompleteSpace (XiB c r N) := inferInstance

/-- The `k`-th component. -/
def compXi (k : Fin N) : XiB c r N →L[ℝ] H1B0 c r := PiLp.proj (𝕜 := ℝ) 2 _ k

/-- The `ν`-th derivative of an `H¹₀(B)` element, in `L²(B)`. -/
def derivL (ν : Fin 4) : H1B0 c r →L[ℝ] L2B c r :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin 4) => L2B c r) (some ν)).comp (H1B0 c r).subtypeL

/-- The Dirichlet form on `N`-component fields. -/
def dirFormN : XiB c r N →L[ℝ] XiB c r N →L[ℝ] ℝ :=
  ∑ k, (dirForm c r).bilinearComp (compXi c r N k) (compXi c r N k)

/-- The coupling `p(ξ, η) = Σ_{ν,k,l} ⟨a_ν^{kl} ξ_l, ∂_ν η_k⟩_{L²(B)}` of the linearised Coulomb
operator `ξ ↦ d^*(dξ + [a, ξ])` (`a_ν^{kl}` the matrix of `ad a_ν` in a real basis). -/
def couplingN {a : Fin 4 → Fin N → Fin N → (Fin 4 → ℝ) → ℝ}
    (ha : ∀ ν k l, MemLp (a ν k l) 4 (volume.restrict (euclBall c r))) :
    XiB c r N →L[ℝ] XiB c r N →L[ℝ] ℝ :=
  ∑ ν, ∑ k, ∑ l, (innerSL ℝ (E := L2B c r)).bilinearComp
    ((mulCLM c r (ha ν k l)).comp ((sobCLM c r).comp (compXi c r N l)))
    ((derivL c r ν).comp (compXi c r N k))

/-- The full linearised form `a_D + p`. -/
def linFormN {a : Fin 4 → Fin N → Fin N → (Fin 4 → ℝ) → ℝ}
    (ha : ∀ ν k l, MemLp (a ν k l) 4 (volume.restrict (euclBall c r))) :
    XiB c r N →L[ℝ] XiB c r N →L[ℝ] ℝ :=
  dirFormN c r N + couplingN c r N ha

theorem linFormN_apply {a : Fin 4 → Fin N → Fin N → (Fin 4 → ℝ) → ℝ}
    (ha : ∀ ν k l, MemLp (a ν k l) 4 (volume.restrict (euclBall c r))) (ξ η : XiB c r N) :
    linFormN c r N ha ξ η = dirFormN c r N ξ η + couplingN c r N ha ξ η := rfl

theorem norm_sq_XiB (ξ : XiB c r N) : ‖ξ‖ ^ 2 = ∑ k, ‖ξ k‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ ξ

theorem dirFormN_apply (ξ η : XiB c r N) :
    dirFormN c r N ξ η = ∑ k, dirForm c r (ξ k) (η k) := by
  simp [dirFormN, compXi, ContinuousLinearMap.sum_apply]

theorem couplingN_apply {a : Fin 4 → Fin N → Fin N → (Fin 4 → ℝ) → ℝ}
    (ha : ∀ ν k l, MemLp (a ν k l) 4 (volume.restrict (euclBall c r))) (ξ η : XiB c r N) :
    couplingN c r N ha ξ η = ∑ ν, ∑ k, ∑ l,
      ⟪mulCLM c r (ha ν k l) (sobCLM c r (ξ l)), derivL c r ν (η k)⟫ := by
  simp [couplingN, compXi, ContinuousLinearMap.sum_apply]

/-- Explicit coercivity of the scalar Dirichlet form. -/
theorem dirForm_coercive_const : ∃ κ : ℝ, 0 < κ ∧ ∀ x : H1B0 c r, κ * ‖x‖ ^ 2 ≤ dirForm c r x x := by
  obtain ⟨κ, hκ, h⟩ := dirForm_coercive c r
  exact ⟨κ, hκ, fun x => by have := h x; nlinarith⟩

theorem norm_derivL_le (ν : Fin 4) (x : H1B0 c r) : ‖derivL c r ν x‖ ≤ ‖x‖ :=
  PiLp.norm_apply_le (x : H1Amb c r) (some ν)

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
/-- **The linearised Coulomb operator with the natural Neumann condition on a ball** (generic
form, stage C5): there is `δ > 0` (depending on the ball) such that for all coefficients
`a_ν^{kl} ∈ L⁴(B)` with `Σ ‖a_ν^{kl}‖_{L⁴(B)} ≤ δ` and every continuous load `ℓ` on mean-zero
`N`-component `H¹(B)` fields, there is a unique mean-zero `ξ` with
`Σ_k Σ_ν ⟨∂_ν ξ_k + Σ_l a_ν^{kl} ξ_l, ∂_ν η_k⟩_{L²(B)} = ℓ(η)` for all mean-zero `η` — the weak
form of `d^*(dξ + [a, ξ]) = f` with `(dξ + [a,ξ])·ν = 0` on the sphere (Lax–Milgram for the
coercive form `a_D + p`, the coupling being small by Hölder and the Sobolev inequality on
`H¹(B)`). -/
theorem linearized_neumann_ball : ∃ δ : ℝ, 0 < δ ∧
    ∀ (a : Fin 4 → Fin N → Fin N → (Fin 4 → ℝ) → ℝ)
      (ha : ∀ ν k l, MemLp (a ν k l) 4 (volume.restrict (euclBall c r))),
      ∑ ν, ∑ k, ∑ l, (eLpNorm (a ν k l) 4 (volume.restrict (euclBall c r))).toReal ≤ δ →
      ∀ ℓ : XiB c r N →L[ℝ] ℝ, ∃! ξ : XiB c r N, ∀ η : XiB c r N,
        dirFormN c r N ξ η + couplingN c r N ha ξ η = ℓ η := by
  obtain ⟨κ, hκ, hcoer⟩ := dirForm_coercive_const c r
  have hK : 0 < sobK r + 1 := by unfold sobK; have := hr.out; positivity
  refine ⟨κ / (2 * (sobK r + 1)), by positivity, fun a ha hsmall ℓ => ?_⟩
  set A := ∑ ν, ∑ k, ∑ l, (eLpNorm (a ν k l) 4 (volume.restrict (euclBall c r))).toReal
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hsobK : 0 ≤ sobK r := by unfold sobK; have := hr.out; positivity
  -- the coupling is small
  have hP : ∀ ξ : XiB c r N, |couplingN c r N ha ξ ξ| ≤ A * sobK r * ‖ξ‖ ^ 2 := by
    intro ξ
    rw [couplingN_apply]
    have hcomp : ∀ k, ‖ξ k‖ ≤ ‖ξ‖ := fun k => PiLp.norm_apply_le ξ k
    have h1 : ∀ ν k l, |⟪mulCLM c r (ha ν k l) (sobCLM c r (ξ l)), derivL c r ν (ξ k)⟫| ≤
        (eLpNorm (a ν k l) 4 (volume.restrict (euclBall c r))).toReal * sobK r * ‖ξ‖ ^ 2 := by
      intro ν k l
      refine (abs_real_inner_le_norm _ _).trans ?_
      have e1 := norm_mulCLM_apply_le c r (ha ν k l) (sobCLM c r (ξ l))
      have e2 : ‖sobCLM c r (ξ l)‖ ≤ sobK r * ‖ξ‖ :=
        (norm_sobLin_le c r (ξ l)).trans (mul_le_mul_of_nonneg_left (hcomp l) hsobK)
      have e3 : ‖derivL c r ν (ξ k)‖ ≤ ‖ξ‖ := (norm_derivL_le c r ν (ξ k)).trans (hcomp k)
      calc ‖mulCLM c r (ha ν k l) (sobCLM c r (ξ l))‖ * ‖derivL c r ν (ξ k)‖
          ≤ ((eLpNorm (a ν k l) 4 (volume.restrict (euclBall c r))).toReal *
              (sobK r * ‖ξ‖)) * ‖ξ‖ := by
            gcongr
            exact e1.trans (mul_le_mul_of_nonneg_left e2 ENNReal.toReal_nonneg)
        _ = _ := by ring
    calc |∑ ν, ∑ k, ∑ l, ⟪mulCLM c r (ha ν k l) (sobCLM c r (ξ l)), derivL c r ν (ξ k)⟫|
        ≤ ∑ ν, ∑ k, ∑ l, |⟪mulCLM c r (ha ν k l) (sobCLM c r (ξ l)), derivL c r ν (ξ k)⟫| :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ν _ =>
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ =>
              Finset.abs_sum_le_sum_abs _ _))
      _ ≤ ∑ ν, ∑ k, ∑ l, (eLpNorm (a ν k l) 4 (volume.restrict (euclBall c r))).toReal *
            sobK r * ‖ξ‖ ^ 2 :=
          Finset.sum_le_sum fun ν _ => Finset.sum_le_sum fun k _ => Finset.sum_le_sum
            fun l _ => h1 ν k l
      _ = A * sobK r * ‖ξ‖ ^ 2 := by
          simp only [A, Finset.sum_mul]
  -- coercivity of the perturbed form
  have hcoerN : IsCoercive (linFormN c r N ha) := by
    refine ⟨κ / 2, by positivity, fun ξ => ?_⟩
    have hD : κ * ‖ξ‖ ^ 2 ≤ dirFormN c r N ξ ξ := by
      rw [dirFormN_apply, norm_sq_XiB, Finset.mul_sum]
      exact Finset.sum_le_sum fun k _ => hcoer (ξ k)
    have hAs : A * sobK r ≤ κ / 2 := by
      calc A * sobK r ≤ κ / (2 * (sobK r + 1)) * (sobK r + 1) :=
            mul_le_mul hsmall (by linarith) hsobK (by positivity)
        _ = κ / 2 := by field_simp
    have hPξ := hP ξ
    rw [linFormN_apply]
    have : -(A * sobK r * ‖ξ‖ ^ 2) ≤ couplingN c r N ha ξ ξ := neg_le_of_abs_le hPξ
    nlinarith [sq_nonneg ‖ξ‖]
  -- Lax–Milgram
  refine ⟨hcoerN.continuousLinearEquivOfBilin.symm
    ((InnerProductSpace.toDual ℝ (XiB c r N)).symm ℓ), fun η => ?_, fun ξ' hξ' => ?_⟩
  · rw [← linFormN_apply, ← IsCoercive.continuousLinearEquivOfBilin_apply hcoerN,
      ContinuousLinearEquiv.apply_symm_apply, InnerProductSpace.toDual_symm_apply]
  · rw [ContinuousLinearEquiv.eq_symm_apply]
    refine (IsCoercive.unique_continuousLinearEquivOfBilin hcoerN fun w => ?_).symm
    rw [InnerProductSpace.toDual_symm_apply, linFormN_apply, hξ' w]

end Coupled


/-- Non-vacuity: the zero coefficient satisfies the smallness hypothesis of
`linearized_neumann_ball` (so the theorem applies, e.g. with `ℓ = 0`). -/
example (N : ℕ) : ∃ δ : ℝ, 0 < δ ∧ ∑ ν : Fin 4, ∑ k : Fin N, ∑ l : Fin N,
    (eLpNorm (fun _ : Fin 4 → ℝ => (0 : ℝ)) 4 (volume.restrict (euclBall (0 : Fin 4 → ℝ) 1))).toReal
      ≤ δ := ⟨1, one_pos, by simp⟩

end RenewalGeometry.BallAnalysis
