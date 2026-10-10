/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallCoulombGaugeMap

/-!
# Openness of the Coulomb–Neumann gauge condition (implicit function theorem on `H^s(B)`)
  (stage D1 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `neuSub`, `tanSub`, `meanZeroSub` — the closed subspaces of mean-zero weakly Neumann
  `H⁵(B)` functions, of weakly tangential `H⁴(B)` coefficient fields and of mean-zero `H³(B)`
  functions; `XSp L`, `TSp L`, `YSp L` — their `d`-component versions (Banach spaces);
* `projMean` — the projection onto mean-zero functions;
* `coulIFT` — the restricted Coulomb functional `T × X → Y`;
* `coulomb_openness` (**the implicit function theorem**): at a Coulomb connection `a ∈ T`
  (`coulF L (a, 0) = 0`) with small `L⁴` coefficients, there is a function `ψ : T → X`,
  continuous at `a`, `ψ a = 0`, with `coulIFT (t, ψ t) = 0` for all `t` near `a`.
-/

open MeasureTheory Set Filter Topology NormedSpace
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator RealInnerProductSpace

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallAlg

open SobolevOpen BallReg SobAlg

set_option linter.unusedSectionVars false

section Subspaces

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)]

/-- The function component as a continuous linear map into `L²(B)`. -/
def fnL {s : ℕ} [Fact (3 ≤ s)] : SobAlg c r s →L[ℝ] L2B c r :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ↥(wordsUpTo 4 s) => L2B c r) (nilW s)).comp
    ((HsB c r s).subtypeL.comp jetL)

theorem fnL_coe {s : ℕ} [Fact (3 ≤ s)] (F : SobAlg c r s) :
    ((fnL F : L2B c r) : (Fin 4 → ℝ) → ℝ) = fn F := rfl

theorem integral_fn_mul {s : ℕ} [Fact (3 ≤ s)] (F : SobAlg c r s) {g : (Fin 4 → ℝ) → ℝ}
    (hg : MemLp g 2 (volume.restrict (euclBall c r))) :
    ∫ x in euclBall c r, fn F x * g x = ⟪fnL F, hg.toLp g⟫ := by
  rw [real_inner_comm, inner_toLp_left]
  congr 1; funext x; rw [fnL_coe, mul_comm]

theorem meanS_eq_inner {s : ℕ} [Fact (3 ≤ s)] (F : SobAlg c r s) :
    meanS F = ⟪oneB c r, fnL F⟫ := by
  rw [inner_oneB]; rfl

/-- The Neumann functional `η ↦ Σ_ν ∫ ∂_νη ∂_νφ + ∫ Δη φ` of a `C¹` test function. -/
def neuFun (φ : (Fin 4 → ℝ) → ℝ) (hφ : ContDiff ℝ 1 φ) : SobAlg c r 5 →L[ℝ] ℝ :=
  ∑ ν, (innerSL ℝ ((memLp_ball_pd_of_C1 c r hφ ν).toLp (pd φ ν))).comp (fnL.comp (derS ν)) +
    (innerSL ℝ ((memLp_ball_of_C1 c r hφ).toLp φ)).comp (fnL.comp
      (∑ ν, (derS (s := 3) ν).comp (derS ν)))

theorem neuFun_apply (φ : (Fin 4 → ℝ) → ℝ) (hφ : ContDiff ℝ 1 φ) (η : SobAlg c r 5) :
    neuFun φ hφ η = (∑ ν, ∫ x in euclBall c r, fn (derS ν η) x * pd φ ν x) +
      ∫ x in euclBall c r, fn (lapS η) x * φ x := by
  simp only [neuFun, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  rw [integral_fn_mul (lapS η) (memLp_ball_of_C1 c r hφ), real_inner_comm]
  congr 1
  · refine Finset.sum_congr rfl fun ν _ => ?_
    rw [integral_fn_mul _ (memLp_ball_pd_of_C1 c r hφ ν), real_inner_comm]

theorem isNeumannS_iff (η : SobAlg c r 5) :
    IsNeumannS η ↔ ∀ φ (hφ : ContDiff ℝ 1 φ), neuFun φ hφ η = 0 := by
  constructor
  · intro h φ hφ
    rw [neuFun_apply, h φ hφ]; ring
  · intro h φ hφ
    have := h φ hφ
    rw [neuFun_apply] at this
    linarith

/-- **Mean-zero weakly Neumann `H⁵(B)` functions** (a closed subspace). -/
def neuSub : Submodule ℝ (SobAlg c r 5) where
  carrier := {η | (∀ φ (hφ : ContDiff ℝ 1 φ), neuFun φ hφ η = 0) ∧ ⟪oneB c r, fnL η⟫ = 0}
  add_mem' := fun {η ζ} hη hζ => ⟨fun φ hφ => by rw [map_add, hη.1 φ hφ, hζ.1 φ hφ, add_zero],
    by rw [map_add, inner_add_right, hη.2, hζ.2, add_zero]⟩
  zero_mem' := ⟨fun φ hφ => map_zero _, by rw [map_zero, inner_zero_right]⟩
  smul_mem' := fun t η hη => ⟨fun φ hφ => by rw [map_smul, hη.1 φ hφ, smul_zero],
    by rw [map_smul, inner_smul_right, hη.2, mul_zero]⟩

theorem mem_neuSub {η : SobAlg c r 5} : η ∈ neuSub (c := c) (r := r) ↔
    IsNeumannS η ∧ meanS η = 0 := by
  rw [isNeumannS_iff, meanS_eq_inner]; rfl

theorem isClosed_neuSub : IsClosed (neuSub (c := c) (r := r) : Set (SobAlg c r 5)) := by
  have : (neuSub (c := c) (r := r) : Set (SobAlg c r 5)) =
      (⋂ (φ : (Fin 4 → ℝ) → ℝ) (hφ : ContDiff ℝ 1 φ), {η | neuFun φ hφ η = 0}) ∩
        {η | ⟪oneB c r, fnL η⟫ = 0} := by
    ext η; simp [neuSub]
  rw [this]
  exact (isClosed_iInter fun φ => isClosed_iInter fun hφ =>
    isClosed_eq (neuFun φ hφ).continuous continuous_const).inter
    (isClosed_eq (continuous_const.inner fnL.continuous) continuous_const)

/-- Mean-zero `H³(B)` functions. -/
def meanZeroSub : Submodule ℝ (SobAlg c r 3) :=
  LinearMap.ker ((innerSL ℝ (oneB c r)).comp (fnL (s := 3)) : SobAlg c r 3 →L[ℝ] ℝ).toLinearMap

theorem mem_meanZeroSub {F : SobAlg c r 3} : F ∈ meanZeroSub (c := c) (r := r) ↔ meanS F = 0 := by
  rw [meanS_eq_inner]; rfl

theorem isClosed_meanZeroSub : IsClosed (meanZeroSub (c := c) (r := r) : Set (SobAlg c r 3)) :=
  ContinuousLinearMap.isClosed_ker _

/-- The tangential functional of a `C¹` test function. -/
def tanFun (φ : (Fin 4 → ℝ) → ℝ) (hφ : ContDiff ℝ 1 φ) : (Fin 4 → SobAlg c r 4) →L[ℝ] ℝ :=
  ∑ ν, (innerSL ℝ ((memLp_ball_pd_of_C1 c r hφ ν).toLp (pd φ ν))).comp
      (fnL.comp (ContinuousLinearMap.proj ν)) +
    (innerSL ℝ ((memLp_ball_of_C1 c r hφ).toLp φ)).comp (fnL.comp
      (∑ ν, (derS (s := 3) ν).comp (ContinuousLinearMap.proj ν)))

theorem tanFun_apply (φ : (Fin 4 → ℝ) → ℝ) (hφ : ContDiff ℝ 1 φ) (a : Fin 4 → SobAlg c r 4) :
    tanFun φ hφ a = (∑ ν, ∫ x in euclBall c r, fn (a ν) x * pd φ ν x) +
      ∫ x in euclBall c r, fn (divS a) x * φ x := by
  simp only [tanFun, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, ContinuousLinearMap.proj_apply]
  rw [integral_fn_mul (divS a) (memLp_ball_of_C1 c r hφ), real_inner_comm]
  congr 1
  · refine Finset.sum_congr rfl fun ν _ => ?_
    rw [integral_fn_mul _ (memLp_ball_pd_of_C1 c r hφ ν), real_inner_comm]

theorem isTangentialS_iff (a : Fin 4 → SobAlg c r 4) :
    IsTangentialS a ↔ ∀ φ (hφ : ContDiff ℝ 1 φ), tanFun φ hφ a = 0 := by
  constructor
  · intro h φ hφ
    rw [tanFun_apply, h φ hφ]; ring
  · intro h φ hφ
    have := h φ hφ
    rw [tanFun_apply] at this
    linarith

/-- **Weakly tangential `H⁴(B)` vector fields** (a closed subspace). -/
def tanSub : Submodule ℝ (Fin 4 → SobAlg c r 4) where
  carrier := {a | ∀ φ (hφ : ContDiff ℝ 1 φ), tanFun φ hφ a = 0}
  add_mem' := fun {a b} ha hb φ hφ => by rw [map_add, ha φ hφ, hb φ hφ, add_zero]
  zero_mem' := fun φ hφ => map_zero _
  smul_mem' := fun t a ha φ hφ => by rw [map_smul, ha φ hφ, smul_zero]

theorem mem_tanSub {a : Fin 4 → SobAlg c r 4} : a ∈ tanSub (c := c) (r := r) ↔ IsTangentialS a := by
  rw [isTangentialS_iff]; rfl

theorem isClosed_tanSub : IsClosed (tanSub (c := c) (r := r) : Set (Fin 4 → SobAlg c r 4)) := by
  have : (tanSub (c := c) (r := r) : Set (Fin 4 → SobAlg c r 4)) =
      ⋂ (φ : (Fin 4 → ℝ) → ℝ) (hφ : ContDiff ℝ 1 φ), {a | tanFun φ hφ a = 0} := by
    ext a; simp [tanSub]
  rw [this]
  exact isClosed_iInter fun φ => isClosed_iInter fun hφ =>
    isClosed_eq (tanFun φ hφ).continuous continuous_const

end Subspaces

/-! ### The `d`-component Banach spaces and the projection onto mean zero -/

section Spaces

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {d : ℕ}

/-- **The unknowns**: `d` mean-zero weakly Neumann `H⁵(B)` functions. -/
def XSp (d : ℕ) : Submodule ℝ (Fin d → SobAlg c r 5) :=
  Submodule.pi Set.univ fun _ => neuSub (c := c) (r := r)

/-- **The parameters**: coefficient fields `a_μ^e ∈ H⁴(B)`, weakly tangential for each `e`. -/
def TSp (d : ℕ) : Submodule ℝ (Fin 4 → Fin d → SobAlg c r 4) where
  carrier := {a | ∀ e, (fun μ => a μ e) ∈ tanSub (c := c) (r := r)}
  add_mem' := fun {a b} ha hb e => by
    have := (tanSub (c := c) (r := r)).add_mem (ha e) (hb e)
    exact this
  zero_mem' := fun e => (tanSub (c := c) (r := r)).zero_mem
  smul_mem' := fun t a ha e => by
    have := (tanSub (c := c) (r := r)).smul_mem t (ha e)
    exact this

/-- **The targets**: `d` mean-zero `H³(B)` functions. -/
def YSp (d : ℕ) : Submodule ℝ (Fin d → SobAlg c r 3) :=
  Submodule.pi Set.univ fun _ => meanZeroSub (c := c) (r := r)

theorem isClosed_XSp : IsClosed (XSp (c := c) (r := r) d : Set (Fin d → SobAlg c r 5)) := by
  have : (XSp (c := c) (r := r) d : Set (Fin d → SobAlg c r 5)) =
      Set.pi Set.univ fun _ => (neuSub (c := c) (r := r) : Set (SobAlg c r 5)) := by
    ext x; simp [XSp, Submodule.mem_pi]
  rw [this]; exact isClosed_set_pi fun _ _ => isClosed_neuSub

theorem isClosed_YSp : IsClosed (YSp (c := c) (r := r) d : Set (Fin d → SobAlg c r 3)) := by
  have : (YSp (c := c) (r := r) d : Set (Fin d → SobAlg c r 3)) =
      Set.pi Set.univ fun _ => (meanZeroSub (c := c) (r := r) : Set (SobAlg c r 3)) := by
    ext x; simp [YSp, Submodule.mem_pi]
  rw [this]; exact isClosed_set_pi fun _ _ => isClosed_meanZeroSub

theorem isClosed_TSp : IsClosed (TSp (c := c) (r := r) d : Set (Fin 4 → Fin d → SobAlg c r 4)) := by
  have : (TSp (c := c) (r := r) d : Set (Fin 4 → Fin d → SobAlg c r 4)) =
      ⋂ e : Fin d, (fun a : Fin 4 → Fin d → SobAlg c r 4 => fun μ => a μ e) ⁻¹'
        (tanSub (c := c) (r := r) : Set (Fin 4 → SobAlg c r 4)) := by
    ext x; simp [TSp]
  rw [this]
  exact isClosed_iInter fun e => isClosed_tanSub.preimage
    (continuous_pi fun μ => (continuous_apply e).comp (continuous_apply μ))

instance : CompleteSpace (XSp (c := c) (r := r) d) := isClosed_XSp.completeSpace_coe
instance : CompleteSpace (YSp (c := c) (r := r) d) := isClosed_YSp.completeSpace_coe
instance : CompleteSpace (TSp (c := c) (r := r) d) := isClosed_TSp.completeSpace_coe

theorem meanS_one {s : ℕ} [Fact (3 ≤ s)] : meanS (1 : SobAlg c r s) = volB c r := by
  rw [meanS, integral_congr_ae (fn_one (c := c) (r := r) (s := s))]
  simp [volB, measureReal_def]

/-- The mean-zero projection `F ↦ F - (meanS F / |B|) 1`. -/
def projMeanFun (F : SobAlg c r 3) : SobAlg c r 3 := F - (meanS F / volB c r) • 1

theorem meanS_projMeanFun (F : SobAlg c r 3) : meanS (projMeanFun F) = 0 := by
  have hv := (volB_pos c r).ne'
  have h1 : meanS (projMeanFun F) = meanS F - (meanS F / volB c r) * meanS (1 : SobAlg c r 3) := by
    simp only [meanS_eq_inner, projMeanFun, map_sub, map_smul, inner_sub_right, inner_smul_right]
  rw [h1, meanS_one]
  field_simp
  ring

/-- **The projection onto mean-zero functions**, as a continuous linear map into `YSp`. -/
def projMean (d : ℕ) : (Fin d → SobAlg c r 3) →L[ℝ] YSp (c := c) (r := r) d :=
  ContinuousLinearMap.codRestrict
    (ContinuousLinearMap.id ℝ (Fin d → SobAlg c r 3) -
      ContinuousLinearMap.pi fun k => (ContinuousLinearMap.smulRight
        (((volB c r)⁻¹ • (innerSL ℝ (oneB c r))).comp ((fnL (s := 3)).comp
          (ContinuousLinearMap.proj k))) (1 : SobAlg c r 3)))
    (YSp (c := c) (r := r) d) fun f => by
      simp only [YSp, Submodule.mem_pi, Set.mem_univ, true_imp_iff]
      intro k
      rw [mem_meanZeroSub]
      have := meanS_projMeanFun (c := c) (r := r) (f k)
      convert this using 2
      simp [projMeanFun, meanS_eq_inner, div_eq_inv_mul]

theorem projMean_apply (f : Fin d → SobAlg c r 3) (k : Fin d) :
    ((projMean d f : YSp (c := c) (r := r) d) : Fin d → SobAlg c r 3) k = projMeanFun (f k) := by
  simp [projMean, projMeanFun, meanS_eq_inner, div_eq_inv_mul]

theorem projMean_of_mem {f : Fin d → SobAlg c r 3} (hf : ∀ k, meanS (f k) = 0) :
    ((projMean d f : YSp (c := c) (r := r) d) : Fin d → SobAlg c r 3) = f := by
  funext k
  rw [projMean_apply, projMeanFun, hf k, zero_div, zero_smul, sub_zero]

end Spaces

/-! ### The implicit function theorem -/

section IFT

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {m d : ℕ}

/-- The linearised operator maps Neumann fields to mean-zero fields. -/
theorem meanS_linOpS {N : ℕ} {A : Fin 4 → Fin N → Fin N → SobAlg c r 4}
    (htan : ∀ k l, IsTangentialS (fun ν => A ν k l)) {η : Fin N → SobAlg c r 5}
    (hN : ∀ k, IsNeumannS (η k)) (k : Fin N) : meanS (linOpS A η k) = 0 := by
  have h := weak_linOpS htan hN k (oneH_mem c r)
  have hzero : ∀ ν, ((oneH c r (some ν) : L2B c r) : (Fin 4 → ℝ) → ℝ) =ᵐ[volume.restrict
      (euclBall c r)] fun _ => 0 := fun ν => by
    show (((0 : L2B c r)) : (Fin 4 → ℝ) → ℝ) =ᵐ[_] fun _ => 0
    exact Lp.coeFn_zero _ _ _
  have hone : ((oneH c r none : L2B c r) : (Fin 4 → ℝ) → ℝ) =ᵐ[volume.restrict (euclBall c r)]
      fun _ => 1 := by
    show ((oneB c r : L2B c r) : (Fin 4 → ℝ) → ℝ) =ᵐ[_] fun _ => 1
    exact (memLp_const (1 : ℝ)).coeFn_toLp
  have e0 : ∀ (F : (Fin 4 → ℝ) → ℝ) ν, ∫ x in euclBall c r, F x *
      ((oneH c r (some ν) : L2B c r) : (Fin 4 → ℝ) → ℝ) x = 0 := fun F ν => by
    refine (integral_congr_ae ?_).trans (integral_zero _ _)
    filter_upwards [hzero ν] with x hx
    simp [hx]
  simp only [e0, Finset.sum_const_zero, add_zero] at h
  have e1 : ∫ x in euclBall c r, fn (linOpS A η k) x *
      ((oneH c r none : L2B c r) : (Fin 4 → ℝ) → ℝ) x = meanS (linOpS A η k) := by
    refine integral_congr_ae ?_
    filter_upwards [hone] with x hx
    simp [hx]
  rw [e1] at h
  linarith

/-- The tangentiality of the coefficients of the linearised operator. -/
theorem brkCoef_tangential (L : LieBasis m d) {a : Fin 4 → Fin d → SobAlg c r 4}
    (ha : a ∈ TSp (c := c) (r := r) d) (k l : Fin d) :
    IsTangentialS (fun ν => brkCoef L a ν k l) := by
  rw [← mem_tanSub]
  have : (fun ν => brkCoef L a ν k l) = -∑ b, L.f l b k • (fun ν => a ν b) := by
    funext ν; simp [brkCoef, Finset.sum_apply]
  rw [this]
  exact (tanSub (c := c) (r := r)).neg_mem ((tanSub (c := c) (r := r)).sum_mem fun b _ =>
    (tanSub (c := c) (r := r)).smul_mem _ (ha b))

/-- The size of the structure constants. -/
def LieBasis.fNorm (L : LieBasis m d) : ℝ := ∑ l, ∑ b, ∑ k, |L.f l b k| + 1

theorem LieBasis.fNorm_pos (L : LieBasis m d) : 0 < L.fNorm := by
  unfold LieBasis.fNorm; positivity

theorem eLpNorm_fn_brkCoef_le (L : LieBasis m d) (a : Fin 4 → Fin d → SobAlg c r 4) (ν : Fin 4)
    (k l : Fin d) :
    (eLpNorm (fn (brkCoef L a ν k l)) 4 (volume.restrict (euclBall c r))).toReal ≤
      ∑ b, |L.f l b k| * (eLpNorm (fn (a ν b)) 4 (volume.restrict (euclBall c r))).toReal := by
  set μB := volume.restrict (euclBall c r)
  have hae : fn (brkCoef L a ν k l) =ᵐ[μB] ∑ b, fun x => -(L.f l b k * fn (a ν b) x) := by
    have h1 := fn_neg (∑ b, L.f l b k • a ν b)
    have h2 := fn_sum Finset.univ (fun b => L.f l b k • a ν b)
    have h3 : ∀ᵐ x ∂μB, ∀ b, fn (L.f l b k • a ν b) x = L.f l b k * fn (a ν b) x := by
      rw [ae_all_iff]; exact fun b => fn_smul _ _
    filter_upwards [h1, h2, h3] with x e1 e2 e3
    simp only [brkCoef]
    rw [e1, e2, Finset.sum_apply, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun b _ => by rw [e3 b]
  rw [eLpNorm_congr_ae hae]
  have hm : ∀ b, AEStronglyMeasurable (fun x => -(L.f l b k * fn (a ν b) x)) μB := fun b =>
    ((memLp_fn _).aestronglyMeasurable.const_mul _).neg
  have hfin : ∀ b, eLpNorm (fun x => -(L.f l b k * fn (a ν b) x)) 4 μB ≠ ⊤ := fun b => by
    have := ((memLp_four_fn (a ν b)).const_mul (L.f l b k)).neg
    exact this.eLpNorm_ne_top
  refine (ENNReal.toReal_mono (by
    exact (ENNReal.sum_lt_top.mpr fun b _ => (hfin b).lt_top).ne)
    (eLpNorm_sum_le (fun b _ => hm b) (by norm_num))).trans ?_
  rw [ENNReal.toReal_sum fun b _ => hfin b]
  refine Finset.sum_le_sum fun b _ => le_of_eq ?_
  have : (fun x => -(L.f l b k * fn (a ν b) x)) = -((L.f l b k) • fn (a ν b)) := by
    funext x; simp
  rw [this, eLpNorm_neg, eLpNorm_const_smul, ENNReal.toReal_mul]
  simp

/-- **Smallness of the coefficients of the linearised operator.** -/
theorem sum_eLpNorm_brkCoef_le (L : LieBasis m d) (a : Fin 4 → Fin d → SobAlg c r 4) :
    ∑ ν, ∑ k, ∑ l, (eLpNorm (fn (brkCoef L a ν k l)) 4 (volume.restrict (euclBall c r))).toReal ≤
      L.fNorm * ∑ ν, ∑ b, (eLpNorm (fn (a ν b)) 4 (volume.restrict (euclBall c r))).toReal := by
  set N : Fin 4 → Fin d → ℝ := fun ν b =>
    (eLpNorm (fn (a ν b)) 4 (volume.restrict (euclBall c r))).toReal
  have hN : ∀ ν b, 0 ≤ N ν b := fun ν b => ENNReal.toReal_nonneg
  calc ∑ ν, ∑ k, ∑ l, (eLpNorm (fn (brkCoef L a ν k l)) 4 (volume.restrict (euclBall c r))).toReal
      ≤ ∑ ν, ∑ k, ∑ l, ∑ b, |L.f l b k| * N ν b :=
        Finset.sum_le_sum fun ν _ => Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ =>
          eLpNorm_fn_brkCoef_le L a ν k l
    _ ≤ ∑ ν, ∑ b, L.fNorm * N ν b := by
        refine Finset.sum_le_sum fun ν _ => ?_
        have h1 : ∑ k, ∑ l, ∑ b, |L.f l b k| * N ν b =
            ∑ b, (∑ k, ∑ l, |L.f l b k|) * N ν b := by
          simp only [Finset.sum_mul]
          rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm, Finset.sum_comm]
        rw [h1]
        refine Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_right ?_ (hN ν b)
        have h2 : ∑ k, ∑ l, |L.f l b k| ≤ ∑ l, ∑ b', ∑ k, |L.f l b' k| := by
          rw [Finset.sum_comm]
          refine Finset.sum_le_sum fun l _ => ?_
          exact Finset.single_le_sum (f := fun b' => ∑ k, |L.f l b' k|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ b)
        unfold LieBasis.fNorm
        linarith
    _ = L.fNorm * ∑ ν, ∑ b, N ν b := by simp [Finset.mul_sum]

/-- The inclusion `T × X → H⁴(B)^{4d} × H⁵(B)^d`. -/
def inclTX (d : ℕ) : (TSp (c := c) (r := r) d × XSp (c := c) (r := r) d) →L[ℝ]
    (Fin 4 → Fin d → SobAlg c r 4) × (Fin d → SobAlg c r 5) :=
  ContinuousLinearMap.prodMap (TSp (c := c) (r := r) d).subtypeL (XSp (c := c) (r := r) d).subtypeL

/-- **The restricted Coulomb functional** `T × X → Y`, `(a, ξ) ↦ P₀ κ(d^*(e^ξ·A))`. -/
def coulIFT (L : LieBasis m d) (p : TSp (c := c) (r := r) d × XSp (c := c) (r := r) d) :
    YSp (c := c) (r := r) d :=
  projMean d (coulF L (inclTX d p))

set_option backward.isDefEq.respectTransparency false in
theorem hasStrictFDerivAt_coulIFT (L : LieBasis m d)
    (u : TSp (c := c) (r := r) d × XSp (c := c) (r := r) d) :
    HasStrictFDerivAt (coulIFT L)
      ((projMean d).comp ((fderiv ℝ (coulF L) (inclTX d u)).comp (inclTX d))) u := by
  have hF := ((contDiff_coulF (c := c) (r := r) L).contDiffAt (x := inclTX d u)).hasStrictFDerivAt
    (by simp)
  exact (projMean d).hasStrictFDerivAt.comp u (hF.comp u (inclTX d).hasStrictFDerivAt)

set_option backward.isDefEq.respectTransparency false in
theorem fderiv_coulF_inr (L : LieBasis m d) (a : Fin 4 → Fin d → SobAlg c r 4) :
    (fderiv ℝ (coulF L) (a, 0)).comp (ContinuousLinearMap.inr ℝ _ _) = coulD (m := m) L a := by
  have hF := ((contDiff_coulF (c := c) (r := r) L).contDiffAt (x := (a, 0))).differentiableAt
    (by simp)
  have h1 : HasFDerivAt (fun ξ : Fin d → SobAlg c r 5 => (a, ξ))
      (ContinuousLinearMap.inr ℝ (Fin 4 → Fin d → SobAlg c r 4) (Fin d → SobAlg c r 5)) 0 :=
    (hasFDerivAt_const a 0).prodMk (hasFDerivAt_id 0)
  have h2 := hF.hasFDerivAt.comp (0 : Fin d → SobAlg c r 5) h1
  exact h2.unique (hasFDerivAt_coulF_snd L a)

/-- The common smallness constant of `linOpS_injective` and `exists_linOpS_eq`. -/
theorem exists_delta_lin (d : ℕ) : ∃ δ : ℝ, 0 < δ ∧ ∀ (A : Fin 4 → Fin d → Fin d → SobAlg c r 4),
    (∀ k l, IsTangentialS (fun ν => A ν k l)) →
    ∑ ν, ∑ k, ∑ l, (eLpNorm (fn (A ν k l)) 4 (volume.restrict (euclBall c r))).toReal ≤ δ →
    (∀ η : Fin d → SobAlg c r 5, (∀ k, IsNeumannS (η k)) → (∀ k, meanS (η k) = 0) →
      linOpS A η = 0 → η = 0) ∧
    (∀ f : Fin d → SobAlg c r 3, (∀ k, meanS (f k) = 0) →
      ∃ η : Fin d → SobAlg c r 5, (∀ k, IsNeumannS (η k)) ∧ (∀ k, meanS (η k) = 0) ∧
        linOpS A η = f) := by
  obtain ⟨δ1, hδ1, h1⟩ := linOpS_injective (c := c) (r := r) (N := d)
  obtain ⟨δ2, hδ2, h2⟩ := exists_linOpS_eq (c := c) (r := r) (N := d)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun A htan hsmall => ⟨fun η hN hm h0 => ?_, fun f hf => ?_⟩⟩
  · exact h1 A htan (hsmall.trans (min_le_left _ _)) η hN hm h0
  · exact h2 A htan (hsmall.trans (min_le_right _ _)) f hf

set_option backward.isDefEq.respectTransparency false in
/-- **Openness of the Coulomb–Neumann condition (implicit function theorem on `H^s(B)`)**: there
is `δ₁ > 0` such that for every weakly tangential coefficient field `a ∈ T` (`A = Σ a^b e_b`)
which is Coulomb (`coulF L (a, 0) = 0`) and `L⁴`-small (`Σ ‖a_ν^b‖_{L⁴(B)} ≤ δ₁`), there is
`ψ : T → X`, continuous at `a`, with `ψ a = 0` and `coulIFT L (t, ψ t) = 0` for all `t` near `a`:
the gauge `exp(Σ ψ(t)^b e_b)` puts every nearby connection into Coulomb–Neumann gauge
(modulo the mean, removed by `projMean`). -/
theorem coulomb_openness (L : LieBasis m d) : ∃ δ₁ : ℝ, 0 < δ₁ ∧
    ∀ a : TSp (c := c) (r := r) d,
      coulF L ((a : Fin 4 → Fin d → SobAlg c r 4), 0) = 0 →
      ∑ ν, ∑ b, (eLpNorm (fn ((a : Fin 4 → Fin d → SobAlg c r 4) ν b)) 4
        (volume.restrict (euclBall c r))).toReal ≤ δ₁ →
      ∃ ψ : TSp (c := c) (r := r) d → XSp (c := c) (r := r) d, ψ a = 0 ∧ ContinuousAt ψ a ∧
        ∀ᶠ t in 𝓝 a, coulIFT L (t, ψ t) = 0 := by
  obtain ⟨δ, hδ, hlin⟩ := exists_delta_lin (c := c) (r := r) d
  refine ⟨δ / L.fNorm, div_pos hδ L.fNorm_pos, fun a hC hsmall => ?_⟩
  set u : TSp (c := c) (r := r) d × XSp (c := c) (r := r) d := (a, 0)
  have hD := hasStrictFDerivAt_coulIFT (c := c) (r := r) L u
  set D := (projMean d).comp ((fderiv ℝ (coulF L) (inclTX d u)).comp (inclTX d))
  -- the coefficients of the linearised operator
  set A := brkCoef L (a : Fin 4 → Fin d → SobAlg c r 4)
  have htanA : ∀ k l, IsTangentialS (fun ν => A ν k l) := brkCoef_tangential L a.2
  have hsmallA : ∑ ν, ∑ k, ∑ l, (eLpNorm (fn (A ν k l)) 4
      (volume.restrict (euclBall c r))).toReal ≤ δ := by
    refine (sum_eLpNorm_brkCoef_le L _).trans ?_
    have := mul_le_mul_of_nonneg_left hsmall L.fNorm_pos.le
    rwa [mul_div_cancel₀ _ L.fNorm_pos.ne'] at this
  obtain ⟨hinj, hsurj⟩ := hlin A htanA hsmallA
  -- the partial derivative
  have hinclu : inclTX d u = ((a : Fin 4 → Fin d → SobAlg c r 4), 0) := rfl
  have hDx : ∀ x : XSp (c := c) (r := r) d, (D.comp (ContinuousLinearMap.inr ℝ _ _) x :
      Fin d → SobAlg c r 3) = -linOpS A (x : Fin d → SobAlg c r 5) := by
    intro x
    have hx : ∀ k, IsNeumannS ((x : Fin d → SobAlg c r 5) k) ∧ meanS ((x : Fin d → SobAlg c r 5) k) = 0 :=
      fun k => mem_neuSub.mp ((Submodule.mem_pi).mp x.2 k (Set.mem_univ k))
    have e1 : (fderiv ℝ (coulF L) (inclTX d u)) (inclTX d (0, x)) =
        coulD L (a : Fin 4 → Fin d → SobAlg c r 4) x := by
      rw [hinclu, ← fderiv_coulF_inr L]
      rfl
    simp only [D, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, e1,
      coulD_eq_neg_linOpS]
    rw [projMean_of_mem]
    intro k
    simp only [Pi.neg_apply]
    rw [meanS_eq_inner, map_neg, inner_neg_right, ← meanS_eq_inner,
      meanS_linOpS htanA (fun k => (hx k).1) k, neg_zero]
  -- invertibility
  have hinv : (D.comp (ContinuousLinearMap.inr ℝ _ _)).IsInvertible := by
    refine ⟨ContinuousLinearEquiv.ofBijective (D.comp (ContinuousLinearMap.inr ℝ _ _)) ?_ ?_, rfl⟩
    · rw [LinearMap.ker_eq_bot']
      intro x hx
      have hx' : ∀ k, IsNeumannS ((x : Fin d → SobAlg c r 5) k) ∧
          meanS ((x : Fin d → SobAlg c r 5) k) = 0 :=
        fun k => mem_neuSub.mp ((Submodule.mem_pi).mp x.2 k (Set.mem_univ k))
      have h0 := congrArg Subtype.val hx
      simp only [ContinuousLinearMap.coe_coe] at h0
      rw [hDx x] at h0
      have h1 : linOpS A (x : Fin d → SobAlg c r 5) = 0 := by
        have := congrArg Neg.neg h0; simpa using this
      exact Subtype.ext (hinj _ (fun k => (hx' k).1) (fun k => (hx' k).2) h1)
    · rw [LinearMap.range_eq_top]
      intro y
      have hy : ∀ k, meanS ((y : Fin d → SobAlg c r 3) k) = 0 :=
        fun k => mem_meanZeroSub.mp ((Submodule.mem_pi).mp y.2 k (Set.mem_univ k))
      obtain ⟨η, hηN, hηm, hη⟩ := hsurj (-(y : Fin d → SobAlg c r 3)) (fun k => by
        rw [Pi.neg_apply, meanS_eq_inner, map_neg, inner_neg_right, ← meanS_eq_inner, hy k,
          neg_zero])
      refine ⟨⟨η, (Submodule.mem_pi).mpr fun k _ => mem_neuSub.mpr ⟨hηN k, hηm k⟩⟩, ?_⟩
      apply Subtype.ext
      simp only [ContinuousLinearMap.coe_coe]
      rw [hDx, hη, neg_neg]
  -- the implicit function theorem
  set ψ := hD.implicitFunctionOfProdDomain hinv
  have hT := hD.tendsto_implicitFunctionOfProdDomain hinv
  have hψa : ψ a = 0 := by
    have h1 : Tendsto ψ (pure a) (𝓝 (0 : XSp (c := c) (r := r) d)) := hT.mono_left (pure_le_nhds a)
    exact tendsto_nhds_unique (tendsto_pure_nhds ψ a) h1
  refine ⟨ψ, hψa, ?_, ?_⟩
  · show Tendsto ψ (𝓝 a) (𝓝 (ψ a))
    rw [hψa]; exact hT
  · have hu0 : coulIFT L u = 0 := by
      apply Subtype.ext
      show ((projMean d (coulF L (inclTX d u)) : YSp (c := c) (r := r) d) :
        Fin d → SobAlg c r 3) = 0
      rw [hinclu, hC, map_zero]
      rfl
    have := hD.eventually_apply_implicitFunctionOfProdDomain hinv
    simpa [hu0] using this

end IFT

end RenewalGeometry.BallAnalysis.BallAlg
