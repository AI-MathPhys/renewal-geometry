/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallCoulombOpenness

/-!
# Structure of gauge transforms in `H^s(B, M_m(ℂ))`: tangentiality
  (stage D1 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `IsWeakTangential.congr_ae` and `IsTangentialS.mul_left` — **weakly tangential `H⁴` fields
  form a module over `H⁴(B)`** (in the Banach-algebra notation);
* `tanM` — the closed subspace of weakly tangential matrix-valued fields, closed under left and
  right multiplication (`tanM_mul_left`, `tanM_mul_right`);
* `IsNeumM X` — `X ∈ H⁵(B, M_m(ℂ))` has weakly tangential gradient; closed under products
  (`IsNeumM.mul`), and **`exp X` is Neumann when `X` is** (`isNeumM_exp`, power series);
* `gaugeAct_tanM` — the gauge transform of a tangential connection by `exp ξ`, `ξ` Neumann, is
  tangential.
-/

open MeasureTheory Set Filter Topology NormedSpace
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator RealInnerProductSpace

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallAlg

open SobolevOpen BallReg SobAlg

set_option linter.unusedSectionVars false

section ScalarModule

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)]

theorem IsWeakTangential.congr_ae {a a' : Fin 4 → (Fin 4 → ℝ) → ℝ} {d d' : (Fin 4 → ℝ) → ℝ}
    (h : IsWeakTangential c r a d) (ha : ∀ ν, a ν =ᵐ[volume.restrict (euclBall c r)] a' ν)
    (hd : d =ᵐ[volume.restrict (euclBall c r)] d') : IsWeakTangential c r a' d' := by
  intro φ hφ
  have h1 := h φ hφ
  have e1 : ∀ ν, ∫ x in euclBall c r, a ν x * pd φ ν x = ∫ x in euclBall c r, a' ν x * pd φ ν x :=
    fun ν => integral_congr_ae ((ha ν).mono fun x hx => by simp only [hx])
  have e2 : ∫ x in euclBall c r, d x * φ x = ∫ x in euclBall c r, d' x * φ x :=
    integral_congr_ae (hd.mono fun x hx => by simp only [hx])
  rw [Finset.sum_congr rfl fun ν _ => e1 ν, e2] at h1
  exact h1

/-- **Weakly tangential `H⁴` fields form a module over `H⁴(B)`.** -/
theorem IsTangentialS.mul_left {a : Fin 4 → SobAlg c r 4} (ha : IsTangentialS a)
    (z : SobAlg c r 4) : IsTangentialS (fun μ => z * a μ) := by
  obtain ⟨M1, hM10, hM1⟩ := exists_common_bound a
  obtain ⟨M2, hM20, hM2⟩ := exists_ae_bound_fn (divS a)
  have h := ha.mul c r (M := max M1 M2) (le_max_of_le_left hM10)
    (fun ν => (memLp_fn _).aestronglyMeasurable) (memLp_fn _).aestronglyMeasurable
    (fun ν => (hM1 ν).mono fun x hx => hx.trans (le_max_left _ _))
    (hM2.mono fun x hx => hx.trans (le_max_right _ _)) (memLp_fn z)
    (fun ν => memLp_fn (derS ν z)) (fun ν => weak_derS ν z)
  refine h.congr_ae (fun ν => ?_) ?_
  · filter_upwards [fn_mul z (a ν)] with x hx
    rw [hx, mul_comm]
  · have h1 := fn_divS (fun μ => z * a μ)
    have h2 : ∀ᵐ x ∂(volume.restrict (euclBall c r)), ∀ ν,
        fn (derS ν (z * a ν)) x = fn (derS ν z) x * fn (a ν) x + fn z x * fn (derS ν (a ν)) x := by
      rw [ae_all_iff]; intro ν
      rw [derS_mul]
      filter_upwards [fn_add (derS ν z * restrS (Nat.le_succ 3) (a ν))
          (restrS (Nat.le_succ 3) z * derS ν (a ν)),
        fn_mul (derS ν z) (restrS (Nat.le_succ 3) (a ν)),
        fn_mul (restrS (Nat.le_succ 3) z) (derS ν (a ν))] with x e1 e2 e3
      rw [e1, e2, e3, fn_restrS, fn_restrS]
    filter_upwards [h1, h2, fn_divS a] with x e1 e2 e3
    rw [e1, e3]
    simp only [e2, Finset.sum_add_distrib, Finset.sum_mul]
    rw [add_comm]
    exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun ν _ => by ring)
      (Finset.sum_congr rfl fun ν _ => by ring)

end ScalarModule

/-! ### Tangential matrix fields -/

/-- The real part as a continuous linear map. -/
def Cx.reL {V : Type*} [NormedCommRing V] [NormedAlgebra ℝ V] : Cx V →L[ℝ] V :=
  LinearMap.mkContinuous
    { toFun := Cx.re
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 fun z => by simpa using Cx.norm_re_le z

theorem Cx.reL_apply {V : Type*} [NormedCommRing V] [NormedAlgebra ℝ V] (z : Cx V) :
    Cx.reL z = z.re := rfl

/-- The imaginary part as a continuous linear map. -/
def Cx.imL {V : Type*} [NormedCommRing V] [NormedAlgebra ℝ V] : Cx V →L[ℝ] V :=
  LinearMap.mkContinuous
    { toFun := Cx.im
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 fun z => by simpa using Cx.norm_im_le z

theorem Cx.imL_apply {V : Type*} [NormedCommRing V] [NormedAlgebra ℝ V] (z : Cx V) :
    Cx.imL z = z.im := rfl

theorem Cx.sum_re {V : Type*} [NormedCommRing V] [NormedAlgebra ℝ V] {ι : Type*} (t : Finset ι)
    (f : ι → Cx V) : (∑ i ∈ t, f i).re = ∑ i ∈ t, (f i).re :=
  map_sum (Cx.reL (V := V)) f t

theorem Cx.sum_im {V : Type*} [NormedCommRing V] [NormedAlgebra ℝ V] {ι : Type*} (t : Finset ι)
    (f : ι → Cx V) : (∑ i ∈ t, f i).im = ∑ i ∈ t, (f i).im :=
  map_sum (Cx.imL (V := V)) f t

set_option backward.isDefEq.respectTransparency false in
/-- Matrix entries as continuous linear maps. -/
def matEntryL {V : Type*} [NormedCommRing V] [NormedAlgebra ℝ V] {m : ℕ} (i j : Fin m) :
    Matrix (Fin m) (Fin m) (Cx V) →L[ℝ] Cx V :=
  LinearMap.mkContinuous
    { toFun := fun M => M i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1 fun M => by
      show ‖M i j‖ ≤ 1 * ‖M‖
      rw [one_mul]; exact norm_entry_le_linfty M i j

section MatTangential

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {m : ℕ}

/-- The real (resp. imaginary) parts of an entry of a matrix vector field, as a continuous linear
map. -/
def entReL (i j : Fin m) : (Fin 4 → MatSob c r 4 m) →L[ℝ] (Fin 4 → SobAlg c r 4) :=
  ContinuousLinearMap.pi fun μ =>
    (Cx.reL (V := SobAlg c r 4)).comp ((matEntryL (V := SobAlg c r 4) i j).comp
      (ContinuousLinearMap.proj μ))

/-- See `entReL`. -/
def entImL (i j : Fin m) : (Fin 4 → MatSob c r 4 m) →L[ℝ] (Fin 4 → SobAlg c r 4) :=
  ContinuousLinearMap.pi fun μ =>
    (Cx.imL (V := SobAlg c r 4)).comp ((matEntryL (V := SobAlg c r 4) i j).comp
      (ContinuousLinearMap.proj μ))

theorem entReL_apply (i j : Fin m) (C : Fin 4 → MatSob c r 4 m) :
    entReL i j C = fun μ => (C μ i j).re := by
  funext μ; rfl

theorem entImL_apply (i j : Fin m) (C : Fin 4 → MatSob c r 4 m) :
    entImL i j C = fun μ => (C μ i j).im := by
  funext μ; rfl

/-- **Weakly tangential matrix fields** (a closed subspace). -/
def tanM (m : ℕ) : Submodule ℝ (Fin 4 → MatSob c r 4 m) :=
  ⨅ (i : Fin m) (j : Fin m), (tanSub (c := c) (r := r)).comap (entReL i j).toLinearMap ⊓
    (tanSub (c := c) (r := r)).comap (entImL i j).toLinearMap

theorem mem_tanM {C : Fin 4 → MatSob c r 4 m} :
    C ∈ tanM (c := c) (r := r) m ↔ ∀ i j, (fun μ => (C μ i j).re) ∈ tanSub (c := c) (r := r) ∧
      (fun μ => (C μ i j).im) ∈ tanSub (c := c) (r := r) := by
  simp only [tanM, Submodule.mem_iInf, Submodule.mem_inf, Submodule.mem_comap]
  constructor
  · intro h i j
    have := h i j
    rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe, entReL_apply,
      entImL_apply] at this
    exact this
  · intro h i j
    rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe, entReL_apply, entImL_apply]
    exact h i j

theorem isClosed_tanM : IsClosed (tanM (c := c) (r := r) m : Set (Fin 4 → MatSob c r 4 m)) := by
  have : (tanM (c := c) (r := r) m : Set (Fin 4 → MatSob c r 4 m)) =
      ⋂ (i : Fin m) (j : Fin m), ((entReL i j) ⁻¹' (tanSub (c := c) (r := r) : Set _) ∩
        (entImL i j) ⁻¹' (tanSub (c := c) (r := r) : Set _)) := by
    ext C; simp [mem_tanM, entReL_apply, entImL_apply]
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    (isClosed_tanSub.preimage (entReL i j).continuous).inter
      (isClosed_tanSub.preimage (entImL i j).continuous)

theorem tanSub_mul_left {a : Fin 4 → SobAlg c r 4} (ha : a ∈ tanSub (c := c) (r := r))
    (z : SobAlg c r 4) : (fun μ => z * a μ) ∈ tanSub (c := c) (r := r) :=
  mem_tanSub.mpr ((mem_tanSub.mp ha).mul_left z)

theorem tanSub_mul_right {a : Fin 4 → SobAlg c r 4} (ha : a ∈ tanSub (c := c) (r := r))
    (z : SobAlg c r 4) : (fun μ => a μ * z) ∈ tanSub (c := c) (r := r) := by
  have := tanSub_mul_left ha z
  simpa [mul_comm] using this

/-- **Left multiplication preserves tangential matrix fields.** -/
theorem tanM_mul_left {C : Fin 4 → MatSob c r 4 m} (hC : C ∈ tanM (c := c) (r := r) m)
    (Z : MatSob c r 4 m) : (fun μ => Z * C μ) ∈ tanM (c := c) (r := r) m := by
  rw [mem_tanM] at hC ⊢
  intro i j
  simp only [Matrix.mul_apply]
  constructor
  · have : (fun μ => (∑ k, Z i k * C μ k j).re) =
        ∑ k, ((fun μ => (Z i k).re * (C μ k j).re) - fun μ => (Z i k).im * (C μ k j).im) := by
      funext μ
      simp only [Finset.sum_apply, Pi.sub_apply, Cx.sum_re, Cx.mul_re]
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.sub_mem _ (tanSub_mul_left (hC k j).1 _)
      (tanSub_mul_left (hC k j).2 _)
  · have : (fun μ => (∑ k, Z i k * C μ k j).im) =
        ∑ k, ((fun μ => (Z i k).re * (C μ k j).im) + fun μ => (Z i k).im * (C μ k j).re) := by
      funext μ
      simp only [Finset.sum_apply, Pi.add_apply, Cx.sum_im, Cx.mul_im]
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.add_mem _ (tanSub_mul_left (hC k j).2 _)
      (tanSub_mul_left (hC k j).1 _)

/-- **Right multiplication preserves tangential matrix fields.** -/
theorem tanM_mul_right {C : Fin 4 → MatSob c r 4 m} (hC : C ∈ tanM (c := c) (r := r) m)
    (Z : MatSob c r 4 m) : (fun μ => C μ * Z) ∈ tanM (c := c) (r := r) m := by
  rw [mem_tanM] at hC ⊢
  intro i j
  simp only [Matrix.mul_apply]
  constructor
  · have : (fun μ => (∑ k, C μ i k * Z k j).re) =
        ∑ k, ((fun μ => (C μ i k).re * (Z k j).re) - fun μ => (C μ i k).im * (Z k j).im) := by
      funext μ
      simp only [Finset.sum_apply, Pi.sub_apply, Cx.sum_re, Cx.mul_re]
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.sub_mem _ (tanSub_mul_right (hC i k).1 _)
      (tanSub_mul_right (hC i k).2 _)
  · have : (fun μ => (∑ k, C μ i k * Z k j).im) =
        ∑ k, ((fun μ => (C μ i k).re * (Z k j).im) + fun μ => (C μ i k).im * (Z k j).re) := by
      funext μ
      simp only [Finset.sum_apply, Pi.add_apply, Cx.sum_im, Cx.mul_im]
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.add_mem _ (tanSub_mul_right (hC i k).1 _)
      (tanSub_mul_right (hC i k).2 _)

/-- The mean of the divergence of a weakly tangential field vanishes. -/
theorem meanS_divS {a : Fin 4 → SobAlg c r 4} (ha : IsTangentialS a) : meanS (divS a) = 0 := by
  have h := ha (fun _ => 1) contDiff_const
  have hpd : ∀ ν, pd (fun _ : Fin 4 → ℝ => (1 : ℝ)) ν = fun _ => 0 := fun ν => by
    funext x; simp [pd]
  simp only [hpd, mul_zero, integral_zero, Finset.sum_const_zero, mul_one] at h
  rw [meanS]
  linarith

/-- `X ∈ H⁵(B, M_m(ℂ))` **has weakly tangential gradient** (the Neumann condition). -/
def IsNeumM (X : MatSob c r 5 m) : Prop := (fun μ => derM μ X) ∈ tanM (c := c) (r := r) m

theorem isNeumM_one : IsNeumM (1 : MatSob c r 5 m) := by
  unfold IsNeumM
  simp only [derM_one]
  exact (tanM (c := c) (r := r) m).zero_mem

theorem IsNeumM.add {X Y : MatSob c r 5 m} (hX : IsNeumM X) (hY : IsNeumM Y) :
    IsNeumM (X + Y) := by
  unfold IsNeumM at *
  simp only [map_add]
  exact (tanM (c := c) (r := r) m).add_mem hX hY

theorem IsNeumM.smul {X : MatSob c r 5 m} (hX : IsNeumM X) (t : ℝ) : IsNeumM (t • X) := by
  unfold IsNeumM at *
  simp only [map_smul]
  exact (tanM (c := c) (r := r) m).smul_mem t hX

theorem IsNeumM.neg {X : MatSob c r 5 m} (hX : IsNeumM X) : IsNeumM (-X) := by
  unfold IsNeumM at *
  simp only [map_neg]
  exact (tanM (c := c) (r := r) m).neg_mem hX

/-- **Products of Neumann fields are Neumann** (Leibniz rule). -/
theorem IsNeumM.mul {X Y : MatSob c r 5 m} (hX : IsNeumM X) (hY : IsNeumM Y) :
    IsNeumM (X * Y) := by
  unfold IsNeumM at *
  simp only [derM_mul]
  exact (tanM (c := c) (r := r) m).add_mem (tanM_mul_right hX _) (tanM_mul_left hY _)

theorem IsNeumM.pow {X : MatSob c r 5 m} (hX : IsNeumM X) : ∀ n : ℕ, IsNeumM (X ^ n)
  | 0 => by simpa using isNeumM_one
  | n + 1 => by rw [pow_succ]; exact (hX.pow n).mul hX

set_option backward.isDefEq.respectTransparency false in
/-- **The exponential of a Neumann field is Neumann** (power series and closedness). -/
theorem isNeumM_exp {X : MatSob c r 5 m} (hX : IsNeumM X) : IsNeumM (exp X) := by
  have hS : Tendsto (fun N => ∑ n ∈ Finset.range N, ((n.factorial : ℝ)⁻¹) • X ^ n) atTop
      (𝓝 (exp X)) := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) X).tendsto_sum_nat
  have hD1 : ∀ μ, Tendsto (fun N => derM (s := 4) μ
      (∑ n ∈ Finset.range N, ((n.factorial : ℝ)⁻¹) • X ^ n)) atTop (𝓝 (derM μ (exp X))) :=
    fun μ => ((derM (s := 4) μ).continuous.tendsto (exp X)).comp hS
  have hD : Tendsto (fun N => fun μ => derM (s := 4) μ
      (∑ n ∈ Finset.range N, ((n.factorial : ℝ)⁻¹) • X ^ n)) atTop
      (𝓝 (fun μ => derM μ (exp X))) := tendsto_pi_nhds.mpr hD1
  refine isClosed_tanM.mem_of_tendsto hD (Eventually.of_forall fun N => ?_)
  have : IsNeumM (∑ n ∈ Finset.range N, ((n.factorial : ℝ)⁻¹) • X ^ n) := by
    induction N with
    | zero =>
      unfold IsNeumM
      simp only [Finset.range_zero, Finset.sum_empty, map_zero]
      exact (tanM (c := c) (r := r) m).zero_mem
    | succ N ih =>
      rw [Finset.sum_range_succ]
      exact ih.add ((hX.pow N).smul _)
  exact this

end MatTangential

/-! ### Gauge transforms of tangential connections are tangential -/

section GaugeTangential

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {m d : ℕ}

theorem embX_mem_tanM (L : LieBasis m d) {t : Fin 4 → Fin d → SobAlg c r 4}
    (ht : t ∈ TSp (c := c) (r := r) d) : (fun μ => embX L (t μ)) ∈ tanM (c := c) (r := r) m := by
  rw [mem_tanM]
  intro i j
  simp only [embX_apply]
  constructor
  · have : (fun μ => ∑ a, (L.e a i j).re • t μ a) = ∑ a, (L.e a i j).re • fun μ => t μ a := by
      funext μ; simp [Finset.sum_apply]
    rw [this]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (ht a)
  · have : (fun μ => ∑ a, (L.e a i j).im • t μ a) = ∑ a, (L.e a i j).im • fun μ => t μ a := by
      funext μ; simp [Finset.sum_apply]
    rw [this]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (ht a)

theorem isNeumM_embX (L : LieBasis m d) {ξ : Fin d → SobAlg c r 5}
    (hξ : ξ ∈ XSp (c := c) (r := r) d) : IsNeumM (embX L ξ) := by
  unfold IsNeumM
  simp only [derM_embX]
  refine embX_mem_tanM L (t := fun μ a => derS μ (ξ a)) fun a => ?_
  have h := (mem_neuSub.mp ((Submodule.mem_pi).mp hξ a (Set.mem_univ a))).1
  rw [mem_tanSub]
  exact h

/-- **The gauge transform `e^ξ·A` of a tangential connection by a Neumann `ξ` is tangential.** -/
theorem gaugeAct_mem_tanM (L : LieBasis m d) {t : Fin 4 → Fin d → SobAlg c r 4}
    (ht : t ∈ TSp (c := c) (r := r) d) {ξ : Fin d → SobAlg c r 5}
    (hξ : ξ ∈ XSp (c := c) (r := r) d) :
    (fun μ => gaugeAct L t ξ μ) ∈ tanM (c := c) (r := r) m := by
  have hg : IsNeumM (exp (embX L ξ)) := isNeumM_exp (isNeumM_embX L hξ)
  unfold gaugeAct
  exact (tanM (c := c) (r := r) m).sub_mem
    (tanM_mul_right (tanM_mul_left (embX_mem_tanM L ht) _) _) (tanM_mul_right hg _)

/-- **Mean zero of the Coulomb functional** at tangential connections and Neumann gauges. -/
theorem meanS_coulF (L : LieBasis m d) {t : Fin 4 → Fin d → SobAlg c r 4}
    (ht : t ∈ TSp (c := c) (r := r) d) {ξ : Fin d → SobAlg c r 5}
    (hξ : ξ ∈ XSp (c := c) (r := r) d) (k : Fin d) : meanS (coulF L (t, ξ) k) = 0 := by
  have hG := mem_tanM.mp (gaugeAct_mem_tanM L ht hξ)
  rw [coulF, coordL_apply]
  have hre : ∀ i j, (∑ μ, derM μ (gaugeAct L t ξ μ)) i j =
      ⟨divS (fun μ => (gaugeAct L t ξ μ i j).re), divS (fun μ => (gaugeAct L t ξ μ i j).im)⟩ := by
    intro i j
    simp only [Matrix.sum_apply, divS]
    ext
    · rw [Cx.sum_re]; rfl
    · rw [Cx.sum_im]; rfl
  simp only [hre]
  rw [meanS_eq_inner, map_sum, inner_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_sum, inner_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_add, inner_add_right, map_smul, map_smul, inner_smul_right, inner_smul_right,
    ← meanS_eq_inner, ← meanS_eq_inner, meanS_divS (mem_tanSub.mp (hG i j).1),
    meanS_divS (mem_tanSub.mp (hG i j).2)]
  simp

/-- **The implicit-function solutions solve the Coulomb equation exactly.** -/
theorem coulF_eq_zero_of_coulIFT (L : LieBasis m d) {p : TSp (c := c) (r := r) d ×
    XSp (c := c) (r := r) d} (hp : coulIFT L p = 0) :
    coulF L ((p.1 : Fin 4 → Fin d → SobAlg c r 4), (p.2 : Fin d → SobAlg c r 5)) = 0 := by
  have h := congrArg Subtype.val hp
  have e : inclTX d p = ((p.1 : Fin 4 → Fin d → SobAlg c r 4), (p.2 : Fin d → SobAlg c r 5)) :=
    rfl
  simp only [coulIFT, e] at h
  rw [projMean_of_mem (fun k => meanS_coulF L p.1.2 p.2.2 k)] at h
  exact h

end GaugeTangential

end RenewalGeometry.BallAnalysis.BallAlg
