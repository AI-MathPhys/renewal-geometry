/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.SlabSobolevAlgebra

/-!
# The slice Sobolev seminorms: Minkowski inequalities and seminormed groups

Generic infrastructure (no renewal notions) for the norms of `prop:coupled-bootstrap` of the
Einstein–Standard-Model action-closure manuscript (`C_tH^k_x`, `L²_tH^k_x` and the initial `H^k`
norm of families of smooth spatially periodic fields on `ℝ × 𝕋³`).

* `quad_minkowski` — if `A + 2λC + λ²B ≥ 0` for all `λ`, then `A + 2C + B ≤ (√A + √B)²`;
* **`sumQ_add_le`** — Minkowski for `Σ_i Q_j(·_i)(t)`:
  `√(Σ_i Q_j(F_i + G_i)(t)) ≤ √(Σ_i Q_j(F_i)(t)) + √(Σ_i Q_j(G_i)(t))`;
* **`intervalL2_add_le`** — Minkowski in `L²(0, T)` for continuous functions;
* `SmoothPer ι` — the real vector space of smooth spatially periodic families `ι → ST d → ℝ`;
  `hkSemi`, `supSemi`, `l2Semi` — the seminorms `√(Σ_i Q_k(F_i)(t₀))`,
  `sup_{t ∈ [0,T]} √(Σ_i Q_k(F_i)(t))`, `(∫₀ᵀ Σ_i Q_k(F_i))^{1/2}`;
* `SemiSpace p` — the seminormed group carried by an additive group seminorm `p`;
* `hkSeminorm`, `NSpace p` — the `H^k` seminorm as a real seminorm and the seminormed real
  vector space it carries.
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.SlabSemi

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg

set_option linter.unusedSectionVars false

/-- **The quadratic Minkowski lemma**: if `A + 2λC + λ²B ≥ 0` for all real `λ` (`A, B ≥ 0`), then
`A + 2C + B ≤ (√A + √B)²`. -/
theorem quad_minkowski {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ l : ℝ, 0 ≤ A + 2 * l * C + l ^ 2 * B) : A + 2 * C + B ≤ (Real.sqrt A + Real.sqrt B) ^ 2 := by
  have hd := discrim_le_zero (a := B) (b := 2 * C) (c := A) fun x => by
    have := h x; nlinarith
  rw [discrim] at hd
  have hC : C ≤ Real.sqrt A * Real.sqrt B := by
    have h1 : C ^ 2 ≤ A * B := by nlinarith
    rw [← Real.sqrt_mul hA]
    exact (le_abs_self C).trans (Real.abs_le_sqrt h1)
  have hsA := Real.sq_sqrt hA
  have hsB := Real.sq_sqrt hB
  nlinarith

variable {d : ℕ}

/-- `∫ (sd F + λ sd G)²` expanded. -/
theorem integral_sq_lincomb {f g : ST d → ℝ} (hf : Continuous f) (hg : Continuous g) (l t : ℝ) :
    ∫ y in Icc (0 : Fin d → ℝ) 1, (f (Fin.cons t y) + l * g (Fin.cons t y)) ^ 2 =
      (∫ y in Icc (0 : Fin d → ℝ) 1, f (Fin.cons t y) ^ 2) +
        2 * l * (∫ y in Icc (0 : Fin d → ℝ) 1, f (Fin.cons t y) * g (Fin.cons t y)) +
        l ^ 2 * (∫ y in Icc (0 : Fin d → ℝ) 1, g (Fin.cons t y) ^ 2) := by
  have i1 := integrableOn_sq hf t
  have i2 := integrableOn_sq hg t
  have i3 : IntegrableOn (fun y : Fin d → ℝ => f (Fin.cons t y) * g (Fin.cons t y)) (Icc 0 1) :=
    integrableOn_slice (f := fun x => f x * g x) (hf.mul hg) t
  have e : ∀ y : Fin d → ℝ, (f (Fin.cons t y) + l * g (Fin.cons t y)) ^ 2 =
      f (Fin.cons t y) ^ 2 + (2 * l) * (f (Fin.cons t y) * g (Fin.cons t y)) +
        l ^ 2 * g (Fin.cons t y) ^ 2 := fun y => by ring
  simp_rw [e]
  have j1 : Integrable (fun y : Fin d → ℝ => f (Fin.cons t y) ^ 2 +
      (2 * l) * (f (Fin.cons t y) * g (Fin.cons t y))) (volume.restrict (Icc 0 1)) :=
    i1.add (i3.const_mul _)
  rw [integral_add j1 (i2.const_mul _), integral_add i1 (i3.const_mul _), integral_const_mul,
    integral_const_mul]

/-- **Minkowski for sums of slice norms**:
`Σ_i Q_j(F_i + G_i)(t) ≤ (√(Σ_i Q_j(F_i)(t)) + √(Σ_i Q_j(G_i)(t)))²`. -/
theorem sumQ_add_le {ι : Type*} [Fintype ι] (j : ℕ) {F G : ι → ST d → ℝ}
    (hF : ∀ i, ContDiff ℝ ∞ (F i)) (hG : ∀ i, ContDiff ℝ ∞ (G i)) (t : ℝ) :
    ∑ i, Q j (fun x => F i x + G i x) t ≤
      (Real.sqrt (∑ i, Q j (F i) t) + Real.sqrt (∑ i, Q j (G i) t)) ^ 2 := by
  set C := ∑ i, ∑ w ∈ wordsLE d j, ∫ y in Icc (0 : Fin d → ℝ) 1,
    sd w (F i) (Fin.cons t y) * sd w (G i) (Fin.cons t y) with hC
  have hexp : ∀ l : ℝ, ∑ i, Q j (fun x => F i x + l * G i x) t =
      ∑ i, Q j (F i) t + 2 * l * C + l ^ 2 * ∑ i, Q j (G i) t := by
    intro l
    have : ∀ i, Q j (fun x => F i x + l * G i x) t = Q j (F i) t +
        2 * l * (∑ w ∈ wordsLE d j, ∫ y in Icc (0 : Fin d → ℝ) 1,
          sd w (F i) (Fin.cons t y) * sd w (G i) (Fin.cons t y)) + l ^ 2 * Q j (G i) t := by
      intro i
      unfold Q
      have hsd : ∀ w, sd w (fun x => F i x + l * G i x) = fun x => sd w (F i) x + l * sd w (G i) x :=
        fun w => by
          have := sd_lincomb w (hF i) (hG i) 1 l
          simpa only [one_mul] using this
      simp_rw [hsd]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun w _ => ?_
      exact integral_sq_lincomb (contDiff_sd w (hF i)).continuous (contDiff_sd w (hG i)).continuous l t
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hC]
  have hA : 0 ≤ ∑ i, Q j (F i) t := Finset.sum_nonneg fun i _ => Q_nonneg _ _ _
  have hB : 0 ≤ ∑ i, Q j (G i) t := Finset.sum_nonneg fun i _ => Q_nonneg _ _ _
  have h := quad_minkowski hA hB fun l => by
    rw [← hexp l]; exact Finset.sum_nonneg fun i _ => Q_nonneg _ _ _
  have h1 := hexp 1
  simp only [one_mul, one_pow] at h1
  rw [h1]
  linarith

theorem sqrt_sumQ_add_le {ι : Type*} [Fintype ι] (j : ℕ) {F G : ι → ST d → ℝ}
    (hF : ∀ i, ContDiff ℝ ∞ (F i)) (hG : ∀ i, ContDiff ℝ ∞ (G i)) (t : ℝ) :
    Real.sqrt (∑ i, Q j (fun x => F i x + G i x) t) ≤
      Real.sqrt (∑ i, Q j (F i) t) + Real.sqrt (∑ i, Q j (G i) t) :=
  Real.sqrt_le_iff.2 ⟨by positivity, sumQ_add_le j hF hG t⟩

/-- **Minkowski in `L²(0, T)`** for continuous functions. -/
theorem intervalL2_add_le {a b : ℝ → ℝ} (ha : Continuous a) (hb : Continuous b) {T : ℝ}
    (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, (a t + b t) ^ 2 ≤
      (Real.sqrt (∫ t in (0 : ℝ)..T, a t ^ 2) + Real.sqrt (∫ t in (0 : ℝ)..T, b t ^ 2)) ^ 2 := by
  have hexp : ∀ l : ℝ, ∫ t in (0 : ℝ)..T, (a t + l * b t) ^ 2 =
      (∫ t in (0 : ℝ)..T, a t ^ 2) + 2 * l * (∫ t in (0 : ℝ)..T, a t * b t) +
        l ^ 2 * ∫ t in (0 : ℝ)..T, b t ^ 2 := by
    intro l
    have e : ∀ t, (a t + l * b t) ^ 2 = a t ^ 2 + (2 * l) * (a t * b t) + l ^ 2 * b t ^ 2 :=
      fun t => by ring
    simp_rw [e]
    have i1 : IntervalIntegrable (fun t => a t ^ 2) volume 0 T := (ha.pow 2).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun t => b t ^ 2) volume 0 T := (hb.pow 2).intervalIntegrable _ _
    have i3 : IntervalIntegrable (fun t => a t * b t) volume 0 T :=
      (ha.mul hb).intervalIntegrable _ _
    rw [intervalIntegral.integral_add (i1.add (i3.const_mul _)) (i2.const_mul _),
      intervalIntegral.integral_add i1 (i3.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have hA : 0 ≤ ∫ t in (0 : ℝ)..T, a t ^ 2 := intervalIntegral.integral_nonneg hT fun t _ => sq_nonneg _
  have hB : 0 ≤ ∫ t in (0 : ℝ)..T, b t ^ 2 := intervalIntegral.integral_nonneg hT fun t _ => sq_nonneg _
  have h := quad_minkowski hA hB fun l => by
    rw [← hexp l]; exact intervalIntegral.integral_nonneg hT fun t _ => sq_nonneg _
  have h1 := hexp 1
  simp only [one_mul, one_pow] at h1
  rw [h1]
  linarith


/-! ### Smooth periodic families and their seminorms -/

variable {ι : Type*} [Fintype ι]

variable (d ι) in
/-- The real vector space of smooth spatially periodic families `ι → ST d → ℝ`. -/
def SmoothPer : Submodule ℝ (ι → ST d → ℝ) where
  carrier := {F | ∀ i, ContDiff ℝ ∞ (F i) ∧ IsSPeriodic (F i)}
  add_mem' {F G} hF hG i := ⟨(hF i).1.add (hG i).1, fun k x => by
    simp only [Pi.add_apply, (hF i).2 k x, (hG i).2 k x]⟩
  zero_mem' i := ⟨contDiff_const, fun _ _ => rfl⟩
  smul_mem' c {F} hF i := ⟨(hF i).1.const_smul c, fun k x => by
    simp only [Pi.smul_apply, (hF i).2 k x]⟩

/-- `Σ_i Q_j(F_i)(t)`. -/
def sumQ (j : ℕ) (F : ι → ST d → ℝ) (t : ℝ) : ℝ := ∑ i, Q j (F i) t

theorem sumQ_nonneg (j : ℕ) (F : ι → ST d → ℝ) (t : ℝ) : 0 ≤ sumQ j F t :=
  Finset.sum_nonneg fun i _ => Q_nonneg _ _ _

theorem sumQ_zero (j : ℕ) (t : ℝ) : sumQ j (0 : ι → ST d → ℝ) t = 0 := by
  unfold sumQ
  refine Finset.sum_eq_zero fun i _ => ?_
  have h : Q j (fun _ : ST d => (0 : ℝ)) t = 0 := by simpa using Q_const (d := d) j 0 t
  exact h

theorem sumQ_neg (j : ℕ) {F : ι → ST d → ℝ} (hF : ∀ i, ContDiff ℝ ∞ (F i)) (t : ℝ) :
    sumQ j (-F) t = sumQ j F t := by
  unfold sumQ
  exact Finset.sum_congr rfl fun i _ => Q_neg j (hF i) t

theorem sqrt_sumQ_add (j : ℕ) {F G : ι → ST d → ℝ} (hF : ∀ i, ContDiff ℝ ∞ (F i))
    (hG : ∀ i, ContDiff ℝ ∞ (G i)) (t : ℝ) :
    Real.sqrt (sumQ j (F + G) t) ≤ Real.sqrt (sumQ j F t) + Real.sqrt (sumQ j G t) :=
  sqrt_sumQ_add_le j hF hG t

theorem continuous_sumQ (j : ℕ) {F : ι → ST d → ℝ} (hF : ∀ i, ContDiff ℝ ∞ (F i)) :
    Continuous (sumQ j F) :=
  continuous_finsetSum _ fun i _ => continuous_Q j (hF i)

/-- **The `H^k` seminorm at a fixed time** `√(Σ_i Q_k(F_i)(t₀))`. -/
def hkSemi (k : ℕ) (t₀ : ℝ) : AddGroupSeminorm (SmoothPer d ι) where
  toFun F := Real.sqrt (sumQ k F.1 t₀)
  map_zero' := by simp only [ZeroMemClass.coe_zero, sumQ_zero, Real.sqrt_zero]
  add_le' F G := sqrt_sumQ_add k (fun i => (F.2 i).1) (fun i => (G.2 i).1) t₀
  neg' F := by
    show Real.sqrt (sumQ k (-F.1) t₀) = _
    rw [sumQ_neg k (fun i => (F.2 i).1)]

theorem sumQ_smul (j : ℕ) {F : ι → ST d → ℝ} (hF : ∀ i, ContDiff ℝ ∞ (F i)) (c t : ℝ) :
    sumQ j (c • F) t = c ^ 2 * sumQ j F t := by
  unfold sumQ
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Q_const_mul j (hF i) c t

/-- The `H^k` seminorm at a fixed time as a real seminorm (homogeneity from `Q_const_mul`). -/
def hkSeminorm (k : ℕ) (t₀ : ℝ) : Seminorm ℝ (SmoothPer d ι) :=
  { hkSemi k t₀ with
    smul' := fun c F => by
      show Real.sqrt (sumQ k (c • F.1) t₀) = ‖c‖ * Real.sqrt (sumQ k F.1 t₀)
      rw [sumQ_smul k (fun i => (F.2 i).1), Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs,
        Real.norm_eq_abs] }

theorem hkSeminorm_apply (k : ℕ) (t₀ : ℝ) (F : SmoothPer d ι) :
    hkSeminorm k t₀ F = Real.sqrt (sumQ k F.1 t₀) := rfl

/-- **The `C_tH^k_x` seminorm** `sup_{t ∈ [0, T]} √(Σ_i Q_k(F_i)(t))`. -/
def supSemi (k : ℕ) (T : ℝ) (hT : 0 ≤ T) : AddGroupSeminorm (SmoothPer d ι) where
  toFun F := sSup ((fun t => Real.sqrt (sumQ k F.1 t)) '' Icc 0 T)
  map_zero' := by
    have : (fun t => Real.sqrt (sumQ k ((0 : SmoothPer d ι) : ι → ST d → ℝ) t)) '' Icc 0 T =
        {0} := by
      ext r
      simp only [ZeroMemClass.coe_zero, sumQ_zero, Real.sqrt_zero, mem_image, mem_singleton_iff]
      exact ⟨fun ⟨_, _, h⟩ => h.symm, fun h => ⟨0, ⟨le_rfl, hT⟩, h.symm⟩⟩
    rw [this, csSup_singleton]
  add_le' F G := by
    have hne : (Icc (0 : ℝ) T).Nonempty := ⟨0, le_rfl, hT⟩
    have hbdd : ∀ H : SmoothPer d ι,
        BddAbove ((fun t => Real.sqrt (sumQ k H.1 t)) '' Icc 0 T) := fun H =>
      isCompact_Icc.bddAbove_image
        (Real.continuous_sqrt.comp (continuous_sumQ k fun i => (H.2 i).1)).continuousOn
    refine csSup_le (hne.image _) ?_
    rintro r ⟨t, ht, rfl⟩
    refine (sqrt_sumQ_add k (fun i => (F.2 i).1) (fun i => (G.2 i).1) t).trans ?_
    exact add_le_add (le_csSup (hbdd F) ⟨t, ht, rfl⟩) (le_csSup (hbdd G) ⟨t, ht, rfl⟩)
  neg' F := by
    show sSup ((fun t => Real.sqrt (sumQ k (-F.1) t)) '' Icc 0 T) = _
    simp only [sumQ_neg k (fun i => (F.2 i).1)]

theorem le_supSemi (k : ℕ) {T : ℝ} (hT : 0 ≤ T) (F : SmoothPer d ι) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Real.sqrt (sumQ k F.1 t) ≤ supSemi k T hT F :=
  le_csSup (isCompact_Icc.bddAbove_image
    (Real.continuous_sqrt.comp (continuous_sumQ k fun i => (F.2 i).1)).continuousOn) ⟨t, ht, rfl⟩

theorem supSemi_le (k : ℕ) {T : ℝ} (hT : 0 ≤ T) (F : SmoothPer d ι) {B : ℝ}
    (h : ∀ t ∈ Icc 0 T, Real.sqrt (sumQ k F.1 t) ≤ B) : supSemi k T hT F ≤ B :=
  csSup_le (Set.Nonempty.image _ (⟨0, le_rfl, hT⟩ : (Icc (0 : ℝ) T).Nonempty)) fun _ ⟨t, ht, e⟩ => e ▸ h t ht

/-- **The `L²_tH^k_x` seminorm** `(∫₀ᵀ Σ_i Q_k(F_i))^{1/2}`. -/
def l2Semi (k : ℕ) (T : ℝ) (hT : 0 ≤ T) : AddGroupSeminorm (SmoothPer d ι) where
  toFun F := Real.sqrt (∫ t in (0 : ℝ)..T, sumQ k F.1 t)
  map_zero' := by simp only [ZeroMemClass.coe_zero, sumQ_zero, intervalIntegral.integral_zero,
    Real.sqrt_zero]
  add_le' F G := by
    have hF := fun i => (F.2 i).1
    have hG := fun i => (G.2 i).1
    have ha : Continuous fun t => Real.sqrt (sumQ k F.1 t) :=
      Real.continuous_sqrt.comp (continuous_sumQ k hF)
    have hb : Continuous fun t => Real.sqrt (sumQ k G.1 t) :=
      Real.continuous_sqrt.comp (continuous_sumQ k hG)
    have h1 : ∫ t in (0 : ℝ)..T, sumQ k (F.1 + G.1) t ≤
        ∫ t in (0 : ℝ)..T, (Real.sqrt (sumQ k F.1 t) + Real.sqrt (sumQ k G.1 t)) ^ 2 :=
      intervalIntegral.integral_mono_on hT
        ((continuous_sumQ k fun i => (hF i).add (hG i)).intervalIntegrable _ _)
        ((ha.add hb).pow 2 |>.intervalIntegrable _ _) fun t _ => by
          have h := sqrt_sumQ_add k hF hG t
          calc sumQ k (F.1 + G.1) t = Real.sqrt (sumQ k (F.1 + G.1) t) ^ 2 :=
                (Real.sq_sqrt (sumQ_nonneg k _ t)).symm
            _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
    have h2 := intervalL2_add_le ha hb hT
    have e : ∀ (H : ι → ST d → ℝ), (∀ i, ContDiff ℝ ∞ (H i)) →
        ∫ t in (0 : ℝ)..T, Real.sqrt (sumQ k H t) ^ 2 = ∫ t in (0 : ℝ)..T, sumQ k H t :=
      fun H _ => intervalIntegral.integral_congr fun t _ => Real.sq_sqrt (sumQ_nonneg k H t)
    rw [e _ hF, e _ hG] at h2
    exact Real.sqrt_le_iff.2 ⟨by positivity, h1.trans h2⟩
  neg' F := by
    show Real.sqrt (∫ t in (0 : ℝ)..T, sumQ k (-F.1) t) = _
    simp only [sumQ_neg k (fun i => (F.2 i).1)]


/-! ### The seminormed group carried by an additive group seminorm -/

/-- A type synonym of `G` carrying the seminormed group structure of the seminorm `p`. -/
def SemiSpace {G : Type*} [AddCommGroup G] (_p : AddGroupSeminorm G) : Type _ := G

instance {G : Type*} [AddCommGroup G] (p : AddGroupSeminorm G) :
    SeminormedAddCommGroup (SemiSpace p) :=
  p.toSeminormedAddCommGroup

/-- The canonical map `G → SemiSpace p`. -/
def SemiSpace.of {G : Type*} [AddCommGroup G] (p : AddGroupSeminorm G) (x : G) : SemiSpace p := x

theorem SemiSpace.norm_of {G : Type*} [AddCommGroup G] (p : AddGroupSeminorm G) (x : G) :
    ‖SemiSpace.of p x‖ = p x := rfl

theorem SemiSpace.of_sub {G : Type*} [AddCommGroup G] (p : AddGroupSeminorm G) (x y : G) :
    SemiSpace.of p (x - y) = SemiSpace.of p x - SemiSpace.of p y := rfl

theorem SemiSpace.dist_of {G : Type*} [AddCommGroup G] (p : AddGroupSeminorm G) (x y : G) :
    dist (SemiSpace.of p x) (SemiSpace.of p y) = p (x - y) := by
  rw [dist_eq_norm, ← SemiSpace.of_sub, SemiSpace.norm_of]


/-! ### The seminormed real vector space carried by a seminorm -/

/-- A type synonym of `G` carrying the seminormed space structure of the real seminorm `p`. -/
def NSpace {G : Type*} [AddCommGroup G] [Module ℝ G] (_p : Seminorm ℝ G) : Type _ := G

instance {G : Type*} [AddCommGroup G] [Module ℝ G] (p : Seminorm ℝ G) :
    SeminormedAddCommGroup (NSpace p) :=
  p.toAddGroupSeminorm.toSeminormedAddCommGroup

instance {G : Type*} [AddCommGroup G] [Module ℝ G] (p : Seminorm ℝ G) : Module ℝ (NSpace p) :=
  inferInstanceAs (Module ℝ G)

instance {G : Type*} [AddCommGroup G] [Module ℝ G] (p : Seminorm ℝ G) :
    NormedSpace ℝ (NSpace p) where
  norm_smul_le c x := (map_smul_eq_mul p c (show G from x)).le

/-- The canonical map `G → NSpace p`. -/
def NSpace.of {G : Type*} [AddCommGroup G] [Module ℝ G] (p : Seminorm ℝ G) (x : G) : NSpace p := x

theorem NSpace.norm_of {G : Type*} [AddCommGroup G] [Module ℝ G] (p : Seminorm ℝ G) (x : G) :
    ‖NSpace.of p x‖ = p x := rfl

theorem NSpace.of_sub {G : Type*} [AddCommGroup G] [Module ℝ G] (p : Seminorm ℝ G) (x y : G) :
    NSpace.of p (x - y) = NSpace.of p x - NSpace.of p y := rfl

end RenewalGeometry.SlabSemi
