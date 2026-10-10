/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallSobolevNormedAlgebra

/-!
# Derivatives, restrictions and smooth elements of the Banach algebras `H^s(B)`
  (stage D1b of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `restrJ`, `derJ` — restriction `H^s(B) → H^{s'}(B)` (`s' ≤ s`) and the partial derivative
  `∂_i : H^{s+1}(B) → H^s(B)` on jets (norm `≤ 1`);
* `SobAlg.restrL`, `SobAlg.derL` — the same as continuous linear maps of the Banach algebras;
  `restrL` is multiplicative (`restrL_mul`) and **`derL` is a derivation**
  (`derL_mul`: `∂(F G) = ∂F · G + F · ∂G`), from the product rule for weak derivatives of
  products in `H^{s+1}(B)` (`weak_mul_of_tendsto`, via smooth approximation);
* `SobAlg.ofSmooth` — smooth functions as elements, `derL_ofSmooth`, `exists_tendsto_ofSmooth`
  (density of smooth functions), `SobAlg.meanL` — the integral over the ball as a continuous
  linear functional.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallAlg

open SobolevOpen BallReg

set_option linter.unusedSectionVars false

/-! ### `L¹` convergence of products -/

section L1

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

/-- Products of `L²`-convergent sequences converge in `L¹`. -/
theorem tendsto_eLpNorm_one_mul {a b : ℕ → α → ℝ} {a0 b0 : α → ℝ}
    (ham : ∀ m, AEStronglyMeasurable (a m) μ) (hbm : ∀ m, AEStronglyMeasurable (b m) μ)
    (ha0 : MemLp a0 2 μ) (hb0 : MemLp b0 2 μ)
    (ha : Tendsto (fun m => eLpNorm (a m - a0) 2 μ) atTop (𝓝 0))
    (hb : Tendsto (fun m => eLpNorm (b m - b0) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun m => eLpNorm (fun x => a m x * b m x - a0 x * b0 x) 1 μ) atTop (𝓝 0) := by
  have hbound : ∀ m, eLpNorm (fun x => a m x * b m x - a0 x * b0 x) 1 μ ≤
      eLpNorm (a m - a0) 2 μ * (eLpNorm (b m - b0) 2 μ + eLpNorm b0 2 μ) +
        eLpNorm a0 2 μ * eLpNorm (b m - b0) 2 μ := by
    intro m
    have e2 : (fun x => a m x * b m x - a0 x * b0 x) = (a m - a0) • b m + a0 • (b m - b0) := by
      funext x; simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, smul_eq_mul]; ring
    rw [e2]
    refine (eLpNorm_add_le (((ham m).sub ha0.aestronglyMeasurable).smul (hbm m))
      (ha0.aestronglyMeasurable.smul ((hbm m).sub hb0.aestronglyMeasurable)) le_rfl).trans ?_
    gcongr
    · refine (eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) (hbm m)
        ((ham m).sub ha0.aestronglyMeasurable)).trans ?_
      gcongr
      have e : b m = (b m - b0) + b0 := by funext x; simp
      conv_lhs => rw [e]
      exact eLpNorm_add_le ((hbm m).sub hb0.aestronglyMeasurable) hb0.aestronglyMeasurable
        (by norm_num)
    · exact eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
        ((hbm m).sub hb0.aestronglyMeasurable) ha0.aestronglyMeasurable
  have hlim : Tendsto (fun m => eLpNorm (a m - a0) 2 μ * (eLpNorm (b m - b0) 2 μ +
      eLpNorm b0 2 μ) + eLpNorm a0 2 μ * eLpNorm (b m - b0) 2 μ) atTop (𝓝 0) := by
    have t2 : Tendsto (fun m => eLpNorm (b m - b0) 2 μ + eLpNorm b0 2 μ) atTop
        (𝓝 (eLpNorm b0 2 μ)) := by
      simpa using hb.add (tendsto_const_nhds (x := eLpNorm b0 2 μ))
    have t3 := ENNReal.Tendsto.mul ha (Or.inr hb0.eLpNorm_lt_top.ne) t2
      (Or.inr ENNReal.zero_ne_top)
    have t4 := ENNReal.Tendsto.const_mul hb (Or.inr ha0.eLpNorm_lt_top.ne)
    simpa using t3.add t4
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le) hbound

/-- **Identification of `L²` limits of sums of products**: if `a_m b_m + a'_m b'_m → w` in `L²`
and the factors converge in `L²`, then `w = a b + a' b'` a.e. -/
theorem ae_eq_of_tendsto_mul_add {a b a' b' : ℕ → α → ℝ} {a0 b0 a0' b0' w : α → ℝ}
    (ham : ∀ m, AEStronglyMeasurable (a m) μ) (hbm : ∀ m, AEStronglyMeasurable (b m) μ)
    (ham' : ∀ m, AEStronglyMeasurable (a' m) μ) (hbm' : ∀ m, AEStronglyMeasurable (b' m) μ)
    (ha0 : MemLp a0 2 μ) (hb0 : MemLp b0 2 μ) (ha0' : MemLp a0' 2 μ) (hb0' : MemLp b0' 2 μ)
    (hw : MemLp w 2 μ)
    (ha : Tendsto (fun m => eLpNorm (a m - a0) 2 μ) atTop (𝓝 0))
    (hb : Tendsto (fun m => eLpNorm (b m - b0) 2 μ) atTop (𝓝 0))
    (ha' : Tendsto (fun m => eLpNorm (a' m - a0') 2 μ) atTop (𝓝 0))
    (hb' : Tendsto (fun m => eLpNorm (b' m - b0') 2 μ) atTop (𝓝 0))
    (hc : Tendsto (fun m => eLpNorm ((fun x => a m x * b m x + a' m x * b' m x) - w) 2 μ)
      atTop (𝓝 0)) :
    w =ᵐ[μ] fun x => a0 x * b0 x + a0' x * b0' x := by
  set V : ℝ≥0∞ := μ Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)
  have hVt : V ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _)
  have hcm : ∀ m, AEStronglyMeasurable (fun x => a m x * b m x + a' m x * b' m x) μ :=
    fun m => ((ham m).mul (hbm m)).add ((ham' m).mul (hbm' m))
  have hT := tendsto_eLpNorm_one_mul ham hbm ha0 hb0 ha hb
  have hT' := tendsto_eLpNorm_one_mul ham' hbm' ha0' hb0' ha' hb'
  have hlim : Tendsto (fun m => eLpNorm ((fun x => a m x * b m x + a' m x * b' m x) - w) 2 μ * V +
      (eLpNorm (fun x => a m x * b m x - a0 x * b0 x) 1 μ +
        eLpNorm (fun x => a' m x * b' m x - a0' x * b0' x) 1 μ)) atTop (𝓝 0) := by
    have t1 := ENNReal.Tendsto.mul_const hc (Or.inr hVt)
    simpa using t1.add (hT.add hT')
  have hP0 : AEStronglyMeasurable (fun x => a0 x * b0 x + a0' x * b0' x) μ :=
    (ha0.aestronglyMeasurable.mul hb0.aestronglyMeasurable).add
      (ha0'.aestronglyMeasurable.mul hb0'.aestronglyMeasurable)
  have hbound : ∀ m, eLpNorm (w - fun x => a0 x * b0 x + a0' x * b0' x) 1 μ ≤
      eLpNorm ((fun x => a m x * b m x + a' m x * b' m x) - w) 2 μ * V +
        (eLpNorm (fun x => a m x * b m x - a0 x * b0 x) 1 μ +
          eLpNorm (fun x => a' m x * b' m x - a0' x * b0' x) 1 μ) := by
    intro m
    have e1 : (w - fun x => a0 x * b0 x + a0' x * b0' x) =
        (w - fun x => a m x * b m x + a' m x * b' m x) +
          ((fun x => a m x * b m x - a0 x * b0 x) + fun x => a' m x * b' m x - a0' x * b0' x) := by
      funext x; simp only [Pi.sub_apply, Pi.add_apply]; ring
    rw [e1]
    refine (eLpNorm_add_le (hw.aestronglyMeasurable.sub (hcm m))
      ((((ham m).mul (hbm m)).sub (ha0.aestronglyMeasurable.mul hb0.aestronglyMeasurable)).add
        (((ham' m).mul (hbm' m)).sub (ha0'.aestronglyMeasurable.mul hb0'.aestronglyMeasurable)))
      le_rfl).trans ?_
    gcongr
    · rw [eLpNorm_sub_comm]
      exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num)
        ((hcm m).sub hw.aestronglyMeasurable)
    · exact eLpNorm_add_le (((ham m).mul (hbm m)).sub
        (ha0.aestronglyMeasurable.mul hb0.aestronglyMeasurable))
        (((ham' m).mul (hbm' m)).sub (ha0'.aestronglyMeasurable.mul hb0'.aestronglyMeasurable))
        le_rfl
  have h0 : eLpNorm (w - fun x => a0 x * b0 x + a0' x * b0' x) 1 μ = 0 :=
    le_antisymm (ge_of_tendsto' hlim hbound) bot_le
  have hae := (eLpNorm_eq_zero_iff (hw.aestronglyMeasurable.sub hP0) one_ne_zero).mp h0
  exact hae.mono fun x hx => sub_eq_zero.mp hx

end L1

/-! ### Restriction and derivative of jets -/

section JetMaps

variable {n : ℕ} [NeZero n] (c : Fin n → ℝ) (r : ℝ) [hr : Fact (0 < r)]

/-- Reindexing of `ℓ²` products along an injection does not increase the norm. -/
theorem norm_piLp_comp_le {ι κ : Type*} [Fintype ι] [Fintype κ] {E : Type*}
    [NormedAddCommGroup E] (e : κ → ι) (he : Function.Injective e) (x : PiLp 2 fun _ : ι => E) :
    ‖(WithLp.toLp 2 fun k => x (e k) : PiLp 2 fun _ : κ => E)‖ ≤ ‖x‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  refine Real.sqrt_le_sqrt ?_
  classical
  rw [← Finset.sum_image (f := fun i => ‖x i‖ ^ 2) (fun a _ b _ h => he h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity

theorem mem_wordsUpTo_mono {s s' : ℕ} (h : s' ≤ s) {w : List (Fin n)} (hw : w ∈ wordsUpTo n s') :
    w ∈ wordsUpTo n s := mem_wordsUpTo.mpr ((mem_wordsUpTo.mp hw).trans h)

theorem mem_wordsUpTo_append {s : ℕ} (i : Fin n) {w : List (Fin n)} (hw : w ∈ wordsUpTo n s) :
    w ++ [i] ∈ wordsUpTo n (s + 1) := mem_wordsUpTo.mpr (by
  have := mem_wordsUpTo.mp hw; simp; omega)

/-- Restriction of jets to shorter words. -/
def restrJet {s s' : ℕ} (h : s' ≤ s) (F : JetAmb c r s) : JetAmb c r s' :=
  WithLp.toLp 2 fun w => F ⟨w.1, mem_wordsUpTo_mono h w.2⟩

/-- Derivative of jets: component `w` of `∂_i F` is component `w ++ [i]` of `F`. -/
def derJet {s : ℕ} (i : Fin n) (F : JetAmb c r (s + 1)) : JetAmb c r s :=
  WithLp.toLp 2 fun w => F ⟨w.1 ++ [i], mem_wordsUpTo_append i w.2⟩

theorem restrJet_mem {s s' : ℕ} (h : s' ≤ s) {F : JetAmb c r s} (hF : F ∈ HsB c r s) :
    restrJet c r h F ∈ HsB c r s' := fun w j hj => hF ⟨w.1, mem_wordsUpTo_mono h w.2⟩ j
  (mem_wordsUpTo_mono h hj)

theorem derJet_mem {s : ℕ} (i : Fin n) {F : JetAmb c r (s + 1)} (hF : F ∈ HsB c r (s + 1)) :
    derJet c r i F ∈ HsB c r s := fun w j hj =>
  hF ⟨w.1 ++ [i], mem_wordsUpTo_append i w.2⟩ j (mem_wordsUpTo_append i hj)

theorem norm_restrJet_le {s s' : ℕ} (h : s' ≤ s) (F : JetAmb c r s) :
    ‖restrJet c r h F‖ ≤ ‖F‖ :=
  norm_piLp_comp_le (fun w : ↥(wordsUpTo n s') => (⟨w.1, mem_wordsUpTo_mono h w.2⟩ :
    ↥(wordsUpTo n s))) (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)) F

theorem norm_derJet_le {s : ℕ} (i : Fin n) (F : JetAmb c r (s + 1)) :
    ‖derJet c r i F‖ ≤ ‖F‖ :=
  norm_piLp_comp_le (fun w : ↥(wordsUpTo n s) => (⟨w.1 ++ [i], mem_wordsUpTo_append i w.2⟩ :
    ↥(wordsUpTo n (s + 1)))) (fun a b hab => Subtype.ext (by
      have := congrArg Subtype.val hab
      simpa using this)) F

/-- Restriction as a continuous linear map of the Hilbert spaces. -/
def restrL {s s' : ℕ} (h : s' ≤ s) : HsB c r s →L[ℝ] HsB c r s' :=
  LinearMap.mkContinuous
    { toFun := fun F => ⟨restrJet c r h F, restrJet_mem c r h F.2⟩
      map_add' := fun F G => rfl
      map_smul' := fun a F => rfl } 1 fun F => by
    show ‖restrJet c r h (F : JetAmb c r s)‖ ≤ 1 * ‖(F : JetAmb c r s)‖
    rw [one_mul]; exact norm_restrJet_le c r h (F : JetAmb c r s)

/-- The partial derivative as a continuous linear map of the Hilbert spaces. -/
def derL {s : ℕ} (i : Fin n) : HsB c r (s + 1) →L[ℝ] HsB c r s :=
  LinearMap.mkContinuous
    { toFun := fun F => ⟨derJet c r i F, derJet_mem c r i F.2⟩
      map_add' := fun F G => rfl
      map_smul' := fun a F => rfl } 1 fun F => by
    show ‖derJet c r i (F : JetAmb c r (s + 1))‖ ≤ 1 * ‖(F : JetAmb c r (s + 1))‖
    rw [one_mul]; exact norm_derJet_le c r i (F : JetAmb c r (s + 1))

theorem restrL_apply_nil {s s' : ℕ} (h : s' ≤ s) (F : HsB c r s) :
    ((restrL c r h F : HsB c r s') : JetAmb c r s') (nilW s') = (F : JetAmb c r s) (nilW s) := rfl

theorem derL_apply_nil {s : ℕ} (i : Fin n) (F : HsB c r (s + 1)) :
    ((derL c r i F : HsB c r s) : JetAmb c r s) (nilW s) =
      (F : JetAmb c r (s + 1)) ⟨[i], mem_wordsUpTo.mpr (by simp)⟩ := rfl

/-- The function component of `∂_i F` is the weak `i`-th derivative of that of `F`. -/
theorem weak_derL {s : ℕ} (i : Fin n) (F : HsB c r (s + 1)) :
    HasWeakPartialR (euclBall c r) i
      (((F : JetAmb c r (s + 1)) (nilW (s + 1)) : L2B c r) : (Fin n → ℝ) → ℝ)
      ((((derL c r i F : HsB c r s) : JetAmb c r s) (nilW s) : L2B c r) : (Fin n → ℝ) → ℝ) :=
  F.2 (nilW (s + 1)) i _

end JetMaps

/-! ### The maps on the Banach algebras -/

section AlgMaps

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)]

instance instFactSucc {s : ℕ} [hs : Fact (3 ≤ s)] : Fact (3 ≤ s + 1) := ⟨by have := hs.out; omega⟩

namespace SobAlg

variable {s : ℕ} [hs : Fact (3 ≤ s)]

/-- The jet map `SobAlg → HsB` as a continuous linear map. -/
def jetL : SobAlg c r s →L[ℝ] HsB c r s :=
  LinearMap.mkContinuous { toFun := jet, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    (Kal c r s)⁻¹ fun F => norm_jet_le F

theorem jetL_apply (F : SobAlg c r s) : jetL F = jet F := rfl

theorem norm_ofJet (F : HsB c r s) : ‖ofJet F‖ = Kal c r s * ‖F‖ := norm_def (ofJet F)

/-- **Restriction** `H^s(B) → H^{s'}(B)` (`s' ≤ s`) as a continuous linear map. -/
def restrS {s' : ℕ} [Fact (3 ≤ s')] (h : s' ≤ s) : SobAlg c r s →L[ℝ] SobAlg c r s' :=
  LinearMap.mkContinuous
    { toFun := fun F => ofJet (restrL c r h (jet F))
      map_add' := fun F G => by simp [map_add]; rfl
      map_smul' := fun a F => by simp [map_smul]; rfl }
    (Kal c r s' * (Kal c r s)⁻¹) fun F => by
      show ‖ofJet (restrL c r h (jet F))‖ ≤ _
      rw [norm_ofJet]
      have h1 : ‖restrL c r h (jet F)‖ ≤ ‖jet F‖ := by
        have := (restrL c r h).le_of_opNorm_le
          (LinearMap.mkContinuous_norm_le _ zero_le_one _) (jet F)
        rwa [one_mul] at this
      calc Kal c r s' * ‖restrL c r h (jet F)‖ ≤ Kal c r s' * ‖jet F‖ := by
            gcongr; exact (Kal_pos c r s').le
        _ ≤ Kal c r s' * ((Kal c r s)⁻¹ * ‖F‖) := by
            gcongr; exact (Kal_pos c r s').le; exact norm_jet_le F
        _ = _ := by ring

theorem fn_restrS {s' : ℕ} [Fact (3 ≤ s')] (h : s' ≤ s) (F : SobAlg c r s) :
    fn (restrS h F) = fn F := rfl

theorem restrS_mul {s' : ℕ} [Fact (3 ≤ s')] (h : s' ≤ s) (F G : SobAlg c r s) :
    restrS h (F * G) = restrS h F * restrS h G :=
  ext_fn (by
    filter_upwards [fn_mul F G, fn_mul (restrS h F) (restrS h G)] with x h1 h2
    rw [fn_restrS, h1, h2, fn_restrS, fn_restrS])

theorem restrS_one {s' : ℕ} [Fact (3 ≤ s')] (h : s' ≤ s) :
    restrS h (1 : SobAlg c r s) = 1 :=
  ext_fn (by
    filter_upwards [fn_one (c := c) (r := r) (s := s), fn_one (c := c) (r := r) (s := s')]
      with x h1 h2
    rw [fn_restrS, h1, h2])

/-- Restriction as a ring homomorphism. -/
def restrHom {s' : ℕ} [Fact (3 ≤ s')] (h : s' ≤ s) : SobAlg c r s →+* SobAlg c r s' where
  toFun := restrS h
  map_one' := restrS_one h
  map_mul' := restrS_mul h
  map_zero' := map_zero _
  map_add' := map_add _

/-- **The partial derivative** `∂_i : H^{s+1}(B) → H^s(B)` as a continuous linear map. -/
def derS (i : Fin 4) : SobAlg c r (s + 1) →L[ℝ] SobAlg c r s :=
  LinearMap.mkContinuous
    { toFun := fun F => ofJet (derL c r i (jet F))
      map_add' := fun F G => by simp [map_add]; rfl
      map_smul' := fun a F => by simp [map_smul]; rfl }
    (Kal c r s * (Kal c r (s + 1))⁻¹) fun F => by
      show ‖ofJet (derL c r i (jet F))‖ ≤ _
      rw [norm_ofJet]
      have h1 : ‖derL c r i (jet F)‖ ≤ ‖jet F‖ := by
        have := (derL c r i).le_of_opNorm_le
          (LinearMap.mkContinuous_norm_le _ zero_le_one _) (jet F)
        rwa [one_mul] at this
      calc Kal c r s * ‖derL c r i (jet F)‖ ≤ Kal c r s * ‖jet F‖ := by
            gcongr; exact (Kal_pos c r s).le
        _ ≤ Kal c r s * ((Kal c r (s + 1))⁻¹ * ‖F‖) := by
            gcongr; exact (Kal_pos c r s).le; exact norm_jet_le F
        _ = _ := by ring

/-- The derivative of an element is the weak derivative of its function component. -/
theorem weak_derS (i : Fin 4) (F : SobAlg c r (s + 1)) :
    HasWeakPartialR (euclBall c r) i (fn F) (fn (derS i F)) :=
  weak_derL c r i (jet F)

/-- Smooth functions as elements of `H^s(B)`. -/
def ofSmooth (u : (Fin 4 → ℝ) → ℝ) (hu : ContDiff ℝ ∞ u) : SobAlg c r s :=
  ofJet ⟨smoothJet c r s hu, smoothJet_mem c r s hu⟩

theorem fn_ofSmooth {u : (Fin 4 → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u) :
    fn (ofSmooth (c := c) (r := r) (s := s) u hu) =ᵐ[volume.restrict (euclBall c r)] u :=
  nilF_smoothJet c r hu

theorem derS_ofSmooth (i : Fin 4) {u : (Fin 4 → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u) :
    derS i (ofSmooth (c := c) (r := r) (s := s + 1) u hu) =
      ofSmooth (pd u i) (contDiff_pd hu i) := by
  refine Subtype.ext (PiLp.ext fun w => ?_)
  show smoothJet c r (s + 1) hu ⟨w.1 ++ [i], _⟩ = smoothJet c r s (contDiff_pd hu i) w
  simp only [smoothJet_apply]
  congr 1
  rw [← pdw_append]
  rfl

theorem restrS_ofSmooth {s' : ℕ} [Fact (3 ≤ s')] (h : s' ≤ s) {u : (Fin 4 → ℝ) → ℝ}
    (hu : ContDiff ℝ ∞ u) :
    restrS h (ofSmooth (c := c) (r := r) (s := s) u hu) = ofSmooth u hu := rfl

/-- **Density of smooth functions** in the Banach algebra `H^s(B)`. -/
theorem exists_tendsto_ofSmooth (F : SobAlg c r s) :
    ∃ (φ : ℕ → (Fin 4 → ℝ) → ℝ) (hφ : ∀ m, ContDiff ℝ ∞ (φ m)),
      Tendsto (fun m => ofSmooth (c := c) (r := r) (s := s) (φ m) (hφ m)) atTop (𝓝 F) := by
  obtain ⟨φ, hφ, h⟩ := exists_tendsto_smoothJet c r (jet F).2
  refine ⟨φ, hφ, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero] at h ⊢
  have e : ∀ m, ‖ofSmooth (c := c) (r := r) (s := s) (φ m) (hφ m) - F‖ =
      Kal c r s * ‖smoothJet c r s (hφ m) - ((jet F : HsB c r s) : JetAmb c r s)‖ := fun m => by
    rw [norm_def]; rfl
  simp only [e]
  simpa using h.const_mul (Kal c r s)

/-- Components of convergent smooth jets converge in `L²`. -/
theorem tendsto_eLpNorm_pdw {s' : ℕ} {φ : ℕ → (Fin 4 → ℝ) → ℝ} (hφ : ∀ m, ContDiff ℝ ∞ (φ m))
    {J : JetAmb c r s'} (h : Tendsto (fun m => smoothJet c r s' (hφ m)) atTop (𝓝 J))
    (w : ↥(wordsUpTo 4 s')) :
    Tendsto (fun m => eLpNorm (pdw (φ m) w.1 - ((J w : L2B c r) : (Fin 4 → ℝ) → ℝ)) 2
      (volume.restrict (euclBall c r))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun m => smoothJet c r s' (hφ m) w) atTop (𝓝 (J w)) :=
    (continuous_apply w).continuousAt.tendsto.comp
      ((PiLp.continuous_ofLp 2 _).continuousAt.tendsto.comp h)
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at h1
  refine h1.congr fun m => eLpNorm_congr_ae ?_
  filter_upwards [(memLp_euclBall_of_continuous c hr.out.le (contDiff_pdw (hφ m) w.1).continuous
    2).coeFn_toLp] with x hx
  simp [smoothJet_apply, hx]

/-- **`∂_i` is a derivation**: `∂_i(F G) = ∂_i F · G + F · ∂_i G` (Leibniz rule in `H^s(B)`). -/
theorem derS_mul (i : Fin 4) (F G : SobAlg c r (s + 1)) :
    derS i (F * G) = derS i F * restrS (Nat.le_succ s) G + restrS (Nat.le_succ s) F * derS i G := by
  set μB := volume.restrict (euclBall c r)
  obtain ⟨φ, hφ, hF⟩ := exists_tendsto_smoothJet c r (jet F).2
  obtain ⟨ψ, hψ, hG⟩ := exists_tendsto_smoothJet c r (jet G).2
  have hP := tendsto_smoothJet_mul c r (instFactSucc (s := s)).out hφ hψ hF hG
  set wi : ↥(wordsUpTo 4 (s + 1)) := ⟨[i], mem_wordsUpTo.mpr (by simp)⟩
  set w0 : ↥(wordsUpTo 4 (s + 1)) := nilW (s + 1)
  -- the `[i]`-components
  have hPi := tendsto_eLpNorm_pdw (fun m => (hφ m).mul (hψ m)) hP wi
  have hFi := tendsto_eLpNorm_pdw hφ hF wi
  have hF0 := tendsto_eLpNorm_pdw hφ hF w0
  have hGi := tendsto_eLpNorm_pdw hψ hG wi
  have hG0 := tendsto_eLpNorm_pdw hψ hG w0
  have epd : ∀ m, pdw (fun x => φ m x * ψ m x) wi.1 =
      fun x => pd (φ m) i x * ψ m x + φ m x * pd (ψ m) i x := fun m => by
    funext x
    exact pd_mul_real (((hφ m).differentiable (by simp)) x) (((hψ m).differentiable (by simp)) x) i
  have hφi : ∀ m, pdw (φ m) wi.1 = pd (φ m) i := fun m => rfl
  have hψi : ∀ m, pdw (ψ m) wi.1 = pd (ψ m) i := fun m => rfl
  have hφ0 : ∀ m, pdw (φ m) w0.1 = φ m := fun m => rfl
  have hψ0 : ∀ m, pdw (ψ m) w0.1 = ψ m := fun m => rfl
  simp only [epd] at hPi
  simp only [hφi] at hFi
  simp only [hφ0] at hF0
  simp only [hψi] at hGi
  simp only [hψ0] at hG0
  have key := ae_eq_of_tendsto_mul_add (μ := μB)
    (fun m => (contDiff_pd (hφ m) i).continuous.aestronglyMeasurable)
    (fun m => (hψ m).continuous.aestronglyMeasurable)
    (fun m => (hφ m).continuous.aestronglyMeasurable)
    (fun m => (contDiff_pd (hψ m) i).continuous.aestronglyMeasurable)
    (Lp.memLp _) (Lp.memLp _) (Lp.memLp _) (Lp.memLp _) (Lp.memLp _) hFi hG0 hF0 hGi hPi
  refine ext_fn ?_
  filter_upwards [key, fn_add (derS i F * restrS (Nat.le_succ s) G)
      (restrS (Nat.le_succ s) F * derS i G), fn_mul (derS i F) (restrS (Nat.le_succ s) G),
      fn_mul (restrS (Nat.le_succ s) F) (derS i G)] with x h1 h2 h3 h4
  rw [h2, h3, h4, fn_restrS, fn_restrS]
  exact h1

end SobAlg

end AlgMaps

end RenewalGeometry.BallAnalysis.BallAlg
