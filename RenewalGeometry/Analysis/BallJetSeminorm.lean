/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallNeumannEst

/-!
# `H^K` seminorms of Sobolev fields by explicit derivatives, and the matrix Neumann estimate
  (stage D2 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `hS K F = Σ_{|w| ≤ K} ‖∂^w F‖_{L²(B)}` for `F ∈ H^s(B)`, `K ≤ s` (sum of the jet components);
  `norm_restrL_le_hS`, `hS_le_card_mul`, `hS_zero`, `sN_le_hS`, `hS_derS_le` (derivatives of
  `F` are controlled by `F`), `hS_succ_le` (the recursive decomposition
  `hS (K+1) F ≤ ‖F‖_{L²} + Σ_i hS K (∂_iF)`), `hS_restrS`;
* `hM K X = Σ_{ij} (hS K (Re X_{ij}) + hS K (Im X_{ij}))` for matrix fields;
* `neumann_est_matrix` (**main result**) — `hM (k+2) u ≤ C (hM k (Δu) + Σ ‖u_{ij}‖_{L²})` for
  weakly Neumann matrix fields.
-/

open MeasureTheory Set Metric Filter Topology NormedSpace
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallAlg

open SobolevOpen BallReg SobAlg

set_option linter.unusedSectionVars false

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {m : ℕ}

theorem sum_union_le_of_nonneg {α : Type*} [DecidableEq α] {f : α → ℝ} (hf : ∀ a, 0 ≤ f a)
    (A B : Finset α) : ∑ a ∈ A ∪ B, f a ≤ ∑ a ∈ A, f a + ∑ a ∈ B, f a := by
  have := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := f)
  have h0 : 0 ≤ ∑ a ∈ A ∩ B, f a := Finset.sum_nonneg fun a _ => hf a
  linarith

theorem sum_biUnion_le_of_nonneg {α ι : Type*} [DecidableEq α] [DecidableEq ι] {f : α → ℝ}
    (hf : ∀ a, 0 ≤ f a) (I : Finset ι) (u : ι → Finset α) :
    ∑ a ∈ I.biUnion u, f a ≤ ∑ i ∈ I, ∑ a ∈ u i, f a := by
  induction I using Finset.induction_on with
  | empty => simp
  | insert i I hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    exact (sum_union_le_of_nonneg hf _ _).trans (add_le_add le_rfl ih)

/-! ### Scalar jet seminorms -/

section Scalar

variable {s : ℕ} [Fact (3 ≤ s)]

/-- `hS K F = Σ_{|w| ≤ K} ‖∂^w F‖_{L²(B)}`. -/
def hS (K : ℕ) (hK : K ≤ s) (F : SobAlg c r s) : ℝ :=
  ∑ w : ↥(wordsUpTo 4 K), ‖((restrL c r hK (jet F) : HsB c r K) : JetAmb c r K) w‖

theorem hS_nonneg (K : ℕ) (hK : K ≤ s) (F : SobAlg c r s) : 0 ≤ hS K hK F :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem norm_restrL_le_hS (K : ℕ) (hK : K ≤ s) (F : SobAlg c r s) :
    ‖restrL c r hK (jet F)‖ ≤ hS K hK F :=
  norm_le_sum_norm_piLp _

theorem hS_le_card_mul (K : ℕ) (hK : K ≤ s) (F : SobAlg c r s) :
    hS K hK F ≤ (Fintype.card ↥(wordsUpTo 4 K)) * ‖restrL c r hK (jet F)‖ := by
  unfold hS
  calc ∑ w : ↥(wordsUpTo 4 K), ‖((restrL c r hK (jet F) : HsB c r K) : JetAmb c r K) w‖
      ≤ ∑ _w : ↥(wordsUpTo 4 K), ‖restrL c r hK (jet F)‖ :=
        Finset.sum_le_sum fun w _ => PiLp.norm_apply_le _ w
    _ = _ := by simp

theorem norm_component_eq_sN (F : SobAlg c r s) (hK : 0 ≤ s) :
    ‖((restrL c r hK (jet F) : HsB c r 0) : JetAmb c r 0) (nilW 0)‖ = sN 2 F := by
  rw [restrL_apply_nil, Lp.norm_def]
  rfl

theorem sN_le_hS (K : ℕ) (hK : K ≤ s) (F : SobAlg c r s) : sN 2 F ≤ hS K hK F := by
  have h : ‖((restrL c r hK (jet F) : HsB c r K) : JetAmb c r K) (nilW K)‖ = sN 2 F := by
    rw [restrL_apply_nil, Lp.norm_def]; rfl
  rw [← h]
  exact Finset.single_le_sum (f := fun w : ↥(wordsUpTo 4 K) =>
    ‖((restrL c r hK (jet F) : HsB c r K) : JetAmb c r K) w‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ _)

theorem hS_zero (hK : 0 ≤ s) (F : SobAlg c r s) : hS 0 hK F = sN 2 F := by
  unfold hS
  have : (Finset.univ : Finset ↥(wordsUpTo 4 0)) = {nilW 0} := by
    ext w
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    apply Subtype.ext
    have := mem_wordsUpTo.mp w.2
    simp only [nilW]
    exact List.eq_nil_of_length_eq_zero (by omega)
  rw [this, Finset.sum_singleton, restrL_apply_nil, Lp.norm_def]
  rfl

/-- The components of the jet of a derivative are components of the jet. -/
theorem jet_derS_apply (i : Fin 4) (F : SobAlg c r (s + 1)) (w : ↥(wordsUpTo 4 s)) :
    ((jet (derS i F) : HsB c r s) : JetAmb c r s) w =
      ((jet F : HsB c r (s + 1)) : JetAmb c r (s + 1)) ⟨w.1 ++ [i], mem_wordsUpTo_append i w.2⟩ :=
  rfl

theorem restrL_apply' {s s' : ℕ} (h : s' ≤ s) (F : HsB c r s) (w : ↥(wordsUpTo 4 s')) :
    ((restrL c r h F : HsB c r s') : JetAmb c r s') w =
      (F : JetAmb c r s) ⟨w.1, mem_wordsUpTo_mono h w.2⟩ := rfl

/-- Derivatives are controlled by the field. -/
theorem hS_derS_le (K : ℕ) (hK : K ≤ s) (i : Fin 4) (F : SobAlg c r (s + 1)) :
    hS K hK (derS i F) ≤ hS (K + 1) (Nat.succ_le_succ hK) F := by
  unfold hS
  simp only [restrL_apply', jet_derS_apply]
  set g : ↥(wordsUpTo 4 K) → ↥(wordsUpTo 4 (K + 1)) := fun w =>
    ⟨w.1 ++ [i], mem_wordsUpTo_append i w.2⟩
  have hg : Function.Injective g := fun a b hab => Subtype.ext (by
    have := congrArg Subtype.val hab
    simpa [g] using this)
  calc ∑ w : ↥(wordsUpTo 4 K), ‖((jet F : HsB c r (s + 1)) : JetAmb c r (s + 1))
        ⟨w.1 ++ [i], _⟩‖
      = ∑ w ∈ (Finset.univ : Finset ↥(wordsUpTo 4 K)).map ⟨g, hg⟩,
          ‖((jet F : HsB c r (s + 1)) : JetAmb c r (s + 1)) ⟨w.1, mem_wordsUpTo_mono
            (Nat.succ_le_succ hK) w.2⟩‖ := by
        rw [Finset.sum_map]; rfl
    _ ≤ ∑ w : ↥(wordsUpTo 4 (K + 1)), ‖((jet F : HsB c r (s + 1)) : JetAmb c r (s + 1))
          ⟨w.1, mem_wordsUpTo_mono (Nat.succ_le_succ hK) w.2⟩‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun _ _ _ => norm_nonneg _

/-- **The recursive decomposition** `hS (K+1) F ≤ ‖F‖_{L²} + Σ_i hS K (∂_iF)`. -/
theorem hS_succ_le (K : ℕ) (hK : K ≤ s) (F : SobAlg c r (s + 1)) :
    hS (K + 1) (Nat.succ_le_succ hK) F ≤ sN 2 F + ∑ i, hS K hK (derS i F) := by
  classical
  unfold hS
  simp only [restrL_apply', jet_derS_apply]
  set f : ↥(wordsUpTo 4 (K + 1)) → ℝ := fun w =>
    ‖((jet F : HsB c r (s + 1)) : JetAmb c r (s + 1)) ⟨w.1, mem_wordsUpTo_mono
      (Nat.succ_le_succ hK) w.2⟩‖
  -- the cover of the words by the empty word and the words ending in `i`
  set g : Fin 4 → ↥(wordsUpTo 4 K) → ↥(wordsUpTo 4 (K + 1)) := fun i w =>
    ⟨w.1 ++ [i], mem_wordsUpTo_append i w.2⟩
  have hcover : (Finset.univ : Finset ↥(wordsUpTo 4 (K + 1))) ⊆
      {nilW (K + 1)} ∪ Finset.univ.biUnion fun i => (Finset.univ.image (g i)) := by
    intro w _
    by_cases hw : w.1 = []
    · apply Finset.mem_union_left
      simp only [Finset.mem_singleton]
      exact Subtype.ext (by simp [nilW, hw])
    · apply Finset.mem_union_right
      simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image, true_and]
      refine ⟨w.1.getLast hw, ⟨w.1.dropLast, mem_wordsUpTo.mpr (by
        have := mem_wordsUpTo.mp w.2; simp; omega)⟩, Subtype.ext ?_⟩
      simp [g, List.dropLast_append_getLast]
  calc ∑ w : ↥(wordsUpTo 4 (K + 1)), f w
      ≤ ∑ w ∈ {nilW (K + 1)} ∪ Finset.univ.biUnion fun i => (Finset.univ.image (g i)), f w :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover fun _ _ _ => norm_nonneg _
    _ ≤ ∑ w ∈ ({nilW (K + 1)} : Finset _), f w +
          ∑ w ∈ Finset.univ.biUnion fun i => (Finset.univ.image (g i)), f w :=
        sum_union_le_of_nonneg (fun _ => norm_nonneg _) _ _
    _ ≤ sN 2 F + ∑ i, ∑ w ∈ Finset.univ.image (g i), f w := by
        refine add_le_add (le_of_eq ?_) (sum_biUnion_le_of_nonneg (fun _ => norm_nonneg _) _ _)
        rw [Finset.sum_singleton]
        simp only [f, nilW]
        rw [Lp.norm_def]; rfl
    _ ≤ sN 2 F + ∑ i, ∑ w : ↥(wordsUpTo 4 K), f (g i w) := by
        gcongr with i
        exact Finset.sum_image_le_of_nonneg fun _ _ => norm_nonneg _
    _ = _ := rfl

theorem hS_restrS {s' : ℕ} [Fact (3 ≤ s')] (h : s' ≤ s) (K : ℕ) (hK : K ≤ s') (F : SobAlg c r s) :
    hS K hK (restrS h F) = hS K (hK.trans h) F := rfl

end Scalar

/-! ### Matrix jet seminorms and the matrix Neumann estimate -/

section Matrix

variable {s : ℕ} [Fact (3 ≤ s)]

/-- `hM K X = Σ_{ij} (hS K (Re X_{ij}) + hS K (Im X_{ij}))`. -/
def hM (K : ℕ) (hK : K ≤ s) (X : MatSob c r s m) : ℝ :=
  ∑ i, ∑ j, (hS K hK (X i j).re + hS K hK (X i j).im)

/-- The entrywise `L^p` seminorm `Σ_{ij} (‖Re X_{ij}‖_{L^p} + ‖Im X_{ij}‖_{L^p})`. -/
def mN (p : ℝ≥0∞) (X : MatSob c r s m) : ℝ :=
  ∑ i, ∑ j, (sN p (X i j).re + sN p (X i j).im)

theorem hM_nonneg (K : ℕ) (hK : K ≤ s) (X : MatSob c r s m) : 0 ≤ hM K hK X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    add_nonneg (hS_nonneg _ _ _) (hS_nonneg _ _ _)

theorem mN_nonneg (p : ℝ≥0∞) (X : MatSob c r s m) : 0 ≤ mN p X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    add_nonneg (sN_nonneg _ _) (sN_nonneg _ _)

theorem mN_le_hM (K : ℕ) (hK : K ≤ s) (X : MatSob c r s m) : mN 2 X ≤ hM K hK X :=
  Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    add_le_add (sN_le_hS K hK _) (sN_le_hS K hK _)

theorem hM_zero (hK : 0 ≤ s) (X : MatSob c r s m) : hM 0 hK X = mN 2 X := by
  simp only [hM, mN, hS_zero]

theorem hM_derM_le (K : ℕ) (hK : K ≤ s) (μ : Fin 4) (X : MatSob c r (s + 1) m) :
    hM K hK (derM μ X) ≤ hM (K + 1) (Nat.succ_le_succ hK) X :=
  Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    add_le_add (hS_derS_le K hK μ _) (hS_derS_le K hK μ _)

theorem hM_succ_le (K : ℕ) (hK : K ≤ s) (X : MatSob c r (s + 1) m) :
    hM (K + 1) (Nat.succ_le_succ hK) X ≤ mN 2 X + ∑ μ, hM K hK (derM μ X) := by
  unfold hM mN
  calc ∑ i, ∑ j, (hS (K + 1) (Nat.succ_le_succ hK) (X i j).re +
        hS (K + 1) (Nat.succ_le_succ hK) (X i j).im)
      ≤ ∑ i, ∑ j, ((sN 2 (X i j).re + ∑ μ, hS K hK (derS μ (X i j).re)) +
          (sN 2 (X i j).im + ∑ μ, hS K hK (derS μ (X i j).im))) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          add_le_add (hS_succ_le K hK _) (hS_succ_le K hK _)
    _ = _ := by
        simp only [derM_apply]
        have e : ∀ (F : Fin m → Fin m → Fin 4 → ℝ),
            ∑ i, ∑ j, ∑ μ, F i j μ = ∑ μ, ∑ i, ∑ j, F i j μ := by
          intro F
          calc ∑ i, ∑ j, ∑ μ, F i j μ = ∑ i, ∑ μ, ∑ j, F i j μ :=
                Finset.sum_congr rfl fun i _ => Finset.sum_comm
            _ = ∑ μ, ∑ i, ∑ j, F i j μ := Finset.sum_comm
        rw [show (∑ i, ∑ j, ((sN 2 (X i j).re + ∑ μ, hS K hK (derS μ (X i j).re)) +
            (sN 2 (X i j).im + ∑ μ, hS K hK (derS μ (X i j).im)))) =
            ∑ i, ∑ j, (sN 2 (X i j).re + sN 2 (X i j).im) +
              ∑ i, ∑ j, ∑ μ, (hS K hK (derS μ (X i j).re) + hS K hK (derS μ (X i j).im)) by
          simp only [Finset.sum_add_distrib]; ring, e]

end Matrix

end RenewalGeometry.BallAnalysis.BallAlg

namespace RenewalGeometry.BallAnalysis.BallAlg

open SobolevOpen BallReg SobAlg

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {m : ℕ}

/-! ### The matrix Neumann estimate -/

theorem lapM_re' {t : ℕ} [Fact (3 ≤ t)] (u : MatSob c r (t + 2) m) (i j : Fin m) :
    (lapM (s := t) u i j).re = lap2 (u i j).re := by
  simp only [lapM, lap2, Matrix.sum_apply, Cx.sum_re, derM_apply]

theorem lapM_im' {t : ℕ} [Fact (3 ≤ t)] (u : MatSob c r (t + 2) m) (i j : Fin m) :
    (lapM (s := t) u i j).im = lap2 (u i j).im := by
  simp only [lapM, lap2, Matrix.sum_apply, Cx.sum_im, derM_apply]

/-- **The matrix Neumann estimate** `hM (k+2) u ≤ C (hM k (Δu) + Σ ‖u_{ij}‖_{L²})`. -/
theorem neumann_est_matrix (k t : ℕ) [Fact (3 ≤ t)] (ht : 3 ≤ t) (hkt : k ≤ t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : MatSob c r (t + 2) m, IsNeumM (restrM (by omega : 5 ≤ t + 2) u) →
      hM (k + 2) (by omega : k + 2 ≤ t + 2) u ≤ C * (hM k hkt (lapM (s := t) u) + mN 2 u) := by
  obtain ⟨C, hC0, hC⟩ := neumann_est (c := c) (r := r) k t ht hkt
  set N : ℝ := ((Fintype.card ↥(wordsUpTo 4 (k + 2)) : ℕ) : ℝ)
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  refine ⟨N * C, by positivity, fun u hu => ?_⟩
  have hX : ∀ X : SobAlg c r (t + 2), IsNeumannS (restrS (by omega : 5 ≤ t + 2) X) →
      hS (k + 2) (by omega) X ≤ N * C * (hS k hkt (lap2 X) + sN 2 X) := by
    intro X hX
    calc hS (k + 2) (by omega) X ≤ N * ‖restrL c r (by omega : k + 2 ≤ t + 2) (jet X)‖ :=
          hS_le_card_mul _ _ _
      _ ≤ N * (C * (‖restrL c r hkt (jet (lap2 X))‖ + sN 2 X)) := by gcongr; exact hC X hX
      _ ≤ N * (C * (hS k hkt (lap2 X) + sN 2 X)) := by
          gcongr; exact norm_restrL_le_hS _ _ _
      _ = N * C * (hS k hkt (lap2 X) + sN 2 X) := by ring
  unfold hM mN
  calc ∑ i, ∑ j, (hS (k + 2) (by omega) (u i j).re + hS (k + 2) (by omega) (u i j).im)
      ≤ ∑ i, ∑ j, (N * C * (hS k hkt (lap2 (u i j).re) + sN 2 (u i j).re) +
          N * C * (hS k hkt (lap2 (u i j).im) + sN 2 (u i j).im)) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => add_le_add ?_ ?_
        · exact hX _ (isNeumannS_re hu i j)
        · exact hX _ (isNeumannS_im hu i j)
    _ = N * C * (∑ i, ∑ j, (hS k hkt (lapM (s := t) u i j).re + hS k hkt (lapM (s := t) u i j).im) +
          ∑ i, ∑ j, (sN 2 (u i j).re + sN 2 (u i j).im)) := by
        simp only [lapM_re', lapM_im', mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring

/-! ### Calculus of the entrywise `L^p` seminorms -/

section MN

variable {s : ℕ} [Fact (3 ≤ s)]

theorem mN_add_le {p : ℝ≥0∞} (hp : 1 ≤ p) (X Y : MatSob c r s m) :
    mN p (X + Y) ≤ mN p X + mN p Y := by
  unfold mN
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  simp only [Matrix.add_apply, Cx.add_re, Cx.add_im]
  linarith [sN_add_le hp (X i j).re (Y i j).re, sN_add_le hp (X i j).im (Y i j).im]

theorem mN_neg (p : ℝ≥0∞) (X : MatSob c r s m) : mN p (-X) = mN p X := by
  simp only [mN, Matrix.neg_apply, Cx.neg_re, Cx.neg_im, sN_neg]

theorem mN_sub_le {p : ℝ≥0∞} (hp : 1 ≤ p) (X Y : MatSob c r s m) :
    mN p (X - Y) ≤ mN p X + mN p Y := by
  rw [sub_eq_add_neg]; exact (mN_add_le hp X (-Y)).trans (by rw [mN_neg])

theorem mN_sum_le {p : ℝ≥0∞} (hp : 1 ≤ p) {ι : Type*} (t : Finset ι) (X : ι → MatSob c r s m) :
    mN p (∑ k ∈ t, X k) ≤ ∑ k ∈ t, mN p (X k) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have h0 : mN p (0 : MatSob c r s m) = 0 := by
      simp only [mN, Matrix.zero_apply, Cx.zero_re, Cx.zero_im]
      have : sN p (0 : SobAlg c r s) = 0 := by
        simp [sN, eLpNorm_congr_ae (fn_zero (c := c) (r := r) (s := s))]
      simp [this]
    simp [h0]
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (mN_add_le hp _ _).trans (by linarith)

theorem mN_rhoM (p : ℝ≥0∞) (X : MatSob c r (s + 1) m) : mN p (rhoM X) = mN p X := rfl

theorem mN_restrM {s' : ℕ} [Fact (3 ≤ s')] (h : s' ≤ s) (p : ℝ≥0∞) (X : MatSob c r s m) :
    mN p (restrM h X) = mN p X := rfl

theorem mN_star (p : ℝ≥0∞) (X : MatSob c r s m) : mN p (star X) = mN p X := by
  unfold mN
  simp only [Matrix.star_apply, Cx.star_re', Cx.star_im', sN_neg]
  rw [Finset.sum_comm]

theorem mN_two_mul_le {p : ℝ≥0∞} (hp : 1 ≤ p) (X : MatSob c r s m) :
    mN p (2 * X) ≤ 2 * mN p X := by
  rw [two_mul, two_mul]; exact mN_add_le hp X X

/-- **Hölder for matrix fields** (entrywise seminorms). -/
theorem mN_mul_le (p q r' : ℝ≥0∞) [ENNReal.HolderTriple p q r'] (hr' : 1 ≤ r')
    (X Y : MatSob c r s m) : mN r' (X * Y) ≤ mN p X * mN q Y := by
  have hre : ∀ i j, sN r' ((X * Y) i j).re ≤
      ∑ k, (sN p (X i k).re * sN q (Y k j).re + sN p (X i k).im * sN q (Y k j).im) := by
    intro i j
    simp only [Matrix.mul_apply, Cx.sum_re, Cx.mul_re]
    refine (sN_sum_le hr' _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    exact (sN_sub_le hr' _ _).trans (add_le_add (sN_mul_le p q r' _ _) (sN_mul_le p q r' _ _))
  have him : ∀ i j, sN r' ((X * Y) i j).im ≤
      ∑ k, (sN p (X i k).re * sN q (Y k j).im + sN p (X i k).im * sN q (Y k j).re) := by
    intro i j
    simp only [Matrix.mul_apply, Cx.sum_im, Cx.mul_im]
    refine (sN_sum_le hr' _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    exact (sN_add_le hr' _ _).trans (add_le_add (sN_mul_le p q r' _ _) (sN_mul_le p q r' _ _))
  unfold mN
  calc ∑ i, ∑ j, (sN r' ((X * Y) i j).re + sN r' ((X * Y) i j).im)
      ≤ ∑ i, ∑ j, ∑ k, ((sN p (X i k).re + sN p (X i k).im) *
          (sN q (Y k j).re + sN q (Y k j).im)) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        refine (add_le_add (hre i j) (him i j)).trans (le_of_eq ?_)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ ≤ (∑ i, ∑ k, (sN p (X i k).re + sN p (X i k).im)) *
          (∑ k, ∑ j, (sN q (Y k j).re + sN q (Y k j).im)) := by
        set A : Fin m → Fin m → ℝ := fun i k => sN p (X i k).re + sN p (X i k).im
        set Bq : Fin m → Fin m → ℝ := fun k j => sN q (Y k j).re + sN q (Y k j).im
        have hA : ∀ i k, 0 ≤ A i k := fun i k => add_nonneg (sN_nonneg _ _) (sN_nonneg _ _)
        have hB : ∀ k j, 0 ≤ Bq k j := fun k j => add_nonneg (sN_nonneg _ _) (sN_nonneg _ _)
        set T := ∑ k, ∑ j, Bq k j
        have hT : ∀ k, ∑ j, Bq k j ≤ T := fun k =>
          Finset.single_le_sum (f := fun k' => ∑ j, Bq k' j)
            (fun _ _ => Finset.sum_nonneg fun _ _ => hB _ _) (Finset.mem_univ k)
        calc ∑ i, ∑ j, ∑ k, A i k * Bq k j = ∑ i, ∑ k, A i k * ∑ j, Bq k j := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
          _ ≤ ∑ i, ∑ k, A i k * T := by
              gcongr with i _ k _
              · exact hA i k
              · exact hT k
          _ = (∑ i, ∑ k, A i k) * T := by simp only [Finset.sum_mul]

end MN

end RenewalGeometry.BallAnalysis.BallAlg
