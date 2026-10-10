/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallSobolevAlgebra

/-!
# The Hilbert space `H^s(B)` as a closed space of jets
  (stage D1a of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript: the complete space on which the implicit
function theorem of stage D1 is posed.

* `JetAmb c r s = ⨁_{|w| ≤ s} L²(B)` (an `L²` product indexed by the words of length `≤ s`);
* `HsB c r s` — the jets `F` whose component `i :: w` is the weak `i`-th derivative of the
  component `w`; `isClosed_HsB` (from `isClosed_weakR`) and hence `CompleteSpace (HsB c r s)`:
  **`H^s(B)` is a Hilbert space**;
* `memHk_of_mem_HsB` and `exists_mem_HsB_of_memHk`: the weak Sobolev class `MemHk (B) s u` is
  exactly the set of first components of elements of `HsB c r s` (`memHk_iff_exists_HsB`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallReg

open SobolevOpen

set_option linter.unusedSectionVars false

variable {n : ℕ} [NeZero n] (c : Fin n → ℝ) (r : ℝ) [hr : Fact (0 < r)]

/-- The ambient jet space `⨁_{|w| ≤ s} L²(B)`. -/
abbrev JetAmb (s : ℕ) := PiLp 2 (fun _ : ↥(wordsUpTo n s) => L2B c r)

/-- The jet relations: component `i :: w` is the weak `i`-th derivative of component `w`. -/
def JetRel (s : ℕ) (F : JetAmb c r s) : Prop :=
  ∀ (w : ↥(wordsUpTo n s)) (i : Fin n) (h : i :: w.1 ∈ wordsUpTo n s),
    HasWeakPartialR (euclBall c r) i (F w : (Fin n → ℝ) → ℝ) (F ⟨i :: w.1, h⟩ : (Fin n → ℝ) → ℝ)

theorem weakR_zero_L2B (i : Fin n) :
    HasWeakPartialR (euclBall c r) i ((0 : L2B c r) : (Fin n → ℝ) → ℝ)
      ((0 : L2B c r) : (Fin n → ℝ) → ℝ) := by
  rw [weakR_iff_inner]
  intro φ hφ
  simp

/-- **The Sobolev space `H^s(B)`**, realised as the closed subspace of jets. -/
def HsB (s : ℕ) : Submodule ℝ (JetAmb c r s) where
  carrier := {F | JetRel c r s F}
  add_mem' := fun {F G} hF hG w i h => by
    have := (hF w i h).add_L2B c r (hG w i h)
    simpa using this
  zero_mem' := fun w i h => by simpa using weakR_zero_L2B c r i
  smul_mem' := fun a F hF w i h => by
    have := (hF w i h).smul_L2B c r a
    simpa using this

theorem mem_HsB {s : ℕ} {F : JetAmb c r s} : F ∈ HsB c r s ↔ JetRel c r s F := Iff.rfl

/-- **`H^s(B)` is closed in the jet space.** -/
theorem isClosed_HsB (s : ℕ) : IsClosed (HsB c r s : Set (JetAmb c r s)) := by
  have e : (HsB c r s : Set (JetAmb c r s)) =
      ⋂ (w : ↥(wordsUpTo n s)) (i : Fin n) (h : i :: w.1 ∈ wordsUpTo n s),
        (fun F : JetAmb c r s => (F w, F ⟨i :: w.1, h⟩)) ⁻¹'
          {p : L2B c r × L2B c r |
            HasWeakPartialR (euclBall c r) i (p.1 : (Fin n → ℝ) → ℝ) (p.2 : (Fin n → ℝ) → ℝ)} := by
    ext F
    simp only [SetLike.mem_coe, mem_HsB, JetRel, mem_iInter, mem_preimage, mem_ofPred_eq]
  rw [e]
  refine isClosed_iInter fun w => isClosed_iInter fun i => isClosed_iInter fun h => ?_
  exact (isClosed_weakR c r i).preimage
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : ↥(wordsUpTo n s) => L2B c r) w).continuous.prodMk
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ↥(wordsUpTo n s) => L2B c r) ⟨i :: w.1, h⟩).continuous)

/-- **`H^s(B)` is a Hilbert space.** -/
instance completeSpace_HsB (s : ℕ) : CompleteSpace (HsB c r s) :=
  (isClosed_HsB c r s).completeSpace_coe

/-- Components of an `H^s` jet are weak Sobolev functions of the complementary order. -/
theorem memHk_of_mem_HsB {s : ℕ} {F : JetAmb c r s} (hF : F ∈ HsB c r s) :
    ∀ (k : ℕ) (w : ↥(wordsUpTo n s)), w.1.length + k ≤ s →
      MemHk (euclBall c r) k (F w : (Fin n → ℝ) → ℝ) := by
  intro k
  induction k with
  | zero => intro w _; exact Lp.memLp _
  | succ k ih =>
    intro w hw
    refine ⟨Lp.memLp _, fun i => ?_⟩
    have h : i :: w.1 ∈ wordsUpTo n s := mem_wordsUpTo.mpr (by simp; omega)
    exact ⟨_, hF w i h, ih ⟨i :: w.1, h⟩ (by simp; omega)⟩

/-- The empty word, as an index. -/
def nilW (s : ℕ) : ↥(wordsUpTo n s) := ⟨[], mem_wordsUpTo.mpr (by simp)⟩

/-- Choice of weak derivatives along words. -/
theorem exists_word_derivs : ∀ (k : ℕ) {u : (Fin n → ℝ) → ℝ}, MemHk (euclBall c r) k u →
    ∃ G : List (Fin n) → (Fin n → ℝ) → ℝ, G [] = u ∧
      (∀ w : List (Fin n), w.length ≤ k → MemLp (G w) 2 (volume.restrict (euclBall c r))) ∧
      (∀ (w : List (Fin n)) (i : Fin n), w.length + 1 ≤ k →
        HasWeakPartialR (euclBall c r) i (G w) (G (i :: w))) := by
  intro k
  induction k with
  | zero =>
    intro u hu
    refine ⟨fun _ => u, rfl, fun w _ => hu, fun w i h => absurd h (by omega)⟩
  | succ k ih =>
    intro u hu
    choose g hg hgk using hu.2
    choose Gi hGi0 hGim hGiw using fun i => ih (hgk i)
    classical
    refine ⟨fun w => if h : w = [] then u else Gi (w.getLast h) w.dropLast, by simp, ?_, ?_⟩
    · intro w hw
      by_cases h : w = []
      · simpa [h] using hu.1
      · simp only [h, dite_false]
        exact hGim _ _ (by rw [List.length_dropLast]; omega)
    · intro w i hw
      by_cases h : w = []
      · subst h
        simp only [dite_true, List.cons_ne_nil, dite_false, List.getLast_singleton,
          List.dropLast_singleton]
        rw [hGi0]
        exact hg i
      · have hne : i :: w ≠ [] := List.cons_ne_nil _ _
        simp only [h, hne, dite_false]
        rw [List.getLast_cons h, List.dropLast_cons_of_ne_nil h]
        exact hGiw _ _ _ (by rw [List.length_dropLast]; have := List.length_pos_of_ne_nil h; omega)

/-- **Every weak `H^s(B)` function is the first component of an element of `HsB`.** -/
theorem exists_mem_HsB_of_memHk {s : ℕ} {u : (Fin n → ℝ) → ℝ}
    (hu : MemHk (euclBall c r) s u) :
    ∃ F ∈ HsB c r s, (F (nilW s) : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict (euclBall c r)] u := by
  obtain ⟨G, hG0, hGm, hGw⟩ := exists_word_derivs c r s hu
  have hm : ∀ w : ↥(wordsUpTo n s), MemLp (G w.1) 2 (volume.restrict (euclBall c r)) :=
    fun w => hGm w.1 (mem_wordsUpTo.mp w.2)
  refine ⟨WithLp.toLp 2 fun w => (hm w).toLp (G w.1), ?_, ?_⟩
  · intro w i h
    have hlen : w.1.length + 1 ≤ s := by have := mem_wordsUpTo.mp h; simpa using this
    exact (hGw w.1 i hlen).congr_ae c r (hm w).coeFn_toLp.symm
      (hm ⟨i :: w.1, h⟩).coeFn_toLp.symm
  · have := (hm (nilW s)).coeFn_toLp
    simpa [nilW, hG0] using this

/-- **`MemHk` = first components of `HsB`.** -/
theorem memHk_iff_exists_HsB {s : ℕ} {u : (Fin n → ℝ) → ℝ} :
    MemHk (euclBall c r) s u ↔
      ∃ F ∈ HsB c r s, (F (nilW s) : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict (euclBall c r)] u := by
  refine ⟨exists_mem_HsB_of_memHk c r, ?_⟩
  rintro ⟨F, hF, hu⟩
  exact (memHk_of_mem_HsB c r hF s (nilW s) (by simp [nilW])).congr_ae hu

/-- The jet of a smooth function. -/
def smoothJet (s : ℕ) {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u) : JetAmb c r s :=
  WithLp.toLp 2 fun w => (memLp_euclBall_of_continuous c hr.out.le
    (contDiff_pdw hu w.1).continuous 2).toLp (pdw u w.1)

/-- Jets of smooth functions lie in `H^s(B)`. -/
theorem smoothJet_mem (s : ℕ) {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u) :
    smoothJet c r s hu ∈ HsB c r s := fun w i h =>
  (hasWeakPartialR_of_contDiff _ ((contDiff_pdw hu w.1).of_le (by simp)) i).congr_ae c r
    (memLp_euclBall_of_continuous c hr.out.le
      (contDiff_pdw hu w.1).continuous 2).coeFn_toLp.symm
    (memLp_euclBall_of_continuous c hr.out.le
      (contDiff_pdw hu (i :: w.1)).continuous 2).coeFn_toLp.symm

/-- Non-vacuity: the zero jet lies in `H^3(B)` and `H^3(B)` is complete. -/
example : (0 : JetAmb (0 : Fin 4 → ℝ) 1 3) ∈ HsB (0 : Fin 4 → ℝ) 1 3 :=
  haveI : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  (HsB (0 : Fin 4 → ℝ) 1 3).zero_mem

example : CompleteSpace (HsB (0 : Fin 4 → ℝ) 1 3) :=
  haveI : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  inferInstance

end RenewalGeometry.BallAnalysis.BallReg
