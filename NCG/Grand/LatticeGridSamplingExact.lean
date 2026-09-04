/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.LatticePeriodicDifferentiationExact
import Mathlib.Data.ZMod.Basic

/-!
# Exact sampling across periodic lattice-grid boundaries

Wrapping an integer root step modulo the scalar period changes its Euclidean
representative only by a full lattice period. Hence sampling a periodic field
commutes exactly with every root translation, including boundary crossings.
-/

open Module
open scoped BigOperators

namespace NCG.LatticeGridSampling

open LatticePeriodicDifferentiation

noncomputable section

variable {ι E F : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def embed (b : Basis ι ℝ E) (d : ℕ) (x : ι → ZMod d) : E :=
  ∑ i, (((x i).val : ℝ) / (d : ℝ)) • b i

def step (d : ℕ) (x : ι → ZMod d) (z : ι → ℤ) : ι → ZMod d :=
  fun i => x i + (z i : ZMod d)

theorem val_add_eq_add_period (d : ℕ) [NeZero d] (a : ZMod d) (z : ℤ) :
    ∃ q : ℤ, ((a + (z : ZMod d)).val : ℤ) = (a.val : ℤ) + z + (d : ℤ) * q := by
  have hcast : ((((a + (z : ZMod d)).val : ℤ) - (a.val : ℤ) - z : ℤ) : ZMod d) = 0 := by
    simp
  have hdiv := (ZMod.intCast_zmod_eq_zero_iff_dvd _ d).mp hcast
  obtain ⟨q, hq⟩ := hdiv
  exact ⟨q, by linarith⟩

theorem embed_step_eq_add_period
    (b : Basis ι ℝ E) (d : ℕ) [NeZero d] (x : ι → ZMod d) (z : ι → ℤ) :
    ∃ q : ι → ℤ, embed b d (step d x z) =
      embed b d x + (1 / (d : ℝ)) • integerCombination b z + integerCombination b q := by
  have hcoords : ∀ i, ∃ q : ℤ,
      (((step d x z) i).val : ℤ) = ((x i).val : ℤ) + z i + (d : ℤ) * q :=
    fun i => val_add_eq_add_period d (x i) (z i)
  choose q hq using hcoords
  refine ⟨q, ?_⟩
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  have hreal : ∀ i, (((step d x z) i).val : ℝ) =
      ((x i).val : ℝ) + (z i : ℝ) + (d : ℝ) * (q i : ℝ) := by
    intro i
    exact_mod_cast hq i
  change (∑ i, ((((step d x z) i).val : ℝ) / (d : ℝ)) • b i) =
    (∑ i, (((x i).val : ℝ) / (d : ℝ)) • b i) +
      (1 / (d : ℝ)) • (∑ i, (z i : ℝ) • b i) + ∑ i, (q i : ℝ) • b i
  rw [Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [smul_smul, ← add_smul, ← add_smul]
  congr 1
  rw [hreal]
  field_simp [hd]
  <;> ring

theorem sample_step_eq_translate
    (b : Basis ι ℝ E) (d : ℕ) [NeZero d] (x : ι → ZMod d) (z : ι → ℤ)
    (f : E → F) (hperiod : ∀ p : periodLattice b, ∀ y : E, f (y + p) = f y) :
    f (embed b d (step d x z)) = f (embed b d x + (1 / (d : ℝ)) • integerCombination b z) := by
  obtain ⟨q, hq⟩ := embed_step_eq_add_period b d x z
  rw [hq]
  exact hperiod ⟨integerCombination b q, ⟨q, rfl⟩⟩ _

end

end NCG.LatticeGridSampling
