/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GTSourceVariance
import NCG.Grand.PsdCalculusExact

/-!
# Exact conditional-source variance and the coarsest sufficient record

This file closes the clauses of `thm:GT-source-record-variance` that are not
present in `NCG.gt_source_record_variance`: partition means imply the two
cross-term cancellations, the within-record Gram is the pairwise expression
SK.3 and is positive semidefinite, and equality of profiles gives the
canonical coarsest source-sufficient record.

A finite partition is represented without redundancy by a finite type `B` of
blocks and a finite fibre `Ω b` over each block.
-/

open Matrix Finset
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace SourceRecordVariance

private theorem matrix_sum_posSemidef
    {N ι : Type*} [Fintype N] [Fintype ι]
    {A : ι → Matrix N N ℂ} (hA : ∀ i, (A i).PosSemidef) :
    (∑ i, A i).PosSemidef :=
  Finset.sum_induction _ _ (fun _ _ hP hQ => hP.add hQ)
    Matrix.PosSemidef.zero (fun i _ => hA i)
/-- A record is source sufficient when profiles are constant on its fibres. -/
def SourceSufficient {Ω A R : Type*} (S : Ω → A) (r : Ω → R) : Prop :=
  ∀ ⦃ω η⦄, r ω = r η → S ω = S η

/-- The canonical record: the actually occurring source profile. -/
def canonicalSourceRecord {Ω A : Type*} (S : Ω → A) (ω : Ω) : Set.range S :=
  ⟨S ω, ⟨ω, rfl⟩⟩

/-- The omitted source directions of a proposed record are spanned by profile
differences inside its fibres. -/
def omittedSourceSubspace {Ω R : Type*} [Fintype Ω]
    {Y E : Type*} [Fintype Y] [Fintype E]
    (S : Ω → Matrix Y E ℂ) (r : Ω → R) :
    Submodule ℂ (Matrix Y E ℂ) :=
  Submodule.span ℂ {D | ∃ ω η, r ω = r η ∧ D = S ω - S η}

/-- The innovation rank is the dimension of the orthogonal source directions
omitted by a proposed record. -/
noncomputable def innovationRank {Ω R : Type*} [Fintype Ω]
    {Y E : Type*} [Fintype Y] [Fintype E]
    (S : Ω → Matrix Y E ℂ) (r : Ω → R) : ℕ :=
  Module.finrank ℂ (omittedSourceSubspace S r)

/-- Scalar weighted pairwise-variance identity. -/
private theorem weighted_pairwise_centered
    {Ω : Type*} [Fintype Ω]
    (ν : Ω → ℝ) (m : ℝ) (x y : Ω → ℂ)
    (hm : m = ∑ ω, ν ω) (hm0 : m ≠ 0)
    (hx : ∑ ω, (ν ω : ℂ) * x ω = 0)
    (hy : ∑ ω, (ν ω : ℂ) * y ω = 0) :
    ∑ ω, (ν ω : ℂ) * (star (x ω) * y ω) =
      ((((2 * m : ℝ)⁻¹ : ℝ) : ℂ) *
        ∑ ω, ∑ η, ((ν ω * ν η : ℝ) : ℂ) *
          (star (x ω - x η) * (y ω - y η))) := by
  have hw : ∑ ω, (ν ω : ℂ) = (m : ℂ) := by
    rw [← Complex.ofReal_sum, ← hm]
  have hxstar : ∑ ω, (ν ω : ℂ) * star (x ω) = 0 := by
    have h := congrArg star hx
    simpa [map_sum, map_mul] using h
  have ht1 :
      ∑ ω, ∑ η, (ν ω : ℂ) * (ν η : ℂ) *
          (star (x ω) * y ω) =
        (m : ℂ) * ∑ ω, (ν ω : ℂ) * (star (x ω) * y ω) := by
    calc
      _ = ∑ ω, ((ν ω : ℂ) * (star (x ω) * y ω)) *
          ∑ η, (ν η : ℂ) := by
            apply Finset.sum_congr rfl
            intro ω hω
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro η hη
            ring
      _ = (∑ ω, (ν ω : ℂ) * (star (x ω) * y ω)) *
          ∑ η, (ν η : ℂ) := by rw [Finset.sum_mul]
      _ = _ := by rw [hw]; ring
  have ht2 :
      ∑ ω, ∑ η, (ν ω : ℂ) * (ν η : ℂ) *
          (star (x ω) * y η) = 0 := by
    calc
      _ = (∑ ω, (ν ω : ℂ) * star (x ω)) *
          ∑ η, (ν η : ℂ) * y η := by
            rw [Fintype.sum_mul_sum]
            apply Finset.sum_congr rfl
            intro ω hω
            apply Finset.sum_congr rfl
            intro η hη
            ring
      _ = 0 := by rw [hxstar, hy, zero_mul]
  have ht3 :
      ∑ ω, ∑ η, (ν ω : ℂ) * (ν η : ℂ) *
          (star (x η) * y ω) = 0 := by
    calc
      _ = (∑ ω, (ν ω : ℂ) * y ω) *
          ∑ η, (ν η : ℂ) * star (x η) := by
            rw [Fintype.sum_mul_sum]
            apply Finset.sum_congr rfl
            intro ω hω
            apply Finset.sum_congr rfl
            intro η hη
            ring
      _ = 0 := by rw [hy, hxstar, zero_mul]
  have ht4 :
      ∑ ω, ∑ η, (ν ω : ℂ) * (ν η : ℂ) *
          (star (x η) * y η) =
        (m : ℂ) * ∑ η, (ν η : ℂ) * (star (x η) * y η) := by
    calc
      _ = ∑ ω, (ν ω : ℂ) *
          (∑ η, (ν η : ℂ) * (star (x η) * y η)) := by
            apply Finset.sum_congr rfl
            intro ω hω
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro η hη
            ring
      _ = (∑ ω, (ν ω : ℂ)) *
          (∑ η, (ν η : ℂ) * (star (x η) * y η)) := by
            rw [Finset.sum_mul]
      _ = _ := by rw [hw]
  have hpair :
      ∑ ω, ∑ η, ((ν ω * ν η : ℝ) : ℂ) *
          (star (x ω - x η) * (y ω - y η)) =
        (2 * m : ℂ) *
          ∑ ω, (ν ω : ℂ) * (star (x ω) * y ω) := by
    simp_rw [star_sub, sub_mul, mul_sub]
    simp only [Finset.sum_sub_distrib, Complex.ofReal_mul]
    rw [ht1, ht2, ht3, ht4]
    ring
  rw [hpair]
  have h2m : (2 * m : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hm0
  push_cast
  have h2mc : (2 * (m : ℂ)) ≠ 0 := by norm_num [hm0]
  rw [← mul_assoc, inv_mul_cancel₀ h2mc, one_mul]
/-- A discrepancy Gram vanishes exactly when the two profiles agree. -/
theorem discrepancy_gram_eq_zero_iff
    {Y E : Type*} [Fintype Y] [Fintype E]
    (A B : Matrix Y E ℂ) :
    (A - B)ᴴ * (A - B) = 0 ↔ A = B := by
  rw [Matrix.conjTranspose_mul_self_eq_zero, sub_eq_zero]

/-- The canonical profile record is sufficient and is coarser than every
source-sufficient record.  Its equality classes are exactly the zero
discrepancy classes from the manuscript. -/
theorem canonical_record_is_unique_coarsest
    {Ω A R : Type*} (S : Ω → A) (r : Ω → R)
    (hr : SourceSufficient S r) :
    SourceSufficient S (canonicalSourceRecord S) ∧
      (∀ ω η, r ω = r η →
        canonicalSourceRecord S ω = canonicalSourceRecord S η) := by
  constructor
  · intro ω η h
    exact congrArg Subtype.val h
  · intro ω η h
    apply Subtype.ext
    exact hr h

/-- Matrix form of the pairwise identity SK.3 in one partition fibre. -/
theorem matrix_pairwise_variance
    {Ω Y E : Type} [Fintype Ω] [Fintype Y] [Fintype E]
    (ν : Ω → ℝ) (m : ℝ) (D : Ω → Matrix Y E ℂ)
    (hm : m = ∑ ω, ν ω) (hm0 : m ≠ 0)
    (hcenter : ∑ ω, (ν ω : ℂ) • D ω = 0) :
    ∑ ω, (ν ω : ℂ) • ((D ω)ᴴ * D ω) =
      ((2 * m)⁻¹ : ℝ) •
        ∑ ω, ∑ η, ((ν ω * ν η : ℝ) : ℂ) •
          ((D ω - D η)ᴴ * (D ω - D η)) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.sub_apply]
  have hk (k : Y) :
      ∑ ω, (ν ω : ℂ) * (star (D ω k i) * D ω k j) =
        ((((2 * m)⁻¹ : ℝ) : ℂ) *
          ∑ ω, ∑ η, ((ν ω * ν η : ℝ) : ℂ) *
            (star (D ω k i - D η k i) *
              (D ω k j - D η k j))) := by
    exact weighted_pairwise_centered ν m (fun ω => D ω k i)
      (fun ω => D ω k j) hm hm0
      (by
        have h := congrArg (fun M : Matrix Y E ℂ => M k i) hcenter
        simpa [Matrix.sum_apply, Matrix.smul_apply] using h)
      (by
        have h := congrArg (fun M : Matrix Y E ℂ => M k j) hcenter
        simpa [Matrix.sum_apply, Matrix.smul_apply] using h)
  calc
    ∑ ω, ↑(ν ω) * ∑ k, star (D ω k i) * D ω k j =
        ∑ k, ∑ ω, ↑(ν ω) * (star (D ω k i) * D ω k j) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
    _ = ∑ k, ((((2 * m)⁻¹ : ℝ) : ℂ) *
          ∑ ω, ∑ η, ((ν ω * ν η : ℝ) : ℂ) *
            (star (D ω k i - D η k i) *
              (D ω k j - D η k j))) := by
          apply Finset.sum_congr rfl
          intro k hk'
          exact hk k
    _ = (((2 * m)⁻¹ : ℝ) : ℂ) *
        ∑ k, ∑ ω, ∑ η, ↑(ν ω * ν η) *
          (star (D ω k i - D η k i) *
            (D ω k j - D η k j)) := by
          rw [Finset.mul_sum]
    _ = (((2 * m)⁻¹ : ℝ) : ℂ) *
        ∑ ω, ∑ η, ∑ k, ↑(ν ω * ν η) *
          (star (D ω k i - D η k i) *
            (D ω k j - D η k j)) := by
          congr 1
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro ω hω
          rw [Finset.sum_comm]
    _ = (((2 * m)⁻¹ : ℝ) : ℂ) *
        ∑ ω, ∑ η, ↑(ν ω * ν η) *
          ∑ k, star (D ω k i - D η k i) *
            (D ω k j - D η k j) := by
          congr 1
          apply Finset.sum_congr rfl
          intro ω hω
          apply Finset.sum_congr rfl
          intro η hη
          rw [Finset.mul_sum]
/-- The omitted-source dimension vanishes exactly for source-sufficient
records.  Thus `innovationRank` is the minimal missing orthogonal source
dimension, and it is zero precisely at (or above) the canonical record. -/
theorem innovationRank_eq_zero_iff_sourceSufficient
    {Ω R : Type*} [Fintype Ω]
    {Y E : Type*} [Fintype Y] [Fintype E]
    (S : Ω → Matrix Y E ℂ) (r : Ω → R) :
    innovationRank S r = 0 ↔ SourceSufficient S r := by
  rw [innovationRank, Submodule.finrank_eq_zero]
  constructor
  · intro h ω η hr
    have hmem : S ω - S η ∈ omittedSourceSubspace S r :=
      Submodule.subset_span ⟨ω, η, hr, rfl⟩
    rw [h] at hmem
    exact sub_eq_zero.mp hmem
  · intro h
    apply le_antisymm
    · rw [omittedSourceSubspace, Submodule.span_le]
      intro D hD
      rcases hD with ⟨ω, η, hr, rfl⟩
      simp [h hr]
    · exact bot_le
/-- `thm:GT-source-record-variance`, exact completion.

The dependent finite family `Ω b` is the partition fibre over `b`.  The first
two hypotheses are precisely the mass and conditional-mean definitions; no
cross-term cancellation is assumed. -/
theorem source_record_variance_exact
    {B : Type} [Fintype B]
    {Ω : B → Type} [∀ b, Fintype (Ω b)]
    {Y E : Type} [Fintype Y] [Fintype E]
    (ν : ∀ b, Ω b → ℝ) (S : ∀ b, Ω b → Matrix Y E ℂ)
    (νB : B → ℝ) (Sbar : B → Matrix Y E ℂ)
    (hmass : ∀ b, νB b = ∑ ω, ν b ω)
    (hmass0 : ∀ b, νB b ≠ 0)
    (hmean : ∀ b, (νB b : ℂ) • Sbar b =
      ∑ ω, (ν b ω : ℂ) • S b ω)
    (hν : ∀ b ω, 0 ≤ ν b ω) :
    let G := ∑ b, ∑ ω, (ν b ω : ℂ) • ((S b ω)ᴴ * S b ω)
    let between := ∑ b, (νB b : ℂ) • ((Sbar b)ᴴ * Sbar b)
    let innovation := ∑ b, ∑ ω, (ν b ω : ℂ) •
      ((S b ω - Sbar b)ᴴ * (S b ω - Sbar b))
    let pairwise := ∑ b, ((2 * νB b)⁻¹ : ℝ) •
      ∑ ω, ∑ η, ((ν b ω * ν b η : ℝ) : ℂ) •
        ((S b ω - S b η)ᴴ * (S b ω - S b η))
    G = between + innovation ∧ innovation = pairwise ∧ innovation.PosSemidef := by
  dsimp only
  have hcenter : ∀ b, ∑ ω, (ν b ω : ℂ) • (S b ω - Sbar b) = 0 := by
    intro b
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
    rw [← Complex.ofReal_sum, ← hmass b, hmean b]
    simp
  have hblock : ∀ b,
      ∑ ω, (ν b ω : ℂ) • ((S b ω)ᴴ * S b ω) =
        (νB b : ℂ) • ((Sbar b)ᴴ * Sbar b) +
          ∑ ω, (ν b ω : ℂ) •
            ((S b ω - Sbar b)ᴴ * (S b ω - Sbar b)) := by
    intro b
    have hv := gt_source_record_variance (ν := fun ω => (ν b ω : ℂ))
      (S := S b) (Sbar := fun _ => Sbar b)
      (by
        have hc := congrArg Matrix.conjTranspose (hcenter b)
        simpa [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
          Matrix.sum_mul, smul_mul_assoc] using
          congrArg (fun M => M * Sbar b) hc)
      (by
        simpa [Matrix.mul_sum, mul_smul] using
          congrArg (fun M => (Sbar b)ᴴ * M) (hcenter b))
    simpa [← Finset.sum_smul, ← Complex.ofReal_sum, ← hmass b] using hv
  constructor
  · calc
      ∑ b, ∑ ω, (ν b ω : ℂ) • ((S b ω)ᴴ * S b ω)
          = ∑ b, ((νB b : ℂ) • ((Sbar b)ᴴ * Sbar b) +
              ∑ ω, (ν b ω : ℂ) •
                ((S b ω - Sbar b)ᴴ * (S b ω - Sbar b))) := by
              apply Finset.sum_congr rfl
              intro b hb
              exact hblock b
      _ = _ := by rw [Finset.sum_add_distrib]
  · constructor
    · apply Finset.sum_congr rfl
      intro b hb
      simpa [sub_sub_sub_cancel_right] using
        matrix_pairwise_variance (ν b) (νB b)
          (fun ω => S b ω - Sbar b) (hmass b) (hmass0 b) (hcenter b)
    · apply matrix_sum_posSemidef
      intro b
      apply matrix_sum_posSemidef
      intro ω
      exact QRE.posSemidef_smul_real (hν b ω)
        (Matrix.posSemidef_conjTranspose_mul_self (S b ω - Sbar b))
end SourceRecordVariance
end NCG
