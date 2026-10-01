/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Alternating-sector isolation fixes the branch weight
  (`prop:determinant-normalization-isolation`, spacetime–gauge duality manuscript)

A normalized instrument is a finite family of Kraus amplitudes `K b` with
`∑ b, (K b)ᴴ * K b = 1`.  Let `P_alt` be the (nonzero, idempotent) alternating-sector
projector `T₀ᴴ T₀` of `eq:normalized-determinant-effect`, and suppose one recorded
branch satisfies `eq:naturality-ray`, i.e. its effect is `x • P_alt`.

* `branch_weight_eq_one`: if every Kraus amplitude of every other branch annihilates
  `P_alt` (`K b * P_alt = 0`), then `x = 1`;
* `branch_weight_eq_one_of_amplitude`: the same, with the branch amplitude written as
  `c • T₀` (`x = |c|²`);
* `competing_branch_weights_sum_eq_one`: if instead the branches in a set `S` all have
  effect `x_a • P_alt` (same normalized one-dimensional envelope `ℂ T₀`) and all
  remaining amplitudes annihilate `P_alt`, then `∑ a ∈ S, x a = 1`;
* `scalarNormalizationKernel`, `finrank_scalarNormalizationKernel`: the linear scalar
  normalization kernel `{x : ∑ x_a = 0}` has dimension `k − 1` for `k` branches, and
  `sub_mem_scalarNormalizationKernel` shows that the solution set of `∑ x_a = 1` is a
  coset of it.

Rendering disclosed: `P_alt` is any nonzero idempotent matrix (the paper's
`I_C ⊗ |a⟩⟨a|` is one); the weight `x` is taken in `ℂ` (the paper's `x ≥ 0` is the
special case, `Complex.normSq c` in the amplitude form).  Positivity `x_a ≥ 0` of the
competing weights is a remark in the paper's proof, not part of the claim.
-/

open Matrix

namespace RenewalGeometry
namespace DeterminantNormalization

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- Compression of the trace-preservation identity: right-multiplying
`∑ b, (K b)ᴴ * K b = 1` by `P` leaves only the branches that do not annihilate `P`. -/
theorem compressed_normalization
    (K : ι → Matrix n n ℂ) (hnorm : ∑ b, (K b)ᴴ * K b = 1)
    (P : Matrix n n ℂ) (S : Finset ι)
    (hother : ∀ b, b ∉ S → K b * P = 0) :
    ∑ b ∈ S, (K b)ᴴ * K b * P = P := by
  have h : (∑ b, (K b)ᴴ * K b) * P = P := by rw [hnorm, one_mul]
  rw [Finset.sum_mul, ← Finset.sum_add_sum_compl S] at h
  have hzero : ∑ b ∈ Sᶜ, (K b)ᴴ * K b * P = 0 := by
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [Matrix.mul_assoc, hother b (Finset.mem_compl.mp hb), Matrix.mul_zero]
  rwa [hzero, add_zero] at h

/-- **`prop:determinant-normalization-isolation`, isolated branch**: in a normalized
instrument, if the distinguished branch has effect `x • P_alt` with `P_alt` a nonzero
idempotent and every other Kraus amplitude annihilates `P_alt`, then `x = 1`. -/
theorem branch_weight_eq_one
    (K : ι → Matrix n n ℂ) (hnorm : ∑ b, (K b)ᴴ * K b = 1)
    (P : Matrix n n ℂ) (hP : P * P = P) (hP0 : P ≠ 0)
    (b₀ : ι) (x : ℂ) (h₀ : (K b₀)ᴴ * K b₀ = x • P)
    (hother : ∀ b, b ≠ b₀ → K b * P = 0) : x = 1 := by
  have h := compressed_normalization K hnorm P {b₀}
    (fun b hb => hother b (by simpa using hb))
  rw [Finset.sum_singleton, h₀, Matrix.smul_mul, hP] at h
  have hsub : (x - 1) • P = 0 := by rw [sub_smul, one_smul, h, sub_self]
  rcases smul_eq_zero.mp hsub with hx | hP'
  · exact sub_eq_zero.mp hx
  · exact absurd hP' hP0

/-- The amplitude form: if the distinguished branch amplitude is `c • T₀` with
`T₀ᴴ T₀ = P_alt` (`eq:normalized-determinant-effect`), then `|c|² = 1`. -/
theorem branch_weight_eq_one_of_amplitude
    (K : ι → Matrix n n ℂ) (hnorm : ∑ b, (K b)ᴴ * K b = 1)
    (T₀ : Matrix n n ℂ) (hT : T₀ᴴ * T₀ * (T₀ᴴ * T₀) = T₀ᴴ * T₀) (hT0 : T₀ᴴ * T₀ ≠ 0)
    (b₀ : ι) (c : ℂ) (h₀ : K b₀ = c • T₀)
    (hother : ∀ b, b ≠ b₀ → K b * (T₀ᴴ * T₀) = 0) : Complex.normSq c = 1 := by
  have heff : (K b₀)ᴴ * K b₀ = (Complex.normSq c : ℂ) • (T₀ᴴ * T₀) := by
    rw [h₀, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Complex.normSq_eq_conj_mul_self]
    rfl
  have := branch_weight_eq_one K hnorm (T₀ᴴ * T₀) hT hT0 b₀ _ heff hother
  exact_mod_cast this

/-- **`prop:determinant-normalization-isolation`, competing branches**: if the branches
in `S` have effects `x a • P_alt` on the same envelope and every other amplitude
annihilates `P_alt`, the normalization constrains exactly `∑ a ∈ S, x a = 1`. -/
theorem competing_branch_weights_sum_eq_one
    (K : ι → Matrix n n ℂ) (hnorm : ∑ b, (K b)ᴴ * K b = 1)
    (P : Matrix n n ℂ) (hP : P * P = P) (hP0 : P ≠ 0)
    (S : Finset ι) (x : ι → ℂ) (hS : ∀ a ∈ S, (K a)ᴴ * K a = x a • P)
    (hother : ∀ b, b ∉ S → K b * P = 0) : ∑ a ∈ S, x a = 1 := by
  have h := compressed_normalization K hnorm P S hother
  have hsum : ∑ b ∈ S, (K b)ᴴ * K b * P = (∑ a ∈ S, x a) • P := by
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [hS a ha, Matrix.smul_mul, hP]
  rw [hsum] at h
  have hsub : ((∑ a ∈ S, x a) - 1) • P = 0 := by
    rw [sub_smul, one_smul, h, sub_self]
  rcases smul_eq_zero.mp hsub with hx | hP'
  · exact sub_eq_zero.mp hx
  · exact absurd hP' hP0

/-- The scalar sum functional `x ↦ ∑ a, x a` on `k`-branch weight vectors. -/
noncomputable def scalarSumFunctional (κ : Type*) [Fintype κ] : (κ → ℂ) →ₗ[ℂ] ℂ :=
  ∑ a, LinearMap.proj a

@[simp] theorem scalarSumFunctional_apply {κ : Type*} [Fintype κ] (x : κ → ℂ) :
    scalarSumFunctional κ x = ∑ a, x a := by
  simp [scalarSumFunctional, LinearMap.sum_apply]

/-- The linear scalar normalization kernel `{x : ∑ a, x a = 0}` of `k` competing
branches (`prop:determinant-normalization-isolation`). -/
noncomputable def scalarNormalizationKernel (κ : Type*) [Fintype κ] : Submodule ℂ (κ → ℂ) :=
  LinearMap.ker (scalarSumFunctional κ)

theorem mem_scalarNormalizationKernel {κ : Type*} [Fintype κ] (x : κ → ℂ) :
    x ∈ scalarNormalizationKernel κ ↔ ∑ a, x a = 0 := by
  simp [scalarNormalizationKernel, LinearMap.mem_ker]

/-- Two admissible weight vectors (`∑ x_a = 1`) differ by an element of the scalar
normalization kernel: the solution set is a coset of the kernel. -/
theorem sub_mem_scalarNormalizationKernel {κ : Type*} [Fintype κ] (x y : κ → ℂ)
    (hx : ∑ a, x a = 1) (hy : ∑ a, y a = 1) :
    x - y ∈ scalarNormalizationKernel κ := by
  rw [mem_scalarNormalizationKernel]
  simp [Finset.sum_sub_distrib, hx, hy]

/-- The scalar normalization kernel of `k ≥ 1` competing branches has dimension
`k − 1` (`prop:determinant-normalization-isolation`). -/
theorem finrank_scalarNormalizationKernel (κ : Type*) [Fintype κ] [Nonempty κ] :
    Module.finrank ℂ (scalarNormalizationKernel κ) = Fintype.card κ - 1 := by
  have hsurj : Function.Surjective (scalarSumFunctional κ) := by
    intro c
    obtain ⟨a₀⟩ := ‹Nonempty κ›
    classical
    refine ⟨Pi.single a₀ c, ?_⟩
    rw [scalarSumFunctional_apply, Finset.sum_eq_single a₀]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ a₀) h
  have hrange : LinearMap.range (scalarSumFunctional κ) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hrn := LinearMap.finrank_range_add_finrank_ker (scalarSumFunctional κ)
  rw [hrange, finrank_top, Module.finrank_self, Module.finrank_fintype_fun_eq_card] at hrn
  change Module.finrank ℂ (LinearMap.ker (scalarSumFunctional κ)) = _
  omega

end DeterminantNormalization
end RenewalGeometry

