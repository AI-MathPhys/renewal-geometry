/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Canonical sealed-provenance quotient
  (`thm:sealed-provenance-quotient`, Gran-Tensor manuscript)

* Word transports `wordT`, hidden letters `wordD`, and sealed
  writers `wordH` over the free monoid on the resolved
  alphabet, with the defining recursion
  `H_{a·w} = C_a·T_w + D_a·H_w`.

* `sealed_provenance_quotient`:
  (i) `T` and `D` are word homomorphisms;
  (ii) the boxed word-level cocycle
      `H_{vw} = H_v·T_w + D_v·H_w`;
  (iii) the reconstruction identity
      `D_a·H_w = H_{a·w} - H_a·T_w` (the saturated-panel
      formula `D̄_a[H_w x] = [H_{aw}x] - [H_a T_w x]`);
  (iv) the provenance carrier `ℛ_prov = span{H_w·x}` is
      invariant under every hidden letter;
  (v) the Read-null space `𝒩_prov` is invariant under every
      hidden letter;
  (vi) the boxed exact sequence as the exact rank count
      `dim 𝒩 + dim 𝒫 = dim ℛ`;
  (vii) every centered response factors through the quotient.

The unique-similarity clause for two sealed extensions with
the same passive table is the proved
`hankel_minimality`/`typed_hankel_realization` identification
applied to this quotient.
-/

open Matrix

namespace NCG

variable {σ ι l e y : Type*} [Fintype l] [Fintype e]
variable [DecidableEq l] [DecidableEq e]

/-- Visible word transport. -/
def wordT (T : σ → Matrix l l ℂ) : List σ → Matrix l l ℂ
  | [] => 1
  | a :: w => T a * wordT T w

/-- Hidden word letter. -/
def wordD (Dm : σ → Matrix e e ℂ) : List σ → Matrix e e ℂ
  | [] => 1
  | a :: w => Dm a * wordD Dm w

/-- Sealed provenance writer of a word. -/
def wordH (T : σ → Matrix l l ℂ) (C : σ → Matrix e l ℂ)
    (Dm : σ → Matrix e e ℂ) : List σ → Matrix e l ℂ
  | [] => 0
  | a :: w => C a * wordT T w + Dm a * wordH T C Dm w

/-- The provenance carrier `span{H_w·x}`. -/
def provCarrier (T : σ → Matrix l l ℂ)
    (C : σ → Matrix e l ℂ) (Dm : σ → Matrix e e ℂ) :
    Submodule ℂ (e → ℂ) :=
  Submodule.span ℂ (⋃ w : List σ,
    Set.range fun x : l → ℂ => wordH T C Dm w *ᵥ x)

/-- The Read-null space `{v : R_λ·D_v·v = 0}`. -/
def provNull (R : ι → Matrix y e ℂ)
    (Dm : σ → Matrix e e ℂ) : Submodule ℂ (e → ℂ) :=
  ⨅ p : ι × List σ,
    LinearMap.ker (R p.1 * wordD Dm p.2).mulVecLin

/-- `thm:sealed-provenance-quotient`. -/
theorem sealed_provenance_quotient
    (T : σ → Matrix l l ℂ) (C : σ → Matrix e l ℂ)
    (Dm : σ → Matrix e e ℂ) (R : ι → Matrix y e ℂ) :
    -- (i) word homomorphisms
    (∀ v w : List σ,
      wordT T (v ++ w) = wordT T v * wordT T w)
    ∧ (∀ v w : List σ,
        wordD Dm (v ++ w) = wordD Dm v * wordD Dm w)
    -- (ii) the boxed word cocycle
    ∧ (∀ v w : List σ,
        wordH T C Dm (v ++ w)
          = wordH T C Dm v * wordT T w
            + wordD Dm v * wordH T C Dm w)
    -- (iii) the reconstruction identity
    ∧ (∀ (a : σ) (w : List σ),
        Dm a * wordH T C Dm w
          = wordH T C Dm (a :: w)
            - wordH T C Dm [a] * wordT T w)
    -- (iv) the carrier is hidden-letter invariant
    ∧ (∀ (a : σ) (v : e → ℂ), v ∈ provCarrier T C Dm →
        Dm a *ᵥ v ∈ provCarrier T C Dm)
    -- (v) the Read-null space is hidden-letter invariant
    ∧ (∀ (a : σ) (v : e → ℂ), v ∈ provNull R Dm →
        Dm a *ᵥ v ∈ provNull R Dm)
    -- (vi) the exact sequence as an exact rank count
    ∧ Module.finrank ℂ ((provCarrier T C Dm)
          ⧸ (Submodule.comap (provCarrier T C Dm).subtype
              (provNull R Dm)))
        + Module.finrank ℂ
            (Submodule.comap (provCarrier T C Dm).subtype
              (provNull R Dm))
      = Module.finrank ℂ (provCarrier T C Dm)
    -- (vii) responses factor through the quotient
    ∧ (∀ (lam : ι) (w : List σ) (u u' : e → ℂ),
        u - u' ∈ provNull R Dm →
        (R lam * wordD Dm w) *ᵥ u
          = (R lam * wordD Dm w) *ᵥ u') := by
  have hT : ∀ v w : List σ,
      wordT T (v ++ w) = wordT T v * wordT T w := by
    intro v w
    induction v with
    | nil => simp [wordT]
    | cons a v ih =>
        simp only [List.cons_append, wordT, ih,
          Matrix.mul_assoc]
  have hD : ∀ v w : List σ,
      wordD Dm (v ++ w) = wordD Dm v * wordD Dm w := by
    intro v w
    induction v with
    | nil => simp [wordD]
    | cons a v ih =>
        simp only [List.cons_append, wordD, ih,
          Matrix.mul_assoc]
  have hH : ∀ v w : List σ,
      wordH T C Dm (v ++ w)
        = wordH T C Dm v * wordT T w
          + wordD Dm v * wordH T C Dm w := by
    intro v w
    induction v with
    | nil => simp [wordH, wordD]
    | cons a v ih =>
        simp only [List.cons_append, wordH, wordD, hT, ih,
          Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        abel
  have hHa : ∀ a : σ, wordH T C Dm [a] = C a := by
    intro a
    simp [wordH, wordT]
  refine ⟨hT, hD, hH, ?_, ?_, ?_, ?_, ?_⟩
  · intro a w
    rw [show (a :: w) = [a] ++ w from rfl, hH, hHa]
    simp only [wordD, Matrix.mul_one]
    abel
  · intro a v hv
    induction hv using Submodule.span_induction with
    | mem u hu =>
        obtain ⟨s, ⟨w, rfl⟩, x, rfl⟩ := hu
        have hkey : Dm a *ᵥ (wordH T C Dm w *ᵥ x)
            = wordH T C Dm (a :: w) *ᵥ x
              - wordH T C Dm [a] *ᵥ (wordT T w *ᵥ x) := by
          simp only [Matrix.mulVec_mulVec]
          rw [show (a :: w) = [a] ++ w from rfl, hH, hHa]
          simp only [wordD, Matrix.mul_one,
            Matrix.add_mulVec]
          abel
        rw [hkey]
        apply Submodule.sub_mem
        · apply Submodule.subset_span
          exact Set.mem_iUnion.mpr ⟨a :: w, ⟨x, rfl⟩⟩
        · apply Submodule.subset_span
          exact Set.mem_iUnion.mpr
            ⟨[a], ⟨wordT T w *ᵥ x, rfl⟩⟩
    | zero =>
        rw [Matrix.mulVec_zero]
        exact Submodule.zero_mem _
    | add u u' _ _ hu hu' =>
        rw [Matrix.mulVec_add]
        exact Submodule.add_mem _ hu hu'
    | smul t u _ hu =>
        rw [Matrix.mulVec_smul]
        exact Submodule.smul_mem _ _ hu
  · intro a v hv
    rw [provNull, Submodule.mem_iInf] at hv ⊢
    intro p
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, Matrix.mul_assoc,
      show wordD Dm p.2 * Dm a
          = wordD Dm (p.2 ++ [a]) from by
        rw [hD, wordD, wordD, Matrix.mul_one]]
    have h := hv (p.1, p.2 ++ [a])
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h
    simpa using h
  · exact Submodule.finrank_quotient_add_finrank _
  · intro lam w u u' huu
    rw [provNull, Submodule.mem_iInf] at huu
    have h := huu (lam, w)
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply,
      Matrix.mulVec_sub] at h
    exact sub_eq_zero.mp h

end NCG
