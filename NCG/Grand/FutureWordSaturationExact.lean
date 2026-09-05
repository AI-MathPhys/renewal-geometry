/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Future-word saturation: the flat depth of the return-map kernels

Exact finite-dimensional encoding of `thm:GT-future-word-saturation`.

Primitive operations `L a : E →ₗ[ℂ] E` (including the loop generator) act on
the future-visible quotient `E`, and `S : E →ₗ[ℂ] F` is the return readout.
The depth-`r` future kernel `futureKernel L S r = ⋂_{|w| ≤ r} Ker(S ∘ w)` is
the kernel of the observability Gram `𝕆_r^fut = ∑_{|w| ≤ r} w^* S^* S w`, so
rank monotonicity of the Grams is antitonicity of the kernels.

* `futureKernel_succ`: `K_{r+1} = K_r ⊓ ⨅_a L_a⁻¹(K_r)`; `futureKernel_antitone`;
* `futureKernel_eq_iff_invariant`: `K_{r+1} = K_r` iff `K_r` is invariant under
  every primitive operation;
* `futureKernel_eq_of_stable`: rank equality at depth `r` freezes the chain —
  no later mixed word changes the kernel;
* `exists_flat_depth`: the first flat depth is at most `finrank E`;
* `futureKernel_eq_iInter`: `K_r` is exactly the joint kernel of all return
  maps of length `≤ r` (so `Ker S w x = 0` for every word at the flat depth:
  `sealed_reads_zero`), and `not_sealed_reads`: a vector outside the sealed
  kernel is detected by some return word.
-/

open Submodule

namespace NCG
namespace FutureWordSaturation

variable {ι E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]

/-- The return map of a word, letters applied in list order:
`readWord [] = S`, `readWord (a :: w) = readWord w ∘ L a`. -/
def readWord (L : ι → E →ₗ[ℂ] E) (S : E →ₗ[ℂ] F) : List ι → E →ₗ[ℂ] F
  | [] => S
  | a :: w => readWord L S w ∘ₗ L a

theorem readWord_cons (L : ι → E →ₗ[ℂ] E) (S : E →ₗ[ℂ] F) (a : ι) (w : List ι) :
    readWord L S (a :: w) = readWord L S w ∘ₗ L a := rfl

/-- The depth-`r` future kernel, built recursively:
`K_0 = Ker S`, `K_{r+1} = K_r ⊓ ⨅_a L_a⁻¹(K_r)`. -/
def futureKernel (L : ι → E →ₗ[ℂ] E) (S : E →ₗ[ℂ] F) : ℕ → Submodule ℂ E
  | 0 => LinearMap.ker S
  | r + 1 => futureKernel L S r ⊓ ⨅ a, (futureKernel L S r).comap (L a)

theorem futureKernel_zero (L : ι → E →ₗ[ℂ] E) (S : E →ₗ[ℂ] F) :
    futureKernel L S 0 = LinearMap.ker S := rfl

theorem futureKernel_succ (L : ι → E →ₗ[ℂ] E) (S : E →ₗ[ℂ] F) (r : ℕ) :
    futureKernel L S (r + 1) = futureKernel L S r ⊓ ⨅ a, (futureKernel L S r).comap (L a) := rfl

/-- Ranks of the observability Grams are nondecreasing: the kernels decrease. -/
theorem futureKernel_antitone (L : ι → E →ₗ[ℂ] E) (S : E →ₗ[ℂ] F) :
    Antitone (futureKernel L S) := by
  refine antitone_nat_of_succ_le fun r => ?_
  rw [futureKernel_succ]
  exact inf_le_left

/-- `K_r` is the joint kernel of all return maps `readWord w` with `|w| ≤ r`. -/
theorem futureKernel_eq_iInter (L : ι → E →ₗ[ℂ] E) (S : E →ₗ[ℂ] F) (r : ℕ) :
    futureKernel L S r = ⨅ w : {w : List ι // w.length ≤ r}, LinearMap.ker (readWord L S w.1) := by
  induction r with
  | zero =>
    rw [futureKernel_zero]
    apply le_antisymm
    · refine le_iInf fun w => ?_
      obtain ⟨w, hw⟩ := w
      have hnil : w = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hw)
      subst hnil
      simp [readWord]
    · exact iInf_le_of_le ⟨[], le_rfl⟩ (by simp [readWord])
  | succ r ih =>
    rw [futureKernel_succ, ih]
    apply le_antisymm
    · refine le_iInf fun w => ?_
      obtain ⟨w, hw⟩ := w
      cases w with
      | nil =>
        exact le_trans inf_le_left (iInf_le_of_le ⟨[], by simp⟩ le_rfl)
      | cons a w' =>
        rw [readWord_cons, LinearMap.ker_comp]
        refine le_trans inf_le_right (le_trans (iInf_le _ a) ?_)
        rw [Submodule.comap_iInf]
        exact iInf_le_of_le ⟨w', by simp at hw; omega⟩ le_rfl
    · refine le_inf ?_ (le_iInf fun a => ?_)
      · refine le_iInf fun w => ?_
        exact iInf_le_of_le ⟨w.1, le_trans w.2 (Nat.le_succ r)⟩ le_rfl
      · rw [Submodule.comap_iInf]
        refine le_iInf fun w => ?_
        refine iInf_le_of_le ⟨a :: w.1, by rw [List.length_cons]; exact Nat.succ_le_succ w.2⟩ ?_
        rw [readWord_cons, LinearMap.ker_comp]

/-- **Flatness criterion**: `K_{r+1} = K_r` iff `K_r` is invariant under every
primitive operation. -/
theorem futureKernel_eq_iff_invariant (L : ι → E →ₗ[ℂ] E) (S : E →ₗ[ℂ] F) (r : ℕ) :
    futureKernel L S (r + 1) = futureKernel L S r ↔
      ∀ a, (futureKernel L S r).map (L a) ≤ futureKernel L S r := by
  rw [futureKernel_succ]
  constructor
  · intro h a
    rw [Submodule.map_le_iff_le_comap]
    calc futureKernel L S r = futureKernel L S r ⊓ ⨅ a, (futureKernel L S r).comap (L a) := h.symm
      _ ≤ ⨅ a, (futureKernel L S r).comap (L a) := inf_le_right
      _ ≤ (futureKernel L S r).comap (L a) := iInf_le _ a
  · intro h
    refine le_antisymm inf_le_left (le_inf le_rfl (le_iInf fun a => ?_))
    rw [← Submodule.map_le_iff_le_comap]
    exact h a

/-- **Saturation**: once the chain is flat at depth `r` it is constant from `r` on. -/
theorem futureKernel_eq_of_stable (L : ι → E →ₗ[ℂ] E) (S : E →ₗ[ℂ] F) {r : ℕ}
    (hflat : futureKernel L S (r + 1) = futureKernel L S r) {m : ℕ} (hm : r ≤ m) :
    futureKernel L S m = futureKernel L S r := by
  induction m with
  | zero =>
    have : r = 0 := by omega
    subst this; rfl
  | succ m ih =>
    rcases Nat.lt_or_ge m r with hlt | hge
    · have : r = m + 1 := by omega
      subst this; rfl
    · have hm' := ih hge
      have hinv := (futureKernel_eq_iff_invariant L S r).mp hflat
      rw [← hm'] at hinv
      rw [(futureKernel_eq_iff_invariant L S m).mpr hinv, hm']

/-- **Flat depth bound**: the chain becomes flat at some depth `≤ finrank E`. -/
theorem exists_flat_depth [FiniteDimensional ℂ E] (L : ι → E →ₗ[ℂ] E) (S : E →ₗ[ℂ] F) :
    ∃ r ≤ Module.finrank ℂ E, futureKernel L S (r + 1) = futureKernel L S r := by
  by_contra hcon
  push Not at hcon
  have hstrict : ∀ r ≤ Module.finrank ℂ E, futureKernel L S (r + 1) < futureKernel L S r :=
    fun r hr => lt_of_le_of_ne (futureKernel_antitone L S (Nat.le_succ r)) (hcon r hr)
  have hdrop : ∀ k, k ≤ Module.finrank ℂ E + 1 →
      Module.finrank ℂ (futureKernel L S k) + k ≤ Module.finrank ℂ E := by
    intro k
    induction k with
    | zero => intro _; simpa using Submodule.finrank_le (futureKernel L S 0)
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := Submodule.finrank_lt_finrank_of_lt (hstrict k (by omega))
      omega
  have := hdrop (Module.finrank ℂ E + 1) le_rfl
  omega

/-- **Sealed provenance** (FC.2): vectors in the flat kernel are invisible to
every future return word. -/
theorem sealed_reads_zero (L : ι → E →ₗ[ℂ] E) (S : E →ₗ[ℂ] F) {r : ℕ}
    (hflat : futureKernel L S (r + 1) = futureKernel L S r) (x : E)
    (hx : x ∈ futureKernel L S r) (w : List ι) : readWord L S w x = 0 := by
  have hmem : x ∈ futureKernel L S (max r w.length) := by
    rw [futureKernel_eq_of_stable L S hflat (le_max_left _ _)]
    exact hx
  rw [futureKernel_eq_iInter] at hmem
  have := Submodule.mem_iInf _ |>.mp hmem ⟨w, le_max_right _ _⟩
  simpa [LinearMap.mem_ker] using this

/-- A vector outside the sealed kernel is detected by some return word of
length `≤ r`. -/
theorem not_sealed_reads (L : ι → E →ₗ[ℂ] E) (S : E →ₗ[ℂ] F) (r : ℕ) (x : E)
    (hx : x ∉ futureKernel L S r) : ∃ w : List ι, w.length ≤ r ∧ readWord L S w x ≠ 0 := by
  rw [futureKernel_eq_iInter] at hx
  by_contra hcon
  push Not at hcon
  apply hx
  rw [Submodule.mem_iInf]
  intro w
  simpa [LinearMap.mem_ker] using hcon w.1 w.2

end FutureWordSaturation
end NCG
