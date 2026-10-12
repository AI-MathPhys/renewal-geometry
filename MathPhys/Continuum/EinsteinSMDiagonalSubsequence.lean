/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The subsequence principle and diagonal extraction

* `exists_strictMono_of_range`: a strictly increasing sequence whose tail lies in the range of a
  strictly increasing `F` is a subsequence of `F` along its tail;
* `tendsto_of_forall_strictMono_subseq`: the subsequence principle;
* `exists_diagonal_subseq`: diagonal extraction for countably many extraction-stable,
  tail-determined properties of subsequences.

Split out of `MathPhys.Continuum.EinsteinSMCertificatePacket` (`exists_strictMono_of_range`
out of `MathPhys.Continuum.EinsteinSMReducedClosure`); both re-export it; names are
unchanged.
-/

open Filter Topology Set

namespace MathPhys
namespace EinsteinSM

/-- A strictly increasing sequence whose tail lies in the range of a strictly increasing `F` is a
subsequence of `F` along its tail. -/
theorem exists_strictMono_of_range {F D : ℕ → ℕ} (hF : StrictMono F) (hD : StrictMono D) (m : ℕ)
    (h : ∀ k, D (k + m) ∈ range F) : ∃ χ : ℕ → ℕ, StrictMono χ ∧ ∀ k, D (k + m) = F (χ k) := by
  choose χ hχ using h
  refine ⟨χ, fun a b hab => ?_, fun k => (hχ k).symm⟩
  have : F (χ a) < F (χ b) := by rw [hχ a, hχ b]; exact hD (by omega)
  exact hF.lt_iff_lt.mp this

/-! ### The subsequence principle and diagonal extraction -/

section GenericSubseq

/-- **Subsequence principle**: if every subsequence has a further subsequence converging to `x`,
the sequence converges to `x`. -/
theorem tendsto_of_forall_strictMono_subseq {X : Type*} [TopologicalSpace X] {f : ℕ → X} {x : X}
    (h : ∀ s : ℕ → ℕ, StrictMono s → ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => f (s (φ k))) atTop (𝓝 x)) : Tendsto f atTop (𝓝 x) := by
  by_contra hf
  obtain ⟨U, hU, hfreq⟩ := not_tendsto_iff_exists_frequently_notMem.mp hf
  obtain ⟨s, hs, hsU⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨φ, -, hφ⟩ := h s hs
  obtain ⟨k, hk⟩ := (hφ.eventually hU).exists
  exact hsU (φ k) hk

/-- **Diagonal extraction** for countably many properties `P m` of subsequences that can always be
achieved by further extraction, are stable under further extraction and are determined by tails:
there is one subsequence satisfying all of them. -/
theorem exists_diagonal_subseq (P : ℕ → (ℕ → ℕ) → Prop)
    (hex : ∀ m (s : ℕ → ℕ), StrictMono s → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ P m (s ∘ ψ))
    (hcomp : ∀ m (s ψ : ℕ → ℕ), StrictMono ψ → P m s → P m (s ∘ ψ))
    (htail : ∀ m (s : ℕ → ℕ) (k : ℕ), StrictMono s → P m (fun j => s (j + k)) → P m s) :
    ∃ D : ℕ → ℕ, StrictMono D ∧ ∀ m, P m D := by
  choose ψ hψ hP using hex
  let Φ : ℕ → {f : ℕ → ℕ // StrictMono f} := fun m => Nat.rec
    ⟨ψ 0 id strictMono_id, hψ 0 id strictMono_id⟩
    (fun m F => ⟨F.1 ∘ ψ (m + 1) F.1 F.2, F.2.comp (hψ _ _ _)⟩) m
  have hΦs : ∀ m, (Φ (m + 1)).1 = (Φ m).1 ∘ ψ (m + 1) (Φ m).1 (Φ m).2 := fun m => rfl
  have hPm : ∀ m, P m (Φ m).1 := by
    intro m
    cases m with
    | zero => exact hP 0 id strictMono_id
    | succ m => exact hP (m + 1) (Φ m).1 (Φ m).2
  set D : ℕ → ℕ := fun k => (Φ k).1 k with hD
  have hDs : StrictMono D := by
    refine strictMono_nat_of_lt_succ fun k => ?_
    show (Φ k).1 k < (Φ (k + 1)).1 (k + 1)
    rw [hΦs k]
    exact (Φ k).2.lt_iff_lt.mpr (Nat.lt_of_lt_of_le (Nat.lt_succ_self k)
      ((hψ (k + 1) (Φ k).1 (Φ k).2).id_le (k + 1)))
  have hrange : ∀ m k, m ≤ k → range (Φ k).1 ⊆ range (Φ m).1 := by
    intro m k hmk
    induction k, hmk using Nat.le_induction with
    | base => exact le_rfl
    | succ k _ ih =>
      rw [hΦs k]
      exact (range_comp_subset_range _ _).trans ih
  refine ⟨D, hDs, fun m => ?_⟩
  obtain ⟨χ, hχ, hχD⟩ := exists_strictMono_of_range (Φ m).2 hDs m
    (fun k => hrange m (k + m) (by omega) ⟨k + m, rfl⟩)
  refine htail m D m hDs ?_
  have e : (fun j => D (j + m)) = (Φ m).1 ∘ χ := funext hχD
  rw [e]
  exact hcomp m (Φ m).1 χ hχ (hPm m)

end GenericSubseq

end EinsteinSM
end MathPhys
