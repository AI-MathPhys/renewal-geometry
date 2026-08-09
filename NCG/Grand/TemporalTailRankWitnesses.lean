import NCG.Grand.FeedbackWitnesses
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.Matrix.Hermitian

/-!
# temporal-tail and rank-growth witnesses

This file extracts the escaping finite windows from the literal negation of
uniform finite-tail tightness, strengthens the finite-input pigeonhole step to
one direction recurring arbitrarily far out, and identifies the manuscript's
positive `(M+1)`st singular value with rank strictly larger than `M`.
-/

open Filter Matrix

namespace NCG

/-- Uniform `ℓ¹` tail tightness expressed entirely by finite tail packets.  For
nonnegative summable kernels this is equivalent to the usual infinite-tail
formulation, while being exactly the finite witness used in the manuscript. -/
def UniformFiniteTail (a : ℕ → ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ K, ∀ n (s : Finset ℕ),
    (∀ k ∈ s, K ≤ k) → ∑ k ∈ s, a n k < ε

/-- The maximum of a finite packet, with the harmless value `0` on the empty
packet.  This proof-independent wrapper lets a witness theorem state its
maximal-atom alternative without embedding a proof of nonemptiness in its
type. -/
def packetMax (a : ℕ → ℕ → ℝ) (s : ℕ → Finset ℕ) (j : ℕ) : ℝ :=
  if h : (s j).Nonempty then (s j).sup' h (a j) else 0

/-- Failure of uniform tail tightness produces finite windows whose supports
escape to infinity and whose masses stay uniformly positive. -/
theorem escaping_windows_of_not_uniformFiniteTail
    (a : ℕ → ℕ → ℝ) (_hnn : ∀ n k, 0 ≤ a n k)
    (hfail : ¬ UniformFiniteTail a) :
    ∃ ε > 0, ∃ n : ℕ → ℕ, ∃ s : ℕ → Finset ℕ,
      (∀ j, (s j).Nonempty)
      ∧ (∀ j k, k ∈ s j → j ≤ k)
      ∧ (∀ j, ε ≤ ∑ k ∈ s j, a (n j) k) := by
  rw [UniformFiniteTail] at hfail
  push Not at hfail
  obtain ⟨ε, hε, hbad⟩ := hfail
  choose n s htail hmass using hbad
  refine ⟨ε, hε, n, s, ?_, htail, hmass⟩
  intro j
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have hj : ε ≤ 0 := by simpa [hne] using hmass j
  linarith

/-- In a fixed finite input dimension, one basis direction captures the
`ε/d` fraction for packets occurring arbitrarily far out. -/
theorem recurring_input_direction
    {d : ℕ} (hd : 0 < d) (ε : ℝ) (hε : 0 < ε)
    (f : ℕ → Fin d → ℝ) (_hf : ∀ j i, 0 ≤ f j i)
    (hmass : ∀ j, ε ≤ ∑ i, f j i) :
    ∃ i : Fin d, ∀ J, ∃ j ≥ J, ε / d ≤ f j i := by
  classical
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  by_contra hnone
  push Not at hnone
  choose cutoff hcutoff using hnone
  let J : ℕ := Finset.univ.sup cutoff
  have hJi : ∀ i : Fin d, cutoff i ≤ J := by
    intro i
    exact Finset.le_sup (Finset.mem_univ i)
  have hlt : ∀ i : Fin d, f J i < ε / d := by
    intro i
    exact hcutoff i J (hJi i)
  have hsumlt : ∑ i, f J i < ∑ _i : Fin d, ε / d :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      (fun i _ => hlt i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsumlt
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdeq : (d : ℝ) * (ε / d) = ε := by field_simp
  linarith [hmass J]

/-- Matrix rank is exactly the number of positive singular values; thus the
manuscript's `(M+1)`st singular-value witness is equivalent to rank `> M`.
Singular values are zero-indexed in Mathlib. -/
theorem matrix_singularValue_pos_iff_rank_gt
    {p q : Type} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    (H : Matrix p q ℂ) (M : ℕ) :
    0 < H.toEuclideanLin.singularValues M ↔ M < H.rank := by
  rw [LinearMap.singularValues_pos_iff_lt_finrank_range]
  rw [H.rank_eq_finrank_range_toLin
    (EuclideanSpace.basisFun p ℂ).toBasis
    (EuclideanSpace.basisFun q ℂ).toBasis]
  rfl

/-- `thm:feedback-witnesses`, exact assembly from failure of uniform tail
tightness through the T1/T2 alternatives and the singular-value rank witness. -/
theorem feedback_witnesses_exact
    (a : ℕ → ℕ → ℝ) (hnn : ∀ n k, 0 ≤ a n k)
    (hfail : ¬ UniformFiniteTail a) :
    ∃ ε > 0, ∃ n : ℕ → ℕ, ∃ s : ℕ → Finset ℕ,
      (∀ j, (s j).Nonempty)
      ∧ (∀ j k, k ∈ s j → j ≤ k)
      ∧ (∀ j, ε ≤ ∑ k ∈ s j, a (n j) k)
      ∧ ((Tendsto (packetMax (fun j k => a (n j) k) s)
            atTop (nhds 0)
          ∨ ∃ η > 0, ∀ J, ∃ j ≥ J,
            η ≤ packetMax (fun j k => a (n j) k) s j)
        ∧ (Tendsto (packetMax (fun j k => a (n j) k) s)
              atTop (nhds 0) →
            Tendsto (fun j => ((s j).card : ℝ)) atTop atTop)) := by
  obtain ⟨ε, hε, n, s, hne, htail, hmass⟩ :=
    escaping_windows_of_not_uniformFiniteTail a hnn hfail
  have hw := feedback_witnesses (fun j k => a (n j) k) s ε hε
    (fun j k => hnn (n j) k) hne hmass
  have hpacket : packetMax (fun j k => a (n j) k) s =
      fun j => (s j).sup' (hne j) (a (n j)) := by
    funext j
    simp only [packetMax, dif_pos (hne j)]
  refine ⟨ε, hε, n, s, hne, htail, hmass, ?_⟩
  rw [hpacket]
  exact ⟨hw.1, hw.2.1⟩

end NCG
