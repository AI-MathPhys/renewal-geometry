/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.DecoderInnovationConditionalInformation
import Mathlib

/-!
# Finite future-saturated experiment state

Multi-operator Krylov saturation of a finite experiment, followed by its
intrinsic projective-column quotient and exact common-decoder recursion.
-/

open Finset
open Module

namespace NCG
open AcceptedActionInformationPythagoras
open CanonicalFiniteExperimentQuotient
open ComparisonSignatureQuotient
namespace FiniteFutureSaturatedExperimentState

variable {I U A : Type*} [Fintype U]

/-- Apply a word of later update letters to a row. -/
def applyWord (K : A → Module.End ℝ (U → ℝ)) :
    List A → (U → ℝ) → (U → ℝ)
  | [], f => f
  | a :: w, f => applyWord K w (K a f)

@[simp] theorem applyWord_nil (K : A → Module.End ℝ (U → ℝ))
    (f : U → ℝ) : applyWord K [] f = f := rfl

@[simp] theorem applyWord_cons (K : A → Module.End ℝ (U → ℝ))
    (a : A) (w : List A) (f : U → ℝ) :
    applyWord K (a :: w) f = applyWord K w (K a f) := rfl

/-- The span of all experiment rows reachable by finite update words. -/
def futureSpan (rows : I → U → ℝ)
    (K : A → Module.End ℝ (U → ℝ)) : Submodule ℝ (U → ℝ) :=
  Submodule.span ℝ {f | ∃ i w, f = applyWord K w (rows i)}

/-- The concrete chain `V₀`, `V₁`, ... generated one letter at a time. -/
def futureStage (rows : I → U → ℝ)
    (K : A → Module.End ℝ (U → ℝ)) :
    ℕ → Submodule ℝ (U → ℝ)
  | 0 => Submodule.span ℝ (Set.range rows)
  | n + 1 => futureStage rows K n ⊔
      ⨆ a, Submodule.map (K a) (futureStage rows K n)

theorem futureStage_mono_step (rows : I → U → ℝ)
    (K : A → Module.End ℝ (U → ℝ)) (n : ℕ) :
    futureStage rows K n ≤ futureStage rows K (n + 1) := by
  rw [futureStage]
  exact le_sup_left

theorem futureStage_mono (rows : I → U → ℝ)
    (K : A → Module.End ℝ (U → ℝ)) :
    Monotone (futureStage rows K) :=
  monotone_nat_of_le_succ (futureStage_mono_step rows K)

theorem row_mem_futureStage_zero (rows : I → U → ℝ)
    (K : A → Module.End ℝ (U → ℝ)) (i : I) :
    rows i ∈ futureStage rows K 0 := by
  exact Submodule.subset_span ⟨i, rfl⟩

theorem map_futureStage_le_succ (rows : I → U → ℝ)
    (K : A → Module.End ℝ (U → ℝ)) (a : A) (n : ℕ) :
    Submodule.map (K a) (futureStage rows K n) ≤ futureStage rows K (n + 1) := by
  rw [futureStage]
  exact le_sup_of_le_right (le_iSup (fun b ↦ Submodule.map (K b) (futureStage rows K n)) a)

theorem applyWord_mem_futureStage_add (rows : I → U → ℝ)
    (K : A → Module.End ℝ (U → ℝ)) (w : List A)
    {n : ℕ} {f : U → ℝ} (hf : f ∈ futureStage rows K n) :
    applyWord K w f ∈ futureStage rows K (n + w.length) := by
  induction w generalizing n f with
  | nil => simpa using hf
  | cons a w ih =>
      have hKa : K a f ∈ futureStage rows K (n + 1) :=
        map_futureStage_le_succ rows K a n ⟨f, hf, rfl⟩
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih hKa

theorem applyWord_mem_futureStage (rows : I → U → ℝ)
    (K : A → Module.End ℝ (U → ℝ)) (i : I) (w : List A) :
    applyWord K w (rows i) ∈ futureStage rows K w.length := by
  simpa using applyWord_mem_futureStage_add rows K w
    (row_mem_futureStage_zero rows K i)

theorem applyWord_append (K : A → Module.End ℝ (U → ℝ))
    (v w : List A) (f : U → ℝ) :
    applyWord K (v ++ w) f = applyWord K w (applyWord K v f) := by
  induction v generalizing f with
  | nil => rfl
  | cons a v ih => simpa using ih (K a f)

/-- The saturated span is invariant under every later update letter. -/
theorem futureSpan_invariant (rows : I → U → ℝ)
    (K : A → Module.End ℝ (U → ℝ)) (a : A) :
    Submodule.map (K a) (futureSpan rows K) ≤ futureSpan rows K := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.2
  rintro f ⟨i, w, rfl⟩
  change K a (applyWord K w (rows i)) ∈ futureSpan rows K
  apply Submodule.subset_span
  refine ⟨i, w ++ [a], ?_⟩
  rw [applyWord_append]
  rfl

theorem futureStage_le_futureSpan (rows : I → U → ℝ)
    (K : A → Module.End ℝ (U → ℝ)) (n : ℕ) :
    futureStage rows K n ≤ futureSpan rows K := by
  induction n with
  | zero =>
      apply Submodule.span_le.2
      rintro f ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, [], rfl⟩
  | succ n ih =>
      rw [futureStage]
      apply sup_le ih
      apply iSup_le
      intro a
      exact (Submodule.map_mono ih).trans (futureSpan_invariant rows K a)

/-- The stable value of the concrete chain is exactly the span of all word
rows, rather than merely an abstract eventual fixed point. -/
theorem iSup_futureStage_eq_futureSpan (rows : I → U → ℝ)
    (K : A → Module.End ℝ (U → ℝ)) :
    (⨆ n, futureStage rows K n) = futureSpan rows K := by
  apply le_antisymm
  · exact iSup_le (futureStage_le_futureSpan rows K)
  · apply Submodule.span_le.2
    rintro f ⟨i, w, rfl⟩
    exact le_iSup (futureStage rows K) w.length
      (applyWord_mem_futureStage rows K i w)

/-- Once one Krylov layer is flat, every later layer is equal to it. -/
theorem futureStage_stable_of_eq (rows : I → U → ℝ)
    (K : A → Module.End ℝ (U → ℝ)) (n : ℕ)
    (hflat : futureStage rows K (n + 1) = futureStage rows K n) :
    ∀ k, futureStage rows K (n + k) = futureStage rows K n := by
  have hinvariant (a : A) :
      Submodule.map (K a) (futureStage rows K n) ≤ futureStage rows K n := by
    calc
      Submodule.map (K a) (futureStage rows K n) ≤
          futureStage rows K (n + 1) := map_futureStage_le_succ rows K a n
      _ = futureStage rows K n := hflat
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Nat.add_succ, futureStage, ih]
      apply sup_eq_left.2
      exact iSup_le hinvariant

theorem futureStage_finrank_growth (rows : I → U → ℝ)
    (K : A → Module.End ℝ (U → ℝ)) (n : ℕ)
    (hstrict : ∀ r < n, futureStage rows K r < futureStage rows K (r + 1)) :
    Module.finrank ℝ (futureStage rows K 0) + n ≤
      Module.finrank ℝ (futureStage rows K n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hprev := ih (fun r hr ↦ hstrict r (Nat.lt_succ_of_lt hr))
      have hstep := Submodule.finrank_lt_finrank_of_lt
        (hstrict n (Nat.lt_succ_self n))
      omega

/-- There can be at most `|U| - dim V₀` strict rank increases. -/
theorem futureStage_strict_rank_increase_bound (rows : I → U → ℝ)
    (K : A → Module.End ℝ (U → ℝ)) (n : ℕ)
    (hstrict : ∀ r < n, futureStage rows K r < futureStage rows K (r + 1)) :
    n ≤ Fintype.card U - Module.finrank ℝ (futureStage rows K 0) := by
  have hgrowth := futureStage_finrank_growth rows K n hstrict
  have hambient : Module.finrank ℝ (futureStage rows K n) ≤ Fintype.card U := by
    calc
      Module.finrank ℝ (futureStage rows K n) ≤
          Module.finrank ℝ (U → ℝ) := Submodule.finrank_le _
      _ = Fintype.card U := by simp
  omega

/-- Some layer is already flat within the manuscript's dimension bound. -/
theorem futureStage_stabilizes_within_dimension_bound (rows : I → U → ℝ)
    (K : A → Module.End ℝ (U → ℝ)) :
    ∃ n ≤ Fintype.card U - Module.finrank ℝ (futureStage rows K 0),
      futureStage rows K (n + 1) = futureStage rows K n := by
  let d := Fintype.card U - Module.finrank ℝ (futureStage rows K 0)
  by_contra hnone
  push_neg at hnone
  have hstrict : ∀ r < d + 1,
      futureStage rows K r < futureStage rows K (r + 1) := by
    intro r hr
    have hrle : r ≤ d := by omega
    exact lt_of_le_of_ne (futureStage_mono_step rows K r)
      (Ne.symm (hnone r hrle))
  have hbound := futureStage_strict_rank_increase_bound rows K (d + 1) hstrict
  dsimp [d] at hbound
  omega

theorem stabilized_futureStage_eq_futureSpan (rows : I → U → ℝ)
    (K : A → Module.End ℝ (U → ℝ)) (n : ℕ)
    (hflat : futureStage rows K (n + 1) = futureStage rows K n) :
    futureStage rows K n = futureSpan rows K := by
  rw [← iSup_futureStage_eq_futureSpan]
  apply le_antisymm
  · exact le_iSup (futureStage rows K) n
  · apply iSup_le
    intro k
    by_cases hkn : k ≤ n
    · exact futureStage_mono rows K hkn
    · have hnk : n ≤ k := Nat.le_of_lt (Nat.lt_of_not_ge hkn)
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnk
      exact le_of_eq (futureStage_stable_of_eq rows K n hflat j)

/-- The intrinsic row family indexed by the saturated subspace itself.  This
avoids making the future quotient depend on a chosen basis. -/
def saturatedRows (rows : I → U → ℝ)
    (K : A → Module.End ℝ (U → ℝ)) :
    futureSpan rows K → U → ℝ := fun f ↦ f.1

/-- The future-saturated projective-column quotient. -/
abbrev FutureQuotient (rows : I → U → ℝ)
    (K : A → Module.End ℝ (U → ℝ)) (mixture : U → ℝ) :=
  CanonicalFiniteExperimentQuotient.Quotient (saturatedRows rows K) mixture

noncomputable def futureQuotientMap (rows : I → U → ℝ)
    (K : A → Module.End ℝ (U → ℝ)) (mixture : U → ℝ) :
    U → FutureQuotient rows K mixture :=
  quotientMap (saturatedRows rows K) mixture

noncomputable def futureDecoder (rows : I → U → ℝ)
    (K : A → Module.End ℝ (U → ℝ)) (mixture : U → ℝ) :
    FutureQuotient rows K mixture → U → ℝ :=
  decoder (saturatedRows rows K) mixture

/-- Intrinsic ratio-level-set description.  Quantifying over the subspace
shows directly that the quotient is independent of any displayed basis. -/
theorem futureQuotientMap_eq_iff (rows : I → U → ℝ)
    (K : A → Module.End ℝ (U → ℝ)) (mixture : U → ℝ)
    (u v : U) :
    futureQuotientMap rows K mixture u = futureQuotientMap rows K mixture v ↔
      ∀ f ∈ futureSpan rows K,
        f u / mixture u = f v / mixture v := by
  rw [futureQuotientMap, quotientMap_eq_iff]
  constructor
  · intro h f hf
    exact h ⟨f, hf⟩
  · intro h f
    exact h f f.property

/-- Any basis of the saturated space defines exactly the same ratio level
sets as the intrinsic all-row signature. -/
theorem basis_ratio_level_sets_eq_futureQuotient
    {J : Type*} (rows : I → U → ℝ)
    (K : A → Module.End ℝ (U → ℝ)) (mixture : U → ℝ)
    (hmixture : ∀ u, 0 < mixture u)
    (b : Basis J ℝ (futureSpan rows K)) (u v : U) :
    (∀ j, (b j).1 u / mixture u = (b j).1 v / mixture v) ↔
      futureQuotientMap rows K mixture u = futureQuotientMap rows K mixture v := by
  rw [futureQuotientMap_eq_iff]
  constructor
  · intro hb f hf
    have hcrossBasis (j : J) :
        (b j).1 u * mixture v = (b j).1 v * mixture u := by
      have hj := hb j
      field_simp [ne_of_gt (hmixture u), ne_of_gt (hmixture v)] at hj
      simpa [mul_comm] using hj
    let W : Submodule ℝ (futureSpan rows K) :=
      { carrier := {f | f.1 u * mixture v = f.1 v * mixture u}
        zero_mem' := by simp
        add_mem' := by
          intro f g hf hg
          change (f.1 u + g.1 u) * mixture v =
            (f.1 v + g.1 v) * mixture u
          rw [add_mul, add_mul, hf, hg]
        smul_mem' := by
          intro c f hf
          change (c * f.1 u) * mixture v = (c * f.1 v) * mixture u
          rw [mul_assoc, mul_assoc, hf] }
    have hbW : ∀ j, b j ∈ W := by
      intro j
      exact hcrossBasis j
    have hWtop : W = ⊤ := by
      apply top_unique
      rw [← b.span_eq]
      exact Submodule.span_le.2 fun x hx ↦ by
        obtain ⟨j, rfl⟩ := hx
        exact hbW j
    have hfW : ⟨f, hf⟩ ∈ W := hWtop.symm ▸ Submodule.mem_top
    change f u * mixture v = f v * mixture u at hfW
    apply (div_eq_div_iff (ne_of_gt (hmixture u)) (ne_of_gt (hmixture v))).2
    exact hfW
  · intro h j
    exact h (b j).1 (b j).property

/-- Every saturated row is reconstructed by one mixture-native decoder. -/
theorem futureDecoder_reconstructs (rows : I → U → ℝ)
    (K : A → Module.End ℝ (U → ℝ)) (mixture : U → ℝ)
    (hmixture : ∀ u, 0 < mixture u) :
    ∀ f : futureSpan rows K, ∀ u,
      f.1 u = pushforwardRow (futureQuotientMap rows K mixture) f.1
          (futureQuotientMap rows K mixture u) *
        futureDecoder rows K mixture (futureQuotientMap rows K mixture u) u := by
  simpa [futureQuotientMap, futureDecoder, saturatedRows] using
    (common_decoder_reconstructs (saturatedRows rows K) mixture hmixture)

/-- The future quotient is the unique coarsest surjective deterministic record
with one decoder reconstructing every row in the saturated space. -/
theorem futureQuotient_unique_coarsest
    {Z : Type*} [Fintype Z] [DecidableEq Z]
    (rows : I → U → ℝ) (K : A → Module.End ℝ (U → ℝ))
    (mixture : U → ℝ) (hmixture : ∀ u, 0 < mixture u)
    (hmixtureMem : mixture ∈ futureSpan rows K)
    (record : U → Z) (hrecord : Function.Surjective record)
    (commonDecoder : Z → U → ℝ)
    (hreconstruct : ∀ f : futureSpan rows K, ∀ u,
      f.1 u = pushforwardRow record f.1 (record u) * commonDecoder (record u) u) :
    ∃! g : Z → FutureQuotient rows K mixture,
      Function.Surjective g ∧ g ∘ record = futureQuotientMap rows K mixture := by
  let mixtureRow : futureSpan rows K := ⟨mixture, hmixtureMem⟩
  have hmixreconstruct (u : U) : mixture u =
      pushforwardRow record mixture (record u) * commonDecoder (record u) u := by
    simpa [mixtureRow] using hreconstruct mixtureRow u
  have hratio (f : futureSpan rows K) (u : U) : f.1 u / mixture u =
      pushforwardRow record f.1 (record u) /
        pushforwardRow record mixture (record u) := by
    rw [hreconstruct f u, hmixreconstruct u]
    have hD : commonDecoder (record u) u ≠ 0 := by
      intro hzero
      have hpos := hmixture u
      rw [hmixreconstruct u, hzero, mul_zero] at hpos
      exact (ne_of_gt hpos) rfl
    field_simp [hD]
  have hfibre : ∀ {u v}, record u = record v →
      futureQuotientMap rows K mixture u = futureQuotientMap rows K mixture v := by
    intro u v huv
    apply (futureQuotientMap_eq_iff rows K mixture u v).2
    intro f hf
    rw [hratio ⟨f, hf⟩ u, hratio ⟨f, hf⟩ v, huv]
  let g := descendThroughSurjection record hrecord
    (futureQuotientMap rows K mixture) hfibre
  have hgcomp : g ∘ record = futureQuotientMap rows K mixture :=
    descendThroughSurjection_comp record hrecord _ hfibre
  have hgsurj : Function.Surjective g := by
    intro z
    obtain ⟨u, rfl⟩ := quotientMap_surjective (saturatedRows rows K) mixture z
    exact ⟨record u, congrFun hgcomp u⟩
  refine ⟨g, ⟨hgsurj, hgcomp⟩, ?_⟩
  intro g' hg'
  exact descendThroughSurjection_unique record hrecord
    (futureQuotientMap rows K mixture) g' hg'.2

/-- The future quotient refines the initial experiment quotient; equivalently,
there is a unique surjection from future cells onto experiment cells. -/
theorem futureQuotient_refines_experimentQuotient
    (rows : I → U → ℝ) (K : A → Module.End ℝ (U → ℝ))
    (mixture : U → ℝ) :
    ∃! g : FutureQuotient rows K mixture →
        CanonicalFiniteExperimentQuotient.Quotient rows mixture,
      Function.Surjective g ∧
        g ∘ futureQuotientMap rows K mixture = quotientMap rows mixture := by
  have hfibre : ∀ {u v}, futureQuotientMap rows K mixture u =
      futureQuotientMap rows K mixture v →
      quotientMap rows mixture u = quotientMap rows mixture v := by
    intro u v huv
    apply (quotientMap_eq_iff rows mixture u v).2
    intro i
    exact (futureQuotientMap_eq_iff rows K mixture u v).1 huv
      (rows i) (Submodule.subset_span ⟨i, [], rfl⟩)
  let g := descendThroughSurjection (futureQuotientMap rows K mixture)
    (quotientMap_surjective (saturatedRows rows K) mixture)
    (quotientMap rows mixture) hfibre
  have hgcomp : g ∘ futureQuotientMap rows K mixture = quotientMap rows mixture :=
    descendThroughSurjection_comp _
      (quotientMap_surjective (saturatedRows rows K) mixture) _ hfibre
  have hgsurj : Function.Surjective g := by
    intro z
    obtain ⟨u, rfl⟩ := quotientMap_surjective rows mixture z
    exact ⟨futureQuotientMap rows K mixture u, congrFun hgcomp u⟩
  refine ⟨g, ⟨hgsurj, hgcomp⟩, ?_⟩
  intro g' hg'
  exact descendThroughSurjection_unique (futureQuotientMap rows K mixture)
    (quotientMap_surjective (saturatedRows rows K) mixture)
    (quotientMap rows mixture) g' hg'.2

/-- Decode a coarse row by the future decoder. -/
noncomputable def decodeFutureRow (rows : I → U → ℝ)
    (K : A → Module.End ℝ (U → ℝ)) (mixture : U → ℝ)
    (q : FutureQuotient rows K mixture → ℝ) : U → ℝ := fun u ↦
  q (futureQuotientMap rows K mixture u) *
    futureDecoder rows K mixture (futureQuotientMap rows K mixture u) u

/-- The compressed update `R_fut K_a C_fut` in row convention. -/
noncomputable def futureCoarseLetter (rows : I → U → ℝ)
    (K : A → Module.End ℝ (U → ℝ)) (mixture : U → ℝ)
    (a : A) (q : FutureQuotient rows K mixture → ℝ) :
    FutureQuotient rows K mixture → ℝ :=
  pushforwardRow (futureQuotientMap rows K mixture)
    (K a (decodeFutureRow rows K mixture q))

theorem decode_pushforward_futureRow (rows : I → U → ℝ)
    (K : A → Module.End ℝ (U → ℝ)) (mixture : U → ℝ)
    (hmixture : ∀ u, 0 < mixture u) (f : futureSpan rows K) :
    decodeFutureRow rows K mixture
      (pushforwardRow (futureQuotientMap rows K mixture) f.1) = f.1 := by
  funext u
  exact (futureDecoder_reconstructs rows K mixture hmixture f u).symm

theorem futureCoarseLetter_pushforward (rows : I → U → ℝ)
    (K : A → Module.End ℝ (U → ℝ)) (mixture : U → ℝ)
    (hmixture : ∀ u, 0 < mixture u) (a : A) (f : futureSpan rows K) :
    futureCoarseLetter rows K mixture a
        (pushforwardRow (futureQuotientMap rows K mixture) f.1) =
      pushforwardRow (futureQuotientMap rows K mixture) (K a f.1) := by
  unfold futureCoarseLetter
  rw [decode_pushforward_futureRow rows K mixture hmixture f]

/-- Apply a word of compressed future updates. -/
noncomputable def applyFutureCoarseWord (rows : I → U → ℝ)
    (K : A → Module.End ℝ (U → ℝ)) (mixture : U → ℝ) :
    List A → (FutureQuotient rows K mixture → ℝ) →
      (FutureQuotient rows K mixture → ℝ)
  | [], q => q
  | a :: w, q => applyFutureCoarseWord rows K mixture w
      (futureCoarseLetter rows K mixture a q)

/-- Exact word recursion for every row in the saturated space. -/
theorem saturatedRow_word_recursion (rows : I → U → ℝ)
    (K : A → Module.End ℝ (U → ℝ)) (mixture : U → ℝ)
    (hmixture : ∀ u, 0 < mixture u) (f : futureSpan rows K) (w : List A) :
    applyWord K w f.1 = decodeFutureRow rows K mixture
      (applyFutureCoarseWord rows K mixture w
        (pushforwardRow (futureQuotientMap rows K mixture) f.1)) := by
  induction w generalizing f with
  | nil => exact (decode_pushforward_futureRow rows K mixture hmixture f).symm
  | cons a w ih =>
      let Kf : futureSpan rows K :=
        ⟨K a f.1, futureSpan_invariant rows K a ⟨f.1, f.property, rfl⟩⟩
      change applyWord K w Kf.1 = decodeFutureRow rows K mixture
        (applyFutureCoarseWord rows K mixture w
          (futureCoarseLetter rows K mixture a
            (pushforwardRow (futureQuotientMap rows K mixture) f.1)))
      rw [futureCoarseLetter_pushforward rows K mixture hmixture a f]
      exact ih Kf

/-- Manuscript recursion specialized to the original experiment rows. -/
theorem reachableRow_word_recursion (rows : I → U → ℝ)
    (K : A → Module.End ℝ (U → ℝ)) (mixture : U → ℝ)
    (hmixture : ∀ u, 0 < mixture u) (i : I) (w : List A) :
    applyWord K w (rows i) = decodeFutureRow rows K mixture
      (applyFutureCoarseWord rows K mixture w
        (pushforwardRow (futureQuotientMap rows K mixture) (rows i))) := by
  let f : futureSpan rows K :=
    ⟨rows i, Submodule.subset_span ⟨i, [], rfl⟩⟩
  exact saturatedRow_word_recursion rows K mixture hmixture f w

end FiniteFutureSaturatedExperimentState
end NCG
