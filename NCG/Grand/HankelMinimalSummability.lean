/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.PowerSummabilitySpectralRadius

/-!
# Minimal-realization summability transfer
  (`thm:feedback-Hankel-realization`,
  Gran-Tensor manuscript — final clause)

* `feedback_hankel_minimal_summability`: for a reachable
  and observable finite-dimensional realization
  `K_k = B D^k C`,
  `(K_k) ∈ ℓ¹ ⟺ (D^k) ∈ ℓ¹` — the boxed
  "minimality makes every eigenvalue visible":
  reachability and observability produce finite
  observation/control windows (finite-dimensionality
  stabilizes the reachability chain and the observability
  chain), the windowed Markov block matrix
  `O D^k R` sandwiches `D^k` between one right and one
  left inverse, and the resulting bound
  `‖D^k‖ ≤ ‖h‖·‖g‖·∑_{i,j<κ} ‖K_{k+i+j}‖` transfers
  summability.

* `feedback_hankel_minimal_summability_spectral`: combined
  with `NCG.summable_norm_powers_iff_spectralRadius_lt_one`
  this gives the boxed
  `(K_k) ∈ ℓ¹ ⟺ ρ(D) < 1` for minimal realizations.

Together with `OperatorHankelCanonicalRealization.lean`
(exact realization, reachability, observability, the
dimension lower bound, unique similarity of minimal
realizations) and `FeedbackRealization.lean` (finite
Hankel factorization, rational transfer function), this
closes the boxed clauses of the record; the equivalence
of the canonical quotient construction with an abstract
"stabilized rank" presentation is the manuscript's
bookkeeping layer.
-/

open Filter Module

namespace NCG

section Transfer

variable {X U Y : Type}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [FiniteDimensional ℂ X]
  [NormedAddCommGroup U] [NormedSpace ℂ U]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]
  [FiniteDimensional ℂ Y]

/-- Reachability gives a finite control window: the spans
of the windowed reachable vectors stabilize at `⊤`. -/
private lemma reach_window (D : X →L[ℂ] X)
    (C : U →L[ℂ] X)
    (hreach : Submodule.span ℂ
      {x : X | ∃ (k : ℕ) (u : U), (D ^ k) (C u) = x}
      = ⊤) :
    ∃ κ : ℕ, Submodule.span ℂ
      {x : X | ∃ (k : ℕ) (_ : k ≤ κ) (u : U),
        (D ^ k) (C u) = x} = ⊤ := by
  set S : ℕ → Submodule ℂ X := fun m =>
    Submodule.span ℂ
      {x : X | ∃ (k : ℕ) (_ : k ≤ m) (u : U),
        (D ^ k) (C u) = x} with hS
  have hmono : Monotone S := by
    intro a b hab
    apply Submodule.span_mono
    rintro x ⟨k, hk, u, rfl⟩
    exact ⟨k, le_trans hk hab, u, rfl⟩
  have hsup : (⨆ m, S m) = ⊤ := by
    rw [← hreach]
    apply le_antisymm
    · apply iSup_le
      intro m
      apply Submodule.span_mono
      rintro x ⟨k, _, u, rfl⟩
      exact ⟨k, u, rfl⟩
    · rw [Submodule.span_le]
      rintro x ⟨k, u, rfl⟩
      apply Submodule.mem_iSup_of_mem k
      apply Submodule.subset_span
      exact ⟨k, le_refl k, u, rfl⟩
  -- finite generation reaches the top at a finite stage
  obtain ⟨s, hs⟩ := (Module.finite_def.mp
    (inferInstance : Module.Finite ℂ X))
  have hmem : ∀ x ∈ s, ∃ m, x ∈ S m := by
    intro x hx
    have : x ∈ ⨆ m, S m := by
      rw [hsup]
      trivial
    exact (Submodule.mem_iSup_of_directed S
      hmono.directed_le).mp this
  choose f hf using hmem
  classical
  set M : ℕ := s.attach.sup fun x => f x.1 x.2 with hM
  refine ⟨M, ?_⟩
  rw [← top_le_iff, ← hs, Submodule.span_le]
  intro x hx
  have hxs : x ∈ s := hx
  have hfx := hf x hxs
  have hle : f x hxs ≤ M := by
    rw [hM]
    exact Finset.le_sup
      (f := fun y : {y // y ∈ s} => f y.1 y.2)
      (Finset.mem_attach s ⟨x, hxs⟩)
  exact hmono hle hfx

omit [FiniteDimensional ℂ Y] in
/-- Observability gives a finite observation window: the
windowed kernels stabilize at `⊥`. -/
private lemma obs_window (D : X →L[ℂ] X) (B : X →L[ℂ] Y)
    (hobs : ∀ x : X,
      (∀ k : ℕ, B ((D ^ k) x) = 0) → x = 0) :
    ∃ κ : ℕ, ∀ x : X,
      (∀ k : ℕ, k ≤ κ → B ((D ^ k) x) = 0) → x = 0 := by
  set K : ℕ → Submodule ℂ X := fun m =>
    ⨅ k ∈ Finset.range (m + 1),
      LinearMap.ker ((B.comp (D ^ k)).toLinearMap)
    with hK
  have hanti : Antitone K := by
    intro a b hab
    apply le_iInf₂
    intro k hk
    have hk' : k ∈ Finset.range (b + 1) := by
      simp only [Finset.mem_range] at hk ⊢
      omega
    exact iInf₂_le_of_le k hk' le_rfl
  have hmemK : ∀ (m : ℕ) (x : X), x ∈ K m ↔
      ∀ k ≤ m, B ((D ^ k) x) = 0 := by
    intro m x
    rw [hK]
    simp only [Submodule.mem_iInf, LinearMap.mem_ker,
      Finset.mem_range]
    constructor
    · intro h k hk
      exact h k (by omega)
    · intro h k hk
      exact h k (by omega)
  -- the antitone rank sequence attains its infimum
  have hne : (Set.range fun m => finrank ℂ (K m)).Nonempty :=
    ⟨finrank ℂ (K 0), ⟨0, rfl⟩⟩
  obtain ⟨M, hM⟩ := Nat.sInf_mem hne
  have hstab : ∀ m, M ≤ m → K m = K M := by
    intro m hm
    have h1 : K m ≤ K M := hanti hm
    have h2 : finrank ℂ (K M) ≤ finrank ℂ (K m) := by
      have hmem' : finrank ℂ (K m) ∈
          Set.range fun m => finrank ℂ (K m) := ⟨m, rfl⟩
      have hle := Nat.sInf_le hmem'
      rw [← hM] at hle
      simpa using hle
    exact le_antisymm h1 (Submodule.eq_of_le_of_finrank_le
      h1 h2).ge
  refine ⟨M, ?_⟩
  intro x hx
  have hxM : x ∈ K M := (hmemK M x).mpr hx
  have hxall : ∀ k : ℕ, B ((D ^ k) x) = 0 := by
    intro k
    have hxk : x ∈ K k := by
      rcases le_or_gt k M with h | h
      · exact hanti h hxM
      · rw [hstab k (le_of_lt h)]
        exact hxM
    exact (hmemK k x).mp hxk k le_rfl
  exact hobs x hxall

/-- `thm:feedback-Hankel-realization` (final clause):
for a reachable observable finite-dimensional
realization, summability of the Markov parameters
`B D^k C` is equivalent to summability of the powers
`D^k`. -/
theorem feedback_hankel_minimal_summability
    (D : X →L[ℂ] X) (B : X →L[ℂ] Y) (C : U →L[ℂ] X)
    (hreach : Submodule.span ℂ
      {x : X | ∃ (k : ℕ) (u : U), (D ^ k) (C u) = x}
      = ⊤)
    (hobs : ∀ x : X,
      (∀ k : ℕ, B ((D ^ k) x) = 0) → x = 0) :
    Summable (fun k : ℕ =>
      ‖(B.comp ((D ^ k).comp C) : U →L[ℂ] Y)‖)
    ↔ Summable (fun k : ℕ => ‖(D ^ k : X →L[ℂ] X)‖) := by
  constructor
  · -- the minimality transfer
    intro hsum
    obtain ⟨κR, hκR⟩ := reach_window D C hreach
    obtain ⟨κO, hκO⟩ := obs_window D B hobs
    -- the windowed control and observation maps
    set Rmap : (Fin (κR + 1) → U) →L[ℂ] X :=
      ∑ i : Fin (κR + 1),
        ((D ^ (i : ℕ)).comp C).comp
          (ContinuousLinearMap.proj i) with hRmap
    set Omap : X →L[ℂ] (Fin (κO + 1) → Y) :=
      ContinuousLinearMap.pi
        (fun j : Fin (κO + 1) =>
          B.comp (D ^ (j : ℕ))) with hOmap
    have hRapply : ∀ (u : Fin (κR + 1) → U),
        Rmap u = ∑ i : Fin (κR + 1),
          (D ^ (i : ℕ)) (C (u i)) := by
      intro u
      rw [hRmap]
      simp only [sum_apply,
        ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.proj_apply]
    -- `Rmap` is surjective
    have hRsurj : LinearMap.range Rmap.toLinearMap
        = ⊤ := by
      rw [← top_le_iff, ← hκR, Submodule.span_le]
      rintro x ⟨k, hk, u, rfl⟩
      refine ⟨Pi.single ⟨k, by omega⟩ u, ?_⟩
      rw [ContinuousLinearMap.coe_coe, hRapply]
      rw [Finset.sum_eq_single (⟨k, by omega⟩ :
        Fin (κR + 1))]
      · rw [Pi.single_eq_same]
      · intro i _ hi
        rw [Pi.single_eq_of_ne hi, map_zero, map_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    -- `Omap` is injective
    have hOinj : LinearMap.ker Omap.toLinearMap = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro x hx
      apply hκO
      intro k hk
      have := congrFun hx ⟨k, by omega⟩
      rw [hOmap] at this
      simpa only [ContinuousLinearMap.coe_coe,
        ContinuousLinearMap.pi_apply,
        ContinuousLinearMap.comp_apply,
        Pi.zero_apply] using this
    -- one right and one left inverse
    obtain ⟨g, hg⟩ :=
      Rmap.toLinearMap.exists_rightInverse_of_surjective
        hRsurj
    obtain ⟨h, hh⟩ :=
      Omap.toLinearMap.exists_leftInverse_of_injective
        hOinj
    set gC : X →L[ℂ] (Fin (κR + 1) → U) :=
      LinearMap.toContinuousLinearMap g with hgC
    set hC : (Fin (κO + 1) → Y) →L[ℂ] X :=
      LinearMap.toContinuousLinearMap h with hhC
    have hgid : ∀ x : X, Rmap (gC x) = x := by
      intro x
      have := LinearMap.congr_fun hg x
      simpa [hgC] using this
    have hhid : ∀ x : X, hC (Omap x) = x := by
      intro x
      have := LinearMap.congr_fun hh x
      simpa [hhC] using this
    -- the sandwich identity
    have hsand : ∀ k : ℕ, (D ^ k : X →L[ℂ] X)
        = (hC.comp ((Omap.comp
            ((D ^ k).comp Rmap)).comp gC)) := by
      intro k
      ext x
      simp only [ContinuousLinearMap.comp_apply]
      rw [hgid, hhid]
    -- the windowed Markov bound
    set G : ℕ → ℝ := fun k =>
      ∑ j : Fin (κO + 1), ∑ i : Fin (κR + 1),
        ‖(B.comp ((D ^ ((j : ℕ) + k + (i : ℕ))).comp C) :
          U →L[ℂ] Y)‖ with hG
    have hGnonneg : ∀ k, 0 ≤ G k := by
      intro k
      apply Finset.sum_nonneg
      intro j _
      apply Finset.sum_nonneg
      intro i _
      exact norm_nonneg _
    have hMid : ∀ k : ℕ,
        ‖(Omap.comp ((D ^ k).comp Rmap))‖ ≤ G k := by
      intro k
      apply ContinuousLinearMap.opNorm_le_bound _
        (hGnonneg k)
      intro u
      rw [pi_norm_le_iff_of_nonneg (by
        have := hGnonneg k
        positivity)]
      intro j
      simp only [ContinuousLinearMap.comp_apply]
      rw [hRapply]
      simp only [map_sum, Finset.sum_apply]
      calc ‖∑ i : Fin (κR + 1),
            B ((D ^ (j : ℕ)) ((D ^ k)
              ((D ^ (i : ℕ)) (C (u i)))))‖
          ≤ ∑ i : Fin (κR + 1),
            ‖B ((D ^ (j : ℕ)) ((D ^ k)
              ((D ^ (i : ℕ)) (C (u i)))))‖ :=
            norm_sum_le _ _
        _ ≤ ∑ i : Fin (κR + 1),
            ‖(B.comp ((D ^ ((j : ℕ) + k + (i : ℕ))).comp
              C) : U →L[ℂ] Y)‖ * ‖u‖ := by
            apply Finset.sum_le_sum
            intro i _
            have hcomp : B ((D ^ (j : ℕ)) ((D ^ k)
                ((D ^ (i : ℕ)) (C (u i)))))
                = (B.comp ((D ^ ((j : ℕ) + k + (i : ℕ))).comp
                  C)) (u i) := by
              simp only [ContinuousLinearMap.comp_apply]
              congr 1
              have hpow : (D ^ ((j : ℕ) + k + (i : ℕ)))
                  = (D ^ (j : ℕ)) * ((D ^ k)
                    * (D ^ (i : ℕ))) := by
                rw [← pow_add, ← pow_add]
                congr 1
                omega
              rw [hpow]
              rfl
            rw [hcomp]
            calc ‖(B.comp ((D ^ ((j : ℕ) + k + (i : ℕ))).comp
                  C)) (u i)‖
                ≤ ‖(B.comp ((D ^ ((j : ℕ) + k
                    + (i : ℕ))).comp C) :
                    U →L[ℂ] Y)‖ * ‖u i‖ :=
                  ContinuousLinearMap.le_opNorm _ _
              _ ≤ _ := by
                  apply mul_le_mul_of_nonneg_left
                    (norm_le_pi_norm u i)
                    (norm_nonneg _)
        _ = (∑ i : Fin (κR + 1),
            ‖(B.comp ((D ^ ((j : ℕ) + k + (i : ℕ))).comp
              C) : U →L[ℂ] Y)‖) * ‖u‖ := by
            rw [Finset.sum_mul]
        _ ≤ G k * ‖u‖ := by
            apply mul_le_mul_of_nonneg_right _
              (norm_nonneg u)
            rw [hG]
            exact Finset.single_le_sum
              (f := fun j : Fin (κO + 1) =>
                ∑ i : Fin (κR + 1),
                ‖(B.comp ((D ^ ((j : ℕ) + k
                  + (i : ℕ))).comp C) : U →L[ℂ] Y)‖)
              (fun j _ => Finset.sum_nonneg fun i _ =>
                norm_nonneg _)
              (Finset.mem_univ j)
    -- summability of `G`
    have hGsum : Summable G := by
      rw [hG]
      apply summable_sum
      intro j _
      apply summable_sum
      intro i _
      have := (summable_nat_add_iff
        ((j : ℕ) + (i : ℕ))).mpr hsum
      apply this.congr
      intro k
      have he : k + ((j : ℕ) + (i : ℕ))
          = (j : ℕ) + k + (i : ℕ) := by omega
      rw [he]
    -- assemble the comparison
    apply Summable.of_nonneg_of_le
      (fun k => norm_nonneg _)
      (fun k => ?_) (hGsum.mul_left (‖hC‖ * ‖gC‖))
    calc ‖(D ^ k : X →L[ℂ] X)‖
        = ‖hC.comp ((Omap.comp
            ((D ^ k).comp Rmap)).comp gC)‖ := by
          rw [← hsand]
      _ ≤ ‖hC‖ * ‖(Omap.comp
            ((D ^ k).comp Rmap)).comp gC‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖hC‖ * (‖Omap.comp ((D ^ k).comp Rmap)‖
            * ‖gC‖) := by
          apply mul_le_mul_of_nonneg_left
            (ContinuousLinearMap.opNorm_comp_le _ _)
            (norm_nonneg _)
      _ ≤ ‖hC‖ * (G k * ‖gC‖) := by
          apply mul_le_mul_of_nonneg_left _
            (norm_nonneg _)
          exact mul_le_mul_of_nonneg_right (hMid k)
            (norm_nonneg _)
      _ = ‖hC‖ * ‖gC‖ * G k := by ring
  · -- easy comparison direction
    intro hsum
    apply Summable.of_nonneg_of_le
      (fun k => norm_nonneg _) (fun k => ?_)
      ((hsum.mul_left ‖B‖).mul_right ‖C‖)
    calc ‖(B.comp ((D ^ k).comp C) : U →L[ℂ] Y)‖
        ≤ ‖B‖ * ‖(D ^ k).comp C‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖B‖ * (‖(D ^ k : X →L[ℂ] X)‖ * ‖C‖) := by
          apply mul_le_mul_of_nonneg_left
            (ContinuousLinearMap.opNorm_comp_le _ _)
            (norm_nonneg _)
      _ = ‖B‖ * ‖(D ^ k : X →L[ℂ] X)‖ * ‖C‖ := by ring

/-- The boxed `(K_k) ∈ ℓ¹ ⟺ ρ(D) < 1` for minimal
realizations. -/
theorem feedback_hankel_minimal_summability_spectral
    [Nontrivial X]
    (D : X →L[ℂ] X) (B : X →L[ℂ] Y) (C : U →L[ℂ] X)
    (hreach : Submodule.span ℂ
      {x : X | ∃ (k : ℕ) (u : U), (D ^ k) (C u) = x}
      = ⊤)
    (hobs : ∀ x : X,
      (∀ k : ℕ, B ((D ^ k) x) = 0) → x = 0) :
    Summable (fun k : ℕ =>
      ‖(B.comp ((D ^ k).comp C) : U →L[ℂ] Y)‖)
    ↔ spectralRadius ℂ (D : X →L[ℂ] X) < 1 := by
  rw [feedback_hankel_minimal_summability D B C
    hreach hobs]
  exact summable_norm_powers_iff_spectralRadius_lt_one D

end Transfer

end NCG
