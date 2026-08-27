/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PassiveRealizationSimilarity
import NCG.Grand.ProvenanceHankel

/-!
# Canonical similarity of sealed-provenance quotients

This file instantiates the abstract reachable/observable similarity theorem on
the quotient in `sealed_provenance_quotient`.  It supplies the final uniqueness
clause of `thm:sealed-provenance-quotient`: equal complete passive Read tables
give a unique similarity preserving every writer and Read, and intertwining
every descended hidden letter.
-/

open Matrix

namespace NCG

variable {σ ι l e y : Type*} [Fintype l] [Fintype e] [Fintype y]
variable [DecidableEq l] [DecidableEq e]

/-- The null subspace inside the source-reachable provenance carrier. -/
abbrev provenanceCarrierNull
    (T : σ → Matrix l l ℂ) (C : σ → Matrix e l ℂ)
    (Dm : σ → Matrix e e ℂ) (R : ι → Matrix y e ℂ) :=
  Submodule.comap (provCarrier T C Dm).subtype (provNull R Dm)

/-- The canonical source-reachable, Read-observable provenance space. -/
abbrev SealedProvenanceSpace
    (T : σ → Matrix l l ℂ) (C : σ → Matrix e l ℂ)
    (Dm : σ → Matrix e e ℂ) (R : ι → Matrix y e ℂ) :=
  (provCarrier T C Dm) ⧸ provenanceCarrierNull T C Dm R

/-- A word and visible vector determine a reachable provenance source. -/
noncomputable def sealedProvenanceSource
    (T : σ → Matrix l l ℂ) (C : σ → Matrix e l ℂ)
    (Dm : σ → Matrix e e ℂ) (R : ι → Matrix y e ℂ)
    (q : List σ × (l → ℂ)) : SealedProvenanceSpace T C Dm R :=
  (provenanceCarrierNull T C Dm R).mkQ
    ⟨wordH T C Dm q.1 *ᵥ q.2, by
      apply Submodule.subset_span
      exact Set.mem_iUnion.mpr ⟨q.1, ⟨q.2, rfl⟩⟩⟩

/-- A future Read descends through the common Read-null subspace. -/
noncomputable def sealedProvenanceRead
    (T : σ → Matrix l l ℂ) (C : σ → Matrix e l ℂ)
    (Dm : σ → Matrix e e ℂ) (R : ι → Matrix y e ℂ)
    (f : ι × List σ × y) :
    SealedProvenanceSpace T C Dm R →ₗ[ℂ] ℂ :=
  Submodule.liftQ (provenanceCarrierNull T C Dm R)
    ((provRead Dm R f).domRestrict (provCarrier T C Dm)) (by
      intro v hv
      rw [LinearMap.mem_ker]
      change (v : e → ℂ) ∈ provNull R Dm at hv
      rw [provNull, Submodule.mem_iInf] at hv
      have h := hv (f.1, f.2.1)
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h
      exact congrFun h f.2.2)

@[simp] theorem sealedProvenanceRead_source
    (T : σ → Matrix l l ℂ) (C : σ → Matrix e l ℂ)
    (Dm : σ → Matrix e e ℂ) (R : ι → Matrix y e ℂ)
    (f : ι × List σ × y) (q : List σ × (l → ℂ)) :
    sealedProvenanceRead T C Dm R f
        (sealedProvenanceSource T C Dm R q) =
      ((R f.1 * wordD Dm f.2.1 * wordH T C Dm q.1) *ᵥ q.2) f.2.2 := by
  change ((R f.1 * wordD Dm f.2.1) *ᵥ
      (wordH T C Dm q.1 *ᵥ q.2)) f.2.2 = _
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- The provenance source family spans its quotient. -/
theorem sealedProvenance_reachable
    (T : σ → Matrix l l ℂ) (C : σ → Matrix e l ℂ)
    (Dm : σ → Matrix e e ℂ) (R : ι → Matrix y e ℂ) :
    Submodule.span ℂ (Set.range (sealedProvenanceSource T C Dm R)) = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective
    (provenanceCarrierNull T C Dm R) z
  let S := Submodule.span ℂ
    (Set.range (sealedProvenanceSource T C Dm R))
  have hspan : ∀ (u : e → ℂ) (hu : u ∈ provCarrier T C Dm),
      (provenanceCarrierNull T C Dm R).mkQ ⟨u, hu⟩ ∈ S := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
        obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hu
        obtain ⟨x, rfl⟩ := hw
        apply Submodule.subset_span
        exact ⟨(w, x), rfl⟩
    | zero =>
        change (provenanceCarrierNull T C Dm R).mkQ
          (0 : provCarrier T C Dm) ∈ S
        rw [map_zero]
        exact S.zero_mem
    | add u v hu hv ihu ihv =>
        change (provenanceCarrierNull T C Dm R).mkQ
          (⟨u, hu⟩ + ⟨v, hv⟩) ∈ S
        rw [map_add]
        exact S.add_mem ihu ihv
    | smul a u hu ihu =>
        change (provenanceCarrierNull T C Dm R).mkQ
          (a • ⟨u, hu⟩) ∈ S
        rw [map_smul]
        exact S.smul_mem a ihu
  exact hspan v v.2

/-- The complete descended Read family separates the quotient. -/
theorem sealedProvenance_reads_separate
    (T : σ → Matrix l l ℂ) (C : σ → Matrix e l ℂ)
    (Dm : σ → Matrix e e ℂ) (R : ι → Matrix y e ℂ) :
    (⨅ f, LinearMap.ker (sealedProvenanceRead T C Dm R f)) = ⊥ := by
  apply le_antisymm
  · intro z hz
    rw [Submodule.mem_bot]
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective
      (provenanceCarrierNull T C Dm R) z
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change (v : e → ℂ) ∈ provNull R Dm
    rw [provNull, Submodule.mem_iInf]
    intro p
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    funext j
    rw [Submodule.mem_iInf] at hz
    have h := hz (p.1, p.2, j)
    rw [LinearMap.mem_ker] at h
    exact h
  · exact bot_le

/-- A hidden letter restricted to the reachable provenance carrier. -/
noncomputable def provenanceCarrierLetter
    (T : σ → Matrix l l ℂ) (C : σ → Matrix e l ℂ)
    (Dm : σ → Matrix e e ℂ) (R : ι → Matrix y e ℂ) (a : σ) :
    provCarrier T C Dm →ₗ[ℂ] provCarrier T C Dm :=
  (Dm a).mulVecLin.domRestrict (provCarrier T C Dm) |>.codRestrict
    (provCarrier T C Dm) (fun v =>
      (sealed_provenance_quotient T C Dm R).2.2.2.2.1 a v v.2)

/-- The hidden letter descended to the canonical provenance quotient. -/
noncomputable def sealedProvenanceLetter
    (T : σ → Matrix l l ℂ) (C : σ → Matrix e l ℂ)
    (Dm : σ → Matrix e e ℂ) (R : ι → Matrix y e ℂ) (a : σ) :
    SealedProvenanceSpace T C Dm R →ₗ[ℂ]
      SealedProvenanceSpace T C Dm R :=
  Submodule.mapQ (provenanceCarrierNull T C Dm R)
    (provenanceCarrierNull T C Dm R)
    (provenanceCarrierLetter T C Dm R a) (by
      intro v hv
      change provenanceCarrierLetter T C Dm R a v ∈
        provenanceCarrierNull T C Dm R
      change Dm a *ᵥ (v : e → ℂ) ∈ provNull R Dm
      change (v : e → ℂ) ∈ provNull R Dm at hv
      exact (sealed_provenance_quotient T C Dm R).2.2.2.2.2.1 a v hv)

/-- On a writer source, a descended hidden letter is the cocycle difference
of two writer sources. -/
theorem sealedProvenanceLetter_source
    (T : σ → Matrix l l ℂ) (C : σ → Matrix e l ℂ)
    (Dm : σ → Matrix e e ℂ) (R : ι → Matrix y e ℂ)
    (a : σ) (w : List σ) (x : l → ℂ) :
    sealedProvenanceLetter T C Dm R a
        (sealedProvenanceSource T C Dm R (w, x)) =
      sealedProvenanceSource T C Dm R (a :: w, x) -
        sealedProvenanceSource T C Dm R ([a], wordT T w *ᵥ x) := by
  change (provenanceCarrierNull T C Dm R).mkQ
      (provenanceCarrierLetter T C Dm R a
        ⟨wordH T C Dm w *ᵥ x, _⟩) =
    (provenanceCarrierNull T C Dm R).mkQ
        ⟨wordH T C Dm (a :: w) *ᵥ x, _⟩ -
      (provenanceCarrierNull T C Dm R).mkQ
        ⟨wordH T C Dm [a] *ᵥ (wordT T w *ᵥ x), _⟩
  rw [← map_sub]
  apply congrArg (provenanceCarrierNull T C Dm R).mkQ
  apply Subtype.ext
  change Dm a *ᵥ (wordH T C Dm w *ᵥ x) =
    wordH T C Dm (a :: w) *ᵥ x -
      wordH T C Dm [a] *ᵥ (wordT T w *ᵥ x)
  have h := congrArg (fun M : Matrix e l ℂ => M *ᵥ x)
    ((sealed_provenance_quotient T C Dm R).2.2.2.1 a w)
  simpa only [Matrix.sub_mulVec, Matrix.mulVec_mulVec] using h
/-- Canonical sealed-provenance quotients with the same complete passive Read
table are uniquely similar.  The similarity preserves every writer source and
Read and intertwines every descended hidden letter. -/
theorem sealed_provenance_canonical_similarity
    {e₁ e₂ : Type*} [Fintype e₁] [DecidableEq e₁]
    [Fintype e₂] [DecidableEq e₂]
    (T : σ → Matrix l l ℂ)
    (C₁ : σ → Matrix e₁ l ℂ) (D₁ : σ → Matrix e₁ e₁ ℂ)
    (R₁ : ι → Matrix y e₁ ℂ)
    (C₂ : σ → Matrix e₂ l ℂ) (D₂ : σ → Matrix e₂ e₂ ℂ)
    (R₂ : ι → Matrix y e₂ ℂ)
    (htable : ∀ (f : ι × List σ × y) (q : List σ × (l → ℂ)),
      ((R₁ f.1 * wordD D₁ f.2.1 * wordH T C₁ D₁ q.1) *ᵥ q.2) f.2.2 =
      ((R₂ f.1 * wordD D₂ f.2.1 * wordH T C₂ D₂ q.1) *ᵥ q.2) f.2.2) :
    ∃ E : SealedProvenanceSpace T C₁ D₁ R₁ ≃ₗ[ℂ]
        SealedProvenanceSpace T C₂ D₂ R₂,
      (∀ q, E (sealedProvenanceSource T C₁ D₁ R₁ q) =
        sealedProvenanceSource T C₂ D₂ R₂ q)
      ∧ (∀ f z, sealedProvenanceRead T C₂ D₂ R₂ f (E z) =
        sealedProvenanceRead T C₁ D₁ R₁ f z)
      ∧ (∀ G : SealedProvenanceSpace T C₁ D₁ R₁ ≃ₗ[ℂ]
          SealedProvenanceSpace T C₂ D₂ R₂,
          (∀ q, G (sealedProvenanceSource T C₁ D₁ R₁ q) =
            sealedProvenanceSource T C₂ D₂ R₂ q) → G = E)
      ∧ (∀ a z, E (sealedProvenanceLetter T C₁ D₁ R₁ a z) =
        sealedProvenanceLetter T C₂ D₂ R₂ a (E z)) := by
  obtain ⟨E, hsrc, hread, hunique, _⟩ :=
    reachable_observable_unique_similarity
      (sealedProvenanceSource T C₁ D₁ R₁)
      (sealedProvenanceSource T C₂ D₂ R₂)
      (sealedProvenanceRead T C₁ D₁ R₁)
      (sealedProvenanceRead T C₂ D₂ R₂)
      (fun f q => by simpa using htable f q)
      (sealedProvenance_reachable T C₁ D₁ R₁)
      (sealedProvenance_reachable T C₂ D₂ R₂)
      (sealedProvenance_reads_separate T C₁ D₁ R₁)
      (sealedProvenance_reads_separate T C₂ D₂ R₂)
  refine ⟨E, hsrc, hread, hunique, ?_⟩
  intro a z
  have hz : z ∈ Submodule.span ℂ
      (Set.range (sealedProvenanceSource T C₁ D₁ R₁)) := by
    rw [sealedProvenance_reachable]
    exact Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨q, rfl⟩ := hu
      obtain ⟨w, x⟩ := q
      rw [sealedProvenanceLetter_source, map_sub, hsrc, hsrc, hsrc,
        sealedProvenanceLetter_source]
  | zero => simp
  | add u v hu hv ihu ihv => simpa only [map_add] using congrArg₂ (· + ·) ihu ihv
  | smul c u hu ihu => simpa only [map_smul] using congrArg (c • ·) ihu

end NCG
