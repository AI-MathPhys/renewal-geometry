/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SealedProvenanceCanonicalSimilarityExact
import NCG.Grand.ProvenancePanelSaturation
import NCG.Grand.FiniteLinearSystemPanelSaturation

/-!
# Exact finite-panel saturation of the provenance Hankel table

This instantiates the abstract filtration hypotheses from
`ProvenancePanelSaturation` on the actual bounded writer and future-Read
families.  It proves the manuscript's rank formula for every `p,q ≥ d_prov`
and the dimension lower bound for every finite realization of the complete
passive table.
-/

open Matrix

namespace NCG

variable {σ ι l e y : Type*} [Fintype l] [Fintype e] [Fintype y]
variable [DecidableEq l] [DecidableEq e]

/-- Words of length at most `n`. -/
abbrev ProvenanceBoundedWord (σ : Type*) (n : ℕ) :=
  {w : List σ // w.length ≤ n}

/-- Writer sources appearing in the column truncation of order `q`. -/
noncomputable def boundedProvenanceSource
    (T : σ → Matrix l l ℂ) (C : σ → Matrix e l ℂ)
    (Dm : σ → Matrix e e ℂ) (R : ι → Matrix y e ℂ) (q : ℕ)
    (s : ProvenanceBoundedWord σ q × (l → ℂ)) :
    SealedProvenanceSpace T C Dm R :=
  sealedProvenanceSource T C Dm R (s.1.1, s.2)

/-- Future Reads appearing in the row truncation of order `p`. -/
noncomputable def boundedProvenanceRead
    (T : σ → Matrix l l ℂ) (C : σ → Matrix e l ℂ)
    (Dm : σ → Matrix e e ℂ) (R : ι → Matrix y e ℂ) (p : ℕ)
    (f : ι × ProvenanceBoundedWord σ p × y) :
    SealedProvenanceSpace T C Dm R →ₗ[ℂ] ℂ :=
  sealedProvenanceRead T C Dm R (f.1, f.2.1.1, f.2.2)

/-- The bounded reachable-column filtration. -/
abbrev provenanceReachAt
    (T : σ → Matrix l l ℂ) (C : σ → Matrix e l ℂ)
    (Dm : σ → Matrix e e ℂ) (R : ι → Matrix y e ℂ) (q : ℕ) :=
  Submodule.span ℂ (Set.range (boundedProvenanceSource T C Dm R q))

/-- The common kernel of future Reads with word length at most `p`. -/
noncomputable abbrev provenanceUnobservableAt
    (T : σ → Matrix l l ℂ) (C : σ → Matrix e l ℂ)
    (Dm : σ → Matrix e e ℂ) (R : ι → Matrix y e ℂ) (p : ℕ) :=
  ⨅ f, LinearMap.ker (boundedProvenanceRead T C Dm R p f)

theorem provenanceReachAt_step
    (T : σ → Matrix l l ℂ) (C : σ → Matrix e l ℂ)
    (Dm : σ → Matrix e e ℂ) (R : ι → Matrix y e ℂ) (q : ℕ) :
    provenanceReachAt T C Dm R q ≤ provenanceReachAt T C Dm R (q + 1) := by
  apply Submodule.span_mono
  rintro z ⟨s, rfl⟩
  exact ⟨(⟨s.1.1, Nat.le_succ_of_le s.1.2⟩, s.2), rfl⟩

theorem provenanceReachAt_exhausts
    (T : σ → Matrix l l ℂ) (C : σ → Matrix e l ℂ)
    (Dm : σ → Matrix e e ℂ) (R : ι → Matrix y e ℂ) :
    (⨆ q, provenanceReachAt T C Dm R q) = ⊤ := by
  apply top_unique
  rw [← sealedProvenance_reachable T C Dm R]
  apply Submodule.span_le.2
  rintro z ⟨s, rfl⟩
  exact Submodule.mem_iSup_of_mem s.1.length
    (Submodule.subset_span ⟨(⟨s.1, le_rfl⟩, s.2), rfl⟩)

/-- A plateau in the bounded writer filtration is already the whole quotient.
The cocycle reconstruction formula is the no-delayed-growth mechanism. -/
theorem provenanceReachAt_eq_top_of_plateau
    (T : σ → Matrix l l ℂ) (C : σ → Matrix e l ℂ)
    (Dm : σ → Matrix e e ℂ) (R : ι → Matrix y e ℂ) (q : ℕ)
    (hplateau : provenanceReachAt T C Dm R q =
      provenanceReachAt T C Dm R (q + 1)) :
    provenanceReachAt T C Dm R q = ⊤ := by
  let K := provenanceReachAt T C Dm R q
  have hletter : ∀ (a : σ) (z : SealedProvenanceSpace T C Dm R),
      z ∈ K → sealedProvenanceLetter T C Dm R a z ∈ K := by
    intro a z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨s, rfl⟩ := hz
        change sealedProvenanceLetter T C Dm R a
          (sealedProvenanceSource T C Dm R (s.1.1, s.2)) ∈ K
        rw [sealedProvenanceLetter_source]
        change _ ∈ provenanceReachAt T C Dm R q
        rw [hplateau]
        apply Submodule.sub_mem
        · apply Submodule.subset_span
          exact ⟨(⟨a :: s.1.1, by simpa using Nat.succ_le_succ s.1.2⟩,
            s.2), rfl⟩
        · apply Submodule.subset_span
          exact ⟨(⟨[a], by simp⟩, wordT T s.1.1 *ᵥ s.2), rfl⟩
    | zero => simp
    | add u v hu hv ihu ihv => simpa only [map_add] using K.add_mem ihu ihv
    | smul c u hu ihu => simpa only [map_smul] using K.smul_mem c ihu
  have hone : ∀ (a : σ) (x : l → ℂ),
      sealedProvenanceSource T C Dm R ([a], x) ∈ K := by
    intro a x
    change sealedProvenanceSource T C Dm R ([a], x) ∈
      provenanceReachAt T C Dm R q
    rw [hplateau]
    apply Submodule.subset_span
    exact ⟨(⟨[a], by simp⟩, x), rfl⟩
  have hall : ∀ (w : List σ) (x : l → ℂ),
      sealedProvenanceSource T C Dm R (w, x) ∈ K := by
    intro w
    induction w with
    | nil =>
        intro x
        change (provenanceCarrierNull T C Dm R).mkQ
          ⟨wordH T C Dm [] *ᵥ x, _⟩ ∈ K
        have heq : (provenanceCarrierNull T C Dm R).mkQ
            ⟨wordH T C Dm [] *ᵥ x, by
              simpa [wordH] using (provCarrier T C Dm).zero_mem⟩ = 0 := by
          calc
            (provenanceCarrierNull T C Dm R).mkQ
                ⟨wordH T C Dm [] *ᵥ x, by
                  simpa [wordH] using (provCarrier T C Dm).zero_mem⟩ =
              (provenanceCarrierNull T C Dm R).mkQ
                (0 : provCarrier T C Dm) := by
                  apply congrArg (provenanceCarrierNull T C Dm R).mkQ
                  apply Subtype.ext
                  simp [wordH]
            _ = 0 := map_zero _
        rw [heq]
        exact K.zero_mem
    | cons a w ih =>
        intro x
        have hhid := hletter a
          (sealedProvenanceSource T C Dm R (w, x)) (ih x)
        rw [sealedProvenanceLetter_source] at hhid
        have hbase := hone a (wordT T w *ᵥ x)
        have := K.add_mem hhid hbase
        simpa only [sub_add_cancel] using this
  apply top_unique
  rw [← sealedProvenance_reachable T C Dm R]
  apply Submodule.span_le.2
  rintro z ⟨s, rfl⟩
  exact hall s.1 s.2

theorem provenanceReachAt_freezes
    (T : σ → Matrix l l ℂ) (C : σ → Matrix e l ℂ)
    (Dm : σ → Matrix e e ℂ) (R : ι → Matrix y e ℂ) :
    ∀ q, provenanceReachAt T C Dm R q =
      provenanceReachAt T C Dm R (q + 1) →
      ∀ j, q ≤ j → provenanceReachAt T C Dm R j =
        provenanceReachAt T C Dm R q := by
  intro q hq j hj
  have htop := provenanceReachAt_eq_top_of_plateau T C Dm R q hq
  rw [htop]
  apply top_unique
  have hmono : Monotone (provenanceReachAt T C Dm R) :=
    monotone_nat_of_le_succ (provenanceReachAt_step T C Dm R)
  simpa [htop] using hmono hj

theorem provenanceReachAt_saturated
    (T : σ → Matrix l l ℂ) (C : σ → Matrix e l ℂ)
    (Dm : σ → Matrix e e ℂ) (R : ι → Matrix y e ℂ) :
    ∀ q, Module.finrank ℂ (SealedProvenanceSpace T C Dm R) ≤ q →
      provenanceReachAt T C Dm R q = ⊤ :=
  increasing_filtration_saturates_by_finrank
    (provenanceReachAt T C Dm R)
    (provenanceReachAt_step T C Dm R)
    (provenanceReachAt_freezes T C Dm R)
    (provenanceReachAt_exhausts T C Dm R)

theorem provenanceUnobservableAt_step
    (T : σ → Matrix l l ℂ) (C : σ → Matrix e l ℂ)
    (Dm : σ → Matrix e e ℂ) (R : ι → Matrix y e ℂ) (p : ℕ) :
    provenanceUnobservableAt T C Dm R (p + 1) ≤
      provenanceUnobservableAt T C Dm R p := by
  intro z hz
  rw [Submodule.mem_iInf] at hz ⊢
  intro f
  exact hz (f.1, ⟨f.2.1.1, Nat.le_succ_of_le f.2.1.2⟩, f.2.2)

/-- Appending a future letter is precomposition by its descended hidden
letter. -/
theorem sealedProvenanceRead_append_letter
    (T : σ → Matrix l l ℂ) (C : σ → Matrix e l ℂ)
    (Dm : σ → Matrix e e ℂ) (R : ι → Matrix y e ℂ)
    (lam : ι) (v : List σ) (r : y) (a : σ)
    (z : SealedProvenanceSpace T C Dm R) :
    sealedProvenanceRead T C Dm R (lam, v ++ [a], r) z =
      sealedProvenanceRead T C Dm R (lam, v, r)
        (sealedProvenanceLetter T C Dm R a z) := by
  obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective
    (provenanceCarrierNull T C Dm R) z
  change ((R lam * wordD Dm (v ++ [a])) *ᵥ (u : e → ℂ)) r =
    ((R lam * wordD Dm v) *ᵥ (Dm a *ᵥ (u : e → ℂ))) r
  rw [(sealed_provenance_quotient T C Dm R).2.1 v [a], wordD,
    wordD, Matrix.mul_one, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem provenanceUnobservableAt_exhausts
    (T : σ → Matrix l l ℂ) (C : σ → Matrix e l ℂ)
    (Dm : σ → Matrix e e ℂ) (R : ι → Matrix y e ℂ) :
    (⨅ p, provenanceUnobservableAt T C Dm R p) = ⊥ := by
  apply le_antisymm
  · intro z hz
    have hzall : z ∈ ⨅ f, LinearMap.ker
        (sealedProvenanceRead T C Dm R f) := by
      rw [Submodule.mem_iInf]
      intro f
      rw [Submodule.mem_iInf] at hz
      have hp := hz f.2.1.length
      rw [Submodule.mem_iInf] at hp
      exact hp (f.1, ⟨f.2.1, le_rfl⟩, f.2.2)
    rw [sealedProvenance_reads_separate T C Dm R] at hzall
    exact hzall
  · exact bot_le

/-- A plateau in the bounded future-Read kernels is already bottom. -/
theorem provenanceUnobservableAt_eq_bot_of_plateau
    (T : σ → Matrix l l ℂ) (C : σ → Matrix e l ℂ)
    (Dm : σ → Matrix e e ℂ) (R : ι → Matrix y e ℂ) (p : ℕ)
    (hplateau : provenanceUnobservableAt T C Dm R p =
      provenanceUnobservableAt T C Dm R (p + 1)) :
    provenanceUnobservableAt T C Dm R p = ⊥ := by
  let K := provenanceUnobservableAt T C Dm R p
  have hletter : ∀ (a : σ) (z : SealedProvenanceSpace T C Dm R),
      z ∈ K → sealedProvenanceLetter T C Dm R a z ∈ K := by
    intro a z hz
    rw [Submodule.mem_iInf]
    intro f
    rw [LinearMap.mem_ker]
    change sealedProvenanceRead T C Dm R
      (f.1, f.2.1.1, f.2.2) (sealedProvenanceLetter T C Dm R a z) = 0
    rw [← sealedProvenanceRead_append_letter]
    have hz' : z ∈ provenanceUnobservableAt T C Dm R (p + 1) := by
      rw [← hplateau]
      exact hz
    rw [Submodule.mem_iInf] at hz'
    have h := hz' (f.1, ⟨f.2.1.1 ++ [a], by
      simpa using Nat.succ_le_succ f.2.1.2⟩, f.2.2)
    exact LinearMap.mem_ker.mp h
  apply le_antisymm
  · intro z hz
    have hzword : ∀ (w : List σ)
        (u : SealedProvenanceSpace T C Dm R), u ∈ K →
        ∀ (lam : ι) (r : y),
          sealedProvenanceRead T C Dm R (lam, w, r) u = 0 := by
      intro w
      induction w using List.reverseRecOn with
      | nil =>
          intro u hu lam r
          rw [← LinearMap.mem_ker]
          rw [Submodule.mem_iInf] at hu
          exact hu (lam, ⟨[], Nat.zero_le _⟩, r)
      | append_singleton w a ih =>
          intro u hu lam r
          rw [sealedProvenanceRead_append_letter]
          exact ih (sealedProvenanceLetter T C Dm R a u)
            (hletter a u hu) lam r
    have hzall : ∀ (w : List σ) (lam : ι) (r : y),
        sealedProvenanceRead T C Dm R (lam, w, r) z = 0 := by
      intro w
      exact hzword w z hz
    have hcommon : z ∈ ⨅ f, LinearMap.ker
        (sealedProvenanceRead T C Dm R f) := by
      rw [Submodule.mem_iInf]
      intro f
      rw [LinearMap.mem_ker]
      exact hzall f.2.1 f.1 f.2.2
    rw [sealedProvenance_reads_separate T C Dm R] at hcommon
    exact hcommon
  · exact bot_le

theorem provenanceUnobservableAt_freezes
    (T : σ → Matrix l l ℂ) (C : σ → Matrix e l ℂ)
    (Dm : σ → Matrix e e ℂ) (R : ι → Matrix y e ℂ) :
    ∀ p, provenanceUnobservableAt T C Dm R p =
      provenanceUnobservableAt T C Dm R (p + 1) →
      ∀ j, p ≤ j → provenanceUnobservableAt T C Dm R j =
        provenanceUnobservableAt T C Dm R p := by
  intro p hp j hj
  have hbot := provenanceUnobservableAt_eq_bot_of_plateau T C Dm R p hp
  rw [hbot]
  apply le_antisymm
  · have hanti : Antitone (provenanceUnobservableAt T C Dm R) := by
      intro a b hab
      induction b, hab using Nat.le_induction with
      | base => exact le_rfl
      | succ b hab ih => exact
          (provenanceUnobservableAt_step T C Dm R b).trans ih
    simpa [hbot] using hanti hj
  · exact bot_le

theorem provenanceUnobservableAt_saturated
    (T : σ → Matrix l l ℂ) (C : σ → Matrix e l ℂ)
    (Dm : σ → Matrix e e ℂ) (R : ι → Matrix y e ℂ) :
    ∀ p, Module.finrank ℂ (SealedProvenanceSpace T C Dm R) ≤ p →
      provenanceUnobservableAt T C Dm R p = ⊥ :=
  decreasing_filtration_saturates_by_finrank_of_exhausts
    (provenanceUnobservableAt T C Dm R)
    (provenanceUnobservableAt_step T C Dm R)
    (provenanceUnobservableAt_freezes T C Dm R)
    (provenanceUnobservableAt_exhausts T C Dm R)

/-- The scalar finite provenance-Hankel panel. -/
noncomputable def boundedProvenanceTable
    (T : σ → Matrix l l ℂ) (C : σ → Matrix e l ℂ)
    (Dm : σ → Matrix e e ℂ) (R : ι → Matrix y e ℂ) (p q : ℕ)
    (f : ι × ProvenanceBoundedWord σ p × y)
    (s : ProvenanceBoundedWord σ q × (l → ℂ)) : ℂ :=
  boundedProvenanceRead T C Dm R p f
    (boundedProvenanceSource T C Dm R q s)

/-- `thm:provenance-hankel-minimality`: every panel with both word cutoffs at
least the canonical quotient dimension has rank exactly that dimension. -/
theorem provenance_hankel_finite_panel_rank
    (T : σ → Matrix l l ℂ) (C : σ → Matrix e l ℂ)
    (Dm : σ → Matrix e e ℂ) (R : ι → Matrix y e ℂ)
    (p q : ℕ)
    (hp : Module.finrank ℂ (SealedProvenanceSpace T C Dm R) ≤ p)
    (hq : Module.finrank ℂ (SealedProvenanceSpace T C Dm R) ≤ q) :
    Module.finrank ℂ
        (HankelCore
          (ProvenanceBoundedWord σ q × (l → ℂ))
          (ι × ProvenanceBoundedWord σ p × y)
          (boundedProvenanceTable T C Dm R p q)) =
      Module.finrank ℂ (SealedProvenanceSpace T C Dm R) := by
  symm
  apply hankel_minimality_finrank_eq
    (boundedProvenanceTable T C Dm R p q)
    (boundedProvenanceSource T C Dm R q)
    (boundedProvenanceRead T C Dm R p)
  · intro f s
    rfl
  · exact provenanceReachAt_saturated T C Dm R q hq
  · intro z hz
    have hzker : z ∈ provenanceUnobservableAt T C Dm R p := by
      rw [Submodule.mem_iInf]
      intro f
      rw [LinearMap.mem_ker]
      exact hz f
    rw [provenanceUnobservableAt_saturated T C Dm R p hp] at hzker
    exact hzker

/-- Every finite linear realization of the complete passive table has
dimension at least the canonical sealed-provenance quotient. -/
theorem sealed_provenance_minimal_dimension
    {N : Type*} [AddCommGroup N] [Module ℂ N]
    [FiniteDimensional ℂ N]
    (T : σ → Matrix l l ℂ) (C : σ → Matrix e l ℂ)
    (Dm : σ → Matrix e e ℂ) (R : ι → Matrix y e ℂ)
    (src : (List σ × (l → ℂ)) → N)
    (read : (ι × List σ × y) → N →ₗ[ℂ] ℂ)
    (hmatch : ∀ f s, read f (src s) =
      sealedProvenanceRead T C Dm R f
        (sealedProvenanceSource T C Dm R s)) :
    Module.finrank ℂ (SealedProvenanceSpace T C Dm R) ≤
      Module.finrank ℂ N := by
  let tbl : (ι × List σ × y) → (List σ × (l → ℂ)) → ℂ :=
    fun f s => sealedProvenanceRead T C Dm R f
      (sealedProvenanceSource T C Dm R s)
  have hcanon : Module.finrank ℂ (SealedProvenanceSpace T C Dm R) =
      Module.finrank ℂ (HankelCore (List σ × (l → ℂ))
        (ι × List σ × y) tbl) :=
    hankel_minimality_finrank_eq tbl
      (sealedProvenanceSource T C Dm R)
      (sealedProvenanceRead T C Dm R) (fun _ _ => rfl)
      (sealedProvenance_reachable T C Dm R) (by
        intro z hz
        have hcommon : z ∈ ⨅ f, LinearMap.ker
            (sealedProvenanceRead T C Dm R f) := by
          rw [Submodule.mem_iInf]
          intro f
          rw [LinearMap.mem_ker]
          exact hz f
        rw [sealedProvenance_reads_separate T C Dm R] at hcommon
        exact hcommon)
  rw [hcanon]
  exact (hankel_minimality tbl src read hmatch).2

end NCG
