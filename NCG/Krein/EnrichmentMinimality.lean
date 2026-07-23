/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Krein.ConePositive
import NCG.Krein.EnrichmentClassification
import NCG.Operator.Diagonal

/-!
# Minimality of the signed enrichment: the variable-rank derivation

Covers the derivation step of `thm:classification`
(`manuscripts/lorentzian_emergence/lorentzian_emergence.tex`) and `cor:minimal-signed-enrichment`
(`manuscripts/renewal_emergence/renewal_emergence.tex`) that was previously baked into the
encoding `EnrichmentDatum := G.E → ZMod 2`: starting from a
**variable-rank** enrichment — fibres of arbitrary finite rank with a
diagonal ±1 sign structure, fibrewise indefiniteness, objectwise
minimality, and cone-positive norm-preserving edge transports — we
*derive*:

* `two_le_rank_of_indefinite` / `MinimalEnrichmentData.rank_eq_two` —
  indefiniteness forces rank `≥ 2`, so objectwise minimality forces
  rank exactly two on every fibre;
* `MinimalEnrichmentData.sign_diag` — at rank two the diagonal sign
  is `±diag(1,−1)`: one positive and one negative line exhausting the
  fibre;
* `conePositive_bij` — a cone-positive norm-preserving transport
  between fibres carries the renewal basis to the renewal basis
  (two-space generalization of `conePositive_perm`);
* `perm_fin_two_cases` — the rank-two structure group is
  `{I, S} ≅ ℤ/2`;
* `MinimalEnrichmentData.exists_transition_cochain` — every minimal
  enrichment therefore determines a `ℤ/2` transition cochain
  `c : G.E → ZMod 2`, i.e. exactly an `EnrichmentDatum`, through
  which the existing classification
  (`EnrichmentDatum.classificationEquiv`,
  `card_enrichmentClasses`) applies — the boxed
  `π₀ Enr_min(G) ≅ H¹(G, ℤ/2) ≅ (ℤ/2)^{b₁}`;
* `coverSign` / `coverSign_single` / `coverSign_sq` — the canonical
  fundamental symmetry of the orientation cover,
  `𝕁 e_{(x,η)} = (−1)^η e_{(x,η)}`, an involution
  (`cor:minimal-signed-enrichment`).
-/

namespace NCG

/-! ## Rank forcing -/

/-- **Indefiniteness forces rank at least two**: a fibre carrying
both a positive and a negative diagonal line has dimension `≥ 2`. -/
theorem two_le_rank_of_indefinite {r : ℕ} {s : Fin r → ℤ}
    (hpos : ∃ i, s i = 1) (hneg : ∃ i, s i = -1) : 2 ≤ r := by
  obtain ⟨i, hi⟩ := hpos
  obtain ⟨k, hk⟩ := hneg
  have hik : i ≠ k := fun h => by rw [h, hk] at hi; norm_num at hi
  have h2 : 1 < Fintype.card (Fin r) :=
    Fintype.one_lt_card_iff_nontrivial.mpr ⟨⟨i, k, hik⟩⟩
  have h3 : 1 < r := by simpa using h2
  omega

/-! ## Cone-positive transports between fibres -/

/-- **Two-space cone rigidity** (generalizing `conePositive_perm`): a
linear equivalence between renewal fibres carrying the simplicial
cone onto the simplicial cone and preserving norms maps the
distinguished basis bijectively to the distinguished basis. -/
theorem conePositive_bij {n m : ℕ} (T : (Fin n → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hT : T '' orthant n = orthant m) (hnorm : ∀ x, ‖T x‖ = ‖x‖) :
    ∃ σ : Fin n ≃ Fin m,
      ∀ i, T (Pi.single i 1) = Pi.single (σ i) 1 := by
  have hex : ∀ i : Fin n, ∃ j : Fin m, ∃ t : ℝ, 0 < t ∧
      T (Pi.single i 1) = t • Pi.single j 1 := by
    intro i
    have h1 : IsExtremeDir (orthant n) (Pi.single i (1 : ℝ)) :=
      isExtremeDir_orthant_iff.mpr ⟨i, 1, one_pos, (one_smul ℝ _).symm⟩
    have h2 := h1.map T
    rw [hT] at h2
    exact isExtremeDir_orthant_iff.mp h2
  choose g t ht hg using hex
  have ht1 : ∀ i, t i = 1 := by
    intro i
    have hni := hnorm (Pi.single i 1)
    rw [hg i, norm_smul, Real.norm_eq_abs, abs_of_pos (ht i),
      Pi.norm_single, Pi.norm_single, norm_one, mul_one] at hni
    exact hni
  have hginj : Function.Injective g := by
    intro i j hij
    have h1 : T (Pi.single i 1) = T (Pi.single j 1) := by
      rw [hg i, hg j, ht1 i, ht1 j, hij]
    have h2 := T.injective h1
    by_contra hne
    have h3 := congrFun h2 i
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at h3
    exact one_ne_zero h3
  -- the inverse transport gives the reverse injection, hence equal cards
  have hT' : T.symm '' orthant m = orthant n := by
    rw [← hT, Set.image_image]
    simp
  have hnorm' : ∀ y, ‖T.symm y‖ = ‖y‖ := by
    intro y
    conv_rhs => rw [← T.apply_symm_apply y]
    rw [hnorm]
  have hex' : ∀ j : Fin m, ∃ i : Fin n, ∃ t : ℝ, 0 < t ∧
      T.symm (Pi.single j 1) = t • Pi.single i 1 := by
    intro j
    have h1 : IsExtremeDir (orthant m) (Pi.single j (1 : ℝ)) :=
      isExtremeDir_orthant_iff.mpr ⟨j, 1, one_pos, (one_smul ℝ _).symm⟩
    have h2 := h1.map T.symm
    rw [hT'] at h2
    exact isExtremeDir_orthant_iff.mp h2
  choose g' t' ht' hg' using hex'
  have hg'inj : Function.Injective g' := by
    intro i j hij
    have h1 : (t' i)⁻¹ • T.symm (Pi.single i 1)
        = (t' j)⁻¹ • T.symm (Pi.single j 1) := by
      rw [hg' i, hg' j, smul_smul, smul_smul,
        inv_mul_cancel₀ (ht' i).ne', inv_mul_cancel₀ (ht' j).ne',
        one_smul, one_smul, hij]
    have h2 : Pi.single (M := fun _ : Fin m => ℝ) i (t' i)⁻¹
        = Pi.single j (t' j)⁻¹ := by
      have h3 := congrArg T h1
      rw [map_smul, map_smul, T.apply_symm_apply,
        T.apply_symm_apply] at h3
      rw [← Pi.single_smul, ← Pi.single_smul] at h3
      simpa using h3
    by_contra hne
    have h4 := congrFun h2 i
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at h4
    exact (inv_ne_zero (ht' i).ne') h4
  have hcard : Fintype.card (Fin n) = Fintype.card (Fin m) :=
    le_antisymm (Fintype.card_le_of_injective g hginj)
      (Fintype.card_le_of_injective g' hg'inj)
  have hbij : Function.Bijective g :=
    (Fintype.bijective_iff_injective_and_card g).mpr ⟨hginj, hcard⟩
  refine ⟨Equiv.ofBijective g hbij, fun i => ?_⟩
  rw [Equiv.ofBijective_apply, hg i, ht1 i, one_smul]

/-- **The rank-two structure group is `{I, S} ≅ ℤ/2`**: the only
permutations of a two-element basis are the identity and the sheet
swap. -/
theorem perm_fin_two_cases (π : Equiv.Perm (Fin 2)) :
    π = Equiv.refl (Fin 2) ∨ π = Equiv.swap 0 1 := by
  revert π
  decide

/-! ## Variable-rank minimal enrichments -/

variable {G : Multigraph}

/-- **`thm:classification` / `cor:minimal-signed-enrichment` (the
input datum)**: a variable-rank enrichment of the predictive graph —
finite-rank fibres with diagonal `±1` signs, fibrewise
indefiniteness (renewal positivity of both lines), objectwise
minimality, and cone-positive norm-preserving edge transports. -/
structure MinimalEnrichmentData (G : Multigraph) where
  /-- The fibre rank at each vertex. -/
  rank : G.V → ℕ
  /-- The diagonal sign structure (the fundamental symmetry entries). -/
  sign : (x : G.V) → Fin (rank x) → ℤ
  /-- Signs are `±1`. -/
  sign_pm : ∀ x i, sign x i = 1 ∨ sign x i = -1
  /-- Fibrewise indefiniteness: a positive line. -/
  indef_pos : ∀ x, ∃ i, sign x i = 1
  /-- Fibrewise indefiniteness: a negative line. -/
  indef_neg : ∀ x, ∃ i, sign x i = -1
  /-- Objectwise minimality. -/
  minimal : ∀ x, rank x ≤ 2
  /-- The edge transports. -/
  transport : (e : G.E) →
    (Fin (rank (G.src e)) → ℝ) ≃ₗ[ℝ] (Fin (rank (G.tgt e)) → ℝ)
  /-- Renewal-positivity: transports carry the renewal cone onto the
  renewal cone. -/
  cone_pos : ∀ e, transport e '' orthant _ = orthant _
  /-- Transports preserve the renewal norm. -/
  norm_pres : ∀ e x, ‖transport e x‖ = ‖x‖

namespace MinimalEnrichmentData

variable (D : MinimalEnrichmentData G)

/-- **Rank forcing (`lem:minimal-rank-two`, derived)**: every fibre
of an objectwise-minimal fibrewise-indefinite enrichment has rank
exactly two. -/
theorem rank_eq_two (x : G.V) : D.rank x = 2 :=
  le_antisymm (D.minimal x)
    (two_le_rank_of_indefinite (D.indef_pos x) (D.indef_neg x))

/-- **Sign normal form (`lem:minimal-rank-two`, derived)**: at
minimal rank the diagonal sign structure is `±diag(1,−1)` — one
positive and one negative line exhausting the fibre. -/
theorem sign_diag (x : G.V) :
    ∃ i j : Fin (D.rank x), i ≠ j ∧ D.sign x i = 1 ∧
      D.sign x j = -1 ∧ ∀ k, k = i ∨ k = j := by
  obtain ⟨i, hi⟩ := D.indef_pos x
  obtain ⟨j, hj⟩ := D.indef_neg x
  have hij : i ≠ j := fun h => by rw [h, hj] at hi; norm_num at hi
  refine ⟨i, j, hij, hi, hj, fun k => ?_⟩
  by_contra hk
  push_neg at hk
  have h3 : ({i, j, k} : Finset (Fin (D.rank x))).card = 3 := by
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro (h | h)
        exacts [hij h, hk.1 h.symm]),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]
        exact fun h => hk.2 h.symm),
      Finset.card_singleton]
  have h4 : ({i, j, k} : Finset (Fin (D.rank x))).card
      ≤ Fintype.card (Fin (D.rank x)) := Finset.card_le_univ _
  have h5 : Fintype.card (Fin (D.rank x)) = 2 := by
    rw [Fintype.card_fin]
    exact D.rank_eq_two x
  omega

/-- **`thm:classification` (the derived transition cochain)**: every
objectwise-minimal enrichment determines a `ℤ/2` transition cochain —
each transport carries basis to basis, and under the forced rank-two
identifications the induced permutation is the identity or the sheet
swap according to the bit `c e`.  The datum `c : G.E → ZMod 2` is
exactly an `EnrichmentDatum`, through which the cohomological
classification `π₀ ≅ H¹(G, ℤ/2)` applies. -/
theorem exists_transition_cochain :
    ∃ c : G.E → ZMod 2, ∀ e : G.E,
      ∃ σ : Fin (D.rank (G.src e)) ≃ Fin (D.rank (G.tgt e)),
        (∀ i, D.transport e (Pi.single i 1) = Pi.single (σ i) 1) ∧
        (finCongr (D.rank_eq_two (G.src e))).symm.trans
            (σ.trans (finCongr (D.rank_eq_two (G.tgt e))))
          = if c e = 0 then Equiv.refl (Fin 2)
            else Equiv.swap 0 1 := by
  have hσ : ∀ e : G.E,
      ∃ σ : Fin (D.rank (G.src e)) ≃ Fin (D.rank (G.tgt e)),
        ∀ i, D.transport e (Pi.single i 1) = Pi.single (σ i) 1 :=
    fun e => conePositive_bij (D.transport e) (D.cone_pos e)
      (D.norm_pres e)
  choose σ hσ using hσ
  refine ⟨fun e =>
    if ((finCongr (D.rank_eq_two (G.src e))).symm.trans
        ((σ e).trans (finCongr (D.rank_eq_two (G.tgt e))))) 0 = 0
    then 0 else 1, fun e => ⟨σ e, hσ e, ?_⟩⟩
  dsimp only
  rcases perm_fin_two_cases
      ((finCongr (D.rank_eq_two (G.src e))).symm.trans
        ((σ e).trans (finCongr (D.rank_eq_two (G.tgt e)))))
    with h | h <;> simp only [h] <;> decide

end MinimalEnrichmentData

/-! ## The canonical fundamental symmetry of the orientation cover
(`cor:minimal-signed-enrichment`) -/

variable {V : Type*}

/-- **`cor:minimal-signed-enrichment` (canonical fundamental
symmetry)**: the sheet-sign operator of the orientation cover,
`𝕁 e_{(x,η)} = (−1)^η e_{(x,η)}`. -/
noncomputable def coverSign : (V × ZMod 2 →₀ ℂ) →ₗ[ℂ] (V × ZMod 2 →₀ ℂ) :=
  diagOp (fun p => ((-1 : ℂ) ^ (p.2.val)))

theorem coverSign_single (x : V) (η : ZMod 2) (c : ℂ) :
    coverSign (Finsupp.single (x, η) c)
      = Finsupp.single (x, η) (((-1 : ℂ) ^ η.val) * c) := by
  unfold coverSign
  rw [diagOp_single]

/-- The canonical fundamental symmetry is an involution,
`𝕁² = 1`. -/
theorem coverSign_sq (f : V × ZMod 2 →₀ ℂ) :
    coverSign (coverSign f) = f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg]
  | single p c =>
      obtain ⟨x, η⟩ := p
      rw [coverSign_single, coverSign_single, ← mul_assoc,
        ← pow_add]
      congr 1
      rw [show (-1 : ℂ) ^ (η.val + η.val) = 1 from by
        rw [Even.neg_one_pow ⟨η.val, rfl⟩]]
      rw [one_mul]

end NCG
