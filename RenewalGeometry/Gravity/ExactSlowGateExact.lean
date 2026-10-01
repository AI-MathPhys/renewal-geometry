/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.ExactSlowBranchData

/-!
# First slow correction, Lyapunov–Schmidt reduction of the initial gate, and the
  original slope jets
  (`prop:supp-exact-slow-correction`, `eq:supp-exact-slow-first-tangency`,
  `thm:supp-exact-three-row`, `eq:supp-exact-hard-forcing`,
  `eq:supp-exact-slow-rank-split`, `eq:supp-exact-defect-feedback`,
  `prop:supp-exact-original-slope-jets`, `eq:supp-exact-original-slope-jets`;
  emergent-spacetime manuscript)

All maps are the abstract encodings of `Gravity/ExactSlowBranchData.lean`; the
identification of the matrices with the coefficients of the actual finite action is not
formalised (as in `Gravity/SupplementExactConstraintRankExact.lean`).

## `prop:supp-exact-slow-correction`
Under the weak decomposition `ℝ²⁹ = Ran B ⊕ 𝒵_g ⊕ ℋ` and the coupling tests
`p_H C_red = 0`, `p_g C_red` onto (`range_leadingConstraint`: `Ran Φ₀ = ker p_H`):
* `slow_correction_solvable_iff`: `Φ₀ ξ₁ + Φ₁(ξ₀) = 0` is solvable iff `𝔪(ξ₀) = 0`
  (for every `ξ₀`, in particular for `ξ₀ ∈ ker Φ₀`);
* `slow_correction_particular`, `slow_correction_solution_set`: for a right inverse `R₀`
  of `Φ₀` on its range, `ξ₁ = -R₀ Φ₁(ξ₀)` solves it, and the solution set is
  `-R₀ Φ₁(ξ₀) + ker Φ₀`;
* `slow_first_tangency`: for a path `ξ₀` on `[0, T]` along which the five slow
  identities `𝔆_sl(ξ₀(τ)) = 0` hold (the conclusion of
  `thm:supp-exact-five-compatibility`), with `ξ₀(0) = 0` and one-sided derivative `b`
  at `0` (weaker than `C¹` at zero), and `Σ₀`, `Φ₁` differentiable at `0`,
  `D𝔆_sl(0)[b] = (p_g C_red DΣ₀(0)[b], p_H DΦ₁(0)[b]) = 0`
  (`eq:supp-exact-slow-first-tangency`).

## `thm:supp-exact-three-row`
For an arbitrary linear map `𝓛₀ : K → 𝒵_g × ℋ` on `K = J_g 𝒵_g + E_x 𝒳_h` with
invertible upper vertical block `𝒜_g` (inverse `AgInv`):
* `three_row_solvable_iff` (`eq:supp-exact-hard-forcing`);
* `three_row_rank`, `three_row_rank_two` (`eq:supp-exact-slow-rank-split`);
* `three_row_surjective_iff` (five-row surjectivity iff `rank ℋ_x = 3`);
* `three_row_defect_feedback` (`eq:supp-exact-defect-feedback`);
* `three_row_exists_iff_defect` (existence of some `κ̃` with `𝓛₀ κ̃ = -f₀`).
`initial_gate_three_row` instantiates them for the initial gate map
`𝓛₀ κ = (p_g C_red Df(0) κ, p_H Dg(0) κ)` restricted to `𝒦₀ = ker Φ₀`.

## `prop:supp-exact-original-slope-jets`
`original_slope_jets`: with `Ξ(r, y) = 𝖤 r + J_g γ(r, y) + J_H y`, `γ` a `C²` map with
`γ(0) = 0` and `𝔠_g(Ξ) = 0` near `0` (the graph of
`lem:supp-exact-two-row-elimination`, whose analyticity is replaced by `C²`), `𝔠_g`,
`𝔠_H` of class `C²`, `f` differentiable at `0`, the slope-entrance identity
`D𝔠_g(0) J_H = 0` and a left inverse of `𝒜_g = D𝔠_g(0) J_g`, the slope polynomial of
the reduced functions `𝓕 = L_X f ∘ Ξ`, `𝓗 = 𝔠_H ∘ Ξ` is
`𝒬(c) = D𝔠_H(0) a_* + D²𝔠_H(0)[b(c), b(c)] - 𝒞_g 𝒜_g⁻¹ D²𝔠_g(0)[b(c), b(c)]`.
`slopePolynomial_rowConvention`, `original_slope_jets_rowConvention`: a fixed linear
change of harmonic rows `T` transforms the whole formula (`𝒬`, `D𝔠_H`, `D²𝔠_H`, `𝒞_g`)
together.
-/

namespace RenewalGeometry
namespace ExactSlowGate

open ExactSlowBranch Filter Topology Module Set

/-! ## First correction and initial slow tangency -/

section SlowCorrection

variable {Xs W Zg Hs : Type*}
  [NormedAddCommGroup Xs] [NormedSpace ℝ Xs] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Zg] [NormedSpace ℝ Zg] [NormedAddCommGroup Hs] [NormedSpace ℝ Hs]
  {Cred : Xs →L[ℝ] W} {B : W →L[ℝ] W} {Jg : Zg →L[ℝ] W} {JH : Hs →L[ℝ] W}
  {pg : W →L[ℝ] Zg} {pH : W →L[ℝ] Hs}

/-- **`prop:supp-exact-slow-correction`, solvability.** The first-correction equation
`Φ₀ ξ₁ + Φ₁(ξ₀) = 0` is solvable exactly when `𝔪(ξ₀) = p_H Φ₁(ξ₀) = 0`. -/
theorem slow_correction_solvable_iff (hD : WeakDecomposition B Jg JH pg pH)
    (hHC : ∀ x, pH (Cred x) = 0) (hgC : Function.Surjective fun x => pg (Cred x))
    (Φ₁ : Xs × W → W) (ξ₀ : Xs × W) :
    (∃ ξ₁, leadingConstraint Cred B ξ₁ + Φ₁ ξ₀ = 0) ↔ slowMean pH Φ₁ ξ₀ = 0 := by
  have hR := range_leadingConstraint hD hHC hgC
  constructor
  · rintro ⟨ξ₁, h⟩
    have hmem : -Φ₁ ξ₀ ∈ LinearMap.range (leadingConstraint Cred B : Xs × W →ₗ[ℝ] W) :=
      ⟨ξ₁, eq_neg_of_add_eq_zero_left h⟩
    rw [hR, LinearMap.mem_ker] at hmem
    have : pH (-Φ₁ ξ₀) = 0 := hmem
    rw [map_neg, neg_eq_zero] at this
    exact this
  · intro h
    have hmem : -Φ₁ ξ₀ ∈ LinearMap.ker (pH : W →ₗ[ℝ] Hs) := by
      rw [LinearMap.mem_ker]
      change pH (-Φ₁ ξ₀) = 0
      rw [map_neg, neg_eq_zero]; exact h
    rw [← hR] at hmem
    obtain ⟨ξ₁, hξ₁⟩ := hmem
    refine ⟨ξ₁, ?_⟩
    have : leadingConstraint Cred B ξ₁ = -Φ₁ ξ₀ := hξ₁
    rw [this, neg_add_cancel]

/-- **`prop:supp-exact-slow-correction`, particular solution.** If `𝔪(ξ₀) = 0` and `R₀`
is a right inverse of `Φ₀` on its range, then `ξ₁ = -R₀ Φ₁(ξ₀)` solves the
first-correction equation. -/
theorem slow_correction_particular (hD : WeakDecomposition B Jg JH pg pH)
    (hHC : ∀ x, pH (Cred x) = 0) (hgC : Function.Surjective fun x => pg (Cred x))
    (Φ₁ : Xs × W → W) (ξ₀ : Xs × W) (R₀ : W → Xs × W)
    (hR₀ : ∀ w ∈ LinearMap.range (leadingConstraint Cred B : Xs × W →ₗ[ℝ] W),
      leadingConstraint Cred B (R₀ w) = w)
    (hm : slowMean pH Φ₁ ξ₀ = 0) :
    leadingConstraint Cred B (-R₀ (Φ₁ ξ₀)) + Φ₁ ξ₀ = 0 := by
  have hmem : Φ₁ ξ₀ ∈ LinearMap.range (leadingConstraint Cred B : Xs × W →ₗ[ℝ] W) := by
    rw [range_leadingConstraint hD hHC hgC, LinearMap.mem_ker]; exact hm
  rw [map_neg, hR₀ _ hmem, neg_add_cancel]

/-- **`prop:supp-exact-slow-correction`, uniqueness modulo `ker Φ₀`.** Under the
hypotheses of `slow_correction_particular`, `ξ₁` solves the first-correction equation
iff `ξ₁ - (-R₀ Φ₁(ξ₀)) ∈ ker Φ₀`. -/
theorem slow_correction_solution_set (hD : WeakDecomposition B Jg JH pg pH)
    (hHC : ∀ x, pH (Cred x) = 0) (hgC : Function.Surjective fun x => pg (Cred x))
    (Φ₁ : Xs × W → W) (ξ₀ : Xs × W) (R₀ : W → Xs × W)
    (hR₀ : ∀ w ∈ LinearMap.range (leadingConstraint Cred B : Xs × W →ₗ[ℝ] W),
      leadingConstraint Cred B (R₀ w) = w)
    (hm : slowMean pH Φ₁ ξ₀ = 0) (ξ₁ : Xs × W) :
    leadingConstraint Cred B ξ₁ + Φ₁ ξ₀ = 0 ↔
      ξ₁ - -R₀ (Φ₁ ξ₀) ∈ LinearMap.ker (leadingConstraint Cred B : Xs × W →ₗ[ℝ] W) := by
  have hp := slow_correction_particular hD hHC hgC Φ₁ ξ₀ R₀ hR₀ hm
  rw [LinearMap.mem_ker]
  change _ ↔ leadingConstraint Cred B (ξ₁ - -R₀ (Φ₁ ξ₀)) = 0
  have hP : leadingConstraint Cred B (-R₀ (Φ₁ ξ₀)) = -Φ₁ ξ₀ := eq_neg_of_add_eq_zero_left hp
  rw [map_sub, hP, sub_neg_eq_add]

/-- **`eq:supp-exact-slow-first-tangency`.** The five-map `𝔆_sl` has derivative
`(p_g C_red DΣ₀(0), p_H DΦ₁(0))` at `0`, and along a limiting path with `ξ₀(0) = 0`,
right derivative `b` at `0` and `𝔆_sl(ξ₀(τ)) = 0` on `[0, T]`, this derivative
annihilates `b`. -/
theorem slow_first_tangency (bs : Xs) (Sig0 : Xs × W → Xs) (Φ₁ : Xs × W → W)
    (DSig : Xs × W →L[ℝ] Xs) (DΦ₁ : Xs × W →L[ℝ] W)
    (hSig : HasFDerivAt Sig0 DSig 0) (hΦ : HasFDerivAt Φ₁ DΦ₁ 0)
    (ξ₀ : ℝ → Xs × W) (b : Xs × W) {T : ℝ} (hT : 0 < T) (h0 : ξ₀ 0 = 0)
    (hb : HasDerivWithinAt ξ₀ b (Ici 0) 0)
    (hC : ∀ τ ∈ Icc 0 T, slowConstraint pg pH Cred bs Sig0 Φ₁ (ξ₀ τ) = 0) :
    HasFDerivAt (slowConstraint pg pH Cred bs Sig0 Φ₁)
        ((pg.comp (Cred.comp DSig)).prod (pH.comp DΦ₁)) 0 ∧
      (pg (Cred (DSig b)), pH (DΦ₁ b)) = 0 := by
  have hF : HasFDerivAt (slowConstraint pg pH Cred bs Sig0 Φ₁)
      ((pg.comp (Cred.comp DSig)).prod (pH.comp DΦ₁)) 0 := by
    have h1 : HasFDerivAt (fun ξ => pg (Cred (bs + Sig0 ξ))) (pg.comp (Cred.comp DSig)) 0 :=
      (pg.comp Cred).hasFDerivAt.comp 0 (hSig.const_add bs)
    have h2 : HasFDerivAt (fun ξ => pH (Φ₁ ξ)) (pH.comp DΦ₁) 0 :=
      pH.hasFDerivAt.comp 0 hΦ
    exact h1.prodMk h2
  refine ⟨hF, ?_⟩
  have hF' : HasFDerivAt (slowConstraint pg pH Cred bs Sig0 Φ₁)
      ((pg.comp (Cred.comp DSig)).prod (pH.comp DΦ₁)) (ξ₀ 0) := h0 ▸ hF
  have hchain := hF'.comp_hasDerivWithinAt (0 : ℝ) hb
  have hzero : HasDerivWithinAt (slowConstraint pg pH Cred bs Sig0 Φ₁ ∘ ξ₀) 0 (Ici 0) 0 := by
    refine (hasDerivWithinAt_const (0 : ℝ) (Ici 0) (0 : Zg × Hs)).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [Icc_mem_nhdsGE hT] with τ hτ using hC τ hτ
    · exact hC 0 ⟨le_refl _, hT.le⟩
  have := (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _ hchain hzero
  simpa using this

end SlowCorrection

/-! ## Lyapunov–Schmidt reduction of the initial gate -/

section ThreeRow

variable {K Zg Xh Hs : Type*} [AddCommGroup K] [Module ℝ K] [AddCommGroup Zg] [Module ℝ Zg]
  [AddCommGroup Xh] [Module ℝ Xh] [AddCommGroup Hs] [Module ℝ Hs]
  (L : K →ₗ[ℝ] Zg × Hs) (Jg : Zg →ₗ[ℝ] K) (Ex : Xh →ₗ[ℝ] K) (AgInv : Zg →ₗ[ℝ] Zg)

/-- **`eq:supp-exact-hard-forcing`.** On `K = J_g 𝒵_g + E_x 𝒳_h` with `𝒜_g` invertible,
`𝓛₀ κ = -(f_g, f_H)` is solvable iff `f_H - 𝒞_g 𝒜_g⁻¹ f_g ∈ Ran ℋ_x`. -/
theorem three_row_solvable_iff (hspan : ∀ κ, ∃ z x, κ = Jg z + Ex x)
    (hleft : ∀ z, AgInv (blockAg L Jg z) = z) (hright : ∀ z, blockAg L Jg (AgInv z) = z)
    (fg : Zg) (fH : Hs) :
    (∃ κ, L κ = -(fg, fH)) ↔
      fH - blockCg L Jg (AgInv fg) ∈ LinearMap.range (reducedHx L Jg Ex AgInv) := by
  constructor
  · rintro ⟨κ, hκ⟩
    obtain ⟨z, x, rfl⟩ := hspan κ
    rw [map_split_eq_blocks, Prod.neg_mk, Prod.mk.injEq] at hκ
    obtain ⟨h1, h2⟩ := hκ
    have hz : z = AgInv (-fg - blockBx L Ex x) := by
      rw [← hleft z, ← h1]; congr 1; abel
    refine ⟨-x, ?_⟩
    rw [hz] at h2
    rw [reducedHx_apply]
    simp only [map_neg, map_sub] at h2 ⊢
    rw [← neg_neg fH, ← h2]; abel
  · rintro ⟨x₀, hx₀⟩
    rw [reducedHx_apply] at hx₀
    refine ⟨Jg (AgInv (blockBx L Ex x₀ - fg)) + Ex (-x₀), ?_⟩
    rw [map_split_eq_blocks, hright, Prod.neg_mk]
    simp only [map_neg, map_sub]
    congr 1
    · abel
    · rw [← sub_eq_zero]
      have : fH = blockDx L Ex x₀ - blockCg L Jg (AgInv (blockBx L Ex x₀))
          + blockCg L Jg (AgInv fg) := by rw [hx₀]; abel
      rw [this]; abel

/-- The kernel of the block map `(z, x) ↦ 𝓛₀ (J_g z + E_x x)` is the graph
`{(-𝒜_g⁻¹ ℬ_x x, x) : x ∈ ker ℋ_x}`. -/
theorem ker_blockMap_eq_map (hleft : ∀ z, AgInv (blockAg L Jg z) = z)
    (hright : ∀ z, blockAg L Jg (AgInv z) = z) :
    LinearMap.ker (L.comp (Jg.coprod Ex))
      = (LinearMap.ker (reducedHx L Jg Ex AgInv)).map
          ((-(AgInv.comp (blockBx L Ex))).prod LinearMap.id) := by
  ext ⟨z, x⟩
  rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.coprod_apply, map_split_eq_blocks,
    Prod.mk_eq_zero, Submodule.mem_map]
  constructor
  · rintro ⟨h1, h2⟩
    dsimp only at h1 h2
    have hz : z = -AgInv (blockBx L Ex x) := by
      rw [← hleft z, ← neg_eq_of_add_eq_zero_left h1, map_neg]
    refine ⟨x, ?_, ?_⟩
    · rw [hz, map_neg] at h2
      rw [LinearMap.mem_ker, reducedHx_apply, ← h2]
      abel
    · rw [hz]; rfl
  · rintro ⟨x', hx', hG⟩
    rw [LinearMap.mem_ker, reducedHx_apply] at hx'
    have hG' : (-AgInv (blockBx L Ex x'), x') = (z, x) := hG
    rw [Prod.mk.injEq] at hG'
    obtain ⟨rfl, rfl⟩ := hG'
    simp only [map_neg, hright]
    constructor
    · abel
    · rw [← hx']; abel

/-- **`eq:supp-exact-slow-rank-split`, general form.**
`rank 𝓛₀ = dim 𝒵_g + rank ℋ_x`. -/
theorem three_row_rank [FiniteDimensional ℝ Zg] [FiniteDimensional ℝ Xh]
    (hspan : ∀ κ, ∃ z x, κ = Jg z + Ex x)
    (hleft : ∀ z, AgInv (blockAg L Jg z) = z) (hright : ∀ z, blockAg L Jg (AgInv z) = z) :
    finrank ℝ (LinearMap.range L)
      = finrank ℝ Zg + finrank ℝ (LinearMap.range (reducedHx L Jg Ex AgInv)) := by
  have hsurj : LinearMap.range (Jg.coprod Ex) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro κ
    obtain ⟨z, x, rfl⟩ := hspan κ
    exact ⟨(z, x), by simp⟩
  have hrange : LinearMap.range (L.comp (Jg.coprod Ex)) = LinearMap.range L :=
    LinearMap.range_comp_of_range_eq_top L hsurj
  have hG : Function.Injective
      ((-(AgInv.comp (blockBx L Ex))).prod (LinearMap.id : Xh →ₗ[ℝ] Xh)) := by
    intro a b hab
    simpa using congrArg Prod.snd hab
  have hker : finrank ℝ (LinearMap.ker (L.comp (Jg.coprod Ex)))
      = finrank ℝ (LinearMap.ker (reducedHx L Jg Ex AgInv)) := by
    rw [ker_blockMap_eq_map L Jg Ex AgInv hleft hright]
    exact (Submodule.equivMapOfInjective _ hG _).finrank_eq.symm
  have h1 := LinearMap.finrank_range_add_finrank_ker (L.comp (Jg.coprod Ex))
  have h2 := LinearMap.finrank_range_add_finrank_ker (reducedHx L Jg Ex AgInv)
  rw [hrange, hker, Module.finrank_prod] at h1
  omega

/-- **`eq:supp-exact-slow-rank-split`.** With `dim 𝒵_g = 2`,
`rank 𝓛₀ = 2 + rank ℋ_x`. -/
theorem three_row_rank_two [FiniteDimensional ℝ Zg] [FiniteDimensional ℝ Xh]
    (hZ : finrank ℝ Zg = 2) (hspan : ∀ κ, ∃ z x, κ = Jg z + Ex x)
    (hleft : ∀ z, AgInv (blockAg L Jg z) = z) (hright : ∀ z, blockAg L Jg (AgInv z) = z) :
    finrank ℝ (LinearMap.range L) = 2 + finrank ℝ (LinearMap.range (reducedHx L Jg Ex AgInv)) := by
  rw [three_row_rank L Jg Ex AgInv hspan hleft hright, hZ]

/-- **Five-row surjectivity.** With `dim 𝒵_g = 2` and `dim ℋ = 3`, `𝓛₀` is onto iff
`rank ℋ_x = 3`. -/
theorem three_row_surjective_iff [FiniteDimensional ℝ Zg] [FiniteDimensional ℝ Xh]
    [FiniteDimensional ℝ Hs] (hZ : finrank ℝ Zg = 2) (hH : finrank ℝ Hs = 3)
    (hspan : ∀ κ, ∃ z x, κ = Jg z + Ex x)
    (hleft : ∀ z, AgInv (blockAg L Jg z) = z) (hright : ∀ z, blockAg L Jg (AgInv z) = z) :
    LinearMap.range L = ⊤ ↔ finrank ℝ (LinearMap.range (reducedHx L Jg Ex AgInv)) = 3 := by
  have hr := three_row_rank_two L Jg Ex AgInv hZ hspan hleft hright
  have hdim : finrank ℝ (Zg × Hs) = 5 := by rw [Module.finrank_prod, hZ, hH]
  constructor
  · intro htop
    rw [htop, finrank_top, hdim] at hr
    omega
  · intro h3
    apply Submodule.eq_top_of_finrank_eq
    rw [hr, h3, hdim]

/-- **`eq:supp-exact-defect-feedback`.** If the actual initialized coefficient
`κ_* = J_g z_* + E_x x_*` satisfies `𝓛₀ κ_* + f₀ = (Δ_g, 0)`, then
`ℋ_x x_* + f₀,H - 𝒞_g 𝒜_g⁻¹ f₀,g = -𝒞_g 𝒜_g⁻¹ Δ_g`. -/
theorem three_row_defect_feedback (hleft : ∀ z, AgInv (blockAg L Jg z) = z)
    (z x : _) (f₀ : Zg × Hs) (Δ : Zg) (h : L (Jg z + Ex x) + f₀ = (Δ, 0)) :
    reducedHx L Jg Ex AgInv x + f₀.2 - blockCg L Jg (AgInv f₀.1)
      = -blockCg L Jg (AgInv Δ) := by
  rw [map_split_eq_blocks, Prod.mk_add_mk, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hz : z = AgInv (Δ - blockBx L Ex x - f₀.1) := by
    rw [← hleft z, ← h1]; congr 1; abel
  rw [hz] at h2
  rw [reducedHx_apply]
  simp only [map_sub] at h2 ⊢
  rw [← sub_eq_zero, ← h2]; abel

/-- **`thm:supp-exact-three-row`, last clause.** Under the hypotheses of
`three_row_defect_feedback`, some `κ̃` with `𝓛₀ κ̃ = -f₀` exists iff
`𝒞_g 𝒜_g⁻¹ Δ_g ∈ Ran ℋ_x`. -/
theorem three_row_exists_iff_defect (hspan : ∀ κ, ∃ z x, κ = Jg z + Ex x)
    (hleft : ∀ z, AgInv (blockAg L Jg z) = z) (hright : ∀ z, blockAg L Jg (AgInv z) = z)
    (z x : _) (f₀ : Zg × Hs) (Δ : Zg) (h : L (Jg z + Ex x) + f₀ = (Δ, 0)) :
    (∃ κ, L κ = -f₀) ↔
      blockCg L Jg (AgInv Δ) ∈ LinearMap.range (reducedHx L Jg Ex AgInv) := by
  have hfb := three_row_defect_feedback L Jg Ex AgInv hleft z x f₀ Δ h
  have e : f₀.2 - blockCg L Jg (AgInv f₀.1)
      = -(blockCg L Jg (AgInv Δ) + reducedHx L Jg Ex AgInv x) := by
    rw [← sub_eq_zero, neg_add, ← hfb]; abel
  have := three_row_solvable_iff L Jg Ex AgInv hspan hleft hright f₀.1 f₀.2
  rw [Prod.mk.eta, e, Submodule.neg_mem_iff] at this
  rw [this]
  constructor
  · intro hm
    have := Submodule.sub_mem _ hm (LinearMap.mem_range_self (reducedHx L Jg Ex AgInv) x)
    simpa using this
  · intro hm
    exact Submodule.add_mem _ hm (LinearMap.mem_range_self _ x)

end ThreeRow

/-! ### The actual initial gate map on `𝒦₀ = ker Φ₀` -/

section InitialGate

variable {Xs W Zg Hs Xh : Type*}
  [NormedAddCommGroup Xs] [NormedSpace ℝ Xs] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Zg] [NormedSpace ℝ Zg] [NormedAddCommGroup Hs] [NormedSpace ℝ Hs]
  [AddCommGroup Xh] [Module ℝ Xh]

/-- The blocks of the initial gate map on `𝒦₀` at the vertical insertion `(0, J_g z)`:
`𝒜_g z = p_g C_red Df(0) (0, J_g z)` and `𝒞_g z = p_H Dg(0) (0, J_g z)`. -/
theorem initialGate_blocks (pg : W →L[ℝ] Zg) (pH : W →L[ℝ] Hs) (Cred : Xs →L[ℝ] W)
    (B : W →L[ℝ] W) (Df0 : Xs × W →L[ℝ] Xs) (Dg0 : Xs × W →L[ℝ] W) (Jg : Zg →L[ℝ] W)
    (hJ : ∀ z, B (Jg z) = 0) (z : Zg) :
    blockAg (initialGateOnKernel pg pH Cred B Df0 Dg0) (kernelInsertion Cred B Jg hJ) z
        = pg (Cred (Df0 (0, Jg z))) ∧
      blockCg (initialGateOnKernel pg pH Cred B Df0 Dg0) (kernelInsertion Cred B Jg hJ) z
        = pH (Dg0 (0, Jg z)) :=
  ⟨rfl, rfl⟩

/-- **`thm:supp-exact-three-row` for the initial gate map** `𝓛₀` of
`eq:supp-L0-definition` restricted to `𝒦₀ = ker Φ₀`, with vertical insertion
`z ↦ (0, J_g z)` (`B J_g = 0`) and an arbitrary complement insertion `E_x`:
solvability criterion `eq:supp-exact-hard-forcing` and rank split
`eq:supp-exact-slow-rank-split`. -/
theorem initial_gate_three_row [FiniteDimensional ℝ Zg] [FiniteDimensional ℝ Xh]
    (pg : W →L[ℝ] Zg) (pH : W →L[ℝ] Hs) (Cred : Xs →L[ℝ] W)
    (B : W →L[ℝ] W) (Df0 : Xs × W →L[ℝ] Xs) (Dg0 : Xs × W →L[ℝ] W) (Jg : Zg →L[ℝ] W)
    (hJ : ∀ z, B (Jg z) = 0)
    (Ex : Xh →ₗ[ℝ] LinearMap.ker (leadingConstraint Cred B : Xs × W →ₗ[ℝ] W))
    (AgInv : Zg →ₗ[ℝ] Zg) (hZ : finrank ℝ Zg = 2)
    (hspan : ∀ κ, ∃ z x, κ = kernelInsertion Cred B Jg hJ z + Ex x)
    (hleft : ∀ z, AgInv (pg (Cred (Df0 (0, Jg z)))) = z)
    (hright : ∀ z, pg (Cred (Df0 (0, Jg (AgInv z)))) = z) (fg : Zg) (fH : Hs) :
    ((∃ κ, initialGateOnKernel pg pH Cred B Df0 Dg0 κ = -(fg, fH)) ↔
      fH - pH (Dg0 (0, Jg (AgInv fg))) ∈ LinearMap.range
        (reducedHx (initialGateOnKernel pg pH Cred B Df0 Dg0) (kernelInsertion Cred B Jg hJ)
          Ex AgInv)) ∧
    finrank ℝ (LinearMap.range (initialGateOnKernel pg pH Cred B Df0 Dg0))
      = 2 + finrank ℝ (LinearMap.range
        (reducedHx (initialGateOnKernel pg pH Cred B Df0 Dg0) (kernelInsertion Cred B Jg hJ)
          Ex AgInv)) :=
  ⟨three_row_solvable_iff (initialGateOnKernel pg pH Cred B Df0 Dg0)
      (kernelInsertion Cred B Jg hJ) Ex AgInv hspan hleft hright fg fH,
    three_row_rank_two (initialGateOnKernel pg pH Cred B Df0 Dg0)
      (kernelInsertion Cred B Jg hJ) Ex AgInv hZ hspan hleft hright⟩

end InitialGate

/-! ## Slope coefficients from the original compatibility rows -/

section SlopeJets

variable {R Y Zg V Xs Ho : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Zg] [NormedSpace ℝ Zg]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup Xs] [NormedSpace ℝ Xs]
  [NormedAddCommGroup Ho] [NormedSpace ℝ Ho]

/-- The reduced chart is `C²` at `0` when `γ` is. -/
theorem reducedChart_contDiffAt (E : R →L[ℝ] V) (Jg : Zg →L[ℝ] V) (JH : Y →L[ℝ] V)
    {γ : R × Y → Zg} (hγ : ContDiffAt ℝ 2 γ 0) :
    ContDiffAt ℝ 2 (reducedChart E Jg JH γ) 0 := by
  unfold reducedChart
  have h1 : ContDiffAt ℝ 2 (fun q : R × Y => E q.1) 0 :=
    (E.contDiff.comp contDiff_fst).contDiffAt
  have h2 : ContDiffAt ℝ 2 (fun q : R × Y => Jg (γ q)) 0 :=
    Jg.contDiff.contDiffAt.comp 0 hγ
  have h3 : ContDiffAt ℝ 2 (fun q : R × Y => JH q.2) 0 :=
    (JH.contDiff.comp contDiff_snd).contDiffAt
  exact (h1.add h2).add h3

/-- First derivative of the reduced chart. -/
theorem reducedChart_hasFDerivAt (E : R →L[ℝ] V) (Jg : Zg →L[ℝ] V) (JH : Y →L[ℝ] V)
    {γ : R × Y → Zg} {q : R × Y} {Dγ : R × Y →L[ℝ] Zg} (hγ : HasFDerivAt γ Dγ q) :
    HasFDerivAt (reducedChart E Jg JH γ)
      (E.comp (ContinuousLinearMap.fst ℝ R Y) + Jg.comp Dγ
        + JH.comp (ContinuousLinearMap.snd ℝ R Y)) q := by
  have h1 : HasFDerivAt (fun q : R × Y => E q.1) (E.comp (ContinuousLinearMap.fst ℝ R Y)) q :=
    E.hasFDerivAt.comp q hasFDerivAt_fst
  have h2 : HasFDerivAt (fun q : R × Y => Jg (γ q)) (Jg.comp Dγ) q :=
    Jg.hasFDerivAt.comp q hγ
  have h3 : HasFDerivAt (fun q : R × Y => JH q.2)
      (JH.comp (ContinuousLinearMap.snd ℝ R Y)) q :=
    JH.hasFDerivAt.comp q hasFDerivAt_snd
  exact (h1.add h2).add h3

/-- Second derivative of the reduced chart: `D²Ξ(0)[u, w] = J_g D²γ(0)[u, w]`. -/
theorem reducedChart_sndDeriv (E : R →L[ℝ] V) (Jg : Zg →L[ℝ] V) (JH : Y →L[ℝ] V)
    {γ : R × Y → Zg} (hγ : ContDiffAt ℝ 2 γ 0) (u w : R × Y) :
    sndDeriv (reducedChart E Jg JH γ) 0 u w = Jg (sndDeriv γ 0 u w) := by
  have hγ1 : ∀ᶠ q in 𝓝 (0 : R × Y), DifferentiableAt ℝ γ q :=
    (hγ.eventually (by simp)).mono fun y hy => hy.differentiableAt two_ne_zero
  set C0 : R × Y →L[ℝ] V :=
    E.comp (ContinuousLinearMap.fst ℝ R Y) + JH.comp (ContinuousLinearMap.snd ℝ R Y)
  have hev : fderiv ℝ (reducedChart E Jg JH γ) =ᶠ[𝓝 0]
      fun q => C0 + Jg.comp (fderiv ℝ γ q) := by
    filter_upwards [hγ1] with q hq
    rw [(reducedChart_hasFDerivAt E Jg JH hq.hasFDerivAt).fderiv]
    simp only [C0]; abel
  have hD2γ : HasFDerivAt (fderiv ℝ γ) (fderiv ℝ (fderiv ℝ γ) 0) 0 :=
    ((hγ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have hall := ((hasFDerivAt_const Jg (0 : R × Y)).clm_comp hD2γ).const_add C0
  unfold sndDeriv
  rw [hev.fderiv_eq, hall.fderiv]
  simp

/-- **`prop:supp-exact-original-slope-jets`, `eq:supp-exact-original-slope-jets`.**
Let `Ξ(r, y) = 𝖤 r + J_g γ(r, y) + J_H y` with `γ` of class `C²`, `γ(0) = 0` and
`𝔠_g(Ξ(r, y)) = 0` near `0`; let `𝔠_g`, `𝔠_H` be `C²` at `0`, `f` differentiable at `0`,
`D𝔠_g(0) J_H = 0` (`eq:supp-exact-slope-entrance`) and `AgInv` a left inverse of
`𝒜_g = D𝔠_g(0) J_g`.  Then for the reduced functions `𝓕 = L_X f ∘ Ξ`, `𝓗 = 𝔠_H ∘ Ξ`
and every `v`, `c`,
`𝒬(c) = D𝔠_H(0) a_* + D²𝔠_H(0)[b(c), b(c)] - 𝒞_g 𝒜_g⁻¹ D²𝔠_g(0)[b(c), b(c)]`,
with `𝒞_g = D𝔠_H(0) J_g`, `b(c) = Ê v + J_H c`, `a_* = Ê L_X Df(0) b_*`. -/
theorem original_slope_jets (E : R →L[ℝ] V) (Jg : Zg →L[ℝ] V) (JH : Y →L[ℝ] V)
    (γ : R × Y → Zg) (cg : V → Zg) (cH : V → Ho) (f : V → Xs) (LX : Xs →L[ℝ] R)
    (AgInv : Zg →L[ℝ] Zg)
    (hγ : ContDiffAt ℝ 2 γ 0) (hγ0 : γ 0 = 0)
    (hcg : ContDiffAt ℝ 2 cg 0) (hcH : ContDiffAt ℝ 2 cH 0) (hf : DifferentiableAt ℝ f 0)
    (himp : ∀ᶠ q in 𝓝 (0 : R × Y), cg (reducedChart E Jg JH γ q) = 0)
    (hJH : ∀ y, fderiv ℝ cg 0 (JH y) = 0)
    (hAg : ∀ z, AgInv (fderiv ℝ cg 0 (Jg z)) = z) (v : R) (c : Y) :
    slopePolynomial (reducedDrift LX f (reducedChart E Jg JH γ))
        (reducedHarmonic cH (reducedChart E Jg JH γ)) v c
      = fderiv ℝ cH 0 (slopeAccel E Jg AgInv (fderiv ℝ cg 0) LX (fderiv ℝ f 0) v)
        + sndDeriv cH 0 (slopeDirection E Jg JH AgInv (fderiv ℝ cg 0) v c)
            (slopeDirection E Jg JH AgInv (fderiv ℝ cg 0) v c)
        - ((fderiv ℝ cH 0).comp Jg)
            (AgInv (sndDeriv cg 0 (slopeDirection E Jg JH AgInv (fderiv ℝ cg 0) v c)
              (slopeDirection E Jg JH AgInv (fderiv ℝ cg 0) v c))) := by
  set Ξ := reducedChart E Jg JH γ with hΞdef
  set Dcg := fderiv ℝ cg 0
  set DcH := fderiv ℝ cH 0
  have hΞ0 : Ξ 0 = 0 := by simp [hΞdef, reducedChart, hγ0]
  have hΞ2 : ContDiffAt ℝ 2 Ξ 0 := reducedChart_contDiffAt E Jg JH hγ
  have hcg2 : ContDiffAt ℝ 2 cg (Ξ 0) := hΞ0 ▸ hcg
  have hcH2 : ContDiffAt ℝ 2 cH (Ξ 0) := hΞ0 ▸ hcH
  have hγd : DifferentiableAt ℝ γ 0 := hγ.differentiableAt two_ne_zero
  have hΞd : DifferentiableAt ℝ Ξ 0 := hΞ2.differentiableAt two_ne_zero
  -- first derivative of the chart
  have hDΞ : ∀ q : R × Y, fderiv ℝ Ξ 0 q = E q.1 + Jg (fderiv ℝ γ 0 q) + JH q.2 := by
    intro q
    rw [(reducedChart_hasFDerivAt E Jg JH hγd.hasFDerivAt).fderiv]
    simp
  -- implicit relations from `𝔠_g ∘ Ξ = 0` near `0`
  have hzero : (cg ∘ Ξ) =ᶠ[𝓝 0] 0 := himp
  have hfirst : ∀ q, Dcg (fderiv ℝ Ξ 0 q) = 0 := by
    intro q
    have h := fderiv_of_eventually_zero (cg ∘ Ξ) 0 hzero
    rw [fderiv_comp 0 (hcg2.differentiableAt two_ne_zero) hΞd, hΞ0] at h
    simpa using congrArg (fun T => T q) h
  have hγ1 : ∀ r y, fderiv ℝ γ 0 (r, y) = -AgInv (Dcg (E r)) := by
    intro r y
    have h := hfirst (r, y)
    rw [hDΞ, map_add, map_add, hJH, add_zero] at h
    rw [← hAg (fderiv ℝ γ 0 (r, y)), eq_neg_of_add_eq_zero_right h, map_neg]
  have hDΞ' : ∀ r y, fderiv ℝ Ξ 0 (r, y) = hatE E Jg AgInv Dcg r + JH y := by
    intro r y
    rw [hDΞ, hγ1]
    simp [hatE, sub_eq_add_neg]
  have hsecond : ∀ u w, sndDeriv γ 0 u w
      = -AgInv (sndDeriv cg 0 (fderiv ℝ Ξ 0 u) (fderiv ℝ Ξ 0 w)) := by
    intro u w
    have h := sndDeriv_of_eventually_zero (cg ∘ Ξ) 0 hzero u w
    rw [sndDeriv_comp cg Ξ 0 hcg2 hΞ2, hΞ0, reducedChart_sndDeriv E Jg JH hγ] at h
    rw [← hAg (sndDeriv γ 0 u w), eq_neg_of_add_eq_zero_right h, map_neg]
  -- the reduced harmonic function
  have hH : ∀ u w, sndDeriv (reducedHarmonic cH Ξ) 0 u w
      = sndDeriv cH 0 (fderiv ℝ Ξ 0 u) (fderiv ℝ Ξ 0 w)
        - DcH (Jg (AgInv (sndDeriv cg 0 (fderiv ℝ Ξ 0 u) (fderiv ℝ Ξ 0 w)))) := by
    intro u w
    have : reducedHarmonic cH Ξ = cH ∘ Ξ := rfl
    rw [this, sndDeriv_comp cH Ξ 0 hcH2 hΞ2, hΞ0, reducedChart_sndDeriv E Jg JH hγ, hsecond,
      map_neg, map_neg, sub_eq_add_neg]
  have hH1 : fderiv ℝ (reducedHarmonic cH Ξ) 0 = DcH.comp (fderiv ℝ Ξ 0) := by
    have : reducedHarmonic cH Ξ = cH ∘ Ξ := rfl
    rw [this, fderiv_comp 0 (hcH2.differentiableAt two_ne_zero) hΞd, hΞ0]
  have hF1 : ∀ q, fderiv ℝ (reducedDrift LX f Ξ) 0 q
      = LX (fderiv ℝ f 0 (fderiv ℝ Ξ 0 q)) := by
    intro q
    have hf2 : HasFDerivAt f (fderiv ℝ f 0) (Ξ 0) := hΞ0 ▸ hf.hasFDerivAt
    have : HasFDerivAt (reducedDrift LX f Ξ)
        (LX.comp ((fderiv ℝ f 0).comp (fderiv ℝ Ξ 0))) 0 :=
      LX.hasFDerivAt.comp 0 (hf2.comp 0 hΞd.hasFDerivAt)
    rw [this.fderiv]; rfl
  -- symmetry of the second derivatives of the original rows
  have hsH : ∀ a b, sndDeriv cH 0 a b = sndDeriv cH 0 b a :=
    fun a b => hcH.isSymmSndFDerivAt (by simp) a b
  have hsg : ∀ a b, sndDeriv cg 0 a b = sndDeriv cg 0 b a :=
    fun a b => hcg.isSymmSndFDerivAt (by simp) a b
  -- assemble
  unfold slopePolynomial
  rw [hH1, hH, hH, hH, ContinuousLinearMap.comp_apply, hF1]
  simp only [hDΞ', map_zero, add_zero, zero_add]
  simp only [slopeAccel, slopeDirection, slopeBase, ContinuousLinearMap.comp_apply]
  set bs := hatE E Jg AgInv Dcg v
  set h := JH c
  have e1 := hsH h bs
  have e2 := hsg h bs
  unfold sndDeriv at e1 e2 ⊢
  simp only [map_add, add_apply]
  rw [e1, e2]
  module

/-- Composition with a fixed linear row map `T`: `D²(T ∘ H)(0) = T ∘ D²H(0)`. -/
theorem sndDeriv_clm_comp {Ho' : Type*} [NormedAddCommGroup Ho'] [NormedSpace ℝ Ho']
    (T : Ho →L[ℝ] Ho') (H : R × Y → Ho) (hH : ContDiffAt ℝ 2 H 0) (u w : R × Y) :
    sndDeriv (T ∘ H) 0 u w = T (sndDeriv H 0 u w) := by
  rw [sndDeriv_comp T H 0 T.contDiff.contDiffAt hH, T.fderiv]
  have : sndDeriv T (H 0) (fderiv ℝ H 0 u) (fderiv ℝ H 0 w) = 0 := by
    unfold sndDeriv
    have hT : fderiv ℝ (T : Ho → Ho') = fun _ => T := funext fun _ => T.fderiv
    rw [hT]; simp
  rw [this, zero_add]

/-- **Row convention** (`prop:supp-exact-original-slope-jets`, last sentence): a fixed
linear change `T` of the harmonic rows transforms the slope polynomial by `T`. -/
theorem slopePolynomial_rowConvention {Ho' : Type*} [NormedAddCommGroup Ho']
    [NormedSpace ℝ Ho'] (T : Ho →L[ℝ] Ho') (Fr : R × Y → R) (H : R × Y → Ho)
    (hH : ContDiffAt ℝ 2 H 0) (v : R) (c : Y) :
    slopePolynomial Fr (T ∘ H) v c = T (slopePolynomial Fr H v c) := by
  unfold slopePolynomial
  rw [fderiv_comp 0 T.differentiableAt (hH.differentiableAt two_ne_zero), T.fderiv,
    sndDeriv_clm_comp T H hH, sndDeriv_clm_comp T H hH, sndDeriv_clm_comp T H hH]
  simp only [ContinuousLinearMap.comp_apply, map_add, map_smul]

/-- **Row convention for the whole formula.** In the harmonic row convention
`𝔠_H' = T ∘ 𝔠_H` the slope polynomial is `T` applied to the right-hand side of
`eq:supp-exact-original-slope-jets`; equivalently every ingredient (`𝒬`, `D𝔠_H(0)`,
`D²𝔠_H(0)`, `𝒞_g = D𝔠_H(0) J_g`, hence `q₀ = 𝒬(0)`) is transformed together. -/
theorem original_slope_jets_rowConvention {Ho' : Type*} [NormedAddCommGroup Ho']
    [NormedSpace ℝ Ho'] (T : Ho →L[ℝ] Ho') (E : R →L[ℝ] V) (Jg : Zg →L[ℝ] V)
    (JH : Y →L[ℝ] V) (γ : R × Y → Zg) (cg : V → Zg) (cH : V → Ho) (f : V → Xs)
    (LX : Xs →L[ℝ] R) (AgInv : Zg →L[ℝ] Zg)
    (hγ : ContDiffAt ℝ 2 γ 0) (hγ0 : γ 0 = 0)
    (hcg : ContDiffAt ℝ 2 cg 0) (hcH : ContDiffAt ℝ 2 cH 0) (hf : DifferentiableAt ℝ f 0)
    (himp : ∀ᶠ q in 𝓝 (0 : R × Y), cg (reducedChart E Jg JH γ q) = 0)
    (hJH : ∀ y, fderiv ℝ cg 0 (JH y) = 0)
    (hAg : ∀ z, AgInv (fderiv ℝ cg 0 (Jg z)) = z) (v : R) (c : Y) :
    slopePolynomial (reducedDrift LX f (reducedChart E Jg JH γ))
        (reducedHarmonic (T ∘ cH) (reducedChart E Jg JH γ)) v c
      = T (fderiv ℝ cH 0 (slopeAccel E Jg AgInv (fderiv ℝ cg 0) LX (fderiv ℝ f 0) v)
        + sndDeriv cH 0 (slopeDirection E Jg JH AgInv (fderiv ℝ cg 0) v c)
            (slopeDirection E Jg JH AgInv (fderiv ℝ cg 0) v c)
        - ((fderiv ℝ cH 0).comp Jg)
            (AgInv (sndDeriv cg 0 (slopeDirection E Jg JH AgInv (fderiv ℝ cg 0) v c)
              (slopeDirection E Jg JH AgInv (fderiv ℝ cg 0) v c)))) := by
  have hΞ0 : reducedChart E Jg JH γ 0 = 0 := by simp [reducedChart, hγ0]
  have hcH2 : ContDiffAt ℝ 2 cH (reducedChart E Jg JH γ 0) := hΞ0 ▸ hcH
  have hHc : ContDiffAt ℝ 2 (reducedHarmonic cH (reducedChart E Jg JH γ)) 0 :=
    hcH2.comp 0 (reducedChart_contDiffAt E Jg JH hγ)
  have e : reducedHarmonic (T ∘ cH) (reducedChart E Jg JH γ)
      = T ∘ reducedHarmonic cH (reducedChart E Jg JH γ) := rfl
  rw [e, slopePolynomial_rowConvention T _ _ hHc,
    original_slope_jets E Jg JH γ cg cH f LX AgInv hγ hγ0 hcg hcH hf himp hJH hAg v c]

end SlopeJets

end ExactSlowGate
end RenewalGeometry
