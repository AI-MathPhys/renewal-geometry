/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Sharp affine acquisition and the selector-fibre boundary

Exact encoding of `thm:SMYM-affine-minimality` (CY.10–CY.13).

## The affine panel (CY.9–CY.11)

For executable contrasts `a : Fin r → E` and a positive setting metric `q`, the panel
is `A v = (⟪a α, v⟫)_α` and the Fisher form `F = A^* Q A` is
`F v = ∑ α, q α ⟪a α, v⟫ • a α`.

* `posDefOn_iff_injective` (CY.10): `F ≻ 0` on `E` iff the panel is injective;
* `reconstruction_iff`: the source-labelled moments `b_{ℓ,α} = μ_ℓ (A θ_ℓ)_α` identify
  `θ_ℓ` exactly when `F ≻ 0`;
* `theta_eq` (CY.11): `θ_ℓ = F⁻¹ A^* Q b_ℓ / μ_ℓ`;
* `exists_null_of_rank_lt`: a panel of fewer than `dim E` rows has a null direction.

## The faithful selector fibre (CY.12–CY.13)

For response atoms `z : Fin m → E` and the acquisition dimension
`d = dim aff(Z) = finrank (vectorSpan (range z))`, the faithful fibre
`𝒬(t) = {c > 0 : ∑ c = 1, ∑ c_i z_i = t}` satisfies, whenever it is nonempty
(i.e. `t` is in the relative interior of the convex hull):

* `affineSpan_fibre`: its affine span is `c₀ + ker L` with `L c = (∑ c, ∑ c_i z_i)`;
* `finrank_ker_augmented`: `dim ker L = m - d - 1`, the affine dimension (CY.13);
* `fibre_singleton_iff`: the fibre is a singleton iff `d = m - 1` iff the atoms are
  affinely independent (the simplicial branch).
-/

open Finset
open scoped RealInnerProductSpace

namespace NCG
namespace SMYMAffineMinimality

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### The affine panel -/

section panel

variable {r : ℕ} (a : Fin r → E) (q : Fin r → ℝ)

/-- The panel `A v = (⟪a α, v⟫)_α`. -/
noncomputable def panel : E →ₗ[ℝ] (Fin r → ℝ) where
  toFun v := fun α => ⟪a α, v⟫
  map_add' u v := by funext α; simp [inner_add_right]
  map_smul' c v := by funext α; simp [inner_smul_right]

theorem panel_apply (v : E) (α : Fin r) : panel a v α = ⟪a α, v⟫ := rfl

/-- The Fisher form `F = A^* Q A`, `F v = ∑ α, q α ⟪a α, v⟫ • a α`. -/
noncomputable def fisher : E →ₗ[ℝ] E where
  toFun v := ∑ α, (q α * ⟪a α, v⟫) • a α
  map_add' u v := by simp [inner_add_right, mul_add, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [inner_smul_right, RingHom.id_apply, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun α _ => ?_
    ring_nf

theorem quad_eq (v : E) : ⟪v, fisher a q v⟫ = ∑ α, q α * ⟪a α, v⟫ ^ 2 := by
  simp only [fisher, LinearMap.coe_mk, AddHom.coe_mk, inner_sum, inner_smul_right]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [real_inner_comm]
  ring

/-- **(CY.10)**: `F ≻ 0` on the acquisition space. -/
def PosDefOn : Prop := ∀ v : E, v ≠ 0 → 0 < ⟪v, fisher a q v⟫

/-- **(CY.10)**: `F ≻ 0` iff the panel is injective (the contrasts separate `E`). -/
theorem posDefOn_iff_injective (hq : ∀ α, 0 < q α) :
    PosDefOn a q ↔ Function.Injective (panel a) := by
  constructor
  · intro h u v huv
    by_contra hne
    have hpos := h (u - v) (sub_ne_zero.mpr hne)
    rw [quad_eq] at hpos
    have hz : ∀ α, ⟪a α, u - v⟫ = 0 := fun α => by
      have := congrFun huv α
      simp only [panel_apply] at this
      rw [inner_sub_right, this, sub_self]
    simp [hz] at hpos
  · intro hinj v hv
    rw [quad_eq]
    have hne : panel a v ≠ 0 := fun h0 => hv (hinj (by rw [h0, map_zero]))
    obtain ⟨α, hα⟩ : ∃ α, ⟪a α, v⟫ ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne (funext fun α => by simp [panel_apply, hall α])
    have h1 : 0 < q α * ⟪a α, v⟫ ^ 2 :=
      mul_pos (hq α) (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hα)))
    exact lt_of_lt_of_le h1
      (Finset.single_le_sum (f := fun β => q β * ⟪a β, v⟫ ^ 2)
        (fun β _ => mul_nonneg (hq β).le (sq_nonneg _)) (Finset.mem_univ α))

/-- **(CY.9)**: the source-labelled moments `b_{ℓ,α} = μ_ℓ (A θ_ℓ)_α`. -/
noncomputable def moments (μ : ℝ) (θ : E) : Fin r → ℝ := fun α => μ * panel a θ α

/-- **(CY.10)**: the panel reconstructs every conditional response mean exactly when
`F ≻ 0`. -/
theorem reconstruction_iff (hq : ∀ α, 0 < q α) {μ : ℝ} (hμ : μ ≠ 0) :
    (∀ θ θ' : E, moments a μ θ = moments a μ θ' → θ = θ') ↔ PosDefOn a q := by
  rw [posDefOn_iff_injective a q hq]
  constructor
  · intro h u v huv
    exact h u v (by funext α; simp [moments, huv])
  · intro hinj θ θ' h
    apply hinj
    funext α
    have := congrFun h α
    simp only [moments] at this
    exact mul_left_cancel₀ hμ this

theorem fisher_injective (h : PosDefOn a q) : Function.Injective (fisher a q) := by
  intro u v huv
  by_contra hne
  have := h (u - v) (sub_ne_zero.mpr hne)
  rw [map_sub, huv, sub_self, inner_zero_right] at this
  exact lt_irrefl _ this

/-- The Fisher form as a linear automorphism on the positive branch. -/
noncomputable def fisherEquiv (h : PosDefOn a q) : E ≃ₗ[ℝ] E :=
  LinearEquiv.ofBijective (fisher a q)
    ⟨fisher_injective a q h, LinearMap.injective_iff_surjective.mp (fisher_injective a q h)⟩

/-- `F θ = A^* Q (b_ℓ / μ_ℓ)`. -/
theorem fisher_eq_adjoint {μ : ℝ} (hμ : μ ≠ 0) (θ : E) :
    fisher a q θ = ∑ α, (q α * (moments a μ θ α / μ)) • a α := by
  simp [fisher, moments, panel_apply, mul_div_cancel_left₀ _ hμ]

/-- **(CY.11)**: `θ_ℓ = F⁻¹ A^* Q b_ℓ / μ_ℓ`. -/
theorem theta_eq (h : PosDefOn a q) {μ : ℝ} (hμ : μ ≠ 0) (θ : E) :
    θ = (fisherEquiv a q h).symm (∑ α, (q α * (moments a μ θ α / μ)) • a α) := by
  rw [← fisher_eq_adjoint a q hμ θ]
  exact ((fisherEquiv a q h).symm_apply_apply θ).symm

/-- A panel with fewer rows than `dim E` has a nonzero null direction (so some
conditional mean is not acquired). -/
theorem exists_null_of_rank_lt (hr : r < Module.finrank ℝ E) :
    ∃ v : E, v ≠ 0 ∧ panel a v = 0 := by
  have h := LinearMap.finrank_range_add_finrank_ker (panel a)
  have h1 : Module.finrank ℝ (LinearMap.range (panel a)) ≤ r := by
    have := Submodule.finrank_le (LinearMap.range (panel a))
    rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
  have hker : 0 < Module.finrank ℝ (LinearMap.ker (panel a)) := by omega
  obtain ⟨⟨v, hv⟩, hne⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hker
  exact ⟨v, fun h0 => hne (Subtype.ext h0), hv⟩

end panel

/-! ### The faithful selector fibre -/

section fibre

variable {m : ℕ} (z : Fin m → E)

/-- The augmented map `L c = (∑ c, ∑ c_i z_i)`. -/
noncomputable def augmented : (Fin m → ℝ) →ₗ[ℝ] ℝ × E :=
  LinearMap.prod (Fintype.linearCombination ℝ (fun _ : Fin m => (1 : ℝ)))
    (Fintype.linearCombination ℝ z)

theorem augmented_apply (c : Fin m → ℝ) : augmented z c = (∑ i, c i, ∑ i, c i • z i) := by
  simp [augmented, Fintype.linearCombination_apply]

/-- **(CY.12)**: the faithful selector fibre over the affine mean `t`. -/
def fibre (t : E) : Set (Fin m → ℝ) :=
  {c | (∀ i, 0 < c i) ∧ ∑ i, c i = 1 ∧ ∑ i, c i • z i = t}

/-- The sharp acquisition dimension `d = dim aff(Z)`. -/
noncomputable def acquisitionDim : ℕ := Module.finrank ℝ (vectorSpan ℝ (Set.range z))

/-- The centering map `(c, v) ↦ v - c • z i₀`. -/
noncomputable def centering (i₀ : Fin m) : ℝ × E →ₗ[ℝ] E where
  toFun x := x.2 - x.1 • z i₀
  map_add' x y := by simp [add_smul]; abel
  map_smul' c x := by simp [smul_sub, smul_smul]

theorem centering_comp_augmented (i₀ : Fin m) :
    (centering z i₀).comp (augmented z) = Fintype.linearCombination ℝ (fun i => z i - z i₀) := by
  ext c
  simp [centering, augmented_apply, Fintype.linearCombination_apply, smul_sub,
    Finset.sum_sub_distrib]

/-- `rank L = d + 1`. -/
theorem finrank_range_augmented (i₀ : Fin m) :
    Module.finrank ℝ (LinearMap.range (augmented z)) = acquisitionDim z + 1 := by
  set R := LinearMap.range (augmented z) with hR
  set g := (centering z i₀).comp R.subtype with hg
  have hrn := LinearMap.finrank_range_add_finrank_ker g
  -- the range of `g` is the vector span
  have hrange : LinearMap.range g = vectorSpan ℝ (Set.range z) := by
    rw [hg, LinearMap.range_comp, Submodule.range_subtype, hR, ← LinearMap.range_comp,
      centering_comp_augmented, Fintype.range_linearCombination,
      vectorSpan_range_eq_span_range_vsub_right ℝ z i₀]
    simp only [vsub_eq_sub]
  -- the kernel of `g` is the line through `(1, z i₀)`
  have hu : ((1 : ℝ), z i₀) ∈ R := ⟨Pi.single i₀ 1, by simp [augmented_apply, Pi.single_apply]⟩
  set u : R := ⟨((1 : ℝ), z i₀), hu⟩ with hudef
  have hker : LinearMap.ker g = Submodule.span ℝ {u} := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
    constructor
    · intro hx
      refine ⟨x.1.1, ?_⟩
      apply Subtype.ext
      have hx' : (x : ℝ × E).2 - (x : ℝ × E).1 • z i₀ = 0 := hx
      rw [sub_eq_zero] at hx'
      ext
      · simp [hudef]
      · simp [hudef, hx']
    · rintro ⟨c, rfl⟩
      change ((c • u : R) : ℝ × E).2 - ((c • u : R) : ℝ × E).1 • z i₀ = 0
      simp [hudef]
  have hu0 : u ≠ 0 := fun h0 => by
    have := congrArg (fun x : R => (x : ℝ × E).1) h0
    simp [hudef] at this
  rw [hrange, hker, finrank_span_singleton hu0] at hrn
  unfold acquisitionDim
  omega

/-- **(CY.13)**: `dim ker L = m - d - 1`. -/
theorem finrank_ker_augmented (hm : 0 < m) :
    Module.finrank ℝ (LinearMap.ker (augmented z)) = m - acquisitionDim z - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (augmented z)
  rw [finrank_range_augmented z ⟨0, hm⟩, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    at h
  omega

theorem acquisitionDim_add_one_le (hm : 0 < m) : acquisitionDim z + 1 ≤ m := by
  have h := LinearMap.finrank_range_add_finrank_ker (augmented z)
  rw [finrank_range_augmented z ⟨0, hm⟩, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    at h
  omega

variable {z}

theorem pos_of_mem_fibre {t : E} {c₀ : Fin m → ℝ} (h₀ : c₀ ∈ fibre z t) : 0 < m := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · exfalso
    have := h₀.2.1
    subst hm
    simp at this
  · exact hm

/-- The fibre is the positive part of the affine subspace `c₀ + ker L`. -/
theorem mem_fibre_iff {t : E} {c₀ : Fin m → ℝ} (h₀ : c₀ ∈ fibre z t) (c : Fin m → ℝ) :
    c ∈ fibre z t ↔ c - c₀ ∈ LinearMap.ker (augmented z) ∧ ∀ i, 0 < c i := by
  obtain ⟨-, hs₀, hz₀⟩ := h₀
  simp only [fibre, Set.mem_setOf_eq, LinearMap.mem_ker, map_sub, augmented_apply, hs₀, hz₀,
    Prod.ext_iff, sub_eq_zero]
  tauto

/-- The fibre contains a ball of the affine subspace around any of its points. -/
theorem exists_ball_subset_fibre {t : E} {c₀ : Fin m → ℝ} (h₀ : c₀ ∈ fibre z t) :
    ∃ ε > 0, ∀ v ∈ LinearMap.ker (augmented z), ‖v‖ < ε → c₀ + v ∈ fibre z t := by
  have hm := pos_of_mem_fibre h₀
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  refine ⟨univ.inf' univ_nonempty c₀, ?_, fun v hv hvε => ?_⟩
  · obtain ⟨i, -, hi⟩ := exists_mem_eq_inf' univ_nonempty c₀
    rw [hi]; exact h₀.1 i
  · rw [mem_fibre_iff h₀]
    refine ⟨by simpa using hv, fun i => ?_⟩
    have h1 : ‖v i‖ ≤ ‖v‖ := norm_le_pi_norm v i
    have h2 : univ.inf' univ_nonempty c₀ ≤ c₀ i := inf'_le _ (mem_univ i)
    have h3 : -(v i) ≤ ‖v i‖ := by
      rw [Real.norm_eq_abs]; exact neg_le_abs _
    simp only [Pi.add_apply]
    linarith

/-- **(CY.13)**: the affine span of the fibre is `c₀ + ker L`. -/
theorem affineSpan_fibre {t : E} {c₀ : Fin m → ℝ} (h₀ : c₀ ∈ fibre z t) :
    affineSpan ℝ (fibre z t) = AffineSubspace.mk' c₀ (LinearMap.ker (augmented z)) := by
  apply le_antisymm
  · rw [affineSpan_le]
    intro c hc
    rw [SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub]
    exact ((mem_fibre_iff h₀ c).mp hc).1
  · intro x hx
    rw [AffineSubspace.mem_mk', vsub_eq_sub] at hx
    obtain ⟨ε, hε, hball⟩ := exists_ball_subset_fibre h₀
    have hc₀ : c₀ ∈ affineSpan ℝ (fibre z t) := mem_affineSpan ℝ h₀
    by_cases hv : x - c₀ = 0
    · rw [sub_eq_zero] at hv; rw [hv]; exact hc₀
    · set v := x - c₀ with hvdef
      have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
      set w := (ε / (2 * ‖v‖)) • v with hw
      have hwker : w ∈ LinearMap.ker (augmented z) := Submodule.smul_mem _ _ hx
      have hwn : ‖w‖ < ε := by
        rw [hw, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
        field_simp
        linarith
      have hmem := hball w hwker hwn
      have hdir : w ∈ (affineSpan ℝ (fibre z t)).direction := by
        rw [direction_affineSpan]
        have := vsub_mem_vectorSpan ℝ hmem h₀
        simpa using this
      have hvdir : v ∈ (affineSpan ℝ (fibre z t)).direction := by
        have : v = (2 * ‖v‖ / ε) • w := by
          rw [hw, smul_smul]
          field_simp
          simp
        rw [this]
        exact Submodule.smul_mem _ _ hdir
      have := AffineSubspace.vadd_mem_of_mem_direction hvdir hc₀
      rwa [vadd_eq_add, hvdef, sub_add_cancel] at this

/-- **(CY.13)**: the affine dimension of the fibre is `m - d - 1`. -/
theorem finrank_direction_affineSpan_fibre {t : E} {c₀ : Fin m → ℝ} (h₀ : c₀ ∈ fibre z t) :
    Module.finrank ℝ (affineSpan ℝ (fibre z t)).direction = m - acquisitionDim z - 1 := by
  rw [affineSpan_fibre h₀, AffineSubspace.direction_mk',
    finrank_ker_augmented z (pos_of_mem_fibre h₀)]

/-- **Simplicial branch**: the fibre is a singleton iff `d = m - 1` iff the response atoms
are affinely independent. -/
theorem fibre_singleton_iff {t : E} {c₀ : Fin m → ℝ} (h₀ : c₀ ∈ fibre z t) :
    (fibre z t = {c₀} ↔ acquisitionDim z = m - 1) ∧
      (acquisitionDim z = m - 1 ↔ AffineIndependent ℝ z) := by
  have hm := pos_of_mem_fibre h₀
  have hle := acquisitionDim_add_one_le z hm
  have hker := finrank_ker_augmented z hm
  constructor
  · constructor
    · intro hsing
      -- the kernel is trivial
      have hbot : LinearMap.ker (augmented z) = ⊥ := by
        by_contra hne
        obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
        obtain ⟨ε, hε, hball⟩ := exists_ball_subset_fibre h₀
        have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
        set w := (ε / (2 * ‖v‖)) • v with hw
        have hwker : w ∈ LinearMap.ker (augmented z) := Submodule.smul_mem _ _ hv
        have hwn : ‖w‖ < ε := by
          rw [hw, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
          field_simp
          linarith
        have hmem := hball w hwker hwn
        rw [hsing, Set.mem_singleton_iff] at hmem
        have hw0 : w = 0 := by
          have := congrArg (fun c => c - c₀) hmem
          simpa using this
        have : (ε / (2 * ‖v‖)) ≠ 0 := by positivity
        exact hv0 ((smul_eq_zero.mp hw0).resolve_left this)
      have h0 : Module.finrank ℝ (LinearMap.ker (augmented z)) = 0 := by
        rw [hbot]; exact finrank_bot ℝ _
      omega
    · intro hd
      have h0 : Module.finrank ℝ (LinearMap.ker (augmented z)) = 0 := by omega
      have hbot : LinearMap.ker (augmented z) = ⊥ := Submodule.finrank_eq_zero.mp h0
      ext c
      rw [Set.mem_singleton_iff, mem_fibre_iff h₀]
      constructor
      · rintro ⟨hc, -⟩
        rw [hbot, Submodule.mem_bot, sub_eq_zero] at hc
        exact hc
      · rintro rfl
        exact ⟨by simp, h₀.1⟩
  · have hc : Fintype.card (Fin m) = (m - 1) + 1 := by
      rw [Fintype.card_fin]; omega
    rw [affineIndependent_iff_finrank_vectorSpan_eq ℝ z hc]
    rfl

end fibre

end SMYMAffineMinimality
end NCG
