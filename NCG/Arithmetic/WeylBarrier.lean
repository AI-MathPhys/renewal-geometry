/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The scalar-invariant two-channel Weyl barrier and the scalar-bulk no-go
  (`thm:v002-weyl-barrier`, `thm:v002-scalar-bulk`, arithmetic monograph)

The spectral quantities are represented by their Courant–Fischer
min–max values (`lamMin`, `lamMax` — the extreme Rayleigh bounds;
`lamTwo`, `lamTwoTop` — the second levels through two-dimensional
trial subspaces), which agree with the sorted eigenvalues for
self-adjoint operators on a finite-dimensional space.  The affine
barrier is
`Γ^W(L,D;g) = max{(ℓ₂−m)−(d₁−d̄), (ℓ₁−m)−(d₂−d̄)}`.

* `weyl_barrier` — `λ₂(L−D) − μ ≥ Γ^W(L,D;g)`
  (both Weyl channels through the same trial subspace);
* `scalar_bulk` — if the compressed defect `L − cI − D` has Rayleigh
  quotients bounded by `ε` on the physical subspace (which has a
  two-dimensional trial subspace and carries `g`), then
  `Γ^W(L,D;g) ≤ 2ε`: no scalar bulk can supply an affine-invariant
  gap.
-/

open scoped InnerProductSpace

namespace NCG

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The (real) Rayleigh quotient at a unit vector. -/
noncomputable def rayleigh (T : H →L[ℂ] H) (x : H) : ℝ :=
  (⟪x, T x⟫_ℂ).re

/-- Unit vectors of a subspace. -/
def unitSet (V : Submodule ℂ H) : Set H := {x | x ∈ V ∧ ‖x‖ = 1}

/-- A two-dimensional trial subspace. -/
def TwoDim (V : Submodule ℂ H) : Prop := Module.finrank ℂ V = 2

/-- Largest Rayleigh value over the unit sphere of a subspace. -/
noncomputable def maxOn (T : H →L[ℂ] H) (V : Submodule ℂ H) : ℝ :=
  sSup (rayleigh T '' unitSet V)

/-- Smallest Rayleigh value over the unit sphere of a subspace. -/
noncomputable def minOn (T : H →L[ℂ] H) (V : Submodule ℂ H) : ℝ :=
  sInf (rayleigh T '' unitSet V)

/-- Bottom of the Rayleigh range (`ℓ₁`). -/
noncomputable def lamMin (T : H →L[ℂ] H) : ℝ :=
  sInf (rayleigh T '' {x : H | ‖x‖ = 1})

/-- Top of the Rayleigh range (`d₁`). -/
noncomputable def lamMax (T : H →L[ℂ] H) : ℝ :=
  sSup (rayleigh T '' {x : H | ‖x‖ = 1})

/-- Second level from below (`ℓ₂`): min–max over two-dimensional
trial subspaces. -/
noncomputable def lamTwo (T : H →L[ℂ] H) : ℝ :=
  sInf (Set.image (maxOn T) {V : Submodule ℂ H | TwoDim V})

/-- Second level from above (`d₂`): max–min over two-dimensional
trial subspaces. -/
noncomputable def lamTwoTop (T : H →L[ℂ] H) : ℝ :=
  sSup (Set.image (minOn T) {V : Submodule ℂ H | TwoDim V})

/-- The affine two-channel Weyl barrier `Γ^W(L,D;g)`. -/
noncomputable def weylGap (L D : H →L[ℂ] H) (g : H) : ℝ :=
  max ((lamTwo L - rayleigh L g) - (lamMax D - rayleigh D g))
    ((lamMin L - rayleigh L g) - (lamTwoTop D - rayleigh D g))

/-- Rayleigh values at unit vectors are bounded by the operator
norm. -/
lemma abs_rayleigh_le (T : H →L[ℂ] H) {x : H} (hx : ‖x‖ = 1) :
    |rayleigh T x| ≤ ‖T‖ := by
  have h1 : |(⟪x, T x⟫_ℂ).re| ≤ ‖⟪x, T x⟫_ℂ‖ := Complex.abs_re_le_norm _
  have h2 : ‖⟪x, T x⟫_ℂ‖ ≤ ‖x‖ * ‖T x‖ := norm_inner_le_norm x (T x)
  have h3 : ‖T x‖ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
  calc |rayleigh T x| ≤ ‖x‖ * ‖T x‖ := h1.trans h2
    _ ≤ ‖x‖ * (‖T‖ * ‖x‖) := by
        exact mul_le_mul_of_nonneg_left h3 (norm_nonneg x)
    _ = ‖T‖ := by rw [hx]; ring

/-- Rayleigh quotients are additive across operator differences. -/
lemma rayleigh_sub (S T : H →L[ℂ] H) (x : H) :
    rayleigh (S - T) x = rayleigh S x - rayleigh T x := by
  simp only [rayleigh, sub_apply, inner_sub_right, Complex.sub_re]

/-- A real scalar operator has constant Rayleigh quotient on the
unit sphere. -/
lemma rayleigh_smul_one (c : ℝ) {x : H} (hx : ‖x‖ = 1) :
    rayleigh (c • (1 : H →L[ℂ] H)) x = c := by
  have h1 : (c • (1 : H →L[ℂ] H)) x = (c : ℂ) • x := by
    simp [Complex.coe_smul]
  rw [rayleigh, h1, inner_smul_right, inner_self_eq_norm_sq_to_K, hx]
  simp

/-- Every two-dimensional subspace contains a unit vector. -/
lemma exists_unit_twoDim {V : Submodule ℂ H} (hV : TwoDim V) :
    ∃ x, x ∈ V ∧ ‖x‖ = 1 := by
  have hne : V ≠ ⊥ := by
    intro h
    rw [TwoDim, h, finrank_bot] at hV
    omega
  obtain ⟨v, hvV, hv0⟩ := (Submodule.ne_bot_iff V).mp hne
  have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
  refine ⟨((‖v‖ : ℂ))⁻¹ • v, V.smul_mem _ hvV, ?_⟩
  rw [norm_smul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hnv]

/-- Rayleigh images of unit-vector sets are bounded above. -/
lemma bddAbove_ray (T : H →L[ℂ] H) {S : Set H}
    (hS : ∀ x ∈ S, ‖x‖ = 1) : BddAbove (rayleigh T '' S) := by
  refine ⟨‖T‖, ?_⟩
  rintro r ⟨x, hx, rfl⟩
  exact (abs_le.mp (abs_rayleigh_le T (hS x hx))).2

/-- Rayleigh images of unit-vector sets are bounded below. -/
lemma bddBelow_ray (T : H →L[ℂ] H) {S : Set H}
    (hS : ∀ x ∈ S, ‖x‖ = 1) : BddBelow (rayleigh T '' S) := by
  refine ⟨-‖T‖, ?_⟩
  rintro r ⟨x, hx, rfl⟩
  exact (abs_le.mp (abs_rayleigh_le T (hS x hx))).1

/-- The trial maxima are bounded below by `−‖T‖`. -/
lemma neg_norm_le_maxOn (T : H →L[ℂ] H) {V : Submodule ℂ H}
    (hV : TwoDim V) : -‖T‖ ≤ maxOn T V := by
  obtain ⟨x, hxV, hx1⟩ := exists_unit_twoDim hV
  have h1 : rayleigh T x ≤ maxOn T V :=
    le_csSup (bddAbove_ray T fun y hy => hy.2) ⟨x, ⟨hxV, hx1⟩, rfl⟩
  have h2 : -‖T‖ ≤ rayleigh T x :=
    (abs_le.mp (abs_rayleigh_le T hx1)).1
  linarith

/-- The trial minima are bounded above by `‖T‖`. -/
lemma minOn_le_norm (T : H →L[ℂ] H) {V : Submodule ℂ H}
    (hV : TwoDim V) : minOn T V ≤ ‖T‖ := by
  obtain ⟨x, hxV, hx1⟩ := exists_unit_twoDim hV
  have h1 : minOn T V ≤ rayleigh T x :=
    csInf_le (bddBelow_ray T fun y hy => hy.2) ⟨x, ⟨hxV, hx1⟩, rfl⟩
  have h2 : rayleigh T x ≤ ‖T‖ :=
    (abs_le.mp (abs_rayleigh_le T hx1)).2
  linarith

/-- `thm:v002-weyl-barrier`: both Weyl channels bound the affine
barrier by the second level of `L − D`:
`λ₂(L−D) − μ ≥ Γ^W(L,D;g)`.  (Both sides are invariant under real
scalar shifts of `L` and `D`, which cancel from the
eigenvalue–Rayleigh differences.) -/
theorem weyl_barrier (L D : H →L[ℂ] H) (g : H) (_hg : ‖g‖ = 1)
    (hdim : ∃ V : Submodule ℂ H, TwoDim V) :
    weylGap L D g
      ≤ lamTwo (L - D) - (rayleigh L g - rayleigh D g) := by
  obtain ⟨V₀, hV₀⟩ := hdim
  have hne2 : (Set.image (maxOn (L - D))
      {V : Submodule ℂ H | TwoDim V}).Nonempty := ⟨_, ⟨V₀, hV₀, rfl⟩⟩
  -- channel 1: `λ₂(L−D) ≥ ℓ₂(L) − d₁(D)`
  have hch1 : lamTwo L - lamMax D ≤ lamTwo (L - D) := by
    refine le_csInf hne2 ?_
    rintro r ⟨V, hV, rfl⟩
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hneV : (rayleigh L '' unitSet V).Nonempty := by
      obtain ⟨x, hxV, hx1⟩ := exists_unit_twoDim hV
      exact ⟨_, ⟨x, ⟨hxV, hx1⟩, rfl⟩⟩
    have hlt : maxOn L V - ε < maxOn L V := by linarith
    obtain ⟨r', ⟨x, ⟨hxV, hx1⟩, rfl⟩, hr'⟩ :=
      exists_lt_of_lt_csSup hneV hlt
    have hRD : rayleigh D x ≤ lamMax D :=
      le_csSup (bddAbove_ray D fun y hy => hy) ⟨x, hx1, rfl⟩
    have hmax : rayleigh (L - D) x ≤ maxOn (L - D) V :=
      le_csSup (bddAbove_ray (L - D) fun y hy => hy.2)
        ⟨x, ⟨hxV, hx1⟩, rfl⟩
    have hsub := rayleigh_sub L D x
    have hlam : lamTwo L ≤ maxOn L V := by
      refine csInf_le ?_ ⟨V, hV, rfl⟩
      exact ⟨-‖L‖, by rintro s ⟨W, hW, rfl⟩; exact neg_norm_le_maxOn L hW⟩
    linarith
  -- channel 2: `λ₂(L−D) ≥ ℓ₁(L) − d₂(D)`
  have hch2 : lamMin L - lamTwoTop D ≤ lamTwo (L - D) := by
    refine le_csInf hne2 ?_
    rintro r ⟨V, hV, rfl⟩
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hneV : (rayleigh D '' unitSet V).Nonempty := by
      obtain ⟨x, hxV, hx1⟩ := exists_unit_twoDim hV
      exact ⟨_, ⟨x, ⟨hxV, hx1⟩, rfl⟩⟩
    have hlt : minOn D V < minOn D V + ε := by linarith
    obtain ⟨r', ⟨x, ⟨hxV, hx1⟩, rfl⟩, hr'⟩ :=
      exists_lt_of_csInf_lt hneV hlt
    have hRL : lamMin L ≤ rayleigh L x :=
      csInf_le (bddBelow_ray L fun y hy => hy) ⟨x, hx1, rfl⟩
    have hmax : rayleigh (L - D) x ≤ maxOn (L - D) V :=
      le_csSup (bddAbove_ray (L - D) fun y hy => hy.2)
        ⟨x, ⟨hxV, hx1⟩, rfl⟩
    have hsub := rayleigh_sub L D x
    have htop : minOn D V ≤ lamTwoTop D := by
      refine le_csSup ?_ ⟨V, hV, rfl⟩
      exact ⟨‖D‖, by rintro s ⟨W, hW, rfl⟩; exact minOn_le_norm D hW⟩
    linarith
  rw [weylGap]
  refine max_le ?_ ?_ <;> linarith

/-- `thm:v002-scalar-bulk`: if the compressed defect `L − cI − D`
has Rayleigh quotients bounded by `ε` on the physical subspace `W`
(of rank at least two, witnessed by a two-dimensional trial subspace
`V ≤ W`, and carrying the unit vector `g`), then the affine Weyl
barrier is at most `2ε` — a scalar bulk carries no ordering. -/
theorem scalar_bulk (L D : H →L[ℂ] H) (c : ℝ)
    (W V : Submodule ℂ H) (hV : TwoDim V) (hVW : V ≤ W)
    {g : H} (hgW : g ∈ W) (hg : ‖g‖ = 1)
    {ε : ℝ}
    (hdef : ∀ x ∈ W, ‖x‖ = 1 →
      |rayleigh (L - c • (1 : H →L[ℂ] H) - D) x| ≤ ε) :
    weylGap L D g ≤ 2 * ε := by
  -- tested defect in Rayleigh coordinates
  have hkey : ∀ x ∈ W, ‖x‖ = 1 →
      |rayleigh L x - c - rayleigh D x| ≤ ε := by
    intro x hxW hx1
    have h1 := hdef x hxW hx1
    rw [rayleigh_sub, rayleigh_sub, rayleigh_smul_one c hx1] at h1
    exact h1
  -- `ℓ₂(L) ≤ c + d₁(D) + ε`
  have h2 : lamTwo L ≤ c + lamMax D + ε := by
    have hlam : lamTwo L ≤ maxOn L V := by
      refine csInf_le ?_ ⟨V, hV, rfl⟩
      exact ⟨-‖L‖, by rintro s ⟨U, hU, rfl⟩; exact neg_norm_le_maxOn L hU⟩
    have hmaxb : maxOn L V ≤ c + lamMax D + ε := by
      have hneV : (rayleigh L '' unitSet V).Nonempty := by
        obtain ⟨x, hxV, hx1⟩ := exists_unit_twoDim hV
        exact ⟨_, ⟨x, ⟨hxV, hx1⟩, rfl⟩⟩
      refine csSup_le hneV ?_
      rintro r ⟨x, ⟨hxV, hx1⟩, rfl⟩
      have hb := hkey x (hVW hxV) hx1
      have hRD : rayleigh D x ≤ lamMax D :=
        le_csSup (bddAbove_ray D fun y hy => hy) ⟨x, hx1, rfl⟩
      have := (abs_le.mp hb).2
      linarith
    linarith
  -- `ℓ₁(L) ≤ c + d₂(D) + ε`
  have h1 : lamMin L ≤ c + lamTwoTop D + ε := by
    refine le_of_forall_pos_le_add fun ε' hε' => ?_
    have hneV : (rayleigh D '' unitSet V).Nonempty := by
      obtain ⟨x, hxV, hx1⟩ := exists_unit_twoDim hV
      exact ⟨_, ⟨x, ⟨hxV, hx1⟩, rfl⟩⟩
    have hlt : minOn D V < minOn D V + ε' := by linarith
    obtain ⟨r', ⟨x, ⟨hxV, hx1⟩, rfl⟩, hr'⟩ :=
      exists_lt_of_csInf_lt hneV hlt
    have hRL : lamMin L ≤ rayleigh L x :=
      csInf_le (bddBelow_ray L fun y hy => hy) ⟨x, hx1, rfl⟩
    have hb := hkey x (hVW hxV) hx1
    have htop : minOn D V ≤ lamTwoTop D := by
      refine le_csSup ?_ ⟨V, hV, rfl⟩
      exact ⟨‖D‖, by rintro s ⟨U, hU, rfl⟩; exact minOn_le_norm D hU⟩
    have := (abs_le.mp hb).2
    linarith
  -- the Rayleigh centre is `ε`-close to `c + d̄`
  have hm := hkey g hgW hg
  have hm1 := (abs_le.mp hm).1
  have hm2 := (abs_le.mp hm).2
  rw [weylGap]
  refine max_le ?_ ?_ <;> linarith

end NCG
