/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Isotropic direction moments (exact)

Exact formalization of `lem:diamond-iso-moments`: on unit
directions in `n` dimensions with the rotation-invariant
measure,

`⟨uᵘuᵛ⟩ = δᵘᵛ/n`,
`⟨uᵘuᵛuʳuˢ⟩ = (δᵘᵛδʳˢ + δᵘʳδᵛˢ + δᵘˢδᵛʳ)/(n(n+2))`,

and consequently `⟨R_{μν}uᵘuᵛ⟩ = R/n` and
`⟨(R_{μν}uᵘuᵛ)²⟩ = (R² + 2‖Ric‖²)/(n(n+2))`.

The rotation-invariant unit-direction expectation is an
abstract linear functional `E` on functions of the direction
with the data of the uniform sphere measure: invariance under
every linear isometry of the Euclidean quadratic form, and the
unit-norm normalizations `E(‖u‖²) = 1`, `E(‖u‖⁴) = 1`.  Every
boxed identity is **derived**:

* `second_moment_diag` / `second_moment_off`: sign flips kill
  the off-diagonal second moments, permutations equalize the
  diagonal, and the trace normalization fixes `⟨uᵢ²⟩ = 1/n`;
* `fourth_moment_eq`: sign flips kill every odd pattern,
  transpositions equalize `a = ⟨uᵢ⁴⟩` across `i`, the **45°
  rotation** in the `(i,k)` plane gives `⟨uᵢ²uₖ²⟩ = a/3`
  (binomial expansion of `⟨((uᵢ+uₖ)/√2)⁴⟩`), and the norm
  normalization gives `n·a + n(n-1)·a/3 = 1`, hence
  `a = 3/(n(n+2))` and the boxed symmetric-δ formula;
* `ricci_average` / `ricci_square_average`: the curvature
  contractions `⟨R_{uu}⟩ = R/n`,
  `⟨R_{uu}²⟩ = (R² + 2Ric²)/(n(n+2))` for symmetric `Ric`.
-/

open Finset

namespace NCG
namespace Isotropy

variable {n : ℕ}

/-- The direction space. -/
abbrev Dir (n : ℕ) : Type := Fin n → ℝ

/-- Invariance of the direction expectation under every linear
isometry of the Euclidean quadratic form — the defining
symmetry of the uniform sphere measure. -/
def IsoInvariant (E : ((Dir n) → ℝ) →ₗ[ℝ] ℝ) : Prop :=
  ∀ L : Dir n →ₗ[ℝ] Dir n,
    (∀ u, (∑ i, L u i ^ 2) = ∑ i, u i ^ 2) →
    ∀ F : (Dir n) → ℝ, E (fun u => F (L u)) = E F

/-! ### The three isometry families -/

/-- The coordinate sign flip at `m`. -/
def signFlipL (m : Fin n) : Dir n →ₗ[ℝ] Dir n where
  toFun u := fun j => (if j = m then (-1 : ℝ) else 1) * u j
  map_add' u v := by
    funext j
    simp [mul_add]
  map_smul' c u := by
    funext j
    simp [smul_eq_mul]

theorem signFlipL_iso (m : Fin n) :
    ∀ u : Dir n, (∑ i, signFlipL m u i ^ 2) = ∑ i, u i ^ 2 := by
  intro u
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [signFlipL, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases h : i = m <;> simp [h]

/-- The coordinate permutation. -/
def permL (σ : Equiv.Perm (Fin n)) : Dir n →ₗ[ℝ] Dir n where
  toFun u := fun j => u (σ j)
  map_add' u v := by funext j; simp
  map_smul' c u := by funext j; simp

theorem permL_iso (σ : Equiv.Perm (Fin n)) :
    ∀ u : Dir n, (∑ i, permL σ u i ^ 2) = ∑ i, u i ^ 2 := by
  intro u
  simp only [permL, LinearMap.coe_mk, AddHom.coe_mk]
  exact Equiv.sum_comp σ fun i => u i ^ 2

/-- The 45° rotation in the plane `(a, b)`. -/
noncomputable def givensL (a b : Fin n) : Dir n →ₗ[ℝ] Dir n where
  toFun u := fun j =>
    if j = a then (Real.sqrt 2)⁻¹ * (u a + u b)
    else if j = b then (Real.sqrt 2)⁻¹ * (u b - u a)
    else u j
  map_add' u v := by
    funext j
    by_cases h : j = a
    · simp [h]
      ring
    · by_cases h' : j = b
      · have hba : ¬ (b = a) := by rw [← h']; exact h
        simp [h', hba]
        ring
      · simp [h, h']
  map_smul' c u := by
    funext j
    by_cases h : j = a
    · simp [h, smul_eq_mul]
      ring
    · by_cases h' : j = b
      · have hba : ¬ (b = a) := by rw [← h']; exact h
        simp [h', hba, smul_eq_mul]
        ring
      · simp [h, h', smul_eq_mul]

theorem sq_invSqrt2 : ((Real.sqrt 2)⁻¹) ^ 2 = 1 / 2 := by
  rw [← Real.sqrt_inv]
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2⁻¹)]
  norm_num

theorem givensL_iso (a b : Fin n) (hab : a ≠ b) :
    ∀ u : Dir n, (∑ i, givensL a b u i ^ 2) = ∑ i, u i ^ 2 := by
  intro u
  have hmem : ({a, b} : Finset (Fin n)) ⊆ Finset.univ :=
    Finset.subset_univ _
  have hsplit : ∀ f : Fin n → ℝ, (∑ i, f i)
      = f a + f b + ∑ i ∈ Finset.univ \ {a, b}, f i := by
    intro f
    rw [← Finset.sum_sdiff hmem]
    rw [Finset.sum_insert (by simp [hab]),
      Finset.sum_singleton]
    ring
  rw [hsplit (fun i => givensL a b u i ^ 2),
    hsplit (fun i => u i ^ 2)]
  have hrest : ∀ i ∈ Finset.univ \ ({a, b} : Finset (Fin n)),
      givensL a b u i ^ 2 = u i ^ 2 := by
    intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_singleton] at hi
    push Not at hi
    simp only [givensL, LinearMap.coe_mk, AddHom.coe_mk,
      if_neg hi.2.1, if_neg hi.2.2]
  rw [Finset.sum_congr rfl hrest]
  have ha : givensL a b u a
      = (Real.sqrt 2)⁻¹ * (u a + u b) := by
    simp [givensL]
  have hb : givensL a b u b
      = (Real.sqrt 2)⁻¹ * (u b - u a) := by
    simp [givensL, Ne.symm hab]
  rw [ha, hb]
  have hc := sq_invSqrt2
  nlinarith [hc]

/-! ### The moment tensors -/

section Moments

variable (E : ((Dir n) → ℝ) →ₗ[ℝ] ℝ)

/-- Second moments as smul-pull: `E(c·F) = c·E(F)`. -/
theorem E_const_mul (c : ℝ) (F : (Dir n) → ℝ) :
    E (fun u => c * F u) = c * E F := by
  have h : (fun u => c * F u) = c • F := by
    funext u
    simp [smul_eq_mul]
  rw [h, map_smul, smul_eq_mul]

/-- Off-diagonal second moments vanish (sign flip). -/
theorem second_moment_off (hE : IsoInvariant E)
    (i j : Fin n) (hij : i ≠ j) :
    E (fun u => u i * u j) = 0 := by
  have h := hE (signFlipL i) (signFlipL_iso i)
    (fun v => v i * v j)
  have hfun : (fun u : Dir n =>
      signFlipL i u i * signFlipL i u j)
      = fun u => (-1 : ℝ) * (u i * u j) := by
    funext u
    simp only [signFlipL, LinearMap.coe_mk, AddHom.coe_mk,
      if_true, if_neg (Ne.symm hij)]
    ring
  rw [hfun, E_const_mul E] at h
  linarith

/-- Diagonal second moments are equal (transposition). -/
theorem second_moment_diag_eq (hE : IsoInvariant E)
    (i j : Fin n) :
    E (fun u => u i ^ 2) = E (fun u => u j ^ 2) := by
  have h := hE (permL (Equiv.swap i j))
    (permL_iso (Equiv.swap i j)) (fun v => v i ^ 2)
  simp only [permL, LinearMap.coe_mk, AddHom.coe_mk,
    Equiv.swap_apply_left] at h
  exact h.symm

/-- **The boxed second moment**: `⟨uᵢ²⟩ = 1/n`. -/
theorem second_moment_diag (hE : IsoInvariant E)
    (hn2 : E (fun u => ∑ i, u i ^ 2) = 1)
    (hn : 0 < n) (i : Fin n) :
    E (fun u => u i ^ 2) = 1 / n := by
  have hsum : (∑ j, E (fun u => u j ^ 2)) = 1 := by
    rw [← map_sum]
    have h : (∑ j, (fun u : Dir n => u j ^ 2))
        = fun u => ∑ j, u j ^ 2 := by
      funext u
      simp
    rw [h, hn2]
  have hall : ∀ j, E (fun u => u j ^ 2)
      = E (fun u => u i ^ 2) := fun j =>
    second_moment_diag_eq E hE j i
  rw [Finset.sum_congr rfl fun j _ => hall j] at hsum
  simp only [Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  have hnne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp
  linarith

/-! ### Fourth moments -/

/-- A lone first index kills the fourth moment (sign flip). -/
theorem fourth_lone (hE : IsoInvariant E) (i j k l : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) :
    E (fun u => u i * u j * u k * u l) = 0 := by
  have h := hE (signFlipL i) (signFlipL_iso i)
    (fun v => v i * v j * v k * v l)
  have hfun : (fun u : Dir n => signFlipL i u i
      * signFlipL i u j * signFlipL i u k * signFlipL i u l)
      = fun u => (-1 : ℝ) * (u i * u j * u k * u l) := by
    funext u
    simp only [signFlipL, LinearMap.coe_mk, AddHom.coe_mk,
      if_true, if_neg (Ne.symm hij), if_neg (Ne.symm hik),
      if_neg (Ne.symm hil)]
    ring
  rw [hfun, E_const_mul E] at h
  linarith

/-- Diagonal fourth moments are equal (transposition). -/
theorem fourth_diag_eq (hE : IsoInvariant E) (i j : Fin n) :
    E (fun u => u i * u i * u i * u i)
      = E (fun u => u j * u j * u j * u j) := by
  have h := hE (permL (Equiv.swap i j))
    (permL_iso (Equiv.swap i j))
    (fun v => v i * v i * v i * v i)
  simp only [permL, LinearMap.coe_mk, AddHom.coe_mk,
    Equiv.swap_apply_left] at h
  exact h.symm

/-- **The 45° rotation relation**: `⟨uᵢ²uₖ²⟩ = ⟨uᵢ⁴⟩/3`. -/
theorem fourth_cross (hE : IsoInvariant E) (i k : Fin n)
    (hik : i ≠ k) :
    E (fun u => u i * u i * u k * u k)
      = E (fun u => u i * u i * u i * u i) / 3 := by
  have h := hE (givensL i k) (givensL_iso i k hik)
    (fun v => v i * v i * v i * v i)
  have hc2 := sq_invSqrt2
  have hfun : (fun u : Dir n => givensL i k u i
      * givensL i k u i * givensL i k u i * givensL i k u i)
      = (1/4 : ℝ) • (fun u : Dir n => u i * u i * u i * u i)
        + ((1 : ℝ) • (fun u : Dir n => u k * u i * u i * u i)
        + ((3/2 : ℝ) • (fun u : Dir n => u i * u i * u k * u k)
        + ((1 : ℝ) • (fun u : Dir n => u k * u k * u k * u i)
        + (1/4 : ℝ) • (fun u : Dir n =>
            u k * u k * u k * u k)))) := by
    funext u
    simp only [givensL, LinearMap.coe_mk, AddHom.coe_mk,
      if_true, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination
      ((((Real.sqrt 2)⁻¹) ^ 2 + 1/2)
        * (u i + u k) ^ 4) * hc2
  rw [hfun] at h
  simp only [map_add, map_smul, smul_eq_mul] at h
  have hlone1 : E (fun u : Dir n => u k * u i * u i * u i)
      = 0 :=
    fourth_lone E hE k i i i (Ne.symm hik) (Ne.symm hik)
      (Ne.symm hik)
  have hlone2 : E (fun u : Dir n => u k * u k * u k * u i)
      = 0 := by
    have hre : (fun u : Dir n => u k * u k * u k * u i)
        = fun u => u i * u k * u k * u k := by
      funext u
      ring
    rw [hre]
    exact fourth_lone E hE i k k k hik hik hik
  have hdiag := fourth_diag_eq E hE k i
  rw [hlone1, hlone2, hdiag] at h
  linarith

/-- **The diagonal fourth-moment value**:
`⟨uᵢ⁴⟩ = 3/(n(n+2))`. -/
theorem fourth_diag_value (hE : IsoInvariant E)
    (hn4 : E (fun u => (∑ i, u i ^ 2) ^ 2) = 1)
    (hn : 0 < n) (i : Fin n) :
    E (fun u => u i * u i * u i * u i)
      = 3 / (n * (n + 2)) := by
  set a : ℝ := E (fun u => u i * u i * u i * u i) with ha
  -- expand the norm-square normalization into fourth moments
  have hexp : (fun u : Dir n => (∑ i, u i ^ 2) ^ 2)
      = ∑ j, ∑ k, (fun u : Dir n => u j * u j * u k * u k) := by
    funext u
    rw [Finset.sum_apply]
    have hinner : ∀ j, (∑ k, (fun u : Dir n =>
        u j * u j * u k * u k)) u
        = u j ^ 2 * ∑ k, u k ^ 2 := by
      intro j
      rw [Finset.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [Finset.sum_congr rfl fun j _ => hinner j]
    rw [← Finset.sum_mul]
    ring
  have hsum : (∑ j, ∑ k,
      E (fun u : Dir n => u j * u j * u k * u k)) = 1 := by
    rw [← hn4, hexp]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_sum]
  -- each inner sum is `a + (n-1)·a/3`
  have hinner : ∀ j, (∑ k,
      E (fun u : Dir n => u j * u j * u k * u k))
      = a + (n - 1) * (a / 3) := by
    intro j
    have haj : E (fun u : Dir n => u j * u j * u j * u j)
        = a := by
      rw [ha]
      exact fourth_diag_eq E hE j i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    rw [haj]
    have hoffdiag : ∀ k ∈ Finset.univ.erase j,
        E (fun u : Dir n => u j * u j * u k * u k)
        = a / 3 := by
      intro k hk
      have hkj : k ≠ j := Finset.ne_of_mem_erase hk
      rw [fourth_cross E hE j k (Ne.symm hkj), haj]
    rw [Finset.sum_congr rfl hoffdiag]
    rw [Finset.sum_const, Finset.card_erase_of_mem
      (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn]
      simp
    rw [hcast]
  rw [Finset.sum_congr rfl fun j _ => hinner j] at hsum
  simp only [Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  have hnne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hkey : a * ((n : ℝ) * ((n : ℝ) + 2)) = 3 := by
    nlinarith
  have hden : (n : ℝ) * ((n : ℝ) + 2) ≠ 0 := by positivity
  field_simp
  linarith [hkey]

/-- **The boxed fourth moment**:
`⟨uᵢuⱼuₖuₗ⟩ = (δᵢⱼδₖₗ + δᵢₖδⱼₗ + δᵢₗδⱼₖ)/(n(n+2))`. -/
theorem fourth_moment_eq (hE : IsoInvariant E)
    (hn4 : E (fun u => (∑ i, u i ^ 2) ^ 2) = 1)
    (hn : 0 < n) (i j k l : Fin n) :
    E (fun u => u i * u j * u k * u l)
    = ((if i = j then (1:ℝ) else 0) * (if k = l then 1 else 0)
      + (if i = k then (1:ℝ) else 0) * (if j = l then 1 else 0)
      + (if i = l then (1:ℝ) else 0) * (if j = k then 1 else 0))
      / (n * (n + 2)) := by
  have hb : ∀ p q : Fin n, p ≠ q →
      E (fun u => u p * u p * u q * u q)
        = 1 / (n * (n + 2)) := by
    intro p q hpq
    rw [fourth_cross E hE p q hpq,
      fourth_diag_value E hE hn4 hn p]
    ring
  have hden : (n : ℝ) * ((n : ℝ) + 2) ≠ 0 := by
    have hnne : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    positivity
  by_cases h1 : i = j
  · subst h1
    by_cases h2 : k = l
    · subst h2
      by_cases h3 : i = k
      · subst h3
        rw [fourth_diag_value E hE hn4 hn i]
        norm_num
      · rw [hb i k h3]
        simp [h3]
    · -- `k ≠ l`: a lone index exists among `k, l`
      by_cases h3 : l = i
      · subst h3
        have hre : (fun u : Dir n => u l * u l * u k * u l)
            = fun u => u k * u l * u l * u l := by
          funext u
          ring
        rw [hre, fourth_lone E hE k l l l
          (fun h => h2 h) (fun h => h2 h) (fun h => h2 h)]
        have hkl : ¬ (l = k) := fun h => h2 h.symm
        simp [h2, hkl]
      · have hre : (fun u : Dir n => u i * u i * u k * u l)
            = fun u => u l * u i * u i * u k := by
          funext u
          ring
        rw [hre, fourth_lone E hE l i i k
          (fun h => h3 h) (fun h => h3 h)
          (fun h => h2 h.symm)]
        have hli : ¬ (i = l) := fun h => h3 h.symm
        have hlk : ¬ (k = l) := h2
        simp [h2, hli]
  · by_cases h2 : k = l
    · subst h2
      -- mirror: reorder to put the pair first
      by_cases h3 : i = k
      · subst h3
        have hre : (fun u : Dir n => u i * u j * u i * u i)
            = fun u => u j * u i * u i * u i := by
          funext u
          ring
        rw [hre, fourth_lone E hE j i i i
          (fun h => h1 h.symm) (fun h => h1 h.symm)
          (fun h => h1 h.symm)]
        have hji : ¬ (j = i) := fun h => h1 h.symm
        simp [h1, hji]
      · by_cases h4 : j = k
        · subst h4
          have hre : (fun u : Dir n => u i * u j * u j * u j)
              = fun u => u i * u j * u j * u j := rfl
          rw [fourth_lone E hE i j j j h1 h1 h1]
          simp [h1]
        · have hre : (fun u : Dir n => u i * u j * u k * u k)
              = fun u => u i * u j * u k * u k := rfl
          have hre2 : (fun u : Dir n => u i * u j * u k * u k)
              = fun u => u j * u i * u k * u k := by
            funext u
            ring
          rw [hre2, fourth_lone E hE j i k k
            (fun h => h1 h.symm) h4 h4]
          simp [h1, h3, h4]
    · -- `i ≠ j`, `k ≠ l`
      by_cases h3 : i = k
      · subst h3
        by_cases h4 : j = l
        · subst h4
          have hre : (fun u : Dir n => u i * u j * u i * u j)
              = fun u => u i * u i * u j * u j := by
            funext u
            ring
          rw [hre, hb i j h1]
          have hji : ¬ (j = i) := fun h => h1 h.symm
          simp [h1, hji]
        · -- `j` is lone
          have hre : (fun u : Dir n => u i * u j * u i * u l)
              = fun u => u j * u i * u i * u l := by
            funext u
            ring
          rw [hre, fourth_lone E hE j i i l
            (fun h => h1 h.symm) (fun h => h1 h.symm) h4]
          simp [h1, h2, h4]
      · by_cases h4 : i = l
        · subst h4
          by_cases h5 : j = k
          · subst h5
            have hre : (fun u : Dir n => u i * u j * u j * u i)
                = fun u => u i * u i * u j * u j := by
              funext u
              ring
            rw [hre, hb i j h1]
            have hji : ¬ (j = i) := fun h => h1 h.symm
            simp [h1, hji]
          · -- `j` is lone
            have hre : (fun u : Dir n => u i * u j * u k * u i)
                = fun u => u j * u i * u k * u i := by
              funext u
              ring
            rw [hre, fourth_lone E hE j i k i
              (fun h => h1 h.symm) h5 (fun h => h1 h.symm)]
            simp [h1, h3, h5]
        · -- `i` is lone
          rw [fourth_lone E hE i j k l h1 h3 h4]
          simp [h1, h3, h4]

end Moments

/-! ### Curvature consequences -/

section Curvature

variable (E : ((Dir n) → ℝ) →ₗ[ℝ] ℝ)

/-- **The boxed Ricci average**: `⟨R_{μν}uᵘuᵛ⟩ = R/n` for the
scalar curvature `R = tr Ric`. -/
theorem ricci_average (hE : IsoInvariant E)
    (hn2 : E (fun u => ∑ i, u i ^ 2) = 1) (hn : 0 < n)
    (Ric : Matrix (Fin n) (Fin n) ℝ) :
    E (fun u => ∑ μ, ∑ ν, Ric μ ν * (u μ * u ν))
      = Matrix.trace Ric / n := by
  have hsplit : (fun u : Dir n =>
      ∑ μ, ∑ ν, Ric μ ν * (u μ * u ν))
      = ∑ μ, ∑ ν, Ric μ ν • (fun u : Dir n => u μ * u ν) := by
    funext u
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun ν _ => ?_
    simp [smul_eq_mul]
  rw [hsplit, map_sum]
  have hpush : ∀ μ, E (∑ ν, Ric μ ν
      • (fun u : Dir n => u μ * u ν))
      = ∑ ν, E (Ric μ ν • (fun u : Dir n => u μ * u ν)) :=
    fun μ => map_sum E _ _
  rw [Finset.sum_congr rfl fun μ _ => hpush μ]
  have hterm : ∀ μ, (∑ ν, E (Ric μ ν
      • (fun u : Dir n => u μ * u ν)))
      = Ric μ μ * (1 / n) := by
    intro μ
    have hval : ∀ ν, E (Ric μ ν
        • (fun u : Dir n => u μ * u ν))
        = Ric μ ν * (if μ = ν then 1 / (n:ℝ) else 0) := by
      intro ν
      rw [map_smul, smul_eq_mul]
      by_cases h : μ = ν
      · subst h
        have hsq : (fun u : Dir n => u μ * u μ)
            = fun u => u μ ^ 2 := by
          funext u
          ring
        rw [hsq, second_moment_diag E hE hn2 hn μ]
        simp
      · rw [second_moment_off E hE μ ν h]
        simp [h]
    rw [Finset.sum_congr rfl fun ν _ => hval ν]
    rw [Finset.sum_eq_single μ]
    · simp
    · intro ν _ hν
      simp [Ne.symm hν]
    · intro h
      exact absurd (Finset.mem_univ μ) h
  rw [Finset.sum_congr rfl fun μ _ => hterm μ]
  rw [← Finset.sum_mul, Matrix.trace]
  simp [Matrix.diag]
  ring

/-- **The boxed Ricci-square average**:
`⟨(R_{μν}uᵘuᵛ)²⟩ = (R² + 2·Ric²)/(n(n+2))` for symmetric
`Ric`. -/
theorem ricci_square_average (hE : IsoInvariant E)
    (hn4 : E (fun u => (∑ i, u i ^ 2) ^ 2) = 1) (hn : 0 < n)
    (Ric : Matrix (Fin n) (Fin n) ℝ)
    (hsymm : Ric.transpose = Ric) :
    E (fun u => (∑ μ, ∑ ν, Ric μ ν * (u μ * u ν)) ^ 2)
      = (Matrix.trace Ric ^ 2
          + 2 * ∑ μ, ∑ ν, Ric μ ν ^ 2)
        / (n * (n + 2)) := by
  have hsym : ∀ μ ν, Ric ν μ = Ric μ ν := by
    intro μ ν
    have := congrFun (congrFun hsymm μ) ν
    simpa [Matrix.transpose_apply] using this
  have htrace : Matrix.trace Ric = ∑ ρ, Ric ρ ρ := by
    rw [Matrix.trace]
    simp [Matrix.diag]
  -- expand the square into fourth moments
  have hsq : (fun u : Dir n =>
      (∑ μ, ∑ ν, Ric μ ν * (u μ * u ν)) ^ 2)
      = ∑ μ, ∑ ν, ∑ ρ, ∑ σ, (Ric μ ν * Ric ρ σ)
          • (fun u : Dir n => u μ * u ν * u ρ * u σ) := by
    funext u
    have hexpand : (∑ μ, ∑ ν, Ric μ ν * (u μ * u ν)) ^ 2
        = ∑ μ, ∑ ν, ∑ ρ, ∑ σ,
            Ric μ ν * Ric ρ σ * (u μ * u ν * u ρ * u σ) := by
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun μ _ => ?_
      have hstep : ∀ ρ : Fin n,
          (∑ ν, Ric μ ν * (u μ * u ν))
            * (∑ σ, Ric ρ σ * (u ρ * u σ))
          = ∑ ν, ∑ σ, Ric μ ν * Ric ρ σ
              * (u μ * u ν * u ρ * u σ) := by
        intro ρ
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun ν _ => ?_
        refine Finset.sum_congr rfl fun σ _ => ?_
        ring
      rw [Finset.sum_congr rfl fun ρ _ => hstep ρ]
      exact Finset.sum_comm
        (f := fun ρ ν => ∑ σ, Ric μ ν * Ric ρ σ
          * (u μ * u ν * u ρ * u σ))
    rw [hexpand]
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp [smul_eq_mul]
  rw [hsq]
  rw [map_sum]
  have hpush : ∀ μ, E (∑ ν, ∑ ρ, ∑ σ, (Ric μ ν * Ric ρ σ)
      • (fun u : Dir n => u μ * u ν * u ρ * u σ))
      = ∑ ν, ∑ ρ, ∑ σ, (Ric μ ν * Ric ρ σ)
          * E (fun u : Dir n => u μ * u ν * u ρ * u σ) := by
    intro μ
    rw [map_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [map_smul, smul_eq_mul]
  rw [Finset.sum_congr rfl fun μ _ => hpush μ]
  -- substitute the boxed fourth moment
  have hsub : ∀ μ ν ρ σ : Fin n,
      (Ric μ ν * Ric ρ σ)
        * E (fun u : Dir n => u μ * u ν * u ρ * u σ)
      = (Ric μ ν * Ric ρ σ)
        * (((if μ = ν then (1:ℝ) else 0)
              * (if ρ = σ then 1 else 0)
            + (if μ = ρ then (1:ℝ) else 0)
              * (if ν = σ then 1 else 0)
            + (if μ = σ then (1:ℝ) else 0)
              * (if ν = ρ then 1 else 0))
          / (n * (n + 2))) := by
    intro μ ν ρ σ
    rw [fourth_moment_eq E hE hn4 hn μ ν ρ σ]
  -- three δ-contractions
  have hδ : ∀ f : Fin n → Fin n → ℝ, ∀ ν : Fin n,
      (∑ σ, f ν σ * (if ν = σ then (1:ℝ) else 0))
      = f ν ν := by
    intro f ν
    rw [Finset.sum_eq_single ν]
    · simp
    · intro σ _ hσ
      simp [Ne.symm hσ]
    · intro h
      exact absurd (Finset.mem_univ ν) h
  -- assemble by expanding the product with the three δ-terms
  have hkey : (∑ μ, ∑ ν, ∑ ρ, ∑ σ, (Ric μ ν * Ric ρ σ)
      * (((if μ = ν then (1:ℝ) else 0)
            * (if ρ = σ then 1 else 0)
          + (if μ = ρ then (1:ℝ) else 0)
            * (if ν = σ then 1 else 0)
          + (if μ = σ then (1:ℝ) else 0)
            * (if ν = ρ then 1 else 0))
        / (n * (n + 2))))
      = (Matrix.trace Ric ^ 2
          + 2 * ∑ μ, ∑ ν, Ric μ ν ^ 2)
        / (n * (n + 2)) := by
    have hsplit : ∀ μ ν ρ σ : Fin n, (Ric μ ν * Ric ρ σ)
        * (((if μ = ν then (1:ℝ) else 0)
              * (if ρ = σ then 1 else 0)
            + (if μ = ρ then (1:ℝ) else 0)
              * (if ν = σ then 1 else 0)
            + (if μ = σ then (1:ℝ) else 0)
              * (if ν = ρ then 1 else 0))
          / (n * (n + 2)))
        = ((Ric μ ν * Ric ρ σ * ((if μ = ν then (1:ℝ) else 0)
              * (if ρ = σ then 1 else 0)))
          + (Ric μ ν * Ric ρ σ * ((if μ = ρ then (1:ℝ) else 0)
              * (if ν = σ then 1 else 0)))
          + (Ric μ ν * Ric ρ σ * ((if μ = σ then (1:ℝ) else 0)
              * (if ν = ρ then 1 else 0))))
          / (n * (n + 2)) := by
      intro μ ν ρ σ
      ring
    simp_rw [hsplit]
    -- term 1: `(tr Ric)²`
    have ht1 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ,
        Ric μ ν * Ric ρ σ * ((if μ = ν then (1:ℝ) else 0)
          * (if ρ = σ then 1 else 0)))
        = Matrix.trace Ric ^ 2 := by
      have hinner : ∀ μ ν : Fin n, (∑ ρ, ∑ σ,
          Ric μ ν * Ric ρ σ * ((if μ = ν then (1:ℝ) else 0)
            * (if ρ = σ then 1 else 0)))
          = Ric μ ν * (if μ = ν then (1:ℝ) else 0)
            * Matrix.trace Ric := by
        intro μ ν
        have h : ∀ ρ, (∑ σ, Ric μ ν * Ric ρ σ
            * ((if μ = ν then (1:ℝ) else 0)
              * (if ρ = σ then 1 else 0)))
            = Ric μ ν * (if μ = ν then (1:ℝ) else 0)
              * Ric ρ ρ := by
          intro ρ
          have := hδ (fun ρ σ => Ric μ ν * Ric ρ σ
            * (if μ = ν then (1:ℝ) else 0)) ρ
          calc (∑ σ, Ric μ ν * Ric ρ σ
              * ((if μ = ν then (1:ℝ) else 0)
                * (if ρ = σ then 1 else 0)))
              = ∑ σ, (Ric μ ν * Ric ρ σ
                * (if μ = ν then (1:ℝ) else 0))
                * (if ρ = σ then 1 else 0) := by
                refine Finset.sum_congr rfl fun σ _ => ?_
                ring
            _ = Ric μ ν * Ric ρ ρ
                * (if μ = ν then (1:ℝ) else 0) := this
            _ = Ric μ ν * (if μ = ν then (1:ℝ) else 0)
                * Ric ρ ρ := by ring
        rw [Finset.sum_congr rfl fun ρ _ => h ρ]
        rw [← Finset.mul_sum, ← htrace]
      rw [Finset.sum_congr rfl fun μ _ =>
        Finset.sum_congr rfl fun ν _ => hinner μ ν]
      have houter : ∀ μ : Fin n, (∑ ν, Ric μ ν
          * (if μ = ν then (1:ℝ) else 0) * Matrix.trace Ric)
          = Ric μ μ * Matrix.trace Ric := by
        intro μ
        have := hδ (fun μ ν => Ric μ ν * Matrix.trace Ric) μ
        calc (∑ ν, Ric μ ν * (if μ = ν then (1:ℝ) else 0)
            * Matrix.trace Ric)
            = ∑ ν, (Ric μ ν * Matrix.trace Ric)
              * (if μ = ν then (1:ℝ) else 0) := by
              refine Finset.sum_congr rfl fun ν _ => ?_
              ring
          _ = Ric μ μ * Matrix.trace Ric := this
      rw [Finset.sum_congr rfl fun μ _ => houter μ]
      rw [← Finset.sum_mul, ← htrace]
      ring
    -- terms 2 and 3: `∑ Ric²` each (symmetry for term 3)
    have ht2 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ,
        Ric μ ν * Ric ρ σ * ((if μ = ρ then (1:ℝ) else 0)
          * (if ν = σ then 1 else 0)))
        = ∑ μ, ∑ ν, Ric μ ν ^ 2 := by
      refine Finset.sum_congr rfl fun μ _ => ?_
      refine Finset.sum_congr rfl fun ν _ => ?_
      have h : ∀ ρ, (∑ σ, Ric μ ν * Ric ρ σ
          * ((if μ = ρ then (1:ℝ) else 0)
            * (if ν = σ then 1 else 0)))
          = (Ric μ ν * Ric ρ ν
            * (if μ = ρ then (1:ℝ) else 0)) := by
        intro ρ
        have := hδ (fun ν σ => Ric μ ν * Ric ρ σ
          * (if μ = ρ then (1:ℝ) else 0)) ν
        calc (∑ σ, Ric μ ν * Ric ρ σ
            * ((if μ = ρ then (1:ℝ) else 0)
              * (if ν = σ then 1 else 0)))
            = ∑ σ, (Ric μ ν * Ric ρ σ
              * (if μ = ρ then (1:ℝ) else 0))
              * (if ν = σ then 1 else 0) := by
              refine Finset.sum_congr rfl fun σ _ => ?_
              ring
          _ = Ric μ ν * Ric ρ ν
              * (if μ = ρ then (1:ℝ) else 0) := this
      rw [Finset.sum_congr rfl fun ρ _ => h ρ]
      have := hδ (fun μ ρ => Ric μ ν * Ric ρ ν) μ
      calc (∑ ρ, Ric μ ν * Ric ρ ν
          * (if μ = ρ then (1:ℝ) else 0))
          = ∑ ρ, (Ric μ ν * Ric ρ ν)
            * (if μ = ρ then (1:ℝ) else 0) := by
            refine Finset.sum_congr rfl fun ρ _ => ?_
            ring
        _ = Ric μ ν * Ric μ ν := this
        _ = Ric μ ν ^ 2 := by ring
    have ht3 : (∑ μ, ∑ ν, ∑ ρ, ∑ σ,
        Ric μ ν * Ric ρ σ * ((if μ = σ then (1:ℝ) else 0)
          * (if ν = ρ then 1 else 0)))
        = ∑ μ, ∑ ν, Ric μ ν ^ 2 := by
      refine Finset.sum_congr rfl fun μ _ => ?_
      refine Finset.sum_congr rfl fun ν _ => ?_
      have h : ∀ ρ, (∑ σ, Ric μ ν * Ric ρ σ
          * ((if μ = σ then (1:ℝ) else 0)
            * (if ν = ρ then 1 else 0)))
          = (Ric μ ν * Ric ρ μ
            * (if ν = ρ then (1:ℝ) else 0)) := by
        intro ρ
        have := hδ (fun μ σ => Ric μ ν * Ric ρ σ
          * (if ν = ρ then (1:ℝ) else 0)) μ
        calc (∑ σ, Ric μ ν * Ric ρ σ
            * ((if μ = σ then (1:ℝ) else 0)
              * (if ν = ρ then 1 else 0)))
            = ∑ σ, (Ric μ ν * Ric ρ σ
              * (if ν = ρ then (1:ℝ) else 0))
              * (if μ = σ then 1 else 0) := by
              refine Finset.sum_congr rfl fun σ _ => ?_
              ring
          _ = Ric μ ν * Ric ρ μ
              * (if ν = ρ then (1:ℝ) else 0) := this
      rw [Finset.sum_congr rfl fun ρ _ => h ρ]
      have := hδ (fun ν ρ => Ric μ ν * Ric ρ μ) ν
      calc (∑ ρ, Ric μ ν * Ric ρ μ
          * (if ν = ρ then (1:ℝ) else 0))
          = ∑ ρ, (Ric μ ν * Ric ρ μ)
            * (if ν = ρ then (1:ℝ) else 0) := by
            refine Finset.sum_congr rfl fun ρ _ => ?_
            ring
        _ = Ric μ ν * Ric ν μ := this
        _ = Ric μ ν ^ 2 := by
            rw [hsym μ ν]
            ring
    -- combine
    have hfinal : (∑ μ, ∑ ν, ∑ ρ, ∑ σ,
        ((Ric μ ν * Ric ρ σ * ((if μ = ν then (1:ℝ) else 0)
            * (if ρ = σ then 1 else 0)))
          + (Ric μ ν * Ric ρ σ * ((if μ = ρ then (1:ℝ) else 0)
              * (if ν = σ then 1 else 0)))
          + (Ric μ ν * Ric ρ σ * ((if μ = σ then (1:ℝ) else 0)
              * (if ν = ρ then 1 else 0)))))
        = Matrix.trace Ric ^ 2
          + 2 * ∑ μ, ∑ ν, Ric μ ν ^ 2 := by
      simp_rw [Finset.sum_add_distrib]
      rw [ht1, ht2, ht3]
      ring
    simp_rw [← Finset.sum_div]
    rw [hfinal]
  simp_rw [hsub]
  exact hkey

end Curvature

end Isotropy
end NCG
