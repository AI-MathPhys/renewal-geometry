/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Orbit-orthogonal bracket concentration
  (`lem:renewal-orbit-bracket`)

A concrete finite spin model over an arbitrary finite abelian
site group `G` (instantiated to the `N³` torus below): spins
`ε_x(ω) = ±1` under the uniform product state, Walsh monomials
`w_S = ∏_{x∈S} ε_x`, and the translation average
`Av f = |G|⁻¹ ∑_x τ_x f`.

This file proves, exactly:

* `expect_walsh_mul_walsh`: Walsh orthonormality under the
  product state (by an explicit spin-flip involution);
* `expect_poly_sq` (Parseval): `E[f²] = ∑_S f̂(S)²`;
* `orbit_variance_bound` (**the boxed estimate**): for a
  centered rooted Walsh polynomial of degree at most `R`,
  `Var(Av f) ≤ (R/|G|)·‖f‖₂²` — the rooted support meets each
  translation orbit in at most `R` translates, so
  Cauchy–Schwarz on each averaged coefficient loses only `R`;
* `orbit_variance_bound_cube`: the `N³`-site statement with
  `|G| = N³`;
* `time_integral_sq_bound`: the stationary-interval clause —
  a time integral over `[0,T]` of a family with the uniform
  variance bound obeys the same estimate multiplied by `T²`.
-/

open Finset

namespace NCG
namespace RenewalOrbitBracket

variable {G : Type} [AddCommGroup G] [Fintype G]
  [DecidableEq G]

/-! ### The spin model -/

/-- The site spin `ε_x(ω) = ±1`. -/
def eps (x : G) (ω : G → Bool) : ℝ :=
  if ω x then 1 else -1

omit [AddCommGroup G] [Fintype G] [DecidableEq G] in
theorem eps_mul_self (x : G) (ω : G → Bool) :
    eps x ω * eps x ω = 1 := by
  unfold eps
  split <;> norm_num

/-- The Walsh monomial `w_S = ∏_{x∈S} ε_x`. -/
def walsh (S : Finset G) (ω : G → Bool) : ℝ :=
  ∏ x ∈ S, eps x ω

/-- The uniform product-state expectation. -/
noncomputable def expect (g : (G → Bool) → ℝ) : ℝ :=
  (Fintype.card (G → Bool) : ℝ)⁻¹ * ∑ ω : G → Bool, g ω

omit [AddCommGroup G] in
theorem expect_finset_sum {ι : Type} (s : Finset ι)
    (F : ι → (G → Bool) → ℝ) :
    expect (fun ω => ∑ i ∈ s, F i ω)
      = ∑ i ∈ s, expect (F i) := by
  unfold expect
  rw [Finset.sum_comm, Finset.mul_sum]

omit [AddCommGroup G] in
theorem expect_const_mul (a : ℝ) (g : (G → Bool) → ℝ) :
    expect (fun ω => a * g ω) = a * expect g := by
  unfold expect
  rw [← Finset.mul_sum]
  ring

/-! ### Walsh orthonormality -/

omit [AddCommGroup G] [Fintype G] in
theorem walsh_mul (S T : Finset G) (ω : G → Bool) :
    walsh S ω * walsh T ω = walsh (symmDiff S T) ω := by
  unfold walsh
  have h1 : (∏ x ∈ S, eps x ω)
      = (∏ x ∈ S \ T, eps x ω)
        * ∏ x ∈ S ∩ T, eps x ω := by
    rw [← Finset.prod_union
      (Finset.disjoint_sdiff_inter S T),
      Finset.sdiff_union_inter]
  have h2 : (∏ x ∈ T, eps x ω)
      = (∏ x ∈ T \ S, eps x ω)
        * ∏ x ∈ S ∩ T, eps x ω := by
    rw [Finset.inter_comm, ← Finset.prod_union
      (Finset.disjoint_sdiff_inter T S),
      Finset.sdiff_union_inter]
  have h3 : (∏ x ∈ symmDiff S T, eps x ω)
      = (∏ x ∈ S \ T, eps x ω)
        * ∏ x ∈ T \ S, eps x ω := by
    have hsymm : symmDiff S T = (S \ T) ∪ (T \ S) := by
      rw [Finset.symmDiff_def]
    rw [hsymm, Finset.prod_union disjoint_sdiff_sdiff]
  have hsq : (∏ x ∈ S ∩ T, eps x ω)
      * ∏ x ∈ S ∩ T, eps x ω = 1 := by
    rw [← Finset.prod_mul_distrib,
      Finset.prod_congr rfl fun x _ => eps_mul_self x ω]
    exact Finset.prod_const_one
  rw [h1, h2, h3]
  calc (∏ x ∈ S \ T, eps x ω) * (∏ x ∈ S ∩ T, eps x ω)
      * ((∏ x ∈ T \ S, eps x ω)
        * ∏ x ∈ S ∩ T, eps x ω)
      = (∏ x ∈ S \ T, eps x ω) * (∏ x ∈ T \ S, eps x ω)
        * ((∏ x ∈ S ∩ T, eps x ω)
          * ∏ x ∈ S ∩ T, eps x ω) := by ring
    _ = (∏ x ∈ S \ T, eps x ω)
        * ∏ x ∈ T \ S, eps x ω := by rw [hsq, mul_one]

omit [AddCommGroup G] in
theorem expect_walsh_empty :
    expect (walsh (∅ : Finset G)) = 1 := by
  unfold expect walsh
  simp only [Finset.prod_empty, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [inv_mul_cancel₀]
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

omit [AddCommGroup G] in
theorem expect_walsh_of_ne_empty {U : Finset G}
    (hU : U ≠ ∅) : expect (walsh U) = 0 := by
  obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hU
  have hsum : ∑ ω : G → Bool, walsh U ω = 0 := by
    refine Finset.sum_involution
      (fun ω _ => Function.update ω u (! ω u)) ?_ ?_ ?_ ?_
    · intro ω _
      have hflip : walsh U (Function.update ω u (! ω u))
          = - walsh U ω := by
        unfold walsh
        rw [← Finset.mul_prod_erase _ _ hu,
          ← Finset.mul_prod_erase _ _ hu]
        have h1 : eps u (Function.update ω u (! ω u))
            = - eps u ω := by
          unfold eps
          rw [Function.update_self]
          cases h : ω u <;> simp
        have h2 : ∀ x ∈ U.erase u,
            eps x (Function.update ω u (! ω u))
            = eps x ω := by
          intro x hx
          have hxu := Finset.ne_of_mem_erase hx
          unfold eps
          rw [Function.update_of_ne hxu]
        rw [h1, Finset.prod_congr rfl h2]
        ring
      rw [hflip]
      ring
    · intro ω _ hω hcon
      have h := congrFun hcon u
      rw [Function.update_self] at h
      exact (Bool.not_ne_self (ω u)) h
    · intro ω _
      exact Finset.mem_univ _
    · intro ω _
      funext y
      by_cases hy : y = u
      · subst hy
        simp [Function.update_self]
      · rw [Function.update_of_ne hy,
          Function.update_of_ne hy]
  unfold expect
  rw [hsum, mul_zero]

omit [AddCommGroup G] in
/-- **Walsh orthonormality** under the product state. -/
theorem expect_walsh_mul_walsh (S T : Finset G) :
    expect (fun ω => walsh S ω * walsh T ω)
      = if S = T then 1 else 0 := by
  have h : expect (fun ω => walsh S ω * walsh T ω)
      = expect (walsh (symmDiff S T)) := by
    unfold expect
    congr 1
    exact Finset.sum_congr rfl fun ω _ => walsh_mul S T ω
  rw [h]
  by_cases hST : S = T
  · subst hST
    rw [if_pos rfl, symmDiff_self]
    exact expect_walsh_empty
  · rw [if_neg hST]
    exact expect_walsh_of_ne_empty
      (fun hcon => hST (Finset.symmDiff_eq_empty.mp hcon))

/-! ### Walsh polynomials and Parseval -/

/-- The Walsh polynomial with coefficients `c`. -/
def poly (c : Finset G → ℝ) : (G → Bool) → ℝ :=
  fun ω => ∑ S : Finset G, c S * walsh S ω

omit [AddCommGroup G] in
theorem expect_poly (c : Finset G → ℝ) :
    expect (poly c) = c ∅ := by
  unfold poly
  rw [expect_finset_sum]
  have h : ∀ S : Finset G,
      expect (fun ω => c S * walsh S ω)
      = c S * (if S = ∅ then 1 else 0) := by
    intro S
    rw [expect_const_mul]
    by_cases hS : S = ∅
    · subst hS
      rw [if_pos rfl, expect_walsh_empty]
    · rw [if_neg hS, expect_walsh_of_ne_empty hS]
  rw [Finset.sum_congr rfl fun S _ => h S]
  simp

omit [AddCommGroup G] in
/-- **Parseval**: `E[f²] = ∑_S f̂(S)²`. -/
theorem expect_poly_sq (c : Finset G → ℝ) :
    expect (fun ω => poly c ω ^ 2)
      = ∑ S : Finset G, c S ^ 2 := by
  have hexp : ∀ ω : G → Bool, poly c ω ^ 2
      = ∑ S : Finset G, ∑ T : Finset G,
          c S * c T * (walsh S ω * walsh T ω) := by
    intro ω
    rw [sq, poly, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun S _ =>
      Finset.sum_congr rfl fun T _ => by ring
  have h1 : expect (fun ω => poly c ω ^ 2)
      = ∑ S : Finset G, ∑ T : Finset G, c S * c T
          * (if S = T then 1 else 0) := by
    rw [show (fun ω => poly c ω ^ 2) = fun ω =>
      ∑ S : Finset G, ∑ T : Finset G,
        c S * c T * (walsh S ω * walsh T ω) from
      funext hexp, expect_finset_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [expect_finset_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [expect_const_mul, expect_walsh_mul_walsh]
  rw [h1]
  refine Finset.sum_congr rfl fun S _ => ?_
  have h2 : ∀ T : Finset G,
      c S * c T * (if S = T then 1 else 0)
      = if S = T then c S * c T else 0 := by
    intro T
    by_cases h : S = T <;> simp [h]
  rw [Finset.sum_congr rfl fun T _ => h2 T,
    Finset.sum_ite_eq Finset.univ S (fun T => c S * c T),
    if_pos (Finset.mem_univ S), sq]

/-! ### Translation averaging -/

/-- Configuration shift. -/
def shiftCfg (x : G) (ω : G → Bool) : G → Bool :=
  fun y => ω (y + x)

/-- Observable translation `τ_x f = f ∘ shift_x`. -/
def translate (x : G) (f : (G → Bool) → ℝ) :
    (G → Bool) → ℝ :=
  fun ω => f (shiftCfg x ω)

/-- The empirical translation average
`Av f = |G|⁻¹ ∑_x τ_x f`. -/
noncomputable def average (f : (G → Bool) → ℝ) :
    (G → Bool) → ℝ :=
  fun ω => (Fintype.card G : ℝ)⁻¹
    * ∑ x : G, translate x f ω

omit [Fintype G] in
theorem walsh_translate (x : G) (S : Finset G)
    (ω : G → Bool) :
    translate x (walsh S) ω
      = walsh (S.image (· + x)) ω := by
  unfold translate walsh shiftCfg
  rw [Finset.prod_image (fun a _ b _ h =>
    add_right_cancel h)]
  rfl

omit [Fintype G] in
/-- Cancellation of the two translations on subsets. -/
theorem image_add_sub_cancel (S : Finset G) (x : G) :
    (S.image (· + x)).image (· - x) = S := by
  rw [Finset.image_image]
  have h : ((· - x) ∘ (· + x)) = (id : G → G) := by
    funext y
    simp
  rw [h, Finset.image_id]

/-- The averaged polynomial in coefficient form. -/
theorem average_poly (c : Finset G → ℝ) :
    average (poly c)
      = poly (fun U => (Fintype.card G : ℝ)⁻¹
          * ∑ x : G, c (U.image (· - x))) := by
  funext ω
  have h1 : ∀ x : G, translate x (poly c) ω
      = ∑ U : Finset G,
          c (U.image (· - x)) * walsh U ω := by
    intro x
    have h2 : translate x (poly c) ω
        = ∑ S : Finset G,
            c S * walsh (S.image (· + x)) ω := by
      unfold translate poly
      refine Finset.sum_congr rfl fun S _ => ?_
      have := walsh_translate x S ω
      unfold translate at this
      rw [← this]
    rw [h2]
    refine Fintype.sum_equiv
      ((Equiv.addRight x).finsetCongr)
      (fun S => c S * walsh (S.image (· + x)) ω)
      (fun U => c (U.image (· - x)) * walsh U ω)
      (fun S => ?_)
    have he : (Equiv.addRight x).finsetCongr S
        = S.image (· + x) := by
      rw [Equiv.finsetCongr_apply, Finset.map_eq_image]
      rfl
    rw [he, image_add_sub_cancel]
  have hgoal : average (poly c) ω
      = (Fintype.card G : ℝ)⁻¹
        * ∑ x : G, translate x (poly c) ω := rfl
  have hR : poly (fun U => (Fintype.card G : ℝ)⁻¹
      * ∑ x : G, c (U.image (· - x))) ω
      = ∑ U : Finset G, ((Fintype.card G : ℝ)⁻¹
          * ∑ x : G, c (U.image (· - x)))
        * walsh U ω := rfl
  rw [hgoal, hR, Finset.sum_congr rfl fun x _ => h1 x,
    Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [← Finset.sum_mul, ← mul_assoc]

/-! ### The boxed variance bound -/

/-- **Orbit-orthogonal bracket concentration**: a centered
rooted Walsh polynomial of degree at most `R` on the product
stationary state of the sites `G` satisfies
`Var(Av f) ≤ (R/|G|)·‖f‖₂²`. -/
theorem orbit_variance_bound (c : Finset G → ℝ) (R : ℕ)
    (hroot : ∀ S, c S ≠ 0 → (0 : G) ∈ S)
    (hdeg : ∀ S, c S ≠ 0 → S.card ≤ R) :
    expect (fun ω => average (poly c) ω ^ 2)
      - expect (average (poly c)) ^ 2
    ≤ (R : ℝ) / (Fintype.card G)
      * expect (fun ω => poly c ω ^ 2) := by
  set d : Finset G → ℝ := fun U =>
    (Fintype.card G : ℝ)⁻¹
      * ∑ x : G, c (U.image (· - x)) with hd
  have hcpos : (0 : ℝ) < (Fintype.card G : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hcne : (Fintype.card G : ℝ) ≠ 0 := ne_of_gt hcpos
  -- the average is centered
  have hc0 : c ∅ = 0 := by
    by_contra hcon
    exact absurd (hroot ∅ hcon) (by simp)
  have hmean : expect (average (poly c)) = 0 := by
    rw [average_poly, expect_poly]
    simp only [Finset.image_empty]
    rw [Finset.sum_const, hc0]
    simp
  -- rooted restriction of each averaged coefficient
  have hrestrict : ∀ U : Finset G,
      (∑ x : G, c (U.image (· - x)))
      = ∑ x ∈ U, c (U.image (· - x)) := by
    intro U
    refine (Finset.sum_subset (Finset.subset_univ U)
      ?_).symm
    intro x _ hx
    by_contra hcon
    have h0 := hroot _ hcon
    rw [Finset.mem_image] at h0
    obtain ⟨u, hu, hux⟩ := h0
    have : u = x := by
      have := sub_eq_zero.mp hux
      exact this
    exact hx (this ▸ hu)
  -- per-orbit Cauchy–Schwarz with the rooted count
  have hperU : ∀ U : Finset G, d U ^ 2
      ≤ (Fintype.card G : ℝ)⁻¹ ^ 2 * R
        * ∑ x ∈ U, c (U.image (· - x)) ^ 2 := by
    intro U
    simp only [hd]
    by_cases hall : ∀ x ∈ U, c (U.image (· - x)) = 0
    · have hz : (∑ x ∈ U, c (U.image (· - x))) = 0 :=
        Finset.sum_eq_zero hall
      rw [hrestrict U, hz, mul_zero]
      have hz2 : (∑ x ∈ U, c (U.image (· - x)) ^ 2)
          = 0 :=
        Finset.sum_eq_zero fun x hx => by
          rw [hall x hx]
          ring
      rw [hz2, mul_zero]
      norm_num
    · push Not at hall
      obtain ⟨x₀, hx₀, hcx₀⟩ := hall
      have hcard : U.card ≤ R := by
        have h1 := hdeg _ hcx₀
        rwa [Finset.card_image_of_injective _
          sub_left_injective] at h1
      have hcs := sq_sum_le_card_mul_sum_sq
        (s := U) (f := fun x => c (U.image (· - x)))
      rw [hrestrict U, mul_pow]
      calc ((Fintype.card G : ℝ)⁻¹) ^ 2
          * (∑ x ∈ U, c (U.image (· - x))) ^ 2
          ≤ ((Fintype.card G : ℝ)⁻¹) ^ 2
            * (U.card * ∑ x ∈ U,
                c (U.image (· - x)) ^ 2) := by
            refine mul_le_mul_of_nonneg_left hcs
              (by positivity)
        _ ≤ (Fintype.card G : ℝ)⁻¹ ^ 2 * R
            * ∑ x ∈ U, c (U.image (· - x)) ^ 2 := by
            rw [← mul_assoc]
            refine mul_le_mul_of_nonneg_right ?_
              (Finset.sum_nonneg fun x _ => sq_nonneg _)
            refine mul_le_mul_of_nonneg_left ?_
              (by positivity)
            exact_mod_cast hcard
  -- the double-sum swap with the rooted reindexing
  have hswap : (∑ U : Finset G,
      ∑ x ∈ U, c (U.image (· - x)) ^ 2)
      ≤ (Fintype.card G : ℝ)
        * ∑ T : Finset G, c T ^ 2 := by
    have h1 : ∀ U : Finset G,
        (∑ x ∈ U, c (U.image (· - x)) ^ 2)
        = ∑ x : G, if x ∈ U then
            c (U.image (· - x)) ^ 2 else 0 := by
      intro U
      rw [Finset.sum_ite_mem]
      rw [Finset.univ_inter]
    rw [Finset.sum_congr rfl fun U _ => h1 U,
      Finset.sum_comm]
    have h2 : ∀ x : G, (∑ U : Finset G,
        if x ∈ U then c (U.image (· - x)) ^ 2 else 0)
        ≤ ∑ T : Finset G, c T ^ 2 := by
      intro x
      have h3 : (∑ U : Finset G,
          if x ∈ U then c (U.image (· - x)) ^ 2 else 0)
          = ∑ T : Finset G,
            if x ∈ T.image (· + x) then c T ^ 2
              else 0 := by
        refine (Fintype.sum_equiv
          ((Equiv.addRight x).finsetCongr)
          (fun T => if x ∈ T.image (· + x) then c T ^ 2
            else 0)
          (fun U => if x ∈ U then
            c (U.image (· - x)) ^ 2 else 0)
          (fun T => ?_)).symm
        have he : (Equiv.addRight x).finsetCongr T
            = T.image (· + x) := by
          rw [Equiv.finsetCongr_apply,
            Finset.map_eq_image]
          rfl
        rw [he, image_add_sub_cancel]
      rw [h3]
      refine Finset.sum_le_sum fun T _ => ?_
      by_cases h : x ∈ T.image (· + x)
      · rw [if_pos h]
      · rw [if_neg h]
        exact sq_nonneg _
    calc (∑ x : G, ∑ U : Finset G,
        if x ∈ U then c (U.image (· - x)) ^ 2 else 0)
        ≤ ∑ _x : G, ∑ T : Finset G, c T ^ 2 :=
          Finset.sum_le_sum fun x _ => h2 x
      _ = (Fintype.card G : ℝ)
          * ∑ T : Finset G, c T ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul]
  -- assemble
  rw [hmean, average_poly, expect_poly_sq, expect_poly_sq]
  have hchain : (∑ U : Finset G,
      ((Fintype.card G : ℝ)⁻¹
        * ∑ x : G, c (U.image (· - x))) ^ 2)
      ≤ (Fintype.card G : ℝ)⁻¹ ^ 2 * R
        * ((Fintype.card G : ℝ)
          * ∑ T : Finset G, c T ^ 2) := by
    calc (∑ U : Finset G,
        ((Fintype.card G : ℝ)⁻¹
          * ∑ x : G, c (U.image (· - x))) ^ 2)
        ≤ ∑ U : Finset G,
            (Fintype.card G : ℝ)⁻¹ ^ 2 * R
              * ∑ x ∈ U, c (U.image (· - x)) ^ 2 :=
          Finset.sum_le_sum fun U _ => hperU U
      _ = (Fintype.card G : ℝ)⁻¹ ^ 2 * R
          * ∑ U : Finset G,
              ∑ x ∈ U, c (U.image (· - x)) ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ (Fintype.card G : ℝ)⁻¹ ^ 2 * R
          * ((Fintype.card G : ℝ)
            * ∑ T : Finset G, c T ^ 2) := by
          refine mul_le_mul_of_nonneg_left hswap
            (by positivity)
  have hval : (Fintype.card G : ℝ)⁻¹ ^ 2 * R
      * ((Fintype.card G : ℝ)
        * ∑ T : Finset G, c T ^ 2)
      = (R : ℝ) / (Fintype.card G)
        * ∑ T : Finset G, c T ^ 2 := by
    field_simp
  rw [← hval]
  calc (∑ U : Finset G,
      ((Fintype.card G : ℝ)⁻¹
        * ∑ x : G, c (U.image (· - x))) ^ 2) - 0 ^ 2
      = ∑ U : Finset G,
          ((Fintype.card G : ℝ)⁻¹
            * ∑ x : G, c (U.image (· - x))) ^ 2 := by
        ring
    _ ≤ (Fintype.card G : ℝ)⁻¹ ^ 2 * R
        * ((Fintype.card G : ℝ)
          * ∑ T : Finset G, c T ^ 2) := hchain

/-- The `N³`-site instantiation: `Var(Av f) ≤ (R/N³)·‖f‖₂²`. -/
theorem orbit_variance_bound_cube (N R : ℕ) [NeZero N]
    (c : Finset (ZMod N × ZMod N × ZMod N) → ℝ)
    (hroot : ∀ S, c S ≠ 0 → 0 ∈ S)
    (hdeg : ∀ S, c S ≠ 0 → S.card ≤ R) :
    expect (fun ω => average (poly c) ω ^ 2)
      - expect (average (poly c)) ^ 2
    ≤ (R : ℝ) / (N ^ 3 : ℕ)
      * expect (fun ω => poly c ω ^ 2) := by
  have h := orbit_variance_bound c R hroot hdeg
  have hcard : (Fintype.card
      (ZMod N × ZMod N × ZMod N) : ℝ)
      = ((N ^ 3 : ℕ) : ℝ) := by
    rw [Fintype.card_prod, Fintype.card_prod, ZMod.card]
    push_cast
    ring
  rwa [hcard] at h

/-! ### The stationary time-integral clause -/

/-- **The stationary interval clause**: if every time slice of
a stationary family obeys the variance bound `B`, the time
integral over `[0,T]` obeys the same bound multiplied by
`T²`. -/
theorem time_integral_sq_bound {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℝ → E) (T B : ℝ) (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hu : ∀ s ∈ Set.uIoc (0 : ℝ) T, ‖u s‖ ^ 2 ≤ B) :
    ‖∫ s in (0 : ℝ)..T, u s‖ ^ 2 ≤ T ^ 2 * B := by
  have h1 : ∀ s ∈ Set.uIoc (0 : ℝ) T,
      ‖u s‖ ≤ Real.sqrt B := by
    intro s hs
    have h2 := hu s hs
    calc ‖u s‖ = Real.sqrt (‖u s‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt B := Real.sqrt_le_sqrt h2
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    h1
  rw [sub_zero, abs_of_nonneg hT] at h
  calc ‖∫ s in (0 : ℝ)..T, u s‖ ^ 2
      ≤ (Real.sqrt B * T) ^ 2 := by
        refine pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = T ^ 2 * B := by
        rw [mul_pow, Real.sq_sqrt hB]
        ring

end RenewalOrbitBracket
end NCG
