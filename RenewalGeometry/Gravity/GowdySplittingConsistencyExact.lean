/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.GowdyStaggeredMomentumExact

/-!
# Second-order consistency pieces of the Gowdy symmetric splitting
  (`thm:supp-gowdy-momentum`, consistency clause, emergent-spacetime supplement)

The manuscript's consistency argument has two analytic ingredients: the
background increment of the transport step is the trapezoid rule for the
integral of the translated squares (local error `O(ℓ³)`), and the implicit
midpoint source step has local error `O(σ³)` on smooth charts.  This file
proves both, on top of the exact scheme of `GowdyStaggeredMomentumExact`.

Generic (vector-valued, fencing-lemma) bounds:

* `symmetric_difference_bound` — for a `C²` path `Y` with `‖Y''‖ ≤ M` on
  `[a,b]`, `‖Y(c+s) + Y(c-s) - 2Y(c)‖ ≤ M s²` for `0 ≤ s ≤ (b-a)/2`,
  `c = (a+b)/2`;
* `midpoint_rule_bound` — for a `C³` path `X` with `‖X'''‖ ≤ M₃` on `[a,b]`,
  `‖X(b) - X(a) - (b-a) X'((a+b)/2)‖ ≤ M₃ (b-a)³ / 24`;
* `implicit_midpoint_residual` — for a `C³` trajectory `X' = F(X)` of a field
  `F` that is `L`-Lipschitz on a chart `K` containing the midpoints, the exact
  trajectory satisfies the implicit-midpoint relation up to the residual
  `‖X(b) - X(a) - (b-a) F((X(a)+X(b))/2)‖ ≤ (b-a)³ (M₃/24 + L M₂/8)`.

Gowdy instantiations:

* `transport_lam_trapezoid_error` — if the characteristic squares at the sites
  `j-1, j, j+1` are the samples `g⁺(x), g⁺(x+ℓ)`, `g⁻(x-ℓ), g⁻(x)` of `C²`
  functions with `|g''| ≤ ζ±`, then the background increment of `transport`
  differs from `∫_x^{x+ℓ} g⁺ + ∫_{x-ℓ}^{x} g⁻` by at most `ℓ³ (ζ⁺ + ζ⁻)/12`
  (Mathlib's `trapezoidal_error_le_of_c2`);
* `LocalState.toVec`, `localFieldVec`, `isMidpointStep_iff_toVec` — the local
  `(U,P,Q,t)` state as a vector in `(Fin 4 → ℝ) × ℝ × ℝ × ℝ`, and the
  implicit-midpoint relation in vector form;
* `sourceStep_residual` — a `C³` trajectory of the local source flow on a chart
  where the source field is `L`-Lipschitz satisfies the implicit-midpoint
  relation of duration `σ` up to a residual of norm
  `≤ σ³ (M₃/24 + L M₂/8)`: second-order local consistency of the source
  half-steps.

Not formalised (disclosed): the Lipschitz constant of the source field on a
concrete chart `{t ≥ t₀ > 0, bounded}` is taken as the chart hypothesis, and
the symmetric-composition (Strang) local error of the full split scheme
against the continuum Gowdy system is not assembled.
-/

open Set
open scoped BigOperators

namespace RenewalGeometry.GowdyStaggered

noncomputable section

/-! ### Generic fencing bounds -/

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Symmetric second difference of a `C²` path: `‖Y(c+s) + Y(c-s) - 2Y(c)‖ ≤ M s²`
for `0 ≤ s ≤ (b-a)/2`, `c = (a+b)/2`, when `‖Y''‖ ≤ M` on `[a,b]`. -/
theorem symmetric_difference_bound (Y Y' Y'' : ℝ → E) (a b M : ℝ)
    (h1 : ∀ s, HasDerivAt Y (Y' s) s) (h2 : ∀ s, HasDerivAt Y' (Y'' s) s)
    (hM : ∀ s ∈ Icc a b, ‖Y'' s‖ ≤ M) :
    ∀ s ∈ Icc 0 ((b - a) / 2),
      ‖Y ((a + b) / 2 + s) + Y ((a + b) / 2 - s) - (2 : ℝ) • Y ((a + b) / 2)‖ ≤
        M * s ^ 2 := by
  set c := (a + b) / 2 with hc
  set r := (b - a) / 2 with hr
  -- the symmetric difference and its derivative
  set χ : ℝ → E := fun s => Y (c + s) + Y (c - s) - (2 : ℝ) • Y c with hχ
  set χ' : ℝ → E := fun s => Y' (c + s) - Y' (c - s) with hχ'
  have hχd : ∀ s, HasDerivAt χ (χ' s) s := by
    intro s
    have hp := (h1 (c + s)).comp_const_add c s
    have hm := (h1 (c - s)).comp_const_sub c s
    have hd := (hp.add hm).sub (hasDerivAt_const s ((2 : ℝ) • Y c))
    exact hd.congr_deriv (by simp only [hχ']; abel)
  -- the derivative bound `‖χ' s‖ ≤ 2 M s` on `[0, r]`
  have hmem : ∀ s ∈ Icc 0 r, c + s ∈ Icc a b ∧ c - s ∈ Icc a b := by
    intro s hs
    obtain ⟨hs0, hsr⟩ := hs
    constructor <;> constructor <;> linarith
  have hbound : ∀ s ∈ Ico 0 r, ‖χ' s‖ ≤ 2 * M * s := by
    intro s hs
    have hs' : s ∈ Icc 0 r := Ico_subset_Icc_self hs
    obtain ⟨hp, hm⟩ := hmem s hs'
    have := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := Y') (f' := Y'') (fun x _ => (h2 x).hasDerivWithinAt) hM hm hp
    have hnorm : ‖c + s - (c - s)‖ = 2 * s := by
      rw [show c + s - (c - s) = 2 * s by ring, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [hs.1])]
    rw [hnorm] at this
    simp only [hχ']
    linarith
  -- fencing with `B s = M s²`
  have hB : ∀ s : ℝ, HasDerivAt (fun s => M * s ^ 2) (2 * M * s) s := by
    intro s
    have := ((hasDerivAt_pow 2 s).const_mul M)
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have hχ0 : ‖χ 0‖ ≤ M * (0 : ℝ) ^ 2 := by
    simp [hχ, two_smul]
  have hfence := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := χ) (f' := χ') (a := 0) (b := r)
    (fun s _ => (hχd s).continuousAt.continuousWithinAt)
    (fun s _ => (hχd s).hasDerivWithinAt) hχ0 hB hbound
  intro s hs
  simpa [hχ] using hfence hs

/-- Midpoint-rule bound for a `C³` path:
`‖X(b) - X(a) - (b-a) X'((a+b)/2)‖ ≤ M₃ (b-a)³ / 24` when `‖X'''‖ ≤ M₃` on `[a,b]`. -/
theorem midpoint_rule_bound (X X' X'' X''' : ℝ → E) (a b M₃ : ℝ) (hab : a ≤ b)
    (h1 : ∀ s, HasDerivAt X (X' s) s) (h2 : ∀ s, HasDerivAt X' (X'' s) s)
    (h3 : ∀ s, HasDerivAt X'' (X''' s) s)
    (hM : ∀ s ∈ Icc a b, ‖X''' s‖ ≤ M₃) :
    ‖X b - X a - (b - a) • X' ((a + b) / 2)‖ ≤ M₃ * (b - a) ^ 3 / 24 := by
  set c := (a + b) / 2 with hc
  set r := (b - a) / 2 with hr
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  have hψ := symmetric_difference_bound X' X'' X''' a b M₃ h2 h3 hM
  -- the midpoint defect and its derivative
  set φ : ℝ → E := fun s => X (c + s) - X (c - s) - (2 * s) • X' c with hφ
  set φ' : ℝ → E := fun s => X' (c + s) + X' (c - s) - (2 : ℝ) • X' c with hφ'
  have hφd : ∀ s, HasDerivAt φ (φ' s) s := by
    intro s
    have hp := (h1 (c + s)).comp_const_add c s
    have hm := (h1 (c - s)).comp_const_sub c s
    have hl : HasDerivAt (fun s : ℝ => (2 * s) • X' c) ((2 : ℝ) • X' c) s := by
      have := ((hasDerivAt_id s).const_mul (2 : ℝ)).smul_const (X' c)
      simpa using this
    have hd := (hp.sub hm).sub hl
    exact hd.congr_deriv (by simp only [hφ']; abel)
  have hbound : ∀ s ∈ Ico 0 r, ‖φ' s‖ ≤ M₃ * s ^ 2 := fun s hs =>
    hψ s (Ico_subset_Icc_self hs)
  have hB : ∀ s : ℝ, HasDerivAt (fun s => M₃ * s ^ 3 / 3) (M₃ * s ^ 2) s := by
    intro s
    have := ((hasDerivAt_pow 3 s).const_mul M₃).div_const 3
    refine this.congr_deriv ?_
    push_cast; ring
  have hφ0 : ‖φ 0‖ ≤ M₃ * (0 : ℝ) ^ 3 / 3 := by simp [hφ]
  have hfence := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := φ) (f' := φ') (a := 0) (b := r)
    (fun s _ => (hφd s).continuousAt.continuousWithinAt)
    (fun s _ => (hφd s).hasDerivWithinAt) hφ0 hB hbound
  have hend := hfence (right_mem_Icc.mpr hr0)
  have hcr1 : c + r = b := by rw [hc, hr]; ring
  have hcr2 : c - r = a := by rw [hc, hr]; ring
  have hcr3 : 2 * r = b - a := by rw [hr]; ring
  simp only [hφ, hcr1, hcr2, hcr3] at hend
  calc ‖X b - X a - (b - a) • X' ((a + b) / 2)‖ ≤ M₃ * r ^ 3 / 3 := hend
    _ = M₃ * (b - a) ^ 3 / 24 := by rw [hr]; ring

/-- Second-order local residual of the implicit midpoint rule along an exact
`C³` trajectory `X' = F(X)` of a field `F` that is `L`-Lipschitz on a chart `K`
containing `X((a+b)/2)` and `(X(a)+X(b))/2`:
`‖X(b) - X(a) - (b-a) F((X(a)+X(b))/2)‖ ≤ (b-a)³ (M₃/24 + L M₂/8)`. -/
theorem implicit_midpoint_residual (F : E → E) (X X'' X''' : ℝ → E) (K : Set E)
    (a b M₂ M₃ L : ℝ) (hab : a ≤ b) (hL0 : 0 ≤ L)
    (h1 : ∀ s, HasDerivAt X (F (X s)) s)
    (h2 : ∀ s, HasDerivAt (fun s => F (X s)) (X'' s) s)
    (h3 : ∀ s, HasDerivAt X'' (X''' s) s)
    (hM₂ : ∀ s ∈ Icc a b, ‖X'' s‖ ≤ M₂) (hM₃ : ∀ s ∈ Icc a b, ‖X''' s‖ ≤ M₃)
    (hLip : ∀ x ∈ K, ∀ y ∈ K, ‖F x - F y‖ ≤ L * ‖x - y‖)
    (hmid : X ((a + b) / 2) ∈ K) (hmid' : (1 / 2 : ℝ) • (X a + X b) ∈ K) :
    ‖X b - X a - (b - a) • F ((1 / 2 : ℝ) • (X a + X b))‖ ≤
      (b - a) ^ 3 * (M₃ / 24 + L * M₂ / 8) := by
  have hmr := midpoint_rule_bound X (fun s => F (X s)) X'' X''' a b M₃ hab h1 h2 h3 hM₃
  have hsd := symmetric_difference_bound X (fun s => F (X s)) X'' a b M₂ h1 h2 hM₂
    ((b - a) / 2) ⟨by linarith, le_rfl⟩
  have hc1 : (a + b) / 2 + (b - a) / 2 = b := by ring
  have hc2 : (a + b) / 2 - (b - a) / 2 = a := by ring
  rw [hc1, hc2] at hsd
  -- `‖X c - (X a + X b)/2‖ ≤ M₂ (b-a)²/8`
  have hhalf : ‖X ((a + b) / 2) - (1 / 2 : ℝ) • (X a + X b)‖ ≤
      M₂ * (b - a) ^ 2 / 8 := by
    have heq : X ((a + b) / 2) - (1 / 2 : ℝ) • (X a + X b) =
        (-(1 / 2) : ℝ) • (X b + X a - (2 : ℝ) • X ((a + b) / 2)) := by
      simp only [smul_sub, smul_add, smul_smul]
      norm_num
      abel
    rw [heq, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    calc 1 / 2 * ‖X b + X a - (2 : ℝ) • X ((a + b) / 2)‖ ≤ 1 / 2 * (M₂ * ((b - a) / 2) ^ 2) := by
          gcongr
      _ = M₂ * (b - a) ^ 2 / 8 := by ring
  have hLipmid := hLip _ hmid _ hmid'
  have hba : 0 ≤ b - a := by linarith
  calc ‖X b - X a - (b - a) • F ((1 / 2 : ℝ) • (X a + X b))‖
      = ‖(X b - X a - (b - a) • F (X ((a + b) / 2))) +
          (b - a) • (F (X ((a + b) / 2)) - F ((1 / 2 : ℝ) • (X a + X b)))‖ := by
        congr 1
        simp only [smul_sub]
        abel
    _ ≤ ‖X b - X a - (b - a) • F (X ((a + b) / 2))‖ +
          ‖(b - a) • (F (X ((a + b) / 2)) - F ((1 / 2 : ℝ) • (X a + X b)))‖ :=
        norm_add_le _ _
    _ ≤ M₃ * (b - a) ^ 3 / 24 +
          (b - a) * (L * (M₂ * (b - a) ^ 2 / 8)) := by
        gcongr
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hba]
        gcongr
        exact hLipmid.trans (by gcongr)
    _ = (b - a) ^ 3 * (M₃ / 24 + L * M₂ / 8) := by ring

end Generic

/-! ### The transport background increment is a trapezoid rule -/

variable {N : ℕ}

/-- The background increment `λ⁺_j - λ_j` of `transport` is the trapezoid rule
for `∫_x^{x+ℓ} g⁺ + ∫_{x-ℓ}^{x} g⁻`, with local error `≤ ℓ³ (ζ⁺ + ζ⁻)/12`, whenever
the characteristic squares at the sites `j, j±1` sample `C²` functions `g±` with
second derivatives bounded by `ζ±` (`0 ≤ ℓ`). -/
theorem transport_lam_trapezoid_error (ℓ x ζp ζm : ℝ) (hℓ : 0 ≤ ℓ)
    (X : GridState N) (j : ZMod N) (gp gm : ℝ → ℝ)
    (hgp : ContDiffOn ℝ 2 gp (uIcc x (x + ℓ)))
    (hgm : ContDiffOn ℝ 2 gm (uIcc (x - ℓ) x))
    (hζp : ∀ y, |iteratedDerivWithin 2 gp (uIcc x (x + ℓ)) y| ≤ ζp)
    (hζm : ∀ y, |iteratedDerivWithin 2 gm (uIcc (x - ℓ) x) y| ≤ ζm)
    (h0p : gPlus (X.site j).u = gp x) (h1p : gPlus (X.site (j + 1)).u = gp (x + ℓ))
    (h0m : gMinus (X.site j).u = gm x) (h1m : gMinus (X.site (j - 1)).u = gm (x - ℓ)) :
    |((transport ℓ X).lam j - X.lam j) -
        ((∫ y in x..x + ℓ, gp y) + ∫ y in x - ℓ..x, gm y)| ≤
      ℓ ^ 3 * (ζp + ζm) / 12 := by
  have hp := trapezoidal_error_le_of_c2 hgp hζp one_pos
  have hm := trapezoidal_error_le_of_c2 hgm hζm one_pos
  simp only [trapezoidal_error, trapezoidal_integral_one, Nat.cast_one, one_pow, mul_one,
    add_sub_cancel_left, sub_sub_cancel, abs_of_nonneg hℓ] at hp hm
  have hinc : (transport ℓ X).lam j - X.lam j -
      ((∫ y in x..x + ℓ, gp y) + ∫ y in x - ℓ..x, gm y) =
      (ℓ / 2 * (gp x + gp (x + ℓ)) - ∫ y in x..x + ℓ, gp y) +
        (ℓ / 2 * (gm (x - ℓ) + gm x) - ∫ y in x - ℓ..x, gm y) := by
    simp only [transport, add_sub_cancel_left, h0p, h1p, h0m, h1m]
    ring
  rw [hinc]
  calc |(ℓ / 2 * (gp x + gp (x + ℓ)) - ∫ y in x..x + ℓ, gp y) +
        (ℓ / 2 * (gm (x - ℓ) + gm x) - ∫ y in x - ℓ..x, gm y)|
      ≤ |ℓ / 2 * (gp x + gp (x + ℓ)) - ∫ y in x..x + ℓ, gp y| +
        |ℓ / 2 * (gm (x - ℓ) + gm x) - ∫ y in x - ℓ..x, gm y| := abs_add_le _ _
    _ ≤ ℓ ^ 3 * ζp / 12 + ℓ ^ 3 * ζm / 12 := add_le_add hp hm
    _ = ℓ ^ 3 * (ζp + ζm) / 12 := by ring

/-! ### The source half-step in vector form -/

/-- The state space `(U, P, Q, t)` of the local source flow as a normed vector space. -/
abbrev StateVec := (Fin 4 → ℝ) × ℝ × ℝ × ℝ

/-- The local state as a vector. -/
def LocalState.toVec (X : LocalState) : StateVec := (X.u, X.P, X.Q, X.t)

/-- A vector as a local state. -/
def LocalState.ofVec (v : StateVec) : LocalState :=
  { u := v.1, P := v.2.1, Q := v.2.2.1, t := v.2.2.2 }

@[simp] theorem LocalState.ofVec_toVec (X : LocalState) : LocalState.ofVec X.toVec = X := rfl

@[simp] theorem LocalState.toVec_ofVec (v : StateVec) : (LocalState.ofVec v).toVec = v := rfl

/-- The local source field `eq:supp-gowdy-source-flow` in vector form. -/
def localFieldVec (v : StateVec) : StateVec := (localField (LocalState.ofVec v)).toVec

/-- The arithmetic midpoint in vector form. -/
theorem toVec_midpoint (X Y : LocalState) :
    (midpoint X Y).toVec = (1 / 2 : ℝ) • (X.toVec + Y.toVec) := by
  simp only [LocalState.toVec, midpoint, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp <;> ring

/-- The implicit-midpoint relation `Y = X + σ F((X+Y)/2)` in vector form. -/
theorem isMidpointStep_iff_toVec (σ : ℝ) (X Y : LocalState) :
    IsMidpointStep σ X Y ↔
      Y.toVec = X.toVec + σ • localFieldVec ((1 / 2 : ℝ) • (X.toVec + Y.toVec)) := by
  rw [← toVec_midpoint]
  unfold IsMidpointStep localFieldVec
  simp only [LocalState.toVec, Prod.smul_mk, Prod.mk_add_mk,
    Prod.mk.injEq, smul_eq_mul]
  tauto

/-- **Second-order local consistency of the implicit-midpoint source step**
(`thm:supp-gowdy-momentum`, consistency clause, source part): a `C³` trajectory
`Z` of the local source flow (`Z' = localField Z`) on a chart `K` where the vector
source field is `L`-Lipschitz satisfies the implicit-midpoint relation of duration
`σ = b - a` up to a residual of norm at most `σ³ (M₃/24 + L M₂/8)`, where `M₂, M₃`
bound the second and third derivatives of the trajectory on `[a, b]`. -/
theorem sourceStep_residual (Z : ℝ → LocalState) (V'' V''' : ℝ → StateVec) (K : Set StateVec)
    (a b M₂ M₃ L : ℝ) (hab : a ≤ b) (hL0 : 0 ≤ L)
    (h1 : ∀ s, HasDerivAt (fun s => (Z s).toVec) ((localField (Z s)).toVec) s)
    (h2 : ∀ s, HasDerivAt (fun s => (localField (Z s)).toVec) (V'' s) s)
    (h3 : ∀ s, HasDerivAt V'' (V''' s) s)
    (hM₂ : ∀ s ∈ Icc a b, ‖V'' s‖ ≤ M₂) (hM₃ : ∀ s ∈ Icc a b, ‖V''' s‖ ≤ M₃)
    (hLip : ∀ x ∈ K, ∀ y ∈ K, ‖localFieldVec x - localFieldVec y‖ ≤ L * ‖x - y‖)
    (hmid : (Z ((a + b) / 2)).toVec ∈ K) (hmid' : (midpoint (Z a) (Z b)).toVec ∈ K) :
    ‖(Z b).toVec - ((Z a).toVec + (b - a) • (localField (midpoint (Z a) (Z b))).toVec)‖ ≤
      (b - a) ^ 3 * (M₃ / 24 + L * M₂ / 8) := by
  have hF : ∀ s, localFieldVec ((Z s).toVec) = (localField (Z s)).toVec := by
    intro s; simp [localFieldVec]
  have h1' : ∀ s, HasDerivAt (fun s => (Z s).toVec) (localFieldVec ((Z s).toVec)) s := by
    intro s; rw [hF]; exact h1 s
  have h2' : ∀ s, HasDerivAt (fun s => localFieldVec ((Z s).toVec)) (V'' s) s := by
    intro s; simp only [hF]; exact h2 s
  rw [toVec_midpoint] at hmid'
  have := implicit_midpoint_residual localFieldVec (fun s => (Z s).toVec) V'' V''' K
    a b M₂ M₃ L hab hL0 h1' h2' h3 hM₂ hM₃ hLip hmid hmid'
  have hmidvec : (localField (midpoint (Z a) (Z b))).toVec =
      localFieldVec ((1 / 2 : ℝ) • ((Z a).toVec + (Z b).toVec)) := by
    rw [← toVec_midpoint]; simp [localFieldVec]
  rw [hmidvec, sub_add_eq_sub_sub]
  exact this

end

end RenewalGeometry.GowdyStaggered
