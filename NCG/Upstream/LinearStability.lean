/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.LinearRetract

/-!
# Quantitative stability of minimal predictive memory

Covers, from `manuscripts/renewal_emergence/renewal_emergence.tex`:

* `def:approx-compression` — the idempotence and sufficiency defects
  `δ(E) = ‖E² − E‖`, `ε_q(E) = ‖qE − q‖`;
* `thm:predictive-stability` — an approximately idempotent,
  approximately future-sufficient compression `E` with a nearby
  idempotent `P` of the minimal spectral rank, transverse to the
  null directions (`κη < 1`), lies near the exact minimal predictive
  retract `R = P s B⁻¹ q`, with the explicit bound
  `‖R − E‖ ≤ α + ‖P‖κη/(1−κη)`;
* `cor:dynamics-stability` — the induced renewal dynamics on the
  common carrier is norm-stable, one step and along words (with the
  standard telescoping bound).

Setting: finite-dimensional real normed spaces and bounded operators
(`X →L[ℝ] X`); the idempotent `P` is an input with `α = ‖P − E‖`,
exactly as the theorem uses the output of `lem:idempotentization`.
-/

namespace NCG.Upstream

open Module

variable {X Q : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Q]

/-- **Definition `def:approx-compression` (idempotence defect)**:
`δ(E) = ‖E² − E‖`. -/
noncomputable def idemDefect (E : X →L[ℝ] X) : ℝ :=
  ‖E * E - E‖

/-- **Definition `def:approx-compression` (sufficiency defect)**:
`ε_q(E) = ‖qE − q‖`. -/
noncomputable def suffDefect (q : X →L[ℝ] Q) (E : X →L[ℝ] X) : ℝ :=
  ‖q.comp E - q‖

section Stability

variable (q : X →L[ℝ] Q) (s : Q →L[ℝ] X) (P E : X →L[ℝ] X)

/-- The perturbed quotient transfer `B = qPs`. -/
noncomputable def stabilityB : Q →L[ℝ] Q :=
  (q.comp P).comp s

omit [FiniteDimensional ℝ Q] [FiniteDimensional ℝ X] in
/-- `‖qP − q‖ ≤ η = ε + ‖q‖α`. -/
theorem qP_sub_q_norm_le :
    ‖q.comp P - q‖ ≤ suffDefect q E + ‖q‖ * ‖P - E‖ := by
  have hdecomp : q.comp P - q = q.comp (P - E) + (q.comp E - q) := by
    rw [ContinuousLinearMap.comp_sub]
    abel
  rw [hdecomp]
  refine (norm_add_le _ _).trans ?_
  rw [suffDefect, add_comm]
  gcongr
  exact ContinuousLinearMap.opNorm_comp_le q (P - E)

omit [FiniteDimensional ℝ Q] [FiniteDimensional ℝ X] in
/-- `‖B − 1‖ ≤ κη` (using `qs = 1`). -/
theorem stabilityB_sub_one_norm_le
    (hs : q.comp s = ContinuousLinearMap.id ℝ Q) :
    ‖stabilityB q s P - 1‖
      ≤ ‖s‖ * (suffDefect q E + ‖q‖ * ‖P - E‖) := by
  have hdecomp : stabilityB q s P - 1 = (q.comp P - q).comp s := by
    rw [ContinuousLinearMap.sub_comp, hs, ContinuousLinearMap.one_def]
    rfl
  rw [hdecomp, mul_comm]
  exact (ContinuousLinearMap.opNorm_comp_le _ s).trans
    (by gcongr; exact qP_sub_q_norm_le q P E)

variable {q s P E}

omit [FiniteDimensional ℝ Q] [FiniteDimensional ℝ X] in
/-- Under `κη < 1`, `‖1 − B‖ < 1`. -/
theorem one_sub_stabilityB_norm_lt
    (hs : q.comp s = ContinuousLinearMap.id ℝ Q)
    (hlt : ‖s‖ * (suffDefect q E + ‖q‖ * ‖P - E‖) < 1) :
    ‖(1 : Q →L[ℝ] Q) - stabilityB q s P‖ < 1 := by
  rw [norm_sub_rev]
  exact lt_of_le_of_lt (stabilityB_sub_one_norm_le q s P E hs) hlt

/-- The invertible transfer as a unit of the operator algebra. -/
noncomputable def stabilityUnit
    (h : ‖(1 : Q →L[ℝ] Q) - stabilityB q s P‖ < 1) : (Q →L[ℝ] Q)ˣ :=
  Units.oneSub ((1 : Q →L[ℝ] Q) - stabilityB q s P) h

omit [FiniteDimensional ℝ X] in
theorem stabilityUnit_val
    (h : ‖(1 : Q →L[ℝ] Q) - stabilityB q s P‖ < 1) :
    ((stabilityUnit h : (Q →L[ℝ] Q)ˣ) : Q →L[ℝ] Q)
      = stabilityB q s P := by
  change ((Units.oneSub _ h : (Q →L[ℝ] Q)ˣ) : Q →L[ℝ] Q) = _
  rw [Units.val_oneSub, sub_sub_cancel]

omit [FiniteDimensional ℝ X] in
/-- **Theorem `thm:predictive-stability` (Neumann bound)**:
`‖B⁻¹‖ ≤ (1 − ‖1 − B‖)⁻¹`. -/
theorem stabilityUnit_inv_norm_le [Nontrivial Q]
    (h : ‖(1 : Q →L[ℝ] Q) - stabilityB q s P‖ < 1) :
    ‖(((stabilityUnit h)⁻¹ : (Q →L[ℝ] Q)ˣ) : Q →L[ℝ] Q)‖
      ≤ (1 - ‖(1 : Q →L[ℝ] Q) - stabilityB q s P‖)⁻¹ := by
  change ‖∑' n : ℕ, ((1 : Q →L[ℝ] Q) - stabilityB q s P) ^ n‖ ≤ _
  have hgeom := tsum_geometric_le_of_norm_lt_one _ h
  have hone : ‖(1 : Q →L[ℝ] Q)‖ = 1 := by
    rw [ContinuousLinearMap.one_def]
    exact ContinuousLinearMap.norm_id
  rw [hone] at hgeom
  simpa using hgeom

/-- **Theorem `thm:predictive-stability` (the exact retract)**:
`R = P s B⁻¹ q`. -/
noncomputable def stabilityR
    (h : ‖(1 : Q →L[ℝ] Q) - stabilityB q s P‖ < 1) : X →L[ℝ] X :=
  ((P.comp s).comp
    (((stabilityUnit h)⁻¹ : (Q →L[ℝ] Q)ˣ) : Q →L[ℝ] Q)).comp q

omit [FiniteDimensional ℝ X] in
theorem stabilityR_apply
    (h : ‖(1 : Q →L[ℝ] Q) - stabilityB q s P‖ < 1) (x : X) :
    stabilityR h x
      = P (s ((((stabilityUnit h)⁻¹ : (Q →L[ℝ] Q)ˣ)
          : Q →L[ℝ] Q) (q x))) := rfl

omit [FiniteDimensional ℝ X] in
theorem stabilityB_apply_inv
    (h : ‖(1 : Q →L[ℝ] Q) - stabilityB q s P‖ < 1) (y : Q) :
    stabilityB q s P
        ((((stabilityUnit h)⁻¹ : (Q →L[ℝ] Q)ˣ) : Q →L[ℝ] Q) y)
      = y := by
  have hmul : stabilityB q s P
      * (((stabilityUnit h)⁻¹ : (Q →L[ℝ] Q)ˣ) : Q →L[ℝ] Q) = 1 := by
    rw [← stabilityUnit_val h]
    exact (stabilityUnit h).mul_inv
  have h2 := congrFun (congrArg DFunLike.coe hmul) y
  simpa using h2

omit [FiniteDimensional ℝ X] in
/-- **Theorem `thm:predictive-stability` (`qR = q`)**. -/
theorem stabilityR_q
    (h : ‖(1 : Q →L[ℝ] Q) - stabilityB q s P‖ < 1) :
    q.comp (stabilityR h) = q := by
  ext x
  change q (stabilityR h x) = q x
  rw [stabilityR_apply]
  exact stabilityB_apply_inv h (q x)

omit [FiniteDimensional ℝ X] in
theorem stabilityR_q_apply
    (h : ‖(1 : Q →L[ℝ] Q) - stabilityB q s P‖ < 1) (x : X) :
    q (stabilityR h x) = q x :=
  congrFun (congrArg DFunLike.coe (stabilityR_q h)) x

omit [FiniteDimensional ℝ X] in
/-- **Theorem `thm:predictive-stability` (`R² = R`)**. -/
theorem stabilityR_idem
    (h : ‖(1 : Q →L[ℝ] Q) - stabilityB q s P‖ < 1) :
    (stabilityR h).comp (stabilityR h) = stabilityR h := by
  ext x
  change stabilityR h (stabilityR h x) = stabilityR h x
  conv_lhs => rw [stabilityR_apply h (stabilityR h x),
    stabilityR_q_apply h x]
  rw [← stabilityR_apply]

omit [FiniteDimensional ℝ X] in
/-- `R` at the `LinearMap` level is an exact projection. -/
theorem stabilityR_isExactProjection
    (h : ‖(1 : Q →L[ℝ] Q) - stabilityB q s P‖ < 1) :
    IsExactProjection (q : X →ₗ[ℝ] Q)
      ((stabilityR h : X →L[ℝ] X) : X →ₗ[ℝ] X) :=
  ⟨congrArg ContinuousLinearMap.toLinearMap (stabilityR_idem h),
   congrArg ContinuousLinearMap.toLinearMap (stabilityR_q h)⟩

omit [FiniteDimensional ℝ X] in
theorem stabilityR_range_le
    (h : ‖(1 : Q →L[ℝ] Q) - stabilityB q s P‖ < 1) :
    LinearMap.range ((stabilityR h : X →L[ℝ] X) : X →ₗ[ℝ] X)
      ≤ LinearMap.range (P : X →ₗ[ℝ] X) := by
  rintro x ⟨y, rfl⟩
  exact ⟨s ((((stabilityUnit h)⁻¹ : (Q →L[ℝ] Q)ˣ)
    : Q →L[ℝ] Q) (q y)), rfl⟩

/-- **Theorem `thm:predictive-stability` (rank and image)**: under
the spectral-rank hypothesis, `rank R = r` and `im R = im P`. -/
theorem stabilityR_range_eq
    (hq : Function.Surjective q)
    (hrank : finrank ℝ (LinearMap.range (P : X →ₗ[ℝ] X))
      = finrank ℝ Q)
    (h : ‖(1 : Q →L[ℝ] Q) - stabilityB q s P‖ < 1) :
    LinearMap.range ((stabilityR h : X →L[ℝ] X) : X →ₗ[ℝ] X)
      = LinearMap.range (P : X →ₗ[ℝ] X) := by
  have hge : finrank ℝ Q ≤ finrank ℝ
      (LinearMap.range ((stabilityR h : X →L[ℝ] X) : X →ₗ[ℝ] X)) :=
    exactProjection_rank_ge hq (stabilityR_isExactProjection h)
  exact Submodule.eq_of_le_of_finrank_le (stabilityR_range_le h)
    (le_trans hrank.le hge)

theorem stabilityR_rank
    (hq : Function.Surjective q)
    (hrank : finrank ℝ (LinearMap.range (P : X →ₗ[ℝ] X))
      = finrank ℝ Q)
    (h : ‖(1 : Q →L[ℝ] Q) - stabilityB q s P‖ < 1) :
    finrank ℝ
        (LinearMap.range ((stabilityR h : X →L[ℝ] X) : X →ₗ[ℝ] X))
      = finrank ℝ Q := by
  rw [stabilityR_range_eq hq hrank h]
  exact hrank

omit [FiniteDimensional ℝ X] in
/-- Elements of `im R` vanish when their `q`-value vanishes. -/
theorem stabilityR_q_injOn
    (h : ‖(1 : Q →L[ℝ] Q) - stabilityB q s P‖ < 1) {x : X}
    (hx : x ∈
      LinearMap.range ((stabilityR h : X →L[ℝ] X) : X →ₗ[ℝ] X))
    (hqx : q x = 0) : x = 0 := by
  obtain ⟨y, rfl⟩ := hx
  change stabilityR h y = 0
  have hfix : stabilityR h (stabilityR h y) = stabilityR h y :=
    congrFun (congrArg DFunLike.coe (stabilityR_idem h)) y
  have hqy : q (stabilityR h y) = 0 := hqx
  rw [← hfix, stabilityR_apply, hqy]
  simp

/-- **Theorem `thm:predictive-stability` (`RP = P`)**: `R` restricts
to the identity on the near-one spectral carrier. -/
theorem stabilityR_comp_P
    (hq : Function.Surjective q)
    (hrank : finrank ℝ (LinearMap.range (P : X →ₗ[ℝ] X))
      = finrank ℝ Q)
    (h : ‖(1 : Q →L[ℝ] Q) - stabilityB q s P‖ < 1) :
    (stabilityR h).comp P = P := by
  ext x
  change stabilityR h (P x) = P x
  have hmemA : stabilityR h (P x) ∈
      LinearMap.range ((stabilityR h : X →L[ℝ] X) : X →ₗ[ℝ] X) :=
    ⟨P x, rfl⟩
  have hmemB : P x ∈
      LinearMap.range ((stabilityR h : X →L[ℝ] X) : X →ₗ[ℝ] X) := by
    rw [stabilityR_range_eq hq hrank h]
    exact LinearMap.mem_range_self (P : X →ₗ[ℝ] X) x
  have hq0 : q (stabilityR h (P x) - P x) = 0 := by
    rw [map_sub, stabilityR_q_apply h (P x), sub_self]
  exact sub_eq_zero.mp
    (stabilityR_q_injOn h (Submodule.sub_mem _ hmemA hmemB) hq0)

/-- `R − P = R(1 − P)` on the nose. -/
theorem stabilityR_sub_P
    (hq : Function.Surjective q)
    (hrank : finrank ℝ (LinearMap.range (P : X →ₗ[ℝ] X))
      = finrank ℝ Q)
    (h : ‖(1 : Q →L[ℝ] Q) - stabilityB q s P‖ < 1) :
    stabilityR h - P
      = (stabilityR h).comp (ContinuousLinearMap.id ℝ X - P) := by
  rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id,
    stabilityR_comp_P hq hrank h]

/-- **Theorem `thm:predictive-stability` (main bound)**:
`‖R − E‖ ≤ α + ‖P‖ κη/(1 − κη)` with `α = ‖P − E‖`, `κ = ‖s‖`,
`η = ε_q(E) + ‖q‖α`. -/
theorem predictive_stability_norm_le [Nontrivial Q]
    (hs : q.comp s = ContinuousLinearMap.id ℝ Q)
    (hq : Function.Surjective q)
    (hrank : finrank ℝ (LinearMap.range (P : X →ₗ[ℝ] X))
      = finrank ℝ Q)
    (hlt : ‖s‖ * (suffDefect q E + ‖q‖ * ‖P - E‖) < 1) :
    ‖stabilityR (one_sub_stabilityB_norm_lt hs hlt) - E‖
      ≤ ‖P - E‖
        + ‖P‖ * (‖s‖ * (suffDefect q E + ‖q‖ * ‖P - E‖))
          / (1 - ‖s‖ * (suffDefect q E + ‖q‖ * ‖P - E‖)) := by
  set η : ℝ := suffDefect q E + ‖q‖ * ‖P - E‖ with hη
  set h := one_sub_stabilityB_norm_lt hs hlt
  have hηpos : 0 ≤ η := by
    rw [hη, suffDefect]
    positivity
  have hκη : 0 ≤ ‖s‖ * η := mul_nonneg (norm_nonneg s) hηpos
  have hden : 0 < 1 - ‖s‖ * η := by
    rw [hη] at hlt ⊢
    linarith
  have hinv_nonneg : (0 : ℝ) ≤ (1 - ‖s‖ * η)⁻¹ :=
    inv_nonneg.mpr hden.le
  -- the operator-norm chain for ‖R − P‖
  have hqid : ‖q.comp (ContinuousLinearMap.id ℝ X - P)‖ ≤ η := by
    have hd : q.comp (ContinuousLinearMap.id ℝ X - P)
        = -(q.comp P - q) := by
      rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id]
      abel
    rw [hd, norm_neg, hη]
    exact qP_sub_q_norm_le q P E
  have hBinv : ‖(((stabilityUnit h)⁻¹ : (Q →L[ℝ] Q)ˣ) : Q →L[ℝ] Q)‖
      ≤ (1 - ‖s‖ * η)⁻¹ := by
    refine (stabilityUnit_inv_norm_le h).trans ?_
    have hτ : ‖(1 : Q →L[ℝ] Q) - stabilityB q s P‖ ≤ ‖s‖ * η := by
      rw [norm_sub_rev, hη]
      exact stabilityB_sub_one_norm_le q s P E hs
    exact inv_anti₀ hden (by linarith)
  have hsplit : stabilityR h - P
      = ((P.comp s).comp
          (((stabilityUnit h)⁻¹ : (Q →L[ℝ] Q)ˣ) : Q →L[ℝ] Q)).comp
        (q.comp (ContinuousLinearMap.id ℝ X - P)) := by
    rw [stabilityR_sub_P hq hrank h]
    rw [show stabilityR h = ((P.comp s).comp
        (((stabilityUnit h)⁻¹ : (Q →L[ℝ] Q)ˣ) : Q →L[ℝ] Q)).comp q
      from rfl]
    rw [ContinuousLinearMap.comp_assoc]
  have hPS : ‖P.comp s‖ ≤ ‖P‖ * ‖s‖ :=
    ContinuousLinearMap.opNorm_comp_le P s
  have hPSB : ‖(P.comp s).comp
      (((stabilityUnit h)⁻¹ : (Q →L[ℝ] Q)ˣ) : Q →L[ℝ] Q)‖
      ≤ ‖P‖ * ‖s‖ * (1 - ‖s‖ * η)⁻¹ := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    exact mul_le_mul hPS hBinv (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hRP : ‖stabilityR h - P‖
      ≤ ‖P‖ * ‖s‖ * (1 - ‖s‖ * η)⁻¹ * η := by
    rw [hsplit]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    refine mul_le_mul hPSB hqid (norm_nonneg _) ?_
    exact mul_nonneg
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hinv_nonneg
  have htri : ‖stabilityR h - E‖
      ≤ ‖stabilityR h - P‖ + ‖P - E‖ := by
    have hdec : stabilityR h - E = (stabilityR h - P) + (P - E) := by
      abel
    rw [hdec]
    exact norm_add_le _ _
  have hRP' : ‖stabilityR h - P‖
      ≤ ‖P‖ * (‖s‖ * η) / (1 - ‖s‖ * η) := by
    refine hRP.trans (le_of_eq ?_)
    rw [div_eq_mul_inv]
    ring
  linarith

end Stability

section Dynamics

omit [FiniteDimensional ℝ X] in
/-- **Corollary `cor:dynamics-stability` (one step)**: on the common
carrier `M = im P = im R` the compressed dynamics of two idempotents
differ by at most `‖P − R‖ ‖U_σ‖` in norm. -/
theorem dynamics_stability (U : X →L[ℝ] X) {P R : X →L[ℝ] X}
    (hP : P.comp P = P) (hR : R.comp R = R)
    (hrange : LinearMap.range ((R : X →L[ℝ] X) : X →ₗ[ℝ] X)
      = LinearMap.range ((P : X →L[ℝ] X) : X →ₗ[ℝ] X))
    {x : X}
    (hx : x ∈ LinearMap.range ((P : X →L[ℝ] X) : X →ₗ[ℝ] X)) :
    ‖(P.comp (U.comp P)) x - (R.comp (U.comp R)) x‖
      ≤ ‖P - R‖ * ‖U‖ * ‖x‖ := by
  have hPx : P x = x := by
    obtain ⟨y, rfl⟩ := hx
    exact congrFun (congrArg DFunLike.coe hP) y
  have hRx : R x = x := by
    rw [← hrange] at hx
    obtain ⟨y, hy⟩ := hx
    rw [← hy]
    exact congrFun (congrArg DFunLike.coe hR) y
  have hval : (P.comp (U.comp P)) x - (R.comp (U.comp R)) x
      = (P - R) (U x) := by
    change P (U (P x)) - R (U (R x)) = (P - R) (U x)
    rw [hPx, hRx, sub_apply]
  rw [hval]
  calc ‖(P - R) (U x)‖ ≤ ‖P - R‖ * ‖U x‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖P - R‖ * (‖U‖ * ‖x‖) := by
        gcongr
        exact ContinuousLinearMap.le_opNorm U x
    _ = ‖P - R‖ * ‖U‖ * ‖x‖ := by ring

/-- The telescoping bound for the difference of two ordered products
(sharp form, with the true norm of each tail product). -/
noncomputable def telescopeBound :
    List ((X →L[ℝ] X) × (X →L[ℝ] X)) → ℝ
  | [] => 0
  | p :: l => ‖p.1‖ * telescopeBound l
      + ‖p.1 - p.2‖ * ‖(l.map Prod.snd).prod‖

omit [FiniteDimensional ℝ X] in
/-- **Corollary `cor:dynamics-stability` (word estimate)**: the
difference of two ordered products of one-step maps is bounded by
the standard telescoping sum
`∑_j (∏_{k>j} ‖Φ̃_k‖) ‖Φ̃_j − Φ_j‖ (∏_{k<j} ‖Φ_k‖)` (stated in the
sharp form where each right factor is the norm of the actual tail
product, which is bounded by the product of norms). -/
theorem prod_sub_prod_norm_le :
    ∀ l : List ((X →L[ℝ] X) × (X →L[ℝ] X)),
      ‖(l.map Prod.fst).prod - (l.map Prod.snd).prod‖
        ≤ telescopeBound l
  | [] => by simp [telescopeBound]
  | p :: l => by
    have key : (((p :: l).map Prod.fst).prod)
        - (((p :: l).map Prod.snd).prod)
        = p.1 * ((l.map Prod.fst).prod - (l.map Prod.snd).prod)
          + (p.1 - p.2) * (l.map Prod.snd).prod := by
      simp only [List.map_cons, List.prod_cons]
      noncomm_ring
    rw [key]
    refine (norm_add_le _ _).trans ?_
    change _ ≤ ‖p.1‖ * telescopeBound l
      + ‖p.1 - p.2‖ * ‖(l.map Prod.snd).prod‖
    have h1 : ‖p.1 * ((l.map Prod.fst).prod - (l.map Prod.snd).prod)‖
        ≤ ‖p.1‖ * telescopeBound l :=
      (norm_mul_le _ _).trans (by
        gcongr
        exact prod_sub_prod_norm_le l)
    have h2 : ‖(p.1 - p.2) * (l.map Prod.snd).prod‖
        ≤ ‖p.1 - p.2‖ * ‖(l.map Prod.snd).prod‖ := norm_mul_le _ _
    linarith

end Dynamics

end NCG.Upstream
