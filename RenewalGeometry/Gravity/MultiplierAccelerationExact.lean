/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Original-action multiplier acceleration and exact elimination of the active acceleration
  (`prop:supp-exact-action-acceleration`, `eq:supp-exact-action-acceleration`,
  `prop:supp-finite-acc-schur`, `eq:supp-finite-acc-mass`,
  `eq:supp-finite-acc-effective`, `eq:supp-finite-acc-elimination`;
  emergent-spacetime manuscript)

## Multiplier acceleration (`prop:supp-exact-action-acceleration`)

On the normalized multiplier slice the consistency relation
`𝓑(Q) + 𝓜(Q) r = 0` (`eq:supp-exact-original-consistency`) holds along the
exact physical solution `t ↦ (Q(t), r(t))`, whose configuration velocity is
`Q̇ = V` (the paper's `V = (F^can, r)`).  `multiplier_acceleration`
differentiates this identity (chain rule and product rule for the
operator-valued mass) and proves `eq:supp-exact-action-acceleration`
`𝓜 ṙ = -D_Q𝓑[V] - D_Q𝓜[V] r`, for arbitrary normed spaces and
Fréchet-differentiable `𝓑`, `𝓜`; `multiplier_acceleration_solve` solves it for
`ṙ` where `𝓜` is invertible.  The interpretive sentence of the proposition
(the source is the directional derivative of the unchanged finite action) is
the reading of `𝓑`, `𝓜` as the derivatives of that action, which enter here as
parameters.

## Exact Schur elimination (`prop:supp-finite-acc-schur`)

With the amplitude-graded mass
`𝓜_a = [[a² A, a³ L], [a³ Lᵀ, a⁴ C]]` (`eq:supp-finite-acc-mass`), the Schur
complement `D = C - Lᵀ A⁻¹ L`, the effective source `χ = S_W - a Lᵀ A⁻¹ S_A`
and `v = D⁻¹ χ` (`eq:supp-finite-acc-effective`), every solution of the
acceleration equation `𝓜_a λ_tt = -𝓢_a` satisfies
`λ_tt,W = -a⁻⁴ v`, `λ_tt,A = -a⁻² A⁻¹ S_A + a⁻³ A⁻¹ L v`
(`eq:supp-finite-acc-elimination`): `finite_acc_schur_elimination` at every
amplitude `a ≠ 0` where `A(a)` and `D(a)` are invertible, and
`finite_acc_schur_eventually`, which derives that invertibility for all small
`a ≠ 0` from the paper's hypothesis that `A(0)` and `D(0)` are invertible
(only continuity of the family at `a = 0` is used; the paper's family is
analytic), via `det 𝓜 = det A · det D` and continuity of the determinant.
-/

namespace RenewalGeometry
namespace MultiplierAcceleration

open Matrix Filter Topology

section Acceleration

variable {E Fr Fb : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Fr] [NormedSpace ℝ Fr] [NormedAddCommGroup Fb] [NormedSpace ℝ Fb]

/-- **Original-action multiplier acceleration** (`prop:supp-exact-action-acceleration`,
`eq:supp-exact-action-acceleration`).  If the consistency relation
`𝓑(Q(s)) + 𝓜(Q(s)) r(s) = 0` holds for `s` near `t` along a trajectory with
`Q̇(t) = V` and `ṙ(t) = rdot`, and `𝓑`, `𝓜` are differentiable at `Q(t)`, then
`𝓜(Q) ṙ = -D_Q𝓑[V] - D_Q𝓜[V] r`. -/
theorem multiplier_acceleration (B : E → Fb) (M : E → (Fr →L[ℝ] Fb)) (Q : ℝ → E)
    (r : ℝ → Fr) (t : ℝ) (B' : E →L[ℝ] Fb) (M' : E →L[ℝ] (Fr →L[ℝ] Fb)) (V : E)
    (rdot : Fr) (hB : HasFDerivAt B B' (Q t)) (hM : HasFDerivAt M M' (Q t))
    (hQ : HasDerivAt Q V t) (hr : HasDerivAt r rdot t)
    (hcons : ∀ᶠ s in 𝓝 t, B (Q s) + M (Q s) (r s) = 0) :
    M (Q t) rdot = -B' V - M' V (r t) := by
  have h1 : HasDerivAt (fun s => B (Q s)) (B' V) t := hB.comp_hasDerivAt t hQ
  have h2 : HasDerivAt (fun s => M (Q s)) (M' V) t := hM.comp_hasDerivAt t hQ
  have h3 : HasDerivAt (fun s => M (Q s) (r s)) (M' V (r t) + M (Q t) rdot) t := h2.clm_apply hr
  have h4 := h1.add h3
  have h0 : HasDerivAt (fun s => B (Q s) + M (Q s) (r s)) 0 t :=
    (hasDerivAt_const t (0 : Fb)).congr_of_eventuallyEq hcons
  have := h4.unique h0
  calc M (Q t) rdot = (B' V + (M' V (r t) + M (Q t) rdot)) - B' V - M' V (r t) := by abel
    _ = -B' V - M' V (r t) := by rw [this]; abel

/-- `eq:supp-exact-action-acceleration` solved for the acceleration where the
multiplier mass is invertible: `ṙ = -𝓜⁻¹ (D_Q𝓑[V] + D_Q𝓜[V] r)`
(`prop:supp-exact-action-acceleration`). -/
theorem multiplier_acceleration_solve (B : E → Fb) (M : E → (Fr →L[ℝ] Fb)) (Q : ℝ → E)
    (r : ℝ → Fr) (t : ℝ) (B' : E →L[ℝ] Fb) (M' : E →L[ℝ] (Fr →L[ℝ] Fb)) (V : E)
    (rdot : Fr) (hB : HasFDerivAt B B' (Q t)) (hM : HasFDerivAt M M' (Q t))
    (hQ : HasDerivAt Q V t) (hr : HasDerivAt r rdot t)
    (hcons : ∀ᶠ s in 𝓝 t, B (Q s) + M (Q s) (r s) = 0)
    (e : Fr ≃L[ℝ] Fb) (he : M (Q t) = (e : Fr →L[ℝ] Fb)) :
    rdot = -e.symm (B' V + M' V (r t)) := by
  have h := multiplier_acceleration B M Q r t B' M' V rdot hB hM hQ hr hcons
  rw [he, ContinuousLinearEquiv.coe_coe] at h
  rw [← map_neg, ← ContinuousLinearEquiv.symm_apply_apply e rdot, h, neg_add]
  abel_nf

end Acceleration

section Schur

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **Exact elimination of the active acceleration** (`prop:supp-finite-acc-schur`,
`eq:supp-finite-acc-elimination`) at an amplitude `a ≠ 0` where `A` and the
Schur complement `D = C - Lᵀ A⁻¹ L` are invertible: every solution
`λ_tt = (λ_A, λ_W)` of `𝓜_a λ_tt = -(S_A, S_W)` with
`𝓜_a = [[a² A, a³ L], [a³ Lᵀ, a⁴ C]]` satisfies `λ_W = -a⁻⁴ v` and
`λ_A = -a⁻² A⁻¹ S_A + a⁻³ A⁻¹ L v`, where `χ = S_W - a Lᵀ A⁻¹ S_A` and
`v = D⁻¹ χ`. -/
theorem finite_acc_schur_elimination (a : ℝ) (ha : a ≠ 0) (A : Matrix m m ℝ)
    (L : Matrix m n ℝ) (C : Matrix n n ℝ)
    (hA : IsUnit A.det) (hD : IsUnit (C - Lᵀ * A⁻¹ * L).det)
    (SA lA : m → ℝ) (SW lW : n → ℝ)
    (hacc : fromBlocks (a ^ 2 • A) (a ^ 3 • L) (a ^ 3 • Lᵀ) (a ^ 4 • C) *ᵥ Sum.elim lA lW
      = -Sum.elim SA SW) :
    lW = -(a ^ 4)⁻¹ • ((C - Lᵀ * A⁻¹ * L)⁻¹ *ᵥ (SW - a • (Lᵀ * A⁻¹) *ᵥ SA)) ∧
    lA = -(a ^ 2)⁻¹ • (A⁻¹ *ᵥ SA)
      + (a ^ 3)⁻¹ • ((A⁻¹ * L) *ᵥ ((C - Lᵀ * A⁻¹ * L)⁻¹ *ᵥ (SW - a • (Lᵀ * A⁻¹) *ᵥ SA))) := by
  set D := C - Lᵀ * A⁻¹ * L with hDdef
  set χ := SW - a • (Lᵀ * A⁻¹) *ᵥ SA with hχ
  rw [fromBlocks_mulVec] at hacc
  have r1 : a ^ 2 • A *ᵥ lA + a ^ 3 • L *ᵥ lW = -SA := by
    ext i
    have := congrFun hacc (Sum.inl i)
    simpa [smul_mulVec] using this
  have r2 : a ^ 3 • Lᵀ *ᵥ lA + a ^ 4 • C *ᵥ lW = -SW := by
    ext i
    have := congrFun hacc (Sum.inr i)
    simpa [smul_mulVec] using this
  -- active row solved
  have hAA : A⁻¹ * A = 1 := nonsing_inv_mul A hA
  have r1' : a ^ 2 • lA + a ^ 3 • (A⁻¹ * L) *ᵥ lW = -(A⁻¹ *ᵥ SA) := by
    have := congrArg (fun v => A⁻¹ *ᵥ v) r1
    simp only [mulVec_add, mulVec_smul, mulVec_mulVec, hAA, one_mulVec, mulVec_neg] at this
    exact this
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  have hlA : lA = -(a ^ 2)⁻¹ • (A⁻¹ *ᵥ SA) - a • (A⁻¹ * L) *ᵥ lW := by
    have e : lA = (a ^ 2)⁻¹ • (a ^ 2 • lA) := (inv_smul_smul₀ ha2 lA).symm
    rw [e, eq_sub_of_add_eq r1', smul_sub, smul_smul]
    have : (a ^ 2)⁻¹ * a ^ 3 = a := by field_simp
    rw [this, smul_neg, neg_smul]
  -- weak row
  have r2' : a ^ 4 • D *ᵥ lW = -χ := by
    rw [hlA] at r2
    simp only [mulVec_sub, mulVec_smul, mulVec_mulVec, mulVec_neg, smul_sub,
      smul_neg, smul_smul, neg_smul] at r2
    have e1 : a ^ 3 * (a ^ 2)⁻¹ = a := by field_simp
    have e2 : a ^ 3 * a = a ^ 4 := by ring
    rw [e1, e2, ← Matrix.mul_assoc] at r2
    rw [hDdef, hχ, sub_mulVec]
    linear_combination (norm := module) r2
  have hDD : D⁻¹ * D = 1 := nonsing_inv_mul D hD
  have ha4 : a ^ 4 ≠ 0 := pow_ne_zero 4 ha
  have hlW : lW = -(a ^ 4)⁻¹ • (D⁻¹ *ᵥ χ) := by
    have h4 : a ^ 4 • lW = -(D⁻¹ *ᵥ χ) := by
      have := congrArg (fun v => D⁻¹ *ᵥ v) r2'
      simp only [mulVec_smul, mulVec_mulVec, hDD, one_mulVec, mulVec_neg] at this
      exact this
    have e : lW = (a ^ 4)⁻¹ • (a ^ 4 • lW) := (inv_smul_smul₀ ha4 lW).symm
    rw [e, h4, smul_neg, neg_smul]
  refine ⟨hlW, ?_⟩
  rw [hlA, hlW]
  simp only [mulVec_smul, smul_smul]
  have : a * -(a ^ 4)⁻¹ = -(a ^ 3)⁻¹ := by field_simp
  rw [this]
  module

/-- Invertibility of `A(a)` and `D(a) = C(a) - L(a)ᵀ A(a)⁻¹ L(a)` for all small
amplitudes, from invertibility of `A(0)` and `D(0)` and continuity of the
family at `a = 0` (`prop:supp-finite-acc-schur`, hypothesis). -/
theorem schur_blocks_eventually_invertible (A : ℝ → Matrix m m ℝ) (L : ℝ → Matrix m n ℝ)
    (C : ℝ → Matrix n n ℝ)
    (hAc : ContinuousAt A 0) (hLc : ContinuousAt L 0) (hCc : ContinuousAt C 0)
    (hA0 : IsUnit (A 0).det) (hD0 : IsUnit (C 0 - (L 0)ᵀ * (A 0)⁻¹ * L 0).det) :
    ∀ᶠ a in 𝓝 (0 : ℝ), IsUnit (A a).det ∧ IsUnit (C a - (L a)ᵀ * (A a)⁻¹ * L a).det := by
  have hschur : ∀ a, IsUnit (A a).det →
      (fromBlocks (A a) (L a) (L a)ᵀ (C a)).det
        = (A a).det * (C a - (L a)ᵀ * (A a)⁻¹ * L a).det := by
    intro a ha
    let _ := invertibleOfIsUnitDet (A a) ha
    rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  have gcont : Continuous fun p : Matrix m m ℝ × Matrix m n ℝ × Matrix n n ℝ =>
      (fromBlocks p.1 p.2.1 p.2.1ᵀ p.2.2).det :=
    (continuous_fst.matrix_fromBlocks continuous_snd.fst continuous_snd.fst.matrix_transpose
      continuous_snd.snd).matrix_det
  have hblk : ContinuousAt (fun a => (fromBlocks (A a) (L a) (L a)ᵀ (C a)).det) 0 :=
    gcont.continuousAt.comp (f := fun a => (A a, L a, C a)) (hAc.prodMk (hLc.prodMk hCc))
  have hdetA : ContinuousAt (fun a => (A a).det) 0 :=
    (continuous_id.matrix_det).continuousAt.comp (f := A) hAc
  have e1 : ∀ᶠ a in 𝓝 (0 : ℝ), (A a).det ≠ 0 := hdetA.eventually_ne hA0.ne_zero
  have e2 : ∀ᶠ a in 𝓝 (0 : ℝ), (fromBlocks (A a) (L a) (L a)ᵀ (C a)).det ≠ 0 :=
    hblk.eventually_ne (by rw [hschur 0 hA0]; exact mul_ne_zero hA0.ne_zero hD0.ne_zero)
  filter_upwards [e1, e2] with a ha hb
  have hu : IsUnit (A a).det := isUnit_iff_ne_zero.mpr ha
  refine ⟨hu, isUnit_iff_ne_zero.mpr fun hz => hb ?_⟩
  rw [hschur a hu, hz, mul_zero]

/-- **Exact elimination of the active acceleration** (`prop:supp-finite-acc-schur`)
on the initial family: if `A(0)` and `D(0)` are invertible and the mass blocks
are continuous at `a = 0`, then for every sufficiently small amplitude `a ≠ 0`
every solution of the acceleration equation `𝓜_a λ_tt = -𝓢_a` satisfies
`eq:supp-finite-acc-elimination`. -/
theorem finite_acc_schur_eventually (A : ℝ → Matrix m m ℝ) (L : ℝ → Matrix m n ℝ)
    (C : ℝ → Matrix n n ℝ)
    (hAc : ContinuousAt A 0) (hLc : ContinuousAt L 0) (hCc : ContinuousAt C 0)
    (hA0 : IsUnit (A 0).det) (hD0 : IsUnit (C 0 - (L 0)ᵀ * (A 0)⁻¹ * L 0).det) :
    ∀ᶠ a in 𝓝[≠] (0 : ℝ), ∀ (SA lA : m → ℝ) (SW lW : n → ℝ),
      fromBlocks (a ^ 2 • A a) (a ^ 3 • L a) (a ^ 3 • (L a)ᵀ) (a ^ 4 • C a)
          *ᵥ Sum.elim lA lW = -Sum.elim SA SW →
      lW = -(a ^ 4)⁻¹ • ((C a - (L a)ᵀ * (A a)⁻¹ * L a)⁻¹
              *ᵥ (SW - a • ((L a)ᵀ * (A a)⁻¹) *ᵥ SA)) ∧
      lA = -(a ^ 2)⁻¹ • ((A a)⁻¹ *ᵥ SA)
        + (a ^ 3)⁻¹ • (((A a)⁻¹ * L a) *ᵥ ((C a - (L a)ᵀ * (A a)⁻¹ * L a)⁻¹
              *ᵥ (SW - a • ((L a)ᵀ * (A a)⁻¹) *ᵥ SA))) := by
  have hev := schur_blocks_eventually_invertible A L C hAc hLc hCc hA0 hD0
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with a hinv hne
  intro SA lA SW lW hacc
  exact finite_acc_schur_elimination a hne (A a) (L a) (C a) hinv.1 hinv.2 SA lA SW lW hacc

end Schur

end MultiplierAcceleration
end RenewalGeometry
