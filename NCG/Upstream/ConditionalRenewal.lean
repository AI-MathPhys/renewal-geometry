/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.PrimitiveWeight
import NCG.Upstream.PathLaw

/-!
# Conditional predictive quotients and reference renewal

Covers `def:conditional-future-profile`, `lem:conditional-successor`,
`def:conditional-predictive-quotient`,
`def:reduced-resolved-realization`,
`thm:predictive-reference-renewal`, `cor:petz-reciprocal-weights`,
`def:tomographic-frame-constant` and
`thm:approximate-reference-renewal` from `manuscripts/renewal_emergence/renewal_emergence.tex`.

* Conditional profiles are success-normalized future weights
  `condProfile h F = ev F h / p h`; the successor congruence
  (`conditional_successor`) shows conditional equivalence is
  preserved by resolved continuations of positive weight, so the
  conditional quotient is **outcome unifilar**
  (`cond_successor_well_defined`).
* In a reduced resolved operator realization — future tests separate
  the reachable states (F3), and the normalized branch output
  represents the successor class (F1–F2), both taken in their
  operator form — branchwise reference renewal `E(ρₓ) = w·ρ_y` is
  **derived** (`predictive_reference_renewal`).
* The Petz reverse of the opposite branch has reference weight equal
  to the forward weight of that branch, `w_e⁻ = w_ē⁺`
  (`petz_reciprocal_weight`).
* With a tomographic frame constant (`IsFrameConstant`), approximate
  conditional sufficiency is quantitatively stable: one edge
  (`approximate_reference_renewal_edge`) and along every fixed path
  by telescoping (`approximate_reference_renewal_path`), taking the
  standard trace-norm contractivity of the CP branches as the
  disclosed hypothesis `hcontr`.
-/

namespace NCG

open Matrix
open scoped ComplexOrder

/-! ## Conditional future profiles and the successor congruence -/

section Conditional

variable {H : Type*} {Fexp : Type*}
variable (ev : Fexp → H → ℝ) (p : H → ℝ)

/-- **Definition `def:conditional-future-profile`**: the
success-normalized conditional future profile. -/
noncomputable def condProfile (h : H) : Fexp → ℝ :=
  fun F => ev F h / p h

/-- Conditional predictive equivalence of successful histories. -/
def CondEquiv (h h' : H) : Prop :=
  condProfile ev p h = condProfile ev p h'

/-- **Lemma `lem:conditional-successor`**: conditional equivalence is
preserved by appending a resolved continuation of positive weight.
The compositional structure is abstracted by `act` (pullback of
future experiments along the continuation) and `succF` (the success
test of the continuation). -/
theorem conditional_successor {E : Type*}
    (act : Fexp → E → Fexp) (app : E → H → H) (succF : E → Fexp)
    (hcomp : ∀ (F : Fexp) (e : E) (h : H),
      ev F (app e h) = ev (act F e) h)
    (hp : ∀ (e : E) (h : H), p (app e h) = ev (succF e) h)
    {h h' : H} (hph : p h ≠ 0) (hph' : p h' ≠ 0)
    (heq : CondEquiv ev p h h') (e : E)
    (hpe : p (app e h) ≠ 0) (hpe' : p (app e h') ≠ 0) :
    CondEquiv ev p (app e h) (app e h') := by
  funext F
  change ev F (app e h) / p (app e h) = ev F (app e h') / p (app e h')
  rw [hcomp F e h, hcomp F e h', hp e h, hp e h']
  have h3 : ev (succF e) h ≠ 0 := by
    rw [← hp e h]
    exact hpe
  have h4 : ev (succF e) h' ≠ 0 := by
    rw [← hp e h']
    exact hpe'
  have h1 : ev (act F e) h * p h' = ev (act F e) h' * p h := by
    have h5 := congrFun heq (act F e)
    rw [show condProfile ev p h (act F e)
        = ev (act F e) h / p h from rfl,
      show condProfile ev p h' (act F e)
        = ev (act F e) h' / p h' from rfl,
      div_eq_div_iff hph hph'] at h5
    exact h5
  have h2 : ev (succF e) h * p h' = ev (succF e) h' * p h := by
    have h5 := congrFun heq (succF e)
    rw [show condProfile ev p h (succF e)
        = ev (succF e) h / p h from rfl,
      show condProfile ev p h' (succF e)
        = ev (succF e) h' / p h' from rfl,
      div_eq_div_iff hph hph'] at h5
    exact h5
  rw [div_eq_div_iff h3 h4]
  have h6 : (ev (act F e) h * ev (succF e) h') * (p h * p h')
      = (ev (act F e) h' * ev (succF e) h) * (p h * p h') := by
    calc (ev (act F e) h * ev (succF e) h') * (p h * p h')
        = (ev (act F e) h * p h') * (ev (succF e) h' * p h) := by
          ring
      _ = (ev (act F e) h' * p h) * (ev (succF e) h * p h') := by
          rw [h1, ← h2]
      _ = (ev (act F e) h' * ev (succF e) h) * (p h * p h') := by
          ring
  exact mul_right_cancel₀ (mul_ne_zero hph hph') h6

/-- **Definition `def:conditional-predictive-quotient`**: successful
histories modulo conditional predictive equivalence. -/
def condSetoid : Setoid {h : H // 0 < p h} :=
  ⟨fun a b => CondEquiv ev p a.1 b.1,
    ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩

/-- The conditional predictive quotient `𝒬_cond`. -/
def CondClasses := Quotient (condSetoid ev p)

/-- **Outcome unifilarity** (`def:conditional-predictive-quotient`):
the successor of a class along a resolved outcome is well defined —
the current class and the observed outcome determine one successor
class. -/
theorem cond_successor_well_defined {E : Type*}
    (act : Fexp → E → Fexp) (app : E → H → H) (succF : E → Fexp)
    (hcomp : ∀ (F : Fexp) (e : E) (h : H),
      ev F (app e h) = ev (act F e) h)
    (hp : ∀ (e : E) (h : H), p (app e h) = ev (succF e) h)
    (h h' : {x : H // 0 < p x})
    (heq : Quotient.mk (condSetoid ev p) h
      = Quotient.mk (condSetoid ev p) h')
    (e : E) (hpe : 0 < p (app e h.1)) (hpe' : 0 < p (app e h'.1)) :
    Quotient.mk (condSetoid ev p)
        (⟨app e h.1, hpe⟩ : {x : H // 0 < p x})
      = Quotient.mk (condSetoid ev p) ⟨app e h'.1, hpe'⟩ := by
  refine Quotient.sound ?_
  exact conditional_successor ev p act app succF hcomp hp
    h.2.ne' h'.2.ne' (Quotient.exact heq) e hpe.ne' hpe'.ne'

end Conditional

/-! ## Reference renewal in reduced resolved realizations -/

section ReferenceRenewal

variable {dd : ℕ}

/-- **Theorem `thm:predictive-reference-renewal`**: in a reduced
resolved operator realization — the represented future tests
separate the reachable states (F3), and the normalized branch output
carries the conditional profile of the successor class, i.e. the
same test statistics as its reference state (F1)+(F2), both taken in
their operator form — every positive-weight branch renews the
reference state exactly: `E(ρₓ) = w·ρ_y`. -/
theorem predictive_reference_renewal
    (Tests : Set (Matrix (Fin dd) (Fin dd) ℂ))
    (Reach : Set (Matrix (Fin dd) (Fin dd) ℂ))
    (hsep : ∀ σ ∈ Reach, ∀ τ ∈ Reach,
      (∀ Q ∈ Tests, (σ * Q).trace = (τ * Q).trace) → σ = τ)
    {ρx ρy : Matrix (Fin dd) (Fin dd) ℂ}
    (E : Matrix (Fin dd) (Fin dd) ℂ →ₗ[ℂ]
      Matrix (Fin dd) (Fin dd) ℂ)
    {w : ℂ} (hw : w ≠ 0)
    (hnorm_mem : w⁻¹ • E ρx ∈ Reach) (hρy_mem : ρy ∈ Reach)
    (hstats : ∀ Q ∈ Tests,
      ((w⁻¹ • E ρx) * Q).trace = (ρy * Q).trace) :
    E ρx = w • ρy := by
  have h1 := hsep _ hnorm_mem _ hρy_mem hstats
  have h2 := congrArg (fun A => w • A) h1
  simpa [smul_smul, mul_inv_cancel₀ hw] using h2

/-! ### Complex positive square roots -/

/-- `ρ^{1/2}` of a positive-definite complex matrix. -/
noncomputable def csqrt {ρ : Matrix (Fin dd) (Fin dd) ℂ}
    (hρ : ρ.PosDef) : Matrix (Fin dd) (Fin dd) ℂ :=
  hρ.1.cfc Real.sqrt

/-- `ρ^{-1/2}` of a positive-definite complex matrix. -/
noncomputable def cinvsqrt {ρ : Matrix (Fin dd) (Fin dd) ℂ}
    (hρ : ρ.PosDef) : Matrix (Fin dd) (Fin dd) ℂ :=
  hρ.1.cfc fun x => (Real.sqrt x)⁻¹

theorem csqrt_mul_self {ρ : Matrix (Fin dd) (Fin dd) ℂ}
    (hρ : ρ.PosDef) : csqrt hρ * csqrt hρ = ρ := by
  unfold csqrt
  rw [Upstream.PrimitiveWeight.cfc_mul]
  have h1 : hρ.1.cfc (fun x => Real.sqrt x * Real.sqrt x)
      = hρ.1.cfc id :=
    Upstream.PrimitiveWeight.cfc_congr hρ.1 fun i =>
      Real.mul_self_sqrt (hρ.posSemidef.eigenvalues_nonneg i)
  rw [h1, Upstream.PrimitiveWeight.cfc_id']

theorem cinvsqrt_conj {ρ : Matrix (Fin dd) (Fin dd) ℂ}
    (hρ : ρ.PosDef) : cinvsqrt hρ * ρ * cinvsqrt hρ = 1 := by
  unfold cinvsqrt
  rw [Upstream.PrimitiveWeight.cfc_mul_self,
    Upstream.PrimitiveWeight.cfc_mul]
  have h1 : hρ.1.cfc
      (fun x => (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹)
      = hρ.1.cfc fun _ => (1 : ℝ) := by
    refine Upstream.PrimitiveWeight.cfc_congr hρ.1 fun i => ?_
    have hμ := hρ.eigenvalues_pos i
    have hs : 0 < Real.sqrt (hρ.1.eigenvalues i) :=
      Real.sqrt_pos.mpr hμ
    have hss := Real.mul_self_sqrt hμ.le
    field_simp
    linarith [hss]
  rw [h1, Upstream.PrimitiveWeight.cfc_const]
  simp

/-- **Corollary `cor:petz-reciprocal-weights` (boxed identity)**: the
reference weight of the Petz reverse of the opposite branch equals
the forward weight of that branch:
`w_e⁻ = Tr(Γ_{ρ_y}(E_ē^*(Γ_{ρ_x}^{-1}(ρ_x)))) = Tr(E_ē(ρ_y)) =
w_ē⁺`. -/
theorem petz_reciprocal_weight
    {ρx ρy : Matrix (Fin dd) (Fin dd) ℂ}
    (hρx : ρx.PosDef) (hρy : ρy.PosDef)
    (E Estar : Matrix (Fin dd) (Fin dd) ℂ →ₗ[ℂ]
      Matrix (Fin dd) (Fin dd) ℂ)
    (hadj : ∀ a b, (Estar a * b).trace = (a * E b).trace) :
    (csqrt hρy * Estar (cinvsqrt hρx * ρx * cinvsqrt hρx)
        * csqrt hρy).trace
      = (E ρy).trace := by
  rw [cinvsqrt_conj hρx]
  rw [Matrix.trace_mul_cycle, csqrt_mul_self hρy,
    Matrix.trace_mul_comm, hadj 1 ρy, Matrix.one_mul]

end ReferenceRenewal

/-! ## Tomographic frame constants and approximate renewal -/

section Approximate

open Upstream.PrimitiveWeight

variable {dd : ℕ}

/-- **Definition `def:tomographic-frame-constant`**: a constant
comparing the trace-norm distance of reachable states to their
maximal test deviation. -/
def IsFrameConstant (Tests : Finset (Matrix (Fin dd) (Fin dd) ℂ))
    (Reach : Set (Matrix (Fin dd) (Fin dd) ℂ)) (κ : ℝ) : Prop :=
  ∀ τ ∈ Reach, ∀ σ ∈ Reach, (τ - σ).IsHermitian →
    ∀ ε : ℝ, (∀ Q ∈ Tests, ‖((τ - σ) * Q).trace‖ ≤ ε) →
      trNorm (τ - σ) ≤ κ * ε

/-- Trace-norm triangle inequality (from the duality achiever). -/
theorem trNorm_add_le {A B : Matrix (Fin dd) (Fin dd) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    trNorm (A + B) ≤ trNorm A + trNorm B := by
  have hAB : (A + B).IsHermitian := hA.add hB
  have h1 := re_trace_signOp_mul hAB
  have h2 : signOp hAB * (A + B) = signOp hAB * A + signOp hAB * B :=
    mul_add _ _ _
  have h3 : RCLike.re ((signOp hAB * (A + B)).trace)
      = RCLike.re ((signOp hAB * A).trace)
        + RCLike.re ((signOp hAB * B).trace) := by
    rw [h2, Matrix.trace_add, map_add]
  have h4 := re_trace_mul_le_trNorm hA
    (one_sub_signOp_posSemidef hAB) (one_add_signOp_posSemidef hAB)
  have h5 := re_trace_mul_le_trNorm hB
    (one_sub_signOp_posSemidef hAB) (one_add_signOp_posSemidef hAB)
  linarith [h1, h3, h4, h5]

/-- **Theorem `thm:approximate-reference-renewal` (one edge)**. -/
theorem approximate_reference_renewal_edge
    (Tests : Finset (Matrix (Fin dd) (Fin dd) ℂ))
    (Reach : Set (Matrix (Fin dd) (Fin dd) ℂ)) {κ : ℝ}
    (hκ : IsFrameConstant Tests Reach κ)
    {ρx ρy : Matrix (Fin dd) (Fin dd) ℂ}
    (E : Matrix (Fin dd) (Fin dd) ℂ →ₗ[ℂ]
      Matrix (Fin dd) (Fin dd) ℂ)
    {w : ℝ} (hw : 0 < w)
    (hmem1 : ((w : ℂ)⁻¹ • E ρx) ∈ Reach) (hmem2 : ρy ∈ Reach)
    (hherm : ((w : ℂ)⁻¹ • E ρx - ρy).IsHermitian)
    {ε : ℝ}
    (hε : ∀ Q ∈ Tests, ‖(((w : ℂ)⁻¹ • E ρx - ρy) * Q).trace‖ ≤ ε) :
    trNorm (E ρx - (w : ℂ) • ρy) ≤ w * (κ * ε) := by
  have h1 := hκ _ hmem1 _ hmem2 hherm ε hε
  have h2 : E ρx - (w : ℂ) • ρy
      = ((w : ℝ) : ℂ) • ((w : ℂ)⁻¹ • E ρx - ρy) := by
    have hwc : ((w : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hwc, one_smul]
  calc trNorm (E ρx - (w : ℂ) • ρy)
      = trNorm (((w : ℝ) : ℂ) • ((w : ℂ)⁻¹ • E ρx - ρy)) := by
        rw [h2]
    _ = w * trNorm ((w : ℂ)⁻¹ • E ρx - ρy) :=
        trNorm_smul_pos hherm hw
    _ ≤ w * (κ * ε) := mul_le_mul_of_nonneg_left h1 hw.le

/-- **Theorem `thm:approximate-reference-renewal` (path bound)**:
telescoping the one-edge bounds along a fixed resolved history.  The
cumulative weights `W_k = ∏_{j≤k} w_j` enter through their recursion;
the standard trace-norm contractivity of the CP branches on Hermitian
differences is the disclosed hypothesis `hcontr` (provable from
positivity and trace preservation via the same duality; not
re-derived here). -/
theorem approximate_reference_renewal_path :
    ∀ (n : ℕ) (ρ : Fin (n + 1) → Matrix (Fin dd) (Fin dd) ℂ)
      (E : Fin n → (Matrix (Fin dd) (Fin dd) ℂ →ₗ[ℂ]
        Matrix (Fin dd) (Fin dd) ℂ))
      (w η : Fin n → ℝ) (W : Fin (n + 1) → ℝ),
      W 0 = 1 →
      (∀ i : Fin n, W i.succ = W i.castSucc * w i) →
      (∀ i : Fin (n + 1), 0 < W i) →
      (∀ i, 0 < w i) → (∀ i, (0:ℝ) ≤ η i) →
      (∀ i (A : Matrix (Fin dd) (Fin dd) ℂ),
        A.IsHermitian → (E i A).IsHermitian) →
      (∀ i, (ρ i).IsHermitian) →
      (∀ i (A : Matrix (Fin dd) (Fin dd) ℂ), A.IsHermitian →
        trNorm (E i A) ≤ trNorm A) →
      (∀ i : Fin n,
        trNorm (E i (ρ i.castSucc) - (w i : ℂ) • ρ i.succ)
          ≤ w i * η i) →
      trNorm (pathComp n E (ρ 0)
          - ((W (Fin.last n) : ℝ) : ℂ) • ρ (Fin.last n))
        ≤ ∑ i : Fin n, W i.succ * η i := by
  intro n
  induction n with
  | zero =>
    intro ρ E w η W hW0 _ _ _ _ _ _ _ _
    simp only [pathComp_zero, LinearMap.id_coe, id_eq]
    have h0 : ρ 0 - ((W (Fin.last 0) : ℝ) : ℂ) • ρ (Fin.last 0)
        = 0 := by
      have h1 : Fin.last 0 = 0 := rfl
      rw [h1, hW0]
      push_cast
      rw [one_smul, sub_self]
    rw [h0, show trNorm (0 : Matrix (Fin dd) (Fin dd) ℂ) = 0 from
      (trNorm_eq_zero_iff isHermitian_zero).mpr rfl]
    simp
  | succ m ih =>
    intro ρ E w η W hW0 hWrec hWpos hw hη hEherm hρherm hcontr hedge
    -- truncated cumulative weights satisfy the same recursion
    have hW'0 : W ((0 : Fin (m + 1)).castSucc) = 1 := by
      rw [show ((0 : Fin (m + 1)).castSucc) = (0 : Fin (m + 2))
        from by simp]
      exact hW0
    have hW'rec : ∀ i : Fin m,
        W ((i.succ).castSucc) = W ((i.castSucc).castSucc)
          * w i.castSucc := by
      intro i
      rw [← Fin.succ_castSucc]
      exact hWrec i.castSucc
    have hIH := ih (fun i => ρ i.castSucc) (fun i => E i.castSucc)
      (fun i => w i.castSucc) (fun i => η i.castSucc)
      (fun i => W i.castSucc) hW'0 hW'rec
      (fun i => hWpos i.castSucc)
      (fun i => hw i.castSucc) (fun i => hη i.castSucc)
      (fun i => hEherm i.castSucc) (fun i => hρherm i.castSucc)
      (fun i => hcontr i.castSucc)
      (fun i => by
        have h1 := hedge i.castSucc
        rw [show (i.castSucc).succ = (i.succ).castSucc from
          (Fin.succ_castSucc i).symm] at h1
        exact h1)
    -- hermiticity of accumulated maps
    have hprevherm : ∀ (A : Matrix (Fin dd) (Fin dd) ℂ),
        A.IsHermitian →
        (pathComp m (fun i => E i.castSucc) A).IsHermitian := by
      have haux : ∀ (k : ℕ)
          (Ek : Fin k → (Matrix (Fin dd) (Fin dd) ℂ →ₗ[ℂ]
            Matrix (Fin dd) (Fin dd) ℂ)),
          (∀ i (A : Matrix (Fin dd) (Fin dd) ℂ), A.IsHermitian →
            (Ek i A).IsHermitian) →
          ∀ A : Matrix (Fin dd) (Fin dd) ℂ, A.IsHermitian →
            (pathComp k Ek A).IsHermitian := by
        intro k
        induction k with
        | zero =>
          intro Ek _ A hA
          simpa [pathComp_zero] using hA
        | succ j ihj =>
          intro Ek hEk A hA
          rw [pathComp_succ]
          exact hEk (Fin.last j) _
            (ihj (fun i => Ek i.castSucc)
              (fun i => hEk i.castSucc) A hA)
      exact haux m _ (fun i => hEherm i.castSucc)
    -- the split of the (m+1)-step defect
    have hz : ρ (Fin.castSucc (0 : Fin (m + 1))) = ρ 0 := by
      rw [Fin.castSucc_zero]
    have hWlast : W (Fin.last (m + 1))
        = W ((Fin.last m).castSucc) * w (Fin.last m) := by
      rw [show Fin.last (m + 1) = (Fin.last m).succ from
        (Fin.succ_last m).symm]
      exact hWrec (Fin.last m)
    have hsplit : pathComp (m + 1) E (ρ 0)
        - ((W (Fin.last (m + 1)) : ℝ) : ℂ) • ρ (Fin.last (m + 1))
        = E (Fin.last m) (pathComp m (fun i => E i.castSucc) (ρ 0)
            - ((W ((Fin.last m).castSucc) : ℝ) : ℂ)
              • ρ (Fin.last m).castSucc)
          + ((W ((Fin.last m).castSucc) : ℝ) : ℂ)
            • (E (Fin.last m) (ρ (Fin.last m).castSucc)
              - (w (Fin.last m) : ℂ) • ρ (Fin.last m).succ) := by
      rw [pathComp_succ, hWlast]
      simp only [LinearMap.comp_apply, map_sub, map_smul, smul_sub,
        smul_smul]
      rw [show Fin.last (m + 1) = (Fin.last m).succ from
        (Fin.succ_last m).symm]
      push_cast
      abel
    rw [hsplit]
    -- hermiticity of the two summands
    have hd1herm : (pathComp m (fun i => E i.castSucc) (ρ 0)
        - ((W ((Fin.last m).castSucc) : ℝ) : ℂ)
          • ρ (Fin.last m).castSucc).IsHermitian :=
      (hprevherm _ (hρherm 0)).sub
        (Upstream.PrimitiveWeight.isHermitian_real_smul
          (hρherm (Fin.last m).castSucc) _)
    have hd2herm : (E (Fin.last m) (ρ (Fin.last m).castSucc)
        - (w (Fin.last m) : ℂ)
          • ρ (Fin.last m).succ).IsHermitian :=
      (hEherm (Fin.last m) _ (hρherm (Fin.last m).castSucc)).sub
        (Upstream.PrimitiveWeight.isHermitian_real_smul
          (hρherm (Fin.last m).succ) _)
    have htri := trNorm_add_le
      (hEherm (Fin.last m) _ hd1herm)
      (Upstream.PrimitiveWeight.isHermitian_real_smul hd2herm
        (W ((Fin.last m).castSucc)))
    refine le_trans htri ?_
    -- first term: contraction then the inductive bound
    have hb1 : trNorm (E (Fin.last m)
        (pathComp m (fun i => E i.castSucc) (ρ 0)
          - ((W ((Fin.last m).castSucc) : ℝ) : ℂ)
            • ρ (Fin.last m).castSucc))
        ≤ ∑ i : Fin m, W ((i.succ).castSucc) * η i.castSucc := by
      refine le_trans (hcontr (Fin.last m) _ hd1herm) ?_
      rw [hz] at hIH
      exact hIH
    -- second term: homogeneity and the last edge bound
    have hb2 : trNorm (((W ((Fin.last m).castSucc) : ℝ) : ℂ)
        • (E (Fin.last m) (ρ (Fin.last m).castSucc)
          - (w (Fin.last m) : ℂ) • ρ (Fin.last m).succ))
        ≤ W ((Fin.last m).castSucc)
          * (w (Fin.last m) * η (Fin.last m)) := by
      calc trNorm (((W ((Fin.last m).castSucc) : ℝ) : ℂ)
          • (E (Fin.last m) (ρ (Fin.last m).castSucc)
            - (w (Fin.last m) : ℂ) • ρ (Fin.last m).succ))
          = W ((Fin.last m).castSucc)
            * trNorm (E (Fin.last m) (ρ (Fin.last m).castSucc)
              - (w (Fin.last m) : ℂ) • ρ (Fin.last m).succ) :=
            trNorm_smul_pos hd2herm (hWpos (Fin.last m).castSucc)
        _ ≤ W ((Fin.last m).castSucc)
            * (w (Fin.last m) * η (Fin.last m)) :=
            mul_le_mul_of_nonneg_left (hedge (Fin.last m))
              (hWpos (Fin.last m).castSucc).le
    refine le_trans (add_le_add hb1 hb2) ?_
    -- assemble the sums
    rw [Fin.sum_univ_castSucc]
    have hlastw : W ((Fin.last m).castSucc) * (w (Fin.last m)
        * η (Fin.last m))
        = W ((Fin.last m).succ) * η (Fin.last m) := by
      rw [hWrec (Fin.last m)]
      ring
    rw [hlastw]
    refine le_of_eq ?_
    congr 1

end Approximate

end NCG
