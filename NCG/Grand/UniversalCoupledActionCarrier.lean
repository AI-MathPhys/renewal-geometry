/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExactSourceSchurResidual
import NCG.Grand.EdgeActionPythagoras
import NCG.Grand.FiniteBRSTWardEinstein
import NCG.Grand.K4BridgeTransparency

/-!
# Universal finite gravity--internal action carrier

This file assembles the finite, source-minimal content of
`thm:SMST-universal-coupled-action`.  The same-history common carrier is the
Schur quotient of the joint source Gram, rather than the direct sum of two
separately minimal carriers.  The file also records the independent whitened
branch, the finite Ward/BRST/stress output, the centred vacuum zero, the
one-point Perron loading, and the finite-fibre screen bound.
-/

open Matrix Kronecker
open scoped ComplexOrder

namespace NCG

/-- The source-minimal internal variation space (CA.3). -/
noncomputable def sourceMinimalInternalVariation {h eg ei : ℕ}
    (Sg : Matrix (Fin h) (Fin eg) ℂ)
    (Si : Matrix (Fin h) (Fin ei) ℂ) :=
  (Fin ei → ℂ) ⧸ LinearMap.ker (Matrix.mulVecLin (sourceSchurResidual Sg Si))

/-- On a faithful gravitational source, the spectral Gram pseudoinverse is
the ordinary inverse used in the manuscript's CA.1 formula. -/
theorem sourceGramPseudoinverse_eq_inv_of_posDef {h e : ℕ}
    (S : Matrix (Fin h) (Fin e) ℂ) (hG : (Sᴴ * S).PosDef) :
    sourceGramPseudoinverse S = (Sᴴ * S)⁻¹ := by
  let G : Matrix (Fin e) (Fin e) ℂ := Sᴴ * S
  let J : Matrix (Fin e) (Fin e) ℂ := sourceGramPseudoinverse S
  haveI := hG.isUnit.invertible
  have hpenrose : G * J * G = G :=
    (sourceGramPseudoinverse_projection S).2.1
  calc
    J = 1 * J * 1 := by simp
    _ = (G⁻¹ * G) * J * (G * G⁻¹) := by
      rw [Matrix.inv_mul_of_invertible, Matrix.mul_inv_of_invertible]
    _ = G⁻¹ * (G * J * G) * G⁻¹ := by
      simp only [Matrix.mul_assoc]
    _ = G⁻¹ * G * G⁻¹ := by rw [hpenrose]
    _ = G⁻¹ := by rw [Matrix.inv_mul_of_invertible, Matrix.one_mul]

/-- CA.1 and CA.2: exact orthogonal-residual formula and faithful-source
block LDU factorization. -/
theorem coupledSourceSchur_factorization {h eg ei : ℕ}
    (Sg : Matrix (Fin h) (Fin eg) ℂ)
    (Si : Matrix (Fin h) (Fin ei) ℂ)
    (hGg : (Sgᴴ * Sg).PosDef) :
    let Gg := Sgᴴ * Sg
    let B := Sgᴴ * Si
    let Gi := Siᴴ * Si
    let R := Gi - Bᴴ * Gg⁻¹ * B
    R = sourceSchurResidual Sg Si
    ∧ R = Siᴴ * (1 - sourceRangeProjection Sg) * Si
    ∧ Matrix.fromBlocks Gg B Bᴴ Gi
        = Matrix.fromBlocks 1 0 ((Gg⁻¹ * B)ᴴ) 1
          * Matrix.fromBlocks Gg 0 0 R
          * Matrix.fromBlocks 1 (Gg⁻¹ * B) 0 1
    ∧ R.PosSemidef
    ∧ (Matrix.fromBlocks Gg B Bᴴ Gi).rank - Gg.rank = R.rank := by
  dsimp
  have hJ := sourceGramPseudoinverse_eq_inv_of_posDef Sg hGg
  have hR : Siᴴ * Si - (Sgᴴ * Si)ᴴ * (Sgᴴ * Sg)⁻¹ * (Sgᴴ * Si)
      = sourceSchurResidual Sg Si := by
    simp only [sourceSchurResidual, hJ]
  have hGram :
      (Matrix.fromBlocks (Sgᴴ * Sg) (Sgᴴ * Si)
        ((Sgᴴ * Si)ᴴ) (Siᴴ * Si)).PosSemidef := by
    let S : Matrix (Fin h) (Fin eg ⊕ Fin ei) ℂ := Matrix.fromCols Sg Si
    have hs : Sᴴ * S = Matrix.fromBlocks (Sgᴴ * Sg) (Sgᴴ * Si)
        ((Sgᴴ * Si)ᴴ) (Siᴴ * Si) := by
      dsimp [S]
      rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
        Matrix.fromRows_mul_fromCols]
      simp
    rw [← hs]
    exact Matrix.posSemidef_conjTranspose_mul_self S
  have hfac := connected_edge_action_pythagoras
    (Sgᴴ * Sg) (-(Sgᴴ * Si)) (Siᴴ * Si) hGg (by simpa using hGram)
  refine ⟨hR, ?_, ?_, ?_, ?_⟩
  · rw [hR]
    exact sourceSchurResidual_eq_orthogonalResidual Sg Si
  · simpa only [neg_neg, Matrix.conjTranspose_neg, Matrix.mul_neg,
      Matrix.neg_mul, Matrix.conjTranspose_mul] using hfac.1
  · rw [hR]
    exact sourceSchurResidual_posSemidef Sg Si
  · rw [hR]
    exact sourceSchurResidual_rank_increment Sg Si

/-- CA.4: zero mixed covariance and whitening make the internal Schur residual
the identity.  These are precisely the two covariance facts supplied by an
independent centred, whitened intervention bank. -/
theorem independentWhitenedInternalBranch {h eg ei : ℕ}
    (Sg : Matrix (Fin h) (Fin eg) ℂ)
    (Si : Matrix (Fin h) (Fin ei) ℂ)
    (hcentered : Sgᴴ * Si = 0) (hwhite : Siᴴ * Si = 1) :
    Siᴴ * Sg = 0 ∧ sourceSchurResidual Sg Si = 1 := by
  have hcross : Siᴴ * Sg = 0 := by
    have := congrArg Matrix.conjTranspose hcentered
    simpa using this
  refine ⟨hcross, ?_⟩
  simp [sourceSchurResidual, hcentered, hwhite]

/-- A centred positive finite graph action.  Its coordinates are the
plaquette, transported-Higgs, radial, and fermionic deviations after the
vacuum values have been subtracted. -/
noncomputable def centredInternalAction {k : Type*} [Fintype k]
    (w : k → ℝ) (Φ : k → ℂ) : ℝ :=
  ∑ a, w a * Complex.normSq (Φ a)

/-- Euler coordinates of the same centred quadratic action. -/
noncomputable def centredInternalEuler {k : Type*} (w : k → ℝ) (Φ : k → ℂ) : k → ℂ :=
  fun a => (2 * w a : ℝ) • Φ a

/-- CA.7--CA.8 in centred coordinates: every local positive graph term, the
signed action built from it, and the complete first variation vanish at the
invariant vacuum. -/
theorem centredInternalAction_vacuum {k : Type*} [Fintype k]
    (w : k → ℝ) (hw : ∀ a, 0 ≤ w a) :
    (∀ Φ, 0 ≤ centredInternalAction w Φ)
    ∧ centredInternalAction w 0 = 0
    ∧ centredInternalEuler w 0 = 0 := by
  refine ⟨?_, by simp [centredInternalAction], ?_⟩
  · intro Φ
    exact Finset.sum_nonneg fun a _ =>
      mul_nonneg (hw a) (Complex.normSq_nonneg _)
  · funext a
    simp [centredInternalEuler]

/-- One-point internal vacuum loading changes neither a driven row nor its
rank.  Entrywise it is exactly the gravity row tensored with the delta mass;
this is the finite CA.9 tensor-product statement. -/
theorem onePointVacuumLoading {p u : Type*}
    [Fintype p] [Fintype u] [DecidableEq p] [DecidableEq u] [Unique u]
    (Q : Matrix p p ℂ) :
    (∀ i j, (Q ⊗ₖ (1 : Matrix u u ℂ)) (i, default) (j, default) = Q i j)
    ∧ Matrix.rank (Q ⊗ₖ (1 : Matrix u u ℂ)) = Matrix.rank Q := by
  constructor
  · intro i j
    simp [Matrix.kroneckerMap_apply]
  · let e : p × u ≃ p := Equiv.prodUnique p u
    have hreindex : (Q ⊗ₖ (1 : Matrix u u ℂ)).reindex e e = Q := by
      ext i j
      simp [e, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
        Equiv.prodUnique_symm_apply]
    calc
      Matrix.rank (Q ⊗ₖ (1 : Matrix u u ℂ))
          = Matrix.rank ((Q ⊗ₖ (1 : Matrix u u ℂ)).reindex e e) :=
            (Matrix.rank_reindex e e _).symm
      _ = Matrix.rank Q := by rw [hreindex]

/-- Diagonal spectral screen used in CA.10. -/
def finiteFibreScreen {p r : Type*} [DecidableEq p] [DecidableEq r]
    (z : p → Prop) [DecidablePred z] : Matrix (p × r) (p × r) ℂ :=
  Matrix.diagonal fun x => if z x.1 then 1 else 0

/-- CA.10: a fixed finite internal fibre multiplies every gravitational
screen multiplicity by exactly the fibre rank (and hence by at most that
rank). -/
theorem finiteFibreScreen_rank {p r : Type*}
    [Fintype p] [Fintype r] [DecidableEq p] [DecidableEq r]
    (z : p → Prop) [DecidablePred z] :
    (finiteFibreScreen (r := r) z).rank
      = Fintype.card r * (Matrix.diagonal
          (fun i : p => if z i then (1 : ℂ) else 0)).rank := by
  classical
  simp only [finiteFibreScreen]
  rw [Matrix.rank_diagonal, Matrix.rank_diagonal]
  let e0 :
      {x : p × r // (if z x.1 then (1 : ℂ) else 0) ≠ 0}
        ≃ {x : p × r // z x.1} :=
    Equiv.subtypeEquivProp (by
      funext x
      apply propext
      by_cases hx : z x.1 <;> simp [hx])
  let e : {x : p × r // z x.1} ≃ {i : p // z i} × r :=
    { toFun := fun x => (⟨x.1.1, x.2⟩, x.1.2)
      invFun := fun x => ⟨(x.1.1, x.2), x.1.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  let e1 :
      {i : p // (if z i then (1 : ℂ) else 0) ≠ 0}
        ≃ {i : p // z i} :=
    Equiv.subtypeEquivProp (by
      funext i
      apply propext
      by_cases hi : z i <;> simp [hi])
  calc
    Fintype.card
          {x : p × r // (if z x.1 then (1 : ℂ) else 0) ≠ 0}
        = Fintype.card {x : p × r // z x.1} := Fintype.card_congr e0
    _
        = Fintype.card ({i : p // z i} × r) := Fintype.card_congr e
    _ = Fintype.card {i : p // z i} * Fintype.card r := Fintype.card_prod _ _
    _ = Fintype.card r * Fintype.card {i : p // z i} := Nat.mul_comm _ _
    _ = Fintype.card r *
          Fintype.card {i : p // (if z i then (1 : ℂ) else 0) ≠ 0} := by
      rw [← Fintype.card_congr e1]

/-- CA.5--CA.6 are the finite Ward, BRST, stress, and Einstein outputs of the
same action.  This named wrapper makes their role in the coupled-carrier
assembly explicit. -/
theorem coupledInternalWardStressEinstein
    {Gauge Field n : Type*} [Group Gauge]
    [Fintype n] [DecidableEq n]
    (act : Gauge → Field → Field)
    (hact : ∀ g h x, act (g * h) x = act g (act h x))
    (Smat : Field → ℝ) (hgauge : ∀ g x, Smat (act g x) = Smat x)
    (gaugeFlow relabelFlow : ℝ → ℝ)
    (hgaugeFlow : ∀ t, gaugeFlow t = gaugeFlow 0)
    (hrelabelFlow : ∀ t, relabelFlow t = relabelFlow 0)
    (divJ gaugePair stressPair fieldPair t₀ : ℝ)
    (hWardDeriv : HasDerivAt gaugeFlow (divJ + gaugePair) t₀)
    (hStressDeriv : HasDerivAt relabelFlow (stressPair - 2 * fieldPair) t₀)
    (GQ : Matrix n n ℂ) (hGQ : GQ.PosDef) (E : n → ℂ) :
    FiniteActionEinsteinCertificate act Smat
      (divJ + gaugePair) (stressPair - 2 * fieldPair) GQ E :=
  finite_action_Einstein act hact Smat hgauge gaugeFlow relabelFlow
    hgaugeFlow hrelabelFlow divJ gaugePair stressPair fieldPair t₀
    hWardDeriv hStressDeriv GQ hGQ E

/-- `thm:SMST-universal-coupled-action`: finite exact assembly of CA.1--CA.10.
The tuple exposes the source quotient and all derived algebraic/variational
components without introducing a second carrier or compactness primitive. -/
theorem universal_coupled_action_carrier :
    (∀ {h eg ei : ℕ} (Sg : Matrix (Fin h) (Fin eg) ℂ)
      (Si : Matrix (Fin h) (Fin ei) ℂ),
      (sourceSchurResidual Sg Si).PosSemidef
      ∧ (Matrix.fromBlocks (Sgᴴ * Sg) (Sgᴴ * Si)
          ((Sgᴴ * Si)ᴴ) (Siᴴ * Si)).rank - (Sgᴴ * Sg).rank
        = (sourceSchurResidual Sg Si).rank)
    ∧ (∀ {h eg ei : ℕ} (Sg : Matrix (Fin h) (Fin eg) ℂ)
        (Si : Matrix (Fin h) (Fin ei) ℂ),
        Sgᴴ * Si = 0 → Siᴴ * Si = 1 →
        sourceSchurResidual Sg Si = 1)
    ∧ (∀ {k : Type*} [Fintype k] (w : k → ℝ),
        (∀ a, 0 ≤ w a) → centredInternalAction w 0 = 0
          ∧ centredInternalEuler w 0 = 0)
    ∧ (∀ {p u : Type*} [Fintype p] [Fintype u]
        [DecidableEq p] [DecidableEq u] [Unique u]
        (Q : Matrix p p ℂ),
        Matrix.rank (Q ⊗ₖ (1 : Matrix u u ℂ)) = Matrix.rank Q)
    ∧ (∀ {p r : Type*} [Fintype p] [Fintype r]
        [DecidableEq p] [DecidableEq r]
        (z : p → Prop) [DecidablePred z],
        (finiteFibreScreen (r := r) z).rank
          = Fintype.card r * (Matrix.diagonal
              (fun i : p => if z i then (1 : ℂ) else 0)).rank) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h eg ei Sg Si
    exact ⟨sourceSchurResidual_posSemidef Sg Si,
      sourceSchurResidual_rank_increment Sg Si⟩
  · intro h eg ei Sg Si hc hw
    exact (independentWhitenedInternalBranch Sg Si hc hw).2
  · intro k _ w hw
    exact (centredInternalAction_vacuum w hw).2
  · intro p u _ _ _ _ _ Q
    exact (onePointVacuumLoading Q).2
  · intro p r _ _ _ _ z _
    exact finiteFibreScreen_rank z

end NCG
