/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.SMGaugeLieDerivative
import RenewalGeometry.Continuum.EinsteinSMEquivariantBound
import RenewalGeometry.Analysis.UhlenbeckCurvatureCovariance

/-!
# `G_SM` gauge invariance of the Einstein–Standard-Model jet density
  (`lem:equivariant-tests`, `thm:critical-quotient-defect`; Einstein–Standard-Model
  action-closure manuscript)

The complete jet density `gravPt + bosonPt + diracPt` of the library (`EinsteinSMBosonicVariation`,
`EinsteinSMFermionicContinuity`, `EinsteinSMGravityFirstOrder`) is invariant under the gauge
transformations of `G_SM = S(U(3) × U(2))` acting on jets.  Matter content: the Higgs doublet in the
weak block `ℂ² ⊂ ℂ³ ⊕ ℂ²` (`higgsAct`), the fermions on the **defining carrier** `defCarrier`
(`C = Fin 5`, `ρ_F = id`, the defining representation of `G_SM`, with a `G_SM`-covariant (scalar)
Yukawa/mass coupling) — the matter rendering of the critical-quotient chain.

* `higgsG`, `spinG`, `cospinG`, `adG`, `connG`: the fibre actions of `g ∈ G_SM` (doublet block,
  defining, conjugate, adjoint, affine connection action with derivative `dg`);
* `gaugeJet g dg J`: the induced action on reduced jets `(e, ∂e, A, F, H, K, Ψ, ∂Ψ, Ψ̄, ∂Ψ̄)`;
* `liePL_adG`: the invariant metric of `𝔰(𝔲(3) ⊕ 𝔲(2))` (three coupling parts) is
  `Ad_{G_SM}`-invariant; `hInnerReL_higgsG`: the doublet product is `G_SM`-invariant;
* **`bosonPt_gaugeJet`**, **`diracPt_gaugeJet`**, `gravPt_gaugeJet`: invariance of the jet density
  (for `dg` with `g^* dg` skew-Hermitian; the Maurer–Cartan terms of the kinetic and minimal
  coupling parts of the Dirac density cancel).
-/

open MeasureTheory Filter Topology Set Matrix
open scoped ENNReal NNReal ContDiff ComplexConjugate

noncomputable section

namespace RenewalGeometry.SMGaugeJet

open SobolevOpen CriticalGauge CriticalQuotient BallAnalysis.SMGaugeStructure SMGaugeLie EinsteinSM

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! ### The defining fermion carrier -/

/-- The scalar matrix `m · 1` on the carrier `Fin 5`. -/
def scalarM (m : ℂ) : Fin 5 → Fin 5 → ℂ := fun c c' => if c = c' then m else 0

theorem comm_scalarM (X : LieFibre) (m : ℂ) : EinsteinSM.comm X (scalarM m) = 0 := by
  funext i j
  simp only [EinsteinSM.comm, mmul, scalarM, Pi.sub_apply, Pi.zero_apply, mul_ite, mul_zero,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- **The defining fermion carrier**: carrier `Fin 5` (`ℂ³ ⊕ ℂ²`, all rows one chirality), the
defining representation `ρ_F = id` of `𝔰(𝔲(3) ⊕ 𝔲(2))`, and the `G_SM`-covariant Yukawa/mass
coupling `𝓜(θ) = m(θ) · 1` (in the defining representation a covariant coupling linear in the
doublet must vanish, so only the constant block remains). -/
abbrev defCarrier (Ysec : Type) (mY : CoefficientBank Ysec → ℂ) : FermionCarrier Ysec where
  C := Fin 5
  left := fun _ => true
  rho := LinearMap.id
  rho_skew := fun X hX c c' => hX.1 c c'
  rho_bracket := fun _ _ _ _ => rfl
  rho_chiral := fun _ _ _ h => absurd rfl h
  yukawa := fun θ => AffineMap.const ℝ HiggsFibre (scalarM (mY θ))
  yukawa_covariant := fun θ X _ v => by
    simp only [AffineMap.const_linear, LinearMap.zero_apply]
    exact (comm_scalarM X (mY θ)).symm

@[simp] theorem defCarrier_rho {Ysec : Type} (mY : CoefficientBank Ysec → ℂ) (X : LieFibre) :
    (defCarrier Ysec mY).rho X = X := rfl

@[simp] theorem defCarrier_yukawa {Ysec : Type} (mY : CoefficientBank Ysec → ℂ)
    (θ : CoefficientBank Ysec) (v : HiggsFibre) :
    (defCarrier Ysec mY).yukawa θ v = scalarM (mY θ) := rfl

/-! ### Fibre actions of `G_SM` -/

/-- The weak `2 × 2` block of a `5 × 5` matrix. -/
def wk (g : M5) : Matrix (Fin 2) (Fin 2) ℂ := g.submatrix (Fin.natAdd 3) (Fin.natAdd 3)

/-- The colour `3 × 3` block of a `5 × 5` matrix. -/
def col (g : M5) : Matrix (Fin 3) (Fin 3) ℂ := g.submatrix (Fin.castAdd 2) (Fin.castAdd 2)

/-- Action on the Higgs doublet (weak block). -/
def higgsG (g : M5) (v : HiggsFibre) : HiggsFibre := wk g *ᵥ v

/-- Defining action on spinors (internal index). -/
def spinG (g : M5) (ψ : SpinorFibre (Fin 5)) : SpinorFibre (Fin 5) := fun s => g *ᵥ ψ s

/-- Conjugate action on dual spinors: `Ψ̄ ↦ Ψ̄ g^*`, i.e. `Ψ̄_s ↦ ḡ Ψ̄_s` in column form. -/
def cospinG (g : M5) (ψ : SpinorFibre (Fin 5)) : SpinorFibre (Fin 5) := fun s => (star g)ᵀ *ᵥ ψ s

/-- Adjoint action `X ↦ g X g^*` on the Lie fibre. -/
def adG (g : M5) (X : LieFibre) : LieFibre := fun i j => (g * Matrix.of X * star g) i j

/-- Affine action on connections `A_μ ↦ g A_μ g^* - (∂_μ g) g^*`. -/
def connG (g : M5) (dg : Fin 4 → M5) (A : ConnFibre) : ConnFibre :=
  fun μ i j => adG g (A μ) i j - (dg μ * star g) i j

/-- **The induced gauge action on reduced jets.** -/
def gaugeJet (g : M5) (dg : Fin 4 → M5) (J : RJet (Fin 5)) : RJet (Fin 5) :=
  RJet.mk J.e J.de (connG g dg J.A) (fun μ ν => adG g (J.F μ ν)) (higgsG g J.H)
    (fun μ => higgsG g (J.K μ)) (spinG g J.Ψ) (fun μ => spinG g (J.dΨ μ) + spinG (dg μ) J.Ψ)
    (cospinG g J.Ψb) (fun μ => cospinG g (J.dΨb μ) + cospinG (dg μ) J.Ψb)

/-! ### Block calculus for `G_SM` -/

theorem colourBlock_castAdd (k : Fin 3) : colourBlock (Fin.castAdd 2 k) = true := by
  simp [colourBlock, k.isLt]

theorem colourBlock_natAdd (k : Fin 2) : colourBlock (Fin.natAdd 3 k) = false := by
  simp [colourBlock]

theorem sum_fin5 {β : Type*} [AddCommMonoid β] (f : Fin 5 → β) :
    ∑ k, f k = ∑ k : Fin 3, f (Fin.castAdd 2 k) + ∑ k : Fin 2, f (Fin.natAdd 3 k) :=
  Fin.sum_univ_add (a := 3) (b := 2) f

theorem col_mul_left {g : M5} (hg : IsSMBlock g) (Y : M5) :
    col (g * Y) = col g * col Y := by
  ext i j
  simp only [col, submatrix_apply, Matrix.mul_apply]
  rw [sum_fin5]
  have : ∑ k : Fin 2, g (Fin.castAdd 2 i) (Fin.natAdd 3 k) * Y (Fin.natAdd 3 k) (Fin.castAdd 2 j)
      = 0 := Finset.sum_eq_zero fun k _ => by
    rw [hg _ _ (by rw [colourBlock_castAdd, colourBlock_natAdd]; decide), zero_mul]
  rw [this, add_zero]

theorem col_mul_right {g : M5} (hg : IsSMBlock g) (Y : M5) :
    col (Y * g) = col Y * col g := by
  ext i j
  simp only [col, submatrix_apply, Matrix.mul_apply]
  rw [sum_fin5]
  have : ∑ k : Fin 2, Y (Fin.castAdd 2 i) (Fin.natAdd 3 k) * g (Fin.natAdd 3 k) (Fin.castAdd 2 j)
      = 0 := Finset.sum_eq_zero fun k _ => by
    rw [hg _ _ (by rw [colourBlock_castAdd, colourBlock_natAdd]; decide), mul_zero]
  rw [this, add_zero]

theorem wk_mul_left {g : M5} (hg : IsSMBlock g) (Y : M5) :
    wk (g * Y) = wk g * wk Y := by
  ext i j
  simp only [wk, submatrix_apply, Matrix.mul_apply]
  rw [sum_fin5]
  have : ∑ k : Fin 3, g (Fin.natAdd 3 i) (Fin.castAdd 2 k) * Y (Fin.castAdd 2 k) (Fin.natAdd 3 j)
      = 0 := Finset.sum_eq_zero fun k _ => by
    rw [hg _ _ (by rw [colourBlock_castAdd, colourBlock_natAdd]; decide), zero_mul]
  rw [this, zero_add]

theorem wk_mul_right {g : M5} (hg : IsSMBlock g) (Y : M5) :
    wk (Y * g) = wk Y * wk g := by
  ext i j
  simp only [wk, submatrix_apply, Matrix.mul_apply]
  rw [sum_fin5]
  have : ∑ k : Fin 3, Y (Fin.natAdd 3 i) (Fin.castAdd 2 k) * g (Fin.castAdd 2 k) (Fin.natAdd 3 j)
      = 0 := Finset.sum_eq_zero fun k _ => by
    rw [hg _ _ (by rw [colourBlock_castAdd, colourBlock_natAdd]; decide), mul_zero]
  rw [this, zero_add]

theorem col_star (g : M5) : col (star g) = star (col g) := by
  ext i j; simp [col, star_apply]

theorem wk_star (g : M5) : wk (star g) = star (wk g) := by
  ext i j; simp [wk, star_apply]

theorem col_one : col (1 : M5) = 1 := by
  ext i j
  rcases eq_or_ne i j with rfl | h
  · simp [col]
  · simp [col, one_apply_ne h, one_apply_ne ((Fin.castAdd_injective 3 2).ne h)]

theorem wk_one : wk (1 : M5) = 1 := by
  ext i j
  rcases eq_or_ne i j with rfl | h
  · simp [wk]
  · simp [wk, one_apply_ne h, one_apply_ne ((Fin.natAdd_injective 2 3).ne h)]

theorem col_unitary {g : M5} (hg : g ∈ GSM) : col g * star (col g) = 1 ∧ star (col g) * col g = 1 := by
  have h1 : g * star g = 1 := mem_unitaryGroup_iff.mp hg.1
  have h2 : star g * g = 1 := mem_unitaryGroup_iff'.mp hg.1
  have hs := isSMBlock_star hg.2.1
  refine ⟨?_, ?_⟩
  · rw [← col_star, ← col_mul_left hg.2.1, h1, col_one]
  · rw [← col_star, ← col_mul_left hs, h2, col_one]

theorem wk_unitary {g : M5} (hg : g ∈ GSM) : wk g * star (wk g) = 1 ∧ star (wk g) * wk g = 1 := by
  have h1 : g * star g = 1 := mem_unitaryGroup_iff.mp hg.1
  have h2 : star g * g = 1 := mem_unitaryGroup_iff'.mp hg.1
  have hs := isSMBlock_star hg.2.1
  refine ⟨?_, ?_⟩
  · rw [← wk_star, ← wk_mul_left hg.2.1, h1, wk_one]
  · rw [← wk_star, ← wk_mul_left hs, h2, wk_one]

theorem col_conj {g : M5} (hg : g ∈ GSM) (Y : M5) :
    col (g * Y * star g) = col g * col Y * star (col g) := by
  rw [col_mul_right (isSMBlock_star hg.2.1), col_mul_left hg.2.1, col_star]

theorem wk_conj {g : M5} (hg : g ∈ GSM) (Y : M5) :
    wk (g * Y * star g) = wk g * wk Y * star (wk g) := by
  rw [wk_mul_right (isSMBlock_star hg.2.1), wk_mul_left hg.2.1, wk_star]

/-! ### Invariance of the Lie-algebra metric -/

theorem block3_eq_col (X : LieFibre) : block3 X = (col (Matrix.of X) : Fin 3 → Fin 3 → ℂ) := rfl

theorem block2_eq_wk (X : LieFibre) : block2 X = (wk (Matrix.of X) : Fin 2 → Fin 2 → ℂ) := rfl

theorem mtrace_eq {n : ℕ} (X : Fin n → Fin n → ℂ) : mtrace X = (Matrix.of X).trace := rfl

theorem mmul_eq {n : ℕ} (X Y : Fin n → Fin n → ℂ) :
    mmul X Y = ((Matrix.of X * Matrix.of Y : Matrix (Fin n) (Fin n) ℂ) : Fin n → Fin n → ℂ) := by
  funext i j; simp [mmul, Matrix.mul_apply]

/-- The traceless part in matrix form. -/
def tl {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := Y - (Y.trace / n) • 1

theorem traceless_eq {n : ℕ} (X : Fin n → Fin n → ℂ) :
    traceless X = ((tl (Matrix.of X) : Matrix (Fin n) (Fin n) ℂ) : Fin n → Fin n → ℂ) := by
  funext i j
  simp only [traceless, tl, mtrace_eq, Matrix.sub_apply, Matrix.smul_apply, one_apply, of_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]

theorem trace_conj_unitary {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ} (hU : star U * U = 1)
    (Y : Matrix (Fin n) (Fin n) ℂ) : (U * Y * star U).trace = Y.trace := by
  rw [trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]

theorem tl_conj_unitary {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ} (hU : U * star U = 1)
    (hU' : star U * U = 1) (Y : Matrix (Fin n) (Fin n) ℂ) :
    tl (U * Y * star U) = U * tl Y * star U := by
  simp only [tl, trace_conj_unitary hU', Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, hU]

theorem trace_mul_conj_unitary {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ} (hU' : star U * U = 1)
    (P Q : Matrix (Fin n) (Fin n) ℂ) :
    ((U * P * star U) * (U * Q * star U)).trace = (P * Q).trace := by
  have : (U * P * star U) * (U * Q * star U) = U * (P * Q) * star U := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star U) U, hU', Matrix.one_mul]
  rw [this, trace_conj_unitary hU']

theorem lieP3_eq (X Z : LieFibre) :
    lieP3 X Z = -2 * ((tl (col (Matrix.of X)) * tl (col (Matrix.of Z))).trace).re := by
  unfold lieP3
  rw [mtrace_eq, mmul_eq, traceless_eq, traceless_eq, block3_eq_col, block3_eq_col]
  rfl

theorem lieP2_eq (X Z : LieFibre) :
    lieP2 X Z = -2 * ((tl (wk (Matrix.of X)) * tl (wk (Matrix.of Z))).trace).re := by
  unfold lieP2
  rw [mtrace_eq, mmul_eq, traceless_eq, traceless_eq, block2_eq_wk, block2_eq_wk]
  rfl

theorem lieP1_eq (X Z : LieFibre) :
    lieP1 X Z = (wk (Matrix.of X)).trace.im * (wk (Matrix.of Z)).trace.im := by
  unfold lieP1
  rw [mtrace_eq, mtrace_eq, block2_eq_wk, block2_eq_wk]
  rfl

theorem of_adG (g : M5) (X : LieFibre) : Matrix.of (adG g X) = g * Matrix.of X * star g := rfl

theorem lieP3_adG {g : M5} (hg : g ∈ GSM) (X Z : LieFibre) :
    lieP3 (adG g X) (adG g Z) = lieP3 X Z := by
  obtain ⟨hU, hU'⟩ := col_unitary hg
  rw [lieP3_eq, lieP3_eq, of_adG, of_adG, col_conj hg, col_conj hg, tl_conj_unitary hU hU',
    tl_conj_unitary hU hU', trace_mul_conj_unitary hU']

theorem lieP2_adG {g : M5} (hg : g ∈ GSM) (X Z : LieFibre) :
    lieP2 (adG g X) (adG g Z) = lieP2 X Z := by
  obtain ⟨hU, hU'⟩ := wk_unitary hg
  rw [lieP2_eq, lieP2_eq, of_adG, of_adG, wk_conj hg, wk_conj hg, tl_conj_unitary hU hU',
    tl_conj_unitary hU hU', trace_mul_conj_unitary hU']

theorem lieP1_adG {g : M5} (hg : g ∈ GSM) (X Z : LieFibre) :
    lieP1 (adG g X) (adG g Z) = lieP1 X Z := by
  obtain ⟨-, hU'⟩ := wk_unitary hg
  rw [lieP1_eq, lieP1_eq, of_adG, of_adG, wk_conj hg, wk_conj hg, trace_conj_unitary hU',
    trace_conj_unitary hU']

/-- **`Ad_{G_SM}`-invariance of the three parts of the invariant metric of
`𝔰(𝔲(3) ⊕ 𝔲(2))`.** -/
theorem liePL_adG {g : M5} (hg : g ∈ GSM) (j : Fin 3) (X Z : LieFibre) :
    liePL j (adG g X) (adG g Z) = liePL j X Z := by
  fin_cases j
  · exact lieP3_adG hg X Z
  · exact lieP2_adG hg X Z
  · exact lieP1_adG hg X Z

/-! ### Invariance of the doublet product -/

theorem hInner_mulVec_unitary {U : Matrix (Fin 2) (Fin 2) ℂ} (hU : star U * U = 1)
    (u v : HiggsFibre) : hInner (U *ᵥ u) (U *ᵥ v) = hInner u v := by
  have e : ∀ w w' : HiggsFibre, hInner w w' = star w ⬝ᵥ w' := fun w w' => by
    simp [hInner, dotProduct]
  rw [e, e, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]
  rw [show Uᴴ = star U from rfl, hU, one_mulVec]

theorem hInnerReL_higgsG {g : M5} (hg : g ∈ GSM) (u v : HiggsFibre) :
    hInnerReL (higgsG g u) (higgsG g v) = hInnerReL u v := by
  simp only [hInnerReL, mkBilinL_apply, higgsG, hInner_mulVec_unitary (wk_unitary hg).2]

theorem higgsQuad_higgsG {g : M5} (hg : g ∈ GSM) (v : HiggsFibre) :
    higgsQuad (higgsG g v) = higgsQuad v :=
  hInnerReL_higgsG hg v v

/-! ### Invariance of the bosonic jet density -/

theorem ymCoeff_adG {g : M5} (hg : g ∈ GSM) (j : Fin 3) (e : CoframeFibre)
    (F : Fin 4 → ConnFibre) :
    ymCoeff j e (fun μ ν => adG g (F μ ν)) (fun μ ν => adG g (F μ ν)) = ymCoeff j e F F := by
  simp only [ymCoeff_apply, liePL_adG hg]

theorem higgsCoeff_higgsG {g : M5} (hg : g ∈ GSM) (e : CoframeFibre) (K : Fin 4 → HiggsFibre) :
    higgsCoeff e (fun μ => higgsG g (K μ)) (fun μ => higgsG g (K μ)) = higgsCoeff e K K := by
  simp only [higgsCoeff_apply, hInnerReL_higgsG hg]

/-- **Gauge invariance of the bosonic (Yang–Mills + Higgs) jet density** under `G_SM`. -/
theorem bosonPt_gaugeJet {Y : Type} (θ : CoefficientBank Y) {g : M5} (hg : g ∈ GSM)
    (dg : Fin 4 → M5) (J : RJet (Fin 5)) : bosonPt θ (gaugeJet g dg J) = bosonPt θ J := by
  simp only [bosonPt, gaugeJet, RJet.mk_e, RJet.mk_F, RJet.mk_K, RJet.mk_H, ymCoeff_adG hg,
    higgsCoeff_higgsG hg, higgsQuad_higgsG hg]

/-- The gravitational jet density depends only on `(e, ∂e)`, which the gauge action fixes. -/
theorem gravPt_gaugeJet {Ysec : Type} (θ : CoefficientBank Ysec) (g : M5) (dg : Fin 4 → M5)
    (J : RJet (Fin 5)) : gravPt θ (gaugeJet g dg J) = gravPt θ J := rfl

end RenewalGeometry.SMGaugeJet
