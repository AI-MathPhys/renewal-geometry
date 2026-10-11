/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedDiracField
import RenewalGeometry.Continuum.GeneratedCellBulk
import RenewalGeometry.Continuum.GeneratedDiracStressNoether

/-!
# The bulk rows of the complete first-order action are the physical residuals

Einstein–Standard-Model action-closure manuscript, `app:generated-dynamics` ("integration by
parts expresses `D S^{cmp}_{N,τ}` through the physical rows ... In particular the complete
symmetric spinor stress is included"), for back-reacting Dirac data (`GenDStress.CoupledDirac`).

The complete first-order density is `S^{(1)} = L1SM + L1D` (`L1C`): the first-derivative
Einstein–Yang–Mills–Higgs density of the bosonic part (`GenFOAction.L1SM`; equal for the data and
their bosonic part `GenDSN.bos0`) plus the first-order Dirac density (`GenDAct.L1D`).

* `coord_contract` — `Σ_{μν}T^{μν}k_{μν} = Σ_{A,B}ε_Aε_BT_{AB}k_{AB}` for the coordinate components
  of a frame tensor;
* `bulkJ_sub` — the bilinear bulk expression is additive in the residual;
* `dirJ` — the Dirac bulk rows `ϱ(⟨r̄_D, σΨ⟩ - ⟨σ̄Ψ̄, r_D⟩ - ⟨r̄_D, φ⟩ + ⟨φ̄, r_D⟩)`,
  `σ = -X_M`, `M = ½(Λ - Λᵀ)` (bilinear in the Dirac residual and the variation);
* **`bulk_identity`** — the bosonic bulk rows of the bosonic part (`GenCellVar.bulkT`) plus the
  Dirac bulk rows (`GenDFld.bulkD`) are `bulkJ` of the **complete** bosonic residual of the data
  (Einstein residual with the Dirac stress, Yang–Mills residual with the Dirac current, Higgs
  residual with the Yukawa source) plus `dirJ` of the Dirac residual.
-/

open Finset Set Filter Topology
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenCplCV

open SobolevOpen (pd)
open HarmonicDefect EHJetVariation EHFieldVariation ActualJetSystem ActualJetRecon ActualJetSmooth
  ActualJetGauge ActualJetWriter ActualJetBridge ActualJetState GenMatVar GenFOAction FrameCurvature
  ActualJetFrame GenResMaps JetCurve GenDAlg GenDFJ GenDStress GenDiracCur SpinorProlongation
  GenDAct GenDEul GenNoether GenMatEuler PeriodicCube SlabWaveHk GenDFld GenCellVar GenCellBulk
  ActualJetCompleteForcing

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

/-! ### Frame tensors in coordinates -/

theorem gi_cof {g : Met} (hg : ChartM g) (μ A : Fin 4) :
    ∑ a, ginvOf g μ a * cof g lorentzSign (frR g) A a = lorentzSign A * frR g A μ := by
  unfold cof
  have e : ∑ a, ginvOf g μ a * (lorentzSign A * ∑ ν, g a ν * frR g A ν) =
      lorentzSign A * ∑ ν, (∑ a, ginvOf g μ a * g a ν) * frR g A ν := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [e]
  have h : ∀ ν, ∑ a, ginvOf g μ a * g a ν = if μ = ν then 1 else 0 := by
    intro ν
    have := hinv_R hg ν μ
    rw [show (if μ = ν then (1 : ℝ) else 0) = if ν = μ then 1 else 0 by
      by_cases h' : μ = ν
      · subst h'; simp
      · simp [h', Ne.symm h']]
    rw [← this]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ginvOf_symm hg.2.2 μ a, hg.2.2 a ν]
    ring
  simp only [h, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- **The coordinate pairing of a frame tensor**: `Σ_{μν} T^{μν}k_{μν} = Σ_{AB}ε_Aε_BT_{AB}k_{AB}`. -/
theorem coord_contract {g : Met} (hg : ChartM g) (T : Fin 4 → Fin 4 → ℝ) (k : Met) :
    ∑ μ, ∑ ν, up (ginvOf g) (fun a b => ∑ A, ∑ B, cof g lorentzSign (frR g) A a *
      cof g lorentzSign (frR g) B b * T A B) μ ν * k μ ν =
      ∑ A, ∑ B, lorentzSign A * lorentzSign B * T A B * kfr g k A B := by
  have hup : ∀ μ ν, up (ginvOf g) (fun a b => ∑ A, ∑ B, cof g lorentzSign (frR g) A a *
      cof g lorentzSign (frR g) B b * T A B) μ ν =
      ∑ A, ∑ B, (lorentzSign A * frR g A μ) * (lorentzSign B * frR g B ν) * T A B := by
    intro μ ν
    unfold up
    simp only [← gi_cof hg, Fin.sum_univ_four]
    ring
  simp only [hup]
  unfold kfr ipg
  simp only [Fin.sum_univ_four]
  ring

/-! ### Linearity of the bosonic bulk expression -/

section Lin

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

theorem traceRev_add (g gi X Y : Met) :
    traceRev g gi (X + Y) = traceRev g gi X + traceRev g gi Y := by
  funext μ ν
  simp only [traceRev, trG, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem sum_up_add (gi X Y k : Met) :
    ∑ μ, ∑ ν, up gi (X + Y) μ ν * k μ ν =
      ∑ μ, ∑ ν, up gi X μ ν * k μ ν + ∑ μ, ∑ ν, up gi Y μ ν * k μ ν := by
  simp only [up, Pi.add_apply, mul_add, Finset.sum_add_distrib, add_mul]

/-- The bilinear bulk expression is additive in the residual. -/
theorem bulkJ_add (SM : SMData (MatLie m) V S S') (g : Met) (b b' : BosP m V) (k : Met)
    (X : Fin 4 → MatLie m) (η : V) :
    bulkJ SM g (b + b') k X η = bulkJ SM g b k X η + bulkJ SM g b' k X η := by
  unfold bulkJ
  have e1 : (b + b').1 = b.1 + b'.1 := rfl
  have e2 : ∀ β, (b + b').2.1 β = b.2.1 β + b'.2.1 β := fun β => rfl
  have e3 : (b + b').2.2 = b.2.2 + b'.2.2 := rfl
  simp only [e1, e2, e3, traceRev_add, sum_up_add, smul_add, Finset.sum_add_distrib, map_add,
    LinearMap.add_apply]
  ring

end Lin

/-! ### The bulk identity -/

section Bulk

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {SM : SMData (MatLie m) V S S'}

/-- The local Lorentz part `M = ½(Λ - Λᵀ)` of the frame variation induced by `k` at `g`. -/
def Mk (g k : Met) (A B : Fin 4) : ℝ := (1 / 2 : ℝ) * (Lam g k A B - Lam g k B A)

/-- **The Dirac bulk rows**, bilinear in the Dirac residual `r = (r_D, r̄_D)` and the variation
`(k, φ, φ̄)`: `√(-det g)(⟨r̄_D, σΨ⟩ - ⟨σ̄Ψ̄, r_D⟩ - ⟨r̄_D, φ⟩ + ⟨φ̄, r_D⟩)`, `σ = -X_M`. -/
def dirJ (hP : DiracPairing SM) (g k : Met) (ψ : S) (ψb : S') (r : S × S') (φ : S) (φb : S') :
    ℝ :=
  volM g * (hP.P r.2 ((-spinPart SM.D.Fr (Mk g k)) ψ) -
    hP.P ((-spinPart SM.Db.Fr (Mk g k)) ψb) r.1 - hP.P r.2 φ + hP.P φb r.1)

variable (z : Tuple m V S S')

theorem rDf_eq_dirF (x : ST 3) :
    rDf SM.D (GR (z.g x) (z.dg x)) (aR (z.g x) (z.A x)) (z.H x) (z.ψ x)
        (dψR (z.g x) (fun γ => pd z.ψ γ x)) = (dirF SM z x).1 ∧
      rDf SM.Db (GR (z.g x) (z.dg x)) (aR (z.g x) (z.A x)) (z.H x) (z.ψb x)
        (dψR (z.g x) (fun γ => pd z.ψb γ x)) = (dirF SM z x).2 := by
  rw [← dirR_hj2 z x SM]
  unfold GenResMaps.dirR rDR hj2 rDf
  simp only
  constructor
  · rw [← XsR_eq_covX]
    unfold resD dirac XsR
    rw [eps_D_eq]
    simp only [Module.End.smul_def]
    rfl
  · rw [← XsR_eq_covX]
    unfold resD dirac XsR
    rw [show SM.Db.Fr.ε = lorentzSign from (eps_Db_eq).trans eps_D_eq]
    simp only [Module.End.smul_def]
    rfl

/-- The bosonic residual of the bosonic part is the complete bosonic residual plus the Dirac
contributions (Dirac stress, Dirac current, Yukawa source). -/
theorem bosF_bos0 (hC : CoupledDirac SM) (x : ST 3) :
    bosF (GenDSN.bos0 SM hC.toVariationalDirac) z x = bosF SM z x +
      (traceRev (z.g x) (ginvOf (z.g x)) (fun a b => SM.κ * GenDSN.TDf (SM := SM) z x a b),
        fun α => diracCur hC.μS SM.D.Fr (z.g x) (z.gi x) (z.ψ x) (z.ψb x) α,
        hC.yuk (z.ψb x) (z.ψ x)) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show ((z.jet x).res (GenDSN.bos0 SM hC.toVariationalDirac)).Etr =
      ((z.jet x).res SM).Etr + traceRev (z.g x) (ginvOf (z.g x)) (fun a b => SM.κ * GenDSN.TDf (SM := SM) z x a b)
    have hT : ∀ a b, (z.jet x).Tact (GenDSN.bos0 SM hC.toVariationalDirac) a b =
        (z.jet x).Tact SM a b - GenDSN.TDf (SM := SM) z x a b := fun a b => by
      have := GenDSN.Tf_split z hC x a b
      unfold GenStress.Tf at this
      linarith
    unfold ActualJet.res
    simp only
    have hfun : (fun a b => einstein (z.jet x).FJ.g (z.jet x).FJ.gi (z.jet x).FJ.dg (z.jet x).FJ.ddg a b +
        (GenDSN.bos0 SM hC.toVariationalDirac).Λ * (z.jet x).FJ.g a b -
        (GenDSN.bos0 SM hC.toVariationalDirac).κ *
          (z.jet x).Tact (GenDSN.bos0 SM hC.toVariationalDirac) a b) =
        (fun a b => einstein (z.jet x).FJ.g (z.jet x).FJ.gi (z.jet x).FJ.dg (z.jet x).FJ.ddg a b +
          SM.Λ * (z.jet x).FJ.g a b - SM.κ * (z.jet x).Tact SM a b) +
        (fun a b => SM.κ * GenDSN.TDf (SM := SM) z x a b) := by
      funext a b
      simp only [Pi.add_apply, hT]
      show _ + SM.Λ * _ - SM.κ * _ = _
      ring
    rw [hfun, traceRev_add]
    rfl
  · funext α
    exact GenDSN.rA_bos0 z hC x α
  · exact GenDSN.rH_bos0 z hC x

/-- The coordinate Dirac stress of the tuple paired with `k` is the frame pairing of the symmetric
Dirac stress at the covariant frame jets. -/
theorem TDf_contract (hC : CoupledDirac SM) (k : Met) (x : ST 3) :
    ∑ μ, ∑ ν, up (ginvOf (z.g x)) (GenDSN.TDf (SM := SM) z x) μ ν * k μ ν =
      ∑ A, ∑ B, lorentzSign A * lorentzSign B *
        (symTD SM.D hC.P).frame (z.H x) (z.ψ x)
          (covX SM.D (GR (z.g x) (z.dg x)) (aR (z.g x) (z.A x)) (z.ψ x) (dψR (z.g x) (fun γ => pd z.ψ γ x)))
          (z.ψb x)
          (covX SM.Db (GR (z.g x) (z.dg x)) (aR (z.g x) (z.A x)) (z.ψb x)
            (dψR (z.g x) (fun γ => pd z.ψb γ x)))
          A B * kfr (z.g x) k A B := by
  have hT : GenDSN.TDf (SM := SM) z x = fun a b => ∑ A, ∑ B,
      cof (z.g x) lorentzSign (frR (z.g x)) A a * cof (z.g x) lorentzSign (frR (z.g x)) B b *
        (symTD SM.D hC.P).frame (z.H x) (z.ψ x)
          (covX SM.D (GR (z.g x) (z.dg x)) (aR (z.g x) (z.A x)) (z.ψ x) (dψR (z.g x) (fun γ => pd z.ψ γ x)))
          (z.ψb x)
          (covX SM.Db (GR (z.g x) (z.dg x)) (aR (z.g x) (z.A x)) (z.ψb x)
            (dψR (z.g x) (fun γ => pd z.ψb γ x))) A B := by
    funext a b
    unfold GenDSN.TDf DiracStressForm.coord
    rw [hC.TD_eq, jet_AF_fr, jet_Xs, jet_Xs, XsR_eq_covX, XsR_eq_covX]
    rfl
  rw [hT]
  exact coord_contract (chartM_tuple z x) _ k

set_option maxHeartbeats 4000000 in
/-- **The bulk identity**: the bosonic bulk rows of the bosonic part plus the Dirac bulk rows are
the bilinear expression `bulkJ` in the complete bosonic residual of back-reacting Dirac data plus
the Dirac bulk rows `dirJ` in the Dirac residual (`κ ≠ 0`). -/
theorem bulk_identity (hC : CoupledDirac SM) (hκ : SM.κ ≠ 0) (k : ST 3 → Met)
    (X : ST 3 → Fin 4 → MatLie m) (η : ST 3 → V) (φ : ST 3 → S) (φb : ST 3 → S') (x : ST 3) :
    bulkT (GenDSN.bos0 SM hC.toVariationalDirac) z k X η x +
        bulkD hC.toDiracPairing z k X η φ φb x =
      bulkJ SM (z.g x) (bosF SM z x) (k x) (X x) (η x) +
        dirJ hC.toDiracPairing (z.g x) (k x) (z.ψ x) (z.ψb x) (dirF SM z x) (φ x) (φb x) := by
  have hdet : (Matrix.of (z.g x)).det ≠ 0 := z.det_ne x
  have hsym : ∀ μ ν, z.g x μ ν = z.g x ν μ := z.g_symm x
  rw [bulkT_eq (GenDSN.bos0 SM hC.toVariationalDirac) (GenDSN.bos0Var hC) hκ z k X η x,
    bosF_bos0 z hC x]
  change bulkJ SM (z.g x) (bosF SM z x + _) (k x) (X x) (η x) + _ = _
  rw [bulkJ_add]
  -- the Dirac contributions to the bosonic rows
  have hmet : -(1 / (2 * SM.κ)) * (volM (z.g x) * ∑ μ, ∑ ν, up (ginvOf (z.g x))
      (traceRev (z.g x) (ginvOf (z.g x)) (traceRev (z.g x) (ginvOf (z.g x))
        (fun a b => SM.κ * GenDSN.TDf (SM := SM) z x a b))) μ ν * k x μ ν) =
      -(1 / 2 : ℝ) * rho z x * ∑ μ, ∑ ν, up (ginvOf (z.g x)) (GenDSN.TDf (SM := SM) z x) μ ν * k x μ ν := by
    have hinv : traceRev (z.g x) (ginvOf (z.g x)) (traceRev (z.g x) (ginvOf (z.g x))
        (fun a b => SM.κ * GenDSN.TDf (SM := SM) z x a b)) = SM.κ • GenDSN.TDf (SM := SM) z x := by
      funext a b
      rw [traceRev_invol hdet hsym]
      rfl
    rw [hinv, sum_up_smul, volM_eq_rho]
    field_simp
  -- the Dirac current
  have hgau : ∑ δ, SM.ipG (volM (z.g x) • ∑ β, ginvOf (z.g x) δ β •
      diracCur hC.μS SM.D.Fr (z.g x) (z.gi x) (z.ψ x) (z.ψb x) β) (X x δ) =
      -(rho z x * ∑ A, lorentzSign A * hC.P (z.ψb x) (SM.D.ρ (aR (z.g x) (X x) A)
        (SM.D.Fr.c A (z.ψ x)))) := by
    have hd : ∀ δ, volM (z.g x) • ∑ β, ginvOf (z.g x) δ β •
        diracCur hC.μS SM.D.Fr (z.g x) (z.gi x) (z.ψ x) (z.ψb x) β =
        densD hC.toVariationalDirac z x δ := fun δ => by
      unfold densD JDf; rw [volM_eq_rho]; rfl
    simp only [hd, densD_eq, map_neg, map_sum, map_smul, LinearMap.neg_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun A _ => ?_
    have hdual : ∀ δ, SM.ipG (psiA hC.toVariationalDirac z A x) (X x δ) =
        hC.P (z.ψb x) (SM.D.ρ (X x δ) (SM.D.Fr.c A (z.ψ x))) := fun δ => by
      unfold psiA; rw [hC.ipG_symm, hC.μS_dual]
    simp only [hdual]
    unfold aR
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun δ _ => ?_
    show _ = _ * (_ * (frR (z.g x) A δ * _))
    rw [show z.e x A δ = frR (z.g x) A δ from rfl]
    ring
  -- the Yukawa source
  have hhig : 2 * volM (z.g x) * SM.ipV (hC.yuk (z.ψb x) (z.ψ x)) (η x) =
      rho z x * hC.P (z.ψb x) (SM.D.L (η x) (z.ψ x)) := by
    rw [hC.ipV_symm, volM_eq_rho, ← hC.yuk_dual]
    ring
  -- the gauge row of the Dirac density
  have hgD : (1 / 2 : ℝ) * ∑ C, lorentzSign C *
      (hC.P (z.ψb x) (SM.D.Fr.c C (SM.D.ρ (aR (z.g x) (X x) C) (z.ψ x))) -
        hC.P (SM.Db.ρ (aR (z.g x) (X x) C) (z.ψb x)) (SM.D.Fr.c C (z.ψ x))) =
      ∑ A, lorentzSign A * hC.P (z.ψb x) (SM.D.ρ (aR (z.g x) (X x) A) (SM.D.Fr.c A (z.ψ x))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun C _ => ?_
    have hc : SM.D.Fr.c C (SM.D.ρ (aR (z.g x) (X x) C) (z.ψ x)) =
        SM.D.ρ (aR (z.g x) (X x) C) (SM.D.Fr.c C (z.ψ x)) := by
      have := congrArg (fun F : Module.End ℝ S => F (z.ψ x)) (SM.D.comm (aR (z.g x) (X x) C) C)
      simpa using this.symm
    rw [hc, hC.ρ_tr]
    ring
  obtain ⟨hr1, hr2⟩ := rDf_eq_dirF z x
  have hΔ : bulkJ SM (z.g x) (traceRev (z.g x) (ginvOf (z.g x))
      (fun a b => SM.κ * GenDSN.TDf (SM := SM) z x a b),
        fun α => diracCur hC.μS SM.D.Fr (z.g x) (z.gi x) (z.ψ x) (z.ψb x) α,
        hC.yuk (z.ψb x) (z.ψ x)) (k x) (X x) (η x) +
      bulkD hC.toDiracPairing z k X η φ φb x =
      dirJ hC.toDiracPairing (z.g x) (k x) (z.ψ x) (z.ψb x) (dirF SM z x) (φ x) (φb x) := by
    unfold bulkJ
    simp only
    rw [hmet, hgau, hhig, TDf_contract z hC (k x) x]
    unfold bulkD dirJ
    rw [hgD, hr1, hr2, volM_eq_rho]
    have hMk : Mf z k x = Mk (z.g x) (k x) := rfl
    rw [hMk]
    ring
  linarith [hΔ]

end Bulk

end RenewalGeometry.GenCplCV
