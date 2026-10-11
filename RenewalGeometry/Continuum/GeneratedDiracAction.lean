/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedDiracFrameJets
import RenewalGeometry.Continuum.GeneratedFirstOrderAction

/-!
# The first-order Dirac action density and its metric variation

Einstein–Standard-Model action-closure manuscript, `eq:dirac-density`
(`L_D = Re{(i/2)[Ψ̄γ^μ∇_μΨ - (∇_μΨ̄)γ^μΨ] - Ψ̄𝓜(H)Ψ}` with the torsion-free spin connection
`ω(e)` and the gauge coupling), `eq:stress-definition` ("the Dirac–Yukawa contribution is always
taken from the complete metric variation; the spin-connection variation is not dropped"),
`app:generated-dynamics` (`S^{(1)}` the complete first-derivative Einstein–Standard-Model action).

In the actual-jet variables (metric `g`, gauge potential `A ∈ gl(m)`, Higgs field `H`, spinor `Ψ`
and co-spinor `Ψ̄` with the transposed Dirac block, a Dirac pairing `⟨Ψ̄, Ψ⟩`), on the extended
head 1-jets `HJ1C = HJ1 × (Ψ, ∂Ψ) × (Ψ̄, ∂Ψ̄)`:

* **`L1D`** — `√(-det g) L_D`, `L_D = ½Σ_Cε_C(⟨Ψ̄, c_CX_C⟩ - ⟨X̄_C, c_CΨ⟩) - ⟨Ψ̄, 𝓜(H)Ψ⟩`
  (`GenDStress.lagD`) with the covariant frame jets `X_C = ∇_{e_C}Ψ` of the adapted frame
  `e = frU(g⁻¹)` (spin connection from the frame jets, gauge coupling `ρ(A(e_C))`);
* `XsR_eq_covX` — the raw covariant jets in the frame-data form of `GenDAlg`;
* **`hasDerivAt_L1D_metric`** — the metric variation: along `(g + εk, ∂g + ε∂k)`,
  `d/dε L1D = √(-det g)(½Σε_Aε_BT_{AB}k_{AB} + ⟨r̄_D, σΨ⟩ - ⟨σ̄Ψ̄, r_D⟩ - Σ_C(div(e_C)Fl_C +
  e_C(Fl_C)))`: the symmetric Hilbert stress `T = GenDStress.symTD`, the Dirac residuals paired
  with the induced local Lorentz rotation `σ = -X_M`, `M = ½(Λ - Λᵀ)` (`Λ_{AB} = g(ė_A, e_B)`), and
  a frame divergence (`GenDAlg.frame_variation`).
-/

open Finset Set Filter Topology
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenDAct

open SobolevOpen (pd)
open HarmonicDefect EHJetVariation EHFieldVariation ActualJetSystem ActualJetRecon ActualJetSmooth
  ActualJetGauge ActualJetWriter ActualJetBridge ActualJetState GenMatVar GenFOAction FrameCurvature
  ActualJetFrame GenResMaps JetCurve GenDAlg GenDFJ GenDStress GenDiracCur SpinorProlongation

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable (m V S S') in
/-- **The extended head 1-jets** `((g, ∂g; A, ∂A; H, ∂H), (Ψ, ∂Ψ), (Ψ̄, ∂Ψ̄))`. -/
abbrev HJ1C := HJ1 m V × ((S × (Fin 4 → S)) × (S' × (Fin 4 → S')))

/-- The frame components of the gauge potential `a_B = Σ_μ e_B{}^μA_μ`. -/
def aR (g : Met) (A : Fin 4 → MatLie m) (B : Fin 4) : MatLie m := ∑ μ, frR g B μ • A μ

/-- **The first-order Dirac density** `√(-det g) L_D` on the extended head 1-jets. -/
def L1D (SM : SMData (MatLie m) V S S') (P : S' →ₗ[ℝ] S →ₗ[ℝ] ℝ) (j : HJ1C m V S S') : ℝ :=
  volM j.1.1.1 * lagD SM.D P j.1.2.2.1 j.2.1.1
    (XsR SM.D j.1.1.1 j.1.1.2 j.1.2.1.1 j.2.1.1 j.2.1.2) j.2.2.1
    (XsR SM.Db j.1.1.1 j.1.1.2 j.1.2.1.1 j.2.2.1 j.2.2.2)

/-- The raw covariant frame jets in frame-data form:
`X_B = e_BΨ + X_{G_B}Ψ + ρ(a_B)Ψ` with `G = GR(g, ∂g)`. -/
theorem XsR_eq_covX {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀] (D : DiracData (MatLie m) V S₀)
    (g : Met) (dg : Fin 4 → Met) (A : Fin 4 → MatLie m) (ψ : S₀) (cψ : Fin 4 → S₀) :
    XsR D g dg A ψ cψ = covX D (GR g dg) (aR g A) ψ (dψR g cψ) := by
  funext B
  unfold XsR cov omR omegaU covX aR GR
  simp only [map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    Module.End.smul_def]
  abel

/-! ### Line derivatives of the covariant jets and of the Dirac Lagrangian -/

section LineDeriv

/-- **The metric variation of the covariant frame jets**: along `(g + εk, ∂g + ε∂k)` at fixed
spinor jets, `δX_B = Σ_Eε_EΛ_{BE}(e_EΨ + ρ(a_E)Ψ) + X_{δG_B}Ψ` (`GenDAlg.varX`). -/
theorem hasDerivAt_covX_line {S₀ : Type*} [NormedAddCommGroup S₀] [NormedSpace ℝ S₀]
    (D : DiracData (MatLie m) V S₀) {g : Met} (hg : ChartM g) (dg : Fin 4 → Met) (k : Met)
    (dk : Fin 4 → Met) (A : Fin 4 → MatLie m) (ψ : S₀) (cψ : Fin 4 → S₀) (B : Fin 4) :
    HasDerivAt (fun ε : ℝ => covX D (GR (g + ε • k) (dg + ε • dk)) (aR (g + ε • k) A) ψ
        (dψR (g + ε • k) cψ) B)
      (varX D (aR g A) ψ (dψR g cψ) (Lam g k) (Gdot g dg k dk) B) 0 := by
  have hf : (fun ε : ℝ => covX D (GR (g + ε • k) (dg + ε • dk)) (aR (g + ε • k) A) ψ
      (dψR (g + ε • k) cψ) B) = fun ε => ∑ γ, frR (g + ε • k) B γ • cψ γ +
        (1 / 4 : ℝ) • ∑ c, ∑ d, (D.Fr.ε c * D.Fr.ε d * GR (g + ε • k) (dg + ε • dk) B c d) •
          (D.Fr.c c * D.Fr.c d) ψ + ∑ μ, frR (g + ε • k) B μ • D.ρ (A μ) ψ := by
    funext ε
    unfold covX dψR aR spinPart
    simp only [map_sum, map_smul, LinearMap.smul_apply, LinearMap.sum_apply]
  rw [hf]
  have h1 : HasDerivAt (fun ε : ℝ => ∑ γ, frR (g + ε • k) B γ • cψ γ)
      (∑ γ, edot g k B γ • cψ γ) 0 :=
    HasDerivAt.fun_sum fun γ _ => (hasDerivAt_edot hg k B γ).smul_const (cψ γ)
  have h2 : HasDerivAt (fun ε : ℝ => (1 / 4 : ℝ) • ∑ c, ∑ d,
      (D.Fr.ε c * D.Fr.ε d * GR (g + ε • k) (dg + ε • dk) B c d) • (D.Fr.c c * D.Fr.c d) ψ)
      ((1 / 4 : ℝ) • ∑ c, ∑ d, (D.Fr.ε c * D.Fr.ε d * Gdot g dg k dk B c d) •
        (D.Fr.c c * D.Fr.c d) ψ) 0 := by
    refine HasDerivAt.const_smul _ (HasDerivAt.fun_sum fun c _ => HasDerivAt.fun_sum fun d _ => ?_)
    exact ((hasDerivAt_GR hg dg k dk B c d).const_mul (D.Fr.ε c * D.Fr.ε d)).smul_const _
  have h3 : HasDerivAt (fun ε : ℝ => ∑ μ, frR (g + ε • k) B μ • D.ρ (A μ) ψ)
      (∑ μ, edot g k B μ • D.ρ (A μ) ψ) 0 :=
    HasDerivAt.fun_sum fun μ _ => (hasDerivAt_edot hg k B μ).smul_const _
  refine ((h1.add h2).add h3).congr_deriv ?_
  unfold varX dψR aR spinPart
  simp only [map_sum, map_smul, LinearMap.smul_apply, LinearMap.sum_apply, edot_decomp hg k B,
    Finset.sum_smul, smul_add, Finset.smul_sum, smul_smul, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun x y => (lorentzSign y * Lam g k B y * frR g y x) • cψ x),
    Finset.sum_comm (f := fun x y => (lorentzSign y * Lam g k B y * frR g y x) • D.ρ (A x) ψ)]
  abel_nf

/-- **The line derivative of the Dirac Lagrangian** (affine in the covariant jets). -/
theorem hasDerivAt_lagD_line (SM : SMData (MatLie m) V S S') (P : S' →ₗ[ℝ] S →ₗ[ℝ] ℝ) (H : V)
    (ψ : S) (ψb : S') {X : ℝ → Fin 4 → S} {Xb : ℝ → Fin 4 → S'} {X' : Fin 4 → S}
    {Xb' : Fin 4 → S'} (hX : ∀ C, HasDerivAt (fun ε => X ε C) (X' C) 0)
    (hXb : ∀ C, HasDerivAt (fun ε => Xb ε C) (Xb' C) 0) :
    HasDerivAt (fun ε => lagD SM.D P H ψ (X ε) ψb (Xb ε))
      ((1 / 2 : ℝ) * ∑ C, lorentzSign C * (P ψb (SM.D.Fr.c C (X' C)) -
        P (Xb' C) (SM.D.Fr.c C ψ))) 0 := by
  unfold lagD
  have h : ∀ C, HasDerivAt (fun ε => lorentzSign C * (P ψb (SM.D.Fr.c C (X ε C)) -
      P (Xb ε C) (SM.D.Fr.c C ψ)))
      (lorentzSign C * (P ψb (SM.D.Fr.c C (X' C)) - P (Xb' C) (SM.D.Fr.c C ψ))) 0 := fun C =>
    ((hasDerivAt_lin ((P ψb).comp (SM.D.Fr.c C)) (hX C)).fun_sub
      (hasDerivAt_lin (P.flip (SM.D.Fr.c C ψ)) (hXb C))).const_mul _
  exact ((HasDerivAt.fun_sum fun C _ => h C).const_mul (1 / 2 : ℝ)).sub_const _

end LineDeriv

/-! ### The metric variation of the Dirac density -/

section Metric

theorem det_neg_R {g : Met} (hg : ChartM g) : (Matrix.of g).det < 0 := by
  set E : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of (frR g) with hE
  have hgi : Matrix.of (ginvOf g) = E.transpose * Matrix.diagonal lorentzSign * E := by
    ext μ ν
    rw [Matrix.of_apply, compl_R hg μ ν, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [Matrix.mul_apply, Finset.sum_eq_single A]
    · simp only [hE, Matrix.transpose_apply, Matrix.of_apply, Matrix.diagonal_apply_eq]
      ring
    · intro B _ hB; simp [Matrix.diagonal_apply_ne _ hB]
    · simp
  have hdiag : (Matrix.diagonal lorentzSign).det = -1 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_four]
    simp [lorentzSign]
  have hdetgi : (Matrix.of (ginvOf g)).det = -(E.det ^ 2) := by
    rw [hgi, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdiag]
    ring
  have hprod : (Matrix.of g).det * (Matrix.of (ginvOf g)).det = 1 := by
    rw [← Matrix.det_mul]
    have : Matrix.of g * Matrix.of (ginvOf g) = 1 := by
      ext a c
      rw [Matrix.mul_apply, Matrix.one_apply]
      exact hinv_R hg a c
    rw [this, Matrix.det_one]
  rw [hdetgi] at hprod
  have hE0 : E.det ≠ 0 := by
    intro h0; rw [h0] at hprod; simp at hprod
  have hpos : 0 < E.det ^ 2 := by positivity
  nlinarith

theorem trG_kfr {g : Met} (hg : ChartM g) (k : Met) :
    trG (ginvOf g) k = ∑ A, lorentzSign A * kfr g k A A := by
  unfold trG kfr ipg
  simp only [compl_R hg, Fin.sum_univ_four]
  ring

variable (m V S S') in
/-- The metric-variation direction `((k, ∂k), 0, 0)` in the extended head 1-jets. -/
def vMet (k : Met) (dk : Fin 4 → Met) : HJ1C m V S S' :=
  (((k, dk), ((0, 0), (0, 0))), ((0, 0), (0, 0)))

variable (SM : SMData (MatLie m) V S S') (hP : DiracPairing SM)

set_option maxHeartbeats 2000000 in
/-- **The metric variation of the first-order Dirac density** at a chart 1-jet: the Hilbert stress
(`GenDStress.symTD`) paired with the frame components `k_{AB}` of the metric variation, plus the
Dirac residuals paired with the induced local Lorentz rotation, minus a frame divergence. -/
theorem hasDerivAt_L1D_metric (j : HJ1C m V S S') (hg : ChartM j.1.1.1)
    (hdg : ∀ α μ ν, j.1.1.2 α μ ν = j.1.1.2 α ν μ) (k : Met) (hk : ∀ μ ν, k μ ν = k ν μ)
    (dk : Fin 4 → Met) (hdk : ∀ α μ ν, dk α μ ν = dk α ν μ) :
    HasDerivAt (fun ε : ℝ => L1D SM hP.P (j + ε • vMet m V S S' k dk))
      (volM j.1.1.1 * ((1 / 2 : ℝ) * ∑ A, ∑ B, lorentzSign A * lorentzSign B *
          (symTD SM.D hP.P).frame j.1.2.2.1 j.2.1.1
            (covX SM.D (GR j.1.1.1 j.1.1.2) (aR j.1.1.1 j.1.2.1.1) j.2.1.1 (dψR j.1.1.1 j.2.1.2))
            j.2.2.1
            (covX SM.Db (GR j.1.1.1 j.1.1.2) (aR j.1.1.1 j.1.2.1.1) j.2.2.1 (dψR j.1.1.1 j.2.2.2))
            A B * kfr j.1.1.1 k A B +
        (hP.P (rDf SM.Db (GR j.1.1.1 j.1.1.2) (aR j.1.1.1 j.1.2.1.1) j.1.2.2.1 j.2.2.1
            (dψR j.1.1.1 j.2.2.2))
            ((-spinPart SM.D.Fr (fun A B => (1 / 2 : ℝ) * (Lam j.1.1.1 k A B - Lam j.1.1.1 k B A)))
              j.2.1.1) -
          hP.P ((-spinPart SM.Db.Fr (fun A B => (1 / 2 : ℝ) *
              (Lam j.1.1.1 k A B - Lam j.1.1.1 k B A))) j.2.2.1)
            (rDf SM.D (GR j.1.1.1 j.1.1.2) (aR j.1.1.1 j.1.2.1.1) j.1.2.2.1 j.2.1.1
              (dψR j.1.1.1 j.2.1.2)) -
          ∑ C, (divEf (GR j.1.1.1 j.1.1.2) C *
              lorFl hP (fun A B => (1 / 2 : ℝ) * (Lam j.1.1.1 k A B - Lam j.1.1.1 k B A))
                j.2.1.1 j.2.2.1 C +
            lorFlD hP (fun A B => (1 / 2 : ℝ) * (Lam j.1.1.1 k A B - Lam j.1.1.1 k B A))
              (fun B A C => (1 / 2 : ℝ) * (dLam j.1.1.1 j.1.1.2 k dk B A C -
                dLam j.1.1.1 j.1.1.2 k dk B C A))
              j.2.1.1 (dψR j.1.1.1 j.2.1.2) j.2.2.1 (dψR j.1.1.1 j.2.2.2) C)))) 0 := by
  obtain ⟨⟨⟨g, dg⟩, ⟨A, dA⟩, ⟨H, dH⟩⟩, ⟨ψ, cψ⟩, ⟨ψb, cψb⟩⟩ := j
  simp only at hg hdg ⊢
  have hfun : (fun ε : ℝ => L1D SM hP.P ((((g, dg), (A, dA), (H, dH)), (ψ, cψ), (ψb, cψb)) +
      ε • vMet m V S S' k dk)) = fun ε : ℝ => volM (g + ε • k) * lagD SM.D hP.P H ψ
        (covX SM.D (GR (g + ε • k) (dg + ε • dk)) (aR (g + ε • k) A) ψ
          (dψR (g + ε • k) cψ)) ψb
        (covX SM.Db (GR (g + ε • k) (dg + ε • dk)) (aR (g + ε • k) A) ψb
          (dψR (g + ε • k) cψb)) := by
    funext ε
    simp only [L1D, vMet, Prod.mk_add_mk, Prod.smul_mk, smul_zero, add_zero, XsR_eq_covX]
  rw [hfun]
  have hvol := hasDerivAt_vol_line (g := g) (k := k) (det_neg_R hg) hg.2.2
  have hlag := hasDerivAt_lagD_line SM hP.P H ψ ψb
    (fun B => hasDerivAt_covX_line SM.D hg dg k dk A ψ cψ B)
    (fun B => hasDerivAt_covX_line SM.Db hg dg k dk A ψb cψb B)
  have hprod := hvol.mul hlag
  simp only [zero_smul, add_zero] at hprod
  refine hprod.congr_deriv ?_
  -- the frame variation identity
  have hkf : kfr g k = fun A B => -(Lam g k A B + Lam g k B A) := by
    funext x y; have := Lam_add hg k hk x y; linarith
  have hom : omG (GR g dg) = OmR g dg := by
    funext x y z; exact GR_tors g dg hdg x y z
  have hGd : Gdot g dg k dk = koszul (dOm lorentzSign (omG (GR g dg)) (Lam g k)
      (fun A B => -(Lam g k A B + Lam g k B A)) (dLam g dg k dk)) := by
    funext B A' C
    rw [Gdot_eq hg dg hdg k hk dk hdk B A' C, hom, hkf]
  have hFV := frame_variation hP H (G := GR g dg) (fun B A C => GR_anti hg dg hdg B A C) (aR g A)
    ψ (dψR g cψ) ψb (dψR g cψb) (Lam g k) (dLam g dg k dk)
  rw [← hGd] at hFV
  have htr : trG (ginvOf g) k = ∑ A, lorentzSign A * (-(Lam g k A A + Lam g k A A)) := by
    rw [trG_kfr hg, hkf]
  unfold varL at hFV
  rw [htr, hkf]
  linear_combination (volM g) * hFV

end Metric


end RenewalGeometry.GenDAct
