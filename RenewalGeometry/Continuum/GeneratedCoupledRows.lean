/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedDiracStress
import RenewalGeometry.Continuum.GeneratedSpinorDefect
import RenewalGeometry.Continuum.GeneratedHiggsDefect

/-!
# The rows of the coupled defect system (Dirac back-reaction)

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`
(`app:generated-dynamics`), coupled spinors.  Let `W` solve the shift-transported system with the
head fields of a tuple `z` (`GenHiggsDefect.MSol`), with the bosonic defining-jet identities
already propagated (`prB W = prB 𝒰(z)`) and the Dirac equations of `z` (`dirF z = 0`) on an open
slab.  Then `W` and `𝒰(z)` differ only in the auxiliary spinor jets `X, X̄`, and:

* `orig_row_cpl` — `W` solves the **original** realized rows (the shift-transport terms cancel;
  no decoupling hypothesis);
* `diff_row` — the difference `W - 𝒰(z)` satisfies the rows with forcing
  `𝓕(W) - 𝓕(𝒰(z)) - errF(z)`;
* **`etr_eq`** (`p`-rows) — `𝓔^{tr}(z) = κ trRev(ΔS) + ∇_{(μ}C_{ν)}` with `ΔS` the difference of
  the complete stresses at the jets of `W` and of `z` (only the Dirac stress differs);
* **`reduced_einstein_cpl`** — the reduced Einstein equation of `z` with source `T(z) + ΔS`;
* **`x_row_cpl`** (`X`-rows) — `∂_tY_a + Σ_j diracP_j∂_jY_a = N(XrowFX(Y)_a + c_0(½Σ_bε_bS_{ab}c_b)Ψ)`
  for the defect `Y = X(W) - X(z)`, `S_{ab}` the frame components of `∇_{(μ}C_{ν)}`: the spinor
  defect is driven only by first derivatives of the harmonic defect (and by itself).
-/

open Filter Topology Set Finset
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenCplRows

open SobolevOpen (pd)
open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci
  ActualJetBridge ActualJetCompleteForcing ActualJetRecon ActualJetState GenConstraint
  GenSpinorDefect GenHiggsDefect SymHypEnergy

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

/-! ### Algebra of the prolonged spinor row -/

section Algebra

variable {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀]

/-- The part of the prolonged spinor row linear in the spinor jets (connection and mass terms). -/
def XrowFX (D : DiracData (MatLie m) V S₀) (g gi : Fin 4 → Fin 4 → ℝ)
    (dg : Fin 4 → Fin 4 → Fin 4 → ℝ) (AF : AdaptedFrame) (de : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (A : Fin 4 → MatLie m) (H : V) (X : Fin 4 → S₀) (a : Fin 4) : S₀ :=
  -(omegaU D g gi dg AF.fr de A 0 • X a) +
    ∑ c, lcΓ lorentzSign (Gfun g gi dg AF.fr de) 0 a c • X c +
    D.Fr.c 0 • ∑ i : Fin 3, D.Fr.c i.succ • (omegaU D g gi dg AF.fr de A i.succ • X a -
      ∑ c, lcΓ lorentzSign (Gfun g gi dg AF.fr de) i.succ a c • X c) -
    D.Fr.c 0 • (mass D.m0 D.L H • X a)

theorem frT2_sub (e : Fin 4 → Fin 4 → ℝ) (T T' : Fin 4 → Fin 4 → ℝ) (a b : Fin 4) :
    frT2 e T a b - frT2 e T' a b = frT2 e (fun μ ν => T μ ν - T' μ ν) a b := by
  unfold frT2
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun ν _ => by ring

theorem frT2_add (e : Fin 4 → Fin 4 → ℝ) (T T' : Fin 4 → Fin 4 → ℝ) (a b : Fin 4) :
    frT2 e (fun μ ν => T μ ν + T' μ ν) a b = frT2 e T a b + frT2 e T' a b := by
  unfold frT2
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ν _ => by ring

theorem frT2_smul (e : Fin 4 → Fin 4 → ℝ) (c : ℝ) (T : Fin 4 → Fin 4 → ℝ) (a b : Fin 4) :
    frT2 e (fun μ ν => c * T μ ν) a b = c * frT2 e T a b := by
  unfold frT2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun ν _ => by ring

/-- The Ricci-elimination term of the prolonged row. -/
def ricTerm (D : DiracData (MatLie m) V S₀) (g gi : Fin 4 → Fin 4 → ℝ) (AF : AdaptedFrame)
    (T : Fin 4 → Fin 4 → ℝ) (ψ : S₀) (a : Fin 4) : S₀ :=
  ((1 / 2 : ℝ) • ∑ b, (lorentzSign b * frT2 AF.fr T a b) • D.Fr.c b) • ψ

theorem ricTerm_sub (D : DiracData (MatLie m) V S₀) (g gi : Fin 4 → Fin 4 → ℝ) (AF : AdaptedFrame)
    (T T' : Fin 4 → Fin 4 → ℝ) (ψ : S₀) (a : Fin 4) :
    ricTerm D g gi AF T ψ a - ricTerm D g gi AF T' ψ a =
      ricTerm D g gi AF (fun μ ν => T μ ν - T' μ ν) ψ a := by
  unfold ricTerm
  rw [← sub_smul, ← smul_sub, ← Finset.sum_sub_distrib]
  congr 2
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← sub_smul, ← mul_sub, frT2_sub]

/-- **The prolonged row is affine in the spinor jets and in the stress**:
`XrowF(X, T₀) - XrowF(X', T₀') = XrowFX(X - X') - c_0 κ ricTerm(trRev(T₀ - T₀'))`. -/
theorem XrowF_sub (D : DiracData (MatLie m) V S₀) (κ Λ : ℝ) (g gi : Fin 4 → Fin 4 → ℝ)
    (dg : Fin 4 → Fin 4 → Fin 4 → ℝ) (AF : AdaptedFrame) (de : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (A : Fin 4 → MatLie m) (F : Fin 4 → Fin 4 → MatLie m) (H : V) (DH : Fin 4 → V) (ψ : S₀)
    (X X' : Fin 4 → S₀) (T0 T0' : Fin 4 → Fin 4 → ℝ) (a : Fin 4) :
    XrowF D κ Λ g gi dg AF de A F H DH ψ X T0 a - XrowF D κ Λ g gi dg AF de A F H DH ψ X' T0' a =
      XrowFX D g gi dg AF de A H (X - X') a -
        D.Fr.c 0 • ricTerm D g gi AF (fun μ ν => κ * (traceRev g gi T0 μ ν -
          traceRev g gi T0' μ ν)) ψ a := by
  have hr : ((1 / 2 : ℝ) • ∑ b, (lorentzSign b * (κ * frT2 AF.fr (traceRev g gi T0) a b +
      Λ * (if a = b then lorentzSign a else 0))) • D.Fr.c b) • ψ -
      ((1 / 2 : ℝ) • ∑ b, (lorentzSign b * (κ * frT2 AF.fr (traceRev g gi T0') a b +
      Λ * (if a = b then lorentzSign a else 0))) • D.Fr.c b) • ψ =
      ricTerm D g gi AF (fun μ ν => κ * (traceRev g gi T0 μ ν - traceRev g gi T0' μ ν)) ψ a := by
    unfold ricTerm
    rw [← sub_smul, ← smul_sub, ← Finset.sum_sub_distrib]
    congr 2
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← sub_smul, frT2_smul, ← frT2_sub]
    congr 1
    ring
  unfold XrowF XrowFX
  simp only [Pi.sub_apply, smul_sub, map_sub, Finset.sum_sub_distrib, sub_smul]
  rw [← hr]
  simp only [smul_sub, smul_add]
  abel

/-- The Ricci-elimination term of the residual multiplier when the Dirac residual vanishes. -/
theorem XrowB_zero_rD (D : DiracData (MatLie m) V S₀) (κ : ℝ) (g gi : Fin 4 → Fin 4 → ℝ)
    (dg : Fin 4 → Fin 4 → Fin 4 → ℝ) (AF : AdaptedFrame) (de : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (A : Fin 4 → MatLie m) (ψ : S₀) (a : Fin 4) (Etr : Fin 4 → Fin 4 → ℝ) :
    XrowB D κ g gi dg AF de A ψ a 0 Etr (fun _ _ => 0) =
      -(D.Fr.c 0 • ricTerm D g gi AF Etr ψ a) := by
  unfold XrowB ricTerm
  have h0 : traceRev g gi (fun _ _ => (0 : ℝ)) = fun _ _ => 0 := by
    funext μ ν; simp [traceRev, trG]
  have h1 : ∀ b, frT2 AF.fr (fun _ _ => (0 : ℝ)) a b = 0 := fun b => by simp [frT2]
  simp [h0, h1]

/-- **The normal Dirac relation of the residual-free normal jet**:
`Σ_Cε_Cc_C X^♮_C = 𝓜(H)Ψ` for `X^♮ = (X_0^♮, X_a)`. -/
theorem dirac_rel_Xnat (D : DiracData (MatLie m) V S₀) (ψ : S₀) (X : Fin 3 → S₀) (H : V) :
    ∑ C, lorentzSign C • D.Fr.c C ((Fin.cases (XnatU D ψ X H) X : Fin 4 → S₀) C) =
      mass D.m0 D.L H ψ := by
  have hc0 : D.Fr.c 0 * D.Fr.c 0 = 1 := c0_mul_c0 D
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ, lorentzSign, if_true, Fin.succ_ne_zero, if_false,
    one_smul]
  unfold XnatU
  have e : ∀ v : S₀, D.Fr.c 0 (D.Fr.c 0 v) = v := fun v => by
    rw [← Module.End.mul_apply, hc0, Module.End.one_apply]
  simp only [Module.End.smul_def, map_sub, e, neg_smul, one_smul]
  abel

end Algebra

/-! ### Coupled solutions of the shift-transported system -/

/-- **A solution of the shift-transported system whose bosonic blocks are actual and whose head
spinors solve the Dirac equations** (the setting of the coupled defect system). -/
structure CplSol (SM : SMData (MatLie m) V S S') (W : ST 3 → StateP m V S S')
    (z : Tuple m V S S') (a b : ℝ) : Prop where
  ms : MSol SM W z a b
  bos : ∀ y ∈ openSlab a b, prB m V S S' (W y) = prB m V S S' (stateF SM z y)
  dir : ∀ y ∈ openSlab a b, dirF SM z y = 0

variable {SM : SMData (MatLie m) V S S'} {W : ST 3 → StateP m V S S'} {z : Tuple m V S S'}
  {a b : ℝ}

theorem CplSol.ψ_eq (h : CplSol SM W z a b) {y : ST 3} (hy : y ∈ openSlab a b) :
    (W y).2.2.2.2.2.2.2.1 = (stateF SM z y).2.2.2.2.2.2.2.1 := h.ms.ψ y hy

theorem CplSol.ψb_eq (h : CplSol SM W z a b) {y : ST 3} (hy : y ∈ openSlab a b) :
    (W y).2.2.2.2.2.2.2.2.2.1 = (stateF SM z y).2.2.2.2.2.2.2.2.2.1 := h.ms.ψb y hy

/-- `FirstJet` with replaced spinor jets. -/
def withX (fj : FirstJet (MatLie m) V S S') (X : Fin 4 → S) (Xb : Fin 4 → S') :
    FirstJet (MatLie m) V S S' :=
  { fj with X := X, Xb := Xb }

/-- **Two states with the same bosonic blocks and head spinors have the same reconstructed first
jets except for the spinor jets.** -/
theorem recon_withX {v w : StateP m V S S'} (hB : prB m V S S' v = prB m V S S' w)
    (hψ : v.2.2.2.2.2.2.2.1 = w.2.2.2.2.2.2.2.1)
    (hψb : v.2.2.2.2.2.2.2.2.2.1 = w.2.2.2.2.2.2.2.2.2.1) :
    recon SM (ofP v) = withX (recon SM (ofP w)) (recon SM (ofP v)).X (recon SM (ofP v)).Xb := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := prB_eq_iff.1 hB
  obtain ⟨v1, vA, vE, vB, vH, vP, vQ, vψ, vX, vψb, vXb⟩ := v
  obtain ⟨w1, wA, wE, wB, wH, wP, wQ, wψ, wX, wψb, wXb⟩ := w
  simp only at h1 h2 h3 h4 h5 h6 h7 hψ hψb
  subst h1 h2 h3 h4 h5 h6 h7 hψ hψb
  rfl

/-- The `g`- and `H`-head rows of the forcing depend only on the bosonic blocks. -/
theorem Fsys_gH_congr {v w : StateP m V S S'} (hB : prB m V S S' v = prB m V S S' w) :
    (Fsys SM (ofP v)).g = (Fsys SM (ofP w)).g ∧ (Fsys SM (ofP v)).H = (Fsys SM (ofP w)).H := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := prB_eq_iff.1 hB
  obtain ⟨v1, vA, vE, vB, vH, vP, vQ, vψ, vX, vψb, vXb⟩ := v
  obtain ⟨w1, wA, wE, wB, wH, wP, wQ, wψ, wX, wψb, wXb⟩ := w
  simp only at h1 h2 h3 h4 h5 h6 h7
  subst h1 h2 h3 h4 h5 h6 h7
  exact ⟨rfl, rfl⟩

theorem fDiff_congr' {v w : StateP m V S S'} (hB : prB m V S S' v = prB m V S S' w) :
    AJKatoMod.fDiff SM v = AJKatoMod.fDiff SM w := by
  obtain ⟨hg, hH⟩ := Fsys_gH_congr (SM := SM) hB
  obtain ⟨h1, hA, -, -, hH', hP, -⟩ := prB_eq_iff.1 hB
  unfold AJKatoMod.fDiff
  rw [h1, hA, hH', hP, hg, hH]

/-- **`W` solves the original realized rows** (coupled spinors: the shift-transport terms cancel
on actual metric and Higgs jets; no decoupling hypothesis). -/
theorem orig_row_cpl (h : CplSol SM W z a b) :
    ∀ x ∈ openSlab a b, pd W 0 x + ∑ j : Fin 3, princL SM (W x) j (pd W j.succ x) =
      toP (Fsys SM (ofP (W x))) := by
  have hO := isOpen_openSlab (d := 3) a b
  have hW1 : ContDiffOn ℝ 1 W (openSlab a b) := h.ms.smooth.of_le (by norm_cast)
  have hUd : DifferentiableOn ℝ (stateF SM z) (openSlab a b) :=
    ((contDiff_stateF SM z).differentiable (by simp)).differentiableOn
  have hpd := pd_block_eq' hO hW1 hUd (prB m V S S') h.bos
  intro x hx
  have hrow := h.ms.row x hx
  rw [AJKatoMod.FsysM_eq] at hrow
  simp only [AJKatoMod.princPM_eq, Finset.sum_add_distrib] at hrow
  have hext : ∑ j : Fin 3, AJKatoMod.extraP ((frameU (ginvOf (W x).1.1)).β j) (pd W j.succ x) =
      AJKatoMod.fDiff SM (W x) := by
    have h1 : (W x).1.1 = (stateF SM z x).1.1 :=
      congrArg Prod.fst (prB_eq_iff.1 (h.bos x hx)).1
    rw [h1, fDiff_congr' (h.bos x hx), ← AJKatoMod.sum_extra_eq_fDiff]
    refine Finset.sum_congr rfl fun j _ => extraP_congr ?_ ?_
    · exact congrArg Prod.fst (prB_eq_iff.1 (hpd x hx j.succ)).1
    · exact (prB_eq_iff.1 (hpd x hx j.succ)).2.2.2.2.1
  rw [hext, ← add_assoc] at hrow
  exact add_right_cancel hrow

/-- The principal operators depend only on the metric block. -/
theorem princL_congr {v w : StateP m V S S'} (h : v.1.1 = w.1.1) (j : Fin 3) (u : StateP m V S S') :
    princL SM v j u = princL SM w j u := by
  unfold princL
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [h]

/-- **The difference rows**: `D = W - 𝒰(z)` satisfies
`∂_tD + Σ_j𝒜^j∂_jD = 𝓕(W) - 𝓕(𝒰(z)) - errF(z)`. -/
theorem diff_row (h : CplSol SM W z a b) {x : ST 3} (hx : x ∈ openSlab a b) :
    pd (fun y => W y - stateF SM z y) 0 x +
        ∑ j : Fin 3, princL SM (stateF SM z x) j (pd (fun y => W y - stateF SM z y) j.succ x) =
      toP (Fsys SM (ofP (W x))) - toP (Fsys SM (ofP (stateF SM z x))) - errF SM z x := by
  have hO := isOpen_openSlab (d := 3) a b
  have hW1 : ContDiffOn ℝ 1 W (openSlab a b) := h.ms.smooth.of_le (by norm_cast)
  have hdW : DifferentiableAt ℝ W x := GenHarmonic.diffAt_of_contDiffOn hO hW1 one_ne_zero hx
  have hdU : DifferentiableAt ℝ (stateF SM z) x := (contDiff_stateF SM z).differentiable (by simp) x
  have hg : (W x).1.1 = (stateF SM z x).1.1 := congrArg Prod.fst (prB_eq_iff.1 (h.bos x hx)).1
  have hrW := orig_row_cpl h x hx
  have hrU := writer_pde_err SM z x
  simp only [GenDefJet.pd_sub_eq hdW hdU, map_sub, Finset.sum_sub_distrib]
  rw [← hrW, sub_sub, ← hrU]
  simp only [princL_congr (SM := SM) hg]
  abel

end RenewalGeometry.GenCplRows
