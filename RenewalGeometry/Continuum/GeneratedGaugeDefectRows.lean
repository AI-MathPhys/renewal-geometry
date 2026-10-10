/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedGaugeDefect

/-!
# The Maxwell `B`-row of a reconstructed field strength is its normal Bianchi relation

Einstein–Standard-Model action-closure manuscript, `prop:actual-jet-writer` (the `B`-row
`∂_tB_a - βʲ∂_jB_a + N ε_{abc}e_bʲ∂_jE_c = N L^B_a`), `lem:generated-physical-identification`.

For an **arbitrary** antisymmetric array `T_{μν}` with derivative jets `∂_γT_{μν}` (not
necessarily a curvature), with frame components `E_a = T(e_0, e_a)`, `B_a = -½ε_{abc}T(e_b, e_c)`,
the frame form of the `B`-row holds up to the normal contraction of the Bianchi expression
`Bian(T)_{γμν} = ∂_γT_{μν} + ∂_μT_{νγ} + ∂_νT_{γμ} + [A_γ, T_{μν}] + [A_μ, T_{νγ}] + [A_ν, T_{γμ}]`
(`frame_B_identity`).  Hence the `B`-row holds iff `e_0{}^γ Bian(T)_{γμν}(e_b, e_c) = 0`, i.e.
(by total antisymmetry and the inversion of the frame) iff `Bian(T)_{0μν} = βʲ Bian(T)_{jμν}`
(`normal_bianchi_of_frame`): this is `GenGaugeDefect.NormalBianchi`.
-/

open Finset Set Filter Topology
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.GenGaugeRows

open SobolevOpen (pd)
open SymHypEnergy PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge ActualJetBridge ActualJetState
  ActualJetCompleteForcing ActualJetRecon GenConstraint GenNoether

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

/-! ### The frame algebra of the `B`-row for a general array -/

section FrameAlg

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
variable (F : AdaptedFrame) (de : Fin 4 → Fin 4 → Fin 4 → ℝ)
variable (A : Fin 4 → 𝔤) (T : Fin 4 → Fin 4 → 𝔤) (dT : Fin 4 → Fin 4 → Fin 4 → 𝔤)

/-- The bracket part of the Bianchi expression. -/
def brT (γ μ ν : Fin 4) : 𝔤 := ⁅A γ, T μ ν⁆ + ⁅A μ, T ν γ⁆ + ⁅A ν, T γ μ⁆

/-- **The Bianchi expression of an array with derivative jets.** -/
def bianT (γ μ ν : Fin 4) : 𝔤 := dT γ μ ν + dT μ ν γ + dT ν γ μ + brT A T γ μ ν

/-- The electric derivative jets `∂_γ T(e_0, e_a)`. -/
def dEg (γ : Fin 4) (a : Fin 3) : 𝔤 := dfrT F de T dT γ 0 a.succ

/-- The magnetic derivative jets `∂_γ B_a`. -/
def dBg (γ : Fin 4) (a : Fin 3) : 𝔤 :=
  dualVec (fun b c : Fin 3 => dfrT F de T dT γ b.succ c.succ) a

/-- The normal contraction `Σ e_b{}^μ e_c{}^ν e_0{}^γ Bian_{γμν}`. -/
def bianC (b c : Fin 4) : 𝔤 :=
  ∑ μ, ∑ ν, ∑ γ, (F.fr b μ * F.fr c ν * F.fr 0 γ) • bianT A T dT γ μ ν

/-- The normal frame derivative of the spatial components of a general array. -/
theorem fD_dFsp_gen (hT : ∀ μ ν, T ν μ = -T μ ν) (hdT : ∀ γ μ ν, dT γ ν μ = -dT γ μ ν)
    (b c : Fin 3) :
    fD F (fun γ => dfrT F de T dT γ b.succ c.succ) 0 =
      lowT F de T 0 b.succ c.succ + fD F (fun γ => dEg F de T dT γ c) b.succ +
        lowT F de T b.succ c.succ 0 - fD F (fun γ => dEg F de T dT γ b) c.succ +
        lowT F de T c.succ 0 b.succ - brCf F A T b.succ c.succ +
        bianC F A T dT b.succ c.succ := by
  have h1 := fD_dfrT F de T dT 0 b.succ c.succ
  have h3 := fD_dfrT F de T dT b.succ c.succ 0
  have h4 := fD_dfrT F de T dT c.succ 0 b.succ
  have hbi : ∀ γ μ ν, dT γ μ ν =
      bianT A T dT γ μ ν - dT μ ν γ - dT ν γ μ - brT A T γ μ ν := by
    intro γ μ ν; unfold bianT; abel
  have hB : ∑ μ, ∑ ν, (F.fr b.succ μ * F.fr c.succ ν) • fD F (fun γ => dT γ μ ν) 0 =
      bianC F A T dT b.succ c.succ -
      (∑ μ, ∑ ν, ∑ γ, (F.fr b.succ μ * F.fr c.succ ν * F.fr 0 γ) • dT μ ν γ) -
        ∑ μ, ∑ ν, ∑ γ, (F.fr b.succ μ * F.fr c.succ ν * F.fr 0 γ) • dT ν γ μ -
          brCf F A T b.succ c.succ := by
    have e : ∑ μ, ∑ ν, (F.fr b.succ μ * F.fr c.succ ν) • fD F (fun γ => dT γ μ ν) 0 =
        ∑ μ, ∑ ν, ∑ γ, (F.fr b.succ μ * F.fr c.succ ν * F.fr 0 γ) •
          (bianT A T dT γ μ ν - dT μ ν γ - dT ν γ μ - brT A T γ μ ν) := by
      unfold fD
      refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun γ _ => ?_
      rw [smul_smul]
      show _ • dT γ μ ν = _
      rw [hbi γ μ ν]
    rw [e]
    unfold brCf bianC
    simp only [smul_sub, Finset.sum_sub_distrib]
    rfl
  have e3 : ∑ μ, ∑ ν, ∑ γ, (F.fr b.succ μ * F.fr c.succ ν * F.fr 0 γ) • dT μ ν γ =
      fD F (fun γ => dfrT F de T dT γ c.succ 0) b.succ - lowT F de T b.succ c.succ 0 := by
    rw [h3, add_sub_cancel_left, sum3_cycle]
    unfold fD
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun γ _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [smul_smul]; congr 1; ring
  have e4 : ∑ μ, ∑ ν, ∑ γ, (F.fr b.succ μ * F.fr c.succ ν * F.fr 0 γ) • dT ν γ μ =
      fD F (fun γ => dfrT F de T dT γ 0 b.succ) c.succ - lowT F de T c.succ 0 b.succ := by
    rw [h4, add_sub_cancel_left, sum3_cycle']
    unfold fD
    refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [smul_smul]; congr 1; ring
  have e5 : (fun γ => dfrT F de T dT γ c.succ 0) = fun γ => -dEg F de T dT γ c := by
    funext γ
    exact dfrT_anti F de hT hdT γ 0 c.succ
  have hneg : fD F (fun γ => -dEg F de T dT γ c) b.succ =
      -fD F (fun γ => dEg F de T dT γ c) b.succ := by
    have := fD_smul F (-1 : ℝ) (fun γ => dEg F de T dT γ c) b.succ
    simpa [neg_one_smul] using this
  rw [h1, hB, e3, e4, e5, hneg]
  unfold dEg
  abel

/-- **The frame form of the `B`-row for a general array**: `e_0(B_a) + ε_{abc} e_b(E_c) =
L^B_a - ½ ε_{abc} e_0{}^γBian_{γ}(e_b, e_c)`. -/
theorem frame_B_identity (hT : ∀ μ ν, T ν μ = -T μ ν) (hdT : ∀ γ μ ν, dT γ ν μ = -dT γ μ ν)
    (a : Fin 3) :
    fD F (fun γ => dBg F de T dT γ a) 0 +
        ∑ b, ∑ c, eps3 a b c • fD F (fun γ => dEg F de T dT γ c) b.succ =
      LBf F de A T a +
        -(1 / 2 : ℝ) • ∑ b, ∑ c, eps3 a b c • bianC F A T dT b.succ c.succ := by
  have h6 : fD F (fun γ => dBg F de T dT γ a) 0 =
      -(1 / 2 : ℝ) • ∑ b, ∑ c, eps3 a b c • fD F (fun γ => dfrT F de T dT γ b.succ c.succ) 0 := by
    unfold dBg dualVec
    rw [fD_smul]
    congr 1
    exact fD_sum2_smul F (fun b c => eps3 a b c)
      (fun b c γ => dfrT F de T dT γ b.succ c.succ) 0
  rw [h6]
  simp_rw [fD_dFsp_gen F de A T dT hT hdT]
  have hswap : ∑ b, ∑ c, eps3 a b c • fD F (fun γ => dEg F de T dT γ b) c.succ =
      -∑ b, ∑ c, eps3 a b c • fD F (fun γ => dEg F de T dT γ c) b.succ := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [eps3_swap23, neg_smul]
  unfold LBf
  simp only [smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hswap]
  simp only [smul_neg]
  module

end FrameAlg

/-! ### From the vanishing normal contraction to the normal Bianchi relation -/

section Normal

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
variable (F : AdaptedFrame) (A : Fin 4 → 𝔤) (T : Fin 4 → Fin 4 → 𝔤)
  (dT : Fin 4 → Fin 4 → Fin 4 → 𝔤)

theorem brT_anti12 (hT : ∀ μ ν, T ν μ = -T μ ν) (γ μ ν : Fin 4) :
    brT A T μ γ ν = -brT A T γ μ ν := by
  unfold brT
  rw [hT ν μ, hT γ ν, hT μ γ, lie_neg, lie_neg, lie_neg]
  abel

theorem brT_anti23 (hT : ∀ μ ν, T ν μ = -T μ ν) (γ μ ν : Fin 4) :
    brT A T γ ν μ = -brT A T γ μ ν := by
  unfold brT
  rw [hT ν μ, hT μ γ, hT γ ν, lie_neg, lie_neg, lie_neg]
  abel

theorem bianT_anti12 (hT : ∀ μ ν, T ν μ = -T μ ν) (hdT : ∀ γ μ ν, dT γ ν μ = -dT γ μ ν)
    (γ μ ν : Fin 4) : bianT A T dT μ γ ν = -bianT A T dT γ μ ν := by
  unfold bianT
  rw [brT_anti12 A T hT, hdT μ γ ν, hdT γ ν μ, hdT ν μ γ]
  abel

theorem bianT_anti23 (hT : ∀ μ ν, T ν μ = -T μ ν) (hdT : ∀ γ μ ν, dT γ ν μ = -dT γ μ ν)
    (γ μ ν : Fin 4) : bianT A T dT γ ν μ = -bianT A T dT γ μ ν := by
  unfold bianT
  rw [brT_anti23 A T hT, hdT γ ν μ, hdT ν γ μ, hdT μ ν γ]
  abel

/-- The normal contraction `S_{μν} = e_0{}^γ Bian_{γμν}`. -/
def normS (μ ν : Fin 4) : 𝔤 := ∑ γ, F.fr 0 γ • bianT A T dT γ μ ν

theorem bianC_eq_frT (b c : Fin 4) : bianC F A T dT b c = frT F (normS F A T dT) b c := by
  unfold bianC frT normS
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [smul_smul]

theorem bianC_zero_left (hT : ∀ μ ν, T ν μ = -T μ ν) (hdT : ∀ γ μ ν, dT γ ν μ = -dT γ μ ν)
    (c : Fin 4) : bianC F A T dT 0 c = 0 := by
  unfold bianC
  have h : ∀ ν, ∑ μ, ∑ γ, (F.fr 0 μ * F.fr c ν * F.fr 0 γ) • bianT A T dT γ μ ν = 0 := by
    intro ν
    have e : ∑ μ, ∑ γ, (F.fr 0 μ * F.fr c ν * F.fr 0 γ) • bianT A T dT γ μ ν =
        F.fr c ν • ∑ μ, ∑ γ, (F.fr 0 μ * F.fr 0 γ) • bianT A T dT γ μ ν := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun γ _ => ?_
      rw [smul_smul]; congr 1; ring
    rw [e, GenNoether.sum_sym_anti_eq_zero (fun μ γ => F.fr 0 μ * F.fr 0 γ)
      (fun μ γ => bianT A T dT γ μ ν) (fun μ γ => mul_comm _ _)
      (fun μ γ => bianT_anti12 A T dT hT hdT γ μ ν), smul_zero]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun ν _ => h ν

/-- From the vanishing of the contractions `e_0{}^γ Bian_γ(e_b, e_c)` for spatial `b, c`,
all frame components of `S` vanish (total antisymmetry). -/
theorem frT_normS_zero (hT : ∀ μ ν, T ν μ = -T μ ν) (hdT : ∀ γ μ ν, dT γ ν μ = -dT γ μ ν)
    (h : ∀ b c : Fin 3, bianC F A T dT b.succ c.succ = 0) (B C : Fin 4) :
    frT F (normS F A T dT) B C = 0 := by
  rw [← bianC_eq_frT]
  induction B using Fin.cases with
  | zero => exact bianC_zero_left F A T dT hT hdT C
  | succ b =>
    induction C using Fin.cases with
    | zero =>
      rw [bianC_eq_frT, frT_anti F (fun μ ν => by
        unfold normS
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun γ _ => ?_
        rw [bianT_anti23 A T dT hT hdT, smul_neg]), ← bianC_eq_frT,
        bianC_zero_left F A T dT hT hdT, neg_zero]
    | succ c => exact h b c

end Normal

/-! ### Coframe duality -/

section Duality

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

theorem cof_e_dual (FJ : FrameJet (Fin 4) (Fin 4)) (X B : Fin 4) :
    ∑ μ, cof FJ.g FJ.ε FJ.e X μ * FJ.e B μ = if X = B then 1 else 0 := by
  have e : ∑ μ, cof FJ.g FJ.ε FJ.e X μ * FJ.e B μ = FJ.ε X * ipg FJ.g (FJ.e X) (FJ.e B) := by
    unfold cof ipg
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun μ _ => ?_
    rw [FJ.g_symm μ ν]; ring
  rw [e, FJ.orth X B]
  split_ifs with h
  · subst h; have := FJ.sign_sq X; rw [← sq]; exact this
  · simp

theorem sum4_swap {N : Type*} [AddCommMonoid N] (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → N) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := Finset.sum_congr rfl fun c _ => Finset.sum_comm

/-- **The frame components of a coframe-reconstructed array are the array.** -/
theorem frT_recon (FJ : FrameJet (Fin 4) (Fin 4)) (AF : AdaptedFrame)
    (hfr : ∀ B μ, FJ.e B μ = AF.fr B μ) (G : Fin 4 → Fin 4 → M) (B C : Fin 4) :
    frT AF (fun μ ν => ∑ X, ∑ Y, (cof FJ.g FJ.ε FJ.e X μ * cof FJ.g FJ.ε FJ.e Y ν) • G X Y)
      B C = G B C := by
  unfold frT
  have e1 : ∑ μ, ∑ ν, (AF.fr B μ * AF.fr C ν) • ∑ X, ∑ Y,
      (cof FJ.g FJ.ε FJ.e X μ * cof FJ.g FJ.ε FJ.e Y ν) • G X Y =
      ∑ X, ∑ Y, ∑ μ, ∑ ν, ((cof FJ.g FJ.ε FJ.e X μ * FJ.e B μ) *
        (cof FJ.g FJ.ε FJ.e Y ν * FJ.e C ν)) • G X Y := by
    simp only [Finset.smul_sum, smul_smul]
    rw [sum4_swap]
    refine Finset.sum_congr rfl fun X _ => Finset.sum_congr rfl fun Y _ =>
      Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
    rw [hfr, hfr]; congr 1; ring
  have e2 : ∀ X Y, ∑ μ, ∑ ν, ((cof FJ.g FJ.ε FJ.e X μ * FJ.e B μ) *
      (cof FJ.g FJ.ε FJ.e Y ν * FJ.e C ν)) • G X Y =
      ((∑ μ, cof FJ.g FJ.ε FJ.e X μ * FJ.e B μ) *
        (∑ ν, cof FJ.g FJ.ε FJ.e Y ν * FJ.e C ν)) • G X Y := by
    intro X Y
    rw [Finset.sum_mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.sum_smul]
  rw [e1]
  simp only [e2, cof_e_dual, ite_mul, one_mul, zero_mul, ite_smul, one_smul, zero_smul]
  simp

end Duality

/-! ### The reconstructed field strength of a state field -/

section Field

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable (SM : SMData (MatLie m) V S S')

/-- The coordinate field strength reconstructed from the auxiliary variables `(E, B)` of a state
field. -/
def Trec (W : ST 3 → StateP m V S S') (x : ST 3) : Fin 4 → Fin 4 → MatLie m :=
  (recon SM (ofP (W x))).F

theorem dualVec_eps {M : Type*} [AddCommGroup M] [Module ℝ M] (B : Fin 3 → M) (a : Fin 3) :
    dualVec (fun b c : Fin 3 => -∑ d, eps3 b c d • B d) a = B a := by
  unfold dualVec
  fin_cases a <;> simp [Fin.sum_univ_three, eps3] <;> module

/-- The metric fields of the reconstruction depend only on the metric block. -/
theorem recon_metric_eq {v w : StateP m V S S'} (h : v.1 = w.1) :
    (recon SM (ofP v)).g = (recon SM (ofP w)).g ∧ (recon SM (ofP v)).gi = (recon SM (ofP w)).gi ∧
      (recon SM (ofP v)).dg = (recon SM (ofP w)).dg ∧
      (recon SM (ofP v)).AF = (recon SM (ofP w)).AF ∧
      (recon SM (ofP v)).de = (recon SM (ofP w)).de := by
  obtain ⟨v1, v2⟩ := v
  obtain ⟨w1, w2⟩ := w
  simp only at h
  subst h
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

variable {SM}

/-- The reconstruction of a state with the metric block of an actual-jet state carries the actual
metric, frame and frame jets. -/
theorem recon_metric_actual {z : Tuple m V S S'} {v : StateP m V S S'} {x : ST 3}
    (h : v.1 = (stateF SM z x).1) :
    (recon SM (ofP v)).g = z.g x ∧ (recon SM (ofP v)).gi = z.gi x ∧
      (recon SM (ofP v)).dg = z.dg x ∧ (recon SM (ofP v)).AF = frameU (z.gi x) ∧
      (recon SM (ofP v)).de = z.de x := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := recon_metric_eq SM h
  have hr := ActualJet.recon_state (z.jet x) SM
  have e : ofP (stateF SM z x) = (z.jet x).state SM := rfl
  rw [e, hr] at h1 h2 h3 h4 h5
  exact ⟨h1, h2, h3, h4.trans (ActualJet.frameU_eq' (z.jet x)).symm, h5⟩

/-- The coframe of the reconstruction is the coframe of the tuple. -/
theorem recon_F_eq {z : Tuple m V S S'} {v : StateP m V S S'} {x : ST 3}
    (h : v.1 = (stateF SM z x).1) (μ ν : Fin 4) :
    (recon SM (ofP v)).F μ ν = ∑ X, ∑ Y, (cof (z.jet x).FJ.g (z.jet x).FJ.ε (z.jet x).FJ.e X μ *
      cof (z.jet x).FJ.g (z.jet x).FJ.ε (z.jet x).FJ.e Y ν) • fieldOfEB v.2.2.1 v.2.2.2.1 X Y := by
  have hg : v.1.1 = z.g x := by rw [h]; rfl
  have hfr : ∀ B μ, (z.jet x).FJ.e B μ = (frameU (z.gi x)).fr B μ := fun B μ =>
    GenConstraint.jet_e_eq z x B μ
  have hgi : ginvOf v.1.1 = z.gi x := by rw [hg]; rfl
  show ∑ X, ∑ Y, (cof (ofP v).g lorentzSign (frameU (ginvOf (ofP v).g)).fr X μ *
      cof (ofP v).g lorentzSign (frameU (ginvOf (ofP v).g)).fr Y ν) •
        fieldOfEB (ofP v).E (ofP v).B X Y = _
  have e1 : (ofP v).g = z.g x := hg
  rw [e1]
  have e3 : (z.jet x).FJ.e = (frameU (z.gi x)).fr := funext fun B => funext fun μ => hfr B μ
  rw [e3]
  rfl

/-- **The electric auxiliary variables are the frame components of the reconstruction.** -/
theorem E_eq_frT {z : Tuple m V S S'} {v : StateP m V S S'} {x : ST 3}
    (h : v.1 = (stateF SM z x).1) (a : Fin 3) :
    v.2.2.1 a = frT (frameU (z.gi x)) (recon SM (ofP v)).F 0 a.succ := by
  have hF : (recon SM (ofP v)).F = fun μ ν => ∑ X, ∑ Y,
      (cof (z.jet x).FJ.g (z.jet x).FJ.ε (z.jet x).FJ.e X μ *
        cof (z.jet x).FJ.g (z.jet x).FJ.ε (z.jet x).FJ.e Y ν) • fieldOfEB v.2.2.1 v.2.2.2.1 X Y :=
    funext fun μ => funext fun ν => recon_F_eq h μ ν
  rw [hF, frT_recon (z.jet x).FJ (frameU (z.gi x)) (GenConstraint.jet_e_eq z x)]
  rfl

/-- **The magnetic auxiliary variables are the dual frame components of the reconstruction.** -/
theorem B_eq_frT {z : Tuple m V S S'} {v : StateP m V S S'} {x : ST 3}
    (h : v.1 = (stateF SM z x).1) (a : Fin 3) :
    v.2.2.2.1 a = dualVec (fun b c : Fin 3 =>
      frT (frameU (z.gi x)) (recon SM (ofP v)).F b.succ c.succ) a := by
  have hF : (recon SM (ofP v)).F = fun μ ν => ∑ X, ∑ Y,
      (cof (z.jet x).FJ.g (z.jet x).FJ.ε (z.jet x).FJ.e X μ *
        cof (z.jet x).FJ.g (z.jet x).FJ.ε (z.jet x).FJ.e Y ν) • fieldOfEB v.2.2.1 v.2.2.2.1 X Y :=
    funext fun μ => funext fun ν => recon_F_eq h μ ν
  simp only [hF, frT_recon (z.jet x).FJ (frameU (z.gi x)) (GenConstraint.jet_e_eq z x)]
  exact (dualVec_eps v.2.2.2.1 a).symm

/-- The reconstruction of an actual-jet state is the actual field strength. -/
theorem recon_F_actual (z : Tuple m V S S') (x : ST 3) :
    (recon SM (ofP (stateF SM z x))).F = fun μ ν => GenNoether.Fld z x μ ν := by
  have hr := ActualJet.recon_state (z.jet x) SM
  have e : ofP (stateF SM z x) = (z.jet x).state SM := rfl
  rw [e, hr]
  rfl

/-- The reconstructed field strength is antisymmetric. -/
theorem recon_F_anti (v : StateP m V S S') (μ ν : Fin 4) :
    (recon SM (ofP v)).F ν μ = -(recon SM (ofP v)).F μ ν := by
  unfold recon
  dsimp only
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun X _ => ?_
  rw [← smul_neg, mul_comm]
  congr 1
  induction X using Fin.cases with
  | zero =>
    induction Y using Fin.cases with
    | zero => simp [fieldOfEB]
    | succ c => simp [fieldOfEB]
  | succ b =>
    induction Y using Fin.cases with
    | zero => simp [fieldOfEB]
    | succ c =>
      simp only [fieldOfEB, Fin.cases_succ, neg_neg]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [eps3_swap12, neg_smul, neg_neg]

end Field

/-! ### The `B`-row of a state field gives the normal Bianchi relation -/

section RowToBianchi

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable {SM : SMData (MatLie m) V S S'}

theorem hasDerivAt_fst' {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → E × F} {f' : E × F} {t : ℝ}
    (h : HasDerivAt f f' t) : HasDerivAt (fun s => (f s).1) f'.1 t :=
  (ContinuousLinearMap.fst ℝ E F).hasFDerivAt.comp_hasDerivAt t h

theorem hasDerivAt_snd' {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → E × F} {f' : E × F} {t : ℝ}
    (h : HasDerivAt f f' t) : HasDerivAt (fun s => (f s).2) f'.2 t :=
  (ContinuousLinearMap.snd ℝ E F).hasFDerivAt.comp_hasDerivAt t h

/-- The reconstructed field strength is smooth on the chart. -/
theorem contDiffAt_reconF {x0 : StateP m V S S'} (hx : MetChart x0.1) (μ ν : Fin 4) :
    ContDiffAt ℝ ∞ (fun x : StateP m V S S' => (recon SM (ofP x)).F μ ν) x0 := by
  simp only [recon, ofP, cof, lorentzSign]
  fun_prop (disch := first | exact hx.1 | exact hx.2)

theorem contDiffOn_Trec {W : ST 3 → StateP m V S S'} {O : Set (ST 3)} (hO : IsOpen O)
    (hW : ContDiffOn ℝ ∞ W O) (hc : ∀ x ∈ O, MetChart (W x).1) :
    ContDiffOn ℝ ∞ (Trec SM W) O := by
  refine contDiffOn_pi.2 fun μ => contDiffOn_pi.2 fun ν => fun x hx => ?_
  exact ((contDiffAt_reconF (SM := SM) (hc x hx) μ ν).comp x
    (hW.contDiffAt (hO.mem_nhds hx))).contDiffWithinAt

/-- **The product rule for frame components of a field** along a coordinate line. -/
theorem hasDerivAt_frT (z : Tuple m V S S') {Tf : ST 3 → Fin 4 → Fin 4 → MatLie m} {x : ST 3}
    (hT : DifferentiableAt ℝ Tf x) (γ B C : Fin 4) :
    HasDerivAt (fun s : ℝ => frT (frameU (z.gi (x + s • ev γ))) (Tf (x + s • ev γ)) B C)
      (dfrT (frameU (z.gi x)) (z.de x) (Tf x)
        (fun γ' μ ν => pd (GenGaugeDefect.Tc Tf μ ν) γ' x) γ B C) 0 := by
  have hTc : ∀ μ ν, DifferentiableAt ℝ (GenGaugeDefect.Tc Tf μ ν) x := fun μ ν =>
    (differentiableAt_pi.1 ((differentiableAt_pi.1 hT) μ)) ν
  have e1 : (fun s : ℝ => frT (frameU (z.gi (x + s • ev γ))) (Tf (x + s • ev γ)) B C) =
      fun s => ∑ μ, ∑ ν, (z.e (x + s • ev γ) B μ * z.e (x + s • ev γ) C ν) •
        Tf (x + s • ev γ) μ ν := by
    funext s; unfold frT; simp only [GenGauss.e_eq_frameU]
  have e2 : dfrT (frameU (z.gi x)) (z.de x) (Tf x)
      (fun γ' μ ν => pd (GenGaugeDefect.Tc Tf μ ν) γ' x) γ B C =
      ∑ μ, ∑ ν, ((z.de x γ B μ * z.e x C ν + z.e x B μ * z.de x γ C ν) • Tf x μ ν +
        (z.e x B μ * z.e x C ν) • pd (GenGaugeDefect.Tc Tf μ ν) γ x) := by
    unfold dfrT; simp only [GenGauss.e_eq_frameU]
  rw [e1, e2]
  refine HasDerivAt.fun_sum fun μ _ => HasDerivAt.fun_sum fun ν _ => ?_
  have h1 := ((z.line_e x γ B μ).mul (z.line_e x γ C ν)).smul
    (ActualJetBridge.hasDerivAt_line0 (hTc μ ν) γ)
  refine h1.congr_deriv ?_
  simp only [Pi.mul_apply, zero_smul, add_zero, GenGaugeDefect.Tc]
  rw [add_comm]

variable (SM) in
/-- The `B`-block of the modified system at a point. -/
theorem row_B {W : ST 3 → StateP m V S S'} {x : ST 3}
    (hrow : pd W 0 x + ∑ j : Fin 3, AJKatoMod.princPM SM (W x) j (pd W j.succ x) =
      toP (AJKatoMod.FsysM SM (ofP (W x)))) (a : Fin 3) :
    (pd W 0 x).2.2.2.1 a + ∑ j : Fin 3, (-((frameU (ginvOf (W x).1.1)).β j •
        (pd W j.succ x).2.2.2.1 a) + (frameU (ginvOf (W x).1.1)).N • ∑ b, ∑ c,
          eps3 a b c • ((frameU (ginvOf (W x).1.1)).E b j • (pd W j.succ x).2.2.1 c)) =
      (frameU (ginvOf (W x).1.1)).N • LBf (recon SM (ofP (W x))).AF (recon SM (ofP (W x))).de
        (recon SM (ofP (W x))).A (recon SM (ofP (W x))).F a := by
  have h := congrArg (fun v : StateP m V S S' => v.2.2.2.1 a) hrow
  simp only [Prod.snd_add, Prod.fst_add, Prod.snd_sum, Prod.fst_sum, Finset.sum_apply,
    Pi.add_apply] at h
  have e1 : ∀ j : Fin 3, (AJKatoMod.princPM SM (W x) j (pd W j.succ x)).2.2.2.1 a =
      -((frameU (ginvOf (W x).1.1)).β j • (pd W j.succ x).2.2.2.1 a) +
        (frameU (ginvOf (W x).1.1)).N • ∑ b, ∑ c,
          eps3 a b c • ((frameU (ginvOf (W x).1.1)).E b j • (pd W j.succ x).2.2.1 c) :=
    fun j => rfl
  have e2 : (toP (AJKatoMod.FsysM SM (ofP (W x)))).2.2.2.1 a =
      (frameU (ginvOf (W x).1.1)).N • LBf (recon SM (ofP (W x))).AF (recon SM (ofP (W x))).de
        (recon SM (ofP (W x))).A (recon SM (ofP (W x))).F a := rfl
  rw [e2] at h
  simp only [e1] at h
  exact h

set_option maxHeartbeats 2000000 in -- large frame-algebra normalisation
/-- **The `B`-row and the head rows give the normal Bianchi relation** at a point where the
metric block of the state field is the actual one. -/
theorem normal_bianchi_at (z : Tuple m V S S') {W : ST 3 → StateP m V S S'} {O : Set (ST 3)}
    (hO : IsOpen O) (hW : ContDiffOn ℝ ∞ W O) (hc : ∀ y ∈ O, MetChart (W y).1)
    (hmet : ∀ y ∈ O, (W y).1 = (stateF SM z y).1)
    (hA : ∀ y ∈ O, ∀ i : Fin 3, (W y).2.1 i = z.A y i.succ)
    {x : ST 3} (hx : x ∈ O)
    (hrow : pd W 0 x + ∑ j : Fin 3, AJKatoMod.princPM SM (W x) j (pd W j.succ x) =
      toP (AJKatoMod.FsysM SM (ofP (W x)))) (i j : Fin 3) :
    GenGaugeDefect.bian z (Trec SM W) x 0 i.succ j.succ =
      ∑ k : Fin 3, (frameU (z.gi x)).β k • GenGaugeDefect.bian z (Trec SM W) x k.succ i.succ j.succ := by
  set T := Trec SM W with hTdef
  set F := frameU (z.gi x) with hF
  set dT : Fin 4 → Fin 4 → Fin 4 → MatLie m := fun γ μ ν => pd (GenGaugeDefect.Tc T μ ν) γ x
    with hdT
  have hTs : ContDiffOn ℝ ∞ T O := contDiffOn_Trec hO hW hc
  have hTd : DifferentiableAt ℝ T x := GenHarmonic.diffAt_of_contDiffOn hO hTs (by simp) hx
  have hTa : ∀ y μ ν, T y ν μ = -T y μ ν := fun y μ ν => recon_F_anti (W y) μ ν
  have hTx : ∀ μ ν, T x ν μ = -T x μ ν := fun μ ν => hTa x μ ν
  have hdTa : ∀ γ μ ν, dT γ ν μ = -dT γ μ ν := by
    intro γ μ ν
    show pd (GenGaugeDefect.Tc T ν μ) γ x = -pd (GenGaugeDefect.Tc T μ ν) γ x
    have e : GenGaugeDefect.Tc T ν μ = fun y => -GenGaugeDefect.Tc T μ ν y :=
      funext fun y => hTa y μ ν
    rw [e]
    unfold SobolevOpen.pd
    rw [fderiv_fun_neg]
    rfl
  -- the reconstruction at `x`
  obtain ⟨-, hgi, -, hAF, hde⟩ := recon_metric_actual (SM := SM) (hmet x hx)
  have hrA : (recon SM (ofP (W x))).A = z.A x := by
    funext μ
    induction μ using Fin.cases with
    | zero => exact (z.temporal x).symm
    | succ i => exact hA x hx i
  have hgW : ginvOf (W x).1.1 = z.gi x := by
    have h1 : (W x).1.1 = z.g x := by rw [hmet x hx]; rfl
    rw [h1]; rfl
  -- the auxiliary fields near `x` are frame components of `T`
  have hEf : ∀ y ∈ O, ∀ c : Fin 3, (W y).2.2.1 c = frT (frameU (z.gi y)) (T y) 0 c.succ :=
    fun y hy c => E_eq_frT (hmet y hy) c
  have hBf : ∀ y ∈ O, ∀ c : Fin 3, (W y).2.2.2.1 c = dualVec (fun b c : Fin 3 =>
      frT (frameU (z.gi y)) (T y) b.succ c.succ) c := fun y hy c => B_eq_frT (hmet y hy) c
  have hWd : DifferentiableAt ℝ W x := GenHarmonic.diffAt_of_contDiffOn hO hW (by simp) hx
  -- derivatives of the auxiliary fields
  have hWline : ∀ γ : Fin 4, HasDerivAt (fun s : ℝ => W (x + s • ev γ)) (pd W γ x) 0 :=
    fun γ => ActualJetBridge.hasDerivAt_line0 hWd γ
  have hev : ∀ γ : Fin 4, ∀ᶠ s in 𝓝 (0 : ℝ), x + s • ev γ ∈ O := by
    intro γ
    have hc : Continuous fun s : ℝ => x + s • (ev γ : ST 3) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have : O ∈ 𝓝 (x + (0 : ℝ) • (ev γ : ST 3)) := by rw [zero_smul, add_zero]; exact hO.mem_nhds hx
    exact hc.continuousAt.preimage_mem_nhds this
  have hdE : ∀ (γ : Fin 4) (c : Fin 3), (pd W γ x).2.2.1 c = dEg F (z.de x) (T x) dT γ c := by
    intro γ c
    have h1 : HasDerivAt (fun s : ℝ => (W (x + s • ev γ)).2.2.1 c) ((pd W γ x).2.2.1 c) 0 :=
      hasDerivAt_pi.1 (hasDerivAt_fst' (hasDerivAt_snd' (hasDerivAt_snd' (hWline γ)))) c
    have h2 := hasDerivAt_frT z hTd γ 0 c.succ
    refine h1.unique (h2.congr_of_eventuallyEq ?_)
    filter_upwards [hev γ] with s hs
    exact hEf _ hs c
  have hdB : ∀ (γ : Fin 4) (c : Fin 3), (pd W γ x).2.2.2.1 c = dBg F (z.de x) (T x) dT γ c := by
    intro γ c
    have h1 : HasDerivAt (fun s : ℝ => (W (x + s • ev γ)).2.2.2.1 c) ((pd W γ x).2.2.2.1 c) 0 :=
      hasDerivAt_pi.1 (hasDerivAt_fst' (hasDerivAt_snd' (hasDerivAt_snd' (hasDerivAt_snd'
        (hWline γ))))) c
    have h2 : HasDerivAt (fun s : ℝ => dualVec (fun b c : Fin 3 =>
        frT (frameU (z.gi (x + s • ev γ))) (T (x + s • ev γ)) b.succ c.succ) c)
        (dBg F (z.de x) (T x) dT γ c) 0 := by
      unfold dualVec dBg dualVec
      exact HasDerivAt.const_smul (-(1 / 2 : ℝ)) (HasDerivAt.fun_sum fun (b : Fin 3) _ =>
        HasDerivAt.fun_sum fun (c' : Fin 3) _ =>
          (hasDerivAt_frT z hTd γ b.succ c'.succ).const_smul (eps3 c b c'))
    refine h1.unique (h2.congr_of_eventuallyEq ?_)
    filter_upwards [hev γ] with s hs
    exact hBf _ hs c
  -- the `B`-row in frame form
  have hrowB := row_B SM hrow
  have hN := F.N_pos
  have hTx' : (recon SM (ofP (W x))).F = T x := rfl
  have hkey : ∀ a : Fin 3, ∑ b, ∑ c, eps3 a b c • bianC F (z.A x) (T x) dT b.succ c.succ = 0 := by
    intro a
    have h := hrowB a
    rw [hgW] at h
    simp only [hdE, hdB, hAF, hde, hrA, hTx'] at h
    have hid := frame_B_identity F (z.de x) (z.A x) (T x) dT hTx hdTa a
    have hN0 := ActualJetGauge.N_fD_zero F (fun γ => dBg F (z.de x) (T x) dT γ a)
    have hsucc : ∀ b c, fD F (fun γ => dEg F (z.de x) (T x) dT γ c) b.succ =
        ∑ j, F.E b j • dEg F (z.de x) (T x) dT j.succ c := fun b c =>
      ActualJetGauge.fD_succ F _ b
    have h2 : F.N • (fD F (fun γ => dBg F (z.de x) (T x) dT γ a) 0 +
        ∑ b, ∑ c, eps3 a b c • fD F (fun γ => dEg F (z.de x) (T x) dT γ c) b.succ) =
        F.N • LBf F (z.de x) (z.A x) (T x) a := by
      rw [← h, smul_add, hN0]
      simp only [hsucc]
      simp only [Fin.sum_univ_three]
      module
    rw [hid, smul_add] at h2
    have h3 : F.N • (-(1 / 2 : ℝ) • ∑ b, ∑ c, eps3 a b c • bianC F (z.A x) (T x) dT b.succ c.succ)
        = 0 := by
      have := congrArg (fun v => v - F.N • LBf F (z.de x) (z.A x) (T x) a) h2
      simpa using this
    rw [smul_smul] at h3
    exact (smul_eq_zero.1 h3).resolve_left (mul_ne_zero hN.ne' (by norm_num))
  -- all spatial contractions vanish
  have hanti : ∀ b c : Fin 3, bianC F (z.A x) (T x) dT c.succ b.succ =
      -bianC F (z.A x) (T x) dT b.succ c.succ := by
    intro b c
    rw [bianC_eq_frT, bianC_eq_frT]
    exact frT_anti F (fun μ ν => by
      unfold normS
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun γ _ => ?_
      rw [bianT_anti23 (z.A x) (T x) dT hTx hdTa, smul_neg]) b.succ c.succ
  have hsp : ∀ b c : Fin 3, bianC F (z.A x) (T x) dT b.succ c.succ = 0 := by
    intro b c
    have hd : dualVec (fun b c : Fin 3 => bianC F (z.A x) (T x) dT b.succ c.succ) = 0 := by
      funext a; unfold dualVec; rw [hkey a, smul_zero]; rfl
    rw [anti_eq_eps_dual (S := fun b c : Fin 3 => bianC F (z.A x) (T x) dT b.succ c.succ)
      (fun b c => hanti b c) b c, hd]
    simp
  -- all frame components of the normal contraction vanish, hence the contraction vanishes
  have hfr : ∀ B μ, (z.jet x).FJ.e B μ = F.fr B μ := fun B μ => GenConstraint.jet_e_eq z x B μ
  have hS0 : ∀ μ ν, normS F (z.A x) (T x) dT μ ν = 0 := by
    intro μ ν
    rw [inv_tensor (z.jet x).FJ (normS F (z.A x) (T x) dT) μ ν]
    refine Finset.sum_eq_zero fun A _ => Finset.sum_eq_zero fun B _ => ?_
    have h := frT_normS_zero F (z.A x) (T x) dT hTx hdTa hsp A B
    unfold frT at h
    simp only [hfr]
    rw [h, smul_zero]
  -- the normal Bianchi relation
  have hNB := ActualJetGauge.N_fD_zero F (fun γ => bianT (z.A x) (T x) dT γ i.succ j.succ)
  have hfD : fD F (fun γ => bianT (z.A x) (T x) dT γ i.succ j.succ) 0 = 0 := hS0 i.succ j.succ
  rw [hfD, smul_zero] at hNB
  have e : ∀ γ, GenGaugeDefect.bian z T x γ i.succ j.succ = bianT (z.A x) (T x) dT γ i.succ j.succ :=
    fun γ => by unfold GenGaugeDefect.bian bianT brT; rfl
  have hNB' : bianT (z.A x) (T x) dT 0 i.succ j.succ =
      ∑ k : Fin 3, F.β k • bianT (z.A x) (T x) dT k.succ i.succ j.succ := sub_eq_zero.1 hNB.symm
  simp only [e]
  exact hNB'

end RowToBianchi

/-! ### Propagation of the gauge auxiliary variables -/

section GaugeSector

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable {SM : SMData (MatLie m) V S S'}

/-- The reconstructed field strength depends only on the metric and on `(E, B)`. -/
theorem recon_F_congr {v w : StateP m V S S'} (hg : v.1.1 = w.1.1) (hE : v.2.2.1 = w.2.2.1)
    (hB : v.2.2.2.1 = w.2.2.2.1) : (recon SM (ofP v)).F = (recon SM (ofP w)).F := by
  unfold recon
  dsimp only
  have e1 : (ofP v).g = (ofP w).g := hg
  have e2 : (ofP v).E = (ofP w).E := hE
  have e3 : (ofP v).B = (ofP w).B := hB
  rw [e1, e2, e3]

/-- The shift of a smooth tuple is smooth and periodic. -/
theorem contDiff_shift (z : Tuple m V S S') (k : Fin 3) :
    ContDiff ℝ ∞ (fun y => (frameU (z.gi y)).β k) := by
  have e : (fun y => (frameU (z.gi y)).β k) = fun y => -(z.e y 0 k.succ / z.e y 0 0) :=
    funext fun y => GenDefJet.frameU_beta z y k
  rw [e]
  exact ((z.contDiff_e 0 k.succ).div (z.contDiff_e 0 0) fun y => (GenDefJet.e00_pos z y).ne').neg

theorem isSPeriodic_shift (z : Tuple m V S S') (k : Fin 3) :
    IsSPeriodic (fun y => (frameU (z.gi y)).β k) := fun q y => by
  simp only [ActualJetState.gi_per z q y]

/-- The head row `∂_tA_i = T_{0i}` of a solution of the modified system whose head potential is
that of the tuple. -/
theorem head_row_A (z : Tuple m V S S') {W : ST 3 → StateP m V S S'} {O : Set (ST 3)}
    (hO : IsOpen O) (hW : ContDiffOn ℝ ∞ W O)
    (hA : ∀ y ∈ O, ∀ i : Fin 3, (W y).2.1 i = z.A y i.succ) {x : ST 3} (hx : x ∈ O)
    (hrow : pd W 0 x + ∑ j : Fin 3, AJKatoMod.princPM SM (W x) j (pd W j.succ x) =
      toP (AJKatoMod.FsysM SM (ofP (W x)))) (i : Fin 3) :
    Trec SM W x 0 i.succ = pd z.A 0 x i.succ := by
  have h := congrArg (fun v : StateP m V S S' => v.2.1 i) hrow
  simp only [Prod.snd_add, Prod.fst_add, Prod.snd_sum, Prod.fst_sum, Finset.sum_apply,
    Pi.add_apply] at h
  have e1 : ∀ j : Fin 3, (AJKatoMod.princPM SM (W x) j (pd W j.succ x)).2.1 i = 0 := fun j => rfl
  have e2 : (toP (AJKatoMod.FsysM SM (ofP (W x)))).2.1 i = Trec SM W x 0 i.succ := rfl
  simp only [e1, Finset.sum_const_zero, add_zero, e2] at h
  rw [← h]
  have hWd : DifferentiableAt ℝ W x := GenHarmonic.diffAt_of_contDiffOn hO hW (by simp) hx
  have h1 : HasDerivAt (fun s : ℝ => (W (x + s • ev 0)).2.1 i) ((pd W 0 x).2.1 i) 0 :=
    hasDerivAt_pi.1 (hasDerivAt_fst' (hasDerivAt_snd' (ActualJetBridge.hasDerivAt_line0 hWd 0))) i
  have h2 : HasDerivAt (fun s : ℝ => z.A (x + s • ev 0) i.succ) (pd z.A 0 x i.succ) 0 :=
    hasDerivAt_pi.1 (ActualJetBridge.hasDerivAt_line0
      (z.A_smooth.differentiable (by simp) x) 0) i.succ
  refine h1.unique (h2.congr_of_eventuallyEq ?_)
  have hc : Continuous fun s : ℝ => x + s • (ev (0 : Fin 4) : ST 3) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hmem : O ∈ 𝓝 (x + (0 : ℝ) • (ev (0 : Fin 4) : ST 3)) := by
    rw [zero_smul, add_zero]; exact hO.mem_nhds hx
  filter_upwards [hc.continuousAt.preimage_mem_nhds hmem] with s hs
  exact hA _ hs i

/-- The state auxiliary variables `(E, B)` agree with the actual ones where the reconstructed
field strength is the actual one. -/
theorem EB_of_T_eq (z : Tuple m V S S') {v : StateP m V S S'} {x : ST 3}
    (hmet : v.1 = (stateF SM z x).1)
    (hT : ∀ μ ν, (recon SM (ofP v)).F μ ν = GenNoether.Fld z x μ ν) :
    v.2.2.1 = (stateF SM z x).2.2.1 ∧ v.2.2.2.1 = (stateF SM z x).2.2.2.1 := by
  have hF : (recon SM (ofP v)).F = fun μ ν => GenNoether.Fld z x μ ν :=
    funext fun μ => funext fun ν => hT μ ν
  have hAF : (z.jet x).AF = frameU (z.gi x) := (ActualJet.frameU_eq' (z.jet x)).symm
  constructor
  · funext a
    rw [E_eq_frT hmet a, hF]
    show _ = elec (z.jet x).AF (z.jet x).A (z.jet x).dA a
    rw [hAF]; rfl
  · funext a
    rw [B_eq_frT hmet a, hF]
    show _ = magn (z.jet x).AF (z.jet x).A (z.jet x).dA a
    rw [hAF]; rfl

/-- **Propagation of the gauge defining-jet identities for a solution of the modified system**
(forward).  Let `W` be a smooth periodic state field on `(a, b) × 𝕋³` in the chart whose metric
block is the actual metric block of a smooth tuple `z` and whose head potential is the potential
of `z`, solving the shift-transported system.  If its electric and magnetic variables are the
actual ones on the slice `t₀`, they are the actual ones on `[t₀, t₁] × 𝕋³`. -/
theorem gauge_sector_forward (z : Tuple m V S S') {W : ST 3 → StateP m V S S'}
    {a t₀ t₁ b : ℝ} (ha : a < t₀) (h01 : t₀ < t₁) (hb : t₁ < b)
    (hW : ContDiffOn ℝ ∞ W (openSlab a b)) (hWp : IsSPeriodic W)
    (hc : ∀ y ∈ openSlab a b, MetChart (W y).1)
    (hmet : ∀ y ∈ openSlab a b, (W y).1 = (stateF SM z y).1)
    (hA : ∀ y ∈ openSlab a b, ∀ i : Fin 3, (W y).2.1 i = z.A y i.succ)
    (hrow : ∀ y ∈ openSlab a b, pd W 0 y + ∑ j : Fin 3, AJKatoMod.princPM SM (W y) j
      (pd W j.succ y) = toP (AJKatoMod.FsysM SM (ofP (W y))))
    (hinit : ∀ y : Fin 3 → ℝ, (W (Fin.cons t₀ y)).2.2.1 = (stateF SM z (Fin.cons t₀ y)).2.2.1 ∧
      (W (Fin.cons t₀ y)).2.2.2.1 = (stateF SM z (Fin.cons t₀ y)).2.2.2.1) :
    ∀ x ∈ slab t₀ t₁, (W x).2.2.1 = (stateF SM z x).2.2.1 ∧
      (W x).2.2.2.1 = (stateF SM z x).2.2.2.1 := by
  have hO := isOpen_openSlab (d := 3) a b
  have hTp : IsSPeriodic (Trec SM W) := fun q y => by simp only [Trec, hWp q y]
  have hv := GenGaugeDefect.gauge_defect_vanish (z := z) (T := Trec SM W)
    (β := fun y k => (frameU (z.gi y)).β k) ha h01 hb (contDiffOn_Trec hO hW hc) hTp
    (fun y μ ν => recon_F_anti (W y) μ ν) (fun k => contDiff_shift z k)
    (fun k => isSPeriodic_shift z k)
    (fun y hy i => head_row_A z hO hW hA hy (hrow y hy) i)
    (fun y hy i j => normal_bianchi_at z hO hW hc hmet hA hy (hrow y hy) i j)
    (fun y i j => by
      have hy : (Fin.cons t₀ y : ST 3) ∈ openSlab a b := ⟨by show a < t₀; linarith,
        by show t₀ < b; linarith⟩
      have hm := hmet _ hy
      obtain ⟨hE, hB⟩ := hinit y
      have hc' := recon_F_congr (SM := SM) (congrArg Prod.fst hm) hE hB
      show (recon SM (ofP (W (Fin.cons t₀ y)))).F i.succ j.succ = _
      rw [hc', recon_F_actual])
  intro x hx
  exact EB_of_T_eq z (hmet x (slab_subset_openSlab ha hb hx)) (hv x hx)

/-- **Propagation of the gauge defining-jet identities** (backward). -/
theorem gauge_sector_backward (z : Tuple m V S S') {W : ST 3 → StateP m V S S'}
    {a t₁ t₀ b : ℝ} (ha : a < t₁) (h10 : t₁ < t₀) (hb : t₀ < b)
    (hW : ContDiffOn ℝ ∞ W (openSlab a b)) (hWp : IsSPeriodic W)
    (hc : ∀ y ∈ openSlab a b, MetChart (W y).1)
    (hmet : ∀ y ∈ openSlab a b, (W y).1 = (stateF SM z y).1)
    (hA : ∀ y ∈ openSlab a b, ∀ i : Fin 3, (W y).2.1 i = z.A y i.succ)
    (hrow : ∀ y ∈ openSlab a b, pd W 0 y + ∑ j : Fin 3, AJKatoMod.princPM SM (W y) j
      (pd W j.succ y) = toP (AJKatoMod.FsysM SM (ofP (W y))))
    (hinit : ∀ y : Fin 3 → ℝ, (W (Fin.cons t₀ y)).2.2.1 = (stateF SM z (Fin.cons t₀ y)).2.2.1 ∧
      (W (Fin.cons t₀ y)).2.2.2.1 = (stateF SM z (Fin.cons t₀ y)).2.2.2.1) :
    ∀ x ∈ slab t₁ t₀, (W x).2.2.1 = (stateF SM z x).2.2.1 ∧
      (W x).2.2.2.1 = (stateF SM z x).2.2.2.1 := by
  have hO := isOpen_openSlab (d := 3) a b
  have hTp : IsSPeriodic (Trec SM W) := fun q y => by simp only [Trec, hWp q y]
  have hv := GenGaugeDefect.gauge_defect_vanish_backward (z := z) (T := Trec SM W)
    (β := fun y k => (frameU (z.gi y)).β k) ha h10 hb (contDiffOn_Trec hO hW hc) hTp
    (fun y μ ν => recon_F_anti (W y) μ ν) (fun k => contDiff_shift z k)
    (fun k => isSPeriodic_shift z k)
    (fun y hy i => head_row_A z hO hW hA hy (hrow y hy) i)
    (fun y hy i j => normal_bianchi_at z hO hW hc hmet hA hy (hrow y hy) i j)
    (fun y i j => by
      have hy : (Fin.cons t₀ y : ST 3) ∈ openSlab a b := ⟨by show a < t₀; linarith,
        by show t₀ < b; linarith⟩
      have hm := hmet _ hy
      obtain ⟨hE, hB⟩ := hinit y
      have hc' := recon_F_congr (SM := SM) (congrArg Prod.fst hm) hE hB
      show (recon SM (ofP (W (Fin.cons t₀ y)))).F i.succ j.succ = _
      rw [hc', recon_F_actual])
  intro x hx
  exact EB_of_T_eq z (hmet x (slab_subset_openSlab ha hb hx)) (hv x hx)

end GaugeSector

end RenewalGeometry.GenGaugeRows
