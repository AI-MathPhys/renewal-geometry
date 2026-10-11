/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.ActualJetSliceCompletion

/-!
# Completion of constrained Cauchy slice data to slice-constrained field tuples

Einstein–Standard-Model action-closure manuscript, `prop:generated-initial` and the constrained
class of `lem:generated-physical-identification`.

**`SliceCauchy.exists_sliceConstrained`**: for theory data whose bosonic residual fields of
smooth tuples are smooth (`SMSmooth` or the chart-local `GenChL.SMSmoothL`) and whose stress is
symmetric (`StressSymm`, e.g. `GenDStress.CoupledDirac`), every smooth periodic slice datum `D`
satisfying the Hamiltonian, momentum and Gauss rows (`Constrained`) is the Cauchy datum of a
smooth field tuple `z` which is **slice-constrained** (`GenPhysIdClosed.SliceConstrained`: the
complete Einstein, Yang–Mills, Higgs, Dirac residuals, the harmonic defect `C` and `∂_tC` vanish
on `t = 0`), with `z = (diag(-1, γ), A, H, Ψ, Ψ̄)` and `(∂_tγ, ∂_tA, ∂_tH) = (-2K, Ȧ, Ḣ)` on the
slice and the harmonic-gauge lapse/shift time derivatives.

Construction (three stages on the slice, all second-order data smooth and periodic):
1. the normal spinor derivatives `∂_tΨ = c₀ r_D[0]` solve the Dirac rows (`c₀² = 1`);
2. `∂_t²Aᵢ = r^A_i[·]`, `∂_t²H = r_H[·]` solve the spatial Yang–Mills and the Higgs rows
   (principal coefficient `g^{00} = -1`), and `∂_t²g = -2(𝓔^{tr} - ∇_{(μ}C_{ν)})[·]` solves the
   reduced Einstein rows (principal coefficient `-½g^{00}`);
3. the Gauss row is the normal Yang–Mills row; the Einstein normal rows (Hamiltonian and
   momentum) force `∂_tC = 0` and hence the full Einstein equations (`slice_close`).

`constrainedData_of_constrained`: the actual-jet state of the completion is a
`GenPhysIdClosed.ConstrainedData` datum.
-/

open Finset
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenSlice

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetBridge ActualJetState ActualJetGauge
  ActualJetSpinor SpinorProlongation SliceExt GenHarmonic GenStress GenConstraint GenPhysIdClosed
  ActualJetRecon

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

/-! ### Smoothness and symmetry of jet fields -/

theorem contDiff_symDefect (z : Tuple m V S S') (a b : Fin 4) :
    ContDiff ℝ ∞ (fun y => symDefect (z.g y) (z.gi y) (z.dg y) (z.ddg y) a b) := by
  have h1 := z.contDiff_gc
  have h2 := z.contDiff_gi
  have h3 := z.contDiff_dg
  have h4 := z.contDiff_ddg
  simp only [symDefect, nablaDefect, nablaC, cUp, dcUp, cDown, chr, dginv, dchr, dchr1, dchr2]
  fun_prop

theorem symDefect_per (z : Tuple m V S S') (k : Fin 3 → ℤ) (x : ST 3) :
    (fun a b => symDefect (z.g (x + sshift k)) (z.gi (x + sshift k)) (z.dg (x + sshift k))
      (z.ddg (x + sshift k)) a b) = fun a b => symDefect (z.g x) (z.gi x) (z.dg x) (z.ddg x) a b := by
  rw [z.g_per k x, gi_per z k x, dg_per z k x, ddg_per z k x]

theorem symDefect_symm (g gi : Met) (dg : Fin 4 → Met) (ddg : Fin 4 → Fin 4 → Met) (a b : Fin 4) :
    symDefect g gi dg ddg a b = symDefect g gi dg ddg b a := by
  unfold symDefect; ring

theorem c0_mul_c0 {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀] (D : DiracData (MatLie m) V S₀) :
    D.Fr.c 0 * D.Fr.c 0 = 1 := by
  have h := D.Fr.anticomm 0 0
  rw [if_pos rfl, D.lorentz.1] at h
  have h2 : (2 : ℝ) • (D.Fr.c 0 * D.Fr.c 0) = (2 : ℝ) • (1 : Module.End ℝ S₀) := by
    rw [two_smul, h]; norm_num
  exact smul_right_injective _ (two_ne_zero) h2

variable (SM : SMData (MatLie m) V S S')

namespace SliceCauchy

variable (D : SliceCauchy m V S S')

/-! ### Completions with chosen time scales -/

theorem exists_epsP (P : Params m V S S') : ∃ ε, 0 < ε ∧ ∀ x, GChart (D.gF P ε x) := by
  obtain ⟨ε₀, h0, h⟩ := D.exists_chart_eps P
  exact ⟨ε₀, h0, h ε₀ h0 le_rfl⟩

/-- The completion with completion data `P` (a chosen admissible time scale). -/
abbrev tup (P : Params m V S S') : Tuple m V S S' :=
  D.mkTuple P (D.exists_epsP P).choose (D.exists_epsP P).choose_spec.2

theorem tup_ne (P : Params m V S S') : (D.exists_epsP P).choose ≠ 0 :=
  (D.exists_epsP P).choose_spec.1.ne'

/-! ### Stage 1: the normal spinor derivatives -/

/-- `∂_tΨ = c₀ r_D[base]` on the slice. -/
def ψd1 (y : Fin 3 → ℝ) : S := SM.D.Fr.c 0 ((dirF SM D.base (Fin.cons 0 y)).1)

/-- `∂_tΨ̄ = c̄₀ r̄_D[base]` on the slice. -/
def ψbd1 (y : Fin 3 → ℝ) : S' := SM.Db.Fr.c 0 ((dirF SM D.base (Fin.cons 0 y)).2)

theorem contDiff_ψd1 : ContDiff ℝ ∞ (D.ψd1 SM) :=
  (LinearMap.toContinuousLinearMap (SM.D.Fr.c 0)).contDiff.comp
    (contDiff_fst.comp (contDiff_slice (contDiff_dirF SM D.base)))

theorem contDiff_ψbd1 : ContDiff ℝ ∞ (D.ψbd1 SM) :=
  (LinearMap.toContinuousLinearMap (SM.Db.Fr.c 0)).contDiff.comp
    (contDiff_snd.comp (contDiff_slice (contDiff_dirF SM D.base)))

theorem ψd1_per : IsZPeriodic (D.ψd1 SM) := fun k y => by
  have := per_slice (isSPeriodic_dirF SM D.base) k y
  try simp only at this
  simp only [ψd1, this]

theorem ψbd1_per : IsZPeriodic (D.ψbd1 SM) := fun k y => by
  have := per_slice (isSPeriodic_dirF SM D.base) k y
  try simp only at this
  simp only [ψbd1, this]

/-- The stage-1 completion data. -/
def P1 : Params m V S S' :=
  { (Params.zero (m := m) (V := V) (S := S) (S' := S')) with
    ψd := D.ψd1 SM
    ψbd := D.ψbd1 SM
    ψd_smooth := D.contDiff_ψd1 SM
    ψbd_smooth := D.contDiff_ψbd1 SM
    ψd_per := D.ψd1_per SM
    ψbd_per := D.ψbd1_per SM }

/-- The stage-1 completion. -/
abbrev z1 : Tuple m V S S' := D.tup (D.P1 SM)

theorem agree0 (P : Params m V S S') (y : Fin 3 → ℝ) :
    Agree ((D.base).jet (Fin.cons 0 y)) ((D.tup P).jet (Fin.cons 0 y)) :=
  D.agree_mk D.ε0_ne (D.tup_ne P) y

/-- **The stage-1 completion solves the Dirac rows on the slice.** -/
theorem z1_rD (y : Fin 3 → ℝ) : (((D.z1 SM).jet (Fin.cons 0 y)).res SM).rD = 0 := by
  set J0 := (D.base).jet (Fin.cons 0 y)
  set J1 := (D.z1 SM).jet (Fin.cons 0 y)
  have hA : Agree J0 J1 := D.agree0 (D.P1 SM) y
  have hc : J1.cψ = fun γ => J0.cψ γ + (if γ = 0 then D.ψd1 SM y - 0 else 0) :=
    D.cψ_mk (P := Params.zero) (P' := D.P1 SM) (hch := D.exists_eps0.choose_spec.2)
      (hch' := (D.exists_epsP (D.P1 SM)).choose_spec.2) D.ε0_ne (D.tup_ne _) y
  have he : ∀ b, J1.FJ.e b 0 = if b = 0 then 1 else 0 := by
    intro b
    refine Fin.cases ?_ (fun a => ?_) b
    · exact D.e_mk (hch := (D.exists_epsP (D.P1 SM)).choose_spec.2) y 0
    · simp only [Fin.succ_ne_zero, ite_false]
      rw [J1.frame]; rfl
  show J1.rD SM.D J1.ψ J1.cψ = 0
  rw [hc, ← hA.ψ, rD_shift_jet, ← hA.rDf]
  have hsum : ∀ b, ∑ γ, J1.FJ.e b γ • (if γ = 0 then D.ψd1 SM y - 0 else 0) =
      J1.FJ.e b 0 • D.ψd1 SM y := by
    intro b
    rw [Finset.sum_eq_single 0 (fun c _ hc => by simp [hc]) (by simp)]
    simp
  simp only [hsum, he]
  rw [Fin.sum_univ_succ]
  simp only [ite_true, one_smul, Fin.succ_ne_zero, ite_false, zero_smul, smul_zero,
    Finset.sum_const_zero, add_zero, SM.D.lorentz.1]
  show (dirF SM D.base (Fin.cons 0 y)).1 + (-1 : ℝ) • (SM.D.Fr.c 0) (D.ψd1 SM y) = 0
  simp only [ψd1, ← Module.End.mul_apply, c0_mul_c0, Module.End.one_apply]
  simp

theorem z1_rDb (y : Fin 3 → ℝ) : (((D.z1 SM).jet (Fin.cons 0 y)).res SM).rDb = 0 := by
  set J0 := (D.base).jet (Fin.cons 0 y)
  set J1 := (D.z1 SM).jet (Fin.cons 0 y)
  have hA : Agree J0 J1 := D.agree0 (D.P1 SM) y
  have hc : J1.cψb = fun γ => J0.cψb γ + (if γ = 0 then D.ψbd1 SM y - 0 else 0) :=
    D.cψb_mk (P := Params.zero) (P' := D.P1 SM) (hch := D.exists_eps0.choose_spec.2)
      (hch' := (D.exists_epsP (D.P1 SM)).choose_spec.2) D.ε0_ne (D.tup_ne _) y
  have he : ∀ b, J1.FJ.e b 0 = if b = 0 then 1 else 0 := by
    intro b
    refine Fin.cases ?_ (fun a => ?_) b
    · exact D.e_mk (hch := (D.exists_epsP (D.P1 SM)).choose_spec.2) y 0
    · simp only [Fin.succ_ne_zero, ite_false]
      rw [J1.frame]; rfl
  show J1.rD SM.Db J1.ψb J1.cψb = 0
  rw [hc, ← hA.ψb, rD_shift_jet, ← hA.rDf]
  have hsum : ∀ b, ∑ γ, J1.FJ.e b γ • (if γ = 0 then D.ψbd1 SM y - 0 else 0) =
      J1.FJ.e b 0 • D.ψbd1 SM y := by
    intro b
    rw [Finset.sum_eq_single 0 (fun c _ hc => by simp [hc]) (by simp)]
    simp
  simp only [hsum, he]
  rw [Fin.sum_univ_succ]
  simp only [ite_true, one_smul, Fin.succ_ne_zero, ite_false, zero_smul, smul_zero,
    Finset.sum_const_zero, add_zero, SM.Db.lorentz.1]
  show (dirF SM D.base (Fin.cons 0 y)).2 + (-1 : ℝ) • (SM.Db.Fr.c 0) (D.ψbd1 SM y) = 0
  simp only [ψbd1, ← Module.End.mul_apply, c0_mul_c0, Module.End.one_apply]
  simp


/-! ### Stage 2: the second time derivatives of the bosonic fields -/

/-- `∂_t²Aᵢ` solving the spatial Yang–Mills rows. -/
def Aa2 (y : Fin 3 → ℝ) : Fin 3 → MatLie m :=
  fun j => (bosF SM (D.z1 SM) (Fin.cons 0 y)).2.1 j.succ

/-- `∂_t²H` solving the Higgs row. -/
def Ha2 (y : Fin 3 → ℝ) : V := (bosF SM (D.z1 SM) (Fin.cons 0 y)).2.2

/-- `∂_t²g` solving the reduced Einstein rows. -/
def W2 (y : Fin 3 → ℝ) : Met := fun μ ν =>
  -2 * ((bosF SM (D.z1 SM) (Fin.cons 0 y)).1 μ ν -
    symDefect ((D.z1 SM).g (Fin.cons 0 y)) ((D.z1 SM).gi (Fin.cons 0 y))
      ((D.z1 SM).dg (Fin.cons 0 y)) ((D.z1 SM).ddg (Fin.cons 0 y)) μ ν)

variable {SM}

theorem contDiff_Aa2 (hB : ∀ z : Tuple m V S S', ContDiff ℝ ∞ (bosF SM z)) :
    ContDiff ℝ ∞ (D.Aa2 SM) := by
  have h := contDiff_slice (hB (D.z1 SM))
  refine contDiff_pi.2 fun j => ?_
  exact (contDiff_apply ℝ (MatLie m) j.succ).comp (contDiff_fst.comp (contDiff_snd.comp h))

theorem contDiff_Ha2 (hB : ∀ z : Tuple m V S S', ContDiff ℝ ∞ (bosF SM z)) :
    ContDiff ℝ ∞ (D.Ha2 SM) :=
  contDiff_snd.comp (contDiff_snd.comp (contDiff_slice (hB (D.z1 SM))))

theorem contDiff_W2 (hB : ∀ z : Tuple m V S S', ContDiff ℝ ∞ (bosF SM z)) :
    ContDiff ℝ ∞ (D.W2 SM) := by
  have h := contDiff_slice (hB (D.z1 SM))
  refine contDiff_pi.2 fun μ => contDiff_pi.2 fun ν => ?_
  have h1 : ContDiff ℝ ∞ (fun y : Fin 3 → ℝ => (bosF SM (D.z1 SM) (Fin.cons 0 y)).1 μ ν) :=
    (contDiff_apply ℝ ℝ ν).comp ((contDiff_apply ℝ (Fin 4 → ℝ) μ).comp (contDiff_fst.comp h))
  have h2 := contDiff_slice (contDiff_symDefect (D.z1 SM) μ ν)
  exact contDiff_const.mul (h1.sub h2)

theorem Aa2_per : IsZPeriodic (D.Aa2 SM) := fun k y => by
  have := per_slice (isSPeriodic_bosF SM (D.z1 SM)) k y
  funext j
  change (bosF SM (D.z1 SM) (Fin.cons 0 (y + zvec k))).2.1 j.succ =
    (bosF SM (D.z1 SM) (Fin.cons 0 y)).2.1 j.succ
  rw [show bosF SM (D.z1 SM) (Fin.cons 0 (y + zvec k)) = bosF SM (D.z1 SM) (Fin.cons 0 y)
    from this]

theorem Ha2_per : IsZPeriodic (D.Ha2 SM) := fun k y => by
  have := per_slice (isSPeriodic_bosF SM (D.z1 SM)) k y
  change (bosF SM (D.z1 SM) (Fin.cons 0 (y + zvec k))).2.2 = (bosF SM (D.z1 SM) (Fin.cons 0 y)).2.2
  rw [show bosF SM (D.z1 SM) (Fin.cons 0 (y + zvec k)) = bosF SM (D.z1 SM) (Fin.cons 0 y)
    from this]

theorem W2_per : IsZPeriodic (D.W2 SM) := fun k y => by
  have h1 : bosF SM (D.z1 SM) (Fin.cons 0 (y + zvec k)) = bosF SM (D.z1 SM) (Fin.cons 0 y) :=
    per_slice (isSPeriodic_bosF SM (D.z1 SM)) k y
  have h2 := symDefect_per (D.z1 SM) k (Fin.cons 0 y)
  rw [← cons0_add_zvec] at h2
  funext μ ν
  change -2 * ((bosF SM (D.z1 SM) (Fin.cons 0 (y + zvec k))).1 μ ν - _) =
    -2 * ((bosF SM (D.z1 SM) (Fin.cons 0 y)).1 μ ν - _)
  rw [h1, congrFun (congrFun h2 μ) ν]

/-- The stage-1 Einstein residual is symmetric on the slice (symmetric stress). -/
theorem z1_Etr_symm (hT : StressSymm SM) (y : Fin 3 → ℝ) (μ ν : Fin 4) :
    (bosF SM (D.z1 SM) (Fin.cons 0 y)).1 μ ν = (bosF SM (D.z1 SM) (Fin.cons 0 y)).1 ν μ := by
  set z := D.z1 SM
  set x : ST 3 := Fin.cons 0 y
  have hg := z.g_symm x
  have hTs : ∀ a b, (z.jet x).Tact SM a b = (z.jet x).Tact SM b a := by
    intro a b
    rw [Tact_eq_stressF SM _ (D.z1_rD SM y) (D.z1_rDb SM y),
      Tact_eq_stressF SM _ (D.z1_rD SM y) (D.z1_rDb SM y)]
    exact hT _ (z.g_symm x) (z.gi_symm x) a b
  have hE : ∀ a b, einstein (z.g x) (z.gi x) (z.dg x) (z.ddg x) a b + SM.Λ * z.g x a b -
      SM.κ * (z.jet x).Tact SM a b = einstein (z.g x) (z.gi x) (z.dg x) (z.ddg x) b a +
      SM.Λ * z.g x b a - SM.κ * (z.jet x).Tact SM b a := by
    intro a b
    rw [RecordTuple.einstein_symm hg (z.gi_symm x) (z.dg_symm x) (z.ddg_symm1 x) (z.ddg_symm2 x),
      hg a b, hTs a b]
  exact AJKatoMod.traceRev_symm hg hE μ ν

theorem W2_symm (hT : StressSymm SM) (y : Fin 3 → ℝ) (μ ν : Fin 4) :
    D.W2 SM y μ ν = D.W2 SM y ν μ := by
  simp only [W2, D.z1_Etr_symm hT y μ ν, symDefect_symm _ _ _ _ μ ν]

/-- The stage-2 completion data. -/
def P2 (hB : ∀ z : Tuple m V S S', ContDiff ℝ ∞ (bosF SM z)) (hT : StressSymm SM) :
    Params m V S S' where
  W := D.W2 SM
  Aa := D.Aa2 SM
  Ha := D.Ha2 SM
  ψd := D.ψd1 SM
  ψbd := D.ψbd1 SM
  W_smooth := D.contDiff_W2 hB
  Aa_smooth := D.contDiff_Aa2 hB
  Ha_smooth := D.contDiff_Ha2 hB
  ψd_smooth := D.contDiff_ψd1 SM
  ψbd_smooth := D.contDiff_ψbd1 SM
  W_per := D.W2_per
  Aa_per := D.Aa2_per
  Ha_per := D.Ha2_per
  ψd_per := D.ψd1_per SM
  ψbd_per := D.ψbd1_per SM
  W_symm := D.W2_symm hT


/-- **The completed tuple** (stage-2 completion data). -/
abbrev z2 (hB : ∀ z : Tuple m V S S', ContDiff ℝ ∞ (bosF SM z)) (hT : StressSymm SM) :
    Tuple m V S S' := D.tup (D.P2 hB hT)

section Final

variable (hB : ∀ z : Tuple m V S S', ContDiff ℝ ∞ (bosF SM z)) (hT : StressSymm SM)

theorem agree12 (y : Fin 3 → ℝ) :
    Agree ((D.z1 SM).jet (Fin.cons 0 y)) ((D.z2 hB hT).jet (Fin.cons 0 y)) :=
  D.agree_mk (hch := (D.exists_epsP (D.P1 SM)).choose_spec.2)
    (hch' := (D.exists_epsP (D.P2 hB hT)).choose_spec.2) (D.tup_ne _) (D.tup_ne _) y

theorem z2_cψ (y : Fin 3 → ℝ) :
    ((D.z2 hB hT).jet (Fin.cons 0 y)).cψ = ((D.z1 SM).jet (Fin.cons 0 y)).cψ := by
  rw [D.cψ_mk (P := D.P1 SM) (P' := D.P2 hB hT)
    (hch := (D.exists_epsP (D.P1 SM)).choose_spec.2)
    (hch' := (D.exists_epsP (D.P2 hB hT)).choose_spec.2) (D.tup_ne _) (D.tup_ne _) y]
  have h0 : (D.P2 hB hT).ψd y - (D.P1 SM).ψd y = 0 := by
    show D.ψd1 SM y - D.ψd1 SM y = 0; exact sub_self _
  funext γ
  simp only [h0, ite_self, add_zero]

theorem z2_cψb (y : Fin 3 → ℝ) :
    ((D.z2 hB hT).jet (Fin.cons 0 y)).cψb = ((D.z1 SM).jet (Fin.cons 0 y)).cψb := by
  rw [D.cψb_mk (P := D.P1 SM) (P' := D.P2 hB hT)
    (hch := (D.exists_epsP (D.P1 SM)).choose_spec.2)
    (hch' := (D.exists_epsP (D.P2 hB hT)).choose_spec.2) (D.tup_ne _) (D.tup_ne _) y]
  have h0 : (D.P2 hB hT).ψbd y - (D.P1 SM).ψbd y = 0 := by
    show D.ψbd1 SM y - D.ψbd1 SM y = 0; exact sub_self _
  funext γ
  simp only [h0, ite_self, add_zero]

theorem z2_rD (y : Fin 3 → ℝ) : (((D.z2 hB hT).jet (Fin.cons 0 y)).res SM).rD = 0 := by
  rw [← (D.agree12 hB hT y).rD_eq (by rw [D.z2_cψ]) SM]
  exact D.z1_rD SM y

theorem z2_rDb (y : Fin 3 → ℝ) : (((D.z2 hB hT).jet (Fin.cons 0 y)).res SM).rDb = 0 := by
  rw [← (D.agree12 hB hT y).rDb_eq (by rw [D.z2_cψb]) SM]
  exact D.z1_rDb SM y

omit hB hT in
theorem sum_shift_A (C : Fin 3 → Fin 3 → ℝ) (a : Fin 3 → MatLie m) (ν : Fin 4) :
    ∑ μ, ∑ ρ, met4 (-1) 0 C μ ρ • ((if ρ = 0 ∧ μ = 0 then padL a ν else 0) -
      (if ρ = 0 ∧ ν = 0 then padL a μ else 0)) = -(padL a ν) := by
  refine Fin.cases ?_ (fun j => ?_) ν
  · simp [Fin.sum_univ_succ]
  · simp [Fin.sum_univ_succ, Fin.succ_ne_zero]

omit hB hT in
theorem sum_shift_H (C : Fin 3 → Fin 3 → ℝ) (h : V) :
    ∑ μ, ∑ ρ, met4 (-1) 0 C μ ρ • (if ρ = 0 ∧ μ = 0 then h else 0) = -h := by
  simp [Fin.sum_univ_succ]

omit hB hT in
theorem sum_shift_g (C : Fin 3 → Fin 3 → ℝ) (W : Met) (μ ν : Fin 4) :
    ∑ α, ∑ β, met4 (-1) 0 C α β * (if α = 0 ∧ β = 0 then W μ ν else 0) = -W μ ν := by
  simp [Fin.sum_univ_succ]

omit hB hT in
theorem z1_ddA_eq (y : Fin 3 → ℝ) :
    ((D.z1 SM).jet (Fin.cons 0 y)).ddA = ((D.base).jet (Fin.cons 0 y)).ddA := by
  rw [D.ddA_mk (P := Params.zero) (P' := D.P1 SM) (hch := D.exists_eps0.choose_spec.2)
    (hch' := (D.exists_epsP (D.P1 SM)).choose_spec.2) D.ε0_ne (D.tup_ne _) y]
  have h0 : (D.P1 SM).Aa y - (Params.zero (m := m) (V := V) (S := S) (S' := S')).Aa y = 0 := by
    show (0 : Fin 3 → MatLie m) - 0 = 0; exact sub_self _
  funext a b c
  simp only [h0, map_zero, Pi.zero_apply, ite_self, add_zero]

/-- **The completed tuple solves the Yang–Mills rows on the slice** (spatial rows by the choice
of `∂_t²A`, the normal row by the Gauss constraint). -/
theorem z2_rA (hc : D.Constrained SM) (y : Fin 3 → ℝ) (ν : Fin 4) :
    (((D.z2 hB hT).jet (Fin.cons 0 y)).res SM).rA ν = 0 := by
  have hdd := D.ddA_mk (P := D.P1 SM) (P' := D.P2 hB hT)
    (hch := (D.exists_epsP (D.P1 SM)).choose_spec.2)
    (hch' := (D.exists_epsP (D.P2 hB hT)).choose_spec.2) (D.tup_ne _) (D.tup_ne _) y
  rw [(D.agree12 hB hT y).rA_shift _ hdd SM ν]
  have hgi : ((D.z1 SM).jet (Fin.cons 0 y)).FJ.gi = met4 (-1) 0 (D.γi y) :=
    D.mk_gi (hch := (D.exists_epsP (D.P1 SM)).choose_spec.2) y
  rw [hgi, sum_shift_A]
  refine Fin.cases ?_ (fun j => ?_) ν
  · rw [padL_zero, neg_zero, add_zero,
      ← (D.agree0 (D.P1 SM) y).rA_eq (D.z1_ddA_eq y).symm SM]
    exact (hc y).2.2
  · rw [padL_succ]
    simp only [P2, P1, Params.zero, sub_zero, Aa2]
    show (((D.z1 SM).jet (Fin.cons 0 y)).res SM).rA j.succ +
      -((((D.z1 SM).jet (Fin.cons 0 y)).res SM).rA j.succ) = 0
    rw [add_neg_cancel]

/-- **The completed tuple solves the Higgs row on the slice.** -/
theorem z2_rH (y : Fin 3 → ℝ) : (((D.z2 hB hT).jet (Fin.cons 0 y)).res SM).rH = 0 := by
  have hdd := D.ddH_mk (P := D.P1 SM) (P' := D.P2 hB hT)
    (hch := (D.exists_epsP (D.P1 SM)).choose_spec.2)
    (hch' := (D.exists_epsP (D.P2 hB hT)).choose_spec.2) (D.tup_ne _) (D.tup_ne _) y
  rw [(D.agree12 hB hT y).rH_shift _ hdd SM]
  have hgi : ((D.z1 SM).jet (Fin.cons 0 y)).FJ.gi = met4 (-1) 0 (D.γi y) :=
    D.mk_gi (hch := (D.exists_epsP (D.P1 SM)).choose_spec.2) y
  rw [hgi, sum_shift_H]
  simp only [P2, P1, Params.zero, sub_zero, Ha2]
  show (((D.z1 SM).jet (Fin.cons 0 y)).res SM).rH +
    -((((D.z1 SM).jet (Fin.cons 0 y)).res SM).rH) = 0
  rw [add_neg_cancel]

/-- **The completed tuple solves the reduced Einstein rows on the slice**:
`𝓔^{tr} = ∇_{(μ}C_{ν)}`. -/
theorem z2_red (y : Fin 3 → ℝ) (μ ν : Fin 4) :
    (bosF SM (D.z2 hB hT) (Fin.cons 0 y)).1 μ ν =
      symDefect ((D.z2 hB hT).g (Fin.cons 0 y)) ((D.z2 hB hT).gi (Fin.cons 0 y))
        ((D.z2 hB hT).dg (Fin.cons 0 y)) ((D.z2 hB hT).ddg (Fin.cons 0 y)) μ ν := by
  have hA := D.agree12 hB hT y
  have hg : (D.z2 hB hT).g (Fin.cons 0 y) = (D.z1 SM).g (Fin.cons 0 y) := hA.g.symm
  have hgi : (D.z2 hB hT).gi (Fin.cons 0 y) = (D.z1 SM).gi (Fin.cons 0 y) := hA.gi.symm
  have hdg : (D.z2 hB hT).dg (Fin.cons 0 y) = (D.z1 SM).dg (Fin.cons 0 y) := hA.dg.symm
  have hdd : (D.z2 hB hT).ddg (Fin.cons 0 y) = fun a b c d => (D.z1 SM).ddg (Fin.cons 0 y) a b c d +
      (if a = 0 ∧ b = 0 then (D.W2 SM y - 0) c d else 0) :=
    D.ddg_mk (P := D.P1 SM) (P' := D.P2 hB hT)
      (hch := (D.exists_epsP (D.P1 SM)).choose_spec.2)
      (hch' := (D.exists_epsP (D.P2 hB hT)).choose_spec.2) (D.tup_ne _) (D.tup_ne _) y
  have hTa : ((D.z2 hB hT).jet (Fin.cons 0 y)).Tact SM = ((D.z1 SM).jet (Fin.cons 0 y)).Tact SM :=
    (hA.Tact_eq (by rw [D.z2_cψ]) (by rw [D.z2_cψb]) SM).symm
  have hW := D.W2_symm hT y
  have key := Etr_shift ((D.z1 SM).g (Fin.cons 0 y)) ((D.z1 SM).gi (Fin.cons 0 y))
    ((D.z1 SM).dg (Fin.cons 0 y)) ((D.z1 SM).ddg (Fin.cons 0 y))
    (fun a b c d => if a = 0 ∧ b = 0 then (D.W2 SM y - 0) c d else 0)
    ((D.z1 SM).gi_symm (Fin.cons 0 y)) ((D.z1 SM).hinv (Fin.cons 0 y))
    ((D.z1 SM).ddg_symm1 (Fin.cons 0 y)) ((D.z1 SM).ddg_symm2 (Fin.cons 0 y))
    (fun α β c d => by
      by_cases h : α = 0 ∧ β = 0
      · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
      · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩)])
    (fun α β c d => by
      split_ifs
      · simp only [sub_zero]; exact hW c d
      · rfl)
    (by simp) (((D.z1 SM).jet (Fin.cons 0 y)).Tact SM) SM.Λ SM.κ μ ν
  have hgz : (D.z1 SM).gi (Fin.cons 0 y) = met4 (-1) 0 (D.γi y) :=
    D.mk_gi (hch := (D.exists_epsP (D.P1 SM)).choose_spec.2) y
  rw [hgz, sum_shift_g, ← hgz] at key
  have hE : (bosF SM (D.z2 hB hT) (Fin.cons 0 y)).1 μ ν =
      traceRev ((D.z2 hB hT).g (Fin.cons 0 y)) ((D.z2 hB hT).gi (Fin.cons 0 y)) (fun a b =>
        einstein ((D.z2 hB hT).g (Fin.cons 0 y)) ((D.z2 hB hT).gi (Fin.cons 0 y))
          ((D.z2 hB hT).dg (Fin.cons 0 y)) ((D.z2 hB hT).ddg (Fin.cons 0 y)) a b +
          SM.Λ * (D.z2 hB hT).g (Fin.cons 0 y) a b -
          SM.κ * ((D.z2 hB hT).jet (Fin.cons 0 y)).Tact SM a b) μ ν := rfl
  have hE1 : (bosF SM (D.z1 SM) (Fin.cons 0 y)).1 μ ν =
      traceRev ((D.z1 SM).g (Fin.cons 0 y)) ((D.z1 SM).gi (Fin.cons 0 y)) (fun a b =>
        einstein ((D.z1 SM).g (Fin.cons 0 y)) ((D.z1 SM).gi (Fin.cons 0 y))
          ((D.z1 SM).dg (Fin.cons 0 y)) ((D.z1 SM).ddg (Fin.cons 0 y)) a b +
          SM.Λ * (D.z1 SM).g (Fin.cons 0 y) a b -
          SM.κ * ((D.z1 SM).jet (Fin.cons 0 y)).Tact SM a b) μ ν := rfl
  rw [hE, hg, hgi, hdg, hdd, hTa]
  have hW2 : (D.W2 SM y - 0) μ ν = -2 * ((bosF SM (D.z1 SM) (Fin.cons 0 y)).1 μ ν -
      symDefect ((D.z1 SM).g (Fin.cons 0 y)) ((D.z1 SM).gi (Fin.cons 0 y))
        ((D.z1 SM).dg (Fin.cons 0 y)) ((D.z1 SM).ddg (Fin.cons 0 y)) μ ν) := by
    simp only [sub_zero]; rfl
  rw [hW2, ← hE1] at key
  linarith

/-- **The completed tuple satisfies the Einstein normal rows** (from the Hamiltonian and
momentum constraints). -/
theorem z2_einsteinConstraint (hc : D.Constrained SM) (y : Fin 3 → ℝ) (ν : Fin 4) :
    einsteinConstraint SM (D.z2 hB hT) (Fin.cons 0 y) ν = 0 := by
  obtain ⟨h0, hs⟩ := D.einsteinConstraint_mk SM
    (hch := (D.exists_epsP (D.P2 hB hT)).choose_spec.2) (D.tup_ne _) y (D.z2_rD hB hT y)
    (D.z2_rDb hB hT y)
  refine Fin.cases ?_ (fun i => ?_) ν
  · exact h0.trans (hc y).1
  · exact (hs i).trans ((hc y).2.1 i)

/-- **The completion is slice-constrained.** -/
theorem z2_sliceConstrained (hc : D.Constrained SM) :
    SliceConstrained SM (D.z2 hB hT) := by
  intro y
  have hC0 : ∀ y' : Fin 3 → ℝ, CF (D.z2 hB hT) (Fin.cons 0 y') = 0 := fun y' =>
    D.CF_mk (hch := (D.exists_epsP (D.P2 hB hT)).choose_spec.2) (D.tup_ne _) y'
  obtain ⟨hdC, hE⟩ := slice_close SM (D.z2 hB hT) y hC0 (D.z2_red hB hT y)
    (D.z2_einsteinConstraint hB hT hc y)
  refine ⟨?_, ?_, hC0 y, hdC⟩
  · have h2 : (((D.z2 hB hT).jet (Fin.cons 0 y)).res SM).rA = 0 :=
      funext fun ν => D.z2_rA hB hT hc y ν
    have h3 := D.z2_rH hB hT y
    refine Prod.ext hE (Prod.ext ?_ ?_)
    · exact h2
    · exact h3
  · refine Prod.ext ?_ ?_
    · exact D.z2_rD hB hT y
    · exact D.z2_rDb hB hT y

end Final

end SliceCauchy

end RenewalGeometry.GenSlice
