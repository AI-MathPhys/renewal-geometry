/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.ActualJetStateField
import RenewalGeometry.Continuum.CoupledBootstrapFlatVacuum

/-!
# Physical solutions of the actual-jet system and the constraint reduction

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`
(`app:generated-dynamics`) on top of `prop:actual-jet-writer` (`ActualJetState.writer_pde`).

For a smooth tuple `z` (`ActualJetBridge.Tuple`: metric, gauge potential in exact temporal gauge,
Higgs field, spinor and dual spinor on `ℝ × 𝕋³`) with actual-jet state field `𝒰(z) = stateF`, the
writer identity `∂_t𝒰 + Σ_j𝒜^j∂_j𝒰 = 𝓕(𝒰) + errF` holds with the residual/gauge forcing
`errF = 𝓑(𝒰)(R_B, R_D) + Σ_j𝒬^j∂_jR_D + 𝒥_C C + 𝒥_C^α∂_αC` (`writer_pde_err`).

* `SymEqAt`, **`symEqAt_iff`** — `𝒰(z)` solves the independent symmetric system
  `eq:generated-extension` at `x` iff `errF(x) = 0`.
* **`symEqAt_of_physical`** — on an open set where `z` is a physical solution (`IsPhysicalOn`:
  all Einstein, Yang–Mills, Higgs, Dirac and dual Dirac residuals and the harmonic defect vanish),
  `𝒰(z)` solves the independent symmetric system (the step "its actual first jets satisfy
  `eq:generated-extension` by `prop:actual-jet-writer`" of the lemma's proof).
* **Residual slaving** (`matter_of_symEqAt`, `einstein_of_symEqAt`): conversely, if `𝒰(z)`
  solves the symmetric system at `x`, then the Dirac, dual Dirac and Higgs equations and the three
  spatial frame components of the Yang–Mills equation hold at `x` (the Dirac rows through
  `c_0² = 1`, `c0_mul_c0`), and if moreover the harmonic defect vanishes to first order at `x`, the
  trace-reversed Einstein residual vanishes at `x`.
* **`physical_iff_constraints`** — on an open set: `z` is a physical solution **iff** `𝒰(z)`
  solves the symmetric system, the harmonic constraint `C(g) = 0` and the Gauss constraint
  `e_0{}^ν r^A_ν = 0` hold.  Hence the physical identification of a solution `U` of the symmetric
  system reduces exactly to the propagation of three constraint families: the defining-jet
  identities `U = 𝒰(head U)`, `C = 0` and the Gauss law.
* Non-vacuity: the flat vacuum (`CoupledBootstrap.FlatVacuum.flat`, data `trivSMM`).

No constraint propagation is proved here.  For general theory data `SMData` (arbitrary currents
`Jcur`, Higgs sources and Dirac stress forms) the Gauss constraint does **not** propagate
(`GenConstraintObs.bad_obstruction`); propagation needs the Noether identities of the
Standard-Model couplings in addition to the symmetric system.
-/

open Filter Topology Set
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.GenConstraint

open SobolevOpen (pd)
open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci
  ActualJetBridge ActualJetCompleteForcing ActualJetRecon ActualJetState

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable (SM : SMData (MatLie m) V S S') (z : Tuple m V S S')

/-- The state field solves the independent symmetric system at `x`. -/
def SymEqAt (x : ST 3) : Prop :=
  pd (stateF SM z) 0 x + ∑ j : Fin 3, princL SM (stateF SM z x) j (pd (stateF SM z) j.succ x) =
    toP (Fsys SM (ofP (stateF SM z x)))

/-- The residual and gauge-defect forcing of `eq:actual-jet-writer` along the tuple. -/
def errF (x : ST 3) : StateP m V S S' :=
  (BmL SM (stateF SM z x) (bosF SM z x) + DmL SM (stateF SM z x) (dirF SM z x)) +
    ∑ j : Fin 3, QmL SM j (stateF SM z x) (pd (dirF SM z) j.succ x) +
    (GcL (stateF SM z x) (CF z x) + GdL 0 (stateF SM z x) (pd (CF z) 0 x) +
      ∑ j : Fin 3, GdL j.succ (stateF SM z x) (pd (CF z) j.succ x))

theorem writer_pde_err (x : ST 3) :
    pd (stateF SM z) 0 x + ∑ j : Fin 3, princL SM (stateF SM z x) j (pd (stateF SM z) j.succ x) =
      toP (Fsys SM (ofP (stateF SM z x))) + errF SM z x := by
  rw [writer_pde SM z x]
  unfold errF
  abel

theorem symEqAt_iff (x : ST 3) : SymEqAt SM z x ↔ errF SM z x = 0 := by
  unfold SymEqAt
  rw [writer_pde_err SM z x]
  exact add_eq_left

/-- The Dirac block of `errF`. -/
theorem errF_psi (x : ST 3) : (errF SM z x).2.2.2.2.2.2.2.1 =
    -((frameU (ginvOf (ofP (stateF SM z x)).g)).N • (SM.D.Fr.c 0 • (dirF SM z x).1)) := by
  simp [errF, BmL, DmL, QmL, GcL, GdL, toP, Bsys, Qsys, pState, bosR, dirR, ofR, recon,
    Prod.fst_sum, Prod.snd_sum]


/-- The dual Dirac block of `errF`. -/
theorem errF_psib (x : ST 3) : (errF SM z x).2.2.2.2.2.2.2.2.2.1 =
    -((frameU (ginvOf (ofP (stateF SM z x)).g)).N • (SM.Db.Fr.c 0 • (dirF SM z x).2)) := by
  simp [errF, BmL, DmL, QmL, GcL, GdL, toP, Bsys, Qsys, pState, bosR, dirR, ofR, recon,
    Prod.fst_sum, Prod.snd_sum]

/-- The Higgs momentum block of `errF`. -/
theorem errF_Pm (x : ST 3) : (errF SM z x).2.2.2.2.2.1 =
    -((frameU (ginvOf (ofP (stateF SM z x)).g)).N • (bosF SM z x).2.2) := by
  simp [errF, BmL, DmL, QmL, GcL, GdL, toP, Bsys, Qsys, pState, bosR, dirR, ofR, recon,
    Prod.fst_sum, Prod.snd_sum]

/-- The electric block of `errF`. -/
theorem errF_E (x : ST 3) (a : Fin 3) : (errF SM z x).2.2.1 a =
    -((frameU (ginvOf (ofP (stateF SM z x)).g)).N •
      ∑ ν, (frameU (ginvOf (ofP (stateF SM z x)).g)).fr a.succ ν • (bosF SM z x).2.1 ν) := by
  simp [errF, BmL, DmL, QmL, GcL, GdL, toP, Bsys, Qsys, pState, bosR, dirR, ofR, recon,
    Prod.fst_sum, Prod.snd_sum]

/-- The metric `p`-block of `errF` when the Dirac residuals and the harmonic defect with its first
derivatives vanish at `x`: `2N 𝓔^{tr}`. -/
theorem errF_p (x : ST 3) (hD : dirF SM z x = 0) (hC : CF z x = 0)
    (hdC : ∀ α, pd (CF z) α x = 0) (μ ν : Fin 4) : (errF SM z x).1.2.1 μ ν =
    2 * (frameU (ginvOf (ofP (stateF SM z x)).g)).N * (bosF SM z x).1 μ ν := by
  unfold errF
  rw [hD, hC]
  simp only [hdC, map_zero, add_zero, zero_add]
  simp [BmL, QmL, toP, Bsys, Qsys, bosR, ofR, recon, stressR, DiracStressForm.stressRes,
    Prod.fst_sum, traceRev, trG]


omit [FiniteDimensional ℝ V] in
/-- `c_0² = 1` for a Lorentzian Clifford frame (`c_0c_0 + c_0c_0 = -2ε_0 = 2`). -/
theorem c0_mul_c0 {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀] (D : DiracData (MatLie m) V S₀) :
    D.Fr.c 0 * D.Fr.c 0 = 1 := by
  have h := D.Fr.anticomm 0 0
  simp only [ite_true, D.lorentz.1] at h
  have h2 : (2 : ℝ) • (D.Fr.c 0 * D.Fr.c 0) = (2 : ℝ) • (1 : Module.End ℝ S₀) := by
    rw [two_smul, h]; norm_num
  exact smul_right_injective _ (two_ne_zero) h2

omit [FiniteDimensional ℝ V] in
/-- A Dirac block row `-(N c_0 r) = 0` with `N > 0` forces `r = 0`. -/
theorem eq_zero_of_dirac_row {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀]
    (D : DiracData (MatLie m) V S₀) {N : ℝ} (hN : 0 < N) {r : S₀}
    (h : -(N • (D.Fr.c 0 • r)) = 0) : r = 0 := by
  have h1 : D.Fr.c 0 • r = 0 := by
    rw [neg_eq_zero] at h
    exact (smul_eq_zero.mp h).resolve_left hN.ne'
  have h2 : D.Fr.c 0 • (D.Fr.c 0 • r) = r := by
    rw [smul_smul, c0_mul_c0, one_smul]
  rw [← h2, h1, smul_zero]

/-- `(ofP (stateF x)).g` is the metric of the tuple. -/
theorem stateF_g (x : ST 3) : (ofP (stateF SM z x)).g = z.g x := rfl

/-- **Residual slaving, matter rows** (`prop:actual-jet-writer` read backwards): if the actual-jet
state field of a smooth tuple solves the independent symmetric system at `x`, then at `x` the Dirac
and dual Dirac equations, the Higgs equation and the three spatial frame components of the
Yang–Mills equation hold. -/
theorem matter_of_symEqAt {x : ST 3} (h : SymEqAt SM z x) :
    dirF SM z x = 0 ∧ (bosF SM z x).2.2 = 0 ∧
      ∀ a : Fin 3, ∑ ν, (frameU (z.gi x)).fr a.succ ν • (bosF SM z x).2.1 ν = 0 := by
  have h0 := (symEqAt_iff SM z x).1 h
  have hN := (frameU (ginvOf (ofP (stateF SM z x)).g)).N_pos
  refine ⟨Prod.ext ?_ ?_, ?_, fun a => ?_⟩
  · have := errF_psi SM z x
    rw [h0] at this
    exact eq_zero_of_dirac_row SM.D hN this.symm
  · have := errF_psib SM z x
    rw [h0] at this
    exact eq_zero_of_dirac_row SM.Db hN this.symm
  · have := errF_Pm SM z x
    rw [h0] at this
    simp only [Prod.snd_zero, Prod.fst_zero] at this
    have h2 := this.symm
    rw [neg_eq_zero] at h2
    exact (smul_eq_zero.mp h2).resolve_left hN.ne'
  · have := errF_E SM z x a
    rw [h0] at this
    simp only [Prod.snd_zero, Prod.fst_zero, Pi.zero_apply] at this
    have h2 := this.symm
    rw [neg_eq_zero] at h2
    exact (smul_eq_zero.mp h2).resolve_left hN.ne'

/-- **Residual slaving, Einstein row**: if the state field solves the independent symmetric system
at `x` and the harmonic defect vanishes with its first derivatives at `x`, then the trace-reversed
Einstein residual vanishes at `x` (the `p`-row of `eq:actual-jet-writer` is `2N 𝓔^{tr}` plus the
gauge forcing). -/
theorem einstein_of_symEqAt {x : ST 3} (h : SymEqAt SM z x) (hC : CF z x = 0)
    (hdC : ∀ α, pd (CF z) α x = 0) : (bosF SM z x).1 = 0 := by
  have h0 := (symEqAt_iff SM z x).1 h
  have hD := (matter_of_symEqAt SM z h).1
  have hN := (frameU (ginvOf (ofP (stateF SM z x)).g)).N_pos
  funext μ ν
  have := errF_p SM z x hD hC hdC μ ν
  rw [h0] at this
  simp only [Prod.snd_zero, Prod.fst_zero] at this
  have h2 := this.symm
  have hN2 : 2 * (frameU (ginvOf (ofP (stateF SM z x)).g)).N ≠ 0 := by positivity
  exact (mul_eq_zero.mp h2).resolve_left hN2


/-- **The Gauss constraint**: the normal frame component `e_0{}^ν r^A_ν` of the Yang–Mills
residual (the component of `∇^μF_{μν} = J_ν` along the unit normal, which contains no time
derivative of the electric field). -/
def gaussF (x : ST 3) : MatLie m := ∑ ν, (frameU (z.gi x)).fr 0 ν • (bosF SM z x).2.1 ν

theorem jet_e_eq (x : ST 3) (A ν : Fin 4) : (z.jet x).FJ.e A ν = (frameU (z.gi x)).fr A ν := by
  have hl : IsLorChart (z.gi x) := z.lor x
  show frU (z.gi x) A ν = _
  rw [frU_eq hl]
  unfold frameU
  rw [dif_pos hl]

/-- A covector-valued family whose four frame components vanish is zero (frame completeness,
`ActualJetRecon.inv_vec`). -/
theorem eq_zero_of_frame_components {M : Type*} [AddCommGroup M] [Module ℝ M] (x : ST 3)
    (w : Fin 4 → M) (h : ∀ A, ∑ ν, (frameU (z.gi x)).fr A ν • w ν = 0) : w = 0 := by
  funext γ
  rw [inv_vec (z.jet x).FJ w γ]
  refine Finset.sum_eq_zero fun A _ => ?_
  have : ∑ β, (z.jet x).FJ.e A β • w β = 0 := by
    simp only [jet_e_eq]; exact h A
  rw [this, smul_zero]

theorem pd_eq_zero_of_eventually {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ST 3 → E} {x : ST 3} (h : f =ᶠ[𝓝 x] 0) (μ : Fin 4) : pd f μ x = 0 := by
  unfold SobolevOpen.pd
  rw [h.fderiv_eq]
  simp

/-- **A physical solution on `O`**: all physical residuals (trace-reversed Einstein, Yang–Mills,
Higgs, Dirac, dual Dirac) and the harmonic defect vanish on `O`. -/
def IsPhysicalOn (O : Set (ST 3)) : Prop :=
  ∀ y ∈ O, bosF SM z y = 0 ∧ dirF SM z y = 0 ∧ CF z y = 0

/-- **Physical tuples generate solutions of the independent symmetric system**
(`lem:generated-physical-identification`: "Its actual first jets satisfy `eq:generated-extension`
by `prop:actual-jet-writer`"): on an open set where the tuple is a physical solution, its actual-jet
state field solves `∂_t𝒰 + Σ_j𝒜^j(g)∂_j𝒰 = 𝓕(𝒰)`. -/
theorem symEqAt_of_physical {O : Set (ST 3)} (hO : IsOpen O) (hP : IsPhysicalOn SM z O)
    {x : ST 3} (hx : x ∈ O) : SymEqAt SM z x := by
  rw [symEqAt_iff]
  have evD : dirF SM z =ᶠ[𝓝 x] 0 :=
    Filter.eventually_of_mem (hO.mem_nhds hx) fun y hy => (hP y hy).2.1
  have evC : CF z =ᶠ[𝓝 x] 0 :=
    Filter.eventually_of_mem (hO.mem_nhds hx) fun y hy => (hP y hy).2.2
  unfold errF
  rw [(hP x hx).1, (hP x hx).2.1, (hP x hx).2.2]
  simp only [pd_eq_zero_of_eventually evD, pd_eq_zero_of_eventually evC, map_zero, add_zero,
    Finset.sum_const_zero]

/-- **Reduction of physical identification to the constraints** (`lem:generated-physical-
identification`, `prop:actual-jet-writer`): on an open set `O`, a smooth tuple is a physical
solution (all residuals and the harmonic defect vanish) **iff** its actual-jet state field solves
the independent symmetric system, the harmonic constraint `C(g) = 0` holds and the Gauss
constraint `e_0{}^ν r^A_ν = 0` holds.  The physical residuals are thus slaved to the two
constraints along every solution of the symmetric system that is the actual-jet state of its own
head fields (`matter_of_symEqAt`, `einstein_of_symEqAt`). -/
theorem physical_iff_constraints {O : Set (ST 3)} (hO : IsOpen O) :
    IsPhysicalOn SM z O ↔ ∀ y ∈ O, SymEqAt SM z y ∧ CF z y = 0 ∧ gaussF SM z y = 0 := by
  constructor
  · intro hP y hy
    refine ⟨symEqAt_of_physical SM z hO hP hy, (hP y hy).2.2, ?_⟩
    unfold gaussF
    rw [(hP y hy).1]
    simp
  · intro h y hy
    obtain ⟨hS, hC, hG⟩ := h y hy
    have evC : CF z =ᶠ[𝓝 y] 0 :=
      Filter.eventually_of_mem (hO.mem_nhds hy) fun w hw => (h w hw).2.1
    have hdC : ∀ α, pd (CF z) α y = 0 := fun α => pd_eq_zero_of_eventually evC α
    obtain ⟨hD, hH, hE⟩ := matter_of_symEqAt SM z hS
    have hEin := einstein_of_symEqAt SM z hS hC hdC
    have hA : (bosF SM z y).2.1 = 0 := by
      refine eq_zero_of_frame_components z y _ fun A => ?_
      induction A using Fin.cases with
      | zero => exact hG
      | succ a => exact hE a
    exact ⟨Prod.ext hEin (Prod.ext hA hH), hD, hC⟩


/-! ### Non-vacuity: the flat vacuum -/

open CoupledBootstrap.FlatVacuum in
/-- The flat vacuum is a physical solution on all of space-time. -/
theorem flat_isPhysicalOn : IsPhysicalOn trivSMM flat Set.univ := fun x _ =>
  ⟨flat_bosF x, Subsingleton.elim _ _, flat_CF x⟩

open CoupledBootstrap.FlatVacuum in
/-- For the flat vacuum the three conditions of `physical_iff_constraints` hold everywhere. -/
example (y : ST 3) : SymEqAt trivSMM flat y ∧ CF flat y = 0 ∧ gaussF trivSMM flat y = 0 :=
  (physical_iff_constraints trivSMM flat isOpen_univ).1 flat_isPhysicalOn y trivial

end RenewalGeometry.GenConstraint
