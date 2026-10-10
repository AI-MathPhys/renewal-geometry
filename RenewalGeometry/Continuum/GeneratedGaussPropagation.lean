/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedNoetherIdentities
import RenewalGeometry.Continuum.GeneratedConstraintObstruction

/-!
# Propagation of the Gauss constraint along the actual-jet symmetric system

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`
(`app:generated-dynamics`), constraint-propagation route: a smooth field tuple whose actual-jet
state solves the independent symmetric system `eq:generated-extension` on a slab satisfies the
Dirac, Higgs and spatial Yang–Mills equations there (`GenConstraint.matter_of_symEqAt`); the
remaining Yang–Mills component, the **Gauss constraint** `G = e_0{}^ν r^A_ν`, then obeys a linear
homogeneous transport equation along the unit normal, by the Yang–Mills Bianchi identity and the
current Noether identity (`GenNoether.div_rA_eq_zero`):
`∂_ν(ϱe_0{}^νG) + [A_ν, ϱe_0{}^νG] = 0`.  Hence `G ≡ 0` if `G = 0` initially.

* **`transport_unique`** (generic, no renewal notions): a `C¹` spatially periodic `ℂ^N`-valued
  field `w` on `[t₀, t₁] × 𝕋^d` with a scalar principal part, `‖Σ_μ c^μ ∂_μw‖ ≤ K‖w‖`, `c^μ`
  periodic and `C¹`, `c⁰ ≥ κ > 0`, vanishing at `t₀` vanishes on the slab (the `L²` energy
  estimate `SymHypEnergy.l2_energy_estimate` with coefficients `c^μ · 1`).
* `densR_eq_gauss` — along a solution of the symmetric system the Yang–Mills residual density is
  `-ϱ e_0{}^ν G` (frame completeness `g^{νβ} = -e_0^νe_0^β + Σ_a e_a^νe_a^β`).
* `gauss_transport` — the transport equation.
* **`gauss_propagation`** — for theory data with the current Noether identity
  (`GenNoether.CurrentNoether`; proved for the Standard-Model-type bosonic data
  `GenNoether.adjSM_currentNoether`) and smooth sources: if the actual-jet state of a smooth tuple
  solves the symmetric system on an open slab `(a, b) × 𝕋³` and the Gauss constraint vanishes at
  `t₀ ∈ (a, b)`, it vanishes on `[t₀, t₁] × 𝕋³` for every `t₁ < b`.
* **`physical_of_harmonic`** — with `GenConstraint.physical_iff_constraints`: such a tuple whose
  harmonic defect vanishes on the slab is a physical solution on `(t₀, b) × 𝕋³`; the physical
  identification is reduced to the harmonic constraint alone.
* `not_currentNoether_badSM` — the obstruction data `GenConstraintObs.badSM` violate the
  current Noether identity (consistency with `GenConstraintObs.bad_obstruction`).

Regularity: the tuple is `C^∞` (`ActualJetBridge.Tuple`); the transport argument uses the third
derivatives of the gauge potential (through `∂G`) and the second derivatives of the metric.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.GenGauss

open SobolevOpen (pd)
open SymHypEnergy PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge ActualJetBridge ActualJetState
  JetCurve GenConstraint GenNoether

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

/-! ### Uniqueness for transport equations with a scalar principal part -/

section Transport

variable {d : ℕ} {N : Type*} [Fintype N] [DecidableEq N]

/-- The coefficient matrices `c^μ · 1`. -/
def scalCoeff (c : Fin (d + 1) → ST d → ℝ) (μ : Fin (d + 1)) (x : ST d) : N → N → ℂ :=
  fun i k => (c μ x : ℂ) * SymHypUniqueness.QLSymSys.idM i k

theorem mv_scalCoeff (c : Fin (d + 1) → ST d → ℝ) (μ : Fin (d + 1)) (x : ST d) (v : N → ℂ) :
    mv (scalCoeff c μ x) v = c μ x • v := by
  funext i
  simp [mv, scalCoeff, SymHypUniqueness.QLSymSys.idM, Complex.real_smul]

theorem norm_scalCoeff_le (r : ℝ) :
    ‖(fun i k => (r : ℂ) * SymHypUniqueness.QLSymSys.idM i k : N → N → ℂ)‖ ≤ |r| := by
  refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr fun i => ?_
  refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr fun k => ?_
  by_cases h : i = k <;> simp [SymHypUniqueness.QLSymSys.idM, h]

/-- **Uniqueness for a transport equation with a scalar principal part** on `[t₀, t₁] × 𝕋^d`:
if `w` is `C¹` on `(a, b) × ℝ^d`, spatially periodic, `‖Σ_μ c^μ∂_μw‖ ≤ K‖w‖` on the closed slab
with periodic `C¹` coefficients `c^μ` and `c⁰ ≥ κ > 0`, and `w(t₀) = 0`, then `w = 0` on the slab. -/
theorem transport_unique {w : ST d → N → ℂ} {c : Fin (d + 1) → ST d → ℝ} {a t₀ t₁ b : ℝ}
    (ha : a < t₀) (h01 : t₀ < t₁) (hb : t₁ < b) (hw : ContDiffOn ℝ 1 w (openSlab a b))
    (hwp : IsSPeriodic w) (hc : ∀ μ, ContDiffOn ℝ 1 (c μ) (openSlab a b))
    (hcp : ∀ μ, IsSPeriodic (c μ)) {κ : ℝ} (hκ : 0 < κ) (hc0 : ∀ x ∈ slab t₀ t₁, κ ≤ c 0 x)
    {K : ℝ} (hK : 0 ≤ K) (heq : ∀ x ∈ slab t₀ t₁, ‖∑ μ, c μ x • pd w μ x‖ ≤ K * ‖w x‖)
    (h0 : ∀ y : Fin d → ℝ, w (Fin.cons t₀ y) = 0) : ∀ x ∈ slab t₀ t₁, w x = 0 := by
  -- Lipschitz constants and bounds of the coefficients
  have hL : ∀ μ, ∃ L : ℝ≥0, LipschitzOnWith L (c μ) (slab t₀ t₁) := fun μ =>
    KatoGalerkin.exists_lipschitzOnWith_slab (hc μ) (hcp μ) ha hb
  choose L hL using hL
  have hB : ∀ μ, ∃ C, ∀ x ∈ slab t₀ t₁, ‖c μ x‖ ≤ C := fun μ =>
    KatoGalerkin.exists_bound_slab (hc μ).continuousOn (hcp μ) ha hb
  choose C hC using hB
  set A : Fin (d + 1) → ST d → N → N → ℂ := fun μ x => scalCoeff c μ x with hA
  have hsym : SymHyp A w a t₀ t₁ b (∑ μ, L μ) (∑ μ, |C μ|) := by
    refine ⟨ha, h01, hb, hw, hwp, fun μ k x => ?_, fun μ x i k => ?_, fun μ => ?_,
      fun μ x hx => ?_⟩
    · show scalCoeff c μ (x + sshift k) = scalCoeff c μ x
      unfold scalCoeff
      rw [hcp μ k x]
    · by_cases h : i = k
      · subst h; simp [hA, scalCoeff, SymHypUniqueness.QLSymSys.idM]
      · simp [hA, scalCoeff, SymHypUniqueness.QLSymSys.idM, h, Ne.symm h]
    · refine LipschitzOnWith.weaken ?_ (Finset.single_le_sum (f := L) (fun i _ => bot_le)
        (Finset.mem_univ μ))
      refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
      have h1 := (hL μ).dist_le_mul x hx y hy
      rw [dist_eq_norm]
      have e : A μ x - A μ y = fun i k => ((c μ x - c μ y : ℝ) : ℂ) *
          SymHypUniqueness.QLSymSys.idM i k := by
        funext i k; simp [hA, scalCoeff]; ring
      rw [e]
      refine (norm_scalCoeff_le _).trans ?_
      rw [← Real.dist_eq]
      exact h1
    · refine (norm_scalCoeff_le _).trans ?_
      refine le_trans ?_ (Finset.single_le_sum (f := fun μ => |C μ|) (fun i _ => abs_nonneg _)
        (Finset.mem_univ μ))
      exact (le_trans (le_of_eq (Real.norm_eq_abs _).symm) (hC μ x hx)).trans (le_abs_self _)
  have hpos : ∀ x ∈ slab t₀ t₁, ∀ ξ : N → ℂ, κ * ∑ i, ‖ξ i‖ ^ 2 ≤ ip ξ (mv (A 0 x) ξ) := by
    intro x hx ξ
    rw [hA, mv_scalCoeff, ip_smul_right, ip_self_eq]
    exact mul_le_mul_of_nonneg_right (hc0 x hx) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hprinc : ∀ x ∈ slab t₀ t₁, ‖SymHypEnergy.princ A w x‖ ≤ (fun _ => (0 : ℝ)) x + K * ‖w x‖ := by
    intro x hx
    have : SymHypEnergy.princ A w x = ∑ μ, c μ x • pd w μ x := by
      unfold SymHypEnergy.princ
      simp only [hA, mv_scalCoeff]
    rw [this, zero_add]
    exact heq x hx
  have hest := l2_energy_estimate hsym hκ hK hpos continuousOn_const hprinc
  have hl0 : l2sq w t₀ = 0 := by
    unfold l2sq
    simp [h0]
  intro x hx
  have ht : x 0 ∈ Icc t₀ t₁ := hx
  have hb' := hest (x 0) ht
  rw [hl0] at hb'
  simp only [mul_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    MeasureTheory.integral_zero, intervalIntegral.integral_zero] at hb'
  have hnn : 0 ≤ l2sq w (x 0) := setIntegral_nonneg measurableSet_Icc fun y _ => sq_nonneg _
  have hzero : l2sq w (x 0) = 0 := by
    have := le_antisymm (by nlinarith [hb'] : l2sq w (x 0) ≤ 0) hnn
    exact this
  have hcont : Continuous fun y : Fin d → ℝ => w (Fin.cons (x 0) y) := hsym.w_slice_cont ht
  have hcube := SymHypUniqueness.eq_zero_on_cube_of_integral_eq_zero hcont hzero
  have hper : IsZPeriodic fun y : Fin d → ℝ => w (Fin.cons (x 0) y) := hwp.slice (x 0)
  have hfr : (fun i => Int.fract (Fin.tail x i)) ∈ Icc (0 : Fin d → ℝ) 1 :=
    ⟨fun i => Int.fract_nonneg _, fun i => (Int.fract_lt_one _).le⟩
  have := hcube _ hfr
  rw [hper.apply_fract (Fin.tail x), Fin.cons_self_tail] at this
  exact this

/-- A positive continuous periodic function has a positive lower bound on every closed sub-slab. -/
theorem exists_pos_lower_slab {f : ST d → ℝ} {a b t₀ t₁ : ℝ} (hf : ContinuousOn f (openSlab a b))
    (hp : IsSPeriodic f) (hpos : ∀ x, 0 < f x) (ha : a < t₀) (hb : t₁ < b) :
    ∃ κ > 0, ∀ x ∈ slab t₀ t₁, κ ≤ f x := by
  have hg : ContinuousOn (fun x => (f x)⁻¹) (openSlab a b) :=
    hf.inv₀ fun x _ => (hpos x).ne'
  have hgp : IsSPeriodic (fun x => (f x)⁻¹) := fun k x => by simp only [hp k x]
  obtain ⟨C, hC⟩ := KatoGalerkin.exists_bound_slab hg hgp ha hb
  refine ⟨(max C 1)⁻¹, inv_pos.2 (lt_of_lt_of_le one_pos (le_max_right _ _)), fun x hx => ?_⟩
  have h1 : (f x)⁻¹ ≤ max C 1 := by
    have := hC x hx
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hpos x))] at this
    exact this.trans (le_max_left _ _)
  have h2 : 0 < (f x)⁻¹ := inv_pos.2 (hpos x)
  calc (max C 1)⁻¹ ≤ ((f x)⁻¹)⁻¹ := inv_anti₀ h2 h1
    _ = f x := inv_inv _

end Transport

/-! ### Complexified matrix fields -/

section Cplx

variable {m : ℕ}

/-- The complexified entries of a `gl(m)` element. -/
def cplxLin (m : ℕ) : MatLie m →ₗ[ℝ] (Fin m × Fin m → ℂ) where
  toFun X p := (toMat X p.1 p.2 : ℂ)
  map_add' X Y := by funext p; simp [toMat_add]
  map_smul' c X := by funext p; simp [toMat_smul, Complex.real_smul]

/-- The complexified entries as a continuous linear map. -/
def cplxL (m : ℕ) : MatLie m →L[ℝ] (Fin m × Fin m → ℂ) := LinearMap.toContinuousLinearMap (cplxLin m)

theorem cplxL_apply (X : MatLie m) (p : Fin m × Fin m) : cplxL m X p = (toMat X p.1 p.2 : ℂ) :=
  rfl

/-- `gl(m)` elements as plain arrays (for the sup norm). -/
def toArr (X : MatLie m) : Fin m → Fin m → ℝ := X

theorem norm_cplxL (X : MatLie m) : ‖cplxL m X‖ = ‖X‖ := by
  have hX : ‖X‖ = ‖toArr X‖ := rfl
  have ht : ∀ i k, toMat X i k = toArr X i k := fun _ _ => rfl
  rw [hX]
  refine le_antisymm ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun p => ?_
    rw [cplxL_apply, Complex.norm_real, ht]
    exact (norm_le_pi_norm (toArr X p.1) p.2).trans (norm_le_pi_norm (toArr X) p.1)
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun k => ?_
    have := norm_le_pi_norm (cplxL m X) (i, k)
    rw [cplxL_apply, Complex.norm_real, ht] at this
    exact this

theorem cplxL_eq_zero {X : MatLie m} (h : cplxL m X = 0) : X = 0 := by
  rw [← norm_eq_zero, ← norm_cplxL, h, norm_zero]

/-- The bracket of `gl(m)` is bounded. -/
theorem exists_lie_bound (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ X Y : MatLie m, ‖⁅X, Y⁆‖ ≤ C * ‖X‖ * ‖Y‖ := by
  let B' : MatLie m →L[ℝ] MatLie m →L[ℝ] MatLie m :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap : (MatLie m →ₗ[ℝ] MatLie m) ≃ₗ[ℝ]
        (MatLie m →L[ℝ] MatLie m)).toLinearMap ∘ₗ lieB m)
  exact ⟨‖B'‖, ContinuousLinearMap.opNorm_nonneg B', fun X Y => B'.le_opNorm₂ X Y⟩

end Cplx

/-! ### The Gauss constraint along the actual-jet symmetric system -/

section Gauss

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable (SM : SMData (MatLie m) V S S') (z : Tuple m V S S')

theorem e_eq_frameU (y : ST 3) (A ν : Fin 4) : z.e y A ν = (frameU (z.gi y)).fr A ν :=
  GenConstraint.jet_e_eq z y A ν

theorem adapted (y : ST 3) : (frameU (z.gi y)).IsAdapted (z.gi y) := by
  have h := (z.jet y).hadapt
  rw [← (z.jet y).frameU_eq'] at h
  exact h

/-- The normal density weights `ϱ e_0{}^ν`. -/
def w0 (ν : Fin 4) (y : ST 3) : ℝ := rho z y * z.e y 0 ν

theorem contDiff_w0 (ν : Fin 4) : ContDiff ℝ ∞ (w0 z ν) := by
  have h1 := contDiff_rho z
  have h2 := z.contDiff_e 0 ν
  unfold w0
  fun_prop

theorem w0_zero_pos (y : ST 3) : 0 < w0 z 0 y := by
  unfold w0
  rw [e_eq_frameU, AdaptedFrame.fr_zero_zero]
  exact mul_pos (rho_pos z y) (inv_pos.2 (frameU (z.gi y)).N_pos)

theorem rho_per (k : Fin 3 → ℤ) (y : ST 3) : rho z (y + sshift k) = rho z y := by
  unfold rho detF
  rw [z.g_per k y]

theorem e_per (k : Fin 3 → ℤ) (y : ST 3) (A ν : Fin 4) : z.e (y + sshift k) A ν = z.e y A ν := by
  unfold Tuple.e
  rw [ActualJetState.gi_per z k y]

theorem isSPeriodic_w0 (ν : Fin 4) : IsSPeriodic (w0 z ν) := fun k y => by
  unfold w0
  rw [rho_per, e_per]

/-- The Gauss constraint in terms of the frame field. -/
theorem gaussF_eq (y : ST 3) :
    gaussF SM z y = ∑ ν, z.e y 0 ν • ((z.jet y).res SM).rA ν := by
  unfold gaussF
  simp only [e_eq_frameU]
  rfl

theorem contDiff_gaussF (hS : SMSmooth SM) : ContDiff ℝ ∞ (gaussF SM z) := by
  have : gaussF SM z = fun y => ∑ ν, z.e y 0 ν • ((z.jet y).res SM).rA ν :=
    funext (gaussF_eq SM z)
  rw [this]
  have h1 := z.contDiff_e
  have h2 := fun ν => ActualJetState.contDiff_rA SM z hS ν
  fun_prop

theorem isSPeriodic_gaussF : IsSPeriodic (gaussF SM z) := fun k y => by
  unfold gaussF
  rw [ActualJetState.gi_per z k y, ActualJetState.isSPeriodic_bosF SM z k y]

/-- **Along a solution of the symmetric system the Yang–Mills residual density is normal**:
`ϱ g^{νβ}r^A_β = -ϱ e_0{}^ν G` (the spatial frame components of `r^A` vanish by residual slaving,
and `g^{νβ} = -e_0^νe_0^β + Σ_a e_a^νe_a^β`). -/
theorem densR_eq_gauss {y : ST 3} (hsym : SymEqAt SM z y) (ν : Fin 4) :
    densR SM z y ν = -(w0 z ν y • gaussF SM z y) := by
  obtain ⟨-, -, hE⟩ := matter_of_symEqAt SM z hsym
  have had := adapted z y
  unfold densR w0
  set F := frameU (z.gi y)
  have hsum : ∑ β, z.gi y ν β • (bosF SM z y).2.1 β =
      -(F.fr 0 ν • ∑ β, F.fr 0 β • (bosF SM z y).2.1 β) +
        ∑ a : Fin 3, F.fr a.succ ν • ∑ β, F.fr a.succ β • (bosF SM z y).2.1 β := by
    simp only [had ν, add_smul, neg_smul, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      Finset.smul_sum, smul_smul, Finset.sum_smul]
    congr 1
    rw [Finset.sum_comm]
  have hz : ∑ a : Fin 3, F.fr a.succ ν • ∑ β, F.fr a.succ β • (bosF SM z y).2.1 β = 0 :=
    Finset.sum_eq_zero fun a _ => by rw [hE a, smul_zero]
  rw [hsum, hz, add_zero, e_eq_frameU]
  unfold gaussF
  rw [smul_neg, mul_smul]

theorem pd_neg' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ST 3 → E) (i : Fin 4)
    (x : ST 3) : pd (fun y => -f y) i x = -pd f i x := by
  unfold SobolevOpen.pd
  rw [fderiv_fun_neg]
  rfl

/-- **The Gauss transport equation**: on an open set where the actual-jet state solves the symmetric
system, `∂_ν(ϱe_0{}^νG) + [A_ν, ϱe_0{}^νG] = 0` (Yang–Mills Bianchi identity + current Noether
identity + residual slaving of the Higgs and Dirac equations). -/
theorem gauss_transport (hN : CurrentNoether SM) (hS : SMSmooth SM) {O : Set (ST 3)}
    (hO : IsOpen O) (hsym : ∀ y ∈ O, SymEqAt SM z y) {x : ST 3} (hx : x ∈ O) :
    ∑ ν, (pd (fun y => w0 z ν y • gaussF SM z y) ν x + ⁅z.A x ν, w0 z ν x • gaussF SM z x⁆) =
      0 := by
  obtain ⟨hD, hH, -⟩ := matter_of_symEqAt SM z (hsym x hx)
  have h0 := div_rA_eq_zero z hN hS hH hD
  have hloc : ∀ ν, (fun y => densR SM z y ν) =ᶠ[𝓝 x]
      fun y => -(w0 z ν y • gaussF SM z y) :=
    fun ν => Filter.eventually_of_mem (hO.mem_nhds hx) fun y hy => densR_eq_gauss SM z (hsym y hy) ν
  have hpd : ∀ ν, pd (fun y => densR SM z y ν) ν x =
      -pd (fun y => w0 z ν y • gaussF SM z y) ν x := by
    intro ν
    unfold SobolevOpen.pd
    rw [(hloc ν).fderiv_eq]
    exact pd_neg' (fun y => w0 z ν y • gaussF SM z y) ν x
  simp only [hpd, densR_eq_gauss SM z (hsym x hx), lie_neg] at h0
  rw [← neg_eq_zero, ← h0, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  abel

/-- The transport equation solved for the normal derivative:
`Σ_ν ϱe_0^ν∂_νG = -(Σ_ν∂_ν(ϱe_0^ν))G - Σ_ν ϱe_0^ν[A_ν, G]`. -/
theorem gauss_transport' (hN : CurrentNoether SM) (hS : SMSmooth SM) {O : Set (ST 3)}
    (hO : IsOpen O) (hsym : ∀ y ∈ O, SymEqAt SM z y) {x : ST 3} (hx : x ∈ O) :
    ∑ ν, w0 z ν x • pd (gaussF SM z) ν x =
      -((∑ ν, pd (w0 z ν) ν x) • gaussF SM z x) -
        ∑ ν, w0 z ν x • ⁅z.A x ν, gaussF SM z x⁆ := by
  have h := gauss_transport SM z hN hS hO hsym hx
  have hprod : ∀ ν, pd (fun y => w0 z ν y • gaussF SM z y) ν x =
      pd (w0 z ν) ν x • gaussF SM z x + w0 z ν x • pd (gaussF SM z) ν x := by
    intro ν
    unfold SobolevOpen.pd
    rw [fderiv_fun_smul (((contDiff_w0 z ν).differentiable (by simp)) x)
      (((contDiff_gaussF SM z hS).differentiable (by simp)) x)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      ContinuousLinearMap.smulRight_apply]
    rw [add_comm]
  simp only [hprod, lie_smul] at h
  rw [Finset.sum_smul, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← h]
  refine Finset.sum_congr rfl fun ν _ => ?_
  abel

theorem isSPeriodic_pd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ST 3 → E}
    (hf : IsSPeriodic f) (i : Fin 4) : IsSPeriodic (pd f i) := fun k x => by
  unfold SobolevOpen.pd
  rw [KatoGalerkin.isSPeriodic_fderiv hf k x]

theorem pd_cplxL {G : ST 3 → MatLie m} {x : ST 3} (hG : DifferentiableAt ℝ G x) (i : Fin 4) :
    pd (fun y => cplxL m (G y)) i x = cplxL m (pd G i x) := by
  unfold SobolevOpen.pd
  have h : HasFDerivAt (fun y => cplxL m (G y)) ((cplxL m).comp (fderiv ℝ G x)) x :=
    (cplxL m).hasFDerivAt.comp x hG.hasFDerivAt
  rw [h.fderiv]
  rfl

/-- **Propagation of the Gauss constraint** (`lem:generated-physical-identification`, the Gauss
part of constraint propagation): for theory data with smooth sources satisfying the current
Noether identity, if the actual-jet state field of a smooth tuple solves the independent symmetric
system `eq:generated-extension` on the open slab `(a, b) × 𝕋³` and the Gauss constraint
`e_0{}^νr^A_ν` vanishes at `t₀ ∈ (a, b)`, then it vanishes on `[t₀, t₁] × 𝕋³` for every
`t₁ ∈ (t₀, b)`. -/
theorem gauss_propagation (hN : CurrentNoether SM) (hS : SMSmooth SM) {a t₀ t₁ b : ℝ}
    (ha : a < t₀) (h01 : t₀ < t₁) (hb : t₁ < b) (hsym : ∀ x ∈ openSlab a b, SymEqAt SM z x)
    (h0 : ∀ y : Fin 3 → ℝ, gaussF SM z (Fin.cons t₀ y) = 0) :
    ∀ x ∈ slab t₀ t₁, gaussF SM z x = 0 := by
  have hGs := contDiff_gaussF SM z hS
  have hGd : ∀ x, DifferentiableAt ℝ (gaussF SM z) x := fun x =>
    (hGs.differentiable (by simp)) x
  set w : ST 3 → Fin m × Fin m → ℂ := fun x => cplxL m (gaussF SM z x) with hw
  have hws : ContDiffOn ℝ 1 w (openSlab a b) :=
    ((cplxL m).contDiff.comp (hGs.of_le (by exact_mod_cast le_top))).contDiffOn
  have hwp : IsSPeriodic w := fun k x => by simp only [hw, isSPeriodic_gaussF SM z k x]
  have hc : ∀ μ, ContDiffOn ℝ 1 (w0 z μ) (openSlab a b) := fun μ =>
    ((contDiff_w0 z μ).of_le (by exact_mod_cast le_top)).contDiffOn
  obtain ⟨κ, hκ, hκle⟩ := exists_pos_lower_slab (contDiff_w0 z 0).continuous.continuousOn
    (isSPeriodic_w0 z 0) (w0_zero_pos z) ha hb
  -- bounds for the transport coefficients on the slab
  have hDc : ContinuousOn (fun x => ∑ ν, pd (w0 z ν) ν x) (openSlab a b) :=
    (continuous_finset_sum _ fun ν _ => (contDiff_pd (contDiff_w0 z ν) ν).continuous).continuousOn
  have hDp : IsSPeriodic (fun x => ∑ ν, pd (w0 z ν) ν x) := fun k x => by
    simp only [isSPeriodic_pd (isSPeriodic_w0 z _) _ k x]
  obtain ⟨CD, hCD⟩ := KatoGalerkin.exists_bound_slab hDc hDp ha hb
  have hW : ∀ ν, ∃ C, ∀ x ∈ slab t₀ t₁, ‖w0 z ν x‖ ≤ C := fun ν =>
    KatoGalerkin.exists_bound_slab (contDiff_w0 z ν).continuous.continuousOn
      (isSPeriodic_w0 z ν) ha hb
  choose CW hCW using hW
  have hAb : ∀ ν, ∃ C, ∀ x ∈ slab t₀ t₁, ‖z.A x ν‖ ≤ C := fun ν =>
    KatoGalerkin.exists_bound_slab (Tuple.contDiff_vec z.A_smooth ν).continuous.continuousOn
      (fun k x => by simp only [z.A_per k x]) ha hb
  choose CA hCA using hAb
  obtain ⟨Cb, hCb0, hCb⟩ := exists_lie_bound m
  set K : ℝ := |CD| + ∑ ν, |CW ν| * (Cb * |CA ν|) with hK
  have hK0 : 0 ≤ K := by positivity
  have heq : ∀ x ∈ slab t₀ t₁, ‖∑ μ, w0 z μ x • pd w μ x‖ ≤ K * ‖w x‖ := by
    intro x hx
    have hxo : x ∈ openSlab a b := slab_subset_openSlab ha hb hx
    have e1 : ∑ μ, w0 z μ x • pd w μ x = cplxL m (∑ μ, w0 z μ x • pd (gaussF SM z) μ x) := by
      simp only [hw, pd_cplxL (hGd x), map_sum, map_smul]
    rw [e1, norm_cplxL, gauss_transport' SM z hN hS (isOpen_openSlab a b) hsym hxo]
    have hwx : ‖w x‖ = ‖gaussF SM z x‖ := norm_cplxL _
    rw [hwx]
    set G := gaussF SM z x
    calc ‖-((∑ ν, pd (w0 z ν) ν x) • G) - ∑ ν, w0 z ν x • ⁅z.A x ν, G⁆‖
        ≤ ‖(∑ ν, pd (w0 z ν) ν x) • G‖ + ‖∑ ν, w0 z ν x • ⁅z.A x ν, G⁆‖ := by
          rw [sub_eq_add_neg, ← neg_add]
          rw [norm_neg]
          exact norm_add_le _ _
      _ ≤ |CD| * ‖G‖ + ∑ ν, |CW ν| * (Cb * |CA ν|) * ‖G‖ := by
          gcongr
          · rw [norm_smul]
            exact mul_le_mul_of_nonneg_right ((hCD x hx).trans (le_abs_self _)) (norm_nonneg _)
          · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ν _ => ?_)
            rw [norm_smul]
            have h1 : ‖w0 z ν x‖ ≤ |CW ν| := (hCW ν x hx).trans (le_abs_self _)
            have h2 : ‖⁅z.A x ν, G⁆‖ ≤ Cb * |CA ν| * ‖G‖ :=
              (hCb _ _).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
                ((hCA ν x hx).trans (le_abs_self _)) hCb0) (norm_nonneg _))
            calc ‖w0 z ν x‖ * ‖⁅z.A x ν, G⁆‖ ≤ |CW ν| * (Cb * |CA ν| * ‖G‖) :=
                  mul_le_mul h1 h2 (norm_nonneg _) (abs_nonneg _)
              _ = |CW ν| * (Cb * |CA ν|) * ‖G‖ := by ring
      _ = K * ‖G‖ := by rw [hK, add_mul, Finset.sum_mul]
  have hw0 : ∀ y : Fin 3 → ℝ, w (Fin.cons t₀ y) = 0 := fun y => by
    simp only [hw, h0 y, map_zero]
  have := transport_unique (N := Fin m × Fin m) (c := w0 z) ha h01 hb hws hwp hc
    (isSPeriodic_w0 z) hκ hκle hK0 heq hw0
  intro x hx
  exact cplxL_eq_zero (this x hx)

/-- **Physical identification modulo the harmonic constraint**: for theory data with smooth
sources and the current Noether identity, a smooth tuple whose actual-jet state solves the
independent symmetric system on `(a, b) × 𝕋³`, whose harmonic defect `C(g)` vanishes there and
whose Gauss constraint vanishes at `t₀ ∈ (a, b)` is a physical solution (all Einstein, Yang–Mills,
Higgs and Dirac residuals vanish) on `(t₀, b) × 𝕋³`. -/
theorem physical_of_harmonic (hN : CurrentNoether SM) (hS : SMSmooth SM) {a t₀ b : ℝ}
    (ha : a < t₀) (hsym : ∀ x ∈ openSlab a b, SymEqAt SM z x)
    (hC : ∀ x ∈ openSlab a b, CF z x = 0)
    (h0 : ∀ y : Fin 3 → ℝ, gaussF SM z (Fin.cons t₀ y) = 0) :
    IsPhysicalOn SM z (openSlab t₀ b) := by
  refine (physical_iff_constraints SM z (isOpen_openSlab t₀ b)).2 fun x hx => ?_
  have hxo : x ∈ openSlab a b := ⟨ha.trans hx.1, hx.2⟩
  refine ⟨hsym x hxo, hC x hxo, ?_⟩
  obtain ⟨t₁, ht₁, ht₁b⟩ := exists_between hx.2
  exact gauss_propagation SM z hN hS ha (hx.1.trans ht₁) ht₁b hsym h0 x ⟨hx.1.le, ht₁.le⟩

end Gauss

/-! ### Non-vacuity and consistency with the obstruction -/

section NonVacuity

open CoupledBootstrap.FlatVacuum GenConstraintObs

/-- **Non-vacuity** (flat vacuum): the hypotheses of `physical_of_harmonic` hold for the flat
vacuum with the variational data `trivSMM` on every slab. -/
example : IsPhysicalOn trivSMM flat (openSlab 0 1) :=
  physical_of_harmonic trivSMM flat (currentNoether_of_variational trivSMM_variational)
    trivSMM_smooth (a := -1) (by norm_num)
    (fun x _ => symEqAt_of_physical trivSMM flat isOpen_univ flat_isPhysicalOn trivial)
    (fun x _ => flat_CF x) (fun y => by
      unfold gaussF
      rw [flat_bosF]
      simp)

/-- The obstruction data `badSM` (charge density `J_0 = H`) **violate the current Noether
identity**: along the obstruction tuple `bad` (Minkowski, `A = 0`, `H = t`) the Higgs and Dirac
residuals vanish but `ϱ D^νJ_ν = -ϱ ≠ 0`. -/
theorem not_currentNoether_badSM : CurrentNoether badSM → False := by
  intro hN
  set x : ST 3 := 0
  have hdiv := hN.div_eq bad x
  have hres : ((bosF badSM bad x).2.2, dirF badSM bad x) = 0 := by
    rw [bad_bosF, bad_dirF]
    rfl
  rw [hres, map_zero, smul_zero] at hdiv
  -- compute `divJ` directly
  set c : ℝ := rho bad x with hc
  have hrho : ∀ y, rho bad y = c := fun y => rfl
  have hgi : ∀ y, bad.gi y = minkInv := fun y => ginvOf_minkInv
  have hJ : ∀ y ν, densJ badSM bad y ν = (c * minkInv ν 0) • hgs y := by
    intro y ν
    unfold densJ Jf
    rw [hrho, hgi]
    simp only [badSM, trivSMM]
    rw [Finset.sum_eq_single 0 (fun β _ hβ => by simp [hβ]) (by simp)]
    simp only [if_true, smul_smul]
    rfl
  have hpd : ∀ ν, pd (fun y => densJ badSM bad y ν) ν x =
      (c * minkInv ν 0 * (Pi.single ν (1 : ℝ) : ST 3) 0) • (1 : MatLie 1) := by
    intro ν
    rw [show (fun y => densJ badSM bad y ν) = fun y => (c * minkInv ν 0) • hgs y from
      funext fun y => hJ y ν]
    unfold SobolevOpen.pd
    rw [fderiv_fun_const_smul (contDiff_hgs.differentiable (by simp) x)]
    have := pd_hgs ν x
    unfold SobolevOpen.pd at this
    simp only [ContinuousLinearMap.smul_apply, this, smul_smul]
  have hdivJ : divJ badSM bad x = (c * minkInv 0 0) • (1 : MatLie 1) := by
    unfold divJ
    have hA : ∀ ν, bad.A x ν = 0 := fun ν => rfl
    simp only [hpd, hA, zero_lie, add_zero]
    rw [Finset.sum_eq_single 0 (fun ν _ hν => by simp [Pi.single_apply, hν]) (by simp)]
    simp
  rw [hdivJ] at hdiv
  have hc0 : 0 < c := rho_pos bad x
  have h1 : (1 : MatLie 1) ≠ 0 := by
    intro h
    have h2 : toMat (1 : MatLie 1) 0 0 = 1 := by
      show (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 = 1
      simp
    have h3 : toMat (0 : MatLie 1) 0 0 = 0 := rfl
    rw [h, h3] at h2
    exact zero_ne_one h2
  have : c * minkInv 0 0 ≠ 0 := by
    simp [minkInv, hc0.ne']
  exact (smul_ne_zero this h1) hdiv

end NonVacuity

end RenewalGeometry.GenGauss
