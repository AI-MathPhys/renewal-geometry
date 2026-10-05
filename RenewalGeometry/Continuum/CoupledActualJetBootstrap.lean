/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.ActualJetStateField
import RenewalGeometry.Continuum.QuasilinearDifferenceStability
import RenewalGeometry.Continuum.SliceForcingBound

/-!
# Coupled actual-jet stability and first-exit closure (`prop:coupled-bootstrap`): the state

Einstein–Standard-Model action-closure manuscript, `prop:coupled-bootstrap`
(`eq:actual-jet-gauge-energy`, `eq:actual-jet-integrated-stability`, `eq:bootstrap-state`).

In orthonormal coordinates `eX : ℝ^n ≃ StateP` for the fixed positive block inner product
(`ipState`), the actual-jet state field `u = eX⁻¹𝒰(z)` of a smooth actual field tuple satisfies
`∂_tu = G(u) + 𝓕_err` (`coord_pde`) with the principal matrices `𝒜^j(g)` **symmetric**
(`Aco_symm`, from `princ_symm`) and the forcing `𝓕_err` of `eq:actual-jet-writer`.  The coefficient
maps are smooth on the chart; outside a compact neighbourhood `K'` of the reference's chart margin
they are replaced by smooth symmetric extensions (`cutoff`).

The main result `state_bootstrap` combines
* the first-exit difference stability of quasilinear symmetric systems
  (`QLDiff.difference_bootstrap`: Lipschitz Moser, commutator estimate, symmetric integration by
  parts, Gronwall, first exit),
* the tube property (`H^k ↪ C⁰`: inside the `H^k` tube the approximate state stays in `K'`, where
  the extended coefficients are the true ones), and
* the derivative-counted forcing bound at each time (`SliceForcing.slice_forcing_bound`,
  `lem:actual-jet-complete-forcing`),
into `eq:bootstrap-state` in squared form: there are `δ_*, C_*` (depending only on the chart
margin `K`, the reference bound `R₁`, `T`, `k`) such that for every exact reference `z_*` with
values in `K` and `‖𝒰_*‖_{C_tH^{k+1}} ≤ R₁`, and every smooth actual tuple `ẑ`,
`D² = ‖𝒰̂(0) - 𝒰_*(0)‖²_{H^k} + ‖R_B‖²_{L²H^k} + ‖R_D‖²_{L²H^{k+1}} + ‖C‖²_{L²H^{k+1}} +
‖∂_tC‖²_{L²H^k} ≤ δ_*` implies `‖𝒰̂(t) - 𝒰_*(t)‖²_{H^k} ≤ C_* D²` on `[0, T]`.
No a priori bound on `ẑ` is assumed.
-/

open MeasureTheory Filter Topology Set Metric
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.CoupledBootstrap

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy QLDiff FrameCurvature HarmonicDefect
  ActualJetWriter ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge
  ActualJetBridge ActualJetCompleteForcing ActualJetState

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable (SM : SMData (MatLie m) V S S')

/-! ### Smoothness of the principal operators on the chart -/

theorem contDiffAt_diracP {S₀ : Type*} [NormedAddCommGroup S₀] [NormedSpace ℝ S₀]
    (Fr : TwistedHalfRicci.CliffordFrame (Fin 4) (Module.End ℝ S₀)) (j : Fin 3) (v : S₀)
    {x0 : StateP m V S S'}
    (hN : ContDiffAt ℝ ∞ (fun x : StateP m V S S' => (frameU (ginvOf x.1.1)).N) x0)
    (hβ : ∀ j, ContDiffAt ℝ ∞ (fun x : StateP m V S S' => (frameU (ginvOf x.1.1)).β j) x0)
    (hE : ∀ a j, ContDiffAt ℝ ∞ (fun x : StateP m V S S' => (frameU (ginvOf x.1.1)).E a j) x0) :
    ContDiffAt ℝ ∞ (fun x : StateP m V S S' => diracP (frameU (ginvOf x.1.1)) Fr j v) x0 := by
  show ContDiffAt ℝ ∞ (fun x : StateP m V S S' => -((frameU (ginvOf x.1.1)).β j • v) -
    (frameU (ginvOf x.1.1)).N • ∑ i : Fin 3, (frameU (ginvOf x.1.1)).E i j •
      ((Fr.c 0 * Fr.c i.succ) • v)) x0
  exact ((hβ j).fun_smul contDiffAt_const).neg.sub (hN.fun_smul (ContDiffAt.sum fun i _ =>
    (hE i j).fun_smul contDiffAt_const))

theorem contDiffAt_princL_of (j : Fin 3) (w : StateP m V S S') {x0 : StateP m V S S'}
    (hN : ContDiffAt ℝ ∞ (fun x : StateP m V S S' => (frameU (ginvOf x.1.1)).N) x0)
    (hβ : ∀ j, ContDiffAt ℝ ∞ (fun x : StateP m V S S' => (frameU (ginvOf x.1.1)).β j) x0)
    (hE : ∀ a j, ContDiffAt ℝ ∞ (fun x : StateP m V S S' => (frameU (ginvOf x.1.1)).E a j) x0) :
    ContDiffAt ℝ ∞ (fun x => princL SM x j w) x0 := by
  refine contDiffAt_toP contDiffAt_const ?_ ?_ contDiffAt_const ?_ ?_ contDiffAt_const ?_ ?_
    (contDiffAt_diracP _ _ _ hN hβ hE) ?_ (contDiffAt_diracP _ _ _ hN hβ hE) ?_
  · exact contDiffAt_pi.2 fun μ => contDiffAt_pi.2 fun ν =>
      ((hβ j).mul contDiffAt_const).neg.sub
        (hN.mul (ContDiffAt.sum fun a _ => (hE a j).mul contDiffAt_const))
  · exact contDiffAt_pi.2 fun a => contDiffAt_pi.2 fun μ => contDiffAt_pi.2 fun ν =>
      ((hN.mul (hE a j)).mul contDiffAt_const).neg.sub ((hβ j).mul contDiffAt_const)
  · exact contDiffAt_pi.2 fun a => ((hβ j).fun_smul contDiffAt_const).neg.sub (hN.fun_smul
      (ContDiffAt.sum fun b _ => ContDiffAt.sum fun c _ =>
        contDiffAt_const.fun_smul ((hE b j).fun_smul contDiffAt_const)))
  · exact contDiffAt_pi.2 fun a => ((hβ j).fun_smul contDiffAt_const).neg.add (hN.fun_smul
      (ContDiffAt.sum fun b _ => ContDiffAt.sum fun c _ =>
        contDiffAt_const.fun_smul ((hE b j).fun_smul contDiffAt_const)))
  · exact ((hβ j).fun_smul contDiffAt_const).neg.sub (hN.fun_smul (ContDiffAt.sum fun a _ =>
      (hE a j).fun_smul contDiffAt_const))
  · exact contDiffAt_pi.2 fun a => ((hβ j).fun_smul contDiffAt_const).neg.sub
      (hN.fun_smul ((hE a j).fun_smul contDiffAt_const))
  · exact contDiffAt_pi.2 fun a => contDiffAt_diracP _ _ _ hN hβ hE
  · exact contDiffAt_pi.2 fun a => contDiffAt_diracP _ _ _ hN hβ hE

theorem contDiffAt_princL (j : Fin 3) (w : StateP m V S S') {x0 : StateP m V S S'}
    (hx : MetChart x0.1) : ContDiffAt ℝ ∞ (fun x => princL SM x j w) x0 := by
  have hgi : ContDiffAt ℝ ∞ (fun x : StateP m V S S' => ginvOf x.1.1) x0 :=
    ContDiffAt.ginvOf_fun (by fun_prop) hx.1
  exact contDiffAt_princL_of SM j w (ContDiffAt.frameU_N hgi hx.2)
    (ContDiffAt.frameU_β hgi hx.2) (ContDiffAt.frameU_E hgi hx.2)


/-! ### State coordinates and the coefficient maps -/

section Coords

variable {n : ℕ} (eX : (Fin n → ℝ) ≃L[ℝ] StateP m V S S')

/-- The Lorentzian chart in state coordinates. -/
def chartC : Set (Fin n → ℝ) := {v | MetChart (eX v).1}

theorem isOpen_chartC : IsOpen (chartC eX) :=
  (isOpen_chart (m := m) (V := V) (S := S) (S' := S')).preimage eX.continuous

/-- The `a`-th coordinate functional `x ↦ (eX⁻¹x)_a`. -/
def pZ (a : Fin n) : StateP m V S S' →ₗ[ℝ] ℝ :=
  (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) a).comp eX.symm.toLinearMap

theorem pZ_apply (a : Fin n) (x : StateP m V S S') : pZ eX a x = eX.symm x a := rfl

/-- The lower-order coefficients `𝓕(𝒰)` in coordinates. -/
def Fco (a : Fin n) (v : Fin n → ℝ) : ℝ := pZ eX a (toP (Fsys SM (ofP (eX v))))

/-- The principal matrices `𝒜^j(g)` in coordinates. -/
def Aco (j : Fin 3) (a b : Fin n) (v : Fin n → ℝ) : ℝ :=
  pZ eX a (princL SM (eX v) j (eX (Pi.single b 1)))

theorem contDiffOn_Fco (hS : SMSmooth SM) (a : Fin n) :
    ContDiffOn ℝ ∞ (Fco SM eX a) (chartC eX) := by
  intro v hv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := Fsys_smooth SM hS hv
  have hT : ContDiffAt ℝ ∞ (fun x => toP (Fsys SM (ofP x))) (eX v) :=
    contDiffAt_toP (pi2 h1) (pi2 h2)
      (contDiffAt_pi.2 fun a => contDiffAt_pi.2 fun μ => contDiffAt_pi.2 fun ν => h3 a μ ν)
      (pi1 h4) (pi1 h5) (pi1 h6) h7 h8 (pi1 h9) h10 (pi1 h11) h12 (pi1 h13)
  exact ((LinearMap.toContinuousLinearMap (pZ eX a)).contDiff.contDiffAt.comp v
    (hT.comp v eX.contDiff.contDiffAt)).contDiffWithinAt

theorem contDiffOn_Aco (j : Fin 3) (a b : Fin n) :
    ContDiffOn ℝ ∞ (Aco SM eX j a b) (chartC eX) := by
  intro v hv
  exact ((LinearMap.toContinuousLinearMap (pZ eX a)).contDiff.contDiffAt.comp v
    ((contDiffAt_princL SM j (eX (Pi.single b 1)) hv).comp v
      eX.contDiff.contDiffAt)).contDiffWithinAt

/-- The principal matrices are linear in the increment. -/
theorem pZ_princL (a : Fin n) (j : Fin 3) (v w : Fin n → ℝ) :
    pZ eX a (princL SM (eX v) j (eX w)) = ∑ b, Aco SM eX j a b v * w b := by
  have hw : w = ∑ b, w b • (Pi.single b 1 : Fin n → ℝ) := by
    funext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hw]
  simp only [map_sum, map_smul, smul_eq_mul, Aco]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- **Symmetry of the principal matrices in orthonormal coordinates** (`princ_symm`):
if `eX` is orthonormal for the block inner product, `𝒜^j_{ab} = 𝒜^j_{ba}`. -/
theorem Aco_symm (bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ) (bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ) (bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ)
    (hc0 : ∀ x y, bS (SM.D.Fr.c 0 • x) y = bS x (SM.D.Fr.c 0 • y))
    (hci : ∀ (i : Fin 3) x y, bS (SM.D.Fr.c i.succ • x) y = -bS x (SM.D.Fr.c i.succ • y))
    (hc0b : ∀ x y, bS' (SM.Db.Fr.c 0 • x) y = bS' x (SM.Db.Fr.c 0 • y))
    (hcib : ∀ (i : Fin 3) x y, bS' (SM.Db.Fr.c i.succ • x) y = -bS' x (SM.Db.Fr.c i.succ • y))
    (hX : ∀ v w, ipState bG bV bS bS' (ofP (eX v)) (ofP (eX w)) = ∑ i, v i * w i)
    (j : Fin 3) (a b : Fin n) (v : Fin n → ℝ) : Aco SM eX j a b v = Aco SM eX j b a v := by
  set AF := frameU (ginvOf (eX v).1.1)
  have hcoord : ∀ (u : Fin n → ℝ) (i : Fin n), u i = ∑ l, (Pi.single i 1 : Fin n → ℝ) l * u l := by
    intro u i; simp [Pi.single_apply]
  have key : ∀ i i', Aco SM eX j i i' v = ipState bG bV bS bS' (ofP (eX (Pi.single i 1)))
      (princ AF SM.D.Fr SM.Db.Fr j (ofP (eX (Pi.single i' 1)))) := by
    intro i i'
    have h := hX (Pi.single i 1) (eX.symm (princL SM (eX v) j (eX (Pi.single i' 1))))
    rw [ContinuousLinearEquiv.apply_symm_apply] at h
    rw [Aco, pZ_apply, hcoord (eX.symm (princL SM (eX v) j (eX (Pi.single i' 1)))) i]
    exact h.symm
  have hsym : ∀ W W' : StateP m V S S', ipState bG bV bS bS' (ofP W) (ofP W') =
      ipState bG bV bS bS' (ofP W') (ofP W) := by
    intro W W'
    have e1 := hX (eX.symm W) (eX.symm W')
    have e2 := hX (eX.symm W') (eX.symm W)
    simp only [ContinuousLinearEquiv.apply_symm_apply] at e1 e2
    rw [e1, e2]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [key, key]
  rw [← princ_symm AF SM.D.Fr SM.Db.Fr bG bV bS bS' hc0 hci hc0b hcib j]
  have := hsym (toP (princ AF SM.D.Fr SM.Db.Fr j (ofP (eX (Pi.single a 1)))))
    (eX (Pi.single b 1))
  simpa only [ofP_toP] using this

/-! ### The state field in coordinates and its system -/

variable (z : Tuple m V S S')

/-- The coordinates `u_a = (eX⁻¹𝒰(z))_a` of the actual-jet state field. -/
def uC (a : Fin n) (x : ST 3) : ℝ := eX.symm (stateF SM z x) a

theorem uC_vec (x : ST 3) : (fun a => uC SM eX z a x) = eX.symm (stateF SM z x) := rfl

theorem contDiff_uC (a : Fin n) : ContDiff ℝ ∞ (uC SM eX z a) :=
  (LinearMap.toContinuousLinearMap (pZ eX a)).contDiff.comp (contDiff_stateF SM z)

theorem isSPeriodic_uC (a : Fin n) : IsSPeriodic (uC SM eX z a) := fun k x => by
  simp only [uC, isSPeriodic_stateF SM z k x]

theorem pd_uC (a : Fin n) (δ : Fin 4) (x : ST 3) :
    pd (uC SM eX z a) δ x = eX.symm (pd (stateF SM z) δ x) a := by
  have hL : HasFDerivAt (fun x => pZ eX a (stateF SM z x))
      ((LinearMap.toContinuousLinearMap (pZ eX a)).comp (fderiv ℝ (stateF SM z) x)) x :=
    (LinearMap.toContinuousLinearMap (pZ eX a)).hasFDerivAt.comp x
      (((contDiff_stateF SM z).differentiable (by simp)) x).hasFDerivAt
  unfold SobolevOpen.pd
  show fderiv ℝ (fun x => pZ eX a (stateF SM z x)) x _ = _
  rw [hL.fderiv]
  rfl

theorem pd_stateF_eq (δ : Fin 4) (x : ST 3) :
    pd (stateF SM z) δ x = eX (fun b => pd (uC SM eX z b) δ x) := by
  have : (fun b => pd (uC SM eX z b) δ x) = eX.symm (pd (stateF SM z) δ x) :=
    funext fun b => pd_uC SM eX z b δ x
  rw [this, ContinuousLinearEquiv.apply_symm_apply]

/-- The forcing `𝓕_err` of `eq:actual-jet-writer` in coordinates. -/
def Ferr (a : Fin n) (x : ST 3) : ℝ :=
  pZ eX a (BmL SM (stateF SM z x) (bosF SM z x) + DmL SM (stateF SM z x) (dirF SM z x) +
    ∑ j : Fin 3, QmL SM j (stateF SM z x) (pd (dirF SM z) j.succ x) +
    (GcL (stateF SM z x) (CF z x) + GdL 0 (stateF SM z x) (pd (CF z) 0 x) +
      ∑ j : Fin 3, GdL j.succ (stateF SM z x) (pd (CF z) j.succ x)))

/-- **The actual-jet system in coordinates**: `∂_tu_a = G(u)_a + 𝓕_err,a` at every point, with
`G(u)_a = 𝓕_a(u) - Σ_{j,b}𝒜^j_{ab}(u)∂_ju_b`. -/
theorem coord_pde (a : Fin n) (x : ST 3) :
    pd (uC SM eX z a) 0 x = genG (Aco SM eX) (Fco SM eX) (uC SM eX z) a x + Ferr SM eX z a x := by
  have hw := congrArg (pZ eX a) (writer_pde SM z x)
  have hu : stateF SM z x = eX (fun b => uC SM eX z b x) := by
    rw [uC_vec, ContinuousLinearEquiv.apply_symm_apply]
  simp only [map_add, map_sum] at hw
  have hP : ∀ j : Fin 3, pZ eX a (princL SM (stateF SM z x) j (pd (stateF SM z) j.succ x)) =
      ∑ b, Aco SM eX j a b (fun b => uC SM eX z b x) * pd (uC SM eX z b) j.succ x := by
    intro j
    rw [pd_stateF_eq SM eX z, hu]
    exact pZ_princL SM eX a j _ _
  have hF : pZ eX a (toP (Fsys SM (ofP (stateF SM z x)))) =
      Fco SM eX a (fun b => uC SM eX z b x) := by
    rw [Fco, ← hu]
  simp only [hP, hF] at hw
  have h0 : pZ eX a (pd (stateF SM z) 0 x) = pd (uC SM eX z a) 0 x := (pd_uC SM eX z a 0 x).symm
  rw [h0] at hw
  unfold genG compF Ferr
  simp only [map_add, map_sum]
  linarith

end Coords

/-! ### Cutoff of the coefficients, the reference system and the tube -/

section Tube

variable {n : ℕ} (eX : (Fin n → ℝ) ≃L[ℝ] StateP m V S S')

/-- **Smooth symmetric extensions of the coefficient maps** from a compact chart margin. -/
theorem exists_cutoff (hS : SMSmooth SM)
    (hAsym : ∀ j a b v, Aco SM eX j a b v = Aco SM eX j b a v)
    {K' : Set (Fin n → ℝ)} (hK' : IsCompact K') (hK'O : K' ⊆ chartC eX) :
    ∃ (A' : Fin 3 → Fin n → Fin n → (Fin n → ℝ) → ℝ) (F' : Fin n → (Fin n → ℝ) → ℝ),
      (∀ j a b, ContDiff ℝ ∞ (A' j a b)) ∧ (∀ j a b v, A' j a b v = A' j b a v) ∧
      (∀ a, ContDiff ℝ ∞ (F' a)) ∧ (∀ v ∈ K', ∀ j a b, A' j a b v = Aco SM eX j a b v) ∧
      (∀ v ∈ K', ∀ a, F' a v = Fco SM eX a v) := by
  choose Ac hAc hAcK using fun p : Fin 3 × Fin n × Fin n =>
    SlabMoser.exists_contDiff_eqOn (isOpen_chartC eX) hK' hK'O
      (contDiffOn_Aco SM eX p.1 p.2.1 p.2.2)
  choose Fc hFc hFcK using fun a : Fin n =>
    SlabMoser.exists_contDiff_eqOn (isOpen_chartC eX) hK' hK'O (contDiffOn_Fco SM eX hS a)
  refine ⟨fun j a b v => (Ac (j, a, b) v + Ac (j, b, a) v) / 2, Fc, fun j a b =>
    ((hAc _).add (hAc _)).div_const 2, fun j a b v => by ring, hFc, fun v hv j a b => ?_,
    fun v hv a => hFcK a v hv⟩
  simp only [hAcK _ v hv, hAsym j b a v]
  ring

/-- `G(u)` only depends on the coefficient values at the point. -/
theorem genG_congr {A A' : Fin 3 → Fin n → Fin n → (Fin n → ℝ) → ℝ}
    {F F' : Fin n → (Fin n → ℝ) → ℝ} (u : Fin n → ST 3 → ℝ) (a : Fin n) (x : ST 3)
    (hA : ∀ j a b, A' j a b (fun b => u b x) = A j a b (fun b => u b x))
    (hF : ∀ a, F' a (fun b => u b x) = F a (fun b => u b x)) :
    genG A' F' u a x = genG A F u a x := by
  unfold genG compF
  simp only [hA, hF]

/-- A vector-valued smooth field vanishing on the slab has vanishing partial derivatives there
(in space; in time when `T > 0`). -/
theorem pd_eq_zero_of_slab {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {T : ℝ}
    {F : ST 3 → E} (hF : ContDiff ℝ ∞ F) (h0 : ∀ y : ST 3, y 0 ∈ Icc 0 T → F y = 0) {x : ST 3}
    (hx : x 0 ∈ Icc 0 T) (μ : Fin 4) (hμ : μ ≠ 0 ∨ 0 < T) : pd F μ x = 0 := by
  have hD := hasDerivAt_line0 (hF.differentiable (by simp) x) μ
  by_cases hμ0 : μ = 0
  · subst hμ0
    have hT : 0 < T := hμ.resolve_left (fun h => h rfl)
    set I := Icc (-x 0) (T - x 0)
    have hI : (0 : ℝ) ∈ I := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hu : UniqueDiffWithinAt ℝ I 0 := uniqueDiffOn_Icc (by linarith) 0 hI
    have h2 : HasDerivWithinAt (fun s : ℝ => F (x + s • ev 0)) 0 I 0 := by
      refine (hasDerivWithinAt_const (0 : ℝ) I (0 : E)).congr (fun s hs => ?_) ?_
      · refine h0 _ ?_
        simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, ite_true, smul_eq_mul, mul_one]
        exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
      · simpa using h0 x hx
    exact hu.eq_deriv I hD.hasDerivWithinAt h2
  · have hc : (fun s : ℝ => F (x + s • ev μ)) = fun _ => 0 := funext fun s => h0 _ (by
      simpa [Pi.single_apply, Ne.symm hμ0, hμ0] using hx)
    rw [hc] at hD
    exact hD.unique (hasDerivAt_const 0 0)

variable (z : Tuple m V S S')

/-- **An exact Einstein–Standard-Model solution on the slab**: vanishing physical residuals
(trace-reversed Einstein, Yang–Mills, Higgs, Dirac, dual Dirac) and harmonic coordinates
(`C(g) = 0`) on `[0, T] × 𝕋³`. -/
def ExactOn (T : ℝ) (z : Tuple m V S S') : Prop :=
  ∀ x : ST 3, x 0 ∈ Icc 0 T → bosF SM z x = 0 ∧ dirF SM z x = 0 ∧ CF z x = 0

/-- The forcing of an exact solution vanishes on the slab. -/
theorem Ferr_eq_zero {T : ℝ} (hT : 0 < T) (hz : ExactOn SM T z) (a : Fin n) {x : ST 3}
    (hx : x 0 ∈ Icc 0 T) : Ferr SM eX z a x = 0 := by
  obtain ⟨hB, hD, hC⟩ := hz x hx
  have hD0 : ∀ j : Fin 3, pd (dirF SM z) j.succ x = 0 := fun j =>
    pd_eq_zero_of_slab (contDiff_dirF SM z) (fun y hy => (hz y hy).2.1) hx j.succ
      (Or.inl (Fin.succ_ne_zero j))
  have hC0 : ∀ δ : Fin 4, pd (CF z) δ x = 0 := fun δ =>
    pd_eq_zero_of_slab (contDiff_CF z) (fun y hy => (hz y hy).2.2) hx δ (Or.inr hT)
  simp only [Ferr, hB, hD, hC, hD0, hC0, map_zero, Finset.sum_const_zero, add_zero]

/-- **The reference system**: an exact solution with values in the margin `K'` on the slab
solves `∂_tu = G'(u)` there, with the extended coefficients. -/
theorem ref_pde {A' : Fin 3 → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F' : Fin n → (Fin n → ℝ) → ℝ}
    {K' : Set (Fin n → ℝ)} (hAK : ∀ v ∈ K', ∀ j a b, A' j a b v = Aco SM eX j a b v)
    (hFK : ∀ v ∈ K', ∀ a, F' a v = Fco SM eX a v) {T : ℝ} (hT : 0 < T) (hz : ExactOn SM T z)
    (hzK : ∀ x : ST 3, x 0 ∈ Icc 0 T → (fun b => uC SM eX z b x) ∈ K') (a : Fin n) (x : ST 3)
    (hx : x 0 ∈ Icc 0 T) : pd (uC SM eX z a) 0 x = genG A' F' (uC SM eX z) a x := by
  rw [coord_pde SM eX z a x, Ferr_eq_zero SM eX z hT hz a hx, add_zero]
  exact (genG_congr _ a x (fun j a b => hAK _ (hzK x hx) j a b) (fun a => hFK _ (hzK x hx) a)).symm

/-- **The tube property**: if `‖V(t) - U(t)‖²_{H^k} ≤ ρ = r²/(C_S + 1)` (`C_S` the Sobolev
constant of `H²(𝕋³) ↪ C⁰`), then `|V(t, y) - U(t, y)| ≤ r` pointwise on the slice. -/
theorem tube_dist {k : ℕ} (hk : 2 ≤ k) {CS : ℝ} (hCS : 0 ≤ CS)
    (hsup : ∀ f : ST 3 → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin 3 → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q 2 f t)
    {u v : Fin n → ST 3 → ℝ} (hu : ∀ b, ContDiff ℝ ∞ (u b)) (hv : ∀ b, ContDiff ℝ ∞ (v b))
    (hpu : ∀ b, IsSPeriodic (u b)) (hpv : ∀ b, IsSPeriodic (v b)) {r t : ℝ} (hr : 0 < r)
    (hE : energyQ k (subF v u) t ≤ r ^ 2 / (CS + 1)) (y : Fin 3 → ℝ) :
    dist (fun b => v b (Fin.cons t y)) (fun b => u b (Fin.cons t y)) ≤ r := by
  rw [dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg hr.le).2 fun b => ?_
  have h1 := hsup _ (contDiff_subF hu hv b) (isSPeriodic_subF hpu hpv b) t y
  have h2 : Q 2 (subF v u b) t ≤ energyQ k (subF v u) t :=
    (Q_mono hk _ t).trans (Finset.single_le_sum (f := fun b => Q k (subF v u b) t)
      (fun b _ => Q_nonneg _ _ t) (Finset.mem_univ b))
  have h3 : (v b (Fin.cons t y) - u b (Fin.cons t y)) ^ 2 ≤ r ^ 2 := by
    have hCS1 : 0 < CS + 1 := by linarith
    calc (v b (Fin.cons t y) - u b (Fin.cons t y)) ^ 2 ≤ CS * Q 2 (subF v u b) t := h1
      _ ≤ CS * (r ^ 2 / (CS + 1)) := mul_le_mul_of_nonneg_left (h2.trans hE) hCS
      _ ≤ r ^ 2 := by
          rw [mul_div_assoc', div_le_iff₀ hCS1]
          nlinarith [sq_nonneg r]
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  exact abs_le_of_sq_le_sq' h3 hr.le |> fun h => abs_le.2 h

end Tube

/-! ### The residual fields in coordinates and the forcing bound in the tube -/

section Forcing

variable {n : ℕ} (eX : (Fin n → ℝ) ≃L[ℝ] StateP m V S S')
variable {na nb : ℕ} (eY : (Fin na → ℝ) ≃L[ℝ] BosP m V) (eYD : (Fin nb → ℝ) ≃L[ℝ] S × S')

theorem pd_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : E →L[ℝ] F) {f : ST 3 → E} (hf : ContDiff ℝ ∞ f) (δ : Fin 4)
    (x : ST 3) : pd (fun x => L (f x)) δ x = L (pd f δ x) := by
  unfold SobolevOpen.pd
  have h : HasFDerivAt (fun x => L (f x)) (L.comp (fderiv ℝ f x)) x :=
    L.hasFDerivAt.comp x ((hf.differentiable (by simp)) x).hasFDerivAt
  rw [h.fderiv]
  rfl

/-- The bosonic residual field in coordinates. -/
def RBc (z : Tuple m V S S') (i : Fin na) (x : ST 3) : ℝ := eY.symm (bosF SM z x) i

/-- The Dirac residual field in coordinates. -/
def RDc (z : Tuple m V S S') (i : Fin nb) (x : ST 3) : ℝ := eYD.symm (dirF SM z x) i

/-- The harmonic-defect components `C^l`. -/
def Cc (z : Tuple m V S S') (l : Fin 4) (x : ST 3) : ℝ := CF z x l

/-- Their time derivatives `∂_tC^l`. -/
def dtCc (z : Tuple m V S S') (l : Fin 4) (x : ST 3) : ℝ := pd (CF z) 0 x l

/-- The squared forcing budget `‖R_B‖²_{H^k} + ‖R_D‖²_{H^{k+1}} + ‖C‖²_{H^{k+1}} + ‖∂_tC‖²_{H^k}`
at time `t`. -/
def forcingSq (k : ℕ) (z : Tuple m V S S') (t : ℝ) : ℝ :=
  ∑ i, Q k (RBc SM eY z i) t + ∑ i, Q (k + 1) (RDc SM eYD z i) t + ∑ l, Q (k + 1) (Cc z l) t +
    ∑ l, Q k (dtCc z l) t

variable (z : Tuple m V S S')

theorem contDiff_RBc (hS : SMSmooth SM) (i : Fin na) : ContDiff ℝ ∞ (RBc SM eY z i) :=
  (contDiff_apply ℝ ℝ i).comp (eY.symm.contDiff.comp (contDiff_bosF SM z hS))

theorem contDiff_RDc (i : Fin nb) : ContDiff ℝ ∞ (RDc SM eYD z i) :=
  (contDiff_apply ℝ ℝ i).comp (eYD.symm.contDiff.comp (contDiff_dirF SM z))

theorem contDiff_Cc (l : Fin 4) : ContDiff ℝ ∞ (Cc z l) := contDiff_pi.1 (contDiff_CF z) l

theorem contDiff_dtCc (l : Fin 4) : ContDiff ℝ ∞ (dtCc z l) :=
  contDiff_pi.1 (contDiff_pd (contDiff_CF z) 0) l

theorem isSPeriodic_RBc (i : Fin na) : IsSPeriodic (RBc SM eY z i) := fun k x => by
  simp only [RBc, isSPeriodic_bosF SM z k x]

theorem isSPeriodic_RDc (i : Fin nb) : IsSPeriodic (RDc SM eYD z i) := fun k x => by
  simp only [RDc, isSPeriodic_dirF SM z k x]

theorem isSPeriodic_Cc (l : Fin 4) : IsSPeriodic (Cc z l) := fun k x => by
  simp only [Cc, isSPeriodic_CF z k x]

theorem isSPeriodic_dtCc (l : Fin 4) : IsSPeriodic (dtCc z l) := fun k x => by
  simp only [dtCc, isSPeriodic_pd' (isSPeriodic_CF z) 0 k x]

theorem continuous_forcingSq (hS : SMSmooth SM) (k : ℕ) : Continuous (forcingSq SM eY eYD k z) := by
  unfold forcingSq
  refine ((continuous_finsetSum _ fun i _ => continuous_Q k (contDiff_RBc SM eY z hS i)).add
    (continuous_finsetSum _ fun i _ => continuous_Q _ (contDiff_RDc SM eYD z i))).add
    (continuous_finsetSum _ fun l _ => continuous_Q _ (contDiff_Cc z l)) |>.add
    (continuous_finsetSum _ fun l _ => continuous_Q k (contDiff_dtCc z l))

theorem forcingSq_nonneg (k : ℕ) (t : ℝ) : 0 ≤ forcingSq SM eY eYD k z t := by
  unfold forcingSq
  have h := fun (f : ST 3 → ℝ) (j : ℕ) => Q_nonneg j f t
  exact add_nonneg (add_nonneg (add_nonneg (Finset.sum_nonneg fun i _ => h _ _)
    (Finset.sum_nonneg fun i _ => h _ _)) (Finset.sum_nonneg fun i _ => h _ _))
    (Finset.sum_nonneg fun i _ => h _ _)

/-- The forcing `𝓕_err` in the form of `SliceForcing.slice_forcing_bound`. -/
theorem Ferr_eq_form (c : Fin n) (x : ST 3) :
    Ferr SM eX z c x =
      pZ eX c (BmL SM (eX fun i => uC SM eX z i x) (eY fun i => RBc SM eY z i x)) +
      pZ eX c (DmL SM (eX fun i => uC SM eX z i x) (eYD fun i => RDc SM eYD z i x)) +
      ∑ j : Fin 3, pZ eX c (QmL SM j (eX fun i => uC SM eX z i x)
        (eYD fun i => pd (RDc SM eYD z i) j.succ x)) +
      pZ eX c (GcL (eX fun i => uC SM eX z i x) fun l => Cc z l x) +
      pZ eX c (GdL 0 (eX fun i => uC SM eX z i x) fun l => dtCc z l x) +
      ∑ j : Fin 3, pZ eX c (GdL j.succ (eX fun i => uC SM eX z i x)
        fun l => pd (Cc z l) j.succ x) := by
  have hu : (eX fun i => uC SM eX z i x) = stateF SM z x := by
    rw [uC_vec, ContinuousLinearEquiv.apply_symm_apply]
  have hB : (eY fun i => RBc SM eY z i x) = bosF SM z x := by
    show eY (eY.symm (bosF SM z x)) = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have hD : (eYD fun i => RDc SM eYD z i x) = dirF SM z x := by
    show eYD (eYD.symm (dirF SM z x)) = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have hdD : ∀ j : Fin 3, (eYD fun i => pd (RDc SM eYD z i) j.succ x) =
      pd (dirF SM z) j.succ x := by
    intro j
    have : (fun i => pd (RDc SM eYD z i) j.succ x) = eYD.symm (pd (dirF SM z) j.succ x) := by
      funext i
      have h := pd_clm ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin nb => ℝ) i).comp
        eYD.symm.toContinuousLinearMap) (contDiff_dirF SM z) j.succ x
      exact h
    rw [this, ContinuousLinearEquiv.apply_symm_apply]
  have hC : (fun l => Cc z l x) = CF z x := rfl
  have hdtC : (fun l => dtCc z l x) = pd (CF z) 0 x := rfl
  have hdC : ∀ j : Fin 3, (fun l => pd (Cc z l) j.succ x) = pd (CF z) j.succ x := by
    intro j; funext l
    exact pd_apply ((contDiff_CF z).differentiable (by simp) x) j.succ l
  simp only [hu, hB, hD, hdD, hC, hdtC, hdC, Ferr, map_add, map_sum]
  ring

/-- **The derivative-counted forcing bound inside the tube** (`lem:actual-jet-complete-forcing`
applied at one time): with smooth extensions `A', F'` of the coefficients agreeing with the true
ones on a compact chart margin `K'`, there is `C_M` such that, whenever the state of a smooth
actual tuple takes values in `K'` on the slice at time `t` and `‖𝒰(t)‖²_{H^k} ≤ R²`, the defect
`e = ∂_tu - G'(u)` satisfies `‖e(t)‖²_{H^k} ≤ C_M (‖R_B‖²_{H^k} + ‖R_D‖²_{H^{k+1}} + ‖C‖²_{H^{k+1}}
+ ‖∂_tC‖²_{H^k})(t)`. -/
theorem exists_forcing_const (hS : SMSmooth SM) {k : ℕ} (hk : 4 ≤ k) {K' : Set (Fin n → ℝ)}
    (hK' : IsCompact K') (hK'O : K' ⊆ chartC eX)
    {A' : Fin 3 → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F' : Fin n → (Fin n → ℝ) → ℝ}
    (hA' : ∀ j a b, ContDiff ℝ ∞ (A' j a b)) (hF' : ∀ a, ContDiff ℝ ∞ (F' a))
    (hAK : ∀ v ∈ K', ∀ j a b, A' j a b v = Aco SM eX j a b v)
    (hFK : ∀ v ∈ K', ∀ a, F' a v = Fco SM eX a v) {R : ℝ} (hR : 0 ≤ R) :
    ∃ CM : ℝ, 0 ≤ CM ∧ ∀ (z : Tuple m V S S') (t : ℝ),
      (∀ y : Fin 3 → ℝ, (fun b => uC SM eX z b (Fin.cons t y)) ∈ K') →
      energyQ k (uC SM eX z) t ≤ R ^ 2 →
      energyQ k (fun c x => pd (uC SM eX z c) 0 x - genG A' F' (uC SM eX z) c x) t ≤
        CM * forcingSq SM eY eYD k z t := by
  have hm : ((3 : ℕ) : ℝ) / 2 < (2 : ℕ) := by norm_num
  have hk' : 2 * 2 ≤ k + 1 := by omega
  set O := {x : StateP m V S S' | MetChart x.1} with hOdef
  have hO : IsOpen O := isOpen_chart
  have hKX : IsCompact (eX '' K') := hK'.image eX.continuous
  have hKXO : eX '' K' ⊆ O := by
    rintro _ ⟨v, hv, rfl⟩; exact hK'O hv
  have hsm : ∀ (c : Fin n) {f : StateP m V S S' → StateP m V S S'},
      (∀ x0 ∈ O, ContDiffAt ℝ ∞ f x0) → ContDiffOn ℝ ∞ (fun x => pZ eX c (f x)) O :=
    fun c f hf x0 hx0 => ((LinearMap.toContinuousLinearMap (pZ eX c)).contDiff.contDiffAt.comp x0
      (hf x0 hx0)).contDiffWithinAt
  have hC := fun c : Fin n => SliceForcing.slice_forcing_bound (d := 3) (n := n) hm hk' eX
    eY.toLinearMap eYD.toLinearMap (pZ eX c) hO hKX hKXO (BmL SM) (DmL SM) (fun j => QmL SM j)
    GcL (GdL 0) (fun j => GdL j.succ)
    (fun y => hsm c fun x0 hx0 => contDiffAt_Bsys SM _ hx0)
    (fun y => hsm c fun x0 hx0 => contDiffAt_Bsys SM _ hx0)
    (fun j y => hsm c fun x0 hx0 => contDiffAt_Qsys SM j y hx0)
    (fun y => hsm c fun x0 hx0 => contDiffAt_GcL y hx0)
    (fun y => hsm c fun x0 hx0 => contDiffAt_GdL 0 y hx0)
    (fun j y => hsm c fun x0 hx0 => contDiffAt_GdL j.succ y hx0) hR
  choose CM hCM0 hCM using hC
  refine ⟨∑ c, CM c, Finset.sum_nonneg fun c _ => hCM0 c, fun z t hK hE => ?_⟩
  have hu := contDiff_uC SM eX z
  have hup := isSPeriodic_uC SM eX z
  have hbound : ∀ c, Q k (fun x => pd (uC SM eX z c) 0 x - genG A' F' (uC SM eX z) c x) t ≤
      CM c * forcingSq SM eY eYD k z t := by
    intro c
    refine hCM c (uC SM eX z) hu hup (contDiff_RBc SM eY z hS) (contDiff_RDc SM eYD z)
      (contDiff_Cc z) (contDiff_dtCc z) (isSPeriodic_RBc SM eY z) (isSPeriodic_RDc SM eYD z)
      (isSPeriodic_Cc z) (isSPeriodic_dtCc z) t (fun y => ⟨_, hK y, rfl⟩) hE _
      ((contDiff_pd_top (hu c) 0).sub (contDiff_genG hA' hF' hu c)) fun x hx => ?_
    have hxK : (fun b => uC SM eX z b x) ∈ K' := by
      have := hK (Fin.tail x)
      rwa [← hx, Fin.cons_self_tail] at this
    rw [coord_pde SM eX z c x, genG_congr (uC SM eX z) c x
      (fun j a b => hAK _ hxK j a b) (fun a => hFK _ hxK a), add_sub_cancel_left,
      Ferr_eq_form SM eX eY eYD z c x]
    rfl
  unfold energyQ
  calc ∑ c, Q k (fun x => pd (uC SM eX z c) 0 x - genG A' F' (uC SM eX z) c x) t
      ≤ ∑ c, CM c * forcingSq SM eY eYD k z t := Finset.sum_le_sum fun c _ => hbound c
    _ = (∑ c, CM c) * forcingSq SM eY eYD k z t := by rw [Finset.sum_mul]

end Forcing

/-! ### The state estimate `eq:bootstrap-state` -/

section Main

variable {n : ℕ} (eX : (Fin n → ℝ) ≃L[ℝ] StateP m V S S')
variable {na nb : ℕ} (eY : (Fin na → ℝ) ≃L[ℝ] BosP m V) (eYD : (Fin nb → ℝ) ≃L[ℝ] S × S')

/-- **The squared mismatch** `d²` of `prop:coupled-bootstrap`:
`‖𝒰̂(0) - 𝒰_*(0)‖²_{H^k} + ∫₀ᵀ(‖R_B‖²_{H^k} + ‖R_D‖²_{H^{k+1}} + ‖C‖²_{H^{k+1}} + ‖∂_tC‖²_{H^k})`. -/
def misSq (k : ℕ) (T : ℝ) (zh zs : Tuple m V S S') : ℝ :=
  energyQ k (subF (uC SM eX zh) (uC SM eX zs)) 0 + ∫ t in (0 : ℝ)..T, forcingSq SM eY eYD k zh t

theorem misSq_nonneg (k : ℕ) {T : ℝ} (hT : 0 ≤ T) (zh zs : Tuple m V S S') :
    0 ≤ misSq SM eX eY eYD k T zh zs :=
  add_nonneg (energyQ_nonneg _ _ _)
    (intervalIntegral.integral_nonneg hT fun s _ => forcingSq_nonneg SM eY eYD zh k s)

/-- **The core of `prop:coupled-bootstrap`** (squared form, with the auxiliary objects exported
for the curvature and stress recovery).  Fix `k ≥ 4`, a slab `[0, T] × 𝕋³` (`T > 0`), a compact
chart margin `K` of state values and a reference bound `R₁`, and assume the principal matrices are
symmetric in the coordinates `eX`.  There are a compact neighbourhood `K' ⊇ K` inside the chart,
smooth symmetric extensions `A', F'` of the coefficients agreeing with the true ones on `K'`, and
constants `δ_*, C_*, C_M, R` such that for every exact solution `z_*` with state values in `K` on
the slab and `‖𝒰_*(t)‖²_{H^{k+1}} ≤ R₁²` and every smooth actual tuple `ẑ` with `d² ≤ δ_*`, at
every time `t ∈ [0, T]`: `‖𝒰̂(t) - 𝒰_*(t)‖²_{H^k} ≤ C_* d²`, the state of `ẑ` takes values in
`K'` on the slice, `‖𝒰̂(t)‖²_{H^k} ≤ R²`, and the defect `e = ∂_tû - G'(û)` obeys
`‖e(t)‖²_{H^k} ≤ C_M (forcing budget)(t)`. -/
theorem bootstrap_core (hS : SMSmooth SM)
    (hAsym : ∀ j a b v, Aco SM eX j a b v = Aco SM eX j b a v)
    {k : ℕ} (hk : 4 ≤ k) {T : ℝ} (hT : 0 < T) {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hKO : K ⊆ chartC eX) {R₁ : ℝ} (hR₁ : 0 ≤ R₁) :
    ∃ (K' : Set (Fin n → ℝ)) (A' : Fin 3 → Fin n → Fin n → (Fin n → ℝ) → ℝ)
      (F' : Fin n → (Fin n → ℝ) → ℝ) (δs Cs CM R : ℝ),
      IsCompact K' ∧ K' ⊆ chartC eX ∧ K ⊆ K' ∧ (∀ j a b, ContDiff ℝ ∞ (A' j a b)) ∧
      (∀ a, ContDiff ℝ ∞ (F' a)) ∧ (∀ v ∈ K', ∀ j a b, A' j a b v = Aco SM eX j a b v) ∧
      (∀ v ∈ K', ∀ a, F' a v = Fco SM eX a v) ∧ 0 < δs ∧ 0 ≤ Cs ∧ 0 ≤ CM ∧ 0 ≤ R ∧
      R₁ ^ 2 ≤ R ^ 2 ∧
      ∀ zs zh : Tuple m V S S', ExactOn SM T zs →
      (∀ x : ST 3, x 0 ∈ Icc 0 T → (fun b => uC SM eX zs b x) ∈ K) →
      (∀ t ∈ Icc 0 T, energyQ (k + 1) (uC SM eX zs) t ≤ R₁ ^ 2) →
      misSq SM eX eY eYD k T zh zs ≤ δs →
      ∀ t ∈ Icc 0 T, energyQ k (subF (uC SM eX zh) (uC SM eX zs)) t ≤
          Cs * misSq SM eX eY eYD k T zh zs ∧
        (∀ y : Fin 3 → ℝ, (fun b => uC SM eX zh b (Fin.cons t y)) ∈ K') ∧
        energyQ k (uC SM eX zh) t ≤ R ^ 2 ∧
        energyQ k (fun c x => pd (uC SM eX zh c) 0 x - genG A' F' (uC SM eX zh) c x) t ≤
          CM * forcingSq SM eY eYD k zh t := by
  obtain ⟨r, hr, hrK⟩ := hK.exists_cthickening_subset_open (isOpen_chartC eX) hKO
  set K' := cthickening r K with hK'def
  have hK'c : IsCompact K' :=
    Metric.isCompact_of_isClosed_isBounded isClosed_cthickening hK.isBounded.cthickening
  obtain ⟨A', F', hA', hsym', hF', hAK, hFK⟩ := exists_cutoff SM eX hS hAsym hK'c hrK
  obtain ⟨CS, hCS, hsup⟩ := exists_sup_sq_le (d := 3) (m := 2) (by norm_num)
  set ρ := r ^ 2 / (CS + 1) with hρdef
  have hρ : 0 < ρ := by positivity
  set R := Real.sqrt (2 * ρ + 2 * R₁ ^ 2) with hRdef
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = 2 * ρ + 2 * R₁ ^ 2 := Real.sq_sqrt (by positivity)
  obtain ⟨CM, hCM0, hCM⟩ :=
    exists_forcing_const SM eX eY eYD hS hk hK'c hrK hA' hF' hAK hFK hR
  obtain ⟨Cst, hCst1, hboot⟩ := difference_bootstrap (d := 3) (m := 2) (k := k)
    (by norm_num) (by omega) hA' hsym' hF' (T := T) (R₁ := R₁) (ρ := ρ) hT.le hR₁ hρ
  set M := max 1 CM with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMCM : CM ≤ M := le_max_right _ _
  have hCst0 : 0 ≤ Cst := by linarith
  refine ⟨K', A', F', ρ / (2 * (Cst * M)), Cst * M, CM, R, hK'c, hrK, self_subset_cthickening K,
    hA', hF', hAK, hFK, by positivity, by positivity, hCM0, hR, by rw [hR2]; nlinarith, ?_⟩
  intro zs zh hex hKs hR1s hmis
  have hu := contDiff_uC SM eX zs
  have hv := contDiff_uC SM eX zh
  have hpu := isSPeriodic_uC SM eX zs
  have hpv := isSPeriodic_uC SM eX zh
  set e : Fin n → ST 3 → ℝ := fun c x => pd (uC SM eX zh c) 0 x -
    genG A' F' (uC SM eX zh) c x with hedef
  have he : ∀ c, ContDiff ℝ ∞ (e c) := fun c =>
    (contDiff_pd_top (hv c) 0).sub (contDiff_genG hA' hF' hv c)
  set Φ : ℝ → ℝ := fun s => CM * forcingSq SM eY eYD k zh s with hΦdef
  have hΦc : ContinuousOn Φ (Icc 0 T) :=
    (continuous_const.mul (continuous_forcingSq SM eY eYD zh hS k)).continuousOn
  have hΦ0 : ∀ s ∈ Icc 0 T, 0 ≤ Φ s := fun s _ =>
    mul_nonneg hCM0 (forcingSq_nonneg SM eY eYD zh k s)
  have hUeq : ∀ a, ∀ x : ST 3, x 0 ∈ Icc 0 T →
      pd (uC SM eX zs a) 0 x = genG A' F' (uC SM eX zs) a x := fun a x hx =>
    ref_pde SM eX zs hAK hFK hT hex (fun x hx => self_subset_cthickening K (hKs x hx)) a x hx
  have hVeq : ∀ a, ∀ x : ST 3, x 0 ∈ Icc 0 T →
      pd (uC SM eX zh a) 0 x = genG A' F' (uC SM eX zh) a x + e a x := fun a x _ => by
    simp only [hedef]; ring
  have htube : ∀ s ∈ Icc 0 T, energyQ k (subF (uC SM eX zh) (uC SM eX zs)) s ≤ ρ →
      (∀ y, (fun b => uC SM eX zh b (Fin.cons s y)) ∈ K') ∧
        energyQ k (uC SM eX zh) s ≤ R ^ 2 := by
    intro s hs hEs
    refine ⟨fun y => mem_cthickening_of_dist_le _ _ r K (hKs _ (by simpa using hs))
      (tube_dist (by omega) hCS hsup hu hv hpu hpv hr hEs y), ?_⟩
    have h1 := energyQ_le_sub k hu hv s
    have h2 : energyQ k (uC SM eX zs) s ≤ R₁ ^ 2 :=
      (Finset.sum_le_sum fun b _ => Q_mono (Nat.le_succ k) _ _).trans (hR1s s hs)
    rw [hR2]; linarith
  have hforce : ∀ s ∈ Icc 0 T, energyQ k (subF (uC SM eX zh) (uC SM eX zs)) s ≤ ρ →
      energyQ k e s ≤ Φ s := fun s hs hEs =>
    hCM zh s (htube s hs hEs).1 (htube s hs hEs).2
  have hint : ∫ s in (0 : ℝ)..T, Φ s = CM * ∫ s in (0 : ℝ)..T, forcingSq SM eY eYD k zh s :=
    intervalIntegral.integral_const_mul _ _
  have hI0 : 0 ≤ ∫ s in (0 : ℝ)..T, forcingSq SM eY eYD k zh s :=
    intervalIntegral.integral_nonneg hT.le fun s _ => forcingSq_nonneg SM eY eYD zh k s
  have hE0 := energyQ_nonneg k (subF (uC SM eX zh) (uC SM eX zs)) 0
  have hbudget : energyQ k (subF (uC SM eX zh) (uC SM eX zs)) 0 + ∫ s in (0 : ℝ)..T, Φ s ≤
      M * misSq SM eX eY eYD k T zh zs := by
    rw [hint, misSq]
    nlinarith [mul_le_mul_of_nonneg_right hMCM hI0, mul_le_mul_of_nonneg_right hM1 hE0]
  have hCM' : 0 < Cst * M := by positivity
  have hsmall2 : (Cst * M) * misSq SM eX eY eYD k T zh zs ≤ ρ / 2 := by
    calc (Cst * M) * misSq SM eX eY eYD k T zh zs ≤ (Cst * M) * (ρ / (2 * (Cst * M))) :=
          mul_le_mul_of_nonneg_left hmis hCM'.le
      _ = ρ / 2 := by field_simp
  have hsmall : Cst * (energyQ k (subF (uC SM eX zh) (uC SM eX zs)) 0 +
      ∫ s in (0 : ℝ)..T, Φ s) < ρ := by
    calc Cst * (energyQ k (subF (uC SM eX zh) (uC SM eX zs)) 0 + ∫ s in (0 : ℝ)..T, Φ s)
        ≤ Cst * (M * misSq SM eX eY eYD k T zh zs) := mul_le_mul_of_nonneg_left hbudget hCst0
      _ = (Cst * M) * misSq SM eX eY eYD k T zh zs := by ring
      _ ≤ ρ / 2 := hsmall2
      _ < ρ := by linarith
  have hstate : ∀ t ∈ Icc 0 T, energyQ k (subF (uC SM eX zh) (uC SM eX zs)) t ≤
      Cst * M * misSq SM eX eY eYD k T zh zs := by
    intro t ht
    have h := hboot (uC SM eX zs) (uC SM eX zh) e hu hv he hpu hpv hR1s hUeq hVeq Φ hΦc hΦ0
      hforce hsmall t ht
    calc energyQ k (subF (uC SM eX zh) (uC SM eX zs)) t
        ≤ Cst * (energyQ k (subF (uC SM eX zh) (uC SM eX zs)) 0 + ∫ s in (0 : ℝ)..T, Φ s) := h
      _ ≤ Cst * (M * misSq SM eX eY eYD k T zh zs) := mul_le_mul_of_nonneg_left hbudget hCst0
      _ = Cst * M * misSq SM eX eY eYD k T zh zs := by ring
  intro t ht
  have hEt := hstate t ht
  have hρt : energyQ k (subF (uC SM eX zh) (uC SM eX zs)) t ≤ ρ := by linarith
  exact ⟨hEt, (htube t ht hρt).1, (htube t ht hρt).2, hforce t ht hρt⟩

/-- **`prop:coupled-bootstrap`, state estimate `eq:bootstrap-state`** (squared form).  Fix
`k ≥ 4`, a slab `[0, T] × 𝕋³` (`T > 0`), a compact chart margin `K` of state values (inside the
Lorentzian foliated chart) and a reference bound `R₁`, and assume the principal matrices are
symmetric in the coordinates `eX` (`Aco_symm`: `eX` orthonormal for the block inner product).
There are `δ_*, C_*` such that for every exact solution `z_*` (`ExactOn`: vanishing physical
residuals and harmonic defect on the slab) whose actual-jet state takes values in `K` on the slab
with `‖𝒰_*(t)‖²_{H^{k+1}} ≤ R₁²`, and for every smooth actual field tuple `ẑ` (no bound assumed),
`d² ≤ δ_*` implies `‖𝒰̂(t) - 𝒰_*(t)‖²_{H^k} ≤ C_* d²` for all `t ∈ [0, T]`. -/
theorem state_bootstrap (hS : SMSmooth SM)
    (hAsym : ∀ j a b v, Aco SM eX j a b v = Aco SM eX j b a v)
    {k : ℕ} (hk : 4 ≤ k) {T : ℝ} (hT : 0 < T) {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hKO : K ⊆ chartC eX) {R₁ : ℝ} (hR₁ : 0 ≤ R₁) :
    ∃ δs Cs : ℝ, 0 < δs ∧ 0 ≤ Cs ∧ ∀ zs zh : Tuple m V S S', ExactOn SM T zs →
      (∀ x : ST 3, x 0 ∈ Icc 0 T → (fun b => uC SM eX zs b x) ∈ K) →
      (∀ t ∈ Icc 0 T, energyQ (k + 1) (uC SM eX zs) t ≤ R₁ ^ 2) →
      misSq SM eX eY eYD k T zh zs ≤ δs →
      ∀ t ∈ Icc 0 T, energyQ k (subF (uC SM eX zh) (uC SM eX zs)) t ≤
        Cs * misSq SM eX eY eYD k T zh zs := by
  obtain ⟨K', A', F', δs, Cs, CM, R, -, -, -, -, -, -, -, hδs, hCs, -, -, -, hmain⟩ :=
    bootstrap_core SM eX eY eYD hS hAsym hk hT hK hKO hR₁
  exact ⟨δs, Cs, hδs, hCs, fun zs zh h1 h2 h3 h4 t ht => (hmain zs zh h1 h2 h3 h4 t ht).1⟩

end Main
end RenewalGeometry.CoupledBootstrap
