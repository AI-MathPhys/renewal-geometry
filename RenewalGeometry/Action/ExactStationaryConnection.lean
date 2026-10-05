/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactPhaseCompatibleConnection
import RenewalGeometry.Action.ExactPhaseCompatibleAnalytic
import RenewalGeometry.Analysis.LinkRemainderAnalytic
import RenewalGeometry.Analysis.LocalSumGradient
import RenewalGeometry.Analysis.StationaryContractionAnalytic

/-!
# The stationary connection of the explicit phase-compatible action
  (`eq:supp-exact-connection-remainder`, `eq:supp-exact-stationary-connection`,
  `thm:supp-exact-action-provenance` (ii); emergent-spacetime manuscript)

Connection fields are taken in Lorentz coordinates (`Conn N = Site N → Fin 4 → Fin 6 → ℝ`, sup
norm), so that the stationary row is a field of the same type.

* `rieszInv`: the identification of local covectors with local connection values by the invariant
  pairing (`bdot`), `rieszInv_spec`.
* The link remainder as a lattice sum of local functions (`remLocal`, offsets `offs`):
  `remLocal_loc`, and its splitting into the scaled Ad-link and plaquette remainders
  (`remE_eq_adRem`, `remB_eq_plaqRem`).
* `Nh χ e A`: the `⟨·,·⟩_{b,h}`-gradient `N_h = ∂_A r_h` of the remainder (site-wise gradient of the
  local sum); `statRow`: the full gradient of the phase-compatible Lagrangian (the stationary row
  `γ°_h(e, A)` of `eq:supp-exact-stationary-connection`).
* `statRow_eq` (exact): `γ°_h = f°_h(e) + C(e)A + N_h(e, A)` on the retained branch, and
  `fderiv_phaseLagr_eq` : `D_A L°(A)[δ] = ⟨γ°_h(A), δ⟩_{b,h}`.
* **`norm_Nh_sub_le`** (`eq:supp-exact-connection-remainder`, in the sup norm `p = ∞`): there are
  constants `ε₀, κ` depending only on `Emax` and `χ` (not on `N`) such that for every coframe with
  `‖e(x)‖ ≤ Emax`, every `R` with `hR ≤ ε₀` and `‖A‖, ‖Ã‖ ≤ R`:
  `‖N_h(e, A) - N_h(e, Ã)‖ ≤ κ hR ‖A - Ã‖`; and `N_h(e, 0) = 0`.
* **`stationary_connection_exists_unique`** (clause (ii), existence and uniqueness): if the Cartan
  operator has least singular value `c_* > 0` on the chart (`c_*‖A‖ ≤ ‖C(e)A‖`, the chart's
  defining hypothesis, verified at flat data separately) and `‖f°_h‖ ≤ c_* R/4`, then for `hR`
  below an `N`-independent threshold the stationary row has exactly one zero in the closed
  `R`-ball, and it satisfies `‖A‖ ≤ 2c_*⁻¹‖f°_h‖`.
-/

open Finset NormedSpace Metric

noncomputable section

namespace RenewalGeometry.ExactPhaseAction

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

set_option linter.unusedSectionVars false

open LogBCH LocalSumGradient

/-! ### Generic composition estimates -/

section Generic

variable {E V F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V]
  [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Every linear map out of a finite-dimensional normed space is bounded. -/
theorem exists_linear_bound [FiniteDimensional ℝ E] (P : E →ₗ[ℝ] V) :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖P x‖ ≤ C * ‖x‖ :=
  ⟨‖LinearMap.toContinuousLinearMap P‖, norm_nonneg _,
    fun x => (LinearMap.toContinuousLinearMap P).le_opNorm x⟩

/-- Derivative of `B ∘ ρ ∘ P` for bounded linear `B`, `P`. -/
theorem hasFDerivAt_comp_linear (B : F →ₗ[ℝ] ℝ) (CB : ℝ) (hB : ∀ y, ‖B y‖ ≤ CB * ‖y‖)
    (P : E →ₗ[ℝ] V) (CP : ℝ) (hP : ∀ x, ‖P x‖ ≤ CP * ‖x‖) (ρ : V → F) {w : E}
    (hd : DifferentiableAt ℝ ρ (P w)) :
    HasFDerivAt (fun x => B (ρ (P x)))
      ((B.mkContinuous CB hB).comp ((fderiv ℝ ρ (P w)).comp (P.mkContinuous CP hP))) w := by
  have hP' : HasFDerivAt (fun x => P x) (P.mkContinuous CP hP) w :=
    (P.mkContinuous CP hP).hasFDerivAt
  have h2 := hd.hasFDerivAt.comp w hP'
  exact (B.mkContinuous CB hB).hasFDerivAt.comp w h2

/-- Lipschitz transfer of derivatives through `B ∘ ρ ∘ P`. -/
theorem norm_fderiv_comp_linear_sub_le (B : F →ₗ[ℝ] ℝ) (CB : ℝ) (hCB : 0 ≤ CB)
    (hB : ∀ y, ‖B y‖ ≤ CB * ‖y‖) (P : E →ₗ[ℝ] V) (CP : ℝ) (hCP : 0 ≤ CP)
    (hP : ∀ x, ‖P x‖ ≤ CP * ‖x‖) (ρ : V → F) {R L : ℝ} (hL : 0 ≤ L)
    (hd : ∀ v, ‖v‖ ≤ CP * R → DifferentiableAt ℝ ρ v)
    (hlip : ∀ v v', ‖v‖ ≤ CP * R → ‖v'‖ ≤ CP * R → ‖fderiv ℝ ρ v - fderiv ℝ ρ v'‖ ≤ L * ‖v - v'‖)
    {w w' : E} (hw : ‖w‖ ≤ R) (hw' : ‖w'‖ ≤ R) :
    ‖fderiv ℝ (fun x => B (ρ (P x))) w - fderiv ℝ (fun x => B (ρ (P x))) w'‖ ≤
      CB * L * CP * CP * ‖w - w'‖ := by
  have hPw : ‖P w‖ ≤ CP * R := (hP w).trans (by gcongr)
  have hPw' : ‖P w'‖ ≤ CP * R := (hP w').trans (by gcongr)
  rw [(hasFDerivAt_comp_linear B CB hB P CP hP ρ (hd _ hPw)).fderiv,
    (hasFDerivAt_comp_linear B CB hB P CP hP ρ (hd _ hPw')).fderiv,
    ← ContinuousLinearMap.comp_sub, ← ContinuousLinearMap.sub_comp]
  have hBn : ‖B.mkContinuous CB hB‖ ≤ CB := LinearMap.mkContinuous_norm_le _ hCB _
  have hPn : ‖P.mkContinuous CP hP‖ ≤ CP := LinearMap.mkContinuous_norm_le _ hCP _
  have hdiff : ‖P w - P w'‖ ≤ CP * ‖w - w'‖ := by rw [← map_sub]; exact hP _
  calc _ ≤ ‖B.mkContinuous CB hB‖ * (‖fderiv ℝ ρ (P w) - fderiv ℝ ρ (P w')‖ *
          ‖P.mkContinuous CP hP‖) := by
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        gcongr
        exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ CB * ((L * (CP * ‖w - w'‖)) * CP) := by
        have h1 : ‖fderiv ℝ ρ (P w) - fderiv ℝ ρ (P w')‖ ≤ L * (CP * ‖w - w'‖) :=
          (hlip _ _ hPw hPw').trans (by gcongr)
        gcongr
    _ = CB * L * CP * CP * ‖w - w'‖ := by ring

end Generic

/-! ### Norm bounds for the coefficient arrays -/

open PalatiniEinsteinAlgebra

theorem norm_le_sum_abs (X : M4) : ‖X‖ ≤ ∑ i, ∑ j, |X i j| := by
  rw [Matrix.linfty_opNorm_def]
  have : ((Finset.univ.sup fun i => ∑ j, ‖X i j‖₊ : NNReal) : ℝ) ≤
      ((∑ i, ∑ j, ‖X i j‖₊ : NNReal) : ℝ) := by
    exact_mod_cast Finset.sup_le fun i _ =>
      Finset.single_le_sum (f := fun i => ∑ j, ‖X i j‖₊) (fun _ _ => by positivity)
        (Finset.mem_univ i)
  refine this.trans (le_of_eq ?_)
  push_cast
  simp [Real.norm_eq_abs]

set_option maxRecDepth 100000 in
theorem abs_eps4_le : ∀ a b c d : Fin 4, |eps4 a b c d| ≤ 1 := by decide

theorem abs_epsR_le (a b c d : Fin 4) : |epsR a b c d| ≤ 1 := by
  have := abs_eps4_le a b c d
  rw [epsR, ← Int.cast_abs]
  exact_mod_cast this

theorem abs_palCoeff_le (e : M4) (ρ σ K L : Fin 4) : |palCoeff e ρ σ K L| ≤ 128 * ‖e‖ ^ 2 := by
  simp only [palCoeff, Matrix.of_apply]
  have hterm : ∀ μ ν I J : Fin 4, |epsR μ ν ρ σ * (epsR I J K L * e I μ * e J ν)| ≤ ‖e‖ ^ 2 := by
    intro μ ν I J
    simp only [abs_mul]
    have h1 := abs_epsR_le μ ν ρ σ
    have h2 := abs_epsR_le I J K L
    have h3 := norm_entry_le e I μ
    have h4 := norm_entry_le e J ν
    calc |epsR μ ν ρ σ| * (|epsR I J K L| * |e I μ| * |e J ν|) ≤ 1 * (1 * ‖e‖ * ‖e‖) := by
          gcongr
      _ = ‖e‖ ^ 2 := by ring
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc (1 / 2 : ℝ) * |∑ μ, ∑ ν, epsR μ ν ρ σ * ∑ I, ∑ J, epsR I J K L * e I μ * e J ν|
      ≤ (1 / 2) * ∑ μ : Fin 4, ∑ ν : Fin 4, ∑ I : Fin 4, ∑ J : Fin 4, ‖e‖ ^ 2 := by
        gcongr
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun μ _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ν _ => ?_)
        rw [Finset.mul_sum]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun I _ => ?_)
        rw [Finset.mul_sum]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun J _ => ?_)
        exact hterm μ ν I J
    _ ≤ 128 * ‖e‖ ^ 2 := by simp; nlinarith [sq_nonneg ‖e‖]

theorem abs_eta_entry (a b : Fin 4) : |eta a b| ≤ 1 := by
  fin_cases a <;> fin_cases b <;> simp [eta, minkowski, Matrix.diagonal]

theorem norm_dualCoeff_palCoeff_le (e : M4) (ρ σ : Fin 4) :
    ‖dualCoeff (palCoeff e ρ σ)‖ ≤ 8192 * ‖e‖ ^ 2 := by
  refine (norm_le_sum_abs _).trans ?_
  have hentry : ∀ a b, |dualCoeff (palCoeff e ρ σ) a b| ≤ 512 * ‖e‖ ^ 2 := by
    intro a b
    simp only [dualCoeff, Matrix.mul_apply, Matrix.transpose_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ c : Fin 4, |eta a c * palCoeff e ρ σ b c| ≤ ∑ _c : Fin 4, 128 * ‖e‖ ^ 2 := by
          refine Finset.sum_le_sum fun c _ => ?_
          rw [abs_mul]
          calc |eta a c| * |palCoeff e ρ σ b c| ≤ 1 * (128 * ‖e‖ ^ 2) := by
                gcongr
                · exact abs_eta_entry a c
                · exact abs_palCoeff_le e ρ σ b c
            _ = 128 * ‖e‖ ^ 2 := one_mul _
      _ = 512 * ‖e‖ ^ 2 := by simp; ring
  calc ∑ a, ∑ b, |dualCoeff (palCoeff e ρ σ) a b| ≤ ∑ _a : Fin 4, ∑ _b : Fin 4, 512 * ‖e‖ ^ 2 :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hentry a b
    _ = 8192 * ‖e‖ ^ 2 := by simp; ring

/-- `‖Π_i(e)‖ ≤ 8192 |χ| ‖e‖²`. -/
theorem norm_piArr_le (χ : ℝ) (e : M4) (i : Fin 3) : ‖piArr χ e i‖ ≤ 8192 * |χ| * ‖e‖ ^ 2 := by
  rw [piArr, norm_smul, Real.norm_eq_abs, mul_comm 8192, mul_assoc]
  gcongr
  exact norm_dualCoeff_palCoeff_le e _ _

/-- `‖Σ_ij(e)‖ ≤ 8192 |χ| ‖e‖²`. -/
theorem norm_sigmaArr_le (χ : ℝ) (e : M4) (i j : Fin 3) :
    ‖sigmaArr χ e i j‖ ≤ 8192 * |χ| * ‖e‖ ^ 2 := by
  rw [sigmaArr, norm_smul, Real.norm_eq_abs, mul_comm 8192, mul_assoc]
  gcongr
  exact norm_dualCoeff_palCoeff_le e _ _

/-! ### The invariant pairing on local connection values and its Riesz map -/

/-- Local connection values at one site (`μ`, Lorentz coordinate `k`). -/
abbrev LocVal := Fin 4 → Fin 6 → ℝ

theorem abs_gram_le (k : Fin 6) : |gram k| ≤ 2 := by fin_cases k <;> norm_num [gram]

theorem abs_bdot_le (u v : LocVal) : |bdot u v| ≤ 48 * (‖u‖ * ‖v‖) := by
  unfold bdot
  have hterm : ∀ μ k, |gram k * u μ k * v μ k| ≤ 2 * (‖u‖ * ‖v‖) := by
    intro μ k
    rw [abs_mul, abs_mul]
    have hu : |u μ k| ≤ ‖u‖ := by
      have := (norm_le_pi_norm (u μ) k).trans (norm_le_pi_norm u μ)
      rwa [Real.norm_eq_abs] at this
    have hv : |v μ k| ≤ ‖v‖ := by
      have := (norm_le_pi_norm (v μ) k).trans (norm_le_pi_norm v μ)
      rwa [Real.norm_eq_abs] at this
    calc |gram k| * |u μ k| * |v μ k| ≤ 2 * ‖u‖ * ‖v‖ := by
          gcongr
          exact abs_gram_le k
      _ = 2 * (‖u‖ * ‖v‖) := by ring
  calc |∑ μ, ∑ k, gram k * u μ k * v μ k| ≤ ∑ _μ : Fin 4, ∑ _k : Fin 6, 2 * (‖u‖ * ‖v‖) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun μ _ => ?_)
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => hterm μ k)
    _ = 48 * (‖u‖ * ‖v‖) := by simp; ring

theorem bdot_add_left (u u' v : LocVal) : bdot (u + u') v = bdot u v + bdot u' v := by
  simp only [bdot, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem bdot_add_right (u v v' : LocVal) : bdot u (v + v') = bdot u v + bdot u v' := by
  simp only [bdot, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem bdot_smul_left (c : ℝ) (u v : LocVal) : bdot (c • u) v = c * bdot u v := by
  simp only [bdot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem bdot_smul_right (c : ℝ) (u v : LocVal) : bdot u (c • v) = c * bdot u v := by
  simp only [bdot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- `bdot` as a bilinear map. -/
def bdotLin : LocVal →ₗ[ℝ] LocVal →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ bdot bdot_add_left bdot_smul_left bdot_add_right bdot_smul_right

/-- `bdot` as a continuous bilinear map. -/
def bdotCLM : LocVal →L[ℝ] LocVal →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂ bdotLin 48 fun u v => by
    rw [Real.norm_eq_abs, mul_assoc]; exact abs_bdot_le u v

@[simp] theorem bdotCLM_apply (u v : LocVal) : bdotCLM u v = bdot u v := rfl

/-- The unit local value `e_{μk}`. -/
def unitLoc (μ : Fin 4) (k : Fin 6) : LocVal := Pi.single μ (Pi.single k 1)

theorem norm_unitLoc (μ : Fin 4) (k : Fin 6) : ‖unitLoc μ k‖ = 1 := by
  simp [unitLoc, Pi.norm_single]

/-- The Riesz map of the invariant pairing on local values:
`(rieszInv ℓ)_{μk} = ℓ(e_{μk}) / g_k`. -/
def rieszInvLin : (LocVal →L[ℝ] ℝ) →ₗ[ℝ] LocVal where
  toFun ℓ := fun μ k => ℓ (unitLoc μ k) / gram k
  map_add' ℓ ℓ' := by funext μ k; simp [add_div]
  map_smul' c ℓ := by funext μ k; simp [mul_div_assoc]

theorem norm_rieszInvLin_le (ℓ : LocVal →L[ℝ] ℝ) : ‖rieszInvLin ℓ‖ ≤ (1 / 2) * ‖ℓ‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun μ => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
  simp only [rieszInvLin, LinearMap.coe_mk, AddHom.coe_mk, Real.norm_eq_abs, abs_div]
  have h1 : |ℓ (unitLoc μ k)| ≤ ‖ℓ‖ := by
    have := ℓ.le_opNorm (unitLoc μ k)
    rwa [norm_unitLoc, mul_one, Real.norm_eq_abs] at this
  have h2 : |gram k| = 2 := by fin_cases k <;> norm_num [gram]
  rw [h2]
  linarith

/-- The Riesz map as a continuous linear map, `‖rieszInv‖ ≤ 1/2`. -/
def rieszInv : (LocVal →L[ℝ] ℝ) →L[ℝ] LocVal :=
  LinearMap.mkContinuous rieszInvLin (1 / 2) norm_rieszInvLin_le

theorem norm_rieszInv_le : ‖rieszInv‖ ≤ 1 / 2 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

theorem eq_sum_unitLoc (v : LocVal) : v = ∑ μ, ∑ k, v μ k • unitLoc μ k := by
  funext μ' k'
  simp only [Finset.sum_apply, Pi.smul_apply, unitLoc, smul_eq_mul]
  rw [Finset.sum_eq_single μ']
  · rw [Finset.sum_eq_single k']
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  · intro b _ hb; simp [Pi.single_apply, Ne.symm hb]
  · simp

/-- **Riesz property**: `bdot (rieszInv ℓ) v = ℓ v`. -/
theorem rieszInv_spec (ℓ : LocVal →L[ℝ] ℝ) (v : LocVal) : bdotCLM (rieszInv ℓ) v = ℓ v := by
  conv_rhs => rw [eq_sum_unitLoc v]
  simp only [bdotCLM_apply, bdot, rieszInv, LinearMap.mkContinuous_apply, rieszInvLin,
    LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun k _ => ?_
  rw [mul_div_cancel₀ _ (gram_ne_zero k)]
  ring

/-! ### The link remainder as a lattice sum of local functions -/

variable {N : ℕ} [NeZero N]

/-- The offsets `(0, e_1, e_2, e_3)` of the local configuration of the link remainder. -/
def offs : Fin 4 → Site N := Fin.cases 0 fun i => unitVec i

@[simp] theorem offs_zero : (offs 0 : Site N) = 0 := rfl

@[simp] theorem offs_succ (i : Fin 3) : (offs i.succ : Site N) = unitVec i := rfl

/-- The local link remainder `r_h` at a site, as a function of the local configuration
`w ℓ = A(x + offs ℓ)`. -/
def remLocal (χ h : ℝ) (e : Site N → M4) (x : Site N) (w : Fin 4 → LocVal) : ℝ :=
  -(∑ i, pairing (piArr χ (e x) i) (remE h (iota (w 0 i.succ)) (iota (w i.succ 0)))) +
    sumLt fun i j => pairing (sigmaArr χ (e x) i j)
      (remB h (iota (w 0 i.succ)) (iota (w i.succ j.succ)) (iota (w j.succ i.succ))
        (iota (w 0 j.succ)))

theorem remLocal_loc (χ h : ℝ) (e : Site N → M4) (A : Conn N) (x : Site N) :
    remLocal χ h e x (loc offs x A) = remDensity χ h e (toA0 A) (toA A) x := by
  simp [remLocal, remDensity, loc_apply, toA0, toA]

/-- The remainder Lagrangian is `h³` times a lattice sum of local functions. -/
theorem gridPair_remDensity (χ h : ℝ) (e : Site N → M4) (A : Conn N) :
    gridPair h (remDensity χ h e (toA0 A) (toA A)) =
      h ^ 3 * localSum offs (fun x => remLocal χ h e x) A := by
  simp [gridPair, localSum, remLocal_loc]

/-- `ι` as a linear map. -/
def iotaLin : (Fin 6 → ℝ) →ₗ[ℝ] M4 where
  toFun := iota
  map_add' := iota_add
  map_smul' := iota_smul

/-- The Ad-link local projection `w ↦ (A_i(x), A₀(x + e_i))`. -/
def projE (i : Fin 3) : (Fin 4 → LocVal) →ₗ[ℝ] M4 × M4 where
  toFun w := (iota (w 0 i.succ), iota (w i.succ 0))
  map_add' w w' := by simp [iota_add]
  map_smul' c w := by simp [iota_smul]

/-- The plaquette local projection `w ↦ (A_i(x), A_j(x+e_i), -A_i(x+e_j), -A_j(x))`. -/
def projB (i j : Fin 3) : (Fin 4 → LocVal) →ₗ[ℝ] (Fin 4 → M4) where
  toFun w := ![iota (w 0 i.succ), iota (w i.succ j.succ), -iota (w j.succ i.succ),
    -iota (w 0 j.succ)]
  map_add' w w' := by
    funext ℓ; fin_cases ℓ <;> simp [iota_add] <;> abel
  map_smul' c w := by
    funext ℓ; fin_cases ℓ <;> simp [iota_smul]

/-- The scaled Ad-link remainder `ρ^E_h(p) = h⁻² adRem(h p)`. -/
def rhoE (h : ℝ) (p : M4 × M4) : M4 := (h ^ 2)⁻¹ • LinkRemainder.adRem (h • p)

/-- The scaled plaquette remainder `ρ^B_h(Y) = h⁻² plaqRem(h Y)`. -/
def rhoB (h : ℝ) (Y : Fin 4 → M4) : M4 := (h ^ 2)⁻¹ • LinkRemainder.plaqRem (h • Y)

theorem remE_eq_rhoE {h : ℝ} (hh : h ≠ 0) (a b : M4) : remE h a b = rhoE h (a, b) := by
  unfold rhoE remE bracket
  rw [Prod.smul_mk, LinkRemainder.smul_adRem_smul hh]
  rfl

theorem remB_eq_rhoB {h : ℝ} (hh : h ≠ 0) (ai ajs ais aj : M4) :
    remB h ai ajs ais aj = rhoB h ![ai, ajs, -ais, -aj] := by
  unfold rhoB remB plaquette plaqList plaqX
  rw [LinkRemainder.smul_plaqRem_smul hh]
  simp [smul_neg, sub_eq_add_neg, add_assoc]

/-- The pairing with a fixed matrix, as a linear functional. -/
def pairingLeft (c : M4) : M4 →ₗ[ℝ] ℝ := pairingBilin c

theorem norm_pairingLeft_le (c y : M4) : ‖pairingLeft c y‖ ≤ (4 * ‖c‖) * ‖y‖ := by
  rw [Real.norm_eq_abs, mul_assoc]; exact abs_pairing_le c y

/-- The six local terms of the remainder: three Ad-link terms and three plaquette terms. -/
def remTerm (χ h : ℝ) (e : Site N → M4) (x : Site N) : Fin 6 → (Fin 4 → LocVal) → ℝ :=
  ![fun w => pairingLeft (-piArr χ (e x) 0) (rhoE h (projE 0 w)),
    fun w => pairingLeft (-piArr χ (e x) 1) (rhoE h (projE 1 w)),
    fun w => pairingLeft (-piArr χ (e x) 2) (rhoE h (projE 2 w)),
    fun w => pairingLeft (sigmaArr χ (e x) 0 1) (rhoB h (projB 0 1 w)),
    fun w => pairingLeft (sigmaArr χ (e x) 0 2) (rhoB h (projB 0 2 w)),
    fun w => pairingLeft (sigmaArr χ (e x) 1 2) (rhoB h (projB 1 2 w))]

theorem remLocal_eq_sum {h : ℝ} (hh : h ≠ 0) (χ : ℝ) (e : Site N → M4) (x : Site N)
    (w : Fin 4 → LocVal) :
    remLocal χ h e x w = ∑ t, remTerm χ h e x t w := by
  simp only [remLocal, remTerm, Fin.sum_univ_six, sumLt_eq, Fin.sum_univ_three,
    remE_eq_rhoE hh, remB_eq_rhoB hh, pairingLeft, pairingBilin_apply, pairing_neg_left]
  simp [projE, projB, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-! ### Cutoff-uniform Lipschitz bound for the local remainder -/

theorem norm_fderiv_finsum_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (F : Fin n → E → ℝ) (L : Fin n → ℝ) {w w' : E} (hd : ∀ t, DifferentiableAt ℝ (F t) w)
    (hd' : ∀ t, DifferentiableAt ℝ (F t) w')
    (hlip : ∀ t, ‖fderiv ℝ (F t) w - fderiv ℝ (F t) w'‖ ≤ L t * ‖w - w'‖) :
    ‖fderiv ℝ (fun v => ∑ t, F t v) w - fderiv ℝ (fun v => ∑ t, F t v) w'‖ ≤
      (∑ t, L t) * ‖w - w'‖ := by
  rw [(HasFDerivAt.fun_sum fun t _ => (hd t).hasFDerivAt).fderiv,
    (HasFDerivAt.fun_sum fun t _ => (hd' t).hasFDerivAt).fderiv, ← Finset.sum_sub_distrib,
    Finset.sum_mul]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => hlip t)

theorem exists_iota_bound : ∃ C, 1 ≤ C ∧ ∀ c, ‖iota c‖ ≤ C * ‖c‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_linear_bound iotaLin
  refine ⟨max C 1, le_max_right _ _, fun c => (hC c).trans ?_⟩
  gcongr; exact le_max_left _ _

theorem norm_locVal_entry_le (w : Fin 4 → LocVal) (μ ν : Fin 4) : ‖w μ ν‖ ≤ ‖w‖ :=
  (norm_le_pi_norm (w μ) ν).trans (norm_le_pi_norm w μ)

theorem norm_projE_le {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ c, ‖iota c‖ ≤ C * ‖c‖) (i : Fin 3)
    (w : Fin 4 → LocVal) : ‖projE i w‖ ≤ C * ‖w‖ := by
  simp only [projE, LinearMap.coe_mk, AddHom.coe_mk, Prod.norm_def]
  refine max_le ((hC _).trans ?_) ((hC _).trans ?_) <;>
    exact mul_le_mul_of_nonneg_left (norm_locVal_entry_le w _ _) hC0

theorem norm_projB_le {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ c, ‖iota c‖ ≤ C * ‖c‖) (i j : Fin 3)
    (w : Fin 4 → LocVal) : ‖projB i j w‖ ≤ C * ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun ℓ => ?_
  have hb : ∀ μ ν, ‖iota (w μ ν)‖ ≤ C * ‖w‖ := fun μ ν =>
    (hC _).trans (mul_le_mul_of_nonneg_left (norm_locVal_entry_le w _ _) hC0)
  fin_cases ℓ <;> simp [projB, norm_neg, hb]

theorem differentiableAt_rhoE (h : ℝ) (p : M4 × M4) : DifferentiableAt ℝ (rhoE h) p := by
  unfold rhoE
  exact ((LinkRemainder.differentiable_adRem (𝔸 := M4) _).comp p
    ((differentiableAt_id).const_smul h)).const_smul ((h ^ 2)⁻¹ : ℝ)

theorem differentiableAt_rhoB {h : ℝ} {Y : Fin 4 → M4} (hY : ‖h • Y‖ < 1 / 16) :
    DifferentiableAt ℝ (rhoB h) Y := by
  unfold rhoB
  have hd : DifferentiableAt ℝ (LinkRemainder.plaqRem (𝔸 := M4)) (h • Y) :=
    (LinkRemainder.differentiableOn_plaqRem (𝔸 := M4) _ (mem_ball_zero_iff.2 hY)).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hY))
  exact (hd.comp Y ((differentiableAt_id).const_smul h)).const_smul ((h ^ 2)⁻¹ : ℝ)

/-- **Cutoff-uniform Lipschitz bound for the local link remainder**
(`eq:supp-exact-connection-remainder`, local form): there are `ε₀ > 0`, `κ ≥ 0` (absolute
constants) such that for every regulator, every coframe value with `‖e(x)‖ ≤ E_max`, every
`h > 0`, `R ≥ 0` with `hR ≤ ε₀`, the local remainder `r_h` at `x` is differentiable on the
`R`-ball of local configurations and its derivative is Lipschitz there with constant
`κ |χ| E_max² · hR`. -/
theorem exists_remLocal_lipschitz :
    ∃ ε₀ > 0, ∃ κ, 0 ≤ κ ∧ ∀ (N : ℕ) [NeZero N] (χ Emax h R : ℝ) (e : Site N → M4) (x : Site N),
      0 < h → 0 ≤ R → h * R ≤ ε₀ → ‖e x‖ ≤ Emax →
      (∀ w : Fin 4 → LocVal, ‖w‖ ≤ R → DifferentiableAt ℝ (remLocal χ h e x) w) ∧
      ∀ w w' : Fin 4 → LocVal, ‖w‖ ≤ R → ‖w'‖ ≤ R →
        ‖fderiv ℝ (remLocal χ h e x) w - fderiv ℝ (remLocal χ h e x) w'‖ ≤
          κ * (|χ| * Emax ^ 2) * (h * R) * ‖w - w'‖ := by
  obtain ⟨C, hC1, hC⟩ := exists_iota_bound
  obtain ⟨rE, hrE, hltE, KE, hKE, hLipE, -⟩ :=
    LinkRemainder.exists_adRem_fderiv_lipschitz (𝔸 := M4)
  obtain ⟨rB, hrB, hltB, KB, hKB, hLipB, -⟩ :=
    LinkRemainder.exists_plaqRem_fderiv_lipschitz (𝔸 := M4)
  have hC0 : 0 ≤ C := by linarith
  have hCpos : 0 < C := by linarith
  refine ⟨min rE rB / C, by positivity, 6 * (4 * 8192) * (KE + KB) * C ^ 3, by positivity, ?_⟩
  intro N _ χ Emax h R e x hh hR hhR heE
  have hCR : h * (C * R) ≤ min rE rB := by
    have h1 : h * R * C ≤ min rE rB := (le_div_iff₀ hCpos).1 hhR
    calc h * (C * R) = h * R * C := by ring
      _ ≤ min rE rB := h1
  have hrE' : h * (C * R) ≤ rE := hCR.trans (min_le_left _ _)
  have hrB' : h * (C * R) ≤ rB := hCR.trans (min_le_right _ _)
  have hCR0 : 0 ≤ C * R := by positivity
  have hE0 : 0 ≤ Emax := (norm_nonneg _).trans heE
  have hEsq : ‖e x‖ ^ 2 ≤ Emax ^ 2 := pow_le_pow_left₀ (norm_nonneg _) heE 2
  set P := 8192 * |χ| * Emax ^ 2 with hPdef
  have hP0 : 0 ≤ P := by positivity
  have hPi : ∀ i, ‖-piArr χ (e x) i‖ ≤ P := fun i => by
    rw [norm_neg]; exact (norm_piArr_le χ (e x) i).trans (by rw [hPdef]; gcongr)
  have hSi : ∀ i j, ‖sigmaArr χ (e x) i j‖ ≤ P := fun i j =>
    (norm_sigmaArr_le χ (e x) i j).trans (by rw [hPdef]; gcongr)
  -- the two scaled remainders
  have hdE : ∀ v : M4 × M4, ‖v‖ ≤ C * R → DifferentiableAt ℝ (rhoE h) v :=
    fun v _ => differentiableAt_rhoE h v
  have hdB : ∀ v : Fin 4 → M4, ‖v‖ ≤ C * R → DifferentiableAt ℝ (rhoB h) v := by
    intro v hv
    refine differentiableAt_rhoB ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    calc h * ‖v‖ ≤ h * (C * R) := by gcongr
      _ ≤ rB := hrB'
      _ < 1 / 16 := hltB
  set Lt := 4 * P * (KE + KB) * (h * (C * R)) * C * C with hLt
  -- per-term estimates
  have termE : ∀ (c : M4) (i : Fin 3), ‖c‖ ≤ P →
      (∀ w : Fin 4 → LocVal, ‖w‖ ≤ R →
        DifferentiableAt ℝ (fun w => pairingLeft c (rhoE h (projE i w))) w) ∧
      ∀ w w' : Fin 4 → LocVal, ‖w‖ ≤ R → ‖w'‖ ≤ R →
        ‖fderiv ℝ (fun w => pairingLeft c (rhoE h (projE i w))) w -
          fderiv ℝ (fun w => pairingLeft c (rhoE h (projE i w))) w'‖ ≤ Lt * ‖w - w'‖ := by
    intro c i hc
    refine ⟨fun w hw => (hasFDerivAt_comp_linear (pairingLeft c) (4 * ‖c‖)
      (norm_pairingLeft_le c) (projE i) C (norm_projE_le hC0 hC i) (rhoE h)
      (differentiableAt_rhoE h _)).differentiableAt, fun w w' hw hw' => ?_⟩
    have := norm_fderiv_comp_linear_sub_le (pairingLeft c) (4 * ‖c‖) (by positivity)
      (norm_pairingLeft_le c) (projE i) C hC0 (norm_projE_le hC0 hC i) (rhoE h)
      (by positivity : 0 ≤ KE * (h * (C * R))) hdE
      (fun v v' hv hv' => StationaryContraction.norm_fderiv_scaled_sub_le
        ((LinkRemainder.differentiable_adRem (𝔸 := M4)).differentiableOn) hltE hLipE hh hCR0 hrE'
        hv hv') hw hw'
    refine this.trans ?_
    rw [hLt]
    have hhCR : 0 ≤ h * (C * R) := by positivity
    have : 4 * ‖c‖ * (KE * (h * (C * R))) * C * C ≤ 4 * P * (KE + KB) * (h * (C * R)) * C * C := by
      have h1 : ‖c‖ * KE ≤ P * (KE + KB) := by
        calc ‖c‖ * KE ≤ P * KE := by gcongr
          _ ≤ P * (KE + KB) := by gcongr; linarith
      have h2 : 0 ≤ (h * (C * R)) * C * C := by positivity
      nlinarith
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  have termB : ∀ (c : M4) (i j : Fin 3), ‖c‖ ≤ P →
      (∀ w : Fin 4 → LocVal, ‖w‖ ≤ R →
        DifferentiableAt ℝ (fun w => pairingLeft c (rhoB h (projB i j w))) w) ∧
      ∀ w w' : Fin 4 → LocVal, ‖w‖ ≤ R → ‖w'‖ ≤ R →
        ‖fderiv ℝ (fun w => pairingLeft c (rhoB h (projB i j w))) w -
          fderiv ℝ (fun w => pairingLeft c (rhoB h (projB i j w))) w'‖ ≤ Lt * ‖w - w'‖ := by
    intro c i j hc
    refine ⟨fun w hw => (hasFDerivAt_comp_linear (pairingLeft c) (4 * ‖c‖)
      (norm_pairingLeft_le c) (projB i j) C (norm_projB_le hC0 hC i j) (rhoB h)
      (hdB _ ((norm_projB_le hC0 hC i j w).trans (by gcongr)))).differentiableAt,
      fun w w' hw hw' => ?_⟩
    have := norm_fderiv_comp_linear_sub_le (pairingLeft c) (4 * ‖c‖) (by positivity)
      (norm_pairingLeft_le c) (projB i j) C hC0 (norm_projB_le hC0 hC i j) (rhoB h)
      (by positivity : 0 ≤ KB * (h * (C * R))) hdB
      (fun v v' hv hv' => StationaryContraction.norm_fderiv_scaled_sub_le
        (LinkRemainder.differentiableOn_plaqRem (𝔸 := M4)) hltB hLipB hh hCR0 hrB' hv hv') hw hw'
    refine this.trans ?_
    rw [hLt]
    have this' : 4 * ‖c‖ * (KB * (h * (C * R))) * C * C ≤
        4 * P * (KE + KB) * (h * (C * R)) * C * C := by
      have h1 : ‖c‖ * KB ≤ P * (KE + KB) := by
        calc ‖c‖ * KB ≤ P * KB := by gcongr
          _ ≤ P * (KE + KB) := by gcongr; linarith
      have h2 : 0 ≤ (h * (C * R)) * C * C := by positivity
      nlinarith
    exact mul_le_mul_of_nonneg_right this' (norm_nonneg _)
  have hterm : ∀ t : Fin 6,
      (∀ w : Fin 4 → LocVal, ‖w‖ ≤ R → DifferentiableAt ℝ (remTerm χ h e x t) w) ∧
      ∀ w w' : Fin 4 → LocVal, ‖w‖ ≤ R → ‖w'‖ ≤ R →
        ‖fderiv ℝ (remTerm χ h e x t) w - fderiv ℝ (remTerm χ h e x t) w'‖ ≤ Lt * ‖w - w'‖ := by
    intro t
    fin_cases t
    · exact termE _ 0 (hPi 0)
    · exact termE _ 1 (hPi 1)
    · exact termE _ 2 (hPi 2)
    · exact termB _ 0 1 (hSi 0 1)
    · exact termB _ 0 2 (hSi 0 2)
    · exact termB _ 1 2 (hSi 1 2)
  have hfun : remLocal χ h e x = fun w => ∑ t, remTerm χ h e x t w :=
    funext fun w => remLocal_eq_sum hh.ne' χ e x w
  refine ⟨fun w hw => ?_, fun w w' hw hw' => ?_⟩
  · rw [hfun]
    exact (HasFDerivAt.fun_sum fun t _ => ((hterm t).1 w hw).hasFDerivAt).differentiableAt
  · rw [hfun]
    refine (norm_fderiv_finsum_sub_le _ (fun _ => Lt) (fun t => (hterm t).1 w hw)
      (fun t => (hterm t).1 w' hw') (fun t => (hterm t).2 w w' hw hw')).trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hLt, hPdef]
    push_cast
    ring

/-! ### The remainder gradient `N_h = ∂_A r_h` -/

theorem norm_rhoE_le {h : ℝ} (hh : 0 < h) (p : M4 × M4) (hp : h * ‖p‖ ≤ 1) :
    ‖rhoE h p‖ ≤ 16 * h * ‖p‖ ^ 3 := by
  unfold rhoE
  have hhp : ‖h • p‖ = h * ‖p‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
  have := LinkRemainder.norm_adRem_le (𝔸 := M4) (h • p) (by rw [hhp]; exact hp)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), hhp] at *
  calc (h ^ 2)⁻¹ * ‖LinkRemainder.adRem (h • p)‖ ≤ (h ^ 2)⁻¹ * (16 * (h * ‖p‖) ^ 3) := by
        gcongr
    _ = 16 * h * ‖p‖ ^ 3 := by field_simp

theorem norm_rhoB_le {h : ℝ} (hh : 0 < h) (Y : Fin 4 → M4) (hY : h * ‖Y‖ ≤ 1 / 16) :
    ‖rhoB h Y‖ ≤ 384 * h * ‖Y‖ ^ 3 := by
  unfold rhoB
  have hhY : ‖h • Y‖ = h * ‖Y‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
  have := LinkRemainder.norm_plaqRem_le (𝔸 := M4) (h • Y) (by rw [hhY]; exact hY)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), hhY] at *
  calc (h ^ 2)⁻¹ * ‖LinkRemainder.plaqRem (h • Y)‖ ≤ (h ^ 2)⁻¹ * (384 * (h * ‖Y‖) ^ 3) := by
        gcongr
    _ = 384 * h * ‖Y‖ ^ 3 := by field_simp

/-- The local remainder has vanishing derivative at the zero connection (it is cubic). -/
theorem fderiv_remLocal_zero {h : ℝ} (hh : 0 < h) (χ : ℝ) (e : Site N → M4) (x : Site N) :
    fderiv ℝ (remLocal χ h e x) 0 = 0 := by
  obtain ⟨C, hC1, hC⟩ := exists_iota_bound
  have hC0 : 0 ≤ C := by linarith
  set P := ‖e x‖ with hP
  set Pm := 8192 * |χ| * P ^ 2 with hPm
  have hPi : ∀ i, ‖-piArr χ (e x) i‖ ≤ Pm := fun i => by
    rw [norm_neg]; exact norm_piArr_le χ (e x) i
  have hSi : ∀ i j, ‖sigmaArr χ (e x) i j‖ ≤ Pm := fun i j => norm_sigmaArr_le χ (e x) i j
  have hr : 0 < 1 / (16 * h * C) := by positivity
  refine StationaryContraction.cubic_remainder_fderiv_zero hr
    (K := 6 * (4 * Pm) * (384 * h * C ^ 3)) fun w hw => ?_
  have hw' : h * (C * ‖w‖) ≤ 1 / 16 := by
    have := mem_ball_zero_iff.1 hw
    rw [lt_div_iff₀ (by positivity)] at this
    nlinarith [norm_nonneg w]
  have hwE : h * (C * ‖w‖) ≤ 1 := by linarith
  rw [remLocal_eq_sum hh.ne', Real.norm_eq_abs]
  have hterm : ∀ t, |remTerm χ h e x t w| ≤ 4 * Pm * (384 * h * C ^ 3) * ‖w‖ ^ 3 := by
    have hE : ∀ (c : M4) (i : Fin 3), ‖c‖ ≤ Pm →
        |pairingLeft c (rhoE h (projE i w))| ≤ 4 * Pm * (384 * h * C ^ 3) * ‖w‖ ^ 3 := by
      intro c i hc
      have h1 := norm_pairingLeft_le c (rhoE h (projE i w))
      have hp := norm_projE_le hC0 hC i w
      have h2 := norm_rhoE_le hh (projE i w) (by
        calc h * ‖projE i w‖ ≤ h * (C * ‖w‖) := by gcongr
          _ ≤ 1 := hwE)
      rw [Real.norm_eq_abs] at h1
      have h3 : ‖rhoE h (projE i w)‖ ≤ 384 * h * C ^ 3 * ‖w‖ ^ 3 := by
        calc ‖rhoE h (projE i w)‖ ≤ 16 * h * ‖projE i w‖ ^ 3 := h2
          _ ≤ 384 * h * (C * ‖w‖) ^ 3 := by
              have : ‖projE i w‖ ^ 3 ≤ (C * ‖w‖) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hp 3
              nlinarith [norm_nonneg (projE i w), pow_nonneg (norm_nonneg (projE i w)) 3]
          _ = 384 * h * C ^ 3 * ‖w‖ ^ 3 := by ring
      calc _ ≤ 4 * ‖c‖ * ‖rhoE h (projE i w)‖ := h1
        _ ≤ 4 * Pm * (384 * h * C ^ 3 * ‖w‖ ^ 3) := by gcongr
        _ = _ := by ring
    have hB : ∀ (c : M4) (i j : Fin 3), ‖c‖ ≤ Pm →
        |pairingLeft c (rhoB h (projB i j w))| ≤ 4 * Pm * (384 * h * C ^ 3) * ‖w‖ ^ 3 := by
      intro c i j hc
      have h1 := norm_pairingLeft_le c (rhoB h (projB i j w))
      have hp := norm_projB_le hC0 hC i j w
      have h2 := norm_rhoB_le hh (projB i j w) (by
        calc h * ‖projB i j w‖ ≤ h * (C * ‖w‖) := by gcongr
          _ ≤ 1 / 16 := hw')
      rw [Real.norm_eq_abs] at h1
      have h3 : ‖rhoB h (projB i j w)‖ ≤ 384 * h * C ^ 3 * ‖w‖ ^ 3 := by
        calc ‖rhoB h (projB i j w)‖ ≤ 384 * h * ‖projB i j w‖ ^ 3 := h2
          _ ≤ 384 * h * (C * ‖w‖) ^ 3 := by
              have : ‖projB i j w‖ ^ 3 ≤ (C * ‖w‖) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hp 3
              gcongr
          _ = 384 * h * C ^ 3 * ‖w‖ ^ 3 := by ring
      calc _ ≤ 4 * ‖c‖ * ‖rhoB h (projB i j w)‖ := h1
        _ ≤ 4 * Pm * (384 * h * C ^ 3 * ‖w‖ ^ 3) := by gcongr
        _ = _ := by ring
    intro t
    fin_cases t
    · exact hE _ 0 (hPi 0)
    · exact hE _ 1 (hPi 1)
    · exact hE _ 2 (hPi 2)
    · exact hB _ 0 1 (hSi 0 1)
    · exact hB _ 0 2 (hSi 0 2)
    · exact hB _ 1 2 (hSi 1 2)
  calc |∑ t, remTerm χ h e x t w| ≤ ∑ t, |remTerm χ h e x t w| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t : Fin 6, 4 * Pm * (384 * h * C ^ 3) * ‖w‖ ^ 3 := Finset.sum_le_sum fun t _ => hterm t
    _ = 6 * (4 * Pm) * (384 * h * C ^ 3) * ‖w‖ ^ 3 := by simp; ring

/-- The remainder gradient `N_h(e, A) = ∂_A r_h(e, A)`: the `⟨·,·⟩_{b,h}`-gradient of the link
remainder `⟨r_h(e, A), 1⟩_h` (`h = 1/N`), computed site-wise. -/
def Nh (χ : ℝ) (e : Site N → M4) (A : Conn N) : Conn N :=
  siteGrad rieszInv 1 (localSum offs fun x => remLocal χ (hN N) e x) A

theorem Nh_zero (χ : ℝ) (e : Site N → M4) : Nh χ e 0 = 0 := by
  funext y
  have hd : ∀ x, DifferentiableAt ℝ (remLocal χ (hN N) e x) (loc offs x (0 : Conn N)) := by
    intro x
    obtain ⟨ε₀, hε₀, κ, hκ, hlip⟩ := exists_remLocal_lipschitz
    exact (hlip N χ ‖e x‖ (hN N) 0 e x hN_pos le_rfl (by simp; exact hε₀.le) le_rfl).1 _
      (by simp)
  have h0 : fderiv ℝ (localSum offs fun x => remLocal χ (hN N) e x) (0 : Conn N) = 0 := by
    rw [(hasFDerivAt_localSum offs _ 0 hd).fderiv]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [map_zero, fderiv_remLocal_zero hN_pos, ContinuousLinearMap.zero_comp]
  simp [Nh, siteGrad, h0]

/-- **The remainder estimate `eq:supp-exact-connection-remainder`** (sup norm, `p = ∞`):
there are absolute constants `ε₀ > 0`, `κ ≥ 0` such that on every regulator, for every coframe
with `‖e(x)‖ ≤ E_max` and every `R` with `hR ≤ ε₀` (`h = 1/N`),
`‖N_h(e, A) - N_h(e, Ã)‖ ≤ κ |χ| E_max² · hR · ‖A - Ã‖` on `‖A‖, ‖Ã‖ ≤ R`. -/
theorem exists_Nh_lipschitz :
    ∃ ε₀ > 0, ∃ κ, 0 ≤ κ ∧ ∀ (N : ℕ) [NeZero N] (χ Emax R : ℝ) (e : Site N → M4),
      0 ≤ R → hN N * R ≤ ε₀ → (∀ x, ‖e x‖ ≤ Emax) →
      ∀ A Ã : Conn N, ‖A‖ ≤ R → ‖Ã‖ ≤ R →
        ‖Nh χ e A - Nh χ e Ã‖ ≤ κ * (|χ| * Emax ^ 2) * (hN N * R) * ‖A - Ã‖ := by
  obtain ⟨ε₀, hε₀, κ, hκ, hlip⟩ := exists_remLocal_lipschitz
  refine ⟨ε₀, hε₀, 2 * κ, by positivity, ?_⟩
  intro N _ χ Emax R e hR hhR he A Ã hA hÃ
  have hL0 : 0 ≤ κ * (|χ| * Emax ^ 2) * (hN N * R) := by
    have := hN_pos (N := N); positivity
  have key := grad_lipschitz offs (fun x => remLocal χ (hN N) e x) rieszInv one_pos hL0
    (fun x a ha => (hlip N χ Emax (hN N) R e x hN_pos hR hhR (he x)).1 a ha)
    (fun x a ã ha hã => (hlip N χ Emax (hN N) R e x hN_pos hR hhR (he x)).2 a ã ha hã) hA hÃ
  have hr := norm_rieszInv_le
  calc ‖Nh χ e A - Nh χ e Ã‖ ≤ 1⁻¹ * ‖rieszInv‖ * (4 : ℕ) * (κ * (|χ| * Emax ^ 2) * (hN N * R)) *
        ‖A - Ã‖ := key
    _ ≤ 1⁻¹ * (1 / 2) * (4 : ℕ) * (κ * (|χ| * Emax ^ 2) * (hN N * R)) * ‖A - Ã‖ := by gcongr
    _ = 2 * κ * (|χ| * Emax ^ 2) * (hN N * R) * ‖A - Ã‖ := by push_cast; ring

/-! ### The stationary row -/

/-- The phase-compatible load `f°_h(e)` in Lorentz coordinates:
`(f°_{h,0}, f°_{h,i}) = (Σ_i δ_iΠ_i, -∂_tΠ_i - Σ_{j≠i} δ_jΣ_ji)`. -/
def fPh (χ : ℝ) (e : Site N → M4) (Pidot : Fin 3 → Site N → M4) : Conn N :=
  fun x μ => Fin.cases (coord (load0Ph χ e x)) (fun i => coord (-Pidot i x + loadSpPh χ e i x)) μ

theorem cartanOp_add (χ : ℝ) (e : Site N → M4) (A B : Conn N) :
    cartanOp χ e (A + B) = cartanOp χ e A + cartanOp χ e B := by
  funext x μ
  refine Fin.cases ?_ (fun i => ?_) μ
  · simp only [cartanOp, Fin.cases_zero, Pi.add_apply, cart0, toA0_add, toA_add,
      bracket_add_left, Finset.sum_add_distrib, coord_add]
  · simp only [cartanOp, Fin.cases_succ, Pi.add_apply, cartSp, toA0_add, toA_add,
      bracket_add_left, bracket_add_right, Finset.sum_add_distrib, coord_add]
    abel

theorem cartanOp_smul (χ : ℝ) (e : Site N → M4) (c : ℝ) (A : Conn N) :
    cartanOp χ e (c • A) = c • cartanOp χ e A := by
  funext x μ
  refine Fin.cases ?_ (fun i => ?_) μ
  · simp only [cartanOp, Fin.cases_zero, Pi.smul_apply, cart0, toA0_smul, toA_smul,
      bracket_smul_left, ← Finset.smul_sum, coord_smul]
  · simp only [cartanOp, Fin.cases_succ, Pi.smul_apply, cartSp, toA0_smul, toA_smul,
      bracket_smul_left, bracket_smul_right, ← Finset.smul_sum, ← smul_add, coord_smul]

/-- The Cartan operator `C(e)` as a linear map. -/
def cartanLin (χ : ℝ) (e : Site N → M4) : Conn N →ₗ[ℝ] Conn N where
  toFun := cartanOp χ e
  map_add' := cartanOp_add χ e
  map_smul' := cartanOp_smul χ e

/-- The Cartan operator `C(e)` as a continuous linear map (finite dimension). -/
def cartanCLM (χ : ℝ) (e : Site N → M4) : Conn N →L[ℝ] Conn N :=
  LinearMap.toContinuousLinearMap (cartanLin χ e)

@[simp] theorem cartanCLM_apply (χ : ℝ) (e : Site N → M4) (A : Conn N) :
    cartanCLM χ e A = cartanOp χ e A := rfl

/-- The explicit stationary row `γ°_h(e, A) = f°_h(e) + C(e)A + N_h(e, A)`
(`eq:supp-exact-stationary-connection`). -/
def statRowExplicit (χ : ℝ) (e : Site N → M4) (Pidot : Fin 3 → Site N → M4) (A : Conn N) :
    Conn N :=
  fPh χ e Pidot + cartanOp χ e A + Nh χ e A

/-- The stationary row as the `⟨·,·⟩_{b,h}`-gradient of the phase-compatible Lagrangian:
`D_A L°(A)[δ] = h³ Σ_x ⟨γ(x), δ(x)⟩_b`. -/
def statRow (χ Λ : ℝ) (e : Site N → M4) (Pidot : Fin 3 → Site N → M4) (A : Conn N) : Conn N :=
  siteGrad rieszInv (hN N ^ 3) (phaseLagr χ Λ e Pidot) A

theorem rieszInv_bdotCLM (u : LocVal) : rieszInv (bdotCLM u) = u := by
  funext μ k
  simp only [rieszInv, LinearMap.mkContinuous_apply, rieszInvLin, LinearMap.coe_mk,
    AddHom.coe_mk, bdotCLM_apply, bdot, unitLoc]
  rw [Finset.sum_eq_single μ, Finset.sum_eq_single k]
  · simp [gram_ne_zero k]
  · intro b _ hb; simp [hb]
  · simp
  · intro b _ hb; simp [hb]
  · simp

/-- A gradient is determined by any derivative formula of the form `w Σ_y ⟨g(y), δ(y)⟩_b`. -/
theorem siteGrad_eq_of_hasFDerivAt {f : Conn N → ℝ} {L : Conn N →L[ℝ] ℝ} {A : Conn N} {w : ℝ}
    (hw : w ≠ 0) (hf : HasFDerivAt f L A) (g : Conn N)
    (hL : ∀ δ, L δ = w * ∑ y, bdot (g y) (δ y)) : siteGrad rieszInv w f A = g := by
  funext y
  have hcomp : L.comp (ContinuousLinearMap.single ℝ (fun _ : Site N => LocVal) y) =
      w • bdotCLM (g y) := by
    refine ContinuousLinearMap.ext fun v => ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply, hL]
    simp only [ContinuousLinearMap.smul_apply, bdotCLM_apply, smul_eq_mul]
    congr 1
    rw [Finset.sum_eq_single y]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb, bdot]
    · simp
  simp only [siteGrad, hf.fderiv, hcomp, map_smul, rieszInv_bdotCLM, smul_smul,
    inv_mul_cancel₀ hw, one_smul]

/-! ### Existence and uniqueness of the stationary connection -/

/-- **The stationary connection** (clause (ii) of `thm:supp-exact-action-provenance`, existence and
uniqueness).  Fix `χ`, a coframe bound `E_max` and a least singular value `c_* > 0`.  There is a
threshold `ε > 0`, independent of the cutoff `N`, such that: whenever `hR ≤ ε` (`h = 1/N`), the
coframe obeys `‖e(x)‖ ≤ E_max`, the Cartan operator obeys `c_*‖A‖ ≤ ‖C(e)A‖` (the chart's
least-singular-value hypothesis) and the phase-compatible load obeys `‖f°_h‖ ≤ c_* R/4`, the
stationary row `γ°_h = f°_h + C(e)A + N_h(e, A)` has exactly one zero in the closed `R`-ball, and
every such zero satisfies `‖A‖ ≤ 2c_*⁻¹‖f°_h‖`.  No Fourier mode is removed. -/
theorem stationary_connection_exists_unique (χ Emax c : ℝ) (hc : 0 < c) :
    ∃ ε > 0, ∀ (N : ℕ) [NeZero N] (R : ℝ) (e : Site N → M4) (Pidot : Fin 3 → Site N → M4),
      0 ≤ R → hN N * R ≤ ε → (∀ x, ‖e x‖ ≤ Emax) →
      (∀ A : Conn N, c * ‖A‖ ≤ ‖cartanOp χ e A‖) → ‖fPh χ e Pidot‖ ≤ c * R / 4 →
      (∃! A : Conn N, A ∈ closedBall (0 : Conn N) R ∧ statRowExplicit χ e Pidot A = 0) ∧
      ∀ A : Conn N, A ∈ closedBall (0 : Conn N) R → statRowExplicit χ e Pidot A = 0 →
        ‖A‖ ≤ 2 * c⁻¹ * ‖fPh χ e Pidot‖ := by
  obtain ⟨ε₀, hε₀, κ, hκ, hlip⟩ := exists_Nh_lipschitz
  set M := κ * (|χ| * Emax ^ 2) with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨min ε₀ (c / (2 * (M + 1))), by positivity, ?_⟩
  intro N _ R e Pidot hR hhR he hC hf
  have hhR0 : hN N * R ≤ ε₀ := hhR.trans (min_le_left _ _)
  have hhR1 : hN N * R ≤ c / (2 * (M + 1)) := hhR.trans (min_le_right _ _)
  have hhpos : 0 ≤ hN N * R := mul_nonneg (hN_pos (N := N)).le hR
  have hL : ∀ x ∈ closedBall (0 : Conn N) R, ∀ y ∈ closedBall (0 : Conn N) R,
      ‖Nh χ e x - Nh χ e y‖ ≤ M * (hN N * R) * ‖x - y‖ := fun x hx y hy =>
    hlip N χ Emax R e hR hhR0 he x y (mem_closedBall_zero_iff.1 hx) (mem_closedBall_zero_iff.1 hy)
  have hKL : c⁻¹ * (M * (hN N * R)) ≤ 1 / 2 := by
    have h1 : M * (hN N * R) ≤ M * (c / (2 * (M + 1))) := by gcongr
    have h2 : M * (c / (2 * (M + 1))) ≤ c / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc c⁻¹ * (M * (hN N * R)) ≤ c⁻¹ * (c / 2) := by gcongr; exact h1.trans h2
      _ = 1 / 2 := by field_simp
  have hN0 : ‖Nh χ e 0‖ = 0 := by rw [Nh_zero, norm_zero]
  have hKR : c⁻¹ * (‖fPh χ e Pidot‖ + ‖Nh χ e 0‖) ≤ R / 2 := by
    rw [hN0, add_zero]
    calc c⁻¹ * ‖fPh χ e Pidot‖ ≤ c⁻¹ * (c * R / 4) := by gcongr
      _ = R / 4 := by field_simp
      _ ≤ R / 2 := by linarith
  have hCl : ∀ x, c * ‖x‖ ≤ ‖cartanCLM χ e x‖ := hC
  refine ⟨?_, fun A hA hz => ?_⟩
  · simpa [statRowExplicit] using
      StationaryContraction.exists_unique_zero_of_lower_bound hc hCl (fPh χ e Pidot) (Nh χ e)
        hL hKL hKR
  · have := StationaryContraction.norm_le_of_zero_of_lower_bound hc hCl hL hKL hA
      (by simpa [statRowExplicit] using hz)
    rwa [hN0, add_zero] at this

/-! ### The stationary row is the gradient of the action -/

theorem bdot_fPh (χ : ℝ) (e : Site N → M4) (Pidot : Fin 3 → Site N → M4) (B : Conn N)
    (x : Site N) :
    bdot (fPh χ e Pidot x) (B x) =
      pairing (load0Ph χ e x) (toA0 B x) +
        ∑ i, pairing (-Pidot i x + loadSpPh χ e i x) (toA B i x) := by
  unfold bdot
  rw [Fin.sum_univ_succ]
  simp only [fPh, Fin.cases_zero, Fin.cases_succ, toA0, toA, pairing_iota]

/-- Splitting of the phase-compatible Lagrangian into constant, linear, Cartan-quadratic and
remainder parts. -/
theorem phaseLagr_split (χ Λ : ℝ) (e : Site N → M4) (Pidot : Fin 3 → Site N → M4) (B : Conn N) :
    phaseLagr χ Λ e Pidot B =
      hN N ^ 3 * ∑ x, (-2 * χ * Λ * (e x).det) +
        (hN N ^ 3 * ∑ x, bdot (fPh χ e Pidot x) (B x) +
          (hN N ^ 3 * ∑ x, qc χ e (toA0 B) (toA B) x +
            hN N ^ 3 * localSum offs (fun x => remLocal χ (hN N) e x) B)) := by
  unfold phaseLagr gridPair nfDensityPh
  simp only [bdot_fPh, localSum, remLocal_loc]
  rw [← mul_add, ← mul_add, ← mul_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- The linear part as a continuous linear functional. -/
def linPart (χ : ℝ) (e : Site N → M4) (Pidot : Fin 3 → Site N → M4) : Conn N →L[ℝ] ℝ :=
  hN N ^ 3 • ∑ x, (bdotCLM (fPh χ e Pidot x)).comp (ContinuousLinearMap.proj x)

theorem linPart_apply (χ : ℝ) (e : Site N → M4) (Pidot : Fin 3 → Site N → M4) (B : Conn N) :
    linPart χ e Pidot B = hN N ^ 3 * ∑ x, bdot (fPh χ e Pidot x) (B x) := by
  simp [linPart, ContinuousLinearMap.sum_apply]

/-- The derivative of the Cartan-quadratic part at `A`. -/
def quadPart (χ : ℝ) (e : Site N → M4) (A : Conn N) : Conn N →L[ℝ] ℝ :=
  hN N ^ 3 • ∑ x, (bdotCLM (cartanOp χ e A x)).comp (ContinuousLinearMap.proj x)

theorem quadPart_apply (χ : ℝ) (e : Site N → M4) (A δ : Conn N) :
    quadPart χ e A δ = hN N ^ 3 * ∑ x, bdot (cartanOp χ e A x) (δ x) := by
  simp [quadPart, ContinuousLinearMap.sum_apply]

theorem hasFDerivAt_quad (χ : ℝ) (e : Site N → M4) (A : Conn N) :
    HasFDerivAt (fun B : Conn N => hN N ^ 3 * ∑ x, qc χ e (toA0 B) (toA B) x)
      (quadPart χ e A) A := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hid : ∀ δ : Conn N, hN N ^ 3 * ∑ x, qc χ e (toA0 (A + δ)) (toA (A + δ)) x -
      hN N ^ 3 * ∑ x, qc χ e (toA0 A) (toA A) x - quadPart χ e A δ =
      hN N ^ 3 * ∑ x, qc χ e (toA0 δ) (toA δ) x := by
    intro δ
    rw [quadPart_apply]
    simp only [qc_add, Finset.sum_add_distrib]
    ring
  simp only [hid]
  set K := hN N ^ 3 * (Fintype.card (Site N) : ℝ) * (24 * ‖cartanCLM χ e‖) with hK
  have hbig : (fun δ : Conn N => hN N ^ 3 * ∑ x, qc χ e (toA0 δ) (toA δ) x) =O[nhds 0]
      (fun δ : Conn N => ‖δ‖ ^ 2) := by
    refine Asymptotics.IsBigO.of_bound K (Filter.Eventually.of_forall fun δ => ?_)
    have hh3 : 0 ≤ hN N ^ 3 := by have := hN_pos (N := N); positivity
    have hterm : ∀ x, |qc χ e (toA0 δ) (toA δ) x| ≤ 24 * ‖cartanCLM χ e‖ * ‖δ‖ ^ 2 := by
      intro x
      rw [qc_eq_half, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have h1 := abs_bdot_le (cartanOp χ e δ x) (δ x)
      have h2 : ‖cartanOp χ e δ x‖ ≤ ‖cartanCLM χ e‖ * ‖δ‖ :=
        (norm_le_pi_norm (cartanOp χ e δ) x).trans ((cartanCLM χ e).le_opNorm δ)
      have h3 : ‖δ x‖ ≤ ‖δ‖ := norm_le_pi_norm δ x
      calc 1 / 2 * |bdot (cartanOp χ e δ x) (δ x)| ≤ 1 / 2 * (48 * (‖cartanOp χ e δ x‖ * ‖δ x‖)) := by
            gcongr
        _ ≤ 1 / 2 * (48 * ((‖cartanCLM χ e‖ * ‖δ‖) * ‖δ‖)) := by gcongr
        _ = 24 * ‖cartanCLM χ e‖ * ‖δ‖ ^ 2 := by ring
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hh3,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖δ‖ ^ 2)]
    calc hN N ^ 3 * |∑ x, qc χ e (toA0 δ) (toA δ) x|
        ≤ hN N ^ 3 * ∑ _x : Site N, 24 * ‖cartanCLM χ e‖ * ‖δ‖ ^ 2 := by
          gcongr
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => hterm x)
      _ = K * ‖δ‖ ^ 2 := by simp [hK]; ring
  exact hbig.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id one_lt_two)

/-- **The stationary row is the gradient of the phase-compatible action**: for connections with
`h‖A‖ ≤ ε₀` (inside the retained branch), the `⟨·,·⟩_{b,h}`-gradient of `A ↦ L°(e, ∂_tΠ; A)` is
exactly `f°_h(e) + C(e)A + N_h(e, A)` (`eq:supp-exact-stationary-connection`). -/
theorem exists_statRow_eq :
    ∃ ε₀ > 0, ∀ (N : ℕ) [NeZero N] (χ Λ : ℝ) (e : Site N → M4) (Pidot : Fin 3 → Site N → M4)
      (A : Conn N), hN N * ‖A‖ ≤ ε₀ → statRow χ Λ e Pidot A = statRowExplicit χ e Pidot A := by
  obtain ⟨ε₀, hε₀, κ, hκ, hlip⟩ := exists_remLocal_lipschitz
  refine ⟨ε₀, hε₀, ?_⟩
  intro N _ χ Λ e Pidot A hA
  have hd : ∀ x, DifferentiableAt ℝ (remLocal χ (hN N) e x) (loc offs x A) := fun x =>
    (hlip N χ ‖e x‖ (hN N) ‖A‖ e x hN_pos (norm_nonneg _) hA le_rfl).1 _
      (norm_loc_apply_le offs x A)
  have hloc := hasFDerivAt_localSum offs (fun x => remLocal χ (hN N) e x) A hd
  set Dl := ∑ x, (fderiv ℝ (remLocal χ (hN N) e x) (loc offs x A)).comp (loc offs x)
  have hfun : phaseLagr χ Λ e Pidot = fun B => hN N ^ 3 * ∑ x, (-2 * χ * Λ * (e x).det) +
      (linPart χ e Pidot B + (hN N ^ 3 * ∑ x, qc χ e (toA0 B) (toA B) x +
        hN N ^ 3 * localSum offs (fun x => remLocal χ (hN N) e x) B)) := by
    funext B; rw [phaseLagr_split, linPart_apply]
  have hF : HasFDerivAt (phaseLagr χ Λ e Pidot)
      (linPart χ e Pidot + (quadPart χ e A + hN N ^ 3 • Dl)) A := by
    rw [hfun]
    have h1 := (linPart χ e Pidot).hasFDerivAt.add
      ((hasFDerivAt_quad χ e A).add (hloc.const_mul (hN N ^ 3)))
    have h2 := (hasFDerivAt_const (hN N ^ 3 * ∑ x, (-2 * χ * Λ * (e x).det)) A).add h1
    rw [zero_add] at h2
    exact h2
  have hDl : ∀ δ, Dl δ = 1 * ∑ y, bdotCLM (Nh χ e A y) (δ y) := by
    intro δ
    rw [← hloc.fderiv]
    exact fderiv_eq_sum_siteGrad rieszInv one_ne_zero bdotCLM rieszInv_spec _ A δ
  have hh3 : hN N ^ 3 ≠ 0 := pow_ne_zero 3 hN_ne_zero
  refine siteGrad_eq_of_hasFDerivAt hh3 hF _ fun δ => ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, linPart_apply,
    quadPart_apply, hDl, smul_eq_mul, bdotCLM_apply, statRowExplicit, Pi.add_apply,
    bdot_add_left, Finset.sum_add_distrib]
  ring

/-- **Clause (ii) of `thm:supp-exact-action-provenance`, existence and uniqueness, gradient form.**
Under the chart hypotheses of `stationary_connection_exists_unique` and for `hR` below an
`N`-independent threshold, the `⟨·,·⟩_{b,h}`-gradient of the phase-compatible Lagrangian in the
connection (the stationary row) has exactly one zero in the closed `R`-ball, it satisfies
`‖A‖ ≤ 2c_*⁻¹‖f°_h‖`, and on that ball the gradient is `f°_h + C(e)A + N_h(e, A)`. -/
theorem stationary_connection_gradient_exists_unique (χ Λ Emax c : ℝ) (hc : 0 < c) :
    ∃ ε > 0, ∀ (N : ℕ) [NeZero N] (R : ℝ) (e : Site N → M4) (Pidot : Fin 3 → Site N → M4),
      0 ≤ R → hN N * R ≤ ε → (∀ x, ‖e x‖ ≤ Emax) →
      (∀ A : Conn N, c * ‖A‖ ≤ ‖cartanOp χ e A‖) → ‖fPh χ e Pidot‖ ≤ c * R / 4 →
      (∃! A : Conn N, A ∈ closedBall (0 : Conn N) R ∧ statRow χ Λ e Pidot A = 0) ∧
      (∀ A : Conn N, A ∈ closedBall (0 : Conn N) R → statRow χ Λ e Pidot A = 0 →
        ‖A‖ ≤ 2 * c⁻¹ * ‖fPh χ e Pidot‖) ∧
      ∀ A : Conn N, A ∈ closedBall (0 : Conn N) R →
        statRow χ Λ e Pidot A = statRowExplicit χ e Pidot A := by
  obtain ⟨ε₁, hε₁, h1⟩ := stationary_connection_exists_unique χ Emax c hc
  obtain ⟨ε₂, hε₂, h2⟩ := exists_statRow_eq
  refine ⟨min ε₁ ε₂, by positivity, ?_⟩
  intro N _ R e Pidot hR hhR he hC hf
  have hball : ∀ A : Conn N, A ∈ closedBall (0 : Conn N) R →
      statRow χ Λ e Pidot A = statRowExplicit χ e Pidot A := by
    intro A hA
    refine h2 N χ Λ e Pidot A ?_
    calc hN N * ‖A‖ ≤ hN N * R := by
          gcongr
          · exact (hN_pos (N := N)).le
          · exact mem_closedBall_zero_iff.1 hA
      _ ≤ ε₂ := hhR.trans (min_le_right _ _)
  obtain ⟨hex, hbd⟩ := h1 N R e Pidot hR (hhR.trans (min_le_left _ _)) he hC hf
  refine ⟨?_, fun A hA hz => hbd A hA (by rwa [← hball A hA]), hball⟩
  obtain ⟨A, ⟨hA, hz⟩, huniq⟩ := hex
  refine ⟨A, ⟨hA, by rw [hball A hA]; exact hz⟩, fun B ⟨hB, hzB⟩ => huniq B ⟨hB, ?_⟩⟩
  rwa [← hball B hB]

/-- Non-vacuity of the stationary row: at flat data (unit coframe, zero load) the zero connection
is a zero of the explicit stationary row. -/
theorem statRowExplicit_zero_of_fPh_zero (χ : ℝ) (e : Site N → M4) (Pidot : Fin 3 → Site N → M4)
    (hf : fPh χ e Pidot = 0) : statRowExplicit χ e Pidot 0 = 0 := by
  have hC : cartanOp χ e 0 = 0 := by
    have := cartanOp_smul χ e 0 0
    simpa using this
  simp [statRowExplicit, hf, hC, Nh_zero]

end RenewalGeometry.ExactPhaseAction
