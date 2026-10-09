/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactShiftCovariance

/-!
# The flat slice of the canonical Hamiltonian at arbitrary lapse and shift
  (`eq:supp-exact-ward-mass-order` on the slice `X = 0`; emergent-spacetime manuscript)

At the flat metric `γ = I` and zero momentum, but **arbitrary** lapse `N(x)` and shift `β(x)`
near `(1, 0)`, the stationary connection of the actual action and the Legendre velocity are
computed exactly:

* `site_identity_flat` (one-site polynomial identity): with the lattice Lie derivative
  `V = L_β I` (`lieVec`, `V_{pq} = δ_pβ_q + δ_qβ_p`) and the temporal connection
  `A₀ = ι(δN, ½ curl β)` (`a0Vec`), the spatial stationary rows vanish.
* `fderiv_phaseLagr_flatConn`: at `e = e(I, N, β)`, `∂_tΠ = DΠ(I)[L_β I]`, the connection
  `flatConn = (A₀, 0)` (no spatial part) is an exact critical point of the phase-compatible
  Lagrangian (the link remainders are quadratic in the spatial connection, `remE_sq_bound`).
* **`flat_slice`**: for `(N, β)` near `(1, 0)` the selected stationary connection at
  `((I, N, β), L_β I)` is `flatConn (N, β)`, the momentum there vanishes, and the Legendre
  velocity of the canonical Hamiltonian at `((I, N, β), π = 0)` is `L_β I`.  In particular the
  spatial part of the stationary connection vanishes on the whole flat slice.
-/

open Filter Finset Metric Asymptotics
open scoped Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace RenewalGeometry.ExactPhaseAction.ShiftWard

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

open PalatiniEinsteinAlgebra OddPhaseDerivativeReal QuadJet InitialConstraintLinearRange

/-! ### The one-site identity -/

/-- `Sym₃` coordinates of the lattice Lie derivative `δ_pβ_q + δ_qβ_p` of the flat metric. -/
def lieVec (b : Fin 3 → Fin 3 → ℝ) : Fin 6 → ℝ :=
  ![b 0 0 + b 0 0, b 1 1 + b 1 1, b 2 2 + b 2 2, b 0 1 + b 1 0, b 0 2 + b 2 0, b 1 2 + b 2 1]

/-- Lorentz coordinates of the flat temporal connection `A₀ = ι(δN, ½ curl β)`. -/
def a0Vec (n : Fin 3 → ℝ) (b : Fin 3 → Fin 3 → ℝ) : Fin 6 → ℝ :=
  ![n 0, n 1, n 2, (b 2 1 - b 1 2) / 2, (b 0 2 - b 2 0) / 2, (b 1 0 - b 0 1) / 2]

set_option maxHeartbeats 4000000 in
-- 18 coordinate identities
/-- **The one-site identity of the flat slice**: `-DΠ_i(1)[½ L_b] - Σ_j (n_j Σ_ji + b_ji Π_j -
b_jj Π_i) + [Π_i, A₀] = 0` in Lorentz coordinates. -/
theorem site_identity_flat (χ : ℝ) (n : Fin 3 → ℝ) (b : Fin 3 → Fin 3 → ℝ) (i : Fin 3) :
    -(χ • piLinVec (admLinA ((1 / 2 : ℝ) • symMat (lieVec b)) 0 0) i) -
      (∑ j, (n j • sigVec χ j i + b j i • piVec χ j - b j j • piVec χ i)) +
      lieCoord (piVec χ i) (a0Vec n b) = 0 := by
  funext k
  fin_cases i <;> fin_cases k <;>
    simp [piLinVec, admLinA_eq, symMat, sym6, sigVec, piVec, lieCoord, a0Vec, lieVec,
      Fin.sum_univ_three, Matrix.vecHead, Matrix.vecTail, Pi.smul_apply] <;> ring

/-! ### The flat slice: coframe, loads and `Π`-velocity -/

variable {N : ℕ} [NeZero N]

/-- Lapse–shift multipliers `λ = (N, β)`. -/
abbrev Lam (N : ℕ) := (Site N → ℝ) × (Site N → Fin 3 → ℝ)

/-- The reference multipliers `e = (1, 0)`. -/
def lamE (N : ℕ) : Lam N := (fun _ => 1, fun _ => 0)

/-- The first jets `δ_j N(x)`. -/
def nJet (n : Site N → ℝ) (x : Site N) : Fin 3 → ℝ := fun j => pd j n x

/-- The first jets `δ_j β^q(x)`. -/
def bJet (β : Site N → Fin 3 → ℝ) (x : Site N) : Fin 3 → Fin 3 → ℝ := fun j q => pd j β x q

/-- The lattice Lie derivative `L_β I` of the flat metric, `δ_pβ_q + δ_qβ_p`. -/
def lieV (β : Site N → Fin 3 → ℝ) : MetF N := fun x => lieVec (bJet β x)

/-- The flat-slice connection `(A₀, A_i) = (ι(δN, ½ curl β), 0)`. -/
def flatConn (lam : Lam N) : Conn N :=
  fun x μ => Fin.cases (motive := fun _ => Fin 6 → ℝ) (a0Vec (nJet lam.1 x) (bJet lam.2 x))
    (fun _ => 0) μ

/-- The flat-slice configuration `((I, N, β), L_β I)`. -/
def flatCfg (lam : Lam N) : ParF N × MetF N := ((flatMet N, lam.1, lam.2), lieV lam.2)

theorem toA_flatConn (lam : Lam N) : toA (flatConn lam) = 0 := by
  funext i x
  simp [toA, flatConn, iota_zero]

theorem toA0_flatConn (lam : Lam N) (x : Site N) :
    toA0 (flatConn lam) x = iota (a0Vec (nJet lam.1 x) (bJet lam.2 x)) := by
  simp [toA0, flatConn]

/-- At the flat metric the canonical coframe is the lapsed and shifted unit coframe. -/
theorem coframeField_flat_slice (n : Site N → ℝ) (β : Site N → Fin 3 → ℝ) (y : Site N) :
    coframeField sqrtTriad ((flatMet N, n, β) : ParF N) y = shiftCo (lapseCo 1 (n y)) (β y) := by
  simp only [coframeField, flatMet, symMat_flatSym, sqrtTriad_one]
  rw [show (β y) = 0 + β y by simp, admCoframe_add_shift]
  rw [show (one3 : M3) = (1 : Matrix (Fin 3) (Fin 3) ℝ) from rfl, admCoframe_one_lapse, zero_add]

theorem piArr_flat_slice (χ : ℝ) (n : Site N → ℝ) (β : Site N → Fin 3 → ℝ) (y : Site N)
    (i : Fin 3) :
    piArr χ (coframeField sqrtTriad ((flatMet N, n, β) : ParF N) y) i = iota (piVec χ i) := by
  rw [coframeField_flat_slice, piArr_shiftCo, piArr_lapseCo, piArr_one]

theorem sigmaArr_flat_slice (χ : ℝ) (n : Site N → ℝ) (β : Site N → Fin 3 → ℝ) (y : Site N)
    (j i : Fin 3) :
    sigmaArr χ (coframeField sqrtTriad ((flatMet N, n, β) : ParF N) y) j i =
      n y • iota (sigVec χ j i) + β y i • iota (piVec χ j) - β y j • iota (piVec χ i) := by
  rw [coframeField_flat_slice, sigmaArr_shiftCo, sigmaArr_lapseCo, piArr_lapseCo, piArr_lapseCo,
    sigmaArr_one, piArr_one, piArr_one]

theorem pd_smul_const (j : Fin 3) (f : Site N → ℝ) (M : M4) (x : Site N) :
    pd j (fun y => f y • M) x = pd j f x • M := by
  have := congrFun (pd_map j (LinearMap.toSpanSingleton ℝ M4 M) f) x
  simpa using this

theorem pd_three_lin (j : Fin 3) (f g k : Site N → ℝ) (M M' M'' : M4) (x : Site N) :
    pd j (fun y => f y • M + g y • M' - k y • M'') x =
      pd j f x • M + pd j g x • M' - pd j k x • M'' := by
  have h : (fun y => f y • M + g y • M' - k y • M'') =
      (fun y => f y • M) + (fun y => g y • M') - (fun y => k y • M'') := rfl
  rw [h, map_sub, map_add]
  simp only [Pi.add_apply, Pi.sub_apply, pd_smul_const]

/-- The temporal load vanishes on the flat slice. -/
theorem load0Ph_flat_slice (χ : ℝ) (n : Site N → ℝ) (β : Site N → Fin 3 → ℝ) (x : Site N) :
    load0Ph χ (coframeField sqrtTriad ((flatMet N, n, β) : ParF N)) x = 0 := by
  simp only [load0Ph, piArr_flat_slice]
  simp [pd_const]

/-- The spatial load on the flat slice. -/
theorem loadSpPh_flat_slice (χ : ℝ) (n : Site N → ℝ) (β : Site N → Fin 3 → ℝ) (i : Fin 3)
    (x : Site N) :
    loadSpPh χ (coframeField sqrtTriad ((flatMet N, n, β) : ParF N)) i x =
      -∑ j, (nJet n x j • iota (sigVec χ j i) + bJet β x j i • iota (piVec χ j) -
        bJet β x j j • iota (piVec χ i)) := by
  simp only [loadSpPh, sigmaArr_flat_slice]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pd_three_lin]
  simp only [nJet, bJet]
  rw [pd_pi_apply j β x i, pd_pi_apply j β x j]

/-- `∂_tΠ_i` at the flat metric: `DΠ_i(1)[δe(½V, 0, 0)]`. -/
theorem piDot_flat (χ : ℝ) (V : MetF N) (i : Fin 3) (x : Site N) :
    piDot χ sqrtTriad (flatMet N) V i x =
      iota (χ • piLinVec (admLinA ((1 / 2 : ℝ) • symMat (V x)) 0 0) i) := by
  rw [← of_dualA_palLinA_pi]
  ext K L
  simp only [piDot, Matrix.of_apply]
  rw [show (flatMet N) x = flatSym from rfl, fderiv_piEntry_flat, piArrADer_apply, admLinD_apply]

theorem iotaLin_apply (c : Fin 6 → ℝ) : iotaLin c = iota c := rfl

/-- **The spatial stationary rows vanish on the flat slice** (M4 form of
`site_identity_flat`): `-∂_tΠ_i + f^sp_i + [Π_i, A₀] = 0` at `((I, N, β), L_β I)`. -/
theorem site_rows_flat (χ : ℝ) (lam : Lam N) (i : Fin 3) (x : Site N) :
    -piDot χ sqrtTriad (flatMet N) (lieV lam.2) i x +
      loadSpPh χ (coframeField sqrtTriad ((flatMet N, lam.1, lam.2) : ParF N)) i x +
      bracket (piArr χ (coframeField sqrtTriad ((flatMet N, lam.1, lam.2) : ParF N) x) i)
        (toA0 (flatConn lam) x) = 0 := by
  rw [piDot_flat, loadSpPh_flat_slice, piArr_flat_slice, toA0_flatConn, bracket_iota_iota]
  have key := congrArg iotaLin (site_identity_flat χ (nJet lam.1 x) (bJet lam.2 x) i)
  simp only [map_add, map_sub, map_neg, map_smul, map_sum, map_zero, iotaLin_apply] at key
  rw [iota_smul]
  simpa [lieV, sub_eq_add_neg] using key

/-! ### Link remainders: quadratic in the spatial connection -/

theorem remE_smul_right (h : ℝ) (a b : M4) (t : ℝ) : remE h a (t • b) = t • remE h a b := by
  have := remE_sub_smul h a 0 b (-t)
  simp only [zero_sub, neg_smul, neg_neg] at this
  have h0 : remE h a 0 = 0 := by simp [remE, bracket]
  rw [this, h0]
  simp

theorem remE_zero_left (h : ℝ) (b : M4) : remE h 0 b = 0 := by
  simp [remE, bracket]

/-- **`ρ^E` is quadratic in the link**: `‖remE h a b‖ ≤ 16 h ‖a‖² ‖b‖` for `h‖a‖ ≤ 1`. -/
theorem norm_remE_le {h : ℝ} (hh : 0 < h) (a b : M4) (ha : h * ‖a‖ ≤ 1) :
    ‖remE h a b‖ ≤ 16 * h * ‖a‖ ^ 2 * ‖b‖ := by
  by_cases hb : b = 0
  · subst hb
    rw [show (0 : M4) = (0 : ℝ) • (0 : M4) by simp, remE_smul_right]; simp
  by_cases ha0 : a = 0
  · subst ha0; rw [remE_zero_left]; simp
  have hbp : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hap : 0 < ‖a‖ := norm_pos_iff.2 ha0
  set t := ‖a‖ / ‖b‖ with ht
  have htp : 0 < t := div_pos hap hbp
  have hnorm : ‖((a, t • b) : M4 × M4)‖ = ‖a‖ := by
    rw [Prod.norm_def, norm_smul, Real.norm_eq_abs, abs_of_pos htp, ht,
      div_mul_cancel₀ _ hbp.ne', max_self]
  have h1 : remE h a b = t⁻¹ • remE h a (t • b) := by
    rw [remE_smul_right, smul_smul, inv_mul_cancel₀ htp.ne', one_smul]
  have h2 : ‖remE h a (t • b)‖ ≤ 16 * h * ‖a‖ ^ 3 := by
    rw [remE_eq_rhoE hh.ne']
    have := norm_rhoE_le hh (a, t • b) (by rw [hnorm]; exact ha)
    rwa [hnorm] at this
  rw [h1, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos htp]
  calc t⁻¹ * ‖remE h a (t • b)‖ ≤ t⁻¹ * (16 * h * ‖a‖ ^ 3) := by gcongr
    _ = 16 * h * ‖a‖ ^ 2 * ‖b‖ := by rw [ht]; field_simp

theorem remB_smul (h : ℝ) (hh : h ≠ 0) (s : ℝ) (a b c d : M4) :
    remB h (s • a) (s • b) (s • c) (s • d) = rhoB h (s • ![a, b, -c, -d]) := by
  rw [remB_eq_rhoB hh]
  congr 1
  funext ℓ
  fin_cases ℓ <;> simp

/-- Along `s ↦ (a₀ + s d₀, s d)`, the Ad-link remainder is `O(s²)`. -/
theorem remE_isBigO {h : ℝ} (hh : 0 < h) (a b b' : M4) :
    (fun s : ℝ => remE h (s • a) (b + s • b')) =O[𝓝 0] fun s => s ^ 2 := by
  have hev : ∀ᶠ s : ℝ in 𝓝 0, |s| ≤ 1 ∧ h * (|s| * ‖a‖) ≤ 1 := by
    have hc : Continuous fun s : ℝ => h * (|s| * ‖a‖) := by fun_prop
    have h1 : ∀ᶠ s : ℝ in 𝓝 0, h * (|s| * ‖a‖) < 1 :=
      hc.continuousAt.eventually (gt_mem_nhds (by simp))
    have h2 : ∀ᶠ s : ℝ in 𝓝 0, |s| < 1 :=
      (continuous_abs.continuousAt).eventually (gt_mem_nhds (by simp))
    filter_upwards [h1, h2] with s hs1 hs2 using ⟨hs2.le, hs1.le⟩
  refine IsBigO.of_bound (16 * h * ‖a‖ ^ 2 * (‖b‖ + ‖b'‖)) ?_
  filter_upwards [hev] with s ⟨hs1, hs2⟩
  have hsa : ‖s • a‖ = |s| * ‖a‖ := by rw [norm_smul, Real.norm_eq_abs]
  have hb : ‖b + s • b'‖ ≤ ‖b‖ + ‖b'‖ := by
    calc ‖b + s • b'‖ ≤ ‖b‖ + ‖s • b'‖ := norm_add_le _ _
      _ ≤ ‖b‖ + ‖b'‖ := by
        gcongr
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) hs1
  have := norm_remE_le hh (s • a) (b + s • b') (by rw [hsa]; exact hs2)
  rw [hsa] at this
  rw [Real.norm_eq_abs (s ^ 2), abs_pow]
  calc ‖remE h (s • a) (b + s • b')‖ ≤ 16 * h * (|s| * ‖a‖) ^ 2 * ‖b + s • b'‖ := this
    _ ≤ 16 * h * (|s| * ‖a‖) ^ 2 * (‖b‖ + ‖b'‖) := by gcongr
    _ = 16 * h * ‖a‖ ^ 2 * (‖b‖ + ‖b'‖) * |s| ^ 2 := by ring

/-- Along `s ↦ s d`, the plaquette remainder is `O(s²)` (it is cubic). -/
theorem remB_isBigO {h : ℝ} (hh : 0 < h) (a b c d : M4) :
    (fun s : ℝ => remB h (s • a) (s • b) (s • c) (s • d)) =O[𝓝 0] fun s => s ^ 2 := by
  set Y : Fin 4 → M4 := ![a, b, -c, -d]
  have hev : ∀ᶠ s : ℝ in 𝓝 0, |s| ≤ 1 ∧ h * (|s| * ‖Y‖) ≤ 1 / 16 := by
    have hc : Continuous fun s : ℝ => h * (|s| * ‖Y‖) := by fun_prop
    have h1 : ∀ᶠ s : ℝ in 𝓝 0, h * (|s| * ‖Y‖) < 1 / 16 :=
      hc.continuousAt.eventually (gt_mem_nhds (by simp))
    have h2 : ∀ᶠ s : ℝ in 𝓝 0, |s| < 1 :=
      (continuous_abs.continuousAt).eventually (gt_mem_nhds (by simp))
    filter_upwards [h1, h2] with s hs1 hs2 using ⟨hs2.le, hs1.le⟩
  refine IsBigO.of_bound (384 * h * ‖Y‖ ^ 3) ?_
  filter_upwards [hev] with s ⟨hs1, hs2⟩
  rw [remB_smul h hh.ne']
  have hsY : ‖s • Y‖ = |s| * ‖Y‖ := by rw [norm_smul, Real.norm_eq_abs]
  have := norm_rhoB_le hh (s • Y) (by rw [hsY]; exact hs2)
  rw [hsY] at this
  rw [Real.norm_eq_abs (s ^ 2), abs_pow]
  have hs3 : |s| ^ 3 ≤ |s| ^ 2 := by
    rw [pow_succ]; exact mul_le_of_le_one_right (by positivity) hs1
  calc ‖rhoB h (s • Y)‖ ≤ 384 * h * (|s| * ‖Y‖) ^ 3 := this
    _ = 384 * h * ‖Y‖ ^ 3 * |s| ^ 3 := by ring
    _ ≤ 384 * h * ‖Y‖ ^ 3 * |s| ^ 2 := by gcongr

/-! ### The flat-slice connection is a critical point -/

/-- The quadratic part of the density along a line `(a₀ + s d₀, s d)`. -/
def q2den (χ : ℝ) (e : Site N → M4) (d0 : Site N → M4) (d : Fin 3 → Site N → M4)
    (x : Site N) : ℝ :=
  (∑ i, pairing (piArr χ (e x) i) (bracket (d0 x) (d i x))) +
    sumLt fun i j => pairing (sigmaArr χ (e x) i j) (bracket (d i x) (d j x))

theorem nfDensityPh_line (χ h s : ℝ) (e : Site N → M4) (P : Fin 3 → Site N → M4)
    (a0 d0 : Site N → M4) (d : Fin 3 → Site N → M4) (x : Site N) (hl0 : load0Ph χ e x = 0) :
    nfDensityPh χ 0 h e P (fun y => a0 y + s • d0 y) (fun i y => s • d i y) x =
      s * (∑ i, pairing (-P i x + loadSpPh χ e i x + bracket (piArr χ (e x) i) (a0 x)) (d i x)) +
      s ^ 2 * q2den χ e d0 d x +
      remDensity χ h e (fun y => a0 y + s • d0 y) (fun i y => s • d i y) x := by
  unfold nfDensityPh qc q2den
  rw [hl0]
  simp only [pairing_zero_left, bracket_add_left, bracket_smul_left, bracket_smul_right,
    pairing_add_right, pairing_smul_right, pairing_add_left, ← pairing_bracket_right, sumLt_eq,
    Fin.sum_univ_three, smul_smul]
  ring

theorem toA0_add_smul (A δ : Conn N) (s : ℝ) :
    toA0 (A + s • δ) = fun y => toA0 A y + s • toA0 δ y := by
  funext y
  simp only [toA0, Pi.add_apply, Pi.smul_apply, iota_add, iota_smul]

theorem toA_add_smul_of (A δ : Conn N) (s : ℝ) (hA : toA A = 0) :
    toA (A + s • δ) = fun i y => s • toA δ i y := by
  funext i y
  have h := congrFun (congrFun hA i) y
  simp only [toA, Pi.add_apply, Pi.smul_apply, iota_add, iota_smul, Pi.zero_apply] at h ⊢
  rw [h, zero_add]

theorem isBigO_finsum {ι : Type*} [Fintype ι] {l : Filter ℝ} {f : ι → ℝ → ℝ} {g : ℝ → ℝ}
    (h : ∀ i, f i =O[l] g) : (fun s => ∑ i, f i s) =O[l] g :=
  (IsBigO.sum (s := Finset.univ) fun i _ => h i).congr_left fun s => by simp [Finset.sum_apply]

theorem pairing_isBigO {l : Filter ℝ} (X : M4) {g : ℝ → M4} {k : ℝ → ℝ} (hg : g =O[l] k) :
    (fun s => pairing X (g s)) =O[l] k := by
  refine IsBigO.trans ?_ hg
  refine IsBigO.of_bound (4 * ‖X‖) (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs]
  calc |pairing X (g s)| ≤ 4 * (‖X‖ * ‖g s‖) := abs_pairing_le _ _
    _ = 4 * ‖X‖ * ‖g s‖ := by ring

/-- The link remainder along a line `(a₀ + s d₀, s d)` is `O(s²)`. -/
theorem remDensity_line_isBigO (χ : ℝ) (e : Site N → M4) (a0 d0 : Site N → M4)
    (d : Fin 3 → Site N → M4) (x : Site N) :
    (fun s : ℝ => remDensity χ (hN N) e (fun y => a0 y + s • d0 y) (fun i y => s • d i y) x)
      =O[𝓝 0] fun s => s ^ 2 := by
  have hh := hN_pos (N := N)
  unfold remDensity
  refine IsBigO.add ?_ ?_
  · refine IsBigO.neg_left ?_
    exact isBigO_finsum fun i => pairing_isBigO _ (remE_isBigO hh _ _ _)
  · simp only [sumLt_eq]
    refine ((IsBigO.add ?_ ?_).add ?_) <;> exact pairing_isBigO _ (remB_isBigO hh _ _ _ _)

/-- **The flat-slice connection is an exact critical point** of the phase-compatible
Lagrangian at `e(I, N, β)`, `∂_tΠ = DΠ(I)[L_β I]`. -/
theorem fderiv_phaseLagr_flatConn (χ : ℝ) (lam : Lam N) :
    fderiv ℝ (phaseLagr χ 0 (coframeField sqrtTriad ((flatMet N, lam.1, lam.2) : ParF N))
      (piDot χ sqrtTriad (flatMet N) (lieV lam.2))) (flatConn lam) = 0 := by
  set e := coframeField sqrtTriad ((flatMet N, lam.1, lam.2) : ParF N)
  set P := piDot χ sqrtTriad (flatMet N) (lieV lam.2)
  have hd : DifferentiableAt ℝ (phaseLagr χ 0 e P) (flatConn lam) := by
    have hbr : PlaqBranch (hN N) (toA (flatConn lam)) := by
      rw [toA_flatConn]; exact plaqBranch_zero _
    have ha := analyticAt_phaseLagr χ 0 (e, P, flatConn lam) hbr
    have hc : AnalyticAt ℝ (fun A : Conn N => ((e, P, A) : (Site N → M4) ×
        (Fin 3 → Site N → M4) × Conn N)) (flatConn lam) :=
      analyticAt_const.prod (analyticAt_const.prod analyticAt_id)
    exact (AnalyticAt.comp_of_eq (g := fun q : (Site N → M4) × (Fin 3 → Site N → M4) × Conn N =>
      phaseLagr χ 0 q.1 q.2.1 q.2.2) ha hc rfl).differentiableAt
  ext δ
  -- the line through `flatConn lam`
  have hline : ∀ s : ℝ, phaseLagr χ 0 e P (flatConn lam + s • δ) =
      s ^ 2 * gridPair (hN N) (q2den χ e (toA0 δ) (toA δ)) + gridPair (hN N) (fun x =>
        remDensity χ (hN N) e (fun y => toA0 (flatConn lam) y + s • toA0 δ y)
          (fun i y => s • toA δ i y) x) := by
    intro s
    have hden : ∀ x, nfDensityPh χ 0 (hN N) e P (fun y => toA0 (flatConn lam) y + s • toA0 δ y)
        (fun i y => s • toA δ i y) x = s ^ 2 * q2den χ e (toA0 δ) (toA δ) x +
          remDensity χ (hN N) e (fun y => toA0 (flatConn lam) y + s • toA0 δ y)
            (fun i y => s • toA δ i y) x := by
      intro x
      rw [nfDensityPh_line χ (hN N) s e P _ _ _ x (load0Ph_flat_slice χ lam.1 lam.2 x)]
      have hrow : ∀ i, -P i x + loadSpPh χ e i x + bracket (piArr χ (e x) i)
          (toA0 (flatConn lam) x) = 0 := fun i => site_rows_flat χ lam i x
      simp only [hrow, pairing_zero_left, Finset.sum_const_zero, mul_zero, zero_add]
    unfold phaseLagr
    rw [toA0_add_smul, toA_add_smul_of _ _ _ (toA_flatConn lam)]
    simp only [gridPair, hden, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  have hR : (fun s : ℝ => gridPair (hN N) (fun x =>
        remDensity χ (hN N) e (fun y => toA0 (flatConn lam) y + s • toA0 δ y)
          (fun i y => s • toA δ i y) x)) =O[𝓝 0] fun s => s ^ 2 := by
    unfold gridPair
    exact (isBigO_finsum fun x => remDensity_line_isBigO χ e _ _ _ x).const_mul_left _
  have hR0 : gridPair (hN N) (fun x =>
        remDensity χ (hN N) e (fun y => toA0 (flatConn lam) y + (0 : ℝ) • toA0 δ y)
          (fun i y => (0 : ℝ) • toA δ i y) x) = 0 := by
    obtain ⟨C, hC⟩ := hR.bound
    have := hC.self_of_nhds
    simpa using this
  have h0 : phaseLagr χ 0 e P (flatConn lam) = 0 := by
    have := hline 0
    simp only [zero_smul, add_zero] at this
    rw [this]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, zero_add]
    simpa using hR0
  have hO : (fun s : ℝ => phaseLagr χ 0 e P (flatConn lam + s • δ) -
      phaseLagr χ 0 e P (flatConn lam)) =O[𝓝 0] fun s => s ^ 2 := by
    simp only [h0, sub_zero, hline]
    refine IsBigO.add ?_ hR
    exact ((isBigO_refl (fun s : ℝ => s ^ 2) (𝓝 0)).const_mul_left
      (gridPair (hN N) (q2den χ e (toA0 δ) (toA δ)))).congr_left fun s => by ring
  have hder : HasDerivAt (fun s : ℝ => phaseLagr χ 0 e P (flatConn lam + s • δ)) 0 0 := by
    rw [hasDerivAt_iff_isLittleO]
    simp only [smul_zero, sub_zero, zero_smul, add_zero]
    refine hO.trans_isLittleO ?_
    simpa using (isLittleO_pow_id (by norm_num : 1 < 2) : (fun s : ℝ => s ^ 2) =o[𝓝 0] id)
  have hline' : HasDerivAt (fun s : ℝ => phaseLagr χ 0 e P (flatConn lam + s • δ))
      (fderiv ℝ (phaseLagr χ 0 e P) (flatConn lam) δ) 0 := by
    have hl : HasDerivAt (fun s : ℝ => flatConn lam + s • δ) δ 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const δ).const_add (flatConn lam)
    have hd' : HasFDerivAt (phaseLagr χ 0 e P) (fderiv ℝ (phaseLagr χ 0 e P) (flatConn lam))
        (flatConn lam + (0 : ℝ) • δ) := by simpa using hd.hasFDerivAt
    exact hd'.comp_hasDerivAt (0 : ℝ) hl
  simpa using hline'.unique hder

/-- The stationary row vanishes at the flat-slice connection. -/
theorem statRow_flatConn (χ : ℝ) (lam : Lam N) :
    statRow χ 0 (coframeField sqrtTriad ((flatMet N, lam.1, lam.2) : ParF N))
      (piDot χ sqrtTriad (flatMet N) (lieV lam.2)) (flatConn lam) = 0 := by
  unfold statRow LocalSumGradient.siteGrad
  rw [fderiv_phaseLagr_flatConn]
  funext y
  simp

/-! ### Linearity and continuity in the multipliers -/

theorem nJet_add (n n' : Site N → ℝ) (x : Site N) : nJet (n + n') x = nJet n x + nJet n' x := by
  funext j; simp [nJet, map_add]

theorem nJet_smul (c : ℝ) (n : Site N → ℝ) (x : Site N) : nJet (c • n) x = c • nJet n x := by
  funext j; simp [nJet, map_smul]

theorem bJet_add (β β' : Site N → Fin 3 → ℝ) (x : Site N) :
    bJet (β + β') x = bJet β x + bJet β' x := by
  funext j q; simp [bJet, map_add]

theorem bJet_smul (c : ℝ) (β : Site N → Fin 3 → ℝ) (x : Site N) :
    bJet (c • β) x = c • bJet β x := by
  funext j q; simp [bJet, map_smul]

/-- `flatConn` as a linear map of the multipliers. -/
def flatConnL : Lam N →ₗ[ℝ] Conn N where
  toFun := flatConn
  map_add' lam lam' := by
    funext x μ k
    cases μ using Fin.cases with
    | zero =>
      simp only [flatConn, Fin.cases_zero, Prod.fst_add, Prod.snd_add, nJet_add, bJet_add,
        Pi.add_apply]
      fin_cases k <;> simp [a0Vec] <;> ring
    | succ i => simp [flatConn]
  map_smul' c lam := by
    funext x μ k
    cases μ using Fin.cases with
    | zero =>
      simp only [flatConn, Fin.cases_zero, Prod.smul_fst, Prod.smul_snd, nJet_smul, bJet_smul,
        Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
      fin_cases k <;> simp [a0Vec] <;> ring
    | succ i => simp [flatConn]

/-- `lieV` as a linear map of the shift. -/
def lieVL : (Site N → Fin 3 → ℝ) →ₗ[ℝ] MetF N where
  toFun := lieV
  map_add' β β' := by
    funext x k; simp only [lieV, bJet_add, Pi.add_apply]; fin_cases k <;> simp [lieVec] <;> ring
  map_smul' c β := by
    funext x k; simp only [lieV, bJet_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    fin_cases k <;> simp [lieVec] <;> ring

theorem continuous_flatConn : Continuous (flatConn (N := N)) :=
  (flatConnL (N := N)).continuous_of_finiteDimensional

theorem continuous_lieV : Continuous (lieV (N := N)) :=
  (lieVL (N := N)).continuous_of_finiteDimensional

theorem continuous_flatCfg : Continuous (flatCfg (N := N)) := by
  unfold flatCfg
  exact (continuous_const.prodMk (continuous_fst.prodMk continuous_snd)).prodMk
    (continuous_lieV.comp continuous_snd)

theorem nJet_const (x : Site N) : nJet (fun _ : Site N => (1 : ℝ)) x = 0 := by
  funext j; simp [nJet, pd_const]

theorem bJet_zero (x : Site N) : bJet (fun _ : Site N => (0 : Fin 3 → ℝ)) x = 0 := by
  funext j q; simp [bJet, pd_const]

theorem flatConn_lamE : flatConn (lamE N) = 0 := by
  funext x μ k
  cases μ using Fin.cases with
  | zero =>
    simp only [flatConn, lamE, Fin.cases_zero, nJet_const, bJet_zero]
    fin_cases k <;> simp [a0Vec]
  | succ i => simp [flatConn]

theorem lieV_zero : lieV (fun _ : Site N => (0 : Fin 3 → ℝ)) = 0 := by
  funext x k; simp only [lieV, bJet_zero]; fin_cases k <;> simp [lieVec]

theorem flatCfg_lamE : flatCfg (lamE N) = zFlat N := by
  simp [flatCfg, lamE, lieV_zero, zFlat, refMult]

/-- When the spatial connection vanishes the phase Lagrangian does not see `∂_tΠ`. -/
theorem phaseLagr_P_indep (χ Λ : ℝ) (e : Site N → M4) (P P' : Fin 3 → Site N → M4) (A : Conn N)
    (hA : toA A = 0) : phaseLagr χ Λ e P A = phaseLagr χ Λ e P' A := by
  unfold phaseLagr nfDensityPh
  simp [hA, pairing_zero_right]

/-- A derivative along a direction in which the function is constant vanishes. -/
theorem fderiv_dir_eq_zero_of_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x v : E} (hf : HasFDerivAt f f' x)
    (hc : ∀ t : ℝ, f (x + t • v) = f x) : f' v = 0 := by
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hf' : HasFDerivAt f f' (x + (0 : ℝ) • v) := by simpa using hf
  have h1 := hf'.comp_hasDerivAt (0 : ℝ) hl
  have h2 : HasDerivAt (fun t : ℝ => f (x + t • v)) 0 0 := by
    simp only [hc]; exact hasDerivAt_const _ _
  simpa using h1.unique h2

/-! ### The flat slice -/

section Chart

variable {χ R : ℝ} {U : Set (CoP N)} (hU : FlatChart χ R U) (hχ : χ ≠ 0)
include hU hχ

set_option maxHeartbeats 1000000 in
/-- **The stationary connection on the flat slice**: for `(N, β)` near `(1, 0)`,
`𝒜_h((I, N, β), L_β I) = flatConn (N, β)` (no spatial part). -/
theorem Sfun_flatCfg : ∀ᶠ lam in 𝓝 (lamE N), Sfun χ R (flatCfg lam) = flatConn lam := by
  set c₀ := 2 * |χ| / 3 with hc₀def
  have hc₀ : 0 < c₀ := by have := abs_pos.2 hχ; positivity
  obtain ⟨ε₁, hε₁, huniq⟩ := stationary_connection_gradient_exists_unique χ 0 2 (c₀ / 2)
    (by positivity)
  set r : ℝ := ε₁ / hN N with hr
  have hh := hN_pos (N := N)
  have hrpos : 0 < r := div_pos hε₁ hh
  have hhr : hN N * r ≤ ε₁ := by rw [hr, mul_div_cancel₀ _ hh.ne']
  have hf0 : fPh χ (ofCo (flatCo N)).1 (ofCo (flatCo N)).2 = 0 := by
    rw [ofCo_flatCo]; exact fPh_const_zero χ 1
  obtain ⟨U', hU'o, hq₀, he, hC, hf⟩ := exists_open_chartCo (N := N) χ 2 c₀ r hc₀ (flatCo N)
    (fun x => by rw [ofCo_flatCo]; simp)
    (fun A => by rw [ofCo_flatCo]; exact cartanOp_flat_lower_bound_explicit χ hχ A)
    (by rw [hf0, norm_zero]; positivity)
  have hcfg : Tendsto (flatCfg (N := N)) (𝓝 (lamE N)) (𝓝 (zFlat N)) := by
    rw [← flatCfg_lamE]; exact continuous_flatCfg.continuousAt
  have hqU : ∀ᶠ lam in 𝓝 (lamE N), toCo (dataMap χ (flatCfg lam)) ∈ U' := by
    have hc : ContinuousAt (fun z : ParF N × MetF N => toCo (dataMap χ z)) (zFlat N) :=
      (analyticAt_toCo_dataMap (N := N) χ).continuousAt
    have hmem : U' ∈ 𝓝 (toCo (dataMap χ (zFlat N))) := by
      rw [toCo_dataMap_flat]; exact hU'o.mem_nhds hq₀
    exact hcfg.eventually (hc.eventually hmem)
  have hSball : ∀ᶠ lam in 𝓝 (lamE N), Sfun χ R (flatCfg lam) ∈ closedBall (0 : Conn N) r := by
    have hc := (analyticAt_Sfun hU).continuousAt
    have hmem : closedBall (0 : Conn N) r ∈ 𝓝 (Sfun χ R (zFlat N)) := by
      rw [Sfun_flat hU]; exact closedBall_mem_nhds _ hrpos
    exact hcfg.eventually (hc.eventually hmem)
  have hSst : ∀ᶠ lam in 𝓝 (lamE N), statRow χ 0 (dataMap χ (flatCfg lam)).1
      (dataMap χ (flatCfg lam)).2 (Sfun χ R (flatCfg lam)) = 0 :=
    hcfg.eventually ((eventually_stationary hU).mono fun z hz => hz.1)
  have hFball : ∀ᶠ lam in 𝓝 (lamE N), flatConn lam ∈ closedBall (0 : Conn N) r := by
    have hmem : closedBall (0 : Conn N) r ∈ 𝓝 (flatConn (lamE N)) := by
      rw [flatConn_lamE]; exact closedBall_mem_nhds _ hrpos
    exact continuous_flatConn.continuousAt.eventually hmem
  filter_upwards [hqU, hSball, hSst, hFball] with lam hq hS hSz hF
  have he' := he _ hq
  have hC' := hC _ hq
  have hf' := (hf _ hq).le
  rw [ofCo_toCo] at he' hC' hf'
  obtain ⟨hex, -, -⟩ := huniq N r (dataMap χ (flatCfg lam)).1 (dataMap χ (flatCfg lam)).2
    hrpos.le hhr he' hC' hf'
  have hF0 : statRow χ 0 (dataMap χ (flatCfg lam)).1 (dataMap χ (flatCfg lam)).2
      (flatConn lam) = 0 := statRow_flatConn χ lam
  exact hex.unique ⟨hS, hSz⟩ ⟨hF, hF0⟩

/-- **The momentum vanishes on the flat slice**: `D_V𝓛°_h((I, N, β), L_β I) = 0`. -/
theorem velMom_flatCfg : ∀ᶠ lam in 𝓝 (lamE N),
    velMom (redLagr χ 0 sqrtTriad (statAst χ R)) (flatCfg lam) = 0 := by
  have hcfg : Tendsto (flatCfg (N := N)) (𝓝 (lamE N)) (𝓝 (zFlat N)) := by
    rw [← flatCfg_lamE]; exact continuous_flatCfg.continuousAt
  have hS := analyticAt_Sfun hU
  have hpair : ContinuousAt (fun z : ParF N × MetF N => (z, Sfun χ R z)) (zFlat N) :=
    continuousAt_id.prodMk hS.continuousAt
  have hPev := (analyticAt_PhiL (N := N) χ).eventually_analyticAt
  rw [← pair_Sfun_flat hU] at hPev
  filter_upwards [hcfg.eventually (eventually_fderiv_redLagr hU), Sfun_flatCfg hU hχ,
    hcfg.eventually (hpair.eventually hPev)] with lam h1 h2 h3
  refine ContinuousLinearMap.ext fun W => ?_
  change fderiv ℝ (redLagr χ 0 sqrtTriad (statAst χ R)) (flatCfg lam) (0, W) = 0
  rw [h1, h2]
  rw [h2] at h3
  have hconst : ∀ t : ℝ, PhiL χ ((flatCfg lam, flatConn lam) + t • (((0 : ParF N), W), (0 : Conn N)))
      = PhiL χ (flatCfg lam, flatConn lam) := by
    intro t
    have he : ((flatCfg lam, flatConn lam) + t • (((0 : ParF N), W), (0 : Conn N)) :
        (ParF N × MetF N) × Conn N) = (((flatCfg lam).1, (flatCfg lam).2 + t • W), flatConn lam) := by
      ext <;> simp
    rw [he]
    exact phaseLagr_P_indep χ 0 _ _ _ _ (toA_flatConn lam)
  exact fderiv_dir_eq_zero_of_const h3.differentiableAt.hasFDerivAt hconst

/-- **The Legendre velocity on the flat slice**: at `((I, N, β), π = 0)` with `(N, β)` near
`(1, 0)`, `V_h = L_β I`. -/
theorem legendreVel_flatCfg : ∀ᶠ lam in 𝓝 (lamE N),
    legendreVel χ 0 sqrtTriad (statAst χ R) (zFlat N) (flatCfg lam).1 0 = lieV lam.2 := by
  have hc := legendreChart_flat hU hχ
  have hπ₀ : pairCov (0 : MetF N) = velMom (redLagr χ 0 sqrtTriad (statAst χ R)) (zFlat N) := by
    rw [velMom_flat hU hχ, map_zero]
  obtain ⟨-, -, -, h4, -⟩ := canonical_legendre χ 0 hc hπ₀
  have hw : Tendsto (fun lam : Lam N => ((((flatCfg lam).1, (0 : MetF N)), (flatCfg lam).2) :
      (ParF N × MetF N) × MetF N)) (𝓝 (lamE N)) (𝓝 (((zFlat N).1, 0), (zFlat N).2)) := by
    have hcont : Continuous (fun lam : Lam N => ((((flatCfg lam).1, (0 : MetF N)),
        (flatCfg lam).2) : (ParF N × MetF N) × MetF N)) :=
      ((continuous_fst.comp continuous_flatCfg).prodMk continuous_const).prodMk
        (continuous_snd.comp continuous_flatCfg)
    have h0 : ((((flatCfg (lamE N)).1, (0 : MetF N)), (flatCfg (lamE N)).2) :
        (ParF N × MetF N) × MetF N) = (((zFlat N).1, 0), (zFlat N).2) := by rw [flatCfg_lamE]
    rw [← h0]; exact hcont.continuousAt
  filter_upwards [hw.eventually h4, velMom_flatCfg hU hχ] with lam h hv
  refine h.1 fun V => ?_
  change velMom (redLagr χ 0 sqrtTriad (statAst χ R)) (flatCfg lam) V = _
  rw [hv]
  simp [pairH, symMat]

/-- **The flat slice of the literal canonical Hamiltonian**: for `(N, β)` near `(1, 0)`, at
`(γ, π) = (I, 0)` the Legendre velocity is `L_β I` and the stationary connection there is
`flatConn (N, β)`, whose spatial part vanishes. -/
theorem flat_slice : ∀ᶠ lam in 𝓝 (lamE N),
    legendreVel χ 0 sqrtTriad (statAst χ R) (zFlat N) (flatCfg lam).1 0 = lieV lam.2 ∧
      Sfun χ R ((flatCfg lam).1,
        legendreVel χ 0 sqrtTriad (statAst χ R) (zFlat N) (flatCfg lam).1 0) = flatConn lam ∧
      toA (Sfun χ R ((flatCfg lam).1,
        legendreVel χ 0 sqrtTriad (statAst χ R) (zFlat N) (flatCfg lam).1 0)) = 0 := by
  filter_upwards [legendreVel_flatCfg hU hχ, Sfun_flatCfg hU hχ] with lam h1 h2
  have h3 : Sfun χ R ((flatCfg lam).1,
      legendreVel χ 0 sqrtTriad (statAst χ R) (zFlat N) (flatCfg lam).1 0) = flatConn lam := by
    rw [h1]; exact h2
  exact ⟨h1, h3, by rw [h3]; exact toA_flatConn lam⟩

end Chart

end RenewalGeometry.ExactPhaseAction.ShiftWard
