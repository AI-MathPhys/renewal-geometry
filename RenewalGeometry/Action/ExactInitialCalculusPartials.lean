/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactInitialCalculusRows
import RenewalGeometry.Action.ExactShiftCovariance
import RenewalGeometry.Action.ExactLapseHomogeneity

/-!
# Velocity, lapse and shift partial derivatives of the phase-compatible Lagrangian
  (infrastructure for `lem:supp-initial-calculus`: the Legendre row and the four original
  lapse–shift rows of `eq:main-action-initial-constraints` as site-wise formulas;
  emergent-spacetime manuscript)

At a fixed connection `A`, the phase-compatible Lagrangian `L°(e, ∂_tΠ; A)` depends on the coframe
only through `Π_i(e(y))` and `Σ_ij(e(y))`, linearly, and on `∂_tΠ` linearly.

* `sigTerm h σ A`: the `Σ`-linear part; `phaseLagr_sub_of_piArr_eq` (exact): two coframe fields
  with the same `Π` differ in `L°` by `sigTerm` of the difference of their `Σ`'s;
  `sigTerm_single` (exact summation by parts with the skew-adjoint `δ_j`): for `σ` supported at one
  site `x`, `sigTerm = h³ [Σ_ij ⟨σ_ji, δ_j A_i⟩ + Σ_{i<j} ⟨σ_ij, [A_i, A_j] + ρ^B_ij⟩](x)`.
* `phaseLagr_Pidot_sub` (exact): `L°(e, P + tQ; A) - L°(e, P; A) = -t h³ Σ_y Σ_i ⟨Q_i, A_i⟩(y)`.
* **`fderiv_PhiL_velocity`**, **`fderiv_PhiL_lapse`**, **`fderiv_PhiL_shift`**: the partial
  derivatives of `Φ(z, A) = L°(e(z), ∂_tΠ(z); A)` in a velocity direction, in the lapse direction
  `δN = e_x` and in the shift direction `δβ = e_x ⊗ e_a`, at unit lapse and zero shift:
  `-h³ Σ_y Σ_i ⟨D_γΠ_i[δV](y), A_i(y)⟩`, `h³ conLapseLoc(x)`, `h³ conShiftLoc_a(x)`, with the
  site-wise lapse and shift rows `conLapseLoc`, `conShiftLoc` (the magnetic curvature
  `δ_iA_j - δ_jA_i + [A_i, A_j] + ρ^B_ij` contracted with `Σ_ij`, resp. its shift transport).
-/

open Filter Finset Metric
open scoped Topology

noncomputable section

namespace RenewalGeometry.ExactPhaseAction.InitialCalculus

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

set_option linter.unusedSectionVars false

open LocalSumGradient OddPhaseDerivativeReal QuadJet

variable {N : ℕ} [NeZero N]

/-! ### The `Σ`-linear part of the Lagrangian -/

/-- The magnetic curvature `[A_i, A_j] + ρ^B_ij` at a site (without the linear difference part). -/
def magRem (h : ℝ) (A : Conn N) (i j : Fin 3) (y : Site N) : M4 :=
  bracket (toA A i y) (toA A j y) +
    remB h (toA A i y) (toA A j (y + unitVec i)) (toA A i (y + unitVec j)) (toA A j y)

/-- **The `Σ`-linear part of the phase-compatible Lagrangian** at a fixed connection. -/
def sigTerm (h : ℝ) (σ : Site N → Fin 3 → Fin 3 → M4) (A : Conn N) : ℝ :=
  hN N ^ 3 * ∑ y, ((∑ i, pairing (-∑ j, pd j (fun y' => σ y' j i) y) (toA A i y)) +
    sumLt fun i j => pairing (σ y i j) (magRem h A i j y))

theorem load0Ph_congr {χ : ℝ} {e e' : Site N → M4} (hpi : ∀ y i, piArr χ (e' y) i = piArr χ (e y) i)
    (x : Site N) : load0Ph χ e' x = load0Ph χ e x := by
  unfold load0Ph
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (fun y => piArr χ (e' y) i) = fun y => piArr χ (e y) i := funext fun y => hpi y i
  rw [this]

theorem loadSpPh_sub (χ : ℝ) (e e' : Site N → M4) (i : Fin 3) (x : Site N) :
    loadSpPh χ e' i x - loadSpPh χ e i x =
      -∑ j, pd j (fun y => sigmaArr χ (e' y) j i - sigmaArr χ (e y) j i) x := by
  unfold loadSpPh
  rw [← neg_sub', ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (fun y => sigmaArr χ (e' y) j i - sigmaArr χ (e y) j i) =
      (fun y => sigmaArr χ (e' y) j i) - fun y => sigmaArr χ (e y) j i := rfl
  rw [this, map_sub]
  rfl

/-- **Coframe fields with equal `Π` differ in `L°` by the `Σ`-linear part** (exact). -/
theorem phaseLagr_sub_of_piArr_eq (χ : ℝ) {e e' : Site N → M4}
    (hpi : ∀ y i, piArr χ (e' y) i = piArr χ (e y) i) (P : Fin 3 → Site N → M4) (A : Conn N) :
    phaseLagr χ 0 e' P A - phaseLagr χ 0 e P A =
      sigTerm (hN N) (fun y i j => sigmaArr χ (e' y) i j - sigmaArr χ (e y) i j) A := by
  unfold phaseLagr gridPair sigTerm
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  have h0 := load0Ph_congr hpi y
  have hsp : ∀ i, loadSpPh χ e' i y = loadSpPh χ e i y +
      -∑ j, pd j (fun y' => sigmaArr χ (e' y') j i - sigmaArr χ (e y') j i) y := by
    intro i; rw [← loadSpPh_sub]; abel
  simp only [nfDensityPh, qc, remDensity, h0, hsp, hpi, magRem, sumLt_eq, pairing_add_left,
    pairing_add_right, pairing_sub_left, Finset.sum_add_distrib, mul_zero, zero_mul]
  ring

theorem sigTerm_smul (h c : ℝ) (σ : Site N → Fin 3 → Fin 3 → M4) (A : Conn N) :
    sigTerm h (fun y i j => c • σ y i j) A = c * sigTerm h σ A := by
  unfold sigTerm
  have hpd : ∀ (i : Fin 3) (y : Site N), (∑ j, (pd j (fun y' => c • σ y' j i) y : M4)) =
      c • ∑ j, (pd j (fun y' => σ y' j i) y : M4) := by
    intro i y
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : (fun y' => c • σ y' j i) = c • fun y' => σ y' j i := rfl
    rw [this, map_smul]
    rfl
  have hy : ∀ y, ((∑ i, pairing (-∑ j, (pd j (fun y' => c • σ y' j i) y : M4)) (toA A i y)) +
      sumLt fun i j => pairing (c • σ y i j) (magRem h A i j y)) =
      c * ((∑ i, pairing (-∑ j, (pd j (fun y' => σ y' j i) y : M4)) (toA A i y)) +
        sumLt fun i j => pairing (σ y i j) (magRem h A i j y)) := by
    intro y
    simp only [hpd, sumLt_eq, ← smul_neg, pairing_smul_left, ← Finset.mul_sum]
    ring
  rw [Finset.sum_congr rfl fun y _ => hy y, ← Finset.mul_sum]
  ring

/-- `pairingBilin` as a bilinear map for `pd_skew`. -/
theorem sum_pairing_pd (j : Fin 3) (u v : Site N → M4) :
    ∑ y, pairing (pd j u y) (v y) = -∑ y, pairing (u y) (pd j v y) :=
  pd_skew j pairingBilin u v

/-- **Summation by parts for a `Σ` supported at one site.** -/
theorem sigTerm_single (h : ℝ) (x : Site N) (s : Fin 3 → Fin 3 → M4) (A : Conn N) :
    sigTerm h (fun y i j => if y = x then s i j else 0) A =
      hN N ^ 3 * ((∑ i, ∑ j, pairing (s j i) (pd j (toA A i) x)) +
        sumLt fun i j => pairing (s i j) (magRem h A i j x)) := by
  unfold sigTerm
  congr 1
  rw [Finset.sum_add_distrib]
  congr 1
  · have key : ∀ i j : Fin 3, ∑ y : Site N, pairing (pd j (fun y' => if y' = x then s j i else
        (0 : M4)) y) (toA A i y) = -pairing (s j i) (pd j (toA A i) x) := by
      intro i j
      rw [sum_pairing_pd j (fun y' => if y' = x then s j i else (0 : M4)) (toA A i)]
      congr 1
      rw [Finset.sum_eq_single x]
      · simp
      · intro y _ hy; simp [hy, pairing_zero_left]
      · simp
    have h1 : ∀ y : Site N, (∑ i, pairing (-∑ j, (pd j (fun y' => if y' = x then s j i else
        (0 : M4)) y : M4)) (toA A i y)) = -∑ i : Fin 3, ∑ j : Fin 3, pairing (pd j (fun y' =>
          if y' = x then s j i else (0 : M4)) y) (toA A i y) := by
      intro y
      simp only [pairing_neg_left, pairing_sum_left, Finset.sum_neg_distrib]
    rw [Finset.sum_congr rfl fun y _ => h1 y, Finset.sum_neg_distrib]
    have h2 : ∑ y : Site N, ∑ i : Fin 3, ∑ j : Fin 3, pairing (pd j (fun y' => if y' = x then s j i
        else (0 : M4)) y) (toA A i y) = ∑ i : Fin 3, ∑ j : Fin 3, ∑ y : Site N, pairing (pd j
          (fun y' => if y' = x then s j i else (0 : M4)) y) (toA A i y) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    rw [h2]
    simp only [key, Finset.sum_neg_distrib, neg_neg]
  · rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy; simp [hy, sumLt_eq, pairing_zero_left]
    · simp

/-! ### The velocity dependence -/

/-- **`L°` is affine in `∂_tΠ`** (exact). -/
theorem phaseLagr_Pidot_add (χ : ℝ) (e : Site N → M4) (P Q : Fin 3 → Site N → M4) (t : ℝ)
    (A : Conn N) :
    phaseLagr χ 0 e (P + t • Q) A = phaseLagr χ 0 e P A +
      t * (-(hN N ^ 3 * ∑ y, ∑ i, pairing (Q i y) (toA A i y))) := by
  unfold phaseLagr gridPair
  have hd : ∀ y, nfDensityPh χ 0 (hN N) e (P + t • Q) (toA0 A) (toA A) y =
      nfDensityPh χ 0 (hN N) e P (toA0 A) (toA A) y + t * -(∑ i, pairing (Q i y) (toA A i y)) := by
    intro y
    simp only [nfDensityPh, Pi.add_apply, Pi.smul_apply, neg_add, pairing_add_left,
      pairing_neg_left, pairing_smul_left, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      ← Finset.mul_sum]
    ring
  rw [Finset.sum_congr rfl fun y _ => hd y, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_neg_distrib]
  ring

/-! ### Line derivatives -/

/-- A derivative along a line on which the function is affine. -/
theorem fderiv_apply_of_affine_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {p w : E} (hf : DifferentiableAt ℝ f p) {c : ℝ}
    (hline : ∀ t : ℝ, f (p + t • w) = f p + t * c) : fderiv ℝ f p w = c := by
  have h1 : HasDerivAt (fun t : ℝ => f (p + t • w)) (fderiv ℝ f p w) 0 := by
    have hl : HasDerivAt (fun t : ℝ => p + t • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add p
    have hf' : HasFDerivAt f (fderiv ℝ f p) (p + (0 : ℝ) • w) := by
      simpa using hf.hasFDerivAt
    exact hf'.comp_hasDerivAt (x := (0 : ℝ)) hl
  have h2 : HasDerivAt (fun t : ℝ => f (p + t • w)) c 0 := by
    have : (fun t : ℝ => f (p + t • w)) = fun t => f p + t * c := funext hline
    rw [this]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const c).const_add (f p)
  exact h1.unique h2

/-! ### The velocity partial derivative -/

theorem piDot_add_smul (χ : ℝ) (γ V W : MetF N) (t : ℝ) :
    piDot χ sqrtTriad γ (V + t • W) = piDot χ sqrtTriad γ V + t • piDot χ sqrtTriad γ W := by
  funext i x
  ext K L
  simp [piDot, map_add, map_smul]

/-- **The velocity partial derivative of `Φ`**: `D_VΦ(z, A)[δV] = -h³ Σ_y Σ_i ⟨D_γΠ_i[δV], A_i⟩(y)`. -/
theorem fderiv_PhiL_velocity (χ : ℝ) {z : ParF N × MetF N} {A : Conn N}
    (hd : DifferentiableAt ℝ (PhiL χ) (z, A)) (δV : MetF N) :
    fderiv ℝ (PhiL χ) (z, A) (((0 : ParF N), δV), (0 : Conn N)) =
      -(hN N ^ 3 * ∑ y, ∑ i, pairing (piDot χ sqrtTriad z.1.1 δV i y) (toA A i y)) := by
  refine fderiv_apply_of_affine_line hd fun t => ?_
  have hp : (z, A) + t • ((((0 : ParF N), δV) : ParF N × MetF N), (0 : Conn N)) =
      ((z.1, z.2 + t • δV), A) := by
    ext <;> simp
  rw [hp]
  simp only [PhiL, dataMap]
  rw [piDot_add_smul, phaseLagr_Pidot_add]

/-! ### The lapse and shift partial derivatives -/

/-- The site-wise row of a `Σ`-variation `s` concentrated at `x`. -/
def conLoc (h : ℝ) (s : Fin 3 → Fin 3 → M4) (A : Conn N) (x : Site N) : ℝ :=
  (∑ i, ∑ j, pairing (s j i) (pd j (toA A i) x)) + sumLt fun i j => pairing (s i j) (magRem h A i j x)

theorem sigTerm_smul_single (h t : ℝ) (x : Site N) (s : Fin 3 → Fin 3 → M4) (A : Conn N) :
    sigTerm h (fun y i j => t • if y = x then s i j else 0) A = t * (hN N ^ 3 * conLoc h s A x) := by
  rw [sigTerm_smul, sigTerm_single]; rfl

/-- The coframe at unit lapse, zero shift. -/
def e0 (γ : MetF N) : Site N → M4 := fun y => admCoframe (sqrtTriad (symMat (γ y))) 1 0

/-- **The lapse partial derivative of `Φ`** at unit lapse and zero shift:
`D_NΦ(z, A)[e_x] = h³ conLoc(Σ(e(x)), A)(x)`. -/
theorem fderiv_PhiL_lapse (χ : ℝ) {γ V : MetF N} {A : Conn N}
    (hd : DifferentiableAt ℝ (PhiL χ) ((refMult γ, V), A)) (x : Site N) :
    fderiv ℝ (PhiL χ) ((refMult γ, V), A) (lapseDir x, (0 : Conn N)) =
      hN N ^ 3 * conLoc (hN N) (sigmaArr χ (e0 γ x)) A x := by
  refine fderiv_apply_of_affine_line hd fun t => ?_
  have hp : ((refMult γ, V), A) + t • ((lapseDir x : ParF N × MetF N), (0 : Conn N)) =
      (((γ, fun y => 1 + t * (Pi.single x (1 : ℝ) : Site N → ℝ) y, fun _ => (0 : Fin 3 → ℝ)), V), A) := by
    ext <;> simp [refMult, lapseDir]
  rw [hp]
  have hpi : ∀ y i, piArr χ (coframeField sqrtTriad (γ, fun y => 1 + t * (Pi.single x (1 : ℝ) :
      Site N → ℝ) y, fun _ => (0 : Fin 3 → ℝ)) y) i = piArr χ (coframeField sqrtTriad (refMult γ) y) i := by
    intro y i
    simp only [coframeField, refMult]
    rw [piArr_admCoframe, piArr_admCoframe (n := 1)]
  have h := phaseLagr_sub_of_piArr_eq χ hpi (piDot χ sqrtTriad γ V) A
  have hσ : (fun y i j => sigmaArr χ (coframeField sqrtTriad (γ, fun y => 1 + t * (Pi.single x (1 : ℝ) :
      Site N → ℝ) y, fun _ => (0 : Fin 3 → ℝ)) y) i j - sigmaArr χ (coframeField sqrtTriad (refMult γ) y) i j) =
      fun y i j => t • if y = x then sigmaArr χ (e0 γ x) i j else 0 := by
    funext y i j
    simp only [coframeField, refMult, e0]
    rw [LapseHomogeneity.sigmaArr_admCoframe_lapse χ _ (1 + _)]
    by_cases hy : y = x
    · subst hy; simp [add_smul]
    · simp [hy]
  rw [hσ, sigTerm_smul_single] at h
  change phaseLagr χ 0 _ _ A = phaseLagr χ 0 _ _ A + t * _
  simp only [dataMap] at h ⊢
  have e2 : piDot χ sqrtTriad (refMult γ).1 V = piDot χ sqrtTriad γ V := rfl
  rw [e2]
  linarith

/-- **The shift partial derivative of `Φ`** at unit lapse and zero shift:
`D_{β^a}Φ(z, A)[e_x] = h³ conLoc(e_a,j Π_i - e_a,i Π_j, A)(x)`. -/
theorem fderiv_PhiL_shift (χ : ℝ) {γ V : MetF N} {A : Conn N}
    (hd : DifferentiableAt ℝ (PhiL χ) ((refMult γ, V), A)) (x : Site N) (a : Fin 3) :
    fderiv ℝ (PhiL χ) ((refMult γ, V), A) (shiftDir x a, (0 : Conn N)) =
      hN N ^ 3 * conLoc (hN N) (fun i j => (Pi.single a (1 : ℝ) : Fin 3 → ℝ) j • piArr χ (e0 γ x) i -
        (Pi.single a (1 : ℝ) : Fin 3 → ℝ) i • piArr χ (e0 γ x) j) A x := by
  refine fderiv_apply_of_affine_line hd fun t => ?_
  have hp : ((refMult γ, V), A) + t • ((shiftDir x a : ParF N × MetF N), (0 : Conn N)) =
      (((γ, fun _ => (1 : ℝ), fun y => t • (Pi.single x (Pi.single a (1 : ℝ)) : Site N → Fin 3 → ℝ) y),
        V), A) := by
    ext <;> simp [refMult, shiftDir]
  rw [hp]
  have hco : ∀ y, coframeField sqrtTriad (γ, fun _ => (1 : ℝ), fun y => t • (Pi.single x
      (Pi.single a (1 : ℝ)) : Site N → Fin 3 → ℝ) y) y = ShiftWard.shiftCo (e0 γ y)
        (t • (Pi.single x (Pi.single a (1 : ℝ)) : Site N → Fin 3 → ℝ) y) := by
    intro y
    simp only [coframeField, e0]
    rw [← ShiftWard.admCoframe_add_shift, zero_add]
  have hpi : ∀ y i, piArr χ (coframeField sqrtTriad (γ, fun _ => (1 : ℝ), fun y => t • (Pi.single x
      (Pi.single a (1 : ℝ)) : Site N → Fin 3 → ℝ) y) y) i = piArr χ (coframeField sqrtTriad (refMult γ) y) i := by
    intro y i
    rw [hco, ShiftWard.piArr_shiftCo]; rfl
  have h := phaseLagr_sub_of_piArr_eq χ hpi (piDot χ sqrtTriad γ V) A
  have hσ : (fun y i j => sigmaArr χ (coframeField sqrtTriad (γ, fun _ => (1 : ℝ), fun y => t • (Pi.single x
      (Pi.single a (1 : ℝ)) : Site N → Fin 3 → ℝ) y) y) i j - sigmaArr χ (coframeField sqrtTriad (refMult γ) y) i j) =
      fun y i j => t • if y = x then ((Pi.single a (1 : ℝ) : Fin 3 → ℝ) j • piArr χ (e0 γ x) i -
        (Pi.single a (1 : ℝ) : Fin 3 → ℝ) i • piArr χ (e0 γ x) j) else 0 := by
    funext y i j
    rw [hco, ShiftWard.sigmaArr_shiftCo]
    have hr : coframeField sqrtTriad (refMult γ) y = e0 γ y := rfl
    rw [hr]
    by_cases hy : y = x
    · subst hy; simp only [smul_sub, smul_smul, if_true, Pi.smul_apply, Pi.single_eq_same]
      simp only [smul_eq_mul]
      abel
    · simp [hy]
  rw [hσ, sigTerm_smul_single] at h
  change phaseLagr χ 0 _ _ A = phaseLagr χ 0 _ _ A + t * _
  simp only [dataMap] at h ⊢
  have e2 : piDot χ sqrtTriad (refMult γ).1 V = piDot χ sqrtTriad γ V := rfl
  rw [e2]
  linarith

end RenewalGeometry.ExactPhaseAction.InitialCalculus
