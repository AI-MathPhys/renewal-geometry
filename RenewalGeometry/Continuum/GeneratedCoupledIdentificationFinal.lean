/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedCoupledIdentification
import RenewalGeometry.Continuum.GeneratedDiracStressNoether

/-!
# `lem:generated-physical-identification` for back-reacting spinors: closed form and instance

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`,
coupled spinors.

* **`generated_physical_identification_coupledDirac`** — the coupled identification with the
  Noether identities discharged: for theory data with smooth sources, back-reacting Dirac data
  (`GenDStress.CoupledDirac`) and the Clifford unitarity relations, the current Noether identity
  (`GenDiracCur.currentNoether_of_variationalDirac`) and the on-shell stress Noether identity with
  the Dirac stress (`GenDSN.stressConservation_of_coupledDirac`) hold, so
  `GenCplId.generated_physical_identification_coupled` applies.
* Non-vacuity: `quatN` — quaternionic Einstein–Yang–Mills–Higgs–Dirac data on `ℍ × ℍ` with
  gauge-neutral spinors, a scalar Yukawa coupling and the **symmetric Dirac stress** (nonzero:
  `quatN_stress_ne`), smooth sources (`quatN_smooth`) and unitary forms (`quatN_unitary`).

Disclosure: for gauge-charged spinors the Dirac current `J^D` involves the adapted frame
`frU(g⁻¹)`, which is smooth only on Lorentzian charts, while `SMSmooth` asks for global smoothness
of the sources in `(g, g⁻¹)`; the charged quaternionic data `GenDStress.quatSMT` are therefore
`CoupledDirac` but not `SMSmooth`, and the instance given here has neutral spinors (the coupling
to the metric through the Dirac stress and to the Higgs field through the Yukawa source is kept).
-/

open Filter Topology Set
open scoped BigOperators ContDiff NNReal

noncomputable section

namespace RenewalGeometry.GenCplIdF

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk QLEnergy KatoGalerkin FrameCurvature HarmonicDefect
  ActualJetWriter ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge ActualJetBridge
  ActualJetState ActualJetCompleteForcing ActualJetRecon ActualJetKato GenConstraint GenGauss
  GenDiracCur

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

/-! ### The closed coupled identification -/

section Main

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable {SM : SMData (MatLie m) V S S'} {bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ}
  {bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ} {bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ}

/-- **`lem:generated-physical-identification` for back-reacting spinors (`Σ = 𝕋³`), closed**:
the hypotheses on the theory data are smooth sources, back-reacting Dirac data
(`GenDStress.CoupledDirac`: the symmetric Dirac stress, the Dirac current and the Yukawa source
of a Dirac pairing) and unitary forms; the current and stress Noether identities are proved
(`GenDiracCur.currentNoether_of_variationalDirac`, `GenDSN.stressConservation_of_coupledDirac`). -/
theorem generated_physical_identification_coupledDirac (hS : SMSmooth SM)
    (hU : UnitaryForms SM bG bV bS bS') (hC : GenDStress.CoupledDirac SM) {mm q : ℕ}
    (hm : (3 : ℝ) / 2 < mm) (hq : 2 * mm + 1 ≤ q) (hq2 : mm + 2 ≤ q) :
    ∃ κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ),
      (∀ v w, ipP bG bV bS bS' (κ.symm v) (κ.symm w) = ∑ i, v i * w i) ∧
      ∀ K₀ K : Set (Fin (dimS m V S S') → ℝ), IsCompact K → (∀ v ∈ K, MetChart (κ.symm v).1) →
      ∀ δ : ℝ, 0 < δ → Metric.cthickening δ K₀ ⊆ K →
      ∃ (A : Fin 3 → Fin (dimS m V S S') → Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ) (F : Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ),
        (∀ i a b, ContDiff ℝ ∞ (A i a b)) ∧ (∀ i a b v, A i a b v = A i b a v) ∧
        (∀ a, ContDiff ℝ ∞ (F a)) ∧
        (∀ v ∈ K, ∀ j a (w : Fin (dimS m V S S') → ℝ), ∑ b, A j a b v * w b =
          κ (toS (princ (frameU (ginvOf (κ.symm v).1.1)) SM.D.Fr SM.Db.Fr j
            (ofP (κ.symm w)))) a) ∧
        (∀ v ∈ K, ∀ a, F a v = κ (toS (Fsys SM (ofP (κ.symm v)))) a) ∧
        ∀ R₀ : ℝ, 0 ≤ R₀ → ∃ T > 0, ∀ U₀ : Fin (dimS m V S S') → ST 3 → ℝ,
          GenPhysIdClosed.ConstrainedData SM κ U₀ → (∀ b, ContDiff ℝ ∞ (U₀ b)) →
          (∀ b, IsSPeriodic (U₀ b)) → energyQ q U₀ 0 ≤ R₀ ^ 2 →
          (∀ y, (fun c => U₀ c (Fin.cons 0 y)) ∈ K₀) →
          ∃ (U : Fin (dimS m V S S') → ST 3 → ℝ) (P : Fin (dimS m V S S') → Fin 3 → ST 3 → ℝ),
            TwoSidedSol A F U₀ T U P ∧
            ∃ (z : Tuple m V S S') (t₁ : ℝ), 0 < t₁ ∧ ∀ x ∈ slab 0 t₁,
              (∀ b, U b x = κ (stateF SM z x) b) ∧
                bosF SM z x = 0 ∧ dirF SM z x = 0 ∧ CF z x = 0 :=
  GenCplId.generated_physical_identification_coupled hS hU hC
    (currentNoether_of_variationalDirac hC.toVariationalDirac)
    (GenDSN.stressConservation_of_coupledDirac hC) hm hq hq2

end Main

/-! ### Non-vacuity: gauge-neutral quaternionic data with the Dirac stress -/

section Quat

open GenDStress GenNoether

/-- Gauge-neutral quaternionic Dirac data (`ρ = 0`, scalar Yukawa coupling). -/
def diracN (s : ℝ) (hs : s ^ 2 = 1) : DiracData (MatLie 1) (MatLie 1) SQ where
  Fr := frQ s hs
  ρ := 0
  ρ_lie X Y := by simp
  m0 := 0
  L := LQ s
  lorentz := ⟨lorentzSign_zero, lorentzSign_succ⟩
  comm X b := by simp
  mass_cl w c d := (diracQ s hs).mass_cl w c d
  mass_eq X w := by
    rw [lie_one, map_zero]
    simp

/-- **Quaternionic Einstein–Yang–Mills–Higgs–Dirac data with gauge-neutral, back-reacting
spinors**: the symmetric Dirac stress of the Euclidean pairing, the (vanishing) Dirac current of
neutral spinors and the scalar Yukawa source. -/
def quatN : SMData (MatLie 1) (MatLie 1) SQ SQ where
  Λ := 0
  κ := 1
  D := diracN 1 (by norm_num)
  Db := diracN (-1) (by norm_num)
  Jcur := fun g gi H DH ψ ψb ν =>
    (2 : ℝ) • (0 : MatLie 1 →ₗ[ℝ] MatLie 1 →ₗ[ℝ] MatLie 1) H (DH ν) +
      diracCur (0 : SQ →ₗ[ℝ] SQ →ₗ[ℝ] MatLie 1) (diracN 1 (by norm_num)).Fr g gi ψ ψb ν
  SH := fun _ _ H ψ ψb => (2 * 0 * (traceForm 1 H H - 0 ^ 2)) • H + yukQ ψb ψ
  ipG := traceForm 1
  ipV := traceForm 1
  lamH := 0
  vH := 0
  TD := symTD (diracN 1 (by norm_num)) PQ

/-- The neutral data are variational Dirac data. -/
def quatNVar : VariationalDirac quatN where
  P := PQ
  c_tr := quatVariationalDirac.c_tr
  ρ_tr X φ x := by
    show PQ ((0 : MatLie 1 →ₗ[ℝ] Module.End ℝ SQ) X φ) x =
      -PQ φ ((0 : MatLie 1 →ₗ[ℝ] Module.End ℝ SQ) X x)
    simp
  m0_tr := quatVariationalDirac.m0_tr
  L_tr := quatVariationalDirac.L_tr
  ipG_nondeg := quatVariationalDirac.ipG_nondeg
  μS := 0
  μS_dual X φ x := by
    show traceForm 1 X ((0 : SQ →ₗ[ℝ] SQ →ₗ[ℝ] MatLie 1) φ x) =
      PQ φ ((0 : MatLie 1 →ₗ[ℝ] Module.End ℝ SQ) X x)
    simp
  μS_equiv X φ x := by simp
  μ := 0
  moment := quatVariationalDirac.moment
  alt := quatVariationalDirac.alt
  equiv := quatVariationalDirac.equiv
  yuk := yukQ
  yuk_dual := quatVariationalDirac.yuk_dual
  J_eq := fun _ _ _ _ _ _ _ => rfl
  SH_eq := fun _ _ _ _ _ => rfl

/-- **The neutral quaternionic data are back-reacting Dirac data.** -/
def quatNCoupled : CoupledDirac quatN where
  toVariationalDirac := quatNVar
  ipG_symm X Y := by
    show traceForm 1 X Y = traceForm 1 Y X
    rw [traceForm_one, traceForm_one, mul_comm]
  ipG_inv X Y Z := by
    rw [lie_one, lie_one]
    simp
  ipV_symm u w := by
    show traceForm 1 u w = traceForm 1 w u
    rw [traceForm_one, traceForm_one, mul_comm]
  TD_eq := rfl

theorem contDiff_bilin {E₁ E₂ E₃ F : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [FiniteDimensional ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : E₁ →ₗ[ℝ] E₂ →ₗ[ℝ] F) {f : E₃ → E₁} {g : E₃ → E₂} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (fun p => B (f p) (g p)) := by
  set L : E₁ →L[ℝ] (E₂ →L[ℝ] F) := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (E₂ →ₗ[ℝ] F) ≃ₗ[ℝ] (E₂ →L[ℝ] F)).toLinearMap ∘ₗ B)
  have e : (fun p => B (f p) (g p)) = fun p => L (f p) (g p) := rfl
  rw [e]
  exact (L.contDiff.comp hf).clm_apply hg

/-- **The neutral quaternionic data have smooth sources.** -/
theorem quatN_smooth : SMSmooth quatN where
  J ν := by
    have : (fun p : Met × Met × MatLie 1 × (Fin 4 → MatLie 1) × SQ × SQ =>
        quatN.Jcur p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 ν) = fun _ => 0 := by
      funext p
      show (2 : ℝ) • (0 : MatLie 1 →ₗ[ℝ] MatLie 1 →ₗ[ℝ] MatLie 1) _ _ +
        diracCur (0 : SQ →ₗ[ℝ] SQ →ₗ[ℝ] MatLie 1) _ _ _ _ _ ν = 0
      simp [diracCur]
    rw [this]
    exact contDiff_const
  SH := by
    have : (fun p : Met × Met × MatLie 1 × SQ × SQ =>
        quatN.SH p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) =
        fun p => yukQ p.2.2.2.2 p.2.2.2.1 := by
      funext p
      show (2 * 0 * (traceForm 1 _ _ - 0 ^ 2)) • _ + yukQ _ _ = _
      simp
    rw [this]
    exact contDiff_bilin yukQ (by fun_prop) (by fun_prop)
  P2 A B := by
    have : (fun p : MatLie 1 × SQ × SQ => quatN.TD.P'' A B p.1 p.2.1 p.2.2) =
        fun p => -etaL A B * (p.1 0 0 * PQ p.2.1 p.2.2) := by
      funext p
      show yukP (diracN 1 _) PQ A B p.1 p.2.1 p.2.2 = _
      unfold yukP
      simp only [LinearMap.smul_apply, LinearMap.compl₂_apply, smul_eq_mul, SpinorProlongation.mass]
      show -etaL A B * PQ p.2.1 ((0 + (1 * p.1 0 0) • (1 : Module.End ℝ SQ)) p.2.2) = _
      simp
    rw [this]
    have h1 : ContDiff ℝ ∞ (fun p : MatLie 1 × SQ × SQ => p.1 0 0) := by
      have : ContDiff ℝ ∞ (fun M : MatLie 1 => M 0 0) :=
        (contDiff_apply ℝ ℝ (0 : Fin 1)).comp (contDiff_apply ℝ (Fin 1 → ℝ) (0 : Fin 1))
      exact this.comp contDiff_fst
    exact contDiff_const.mul (h1.mul (contDiff_bilin PQ (by fun_prop) (by fun_prop)))

theorem dotQ_comm (a b : Quaternion ℝ) : dotQ a b = dotQ b a := by
  unfold dotQ; ring

theorem PQ_symm (x y : SQ) : PQ x y = PQ y x := by
  rw [PQ_apply, PQ_apply, dotQ_comm x.1, dotQ_comm x.2]

theorem PQ_pos (z : SQ) (hz : z ≠ 0) : 0 < PQ z z := by
  rw [PQ_apply]
  unfold dotQ
  by_contra h
  push Not at h
  apply hz
  have h1 : z.1.re = 0 ∧ z.1.imI = 0 ∧ z.1.imJ = 0 ∧ z.1.imK = 0 ∧ z.2.re = 0 ∧ z.2.imI = 0 ∧
      z.2.imJ = 0 ∧ z.2.imK = 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg z.1.re, sq_nonneg z.1.imI,
      sq_nonneg z.1.imJ, sq_nonneg z.1.imK, sq_nonneg z.2.re, sq_nonneg z.2.imI,
      sq_nonneg z.2.imJ, sq_nonneg z.2.imK]
  obtain ⟨a1, a2, a3, a4, b1, b2, b3, b4⟩ := h1
  exact Prod.ext (Quaternion.ext _ _ a1 a2 a3 a4) (Quaternion.ext _ _ b1 b2 b3 b4)

/-- **The neutral quaternionic data carry unitary forms** (Frobenius forms on the algebra and the
Higgs space, the Euclidean pairing on the spinors). -/
theorem quatN_unitary : UnitaryForms quatN (frob 1) (frob 1) PQ PQ where
  symG x y := by simp only [frob_apply, mul_comm]
  symV x y := by simp only [frob_apply, mul_comm]
  symS := PQ_symm
  symS' := PQ_symm
  posG := frob_pos
  posV := frob_pos
  posS := PQ_pos
  posS' := PQ_pos
  c0 x y := by
    show PQ (swapQ x) y = PQ x (swapQ y)
    simp only [PQ_apply, swapQ_apply, dotQ]; ring
  ci i x y := by
    fin_cases i
    all_goals
      show PQ (diagQ 1 _ x) y = -PQ x (diagQ 1 _ y)
      simp only [PQ_apply, diagQ_apply]
      simp only [dotQ, Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul,
        Quaternion.imK_smul, Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg,
        Quaternion.imK_neg, smul_eq_mul, Quaternion.re_mul, Quaternion.imI_mul,
        Quaternion.imJ_mul, Quaternion.imK_mul, qU_re, qU_imI, qU_imJ, qU_imK]
      simp
      ring
  c0b x y := by
    show PQ (swapQ x) y = PQ x (swapQ y)
    simp only [PQ_apply, swapQ_apply, dotQ]; ring
  cib i x y := by
    fin_cases i
    all_goals
      show PQ (diagQ (-1) _ x) y = -PQ x (diagQ (-1) _ y)
      simp only [PQ_apply, diagQ_apply]
      simp only [dotQ, Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul,
        Quaternion.imK_smul, Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg,
        Quaternion.imK_neg, smul_eq_mul, Quaternion.re_mul, Quaternion.imI_mul,
        Quaternion.imJ_mul, Quaternion.imK_mul, qU_re, qU_imI, qU_imJ, qU_imK]
      simp
      ring

/-- **The Dirac stress of the neutral data is nonzero**: for `Ψ = (1, 0)` with the normal jet
`X_0 = (1, 0)`, `X_a = 0`, `X̄ = 0` and `Ψ̄ = (q₁, 0)`, `T_{01} = -¼`. -/
theorem quatN_stress_ne :
    quatN.TD.frame 0 ((1 : Quaternion ℝ), 0)
      (fun A => if A = 0 then ((1 : Quaternion ℝ), 0) else 0) (qU 0, 0) 0 0 1 = -(1 / 4 : ℝ) := by
  show (symTD quatN.D PQ).frame _ _ _ _ _ 0 1 = _
  rw [frame_symTD]
  have h : etaL 0 1 = 0 := by simp [etaL]
  rw [h, zero_mul, add_zero]
  unfold kinT
  have e1 : quatN.D.Fr.c 1 ((1 : Quaternion ℝ), (0 : Quaternion ℝ)) = (qU 0, 0) := by
    show diagQ 1 0 _ = _
    simp
  simp only [Fin.one_eq_zero_iff, OfNat.ofNat_ne_zero, if_false, if_true, map_zero,
    LinearMap.zero_apply, Pi.zero_apply, e1]
  have z1 : (0 : Quaternion ℝ).re = 0 := rfl
  have z2 : (0 : Quaternion ℝ).imI = 0 := rfl
  have z3 : (0 : Quaternion ℝ).imJ = 0 := rfl
  have z4 : (0 : Quaternion ℝ).imK = 0 := rfl
  simp [PQ_apply, dotQ, z1, z2, z3, z4]

/-- **Non-vacuity of `generated_physical_identification_coupledDirac`**: back-reacting Dirac data
with smooth sources, unitary forms, a nonzero spinor space and a nonzero Dirac stress exist, and
the coupled identification applies to them. -/
theorem coupled_nonvacuous :
    Nonempty (CoupledDirac quatN) ∧ SMSmooth quatN ∧ UnitaryForms quatN (frob 1) (frob 1) PQ PQ ∧
      Nontrivial SQ ∧ quatN.TD.frame 0 ((1 : Quaternion ℝ), 0)
        (fun A => if A = 0 then ((1 : Quaternion ℝ), 0) else 0) (qU 0, 0) 0 0 1 ≠ 0 :=
  ⟨⟨quatNCoupled⟩, quatN_smooth, quatN_unitary, inferInstance, by rw [quatN_stress_ne]; norm_num⟩

example : ∃ κ : StateP 1 (MatLie 1) SQ SQ ≃ₗ[ℝ] (Fin (dimS 1 (MatLie 1) SQ SQ) → ℝ),
    ∀ v w, ipP (frob 1) (frob 1) PQ PQ (κ.symm v) (κ.symm w) = ∑ i, v i * w i := by
  obtain ⟨κ, hκ, -⟩ := generated_physical_identification_coupledDirac quatN_smooth quatN_unitary
    quatNCoupled (mm := 2) (q := 5) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨κ, hκ⟩

end Quat

end RenewalGeometry.GenCplIdF
