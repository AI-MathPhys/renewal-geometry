/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedDiracAction

/-!
# The first variation of the first-order Dirac density on extended 1-jets

Einstein–Standard-Model action-closure manuscript, `eq:dirac-density`, `app:generated-dynamics`.

* `chart1C`, `isOpen_chart1C`, **`contDiffOn_L1D`** — the first-order Dirac density is smooth on the
  Lorentzian chart of the extended head 1-jets;
* the line derivatives of `L1D` in the gauge, Higgs, spinor and co-spinor directions
  (`hasDerivAt_L1D_gauge`, `hasDerivAt_L1D_higgs`, `hasDerivAt_L1D_psi`, `hasDerivAt_L1D_psib`);
* **`fderiv_L1D_eq`** — the complete first variation of `L1D` at a chart 1-jet with symmetric
  metric jets, in a direction with symmetric metric jets: the Hilbert stress and the local Lorentz
  terms of the metric direction (`GenDAct.hasDerivAt_L1D_metric`), the Dirac current and Yukawa
  terms, and the spinor rows (`GenDAlg.psi_row`, `GenDAlg.psib_row`).
-/

open Finset Set Filter Topology
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenDEul

open SobolevOpen (pd)
open HarmonicDefect EHJetVariation EHFieldVariation ActualJetSystem ActualJetRecon ActualJetSmooth
  ActualJetGauge ActualJetWriter ActualJetBridge ActualJetState GenMatVar GenFOAction FrameCurvature
  ActualJetFrame GenResMaps JetCurve GenDAlg GenDFJ GenDStress GenDiracCur SpinorProlongation
  GenDAct

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable (m V S S') in
/-- The Lorentzian chart of the extended head 1-jets. -/
def chart1C : Set (HJ1C m V S S') :=
  {j | (Matrix.of j.1.1.1).det < 0 ∧ IsLorChart (ginvOf j.1.1.1)}

theorem isOpen_chart1C : IsOpen (chart1C m V S S') := by
  have hdet : Continuous fun j : HJ1C m V S S' => (Matrix.of j.1.1.1).det :=
    Continuous.matrix_det (A := fun j : HJ1C m V S S' => Matrix.of j.1.1.1) (by fun_prop)
  rw [isOpen_iff_mem_nhds]
  intro j hj
  have hc : ContinuousAt (fun y : HJ1C m V S S' => ginvOf y.1.1.1) j := by
    have : ContDiffAt ℝ ∞ (fun y : HJ1C m V S S' => ginvOf y.1.1.1) j :=
      ContDiffAt.ginvOf_fun (by fun_prop) hj.1.ne
    exact this.continuousAt
  have h1 : ∀ᶠ y in 𝓝 j, (Matrix.of y.1.1.1).det < 0 :=
    (isOpen_lt hdet continuous_const).mem_nhds hj.1
  have h2 : ∀ᶠ y in 𝓝 j, IsLorChart (ginvOf y.1.1.1) := eventually_chart hc hj.2
  filter_upwards [h1, h2] with y hy1 hy2
  exact ⟨hy1, hy2⟩

variable (SM : SMData (MatLie m) V S S') (P : S' →ₗ[ℝ] S →ₗ[ℝ] ℝ)

set_option maxHeartbeats 8000000 in
/-- **The first-order Dirac density is smooth on the chart.** -/
theorem contDiffOn_L1D : ContDiffOn ℝ ∞ (L1D SM P) (chart1C m V S S') := by
  intro j₀ hj
  refine ContDiffAt.contDiffWithinAt ?_
  have hx := hj
  have hv : ContDiffAt ℝ ∞ (fun j : HJ1C m V S S' => volM j.1.1.1) j₀ :=
    contDiffAt_volM (by fun_prop) hj.1
  have hl : ContDiffAt ℝ ∞ (fun j : HJ1C m V S S' => lagD SM.D P j.1.2.2.1 j.2.1.1
      (XsR SM.D j.1.1.1 j.1.1.2 j.1.2.1.1 j.2.1.1 j.2.1.2) j.2.2.1
      (XsR SM.Db j.1.1.1 j.1.1.2 j.1.2.1.1 j.2.2.1 j.2.2.2)) j₀ := by
    have h1 : (Matrix.of j₀.1.1.1).det ≠ 0 := hj.1.ne
    have h2 := hj.2
    simp (config := { maxSteps := 4000000 }) only [lagD, XsR, omR, frR, deR, dψR, cov,
      omegaU, Gfun, spinPart, ipg, cv1, chr, dginv, mass, Module.End.smul_def,
      LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply,
      Module.End.mul_apply]
    fun_prop (disch := first | exact h1 | exact h2)
  unfold L1D
  exact hv.mul hl

/-! ### The directions of the extended 1-jets -/

variable (m V S S') in
/-- The gauge direction `((0, 0), (X, ∂X), (0, 0))`. -/
def vA (X : Fin 4 → MatLie m) (dX : Fin 4 → Fin 4 → MatLie m) : HJ1C m V S S' :=
  (((0, 0), ((X, dX), (0, 0))), ((0, 0), (0, 0)))

variable (m V S S') in
/-- The Higgs direction. -/
def vH (η : V) (dη : Fin 4 → V) : HJ1C m V S S' :=
  (((0, 0), ((0, 0), (η, dη))), ((0, 0), (0, 0)))

variable (m V S S') in
/-- The spinor direction. -/
def vP (φ : S) (cφ : Fin 4 → S) : HJ1C m V S S' :=
  (((0, 0), ((0, 0), (0, 0))), ((φ, cφ), (0, 0)))

variable (m V S S') in
/-- The co-spinor direction. -/
def vPb (φb : S') (cφb : Fin 4 → S') : HJ1C m V S S' :=
  (((0, 0), ((0, 0), (0, 0))), ((0, 0), (φb, cφb)))

theorem decomp_dir (v : HJ1C m V S S') :
    v = vMet m V S S' v.1.1.1 v.1.1.2 + vA m V S S' v.1.2.1.1 v.1.2.1.2 + vH m V S S' v.1.2.2.1 v.1.2.2.2 +
      vP m V S S' v.2.1.1 v.2.1.2 + vPb m V S S' v.2.2.1 v.2.2.2 := by
  obtain ⟨⟨⟨k, dk⟩, ⟨X, dX⟩, ⟨η, dη⟩⟩, ⟨φ, cφ⟩, ⟨φb, cφb⟩⟩ := v
  simp [vMet, vA, vH, vP, vPb]

/-! ### Affine lines -/

theorem covX_gauge {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀] (D : DiracData (MatLie m) V S₀)
    (G : Fin 4 → Fin 4 → Fin 4 → ℝ) (g : Met) (A X : Fin 4 → MatLie m) (ψ : S₀) (Dψ : Fin 4 → S₀)
    (ε : ℝ) (B : Fin 4) :
    covX D G (aR g (A + ε • X)) ψ Dψ B = covX D G (aR g A) ψ Dψ B + ε • D.ρ (aR g X B) ψ := by
  unfold covX aR
  simp only [Pi.add_apply, Pi.smul_apply, smul_add, Finset.sum_add_distrib, map_add, map_sum,
    map_smul, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum,
    smul_comm ε]
  abel

theorem covX_psi {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀] (D : DiracData (MatLie m) V S₀)
    (G : Fin 4 → Fin 4 → Fin 4 → ℝ) (g : Met) (a : Fin 4 → MatLie m) (ψ φ : S₀)
    (cψ cφ : Fin 4 → S₀) (ε : ℝ) (B : Fin 4) :
    covX D G a (ψ + ε • φ) (dψR g (cψ + ε • cφ)) B =
      covX D G a ψ (dψR g cψ) B + ε • covX D G a φ (dψR g cφ) B := by
  unfold covX dψR
  simp only [Pi.add_apply, Pi.smul_apply, smul_add, Finset.sum_add_distrib, map_add, map_smul,
    Finset.smul_sum, smul_comm ε]
  abel

theorem hasDerivAt_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (u v : E) :
    HasDerivAt (fun ε : ℝ => u + ε • v) v 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u

/-- The Dirac Lagrangian is affine along a spinor line. -/
theorem lagD_psi_affine (H : V) (ψ φ : S) (X Xφ : Fin 4 → S) (ψb : S') (Xb : Fin 4 → S') (ε : ℝ) :
    lagD SM.D P H (ψ + ε • φ) (fun B => X B + ε • Xφ B) ψb Xb =
      lagD SM.D P H ψ X ψb Xb + ε * ((1 / 2 : ℝ) * ∑ C, lorentzSign C *
        (P ψb (SM.D.Fr.c C (Xφ C)) - P (Xb C) (SM.D.Fr.c C φ)) - P ψb (mass SM.D.m0 SM.D.L H φ)) := by
  unfold lagD
  have hsum : ∑ C, lorentzSign C * (P ψb (SM.D.Fr.c C (X C + ε • Xφ C)) -
      P (Xb C) (SM.D.Fr.c C (ψ + ε • φ))) = ∑ C, lorentzSign C * (P ψb (SM.D.Fr.c C (X C)) -
        P (Xb C) (SM.D.Fr.c C ψ)) + ε * ∑ C, lorentzSign C * (P ψb (SM.D.Fr.c C (Xφ C)) -
          P (Xb C) (SM.D.Fr.c C φ)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun C _ => ?_
    simp only [map_add, map_smul, smul_eq_mul]
    ring
  have hm : P ψb (mass SM.D.m0 SM.D.L H (ψ + ε • φ)) =
      P ψb (mass SM.D.m0 SM.D.L H ψ) + ε * P ψb (mass SM.D.m0 SM.D.L H φ) := by
    simp only [map_add, map_smul, smul_eq_mul]
  rw [hsum, hm]
  ring

/-- The Dirac Lagrangian is affine along a co-spinor line. -/
theorem lagD_psib_affine (H : V) (ψ : S) (X : Fin 4 → S) (ψb φb : S') (Xb Xφb : Fin 4 → S')
    (ε : ℝ) :
    lagD SM.D P H ψ X (ψb + ε • φb) (fun B => Xb B + ε • Xφb B) =
      lagD SM.D P H ψ X ψb Xb + ε * ((1 / 2 : ℝ) * ∑ C, lorentzSign C *
        (P φb (SM.D.Fr.c C (X C)) - P (Xφb C) (SM.D.Fr.c C ψ)) - P φb (mass SM.D.m0 SM.D.L H ψ)) := by
  unfold lagD
  have hsum : ∑ C, lorentzSign C * (P (ψb + ε • φb) (SM.D.Fr.c C (X C)) -
      P (Xb C + ε • Xφb C) (SM.D.Fr.c C ψ)) = ∑ C, lorentzSign C * (P ψb (SM.D.Fr.c C (X C)) -
        P (Xb C) (SM.D.Fr.c C ψ)) + ε * ∑ C, lorentzSign C * (P φb (SM.D.Fr.c C (X C)) -
          P (Xφb C) (SM.D.Fr.c C ψ)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun C _ => ?_
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hm : P (ψb + ε • φb) (mass SM.D.m0 SM.D.L H ψ) =
      P ψb (mass SM.D.m0 SM.D.L H ψ) + ε * P φb (mass SM.D.m0 SM.D.L H ψ) := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hsum, hm]
  ring

/-! ### Line derivatives in the matter directions -/

section Lines

variable (j : HJ1C m V S S')

/-- **The gauge direction**: the Dirac current row. -/
theorem hasDerivAt_L1D_gauge (X : Fin 4 → MatLie m) (dX : Fin 4 → Fin 4 → MatLie m) :
    HasDerivAt (fun ε : ℝ => L1D SM P (j + ε • vA m V S S' X dX))
      (volM j.1.1.1 * ((1 / 2 : ℝ) * ∑ C, lorentzSign C *
        (P j.2.2.1 (SM.D.Fr.c C (SM.D.ρ (aR j.1.1.1 X C) j.2.1.1)) -
          P (SM.Db.ρ (aR j.1.1.1 X C) j.2.2.1) (SM.D.Fr.c C j.2.1.1)))) 0 := by
  obtain ⟨⟨⟨g, dg⟩, ⟨A, dA⟩, ⟨H, dH⟩⟩, ⟨ψ, cψ⟩, ⟨ψb, cψb⟩⟩ := j
  have hf : (fun ε : ℝ => L1D SM P ((((g, dg), (A, dA), (H, dH)), (ψ, cψ), (ψb, cψb)) +
      ε • vA m V S S' X dX)) = fun ε => volM g * lagD SM.D P H ψ
        (fun B => covX SM.D (GR g dg) (aR g A) ψ (dψR g cψ) B + ε • SM.D.ρ (aR g X B) ψ) ψb
        (fun B => covX SM.Db (GR g dg) (aR g A) ψb (dψR g cψb) B + ε • SM.Db.ρ (aR g X B) ψb) := by
    funext ε
    simp only [L1D, vA, Prod.mk_add_mk, Prod.smul_mk, smul_zero, add_zero, XsR_eq_covX]
    congr 2
    · funext B; exact covX_gauge SM.D _ g A X ψ _ ε B
    · funext B; exact covX_gauge SM.Db _ g A X ψb _ ε B
  rw [hf]
  exact (hasDerivAt_lagD_line SM P H ψ ψb (fun C => hasDerivAt_affine _ _)
    (fun C => hasDerivAt_affine _ _)).const_mul _

/-- **The Higgs direction**: the Yukawa row. -/
theorem hasDerivAt_L1D_higgs (η : V) (dη : Fin 4 → V) :
    HasDerivAt (fun ε : ℝ => L1D SM P (j + ε • vH m V S S' η dη))
      (volM j.1.1.1 * (-P j.2.2.1 (SM.D.L η j.2.1.1))) 0 := by
  obtain ⟨⟨⟨g, dg⟩, ⟨A, dA⟩, ⟨H, dH⟩⟩, ⟨ψ, cψ⟩, ⟨ψb, cψb⟩⟩ := j
  have hf : (fun ε : ℝ => L1D SM P ((((g, dg), (A, dA), (H, dH)), (ψ, cψ), (ψb, cψb)) +
      ε • vH m V S S' η dη)) = fun ε => volM g * (lagD SM.D P H ψ
        (XsR SM.D g dg A ψ cψ) ψb (XsR SM.Db g dg A ψb cψb) + ε * (-P ψb (SM.D.L η ψ))) := by
    funext ε
    simp only [L1D, vH, Prod.mk_add_mk, Prod.smul_mk, smul_zero, add_zero, lagD, mass, map_add,
      map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hf]
  have := (hasDerivAt_affine (lagD SM.D P H ψ (XsR SM.D g dg A ψ cψ) ψb
    (XsR SM.Db g dg A ψb cψb)) (-P ψb (SM.D.L η ψ))).const_mul (volM g)
  simpa [smul_eq_mul] using this

/-- **The spinor direction** (`GenDAlg.psi_row` form). -/
theorem hasDerivAt_L1D_psi (φ : S) (cφ : Fin 4 → S) :
    HasDerivAt (fun ε : ℝ => L1D SM P (j + ε • vP m V S S' φ cφ))
      (volM j.1.1.1 * ((1 / 2 : ℝ) * ∑ C, lorentzSign C *
        (P j.2.2.1 (SM.D.Fr.c C (covX SM.D (GR j.1.1.1 j.1.1.2) (aR j.1.1.1 j.1.2.1.1) φ
          (dψR j.1.1.1 cφ) C)) -
          P (covX SM.Db (GR j.1.1.1 j.1.1.2) (aR j.1.1.1 j.1.2.1.1) j.2.2.1 (dψR j.1.1.1 j.2.2.2) C)
            (SM.D.Fr.c C φ)) - P j.2.2.1 (mass SM.D.m0 SM.D.L j.1.2.2.1 φ))) 0 := by
  obtain ⟨⟨⟨g, dg⟩, ⟨A, dA⟩, ⟨H, dH⟩⟩, ⟨ψ, cψ⟩, ⟨ψb, cψb⟩⟩ := j
  have hf : (fun ε : ℝ => L1D SM P ((((g, dg), (A, dA), (H, dH)), (ψ, cψ), (ψb, cψb)) +
      ε • vP m V S S' φ cφ)) = fun ε => volM g * (lagD SM.D P H ψ
        (covX SM.D (GR g dg) (aR g A) ψ (dψR g cψ)) ψb (covX SM.Db (GR g dg) (aR g A) ψb (dψR g cψb)) + ε *
        ((1 / 2 : ℝ) * ∑ C, lorentzSign C * (P ψb (SM.D.Fr.c C
          (covX SM.D (GR g dg) (aR g A) φ (dψR g cφ) C)) - P (covX SM.Db (GR g dg) (aR g A) ψb (dψR g cψb) C) (SM.D.Fr.c C φ)) -
          P ψb (mass SM.D.m0 SM.D.L H φ))) := by
    funext ε
    simp only [L1D, vP, Prod.mk_add_mk, Prod.smul_mk, smul_zero, add_zero, XsR_eq_covX]
    have hX : covX SM.D (GR g dg) (aR g A) (ψ + ε • φ) (dψR g (cψ + ε • cφ)) =
        fun B => covX SM.D (GR g dg) (aR g A) ψ (dψR g cψ) B +
          ε • covX SM.D (GR g dg) (aR g A) φ (dψR g cφ) B := by
      funext B; exact covX_psi SM.D _ g _ ψ φ cψ cφ ε B
    rw [hX, lagD_psi_affine]
  rw [hf]
  have := (hasDerivAt_affine (lagD SM.D P H ψ (covX SM.D (GR g dg) (aR g A) ψ (dψR g cψ)) ψb (covX SM.Db (GR g dg) (aR g A) ψb (dψR g cψb)))
    ((1 / 2 : ℝ) * ∑ C, lorentzSign C * (P ψb (SM.D.Fr.c C
      (covX SM.D (GR g dg) (aR g A) φ (dψR g cφ) C)) - P (covX SM.Db (GR g dg) (aR g A) ψb (dψR g cψb) C) (SM.D.Fr.c C φ)) -
      P ψb (mass SM.D.m0 SM.D.L H φ))).const_mul (volM g)
  simpa [smul_eq_mul] using this

/-- **The co-spinor direction** (`GenDAlg.psib_row` form). -/
theorem hasDerivAt_L1D_psib (φb : S') (cφb : Fin 4 → S') :
    HasDerivAt (fun ε : ℝ => L1D SM P (j + ε • vPb m V S S' φb cφb))
      (volM j.1.1.1 * ((1 / 2 : ℝ) * ∑ C, lorentzSign C *
        (P φb (SM.D.Fr.c C (covX SM.D (GR j.1.1.1 j.1.1.2) (aR j.1.1.1 j.1.2.1.1) j.2.1.1
          (dψR j.1.1.1 j.2.1.2) C)) -
          P (covX SM.Db (GR j.1.1.1 j.1.1.2) (aR j.1.1.1 j.1.2.1.1) φb (dψR j.1.1.1 cφb) C)
            (SM.D.Fr.c C j.2.1.1)) - P φb (mass SM.D.m0 SM.D.L j.1.2.2.1 j.2.1.1))) 0 := by
  obtain ⟨⟨⟨g, dg⟩, ⟨A, dA⟩, ⟨H, dH⟩⟩, ⟨ψ, cψ⟩, ⟨ψb, cψb⟩⟩ := j
  have hf : (fun ε : ℝ => L1D SM P ((((g, dg), (A, dA), (H, dH)), (ψ, cψ), (ψb, cψb)) +
      ε • vPb m V S S' φb cφb)) = fun ε => volM g * (lagD SM.D P H ψ (covX SM.D (GR g dg) (aR g A) ψ (dψR g cψ)) ψb
        (covX SM.Db (GR g dg) (aR g A) ψb (dψR g cψb)) + ε *
        ((1 / 2 : ℝ) * ∑ C, lorentzSign C * (P φb (SM.D.Fr.c C (covX SM.D (GR g dg) (aR g A) ψ (dψR g cψ) C)) -
          P (covX SM.Db (GR g dg) (aR g A) φb (dψR g cφb) C) (SM.D.Fr.c C ψ)) -
          P φb (mass SM.D.m0 SM.D.L H ψ))) := by
    funext ε
    simp only [L1D, vPb, Prod.mk_add_mk, Prod.smul_mk, smul_zero, add_zero, XsR_eq_covX]
    have hXb : covX SM.Db (GR g dg) (aR g A) (ψb + ε • φb) (dψR g (cψb + ε • cφb)) =
        fun B => covX SM.Db (GR g dg) (aR g A) ψb (dψR g cψb) B +
          ε • covX SM.Db (GR g dg) (aR g A) φb (dψR g cφb) B := by
      funext B; exact covX_psi SM.Db _ g _ ψb φb cψb cφb ε B
    rw [hXb, lagD_psib_affine]
  rw [hf]
  have := (hasDerivAt_affine (lagD SM.D P H ψ (covX SM.D (GR g dg) (aR g A) ψ (dψR g cψ)) ψb (covX SM.Db (GR g dg) (aR g A) ψb (dψR g cψb)))
    ((1 / 2 : ℝ) * ∑ C, lorentzSign C * (P φb (SM.D.Fr.c C (covX SM.D (GR g dg) (aR g A) ψ (dψR g cψ) C)) -
      P (covX SM.Db (GR g dg) (aR g A) φb (dψR g cφb) C) (SM.D.Fr.c C ψ)) -
      P φb (mass SM.D.m0 SM.D.L H ψ))).const_mul (volM g)
  simpa [smul_eq_mul] using this

end Lines

/-! ### The complete first variation -/

section Full

variable (hP : DiracPairing SM)

/-- The metric part of the first variation (`GenDAct.hasDerivAt_L1D_metric`). -/
def dMet (j : HJ1C m V S S') (k : Met) (dk : Fin 4 → Met) : ℝ :=
  volM j.1.1.1 * ((1 / 2 : ℝ) * ∑ A, ∑ B, lorentzSign A * lorentzSign B *
      (symTD SM.D hP.P).frame j.1.2.2.1 j.2.1.1
        (covX SM.D (GR j.1.1.1 j.1.1.2) (aR j.1.1.1 j.1.2.1.1) j.2.1.1 (dψR j.1.1.1 j.2.1.2))
        j.2.2.1
        (covX SM.Db (GR j.1.1.1 j.1.1.2) (aR j.1.1.1 j.1.2.1.1) j.2.2.1 (dψR j.1.1.1 j.2.2.2))
        A B * kfr j.1.1.1 k A B +
    (hP.P (rDf SM.Db (GR j.1.1.1 j.1.1.2) (aR j.1.1.1 j.1.2.1.1) j.1.2.2.1 j.2.2.1
        (dψR j.1.1.1 j.2.2.2))
        ((-spinPart SM.D.Fr (fun A B => (1 / 2 : ℝ) * (Lam j.1.1.1 k A B - Lam j.1.1.1 k B A)))
          j.2.1.1) -
      hP.P ((-spinPart SM.Db.Fr (fun A B => (1 / 2 : ℝ) *
          (Lam j.1.1.1 k A B - Lam j.1.1.1 k B A))) j.2.2.1)
        (rDf SM.D (GR j.1.1.1 j.1.1.2) (aR j.1.1.1 j.1.2.1.1) j.1.2.2.1 j.2.1.1
          (dψR j.1.1.1 j.2.1.2)) -
      ∑ C, (divEf (GR j.1.1.1 j.1.1.2) C *
          lorFl hP (fun A B => (1 / 2 : ℝ) * (Lam j.1.1.1 k A B - Lam j.1.1.1 k B A))
            j.2.1.1 j.2.2.1 C +
        lorFlD hP (fun A B => (1 / 2 : ℝ) * (Lam j.1.1.1 k A B - Lam j.1.1.1 k B A))
          (fun B A C => (1 / 2 : ℝ) * (dLam j.1.1.1 j.1.1.2 k dk B A C -
            dLam j.1.1.1 j.1.1.2 k dk B C A))
          j.2.1.1 (dψR j.1.1.1 j.2.1.2) j.2.2.1 (dψR j.1.1.1 j.2.2.2) C)))

/-- The gauge part (the Dirac current row). -/
def dGau (j : HJ1C m V S S') (X : Fin 4 → MatLie m) : ℝ :=
  volM j.1.1.1 * ((1 / 2 : ℝ) * ∑ C, lorentzSign C *
    (hP.P j.2.2.1 (SM.D.Fr.c C (SM.D.ρ (aR j.1.1.1 X C) j.2.1.1)) -
      hP.P (SM.Db.ρ (aR j.1.1.1 X C) j.2.2.1) (SM.D.Fr.c C j.2.1.1)))

/-- The Higgs part (the Yukawa row). -/
def dHig (j : HJ1C m V S S') (η : V) : ℝ := volM j.1.1.1 * (-hP.P j.2.2.1 (SM.D.L η j.2.1.1))

/-- The spinor part. -/
def dPsi (j : HJ1C m V S S') (φ : S) (cφ : Fin 4 → S) : ℝ :=
  volM j.1.1.1 * ((1 / 2 : ℝ) * ∑ C, lorentzSign C *
    (hP.P j.2.2.1 (SM.D.Fr.c C (covX SM.D (GR j.1.1.1 j.1.1.2) (aR j.1.1.1 j.1.2.1.1) φ
      (dψR j.1.1.1 cφ) C)) -
      hP.P (covX SM.Db (GR j.1.1.1 j.1.1.2) (aR j.1.1.1 j.1.2.1.1) j.2.2.1 (dψR j.1.1.1 j.2.2.2) C)
        (SM.D.Fr.c C φ)) - hP.P j.2.2.1 (mass SM.D.m0 SM.D.L j.1.2.2.1 φ))

/-- The co-spinor part. -/
def dPsib (j : HJ1C m V S S') (φb : S') (cφb : Fin 4 → S') : ℝ :=
  volM j.1.1.1 * ((1 / 2 : ℝ) * ∑ C, lorentzSign C *
    (hP.P φb (SM.D.Fr.c C (covX SM.D (GR j.1.1.1 j.1.1.2) (aR j.1.1.1 j.1.2.1.1) j.2.1.1
      (dψR j.1.1.1 j.2.1.2) C)) -
      hP.P (covX SM.Db (GR j.1.1.1 j.1.1.2) (aR j.1.1.1 j.1.2.1.1) φb (dψR j.1.1.1 cφb) C)
        (SM.D.Fr.c C j.2.1.1)) - hP.P φb (mass SM.D.m0 SM.D.L j.1.2.2.1 j.2.1.1))

/-- **The first variation of the first-order Dirac density** at a chart 1-jet with symmetric metric
jets, in a direction with symmetric metric jets. -/
theorem fderiv_L1D_eq (j : HJ1C m V S S') (hj : j ∈ chart1C m V S S') (hg : ChartM j.1.1.1)
    (hdg : ∀ α μ ν, j.1.1.2 α μ ν = j.1.1.2 α ν μ) (v : HJ1C m V S S')
    (hk : ∀ μ ν, v.1.1.1 μ ν = v.1.1.1 ν μ) (hdk : ∀ α μ ν, v.1.1.2 α μ ν = v.1.1.2 α ν μ) :
    fderiv ℝ (L1D SM hP.P) j v = dMet SM hP j v.1.1.1 v.1.1.2 + dGau SM hP j v.1.2.1.1 +
      dHig SM hP j v.1.2.2.1 + dPsi SM hP j v.2.1.1 v.2.1.2 + dPsib SM hP j v.2.2.1 v.2.2.2 := by
  have hd : DifferentiableAt ℝ (L1D SM hP.P) j :=
    ((contDiffOn_L1D SM hP.P).contDiffAt (isOpen_chart1C.mem_nhds hj)).differentiableAt (by simp)
  have hline : ∀ w : HJ1C m V S S', HasDerivAt (fun ε : ℝ => L1D SM hP.P (j + ε • w))
      (fderiv ℝ (L1D SM hP.P) j w) 0 := fun w => by
    have hl : HasDerivAt (fun ε : ℝ => j + ε • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add j
    exact hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  conv_lhs => rw [decomp_dir v]
  simp only [map_add]
  rw [(hline _).unique (hasDerivAt_L1D_metric SM hP j hg hdg _ hk _ hdk),
    (hline _).unique (hasDerivAt_L1D_gauge SM hP.P j _ _),
    (hline _).unique (hasDerivAt_L1D_higgs SM hP.P j _ _),
    (hline _).unique (hasDerivAt_L1D_psi SM hP.P j _ _),
    (hline _).unique (hasDerivAt_L1D_psib SM hP.P j _ _)]
  rfl

end Full

end RenewalGeometry.GenDEul
