/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMVariationLipschitzDirac

/-!
# First-variation continuity from primitive fields (`prop:variation-continuity`,
  Einstein–Standard-Model action-closure manuscript)

**`variation_continuity`**: fix a chart `Q = (t₀,t₁) × (0,1)³`, a test region `K` with time support
in `(t₀,t₁)`, a test order `r ≥ 1`, a compact coframe chart set `𝒦_e`, a compact physical bank set
`P` and a bound `B < ∞`.  There is `C_K < ∞` such that for all smooth fields `z₁, z₂` in the
bounded strong-packet class (`PacketBound`: coframe values in `𝒦_e` on `Q̄`, and the norms of
`eq:strong-geometry`–`eq:strong-spinors` on `Q` bounded by `B`), all banks `θ₁, θ₂ ∈ P`, both
sectors `b ∈ {g, SM}` and all tests `v ∈ 𝒱_K`:

`|D𝒮_{b,θ₁}(z₁)[v] - D𝒮_{b,θ₂}(z₂)[v]| ≤ C_K · d_K(z₁,θ₁; z₂,θ₂) · ‖v‖_{C^r}`,

i.e. `‖D𝒮_b(z₁) - D𝒮_b(z₂)‖_{(V^r_K)^*} ≤ C_K d_K` with `d_K = dK` of
`EinsteinSMCofinalTransport.lean` (`L^∞ + H¹` coframe, `L⁴` connection, `L²` curvature, `L⁴` Higgs,
`L²` covariant Higgs gradient, `H¹` spinors, bank distance).

Proof: the covector identities `gravVariation_eq_cov`, `smVariation_eq_cov` reduce the first
variations to `∫_Q Cov(J(z))(testJet v)`; the sector Lipschitz estimates of the jet covectors
(`grav_lipschitz`, `boson_lipschitz`, `dirac_lipschitz`) bound the `L¹(Q)` difference of the
covector fields by the jet distance plus the bank distance; the jet distance is bounded by `d_K`
(`jetDist_redJet_le`: the spinor `L⁴` difference by the critical Sobolev embedding
`H¹(Q) ↪ L⁴(Q)`, `SobolevOpen.exists_sobolev_L4_box`).

Hypotheses beyond the manuscript's (disclosed): `YukawaLipOn FC P` (bounded Lipschitz dependence of
the abstract Yukawa map on the bank, automatic in the manuscript where `𝓜_Y` is linear in the Yukawa
matrices); `B` is a common bound for the packet norms (`PacketBound`).  Every smooth field with
coframe values in `𝒦_e` belongs to the class for some finite `B` (`exists_packetBound`).
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal

noncomputable section

set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM
namespace VarLip

/-! ### Bank bounds from compactness -/

section BankCompact

variable {Ysec : Type} [Fintype Ysec]

theorem abs_bankCoord_le (θ : CoefficientBank Ysec) (i : Fin 7) :
    |(bankCoords θ).1 i| ≤ ‖bankVec θ‖ :=
  (Real.norm_eq_abs _ ▸ norm_le_pi_norm (bankVec θ).1 i).trans (norm_fst_le _)

theorem continuous_bankVecOf :
    Continuous fun p : (Fin 7 → ℝ) × (Ysec → Matrix (Fin 3) (Fin 3) ℂ) =>
      ((p.1, fun y i j => p.2 y i j) : (Fin 7 → ℝ) × (Ysec → Fin 3 → Fin 3 → ℂ)) :=
  continuous_fst.prodMk (continuous_pi fun y => continuous_pi fun i => continuous_pi fun j =>
    ((continuous_apply j).comp ((continuous_apply i).comp
      ((continuous_apply y).comp continuous_snd))))

/-- **Uniform bank bounds on a compact physical bank set.** -/
theorem exists_bankBounds {P : Set (CoefficientBank Ysec)} (hP : IsCompactBankSet P) :
    ∃ c Mb : ℝ, BankBounds P c Mb := by
  have hV : IsCompact (bankVec '' P) := by
    have := hP.1.image (continuous_bankVecOf (Ysec := Ysec))
    rwa [image_image] at this
  obtain ⟨M, hM⟩ := hV.isBounded.exists_norm_le
  have hMθ : ∀ θ ∈ P, ‖bankVec θ‖ ≤ max M 0 := fun θ hθ =>
    (hM _ (mem_image_of_mem _ hθ)).trans (le_max_left _ _)
  have hco : ∀ θ ∈ P, ∀ i : Fin 7, |(bankCoords θ).1 i| ≤ max M 0 := fun θ hθ i =>
    (abs_bankCoord_le θ i).trans (hMθ θ hθ)
  -- lower bound
  obtain ⟨c, hc, hcP⟩ : ∃ c > (0 : ℝ), ∀ θ ∈ P, c ≤ θ.kappa ∧ c ≤ θ.g1 ∧ c ≤ θ.g2 ∧
      c ≤ θ.g3 := by
    rcases P.eq_empty_or_nonempty with hPe | ⟨θ₀, hθ₀⟩
    · exact ⟨1, one_pos, fun θ hθ => by rw [hPe] at hθ; exact absurd hθ (notMem_empty θ)⟩
    set f : (Fin 7 → ℝ) × (Ysec → Matrix (Fin 3) (Fin 3) ℂ) → ℝ :=
      fun p => min (p.1 0) (min (p.1 2) (min (p.1 3) (p.1 4))) with hf
    have hfc : Continuous f := by simp only [hf]; fun_prop
    obtain ⟨p₀, hp₀, hmin⟩ := hP.1.exists_isMinOn ⟨_, mem_image_of_mem _ hθ₀⟩ hfc.continuousOn
    obtain ⟨θ₁, hθ₁, rfl⟩ := hp₀
    obtain ⟨h1, h2, h3, h4, -⟩ := hP.2 hθ₁
    refine ⟨f (bankCoords θ₁), ?_, fun θ hθ => ?_⟩
    · simp only [hf, bankCoords, lt_min_iff]
      simp [h1, h2, h3, h4]
    · have h := isMinOn_iff.mp hmin _ (mem_image_of_mem bankCoords hθ)
      have e : f (bankCoords θ) = min θ.kappa (min θ.g1 (min θ.g2 θ.g3)) := by
        simp [hf, bankCoords]
      rw [e] at h
      simp only [le_min_iff] at h
      exact h
  have hcoord : ∀ θ ∈ P, |θ.kappa| ≤ max M 0 ∧ |θ.Lambda| ≤ max M 0 ∧ |θ.g1| ≤ max M 0 ∧
      |θ.g2| ≤ max M 0 ∧ |θ.g3| ≤ max M 0 ∧ |θ.lambdaH| ≤ max M 0 ∧ |θ.vH| ≤ max M 0 :=
    fun θ hθ => ⟨by simpa [bankCoords] using hco θ hθ 0, by simpa [bankCoords] using hco θ hθ 1,
      by simpa [bankCoords] using hco θ hθ 2, by simpa [bankCoords] using hco θ hθ 3,
      by simpa [bankCoords] using hco θ hθ 4, by simpa [bankCoords] using hco θ hθ 5,
      by simpa [bankCoords] using hco θ hθ 6⟩
  refine ⟨c, max M 0, ⟨hc, le_max_right _ _, fun θ hθ => (hcP θ hθ).1, fun θ hθ => ?_,
    fun θ hθ => ?_, fun θ hθ => ?_, fun θ hθ => (hcoord θ hθ).2.1,
    fun θ hθ => (hcoord θ hθ).2.2.2.2.2.1, fun θ hθ => (hcoord θ hθ).2.2.2.2.2.2⟩⟩
  · exact ⟨(hcP θ hθ).2.1, (le_abs_self _).trans (hcoord θ hθ).2.2.1⟩
  · exact ⟨(hcP θ hθ).2.2.1, (le_abs_self _).trans (hcoord θ hθ).2.2.2.1⟩
  · exact ⟨(hcP θ hθ).2.2.2, (le_abs_self _).trans (hcoord θ hθ).2.2.2.2.1⟩

end BankCompact

/-! ### The trivial carrier satisfies the Yukawa hypothesis -/

theorem yukawaLipOn_trivial {Ysec : Type} [Fintype Ysec] (P : Set (CoefficientBank Ysec)) :
    YukawaLipOn (trivialCarrier Ysec) P 0 0 := by
  have h1 : ∀ θ, yukL (trivialCarrier Ysec) θ = 0 := fun θ => by
    ext h c c'
    simp [yukL, trivialCarrier]
    rfl
  have h0 : ∀ θ, (trivialCarrier Ysec).yukawa θ 0 = 0 := fun θ => rfl
  refine ⟨le_rfl, le_rfl, fun θ _ => by simp [h1], fun θ _ => by simp [h0],
    fun θ₁ _ θ₂ _ => by simp [h1], fun θ₁ _ θ₂ _ => by simp [h0]⟩

/-! ### Norms of reduced jets versus the packet norms of `d_K` -/

section JetNorms

variable {C : Type} [Fintype C]

theorem norm_coframeJetC (d : CoframeJet) :
    ‖(fun (i : Fin 4) (p : Fin 4 × Fin 4) => ((d i p.1 p.2 : ℝ) : ℂ))‖ = ‖d‖ :=
  norm_pi_congr fun i => norm_coframeC_eq (d i)

theorem norm_spinorJetC (d : Fin 4 → SpinorFibre C) :
    ‖(fun (i : Fin 4) (p : Fin 4 × C) => d i p.1 p.2)‖ = ‖d‖ :=
  norm_pi_congr fun i => norm_uncurry (d i)

/-- Critical Sobolev embedding for spinor-component packets on a chart box. -/
theorem exists_spinor_L4 {T : ℝ} (Q : ChartBox T) :
    ∃ Cs : ℝ≥0∞, Cs ≠ ⊤ ∧ ∀ (u : E4 → Fin 4 × C → ℂ) (g : E4 → Fin 4 → Fin 4 × C → ℂ),
      MemH1 Q u g → eLpNorm u 4 Q.μ ≤ Cs * h1Norm Q u g := by
  obtain ⟨Cs, hCs⟩ := SobolevOpen.exists_sobolev_L4_box (ι := Fin 4) (by simp) Q.lt
  refine ⟨∑ _p : Fin 4 × C, (Cs : ℝ≥0∞) * (1 + 4), ENNReal.sum_ne_top.mpr fun _ _ =>
    ENNReal.mul_ne_top ENNReal.coe_ne_top (by norm_num), fun u g hu => ?_⟩
  refine (eLpNorm_le_sum_apply (by norm_num) fun p => (hu p).memLp.1).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun p _ => (hCs _ _ (hu p)).trans ?_
  calc (Cs : ℝ≥0∞) * SobolevOpen.w12Norm (SobolevOpen.box Q.a Q.b) (fun x => u x p)
        (fun i x => g x i p) ≤ Cs * (h1Norm Q u g + 4 * h1Norm Q u g) := by
        gcongr; exact w12Norm_le_of_h1 Q p
    _ = Cs * (1 + 4) * h1Norm Q u g := by ring

end JetNorms

/-! ### The bounded strong-packet class -/

section PacketClass

variable {T : ℝ} {C : Type} [Fintype C] {left : C → Bool}

/-- **The bounded strong-packet class on a chart** (`eq:strong-geometry`–`eq:strong-spinors`
norms bounded by `B`, coframe values in `𝒦_e` on `Q̄`). -/
structure PacketBound (Q : ChartBox T) (Ke : Set CoframeFibre) (B : ℝ≥0∞)
    (z : SmoothFields T left) : Prop where
  chart : ∀ x ∈ closure Q.set, z.z.e x ∈ Ke
  coframe : h1Norm Q (coframeC z.z.e) (coframeGrad z.z.e) ≤ B
  conn : eLpNorm z.z.A 4 Q.μ ≤ B
  curv : eLpNorm (curvatureF z.z.A) 2 Q.μ ≤ B
  higgs : eLpNorm z.z.H 4 Q.μ ≤ B
  covgrad : eLpNorm (covDerivHiggs z.z.A z.z.H) 2 Q.μ ≤ B
  spinor : h1Norm Q (spinorC z.z.Ψ) (spinorGrad z.z.Ψ) ≤ B
  cospinor : h1Norm Q (spinorC z.z.Ψb) (spinorGrad z.z.Ψb) ≤ B

theorem le_sum7 (a₁ a₂ a₃ a₄ a₅ a₆ a₇ : ℝ≥0∞) :
    a₁ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ ∧ a₂ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ ∧
      a₃ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ ∧ a₄ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ ∧
      a₅ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ ∧ a₆ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ ∧
      a₇ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_add_right (le_add_right (le_add_right (le_add_right (le_add_right
      (le_add_right le_rfl)))))
  · exact le_add_right (le_add_right (le_add_right (le_add_right (le_add_right
      (le_add_left le_rfl)))))
  · exact le_add_right (le_add_right (le_add_right (le_add_right (le_add_left le_rfl))))
  · exact le_add_right (le_add_right (le_add_right (le_add_left le_rfl)))
  · exact le_add_right (le_add_right (le_add_left le_rfl))
  · exact le_add_right (le_add_left le_rfl)
  · exact le_add_left le_rfl

theorem h1Norm_ne_top {Q : ChartBox T} {ι' : Type} [Fintype ι'] {u : E4 → ι' → ℂ}
    {g : E4 → Fin 4 → ι' → ℂ} (h : MemH1 Q u g) : h1Norm Q u g ≠ ⊤ := by
  have hu : MemLp u 2 Q.μ := memLp_pi_iff.mpr fun c => (h c).memLp
  have hg : MemLp g 2 Q.μ :=
    memLp_pi_iff.mpr fun i => memLp_pi_iff.mpr fun c => (h c).memLp_grad i
  exact ENNReal.add_ne_top.mpr ⟨hu.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩

/-- **Non-vacuity of the class**: every smooth field with coframe values in `𝒦_e` on `Q̄` lies in
the bounded strong-packet class for some finite `B`. -/
theorem exists_packetBound (Q : ChartBox T) {Ke : Set CoframeFibre} (z : SmoothFields T left)
    (hz : ∀ x ∈ closure Q.set, z.z.e x ∈ Ke) : ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ PacketBound Q Ke B z := by
  have hcl := Q.isCompact_closure
  have hsub := Q.closure_subset_cylSlab
  have hJ := (continuousOn_redJet z).mono hsub
  have mA : MemLp z.z.A 4 Q.μ :=
    memLp_of_continuousOn_closure Q.isOpen hcl (z.smooth_A.continuousOn.mono hsub) 4
  have mH : MemLp z.z.H 4 Q.μ :=
    memLp_of_continuousOn_closure Q.isOpen hcl (z.smooth_H.continuousOn.mono hsub) 4
  have mF : MemLp (curvatureF z.z.A) 2 Q.μ :=
    memLp_of_continuousOn_closure Q.isOpen hcl ((πF (C := C)).continuous.comp_continuousOn hJ) 2
  have mK : MemLp (covDerivHiggs z.z.A z.z.H) 2 Q.μ :=
    memLp_of_continuousOn_closure Q.isOpen hcl ((πK (C := C)).continuous.comp_continuousOn hJ) 2
  have he := h1Norm_ne_top (memH1_coframe_of_smooth Q hcl hsub z.smooth_e)
  have hΨ := h1Norm_ne_top (memH1_spinor_of_smooth Q z.smooth_Ψ)
  have hΨb := h1Norm_ne_top (memH1_spinor_of_smooth Q z.smooth_Ψb)
  have hs := le_sum7 (h1Norm Q (coframeC z.z.e) (coframeGrad z.z.e)) (eLpNorm z.z.A 4 Q.μ)
    (eLpNorm (curvatureF z.z.A) 2 Q.μ) (eLpNorm z.z.H 4 Q.μ)
    (eLpNorm (covDerivHiggs z.z.A z.z.H) 2 Q.μ) (h1Norm Q (spinorC z.z.Ψ) (spinorGrad z.z.Ψ))
    (h1Norm Q (spinorC z.z.Ψb) (spinorGrad z.z.Ψb))
  refine ⟨h1Norm Q (coframeC z.z.e) (coframeGrad z.z.e) + eLpNorm z.z.A 4 Q.μ +
    eLpNorm (curvatureF z.z.A) 2 Q.μ + eLpNorm z.z.H 4 Q.μ +
    eLpNorm (covDerivHiggs z.z.A z.z.H) 2 Q.μ + h1Norm Q (spinorC z.z.Ψ) (spinorGrad z.z.Ψ) +
    h1Norm Q (spinorC z.z.Ψb) (spinorGrad z.z.Ψb), ?_, ⟨hz, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · have := mA.eLpNorm_ne_top; have := mH.eLpNorm_ne_top; have := mF.eLpNorm_ne_top
    have := mK.eLpNorm_ne_top
    finiteness
  exacts [hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2.1, hs.2.2.2.2.2.2]

end PacketClass

/-! ### From the packet class to bounded jet fields -/

section PacketToJet

open SobolevOpen (pd)

variable {T : ℝ} {C : Type} [Fintype C] {left : C → Bool} {Ysec : Type} [Fintype Ysec]

theorem one_add_mul_le {Cs a B : ℝ≥0∞} (h : a ≤ B) : a ≤ (1 + Cs) * B :=
  h.trans (le_mul_of_one_le_left' le_self_add)

theorem cs_mul_le {Cs a B : ℝ≥0∞} (h : a ≤ Cs * B) : a ≤ (1 + Cs) * B :=
  h.trans (by gcongr; exact le_add_self)

theorem eLpNorm_redJet_de (Q : ChartBox T) (z : FieldTuple C) :
    eLpNorm (fun x => (redJet z x).de) 2 Q.μ = eLpNorm (coframeGrad z.e) 2 Q.μ :=
  eLpNorm_congr_norm_ae (Eventually.of_forall fun x =>
    (norm_coframeJetC (fun i => pd z.e i x)).symm)

theorem eLpNorm_redJet_dΨ (Q : ChartBox T) (z : FieldTuple C) :
    eLpNorm (fun x => (redJet z x).dΨ) 2 Q.μ = eLpNorm (spinorGrad z.Ψ) 2 Q.μ :=
  eLpNorm_congr_norm_ae (Eventually.of_forall fun x =>
    (norm_spinorJetC (fun i => pd z.Ψ i x)).symm)

theorem eLpNorm_redJet_dΨb (Q : ChartBox T) (z : FieldTuple C) :
    eLpNorm (fun x => (redJet z x).dΨb) 2 Q.μ = eLpNorm (spinorGrad z.Ψb) 2 Q.μ :=
  eLpNorm_congr_norm_ae (Eventually.of_forall fun x =>
    (norm_spinorJetC (fun i => pd z.Ψb i x)).symm)

theorem eLpNorm_spinor_eq (Q : ChartBox T) (Ψ : E4 → SpinorFibre C) (p : ℝ≥0∞) :
    eLpNorm Ψ p Q.μ = eLpNorm (spinorC Ψ) p Q.μ :=
  eLpNorm_congr_norm_ae (Eventually.of_forall fun x => (norm_uncurry (Ψ x)).symm)

/-- A packet-class field gives a uniformly bounded jet field. -/
theorem PacketBound.jetBound {Q : ChartBox T} {Ke : Set CoframeFibre} {B : ℝ≥0∞}
    {z : SmoothFields T left} (hp : PacketBound Q Ke B z) {Cs : ℝ≥0∞}
    (hCs : ∀ (u : E4 → Fin 4 × C → ℂ) (g : E4 → Fin 4 → Fin 4 × C → ℂ),
      MemH1 Q u g → eLpNorm u 4 Q.μ ≤ Cs * h1Norm Q u g) :
    JetBound Q Ke ((1 + Cs) * B) (redJet z.z) where
  meas := ((continuousOn_redJet z).mono (subset_closure.trans Q.closure_subset_cylSlab)).aestronglyMeasurable
    Q.isOpen.measurableSet
  chart := ae_restrict_of_forall_mem Q.isOpen.measurableSet fun x hx => hp.chart x (subset_closure hx)
  de := one_add_mul_le ((eLpNorm_redJet_de Q z.z).le.trans (le_add_self.trans hp.coframe))
  A := one_add_mul_le hp.conn
  F := one_add_mul_le hp.curv
  H := one_add_mul_le hp.higgs
  K := one_add_mul_le hp.covgrad
  Ψ := cs_mul_le ((eLpNorm_spinor_eq Q z.z.Ψ 4).le.trans
    ((hCs _ _ (memH1_spinor_of_smooth Q z.smooth_Ψ)).trans (by gcongr; exact hp.spinor)))
  dΨ := one_add_mul_le ((eLpNorm_redJet_dΨ Q z.z).le.trans (le_add_self.trans hp.spinor))
  Ψb := cs_mul_le ((eLpNorm_spinor_eq Q z.z.Ψb 4).le.trans
    ((hCs _ _ (memH1_spinor_of_smooth Q z.smooth_Ψb)).trans (by gcongr; exact hp.cospinor)))
  dΨb := one_add_mul_le ((eLpNorm_redJet_dΨb Q z.z).le.trans (le_add_self.trans hp.cospinor))

theorem dist_redJet_de (Q : ChartBox T) (z₁ z₂ : FieldTuple C) :
    eLpNorm (fun x => (redJet z₁ x).de - (redJet z₂ x).de) 2 Q.μ =
      eLpNorm (coframeGrad z₁.e - coframeGrad z₂.e) 2 Q.μ := by
  refine eLpNorm_congr_norm_ae (Eventually.of_forall fun x => ?_)
  have e : (coframeGrad z₁.e - coframeGrad z₂.e) x = fun i p =>
      ((((fun i => pd z₁.e i x) - (fun i => pd z₂.e i x)) i p.1 p.2 : ℝ) : ℂ) := by
    funext i p; simp [coframeGrad]
  rw [e, norm_coframeJetC]
  rfl

theorem dist_redJet_dΨ (Q : ChartBox T) (z₁ z₂ : FieldTuple C) :
    eLpNorm (fun x => (redJet z₁ x).dΨ - (redJet z₂ x).dΨ) 2 Q.μ =
      eLpNorm (spinorGrad z₁.Ψ - spinorGrad z₂.Ψ) 2 Q.μ :=
  eLpNorm_congr_norm_ae (Eventually.of_forall fun x =>
    (norm_spinorJetC ((fun i => pd z₁.Ψ i x) - (fun i => pd z₂.Ψ i x))).symm)

theorem dist_redJet_dΨb (Q : ChartBox T) (z₁ z₂ : FieldTuple C) :
    eLpNorm (fun x => (redJet z₁ x).dΨb - (redJet z₂ x).dΨb) 2 Q.μ =
      eLpNorm (spinorGrad z₁.Ψb - spinorGrad z₂.Ψb) 2 Q.μ :=
  eLpNorm_congr_norm_ae (Eventually.of_forall fun x =>
    (norm_spinorJetC ((fun i => pd z₁.Ψb i x) - (fun i => pd z₂.Ψb i x))).symm)

theorem dist_redJet_Ψ (Q : ChartBox T) (z₁ z₂ : FieldTuple C) :
    eLpNorm (fun x => (redJet z₁ x).Ψ - (redJet z₂ x).Ψ) 4 Q.μ =
      eLpNorm (spinorC z₁.Ψ - spinorC z₂.Ψ) 4 Q.μ :=
  eLpNorm_congr_norm_ae (Eventually.of_forall fun x => (norm_uncurry (z₁.Ψ x - z₂.Ψ x)).symm)

theorem dist_redJet_Ψb (Q : ChartBox T) (z₁ z₂ : FieldTuple C) :
    eLpNorm (fun x => (redJet z₁ x).Ψb - (redJet z₂ x).Ψb) 4 Q.μ =
      eLpNorm (spinorC z₁.Ψb - spinorC z₂.Ψb) 4 Q.μ :=
  eLpNorm_congr_norm_ae (Eventually.of_forall fun x => (norm_uncurry (z₁.Ψb x - z₂.Ψb x)).symm)

/-- **The jet distance of reduced jets is bounded by `d_K`.** -/
theorem jetDist_redJet_le {Q : ChartBox T} {Cs : ℝ≥0∞}
    (hCs : ∀ (u : E4 → Fin 4 × C → ℂ) (g : E4 → Fin 4 → Fin 4 × C → ℂ),
      MemH1 Q u g → eLpNorm u 4 Q.μ ≤ Cs * h1Norm Q u g)
    (z₁ z₂ : SmoothFields T left) (θ₁ θ₂ : CoefficientBank Ysec) :
    jetDist Q (redJet z₁.z) (redJet z₂.z) ≤ 10 * ((1 + Cs) * dK Q z₁ θ₁ z₂ θ₂) := by
  obtain ⟨X, hX⟩ : ∃ r, r = (1 + Cs) * dK Q z₁ θ₁ z₂ θ₂ := ⟨_, rfl⟩
  have hc : ∀ i, dKComp Q z₁ z₂ i ≤ X := fun i => by
    rw [hX]; exact one_add_mul_le (dKComp_le_dK Q z₁ θ₁ z₂ θ₂ i)
  have hcs : ∀ i, Cs * dKComp Q z₁ z₂ i ≤ X := fun i => by
    rw [hX]; exact cs_mul_le (by gcongr; exact dKComp_le_dK Q z₁ θ₁ z₂ θ₂ i)
  have hΨ : MemH1 Q (spinorC z₁.z.Ψ - spinorC z₂.z.Ψ) (spinorGrad z₁.z.Ψ - spinorGrad z₂.z.Ψ) :=
    fun c => SobolevOpen.MemW12.sub (memH1_spinor_of_smooth Q z₁.smooth_Ψ c)
      (memH1_spinor_of_smooth Q z₂.smooth_Ψ c)
  have hΨb : MemH1 Q (spinorC z₁.z.Ψb - spinorC z₂.z.Ψb)
      (spinorGrad z₁.z.Ψb - spinorGrad z₂.z.Ψb) :=
    fun c => SobolevOpen.MemW12.sub (memH1_spinor_of_smooth Q z₁.smooth_Ψb c)
      (memH1_spinor_of_smooth Q z₂.smooth_Ψb c)
  have t1 : eLpNorm (fun x => (redJet z₁.z x).e - (redJet z₂.z x).e) ⊤ Q.μ ≤ X := hc 0
  have t2 : eLpNorm (fun x => (redJet z₁.z x).de - (redJet z₂.z x).de) 2 Q.μ ≤ X := by
    rw [dist_redJet_de]; exact le_add_self.trans (hc 1)
  have t3 : eLpNorm (fun x => (redJet z₁.z x).A - (redJet z₂.z x).A) 4 Q.μ ≤ X := hc 2
  have t4 : eLpNorm (fun x => (redJet z₁.z x).F - (redJet z₂.z x).F) 2 Q.μ ≤ X := hc 3
  have t5 : eLpNorm (fun x => (redJet z₁.z x).H - (redJet z₂.z x).H) 4 Q.μ ≤ X := hc 4
  have t6 : eLpNorm (fun x => (redJet z₁.z x).K - (redJet z₂.z x).K) 2 Q.μ ≤ X := hc 5
  have t7 : eLpNorm (fun x => (redJet z₁.z x).Ψ - (redJet z₂.z x).Ψ) 4 Q.μ ≤ X := by
    rw [dist_redJet_Ψ]; exact (hCs _ _ hΨ).trans (hcs 6)
  have t8 : eLpNorm (fun x => (redJet z₁.z x).dΨ - (redJet z₂.z x).dΨ) 2 Q.μ ≤ X := by
    rw [dist_redJet_dΨ]; exact le_add_self.trans (hc 6)
  have t9 : eLpNorm (fun x => (redJet z₁.z x).Ψb - (redJet z₂.z x).Ψb) 4 Q.μ ≤ X := by
    rw [dist_redJet_Ψb]; exact (hCs _ _ hΨb).trans (hcs 7)
  have t10 : eLpNorm (fun x => (redJet z₁.z x).dΨb - (redJet z₂.z x).dΨb) 2 Q.μ ≤ X := by
    rw [dist_redJet_dΨb]; exact le_add_self.trans (hc 7)
  rw [← hX]
  calc jetDist Q (redJet z₁.z) (redJet z₂.z) ≤ X + X + X + X + X + X + X + X + X + X := by
        unfold jetDist; gcongr
    _ = 10 * X := by ring

end PacketToJet

/-! ### Dual-norm bound of first-variation integrals -/

section DualBound

variable {T : ℝ} {C : Type} [Fintype C] {left : C → Bool} {r : ℕ} {K : CylRegion T}

/-- `|∫Φ₁(τ) - ∫Φ₂(τ)| ≤ ‖Φ₁ - Φ₂‖_{L¹} sup‖τ‖`. -/
theorem abs_integral_sub_le {μ : Measure E4} {Φ₁ Φ₂ : E4 → RJet C →L[ℝ] ℝ} {τ : E4 → RJet C}
    {M : ℝ} (hτ : ∀ x, ‖τ x‖ ≤ M) (h₁ : Integrable (fun x => Φ₁ x (τ x)) μ)
    (h₂ : Integrable (fun x => Φ₂ x (τ x)) μ) :
    ENNReal.ofReal |∫ x, Φ₁ x (τ x) ∂μ - ∫ x, Φ₂ x (τ x) ∂μ| ≤
      eLpNorm (fun x => Φ₁ x - Φ₂ x) 1 μ * ENNReal.ofReal M := by
  rw [← integral_sub h₁ h₂, ← Real.enorm_eq_ofReal_abs]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [eLpNorm_one_eq_lintegral_enorm, ← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x => ?_
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e : Φ₁ x (τ x) - Φ₂ x (τ x) = (Φ₁ x - Φ₂ x) (τ x) := rfl
  rw [e]
  exact ((Φ₁ x - Φ₂ x).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hτ x) (norm_nonneg _))

theorem continuousOn_cov_redJet {Q : ChartBox T} {Ke : Set CoframeFibre} (hsub : Ke ⊆ coframeGL)
    {Cov : RJet C → RJet C →L[ℝ] ℝ} (hCov : ContinuousOn Cov (jetGL C))
    (z : SmoothFields T left) (hz : ∀ x ∈ closure Q.set, z.z.e x ∈ Ke) :
    ContinuousOn (fun x => Cov (redJet z.z x)) (closure Q.set) :=
  hCov.comp ((continuousOn_redJet z).mono Q.closure_subset_cylSlab)
    (fun x hx => hsub (hz x hx))

theorem integrableOn_cov {Q : ChartBox T} {Ke : Set CoframeFibre} (hsub : Ke ⊆ coframeGL)
    {Cov : RJet C → RJet C →L[ℝ] ℝ} (hCov : ContinuousOn Cov (jetGL C))
    (z : SmoothFields T left) (hz : ∀ x ∈ closure Q.set, z.z.e x ∈ Ke) (v : CrTest left r K) :
    Integrable (fun x => Cov (redJet z.z x) (testJet v.val x)) Q.μ :=
  (((continuousOn_cov_redJet hsub hCov z hz).clm_apply
    (continuous_testJet v).continuousOn).integrableOn_compact Q.isCompact_closure).mono_set
    subset_closure

theorem aesm_cov {Q : ChartBox T} {Ke : Set CoframeFibre} (hsub : Ke ⊆ coframeGL)
    {Cov : RJet C → RJet C →L[ℝ] ℝ} (hCov : ContinuousOn Cov (jetGL C))
    (z : SmoothFields T left) (hz : ∀ x ∈ closure Q.set, z.z.e x ∈ Ke) :
    AEStronglyMeasurable (fun x => Cov (redJet z.z x)) Q.μ :=
  ((continuousOn_cov_redJet hsub hCov z hz).mono subset_closure).aestronglyMeasurable
    Q.isOpen.measurableSet

end DualBound

/-! ### `prop:variation-continuity` -/

section VariationContinuity

variable {Ysec : Type} [Fintype Ysec] (FC : FermionCarrier Ysec) {T : ℝ} {left : FC.C → Bool}

set_option maxHeartbeats 4000000 in
/-- **`prop:variation-continuity`** (first-variation continuity from primitive fields): on the
bounded strong-packet class of a chart `Q = (t₀,t₁) × (0,1)³` and banks in a compact physical set
`P`, the first variation of each sector is Lipschitz in `d_K` in the dual test norm of a region
`K` with time support in `(t₀,t₁)`:
`|D𝒮_{b,θ₁}(z₁)[v] - D𝒮_{b,θ₂}(z₂)[v]| ≤ C_K d_K(z₁,θ₁; z₂,θ₂) ‖v‖_{C^r}`. -/
theorem variation_continuity {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    {K : CylRegion T} (hK : ∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) {r : ℕ} (hr : 1 ≤ r)
    {Ke : Set CoframeFibre} (hKe : IsCompactCoframeSet Ke) {P : Set (CoefficientBank Ysec)}
    (hP : IsCompactBankSet P) {Ly My : ℝ} (hY : YukawaLipOn FC P Ly My) {B : ℝ≥0∞}
    (hB : B ≠ ⊤) :
    ∃ CK : ℝ≥0∞, CK ≠ ⊤ ∧ ∀ (z₁ z₂ : SmoothFields T left) (θ₁ θ₂ : CoefficientBank Ysec),
      θ₁ ∈ P → θ₂ ∈ P → PacketBound (slabChart t₀ t₁ h0 h01 h1) Ke B z₁ →
      PacketBound (slabChart t₀ t₁ h0 h01 h1) Ke B z₂ → ∀ (b : Sector) (v : CrTest left r K),
        ENNReal.ofReal |firstVariation T FC θ₁ b z₁.z v.val -
            firstVariation T FC θ₂ b z₂.z v.val| ≤
          CK * dK (slabChart t₀ t₁ h0 h01 h1) z₁ θ₁ z₂ θ₂ * ENNReal.ofReal ‖v‖ := by
  obtain ⟨c, Mb, hBB⟩ := exists_bankBounds hP
  obtain ⟨Cs, hCst, hCs⟩ := exists_spinor_L4 (C := FC.C) (slabChart t₀ t₁ h0 h01 h1 (T := T))
  have hB' : (1 + Cs) * B ≠ ⊤ := ENNReal.mul_ne_top (by finiteness) hB
  have hKe' : IsCompact Ke := hKe.1
  have hsub : Ke ⊆ coframeGL := hKe.2.trans coframeChart_subset_GL
  obtain ⟨Cg, hCg, hg⟩ := grav_lipschitz (C := FC.C) (Q := slabChart t₀ t₁ h0 h01 h1 (T := T))
    hKe' hsub (P := P) hBB.pos hBB.nonneg (fun θ hθ => ⟨hBB.kappa θ hθ, hBB.Lambda θ hθ⟩) hB'
  obtain ⟨Cb, hCb, hb⟩ := boson_lipschitz (C := FC.C) (slabChart t₀ t₁ h0 h01 h1 (T := T))
    hKe' hsub hBB hB'
  obtain ⟨Cd, hCd, hd⟩ := dirac_lipschitz FC (slabChart t₀ t₁ h0 h01 h1 (T := T)) hKe' hsub hY hB'
  refine ⟨(Cg + (Cb + Cd)) * (10 * (1 + Cs) + 1), by finiteness, ?_⟩
  intro z₁ z₂ θ₁ θ₂ hθ₁ hθ₂ hp₁ hp₂ b v
  have hJ₁ := hp₁.jetBound hCs
  have hJ₂ := hp₂.jetBound hCs
  obtain ⟨k, hk⟩ : ∃ k : ℝ≥0∞, k = 10 * (1 + Cs) + 1 := ⟨_, rfl⟩
  have hdist : jetDist (slabChart t₀ t₁ h0 h01 h1) (redJet z₁.z) (redJet z₂.z) +
      bankDist θ₁ θ₂ ≤ k * dK (slabChart t₀ t₁ h0 h01 h1) z₁ θ₁ z₂ θ₂ := by
    calc _ ≤ 10 * ((1 + Cs) * dK (slabChart t₀ t₁ h0 h01 h1) z₁ θ₁ z₂ θ₂) +
          dK (slabChart t₀ t₁ h0 h01 h1) z₁ θ₁ z₂ θ₂ :=
          add_le_add (jetDist_redJet_le hCs z₁ z₂ θ₁ θ₂) (edist_bank_le_dK _ z₁ θ₁ z₂ θ₂)
      _ = _ := by rw [hk]; ring
  have hτ : ∀ x, ‖testJet v.val x‖ ≤ ‖v‖ := norm_testJet_le hr v
  rw [← hk]
  cases b
  · rw [gravVariation_eq_cov FC θ₁ h0 h01 h1 hK z₁ v hKe' hsub hp₁.chart,
      gravVariation_eq_cov FC θ₂ h0 h01 h1 hK z₂ v hKe' hsub hp₂.chart]
    have hc₁ := (CovSmooth.contDiffOn_gravCov (C := FC.C) (n := 0) θ₁).continuousOn
    have hc₂ := (CovSmooth.contDiffOn_gravCov (C := FC.C) (n := 0) θ₂).continuousOn
    refine (abs_integral_sub_le hτ (integrableOn_cov hsub hc₁ z₁ hp₁.chart v)
      (integrableOn_cov hsub hc₂ z₂ hp₂.chart v)).trans ?_
    calc _ ≤ Cg * (k * dK (slabChart t₀ t₁ h0 h01 h1) z₁ θ₁ z₂ θ₂) * ENNReal.ofReal ‖v‖ := by
          gcongr
          exact (hg _ _ _ _ hθ₁ hθ₂ hJ₁ hJ₂).trans (by gcongr)
      _ ≤ _ := by
          rw [← mul_assoc]
          gcongr ?_ * _ * _ * _
          exact le_self_add
  · rw [smVariation_eq_cov FC θ₁ h0 h01 h1 (fun p hp => Ioo_subset_Icc_self (hK p hp)) z₁ v hKe'
      hsub hp₁.chart, smVariation_eq_cov FC θ₂ h0 h01 h1 (fun p hp => Ioo_subset_Icc_self (hK p hp))
      z₂ v hKe' hsub hp₂.chart]
    have hb₁ := (CovSmooth.contDiffOn_bosonCov (C := FC.C) (n := 0) θ₁).continuousOn
    have hb₂ := (CovSmooth.contDiffOn_bosonCov (C := FC.C) (n := 0) θ₂).continuousOn
    have hd₁ := (CovSmooth.contDiffOn_diracCov (n := 0) FC θ₁).continuousOn
    have hd₂ := (CovSmooth.contDiffOn_diracCov (n := 0) FC θ₂).continuousOn
    refine (abs_integral_sub_le (Φ₁ := fun x => bosonCov θ₁ (redJet z₁.z x) +
        diracCov FC θ₁ (redJet z₁.z x)) (Φ₂ := fun x => bosonCov θ₂ (redJet z₂.z x) +
        diracCov FC θ₂ (redJet z₂.z x)) hτ
      (integrableOn_cov hsub (hb₁.add hd₁) z₁ hp₁.chart v)
      (integrableOn_cov hsub (hb₂.add hd₂) z₂ hp₂.chart v)).trans ?_
    have hsplit := eLpNorm_sum2_sub (aesm_cov hsub hb₁ z₁ hp₁.chart)
      (aesm_cov hsub hb₂ z₂ hp₂.chart) (aesm_cov hsub hd₁ z₁ hp₁.chart)
      (aesm_cov hsub hd₂ z₂ hp₂.chart)
    calc _ ≤ (Cb * (k * dK (slabChart t₀ t₁ h0 h01 h1) z₁ θ₁ z₂ θ₂) +
          Cd * (k * dK (slabChart t₀ t₁ h0 h01 h1) z₁ θ₁ z₂ θ₂)) * ENNReal.ofReal ‖v‖ := by
          gcongr
          refine hsplit.trans (add_le_add ?_ ?_)
          · exact (hb _ _ _ _ hθ₁ hθ₂ hJ₁ hJ₂).trans (by gcongr)
          · exact (hd _ _ _ _ hθ₁ hθ₂ hJ₁ hJ₂).trans (by gcongr)
      _ = (Cb + Cd) * k * dK (slabChart t₀ t₁ h0 h01 h1) z₁ θ₁ z₂ θ₂ * ENNReal.ofReal ‖v‖ := by
          ring
      _ ≤ _ := by
          gcongr ?_ * _ * _ * _
          exact le_add_self

end VariationContinuity

/-! ### Non-vacuity -/

section NonVacuity

/-- The flat fields lie in the bounded strong-packet class of every slab chart. -/
theorem flat_packetBound {T t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧
      PacketBound (slabChart t₀ t₁ h0 h01 h1) {flatCoframe} B ((flatRegulator T).fields 0) :=
  exists_packetBound _ _ fun _ _ => rfl

/-- **Non-vacuity of `variation_continuity`**: all hypotheses are met by the trivial carrier, the
flat coframe set, the physical bank and the flat fields (which lie in the class). -/
example {T t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) {K : CylRegion T}
    (hK : ∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧
      PacketBound (slabChart t₀ t₁ h0 h01 h1) {flatCoframe} B ((flatRegulator T).fields 0) ∧
      ∃ CK : ℝ≥0∞, CK ≠ ⊤ ∧ ∀ (b : Sector) (v : CrTest (trivialCarrier Unit).left 4 K),
        ENNReal.ofReal |firstVariation T (trivialCarrier Unit) physicalBank b
            ((flatRegulator T).fields 0).z v.val -
          firstVariation T (trivialCarrier Unit) physicalBank b
            ((flatRegulator T).fields 0).z v.val| ≤
          CK * dK (slabChart t₀ t₁ h0 h01 h1) ((flatRegulator T).fields 0) physicalBank
            ((flatRegulator T).fields 0) physicalBank * ENNReal.ofReal ‖v‖ := by
  obtain ⟨B, hB, hp⟩ := flat_packetBound h0 h01 h1
  obtain ⟨CK, hCK, h⟩ := variation_continuity (trivialCarrier Unit) h0 h01 h1 hK (r := 4)
    (by norm_num) isCompactCoframeSet_flat isCompactBankSet_physical (yukawaLipOn_trivial _) hB
  exact ⟨B, hB, hp, CK, hCK, fun b v => h _ _ _ _ rfl rfl hp hp b v⟩

end NonVacuity

end VarLip
end EinsteinSM
end RenewalGeometry
