/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedDiracStressJet
import RenewalGeometry.Continuum.GeneratedCoupledMatter

/-!
# The stress Noether identity with the Dirac stress: the actual jets of a tuple

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`,
coupled spinors (task: the Dirac stress Noether identity).  The jet-level conservation law
`GenDSJ.div_kin_onshell` is instantiated for the actual jets of a smooth tuple:

* `tr_ω`, `tr_F`, `F_comm` — the co-spinor connection and gauge curvature are minus the transposes
  of the spinor ones (`GenDiracCur.DiracPairing`), and the gauge curvature commutes with Clifford
  multiplication;
* `fd_ψ`, `fd_X`, **`fd_kin`** — the frame derivatives of the spinor field, of its covariant
  derivative field `X_A = ∇_AΨ` and of the kinetic Dirac stress field are the jets of
  `GenDSJ.dkinJ`.
-/

open Filter Topology Set Finset
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenDSN

open SobolevOpen (pd)
open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci
  ActualJetBridge ActualJetCompleteForcing ActualJetRecon ActualJetState SymHypEnergy GenSFJ
  GenCplCov GenCplN GenDSJ ActualJetSpinor

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {S₀ : Type*} [NormedAddCommGroup S₀] [NormedSpace ℝ S₀] [FiniteDimensional ℝ S₀]

/-! ### Transposition of the co-spinor jets -/

section Transpose

variable {SM : SMData (MatLie m) V S S'} (hP : GenDiracCur.DiracPairing SM)
  (J : ActualJet (MatLie m) V S S')

theorem tr_ω (a : Fin 4) (φ : S') (y : S) :
    hP.P ((J.LJ SM.Db).ω a φ) y = -hP.P φ ((J.LJ SM.D).ω a y) := by
  show hP.P ((spinPart SM.Db.Fr (J.FJ.G a) + ∑ μ, J.FJ.e a μ • SM.Db.ρ (J.A μ)) φ) y =
    -hP.P φ ((spinPart SM.D.Fr (J.FJ.G a) + ∑ μ, J.FJ.e a μ • SM.D.ρ (J.A μ)) y)
  simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_add, map_sum,
    map_smul, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    hP.P_spin (J.FJ.G a) (fun c d => J.FJ.G_anti a c d), hP.ρ_tr, mul_neg, Finset.sum_neg_distrib,
    neg_add]

theorem tr_F (a b : Fin 4) (φ : S') (y : S) :
    hP.P ((J.LJ SM.Db).F a b φ) y = -hP.P φ ((J.LJ SM.D).F a b y) := by
  have e1 : (J.LJ SM.D).F a b = ∑ μ, ∑ ν,
      (J.FJ.e a μ * J.FJ.e b ν) • (SM.D.ρ (J.dA μ ν) - SM.D.ρ (J.dA ν μ) +
        (SM.D.ρ (J.A μ) * SM.D.ρ (J.A ν) - SM.D.ρ (J.A ν) * SM.D.ρ (J.A μ))) :=
    J.FJ.frameF_eq SM.D.Fr (J.hε SM.D) (fun μ => SM.D.ρ (J.A μ)) (fun γ μ => SM.D.ρ (J.dA γ μ))
      (fun μ b => SM.D.comm (J.A μ) b) a b
  have e2 : (J.LJ SM.Db).F a b = ∑ μ, ∑ ν,
      (J.FJ.e a μ * J.FJ.e b ν) • (SM.Db.ρ (J.dA μ ν) - SM.Db.ρ (J.dA ν μ) +
        (SM.Db.ρ (J.A μ) * SM.Db.ρ (J.A ν) - SM.Db.ρ (J.A ν) * SM.Db.ρ (J.A μ))) :=
    J.FJ.frameF_eq SM.Db.Fr (J.hε SM.Db) (fun μ => SM.Db.ρ (J.A μ))
      (fun γ μ => SM.Db.ρ (J.dA γ μ)) (fun μ b => SM.Db.comm (J.A μ) b) a b
  rw [e2, e1]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply,
    Module.End.mul_apply, map_sum, map_smul, map_add, map_sub, LinearMap.add_apply,
    LinearMap.sub_apply, smul_eq_mul, hP.ρ_tr, map_neg, LinearMap.neg_apply, neg_neg,
    Finset.sum_neg_distrib, mul_neg, neg_add, neg_sub]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  ring

theorem F_comm (D : DiracData (MatLie m) V S₀) (a b c : Fin 4) :
    (J.LJ D).F a b * D.Fr.c c = D.Fr.c c * (J.LJ D).F a b := by
  have e : (J.LJ D).F a b = ∑ μ, ∑ ν,
      (J.FJ.e a μ * J.FJ.e b ν) • (D.ρ (J.dA μ ν) - D.ρ (J.dA ν μ) +
        (D.ρ (J.A μ) * D.ρ (J.A ν) - D.ρ (J.A ν) * D.ρ (J.A μ))) :=
    J.FJ.frameF_eq D.Fr (J.hε D) (fun μ => D.ρ (J.A μ)) (fun γ μ => D.ρ (J.dA γ μ))
      (fun μ b => D.comm (J.A μ) b) a b
  rw [e, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [smul_mul_assoc, mul_smul_comm]
  congr 1
  simp only [add_mul, sub_mul, mul_add, mul_sub, mul_assoc, D.comm]
  simp only [← mul_assoc, D.comm]

theorem tr_M (w : V) (φ : S') (y : S) :
    hP.P (mass SM.Db.m0 SM.Db.L w φ) y = -hP.P φ (mass SM.D.m0 SM.D.L w y) := by
  simp only [mass, LinearMap.add_apply, map_add, hP.m0_tr, hP.L_tr, neg_add]

end Transpose

/-! ### The frame derivatives of the spinor fields are the jets -/

section Fields

variable (z : Tuple m V S S')

theorem fd_ψ (ψf : ST 3 → S₀) (C : Fin 4) (x : ST 3) :
    fd z ψf C x = dψf (z.FJ x) (fun γ => pd ψf γ x) C := by
  rw [fd_eq_sum]
  rfl

/-- The covariant-derivative field `X_A = ∇_AΨ` of a spinor field. -/
def Xf (D : DiracData (MatLie m) V S₀) (ψf : ST 3 → S₀) (y : ST 3) : Fin 4 → S₀ :=
  fun B => (z.jet y).Xs D (ψf y) (fun γ => pd ψf γ y) B

theorem contDiff_Xf (D : DiracData (MatLie m) V S₀) {ψf : ST 3 → S₀} (hψ : ContDiff ℝ ∞ ψf) :
    ContDiff ℝ ∞ (Xf z D ψf) :=
  contDiff_pi.2 fun B => z.contDiff_Xs D hψ B

theorem fd_X (D : DiracData (MatLie m) V S₀) {ψf : ST 3 → S₀} (hψ : ContDiff ℝ ∞ ψf)
    (x : ST 3) (C B : Fin 4) :
    fd z (Xf z D ψf) C x B = dcov ((z.jet x).LJ D).ω ((z.jet x).LJ D).dω (ψf x)
      (dψf (z.FJ x) (fun γ => pd ψf γ x))
      (ddψf (z.FJ x) (fun γ => pd ψf γ x) (fun δ γ => pd (pd ψf γ) δ x)) C B := by
  rw [fd_apply z ((contDiff_Xf z D hψ).differentiable (by simp) x) C B, fd_eq_sum]
  have hpd : ∀ γ, pd (fun y => Xf z D ψf y B) γ x = (z.jet x).dXs D (ψf x)
      (fun γ => pd ψf γ x) (fun δ γ => pd (pd ψf γ) δ x) γ B := fun γ =>
    pd_eq_of_line ((z.contDiff_Xs D hψ B).differentiable (by simp) x) (z.line_Xs x γ D hψ B)
  simp only [hpd]
  have h := ActualJetSpinor.dcov_eq (z.FJ x) D.Fr ((z.jet x).hε D) (fun μ => D.ρ (z.A x μ))
    (fun γ μ => D.ρ (pd z.A γ x μ)) (fun μ b => D.comm (z.A x μ) b) (ψf x)
    (fun γ => pd ψf γ x) (fun δ γ => pd (pd ψf γ) δ x) C B
  exact h.symm

variable {SM : SMData (MatLie m) V S S'}

/-- **The frame derivative of the kinetic Dirac stress field is the jet `dkinJ`.** -/
theorem fd_kin (hC : GenDStress.CoupledDirac SM) (x : ST 3) (C A B : Fin 4) :
    fd z (fun y => GenDStress.kinT SM.D hC.P (z.ψ y) (Xf z SM.D z.ψ y) (z.ψb y)
        (Xf z SM.Db z.ψb y) A B) C x =
      dkinJ SM.D.Fr hC.P (z.ψ x) (dψf (z.FJ x) (fun γ => pd z.ψ γ x)) (Xf z SM.D z.ψ x)
        (fun C B => dcov ((z.jet x).LJ SM.D).ω ((z.jet x).LJ SM.D).dω (z.ψ x)
          (dψf (z.FJ x) (fun γ => pd z.ψ γ x))
          (ddψf (z.FJ x) (fun γ => pd z.ψ γ x) (fun δ γ => pd (pd z.ψ γ) δ x)) C B)
        (z.ψb x) (dψf (z.FJ x) (fun γ => pd z.ψb γ x)) (Xf z SM.Db z.ψb x)
        (fun C B => dcov ((z.jet x).LJ SM.Db).ω ((z.jet x).LJ SM.Db).dω (z.ψb x)
          (dψf (z.FJ x) (fun γ => pd z.ψb γ x))
          (ddψf (z.FJ x) (fun γ => pd z.ψb γ x) (fun δ γ => pd (pd z.ψb γ) δ x)) C B)
        C A B := by
  rw [GenCplDiv.fd_kinT z SM.D hC.P z.ψ_smooth z.ψb_smooth (contDiff_Xf z SM.D z.ψ_smooth)
    (contDiff_Xf z SM.Db z.ψb_smooth) x A B C]
  simp only [fd_ψ, fd_X z SM.D z.ψ_smooth, fd_X z SM.Db z.ψb_smooth]
  rfl

end Fields

/-! ### The covariant derivative of the coframe -/

section Coframe

open ActualJetRecon in
/-- **The covariant derivative of the coframe** (algebra on a frame 2-jet):
`∂_eθ^A{}_a - Γ^l{}_{ea}θ^A{}_l = -Σ_{C,D}θ^C{}_eΓ_{CD}{}^Aθ^D{}_a` with `Γ_{CD}{}^A = ε_AG_{CDA}`. -/
theorem nabla_cof_alg (F : FrameJet (Fin 4) (Fin 4)) (A a e : Fin 4) :
    F.ε A * ∑ ν, (F.dg e a ν * F.e A ν + F.g a ν * F.de e A ν) -
      ∑ l, F.Γ l e a * cof F.g F.ε F.e A l =
    -∑ C, ∑ D, cof F.g F.ε F.e C e * (F.ε A * F.G C D A) * cof F.g F.ε F.e D a := by
  -- step 1: metric compatibility
  have h1 : F.ε A * ∑ ν, (F.dg e a ν * F.e A ν + F.g a ν * F.de e A ν) -
      ∑ l, F.Γ l e a * cof F.g F.ε F.e A l = F.ε A * ∑ l, F.g a l * F.Ne A e l := by
    unfold cof FrameJet.Ne cv1
    simp only [F.compat, Finset.sum_mul, add_mul, Finset.sum_add_distrib, mul_add,
      Finset.mul_sum]
    have hg := F.g_symm
    have e1 : ∑ ν, ∑ l, F.ε A * (F.g ν l * F.Γ l e a * F.e A ν) =
        ∑ l, F.Γ l e a * ∑ ν, F.ε A * (F.g l ν * F.e A ν) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ν _ => ?_
      rw [hg ν l]; ring
    have e2 : ∑ ν, ∑ l, F.ε A * (F.g a l * F.Γ l e ν * F.e A ν) =
        ∑ l, ∑ σ, F.ε A * (F.g a l * (F.Γ l e σ * F.e A σ)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun σ _ => ?_
      ring
    rw [e1, e2]
    simp only [Finset.mul_sum]
    ring_nf
    have hsw : ∑ x, ∑ x_1, F.Γ x e a * F.ε A * F.g x x_1 * F.e A x_1 =
        ∑ x, ∑ x_1, F.ε A * F.Γ x e a * F.g x x_1 * F.e A x_1 :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [hsw]
    ring
  -- step 2: the frame expansion of `∇_ee_A`
  have h2 : ∀ l, F.Ne A e l = ∑ C, cof F.g F.ε F.e C e * ∑ D, F.ε D * F.G C A D * F.e D l := by
    intro l
    have := inv_vec F (fun γ => F.Ne A γ l) e
    simp only [smul_eq_mul] at this
    rw [this]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [F.Ne_expand C A l]
  rw [h1]
  simp only [h2]
  -- step 3: lower the index and use the antisymmetry of `G`
  have h3 : ∀ C D, ∑ l, F.g a l * (F.ε D * F.G C A D * F.e D l) =
      F.G C A D * cof F.g F.ε F.e D a := by
    intro C D
    unfold cof
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have h4 : ∀ l, F.g a l * ∑ C, cof F.g F.ε F.e C e * ∑ D, F.ε D * F.G C A D * F.e D l =
      ∑ C, ∑ D, cof F.g F.ε F.e C e * (F.g a l * (F.ε D * F.G C A D * F.e D l)) := by
    intro l
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun D _ => ?_
    ring
  simp only [h4]
  rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun D _ => ?_
  rw [← Finset.mul_sum, h3, F.G_anti C D A]
  ring

end Coframe

section CoframeAlg

/-- `θ^C(e_D) = δ_{CD}`. -/
theorem cof_e (F : FrameJet (Fin 4) (Fin 4)) (C D : Fin 4) :
    ∑ μ, cof F.g F.ε F.e C μ * F.e D μ = if C = D then 1 else 0 := by
  have h := F.orth D C
  unfold ipg at h
  have e : ∑ μ, cof F.g F.ε F.e C μ * F.e D μ = F.ε C * ∑ μ, ∑ ν, F.g μ ν * F.e D μ * F.e C ν := by
    unfold cof
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun ν _ => ?_
    ring
  rw [e, h]
  by_cases hCD : C = D
  · subst hCD
    simp only [if_true]
    have := F.sign_sq C
    nlinarith [this]
  · simp [hCD, Ne.symm hCD]

/-- `g^{ea}θ^D{}_a = ε_De_D{}^e`. -/
theorem gi_cof (F : FrameJet (Fin 4) (Fin 4)) (e D : Fin 4) :
    ∑ a, F.gi e a * cof F.g F.ε F.e D a = F.ε D * F.e D e := by
  have hinv : ∀ ν, ∑ a, F.gi e a * F.g a ν = if e = ν then 1 else 0 := by
    intro ν
    have h1 := F.hinv ν e
    have h2 : ∑ a, F.gi e a * F.g a ν = ∑ b, F.g ν b * F.gi b e :=
      Finset.sum_congr rfl fun a _ => by rw [F.gi_symm e a, F.g_symm a ν, mul_comm]
    rw [h2, h1]
    by_cases h : ν = e
    · simp [h]
    · simp [h, Ne.symm h]
  unfold cof
  have e1 : ∑ a, F.gi e a * (F.ε D * ∑ ν, F.g a ν * F.e D ν) =
      F.ε D * ∑ ν, (∑ a, F.gi e a * F.g a ν) * F.e D ν := by
    rw [Finset.mul_sum]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun a _ => by ring
  rw [e1]
  simp only [hinv, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- `g^{ea}θ^C{}_eθ^D{}_a = ε_Cδ_{CD}`. -/
theorem gi_cof_cof (F : FrameJet (Fin 4) (Fin 4)) (C D : Fin 4) :
    ∑ e, ∑ a, F.gi e a * cof F.g F.ε F.e C e * cof F.g F.ε F.e D a =
      if C = D then F.ε C else 0 := by
  have e1 : ∀ e, ∑ a, F.gi e a * cof F.g F.ε F.e C e * cof F.g F.ε F.e D a =
      cof F.g F.ε F.e C e * (F.ε D * F.e D e) := by
    intro e
    rw [← gi_cof F e D, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  simp only [e1]
  have e2 : ∑ e, cof F.g F.ε F.e C e * (F.ε D * F.e D e) =
      F.ε D * ∑ e, cof F.g F.ε F.e C e * F.e D e := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by ring
  rw [e2, cof_e]
  by_cases h : C = D
  · subst h; simp
  · simp [h]

end CoframeAlg

section RemDiv

theorem swap22 {M : Type*} [AddCommMonoid M] (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem sum3_rot {M : Type*} [AddCommMonoid M] (f : Fin 4 → Fin 4 → Fin 4 → M) :
    ∑ l, ∑ A, ∑ B, f l A B = ∑ A, ∑ B, ∑ l, f l A B := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun A _ => Finset.sum_comm

/-- **The divergence remainder of a frame tensor in frame-covariant form** (algebra): if the
derivative `dθ` of the coframe obeys `∂_eθ^A{}_a - Γ^l{}_{ea}θ^A{}_l = -θ^C{}_eΓ'_{CD}{}^Aθ^D{}_a`,
then the Christoffel/coframe-derivative remainder of `∇^a(θ^A{}_aθ^B{}_bK_{AB})` is
`-θ^B{}_bε_A(Γ'_{AA}{}^DK_{DB} + Γ'_{AB}{}^DK_{AD})`. -/
theorem remDiv_alg (F : FrameJet (Fin 4) (Fin 4)) (dθ : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (Γ' : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hdθ : ∀ e A a, dθ e A a - ∑ l, F.Γ l e a * cof F.g F.ε F.e A l =
      -∑ C, ∑ D, cof F.g F.ε F.e C e * Γ' C D A * cof F.g F.ε F.e D a)
    (K : Fin 4 → Fin 4 → ℝ) (b : Fin 4) :
    ∑ e, ∑ a, F.gi e a * (∑ A, ∑ B, (dθ e A a * cof F.g F.ε F.e B b +
        cof F.g F.ε F.e A a * dθ e B b) * K A B -
      ∑ l, F.Γ l e a * (∑ A, ∑ B, cof F.g F.ε F.e A l * cof F.g F.ε F.e B b * K A B) -
      ∑ l, (∑ A, ∑ B, cof F.g F.ε F.e A a * cof F.g F.ε F.e B l * K A B) * F.Γ l e b) =
    -∑ B, cof F.g F.ε F.e B b * ∑ A, F.ε A *
      (∑ D, Γ' A A D * K D B + ∑ D, Γ' A B D * K A D) := by
  set θ := cof F.g F.ε F.e with hθ
  -- pointwise: the covariant derivative of the coframe
  have hpt : ∀ e a, ∑ A, ∑ B, (dθ e A a * θ B b + θ A a * dθ e B b) * K A B -
      ∑ l, F.Γ l e a * (∑ A, ∑ B, θ A l * θ B b * K A B) -
      ∑ l, (∑ A, ∑ B, θ A a * θ B l * K A B) * F.Γ l e b =
      ∑ A, ∑ B, K A B * ((dθ e A a - ∑ l, F.Γ l e a * θ A l) * θ B b +
        θ A a * (dθ e B b - ∑ l, F.Γ l e b * θ B l)) := by
    intro e a
    have t1 : ∑ l, F.Γ l e a * (∑ A, ∑ B, θ A l * θ B b * K A B) =
        ∑ A, ∑ B, K A B * ((∑ l, F.Γ l e a * θ A l) * θ B b) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [sum3_rot]
      exact Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ =>
        Finset.sum_congr rfl fun l _ => by ring
    have t2 : ∑ l, (∑ A, ∑ B, θ A a * θ B l * K A B) * F.Γ l e b =
        ∑ A, ∑ B, K A B * (θ A a * ∑ l, F.Γ l e b * θ B l) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [sum3_rot]
      exact Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ =>
        Finset.sum_congr rfl fun l _ => by ring
    rw [t1, t2, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun B _ => ?_
    ring
  simp only [hpt, hdθ]
  -- contract with the inverse metric
  have hc : ∀ C D, ∑ e, ∑ a, F.gi e a * θ C e * θ D a = if C = D then F.ε C else 0 :=
    gi_cof_cof F
  have hX : ∀ A, ∑ e, ∑ a, F.gi e a * ∑ C, ∑ D, θ C e * Γ' C D A * θ D a =
      ∑ C, F.ε C * Γ' C C A := by
    intro A
    have e1 : ∑ e, ∑ a, F.gi e a * ∑ C, ∑ D, θ C e * Γ' C D A * θ D a =
        ∑ e, ∑ a, ∑ C, ∑ D, Γ' C D A * (F.gi e a * θ C e * θ D a) := by
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun D _ => by ring
    rw [e1, swap22]
    simp only [← Finset.mul_sum, hc]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [Finset.sum_eq_single C (fun D _ hD => by rw [if_neg (Ne.symm hD)]; simp) (by simp),
      if_pos rfl]
    ring
  have hY : ∀ A B, ∑ e, ∑ a, F.gi e a * (θ A a * ∑ C, ∑ D, θ C e * Γ' C D B * θ D b) =
      F.ε A * ∑ D, Γ' A D B * θ D b := by
    intro A B
    have e1 : ∑ e, ∑ a, F.gi e a * (θ A a * ∑ C, ∑ D, θ C e * Γ' C D B * θ D b) =
        ∑ e, ∑ a, ∑ C, ∑ D, Γ' C D B * θ D b * (F.gi e a * θ C e * θ A a) := by
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun D _ => by ring
    rw [e1, swap22]
    simp only [← Finset.mul_sum, hc]
    rw [Finset.sum_eq_single A (fun C _ hC => by
      refine Finset.sum_eq_zero fun D _ => ?_
      rw [if_neg hC]; simp) (by simp)]
    simp only [if_true, Finset.mul_sum]
    exact Finset.sum_congr rfl fun D _ => by ring
  -- assemble
  have e2 : ∀ e a, F.gi e a * ∑ A, ∑ B, K A B *
      ((-∑ C, ∑ D, θ C e * Γ' C D A * θ D a) * θ B b +
        θ A a * (-∑ C, ∑ D, θ C e * Γ' C D B * θ D b)) =
      ∑ A, ∑ B, (-(K A B * θ B b) * (F.gi e a * ∑ C, ∑ D, θ C e * Γ' C D A * θ D a) -
        K A B * (F.gi e a * (θ A a * ∑ C, ∑ D, θ C e * Γ' C D B * θ D b))) := by
    intro e a
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun B _ => ?_
    ring
  simp only [e2]
  rw [swap22]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hX, hY]
  -- relabel to the target
  have r1 : ∑ A, ∑ B, -(K A B * θ B b) * ∑ C, F.ε C * Γ' C C A =
      -∑ B, θ B b * ∑ A, F.ε A * ∑ D, Γ' A A D * K D B := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun B _ => ?_
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun D _ => by ring
  have r2 : ∑ A, ∑ B, K A B * (F.ε A * ∑ D, Γ' A D B * θ D b) =
      ∑ B, θ B b * ∑ A, F.ε A * ∑ D, Γ' A B D * K A D := by
    simp only [Finset.mul_sum]
    symm
    rw [sum3_rot]
    exact Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ =>
      Finset.sum_congr rfl fun D _ => by ring
  rw [r1, r2]
  simp only [mul_add, Finset.sum_add_distrib]
  ring

end RemDiv

/-! ### The covariant divergence of a frame tensor field -/

section CovDiv

variable (z : Tuple m V S S')

theorem θF_eq (y : ST 3) (A a : Fin 4) :
    GenCplSD.θF z y A a = cof (z.FJ y).g (z.FJ y).ε (z.FJ y).e A a := by
  have h := congrFun (congrFun (z.jet y).cof_eq A) a
  rw [GenCplN.jetAF] at h
  exact h

theorem pd_θF (x : ST 3) (A a e : Fin 4) :
    pd (fun y => GenCplSD.θF z y A a) e x = (z.FJ x).ε A *
      ∑ ν, ((z.FJ x).dg e a ν * (z.FJ x).e A ν + (z.FJ x).g a ν * (z.FJ x).de e A ν) := by
  have e1 : (fun y => GenCplSD.θF z y A a) = fun y => lorentzSign A * ∑ ν, z.g y a ν * z.e y A ν := by
    funext y
    rw [θF_eq]
    rfl
  rw [e1]
  have hs : ContDiff ℝ ∞ (fun y => lorentzSign A * ∑ ν, z.g y a ν * z.e y A ν) := by
    have h1 := z.contDiff_gc
    have h2 := z.contDiff_e
    fun_prop
  refine pd_eq_of_line (hs.differentiable (by simp) x) ?_
  have h := (HasDerivAt.fun_sum (u := Finset.univ) fun ν _ =>
    (z.line_g x e a ν).fun_mul (z.line_e x e A ν)).const_mul (lorentzSign A)
  simp only [zero_smul, add_zero] at h
  exact h.congr_deriv rfl

/-- **The remainder of the divergence of a frame tensor in frame-covariant form**. -/
theorem remDiv_cov (K : ST 3 → Fin 4 → Fin 4 → ℝ) (x : ST 3) (b : Fin 4) :
    GenCplDiv.remDiv z K x b = -∑ B, GenCplSD.θF z x B b * ∑ A, lorentzSign A *
      (∑ D, ΓF z x A A D * K x D B + ∑ D, ΓF z x A B D * K x A D) := by
  have h := remDiv_alg (z.FJ x) (fun e A a => pd (fun y => GenCplSD.θF z y A a) e x) (ΓF z x)
    (fun e A a => by
      rw [pd_θF, nabla_cof_alg]
      refine congrArg Neg.neg (Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun D _ => ?_)
      rw [GenCplN.ΓF_eq_G]
      rfl) (K x) b
  unfold GenCplDiv.remDiv GenCplDiv.frameTensor
  simp only [θF_eq] at h ⊢
  exact h

/-- **The divergence of a frame tensor field is the frame trace of its covariant derivative**:
`∇^a(θ^A{}_aθ^B{}_bK_{AB}) = Σ_Bθ^B{}_bΣ_Aε_A(e_A(K_{AB}) - Γ_{AA}{}^DK_{DB} - Γ_{AB}{}^DK_{AD})`. -/
theorem divS_frameTensor {K : ST 3 → Fin 4 → Fin 4 → ℝ}
    (hK : ∀ A B, ContDiff ℝ ∞ (fun y => K y A B)) (x : ST 3) (b : Fin 4) :
    ContractedBianchiJet.SubsidiarySource.divS (GenHarmonic.jet3 z x)
        (Matrix.of (GenCplDiv.frameTensor z K x))
        (fun e => Matrix.of fun a' b' => pd (fun y => GenCplDiv.frameTensor z K y a' b') e x) b =
      ∑ B, GenCplSD.θF z x B b * ∑ A, lorentzSign A * (fd z (fun y => K y A B) A x -
        ∑ D, ΓF z x A A D * K x D B - ∑ D, ΓF z x A B D * K x A D) := by
  rw [GenCplDiv.divS_main z hK x b, remDiv_cov]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_neg_distrib,
    mul_add, Finset.sum_add_distrib]
  rw [← sub_eq_zero]
  ring_nf

end CovDiv

/-! ### The bosonic part and the Dirac part of the complete stress -/

section Split

variable (SM : SMData (MatLie m) V S S')

/-- The zero Dirac stress form. -/
def zeroTD : DiracStressForm S S' V where
  P := fun _ _ _ => 0
  P' := fun _ _ _ => 0
  P'' := fun _ _ _ => 0

/-- The bosonic part of back-reacting Dirac data: Higgs current, potential force, no Dirac
stress. -/
def bos0 (hV : GenDiracCur.VariationalDirac SM) : SMData (MatLie m) V S S' :=
  { GenDiracCur.bosData SM hV with TD := zeroTD }

variable {SM}

/-- The bosonic part is variational Yang–Mills–Higgs data with vanishing Dirac stress. -/
def bos0Var (hC : GenDStress.CoupledDirac SM) :
    GenStress.VariationalStress (bos0 SM hC.toVariationalDirac) where
  μ := hC.μ
  moment := hC.moment
  alt := hC.alt
  equiv := hC.equiv
  J_eq := fun _ _ _ _ _ _ _ => rfl
  SH_eq := fun _ _ _ _ _ => rfl
  ipG_symm := hC.ipG_symm
  ipG_inv := hC.ipG_inv
  ipV_symm := hC.ipV_symm
  P_zero := fun _ _ _ => rfl
  P'_zero := fun _ _ _ => rfl
  P''_zero := fun _ _ _ => rfl

variable (z : Tuple m V S S')

/-- The coordinate Dirac stress field of the tuple. -/
def TDf (y : ST 3) (μ ν : Fin 4) : ℝ :=
  SM.TD.coord (z.jet y).FJ.g lorentzSign (z.jet y).AF.fr (z.jet y).H (z.jet y).ψ
    ((z.jet y).Xs SM.D (z.jet y).ψ (z.jet y).cψ) (z.jet y).ψb
    ((z.jet y).Xs SM.Db (z.jet y).ψb (z.jet y).cψb) μ ν

theorem Tf_split (hC : GenDStress.CoupledDirac SM) (y : ST 3) (μ ν : Fin 4) :
    GenStress.Tf SM z y μ ν = GenStress.Tf (bos0 SM hC.toVariationalDirac) z y μ ν +
      TDf (SM := SM) z y μ ν := by
  unfold GenStress.Tf ActualJet.Tact TDf
  have h0 : (bos0 SM hC.toVariationalDirac).TD.coord (z.jet y).FJ.g lorentzSign (z.jet y).AF.fr
      (z.jet y).H (z.jet y).ψ ((z.jet y).Xs (bos0 SM hC.toVariationalDirac).D (z.jet y).ψ
        (z.jet y).cψ) (z.jet y).ψb ((z.jet y).Xs (bos0 SM hC.toVariationalDirac).Db (z.jet y).ψb
        (z.jet y).cψb) μ ν = 0 := by
    show zeroTD.coord _ _ _ _ _ _ _ _ μ ν = 0
    unfold DiracStressForm.coord DiracStressForm.frame zeroTD
    simp
  rw [h0, add_zero]
  rfl

/-- **On the Dirac equations the coordinate Dirac stress is the frame tensor of the kinetic
stress** (the Dirac Lagrangian vanishes). -/
theorem TDf_eq (hC : GenDStress.CoupledDirac SM) {y : ST 3} (hy : dirF SM z y = 0)
    (μ ν : Fin 4) :
    TDf (SM := SM) z y μ ν = GenCplDiv.frameTensor z (fun y A B => GenDStress.kinT SM.D hC.P
      (z.ψ y) (Xf z SM.D z.ψ y) (z.ψb y) (Xf z SM.Db z.ψb y) A B) y μ ν := by
  have hr1 : ((z.jet y).res SM).rD = 0 := congrArg Prod.fst hy
  have hr2 : ((z.jet y).res SM).rDb = 0 := congrArg Prod.snd hy
  have hX : ∑ C, lorentzSign C • SM.D.Fr.c C (Xf z SM.D z.ψ y C) =
      mass SM.D.m0 SM.D.L (z.H y) (z.ψ y) := by
    have h := hr1
    change resD SM.D.Fr ((z.jet y).LJ SM.D).ω SM.D.m0 SM.D.L (z.H y) (z.ψ y)
      (dψf (z.FJ y) (fun γ => pd z.ψ γ y)) = 0 at h
    unfold resD dirac at h
    rw [sub_eq_zero, ((z.jet y).hε SM.D)] at h
    simp only [Module.End.smul_def] at h
    rw [show (z.jet y).FJ.ε = lorentzSign from (z.jet y).sign] at h
    exact h
  have hXb : ∑ C, lorentzSign C • SM.Db.Fr.c C (Xf z SM.Db z.ψb y C) =
      mass SM.Db.m0 SM.Db.L (z.H y) (z.ψb y) := by
    have h := hr2
    change resD SM.Db.Fr ((z.jet y).LJ SM.Db).ω SM.Db.m0 SM.Db.L (z.H y) (z.ψb y)
      (dψf (z.FJ y) (fun γ => pd z.ψb γ y)) = 0 at h
    unfold resD dirac at h
    rw [sub_eq_zero, ((z.jet y).hε SM.Db)] at h
    simp only [Module.End.smul_def] at h
    rw [show (z.jet y).FJ.ε = lorentzSign from (z.jet y).sign] at h
    exact h
  have hL : GenDStress.lagD SM.D hC.P (z.jet y).H (z.jet y).ψ
      ((z.jet y).Xs SM.D (z.jet y).ψ (z.jet y).cψ) (z.jet y).ψb
      ((z.jet y).Xs SM.Db (z.jet y).ψb (z.jet y).cψb) = 0 :=
    GenDStress.lagD_eq_zero hC.toDiracPairing _ _ _ _ _ hX hXb
  unfold TDf DiracStressForm.coord GenCplDiv.frameTensor
  rw [hC.TD_eq]
  refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
  rw [GenDStress.frame_symTD, hL, mul_zero, add_zero, GenCplN.jetAF]
  rfl

end Split

/-! ### The divergence of the Dirac stress along a tuple on the Dirac equations -/

section DiracDiv

variable (z : Tuple m V S S')

/-- The frame Higgs derivative jets. -/
def dhf (x : ST 3) (b : Fin 4) : V := ∑ δ, (z.FJ x).e b δ • pd z.H δ x

/-- **The covariant derivative of the Dirac residual vanishes where the residual vanishes on a
neighbourhood.** -/
theorem covResD_zero (D : DiracData (MatLie m) V S₀) {ψf : ST 3 → S₀} (hψ : ContDiff ℝ ∞ ψf)
    {x : ST 3} (hd : DifferentiableAt ℝ (fun y => (z.jet y).rD D (ψf y) (fun γ => pd ψf γ y)) x)
    (hev : (fun y => (z.jet y).rD D (ψf y) (fun γ => pd ψf γ y)) =ᶠ[𝓝 x] 0) (a : Fin 4) :
    covResD D.Fr ((z.jet x).LJ D).ω ((z.jet x).LJ D).dω D.m0 D.L (z.H x) (dhf z x) (ψf x)
      (dψf (z.FJ x) (fun γ => pd ψf γ x))
      (ddψf (z.FJ x) (fun γ => pd ψf γ x) (fun δ γ => pd (pd ψf γ) δ x)) a = 0 := by
  have h0 : resD D.Fr ((z.jet x).LJ D).ω D.m0 D.L (z.H x) (ψf x)
      (dψf (z.FJ x) (fun γ => pd ψf γ x)) = 0 := hev.self_of_nhds
  have hdr : ∀ δ, (z.jet x).drD D (ψf x) (fun γ => pd ψf γ x) (fun δ γ => pd (pd ψf γ) δ x) δ =
      0 := by
    intro δ
    rw [← pd_eq_of_line hd (z.line_rD x δ D hψ)]
    exact GenConstraint.pd_eq_zero_of_eventually hev δ
  unfold covResD
  rw [h0, smul_zero, add_zero]
  have := ActualJetSpinor.dresD_eq (z.FJ x) D.Fr ((z.jet x).hε D) (fun μ => D.ρ (z.A x μ))
    (fun γ μ => D.ρ (pd z.A γ x μ)) (fun μ b => D.comm (z.A x μ) b) D.m0 D.L (z.H x)
    (fun δ => pd z.H δ x) (ψf x) (fun γ => pd ψf γ x) (fun δ γ => pd (pd ψf γ) δ x) a
  refine this.trans ?_
  refine Finset.sum_eq_zero fun δ _ => ?_
  have h := hdr δ
  unfold ActualJet.drD at h
  rw [smul_eq_zero]
  right
  exact h

end DiracDiv

section DiracDiv2

variable {SM : SMData (MatLie m) V S S'} (z : Tuple m V S S')

/-- **The divergence of the coordinate Dirac stress on the Dirac equations**: the Lorentz force of
the Dirac current minus the Yukawa force, in frame components. -/
theorem divS_TDf (hC : GenDStress.CoupledDirac SM) {x : ST 3}
    (hDn : (fun y => dirF SM z y) =ᶠ[𝓝 x] 0) (b : Fin 4) :
    ContractedBianchiJet.SubsidiarySource.divS (GenHarmonic.jet3 z x)
        (Matrix.of (TDf (SM := SM) z x))
        (fun e => Matrix.of fun a' b' => pd (fun y => TDf (SM := SM) z y a' b') e x) b =
      ∑ B, GenCplSD.θF z x B b * (∑ c, SM.D.Fr.ε c * hC.P (z.ψb x)
          ((((z.jet x).LJ SM.D).F B c * SM.D.Fr.c c) • z.ψ x) -
        hC.P (z.ψb x) (SM.D.L (DH (z.jet x).ρH (z.H x) (dhf z x) B) • z.ψ x)) := by
  set Kd : ST 3 → Fin 4 → Fin 4 → ℝ := fun y A B => GenDStress.kinT SM.D hC.P (z.ψ y)
    (Xf z SM.D z.ψ y) (z.ψb y) (Xf z SM.Db z.ψb y) A B with hKd
  have hev : ∀ a' b', (fun y => TDf (SM := SM) z y a' b') =ᶠ[𝓝 x]
      (fun y => GenCplDiv.frameTensor z Kd y a' b') := fun a' b' =>
    hDn.mono fun y hy => TDf_eq z hC hy a' b'
  have hval : Matrix.of (TDf (SM := SM) z x) = Matrix.of (GenCplDiv.frameTensor z Kd x) := by
    ext a' b'; exact (hev a' b').self_of_nhds
  have hpd : (fun e => Matrix.of fun a' b' => pd (fun y => TDf (SM := SM) z y a' b') e x) =
      fun e => Matrix.of fun a' b' => pd (fun y => GenCplDiv.frameTensor z Kd y a' b') e x := by
    funext e; ext a' b'
    exact (SlabLocal.pd_eventuallyEq (hev a' b') e).self_of_nhds
  have hKs : ∀ A B, ContDiff ℝ ∞ (fun y => Kd y A B) := fun A B =>
    GenCplSub.contDiff_kinT SM.D hC.P z.ψ_smooth z.ψb_smooth (contDiff_Xf z SM.D z.ψ_smooth)
      (contDiff_Xf z SM.Db z.ψb_smooth) A B
  rw [hval, hpd, divS_frameTensor z hKs x b]
  refine Finset.sum_congr rfl fun B _ => ?_
  congr 1
  -- the jets at `x`
  set J := (z.jet x).LJ SM.D with hJ
  set Jb := (z.jet x).LJ SM.Db with hJb
  set cψ : Fin 4 → S := fun γ => pd z.ψ γ x
  set ccψ : Fin 4 → Fin 4 → S := fun δ γ => pd (pd z.ψ γ) δ x
  set cψb : Fin 4 → S' := fun γ => pd z.ψb γ x
  set ccψb : Fin 4 → Fin 4 → S' := fun δ γ => pd (pd z.ψb γ) δ x
  have hε := GenCplBox.eps_eq SM.D
  have hcov : ∑ A, lorentzSign A * (fd z (fun y => Kd y A B) A x -
      ∑ D, ΓF z x A A D * Kd x D B - ∑ D, ΓF z x A B D * Kd x A D) =
      ∑ A, SM.D.Fr.ε A * covKJ hC.P J Jb (z.ψ x) (dψf (z.FJ x) cψ) (ddψf (z.FJ x) cψ ccψ)
        (z.ψb x) (dψf (z.FJ x) cψb) (ddψf (z.FJ x) cψb ccψb) A A B := by
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [hε, hKd, fd_kin z hC x A A B, GenCplN.ΓF_eq z SM.D x]
    rfl
  rw [hcov]
  -- the conservation law on the jets
  have hD : (fun y => (z.jet y).rD SM.D (z.ψ y) (fun γ => pd z.ψ γ y)) =ᶠ[𝓝 x] 0 :=
    hDn.mono fun y hy => congrArg Prod.fst hy
  have hDb : (fun y => (z.jet y).rD SM.Db (z.ψb y) (fun γ => pd z.ψb γ y)) =ᶠ[𝓝 x] 0 :=
    hDn.mono fun y hy => congrArg Prod.snd hy
  have hdD : DifferentiableAt ℝ (fun y => (z.jet y).rD SM.D (z.ψ y) (fun γ => pd z.ψ γ y)) x :=
    (contDiff_fst.comp (contDiff_dirF SM z)).differentiable (by simp) x
  have hdDb : DifferentiableAt ℝ (fun y => (z.jet y).rD SM.Db (z.ψb y) (fun γ => pd z.ψb γ y)) x :=
    (contDiff_snd.comp (contDiff_dirF SM z)).differentiable (by simp) x
  have hsD : ∀ a' b', ddψf (z.FJ x) cψ ccψ a' b' - ddψf (z.FJ x) cψ ccψ b' a' =
      ∑ c, lcΛ SM.D.Fr.ε J.G a' b' c • dψf (z.FJ x) cψ c :=
    ActualJetSpinor.hψ (z.FJ x) SM.D.Fr ((z.jet x).hε SM.D) (fun μ => SM.D.ρ (z.A x μ))
      (fun γ μ => SM.D.ρ (pd z.A γ x μ)) (fun μ b => SM.D.comm (z.A x μ) b) cψ ccψ
      (fun δ γ => Tuple.vec_symm' x z.ψ_smooth δ γ)
  have hsDb : ∀ a' b', ddψf (z.FJ x) cψb ccψb a' b' - ddψf (z.FJ x) cψb ccψb b' a' =
      ∑ c, lcΛ SM.Db.Fr.ε Jb.G a' b' c • dψf (z.FJ x) cψb c :=
    ActualJetSpinor.hψ (z.FJ x) SM.Db.Fr ((z.jet x).hε SM.Db) (fun μ => SM.Db.ρ (z.A x μ))
      (fun γ μ => SM.Db.ρ (pd z.A γ x μ)) (fun μ b => SM.Db.comm (z.A x μ) b) cψb ccψb
      (fun δ γ => Tuple.vec_symm' x z.ψb_smooth δ γ)
  exact div_kin_onshell hC.P SM.D.m0 SM.D.L SM.Db.m0 SM.Db.L (z.jet x).ρH (z.H x) (dhf z x)
    rfl rfl GenDiracCur.eps_Db_eq (fun a φ y => tr_ω hC.toDiracPairing (z.jet x) a φ y)
    (fun A φ y => hC.c_tr A φ y) (fun a b φ y => tr_F hC.toDiracPairing (z.jet x) a b φ y)
    (fun w φ y => tr_M hC.toDiracPairing w φ y) (fun w φ y => hC.L_tr w φ y)
    (F_comm (z.jet x) SM.D) SM.D.mass_cl ((z.jet x).hMg SM.D) SM.Db.mass_cl
    ((z.jet x).hMg SM.Db) (z.ψ x) (dψf (z.FJ x) cψ) (ddψf (z.FJ x) cψ ccψ) (z.ψb x)
    (dψf (z.FJ x) cψb) (ddψf (z.FJ x) cψb ccψb) hsD hsDb hD.self_of_nhds
    (covResD_zero z SM.D z.ψ_smooth hdD hD) hDb.self_of_nhds
    (covResD_zero z SM.Db z.ψb_smooth hdDb hDb) B

end DiracDiv2

/-! ### Assembly: the complete stress is conserved on the matter equations -/

section Assembly

variable {SM : SMData (MatLie m) V S S'} (z : Tuple m V S S')

theorem pd_add_fun {f g : ST 3 → ℝ} {x : ST 3} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (e : Fin 4) : pd (fun y => f y + g y) e x = pd f e x + pd g e x := by
  unfold SobolevOpen.pd
  rw [fderiv_fun_add hf hg]
  rfl

/-- **The divergence splits into the bosonic and the Dirac parts.** -/
theorem divT_split (hC : GenDStress.CoupledDirac SM) {x : ST 3}
    (hDn : (fun y => dirF SM z y) =ᶠ[𝓝 x] 0) (ν : Fin 4) :
    GenStress.divT SM z x ν = GenStress.divT (bos0 SM hC.toVariationalDirac) z x ν +
      ContractedBianchiJet.SubsidiarySource.divS (GenHarmonic.jet3 z x)
        (Matrix.of (TDf (SM := SM) z x))
        (fun e => Matrix.of fun a' b' => pd (fun y => TDf (SM := SM) z y a' b') e x) ν := by
  have hV := bos0Var hC
  -- differentiability of the two parts
  have hdb : ∀ a ν', DifferentiableAt ℝ (fun y => GenStress.Tf (bos0 SM hC.toVariationalDirac) z y a ν') x := by
    intro a ν'
    have e : (fun y => GenStress.Tf (bos0 SM hC.toVariationalDirac) z y a ν') = fun y => GenStress.ymT (bos0 SM hC.toVariationalDirac).ipG (z.g y) (z.gi y)
        (GenNoether.Fld z y) a ν' + GenStress.hT (bos0 SM hC.toVariationalDirac).ipV (bos0 SM hC.toVariationalDirac).lamH (bos0 SM hC.toVariationalDirac).vH (z.g y) (z.gi y) (z.H y)
        (GenNoether.DHf z y) a ν' := funext fun y => GenStress.Tf_eq z hV y a ν'
    rw [e]
    exact ((GenStress.contDiffAt_ymT z (bos0 SM hC.toVariationalDirac).ipG a ν' x).add
      (GenStress.contDiffAt_hT z (bos0 SM hC.toVariationalDirac).ipV (bos0 SM hC.toVariationalDirac).lamH (bos0 SM hC.toVariationalDirac).vH a ν' x)).differentiableAt (by simp)
  have hdd : ∀ a ν', DifferentiableAt ℝ (fun y => TDf (SM := SM) z y a ν') x := by
    intro a ν'
    have hKs : ∀ A B, ContDiff ℝ ∞ (fun y => GenDStress.kinT SM.D hC.P (z.ψ y)
        (Xf z SM.D z.ψ y) (z.ψb y) (Xf z SM.Db z.ψb y) A B) := fun A B =>
      GenCplSub.contDiff_kinT SM.D hC.P z.ψ_smooth z.ψb_smooth (contDiff_Xf z SM.D z.ψ_smooth)
        (contDiff_Xf z SM.Db z.ψb_smooth) A B
    have hft : ContDiff ℝ ∞ (fun y => GenCplDiv.frameTensor z (fun y A B =>
        GenDStress.kinT SM.D hC.P (z.ψ y) (Xf z SM.D z.ψ y) (z.ψb y) (Xf z SM.Db z.ψb y) A B)
        y a ν') := by
      unfold GenCplDiv.frameTensor
      exact ContDiff.sum fun A _ => ContDiff.sum fun B _ =>
        ((GenCplSub.contDiff_θF (z := z) A a).mul (GenCplSub.contDiff_θF (z := z) B ν')).mul
          (hKs A B)
    have hev : (fun y => GenCplDiv.frameTensor z (fun y A B => GenDStress.kinT SM.D hC.P (z.ψ y)
        (Xf z SM.D z.ψ y) (z.ψb y) (Xf z SM.Db z.ψb y) A B) y a ν') =ᶠ[𝓝 x]
        fun y => TDf (SM := SM) z y a ν' := hDn.mono fun y hy => (TDf_eq z hC hy a ν').symm
    exact (hft.differentiable (by simp) x).congr_of_eventuallyEq hev.symm
  rw [← GenHarmonic.divS_eq_divT SM z x ν, ← GenHarmonic.divS_eq_divT (bos0 SM hC.toVariationalDirac) z x ν,
    ← ContractedBianchiJet.SubsidiarySource.divS_add]
  congr 1
  · ext a b
    simp only [Matrix.of_apply, Matrix.add_apply, Tf_split z hC]
  · funext e
    ext a b
    simp only [Matrix.of_apply, Matrix.add_apply]
    rw [show (fun y => GenStress.Tf SM z y a b) = fun y => GenStress.Tf (bos0 SM hC.toVariationalDirac) z y a b +
      TDf (SM := SM) z y a b from funext fun y => Tf_split z hC y a b]
    exact pd_add_fun (hdb a b) (hdd a b) e

end Assembly

section Final

variable {SM : SMData (MatLie m) V S S'} (z : Tuple m V S S')

theorem rA_bos0 (hC : GenDStress.CoupledDirac SM) (x : ST 3) (α : Fin 4) :
    (bosF (bos0 SM hC.toVariationalDirac) z x).2.1 α = (bosF SM z x).2.1 α +
      GenDiracCur.diracCur hC.μS SM.D.Fr (z.jet x).FJ.g (z.jet x).FJ.gi (z.jet x).ψ
        (z.jet x).ψb α := by
  show ymRes _ _ _ _ _ _ α = ymRes _ _ _ _ _ _ α + _
  unfold ymRes
  rw [hC.J_eq]
  show _ - (2 : ℝ) • hC.μ _ _ = _ - ((2 : ℝ) • hC.μ _ _ + _) + _
  abel

theorem rH_bos0 (hC : GenDStress.CoupledDirac SM) (x : ST 3) :
    (bosF (bos0 SM hC.toVariationalDirac) z x).2.2 = (bosF SM z x).2.2 +
      hC.yuk (z.jet x).ψb (z.jet x).ψ := by
  show higgsRes _ _ _ _ _ _ _ _ = higgsRes _ _ _ _ _ _ _ _ + _
  unfold higgsRes
  rw [hC.SH_eq]
  show _ - (2 * SM.lamH * (SM.ipV _ _ - SM.vH ^ 2)) • _ =
    _ - ((2 * SM.lamH * (SM.ipV _ _ - SM.vH ^ 2)) • _ + _) + _
  abel

/-- `Σ_Bθ^B{}_νe_B{}^μ = δ_ν^μ` along the tuple. -/
theorem θF_e (x : ST 3) (ν μ : Fin 4) :
    ∑ B, GenCplSD.θF z x B ν * (z.FJ x).e B μ = if ν = μ then 1 else 0 := by
  simp only [θF_eq]
  exact ActualJetRecon.cof_dual (z.FJ x) ν μ

/-- **The Lorentz force of the Dirac current** (bosonic side). -/
theorem lorentz_bos (hC : GenDStress.CoupledDirac SM) (x : ST 3) (ν : Fin 4) :
    ∑ α, ∑ β, z.gi x α β * SM.ipG (GenDiracCur.diracCur hC.μS SM.D.Fr (z.g x) (z.gi x) (z.ψ x)
        (z.ψb x) α) (Fm (z.jet x).A (z.jet x).dA ν β) =
      -∑ A, SM.D.Fr.ε A * ∑ β, (z.FJ x).e A β * hC.P (z.ψb x)
        (SM.D.ρ (Fm (z.jet x).A (z.jet x).dA ν β) (SM.D.Fr.c A (z.ψ x))) := by
  have hε := GenCplBox.eps_eq SM.D
  have hdual : ∀ A β, SM.ipG (hC.μS (z.ψb x) (SM.D.Fr.c A (z.ψ x)))
      (Fm (z.jet x).A (z.jet x).dA ν β) = hC.P (z.ψb x)
        (SM.D.ρ (Fm (z.jet x).A (z.jet x).dA ν β) (SM.D.Fr.c A (z.ψ x))) := by
    intro A β
    rw [hC.ipG_symm, hC.μS_dual]
  unfold GenDiracCur.diracCur
  simp only [map_neg, map_sum, map_smul, LinearMap.neg_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, hdual]
  -- contract `g^{αβ}g_{αμ}`
  have e1 : ∀ β, ∑ α, z.gi x α β * -∑ μ, z.g x α μ * ∑ A, lorentzSign A * frU (z.gi x) A μ *
      hC.P (z.ψb x) (SM.D.ρ (Fm (z.jet x).A (z.jet x).dA ν β) (SM.D.Fr.c A (z.ψ x))) =
      -∑ A, lorentzSign A * frU (z.gi x) A β *
        hC.P (z.ψb x) (SM.D.ρ (Fm (z.jet x).A (z.jet x).dA ν β) (SM.D.Fr.c A (z.ψ x))) := by
    intro β
    have hg : ∀ μ, ∑ α, z.gi x α β * z.g x α μ = if β = μ then 1 else 0 := by
      intro μ
      rw [← GenStress.gi_mul_g z x β μ]
      exact Finset.sum_congr rfl fun α _ => by rw [z.gi_symm x α β]
    have e : ∑ α, z.gi x α β * -∑ μ, z.g x α μ * ∑ A, lorentzSign A * frU (z.gi x) A μ *
        hC.P (z.ψb x) (SM.D.ρ (Fm (z.jet x).A (z.jet x).dA ν β) (SM.D.Fr.c A (z.ψ x))) =
        -∑ μ, (∑ α, z.gi x α β * z.g x α μ) * ∑ A, lorentzSign A * frU (z.gi x) A μ *
        hC.P (z.ψb x) (SM.D.ρ (Fm (z.jet x).A (z.jet x).dA ν β) (SM.D.Fr.c A (z.ψ x))) := by
      simp only [mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul]
      rw [sum3_rot]
      refine congrArg Neg.neg (Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun A _ =>
        Finset.sum_congr rfl fun α _ => by ring)
    rw [e]
    simp only [hg, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  simp only [e1, Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine congrArg Neg.neg (Finset.sum_congr rfl fun A _ => ?_)
  rw [hε, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  show _ = lorentzSign A * (frU (z.gi x) A β * _)
  ring

end Final

section Final2

variable {SM : SMData (MatLie m) V S S'} (z : Tuple m V S S')

/-- `Σ_Bθ^B{}_νΣ_μe_B{}^μQ_μ = Q_ν`. -/
theorem θF_contract {M : Type*} [AddCommGroup M] [Module ℝ M] (x : ST 3) (ν : Fin 4)
    (Q : Fin 4 → M) :
    ∑ B, GenCplSD.θF z x B ν • ∑ μ, (z.FJ x).e B μ • Q μ = Q ν := by
  have := ActualJetRecon.inv_vec (z.FJ x) Q ν
  rw [this]
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [θF_eq]

/-- **The Lorentz force of the Dirac current** (Dirac-stress side). -/
theorem lorentz_dirac (hC : GenDStress.CoupledDirac SM) (x : ST 3) (ν : Fin 4) :
    ∑ B, GenCplSD.θF z x B ν * ∑ c, SM.D.Fr.ε c * hC.P (z.ψb x)
        ((((z.jet x).LJ SM.D).F B c * SM.D.Fr.c c) • z.ψ x) =
      ∑ c, SM.D.Fr.ε c * ∑ β, (z.FJ x).e c β * hC.P (z.ψb x)
        (SM.D.ρ (Fm (z.jet x).A (z.jet x).dA ν β) (SM.D.Fr.c c (z.ψ x))) := by
  have hF : ∀ B c, ((z.jet x).LJ SM.D).F B c = ∑ μ, ∑ β, ((z.FJ x).e B μ * (z.FJ x).e c β) •
      SM.D.ρ (Fm (z.jet x).A (z.jet x).dA μ β) := by
    intro B c
    have h := (z.jet x).FJ.frameF_eq SM.D.Fr ((z.jet x).hε SM.D)
      (fun μ => SM.D.ρ ((z.jet x).A μ)) (fun γ μ => SM.D.ρ ((z.jet x).dA γ μ))
      (fun μ b => SM.D.comm ((z.jet x).A μ) b) B c
    refine h.trans (Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun β _ => ?_)
    congr 1
    unfold Fm fieldStrength
    rw [map_add, map_sub, SM.D.ρ_lie]
  have hP : ∀ B c, hC.P (z.ψb x) ((((z.jet x).LJ SM.D).F B c * SM.D.Fr.c c) • z.ψ x) =
      ∑ μ, (z.FJ x).e B μ • ∑ β, (z.FJ x).e c β • hC.P (z.ψb x)
        (SM.D.ρ (Fm (z.jet x).A (z.jet x).dA μ β) (SM.D.Fr.c c (z.ψ x))) := by
    intro B c
    rw [hF, Module.End.smul_def, Module.End.mul_apply]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, smul_eq_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun β _ => by ring
  simp only [hP]
  have e1 : ∀ B, GenCplSD.θF z x B ν * ∑ c, SM.D.Fr.ε c * ∑ μ, (z.FJ x).e B μ • ∑ β,
      (z.FJ x).e c β • hC.P (z.ψb x) (SM.D.ρ (Fm (z.jet x).A (z.jet x).dA μ β)
        (SM.D.Fr.c c (z.ψ x))) =
      GenCplSD.θF z x B ν • ∑ μ, (z.FJ x).e B μ • (fun μ => ∑ c, SM.D.Fr.ε c * ∑ β,
        (z.FJ x).e c β * hC.P (z.ψb x) (SM.D.ρ (Fm (z.jet x).A (z.jet x).dA μ β)
          (SM.D.Fr.c c (z.ψ x)))) μ := by
    intro B
    simp only [smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun β _ => by ring
  simp only [e1]
  exact θF_contract z x ν _

/-- **The Yukawa force** (Dirac-stress side). -/
theorem yukawa_dirac (hC : GenDStress.CoupledDirac SM) (x : ST 3) (ν : Fin 4) :
    ∑ B, GenCplSD.θF z x B ν * hC.P (z.ψb x) (SM.D.L (SpinorProlongation.DH (z.jet x).ρH (z.H x) (dhf z x) B) •
      z.ψ x) = hC.P (z.ψb x) (SM.D.L (ActualJetGauge.DH (z.jet x).A (z.jet x).H
        (z.jet x).dH ν) (z.ψ x)) := by
  have hD : ∀ B, SpinorProlongation.DH (z.jet x).ρH (z.H x) (dhf z x) B = ∑ μ, (z.FJ x).e B μ •
      ActualJetGauge.DH (z.jet x).A (z.jet x).H (z.jet x).dH μ := by
    intro B
    unfold SpinorProlongation.DH dhf
    rw [(z.jet x).ρH_apply]
    simp only [ActualJetGauge.DH, smul_add, Finset.sum_add_distrib]
    rfl
  have hP : ∀ B, hC.P (z.ψb x) (SM.D.L (SpinorProlongation.DH (z.jet x).ρH (z.H x) (dhf z x) B) • z.ψ x) =
      ∑ μ, (z.FJ x).e B μ • hC.P (z.ψb x) (SM.D.L (ActualJetGauge.DH (z.jet x).A (z.jet x).H
        (z.jet x).dH μ) (z.ψ x)) := by
    intro B
    rw [hD, Module.End.smul_def]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  simp only [hP, ← smul_eq_mul (a := GenCplSD.θF z x _ ν)]
  exact θF_contract z x ν (fun μ => hC.P (z.ψb x) (SM.D.L (ActualJetGauge.DH (z.jet x).A
    (z.jet x).H (z.jet x).dH μ) (z.ψ x)))

/-- **The Yukawa force** (bosonic side). -/
theorem yukawa_bos (hC : GenDStress.CoupledDirac SM) (w : V) (φ : S') (y : S) :
    2 * SM.ipV (hC.yuk φ y) w = hC.P φ (SM.D.L w y) := by
  rw [hC.ipV_symm, hC.yuk_dual]

end Final2

/-! ### The stress Noether identity on the matter equations -/

section Main

variable {SM : SMData (MatLie m) V S S'}

/-- **On-shell conservation of the complete stress with the Dirac stress**
(task 1 of the coupled lift, `lem:generated-physical-identification`, `prop:subsidiary`): for
back-reacting Dirac theory data (`GenDStress.CoupledDirac`: symmetric Hilbert Dirac stress, Dirac
current and Yukawa source of a Dirac pairing), wherever the Dirac equations hold on a
neighbourhood and the Yang–Mills and Higgs equations hold at the point,
`∇^μT^{SM}_{μν} = 0`.  The Yang–Mills/Higgs stress divergence produces the Lorentz force of the
Dirac current and the Yukawa force; the Dirac stress divergence (`GenDSJ.div_kin_onshell`:
covariant Leibniz rule, Ricci identity, half-Ricci contraction, Lichnerowicz scalar, Clifford
triple identity) produces their negatives. -/
theorem stressConservation_of_coupledDirac (hC : GenDStress.CoupledDirac SM) :
    GenCplMat.StressConservation SM := by
  intro z x hDn hA hH ν
  have hDn' : (fun y => dirF SM z y) =ᶠ[𝓝 x] 0 := hDn
  rw [divT_split z hC hDn' ν, GenStress.divT_variational z (bos0Var hC) x ν,
    divS_TDf z hC hDn' ν]
  have hr1 : ∀ α, (bosF (bos0 SM hC.toVariationalDirac) z x).2.1 α =
      GenDiracCur.diracCur hC.μS SM.D.Fr (z.g x) (z.gi x) (z.ψ x) (z.ψb x) α := by
    intro α
    rw [rA_bos0, hA]
    simp only [Pi.zero_apply, zero_add]
    rfl
  have hr2 : (bosF (bos0 SM hC.toVariationalDirac) z x).2.2 = hC.yuk (z.ψb x) (z.ψ x) := by
    rw [rH_bos0, hH, zero_add]
    rfl
  show (∑ α, ∑ β, (z.jet x).FJ.gi α β * SM.ipG ((bosF (bos0 SM hC.toVariationalDirac) z x).2.1 α)
      (Fm (z.jet x).A (z.jet x).dA ν β) +
      2 * SM.ipV (bosF (bos0 SM hC.toVariationalDirac) z x).2.2
        (ActualJetGauge.DH (z.jet x).A (z.jet x).H (z.jet x).dH ν)) + _ = 0
  simp only [hr1, hr2]
  rw [show (z.jet x).FJ.gi = z.gi x from rfl, lorentz_bos z hC x ν, yukawa_bos hC]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [lorentz_dirac z hC x ν, yukawa_dirac z hC x ν]
  ring

end Main

end RenewalGeometry.GenDSN
