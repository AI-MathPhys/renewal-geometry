/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.SpinorProlongationJet

/-!
# The divergence of the symmetric Dirac stress on jets

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`,
coupled spinors (task: the stress Noether identity with the Dirac stress).  Exact algebra on jets
at a point in an orthonormal moving frame, for a spinor `Ψ` and a co-spinor `Ψ̄` with jets
`(ψ, e_aψ, e_ae_bψ)`, a Dirac pairing `⟨·,·⟩ : S' × S → ℝ` for which the co-spinor Clifford
generators are the transposes of the spinor ones and the co-spinor connection is minus the
transpose of the spinor connection.

* `kinJ` — the kinetic (symmetric) Dirac stress
  `K_{AB} = -¼[⟨Ψ̄, c_AX_B⟩ + ⟨Ψ̄, c_BX_A⟩ - ⟨X̄_B, c_AΨ⟩ - ⟨X̄_A, c_BΨ⟩]` of the jets
  `X_A = ∇_AΨ`, `X̄_A = ∇_AΨ̄`; `dkinJ` — its frame derivative (product rule); `covKJ` — its
  frame-covariant derivative `∇_CK_{AB} = e_C(K_{AB}) - Γ_{CA}{}^DK_{DB} - Γ_{CB}{}^DK_{AD}`;
* **`covKJ_eq`** — the covariant Leibniz rule: `∇_CK_{AB}` is `kinJ` with every derivative
  replaced by a covariant one (the pairing is invariant, Clifford multiplication is parallel).
-/

open Finset

noncomputable section

namespace RenewalGeometry.GenDSJ

open TwistedHalfRicci SpinorProlongation

set_option linter.unusedSectionVars false

variable {S : Type*} [AddCommGroup S] [Module ℝ S]
variable {S' : Type*} [AddCommGroup S'] [Module ℝ S']

section Kinetic

variable (Fr : CliffordFrame (Fin 4) (Module.End ℝ S)) (P : S' →ₗ[ℝ] S →ₗ[ℝ] ℝ)

/-- The kinetic Dirac stress of jets. -/
def kinJ (ψ : S) (X : Fin 4 → S) (ψb : S') (Xb : Fin 4 → S') (A B : Fin 4) : ℝ :=
  -(1 / 4 : ℝ) * (P ψb (Fr.c A • X B) + P ψb (Fr.c B • X A) - P (Xb B) (Fr.c A • ψ) -
    P (Xb A) (Fr.c B • ψ))

/-- Its frame derivative in direction `C` (product rule on jets). -/
def dkinJ (ψ : S) (dψ : Fin 4 → S) (X : Fin 4 → S) (dX : Fin 4 → Fin 4 → S) (ψb : S')
    (dψb : Fin 4 → S') (Xb : Fin 4 → S') (dXb : Fin 4 → Fin 4 → S') (C A B : Fin 4) : ℝ :=
  -(1 / 4 : ℝ) * (P (dψb C) (Fr.c A • X B) + P ψb (Fr.c A • dX C B) +
    P (dψb C) (Fr.c B • X A) + P ψb (Fr.c B • dX C A) -
    P (dXb C B) (Fr.c A • ψ) - P (Xb B) (Fr.c A • dψ C) -
    P (dXb C A) (Fr.c B • ψ) - P (Xb A) (Fr.c B • dψ C))

end Kinetic

/-! ### The covariant Leibniz rule -/

section Leibniz

variable {Fr : CliffordFrame (Fin 4) (Module.End ℝ S)}
  {Frb : CliffordFrame (Fin 4) (Module.End ℝ S')} (P : S' →ₗ[ℝ] S →ₗ[ℝ] ℝ)
  (J : LCJet Fr) (Jb : LCJet Frb)

/-- **Leibniz rule for an invariant pairing and a parallel Clifford generator.** -/
theorem leib (htω : ∀ a (φ : S') (x : S), P (Jb.ω a • φ) x = -P φ (J.ω a • x))
    (C A : Fin 4) (φ dφ : S') (x dx : S) :
    P dφ (Fr.c A • x) + P φ (Fr.c A • dx) =
      P (dφ + Jb.ω C • φ) (Fr.c A • x) + P φ (Fr.c A • (dx + J.ω C • x)) +
        ∑ D, lcΓ Fr.ε J.G C A D * P φ (Fr.c D • x) := by
  have hcl := omega_smul_c Fr (lcΓ Fr.ε J.G) J.ω J.clifford_parallel C A x
  simp only [map_add, LinearMap.add_apply, htω, smul_add]
  rw [hcl, map_add, map_sum]
  simp only [map_smul, smul_eq_mul]
  ring

/-- The covariant derivatives of the jets. -/
def Xj (ψ : S) (dψ : Fin 4 → S) : Fin 4 → S := cov J.ω ψ dψ

variable {J Jb}

/-- **The covariant Leibniz rule for the kinetic Dirac stress**: with `X = ∇Ψ`, `X̄ = ∇Ψ̄`,
`e_C(K_{AB}) - Γ_{CA}{}^DK_{DB} - Γ_{CB}{}^DK_{AD}` is the kinetic stress with all derivatives
covariant (`∇_CX_B = ∇²_{CB}Ψ`). -/
theorem covKJ_eq (hG : Jb.G = J.G) (hε : Frb.ε = Fr.ε)
    (htω : ∀ a (φ : S') (x : S), P (Jb.ω a • φ) x = -P φ (J.ω a • x))
    (ψ : S) (dψ : Fin 4 → S) (ddψ : Fin 4 → Fin 4 → S) (ψb : S') (dψb : Fin 4 → S')
    (ddψb : Fin 4 → Fin 4 → S') (C A B : Fin 4) :
    dkinJ Fr P ψ dψ (cov J.ω ψ dψ) (dcov J.ω J.dω ψ dψ ddψ) ψb dψb (cov Jb.ω ψb dψb)
        (dcov Jb.ω Jb.dω ψb dψb ddψb) C A B -
      ∑ D, lcΓ Fr.ε J.G C A D * kinJ Fr P ψ (cov J.ω ψ dψ) ψb (cov Jb.ω ψb dψb) D B -
      ∑ D, lcΓ Fr.ε J.G C B D * kinJ Fr P ψ (cov J.ω ψ dψ) ψb (cov Jb.ω ψb dψb) A D =
    -(1 / 4 : ℝ) * (P (cov Jb.ω ψb dψb C) (Fr.c A • cov J.ω ψ dψ B) +
      P ψb (Fr.c A • cov2 (lcΓ Fr.ε J.G) J.ω J.dω ψ dψ ddψ C B) +
      P (cov Jb.ω ψb dψb C) (Fr.c B • cov J.ω ψ dψ A) +
      P ψb (Fr.c B • cov2 (lcΓ Fr.ε J.G) J.ω J.dω ψ dψ ddψ C A) -
      P (cov2 (lcΓ Frb.ε Jb.G) Jb.ω Jb.dω ψb dψb ddψb C B) (Fr.c A • ψ) -
      P (cov Jb.ω ψb dψb B) (Fr.c A • cov J.ω ψ dψ C) -
      P (cov2 (lcΓ Frb.ε Jb.G) Jb.ω Jb.dω ψb dψb ddψb C A) (Fr.c B • ψ) -
      P (cov Jb.ω ψb dψb A) (Fr.c B • cov J.ω ψ dψ C)) := by
  set X := cov J.ω ψ dψ with hX
  set Xb := cov Jb.ω ψb dψb with hXb
  have hΓb : lcΓ Frb.ε Jb.G = lcΓ Fr.ε J.G := by rw [hG, hε]
  -- the derivative jets in covariant form
  have hdX : ∀ C B, dcov J.ω J.dω ψ dψ ddψ C B + J.ω C • X B =
      cov2 (lcΓ Fr.ε J.G) J.ω J.dω ψ dψ ddψ C B + ∑ D, lcΓ Fr.ε J.G C B D • X D := by
    intro C B; unfold cov2; rw [← hX]; abel
  have hdXb : ∀ C B, dcov Jb.ω Jb.dω ψb dψb ddψb C B + Jb.ω C • Xb B =
      cov2 (lcΓ Frb.ε Jb.G) Jb.ω Jb.dω ψb dψb ddψb C B + ∑ D, lcΓ Fr.ε J.G C B D • Xb D := by
    intro C B; unfold cov2; rw [← hXb, hΓb]; abel
  have hdψb : ∀ C, dψb C + Jb.ω C • ψb = Xb C := fun C => rfl
  have hdψ : ∀ C, dψ C + J.ω C • ψ = X C := fun C => rfl
  -- the four pairs
  have p1 := leib P J Jb htω C A ψb (dψb C) (X B) (dcov J.ω J.dω ψ dψ ddψ C B)
  have p2 := leib P J Jb htω C B ψb (dψb C) (X A) (dcov J.ω J.dω ψ dψ ddψ C A)
  have p3 := leib P J Jb htω C A (Xb B) (dcov Jb.ω Jb.dω ψb dψb ddψb C B) ψ (dψ C)
  have p4 := leib P J Jb htω C B (Xb A) (dcov Jb.ω Jb.dω ψb dψb ddψb C A) ψ (dψ C)
  rw [hdψb, hdX] at p1 p2
  rw [hdXb, hdψ] at p3 p4
  unfold dkinJ kinJ
  simp only [Module.End.smul_def, map_add, map_sum, map_smul, smul_eq_mul, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply] at p1 p2 p3 p4 ⊢
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_add, mul_sub, Finset.mul_sum,
    Finset.sum_mul] at p1 p2 p3 p4 ⊢
  ring_nf at p1 p2 p3 p4 ⊢
  simp only [← Finset.sum_mul] at p1 p2 p3 p4 ⊢
  linear_combination (-(1 / 4 : ℝ)) * (p1 + p2 - p3 - p4)

end Leibniz

/-! ### The frame divergence -/

section Divergence

variable {Fr : CliffordFrame (Fin 4) (Module.End ℝ S)}
  {Frb : CliffordFrame (Fin 4) (Module.End ℝ S')} (P : S' →ₗ[ℝ] S →ₗ[ℝ] ℝ)
  {J : LCJet Fr} {Jb : LCJet Frb}

/-- The covariant derivative `∇_CK_{AB}` of the kinetic stress of the jets. -/
def covKJ (J : LCJet Fr) (Jb : LCJet Frb) (ψ : S) (dψ : Fin 4 → S) (ddψ : Fin 4 → Fin 4 → S)
    (ψb : S') (dψb : Fin 4 → S') (ddψb : Fin 4 → Fin 4 → S') (C A B : Fin 4) : ℝ :=
  dkinJ Fr P ψ dψ (cov J.ω ψ dψ) (dcov J.ω J.dω ψ dψ ddψ) ψb dψb (cov Jb.ω ψb dψb)
      (dcov Jb.ω Jb.dω ψb dψb ddψb) C A B -
    ∑ D, lcΓ Fr.ε J.G C A D * kinJ Fr P ψ (cov J.ω ψ dψ) ψb (cov Jb.ω ψb dψb) D B -
    ∑ D, lcΓ Fr.ε J.G C B D * kinJ Fr P ψ (cov J.ω ψ dψ) ψb (cov Jb.ω ψb dψb) A D

/-- The Laplacian `Σ_Aε_A∇²_{AA}Ψ` of the jets. -/
def lapJ (Fr : CliffordFrame (Fin 4) (Module.End ℝ S)) (J : LCJet Fr) (ψ : S) (dψ : Fin 4 → S)
    (ddψ : Fin 4 → Fin 4 → S) : S :=
  ∑ A, Fr.ε A • cov2 (lcΓ Fr.ε J.G) J.ω J.dω ψ dψ ddψ A A

/-- **The frame divergence of the kinetic Dirac stress**:
`Σ_Aε_A∇_AK_{AB} = -¼[⟨𝒟̄Ψ̄, X_B⟩ + ⟨Ψ̄, (𝒟X)_B⟩ + ⟨Ψ̄, c_BΔΨ⟩ - ⟨(𝒟̄X̄)_B, Ψ⟩ - ⟨X̄_B, 𝒟Ψ⟩ -
⟨ΔΨ̄, c_BΨ⟩]`. -/
theorem div_covKJ (hG : Jb.G = J.G) (hε : Frb.ε = Fr.ε)
    (htω : ∀ a (φ : S') (x : S), P (Jb.ω a • φ) x = -P φ (J.ω a • x))
    (htc : ∀ A (φ : S') (x : S), P (Frb.c A • φ) x = P φ (Fr.c A • x))
    (ψ : S) (dψ : Fin 4 → S) (ddψ : Fin 4 → Fin 4 → S) (ψb : S') (dψb : Fin 4 → S')
    (ddψb : Fin 4 → Fin 4 → S') (B : Fin 4) :
    ∑ A, Fr.ε A * covKJ P J Jb ψ dψ ddψ ψb dψb ddψb A A B =
      -(1 / 4 : ℝ) * (P (dirac Frb Jb.ω ψb dψb) (cov J.ω ψ dψ B) +
        P ψb (dTX Fr (lcΓ Fr.ε J.G) J.ω J.dω ψ dψ ddψ B) +
        P ψb (Fr.c B • lapJ Fr J ψ dψ ddψ) -
        P (dTX Frb (lcΓ Frb.ε Jb.G) Jb.ω Jb.dω ψb dψb ddψb B) ψ -
        P (cov Jb.ω ψb dψb B) (dirac Fr J.ω ψ dψ) -
        P (lapJ Frb Jb ψb dψb ddψb) (Fr.c B • ψ)) := by
  have hc : ∀ A, covKJ P J Jb ψ dψ ddψ ψb dψb ddψb A A B = _ := fun A =>
    covKJ_eq P hG hε htω ψ dψ ddψ ψb dψb ddψb A A B
  simp only [hc]
  unfold dirac dTX lapJ
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, htc, hε]
  simp only [Module.End.smul_def, map_sum, map_smul, smul_eq_mul]
  simp only [mul_add, mul_sub, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring_nf

end Divergence

/-! ### The Laplacian of the jets -/

section Laplacian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : Type*} [Ring A] [Algebra ℝ A]
variable {V : Type*} [AddCommGroup V] [Module A V] [Module ℝ V] [IsScalarTower ℝ A V]

/-- **Clifford splitting of `𝒟∇`**: `Σ_{C,b}ε_Cε_bc_Cc_bQ_{Cb} = -Σ_Cε_CQ_{CC} +
½Σ_{C,b}ε_Cε_bc_Cc_b(Q_{Cb} - Q_{bC})`. -/
theorem clifford_split' (Fr : CliffordFrame ι A) (Q : ι → ι → V) :
    ∑ C, ∑ b, (Fr.ε C * Fr.ε b) • ((Fr.c C * Fr.c b) • Q C b) =
      -∑ C, Fr.ε C • Q C C +
        (1 / 2 : ℝ) • ∑ C, ∑ b, (Fr.ε C * Fr.ε b) • ((Fr.c C * Fr.c b) • (Q C b - Q b C)) := by
  have hε : ∀ x, Fr.ε x * Fr.ε x = 1 := fun x => by rw [← sq]; exact Fr.sign_sq x
  have hrel : ∀ C b, Fr.c b * Fr.c C = -(Fr.c C * Fr.c b) +
      ((-2 : ℝ) * (if C = b then Fr.ε C else 0)) • (1 : A) := by
    intro C b
    rw [← Fr.anticomm C b]; abel
  -- relabel the second half
  have hswap : ∑ C, ∑ b, (Fr.ε C * Fr.ε b) • ((Fr.c C * Fr.c b) • Q b C) =
      ∑ C, ∑ b, (Fr.ε C * Fr.ε b) • ((Fr.c b * Fr.c C) • Q C b) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun b _ => ?_
    rw [mul_comm (Fr.ε b)]
  have hdiag : ∑ C, ∑ b, (Fr.ε C * Fr.ε b) •
      ((((-2 : ℝ) * (if C = b then Fr.ε C else 0)) • (1 : A)) • Q C b) =
      (-2 : ℝ) • ∑ C, Fr.ε C • Q C C := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [Finset.sum_eq_single C (fun b _ hb => by rw [if_neg (Ne.symm hb)]; simp) (by simp),
      if_pos rfl, smul_assoc, one_smul, smul_smul, smul_smul]
    congr 1
    have := hε C
    linear_combination (-2 * Fr.ε C) * this
  have key : ∀ C b, (Fr.ε C * Fr.ε b) • ((Fr.c b * Fr.c C) • Q C b) =
      -((Fr.ε C * Fr.ε b) • ((Fr.c C * Fr.c b) • Q C b)) + (Fr.ε C * Fr.ε b) •
        ((((-2 : ℝ) * (if C = b then Fr.ε C else 0)) • (1 : A)) • Q C b) := by
    intro C b
    rw [hrel C b, add_smul, neg_smul, smul_add, smul_neg]
  have hsum : ∑ C, ∑ b, (Fr.ε C * Fr.ε b) • ((Fr.c b * Fr.c C) • Q C b) =
      -∑ C, ∑ b, (Fr.ε C * Fr.ε b) • ((Fr.c C * Fr.c b) • Q C b) +
        (-2 : ℝ) • ∑ C, Fr.ε C • Q C C := by
    rw [← hdiag, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => key C b
  have e2 : ∑ C, ∑ b, (Fr.ε C * Fr.ε b) • ((Fr.c C * Fr.c b) • (Q C b - Q b C)) =
      ∑ C, ∑ b, (Fr.ε C * Fr.ε b) • ((Fr.c C * Fr.c b) • Q C b) -
        ∑ C, ∑ b, (Fr.ε C * Fr.ε b) • ((Fr.c C * Fr.c b) • Q b C) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_sub, smul_sub]
  rw [e2, hswap, hsum]
  module

end Laplacian

section LapJets

variable {Fr : CliffordFrame (Fin 4) (Module.End ℝ S)}

/-- **The Laplacian of the jets**: `ΔΨ = -Σ_Cε_Cc_C∇_C(𝒟Ψ) + ½Σ_{C,b}ε_Cε_bc_Cc_bR^∇_{Cb}Ψ`. -/
theorem lapJ_eq (J : LCJet Fr) (ψ : S) (dψ : Fin 4 → S) (ddψ : Fin 4 → Fin 4 → S)
    (hψ : ∀ a b, ddψ a b - ddψ b a = ∑ c, lcΛ Fr.ε J.G a b c • dψ c) :
    lapJ Fr J ψ dψ ddψ = -∑ C, Fr.ε C • (Fr.c C • covDirac Fr J.ω J.dω ψ dψ ddψ C) +
      (1 / 2 : ℝ) • ∑ C, ∑ b, (Fr.ε C * Fr.ε b) •
        ((Fr.c C * Fr.c b) • (curv (lcΛ Fr.ε J.G) J.ω J.dω C b • ψ)) := by
  have hcd : ∀ C, Fr.ε C • (Fr.c C • covDirac Fr J.ω J.dω ψ dψ ddψ C) =
      ∑ b, (Fr.ε C * Fr.ε b) • ((Fr.c C * Fr.c b) •
        cov2 (lcΓ Fr.ε J.G) J.ω J.dω ψ dψ ddψ C b) := by
    intro C
    rw [covDirac_eq Fr (lcΓ Fr.ε J.G) J.ω J.dω ψ dψ ddψ J.clifford_parallel J.metric_compat C]
    simp only [Module.End.smul_def, map_sum, map_smul, Finset.smul_sum, smul_smul,
      Module.End.mul_apply]
  have hsplit := clifford_split' Fr (fun C b => cov2 (lcΓ Fr.ε J.G) J.ω J.dω ψ dψ ddψ C b)
  have hri : ∀ C b, cov2 (lcΓ Fr.ε J.G) J.ω J.dω ψ dψ ddψ C b -
      cov2 (lcΓ Fr.ε J.G) J.ω J.dω ψ dψ ddψ b C = curv (lcΛ Fr.ε J.G) J.ω J.dω C b • ψ :=
    fun C b => ricci_identity (lcΛ Fr.ε J.G) (lcΓ Fr.ε J.G) J.ω J.dω ψ dψ ddψ hψ
      J.torsion_free C b
  simp only [hri] at hsplit
  simp only [hcd]
  unfold lapJ
  rw [hsplit]
  abel

end LapJets

/-! ### Curvature identities of the twisted Levi-Civita jets -/

section Curvature

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- **Contraction of a symmetric array with a Clifford pair**:
`Σ_{C,b}w_{Cb}c_Cc_b = -(Σ_Cε_Cw_{CC})`. -/
theorem sym_pair (Fr : CliffordFrame ι A) (w : ι → ι → ℝ) (hw : ∀ C b, w C b = w b C) :
    ∑ C, ∑ b, w C b • (Fr.c C * Fr.c b) = -(∑ C, Fr.ε C * w C C) • (1 : A) := by
  have hswap : ∑ C, ∑ b, w C b • (Fr.c C * Fr.c b) = ∑ C, ∑ b, w C b • (Fr.c b * Fr.c C) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun b _ => by rw [hw]
  have h2 : (2 : ℝ) • ∑ C, ∑ b, w C b • (Fr.c C * Fr.c b) =
      ∑ C, ∑ b, w C b • (Fr.c C * Fr.c b + Fr.c b * Fr.c C) := by
    rw [two_smul]
    conv_lhs => arg 2; rw [hswap]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => by rw [smul_add]
  simp only [Fr.anticomm, smul_smul] at h2
  have h3 : ∑ C, ∑ b, (w C b * ((-2 : ℝ) * (if C = b then Fr.ε C else 0))) • (1 : A) =
      (-2 * ∑ C, Fr.ε C * w C C) • (1 : A) := by
    rw [Finset.mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [Finset.sum_eq_single C (fun b _ hb => by rw [if_neg (Ne.symm hb)]; simp) (by simp),
      if_pos rfl]
    congr 1; ring
  rw [h3] at h2
  have h4 : (2 : ℝ) • ∑ C, ∑ b, w C b • (Fr.c C * Fr.c b) =
      (2 : ℝ) • (-(∑ C, Fr.ε C * w C C) • (1 : A)) := by
    rw [h2, smul_smul]; congr 1; ring
  exact smul_right_injective A (two_ne_zero) h4

namespace LCJetAux

variable {Fr : CliffordFrame ι A} (J : LCJet Fr)

/-- The Ricci tensor of the frame curvature is symmetric. -/
theorem ric_symm (a b : ι) : ricciOf Fr.ε J.Rm a b = ricciOf Fr.ε J.Rm b a := by
  unfold ricciOf
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [J.Rm_pair c a b c, J.Rm_anti₂ c b c a, J.Rm_anti₁ c b a c, neg_neg]

/-- The gauge curvature is antisymmetric. -/
theorem F_anti (a b : ι) : J.F b a = -J.F a b := by
  unfold LCJet.F
  have hΛ : ∀ e, lcΛ Fr.ε J.G b a e = -lcΛ Fr.ε J.G a b e := fun e => by
    unfold lcΛ; ring
  simp only [hΛ, neg_smul, Finset.sum_neg_distrib]
  abel

theorem spinPart_anti (a b : ι) : spinPart Fr (J.Rm b a) = -spinPart Fr (J.Rm a b) := by
  unfold spinPart
  rw [← smul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [J.Rm_anti₂, ← neg_smul]
  congr 1; ring

/-- **The Clifford trace of the spin curvature is the scalar curvature**:
`Σ_{C,b}ε_Cε_bc_Cc_bR^S_{Cb} = ½(Σ_Cε_CRic_{CC})`. -/
theorem spin_scalar :
    ∑ C, ∑ b, (Fr.ε C * Fr.ε b) • (Fr.c C * Fr.c b * spinPart Fr (J.Rm C b)) =
      ((1 / 2 : ℝ) * ∑ C, Fr.ε C * ricciOf Fr.ε J.Rm C C) • (1 : A) := by
  have hR := fun a => half_ricci_contraction Fr J.Rm (fun a b c d => J.Rm_anti₁ a b c d)
    (fun a b c d => J.Rm_anti₂ a b c d) J.Rm_bianchi' a
  simp only [spinorCurvature_eq_spinPart] at hR
  have e1 : ∀ C, ∑ b, (Fr.ε C * Fr.ε b) • (Fr.c C * Fr.c b * spinPart Fr (J.Rm C b)) =
      -(Fr.ε C • (Fr.c C * ∑ b, Fr.ε b • (Fr.c b * spinPart Fr (J.Rm b C)))) := by
    intro C
    rw [Finset.mul_sum, Finset.smul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [spinPart_anti J C b, mul_neg, mul_smul_comm, smul_smul, mul_neg, smul_neg, neg_neg,
      mul_assoc]
  simp only [e1, hR, Finset.sum_neg_distrib]
  have e2 : ∀ C, Fr.ε C • (Fr.c C * ((1 / 2 : ℝ) • ∑ b, (Fr.ε b * ricciOf Fr.ε J.Rm C b) •
      Fr.c b)) = (1 / 2 : ℝ) • ∑ b, (Fr.ε C * Fr.ε b * ricciOf Fr.ε J.Rm C b) •
        (Fr.c C * Fr.c b) := by
    intro C
    simp only [mul_smul_comm, Finset.mul_sum, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 1; ring
  simp only [e2]
  rw [← Finset.smul_sum, sym_pair Fr (fun C b => Fr.ε C * Fr.ε b * ricciOf Fr.ε J.Rm C b)
    (fun C b => by rw [ric_symm J]; ring)]
  have hε3 : ∀ C, Fr.ε C * (Fr.ε C * Fr.ε C * ricciOf Fr.ε J.Rm C C) =
      Fr.ε C * ricciOf Fr.ε J.Rm C C := by
    intro C
    have := Fr.sign_sq C
    have h3 : Fr.ε C * (Fr.ε C * Fr.ε C * ricciOf Fr.ε J.Rm C C) =
        Fr.ε C ^ 2 * (Fr.ε C * ricciOf Fr.ε J.Rm C C) := by ring
    rw [h3, this, one_mul]
  simp only [hε3]
  rw [smul_smul, ← neg_smul]
  congr 1
  ring

end LCJetAux

end Curvature

/-! ### Conservation of the Dirac stress on the Dirac equations -/

section OnShell

variable {W : Type*} [AddCommGroup W] [Module ℝ W]
variable {Fr : CliffordFrame (Fin 4) (Module.End ℝ S)}
  {Frb : CliffordFrame (Fin 4) (Module.End ℝ S')} (P : S' →ₗ[ℝ] S →ₗ[ℝ] ℝ)
  {J : LCJet Fr} {Jb : LCJet Frb}

/-- Mass operators commuting with Clifford pairs: so does the Yukawa part. -/
theorem L_comm_pair {m0 : Module.End ℝ S} {L : W →ₗ[ℝ] Module.End ℝ S}
    (hMcl : ∀ w c d, mass m0 L w * (Fr.c c * Fr.c d) = Fr.c c * Fr.c d * mass m0 L w)
    (w : W) (c d : Fin 4) : L w * (Fr.c c * Fr.c d) = Fr.c c * Fr.c d * L w := by
  have h1 := hMcl w c d
  have h0 := hMcl 0 c d
  unfold mass at h1 h0
  rw [map_zero, add_zero] at h0
  rw [add_mul, mul_add, h0] at h1
  exact add_left_cancel h1

/-- **`Σ_Cε_C(c_Bc_C + c_Cc_B)L_C = -2L_B`.** -/
theorem op_L (Lop : Fin 4 → Module.End ℝ S) (B : Fin 4) :
    ∑ C, Fr.ε C • ((Fr.c B * Fr.c C + Fr.c C * Fr.c B) * Lop C) = (-2 : ℝ) • Lop B := by
  simp only [Fr.anticomm, smul_mul_assoc, one_mul, smul_smul]
  rw [Finset.sum_eq_single B (fun C _ hC => by rw [if_neg (Ne.symm hC)]; simp) (by simp),
    if_pos rfl]
  congr 1
  have := Fr.sign_sq B
  linear_combination (-2 : ℝ) * this

/-- **The Clifford triple identity for an antisymmetric commuting array**:
`½Σ_{C,b}ε_Cε_b(c_Bc_Cc_b + c_bc_Cc_B)F_{Cb} = 2Σ_bε_bc_bF_{bB}`. -/
theorem op_F (Fop : Fin 4 → Fin 4 → Module.End ℝ S) (hanti : ∀ a b, Fop b a = -Fop a b)
    (B : Fin 4) :
    (1 / 2 : ℝ) • ∑ C, ∑ b, (Fr.ε C * Fr.ε b) •
        ((Fr.c B * Fr.c C * Fr.c b + Fr.c b * Fr.c C * Fr.c B) * Fop C b) =
      (2 : ℝ) • ∑ b, Fr.ε b • (Fr.c b * Fop b B) := by
  have hε : ∀ x, Fr.ε x * Fr.ε x = 1 := fun x => by rw [← sq]; exact Fr.sign_sq x
  have h0 : ∀ a, Fop a a = 0 := fun a => by
    have h := hanti a a
    have h2 : (2 : ℝ) • Fop a a = 0 := by
      rw [two_smul]
      conv_lhs => arg 1; rw [h]
      exact neg_add_cancel _
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  have hT : ∀ C b, Fr.c B * Fr.c C * Fr.c b + Fr.c b * Fr.c C * Fr.c B =
      ((-2 : ℝ) * Fr.η C b) • Fr.c B + (2 * Fr.η B b) • Fr.c C - (2 * Fr.η B C) • Fr.c b := by
    intro C b
    rw [triple_comm Fr B C b]
    have h := Fr.anticomm C b
    have e : Fr.c C * Fr.c b * Fr.c B + Fr.c b * Fr.c C * Fr.c B =
        (Fr.c C * Fr.c b + Fr.c b * Fr.c C) * Fr.c B := by rw [add_mul]
    rw [show Fr.c C * Fr.c b * Fr.c B + (2 * Fr.η B b) • Fr.c C - (2 * Fr.η B C) • Fr.c b +
        Fr.c b * Fr.c C * Fr.c B = (Fr.c C * Fr.c b * Fr.c B + Fr.c b * Fr.c C * Fr.c B) +
          (2 * Fr.η B b) • Fr.c C - (2 * Fr.η B C) • Fr.c b by abel, e, h, smul_mul_assoc,
      one_mul]
    rfl
  simp only [hT, add_mul, sub_mul, smul_mul_assoc, smul_add, smul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, smul_smul]
  unfold CliffordFrame.η
  -- the three sums
  have s1 : ∑ C, ∑ b, (Fr.ε C * Fr.ε b * (-2 * if C = b then Fr.ε C else 0)) •
      (Fr.c B * Fop C b) = 0 := by
    refine Finset.sum_eq_zero fun C _ => ?_
    rw [Finset.sum_eq_single C (fun b _ hb => by rw [if_neg (Ne.symm hb)]; simp) (by simp),
      h0, mul_zero, smul_zero]
  have s2 : ∑ C, ∑ b, (Fr.ε C * Fr.ε b * (2 * if B = b then Fr.ε B else 0)) •
      (Fr.c C * Fop C b) = (2 : ℝ) • ∑ C, Fr.ε C • (Fr.c C * Fop C B) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [Finset.sum_eq_single B (fun b _ hb => by rw [if_neg (Ne.symm hb)]; simp) (by simp),
      if_pos rfl, smul_smul]
    congr 1
    have := hε B
    linear_combination (2 * Fr.ε C) * this
  have s3 : ∑ C, ∑ b, (Fr.ε C * Fr.ε b * (2 * if B = C then Fr.ε B else 0)) •
      (Fr.c b * Fop C b) = (-2 : ℝ) • ∑ b, Fr.ε b • (Fr.c b * Fop b B) := by
    rw [Finset.sum_eq_single B (fun C _ hC => by
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [if_neg (Ne.symm hC)]; simp) (by simp)]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [if_pos rfl, hanti B b]
    have hc : Fr.ε B * Fr.ε b * (2 * Fr.ε B) = 2 * Fr.ε b := by
      have := hε B
      linear_combination (2 * Fr.ε b) * this
    rw [hc, mul_neg]
    module
  rw [s1, s2, s3]
  module

end OnShell

section OnShell2

variable {W : Type*} [AddCommGroup W] [Module ℝ W]
variable {Fr : CliffordFrame (Fin 4) (Module.End ℝ S)}
  {Frb : CliffordFrame (Fin 4) (Module.End ℝ S')} (P : S' →ₗ[ℝ] S →ₗ[ℝ] ℝ)
  {J : LCJet Fr} {Jb : LCJet Frb}

/-- Equal frame data give equal curvature arrays. -/
theorem Rm_congr (hG : Jb.G = J.G) (hdG : Jb.dG = J.dG) (hε : Frb.ε = Fr.ε) : Jb.Rm = J.Rm := by
  funext a b x y
  unfold LCJet.Rm lcΛ lcΓ
  rw [hG, hdG, hε]

/-- **The Laplacian on the Dirac equation**:
`ΔΨ = -Σ_Cε_Cc_C(𝓜X_C + 𝓜_H[D_CH]Ψ) + ¼(Σε_CRic_{CC})Ψ + ½Σε_Cε_bc_Cc_bρ(F_{Cb})Ψ`. -/
theorem lapJ_onshell (m0 : Module.End ℝ S) (L : W →ₗ[ℝ] Module.End ℝ S) (ρH : Fin 4 → W →ₗ[ℝ] W)
    (h : W) (dh : Fin 4 → W)
    (hMcl : ∀ w c d, mass m0 L w * (Fr.c c * Fr.c d) = Fr.c c * Fr.c d * mass m0 L w)
    (hMg : ∀ a w, J.ρ a * mass m0 L w - mass m0 L w * J.ρ a = L (ρH a w))
    (ψ : S) (dψ : Fin 4 → S) (ddψ : Fin 4 → Fin 4 → S)
    (hψ : ∀ a b, ddψ a b - ddψ b a = ∑ c, lcΛ Fr.ε J.G a b c • dψ c)
    (hcD : ∀ a, covResD Fr J.ω J.dω m0 L h dh ψ dψ ddψ a = 0) :
    lapJ Fr J ψ dψ ddψ = -∑ C, Fr.ε C • (Fr.c C • (mass m0 L h • cov J.ω ψ dψ C +
        L (DH ρH h dh C) • ψ)) +
      ((1 / 4 : ℝ) * ∑ C, Fr.ε C * ricciOf Fr.ε J.Rm C C) • ψ +
      (1 / 2 : ℝ) • ∑ C, ∑ b, (Fr.ε C * Fr.ε b) • ((Fr.c C * Fr.c b) • (J.F C b • ψ)) := by
  rw [lapJ_eq J ψ dψ ddψ hψ]
  have hcd : ∀ C, covDirac Fr J.ω J.dω ψ dψ ddψ C =
      mass m0 L h • cov J.ω ψ dψ C + L (DH ρH h dh C) • ψ := fun C => by
    rw [covDirac_eq_mass Fr J.ω J.dω m0 L ρH h dh ψ dψ ddψ
      (J.mass_equivariant m0 L ρH hMcl hMg) C, hcD C, add_zero]
  have hsp : (1 / 2 : ℝ) • ∑ C, ∑ b, (Fr.ε C * Fr.ε b) •
      ((Fr.c C * Fr.c b) • (spinPart Fr (J.Rm C b) • ψ)) =
      ((1 / 4 : ℝ) * ∑ C, Fr.ε C * ricciOf Fr.ε J.Rm C C) • ψ := by
    have e : ∑ C, ∑ b, (Fr.ε C * Fr.ε b) • ((Fr.c C * Fr.c b) • (spinPart Fr (J.Rm C b) • ψ)) =
        (∑ C, ∑ b, (Fr.ε C * Fr.ε b) • (Fr.c C * Fr.c b * spinPart Fr (J.Rm C b))) • ψ := by
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun C _ => ?_
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [smul_assoc, mul_smul]
    rw [e, LCJetAux.spin_scalar J, smul_assoc, one_smul, smul_smul]
    congr 1; ring
  simp only [hcd, J.curv_eq, add_smul, smul_add, Finset.sum_add_distrib]
  rw [hsp]
  abel

end OnShell2

section OnShell3

variable {W : Type*} [AddCommGroup W] [Module ℝ W]
variable {Fr : CliffordFrame (Fin 4) (Module.End ℝ S)}
  {Frb : CliffordFrame (Fin 4) (Module.End ℝ S')} (P : S' →ₗ[ℝ] S →ₗ[ℝ] ℝ)
  {J : LCJet Fr} {Jb : LCJet Frb}

/-- **Conservation of the Dirac stress on the Dirac equations (jets)**: if the Dirac and dual
Dirac residuals and their first covariant derivatives vanish, the frame divergence of the kinetic
Dirac stress is the Lorentz force minus the Yukawa force:
`Σ_Aε_A∇_AK_{AB} = Σ_bε_b⟨Ψ̄, ρ(F_{Bb})c_bΨ⟩ - ⟨Ψ̄, 𝓜_H[D_BH]Ψ⟩`. -/
theorem div_kin_onshell (m0 : Module.End ℝ S) (L : W →ₗ[ℝ] Module.End ℝ S)
    (m0b : Module.End ℝ S') (Lb : W →ₗ[ℝ] Module.End ℝ S') (ρH : Fin 4 → W →ₗ[ℝ] W) (h : W)
    (dh : Fin 4 → W) (hG : Jb.G = J.G) (hdG : Jb.dG = J.dG) (hε : Frb.ε = Fr.ε)
    (htω : ∀ a (φ : S') (x : S), P (Jb.ω a • φ) x = -P φ (J.ω a • x))
    (htc : ∀ A (φ : S') (x : S), P (Frb.c A • φ) x = P φ (Fr.c A • x))
    (htF : ∀ a b (φ : S') (x : S), P (Jb.F a b • φ) x = -P φ (J.F a b • x))
    (htM : ∀ w (φ : S') (x : S), P (mass m0b Lb w • φ) x = -P φ (mass m0 L w • x))
    (htL : ∀ w (φ : S') (x : S), P (Lb w • φ) x = -P φ (L w • x))
    (hFc : ∀ a b c, J.F a b * Fr.c c = Fr.c c * J.F a b)
    (hMcl : ∀ w c d, mass m0 L w * (Fr.c c * Fr.c d) = Fr.c c * Fr.c d * mass m0 L w)
    (hMg : ∀ a w, J.ρ a * mass m0 L w - mass m0 L w * J.ρ a = L (ρH a w))
    (hMclb : ∀ w c d, mass m0b Lb w * (Frb.c c * Frb.c d) = Frb.c c * Frb.c d * mass m0b Lb w)
    (hMgb : ∀ a w, Jb.ρ a * mass m0b Lb w - mass m0b Lb w * Jb.ρ a = Lb (ρH a w))
    (ψ : S) (dψ : Fin 4 → S) (ddψ : Fin 4 → Fin 4 → S) (ψb : S') (dψb : Fin 4 → S')
    (ddψb : Fin 4 → Fin 4 → S')
    (hψ : ∀ a b, ddψ a b - ddψ b a = ∑ c, lcΛ Fr.ε J.G a b c • dψ c)
    (hψb : ∀ a b, ddψb a b - ddψb b a = ∑ c, lcΛ Frb.ε Jb.G a b c • dψb c)
    (hD : resD Fr J.ω m0 L h ψ dψ = 0)
    (hcD : ∀ a, covResD Fr J.ω J.dω m0 L h dh ψ dψ ddψ a = 0)
    (hDb : resD Frb Jb.ω m0b Lb h ψb dψb = 0)
    (hcDb : ∀ a, covResD Frb Jb.ω Jb.dω m0b Lb h dh ψb dψb ddψb a = 0) (B : Fin 4) :
    ∑ A, Fr.ε A * covKJ P J Jb ψ dψ ddψ ψb dψb ddψb A A B =
      ∑ b, Fr.ε b * P ψb ((J.F B b * Fr.c b) • ψ) - P ψb (L (DH ρH h dh B) • ψ) := by
  rw [div_covKJ P hG hε htω htc ψ dψ ddψ ψb dψb ddψb B]
  have hdir : dirac Fr J.ω ψ dψ = mass m0 L h • ψ := sub_eq_zero.1 hD
  have hdirb : dirac Frb Jb.ω ψb dψb = mass m0b Lb h • ψb := sub_eq_zero.1 hDb
  have hRm := Rm_congr hG hdG hε
  have hT2 := J.spinor_prolongation m0 L ρH h dh ψ dψ ddψ hψ hMcl hMg B
  rw [hcD B, add_zero] at hT2
  have hT2b := Jb.spinor_prolongation m0b Lb ρH h dh ψb dψb ddψb hψb hMclb hMgb B
  rw [hcDb B, add_zero] at hT2b
  have hlap := lapJ_onshell m0 L ρH h dh hMcl hMg ψ dψ ddψ hψ hcD
  have hlapb := lapJ_onshell m0b Lb ρH h dh hMclb hMgb ψb dψb ddψb hψb hcDb
  rw [hdir, hdirb, hT2, hT2b, hlap, hlapb]
  have htc' : ∀ A (φ : S') (x : S), P (Frb.c A φ) x = P φ (Fr.c A x) := htc
  have htF' : ∀ a b (φ : S') (x : S), P (Jb.F a b φ) x = -P φ (J.F a b x) := htF
  have htM' : ∀ w (φ : S') (x : S), P (mass m0b Lb w φ) x = -P φ (mass m0 L w x) := htM
  have htL' : ∀ w (φ : S') (x : S), P (Lb w φ) x = -P φ (L w x) := htL
  have hric : ∀ a b, ricciOf Frb.ε Jb.Rm a b = ricciOf Fr.ε J.Rm a b := by
    intro a b; rw [hRm, hε]
  set M := mass m0 L h with hM
  set X := cov J.ω ψ dψ with hX
  set Xb := cov Jb.ω ψb dψb with hXb
  set LH := fun x => L (DH ρH h dh x) with hLH
  have hdir' : ∑ x, Fr.ε x • Fr.c x (X x) = M ψ := by
    have := hdir; unfold dirac at this; simpa only [Module.End.smul_def] using this
  have hdirb' : ∑ x, Fr.ε x • Frb.c x (Xb x) = mass m0b Lb h ψb := by
    have := hdirb; unfold dirac at this; simpa only [Module.End.smul_def, hε] using this
  -- the relations
  have R1 : ∑ x, Fr.ε x * P ψb (Fr.c B (Fr.c x (M (X x)))) = P ψb (M (Fr.c B (M ψ))) := by
    have hc : ∀ x v, Fr.c B (Fr.c x (M v)) = M (Fr.c B (Fr.c x v)) := by
      intro x v
      have := hMcl h B x
      calc Fr.c B (Fr.c x (M v)) = (Fr.c B * Fr.c x * M) v := rfl
        _ = (M * (Fr.c B * Fr.c x)) v := by rw [this]
        _ = M (Fr.c B (Fr.c x v)) := rfl
    simp only [hc]
    rw [← hdir']
    simp only [map_sum, map_smul, smul_eq_mul]
  have R2 : ∑ x, Fr.ε x * P (Xb x) (M (Fr.c x (Fr.c B ψ))) = -P ψb (M (Fr.c B (M ψ))) := by
    have hc : ∀ x v, M (Fr.c x (Fr.c B v)) = Fr.c x (Fr.c B (M v)) := by
      intro x v
      have := hMcl h x B
      calc M (Fr.c x (Fr.c B v)) = (M * (Fr.c x * Fr.c B)) v := rfl
        _ = (Fr.c x * Fr.c B * M) v := by rw [this]
        _ = Fr.c x (Fr.c B (M v)) := rfl
    simp only [hc]
    have e : ∀ x, P (Xb x) (Fr.c x (Fr.c B (M ψ))) = P (Frb.c x (Xb x)) (Fr.c B (M ψ)) :=
      fun x => (htc' x _ _).symm
    simp only [e]
    rw [← htM', ← hdirb']
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  have R3 : ∑ x, Fr.ε x * P ψb (Fr.c B (Fr.c x (LH x ψ))) +
      ∑ x, Fr.ε x * P ψb (LH x (Fr.c x (Fr.c B ψ))) = -2 * P ψb (LH B ψ) := by
    have hc : ∀ x v, LH x (Fr.c x (Fr.c B v)) = Fr.c x (Fr.c B (LH x v)) := by
      intro x v
      have := L_comm_pair hMcl (DH ρH h dh x) x B
      calc LH x (Fr.c x (Fr.c B v)) = (L (DH ρH h dh x) * (Fr.c x * Fr.c B)) v := rfl
        _ = (Fr.c x * Fr.c B * L (DH ρH h dh x)) v := by rw [this]
        _ = Fr.c x (Fr.c B (LH x v)) := rfl
    have hop := op_L (Fr := Fr) LH B
    have e : P ψb ((∑ x, Fr.ε x • ((Fr.c B * Fr.c x + Fr.c x * Fr.c B) * LH x)) ψ) =
        ∑ x, Fr.ε x * P ψb (Fr.c B (Fr.c x (LH x ψ))) +
          ∑ x, Fr.ε x * P ψb (LH x (Fr.c x (Fr.c B ψ))) := by
      simp only [hc, LinearMap.sum_apply, LinearMap.smul_apply, add_mul, LinearMap.add_apply,
        Module.End.mul_apply, map_sum, map_smul, map_add, smul_eq_mul, mul_add,
        Finset.sum_add_distrib]
    rw [← e, hop, LinearMap.smul_apply, map_smul, smul_eq_mul]
  have R4 : ∑ x, Fr.ε x * P ψb (J.F x B (Fr.c x ψ)) = ∑ x, Fr.ε x * P ψb (Fr.c x (J.F x B ψ)) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 2
    exact LinearMap.congr_fun (hFc x B x) ψ
  have R5 : ∑ x, ∑ i, 1 / 2 * (Fr.ε x * (Fr.ε i * P ψb (Fr.c B (Fr.c x (Fr.c i (J.F x i ψ)))))) +
      ∑ x, ∑ i, 1 / 2 * (Fr.ε x * (Fr.ε i * P ψb (J.F x i (Fr.c i (Fr.c x (Fr.c B ψ)))))) =
      2 * ∑ x, Fr.ε x * P ψb (Fr.c x (J.F x B ψ)) := by
    have hc : ∀ x i v, J.F x i (Fr.c i (Fr.c x (Fr.c B v))) =
        Fr.c i (Fr.c x (Fr.c B (J.F x i v))) := by
      intro x i v
      have h1 := hFc x i i
      have h2 := hFc x i x
      have h3 := hFc x i B
      calc J.F x i (Fr.c i (Fr.c x (Fr.c B v))) = (J.F x i * Fr.c i * Fr.c x * Fr.c B) v := rfl
        _ = (Fr.c i * Fr.c x * Fr.c B * J.F x i) v := by
          rw [h1, mul_assoc (Fr.c i), h2, ← mul_assoc, mul_assoc (Fr.c i * Fr.c x), h3, ← mul_assoc]
        _ = Fr.c i (Fr.c x (Fr.c B (J.F x i v))) := rfl
    have hop := op_F (Fr := Fr) (fun a b => J.F a b) (fun a b => LCJetAux.F_anti J a b) B
    have e : P ψb (((1 / 2 : ℝ) • ∑ C, ∑ b, (Fr.ε C * Fr.ε b) •
        ((Fr.c B * Fr.c C * Fr.c b + Fr.c b * Fr.c C * Fr.c B) * J.F C b)) ψ) =
        ∑ x, ∑ i, 1 / 2 * (Fr.ε x * (Fr.ε i * P ψb (Fr.c B (Fr.c x (Fr.c i (J.F x i ψ)))))) +
        ∑ x, ∑ i, 1 / 2 * (Fr.ε x * (Fr.ε i * P ψb (J.F x i (Fr.c i (Fr.c x (Fr.c B ψ)))))) := by
      simp only [hc, LinearMap.sum_apply, LinearMap.smul_apply, add_mul, LinearMap.add_apply,
        Module.End.mul_apply, map_sum, map_smul, map_add, smul_eq_mul, mul_add,
        Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    rw [← e, hop, LinearMap.smul_apply, map_smul, smul_eq_mul, LinearMap.sum_apply, map_sum]
    simp only [LinearMap.smul_apply, Module.End.mul_apply, map_smul, smul_eq_mul]
  have R6 : ∑ x, Fr.ε x * P ψb (J.F B x (Fr.c x ψ)) = -∑ x, Fr.ε x * P ψb (Fr.c x (J.F x B ψ)) := by
    rw [← R4, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [LCJetAux.F_anti J x B, LinearMap.neg_apply, map_neg, mul_neg]
  simp only [Module.End.smul_def, Module.End.mul_apply, map_add, map_neg, map_sum, map_smul,
    LinearMap.add_apply, LinearMap.neg_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, htc', htF', htM', htL', hRm, hε, Finset.mul_sum, mul_neg, neg_mul,
    Finset.sum_neg_distrib, mul_add, mul_assoc, Finset.sum_add_distrib]
  linear_combination (1 / 4 : ℝ) * R1 + (1 / 4 : ℝ) * R2 + (1 / 4 : ℝ) * R3 -
    (1 / 4 : ℝ) * R4 - (1 / 4 : ℝ) * R5 - R6

end OnShell3

end RenewalGeometry.GenDSJ
