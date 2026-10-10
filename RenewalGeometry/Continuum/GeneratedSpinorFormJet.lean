/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.SpinorProlongationJet

/-!
# Spinor-valued one-forms: the Clifford-contracted square of the twisted Dirac operator

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`
(`app:generated-dynamics`), coupled (Dirac back-reaction) constraint propagation: the defect
`Y_A = X_A(W) - ∇_AΨ(z)` of the auxiliary spinor jets is a spinor-valued one-form with
`Σ_A ε_Ac_AY_A = 0`.  Its subsidiary system needs the **normal prolongation defect**, whose
evolution comes from the identity proved here (jets at one point, generic module):

* `liftE`, `liftFr` — Clifford multiplication acting on the spinor index of `S`-valued one-forms
  `Fin 4 → S`; `formΓ` — the Levi-Civita connection acting on the form index; `omegaP` — the
  twisted connection `ω'_b Y = (ω_bY_A - Σ_CΓ_{bA}{}^CY_C)_A` on one-forms;
* `kap` — the Clifford contraction `κ(Y) = Σ_A ε_Ac_AY_A`; `kap_omegaP` — `κ ∘ ω'_a = ω_a ∘ κ`
  (Clifford parallelism + metric compatibility);
* **`kap_dirac_dirac`** — for jets of a one-form `Y` with `κ(∇_bY) = 0` and `κ(e_a∇_bY) = 0`
  (the jets of `κ(Y) ≡ 0`), `κ(𝒟'(𝒟'Y)) = ½Σ_{a,b} ε_aε_b κ(c_ac_b R'_{ab}Y)`: the Clifford
  contraction of the square of the twisted Dirac operator is of order zero (Weitzenböck: the
  symmetric part is `-Σ_aε_a∇²_{aa}`, annihilated by `κ`; the antisymmetric part is curvature).
-/

open Finset

noncomputable section

namespace RenewalGeometry.GenSFJ

open SpinorProlongation TwistedHalfRicci

set_option linter.unusedSectionVars false

variable {S : Type*} [AddCommGroup S] [Module ℝ S]

/-- Componentwise action of an endomorphism of `S` on `S`-valued one-forms. -/
def liftE (x : Module.End ℝ S) : Module.End ℝ (Fin 4 → S) :=
  LinearMap.pi fun i => x ∘ₗ LinearMap.proj i

@[simp] theorem liftE_apply (x : Module.End ℝ S) (Y : Fin 4 → S) (i : Fin 4) :
    liftE x Y i = x (Y i) := rfl

theorem liftE_mul (x y : Module.End ℝ S) : liftE (x * y) = liftE x * liftE y := by
  ext Y i; rfl

theorem liftE_add (x y : Module.End ℝ S) : liftE (x + y) = liftE x + liftE y := by
  ext Y i; rfl

theorem liftE_smul (r : ℝ) (x : Module.End ℝ S) : liftE (r • x) = r • liftE x := by
  ext Y i; rfl

theorem liftE_one : liftE (1 : Module.End ℝ S) = 1 := by
  ext Y i; rfl

/-- The lifted Clifford frame acting on one-forms. -/
def liftFr (Fr : CliffordFrame (Fin 4) (Module.End ℝ S)) :
    CliffordFrame (Fin 4) (Module.End ℝ (Fin 4 → S)) where
  c b := liftE (Fr.c b)
  ε := Fr.ε
  sign_sq := Fr.sign_sq
  anticomm a b := by
    rw [← liftE_mul, ← liftE_mul, ← liftE_add, Fr.anticomm, liftE_smul, liftE_one]

/-- The Levi-Civita connection on the form index: `(Γ_b Y)_A = Σ_C Γ_{bA}{}^C Y_C`. -/
def formΓ (Γb : Fin 4 → Fin 4 → ℝ) : Module.End ℝ (Fin 4 → S) where
  toFun Y := fun A => ∑ C, Γb A C • Y C
  map_add' Y Y' := by funext A; simp [smul_add, Finset.sum_add_distrib]
  map_smul' r Y := by funext A; simp [Finset.smul_sum, smul_comm r]

@[simp] theorem formΓ_apply (Γb : Fin 4 → Fin 4 → ℝ) (Y : Fin 4 → S) (A : Fin 4) :
    formΓ Γb Y A = ∑ C, Γb A C • Y C := rfl

theorem liftE_formΓ (x : Module.End ℝ S) (Γb : Fin 4 → Fin 4 → ℝ) :
    liftE x * formΓ Γb = formΓ Γb * liftE x := by
  ext Y A
  simp [map_sum, map_smul]

/-- **The twisted connection on spinor-valued one-forms**: `ω'_b = ω_b ⊗ 1 - 1 ⊗ Γ_b`. -/
def omegaP (ω : Fin 4 → Module.End ℝ S) (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) (b : Fin 4) :
    Module.End ℝ (Fin 4 → S) :=
  liftE (ω b) - formΓ (Γ b)

theorem omegaP_apply (ω : Fin 4 → Module.End ℝ S) (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) (b : Fin 4)
    (Y : Fin 4 → S) (A : Fin 4) :
    omegaP ω Γ b Y A = ω b (Y A) - ∑ C, Γ b A C • Y C := rfl

/-- **Clifford parallelism lifts to one-forms**: `[ω'_a, c_b] = Σ_c Γ_{ab}{}^c c_c`. -/
theorem omegaP_cl (Fr : CliffordFrame (Fin 4) (Module.End ℝ S)) (ω : Fin 4 → Module.End ℝ S)
    (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hcl : ∀ a b, ω a * Fr.c b - Fr.c b * ω a = ∑ c, Γ a b c • Fr.c c) (a b : Fin 4) :
    omegaP ω Γ a * (liftFr Fr).c b - (liftFr Fr).c b * omegaP ω Γ a =
      ∑ c, Γ a b c • (liftFr Fr).c c := by
  show (liftE (ω a) - formΓ (Γ a)) * liftE (Fr.c b) - liftE (Fr.c b) * (liftE (ω a) - formΓ (Γ a))
    = ∑ c, Γ a b c • liftE (Fr.c c)
  rw [sub_mul, mul_sub, ← liftE_mul, ← liftE_mul, ← liftE_formΓ (Fr.c b) (Γ a)]
  have : liftE (ω a * Fr.c b) - liftE (Fr.c b * ω a) = ∑ c, Γ a b c • liftE (Fr.c c) := by
    rw [show liftE (ω a * Fr.c b) - liftE (Fr.c b * ω a) = liftE (ω a * Fr.c b - Fr.c b * ω a) by
      ext Y A; simp, hcl]
    ext Y A
    simp [LinearMap.sum_apply, Finset.sum_apply]
  rw [← this]
  abel

/-- **The Clifford contraction** `κ(Y) = Σ_A ε_Ac_AY_A`. -/
def kap (Fr : CliffordFrame (Fin 4) (Module.End ℝ S)) : (Fin 4 → S) →ₗ[ℝ] S where
  toFun Y := ∑ A, Fr.ε A • Fr.c A (Y A)
  map_add' Y Y' := by simp [smul_add, Finset.sum_add_distrib]
  map_smul' r Y := by simp [Finset.smul_sum, smul_comm r]

theorem kap_apply (Fr : CliffordFrame (Fin 4) (Module.End ℝ S)) (Y : Fin 4 → S) :
    kap Fr Y = ∑ A, Fr.ε A • Fr.c A (Y A) := rfl

/-- **`κ` intertwines the connections**: `κ(ω'_aY) = ω_aκ(Y)`. -/
theorem kap_omegaP (Fr : CliffordFrame (Fin 4) (Module.End ℝ S)) (ω : Fin 4 → Module.End ℝ S)
    (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hcl : ∀ a b, ω a * Fr.c b - Fr.c b * ω a = ∑ c, Γ a b c • Fr.c c)
    (hmc : ∀ a b c, Fr.ε c * Γ a b c = -(Fr.ε b * Γ a c b)) (a : Fin 4) (Y : Fin 4 → S) :
    kap Fr (omegaP ω Γ a Y) = ω a (kap Fr Y) := by
  have hc : ∀ A x, ω a (Fr.c A x) = Fr.c A (ω a x) + ∑ C, Γ a A C • Fr.c C x := by
    intro A x
    have h := congrArg (fun T : Module.End ℝ S => T x) (hcl a A)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply,
      LinearMap.smul_apply] at h
    rw [← h]; abel
  simp only [kap_apply, omegaP_apply, map_sub, map_sum, map_smul, smul_sub, Finset.smul_sum]
  rw [Finset.sum_sub_distrib]
  simp only [hc, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
  -- the Γ-terms cancel by metric compatibility
  have key : ∑ A, ∑ C, Fr.ε A • Γ a A C • Fr.c A (Y C) =
      -∑ A, ∑ C, Fr.ε A • Γ a A C • Fr.c C (Y A) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [smul_smul, smul_smul, ← neg_smul]
    congr 1
    have h1 := hmc a A C
    have hA := Fr.sign_sq A
    have hC := Fr.sign_sq C
    linear_combination (Fr.ε A * Fr.ε C) * h1 - (Fr.ε A * Γ a A C) * hC -
      (Fr.ε C * Γ a C A) * hA
  rw [key]
  abel

/-- `Σ_{a,b} ε_aε_b c_ac_bX_{ab} = ½Σ_{a,b} ε_aε_b c_ac_b(X_{ab} - X_{ba}) - Σ_a ε_aX_{aa}`
(the Clifford relation `c_ac_b + c_bc_a = -2ε_aδ_{ab}`), in any module. -/
theorem clifford_split {A V : Type*} [Ring A] [Algebra ℝ A] [AddCommGroup V] [Module A V]
    [Module ℝ V] [IsScalarTower ℝ A V] (Fr : CliffordFrame (Fin 4) A) (X : Fin 4 → Fin 4 → V) :
    ∑ a, ∑ b, (Fr.ε a * Fr.ε b) • ((Fr.c a * Fr.c b) • X a b) =
      (1 / 2 : ℝ) • ∑ a, ∑ b, (Fr.ε a * Fr.ε b) • ((Fr.c a * Fr.c b) • (X a b - X b a)) -
        ∑ a, Fr.ε a • X a a := by
  set T := ∑ a, ∑ b, (Fr.ε a * Fr.ε b) • ((Fr.c a * Fr.c b) • X a b) with hT
  set U := ∑ a, ∑ b, (Fr.ε a * Fr.ε b) • ((Fr.c a * Fr.c b) • X b a) with hU
  have hU' : U = ∑ a, ∑ b, (Fr.ε a * Fr.ε b) • ((Fr.c b * Fr.c a) • X a b) := by
    rw [hU, Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [mul_comm]
  have hTU : T + U = (-2 : ℝ) • ∑ a, Fr.ε a • X a a := by
    rw [hT, hU', ← Finset.sum_add_distrib]
    have e1 : ∀ a, ∑ b, (Fr.ε a * Fr.ε b) • ((Fr.c a * Fr.c b) • X a b) +
        ∑ b, (Fr.ε a * Fr.ε b) • ((Fr.c b * Fr.c a) • X a b) = (-2 : ℝ) • (Fr.ε a • X a a) := by
      intro a
      rw [← Finset.sum_add_distrib]
      have e2 : ∀ b, (Fr.ε a * Fr.ε b) • ((Fr.c a * Fr.c b) • X a b) +
          (Fr.ε a * Fr.ε b) • ((Fr.c b * Fr.c a) • X a b) =
          (Fr.ε a * Fr.ε b * ((-2 : ℝ) * (if a = b then Fr.ε a else 0))) • X a b := by
        intro b
        rw [← smul_add, ← add_smul, Fr.anticomm, smul_assoc, one_smul, smul_smul]
      rw [Finset.sum_congr rfl fun b _ => e2 b, Finset.sum_eq_single a]
      · simp only [if_true, smul_smul]
        congr 1
        have := Fr.sign_sq a
        linear_combination (-2 * Fr.ε a) * this
      · intro b _ hb
        simp [Ne.symm hb]
      · simp
    rw [Finset.sum_congr rfl fun a _ => e1 a, ← Finset.smul_sum]
  have hTmU : T - U = ∑ a, ∑ b, (Fr.ε a * Fr.ε b) • ((Fr.c a * Fr.c b) • (X a b - X b a)) := by
    rw [hT, hU, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_sub, smul_sub]
  have hfin : T = (1 / 2 : ℝ) • (T - U) + (1 / 2 : ℝ) • (T + U) := by
    rw [← smul_add, sub_add_add_cancel, ← two_smul ℝ T, smul_smul]
    norm_num
  rw [hfin, hTmU, hTU, smul_smul]
  norm_num
  abel

variable (Fr : CliffordFrame (Fin 4) (Module.End ℝ S)) (Λ Γ : Fin 4 → Fin 4 → Fin 4 → ℝ)
  (ω : Fin 4 → Module.End ℝ S) (dωP : Fin 4 → Fin 4 → Module.End ℝ (Fin 4 → S))

/-- **The Clifford contraction of the square of the twisted Dirac operator on one-forms is of
order zero** (jets at a point).  For one-form jets `(Y, dY, ddY)` obeying the frame commutator
relation, a torsion-free metric twisted connection with Clifford parallelism, and the jet
identities of `κ(Y) ≡ 0` in the form `κ(∇_bY) = 0`, `κ(e_a∇_bY) = 0`:
`κ(Σ_a ε_ac_a∇_a(𝒟'Y)) = ½Σ_{a,b} ε_aε_b κ(c_ac_b R'_{ab}Y)`. -/
theorem kap_dirac_dirac (Y : Fin 4 → S) (dY : Fin 4 → Fin 4 → S)
    (ddY : Fin 4 → Fin 4 → Fin 4 → S)
    (hψ : ∀ a b, ddY a b - ddY b a = ∑ c, Λ a b c • dY c)
    (htf : ∀ a b c, Γ a b c - Γ b a c = Λ a b c)
    (hcl : ∀ a b, ω a * Fr.c b - Fr.c b * ω a = ∑ c, Γ a b c • Fr.c c)
    (hmc : ∀ a b c, Fr.ε c * Γ a b c = -(Fr.ε b * Γ a c b))
    (hk1 : ∀ b, kap Fr (cov (omegaP ω Γ) Y dY b) = 0)
    (hk2 : ∀ a b, kap Fr (dcov (omegaP ω Γ) dωP Y dY ddY a b) = 0) :
    kap Fr (∑ a, (liftFr Fr).ε a • ((liftFr Fr).c a •
        covDirac (liftFr Fr) (omegaP ω Γ) dωP Y dY ddY a)) =
      (1 / 2 : ℝ) • ∑ a, ∑ b, (Fr.ε a * Fr.ε b) • kap Fr (((liftFr Fr).c a * (liftFr Fr).c b) •
        (curv Λ (omegaP ω Γ) dωP a b • Y)) := by
  have hclP := omegaP_cl Fr ω Γ hcl
  set X : Fin 4 → Fin 4 → (Fin 4 → S) := fun a b => cov2 Γ (omegaP ω Γ) dωP Y dY ddY a b with hX
  have h1 : ∀ a, covDirac (liftFr Fr) (omegaP ω Γ) dωP Y dY ddY a =
      ∑ b, (liftFr Fr).ε b • ((liftFr Fr).c b • X a b) := fun a =>
    covDirac_eq (liftFr Fr) Γ (omegaP ω Γ) dωP Y dY ddY hclP hmc a
  have h2 : ∑ a, (liftFr Fr).ε a • ((liftFr Fr).c a •
        covDirac (liftFr Fr) (omegaP ω Γ) dωP Y dY ddY a) =
      ∑ a, ∑ b, ((liftFr Fr).ε a * (liftFr Fr).ε b) •
        (((liftFr Fr).c a * (liftFr Fr).c b) • X a b) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [h1, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_comm ((liftFr Fr).c a) ((liftFr Fr).ε b)]
    rw [show ((liftFr Fr).c a * (liftFr Fr).c b) • X a b =
      (liftFr Fr).c a • (liftFr Fr).c b • X a b from mul_smul _ _ _, ← smul_smul]
  rw [h2, clifford_split]
  have hric : ∀ a b, X a b - X b a = curv Λ (omegaP ω Γ) dωP a b • Y := fun a b =>
    ricci_identity Λ Γ (omegaP ω Γ) dωP Y dY ddY hψ htf a b
  -- `κ` kills the symmetric part
  have hdiag : ∀ a, kap Fr (X a a) = 0 := by
    intro a
    simp only [hX, cov2, map_sub, map_add, map_sum, map_smul, hk2]
    rw [show omegaP ω Γ a • cov (omegaP ω Γ) Y dY a = omegaP ω Γ a (cov (omegaP ω Γ) Y dY a)
      from rfl, kap_omegaP Fr ω Γ hcl hmc, hk1]
    simp [hk1]
  simp only [hric, map_sub, map_smul, map_sum, hdiag, smul_zero, Finset.sum_const_zero, sub_zero]
  rfl

end RenewalGeometry.GenSFJ
