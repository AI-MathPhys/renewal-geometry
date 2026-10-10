/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedDiracCurrent

/-!
# The symmetric Dirac stress in the theory data (back-reacting spinors)

Einstein–Standard-Model action-closure manuscript, `eq:dirac-density`, `eq:stress-definition`
("the Dirac–Yukawa contribution is always taken from the complete metric variation"),
`prop:actual-jet-writer` and `lem:generated-physical-identification`.

The Hilbert stress of the symmetrised Dirac density
`L_D = ½[⟨Ψ̄, 𝒟Ψ⟩ - ⟨𝒟̄Ψ̄, Ψ⟩] - ⟨Ψ̄, 𝓜(H)Ψ⟩` (which differs from `GenDiracCur`'s
`⟨Ψ̄, 𝒟Ψ - 𝓜Ψ⟩` by a divergence, hence has the same stress) is, in the frame,
`T_{AB} = -¼[⟨Ψ̄, c_AX_B⟩ + ⟨Ψ̄, c_BX_A⟩ - ⟨X̄_B, c_AΨ⟩ - ⟨X̄_A, c_BΨ⟩] + η_{AB}L_D(X)`,
`L_D(X) = ½Σ_C ε_C[⟨Ψ̄, c_CX_C⟩ - ⟨X̄_C, c_CΨ⟩] - ⟨Ψ̄, 𝓜(H)Ψ⟩`
(the same frame form as the native slab stress `SlabData.TD`, `RecordTuple.frame_TD`).

* `symTD` — this stress as a `DiracStressForm` (`P_{ABC}`, `P'_{ABC} = -P_{ABC}`,
  `P''_{AB}(H) = -η_{AB}⟨·, 𝓜(H)·⟩`);
* **`CoupledDirac SM`** — variational Einstein–Yang–Mills–Higgs–Dirac theory data with the
  Dirac back-reaction: `GenDiracCur.VariationalDirac` (spinor pairing, Dirac current, Yukawa
  source), symmetric ad-invariant gauge form, symmetric Higgs form and `SM.TD = symTD`;
* `frame_symTD`, `frame_symTD_symm`, **`frame_symTD_sub`** — the frame stress, its symmetry and
  the difference of the stresses at two spinor jets with the same normal Dirac relation (linear in
  the jet differences, no trace part);
* `quatSMT`, `quatCoupled` — the charged quaternionic data `GenDiracCur.quatSM` with the Dirac
  stress switched on: non-vacuity with a nonzero, charged, back-reacting spinor.
-/

open Finset

noncomputable section

namespace RenewalGeometry.GenDStress

open ActualJetSystem ActualJetRecon SpinorProlongation TwistedHalfRicci GenDiracCur GenNoether ActualJetSmooth
  ActualJetBridge

set_option linter.unusedSectionVars false

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

/-- The Minkowski metric `η_{AB} = ε_Aδ_{AB}`. -/
def etaL (A B : Fin 4) : ℝ := if A = B then lorentzSign A else 0

theorem etaL_symm (A B : Fin 4) : etaL A B = etaL B A := by
  unfold etaL
  by_cases h : A = B
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- The kinetic kernel `P_{ABC}(φ, x) = -¼(δ_{CB}⟨φ, c_Ax⟩ + δ_{CA}⟨φ, c_Bx⟩) + ½η_{AB}ε_C⟨φ, c_Cx⟩`. -/
def kinP (D : DiracData (MatLie m) V S) (P : S' →ₗ[ℝ] S →ₗ[ℝ] ℝ) (A B C : Fin 4) :
    S' →ₗ[ℝ] S →ₗ[ℝ] ℝ :=
  (-(1 / 4 : ℝ)) • ((if C = B then (1 : ℝ) else 0) • P.compl₂ (D.Fr.c A) +
      (if C = A then (1 : ℝ) else 0) • P.compl₂ (D.Fr.c B)) +
    ((1 / 2 : ℝ) * etaL A B * lorentzSign C) • P.compl₂ (D.Fr.c C)

theorem kinP_apply (D : DiracData (MatLie m) V S) (P : S' →ₗ[ℝ] S →ₗ[ℝ] ℝ) (A B C : Fin 4)
    (φ : S') (x : S) :
    kinP D P A B C φ x = -(1 / 4 : ℝ) * ((if C = B then P φ (D.Fr.c A x) else 0) +
      (if C = A then P φ (D.Fr.c B x) else 0)) +
      (1 / 2 : ℝ) * etaL A B * lorentzSign C * P φ (D.Fr.c C x) := by
  simp only [kinP, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.compl₂_apply,
    smul_eq_mul]
  split_ifs <;> ring

/-- The Yukawa kernel `P''_{AB}(H)(φ, x) = -η_{AB}⟨φ, 𝓜(H)x⟩`. -/
def yukP (D : DiracData (MatLie m) V S) (P : S' →ₗ[ℝ] S →ₗ[ℝ] ℝ) (A B : Fin 4) (H : V) :
    S' →ₗ[ℝ] S →ₗ[ℝ] ℝ :=
  (-etaL A B) • P.compl₂ (mass D.m0 D.L H)

/-- **The symmetric Dirac stress form** (Hilbert stress of the symmetrised Dirac density). -/
def symTD (D : DiracData (MatLie m) V S) (P : S' →ₗ[ℝ] S →ₗ[ℝ] ℝ) : DiracStressForm S S' V where
  P := kinP D P
  P' A B C := -kinP D P A B C
  P'' := yukP D P

/-- The Dirac Lagrangian `L_D(X) = ½Σ_Cε_C[⟨Ψ̄, c_CX_C⟩ - ⟨X̄_C, c_CΨ⟩] - ⟨Ψ̄, 𝓜(H)Ψ⟩`. -/
def lagD (D : DiracData (MatLie m) V S) (P : S' →ₗ[ℝ] S →ₗ[ℝ] ℝ) (H : V) (ψ : S) (X : Fin 4 → S)
    (ψb : S') (Xb : Fin 4 → S') : ℝ :=
  (1 / 2 : ℝ) * ∑ C, lorentzSign C * (P ψb (D.Fr.c C (X C)) - P (Xb C) (D.Fr.c C ψ)) -
    P ψb (mass D.m0 D.L H ψ)

/-- The symmetric kinetic part `-¼[⟨Ψ̄, c_AX_B⟩ + ⟨Ψ̄, c_BX_A⟩ - ⟨X̄_B, c_AΨ⟩ - ⟨X̄_A, c_BΨ⟩]`. -/
def kinT (D : DiracData (MatLie m) V S) (P : S' →ₗ[ℝ] S →ₗ[ℝ] ℝ) (ψ : S) (X : Fin 4 → S)
    (ψb : S') (Xb : Fin 4 → S') (A B : Fin 4) : ℝ :=
  -(1 / 4 : ℝ) * (P ψb (D.Fr.c A (X B)) + P ψb (D.Fr.c B (X A)) - P (Xb B) (D.Fr.c A ψ) -
    P (Xb A) (D.Fr.c B ψ))

/-- **The frame components of the symmetric Dirac stress**: `T_{AB} = kinT_{AB} + η_{AB}L_D`. -/
theorem frame_symTD (D : DiracData (MatLie m) V S) (P : S' →ₗ[ℝ] S →ₗ[ℝ] ℝ) (H : V) (ψ : S)
    (X : Fin 4 → S) (ψb : S') (Xb : Fin 4 → S') (A B : Fin 4) :
    (symTD D P).frame H ψ X ψb Xb A B =
      kinT D P ψ X ψb Xb A B + etaL A B * lagD D P H ψ X ψb Xb := by
  unfold DiracStressForm.frame symTD kinT lagD yukP
  simp only [LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.compl₂_apply, smul_eq_mul]
  have hk : ∀ (φ : Fin 4 → S') (Z : Fin 4 → S) (ψ' : S) (ψb' : S'),
      (∑ C, kinP D P A B C ψb' (Z C)) = -(1 / 4 : ℝ) * (P ψb' (D.Fr.c A (Z B)) +
        P ψb' (D.Fr.c B (Z A))) + (1 / 2 : ℝ) * etaL A B * ∑ C, lorentzSign C *
          P ψb' (D.Fr.c C (Z C)) := by
    intro _ Z _ ψb'
    simp only [kinP_apply, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun C _ => by ring
  have hk' : ∀ (Zb : Fin 4 → S') (ψ' : S),
      (∑ C, kinP D P A B C (Zb C) ψ') = -(1 / 4 : ℝ) * (P (Zb B) (D.Fr.c A ψ') +
        P (Zb A) (D.Fr.c B ψ')) + (1 / 2 : ℝ) * etaL A B * ∑ C, lorentzSign C *
          P (Zb C) (D.Fr.c C ψ') := by
    intro Zb ψ'
    simp only [kinP_apply, Finset.sum_add_distrib, ← Finset.mul_sum]
    congr 1
    · congr 1
      congr 1
      · rw [Finset.sum_eq_single B (fun C _ hC => by simp [hC]) (by simp)]; simp
      · rw [Finset.sum_eq_single A (fun C _ hC => by simp [hC]) (by simp)]; simp
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun C _ => by ring
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, hk Xb X ψ ψb, hk' Xb ψ]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

theorem kinT_symm (D : DiracData (MatLie m) V S) (P : S' →ₗ[ℝ] S →ₗ[ℝ] ℝ) (ψ : S)
    (X : Fin 4 → S) (ψb : S') (Xb : Fin 4 → S') (A B : Fin 4) :
    kinT D P ψ X ψb Xb A B = kinT D P ψ X ψb Xb B A := by
  unfold kinT; ring

/-- The symmetric Dirac stress is symmetric. -/
theorem frame_symTD_symm (D : DiracData (MatLie m) V S) (P : S' →ₗ[ℝ] S →ₗ[ℝ] ℝ) (H : V)
    (ψ : S) (X : Fin 4 → S) (ψb : S') (Xb : Fin 4 → S') (A B : Fin 4) :
    (symTD D P).frame H ψ X ψb Xb A B = (symTD D P).frame H ψ X ψb Xb B A := by
  rw [frame_symTD, frame_symTD, kinT_symm, etaL_symm]

/-- The kinetic part is linear in the jets: its difference at two jets is the kinetic part of the
jet differences. -/
theorem kinT_sub (D : DiracData (MatLie m) V S) (P : S' →ₗ[ℝ] S →ₗ[ℝ] ℝ) (ψ : S)
    (X X' : Fin 4 → S) (ψb : S') (Xb Xb' : Fin 4 → S') (A B : Fin 4) :
    kinT D P ψ X ψb Xb A B - kinT D P ψ X' ψb Xb' A B =
      kinT D P ψ (X - X') ψb (Xb - Xb') A B := by
  unfold kinT
  simp only [Pi.sub_apply, map_sub, LinearMap.sub_apply]
  ring

/-- **The Dirac Lagrangian vanishes under both Dirac relations** `Σ_Cε_Cc_CX_C = 𝓜Ψ`,
`Σ_Cε_Cc̄_CX̄_C = 𝓜̄Ψ̄`, when the co-spinor block is the transpose of the spinor block. -/
theorem lagD_eq_zero {SM : SMData (MatLie m) V S S'} (hP : DiracPairing SM) (H : V) (ψ : S)
    (X : Fin 4 → S) (ψb : S') (Xb : Fin 4 → S')
    (hX : ∑ C, lorentzSign C • SM.D.Fr.c C (X C) = mass SM.D.m0 SM.D.L H ψ)
    (hXb : ∑ C, lorentzSign C • SM.Db.Fr.c C (Xb C) = mass SM.Db.m0 SM.Db.L H ψb) :
    lagD SM.D hP.P H ψ X ψb Xb = 0 := by
  unfold lagD
  have h1 : ∑ C, lorentzSign C * hP.P ψb (SM.D.Fr.c C (X C)) = hP.P ψb (mass SM.D.m0 SM.D.L H ψ) := by
    rw [← hX, map_sum]
    simp [map_smul, smul_eq_mul]
  have h2 : ∑ C, lorentzSign C * hP.P (Xb C) (SM.D.Fr.c C ψ) = -hP.P ψb (mass SM.D.m0 SM.D.L H ψ) := by
    have e : ∀ C, hP.P (Xb C) (SM.D.Fr.c C ψ) = hP.P (SM.Db.Fr.c C (Xb C)) ψ := fun C =>
      (hP.c_tr C (Xb C) ψ).symm
    simp only [e]
    have : ∑ C, lorentzSign C * hP.P (SM.Db.Fr.c C (Xb C)) ψ =
        hP.P (∑ C, lorentzSign C • SM.Db.Fr.c C (Xb C)) ψ := by
      simp [map_sum, map_smul, LinearMap.sum_apply, smul_eq_mul]
    rw [this, hXb]
    simp only [mass, LinearMap.add_apply, map_add, LinearMap.add_apply, hP.m0_tr, hP.L_tr]
    ring
  have e3 : ∑ C, lorentzSign C * (hP.P ψb (SM.D.Fr.c C (X C)) - hP.P (Xb C) (SM.D.Fr.c C ψ)) =
      ∑ C, lorentzSign C * hP.P ψb (SM.D.Fr.c C (X C)) -
        ∑ C, lorentzSign C * hP.P (Xb C) (SM.D.Fr.c C ψ) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun C _ => by ring
  rw [e3, h1, h2]
  ring

/-- **The difference of the symmetric Dirac stress at two pairs of spinor jets obeying the Dirac
relations is the kinetic part of the jet differences** (no trace part). -/
theorem frame_symTD_sub {SM : SMData (MatLie m) V S S'} (hP : DiracPairing SM) (H : V) (ψ : S)
    (X X' : Fin 4 → S) (ψb : S') (Xb Xb' : Fin 4 → S')
    (hX : ∑ C, lorentzSign C • SM.D.Fr.c C (X C) = mass SM.D.m0 SM.D.L H ψ)
    (hXb : ∑ C, lorentzSign C • SM.Db.Fr.c C (Xb C) = mass SM.Db.m0 SM.Db.L H ψb)
    (hX' : ∑ C, lorentzSign C • SM.D.Fr.c C (X' C) = mass SM.D.m0 SM.D.L H ψ)
    (hXb' : ∑ C, lorentzSign C • SM.Db.Fr.c C (Xb' C) = mass SM.Db.m0 SM.Db.L H ψb)
    (A B : Fin 4) :
    (symTD SM.D hP.P).frame H ψ X ψb Xb A B - (symTD SM.D hP.P).frame H ψ X' ψb Xb' A B =
      kinT SM.D hP.P ψ (X - X') ψb (Xb - Xb') A B := by
  rw [frame_symTD, frame_symTD, lagD_eq_zero hP H ψ X ψb Xb hX hXb,
    lagD_eq_zero hP H ψ X' ψb Xb' hX' hXb', ← kinT_sub]
  ring

/-! ### The coupled theory data -/

/-- **Variational Einstein–Yang–Mills–Higgs–Dirac theory data with Dirac back-reaction**: the
variational Dirac data of `GenDiracCur.VariationalDirac` (spinor pairing, Higgs moment map,
current `2μ(H, DH) + J^D`, Higgs source with the Yukawa term), a symmetric ad-invariant gauge form,
a symmetric Higgs form, and the **symmetric Dirac stress** `SM.TD = symTD` (Hilbert stress of the
Dirac density). -/
structure CoupledDirac (SM : SMData (MatLie m) V S S') extends VariationalDirac SM where
  ipG_symm : ∀ X Y : MatLie m, SM.ipG X Y = SM.ipG Y X
  ipG_inv : ∀ X Y Z : MatLie m, SM.ipG ⁅X, Y⁆ Z + SM.ipG Y ⁅X, Z⁆ = 0
  ipV_symm : ∀ u w : V, SM.ipV u w = SM.ipV w u
  TD_eq : SM.TD = symTD SM.D P

/-! ### Non-vacuity: the charged quaternionic data with the Dirac stress -/

section Quat

/-- **The charged quaternionic Einstein–Yang–Mills–Higgs–Dirac data with Dirac back-reaction**:
`GenDiracCur.quatSM` with the symmetric Dirac stress. -/
def quatSMT : SMData (MatLie 1) (MatLie 1) SQ SQ :=
  { quatSM with TD := symTD quatSM.D PQ }

/-- The back-reacting quaternionic data are variational Dirac data. -/
def quatVarT : VariationalDirac quatSMT where
  P := PQ
  c_tr := quatVariationalDirac.c_tr
  ρ_tr := quatVariationalDirac.ρ_tr
  m0_tr := quatVariationalDirac.m0_tr
  L_tr := quatVariationalDirac.L_tr
  ipG_nondeg := quatVariationalDirac.ipG_nondeg
  μS := quatVariationalDirac.μS
  μS_dual := quatVariationalDirac.μS_dual
  μS_equiv := quatVariationalDirac.μS_equiv
  μ := quatVariationalDirac.μ
  moment := quatVariationalDirac.moment
  alt := quatVariationalDirac.alt
  equiv := quatVariationalDirac.equiv
  yuk := quatVariationalDirac.yuk
  yuk_dual := quatVariationalDirac.yuk_dual
  J_eq := quatVariationalDirac.J_eq
  SH_eq := quatVariationalDirac.SH_eq

/-- **The back-reacting quaternionic data are coupled Dirac data.** -/
def quatCoupled : CoupledDirac quatSMT where
  toVariationalDirac := quatVarT
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

/-- The Dirac stress of the quaternionic data is nonzero: for `Ψ = (1, 0)` with the normal jet
`X_0 = (1, 0)`, `X_a = 0`, `X̄ = 0` and `Ψ̄ = (q₁, 0)`, `T_{01} = -¼`. -/
theorem quatSMT_stress_ne :
    quatSMT.TD.frame 0 ((1 : Quaternion ℝ), 0)
      (fun A => if A = 0 then ((1 : Quaternion ℝ), 0) else 0) (qU 0, 0) 0 0 1 = -(1 / 4 : ℝ) := by
  show (symTD quatSM.D PQ).frame _ _ _ _ _ 0 1 = _
  rw [frame_symTD]
  have h : etaL 0 1 = 0 := by simp [etaL]
  rw [h, zero_mul, add_zero]
  unfold kinT
  have e1 : quatSM.D.Fr.c 1 ((1 : Quaternion ℝ), (0 : Quaternion ℝ)) = (qU 0, 0) := by
    show diagQ 1 0 _ = _
    simp
  simp only [Fin.one_eq_zero_iff, OfNat.ofNat_ne_zero, if_false, if_true, map_zero,
    LinearMap.zero_apply, Pi.zero_apply, e1]
  have z1 : (0 : Quaternion ℝ).re = 0 := rfl
  have z2 : (0 : Quaternion ℝ).imI = 0 := rfl
  have z3 : (0 : Quaternion ℝ).imJ = 0 := rfl
  have z4 : (0 : Quaternion ℝ).imK = 0 := rfl
  simp [PQ_apply, dotQ, z1, z2, z3, z4]

end Quat

end RenewalGeometry.GenDStress
