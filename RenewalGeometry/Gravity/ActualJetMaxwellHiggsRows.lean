/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.ActualJetWriterRows

/-!
# Maxwell and Higgs blocks of the actual-jet equation (`prop:actual-jet-writer`)

Einstein–Standard-Model action-closure manuscript, `prop:actual-jet-writer`: "The Yang–Mills
equation and Bianchi identity give the symmetric Maxwell blocks for `(E,B)`.  The Higgs equation
and covariant commutator identity give symmetric wave blocks for `(Π,Q)`."  Open clauses (a), (b)
of the ledger note, as exact algebra on jets at one point in the adapted frame
(`ActualJetWriter.AdaptedFrame`), the convention of `ActualJetWriterRows`.

## Setting

A gauge potential with values in a real Lie algebra `𝔤`, jets `(A, ∂A, ∂²A)` (`∂²A` symmetric in
the two derivative slots), field strength `F_{μν} = ∂_μA_ν - ∂_νA_μ + [A_μ, A_ν]`
(`ActualJetWriter.fieldStrength`) with its derivative jet `∂_γF_{μν}` (`dFm`); an arbitrary
inverse metric `g^{μν}` to which the frame is adapted and arbitrary connection symbols `Γ`; frame
derivative jets `∂_γe_A{}^μ` (`de`, data — by `ActualJetFrame.frameJet` they are functions of
the metric 1-jet).  Frame components of a tensor `T(e_b, e_c)` (`frT`) and their coordinate
derivatives (`dfrT`, product rule); `E_a = F(e_0, e_a)`, `B_a = -½ ε_{abc} F(e_b, e_c)`.

## Main results

* `bianchi_jet` — `∂_γF_{μν} + ∂_μF_{νγ} + ∂_νF_{γμ} = -([A_γ, F_{μν}] + [A_μ, F_{νγ}] + [A_ν, F_{γμ}])`
  (Jacobi identity; second derivatives cancel by symmetry).
* **`maxwell_E_row`** — the Yang–Mills row: with the Yang–Mills residual
  `r^A_ν = g^{μρ}(∇_ρF_{μν} + [A_ρ, F_{μν}]) - J_ν`,
  `∂_tE_a - βʲ∂_jE_a - N Σ_{bc} ε_{abc} e_bʲ∂_jB_c = N(L^E_a - (J + r^A)(e_a))`.
* **`maxwell_B_row`** — the Bianchi row:
  `∂_tB_a - βʲ∂_jB_a + N Σ_{bc} ε_{abc} e_bʲ∂_jE_c = N L^B_a`.
* **`higgs_Q_row`**, **`higgs_Pi_row`** — `Π = D_{e_0}H`, `Q_a = D_{e_a}H`:
  `∂_tQ_a - βʲ∂_jQ_a - N e_aʲ∂_jΠ = N L^Q_a` (covariant commutator identity) and
  `∂_tΠ - βʲ∂_jΠ - N Σ_a e_aʲ∂_jQ_a = N(L^Π - (S_H + r_H))` (Higgs equation).
* `maxwellSym_symm`, `higgsSym_symm` — the Maxwell and Higgs principal matrices are symmetric.

The lower-order terms `L^E, L^B, L^Q, L^Π` are explicit and contain no second derivative of `A`
or `H`: only `(A, F, ∂A)`, `(H, DH)`, the frame and its first derivative jets, `g^{-1}`, `Γ`.
-/

namespace RenewalGeometry.ActualJetGauge

open Finset ActualJetWriter

noncomputable section

set_option linter.unusedSectionVars false

/-! ### The Levi-Civita symbol in three dimensions -/

/-- `ε_{abc}` on `Fin 3`. -/
def eps3 (a b c : Fin 3) : ℝ :=
  (((a : ℤ) - b) * ((b : ℤ) - c) * ((c : ℤ) - a) / 2 : ℤ)

theorem eps3_swap12 (a b c : Fin 3) : eps3 b a c = -eps3 a b c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [eps3]

theorem eps3_swap23 (a b c : Fin 3) : eps3 a c b = -eps3 a b c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [eps3]

theorem eps3_cycl (a b c : Fin 3) : eps3 b c a = eps3 a b c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [eps3]

/-- The contraction identity `Σ_c ε_{abc}ε_{cde} = δ_{ad}δ_{be} - δ_{ae}δ_{bd}`. -/
theorem eps3_contract (a b d e : Fin 3) :
    ∑ c, eps3 a b c * eps3 c d e =
      (if a = d ∧ b = e then 1 else 0) - (if a = e ∧ b = d then 1 else 0) := by
  rw [Fin.sum_univ_three]
  fin_cases a <;> fin_cases b <;> fin_cases d <;> fin_cases e <;> simp [eps3]

/-! ### Frame calculus on jets (values in a real vector space) -/

section FrameCalc

variable {M : Type*} [AddCommGroup M] [Module ℝ M]
variable (F : AdaptedFrame) (de : Fin 4 → Fin 4 → Fin 4 → ℝ)

/-- The frame derivative `e_B(X) = e_B{}^γ X_γ` of a coordinate derivative jet `X_γ = ∂_γX`. -/
def fD (X : Fin 4 → M) (B : Fin 4) : M := ∑ γ, F.fr B γ • X γ

theorem N_fD_zero (X : Fin 4 → M) : F.N • fD F X 0 = X 0 - ∑ j, F.β j • X j.succ := by
  unfold fD
  rw [Fin.sum_univ_succ, smul_add, Finset.smul_sum]
  simp only [AdaptedFrame.fr_zero_zero, AdaptedFrame.fr_zero_succ, smul_smul]
  rw [mul_inv_cancel₀ F.N_ne, one_smul, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← neg_smul]
  congr 1
  field_simp [F.N_ne]

theorem fD_succ (X : Fin 4 → M) (a : Fin 3) : fD F X a.succ = ∑ j, F.E a j • X j.succ := by
  unfold fD
  rw [Fin.sum_univ_succ]; simp

/-- Frame components `T(e_b, e_c) = e_b{}^μe_c{}^νT_{μν}`. -/
def frT (T : Fin 4 → Fin 4 → M) (b c : Fin 4) : M :=
  ∑ μ, ∑ ν, (F.fr b μ * F.fr c ν) • T μ ν

/-- Their coordinate derivative jets (product rule): `∂_γ(T(e_b, e_c))`. -/
def dfrT (T : Fin 4 → Fin 4 → M) (dT : Fin 4 → Fin 4 → Fin 4 → M) (γ b c : Fin 4) : M :=
  ∑ μ, ∑ ν, ((de γ b μ * F.fr c ν + F.fr b μ * de γ c ν) • T μ ν +
    (F.fr b μ * F.fr c ν) • dT γ μ ν)

/-- The lower-order part of `e_B(T(e_b, e_c))` (frame derivatives of the frame). -/
def lowT (T : Fin 4 → Fin 4 → M) (B b c : Fin 4) : M :=
  ∑ γ, F.fr B γ • ∑ μ, ∑ ν, (de γ b μ * F.fr c ν + F.fr b μ * de γ c ν) • T μ ν

/-- `e_B(T(e_b, e_c)) = lowT + e_b{}^μe_c{}^ν e_B(T_{μν})`. -/
theorem fD_dfrT (T : Fin 4 → Fin 4 → M) (dT : Fin 4 → Fin 4 → Fin 4 → M) (B b c : Fin 4) :
    fD F (fun γ => dfrT F de T dT γ b c) B = lowT F de T B b c +
      ∑ μ, ∑ ν, (F.fr b μ * F.fr c ν) • fD F (fun γ => dT γ μ ν) B := by
  unfold fD dfrT lowT
  simp only [Finset.sum_add_distrib, Finset.smul_sum, smul_add, smul_smul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun γ _ => ?_
  rw [mul_comm]

/-- Antisymmetric tensors have antisymmetric frame components and derivative jets. -/
theorem frT_anti {T : Fin 4 → Fin 4 → M} (hT : ∀ μ ν, T ν μ = -T μ ν) (b c : Fin 4) :
    frT F T c b = -frT F T b c := by
  unfold frT
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [hT ν μ, smul_neg, mul_comm, neg_neg]

theorem dfrT_anti {T : Fin 4 → Fin 4 → M} {dT : Fin 4 → Fin 4 → Fin 4 → M}
    (hT : ∀ μ ν, T ν μ = -T μ ν) (hdT : ∀ γ μ ν, dT γ ν μ = -dT γ μ ν) (γ b c : Fin 4) :
    dfrT F de T dT γ c b = -dfrT F de T dT γ b c := by
  unfold dfrT
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [hT ν μ, hdT γ ν μ, smul_neg, smul_neg, neg_add, neg_neg, neg_neg]
  congr 1
  · congr 1; ring
  · rw [mul_comm]

/-- The adapted inverse metric splits a double contraction into its normal and tangential
parts: `Σ_{μρ} e_0^μe_0^ρ X_{ρμ} = Σ_b Σ_{μρ} e_b^μe_b^ρ X_{ρμ} - Σ_{μρ} g^{μρ}X_{ρμ}`. -/
theorem split_adapted {gi : Fin 4 → Fin 4 → ℝ} (hadapt : F.IsAdapted gi) (X : Fin 4 → Fin 4 → M) :
    ∑ μ, ∑ ρ, (F.fr 0 μ * F.fr 0 ρ) • X ρ μ =
      ∑ b : Fin 3, ∑ μ, ∑ ρ, (F.fr b.succ μ * F.fr b.succ ρ) • X ρ μ -
        ∑ μ, ∑ ρ, gi μ ρ • X ρ μ := by
  have key : ∀ μ ρ, gi μ ρ • X ρ μ = -((F.fr 0 μ * F.fr 0 ρ) • X ρ μ) +
      ∑ b : Fin 3, (F.fr b.succ μ * F.fr b.succ ρ) • X ρ μ := by
    intro μ ρ
    rw [hadapt μ ρ, add_smul, neg_smul, Finset.sum_smul]
  simp_rw [key, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have hc : ∑ μ, ∑ ρ, ∑ b : Fin 3, (F.fr b.succ μ * F.fr b.succ ρ) • X ρ μ =
      ∑ b : Fin 3, ∑ μ, ∑ ρ, (F.fr b.succ μ * F.fr b.succ ρ) • X ρ μ := by
    calc ∑ μ, ∑ ρ, ∑ b : Fin 3, (F.fr b.succ μ * F.fr b.succ ρ) • X ρ μ
        = ∑ μ, ∑ b : Fin 3, ∑ ρ, (F.fr b.succ μ * F.fr b.succ ρ) • X ρ μ :=
          Finset.sum_congr rfl fun μ _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hc]
  abel

end FrameCalc

/-! ### The dual vector of an antisymmetric family -/

section Dual

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

/-- The dual vector `m_a = -½ ε_{abc} S_{bc}` of an antisymmetric family. -/
def dualVec (S : Fin 3 → Fin 3 → M) (a : Fin 3) : M :=
  -(1 / 2 : ℝ) • ∑ b, ∑ c, eps3 a b c • S b c

/-- **`S_{ba} = -ε_{bac} m_c`** for antisymmetric `S` and its dual vector `m`. -/
theorem anti_eq_eps_dual {S : Fin 3 → Fin 3 → M} (hS : ∀ b c, S c b = -S b c) (b a : Fin 3) :
    S b a = -∑ c, eps3 b a c • dualVec S c := by
  unfold dualVec
  have h1 : ∑ c, eps3 b a c • (-(1 / 2 : ℝ) • ∑ d, ∑ e, eps3 c d e • S d e) =
      -(1 / 2 : ℝ) • ∑ d, ∑ e, (∑ c, eps3 b a c * eps3 c d e) • S d e := by
    simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun c _ => ?_
    congr 1; ring
  rw [h1]
  simp only [eps3_contract]
  have h2 : ∑ d, ∑ e, (((if b = d ∧ a = e then 1 else 0) - (if b = e ∧ a = d then 1 else 0) : ℝ) •
      S d e) = S b a - S a b := by
    simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul]
    congr 1
    · rw [Finset.sum_eq_single b]
      · rw [Finset.sum_eq_single a]
        · simp
        · intro e _ he; simp [Ne.symm he]
        · simp
      · intro d _ hd
        refine Finset.sum_eq_zero fun e _ => ?_
        simp [Ne.symm hd]
      · simp
    · rw [Finset.sum_eq_single a]
      · rw [Finset.sum_eq_single b]
        · simp
        · intro e _ he; simp [Ne.symm he]
        · simp
      · intro d _ hd
        refine Finset.sum_eq_zero fun e _ => ?_
        simp [Ne.symm hd]
      · simp
  rw [h2, hS a b]
  module

end Dual

/-! ### The Maxwell block -/

section Maxwell

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
variable (F : AdaptedFrame) (de : Fin 4 → Fin 4 → Fin 4 → ℝ)
variable (A : Fin 4 → 𝔤) (dA : Fin 4 → Fin 4 → 𝔤) (ddA : Fin 4 → Fin 4 → Fin 4 → 𝔤)

/-- The coordinate field strength `F_{μν}`. -/
def Fm (μ ν : Fin 4) : 𝔤 := fieldStrength A dA μ ν

/-- Its derivative jet `∂_γF_{μν}`. -/
def dFm (γ μ ν : Fin 4) : 𝔤 := ddA γ μ ν - ddA γ ν μ + ⁅dA γ μ, A ν⁆ + ⁅A μ, dA γ ν⁆

theorem Fm_anti (μ ν : Fin 4) : Fm A dA ν μ = -Fm A dA μ ν := by
  unfold Fm fieldStrength
  rw [← lie_skew (A μ) (A ν)]
  abel

theorem dFm_anti (γ μ ν : Fin 4) : dFm A dA ddA γ ν μ = -dFm A dA ddA γ μ ν := by
  unfold dFm
  rw [← lie_skew (dA γ ν) (A μ), ← lie_skew (A ν) (dA γ μ)]
  abel

/-- The electric field `E_a = F(e_0, e_a)`. -/
def elec (a : Fin 3) : 𝔤 := frT F (Fm A dA) 0 a.succ

/-- Its derivative jet `∂_γE_a`. -/
def delec (γ : Fin 4) (a : Fin 3) : 𝔤 := dfrT F de (Fm A dA) (dFm A dA ddA) γ 0 a.succ

/-- The spatial frame components `F(e_b, e_c)`. -/
def Fsp (b c : Fin 3) : 𝔤 := frT F (Fm A dA) b.succ c.succ

/-- Their derivative jets. -/
def dFsp (γ : Fin 4) (b c : Fin 3) : 𝔤 := dfrT F de (Fm A dA) (dFm A dA ddA) γ b.succ c.succ

/-- The magnetic field `B_a = -½ ε_{abc} F(e_b, e_c)`. -/
def magn (a : Fin 3) : 𝔤 := dualVec (Fsp F A dA) a

/-- Its derivative jet `∂_γB_a`. -/
def dmagn (γ : Fin 4) (a : Fin 3) : 𝔤 := dualVec (dFsp F de A dA ddA γ) a

theorem Fsp_anti (b c : Fin 3) : Fsp F A dA c b = -Fsp F A dA b c :=
  frT_anti F (Fm_anti A dA) _ _

theorem dFsp_anti (γ : Fin 4) (b c : Fin 3) : dFsp F de A dA ddA γ c b = -dFsp F de A dA ddA γ b c :=
  dfrT_anti F de (Fm_anti A dA) (dFm_anti A dA ddA) _ _ _

/-- The Yang–Mills divergence `g^{μρ}(∇_ρF_{μν} + [A_ρ, F_{μν}])` with connection symbols `Γ`. -/
def ymDiv (gi : Fin 4 → Fin 4 → ℝ) (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) (ν : Fin 4) : 𝔤 :=
  ∑ μ, ∑ ρ, gi μ ρ • (dFm A dA ddA ρ μ ν -
    ∑ l, (Γ l ρ μ • Fm A dA l ν + Γ l ρ ν • Fm A dA μ l) + ⁅A ρ, Fm A dA μ ν⁆)

/-- The lower-order part of the Yang–Mills divergence. -/
def ymCorr (gi : Fin 4 → Fin 4 → ℝ) (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) (ν : Fin 4) : 𝔤 :=
  ∑ μ, ∑ ρ, gi μ ρ • (∑ l, (Γ l ρ μ • Fm A dA l ν + Γ l ρ ν • Fm A dA μ l) - ⁅A ρ, Fm A dA μ ν⁆)

/-- The Yang–Mills residual `r^A_ν = g^{μρ}(∇_ρF_{μν} + [A_ρ, F_{μν}]) - J_ν`. -/
def ymRes (gi : Fin 4 → Fin 4 → ℝ) (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) (J : Fin 4 → 𝔤)
    (ν : Fin 4) : 𝔤 :=
  ymDiv A dA ddA gi Γ ν - J ν

theorem sum_gi_dFm (gi : Fin 4 → Fin 4 → ℝ) (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) (ν : Fin 4) :
    ∑ μ, ∑ ρ, gi μ ρ • dFm A dA ddA ρ μ ν = ymDiv A dA ddA gi Γ ν + ymCorr A dA gi Γ ν := by
  unfold ymDiv ymCorr
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [← smul_add]
  congr 1
  abel

/-- The lower-order term of the `E`-row. -/
def LE (gi : Fin 4 → Fin 4 → ℝ) (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) (a : Fin 3) : 𝔤 :=
  lowT F de (Fm A dA) 0 0 a.succ - ∑ b : Fin 3, lowT F de (Fm A dA) b.succ b.succ a.succ -
    ∑ ν, F.fr a.succ ν • ymCorr A dA gi Γ ν

/-- **The Yang–Mills (`E`) row in the frame**:
`e_0(E_a) - ε_{abc} e_b(B_c) = L^E_a - (J + r^A)(e_a)`. -/
theorem maxwell_E_frame (gi : Fin 4 → Fin 4 → ℝ) (hadapt : F.IsAdapted gi)
    (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) (J : Fin 4 → 𝔤) (a : Fin 3) :
    fD F (fun γ => delec F de A dA ddA γ a) 0 -
        ∑ b, ∑ c, eps3 a b c • fD F (fun γ => dmagn F de A dA ddA γ c) b.succ =
      LE F de A dA gi Γ a - ∑ ν, F.fr a.succ ν • (J ν + ymRes A dA ddA gi Γ J ν) := by
  -- step 1: the normal derivative of `E`
  have h1 := fD_dfrT F de (Fm A dA) (dFm A dA ddA) 0 0 a.succ
  -- step 2: the adapted split for each `ν`
  have h2 : ∑ μ, ∑ ν, (F.fr 0 μ * F.fr a.succ ν) • fD F (fun γ => dFm A dA ddA γ μ ν) 0 =
      ∑ ν, F.fr a.succ ν • (∑ b : Fin 3, ∑ μ, ∑ ρ, (F.fr b.succ μ * F.fr b.succ ρ) •
        dFm A dA ddA ρ μ ν - ∑ μ, ∑ ρ, gi μ ρ • dFm A dA ddA ρ μ ν) := by
    have hs : ∀ ν, ∑ μ, ∑ ρ, (F.fr 0 μ * F.fr 0 ρ) • dFm A dA ddA ρ μ ν =
        ∑ b : Fin 3, ∑ μ, ∑ ρ, (F.fr b.succ μ * F.fr b.succ ρ) • dFm A dA ddA ρ μ ν -
          ∑ μ, ∑ ρ, gi μ ρ • dFm A dA ddA ρ μ ν := fun ν =>
      split_adapted F hadapt (fun ρ μ => dFm A dA ddA ρ μ ν)
    simp_rw [← hs]
    unfold fD
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => ?_
    simp only [Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ρ _ => ?_
    congr 1; ring
  -- step 3: the tangential terms are the frame derivatives of the spatial components
  have h3 : ∀ b : Fin 3, ∑ ν, F.fr a.succ ν • ∑ μ, ∑ ρ, (F.fr b.succ μ * F.fr b.succ ρ) •
      dFm A dA ddA ρ μ ν = fD F (fun γ => dFsp F de A dA ddA γ b a) b.succ -
        lowT F de (Fm A dA) b.succ b.succ a.succ := by
    intro b
    have := fD_dfrT F de (Fm A dA) (dFm A dA ddA) b.succ b.succ a.succ
    unfold dFsp
    rw [this, add_sub_cancel_left]
    unfold fD
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => ?_
    simp only [Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ρ _ => ?_
    congr 1; ring
  -- step 4: the spatial components through the dual vector `∂B`
  have h4 : ∀ b : Fin 3, fD F (fun γ => dFsp F de A dA ddA γ b a) b.succ =
      -∑ c, eps3 b a c • fD F (fun γ => dmagn F de A dA ddA γ c) b.succ := by
    intro b
    have he : ∀ γ, dFsp F de A dA ddA γ b a = -∑ c, eps3 b a c • dmagn F de A dA ddA γ c :=
      fun γ => anti_eq_eps_dual (dFsp_anti F de A dA ddA γ) b a
    unfold fD
    simp_rw [he]
    simp only [smul_neg, Finset.sum_neg_distrib, Finset.smul_sum, smul_smul]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun γ _ => ?_
    congr 1; ring
  have h5 : ∑ b : Fin 3, ∑ c, eps3 a b c • fD F (fun γ => dmagn F de A dA ddA γ c) b.succ =
      ∑ b : Fin 3, fD F (fun γ => dFsp F de A dA ddA γ b a) b.succ := by
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [h4 b, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [eps3_swap12, neg_smul]
  -- assemble
  unfold delec
  rw [h1, h2, h5]
  have h6 : ∀ ν, ∑ μ, ∑ ρ, gi μ ρ • dFm A dA ddA ρ μ ν =
      J ν + ymRes A dA ddA gi Γ J ν + ymCorr A dA gi Γ ν := by
    intro ν
    rw [sum_gi_dFm A dA ddA gi Γ ν]
    unfold ymRes
    abel
  have h7 : ∑ ν, F.fr a.succ ν • ∑ b : Fin 3, ∑ μ, ∑ ρ, (F.fr b.succ μ * F.fr b.succ ρ) •
      dFm A dA ddA ρ μ ν = ∑ b : Fin 3, (fD F (fun γ => dFsp F de A dA ddA γ b a) b.succ -
        lowT F de (Fm A dA) b.succ b.succ a.succ) := by
    simp only [Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← h3 b]
    simp only [Finset.smul_sum]
  have h8 : ∑ ν, F.fr a.succ ν • (∑ b : Fin 3, ∑ μ, ∑ ρ, (F.fr b.succ μ * F.fr b.succ ρ) •
      dFm A dA ddA ρ μ ν - ∑ μ, ∑ ρ, gi μ ρ • dFm A dA ddA ρ μ ν) =
      ∑ b : Fin 3, (fD F (fun γ => dFsp F de A dA ddA γ b a) b.succ -
        lowT F de (Fm A dA) b.succ b.succ a.succ) -
      ∑ ν, F.fr a.succ ν • (J ν + ymRes A dA ddA gi Γ J ν + ymCorr A dA gi Γ ν) := by
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [h7]
    simp only [h6, Finset.sum_sub_distrib]
  rw [h8]
  unfold LE
  simp only [smul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  abel

end Maxwell

/-! ### The Bianchi (`B`) row and the coordinate forms -/

section MaxwellB

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
variable (F : AdaptedFrame) (de : Fin 4 → Fin 4 → Fin 4 → ℝ)
variable (A : Fin 4 → 𝔤) (dA : Fin 4 → Fin 4 → 𝔤) (ddA : Fin 4 → Fin 4 → Fin 4 → 𝔤)

/-- The bracket term of the Bianchi identity. -/
def brB (γ μ ν : Fin 4) : 𝔤 := ⁅A γ, Fm A dA μ ν⁆ + ⁅A μ, Fm A dA ν γ⁆ + ⁅A ν, Fm A dA γ μ⁆

/-- **The Bianchi identity on jets**: `∂_γF_{μν} + ∂_μF_{νγ} + ∂_νF_{γμ} = -brB` (second
derivatives cancel by Schwarz symmetry, the triple brackets by the Jacobi identity). -/
theorem bianchi_jet (hs : ∀ α β μ, ddA α β μ = ddA β α μ) (γ μ ν : Fin 4) :
    dFm A dA ddA γ μ ν + dFm A dA ddA μ ν γ + dFm A dA ddA ν γ μ = -brB A dA γ μ ν := by
  have hj := lie_jacobi (A γ) (A μ) (A ν)
  have key : dFm A dA ddA γ μ ν + dFm A dA ddA μ ν γ + dFm A dA ddA ν γ μ + brB A dA γ μ ν =
      ⁅A γ, ⁅A μ, A ν⁆⁆ + ⁅A μ, ⁅A ν, A γ⁆⁆ + ⁅A ν, ⁅A γ, A μ⁆⁆ := by
    unfold dFm brB Fm fieldStrength
    rw [hs μ γ ν, hs ν γ μ, hs ν μ γ]
    rw [← lie_skew (dA γ μ) (A ν), ← lie_skew (dA μ ν) (A γ), ← lie_skew (dA ν γ) (A μ)]
    simp only [lie_add, lie_sub]
    abel
  rw [hj] at key
  exact eq_neg_of_add_eq_zero_left key

/-- The bracket contraction `brB(e_0, e_b, e_c)`. -/
def brC (b c : Fin 4) : 𝔤 :=
  ∑ μ, ∑ ν, ∑ γ, (F.fr b μ * F.fr c ν * F.fr 0 γ) • brB A dA γ μ ν

/-- The lower-order term of the `B`-row. -/
def LB (a : Fin 3) : 𝔤 :=
  -(1 / 2 : ℝ) • ∑ b, ∑ c, eps3 a b c • (lowT F de (Fm A dA) 0 b.succ c.succ +
    lowT F de (Fm A dA) b.succ c.succ 0 + lowT F de (Fm A dA) c.succ 0 b.succ -
      brC F A dA b.succ c.succ)

end MaxwellB

section MaxwellBRow

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
variable (F : AdaptedFrame) (de : Fin 4 → Fin 4 → Fin 4 → ℝ)
variable (A : Fin 4 → 𝔤) (dA : Fin 4 → Fin 4 → 𝔤) (ddA : Fin 4 → Fin 4 → Fin 4 → 𝔤)

theorem fD_smul_sum {M : Type*} [AddCommGroup M] [Module ℝ M] {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (X : ι → Fin 4 → M) (B : Fin 4) :
    fD F (fun γ => ∑ i, c i • X i γ) B = ∑ i, c i • fD F (X i) B := by
  unfold fD
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun γ _ => ?_
  rw [mul_comm]

theorem fD_smul {M : Type*} [AddCommGroup M] [Module ℝ M] (c : ℝ) (X : Fin 4 → M) (B : Fin 4) :
    fD F (fun γ => c • X γ) B = c • fD F X B := by
  unfold fD
  simp only [Finset.smul_sum, smul_smul]
  exact Finset.sum_congr rfl fun γ _ => by rw [mul_comm]

theorem fD_sum2_smul {M : Type*} [AddCommGroup M] [Module ℝ M] (c : Fin 3 → Fin 3 → ℝ)
    (X : Fin 3 → Fin 3 → Fin 4 → M) (B : Fin 4) :
    fD F (fun γ => ∑ i, ∑ j, c i j • X i j γ) B = ∑ i, ∑ j, c i j • fD F (X i j) B := by
  unfold fD
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun γ _ => ?_
  rw [mul_comm]

theorem sum3_cycle {M : Type*} [AddCommMonoid M] (f : Fin 4 → Fin 4 → Fin 4 → M) :
    ∑ μ, ∑ ν, ∑ γ, f μ ν γ = ∑ ν, ∑ γ, ∑ μ, f μ ν γ := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  exact Finset.sum_comm

theorem sum3_cycle' {M : Type*} [AddCommMonoid M] (f : Fin 4 → Fin 4 → Fin 4 → M) :
    ∑ μ, ∑ ν, ∑ γ, f μ ν γ = ∑ γ, ∑ μ, ∑ ν, f μ ν γ := by
  rw [sum3_cycle, sum3_cycle]

/-- The normal frame derivative of the spatial components `F(e_b, e_c)`, by the Bianchi
identity. -/
theorem fD_dFsp_zero (hs : ∀ α β μ, ddA α β μ = ddA β α μ) (b c : Fin 3) :
    fD F (fun γ => dFsp F de A dA ddA γ b c) 0 =
      lowT F de (Fm A dA) 0 b.succ c.succ + fD F (fun γ => delec F de A dA ddA γ c) b.succ +
        lowT F de (Fm A dA) b.succ c.succ 0 - fD F (fun γ => delec F de A dA ddA γ b) c.succ +
        lowT F de (Fm A dA) c.succ 0 b.succ - brC F A dA b.succ c.succ := by
  have h1 := fD_dfrT F de (Fm A dA) (dFm A dA ddA) 0 b.succ c.succ
  have h3 := fD_dfrT F de (Fm A dA) (dFm A dA ddA) b.succ c.succ 0
  have h4 := fD_dfrT F de (Fm A dA) (dFm A dA ddA) c.succ 0 b.succ
  -- the Bianchi identity, contracted
  have hbi : ∀ γ μ ν, dFm A dA ddA γ μ ν =
      -dFm A dA ddA μ ν γ - dFm A dA ddA ν γ μ - brB A dA γ μ ν := by
    intro γ μ ν
    have := bianchi_jet A dA ddA hs γ μ ν
    calc dFm A dA ddA γ μ ν = (dFm A dA ddA γ μ ν + dFm A dA ddA μ ν γ + dFm A dA ddA ν γ μ) -
          dFm A dA ddA μ ν γ - dFm A dA ddA ν γ μ := by abel
      _ = -brB A dA γ μ ν - dFm A dA ddA μ ν γ - dFm A dA ddA ν γ μ := by rw [this]
      _ = _ := by abel
  have hB : ∑ μ, ∑ ν, (F.fr b.succ μ * F.fr c.succ ν) •
      fD F (fun γ => dFm A dA ddA γ μ ν) 0 =
      -(∑ μ, ∑ ν, ∑ γ, (F.fr b.succ μ * F.fr c.succ ν * F.fr 0 γ) • dFm A dA ddA μ ν γ) -
        ∑ μ, ∑ ν, ∑ γ, (F.fr b.succ μ * F.fr c.succ ν * F.fr 0 γ) • dFm A dA ddA ν γ μ -
          brC F A dA b.succ c.succ := by
    have e : ∑ μ, ∑ ν, (F.fr b.succ μ * F.fr c.succ ν) • fD F (fun γ => dFm A dA ddA γ μ ν) 0 =
        ∑ μ, ∑ ν, ∑ γ, (F.fr b.succ μ * F.fr c.succ ν * F.fr 0 γ) •
          (-dFm A dA ddA μ ν γ - dFm A dA ddA ν γ μ - brB A dA γ μ ν) := by
      unfold fD
      refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun γ _ => ?_
      rw [smul_smul]
      show _ • dFm A dA ddA γ μ ν = _
      rw [hbi γ μ ν]
    rw [e]
    unfold brC
    simp only [smul_sub, smul_neg, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  -- the three contracted derivative terms as frame derivatives of frame components
  have e3 : ∑ μ, ∑ ν, ∑ γ, (F.fr b.succ μ * F.fr c.succ ν * F.fr 0 γ) • dFm A dA ddA μ ν γ =
      fD F (fun γ => dfrT F de (Fm A dA) (dFm A dA ddA) γ c.succ 0) b.succ -
        lowT F de (Fm A dA) b.succ c.succ 0 := by
    rw [h3, add_sub_cancel_left, sum3_cycle]
    unfold fD
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun γ _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [smul_smul]; congr 1; ring
  have e4 : ∑ μ, ∑ ν, ∑ γ, (F.fr b.succ μ * F.fr c.succ ν * F.fr 0 γ) • dFm A dA ddA ν γ μ =
      fD F (fun γ => dfrT F de (Fm A dA) (dFm A dA ddA) γ 0 b.succ) c.succ -
        lowT F de (Fm A dA) c.succ 0 b.succ := by
    rw [h4, add_sub_cancel_left, sum3_cycle']
    unfold fD
    refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [smul_smul]; congr 1; ring
  have e5 : (fun γ => dfrT F de (Fm A dA) (dFm A dA ddA) γ c.succ 0) =
      fun γ => -delec F de A dA ddA γ c := by
    funext γ
    exact dfrT_anti F de (Fm_anti A dA) (dFm_anti A dA ddA) γ 0 c.succ
  have hneg : fD F (fun γ => -delec F de A dA ddA γ c) b.succ =
      -fD F (fun γ => delec F de A dA ddA γ c) b.succ := by
    have := fD_smul F (-1 : ℝ) (fun γ => delec F de A dA ddA γ c) b.succ
    simpa [neg_one_smul] using this
  unfold dFsp
  rw [h1, hB, e3, e4, e5, hneg]
  unfold delec
  abel

/-- **The Bianchi (`B`) row in the frame**: `e_0(B_a) + ε_{abc} e_b(E_c) = L^B_a`. -/
theorem maxwell_B_frame (hs : ∀ α β μ, ddA α β μ = ddA β α μ) (a : Fin 3) :
    fD F (fun γ => dmagn F de A dA ddA γ a) 0 +
        ∑ b, ∑ c, eps3 a b c • fD F (fun γ => delec F de A dA ddA γ c) b.succ =
      LB F de A dA a := by
  have h6 : fD F (fun γ => dmagn F de A dA ddA γ a) 0 =
      -(1 / 2 : ℝ) • ∑ b, ∑ c, eps3 a b c • fD F (fun γ => dFsp F de A dA ddA γ b c) 0 := by
    unfold dmagn dualVec
    rw [fD_smul]
    congr 1
    exact fD_sum2_smul F (fun b c => eps3 a b c) (fun b c γ => dFsp F de A dA ddA γ b c) 0
  rw [h6]
  simp_rw [fD_dFsp_zero F de A dA ddA hs]
  -- the antisymmetric part
  have hswap : ∑ b, ∑ c, eps3 a b c • fD F (fun γ => delec F de A dA ddA γ b) c.succ =
      -∑ b, ∑ c, eps3 a b c • fD F (fun γ => delec F de A dA ddA γ c) b.succ := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [eps3_swap23, neg_smul]
  unfold LB
  simp only [smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hswap]
  simp only [smul_add, smul_sub, smul_neg]
  module

end MaxwellBRow

/-! ### Coordinate forms of the Maxwell rows and their principal matrices -/

section MaxwellCoord

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
variable (F : AdaptedFrame) (de : Fin 4 → Fin 4 → Fin 4 → ℝ)
variable (A : Fin 4 → 𝔤) (dA : Fin 4 → Fin 4 → 𝔤) (ddA : Fin 4 → Fin 4 → Fin 4 → 𝔤)

/-- **The Yang–Mills row of the actual-jet equation** (`E`-block, coordinates on the adapted
chart): `∂_tE_a - βʲ∂_jE_a - N Σ_{bc} ε_{abc} e_bʲ∂_jB_c = N(L^E_a - (J + r^A)(e_a))`. -/
theorem maxwell_E_row (gi : Fin 4 → Fin 4 → ℝ) (hadapt : F.IsAdapted gi)
    (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) (J : Fin 4 → 𝔤) (a : Fin 3) :
    delec F de A dA ddA 0 a - ∑ j, F.β j • delec F de A dA ddA j.succ a -
        F.N • ∑ b, ∑ c, eps3 a b c • ∑ j, F.E b j • dmagn F de A dA ddA j.succ c =
      F.N • (LE F de A dA gi Γ a - ∑ ν, F.fr a.succ ν • (J ν + ymRes A dA ddA gi Γ J ν)) := by
  rw [← maxwell_E_frame F de A dA ddA gi hadapt Γ J a, smul_sub, N_fD_zero]
  simp only [fD_succ]

/-- **The Bianchi row of the actual-jet equation** (`B`-block, coordinates):
`∂_tB_a - βʲ∂_jB_a + N Σ_{bc} ε_{abc} e_bʲ∂_jE_c = N L^B_a`. -/
theorem maxwell_B_row (hs : ∀ α β μ, ddA α β μ = ddA β α μ) (a : Fin 3) :
    dmagn F de A dA ddA 0 a - ∑ j, F.β j • dmagn F de A dA ddA j.succ a +
        F.N • ∑ b, ∑ c, eps3 a b c • ∑ j, F.E b j • delec F de A dA ddA j.succ c =
      F.N • LB F de A dA a := by
  rw [← maxwell_B_frame F de A dA ddA hs a, smul_add, N_fD_zero]
  simp only [fD_succ]

/-- The principal matrix `A^j` of the Maxwell block on `(E_1, E_2, E_3, B_1, B_2, B_3)`
(`inl a = E_a`, `inr a = B_a`): `A^j_{EE} = A^j_{BB} = -βʲ`,
`A^j_{E_aB_c} = -N Σ_b ε_{abc} e_bʲ`, `A^j_{B_cE_a} = N Σ_b ε_{cba} e_bʲ`. -/
def maxwellSym (j : Fin 3) : Fin 3 ⊕ Fin 3 → Fin 3 ⊕ Fin 3 → ℝ
  | Sum.inl a, Sum.inl c => if a = c then -F.β j else 0
  | Sum.inl a, Sum.inr c => -(F.N * ∑ b, eps3 a b c * F.E b j)
  | Sum.inr a, Sum.inl c => F.N * ∑ b, eps3 a b c * F.E b j
  | Sum.inr a, Sum.inr c => if a = c then -F.β j else 0

theorem eps3_swap13 (a b c : Fin 3) : eps3 c b a = -eps3 a b c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [eps3]

/-- **The Maxwell principal matrices are symmetric.** -/
theorem maxwellSym_symm (j : Fin 3) (r s : Fin 3 ⊕ Fin 3) :
    maxwellSym F j r s = maxwellSym F j s r := by
  rcases r with a | a <;> rcases s with c | c <;> simp only [maxwellSym]
  · by_cases h : a = c
    · subst h; rfl
    · simp [h, Ne.symm h]
  · simp_rw [eps3_swap13 a _ c]
    simp only [neg_mul, Finset.sum_neg_distrib, mul_neg]
  · simp_rw [eps3_swap13 c _ a]
    simp only [neg_mul, Finset.sum_neg_distrib, mul_neg, neg_neg]
  · by_cases h : a = c
    · subst h; rfl
    · simp [h, Ne.symm h]

end MaxwellCoord

/-! ### The Higgs block -/

section Higgs

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [LieRingModule 𝔤 V] [LieModule ℝ 𝔤 V]
variable (F : AdaptedFrame) (de : Fin 4 → Fin 4 → Fin 4 → ℝ)
variable (A : Fin 4 → 𝔤) (dA : Fin 4 → Fin 4 → 𝔤)
variable (H : V) (dH : Fin 4 → V) (ddH : Fin 4 → Fin 4 → V)

/-- The covariant derivative `D_μH = ∂_μH + ρ(A_μ)H`. -/
def DH (μ : Fin 4) : V := dH μ + ⁅A μ, H⁆

/-- Its derivative jet `∂_γD_μH`. -/
def dDH (γ μ : Fin 4) : V := ddH γ μ + ⁅dA γ μ, H⁆ + ⁅A μ, dH γ⁆

/-- Frame components `D_{e_B}H` (`Π = D_{e_0}H`, `Q_a = D_{e_a}H`). -/
def frV (B : Fin 4) : V := ∑ μ, F.fr B μ • DH A H dH μ

/-- Their derivative jets. -/
def dfrV (γ B : Fin 4) : V := ∑ μ, (de γ B μ • DH A H dH μ + F.fr B μ • dDH A dA H dH ddH γ μ)

/-- The lower-order part of `e_C(D_{e_B}H)`. -/
def lowV (C B : Fin 4) : V := ∑ γ, F.fr C γ • ∑ μ, de γ B μ • DH A H dH μ

theorem fD_dfrV (C B : Fin 4) :
    fD F (fun γ => dfrV F de A dA H dH ddH γ B) C = lowV F de A H dH C B +
      ∑ μ, F.fr B μ • fD F (fun γ => dDH A dA H dH ddH γ μ) C := by
  unfold fD dfrV lowV
  simp only [Finset.smul_sum, smul_add, Finset.sum_add_distrib, smul_smul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun γ _ => ?_
  rw [mul_comm]

/-- **The covariant commutator identity on jets**:
`∂_γD_μH - ∂_μD_γH = F_{γμ}·H + A_μ·D_γH - A_γ·D_μH`. -/
theorem covariant_commutator (hs : ∀ α β, ddH α β = ddH β α) (γ μ : Fin 4) :
    dDH A dA H dH ddH γ μ - dDH A dA H dH ddH μ γ =
      ⁅Fm A dA γ μ, H⁆ + ⁅A μ, DH A H dH γ⁆ - ⁅A γ, DH A H dH μ⁆ := by
  unfold dDH DH Fm fieldStrength
  rw [hs μ γ]
  simp only [lie_add, add_lie, sub_lie, lie_lie]
  abel

/-- The lower-order term of the `Q`-row. -/
def LQ (a : Fin 3) : V :=
  lowV F de A H dH 0 a.succ - lowV F de A H dH a.succ 0 +
    ∑ γ, ∑ μ, (F.fr 0 γ * F.fr a.succ μ) •
      (⁅Fm A dA γ μ, H⁆ + ⁅A μ, DH A H dH γ⁆ - ⁅A γ, DH A H dH μ⁆)

/-- **The Higgs `Q`-row in the frame**: `e_0(Q_a) - e_a(Π) = L^Q_a`. -/
theorem higgs_Q_frame (hs : ∀ α β, ddH α β = ddH β α) (a : Fin 3) :
    fD F (fun γ => dfrV F de A dA H dH ddH γ a.succ) 0 -
        fD F (fun γ => dfrV F de A dA H dH ddH γ 0) a.succ = LQ F de A dA H dH a := by
  rw [fD_dfrV, fD_dfrV]
  unfold LQ fD
  have e : ∑ μ, F.fr a.succ μ • ∑ γ, F.fr 0 γ • dDH A dA H dH ddH γ μ -
      ∑ μ, F.fr 0 μ • ∑ γ, F.fr a.succ γ • dDH A dA H dH ddH γ μ =
      ∑ γ, ∑ μ, (F.fr 0 γ * F.fr a.succ μ) •
        (dDH A dA H dH ddH γ μ - dDH A dA H dH ddH μ γ) := by
    simp only [Finset.smul_sum, smul_smul, smul_sub, Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun μ _ => ?_
      rw [mul_comm]
  simp_rw [covariant_commutator A dA H dH ddH hs] at e
  rw [← e]
  abel

/-- The lower-order part of the covariant wave operator. -/
def corrH (gi : Fin 4 → Fin 4 → ℝ) (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) : V :=
  ∑ μ, ∑ ρ, gi μ ρ • (∑ l, Γ l ρ μ • DH A H dH l - ⁅A ρ, DH A H dH μ⁆)

/-- The covariant wave operator `□_A H = g^{μρ}(∇_ρD_μH + A_ρ·D_μH)` with connection symbols `Γ`. -/
def waveH (gi : Fin 4 → Fin 4 → ℝ) (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) : V :=
  ∑ μ, ∑ ρ, gi μ ρ • (dDH A dA H dH ddH ρ μ - ∑ l, Γ l ρ μ • DH A H dH l + ⁅A ρ, DH A H dH μ⁆)

/-- The Higgs residual `r_H = □_A H - S_H` for a source `S_H` (potential and Yukawa terms). -/
def higgsRes (gi : Fin 4 → Fin 4 → ℝ) (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) (SH : V) : V :=
  waveH A dA H dH ddH gi Γ - SH

/-- The lower-order term of the `Π`-row. -/
def LPi (gi : Fin 4 → Fin 4 → ℝ) (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) : V :=
  lowV F de A H dH 0 0 - ∑ b : Fin 3, lowV F de A H dH b.succ b.succ - corrH A H dH gi Γ

/-- **The Higgs `Π`-row in the frame**: `e_0(Π) - Σ_a e_a(Q_a) = L^Π - (S_H + r_H)`. -/
theorem higgs_Pi_frame (gi : Fin 4 → Fin 4 → ℝ) (hadapt : F.IsAdapted gi)
    (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) (SH : V) :
    fD F (fun γ => dfrV F de A dA H dH ddH γ 0) 0 -
        ∑ b : Fin 3, fD F (fun γ => dfrV F de A dA H dH ddH γ b.succ) b.succ =
      LPi F de A H dH gi Γ - (SH + higgsRes A dA H dH ddH gi Γ SH) := by
  have hs := split_adapted F hadapt (fun ρ μ => dDH A dA H dH ddH ρ μ)
  have hw : ∑ μ, ∑ ρ, gi μ ρ • dDH A dA H dH ddH ρ μ =
      SH + higgsRes A dA H dH ddH gi Γ SH + corrH A H dH gi Γ := by
    unfold higgsRes waveH corrH
    simp only [smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    abel
  rw [fD_dfrV]
  simp only [fD_dfrV, Finset.sum_add_distrib]
  have e0 : ∑ μ, F.fr 0 μ • fD F (fun γ => dDH A dA H dH ddH γ μ) 0 =
      ∑ μ, ∑ ρ, (F.fr 0 μ * F.fr 0 ρ) • dDH A dA H dH ddH ρ μ := by
    unfold fD
    simp only [Finset.smul_sum, smul_smul]
  have eb : ∀ b : Fin 3, ∑ μ, F.fr b.succ μ • fD F (fun γ => dDH A dA H dH ddH γ μ) b.succ =
      ∑ μ, ∑ ρ, (F.fr b.succ μ * F.fr b.succ ρ) • dDH A dA H dH ddH ρ μ := by
    intro b
    unfold fD
    simp only [Finset.smul_sum, smul_smul]
  rw [e0, hs, hw]
  simp only [eb]
  unfold LPi
  abel

/-- **The Higgs `Q`-row** (coordinates): `∂_tQ_a - βʲ∂_jQ_a - N e_aʲ∂_jΠ = N L^Q_a`. -/
theorem higgs_Q_row (hs : ∀ α β, ddH α β = ddH β α) (a : Fin 3) :
    dfrV F de A dA H dH ddH 0 a.succ - ∑ j, F.β j • dfrV F de A dA H dH ddH j.succ a.succ -
        F.N • ∑ j, F.E a j • dfrV F de A dA H dH ddH j.succ 0 =
      F.N • LQ F de A dA H dH a := by
  rw [← higgs_Q_frame F de A dA H dH ddH hs a, smul_sub, N_fD_zero, fD_succ]

/-- **The Higgs `Π`-row** (coordinates):
`∂_tΠ - βʲ∂_jΠ - N Σ_a e_aʲ∂_jQ_a = N(L^Π - (S_H + r_H))`. -/
theorem higgs_Pi_row (gi : Fin 4 → Fin 4 → ℝ) (hadapt : F.IsAdapted gi)
    (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) (SH : V) :
    dfrV F de A dA H dH ddH 0 0 - ∑ j, F.β j • dfrV F de A dA H dH ddH j.succ 0 -
        F.N • ∑ b : Fin 3, ∑ j, F.E b j • dfrV F de A dA H dH ddH j.succ b.succ =
      F.N • (LPi F de A H dH gi Γ - (SH + higgsRes A dA H dH ddH gi Γ SH)) := by
  rw [← higgs_Pi_frame F de A dA H dH ddH gi hadapt Γ SH, smul_sub, N_fD_zero]
  simp only [fD_succ]

/-- The principal matrix `A^j` of the Higgs block on `(Π, Q_1, Q_2, Q_3)` (`none = Π`,
`some a = Q_a`), read off from `higgs_Q_row` and `higgs_Pi_row`: `A^j_{ΠΠ} = A^j_{Q_aQ_a} = -βʲ`,
`A^j_{ΠQ_a} = A^j_{Q_aΠ} = -N e_aʲ`. -/
def higgsSym (F : AdaptedFrame) (j : Fin 3) : Option (Fin 3) → Option (Fin 3) → ℝ
  | none, none => -F.β j
  | none, some a => -(F.N * F.E a j)
  | some a, none => -(F.N * F.E a j)
  | some a, some c => if a = c then -F.β j else 0

/-- **The Higgs principal matrices are symmetric.** -/
theorem higgsSym_symm (F : AdaptedFrame) (j : Fin 3) (r s : Option (Fin 3)) :
    higgsSym F j r s = higgsSym F j s r := by
  rcases r with _ | a <;> rcases s with _ | c <;> simp only [higgsSym]
  by_cases h : a = c
  · subst h; rfl
  · simp [h, Ne.symm h]

end Higgs

/-! ### Non-vacuity -/

/-- The row hypotheses are satisfiable: the flat frame is adapted to Minkowski space, so the Higgs
`Π`-row applies to every jet of a Higgs field in any Lie module. -/
example {𝔤 V : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [AddCommGroup V] [Module ℝ V]
    [LieRingModule 𝔤 V] [LieModule ℝ 𝔤 V] (A : Fin 4 → 𝔤) (dA : Fin 4 → Fin 4 → 𝔤)
    (H : V) (dH : Fin 4 → V) (ddH : Fin 4 → Fin 4 → V) :
    dfrV flatFrame (fun _ _ _ => 0) A dA H dH ddH 0 0 -
        ∑ j, flatFrame.β j • dfrV flatFrame (fun _ _ _ => 0) A dA H dH ddH j.succ 0 -
        flatFrame.N • ∑ b : Fin 3, ∑ j, flatFrame.E b j •
          dfrV flatFrame (fun _ _ _ => 0) A dA H dH ddH j.succ b.succ =
      flatFrame.N • (LPi flatFrame (fun _ _ _ => 0) A H dH minkInv (fun _ _ _ => 0) -
        (0 + higgsRes A dA H dH ddH minkInv (fun _ _ _ => 0) 0)) :=
  higgs_Pi_row flatFrame _ A dA H dH ddH minkInv flatFrame_adapted _ 0

end

end RenewalGeometry.ActualJetGauge
