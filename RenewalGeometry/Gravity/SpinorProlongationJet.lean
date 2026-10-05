/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.TwistedHalfRicciContractionExact

/-!
# Residual-sensitive tangential spinor prolongation (`prop:spinor-prolongation`)

Einstein–Standard-Model action-closure manuscript, `prop:spinor-prolongation`
(`eq:spinor-prolongation`, `eq:normal-spinor-jet`), as exact finite algebra on jets at a point
in a moving frame, over an arbitrary finite frame index type `ι`.

## Setting (jets at one point, moving frame `e_a`)

* Clifford multiplication: a `TwistedHalfRicci.CliffordFrame` (`c_a c_b + c_b c_a = -2η_{ab}`,
  `η = diag(ε)`, `ε_a = ±1`) in a real algebra `A`, acting on the spinor space `V` (an
  `A`-module); in the trivialisation by the orthonormal frame the `c_a` are constant.
* Frame: structure functions `[e_a, e_b] = Σ_c Λ_{ab}{}^c e_c`; Levi-Civita coefficients
  `∇_{e_a}e_b = Σ_c Γ_{ab}{}^c e_c`.
* Twisted connection `∇_aΨ = e_aΨ + ω_aΨ` with coefficients `ω_a ∈ A` and their frame
  derivatives `dω a b = e_a(ω_b)`.
* Spinor jets `ψ = Ψ`, `dψ a = e_aΨ`, `ddψ a b = e_a(e_bΨ)`, subject to the frame-commutator
  relation `ddψ a b - ddψ b a = Σ_c Λ_{ab}{}^c dψ c` (the definition of `Λ`).

`X_a = ∇_aΨ` (`cov`), the second covariant derivative `∇²_{ab}Ψ = e_a(X_b) + ω_aX_b - Γ_{ab}{}^cX_c`
(`cov2`), the twisted Dirac operator `𝒟Ψ = Σ_b ε_b c_b X_b` (`dirac`; `c^b = ε_b c_b`), its
covariant derivative `∇_a(𝒟Ψ)` (`covDirac`), and the operator on `T^*⊗S`,
`(𝒟^{T^*}X)_a = Σ_b ε_b c_b (∇_bX)_a = Σ_b ε_b c_b ∇²_{ba}Ψ` (`dTX`).

## Results

* `ricci_identity` — `∇²_{ab}Ψ - ∇²_{ba}Ψ = R^∇_{ab}Ψ` for a torsion-free frame connection, with
  `R^∇_{ab} = e_aω_b - e_bω_a + [ω_a, ω_b] - Λ_{ab}{}^cω_c` (`curv`).
* `covDirac_eq` — `∇_a(𝒟Ψ) = Σ_b ε_b c_b ∇²_{ab}Ψ` (Clifford multiplication is parallel:
  `[ω_a, c_b] = Γ_{ab}{}^c c_c`, metric compatibility).
* `dTX_eq` — the commutation `(𝒟^{T^*}X)_a = ∇_a(𝒟Ψ) + Σ_b ε_b c_b R^∇_{ba}Ψ`.
* `spinor_prolongation_general` — with an affine mass map `𝓜(H) = m₀ + 𝓜_H[H]` obeying the
  covariant product rule and `r_D = 𝒟Ψ - 𝓜(H)Ψ`:
  `(𝒟^{T^*}X)_a = 𝓜X_a + 𝓜_H[D_aH]Ψ + ∇_a r_D + Σ_b ε_b c_b R^∇_{ba}Ψ`.
* The Levi-Civita spin connection twisted by a gauge potential, `ω_a = ¼Σ ε_cε_d G_{acd} c_cc_d +
  ρ_a` (`LCJet`, `LCJet.ω`): `comm_spinPart` and `LCJet.clifford_parallel` (it is parallel for
  Clifford multiplication), `bracket_spinPart` (`so(η) → A` is a Lie map), **`LCJet.curv_eq`**
  (`R^∇_{ab} = ¼Σ ε_cε_d Rm_{abcd} c_cc_d + ρ(F_{ab})` with the frame Riemann tensor `Rm` of the
  connection and the gauge curvature `F`), `LCJet.Rm_anti₁/₂`, **`LCJet.Rm_bianchi`** (first
  Bianchi identity from the Jacobi identity of the frame and torsion-freeness),
  `LCJet.Rm_pair` (pair symmetry), `LCJet.Rm_bianchi'` (the form used by `lem:half-ricci`).
* **`LCJet.spinor_prolongation`** — `eq:spinor-prolongation` verbatim:
  `(𝒟^{T^*}X)_a = 𝓜X_a + 𝓜_H[D_aH]Ψ + ∇_a r_D + ½ Ric_{ab}c^bΨ + c^bρ(F_{ba})Ψ`, with
  `Ric_{ab} = Σ_c ε_c Rm_{cabc}` the Ricci tensor of the frame curvature (via
  `TwistedHalfRicci.twisted_half_ricci_contraction`, `lem:half-ricci`).
* **`normal_spinor_jet`** — `eq:normal-spinor-jet`: in a Lorentzian frame (`ε_0 = -1`,
  `ε_i = 1` otherwise) the Dirac equation `𝒟Ψ = 𝓜Ψ + r_D` gives
  `X_0 = c_0 Σ_{i ≠ 0} c_iX_i - c_0𝓜Ψ - c_0r_D`.
* `covR_local` — `∇_a r_D` involves only `r_D` and its derivative `e_a r_D` along the same frame
  vector: for a tangential index the prolonged equation needs spatial derivatives of `r_D` only.

Rendering (disclosed): the statement is an identity on jets at a point, as for
`lem:half-ricci` and `lem:harmonic-defect-forcing`; the jet relations (frame commutators on
`Ψ`, Jacobi identity of the frame, torsion-freeness, `e_a` of the Clifford generators `= 0`) are
the identities satisfied by the jets of smooth fields in a frame, taken as the jet convention.
-/

namespace RenewalGeometry.SpinorProlongation

open Finset TwistedHalfRicci

noncomputable section

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : Type*} [Ring A] [Algebra ℝ A]
variable {V : Type*} [AddCommGroup V] [Module A V] [Module ℝ V] [IsScalarTower ℝ A V]

/-! ### A general twisted frame connection on jets -/

/-- `X_a = ∇_aΨ = e_aΨ + ω_aΨ`. -/
def cov (ω : ι → A) (ψ : V) (dψ : ι → V) (a : ι) : V := dψ a + ω a • ψ

/-- `e_a(X_b) = e_a(e_bΨ) + e_a(ω_b)Ψ + ω_b e_aΨ` (product rule). -/
def dcov (ω : ι → A) (dω : ι → ι → A) (ψ : V) (dψ : ι → V) (ddψ : ι → ι → V) (a b : ι) : V :=
  ddψ a b + dω a b • ψ + ω b • dψ a

/-- The second covariant derivative `∇²_{ab}Ψ = e_a(X_b) + ω_aX_b - Σ_c Γ_{ab}{}^c X_c`. -/
def cov2 (Γ : ι → ι → ι → ℝ) (ω : ι → A) (dω : ι → ι → A) (ψ : V) (dψ : ι → V)
    (ddψ : ι → ι → V) (a b : ι) : V :=
  dcov ω dω ψ dψ ddψ a b + ω a • cov ω ψ dψ b - ∑ c, Γ a b c • cov ω ψ dψ c

/-- The curvature `R^∇_{ab} = e_aω_b - e_bω_a + [ω_a, ω_b] - Σ_c Λ_{ab}{}^c ω_c`. -/
def curv (Λ : ι → ι → ι → ℝ) (ω : ι → A) (dω : ι → ι → A) (a b : ι) : A :=
  dω a b - dω b a + (ω a * ω b - ω b * ω a) - ∑ c, Λ a b c • ω c

/-- **Ricci identity on jets.**  For a torsion-free frame connection
(`Γ_{ab}{}^c - Γ_{ba}{}^c = Λ_{ab}{}^c`) and spinor jets obeying the frame commutator relation,
`∇²_{ab}Ψ - ∇²_{ba}Ψ = R^∇_{ab}Ψ`. -/
theorem ricci_identity (Λ Γ : ι → ι → ι → ℝ) (ω : ι → A) (dω : ι → ι → A) (ψ : V)
    (dψ : ι → V) (ddψ : ι → ι → V)
    (hψ : ∀ a b, ddψ a b - ddψ b a = ∑ c, Λ a b c • dψ c)
    (htf : ∀ a b c, Γ a b c - Γ b a c = Λ a b c) (a b : ι) :
    cov2 Γ ω dω ψ dψ ddψ a b - cov2 Γ ω dω ψ dψ ddψ b a = curv Λ ω dω a b • ψ := by
  have hΓ : ∑ c, Γ a b c • cov ω ψ dψ c - ∑ c, Γ b a c • cov ω ψ dψ c =
      ∑ c, Λ a b c • dψ c + (∑ c, Λ a b c • ω c) • ψ := by
    rw [← Finset.sum_sub_distrib, Finset.sum_smul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← sub_smul, htf, cov, smul_add, smul_assoc]
  have h1 := hψ a b
  unfold cov2 dcov curv
  simp only [cov] at hΓ ⊢
  rw [sub_smul, add_smul, sub_smul, sub_smul, mul_smul, mul_smul]
  -- collect
  have key : ddψ a b + dω a b • ψ + ω b • dψ a + ω a • (dψ b + ω b • ψ) -
        ∑ c, Γ a b c • (dψ c + ω c • ψ) -
      (ddψ b a + dω b a • ψ + ω a • dψ b + ω b • (dψ a + ω a • ψ) -
        ∑ c, Γ b a c • (dψ c + ω c • ψ)) =
      (ddψ a b - ddψ b a) + (dω a b • ψ - dω b a • ψ) + (ω a • ω b • ψ - ω b • ω a • ψ) -
        (∑ c, Γ a b c • (dψ c + ω c • ψ) - ∑ c, Γ b a c • (dψ c + ω c • ψ)) := by
    rw [smul_add, smul_add]; abel
  rw [key, hΓ, h1]
  abel

/-- The twisted Dirac operator `𝒟Ψ = Σ_b ε_b c_b X_b` (`c^b = ε_b c_b`). -/
def dirac (Fr : CliffordFrame ι A) (ω : ι → A) (ψ : V) (dψ : ι → V) : V :=
  ∑ b, Fr.ε b • (Fr.c b • cov ω ψ dψ b)

/-- `e_a(𝒟Ψ) = Σ_b ε_b c_b e_a(X_b)` (the `c_b` are constant in the frame trivialisation). -/
def ddirac (Fr : CliffordFrame ι A) (ω : ι → A) (dω : ι → ι → A) (ψ : V) (dψ : ι → V)
    (ddψ : ι → ι → V) (a : ι) : V :=
  ∑ b, Fr.ε b • (Fr.c b • dcov ω dω ψ dψ ddψ a b)

/-- `∇_a(𝒟Ψ) = e_a(𝒟Ψ) + ω_a 𝒟Ψ`. -/
def covDirac (Fr : CliffordFrame ι A) (ω : ι → A) (dω : ι → ι → A) (ψ : V) (dψ : ι → V)
    (ddψ : ι → ι → V) (a : ι) : V :=
  ddirac Fr ω dω ψ dψ ddψ a + ω a • dirac Fr ω ψ dψ

/-- `(𝒟^{T^*}X)_a = Σ_b ε_b c_b (∇_bX)_a = Σ_b ε_b c_b ∇²_{ba}Ψ`. -/
def dTX (Fr : CliffordFrame ι A) (Γ : ι → ι → ι → ℝ) (ω : ι → A) (dω : ι → ι → A) (ψ : V)
    (dψ : ι → V) (ddψ : ι → ι → V) (a : ι) : V :=
  ∑ b, Fr.ε b • (Fr.c b • cov2 Γ ω dω ψ dψ ddψ b a)

/-- `[ω_a, c_b] = Σ_c Γ_{ab}{}^c c_c` moves `ω_a` through a Clifford generator. -/
theorem omega_smul_c (Fr : CliffordFrame ι A) (Γ : ι → ι → ι → ℝ) (ω : ι → A)
    (hcl : ∀ a b, ω a * Fr.c b - Fr.c b * ω a = ∑ c, Γ a b c • Fr.c c) (a b : ι) (x : V) :
    ω a • (Fr.c b • x) = Fr.c b • (ω a • x) + ∑ c, Γ a b c • (Fr.c c • x) := by
  have h : ω a * Fr.c b = Fr.c b * ω a + ∑ c, Γ a b c • Fr.c c := by
    rw [← hcl]; abel
  rw [← mul_smul, h, add_smul, mul_smul, Finset.sum_smul]
  simp only [smul_assoc]

/-- **`∇_a(𝒟Ψ) = Σ_b ε_b c_b ∇²_{ab}Ψ`**: Clifford multiplication is parallel
(`[ω_a, c_b] = Γ_{ab}{}^c c_c`) and the frame connection is metric
(`ε_c Γ_{ab}{}^c = -ε_b Γ_{ac}{}^b`). -/
theorem covDirac_eq (Fr : CliffordFrame ι A) (Γ : ι → ι → ι → ℝ) (ω : ι → A)
    (dω : ι → ι → A) (ψ : V) (dψ : ι → V) (ddψ : ι → ι → V)
    (hcl : ∀ a b, ω a * Fr.c b - Fr.c b * ω a = ∑ c, Γ a b c • Fr.c c)
    (hmc : ∀ a b c, Fr.ε c * Γ a b c = -(Fr.ε b * Γ a c b)) (a : ι) :
    covDirac Fr ω dω ψ dψ ddψ a = ∑ b, Fr.ε b • (Fr.c b • cov2 Γ ω dω ψ dψ ddψ a b) := by
  -- the metric antisymmetry in the form needed
  have hm' : ∀ b c, Fr.ε b * Γ a b c = -(Fr.ε c * Γ a c b) := by
    intro b c
    have h1 := hmc a b c
    have hb := Fr.sign_sq b
    have hc := Fr.sign_sq c
    have : Fr.ε b * Fr.ε c * (Fr.ε c * Γ a b c) = Fr.ε b * Fr.ε c * (-(Fr.ε b * Γ a c b)) := by
      rw [h1]
    linear_combination this - (Fr.ε b * Γ a b c) * hc - (Fr.ε c * Γ a c b) * hb
  have hω : ω a • dirac Fr ω ψ dψ =
      ∑ b, Fr.ε b • (Fr.c b • (ω a • cov ω ψ dψ b)) - ∑ b, Fr.ε b • (Fr.c b • ∑ c, Γ a b c • cov ω ψ dψ c) := by
    unfold dirac
    rw [Finset.smul_sum]
    have hsw : ∑ b, ∑ c, (Fr.ε b * Γ a b c) • (Fr.c c • cov ω ψ dψ b) =
        -∑ b, Fr.ε b • (Fr.c b • ∑ c, Γ a b c • cov ω ψ dψ c) := by
      rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hm' b c, neg_smul, mul_smul, smul_comm (Γ a c b) (Fr.c c) (cov ω ψ dψ b)]
    rw [sub_eq_add_neg, ← hsw, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_comm (ω a) (Fr.ε b), omega_smul_c Fr Γ ω hcl a b, smul_add, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [smul_smul]
  unfold covDirac ddirac cov2
  rw [hω, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [smul_sub, smul_sub, smul_add, smul_add]
  abel

/-- **Commutation of `∇_a` with the twisted Dirac operator:**
`(𝒟^{T^*}X)_a = ∇_a(𝒟Ψ) + Σ_b ε_b c_b R^∇_{ba}Ψ`. -/
theorem dTX_eq (Fr : CliffordFrame ι A) (Λ Γ : ι → ι → ι → ℝ) (ω : ι → A) (dω : ι → ι → A)
    (ψ : V) (dψ : ι → V) (ddψ : ι → ι → V)
    (hψ : ∀ a b, ddψ a b - ddψ b a = ∑ c, Λ a b c • dψ c)
    (htf : ∀ a b c, Γ a b c - Γ b a c = Λ a b c)
    (hcl : ∀ a b, ω a * Fr.c b - Fr.c b * ω a = ∑ c, Γ a b c • Fr.c c)
    (hmc : ∀ a b c, Fr.ε c * Γ a b c = -(Fr.ε b * Γ a c b)) (a : ι) :
    dTX Fr Γ ω dω ψ dψ ddψ a =
      covDirac Fr ω dω ψ dψ ddψ a + ∑ b, Fr.ε b • ((Fr.c b * curv Λ ω dω b a) • ψ) := by
  rw [covDirac_eq Fr Γ ω dω ψ dψ ddψ hcl hmc a, dTX, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h := ricci_identity Λ Γ ω dω ψ dψ ddψ hψ htf b a
  rw [sub_eq_iff_eq_add'] at h
  rw [h, smul_add, smul_add, mul_smul]

/-! ### The mass map and the Dirac residual -/

section Mass

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- The affine mass map `𝓜(H) = m₀ + 𝓜_H[H]`. -/
def mass (m0 : A) (L : W →ₗ[ℝ] A) (h : W) : A := m0 + L h

/-- The gauge-covariant Higgs derivative `D_aH = e_aH + ρ_H(A_a)H`. -/
def DH (ρH : ι → W →ₗ[ℝ] W) (h : W) (dh : ι → W) (a : ι) : W := dh a + ρH a h

/-- The Dirac residual `r_D = 𝒟Ψ - 𝓜(H)Ψ`. -/
def resD (Fr : CliffordFrame ι A) (ω : ι → A) (m0 : A) (L : W →ₗ[ℝ] A) (h : W) (ψ : V)
    (dψ : ι → V) : V :=
  dirac Fr ω ψ dψ - mass m0 L h • ψ

/-- Its frame-derivative jet `e_a r_D = e_a(𝒟Ψ) - 𝓜_H[e_aH]Ψ - 𝓜(H)e_aΨ` (product rule). -/
def dresD (Fr : CliffordFrame ι A) (ω : ι → A) (dω : ι → ι → A) (m0 : A) (L : W →ₗ[ℝ] A)
    (h : W) (dh : ι → W) (ψ : V) (dψ : ι → V) (ddψ : ι → ι → V) (a : ι) : V :=
  ddirac Fr ω dω ψ dψ ddψ a - (L (dh a) • ψ + mass m0 L h • dψ a)

/-- `∇_a r_D = e_a r_D + ω_a r_D`. -/
def covResD (Fr : CliffordFrame ι A) (ω : ι → A) (dω : ι → ι → A) (m0 : A) (L : W →ₗ[ℝ] A)
    (h : W) (dh : ι → W) (ψ : V) (dψ : ι → V) (ddψ : ι → ι → V) (a : ι) : V :=
  dresD Fr ω dω m0 L h dh ψ dψ ddψ a + ω a • resD Fr ω m0 L h ψ dψ

/-- **Covariant product rule for the mass term:** if `[ω_a, 𝓜(w)] = 𝓜_H[ρ_H(A_a)w]`, then
`∇_a(𝒟Ψ) = 𝓜X_a + 𝓜_H[D_aH]Ψ + ∇_a r_D`. -/
theorem covDirac_eq_mass (Fr : CliffordFrame ι A) (ω : ι → A) (dω : ι → ι → A) (m0 : A)
    (L : W →ₗ[ℝ] A) (ρH : ι → W →ₗ[ℝ] W) (h : W) (dh : ι → W) (ψ : V) (dψ : ι → V)
    (ddψ : ι → ι → V)
    (heq : ∀ a w, ω a * mass m0 L w - mass m0 L w * ω a = L (ρH a w)) (a : ι) :
    covDirac Fr ω dω ψ dψ ddψ a =
      mass m0 L h • cov ω ψ dψ a + L (DH ρH h dh a) • ψ +
        covResD Fr ω dω m0 L h dh ψ dψ ddψ a := by
  have hc : ω a * mass m0 L h = mass m0 L h * ω a + L (ρH a h) := by
    rw [← heq]; abel
  unfold covResD dresD resD covDirac cov DH
  rw [smul_sub, ← mul_smul, hc, add_smul, mul_smul, map_add, add_smul, smul_add]
  abel

/-- **`eq:spinor-prolongation` for a general twisted frame connection:**
`(𝒟^{T^*}X)_a = 𝓜X_a + 𝓜_H[D_aH]Ψ + ∇_a r_D + Σ_b ε_b c_b R^∇_{ba}Ψ`. -/
theorem spinor_prolongation_general (Fr : CliffordFrame ι A) (Λ Γ : ι → ι → ι → ℝ)
    (ω : ι → A) (dω : ι → ι → A) (m0 : A) (L : W →ₗ[ℝ] A) (ρH : ι → W →ₗ[ℝ] W) (h : W)
    (dh : ι → W) (ψ : V) (dψ : ι → V) (ddψ : ι → ι → V)
    (hψ : ∀ a b, ddψ a b - ddψ b a = ∑ c, Λ a b c • dψ c)
    (htf : ∀ a b c, Γ a b c - Γ b a c = Λ a b c)
    (hcl : ∀ a b, ω a * Fr.c b - Fr.c b * ω a = ∑ c, Γ a b c • Fr.c c)
    (hmc : ∀ a b c, Fr.ε c * Γ a b c = -(Fr.ε b * Γ a c b))
    (heq : ∀ a w, ω a * mass m0 L w - mass m0 L w * ω a = L (ρH a w)) (a : ι) :
    dTX Fr Γ ω dω ψ dψ ddψ a =
      mass m0 L h • cov ω ψ dψ a + L (DH ρH h dh a) • ψ +
        covResD Fr ω dω m0 L h dh ψ dψ ddψ a +
          ∑ b, Fr.ε b • ((Fr.c b * curv Λ ω dω b a) • ψ) := by
  rw [dTX_eq Fr Λ Γ ω dω ψ dψ ddψ hψ htf hcl hmc a,
    covDirac_eq_mass Fr ω dω m0 L ρH h dh ψ dψ ddψ heq a]

/-- **Locality of the residual term:** `∇_a r_D` depends on the residual jet only through
`r_D` and `e_a r_D` (the derivative along the same frame vector).  For a tangential index
`a`, `e_a = e_a{}^j∂_j` is tangent to the slices, so the prolonged equation needs spatial
derivatives of `r_D` but no time derivative. -/
theorem covR_local (ω : ι → A) (a : ι) (r r' : V) (dr dr' : ι → V) (h0 : r = r')
    (h1 : dr a = dr' a) : dr a + ω a • r = dr' a + ω a • r' := by
  rw [h0, h1]

end Mass

/-! ### The spin representation of `so(η)` -/

/-- `X_W = ¼ Σ_{c,d} ε_c ε_d W_{cd} c_c c_d` (the spin lift of an `η`-antisymmetric array).  For
`W = R_{ab··}` this is `TwistedHalfRicci.spinorCurvature`. -/
def spinPart (Fr : CliffordFrame ι A) (W : ι → ι → ℝ) : A :=
  (1 / 4 : ℝ) • ∑ c, ∑ d, (Fr.ε c * Fr.ε d * W c d) • (Fr.c c * Fr.c d)

theorem spinorCurvature_eq_spinPart (Fr : CliffordFrame ι A) (R : ι → ι → ι → ι → ℝ)
    (a b : ι) : spinorCurvature Fr R a b = spinPart Fr (R a b) := rfl

theorem spinPart_add (Fr : CliffordFrame ι A) (W W' : ι → ι → ℝ) :
    spinPart Fr (fun x y => W x y + W' x y) = spinPart Fr W + spinPart Fr W' := by
  unfold spinPart
  rw [← smul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← add_smul]; congr 1; ring

theorem spinPart_sub (Fr : CliffordFrame ι A) (W W' : ι → ι → ℝ) :
    spinPart Fr (fun x y => W x y - W' x y) = spinPart Fr W - spinPart Fr W' := by
  unfold spinPart
  rw [← smul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← sub_smul]; congr 1; ring

theorem spinPart_sum_smul (Fr : CliffordFrame ι A) (f : ι → ℝ) (W : ι → ι → ι → ℝ) :
    spinPart Fr (fun x y => ∑ e, f e * W e x y) = ∑ e, f e • spinPart Fr (W e) := by
  unfold spinPart
  simp only [Finset.smul_sum, smul_smul, Finset.mul_sum, Finset.sum_smul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  refine Finset.sum_congr rfl fun e _ => ?_
  congr 1; ring

/-- Reversal of a triple sum. -/
theorem sum3_rev {M : Type*} [AddCommMonoid M] (F : ι → ι → ι → M) :
    ∑ c, ∑ d, ∑ e, F c d e = ∑ e, ∑ d, ∑ c, F c d e := by
  calc ∑ c, ∑ d, ∑ e, F c d e = ∑ c, ∑ e, ∑ d, F c d e :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ e, ∑ c, ∑ d, F c d e := Finset.sum_comm
    _ = ∑ e, ∑ d, ∑ c, F c d e := Finset.sum_congr rfl fun e _ => Finset.sum_comm

/-- `c_c c_d c_b - c_b c_c c_d = 2η_{bc} c_d - 2η_{bd} c_c`. -/
theorem comm_pair (Fr : CliffordFrame ι A) (b c d : ι) :
    Fr.c c * Fr.c d * Fr.c b - Fr.c b * (Fr.c c * Fr.c d) =
      (2 * Fr.η b c) • Fr.c d - (2 * Fr.η b d) • Fr.c c := by
  rw [← mul_assoc, triple_comm Fr b c d]
  abel

/-- **The spin lift moves through a Clifford generator:** for `W` antisymmetric,
`[X_W, c_b] = Σ_d ε_d W_{bd} c_d`. -/
theorem comm_spinPart (Fr : CliffordFrame ι A) (W : ι → ι → ℝ) (hW : ∀ x y, W y x = -W x y)
    (b : ι) :
    spinPart Fr W * Fr.c b - Fr.c b * spinPart Fr W = ∑ d, (Fr.ε d * W b d) • Fr.c d := by
  have hε : ∀ x, Fr.ε x * Fr.ε x = 1 := fun x => by rw [← sq]; exact Fr.sign_sq x
  have e1 : spinPart Fr W * Fr.c b - Fr.c b * spinPart Fr W =
      (1 / 4 : ℝ) • ∑ c, ∑ d, (Fr.ε c * Fr.ε d * W c d) •
        ((2 * Fr.η b c) • Fr.c d - (2 * Fr.η b d) • Fr.c c) := by
    unfold spinPart
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, Finset.sum_mul, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, comm_pair]
  rw [e1]
  simp only [smul_sub, Finset.sum_sub_distrib, smul_smul, CliffordFrame.η]
  -- evaluate the `δ`-sums
  have s1 : ∑ c, ∑ d, (Fr.ε c * Fr.ε d * W c d * (2 * if b = c then Fr.ε b else 0)) • Fr.c d =
      ∑ d, (2 * (Fr.ε d * W b d)) • Fr.c d := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have := hε b
    linear_combination (2 * Fr.ε d * W b d) * this
  have s2 : ∑ c, ∑ d, (Fr.ε c * Fr.ε d * W c d * (2 * if b = d then Fr.ε b else 0)) • Fr.c c =
      -∑ d, (2 * (Fr.ε d * W b d)) • Fr.c d := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_smul, ← neg_smul]
    congr 1
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have := hε b
    rw [hW b c]
    linear_combination (-2 * Fr.ε c * W b c) * this
  rw [s1, s2, smul_neg, sub_neg_eq_add, ← add_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [smul_smul]; congr 1; ring

/-- `[X_W, c_c c_d] = [X_W, c_c] c_d + c_c [X_W, c_d]`. -/
theorem comm_spinPart_pair (Fr : CliffordFrame ι A) (W : ι → ι → ℝ)
    (hW : ∀ x y, W y x = -W x y) (c d : ι) :
    spinPart Fr W * (Fr.c c * Fr.c d) - Fr.c c * Fr.c d * spinPart Fr W =
      (∑ e, (Fr.ε e * W c e) • Fr.c e) * Fr.c d + Fr.c c * ∑ e, (Fr.ε e * W d e) • Fr.c e := by
  rw [← comm_spinPart Fr W hW c, ← comm_spinPart Fr W hW d]
  noncomm_ring

/-- **The spin lift is a Lie map:** for antisymmetric `W`,
`[X_W, X_V] = X_Z`, `Z_{xy} = Σ_z ε_z (V_{xz} W_{zy} - W_{xz} V_{zy})`. -/
theorem bracket_spinPart (Fr : CliffordFrame ι A) (W V : ι → ι → ℝ)
    (hW : ∀ x y, W y x = -W x y) :
    spinPart Fr W * spinPart Fr V - spinPart Fr V * spinPart Fr W =
      spinPart Fr (fun x y => ∑ z, Fr.ε z * (V x z * W z y - W x z * V z y)) := by
  have hV : spinPart Fr V = (1 / 4 : ℝ) • ∑ c, ∑ d, (Fr.ε c * Fr.ε d * V c d) •
      (Fr.c c * Fr.c d) := rfl
  have e1 : spinPart Fr W * spinPart Fr V - spinPart Fr V * spinPart Fr W =
      (1 / 4 : ℝ) • ∑ c, ∑ d, (Fr.ε c * Fr.ε d * V c d) •
        ((∑ e, (Fr.ε e * W c e) • Fr.c e) * Fr.c d +
          Fr.c c * ∑ e, (Fr.ε e * W d e) • Fr.c e) := by
    rw [hV, mul_smul_comm, smul_mul_assoc, ← smul_sub, Finset.mul_sum, Finset.sum_mul,
      ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, comm_spinPart_pair Fr W hW]
  have hL : ∑ c, ∑ d, (Fr.ε c * Fr.ε d * V c d) •
        ((∑ e, (Fr.ε e * W c e) • Fr.c e) * Fr.c d +
          Fr.c c * ∑ e, (Fr.ε e * W d e) • Fr.c e) =
      ∑ c, ∑ d, ∑ e, (Fr.ε c * Fr.ε d * V c d * (Fr.ε e * W c e)) • (Fr.c e * Fr.c d) +
      ∑ c, ∑ d, ∑ e, (Fr.ε c * Fr.ε d * V c d * (Fr.ε e * W d e)) • (Fr.c c * Fr.c e) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum, smul_add, Finset.smul_sum, Finset.smul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun e _ => ?_
      rw [smul_mul_assoc, smul_smul]
    · refine Finset.sum_congr rfl fun e _ => ?_
      rw [mul_smul_comm, smul_smul]
  have hR : ∑ x, ∑ y, (Fr.ε x * Fr.ε y * ∑ z, Fr.ε z * (V x z * W z y - W x z * V z y)) •
        (Fr.c x * Fr.c y) =
      ∑ x, ∑ y, ∑ z, (Fr.ε x * Fr.ε y * (Fr.ε z * (V x z * W z y))) • (Fr.c x * Fr.c y) -
      ∑ x, ∑ y, ∑ z, (Fr.ε x * Fr.ε y * (Fr.ε z * (W x z * V z y))) • (Fr.c x * Fr.c y) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_sub_distrib]
    simp_rw [← sub_smul]
    rw [← Finset.sum_smul]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    ring
  rw [e1, hL]
  unfold spinPart
  congr 1
  rw [hR, sub_eq_add_neg, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    refine Finset.sum_congr rfl fun z _ => ?_
    congr 1; ring
  · rw [sum3_rev, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← neg_smul, hW z x]
    congr 1; ring

/-- An element commuting with all products `c_c c_d` commutes with every spin lift. -/
theorem commute_spinPart (Fr : CliffordFrame ι A) (x : A)
    (hx : ∀ c d, x * (Fr.c c * Fr.c d) = Fr.c c * Fr.c d * x) (W : ι → ι → ℝ) :
    x * spinPart Fr W = spinPart Fr W * x := by
  unfold spinPart
  rw [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, hx]

/-- An element commuting with every generator commutes with every product `c_c c_d`. -/
theorem commute_pair_of_commute (Fr : CliffordFrame ι A) (x : A)
    (hx : ∀ b, x * Fr.c b = Fr.c b * x) (c d : ι) :
    x * (Fr.c c * Fr.c d) = Fr.c c * Fr.c d * x := by
  rw [← mul_assoc, hx, mul_assoc, hx, mul_assoc]

/-! ### The twisted Levi-Civita spin connection -/

/-- `Γ_{ab}{}^c = ε_c G_{abc}` from the lowered coefficients `G_{abc} = ⟨∇_{e_a}e_b, e_c⟩`. -/
def lcΓ (ε : ι → ℝ) (G : ι → ι → ι → ℝ) (a b c : ι) : ℝ := ε c * G a b c

/-- The structure functions of a torsion-free connection,
`Λ_{ab}{}^c = Γ_{ab}{}^c - Γ_{ba}{}^c` (`[e_a, e_b] = ∇_{e_a}e_b - ∇_{e_b}e_a`). -/
def lcΛ (ε : ι → ℝ) (G : ι → ι → ι → ℝ) (a b c : ι) : ℝ := lcΓ ε G a b c - lcΓ ε G b a c

/-- Their frame derivatives `e_e(Λ_{ab}{}^c)` from the jet `dG e a b c = e_e(G_{abc})`. -/
def lcdΛ (ε : ι → ℝ) (dG : ι → ι → ι → ι → ℝ) (e a b c : ι) : ℝ :=
  ε c * (dG e a b c - dG e b a c)

/-- **Jets of the twisted Levi-Civita spin connection** in an orthonormal moving frame:
lowered connection coefficients `G_{abc} = ⟨∇_{e_a}e_b, e_c⟩` (antisymmetric in `b, c`: metric
connection) with their frame derivatives, a gauge potential `ρ_a = ρ(A(e_a)) ∈ A` commuting with
Clifford multiplication, with its frame derivatives, and the **Jacobi identity**
`Σ_cyc [[e_a, e_b], e_c] = 0` of the frame written with the torsion-free structure functions
`Λ = Γ - Γᵀ`. -/
structure LCJet (Fr : CliffordFrame ι A) where
  /-- `G a b c = ⟨∇_{e_a}e_b, e_c⟩` -/
  G : ι → ι → ι → ℝ
  /-- `dG e a b c = e_e(G a b c)` -/
  dG : ι → ι → ι → ι → ℝ
  /-- the gauge potential acting on the twisting factor -/
  ρ : ι → A
  /-- `dρ e a = e_e(ρ_a)` -/
  dρ : ι → ι → A
  G_anti : ∀ a b c, G a c b = -G a b c
  dG_anti : ∀ e a b c, dG e a c b = -dG e a b c
  ρ_comm : ∀ a b, ρ a * Fr.c b = Fr.c b * ρ a
  jacobi : ∀ a b c f,
    (∑ d, lcΛ Fr.ε G a b d * lcΛ Fr.ε G d c f - lcdΛ Fr.ε dG c a b f) +
      (∑ d, lcΛ Fr.ε G b c d * lcΛ Fr.ε G d a f - lcdΛ Fr.ε dG a b c f) +
        (∑ d, lcΛ Fr.ε G c a d * lcΛ Fr.ε G d b f - lcdΛ Fr.ε dG b c a f) = 0

theorem eps_mul_self (Fr : CliffordFrame ι A) (x : ι) : Fr.ε x * Fr.ε x = 1 := by
  rw [← sq]; exact Fr.sign_sq x

namespace LCJet

variable {Fr : CliffordFrame ι A} (J : LCJet Fr)

/-- The twisted spin connection `ω_a = ¼ Σ ε_cε_d G_{acd} c_cc_d + ρ_a`. -/
def ω (a : ι) : A := spinPart Fr (J.G a) + J.ρ a

/-- Its frame derivatives `e_e(ω_a)`. -/
def dω (e a : ι) : A := spinPart Fr (J.dG e a) + J.dρ e a

/-- The frame Riemann tensor `Rm_{abxy} = ⟨R(e_a, e_b)e_x, e_y⟩`,
`R(X,Y) = ∇_X∇_Y - ∇_Y∇_X - ∇_{[X,Y]}`. -/
def Rm (a b x y : ι) : ℝ :=
  J.dG a b x y - J.dG b a x y + ∑ z, Fr.ε z * (J.G b x z * J.G a z y - J.G a x z * J.G b z y) -
    ∑ e, lcΛ Fr.ε J.G a b e * J.G e x y

/-- The gauge curvature `ρ(F_{ab}) = e_aρ_b - e_bρ_a + [ρ_a, ρ_b] - Λ_{ab}{}^eρ_e`. -/
def F (a b : ι) : A :=
  J.dρ a b - J.dρ b a + (J.ρ a * J.ρ b - J.ρ b * J.ρ a) - ∑ e, lcΛ Fr.ε J.G a b e • J.ρ e


/-- Clifford multiplication is parallel: `[ω_a, c_b] = Σ_c Γ_{ab}{}^c c_c`. -/
theorem clifford_parallel (a b : ι) :
    J.ω a * Fr.c b - Fr.c b * J.ω a = ∑ c, lcΓ Fr.ε J.G a b c • Fr.c c := by
  have h := comm_spinPart Fr (J.G a) (fun x y => J.G_anti a x y) b
  unfold ω
  rw [add_mul, mul_add, J.ρ_comm a b]
  have : spinPart Fr (J.G a) * Fr.c b + Fr.c b * J.ρ a - (Fr.c b * spinPart Fr (J.G a) +
      Fr.c b * J.ρ a) = spinPart Fr (J.G a) * Fr.c b - Fr.c b * spinPart Fr (J.G a) := by abel
  rw [this, h]
  rfl

/-- Metric compatibility `ε_c Γ_{ab}{}^c = -ε_b Γ_{ac}{}^b`. -/
theorem metric_compat (a b c : ι) :
    Fr.ε c * lcΓ Fr.ε J.G a b c = -(Fr.ε b * lcΓ Fr.ε J.G a c b) := by
  unfold lcΓ
  rw [← mul_assoc, ← mul_assoc, eps_mul_self, eps_mul_self, J.G_anti]
  ring

theorem torsion_free (a b c : ι) : lcΓ Fr.ε J.G a b c - lcΓ Fr.ε J.G b a c = lcΛ Fr.ε J.G a b c :=
  rfl

theorem ρ_spin (a : ι) (W : ι → ι → ℝ) : J.ρ a * spinPart Fr W = spinPart Fr W * J.ρ a :=
  commute_spinPart Fr _ (commute_pair_of_commute Fr _ (J.ρ_comm a)) W

/-- **Curvature of the twisted Levi-Civita spin connection:**
`R^∇_{ab} = ¼ Σ ε_xε_y Rm_{abxy} c_xc_y + ρ(F_{ab})`. -/
theorem curv_eq (a b : ι) :
    curv (lcΛ Fr.ε J.G) J.ω J.dω a b = spinPart Fr (J.Rm a b) + J.F a b := by
  have hS : spinPart Fr (J.Rm a b) = spinPart Fr (J.dG a b) - spinPart Fr (J.dG b a) +
      spinPart Fr (fun x y => ∑ z, Fr.ε z * (J.G b x z * J.G a z y - J.G a x z * J.G b z y)) -
      ∑ e, lcΛ Fr.ε J.G a b e • spinPart Fr (J.G e) := by
    rw [← spinPart_sum_smul, ← spinPart_sub, ← spinPart_add, ← spinPart_sub]
    rfl
  have hB := bracket_spinPart Fr (J.G a) (J.G b) (fun x y => J.G_anti a x y)
  have h1 := J.ρ_spin a (J.G b)
  have h2 := J.ρ_spin b (J.G a)
  rw [hS, ← hB]
  unfold curv ω dω F
  simp only [add_mul, mul_add, smul_add, Finset.sum_add_distrib]
  rw [h1, h2]
  abel

/-- `Rm` is antisymmetric in its last pair. -/
theorem Rm_anti₁ (a b x y : ι) : J.Rm a b y x = -J.Rm a b x y := by
  unfold Rm
  have hs : ∑ z, Fr.ε z * (J.G b y z * J.G a z x - J.G a y z * J.G b z x) =
      -∑ z, Fr.ε z * (J.G b x z * J.G a z y - J.G a x z * J.G b z y) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [J.G_anti b z y, J.G_anti a x z, J.G_anti a z y, J.G_anti b x z]
    ring
  have ht : ∑ e, lcΛ Fr.ε J.G a b e * J.G e y x = -∑ e, lcΛ Fr.ε J.G a b e * J.G e x y := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [J.G_anti e x y]; ring
  rw [hs, ht, J.dG_anti a b x y, J.dG_anti b a x y]
  ring

/-- `Rm` is antisymmetric in its first pair. -/
theorem Rm_anti₂ (a b x y : ι) : J.Rm b a x y = -J.Rm a b x y := by
  unfold Rm
  have hs : ∑ z, Fr.ε z * (J.G a x z * J.G b z y - J.G b x z * J.G a z y) =
      -∑ z, Fr.ε z * (J.G b x z * J.G a z y - J.G a x z * J.G b z y) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    ring
  have ht : ∑ e, lcΛ Fr.ε J.G b a e * J.G e x y = -∑ e, lcΛ Fr.ε J.G a b e * J.G e x y := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    unfold lcΛ; ring
  rw [hs, ht]
  ring

theorem Rm_eq_sum (a b c f : ι) :
    J.Rm a b c f = J.dG a b c f - J.dG b a c f +
      ∑ z, (Fr.ε z * (J.G b c z * J.G a z f - J.G a c z * J.G b z f) -
        lcΛ Fr.ε J.G a b z * J.G z c f) := by
  unfold Rm
  rw [add_sub_assoc, ← Finset.sum_sub_distrib]

/-- **First Bianchi identity** `Rm_{abcf} + Rm_{bcaf} + Rm_{cabf} = 0`, from the Jacobi
identity of the frame and torsion-freeness. -/
theorem Rm_bianchi (a b c f : ι) : J.Rm a b c f + J.Rm b c a f + J.Rm c a b f = 0 := by
  have hj := J.jacobi a b c f
  have hf : Fr.ε f * Fr.ε f = 1 := eps_mul_self Fr f
  rw [J.Rm_eq_sum, J.Rm_eq_sum, J.Rm_eq_sum]
  have hpt : ∀ z,
      (Fr.ε z * (J.G b c z * J.G a z f - J.G a c z * J.G b z f) -
          lcΛ Fr.ε J.G a b z * J.G z c f) +
        (Fr.ε z * (J.G c a z * J.G b z f - J.G b a z * J.G c z f) -
          lcΛ Fr.ε J.G b c z * J.G z a f) +
        (Fr.ε z * (J.G a b z * J.G c z f - J.G c b z * J.G a z f) -
          lcΛ Fr.ε J.G c a z * J.G z b f) =
      -(Fr.ε f * (lcΛ Fr.ε J.G a b z * lcΛ Fr.ε J.G z c f +
        lcΛ Fr.ε J.G b c z * lcΛ Fr.ε J.G z a f + lcΛ Fr.ε J.G c a z * lcΛ Fr.ε J.G z b f)) := by
    intro z
    unfold lcΛ lcΓ
    linear_combination (Fr.ε z * ((J.G a b z - J.G b a z) * (J.G z c f - J.G c z f) +
      (J.G b c z - J.G c b z) * (J.G z a f - J.G a z f) +
      (J.G c a z - J.G a c z) * (J.G z b f - J.G b z f))) * hf
  have hsum : ∑ z, (Fr.ε z * (J.G b c z * J.G a z f - J.G a c z * J.G b z f) -
          lcΛ Fr.ε J.G a b z * J.G z c f) +
        ∑ z, (Fr.ε z * (J.G c a z * J.G b z f - J.G b a z * J.G c z f) -
          lcΛ Fr.ε J.G b c z * J.G z a f) +
        ∑ z, (Fr.ε z * (J.G a b z * J.G c z f - J.G c b z * J.G a z f) -
          lcΛ Fr.ε J.G c a z * J.G z b f) =
      -(Fr.ε f * (∑ d, lcΛ Fr.ε J.G a b d * lcΛ Fr.ε J.G d c f +
        ∑ d, lcΛ Fr.ε J.G b c d * lcΛ Fr.ε J.G d a f +
        ∑ d, lcΛ Fr.ε J.G c a d * lcΛ Fr.ε J.G d b f)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun z _ => hpt z
  unfold lcdΛ at hj
  have hd : J.dG a b c f - J.dG b a c f + (J.dG b c a f - J.dG c b a f) +
      (J.dG c a b f - J.dG a c b f) =
      Fr.ε f * (Fr.ε f * (J.dG c a b f - J.dG c b a f) + Fr.ε f * (J.dG a b c f - J.dG a c b f) +
        Fr.ε f * (J.dG b c a f - J.dG b a c f)) := by
    linear_combination (-(J.dG a b c f - J.dG b a c f + (J.dG b c a f - J.dG c b a f) +
      (J.dG c a b f - J.dG a c b f))) * hf
  linear_combination hsum + hd - Fr.ε f * hj

/-- Pair symmetry `Rm_{abcd} = Rm_{cdab}`. -/
theorem Rm_pair (a b c d : ι) : J.Rm a b c d = J.Rm c d a b := by
  have B1 := J.Rm_bianchi a b c d
  have B2 := J.Rm_bianchi a b d c
  have B3 := J.Rm_bianchi c d a b
  have B4 := J.Rm_bianchi c d b a
  have B5 := J.Rm_bianchi a c d b
  have B6 := J.Rm_bianchi b c d a
  have B7 := J.Rm_bianchi a d b c
  have B8 := J.Rm_bianchi b d a c
  linarith [J.Rm_anti₁ a b c d, J.Rm_anti₂ a b c d, J.Rm_anti₁ c d a b, J.Rm_anti₂ c d a b,
    J.Rm_anti₁ b c a d, J.Rm_anti₂ b c a d, J.Rm_anti₁ c a b d, J.Rm_anti₂ c a b d,
    J.Rm_anti₁ a b d c, J.Rm_anti₂ b d a c, J.Rm_anti₁ d a b c, J.Rm_anti₂ d a b c,
    J.Rm_anti₁ d a c b, J.Rm_anti₂ d a c b, J.Rm_anti₁ a c b d, J.Rm_anti₂ a c b d,
    J.Rm_anti₁ c d b a, J.Rm_anti₂ c d b a, J.Rm_anti₁ d b c a, J.Rm_anti₂ d b c a,
    J.Rm_anti₁ b c d a, J.Rm_anti₂ b c d a, J.Rm_anti₁ d b a c, J.Rm_anti₂ d b a c,
    J.Rm_anti₁ c a d b, J.Rm_anti₂ c a d b, J.Rm_anti₁ b a d c, J.Rm_anti₂ b a d c,
    J.Rm_anti₁ a d b c, J.Rm_anti₂ a d b c, J.Rm_anti₁ b d c a, J.Rm_anti₂ b d c a,
    J.Rm_anti₁ c b a d, J.Rm_anti₂ c b a d, J.Rm_anti₁ a c d b, J.Rm_anti₂ a c d b,
    J.Rm_anti₁ d c a b, J.Rm_anti₂ d c a b, J.Rm_anti₁ b a c d, J.Rm_anti₂ b a c d]

/-- The Bianchi identity in the form of `lem:half-ricci`: `R_{abcd} + R_{acdb} + R_{adbc} = 0`. -/
theorem Rm_bianchi' (a b c d : ι) : J.Rm a b c d + J.Rm a c d b + J.Rm a d b c = 0 := by
  rw [J.Rm_pair a b c d, J.Rm_pair a c d b, J.Rm_pair a d b c]
  have B := J.Rm_bianchi c d b a
  rw [J.Rm_anti₁ c d b a, J.Rm_anti₁ d b c a, J.Rm_anti₁ b c d a]
  linarith

end LCJet

/-! ### `prop:spinor-prolongation` -/

section Final

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

namespace LCJet

variable {Fr : CliffordFrame ι A} (J : LCJet Fr)

/-- The covariant product rule for the mass term holds for the twisted Levi-Civita connection
when the mass operators commute with the spin rotations `c_cc_d` and are gauge equivariant. -/
theorem mass_equivariant (m0 : A) (L : W →ₗ[ℝ] A) (ρH : ι → W →ₗ[ℝ] W)
    (hMcl : ∀ w c d, mass m0 L w * (Fr.c c * Fr.c d) = Fr.c c * Fr.c d * mass m0 L w)
    (hMg : ∀ a w, J.ρ a * mass m0 L w - mass m0 L w * J.ρ a = L (ρH a w)) (a : ι) (w : W) :
    J.ω a * mass m0 L w - mass m0 L w * J.ω a = L (ρH a w) := by
  have h := commute_spinPart Fr (mass m0 L w) (hMcl w) (J.G a)
  unfold ω
  rw [add_mul, mul_add, ← h, ← hMg a w]
  abel

/-- **`prop:spinor-prolongation`, `eq:spinor-prolongation`.**  For the twisted Levi-Civita spin
connection (`LCJet`), an affine mass map `𝓜(H) = m₀ + 𝓜_H[H]` commuting with the spin rotations
and gauge equivariant, and spinor jets obeying the frame commutator relation, for every frame
index `a`
`(𝒟^{T^*}X)_a = 𝓜X_a + 𝓜_H[D_aH]Ψ + ∇_a r_D + ½ Σ_b ε_b Ric_{ab} c_bΨ + Σ_b ε_b c_b ρ(F_{ba})Ψ`,
with `Ric_{ab} = Σ_c ε_c Rm_{cabc}` the Ricci tensor of the frame curvature and `ρ(F)` the gauge
curvature (`c^b = ε_b c_b`). -/
theorem spinor_prolongation (m0 : A) (L : W →ₗ[ℝ] A) (ρH : ι → W →ₗ[ℝ] W) (h : W)
    (dh : ι → W) (ψ : V) (dψ : ι → V) (ddψ : ι → ι → V)
    (hψ : ∀ a b, ddψ a b - ddψ b a = ∑ c, lcΛ Fr.ε J.G a b c • dψ c)
    (hMcl : ∀ w c d, mass m0 L w * (Fr.c c * Fr.c d) = Fr.c c * Fr.c d * mass m0 L w)
    (hMg : ∀ a w, J.ρ a * mass m0 L w - mass m0 L w * J.ρ a = L (ρH a w)) (a : ι) :
    dTX Fr (lcΓ Fr.ε J.G) J.ω J.dω ψ dψ ddψ a =
      mass m0 L h • cov J.ω ψ dψ a + L (DH ρH h dh a) • ψ +
        covResD Fr J.ω J.dω m0 L h dh ψ dψ ddψ a +
          ((1 / 2 : ℝ) • ∑ b, (Fr.ε b * ricciOf Fr.ε J.Rm a b) • Fr.c b) • ψ +
            (∑ b, Fr.ε b • (Fr.c b * J.F b a)) • ψ := by
  rw [spinor_prolongation_general Fr (lcΛ Fr.ε J.G) (lcΓ Fr.ε J.G) J.ω J.dω m0 L ρH h dh ψ dψ
    ddψ hψ J.torsion_free J.clifford_parallel J.metric_compat
    (J.mass_equivariant m0 L ρH hMcl hMg) a]
  have hc : ∑ b, Fr.ε b • ((Fr.c b * curv (lcΛ Fr.ε J.G) J.ω J.dω b a) • ψ) =
      (∑ b, Fr.ε b • (Fr.c b * twistedCurvature Fr J.Rm J.F b a)) • ψ := by
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [J.curv_eq, smul_assoc]
    rfl
  rw [hc, twisted_half_ricci_contraction Fr J.Rm J.F (fun a b c d => J.Rm_anti₁ a b c d)
    (fun a b c d => J.Rm_anti₂ a b c d) J.Rm_bianchi' a, add_smul]
  abel

end LCJet

/-- **`eq:normal-spinor-jet`.**  In a Lorentzian Clifford frame (`ε_{0} = -1`, `ε_i = 1` for
`i ≠ 0`), if `Σ_b ε_b c_b X_b = 𝓜Ψ + r_D` (the Dirac equation with residual), then the normal
jet is algebraic: `X_0 = c_0 Σ_{i≠0} c_iX_i - c_0𝓜Ψ - c_0r_D`. -/
theorem normal_spinor_jet (Fr : CliffordFrame ι A) (i0 : ι) (hε0 : Fr.ε i0 = -1)
    (hεi : ∀ i, i ≠ i0 → Fr.ε i = 1) (X : ι → V) (Mψ r : V)
    (hD : ∑ b, Fr.ε b • (Fr.c b • X b) = Mψ + r) :
    X i0 = Fr.c i0 • ∑ i ∈ Finset.univ.erase i0, Fr.c i • X i - Fr.c i0 • Mψ - Fr.c i0 • r := by
  have hc0 : Fr.c i0 * Fr.c i0 = 1 := by
    have h := Fr.anticomm i0 i0
    simp only [↓reduceIte, hε0] at h
    have h2 : (2 : ℝ) • (Fr.c i0 * Fr.c i0) = (2 : ℝ) • (1 : A) := by
      rw [two_smul, h]; norm_num
    exact smul_right_injective A (two_ne_zero) h2
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0), hε0] at hD
  have hrest : ∑ x ∈ Finset.univ.erase i0, Fr.ε x • (Fr.c x • X x) =
      ∑ i ∈ Finset.univ.erase i0, Fr.c i • X i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hεi i (Finset.ne_of_mem_erase hi), one_smul]
  rw [hrest, neg_one_smul] at hD
  have hX : Fr.c i0 • X i0 = ∑ i ∈ Finset.univ.erase i0, Fr.c i • X i - Mψ - r := by
    rw [sub_sub, ← hD]; abel
  calc X i0 = Fr.c i0 • (Fr.c i0 • X i0) := by rw [← mul_smul, hc0, one_smul]
    _ = _ := by rw [hX, smul_sub, smul_sub]

/-- `eq:normal-spinor-jet` for the actual jets: `X_0 = c_0 Σ_{i≠0} c_iX_i - c_0𝓜Ψ - c_0r_D` with
`r_D = 𝒟Ψ - 𝓜(H)Ψ` (no derivative of the residual enters). -/
theorem normal_spinor_jet_resD (Fr : CliffordFrame ι A) (i0 : ι) (hε0 : Fr.ε i0 = -1)
    (hεi : ∀ i, i ≠ i0 → Fr.ε i = 1) (ω : ι → A) (m0 : A) (L : W →ₗ[ℝ] A) (h : W) (ψ : V)
    (dψ : ι → V) :
    cov ω ψ dψ i0 = Fr.c i0 • ∑ i ∈ Finset.univ.erase i0, Fr.c i • cov ω ψ dψ i -
      Fr.c i0 • (mass m0 L h • ψ) - Fr.c i0 • resD Fr ω m0 L h ψ dψ :=
  normal_spinor_jet Fr i0 hε0 hεi _ _ _ (by unfold resD dirac; abel)

end Final

/-! ### Non-vacuity: a Lorentzian `1+1` Clifford frame and the flat twisted connection -/

/-- `c_0 = σ_x`, `c_1 = iσ_y` (real `2 × 2` matrices): `c_0² = 1`, `c_1² = -1`, anticommuting
(`η = diag(-1, 1)`). -/
def lorentz2 : CliffordFrame (Fin 2) (Matrix (Fin 2) (Fin 2) ℝ) where
  c := ![!![0, 1; 1, 0], !![0, 1; -1, 0]]
  ε := ![-1, 1]
  sign_sq := by intro a; fin_cases a <;> norm_num
  anticomm := by
    intro a b
    fin_cases a <;> fin_cases b <;>
      ext i j <;> fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- The flat frame with vanishing gauge potential satisfies all `LCJet` hypotheses. -/
def flatLC : LCJet lorentz2 where
  G := fun _ _ _ => 0
  dG := fun _ _ _ _ => 0
  ρ := fun _ => 0
  dρ := fun _ _ => 0
  G_anti := by intros; simp
  dG_anti := by intros; simp
  ρ_comm := by intros; simp
  jacobi := by intros; simp [lcΛ, lcΓ, lcdΛ]

example : lorentz2.ε 0 = -1 ∧ lorentz2.ε 1 = 1 := by simp [lorentz2]

end

end RenewalGeometry.SpinorProlongation
