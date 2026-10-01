/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.ColourNaturalitySpectrumExact
import RenewalGeometry.StandardModel.DeterminantSkeletonPopulationExact
import RenewalGeometry.StandardModel.DeterminantIncidenceExact

/-!
# Determinant-line reconstruction and positive naturality certificate

Covers `thm:six-naturality` of the spacetime–gauge duality manuscript.

The port `𝒰 = Hom(C ⊗ W₂ ⊗ W₂, Λ²C*)` is realised in two equivalent ways:

* **coordinates** `NatPort = (Fin 3 × Fin 3) × (Fin 2 × Fin 2)`: `v ((p, a), (i, j))` is the
  coefficient of `T(c_a ⊗ w_i ⊗ w_j)` on the oriented orthonormal wedge vector `J_C c_p`
  (`ColourNaturalitySpectrumExact`), with the defect maps `portR X`, `portS Y`;
* **forms**: `formT v x ∈ Λ²C*` (antisymmetric matrices, `ω(u, v) = uᵀ ω v`), with the actions
  of `eq:naturality-actions`: `outAct X ω = −(Xᵀ ω + ω X)` (the derivation
  `φ ∧ ψ ↦ −(φ∘X) ∧ ψ − φ ∧ (ψ∘X)`), `inAct X = X ⊗ I ⊗ I`,
  `weakIn Y = I ⊗ Y ⊗ I + I ⊗ I ⊗ Y`.

`volume_infinitesimal` proves `eq:volume-infinitesimal-action`
(`J_C⁻¹ dρ_C^out(X) J_C = X − (Tr X) I`), and `formT_colourDefect`, `formT_weakDefect` prove
that the coordinate defect maps are exactly `ℛ_X T = dρ^out(X) T − T dρ^in(X)` and
`𝒮_Y T = −T dρ_W^in(Y)` (`eq:naturality-defects`) for the six generators.

Main clauses (`six_naturality` assembles them):
* `mem_natKernel_iff`, `natKernel_eq_theta`, `natTheta_injective`: the common kernel
  `𝖲_nat` of the six defect maps is `Ker H_nat`, the line `{Θ_τ}`; `shadow_natTheta` identifies
  `Θ_τ` with the determinant-incidence embedding of `DeterminantIncidenceExact`
  (`DetIncidence.theta`), whose alternation retracts it (`(det C ⊗ det W₂)*` line);
* `colourKernel_finrank` (= 4), `weakKernel_finrank` (= 9);
* `natKernel_swap`, `natKernel_vanish_sym`: weak-slot interchange acts by `−1` and the
  kernel vanishes on `C ⊗ Sym²W₂`;
* `natTheta_equivariant`: `ρ_out(g) ∘ Θ_τ = Θ_τ ∘ (g ⊗ h ⊗ h)` for `det g = det h = 1`
  (in particular `SU(C) × SU(W₂)`); `central_character`: central phases act by
  `e^{−i(3α+2β)}`;
* `T0_normalization`: `T₀*T₀ = P_alt` iff `T₀ = τ Θ₁` with `|τ|² = 1/2`; then `‖T₀‖² = 3` and
  `P_det = |T₀⟩⟩⟨⟨T₀| / 3`;
* `natDefect_gap_lower`, `natDefect_eigenvalue_two`, `natDefect_eigenvalue_mem` (spectrum file);
* `choi_leakage`, `choi_ray`, `choi_ray_trace`: the Choi clauses
  `eq:naturality-leakage`, `eq:naturality-ray`;
* `unitary_change`: for unitary changes `X ↦ U X U*`, `Y ↦ V Y V*` of the matrix-unit
  systems, the defect operator is conjugated by the induced port unitary, so the
  characteristic polynomial (spectrum) is unchanged.
-/

open Matrix Polynomial
open scoped Kronecker ComplexOrder

namespace RenewalGeometry
namespace SixNaturality

open NaturalitySpectrum DeterminantSkeleton

/-! ## Sums of squares -/

section SumSq

variable {m : Type*} [Fintype m] [DecidableEq m]

theorem star_dot_gram (A : Matrix m m ℂ) (v : m → ℂ) :
    star v ⬝ᵥ ((Aᴴ * A) *ᵥ v) = star (A *ᵥ v) ⬝ᵥ (A *ᵥ v) := by
  rw [← mulVec_mulVec, dotProduct_mulVec, star_mulVec]

/-- The kernel of `∑ A_k* A_k` is the common kernel of the `A_k`. -/
theorem sum_gram_mulVec_eq_zero_iff {ι : Type*} [Fintype ι] (A : ι → Matrix m m ℂ)
    (v : m → ℂ) : (∑ k, (A k)ᴴ * A k) *ᵥ v = 0 ↔ ∀ k, A k *ᵥ v = 0 := by
  constructor
  · intro h
    have h0 : star v ⬝ᵥ ((∑ k, (A k)ᴴ * A k) *ᵥ v) = 0 := by rw [h, dotProduct_zero]
    rw [sum_mulVec, dotProduct_sum] at h0
    simp only [star_dot_gram] at h0
    have := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => dotProduct_star_self_nonneg (A k *ᵥ v)).mp h0
    intro k
    exact dotProduct_star_self_eq_zero.mp (this k (Finset.mem_univ _))
  · intro h
    rw [sum_mulVec]
    simp [← mulVec_mulVec, h]

end SumSq

/-! ## The common kernel -/

/-- The six defect maps as one family `𝒢_C ⊔ 𝒢_W`. -/
def defectFamily : Fin 4 ⊕ Fin 2 → Matrix NatPort NatPort ℂ :=
  Sum.elim (fun k => portR (colourGen k)) (fun k => portS (weakGen k))

theorem natDefectOp_eq_family : natDefectOp = ∑ k, (defectFamily k)ᴴ * defectFamily k := by
  rw [Fintype.sum_sum_type]
  rfl

/-- The common kernel `𝖲_nat` of the six defect maps (`eq:naturality-kernel`). -/
def natKernel : Set (NatPort → ℂ) :=
  {v | (∀ k, portR (colourGen k) *ᵥ v = 0) ∧ ∀ k, portS (weakGen k) *ᵥ v = 0}

/-- **`Ker H_nat = 𝖲_nat`** (`eq:naturality-gap`, first clause). -/
theorem mem_natKernel_iff (v : NatPort → ℂ) : v ∈ natKernel ↔ natDefect *ᵥ v = 0 := by
  rw [← natDefectOp_eq_tensorSum, natDefectOp_eq_family, sum_gram_mulVec_eq_zero_iff]
  simp only [natKernel, Set.mem_setOf_eq, Sum.forall, defectFamily, Sum.elim_inl, Sum.elim_inr]

/-- The determinant-line embedding `Θ_τ = τ (I₃ ⊗ (w₁w₂ − w₂w₁))` in port coordinates. -/
def natTheta (τ : ℂ) : NatPort → ℂ := τ • natKernelVec

theorem natKernel_eq_theta (v : NatPort → ℂ) : v ∈ natKernel ↔ ∃ τ : ℂ, v = natTheta τ := by
  rw [mem_natKernel_iff, natDefect_mulVec_eq_zero_iff]
  rfl

theorem natTheta_injective : Function.Injective natTheta := by
  intro τ σ h
  have := congrFun h ((0, 0), (0, 1))
  simpa [natTheta, natKernelVec, weakAlternating] using this

/-- The common kernel is one-dimensional. -/
theorem natKernel_finrank : Module.finrank ℂ (LinearMap.ker natDefect.mulVecLin) = 1 :=
  natDefect_finrank_ker

/-- Port coordinates → determinant-incidence shadow coordinates: the wedge basis vector
`J_C c_p` is `csign p` times the shadow basis vector of `DetIncidence`. -/
def shadowOf (v : NatPort → ℂ) : DetIncidence.Shadow :=
  fun a i j p => DetIncidence.csign p * v ((p, a), (i, j))

/-- **Canonical identification with `(det C ⊗ det W₂)*`**: `Θ_τ` is the determinant-incidence
embedding `DetIncidence.theta τ`. -/
theorem shadow_natTheta (τ : ℂ) : shadowOf (natTheta τ) = DetIncidence.theta τ := by
  funext a i j p
  fin_cases a <;> fin_cases i <;> fin_cases j <;> fin_cases p <;>
    simp [shadowOf, natTheta, natKernelVec, weakAlternating, DetIncidence.theta,
      DetIncidence.csign, DetIncidence.eps2, one_apply] <;> ring

/-- The complete alternation retracts the kernel line onto the seed. -/
theorem alt_shadow_natTheta (τ : ℂ) : DetIncidence.alt (shadowOf (natTheta τ)) = τ := by
  rw [shadow_natTheta, DetIncidence.alternation_retracts]

/-! ## Colour-only and weak-only kernels -/

/-- The trivial eigenbasis of the zero operator. -/
noncomputable def zeroEigenbasis (m : Type*) [Fintype m] [DecidableEq m] :
    OrthEigenbasis (0 : Matrix m m ℂ) where
  P := 1
  N := fun _ => 1
  ev := fun _ => 0
  N_pos := fun _ => one_pos
  orth := by simp
  eig := by simp

theorem colourOnly_eq :
    ∑ k, (portR (colourGen k))ᴴ * portR (colourGen k) =
      colourDefect ⊗ₖ (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) +
        (1 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) ⊗ₖ (0 : Matrix (Fin 2 × Fin 2) _ ℂ) := by
  rw [kronecker_zero, add_zero, colourDefect, sum_kronecker_one]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [portR, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]

theorem weakOnly_eq :
    ∑ k, (portS (weakGen k))ᴴ * portS (weakGen k) =
      (0 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) ⊗ₖ
          (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) +
        (1 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) ⊗ₖ weakDefect := by
  rw [zero_kronecker, zero_add, ← weak_dual_sum, one_kronecker_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [portS, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul,
    conjTranspose_neg, neg_mul_neg]

/-- **The colour equations alone have kernel dimension four.** -/
theorem colourKernel_finrank :
    Module.finrank ℂ (LinearMap.ker
      (∑ k, (portR (colourGen k))ᴴ * portR (colourGen k)).mulVecLin) = 4 := by
  rw [colourOnly_eq, (colourEigenbasis.kroneckerSum (zeroEigenbasis _)).finrank_ker]
  have : ∀ i : NatPort, (colourEigenbasis.kroneckerSum (zeroEigenbasis _)).ev i = 0 ↔
      i.1 = (0, 0) := by
    intro i
    show colourEv i.1 + 0 = 0 ↔ _
    rw [add_zero, colourEv_eq_zero_iff]
  rw [Fintype.card_congr (Equiv.subtypeEquivRight this)]
  decide

/-- **The weak equations alone have kernel dimension nine.** -/
theorem weakKernel_finrank :
    Module.finrank ℂ (LinearMap.ker
      (∑ k, (portS (weakGen k))ᴴ * portS (weakGen k)).mulVecLin) = 9 := by
  rw [weakOnly_eq, ((zeroEigenbasis _).kroneckerSum weakEigenbasis).finrank_ker]
  have : ∀ i : NatPort, ((zeroEigenbasis _).kroneckerSum weakEigenbasis).ev i = 0 ↔
      i.2 = (1, 0) := by
    intro i
    show 0 + weakEv i.2 = 0 ↔ _
    rw [zero_add, weakEv_eq_zero_iff]
  rw [Fintype.card_congr (Equiv.subtypeEquivRight this)]
  decide

/-! ## Weak-slot interchange and symmetric vanishing -/

/-- **Swap character**: `T (I_C ⊗ τ_W) = −T` on the kernel. -/
theorem natKernel_swap {v : NatPort → ℂ} (hv : v ∈ natKernel) (p a : Fin 3) (i j : Fin 2) :
    v ((p, a), (j, i)) = - v ((p, a), (i, j)) := by
  obtain ⟨τ, rfl⟩ := (natKernel_eq_theta v).mp hv
  fin_cases i <;> fin_cases j <;> simp [natTheta, natKernelVec, weakAlternating]

/-- **Vanishing on `C ⊗ Sym²W₂`**: kernel elements kill every symmetric weak tensor. -/
theorem natKernel_vanish_sym {v : NatPort → ℂ} (hv : v ∈ natKernel) (p a : Fin 3)
    (s : Fin 2 → Fin 2 → ℂ) (hs : ∀ i j, s i j = s j i) :
    ∑ i, ∑ j, v ((p, a), (i, j)) * s i j = 0 := by
  obtain ⟨τ, rfl⟩ := (natKernel_eq_theta v).mp hv
  simp [natTheta, natKernelVec, weakAlternating, Fin.sum_univ_two, hs 1 0]


/-! ## Normalization of `T₀` -/

/-- A port vector as an operator `C ⊗ W₂ ⊗ W₂ → Λ²C*` in the orthonormal bases
`(c_a ⊗ w_i ⊗ w_j)` and `(J_C c_p)`. -/
def portMat (v : NatPort → ℂ) : Matrix (Fin 3) (Fin 3 × (Fin 2 × Fin 2)) ℂ :=
  of fun p q => v ((p, q.1), q.2)

/-- The orthogonal projector `P_alt` onto `C ⊗ Λ²W₂`:
`I_C ⊗ ½ |w₁w₂ − w₂w₁⟩⟨w₁w₂ − w₂w₁|`. -/
noncomputable def pAlt : Matrix (Fin 3 × (Fin 2 × Fin 2)) (Fin 3 × (Fin 2 × Fin 2)) ℂ :=
  (1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ ((1 / 2 : ℂ) • vecMulVec weakAlternating weakAlternating)

theorem star_weakAlternating (w : Fin 2 × Fin 2) : star (weakAlternating w) = weakAlternating w := by
  unfold weakAlternating
  split_ifs <;> simp

theorem portMat_gram (τ : ℂ) :
    (portMat (natTheta τ))ᴴ * portMat (natTheta τ) =
      (star τ * τ) • ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ
        vecMulVec weakAlternating weakAlternating) := by
  ext ⟨a, w⟩ ⟨b, w'⟩
  simp only [mul_apply, conjTranspose_apply, portMat, of_apply, natTheta, natKernelVec,
    Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, kroneckerMap_apply, vecMulVec_apply,
    star_mul', star_weakAlternating]
  simp only [one_apply, Fin.sum_univ_three]
  fin_cases a <;> fin_cases b <;> simp <;> ring

/-- **Normalization of `T₀`**: an element `Θ_τ` of the kernel line satisfies
`T₀* T₀ = P_alt` iff `|τ|² = 1/2`; then `‖T₀‖²_HS = 3` and
`P_det = |T₀⟩⟩⟨⟨T₀| / 3`. Such `T₀` exist. -/
theorem T0_normalization (τ : ℂ) :
    ((portMat (natTheta τ))ᴴ * portMat (natTheta τ) = pAlt ↔ Complex.normSq τ = 1 / 2) ∧
    (Complex.normSq τ = 1 / 2 →
      star (natTheta τ) ⬝ᵥ natTheta τ = 3 ∧
      natDetProj = (1 / 3 : ℂ) • vecMulVec (natTheta τ) (star (natTheta τ))) := by
  have hst : star τ * τ = (Complex.normSq τ : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  refine ⟨?_, ?_⟩
  · rw [portMat_gram, pAlt, kronecker_smul, hst]
    constructor
    · intro h
      have := congrFun (congrFun h (0, (0, 1))) (0, (0, 1))
      simp [kroneckerMap_apply, vecMulVec_apply, weakAlternating] at this
      apply Complex.ofReal_injective
      rw [this]
      norm_num
    · intro h
      rw [h]
      norm_num
  · intro h
    have hst' : star τ * τ = 1 / 2 := by rw [hst, h]; norm_num
    refine ⟨?_, ?_⟩
    · rw [natTheta, star_smul, smul_dotProduct, dotProduct_smul, natKernelVec_normSq, smul_eq_mul,
        smul_eq_mul, ← mul_assoc]
      rw [hst']
      norm_num
    · rw [natDetProj_eq, natTheta, star_smul, smul_vecMulVec, vecMulVec_smul, smul_smul,
        smul_smul]
      congr 1
      linear_combination (-1 / 3 : ℂ) * hst'

/-- Existence of `T₀`: `τ = 1/√2`. -/
theorem exists_T0 : ∃ τ : ℂ, Complex.normSq τ = 1 / 2 := by
  refine ⟨((Real.sqrt 2)⁻¹ : ℝ), ?_⟩
  rw [Complex.normSq_ofReal, ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-! ## Choi clauses -/

/-- **Leakage bound** (`eq:naturality-leakage`): `Tr[(I − P_det) J] ≤ d_nat / 2`. -/
theorem choi_leakage {J : Matrix NatPort NatPort ℂ} (hJ : J.PosSemidef) :
    ((1 - natDetProj) * J).trace.re ≤ branchDefect natDefect J / 2 :=
  leakage_le natDefect_gap_lower hJ

theorem natDefect_mulVec_natTheta (τ : ℂ) : natDefect *ᵥ natTheta τ = 0 :=
  (natDefect_mulVec_eq_zero_iff _).mpr ⟨τ, rfl⟩

theorem trace_vecMulVec_self (v : NatPort → ℂ) :
    (vecMulVec v (star v)).trace = star v ⬝ᵥ v := by
  have h := trace_vecMulVec_mul v 1
  rwa [Matrix.mul_one, one_mulVec] at h

/-- **Ray clause** (`eq:naturality-ray`): for `T₀ = Θ_τ` with `T₀* T₀ = P_alt`, a positive
Choi operator has zero naturality defect iff it is `x |T₀⟩⟩⟨⟨T₀|` with `x ≥ 0`. -/
theorem choi_ray {τ : ℂ} (hτ : Complex.normSq τ = 1 / 2) {J : Matrix NatPort NatPort ℂ}
    (hJ : J.PosSemidef) :
    branchDefect natDefect J = 0 ↔
      ∃ x : ℝ, 0 ≤ x ∧ J = (x : ℂ) • vecMulVec (natTheta τ) (star (natTheta τ)) := by
  have hP := (T0_normalization τ).2 hτ
  constructor
  · intro hd
    have hpure := branch_purity natDefect_gap_lower natDetProj_conjTranspose natDetProj_mul_self
      natDetProj_mul_mul natDetProj_trace hJ hd
    refine ⟨branchMass J / 3, ?_, ?_⟩
    · have := Complex.le_def.mp hJ.trace_nonneg
      simp only [Complex.zero_re] at this
      have : 0 ≤ branchMass J := this.1
      positivity
    · calc J = (branchMass J : ℂ) • natDetProj := hpure
        _ = _ := by
          rw [hP.2, smul_smul]
          congr 1
          push_cast
          ring
  · rintro ⟨x, _, rfl⟩
    simp only [branchDefect, Matrix.mul_smul, mul_vecMulVec, natDefect_mulVec_natTheta]
    simp

/-- The trace of `x |T₀⟩⟩⟨⟨T₀|` is `3x`, so `Tr J_D > 0` iff `x > 0`. -/
theorem choi_ray_trace {τ : ℂ} (hτ : Complex.normSq τ = 1 / 2) (x : ℝ) :
    ((x : ℂ) • vecMulVec (natTheta τ) (star (natTheta τ))).trace = 3 * x ∧
      (0 < branchMass ((x : ℂ) • vecMulVec (natTheta τ) (star (natTheta τ))) ↔ 0 < x) := by
  have hP := (T0_normalization τ).2 hτ
  have htr : ((x : ℂ) • vecMulVec (natTheta τ) (star (natTheta τ))).trace = 3 * x := by
    rw [trace_smul, trace_vecMulVec_self, hP.1, smul_eq_mul, mul_comm]
  refine ⟨htr, ?_⟩
  rw [branchMass, htr]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  norm_num


/-! ## The forms model: `Λ²C*`, the volume identification and the group actions -/

section Forms

/-- The Levi-Civita symbol `ε_{kab}` on `Fin 3`. -/
def levi3 : Fin 3 → Fin 3 → Fin 3 → ℂ :=
  ![![![0, 0, 0], ![0, 0, 1], ![0, -1, 0]],
    ![![0, 0, -1], ![0, 0, 0], ![1, 0, 0]],
    ![![0, 1, 0], ![-1, 0, 0], ![0, 0, 0]]]

/-- The unitary volume identification `J_C : C → Λ²C*`, `(J_C c)(u, v) = det(c, u, v)`;
a 2-form `ω` is the antisymmetric matrix with `ω(u, v) = uᵀ ω v`.  On the oriented basis,
`J_C c₁ = c² ∧ c³`, `J_C c₂ = −c¹ ∧ c³`, `J_C c₃ = c¹ ∧ c²`. -/
def volJ (c : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ := of fun a b => ∑ k, c k * levi3 k a b

/-- The infinitesimal colour action on `Λ²C*`:
`dρ_C^out(X)(φ ∧ ψ) = −(φ∘X) ∧ ψ − φ ∧ (ψ∘X)`, i.e. `ω ↦ −(Xᵀ ω + ω X)`. -/
def outAct (X : Matrix (Fin 3) (Fin 3) ℂ) (ω : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ := -(Xᵀ * ω + ω * X)

theorem outAct_wedge (X : Matrix (Fin 3) (Fin 3) ℂ) (φ ψ : Fin 3 → ℂ) :
    outAct X (vecMulVec φ ψ - vecMulVec ψ φ) =
      -((vecMulVec (Xᵀ *ᵥ φ) ψ - vecMulVec ψ (Xᵀ *ᵥ φ)) +
        (vecMulVec φ (Xᵀ *ᵥ ψ) - vecMulVec (Xᵀ *ᵥ ψ) φ)) := by
  ext a b
  simp only [outAct, Matrix.neg_apply, Matrix.add_apply, Matrix.sub_apply, mul_apply,
    vecMulVec_apply, mulVec, dotProduct, transpose_apply, Fin.sum_univ_three]
  ring

/-- **`eq:volume-infinitesimal-action`**: `J_C⁻¹ dρ_C^out(X) J_C = X − (Tr X) I_C`. -/
theorem volume_infinitesimal (X : Matrix (Fin 3) (Fin 3) ℂ) (c : Fin 3 → ℂ) :
    outAct X (volJ c) = volJ ((X - X.trace • (1 : Matrix (Fin 3) (Fin 3) ℂ)) *ᵥ c) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [outAct, volJ, levi3, mul_apply, mulVec, dotProduct, Fin.sum_univ_three, trace,
      one_apply] <;> ring

theorem volJ_add (c c' : Fin 3 → ℂ) : volJ (c + c') = volJ c + volJ c' := by
  ext a b; simp [volJ, add_mul, Finset.sum_add_distrib]

theorem volJ_smul (r : ℂ) (c : Fin 3 → ℂ) : volJ (r • c) = r • volJ c := by
  ext a b; simp [volJ, Finset.mul_sum, mul_assoc]

theorem volJ_sub (c c' : Fin 3 → ℂ) : volJ (c - c') = volJ c - volJ c' := by
  ext a b; simp [volJ, sub_mul, Finset.sum_sub_distrib]

theorem volJ_neg (c : Fin 3 → ℂ) : volJ (-c) = -volJ c := by
  ext a b; simp [volJ, Finset.sum_neg_distrib]

theorem volJ_injective : Function.Injective volJ := by
  intro c c' h
  have h0 := congrFun (congrFun h 1) 2
  have h1 := congrFun (congrFun h 0) 2
  have h2 := congrFun (congrFun h 0) 1
  simp [volJ, levi3, Fin.sum_univ_three] at h0 h1 h2
  funext k
  fin_cases k
  · exact h0
  · simpa using h1
  · exact h2

/-- The `J_C`-coordinates `t(x)_p = ∑ v((p,a),(i,j)) x(a,i,j)` of `T(x)`. -/
def tvec (v : NatPort → ℂ) (x : Fin 3 × Fin 2 × Fin 2 → ℂ) : Fin 3 → ℂ :=
  fun p => ∑ a, ∑ i, ∑ j, v ((p, a), (i, j)) * x (a, i, j)

/-- The port element as a map `T : C ⊗ W₂ ⊗ W₂ → Λ²C*`, `T(x) = J_C t(x)`. -/
def formT (v : NatPort → ℂ) (x : Fin 3 × Fin 2 × Fin 2 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  volJ (tvec v x)

/-- `formT` is faithful: the port coordinates are determined by the map. -/
theorem formT_injective {v v' : NatPort → ℂ} (h : ∀ x, formT v x = formT v' x) : v = v' := by
  funext ⟨⟨p, a⟩, ⟨i, j⟩⟩
  have := congrFun (volJ_injective (h (Pi.single (a, i, j) 1))) p
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simpa [tvec, Pi.single_apply, Prod.ext_iff, Fin.sum_univ_three, Fin.sum_univ_two] using this

/-- `dρ_C^in(X) = X ⊗ I ⊗ I`. -/
def inAct (X : Matrix (Fin 3) (Fin 3) ℂ) (x : Fin 3 × Fin 2 × Fin 2 → ℂ) :
    Fin 3 × Fin 2 × Fin 2 → ℂ :=
  fun q => ∑ b, X q.1 b * x (b, q.2.1, q.2.2)

/-- `dρ_W^in(Y) = I_C ⊗ Y ⊗ I + I_C ⊗ I ⊗ Y`. -/
def weakIn (Y : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 3 × Fin 2 × Fin 2 → ℂ) :
    Fin 3 × Fin 2 × Fin 2 → ℂ :=
  fun q => ∑ k, Y q.2.1 k * x (q.1, k, q.2.2) + ∑ l, Y q.2.2 l * x (q.1, q.2.1, l)

/-- The colour defect map `ℛ_X T = dρ_C^out(X) T − T dρ_C^in(X)` (`eq:naturality-defects`). -/
def colourDefectForm (X : Matrix (Fin 3) (Fin 3) ℂ) (v : NatPort → ℂ)
    (x : Fin 3 × Fin 2 × Fin 2 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  outAct X (formT v x) - formT v (inAct X x)

/-- The weak defect map `𝒮_Y T = −T dρ_W^in(Y)` (`eq:naturality-defects`). -/
def weakDefectForm (Y : Matrix (Fin 2) (Fin 2) ℂ) (v : NatPort → ℂ)
    (x : Fin 3 × Fin 2 × Fin 2 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  -formT v (weakIn Y x)

theorem tvec_colour (X : Matrix (Fin 3) (Fin 3) ℂ) (v : NatPort → ℂ)
    (x : Fin 3 × Fin 2 × Fin 2 → ℂ) :
    X *ᵥ tvec v x - tvec v (inAct X x) = tvec (portR X *ᵥ v) x := by
  funext p
  fin_cases p <;>
  simp only [Pi.sub_apply, tvec, inAct, mulVec, dotProduct, portR, adMat,
    Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two, kroneckerMap_apply,
    Matrix.sub_apply, one_apply, transpose_apply] <;>
  simp <;>
  ring

/-- **Coordinate form of `ℛ_X`**: for trace-free `X` (all four colour generators),
`ℛ_X T` is the port vector `portR X v`. -/
theorem formT_colourDefect (X : Matrix (Fin 3) (Fin 3) ℂ) (hX : X.trace = 0)
    (v : NatPort → ℂ) (x : Fin 3 × Fin 2 × Fin 2 → ℂ) :
    colourDefectForm X v x = formT (portR X *ᵥ v) x := by
  rw [colourDefectForm, formT, volume_infinitesimal, hX, zero_smul, sub_zero, formT, ← volJ_sub,
    tvec_colour, formT]

theorem tvec_weak (Y : Matrix (Fin 2) (Fin 2) ℂ) (v : NatPort → ℂ)
    (x : Fin 3 × Fin 2 × Fin 2 → ℂ) :
    -tvec v (weakIn Y x) = tvec (portS Y *ᵥ v) x := by
  funext p
  fin_cases p <;>
  simp only [Pi.neg_apply, tvec, weakIn, mulVec, dotProduct, portS, weakL,
    Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two, kroneckerMap_apply,
    Matrix.neg_apply, Matrix.add_apply, one_apply, transpose_apply] <;>
  simp <;>
  ring

/-- **Coordinate form of `𝒮_Y`**: `𝒮_Y T` is the port vector `portS Y v`. -/
theorem formT_weakDefect (Y : Matrix (Fin 2) (Fin 2) ℂ) (v : NatPort → ℂ)
    (x : Fin 3 × Fin 2 × Fin 2 → ℂ) :
    weakDefectForm Y v x = formT (portS Y *ᵥ v) x := by
  rw [weakDefectForm, formT, formT, ← volJ_neg, tvec_weak]

theorem colourGen_trace (k : Fin 4) : (colourGen k).trace = 0 := by
  fin_cases k <;> simp [colourGen, trace, Fin.sum_univ_three, single_apply]

/-- **The common kernel in the forms model**: `T` is annihilated by the six defect maps
`ℛ_X`, `𝒮_Y` (`eq:naturality-kernel`) iff its coordinates lie on the line `Θ_τ`. -/
theorem formKernel_iff (v : NatPort → ℂ) :
    ((∀ k x, colourDefectForm (colourGen k) v x = 0) ∧
      ∀ k x, weakDefectForm (weakGen k) v x = 0) ↔ ∃ τ : ℂ, v = natTheta τ := by
  rw [← natKernel_eq_theta]
  have hz : ∀ w : NatPort → ℂ, (∀ x, formT w x = 0) ↔ w = 0 := by
    intro w
    constructor
    · intro h
      exact formT_injective (v' := 0) fun x => by
        rw [h x]; ext; simp [formT, tvec, volJ]
    · rintro rfl x
      ext; simp [formT, tvec, volJ]
  simp only [formT_colourDefect _ (colourGen_trace _), formT_weakDefect, natKernel,
    Set.mem_setOf_eq]
  simp only [← hz]

/-- The group action on `Λ²C*`: `ρ_out(g)(φ ∧ ψ) = (φ∘g⁻¹) ∧ (ψ∘g⁻¹)`. -/
noncomputable def outGrp (g : Matrix (Fin 3) (Fin 3) ℂ) (ω : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ := (g⁻¹)ᵀ * ω * g⁻¹

/-- The source action `g ⊗ h ⊗ h` on `C ⊗ W₂ ⊗ W₂`. -/
def grpIn (g : Matrix (Fin 3) (Fin 3) ℂ) (h : Matrix (Fin 2) (Fin 2) ℂ)
    (x : Fin 3 × Fin 2 × Fin 2 → ℂ) : Fin 3 × Fin 2 × Fin 2 → ℂ :=
  fun q => ∑ b, ∑ k, ∑ l, g q.1 b * h q.2.1 k * h q.2.2 l * x (b, k, l)

theorem levi_det (g : Matrix (Fin 3) (Fin 3) ℂ) (c : Fin 3 → ℂ) :
    gᵀ * volJ (g *ᵥ c) * g = g.det • volJ c := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [volJ, levi3, mul_apply, mulVec, dotProduct, Fin.sum_univ_three, det_fin_three] <;> ring

theorem outGrp_volJ (g : Matrix (Fin 3) (Fin 3) ℂ) (hg : IsUnit g.det) (c : Fin 3 → ℂ) :
    g.det • outGrp g (volJ c) = volJ (g *ᵥ c) := by
  have h1 : (g⁻¹)ᵀ * gᵀ = 1 := by rw [← transpose_mul, mul_nonsing_inv g hg, transpose_one]
  have h2 : g * g⁻¹ = 1 := mul_nonsing_inv g hg
  rw [outGrp, ← Matrix.smul_mul, ← Matrix.mul_smul, ← levi_det]
  simp only [← Matrix.mul_assoc]
  rw [h1, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]

theorem tvec_natTheta_grpIn (τ : ℂ) (g : Matrix (Fin 3) (Fin 3) ℂ)
    (h : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 3 × Fin 2 × Fin 2 → ℂ) :
    tvec (natTheta τ) (grpIn g h x) = h.det • (g *ᵥ tvec (natTheta τ) x) := by
  funext p
  fin_cases p <;>
  simp only [tvec, grpIn, natTheta, natKernelVec, Pi.smul_apply, smul_eq_mul, mulVec,
    dotProduct, Fin.sum_univ_three, Fin.sum_univ_two, det_fin_two, one_apply] <;>
  simp [weakAlternating] <;>
  ring

/-- **Equivariance**: nonzero elements of the kernel line are
`SL(C) × SL(W₂)`-equivariant, in particular `SU(C) × SU(W₂)`-equivariant:
`ρ_out(g) ∘ Θ_τ = Θ_τ ∘ (g ⊗ h ⊗ h)`. -/
theorem natTheta_equivariant (τ : ℂ) (g : Matrix (Fin 3) (Fin 3) ℂ)
    (h : Matrix (Fin 2) (Fin 2) ℂ) (hg : g.det = 1) (hh : h.det = 1)
    (x : Fin 3 × Fin 2 × Fin 2 → ℂ) :
    outGrp g (formT (natTheta τ) x) = formT (natTheta τ) (grpIn g h x) := by
  have := outGrp_volJ g (by rw [hg]; exact isUnit_one) (tvec (natTheta τ) x)
  rw [hg, one_smul] at this
  rw [formT, this, formT, tvec_natTheta_grpIn, hh, one_smul]

theorem grpIn_scalar (lam mu : ℂ) (x : Fin 3 × Fin 2 × Fin 2 → ℂ) :
    grpIn (lam • 1) (mu • 1) x = (lam * mu * mu) • x := by
  funext ⟨a, i, j⟩
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [grpIn, Fin.sum_univ_three, Fin.sum_univ_two, one_apply] <;> ring

theorem formT_smul (v : NatPort → ℂ) (r : ℂ) (x : Fin 3 × Fin 2 × Fin 2 → ℂ) :
    formT v (r • x) = r • formT v x := by
  rw [formT, formT, ← volJ_smul]
  congr 1
  funext p
  simp only [tvec, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

/-- **Central character** (`eq:naturality-swap-character`, second clause): the central phases
`g = e^{iα} I_C`, `h = e^{iβ} I_W` act on every port element by `e^{−i(3α+2β)}`:
`ρ_out(g) ∘ T ∘ (g ⊗ h ⊗ h)⁻¹ = e^{−i(3α+2β)} T`. -/
theorem central_character (v : NatPort → ℂ) (α β : ℝ) (x : Fin 3 × Fin 2 × Fin 2 → ℂ) :
    outGrp (Complex.exp (α * Complex.I) • 1)
        (formT v (grpIn (Complex.exp (-(α * Complex.I)) • 1)
          (Complex.exp (-(β * Complex.I)) • 1) x)) =
      Complex.exp (-((3 * α + 2 * β) * Complex.I)) • formT v x := by
  set lam := Complex.exp (α * Complex.I)
  have hlam : lam ≠ 0 := Complex.exp_ne_zero _
  have hinv : (lam • (1 : Matrix (Fin 3) (Fin 3) ℂ))⁻¹ = lam⁻¹ • 1 := by
    apply Matrix.inv_eq_left_inv
    rw [smul_mul_smul_comm, Matrix.one_mul, inv_mul_cancel₀ hlam, one_smul]
  rw [grpIn_scalar, formT_smul, outGrp, hinv, transpose_smul, transpose_one]
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, smul_smul]
  congr 1
  have e1 : lam⁻¹ = Complex.exp (-(α * Complex.I)) := by rw [Complex.exp_neg]
  rw [e1, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

end Forms


/-! ## Unitary changes of the matrix-unit systems -/

section UnitaryChange

/-- The defect operator built from arbitrary colour and weak generator systems. -/
noncomputable def natDefectGen (Xs : Fin 4 → Matrix (Fin 3) (Fin 3) ℂ)
    (Ys : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) : Matrix NatPort NatPort ℂ :=
  ∑ k, (portR (Xs k))ᴴ * portR (Xs k) + ∑ k, (portS (Ys k))ᴴ * portS (Ys k)

theorem natDefectGen_std : natDefectGen colourGen weakGen = natDefect :=
  natDefectOp_eq_tensorSum

/-- Complex conjugate `Ū = (U*)ᵀ`. -/
def conjBar {n : Type*} (U : Matrix n n ℂ) : Matrix n n ℂ := (Uᴴ)ᵀ

/-- The port unitary induced by `U ∈ U(C)`, `V ∈ U(W₂)`:
`(U ⊗ Ū) ⊗ (V̄ ⊗ V̄)` on `M₃(ℂ) ⊗ (W₂ ⊗ W₂)*`. -/
def portUnitary (U : Matrix (Fin 3) (Fin 3) ℂ) (V : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix NatPort NatPort ℂ :=
  (U ⊗ₖ conjBar U) ⊗ₖ (conjBar V ⊗ₖ conjBar V)

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem conjBar_conjTranspose (U : Matrix n n ℂ) : (conjBar U)ᴴ = Uᵀ := by
  ext i j; simp [conjBar]

theorem conjBar_mul_conjTranspose {U : Matrix n n ℂ} (hU : U * Uᴴ = 1) :
    conjBar U * (conjBar U)ᴴ = 1 := by
  rw [conjBar_conjTranspose, conjBar, ← transpose_mul, hU, transpose_one]

theorem conjTranspose_mul_conjBar {U : Matrix n n ℂ} (hU : Uᴴ * U = 1) :
    (conjBar U)ᴴ * conjBar U = 1 := by
  rw [conjBar_conjTranspose, conjBar, ← transpose_mul, hU, transpose_one]

theorem kron_conj {a b : Type*} [Fintype a] [Fintype b] (A M : Matrix a a ℂ)
    (B N : Matrix b b ℂ) :
    (A ⊗ₖ B) * (M ⊗ₖ N) * (A ⊗ₖ B)ᴴ = (A * M * Aᴴ) ⊗ₖ (B * N * Bᴴ) := by
  rw [conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul]

theorem adMat_conj {U : Matrix (Fin 3) (Fin 3) ℂ} (hU : U * Uᴴ = 1)
    (X : Matrix (Fin 3) (Fin 3) ℂ) :
    adMat (U * X * Uᴴ) = (U ⊗ₖ conjBar U) * adMat X * (U ⊗ₖ conjBar U)ᴴ := by
  rw [adMat, adMat, Matrix.mul_sub, Matrix.sub_mul, kron_conj, kron_conj, Matrix.mul_one,
    Matrix.mul_one, hU, conjBar_mul_conjTranspose hU]
  congr 2
  rw [conjBar_conjTranspose, conjBar, transpose_mul, transpose_mul, Matrix.mul_assoc]

theorem weakL_conj {V : Matrix (Fin 2) (Fin 2) ℂ} (hV : V * Vᴴ = 1)
    (Y : Matrix (Fin 2) (Fin 2) ℂ) :
    weakL (V * Y * Vᴴ) = (V ⊗ₖ V) * weakL Y * (V ⊗ₖ V)ᴴ := by
  rw [weakL, weakL, Matrix.mul_add, Matrix.add_mul, kron_conj, kron_conj, Matrix.mul_one, hV]

theorem portR_conj {U : Matrix (Fin 3) (Fin 3) ℂ} {V : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U * Uᴴ = 1) (hV : V * Vᴴ = 1) (X : Matrix (Fin 3) (Fin 3) ℂ) :
    portR (U * X * Uᴴ) = portUnitary U V * portR X * (portUnitary U V)ᴴ := by
  rw [portR, portR, portUnitary, kron_conj, Matrix.mul_one, ← adMat_conj hU,
    conjTranspose_kronecker, ← mul_kronecker_mul, conjBar_mul_conjTranspose hV, one_kronecker_one]

theorem portS_conj {U : Matrix (Fin 3) (Fin 3) ℂ} {V : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U * Uᴴ = 1) (hV : V * Vᴴ = 1) (Y : Matrix (Fin 2) (Fin 2) ℂ) :
    portS (V * Y * Vᴴ) = portUnitary U V * portS Y * (portUnitary U V)ᴴ := by
  rw [portS, portS, portUnitary, kron_conj, Matrix.mul_one, conjTranspose_kronecker,
    ← mul_kronecker_mul, conjBar_mul_conjTranspose hU, hU, one_kronecker_one, weakL_conj hV,
    Matrix.mul_neg, Matrix.neg_mul]
  congr 2
  rw [transpose_mul, transpose_mul, conjTranspose_kronecker, conjTranspose_kronecker,
    conjBar_conjTranspose, ← kroneckerMap_transpose, Matrix.mul_assoc]
  rfl

theorem portUnitary_conjTranspose_mul {U : Matrix (Fin 3) (Fin 3) ℂ}
    {V : Matrix (Fin 2) (Fin 2) ℂ} (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    (portUnitary U V)ᴴ * portUnitary U V = 1 := by
  rw [portUnitary, conjTranspose_kronecker, conjTranspose_kronecker, conjTranspose_kronecker,
    ← mul_kronecker_mul, ← mul_kronecker_mul, ← mul_kronecker_mul, hU,
    conjTranspose_mul_conjBar hU, conjTranspose_mul_conjBar hV, one_kronecker_one,
    one_kronecker_one, one_kronecker_one]

theorem gram_conj {W R : Matrix NatPort NatPort ℂ} (hW : Wᴴ * W = 1) :
    (W * R * Wᴴ)ᴴ * (W * R * Wᴴ) = W * (Rᴴ * R) * Wᴴ := by
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Wᴴ W, hW, Matrix.one_mul]

/-- **Transport of `H_nat`**: under unitary changes `X ↦ U X U*`, `Y ↦ V Y V*` of the
matrix-unit systems, the defect operator is conjugated by the port unitary. -/
theorem natDefectGen_conj {U : Matrix (Fin 3) (Fin 3) ℂ} {V : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1) (hV : Vᴴ * V = 1) (hV' : V * Vᴴ = 1)
    (Xs : Fin 4 → Matrix (Fin 3) (Fin 3) ℂ) (Ys : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) :
    natDefectGen (fun k => U * Xs k * Uᴴ) (fun k => V * Ys k * Vᴴ) =
      portUnitary U V * natDefectGen Xs Ys * (portUnitary U V)ᴴ := by
  have hW := portUnitary_conjTranspose_mul hU hV
  simp only [natDefectGen, portR_conj hU' hV', portS_conj hU' hV', gram_conj hW,
    Matrix.mul_add, Matrix.add_mul, Finset.mul_sum, Finset.sum_mul]

/-- **Unitary invariance (`thm:six-naturality`, last clause).**  For unitary changes of the
colour and weak matrix-unit systems, the transported defect operator has the same
characteristic polynomial (spectrum), its kernel is the transported line, the transported
selector still satisfies the gap, and the scalar certificates `m`, `d_nat`, `m_D` of a
simultaneously transported Choi operator are unchanged. -/
theorem unitary_change {U : Matrix (Fin 3) (Fin 3) ℂ} {V : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1) (hV : Vᴴ * V = 1) (hV' : V * Vᴴ = 1) :
    let H' := natDefectGen (fun k => U * colourGen k * Uᴴ) (fun k => V * weakGen k * Vᴴ)
    let W := portUnitary U V
    H'.charpoly = natDefect.charpoly ∧
      (∀ v, H' *ᵥ v = 0 ↔ ∃ τ : ℂ, v = W *ᵥ natTheta τ) ∧
      (H' - (2 : ℂ) • (1 - W * natDetProj * Wᴴ)).PosSemidef ∧
      ∀ J : Matrix NatPort NatPort ℂ,
        branchMass (W * J * Wᴴ) = branchMass J ∧
        branchDefect H' (W * J * Wᴴ) = branchDefect natDefect J ∧
        branchDet (W * natDetProj * Wᴴ) (W * J * Wᴴ) = branchDet natDetProj J := by
  intro H' W
  have hW : Wᴴ * W = 1 := portUnitary_conjTranspose_mul hU hV
  have hW' : W * Wᴴ = 1 := mul_eq_one_comm.mp hW
  have hH : H' = W * natDefect * Wᴴ := by
    show natDefectGen _ _ = _
    rw [natDefectGen_conj hU hU' hV hV', natDefectGen_std]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hH, Matrix.mul_assoc, Matrix.charpoly_mul_comm, Matrix.mul_assoc, hW, Matrix.mul_one]
  · intro v
    rw [hH]
    constructor
    · intro h
      have h2 : natDefect *ᵥ (Wᴴ *ᵥ v) = 0 := by
        have := congrArg (fun z => Wᴴ *ᵥ z) h
        simp only [mulVec_mulVec, mulVec_zero] at this
        rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, hW, Matrix.one_mul, ← mulVec_mulVec] at this
      obtain ⟨τ, hτ⟩ := (natDefect_mulVec_eq_zero_iff _).mp h2
      refine ⟨τ, ?_⟩
      rw [natTheta, ← hτ, mulVec_mulVec, hW', one_mulVec]
    · rintro ⟨τ, rfl⟩
      rw [mulVec_mulVec, Matrix.mul_assoc (W * natDefect), hW, Matrix.mul_one, ← mulVec_mulVec,
        natDefect_mulVec_natTheta, mulVec_zero]
  · have h := (unitary_invariance (H := natDefect) (P := natDetProj) hW 1).2.2.2.1
      natDefect_gap_lower
    rw [hH]
    exact h
  · intro J
    have h := unitary_invariance (H := natDefect) (P := natDetProj) hW J
    rw [hH]
    exact ⟨h.1, h.2.1, h.2.2.1⟩

end UnitaryChange


/-! ## Assembly -/

/-- **Determinant-line reconstruction and positive naturality certificate
(`thm:six-naturality`).**
1. The common kernel `𝖲_nat` of the six defect maps (coordinates, and the forms model
   `ℛ_X T = dρ^out(X)T − T dρ^in(X)`, `𝒮_Y T = −T dρ_W^in(Y)`) is the line `{Θ_τ}`;
   `τ ↦ Θ_τ` is injective, `Θ_τ` is the determinant-incidence embedding and the complete
   alternation retracts it (canonical isomorphism with `(det C ⊗ det W₂)*`); `dim = 1`.
2. Nonzero kernel elements are `SL(C) × SL(W₂)`- (hence `SU(C) × SU(W₂)`-) equivariant,
   vanish on `C ⊗ Sym²W₂`, change sign under weak-slot interchange, and central phases act by
   `e^{−i(3α+2β)}`.
3. The colour equations alone have kernel dimension 4 and the weak equations alone 9.
4. `T₀ = Θ_τ` has `T₀*T₀ = P_alt` iff `|τ|² = 1/2`; then `‖T₀‖² = 3` and
   `P_det = |T₀⟩⟩⟨⟨T₀|/3`; such `T₀` exist.
5. `Ker H_nat = 𝖲_nat`, `H_nat ⪰ 2 (I − P_det)`, and `λ_min⁺(H_nat) = 2`.
6. For every positive Choi operator: `Tr[(I − P_det) J] ≤ d_nat/2`; `d_nat = 0` iff
   `J = x |T₀⟩⟩⟨⟨T₀|` with `x ≥ 0`; and then `Tr J > 0` iff `x > 0`.
The unitary-invariance clause is `unitary_change`. -/
theorem six_naturality :
    (∀ v, v ∈ natKernel ↔ ∃ τ : ℂ, v = natTheta τ) ∧ Function.Injective natTheta ∧
    (∀ τ, shadowOf (natTheta τ) = DetIncidence.theta τ ∧
      DetIncidence.alt (shadowOf (natTheta τ)) = τ) ∧
    Module.finrank ℂ (LinearMap.ker natDefect.mulVecLin) = 1 ∧
    (∀ v, ((∀ k x, colourDefectForm (colourGen k) v x = 0) ∧
      ∀ k x, weakDefectForm (weakGen k) v x = 0) ↔ ∃ τ : ℂ, v = natTheta τ) ∧
    (∀ τ (g : Matrix (Fin 3) (Fin 3) ℂ) (h : Matrix (Fin 2) (Fin 2) ℂ), g.det = 1 → h.det = 1 →
      ∀ x, outGrp g (formT (natTheta τ) x) = formT (natTheta τ) (grpIn g h x)) ∧
    (∀ v ∈ natKernel, ∀ (p a : Fin 3) (i j : Fin 2), v ((p, a), (j, i)) = - v ((p, a), (i, j))) ∧
    (∀ v ∈ natKernel, ∀ (p a : Fin 3) (s : Fin 2 → Fin 2 → ℂ), (∀ i j, s i j = s j i) →
      ∑ i, ∑ j, v ((p, a), (i, j)) * s i j = 0) ∧
    (∀ (v : NatPort → ℂ) (α β : ℝ) x,
      outGrp (Complex.exp (α * Complex.I) • 1)
          (formT v (grpIn (Complex.exp (-(α * Complex.I)) • 1)
            (Complex.exp (-(β * Complex.I)) • 1) x)) =
        Complex.exp (-((3 * α + 2 * β) * Complex.I)) • formT v x) ∧
    Module.finrank ℂ (LinearMap.ker
      (∑ k, (portR (colourGen k))ᴴ * portR (colourGen k)).mulVecLin) = 4 ∧
    Module.finrank ℂ (LinearMap.ker
      (∑ k, (portS (weakGen k))ᴴ * portS (weakGen k)).mulVecLin) = 9 ∧
    (∀ τ : ℂ, (portMat (natTheta τ))ᴴ * portMat (natTheta τ) = pAlt ↔
      Complex.normSq τ = 1 / 2) ∧
    (∀ τ : ℂ, Complex.normSq τ = 1 / 2 →
      star (natTheta τ) ⬝ᵥ natTheta τ = 3 ∧
      natDetProj = (1 / 3 : ℂ) • vecMulVec (natTheta τ) (star (natTheta τ))) ∧
    (∃ τ : ℂ, Complex.normSq τ = 1 / 2) ∧
    (∀ v, v ∈ natKernel ↔ natDefect *ᵥ v = 0) ∧
    (natDefect - (2 : ℂ) • (1 - natDetProj)).PosSemidef ∧
    (∃ v : NatPort → ℂ, v ≠ 0 ∧ natDefect *ᵥ v = (2 : ℂ) • v) ∧
    (∀ (μ : ℂ) (v : NatPort → ℂ), v ≠ 0 → natDefect *ᵥ v = μ • v →
      μ = 0 ∨ ∃ r : ℝ, μ = r ∧ 2 ≤ r ∧ r ≤ 10) ∧
    (∀ J : Matrix NatPort NatPort ℂ, J.PosSemidef →
      ((1 - natDetProj) * J).trace.re ≤ branchDefect natDefect J / 2) ∧
    (∀ τ : ℂ, Complex.normSq τ = 1 / 2 → ∀ J : Matrix NatPort NatPort ℂ, J.PosSemidef →
      (branchDefect natDefect J = 0 ↔
        ∃ x : ℝ, 0 ≤ x ∧ J = (x : ℂ) • vecMulVec (natTheta τ) (star (natTheta τ)))) ∧
    (∀ τ : ℂ, Complex.normSq τ = 1 / 2 → ∀ x : ℝ,
      (0 < branchMass ((x : ℂ) • vecMulVec (natTheta τ) (star (natTheta τ))) ↔ 0 < x)) :=
  ⟨natKernel_eq_theta, natTheta_injective,
    fun τ => ⟨shadow_natTheta τ, alt_shadow_natTheta τ⟩, natKernel_finrank, formKernel_iff,
    fun τ g h hg hh x => natTheta_equivariant τ g h hg hh x,
    fun _ hv p a i j => natKernel_swap hv p a i j,
    fun _ hv p a s hs => natKernel_vanish_sym hv p a s hs,
    central_character, colourKernel_finrank, weakKernel_finrank,
    fun τ => (T0_normalization τ).1, fun τ => (T0_normalization τ).2, exists_T0,
    mem_natKernel_iff, natDefect_gap_lower, natDefect_eigenvalue_two,
    fun _ _ hv hμ => natDefect_eigenvalue_mem hv hμ, fun _ hJ => choi_leakage hJ,
    fun _ hτ _ hJ => choi_ray hτ hJ, fun _ hτ x => (choi_ray_trace hτ x).2⟩

end SixNaturality
end RenewalGeometry
