/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.LinearTransportSecondOrderExpansion
import RenewalGeometry.DiscreteAnalysis.CovariantWilsonCoreConsistencyExact
import RenewalGeometry.Spectralization.DensitySymmetricSpinDiracExact

/-!
# Exact spin parallel transport links and the geometric core estimate

Paper `predictive_spectral_geometry`, `lem:supp-general-core` (ingredients (c) and (e) of its
proof) and `eq:supp-covariant-differences`.

* `IsExactInverseTransport h U Ω`: the link `U_j(x)` is *exact inverse spin parallel transport*
  along the lattice edge `hx → hx + h e_j`: `U_j(x) = Φ(h)` where `Φ' = Φ Ω_j(hx + t e_j)`,
  `Φ(0) = I` (the inverse of the transport `P' = -Ω P`).
* `linkExpansion_of_exactTransport`: for an anti-Hermitian connection with
  `ConnectionBounds Ω B₀ B₁` (bounded and Lipschitz), exact transport links satisfy the
  second-order expansion `LinkExpansion` (`U_j = I + h Ω_j + O(h²)`, `U_j^* = I - h Ω_j + O(h²)`)
  with the explicit constant `(N + 1)(B₀² ‖I‖ e^{B₀} + B₁)` for `0 < h ≤ 1`.  This derives the
  hypothesis `LinkExpansion` of `CovariantWilsonCoreConsistency` from the paper's definition of
  the links (`LinearTransport.norm_transport_sub_le`).
* `norm_covariantWilson_sample_sub_geometricDirac_le`: combined with
  `lem:supp-density-symmetric` (`densitySymmetric_identity`), the covariant Wilson operator with
  exact transport links applied to point samples of a `C³` spinor is `O(h)`-close, pointwise at
  the lattice points, to the density-conjugated geometric Dirac operator
  `ρ^{1/2} D_g ρ^{-1/2}` with the Levi-Civita spin connection of the frame.
* `exactTransport_exp`: non-vacuity — for a constant anti-Hermitian connection the links
  `U = exp(h Ω)` are exact transport.

Still open for `lem:supp-general-core` as stated: the `L²` form of the estimate with Sobolev
norms `‖ψ‖_{H³}`, `‖ψ‖_{H²}` and cell-average sampling `S_h = (𝒥⁰_h)^*` (the estimates here are
pointwise, with `C³` bounds and point sampling).
-/

open Matrix Set Real Filter
open scoped Matrix.Norms.Operator

namespace RenewalGeometry.ExactSpinTransport

open CovariantWilsonCoreConsistency FrozenWilsonCoreConsistency LinearTransport

variable {d N : ℕ}

/-- **Exact inverse spin parallel transport links** (`eq:supp-covariant-differences`): for every
direction `j` and lattice point `x`, `U_j(x) = Φ(h)` where `Φ` solves
`Φ'(t) = Φ(t) Ω_j(hx + t e_j)`, `Φ(0) = I`. -/
def IsExactInverseTransport (h : ℝ) (U : Links d N) (Ω : Coefficients d N) : Prop :=
  ∀ (j : Fin d) (x : Fin d → ℤ), ∃ Φ : ℝ → Matrix (Fin N) (Fin N) ℂ, Φ 0 = 1 ∧
    (∀ t, HasDerivAt Φ (Φ t * Ω j (latticePoint h x + t • dir j)) t) ∧ U j x = Φ h

/-- Entries are bounded by the `ℓ^∞` operator norm. -/
theorem norm_entry_le (M : Matrix (Fin N) (Fin N) ℂ) (i k : Fin N) : ‖M i k‖ ≤ ‖M‖ := by
  classical
  have h1 : ‖M *ᵥ Pi.single k (1 : ℂ)‖ ≤ ‖M‖ * ‖(Pi.single k (1 : ℂ) : Fin N → ℂ)‖ :=
    linfty_opNorm_mulVec M _
  have h2 : ‖(Pi.single k (1 : ℂ) : Fin N → ℂ)‖ = 1 := by
    rw [Pi.norm_single, norm_one]
  have h3 : ‖(M *ᵥ Pi.single k (1 : ℂ)) i‖ ≤ ‖M *ᵥ Pi.single k (1 : ℂ)‖ := norm_le_pi_norm _ i
  rw [mulVec_single_one] at h3 h1
  rw [h2, mul_one] at h1
  simp only [col_apply] at h3
  exact h3.trans h1

/-- `‖Mᴴ v‖_∞ ≤ N ‖M‖ ‖v‖_∞` for the `ℓ^∞` operator norm. -/
theorem norm_conjTranspose_mulVec_le (M : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) :
    ‖Mᴴ *ᵥ v‖ ≤ N * ‖M‖ * ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  simp only [mulVec, dotProduct, conjTranspose_apply, RCLike.star_def]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k, ‖(starRingEnd ℂ) (M k i) * v k‖ ≤ ∑ _k : Fin N, ‖M‖ * ‖v‖ := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul (norm_entry_le M k i) (norm_le_pi_norm v k) (norm_nonneg _)
          (norm_nonneg _)
    _ = N * ‖M‖ * ‖v‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- An operator bound for `M *ᵥ ·` bounds the `ℓ^∞` operator norm. -/
theorem norm_le_of_mulVec_le (M : Matrix (Fin N) (Fin N) ℂ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ v : Fin N → ℂ, ‖M *ᵥ v‖ ≤ B * ‖v‖) : ‖M‖ ≤ B := by
  rw [linfty_opNorm_eq_opNorm]
  exact ContinuousLinearMap.opNorm_le_bound _ hB h

/-- The constant of `linkExpansion_of_exactTransport`. -/
noncomputable def transportConstant (N : ℕ) (B0 B1 : ℝ) : ℝ :=
  (N + 1) * (B0 ^ 2 * ‖(1 : Matrix (Fin N) (Fin N) ℂ)‖ * exp B0 + B1)

/-- **Exact inverse spin parallel transport has the second-order link expansion**
`U_j(x) = I + h Ω_j(hx) + O(h²)` and `U_j(x)^* = I - h Ω_j(hx) + O(h²)` (for an anti-Hermitian,
bounded and Lipschitz connection, `0 < h ≤ 1`). -/
theorem linkExpansion_of_exactTransport (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1) (U : Links d N)
    (Ω : Coefficients d N) (B0 B1 : ℝ) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1)
    (hΩ : ConnectionBounds Ω B0 B1) (hanti : ∀ j y, (Ω j y)ᴴ = -Ω j y)
    (hU : IsExactInverseTransport h U Ω) :
    LinkExpansion h U Ω (transportConstant N B0 B1) := by
  intro j x v
  obtain ⟨Φ, hΦ0, hΦ, hUx⟩ := hU j x
  set Ωt : ℝ → Matrix (Fin N) (Fin N) ℂ := fun t => Ω j (latticePoint h x + t • dir j)
  have hΩt0 : Ωt 0 = Ω j (latticePoint h x) := by simp [Ωt]
  have hbound : ∀ t ∈ Icc 0 h, ‖Ωt t‖ ≤ B0 := fun t _ =>
    norm_le_of_mulVec_le _ hB0 fun w => hΩ.1 j _ w
  have hlip : ∀ t ∈ Icc 0 h, ‖Ωt t - Ωt 0‖ ≤ B1 * t := by
    intro t ht
    refine norm_le_of_mulVec_le _ (by nlinarith [ht.1]) fun w => ?_
    have := hΩ.2 j (latticePoint h x + t • dir j) (latticePoint h x) w
    simp only [add_sub_cancel_left, norm_smul, norm_dir, mul_one, Real.norm_eq_abs,
      abs_of_nonneg ht.1] at this
    simpa [Ωt] using this
  have key := norm_transport_sub_le hh.le hB0 hB1 hbound hlip hΦ0 hΦ
  set K := B0 ^ 2 * ‖(1 : Matrix (Fin N) (Fin N) ℂ)‖ * exp B0 + B1 with hK
  have hK0 : 0 ≤ K := by positivity
  have hexp : exp (B0 * h) ≤ exp B0 := exp_le_exp.2 (by nlinarith)
  have key' : ‖Φ h - 1 - h • Ωt 0‖ ≤ K * h ^ 2 := by
    refine key.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
    have : B0 ^ 2 * ‖(1 : Matrix (Fin N) (Fin N) ℂ)‖ * exp (B0 * h) ≤
        B0 ^ 2 * ‖(1 : Matrix (Fin N) (Fin N) ℂ)‖ * exp B0 :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    linarith
  have hsmul : (h : ℂ) • Ω j (latticePoint h x) = h • Ωt 0 := by
    rw [hΩt0, Complex.coe_smul]
  set M := U j x - 1 - (h : ℂ) • Ω j (latticePoint h x) with hM
  have hMn : ‖M‖ ≤ K * h ^ 2 := by
    rw [hM, hsmul, hUx]; exact key'
  have hN1 : K * h ^ 2 ≤ transportConstant N B0 B1 * h ^ 2 := by
    rw [transportConstant, ← hK]
    have h1 : (1 : ℝ) ≤ N + 1 := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    have h2 : 0 ≤ K * h ^ 2 := mul_nonneg hK0 (sq_nonneg h)
    calc K * h ^ 2 = 1 * (K * h ^ 2) := (one_mul _).symm
      _ ≤ (N + 1) * (K * h ^ 2) := mul_le_mul_of_nonneg_right h1 h2
      _ = (N + 1) * K * h ^ 2 := by ring
  have hN2 : N * (K * h ^ 2) ≤ transportConstant N B0 B1 * h ^ 2 := by
    rw [transportConstant, ← hK]
    have h2 : 0 ≤ K * h ^ 2 := mul_nonneg hK0 (sq_nonneg h)
    calc (N : ℝ) * (K * h ^ 2) ≤ (N + 1) * (K * h ^ 2) :=
          mul_le_mul_of_nonneg_right (by linarith) h2
      _ = (N + 1) * K * h ^ 2 := by ring
  constructor
  · calc ‖M *ᵥ v‖ ≤ ‖M‖ * ‖v‖ := linfty_opNorm_mulVec M v
      _ ≤ K * h ^ 2 * ‖v‖ := mul_le_mul_of_nonneg_right hMn (norm_nonneg _)
      _ ≤ transportConstant N B0 B1 * h ^ 2 * ‖v‖ :=
          mul_le_mul_of_nonneg_right hN1 (norm_nonneg _)
  · have hadj : (U j x)ᴴ - 1 + (h : ℂ) • Ω j (latticePoint h x) = Mᴴ := by
      rw [hM, conjTranspose_sub, conjTranspose_sub, conjTranspose_one, conjTranspose_smul,
        hanti, Complex.star_def, Complex.conj_ofReal, smul_neg, sub_neg_eq_add]
    rw [hadj]
    calc ‖Mᴴ *ᵥ v‖ ≤ N * ‖M‖ * ‖v‖ := norm_conjTranspose_mulVec_le M v
      _ ≤ N * (K * h ^ 2) * ‖v‖ := by gcongr
      _ ≤ transportConstant N B0 B1 * h ^ 2 * ‖v‖ :=
          mul_le_mul_of_nonneg_right hN2 (norm_nonneg _)

/-- **Non-vacuity**: for a constant anti-Hermitian connection `Ω`, the links `U = exp(h Ω)` are
exact inverse spin parallel transport. -/
theorem exactTransport_exp (h : ℝ) (Ω₀ : Fin d → Matrix (Fin N) (Fin N) ℂ) :
    IsExactInverseTransport h (fun j _ => NormedSpace.exp (h • Ω₀ j)) (fun j _ => Ω₀ j) := by
  intro j x
  refine ⟨fun t => NormedSpace.exp (t • Ω₀ j), by simp, fun t => ?_, rfl⟩
  exact hasDerivAt_exp_smul_const (Ω₀ j) t

/-- **Non-vacuity of `linkExpansion_of_exactTransport`**: the constant anti-Hermitian connection
`Ω_j = i I` on `ℂ²` in dimension two, with the exact links `U = exp(i h I)`. -/
example (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1) :
    LinkExpansion h
      (fun (_ : Fin 2) _ => NormedSpace.exp (h • (Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ))))
      (fun _ _ => Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ)) (transportConstant 2 1 0) := by
  refine linkExpansion_of_exactTransport h hh hh1 _ _ 1 0 zero_le_one le_rfl ⟨fun j y v => ?_,
    fun j y z v => by simp⟩ (fun j y => ?_) (exactTransport_exp h fun _ => Complex.I • 1)
  · rw [smul_mulVec, one_mulVec, norm_smul, Complex.norm_I, one_mul]
  · rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_I, neg_smul]

/-- **`lem:supp-general-core`, geometric pointwise form**: the covariant doubled Wilson operator
with *exact* spin parallel transport links and the Clifford coefficients `c^j = E_a^j γ_a` of
the frame, applied to the point samples of a `C³` spinor `ψ`, is `O(h)`-close at every lattice
point to the density-conjugated geometric Dirac operator `ρ^{1/2} D_g (ρ^{-1/2} ψ)` with the
Levi-Civita spin connection, for `0 < h ≤ 1` (constant explicit in the `C³` bounds). -/
theorem norm_covariantWilson_sample_sub_geometricDirac_le (h ϖ : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
    (E e : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ) (γ : Fin d → Matrix (Fin N) (Fin N) ℂ)
    (U : Links d N) (Γ : Matrix (Fin N) (Fin N) ℂ) (B0 B1 C0 : ℝ) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1)
    (hC0 : 0 ≤ C0)
    (hΩ : ConnectionBounds (DensitySymmetricSpinDirac.spinConnectionField E e γ) B0 B1)
    (hanti : ∀ j y, (DensitySymmetricSpinDirac.spinConnectionField E e γ j y)ᴴ =
      -DensitySymmetricSpinDirac.spinConnectionField E e γ j y)
    (hU : IsExactInverseTransport h U (DensitySymmetricSpinDirac.spinConnectionField E e γ))
    (hc0 : ∀ j y, matBound (DensitySymmetricSpinDirac.cliffordField E γ j y) ≤ C0)
    {Q : Set (Fin d → ℝ)} (hQ : IsOpen Q) (x : Fin d → ℤ) (hx : latticePoint h x ∈ Q)
    (hEe : ∀ y ∈ Q, E y * e y = 1)
    (hE : ∀ a b, DifferentiableAt ℝ (fun y => E y a b) (latticePoint h x))
    (he : ∀ a b, DifferentiableAt ℝ (fun y => e y a b) (latticePoint h x))
    (hdet : 0 < (e (latticePoint h x)).det) (hγ : DensitySymmetricSpinDirac.IsClifford γ)
    (ψ : (Fin d → ℝ) → (Fin N → ℂ)) (hψ : ContDiff ℝ 3 ψ) (M₀ M₁ M₂ M₃ : ℝ)
    (hM0 : ∀ y, ‖ψ y‖ ≤ M₀) (hM1 : ∀ y, ‖iteratedFDeriv ℝ 1 ψ y‖ ≤ M₁)
    (hM2 : ∀ y, ‖iteratedFDeriv ℝ 2 ψ y‖ ≤ M₂) (hM3 : ∀ y, ‖iteratedFDeriv ℝ 3 ψ y‖ ≤ M₃)
    (hcψ : ∀ j, ContDiff ℝ 3 (fun z => DensitySymmetricSpinDirac.cliffordField E γ j z *ᵥ ψ z))
    (M'₀ M'₁ M'₃ : ℝ)
    (hM'0 : ∀ j y, ‖DensitySymmetricSpinDirac.cliffordField E γ j y *ᵥ ψ y‖ ≤ M'₀)
    (hM'1 : ∀ j y, ‖iteratedFDeriv ℝ 1
      (fun z => DensitySymmetricSpinDirac.cliffordField E γ j z *ᵥ ψ z) y‖ ≤ M'₁)
    (hM'3 : ∀ j y, ‖iteratedFDeriv ℝ 3
      (fun z => DensitySymmetricSpinDirac.cliffordField E γ j z *ᵥ ψ z) y‖ ≤ M'₃) :
    ‖covariantWilson h ϖ (DensitySymmetricSpinDirac.cliffordField E γ) U Γ (sample h ψ) x -
        ((DensitySymmetricSpinDirac.halfDensity e (latticePoint h x) : ℝ) : ℂ) •
          DensitySymmetricSpinDirac.geometricDirac E e γ
            (fun y => (((DensitySymmetricSpinDirac.halfDensity e y)⁻¹ : ℝ) : ℂ) • ψ y)
            (latticePoint h x)‖ ≤
      h * coreConstant d C0
        (covariantConsistencyConstant M₀ M₁ M₃ B0 B1 (transportConstant N B0 B1))
        (covariantConsistencyConstant M'₀ M'₁ M'₃ B0 B1 (transportConstant N B0 B1))
        (wilsonConsistencyConstant M₀ M₁ M₂ B0 B1 (transportConstant N B0 B1)) ϖ
        (matBound Γ) := by
  have hCU : 0 ≤ transportConstant N B0 B1 := by unfold transportConstant; positivity
  rw [DensitySymmetricSpinDirac.densitySymmetric_identity (E := E) (e := e) (γ := γ) hQ hx hEe
    hE he hdet hγ ψ
    ((hψ.differentiable (by norm_num)).differentiableAt)]
  exact norm_covariantWilson_sample_sub_densitySymmetricDirac_le h ϖ hh hh1 _ U _ Γ
    (transportConstant N B0 B1) B0 B1 C0 hCU hB0 hB1 hC0
    (linkExpansion_of_exactTransport h hh hh1 U _ B0 B1 hB0 hB1 hΩ hanti hU) hΩ hc0 ψ hψ
    M₀ M₁ M₂ M₃ hM0 hM1 hM2 hM3 hcψ M'₀ M'₁ M'₃ hM'0 hM'1 hM'3 x

end RenewalGeometry.ExactSpinTransport
