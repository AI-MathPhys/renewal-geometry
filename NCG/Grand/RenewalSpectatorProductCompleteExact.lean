/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SpectatorProduct
import NCG.Grand.TwoStateRenewalDecay
import NCG.Grand.RenewalProductAFQuasilocalExact

/-!
# Complete spectator and independent-cell renewal regulators

This file closes the clauses of `thm:renewal-spectator-product` that were
previously only disclosed:

* the partial-trace identity for an arbitrary correlated bipartite matrix,
  not merely an elementary tensor;
* exact `m`-cell Walsh diagonalization and the volume-independent
  `7/15` nonconstant spectral factor;
* injectivity of the full tensorized Walsh response panel, hence predictive
  rank exactly `2^m`;
* the faithful countable AF/quasilocal product state; and
* impossibility of a finite-dimensional carrier faithfully containing all
  labelled finite screens.
-/

open Matrix Finset
open scoped Kronecker

namespace NCG
namespace RenewalSpectatorProduct

noncomputable section

variable {A K : Type*} [Fintype A] [Fintype K]
  [DecidableEq A] [DecidableEq K]

/-- The spectator block of a bipartite matrix at active indices `a,b`. -/
def spectatorBlock (X : Matrix (A × K) (A × K) ℂ) (a b : A) :
    Matrix K K ℂ :=
  Matrix.of fun k l => X (a, k) (b, l)

/-- The linear partial trace over the spectator factor. -/
def partialTraceRightLinear :
    Matrix (A × K) (A × K) ℂ →ₗ[ℂ] Matrix A A ℂ where
  toFun := partialTraceRight
  map_add' X Y := by
    ext a b
    change (∑ k, (X (a, k) (b, k) + Y (a, k) (b, k))) =
      (∑ k, X (a, k) (b, k)) + ∑ k, Y (a, k) (b, k)
    exact Finset.sum_add_distrib
  map_smul' c X := by
    ext a b
    simp [partialTraceRight, Finset.mul_sum]

/-- Tensor product of two linear matrix maps, defined on an arbitrary
correlated matrix by its active matrix-unit/spectator-block decomposition. -/
def correlatedTensorMap
    (Phi : Matrix A A ℂ →ₗ[ℂ] Matrix A A ℂ)
    (Psi : Matrix K K ℂ →ₗ[ℂ] Matrix K K ℂ)
    (X : Matrix (A × K) (A × K) ℂ) :
    Matrix (A × K) (A × K) ℂ :=
  ∑ a, ∑ b,
    (Phi (Matrix.single a b 1)) ⊗ₖ (Psi (spectatorBlock X a b))

theorem partialTrace_eq_sum_blocks (X : Matrix (A × K) (A × K) ℂ) :
    partialTraceRight X =
      ∑ a, ∑ b, (spectatorBlock X a b).trace • Matrix.single a b 1 := by
  ext i j
  simp only [partialTraceRight, Matrix.of_apply, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.single_apply, smul_eq_mul,
    spectatorBlock, Matrix.trace, Matrix.diag_apply]
  have hdelta (a b : A) :
      (∑ k, X (a, k) (b, k)) *
          (if a = i ∧ b = j then 1 else 0) =
        if a = i then (if b = j then ∑ k, X (a, k) (b, k) else 0) else 0 := by
    by_cases hai : a = i <;> by_cases hbj : b = j <;> simp [hai, hbj]
  simp_rw [hdelta]
  simp

/-- **Arbitrary correlated spectator identity.**  A trace-preserving
spectator channel is invisible after partial trace, even when the input is
not a tensor product. -/
theorem partialTrace_correlatedTensorMap
    (Phi : Matrix A A ℂ →ₗ[ℂ] Matrix A A ℂ)
    (Psi : Matrix K K ℂ →ₗ[ℂ] Matrix K K ℂ)
    (hPsi : ∀ B, (Psi B).trace = B.trace)
    (X : Matrix (A × K) (A × K) ℂ) :
    partialTraceRight (correlatedTensorMap Phi Psi X) =
      Phi (partialTraceRight X) := by
  have hElementary := (renewal_spectator_product Phi Psi hPsi).1
  have hCollapse := (renewal_spectator_product Phi Psi hPsi).2
  rw [correlatedTensorMap]
  change partialTraceRightLinear
      (∑ a, ∑ b,
        (Phi (Matrix.single a b 1)) ⊗ₖ
          (Psi (spectatorBlock X a b))) =
    Phi (partialTraceRight X)
  simp only [map_sum]
  have hlin (Y : Matrix (A × K) (A × K) ℂ) :
      partialTraceRightLinear Y = partialTraceRight Y := rfl
  simp_rw [hlin]
  simp_rw [hCollapse, hElementary]
  rw [partialTrace_eq_sum_blocks]
  simp only [map_sum, map_smul]

/-! ### Exact predictive rank of the independent labelled product -/

abbrev Configuration (m : ℕ) := Fin m → Fin 2
abbrev RealStage (m : ℕ) := Configuration m → ℝ

/-- The tensorized Walsh response panel. -/
def walshSynthesis (m : ℕ) :
    (Finset (Fin m) → ℝ) →ₗ[ℝ] RealStage m where
  toFun c := fun x => ∑ S, c S * RenewalWalsh.walsh S x
  map_add' c d := by
    funext x
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r c := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      (∑ S, (r * c S) * RenewalWalsh.walsh S x) =
          ∑ S, r * (c S * RenewalWalsh.walsh S x) := by
            refine Finset.sum_congr rfl fun S _ => ?_
            ring
      _ = r * ∑ S, c S * RenewalWalsh.walsh S x := by
            rw [Finset.mul_sum]

/-- Weighted Walsh orthogonality makes the full response panel injective. -/
theorem walshSynthesis_injective (m : ℕ) :
    Function.Injective (walshSynthesis m) := by
  intro c d hcd
  apply funext
  intro T
  have hpoint : ∀ x : Configuration m,
      ∑ S, (c S - d S) * RenewalWalsh.walsh S x = 0 := by
    intro x
    have h := congrFun hcd x
    simpa [walshSynthesis, Finset.sum_sub_distrib, sub_mul] using
      sub_eq_zero.mpr h
  have hweighted :
      ∑ x : Configuration m,
        (∏ i, RenewalWalsh.piw (x i)) *
          ((∑ S, (c S - d S) * RenewalWalsh.walsh S x) *
            RenewalWalsh.walsh T x) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [hpoint x, zero_mul, mul_zero]
  have hdiag :
      ∑ x : Configuration m,
        (∏ i, RenewalWalsh.piw (x i)) *
          ((∑ S, (c S - d S) * RenewalWalsh.walsh S x) *
            RenewalWalsh.walsh T x) =
        (c T - d T) * (30 : ℝ) ^ T.card := by
    calc
      _ = ∑ S, (c S - d S) *
          (∑ x : Configuration m,
            (∏ i, RenewalWalsh.piw (x i)) *
              (RenewalWalsh.walsh S x * RenewalWalsh.walsh T x)) := by
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun S _ => ?_
          refine Finset.sum_congr rfl fun x _ => ?_
          ring
      _ = _ := by
          simp_rw [RenewalWalsh.walsh_orthogonal]
          simp
  rw [hdiag] at hweighted
  have hpow : (30 : ℝ) ^ T.card ≠ 0 := pow_ne_zero _ (by norm_num)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hweighted).resolve_right hpow)

theorem configuration_card (m : ℕ) :
    Fintype.card (Configuration m) = 2 ^ m := by
  simp [Configuration]

theorem walsh_label_card (m : ℕ) :
    Fintype.card (Finset (Fin m)) = 2 ^ m := by
  simp

theorem realStage_finrank (m : ℕ) :
    Module.finrank ℝ (RealStage m) = 2 ^ m := by
  simp [RealStage, Configuration]

/-- The full point-labelled predictive response panel has rank exactly
`2^m`: it is an injective family of `2^m` Walsh columns in a
`2^m`-dimensional stage. -/
theorem predictive_rank_eq_two_pow (m : ℕ) :
    Function.Injective (walshSynthesis m) ∧
      Module.finrank ℝ (RealStage m) = 2 ^ m ∧
      Fintype.card (Finset (Fin m)) = 2 ^ m := by
  exact ⟨walshSynthesis_injective m, realStage_finrank m,
    walsh_label_card m⟩

/-- No fixed finite-dimensional vector space can faithfully contain every
labelled renewal screen. -/
theorem no_finite_faithful_global_carrier
    (V : Type*) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] :
    ¬ ∀ m : ℕ, ∃ J : RealStage m →ₗ[ℝ] V, Function.Injective J := by
  intro h
  let m := Module.finrank ℝ V
  obtain ⟨J, hJ⟩ := h m
  have hle : Module.finrank ℝ (RealStage m) ≤ Module.finrank ℝ V :=
    LinearMap.finrank_le_finrank_of_injective hJ
  rw [realStage_finrank] at hle
  have hlt : m < 2 ^ m := Nat.lt_two_pow_self
  exact (Nat.not_lt_of_ge hle) hlt

/-- Complete exact package for the independent-cell half of the manuscript
theorem: product spectrum, response rank, faithful quasilocal state, and no
finite faithful global carrier. -/
theorem independent_cell_regulator_certificate :
    (∀ {m : ℕ} (S : Finset (Fin m)) (x : Configuration m),
      RenewalWalsh.transferOp (RenewalWalsh.walsh S) x =
        (-(7 / 15 : ℝ)) ^ S.card * RenewalWalsh.walsh S x)
    ∧ (∀ {m : ℕ} {S : Finset (Fin m)}, S.Nonempty →
        |(-(7 / 15 : ℝ)) ^ S.card| ≤ 7 / 15)
    ∧ (∀ m, Function.Injective (walshSynthesis m))
    ∧ (∀ m, Module.finrank ℝ (RealStage m) = 2 ^ m)
    ∧ RenewalProductAF.ConcreteRenewalProductAFProfile := by
  exact ⟨RenewalWalsh.transfer_walsh, fun hS =>
    RenewalWalsh.mean_zero_contraction hS,
    walshSynthesis_injective, realStage_finrank,
    RenewalProductAF.concreteRenewalProductAF_profile⟩

end
end RenewalSpectatorProduct
end NCG
