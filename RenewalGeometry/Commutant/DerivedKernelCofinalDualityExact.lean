/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.OperatorLimits.TransportedMoscoAsymptoticCompactness
import RenewalGeometry.OperatorLimits.ProtectedBasisTransport
import RenewalGeometry.Commutant.JointCommutatorContinuousOperator
import RenewalGeometry.Commutant.ArbitraryIncidenceDualityExact

/-!
# Derived-kernel cofinal action–multiplicity duality

Covers `thm:cofinal-duality` of the spacetime–gauge duality manuscript (revised version with
hypotheses (D1)–(D3) and *derived* limiting kernel).

* `derivedKernelCofinal_abstract`: for arbitrary extended nonnegative forms `q_X` on varying
  Hilbert spaces `H_X` and a limit form `q_∞` on `H_∞`, compared in a common carrier through
  isometries `J_X`, `J_∞`:
  (D1) transported Mosco convergence `q_X → q_∞` (`def:transported-mosco`),
  (D2) protected subspaces `M_X` of one finite dimension (orthonormal bases `e_{a,X}`) on which
  `q_X` vanishes, and a specified `M_∞` (orthonormal basis `e_{a,∞}`) with basis transport
  defect `η_X → 0` (`eq:protected-basis-transport`),
  (D3) a uniform late-cutoff gap `q_X(A) ≥ γ_* ‖(I − P_{M_X})A‖²`,
  imply: eventually the zero set of `q_X` is exactly `M_X`; the limiting gap
  `q_∞(A) ≥ γ_* ‖(I − P_{M_∞})A‖²` (`eq:cofinal-limit-gap`); and the zero set of `q_∞` is
  exactly `M_∞` (`eq:cofinal-limit-kernel`).  No compactness is used.
* `derivedKernelCofinalDuality_exact`: the theorem for the closed commutator forms
  `q_X(A) = Σ_j ‖[c_{j,X}, A]‖²_HS` on the Hilbert–Schmidt spaces of the finite screens: in
  addition `Ker 𝓛_X = M_X` for the commutant Laplacian and `C^*(c_X)' = M_X`
  (`eq:cofinal-kernel`) at every late cutoff.
-/

open Filter Topology Matrix
open scoped ENNReal

noncomputable section

namespace RenewalGeometry.VaryingHilbert.System

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {Hn : ℕ → Type*} [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
variable {Hlim : Type*} [NormedAddCommGroup Hlim] [InnerProductSpace ℂ Hlim]

/-- Residual of a vector after removing its components along a finite family:
`y − Σ_a ⟨u_a, y⟩ u_a`. -/
def derivedKernelResidual {ι : Type*} [Fintype ι] (u : ι → H) (y : H) : H :=
  y - ∑ a, inner ℂ (u a) y • u a

/-- For an orthonormal basis `e` of `M` and a linear isometry `J`,
`J (A − P_M A) = J A − Σ_a ⟨J e_a, J A⟩ J e_a`. -/
theorem derivedKernel_map_sub_starProjection {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {ι : Type*} [Fintype ι]
    (J : E →ₗᵢ[ℂ] H) (M : Submodule ℂ E) [M.HasOrthogonalProjection]
    (e : ι → E) (he : Orthonormal ℂ e) (hspan : Submodule.span ℂ (Set.range e) = M) (A : E) :
    J (A - M.starProjection A) = derivedKernelResidual (fun a => J (e a)) (J A) := by
  rw [starProjection_eq_transportedProjection M e he hspan, transportedProjection_apply,
    derivedKernelResidual, map_sub, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, LinearIsometry.inner_map_map]

/-- `‖A − P_M A‖` read off the transported residual. -/
theorem derivedKernel_norm_sub_starProjection {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {ι : Type*} [Fintype ι]
    (J : E →ₗᵢ[ℂ] H) (M : Submodule ℂ E) [M.HasOrthogonalProjection]
    (e : ι → E) (he : Orthonormal ℂ e) (hspan : Submodule.span ℂ (Set.range e) = M) (A : E) :
    ‖A - M.starProjection A‖ = ‖derivedKernelResidual (fun a => J (e a)) (J A)‖ := by
  rw [← derivedKernel_map_sub_starProjection J M e he hspan A, LinearIsometry.norm_map]

/-- The residual is jointly continuous in the vector and the finite family. -/
theorem derivedKernelResidual_tendsto {ι : Type*} [Fintype ι] {u : ℕ → ι → H} {ulim : ι → H}
    {y : ℕ → H} {ylim : H} (hu : ∀ a, Tendsto (fun X => u X a) atTop (𝓝 (ulim a)))
    (hy : Tendsto y atTop (𝓝 ylim)) :
    Tendsto (fun X => derivedKernelResidual (u X) (y X)) atTop
      (𝓝 (derivedKernelResidual ulim ylim)) := by
  unfold derivedKernelResidual
  refine hy.sub (tendsto_finsetSum _ fun a _ => ?_)
  exact ((hu a).inner hy).smul (hu a)

/-- A vector is in `M` iff its residual `A − P_M A` vanishes. -/
theorem derivedKernel_mem_iff_sub_starProjection_eq_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (M : Submodule ℂ E) [M.HasOrthogonalProjection] (A : E) :
    A ∈ M ↔ A - M.starProjection A = 0 := by
  rw [sub_eq_zero]
  constructor
  · intro hA
    exact (Submodule.starProjection_eq_self_iff.mpr hA).symm
  · intro hA
    rw [hA]
    exact Submodule.starProjection_apply_mem M A

/-- The gap inequality forces vanishing of the form only on `M`. -/
theorem derivedKernel_mem_of_gap_of_eq_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (M : Submodule ℂ E) [M.HasOrthogonalProjection]
    (γ : ℝ) (hγ : 0 < γ) (A : E) (Q : ℝ≥0∞)
    (hgap : ENNReal.ofReal (γ * ‖A - M.starProjection A‖ ^ 2) ≤ Q) (hQ : Q = 0) :
    A ∈ M := by
  rw [hQ, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hgap
  have hsq : ‖A - M.starProjection A‖ ^ 2 ≤ 0 := by
    by_contra h
    push Not at h
    nlinarith [mul_pos hγ h]
  have hnorm : ‖A - M.starProjection A‖ = 0 :=
    pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm hsq (sq_nonneg _))
  exact (derivedKernel_mem_iff_sub_starProjection_eq_zero M A).mpr (norm_eq_zero.mp hnorm)

/-- **Derived-kernel cofinal duality, abstract form (`thm:cofinal-duality`).**
(D1) transported Mosco convergence, (D2) protected subspaces of one finite dimension with
orthonormal bases on which the stage forms vanish and basis transport `η_X → 0` to a specified
`M_∞`, and (D3) a uniform late-cutoff complement gap give:
eventually `{q_X = 0} = M_X`; the limiting gap `q_∞(A) ≥ γ_* ‖(I − P_{M_∞}) A‖²`; and
`{q_∞ = 0} = M_∞`.  No compactness hypothesis is used. -/
theorem derivedKernelCofinal_abstract
    (J : System (K := ℂ) (H := H) (Hn := Hn)) (Jlim : Hlim →ₗᵢ[ℂ] H)
    (q : (n : ℕ) → Hn n → ℝ≥0∞) (qlim : Hlim → ℝ≥0∞)
    (hD1 : J.TransportedMoscoConverges Jlim q qlim)
    {ι : Type*} [Fintype ι]
    (M : ∀ X, Submodule ℂ (Hn X)) [∀ X, (M X).HasOrthogonalProjection]
    (e : ∀ X, ι → Hn X) (he : ∀ X, Orthonormal ℂ (e X))
    (hspan : ∀ X, Submodule.span ℂ (Set.range (e X)) = M X)
    (hMzero : ∀ X, ∀ A ∈ M X, q X A = 0)
    (Mlim : Submodule ℂ Hlim) [Mlim.HasOrthogonalProjection]
    (elim : ι → Hlim) (helim : Orthonormal ℂ elim)
    (hspanlim : Submodule.span ℂ (Set.range elim) = Mlim)
    (hη : Tendsto (J.basisTransportDefect e Jlim elim) atTop (𝓝 0))
    (γstar : ℝ) (hγ : 0 < γstar)
    (hD3 : ∀ᶠ X in atTop, ∀ A : Hn X,
      ENNReal.ofReal (γstar * ‖A - (M X).starProjection A‖ ^ 2) ≤ q X A) :
    (∀ᶠ X in atTop, ∀ A : Hn X, q X A = 0 ↔ A ∈ M X) ∧
      (∀ A : Hlim, ENNReal.ofReal (γstar * ‖A - Mlim.starProjection A‖ ^ 2) ≤ qlim A) ∧
      (∀ A : Hlim, qlim A = 0 ↔ A ∈ Mlim) := by
  -- transported basis vectors converge strongly
  have hbasis : ∀ a, Tendsto (fun X => J.embedding X (e X a)) atTop (𝓝 (Jlim (elim a))) := by
    intro a
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _)
      (fun X => J.norm_sub_le_basisTransportDefect e Jlim elim X a) hη
  -- (1) finite kernels
  have hfinite : ∀ᶠ X in atTop, ∀ A : Hn X, q X A = 0 ↔ A ∈ M X := by
    filter_upwards [hD3] with X hX A
    exact ⟨fun h0 => derivedKernel_mem_of_gap_of_eq_zero (M X) γstar hγ A _ (hX A) h0,
      hMzero X A⟩
  -- (2) the limiting protected space lies in the zero set of q_∞
  have hlimzero : ∀ A ∈ Mlim, qlim A = 0 := by
    intro A hA
    rw [← hspanlim, Submodule.mem_span_range_iff_exists_fun] at hA
    obtain ⟨c, rfl⟩ := hA
    let x : ∀ X, Hn X := fun X => ∑ a, c a • e X a
    have hxstrong : J.StronglyConverges x (Jlim (∑ a, c a • elim a)) := by
      unfold StronglyConverges
      simp only [x, map_sum, map_smul]
      exact tendsto_finsetSum _ fun a _ => (hbasis a).const_smul (c a)
    obtain ⟨A', hA', hle⟩ := hD1.weak_liminf x _ hxstrong.weak
    have hA'eq : A' = ∑ a, c a • elim a := Jlim.injective hA'
    have hzero : ∀ X, q X (x X) = 0 := by
      intro X
      apply hMzero
      rw [← hspan X]
      exact Submodule.sum_mem _ fun a _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    rw [← hA'eq]
    simpa [hzero] using hle
  -- (3) the limiting gap
  have hlimgap : ∀ A : Hlim,
      ENNReal.ofReal (γstar * ‖A - Mlim.starProjection A‖ ^ 2) ≤ qlim A := by
    intro A
    by_cases htop : qlim A = ∞
    · rw [htop]
      exact le_top
    obtain ⟨x, hx, hqx⟩ := hD1.recovery A htop
    have hres : Tendsto (fun X => ENNReal.ofReal (γstar * ‖x X - (M X).starProjection (x X)‖ ^ 2))
        atTop (𝓝 (ENNReal.ofReal (γstar * ‖A - Mlim.starProjection A‖ ^ 2))) := by
      apply ENNReal.tendsto_ofReal
      apply Tendsto.const_mul
      apply Tendsto.pow
      have h1 : (fun X => ‖x X - (M X).starProjection (x X)‖) = fun X =>
          ‖derivedKernelResidual (fun a => J.embedding X (e X a)) (J.embedding X (x X))‖ := by
        funext X
        exact derivedKernel_norm_sub_starProjection (J.embedding X) (M X) (e X) (he X)
          (hspan X) (x X)
      rw [h1, derivedKernel_norm_sub_starProjection Jlim Mlim elim helim hspanlim A]
      exact (derivedKernelResidual_tendsto hbasis hx).norm
    exact le_of_tendsto_of_tendsto hres hqx (hD3.mono fun X hX => hX (x X))
  refine ⟨hfinite, hlimgap, fun A => ⟨fun h0 => ?_, hlimzero A⟩⟩
  exact derivedKernel_mem_of_gap_of_eq_zero Mlim γstar hγ A _ (hlimgap A) h0

end Abstract

section Commutator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {Hlim : Type*} [NormedAddCommGroup Hlim] [InnerProductSpace ℂ Hlim]

/-- The kernel of the commutant Laplacian `𝓛 = ∂† ∂` is the kernel of the stacked
commutator map `∂ A = ([c_j, A])_j`. -/
theorem derivedKernel_mem_ker_commutantLaplacian_iff {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) (A : EuclideanSpace ℂ (n × n)) :
    A ∈ LinearMap.ker (RenewalGeometry.commutantLaplacianCLM c).toLinearMap ↔
      RenewalGeometry.jointCommutatorCLM c A = 0 := by
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  constructor
  · intro h
    have h0 : inner ℂ (RenewalGeometry.commutantLaplacianCLM c A) A = 0 := by
      rw [h, inner_zero_left]
    rw [RenewalGeometry.commutantLaplacianCLM, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_left, inner_self_eq_zero] at h0
    exact h0
  · intro h
    simp [RenewalGeometry.commutantLaplacianCLM, h]

/-- The commutator energy `ofReal ‖∂ A‖²` vanishes exactly on the commutant-Laplacian
kernel. -/
theorem derivedKernel_commutatorEnergy_eq_zero_iff {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) (A : EuclideanSpace ℂ (n × n)) :
    ennrealBoundedOperatorEnergy (RenewalGeometry.jointCommutatorCLM c) A = 0 ↔
      A ∈ LinearMap.ker (RenewalGeometry.commutantLaplacianCLM c).toLinearMap := by
  rw [derivedKernel_mem_ker_commutantLaplacian_iff, ennrealBoundedOperatorEnergy,
    ENNReal.ofReal_eq_zero]
  constructor
  · intro h
    have h2 : ‖RenewalGeometry.jointCommutatorCLM c A‖ ^ 2 = 0 :=
      le_antisymm h (sq_nonneg _)
    exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2)
  · intro h
    simp [h]

/-- For an adjoint-closed generator family, the commutant of the generated `C^*`-algebra is
the joint commutator kernel (`thm:howe-certificate`, kernel clause). -/
theorem derivedKernel_mem_matCommutant_iff {n : Type*} [Fintype n] [DecidableEq n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) (hstar : ∀ j, ∃ k, (c j)ᴴ = c k) (T : Matrix n n ℂ) :
    T ∈ RenewalGeometry.matCommutant
        ((StarAlgebra.adjoin ℂ (Set.range c) : StarSubalgebra ℂ (Matrix n n ℂ)) :
          Set (Matrix n n ℂ)) ↔
      RenewalGeometry.matrixL2 T ∈
        LinearMap.ker (RenewalGeometry.commutantLaplacianCLM c).toLinearMap := by
  rw [RenewalGeometry.ArbitraryIncidenceDuality.mem_matCommutant_starAdjoin_iff,
    derivedKernel_mem_ker_commutantLaplacian_iff]
  have hk := RenewalGeometry.matrixL2_mem_jointCommutatorCLM_ker_iff c T
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hk
  rw [hk]
  constructor
  · intro h j
    exact ((h (c j) ⟨j, rfl⟩).1).symm
  · rintro h a ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := hstar j
    rw [hk]
    exact ⟨(h j).symm, (h k).symm⟩

/-- **Derived-kernel cofinal action–multiplicity duality (`thm:cofinal-duality`).**
Let `q_X(A) = Σ_j ‖[c_{j,X}, A]‖²_HS` be the commutator forms of a cofinal family of finite
screened generator families (adjoint-closed, as in `thm:howe-certificate`) on the
Hilbert–Schmidt spaces `ℂ^{d_X × d_X}`, transported into a common Hilbert carrier by `J_X`.
Assume (D1) transported Mosco convergence `q_X → q_∞` to a form on `H_∞` embedded by `J_∞`;
(D2) protected subspaces `M_X ⊆ Ker 𝓛_X` with orthonormal bases `e_{a,X}` indexed by one
finite type, and a specified `M_∞` with orthonormal basis `e_{a,∞}` such that the basis
transport defect `η_X → 0`; (D3) one `γ_* > 0` with
`q_X(A) ≥ γ_* ‖(I − P_{M_X})A‖²` for all late cutoffs.  Then at every late cutoff
`Ker 𝓛_X = M_X` and `C^*(c_X)' = M_X` (`eq:cofinal-kernel`, on the full Hilbert–Schmidt
test space), the limiting gap `q_∞(A) ≥ γ_* ‖(I − P_{M_∞})A‖²` holds
(`eq:cofinal-limit-gap`), and the kernel (zero set) of the limiting form is exactly `M_∞`
(`eq:cofinal-limit-kernel`).  No compactness is assumed. -/
theorem derivedKernelCofinalDuality_exact
    {d : ℕ → Type*} [∀ X, Fintype (d X)] [∀ X, DecidableEq (d X)] {s : ℕ}
    (c : ∀ X, Fin s → Matrix (d X) (d X) ℂ)
    (hstar : ∀ X j, ∃ k, (c X j)ᴴ = c X k)
    (J : System (K := ℂ) (H := H) (Hn := fun X => EuclideanSpace ℂ (d X × d X)))
    (Jlim : Hlim →ₗᵢ[ℂ] H) (qlim : Hlim → ℝ≥0∞)
    (hD1 : J.TransportedMoscoConverges Jlim
      (fun X => ennrealBoundedOperatorEnergy (RenewalGeometry.jointCommutatorCLM (c X))) qlim)
    {ι : Type*} [Fintype ι]
    (M : ∀ X, Submodule ℂ (EuclideanSpace ℂ (d X × d X)))
    (e : ∀ X, ι → EuclideanSpace ℂ (d X × d X)) (he : ∀ X, Orthonormal ℂ (e X))
    (hspan : ∀ X, Submodule.span ℂ (Set.range (e X)) = M X)
    (hMker : ∀ X,
      M X ≤ LinearMap.ker (RenewalGeometry.commutantLaplacianCLM (c X)).toLinearMap)
    (Mlim : Submodule ℂ Hlim) [Mlim.HasOrthogonalProjection]
    (elim : ι → Hlim) (helim : Orthonormal ℂ elim)
    (hspanlim : Submodule.span ℂ (Set.range elim) = Mlim)
    (hη : Tendsto (J.basisTransportDefect e Jlim elim) atTop (𝓝 0))
    (γstar : ℝ) (hγ : 0 < γstar)
    (hD3 : ∀ᶠ X in atTop, ∀ A : EuclideanSpace ℂ (d X × d X),
      γstar * ‖A - (M X).starProjection A‖ ^ 2 ≤
        ‖RenewalGeometry.jointCommutatorCLM (c X) A‖ ^ 2) :
    (∀ᶠ X in atTop,
      LinearMap.ker (RenewalGeometry.commutantLaplacianCLM (c X)).toLinearMap = M X ∧
        ∀ T : Matrix (d X) (d X) ℂ,
          T ∈ RenewalGeometry.matCommutant
              ((StarAlgebra.adjoin ℂ (Set.range (c X)) :
                StarSubalgebra ℂ (Matrix (d X) (d X) ℂ)) : Set (Matrix (d X) (d X) ℂ)) ↔
            RenewalGeometry.matrixL2 T ∈ M X) ∧
      (∀ A : Hlim, ENNReal.ofReal (γstar * ‖A - Mlim.starProjection A‖ ^ 2) ≤ qlim A) ∧
      (∀ A : Hlim, qlim A = 0 ↔ A ∈ Mlim) := by
  obtain ⟨hfinite, hlimgap, hlimker⟩ :=
    derivedKernelCofinal_abstract J Jlim _ qlim hD1 M e he hspan
      (fun X A hA => (derivedKernel_commutatorEnergy_eq_zero_iff (c X) A).mpr (hMker X hA))
      Mlim elim helim hspanlim hη γstar hγ
      (hD3.mono fun X hX A => by
        rw [ennrealBoundedOperatorEnergy]
        exact ENNReal.ofReal_le_ofReal (hX A))
  refine ⟨?_, hlimgap, hlimker⟩
  filter_upwards [hfinite] with X hX
  have hker : LinearMap.ker (RenewalGeometry.commutantLaplacianCLM (c X)).toLinearMap = M X := by
    ext A
    rw [← derivedKernel_commutatorEnergy_eq_zero_iff, hX A]
  refine ⟨hker, fun T => ?_⟩
  rw [derivedKernel_mem_matCommutant_iff (c X) (hstar X), hker]

end Commutator

end RenewalGeometry.VaryingHilbert.System
