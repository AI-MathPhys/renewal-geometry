/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GrandInterface2
import NCG.Upstream.PrimitiveWeight
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Exact EASY 77: the finite commutant Poincare gap

The existing commutant audit identifies the zero-energy space and proves the
projection/blindness algebra.  This file supplies the missing finite-dimensional
gap: a linear operator is uniformly bounded below on the orthogonal complement
of its kernel.  Applied to the joint commutator map, this is precisely the
positive commutant rigidity margin.
-/

namespace NCG

open Matrix
open Upstream.PrimitiveWeight
open scoped ComplexOrder MatrixOrder

/-- Every linear map on a finite-dimensional complex inner-product space has a
strictly positive squared-norm gap on the orthogonal complement of its kernel. -/
theorem finite_dimensional_kernel_gap
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : E →ₗ[ℂ] F) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ x : E, x ∈ (LinearMap.ker T)ᗮ →
      lam * ‖x‖ ^ 2 ≤ ‖T x‖ ^ 2 := by
  let K : Submodule ℂ E := (LinearMap.ker T)ᗮ
  let Tr : K →ₗ[ℂ] F := T.domRestrict K
  have hTr : Function.Injective Tr := by
    intro x y hxy
    apply Subtype.ext
    have hmap : T (x.1 - y.1) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact hxy
    have hker : x.1 - y.1 ∈ LinearMap.ker T := hmap
    have horth : x.1 - y.1 ∈ (LinearMap.ker T)ᗮ :=
      K.sub_mem x.2 y.2
    have hinf : x.1 - y.1 ∈
        LinearMap.ker T ⊓ (LinearMap.ker T)ᗮ := ⟨hker, horth⟩
    have hzero : x.1 - y.1 = 0 := by
      have hbot : x.1 - y.1 ∈ (⊥ : Submodule ℂ E) := by
        rwa [(LinearMap.ker T).inf_orthogonal_eq_bot] at hinf
      simpa using hbot
    exact sub_eq_zero.mp hzero
  obtain ⟨C, hC, hanti⟩ :=
    (LinearMap.injective_iff_antilipschitz Tr).mp hTr
  let r : ℝ := C
  have hr : 0 < r := by exact_mod_cast hC
  refine ⟨r⁻¹ ^ 2, sq_pos_of_pos (inv_pos.mpr hr), ?_⟩
  intro x hx
  have hb := hanti.le_mul_dist ⟨x, hx⟩ (0 : K)
  simp only [dist_zero_right, Tr, LinearMap.domRestrict_apply, map_zero] at hb
  change ‖x‖ ≤ (C : ℝ) * ‖T x‖ at hb
  have hb' : ‖x‖ ≤ r * ‖T x‖ := by
    simpa only [r] using hb
  have hbdiv : r⁻¹ * ‖x‖ ≤ ‖T x‖ := by
    calc
      r⁻¹ * ‖x‖ ≤ r⁻¹ * (r * ‖T x‖) :=
        mul_le_mul_of_nonneg_left hb' (le_of_lt (inv_pos.mpr hr))
      _ = ‖T x‖ := by field_simp
  nlinarith [norm_nonneg x, norm_nonneg (T x),
    mul_nonneg (le_of_lt (inv_pos.mpr hr)) (norm_nonneg x)]

/-- Projection form of the gap.  If `p` is the orthogonal kernel component of
`x`, the commutator energy of `x` controls exactly `x-p`. -/
theorem finite_dimensional_projected_kernel_gap
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : E →ₗ[ℂ] F) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ (x p : E),
      p ∈ LinearMap.ker T → x - p ∈ (LinearMap.ker T)ᗮ →
      lam * ‖x - p‖ ^ 2 ≤ ‖T x‖ ^ 2 := by
  obtain ⟨lam, hlam, hgap⟩ := finite_dimensional_kernel_gap T
  refine ⟨lam, hlam, ?_⟩
  intro x p hp horth
  have h := hgap (x - p) horth
  have hTp : T p = 0 := hp
  simpa only [map_sub, hTp, sub_zero] using h

/-- For a nonempty positive-definite Hermitian matrix, its minimum spectral
value is positive, is an actual eigenvalue, and gives the sharp quadratic
lower bound. -/
theorem posDef_min_eigenvalue_quadratic
    {r : ℕ} (hr : 0 < r) (G : Matrix (Fin r) (Fin r) ℂ)
    (hG : G.PosDef) :
    ∃ lam : ℝ, 0 < lam
      ∧ (∃ i : Fin r, lam = hG.1.eigenvalues i)
      ∧ (∀ i : Fin r, lam ≤ hG.1.eigenvalues i)
      ∧ ∀ x : Fin r → ℂ,
          lam * ∑ i, Complex.normSq (x i) ≤
            (star x ⬝ᵥ (G *ᵥ x)).re := by
  have hne : (Finset.univ : Finset (Fin r)).Nonempty := by
    exact ⟨⟨0, hr⟩, Finset.mem_univ _⟩
  obtain ⟨i0, _, hi0⟩ :=
    Finset.exists_min_image Finset.univ hG.1.eigenvalues hne
  let lam : ℝ := hG.1.eigenvalues i0
  have hlam : 0 < lam := hG.eigenvalues_pos i0
  have heig : ∃ i : Fin r, lam = hG.1.eigenvalues i := ⟨i0, rfl⟩
  have hleast : ∀ i : Fin r, lam ≤ hG.1.eigenvalues i := by
    intro i
    exact hi0 i (Finset.mem_univ i)
  have hshift : (G - (lam : ℂ) • 1).PosSemidef := by
    have heq : G - (lam : ℂ) • 1 =
        hG.1.cfc fun x => x - lam := by
      have h1 := cfc_sub hG.1 id (fun _ => lam)
      rw [Upstream.PrimitiveWeight.cfc_id',
        Upstream.PrimitiveWeight.cfc_const] at h1
      exact h1
    rw [heq]
    refine cfc_posSemidef hG.1 fun i => ?_
    exact sub_nonneg.mpr (hi0 i (Finset.mem_univ i))
  refine ⟨lam, hlam, heig, hleast, ?_⟩
  intro x
  have hnon := hshift.re_dotProduct_nonneg x
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hnon
  simp only [dotProduct_sub, dotProduct_smul] at hnon
  have hself : (star x ⬝ᵥ x).re = ∑ i, Complex.normSq (x i) := by
    simp [dotProduct, Complex.normSq_apply]
  change 0 ≤ (star x ⬝ᵥ (G *ᵥ x)).re -
    (((lam : ℂ) * (star x ⬝ᵥ x)).re) at hnon
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, hself] at hnon
  linarith

/-- On the nontrivial kernel-orthogonal subspace, the least eigenvalue of the
restricted Gram operator is an actual positive spectral value and gives the
Poincare inequality.  If the complement is zero, there is no positive
eigenvalue and the audit is vacuous. -/
theorem finite_dimensional_kernel_least_eigenvalue_gap
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (T : E →ₗ[ℂ] F) :
    let K : Submodule ℂ E := (LinearMap.ker T)ᗮ
    K = ⊥ ∨
      ∃ (r : ℕ) (G : Matrix (Fin r) (Fin r) ℂ)
        (hG : G.PosDef) (lam : ℝ),
        r = Module.finrank ℂ K
        ∧ 0 < lam
        ∧ (∃ i : Fin r, lam = hG.1.eigenvalues i)
        ∧ (∀ i : Fin r, lam ≤ hG.1.eigenvalues i)
        ∧ ∀ x : E, x ∈ K → lam * ‖x‖ ^ 2 ≤ ‖T x‖ ^ 2 := by
  dsimp only
  let K : Submodule ℂ E := (LinearMap.ker T)ᗮ
  by_cases hK : K = ⊥
  · exact Or.inl hK
  · right
    let r : ℕ := Module.finrank ℂ K
    have hr : 0 < r := by
      rw [Nat.pos_iff_ne_zero]
      intro hr0
      apply hK
      exact Submodule.finrank_eq_zero.mp hr0
    let b : OrthonormalBasis (Fin r) ℂ K :=
      stdOrthonormalBasis ℂ K
    let Tr : K →ₗ[ℂ] F := T.domRestrict K
    have hTr : Function.Injective Tr := by
      intro x y hxy
      apply Subtype.ext
      have hmap : T (x.1 - y.1) = 0 := by
        rw [map_sub, sub_eq_zero]
        exact hxy
      have hker : x.1 - y.1 ∈ LinearMap.ker T := hmap
      have horth : x.1 - y.1 ∈ (LinearMap.ker T)ᗮ :=
        K.sub_mem x.2 y.2
      have hinf : x.1 - y.1 ∈
          LinearMap.ker T ⊓ (LinearMap.ker T)ᗮ := ⟨hker, horth⟩
      have hzero : x.1 - y.1 = 0 := by
        have hbot : x.1 - y.1 ∈ (⊥ : Submodule ℂ E) := by
          rwa [(LinearMap.ker T).inf_orthogonal_eq_bot] at hinf
        simpa using hbot
      exact sub_eq_zero.mp hzero
    let v : Fin r → F := fun i => Tr (b i)
    have hv : LinearIndependent ℂ v := by
      exact b.toBasis.linearIndependent.map' Tr
        (LinearMap.ker_eq_bot.mpr hTr)
    let G : Matrix (Fin r) (Fin r) ℂ := gram ℂ v
    have hG : G.PosDef := by
      exact posDef_gram_of_linearIndependent hv
    obtain ⟨lam, hlam, heig, hleast, hquad⟩ :=
      posDef_min_eigenvalue_quadratic hr G hG
    refine ⟨r, G, hG, lam, rfl, hlam, heig, hleast, ?_⟩
    intro x hx
    let z : K := ⟨x, hx⟩
    let coeff : Fin r → ℂ := fun i => WithLp.ofLp (b.repr z) i
    have hsum : ∑ i, coeff i • b i = z := by
      simpa only [coeff] using b.sum_repr z
    have hTvsum : ∑ i, coeff i • v i = T x := by
      calc
        ∑ i, coeff i • v i
            = T (∑ i, coeff i • (b i : E)) := by
                simp only [v, Tr, LinearMap.domRestrict_apply,
                  map_sum, map_smul]
        _ = T x := by
          congr 1
          simpa using congrArg Subtype.val hsum
    have hqG : (star coeff ⬝ᵥ (G *ᵥ coeff)).re = ‖T x‖ ^ 2 := by
      rw [show G = gram ℂ v from rfl,
        star_dotProduct_gram_mulVec, hTvsum,
        inner_self_eq_norm_sq_to_K]
      rw [pow_two, Complex.mul_re]
      simp [pow_two]
    have hcoeff : ∑ i, Complex.normSq (coeff i) = ‖x‖ ^ 2 := by
      calc
        ∑ i, Complex.normSq (coeff i)
            = ∑ i, ‖WithLp.ofLp (b.repr z) i‖ ^ 2 := by
                simp only [coeff, Complex.normSq_eq_norm_sq]
        _ = ‖b.repr z‖ ^ 2 := by
              rw [EuclideanSpace.norm_sq_eq]
        _ = ‖z‖ ^ 2 := by rw [b.repr.norm_map]
        _ = ‖x‖ ^ 2 := rfl
    have h := hquad coeff
    rw [hcoeff, hqG] at h
    exact h

/-- A matrix in its genuine Hilbert--Schmidt `ℓ²` realization. -/
noncomputable def matrixL2 {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) : EuclideanSpace ℂ (m × n) :=
  WithLp.toLp 2 (fun ij => M ij.1 ij.2)

/-- Recover the matrix entries from the Hilbert--Schmidt realization. -/
def l2Matrix {m n : Type*} [Fintype m] [Fintype n]
    (x : EuclideanSpace ℂ (m × n)) : Matrix m n ℂ :=
  fun i j => WithLp.ofLp x (i, j)

@[simp] theorem l2Matrix_matrixL2 {m n : Type*} [Fintype m]
    [Fintype n] (M : Matrix m n ℂ) : l2Matrix (matrixL2 M) = M := by
  ext i j
  simp [l2Matrix, matrixL2]

theorem matrixL2_sub {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℂ) :
    matrixL2 (A - B) = matrixL2 A - matrixL2 B := by
  ext ij
  simp [matrixL2]

theorem l2Matrix_add {m n : Type*} [Fintype m] [Fintype n]
    (x y : EuclideanSpace ℂ (m × n)) :
    l2Matrix (x + y) = l2Matrix x + l2Matrix y := by
  ext i j
  simp [l2Matrix]

theorem l2Matrix_smul {m n : Type*} [Fintype m] [Fintype n]
    (a : ℂ) (x : EuclideanSpace ℂ (m × n)) :
    l2Matrix (a • x) = a • l2Matrix x := by
  ext i j
  simp [l2Matrix]

/-- The joint commutator as one linear map between Hilbert--Schmidt spaces. -/
noncomputable def jointCommutatorL2 {n : Type*} [Fintype n]
    {s : ℕ} (c : Fin s → Matrix n n ℂ) :
    EuclideanSpace ℂ (n × n) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin s × (n × n)) where
  toFun x := WithLp.toLp 2 (fun q =>
    (c q.1 * l2Matrix x - l2Matrix x * c q.1) q.2.1 q.2.2)
  map_add' x y := by
    ext q
    change
      (c q.1 * l2Matrix (x + y) - l2Matrix (x + y) * c q.1)
          q.2.1 q.2.2 =
        (c q.1 * l2Matrix x - l2Matrix x * c q.1) q.2.1 q.2.2 +
        (c q.1 * l2Matrix y - l2Matrix y * c q.1) q.2.1 q.2.2
    rw [l2Matrix_add, Matrix.mul_add, Matrix.add_mul]
    simp only [Matrix.add_apply, Matrix.sub_apply]
    module
  map_smul' a x := by
    ext q
    change
      (c q.1 * l2Matrix (a • x) - l2Matrix (a • x) * c q.1)
          q.2.1 q.2.2 =
        a * (c q.1 * l2Matrix x - l2Matrix x * c q.1) q.2.1 q.2.2
    rw [l2Matrix_smul, Matrix.mul_smul, Matrix.smul_mul]
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring

/-- Hilbert--Schmidt norm is exactly the manuscript's trace convention. -/
theorem matrixL2_norm_sq {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) :
    ‖matrixL2 M‖ ^ 2 = ((Mᴴ * M).trace).re := by
  rw [EuclideanSpace.norm_sq_eq, trace_conj_self_re]
  simp only [matrixL2, WithLp.ofLp_toLp, Fintype.sum_prod_type,
    Complex.normSq_eq_norm_sq]
  rw [Finset.sum_comm]

/-- The codomain norm of the joint commutator is literally the sum of squared
Hilbert--Schmidt commutator norms. -/
theorem jointCommutatorL2_norm_sq {n : Type*} [Fintype n]
    {s : ℕ} (c : Fin s → Matrix n n ℂ)
    (X : Matrix n n ℂ) :
    ‖jointCommutatorL2 c (matrixL2 X)‖ ^ 2 =
      ∑ j, (((c j * X - X * c j)ᴴ *
        (c j * X - X * c j)).trace).re := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [jointCommutatorL2, LinearMap.coe_mk, AddHom.coe_mk,
    WithLp.ofLp_toLp, l2Matrix_matrixL2, Fintype.sum_prod_type,
    Complex.normSq_eq_norm_sq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [trace_conj_self_re]
  rw [Finset.sum_comm]
  simp only [Complex.normSq_eq_norm_sq]

/-- The kernel of the joint Hilbert--Schmidt commutator map is the exact
matrix commutant. -/
theorem matrixL2_mem_jointCommutator_ker_iff {n : Type*} [Fintype n]
    {s : ℕ} (c : Fin s → Matrix n n ℂ) (X : Matrix n n ℂ) :
    matrixL2 X ∈ LinearMap.ker (jointCommutatorL2 c) ↔
      ∀ j, c j * X = X * c j := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h j
    apply sub_eq_zero.mp
    ext i k
    have hc := congrArg
      (fun z : EuclideanSpace ℂ (Fin s × (n × n)) =>
        WithLp.ofLp z (j, (i, k))) h
    simpa [jointCommutatorL2] using hc
  · intro h
    ext q
    rcases q with ⟨j, i, k⟩
    simp [jointCommutatorL2, h j]

/-- The exact Hilbert--Schmidt commutant Poincare inequality.  The hypothesis
on `X-P` is precisely the defining property of Hilbert--Schmidt orthogonal
projection onto the commutant. -/
theorem matrix_commutant_poincare_gap {n : Type*} [Fintype n]
    {s : ℕ} (c : Fin s → Matrix n n ℂ) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ (X P : Matrix n n ℂ),
      (∀ j, c j * P = P * c j) →
      matrixL2 (X - P) ∈ (LinearMap.ker (jointCommutatorL2 c))ᗮ →
      lam * (((X - P)ᴴ * (X - P)).trace).re ≤
        ∑ j, (((c j * X - X * c j)ᴴ *
          (c j * X - X * c j)).trace).re := by
  obtain ⟨lam, hlam, hgap⟩ :=
    finite_dimensional_projected_kernel_gap (jointCommutatorL2 c)
  refine ⟨lam, hlam, ?_⟩
  intro X P hP horth
  have hp : matrixL2 P ∈ LinearMap.ker (jointCommutatorL2 c) :=
    (matrixL2_mem_jointCommutator_ker_iff c P).2 hP
  have h := hgap (matrixL2 X) (matrixL2 P) hp
    (by simpa only [← matrixL2_sub] using horth)
  simpa only [← matrixL2_sub, matrixL2_norm_sq,
    jointCommutatorL2_norm_sq] using h

/-- The sharp version of the finite commutant gap.  When the orthogonal
complement of the commutant is nonzero, `lam` is an actual least eigenvalue of
the Gram matrix of the restricted joint commutator, not merely an unspecified
positive lower bound. -/
theorem matrix_commutant_least_eigenvalue_gap {n : Type*} [Fintype n]
    {s : ℕ} (c : Fin s → Matrix n n ℂ) :
    let K : Submodule ℂ (EuclideanSpace ℂ (n × n)) :=
      (LinearMap.ker (jointCommutatorL2 c))ᗮ
    K = ⊥ ∨
      ∃ (r : ℕ) (G : Matrix (Fin r) (Fin r) ℂ)
        (hG : G.PosDef) (lam : ℝ),
        r = Module.finrank ℂ K
        ∧ 0 < lam
        ∧ (∃ i : Fin r, lam = hG.1.eigenvalues i)
        ∧ (∀ i : Fin r, lam ≤ hG.1.eigenvalues i)
        ∧ ∀ (X P : Matrix n n ℂ),
          (∀ j, c j * P = P * c j) →
          matrixL2 (X - P) ∈ K →
          lam * (((X - P)ᴴ * (X - P)).trace).re ≤
            ∑ j, (((c j * X - X * c j)ᴴ *
              (c j * X - X * c j)).trace).re := by
  dsimp only
  obtain hzero | ⟨r, G, hG, lam, hr, hlam, heig, hleast, hgap⟩ :=
    finite_dimensional_kernel_least_eigenvalue_gap (jointCommutatorL2 c)
  · exact Or.inl hzero
  · right
    refine ⟨r, G, hG, lam, hr, hlam, heig, hleast, ?_⟩
    intro X P hP horth
    have hp : matrixL2 P ∈ LinearMap.ker (jointCommutatorL2 c) :=
      (matrixL2_mem_jointCommutator_ker_iff c P).2 hP
    have hTP : jointCommutatorL2 c (matrixL2 P) = 0 :=
      LinearMap.mem_ker.mp hp
    have hT : jointCommutatorL2 c (matrixL2 (X - P)) =
        jointCommutatorL2 c (matrixL2 X) := by
      rw [matrixL2_sub, map_sub, hTP, sub_zero]
    have h := hgap (matrixL2 (X - P)) horth
    rw [hT, matrixL2_norm_sq, jointCommutatorL2_norm_sq] at h
    exact h

/-- Exact assembly for the missing spectral-gap clause of the commutant audit:
the trace-energy kernel theorem is paired with the actual least positive
eigenvalue of the restricted commutator Gram matrix.  The zero-complement
branch records the only case in which no positive eigenvalue exists. -/
theorem commutant_audit_gap_exact :
    (∀ {n : Type*} [Fintype n] {s : ℕ}
      (c : Fin s → Matrix n n ℂ) (X P : Matrix n n ℂ),
      (∀ j, c j * P = P * c j) →
      ((∑ j, (((c j * X - X * c j)ᴴ
          * (c j * X - X * c j)).trace).re) = 0
        ↔ ∀ j, c j * X = X * c j))
    ∧ (∀ {n : Type*} [Fintype n] {s : ℕ}
      (c : Fin s → Matrix n n ℂ),
      let K : Submodule ℂ (EuclideanSpace ℂ (n × n)) :=
        (LinearMap.ker (jointCommutatorL2 c))ᗮ
      K = ⊥ ∨
        ∃ (r : ℕ) (G : Matrix (Fin r) (Fin r) ℂ)
          (hG : G.PosDef) (lam : ℝ),
          r = Module.finrank ℂ K
          ∧ 0 < lam
          ∧ (∃ i : Fin r, lam = hG.1.eigenvalues i)
          ∧ (∀ i : Fin r, lam ≤ hG.1.eigenvalues i)
          ∧ ∀ (X P : Matrix n n ℂ),
            (∀ j, c j * P = P * c j) →
            matrixL2 (X - P) ∈ K →
            lam * (((X - P)ᴴ * (X - P)).trace).re ≤
              ∑ j, (((c j * X - X * c j)ᴴ *
                (c j * X - X * c j)).trace).re) := by
  refine ⟨?_, ?_⟩
  · intro n _ s c X P hP
    exact (commutant_audit c X P hP).1
  · intro n _ s c
    exact matrix_commutant_least_eigenvalue_gap c

end NCG
