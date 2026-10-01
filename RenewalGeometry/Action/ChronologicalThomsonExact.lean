/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.SameCylinderTransferExact

/-!
# Chronological source-shorted Thomson correction
  (`thm:supp-chronological-thomson`, `eq:supp-thomson-Ps`, `eq:supp-thomson-L`,
  `eq:supp-thomson-variance`, `eq:supp-thomson-hstar`, `eq:supp-thomson-energy`;
  emergent-spacetime manuscript)

Finite stage spaces `X, Y`; a faithful source law `α > 0`; a stochastic
comparator `Q x y = Q(y | x) ≥ 0` with `∑_y Q(y | x) = 1`; the admitted support
`𝓔 = {(x,y) : Q(y | x) > 0} = {R > 0}` with `R(x,y) = α(x) Q(y | x)`.
Edge arrays are functions `h : X → Y → ℝ` vanishing off `𝓔`
(`SupportedOn Q h`); the weighted norm is `‖h‖²_{R⁻¹} = ∑ h² / R`
(`SameCylinderTransfer.invWeightNormSq`), `A h = ∑_y h(·,y)`, `B h = ∑_x h(x,·)`,
with weighted adjoints `A* f = R f(x)`, `B* g = R g(y)` (`srcAdj`, `tgtAdj`,
adjointness in `inner_srcAdj`, `inner_tgtAdj`).

* `ChronologicalThomson.sourceShort` is `P_s = I - A* diag(α)⁻¹ A`
  (`eq:supp-thomson-Ps`); `sourceShort_isOrthogonalProjection` shows it is the
  `R⁻¹`-orthogonal projection onto `ker A`.
* `thomson_L_eq`: `B P_s B* = diag(ρ) - Qᵀ diag(α) Q` (`eq:supp-thomson-L`), as
  operators and as the matrix `thomsonMatrix`; `thomsonMatrix_posSemidef`:
  `𝓛_{α,Q} ⪰ 0`; `thomson_variance_identity` (`eq:supp-thomson-variance`).
* The Moore–Penrose inverse: `IsPenroseInverse L M` (the four Penrose
  equations); `exists_isPenroseInverse` constructs one for every real symmetric
  matrix (spectral theorem), and `IsPenroseInverse.unique` shows it is unique, so
  `thomsonPinv α Q` *is* `𝓛_{α,Q}^†`.
* `thomson_solvable_iff`: `A h = 0`, `B h = d` is solvable by an edge array iff
  `d ∈ Ran 𝓛_{α,Q}`.
* `thomson_min_norm`: on that branch, `h_* = R (u(y) - (Qu)(x))` with
  `u = 𝓛† d` (`eq:supp-thomson-hstar`) is feasible, every feasible `h` satisfies
  `‖h‖² = ‖h_*‖² + ‖h - h_*‖²`, so `h_*` is the unique minimum-norm solution, and
  `‖h_*‖²_{R⁻¹} = ⟨d, 𝓛† d⟩` (`eq:supp-thomson-energy`).
* `thomson_leverage`: if `|u(y) - (Qu)(x)| ≤ 1/2` on `𝓔` then `R + h_* ≥ 0` with
  source marginal `α` and target marginal `β` (`d = β - ρ`).
* `thm_supp_chronological_thomson` assembles the theorem.
-/

namespace RenewalGeometry
namespace ChronologicalThomson

open Finset Matrix SameCylinderTransfer

noncomputable section

/-! ## Real Moore–Penrose inverse of a symmetric matrix -/

section Penrose

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The four Penrose equations: `M` is the Moore–Penrose inverse of `L`. -/
def IsPenroseInverse (L M : Matrix n n ℝ) : Prop :=
  L * M * L = L ∧ M * L * M = M ∧ (L * M)ᵀ = L * M ∧ (M * L)ᵀ = M * L

/-- Reciprocal of a real symmetric eigenvalue, extended by zero on the kernel. -/
def recipEigenvalue (A : Matrix n n ℝ) (hA : A.IsHermitian) (i : n) : ℝ :=
  if hA.eigenvalues i = 0 then 0 else (hA.eigenvalues i)⁻¹

/-- Spectral Moore–Penrose inverse of a real symmetric matrix. -/
def symmPinv (A : Matrix n n ℝ) (hA : A.IsHermitian) : Matrix n n ℝ :=
  Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary (diagonal (recipEigenvalue A hA))

theorem symmPinv_spec (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    IsPenroseInverse A (symmPinv A hA) ∧ (symmPinv A hA)ᵀ = symmPinv A hA := by
  have hA' : A = Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) hA.eigenvectorUnitary
      (diagonal hA.eigenvalues) := by simpa using hA.spectral_theorem
  set φ := Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) hA.eigenvectorUnitary
  set D := diagonal hA.eigenvalues
  set R := diagonal (recipEigenvalue A hA)
  have h1 : D * R * D = D := by
    simp only [D, R, diagonal_mul_diagonal]; congr 1; funext i
    by_cases h : hA.eigenvalues i = 0 <;> simp [recipEigenvalue, h]
  have h2 : R * D * R = R := by
    simp only [D, R, diagonal_mul_diagonal]; congr 1; funext i
    by_cases h : hA.eigenvalues i = 0 <;> simp [recipEigenvalue, h]
  have hc : D * R = R * D := by
    simp only [D, R, diagonal_mul_diagonal]; congr 1; funext i; ring
  have hRh : (φ R)ᵀ = φ R := by
    have hdiag : (R).IsHermitian := by
      rw [Matrix.isHermitian_diagonal_iff]; intro i; simp [isSelfAdjoint_iff]
    have := (hdiag.isSelfAdjoint.map φ).star_eq
    simpa [Matrix.star_eq_conjTranspose] using this
  have hDh : (φ D)ᵀ = φ D := by
    rw [← hA']; simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.eq
  have hcomm : φ D * φ R = φ R * φ D := by rw [← map_mul, ← map_mul, hc]
  change (A * φ R * A = A ∧ φ R * A * φ R = φ R ∧ (A * φ R)ᵀ = A * φ R ∧
    (φ R * A)ᵀ = φ R * A) ∧ (φ R)ᵀ = φ R
  rw [hA']
  refine ⟨⟨by rw [← map_mul, ← map_mul, h1], by rw [← map_mul, ← map_mul, h2], ?_, ?_⟩, hRh⟩
  · rw [transpose_mul, hRh, hDh, hcomm]
  · rw [transpose_mul, hRh, hDh, hcomm]

/-- Every real symmetric matrix has a Moore–Penrose inverse. -/
theorem exists_isPenroseInverse (L : Matrix n n ℝ) (hL : Lᵀ = L) :
    ∃ M, IsPenroseInverse L M := by
  have hA : L.IsHermitian := by
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hL
  exact ⟨_, (symmPinv_spec L hA).1⟩

/-- The Moore–Penrose inverse is unique. -/
theorem IsPenroseInverse.unique {L M M' : Matrix n n ℝ} (h : IsPenroseInverse L M)
    (h' : IsPenroseInverse L M') : M = M' := by
  obtain ⟨a1, a2, a3, a4⟩ := h
  obtain ⟨b1, b2, b3, b4⟩ := h'
  have hLM : L * M = L * M' := by
    calc L * M = (L * M)ᵀ := a3.symm
      _ = ((L * M') * (L * M))ᵀ := by
          rw [show (L * M') * (L * M) = (L * M' * L) * M by simp only [Matrix.mul_assoc], b1]
      _ = (L * M)ᵀ * (L * M')ᵀ := by rw [transpose_mul]
      _ = L * M * (L * M') := by rw [a3, b3]
      _ = L * M' := by rw [← Matrix.mul_assoc, a1]
  have hML : M * L = M' * L := by
    calc M * L = (M * L)ᵀ := a4.symm
      _ = ((M * L) * (M' * L))ᵀ := by
          rw [show (M * L) * (M' * L) = M * (L * M' * L) by simp only [Matrix.mul_assoc], b1]
      _ = (M' * L)ᵀ * (M * L)ᵀ := by rw [transpose_mul]
      _ = M' * L * (M * L) := by rw [a4, b4]
      _ = M' * L := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc L, a1]
  calc M = M * L * M := a2.symm
    _ = M * (L * M') := by rw [Matrix.mul_assoc, hLM]
    _ = M' * L * M' := by rw [← Matrix.mul_assoc, hML]
    _ = M' := b2

end Penrose

/-! ## Edge geometry -/

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]

/-- Edge arrays supported on the admitted support `𝓔 = {Q > 0}`. -/
def SupportedOn (Q h : X → Y → ℝ) : Prop := ∀ x y, Q x y = 0 → h x y = 0

/-- Source map `(A h)(x) = ∑_y h(x,y)`. -/
def srcMap (h : X → Y → ℝ) (x : X) : ℝ := ∑ y, h x y

/-- Target map `(B h)(y) = ∑_x h(x,y)`. -/
def tgtMap (h : X → Y → ℝ) (y : Y) : ℝ := ∑ x, h x y

/-- Weighted adjoint of `A`: `(A* f)(x,y) = R(x,y) f(x)`. -/
def srcAdj (α : X → ℝ) (Q : X → Y → ℝ) (f : X → ℝ) : X → Y → ℝ :=
  fun x y => refCoupling α Q x y * f x

/-- Weighted adjoint of `B`: `(B* g)(x,y) = R(x,y) g(y)`. -/
def tgtAdj (α : X → ℝ) (Q : X → Y → ℝ) (g : Y → ℝ) : X → Y → ℝ :=
  fun x y => refCoupling α Q x y * g y

/-- The `R⁻¹` inner product `⟪h, k⟫ = ∑ h k / R`. -/
def wInner (α : X → ℝ) (Q : X → Y → ℝ) (h k : X → Y → ℝ) : ℝ :=
  ∑ x, ∑ y, h x y * k x y / refCoupling α Q x y

/-- The source-shorting projection `P_s = I - A* diag(α)⁻¹ A`
(`eq:supp-thomson-Ps`). -/
def sourceShort (α : X → ℝ) (Q : X → Y → ℝ) (h : X → Y → ℝ) : X → Y → ℝ :=
  fun x y => h x y - srcAdj α Q (fun x => srcMap h x / α x) x y

section Geometry

variable (α : X → ℝ) (Q : X → Y → ℝ)

omit [DecidableEq Y] in
theorem refCoupling_eq_zero_of_supp {h : X → Y → ℝ} (hs : SupportedOn Q h) {x : X} {y : Y}
    (hR : refCoupling α Q x y = 0) (hα : 0 < α x) : h x y = 0 := by
  apply hs
  simpa [refCoupling, hα.ne'] using hR

omit [DecidableEq Y] in
/-- `A* ` is the `R⁻¹`-adjoint of `A` on edge arrays. -/
theorem inner_srcAdj (hα : ∀ x, 0 < α x) (f : X → ℝ) {h : X → Y → ℝ} (hs : SupportedOn Q h) :
    wInner α Q (srcAdj α Q f) h = ∑ x, f x * srcMap h x := by
  unfold wInner srcAdj srcMap
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hR : refCoupling α Q x y = 0
  · simp [hR, refCoupling_eq_zero_of_supp α Q hs hR (hα x)]
  · field_simp

omit [DecidableEq Y] in
/-- `B*` is the `R⁻¹`-adjoint of `B` on edge arrays. -/
theorem inner_tgtAdj (hα : ∀ x, 0 < α x) (g : Y → ℝ) {h : X → Y → ℝ} (hs : SupportedOn Q h) :
    wInner α Q (tgtAdj α Q g) h = ∑ y, g y * tgtMap h y := by
  unfold wInner tgtAdj tgtMap
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  by_cases hR : refCoupling α Q x y = 0
  · simp [hR, refCoupling_eq_zero_of_supp α Q hs hR (hα x)]
  · field_simp

omit [DecidableEq Y] in
theorem srcMap_srcAdj (hQ1 : ∀ x, ∑ y, Q x y = 1) (f : X → ℝ) (x : X) :
    srcMap (srcAdj α Q f) x = α x * f x := by
  simp only [srcMap, srcAdj, refCoupling]
  rw [← Finset.sum_mul, ← Finset.mul_sum, hQ1 x, mul_one]

omit [DecidableEq Y] in
theorem srcAdj_supported (f : X → ℝ) : SupportedOn Q (srcAdj α Q f) := by
  intro x y h0; simp [srcAdj, refCoupling, h0]

omit [DecidableEq Y] in
theorem tgtAdj_supported (g : Y → ℝ) : SupportedOn Q (tgtAdj α Q g) := by
  intro x y h0; simp [tgtAdj, refCoupling, h0]

omit [DecidableEq Y] in
/-- `P_s` is the `R⁻¹`-orthogonal projection onto `ker A`: it maps edge arrays
to edge arrays in `ker A`, fixes `ker A`, and its defect `h - P_s h` is
`R⁻¹`-orthogonal to every edge array in `ker A`. -/
theorem sourceShort_isOrthogonalProjection (hα : ∀ x, 0 < α x)
    (hQ1 : ∀ x, ∑ y, Q x y = 1) (h : X → Y → ℝ) (hs : SupportedOn Q h) :
    SupportedOn Q (sourceShort α Q h) ∧
    (∀ x, srcMap (sourceShort α Q h) x = 0) ∧
    ((∀ x, srcMap h x = 0) → sourceShort α Q h = h) ∧
    (∀ k, SupportedOn Q k → (∀ x, srcMap k x = 0) →
      wInner α Q (fun x y => h x y - sourceShort α Q h x y) k = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y h0; simp [sourceShort, hs x y h0, srcAdj, refCoupling, h0]
  · intro x
    have : srcMap (sourceShort α Q h) x
        = srcMap h x - srcMap (srcAdj α Q (fun x => srcMap h x / α x)) x := by
      simp [srcMap, sourceShort, Finset.sum_sub_distrib]
    rw [this, srcMap_srcAdj α Q hQ1]; field_simp [(hα x).ne']; ring
  · intro hA; funext x y; simp [sourceShort, hA, srcAdj]
  · intro k hk hAk
    have : (fun x y => h x y - sourceShort α Q h x y)
        = srcAdj α Q (fun x => srcMap h x / α x) := by
      funext x y; simp [sourceShort]
    rw [this, inner_srcAdj α Q hα _ hk]
    simp [hAk]

end Geometry

/-! ## The source-shorted operator -/

/-- The matrix `𝓛_{α,Q} = diag(ρ) - Qᵀ diag(α) Q` (`eq:supp-thomson-L`). -/
def thomsonMatrix [DecidableEq X] (α : X → ℝ) (Q : X → Y → ℝ) : Matrix Y Y ℝ :=
  diagonal (targetMarginal α Q) - (Matrix.of Q)ᵀ * diagonal α * Matrix.of Q

variable [DecidableEq X] (α : X → ℝ) (Q : X → Y → ℝ)

theorem thomsonMatrix_mulVec (u : Y → ℝ) :
    thomsonMatrix α Q *ᵥ u = thomsonOperator α Q u := by
  funext y
  simp only [thomsonMatrix, sub_mulVec, ← mulVec_mulVec, Pi.sub_apply, mulVec_diagonal,
    thomsonOperator, rowAvg]
  congr 1
  simp [mulVec, dotProduct, transpose_apply, of_apply, diagonal_apply, ite_mul,
    Finset.sum_ite_eq]

theorem thomsonMatrix_transpose : (thomsonMatrix α Q)ᵀ = thomsonMatrix α Q := by
  simp [thomsonMatrix, transpose_sub, transpose_mul, Matrix.mul_assoc]

/-- `B P_s B* = 𝓛_{α,Q}` (first equality of `eq:supp-thomson-L`). -/
theorem thomson_L_eq (hα : ∀ x, 0 < α x) (g : Y → ℝ) :
    tgtMap (sourceShort α Q (tgtAdj α Q g)) = thomsonMatrix α Q *ᵥ g := by
  rw [thomsonMatrix_mulVec]
  funext y
  have hA : ∀ x, srcMap (tgtAdj α Q g) x / α x = rowAvg Q g x := by
    intro x
    simp only [srcMap, tgtAdj, refCoupling, rowAvg]
    rw [div_eq_iff (hα x).ne', Finset.sum_mul]
    exact Finset.sum_congr rfl fun y _ => by ring
  simp only [tgtMap, sourceShort, hA, tgtAdj, srcAdj, refCoupling, thomsonOperator,
    targetMarginal, Finset.sum_sub_distrib, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun x _ => by ring

/-- The Thomson correction is `P_s B* u`. -/
theorem thomsonCorrection_eq_sourceShort (hα : ∀ x, 0 < α x) (u : Y → ℝ) :
    thomsonCorrection α Q u = sourceShort α Q (tgtAdj α Q u) := by
  funext x y
  have hA : srcMap (tgtAdj α Q u) x / α x = rowAvg Q u x := by
    simp only [srcMap, tgtAdj, refCoupling, rowAvg]
    rw [div_eq_iff (hα x).ne', Finset.sum_mul]
    exact Finset.sum_congr rfl fun y _ => by ring
  simp only [thomsonCorrection, sourceShort, hA, tgtAdj, srcAdj]
  ring

/-- `B h_* = 𝓛 u`. -/
theorem tgtMap_thomsonCorrection (hα : ∀ x, 0 < α x) (u : Y → ℝ) :
    tgtMap (thomsonCorrection α Q u) = thomsonMatrix α Q *ᵥ u := by
  rw [thomsonCorrection_eq_sourceShort α Q hα, thomson_L_eq α Q hα]

omit [DecidableEq X] [DecidableEq Y] in
theorem thomsonCorrection_supported (u : Y → ℝ) :
    SupportedOn Q (thomsonCorrection α Q u) := by
  intro x y h0; simp [thomsonCorrection, refCoupling, h0]

omit [DecidableEq X] [DecidableEq Y] in
/-- Pointwise form of the energy: `‖h_*‖²_{R⁻¹} = ∑_x α(x) Var_{Q(x,·)}(u)`. -/
theorem invWeightNormSq_thomsonCorrection_eq_variance (u : Y → ℝ) :
    invWeightNormSq (refCoupling α Q) (thomsonCorrection α Q u)
      = ∑ x, α x * ∑ y, Q x y * (u y - rowAvg Q u x) ^ 2 := by
  unfold invWeightNormSq
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [thomsonCorrection]
  by_cases h0 : refCoupling α Q x y = 0
  · have : α x * (Q x y * (u y - rowAvg Q u x) ^ 2) = 0 := by
      simp only [refCoupling] at h0
      rw [← mul_assoc, h0, zero_mul]
    simp [h0, this]
  · field_simp
    simp only [refCoupling]; ring

/-- The variance identity `eq:supp-thomson-variance`:
`⟨u, 𝓛_{α,Q} u⟩ = ∑_x α(x) Var_{Q(x,·)}(u)`. -/
theorem thomson_variance_identity (hQ1 : ∀ x, ∑ y, Q x y = 1) (u : Y → ℝ) :
    u ⬝ᵥ (thomsonMatrix α Q *ᵥ u) = ∑ x, α x * ∑ y, Q x y * (u y - rowAvg Q u x) ^ 2 := by
  rw [thomsonMatrix_mulVec, ← invWeightNormSq_thomsonCorrection_eq_variance,
    invWeightNormSq_thomsonCorrection α Q hQ1]
  rfl

/-- `𝓛_{α,Q} ⪰ 0` (`eq:supp-thomson-L`). -/
theorem thomsonMatrix_posSemidef (hα : ∀ x, 0 ≤ α x) (hQ : ∀ x y, 0 ≤ Q x y)
    (hQ1 : ∀ x, ∑ y, Q x y = 1) : (thomsonMatrix α Q).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun u => ?_⟩
  · simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
      thomsonMatrix_transpose α Q
  · have : star u = u := rfl
    rw [this, thomson_variance_identity α Q hQ1]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (hα x)
      (Finset.sum_nonneg fun y _ => mul_nonneg (hQ x y) (sq_nonneg _))

/-- Kernel of `𝓛`: if `𝓛 v = 0` then `v(y) = (Qv)(x)` on the admitted support. -/
theorem thomson_kernel (hα : ∀ x, 0 < α x) (hQ : ∀ x y, 0 ≤ Q x y)
    (hQ1 : ∀ x, ∑ y, Q x y = 1) (v : Y → ℝ) (hv : thomsonMatrix α Q *ᵥ v = 0)
    (x : X) (y : Y) (hxy : Q x y ≠ 0) : v y = rowAvg Q v x := by
  have h0 := thomson_variance_identity α Q hQ1 v
  rw [hv, dotProduct_zero] at h0
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => mul_nonneg (hα x).le
    (Finset.sum_nonneg fun y _ => mul_nonneg (hQ x y) (sq_nonneg _)))).1 h0.symm x
    (Finset.mem_univ _)
  have hrow : ∑ y, Q x y * (v y - rowAvg Q v x) ^ 2 = 0 := by
    rcases mul_eq_zero.1 hterm with h | h
    · exact absurd h (hα x).ne'
    · exact h
  have hy := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => mul_nonneg (hQ x y)
    (sq_nonneg _))).1 hrow y (Finset.mem_univ _)
  rcases mul_eq_zero.1 hy with h | h
  · exact absurd h hxy
  · exact sub_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 h)

/-- Feasible targets are orthogonal to `ker 𝓛`. -/
theorem feasible_orthogonal_kernel (hα : ∀ x, 0 < α x) (hQ : ∀ x y, 0 ≤ Q x y)
    (hQ1 : ∀ x, ∑ y, Q x y = 1) (h : X → Y → ℝ) (hs : SupportedOn Q h)
    (hA : ∀ x, srcMap h x = 0) (v : Y → ℝ) (hv : thomsonMatrix α Q *ᵥ v = 0) :
    tgtMap h ⬝ᵥ v = 0 := by
  have : tgtMap h ⬝ᵥ v = ∑ x, rowAvg Q v x * srcMap h x := by
    simp only [dotProduct, tgtMap, srcMap, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    by_cases hq : Q x y = 0
    · simp [hs x y hq]
    · rw [thomson_kernel α Q hα hQ hQ1 v hv x y hq]; ring
  rw [this]; simp [hA]

/-- If `M` is a Moore–Penrose inverse of the symmetric `L`, every vector
orthogonal to `ker L` lies in `Ran L`, namely `L (M d) = d`. -/
theorem penrose_range_of_orth {L M : Matrix Y Y ℝ} (hL : Lᵀ = L) (hM : IsPenroseInverse L M)
    (d : Y → ℝ) (hd : ∀ v, L *ᵥ v = 0 → d ⬝ᵥ v = 0) : L *ᵥ (M *ᵥ d) = d := by
  obtain ⟨h1, -, h3, -⟩ := hM
  set P : Matrix Y Y ℝ := 1 - L * M
  have hPt : Pᵀ = P := by simp [P, transpose_sub, h3]
  have hPL : P * L = 0 := by simp [P, Matrix.sub_mul, h1]
  have hLP : L * P = 0 := by
    have := congrArg transpose hPL
    rwa [transpose_mul, hL, hPt, transpose_zero] at this
  have hPP : P * P = P := by
    simp only [P, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    rw [← Matrix.mul_assoc, h1]; abel
  set w := P *ᵥ d
  have hw : L *ᵥ w = 0 := by simp [w, mulVec_mulVec, hLP]
  have hdw : d ⬝ᵥ w = 0 := hd w hw
  have hww : w ⬝ᵥ w = d ⬝ᵥ w := by
    simp only [w]
    nth_rw 1 [← vecMul_transpose]
    rw [← dotProduct_mulVec, mulVec_mulVec, hPt, hPP]
  have hw0 : w = 0 := by
    have : w ⬝ᵥ w = 0 := hww.trans hdw
    exact dotProduct_self_eq_zero.1 this
  have : d - L *ᵥ (M *ᵥ d) = 0 := by
    have : w = d - L *ᵥ (M *ᵥ d) := by
      simp [w, P, sub_mulVec, mulVec_mulVec]
    rw [← this, hw0]
  exact (sub_eq_zero.1 this).symm

/-- Solvability (`thm:supp-chronological-thomson`): the constraints `A h = 0`,
`B h = d` have a solution among edge arrays iff `d ∈ Ran 𝓛_{α,Q}`. -/
theorem thomson_solvable_iff (hα : ∀ x, 0 < α x) (hQ : ∀ x y, 0 ≤ Q x y)
    (hQ1 : ∀ x, ∑ y, Q x y = 1) (d : Y → ℝ) :
    (∃ h : X → Y → ℝ, SupportedOn Q h ∧ (∀ x, srcMap h x = 0) ∧ tgtMap h = d) ↔
      d ∈ Set.range (thomsonMatrix α Q).mulVec := by
  constructor
  · rintro ⟨h, hs, hA, hB⟩
    obtain ⟨M, hM⟩ := exists_isPenroseInverse _ (thomsonMatrix_transpose α Q)
    refine ⟨M *ᵥ d, penrose_range_of_orth (thomsonMatrix_transpose α Q) hM d ?_⟩
    intro v hv
    rw [← hB]; exact feasible_orthogonal_kernel α Q hα hQ hQ1 h hs hA v hv
  · rintro ⟨u, rfl⟩
    exact ⟨thomsonCorrection α Q u, thomsonCorrection_supported α Q u,
      thomsonCorrection_source_null α Q hQ1 u, tgtMap_thomsonCorrection α Q hα u⟩

/-- On the solvable branch, `u = 𝓛† d` solves `𝓛 u = d` for any Moore–Penrose
inverse. -/
theorem pinv_solves {M : Matrix Y Y ℝ} (hM : IsPenroseInverse (thomsonMatrix α Q) M)
    {d : Y → ℝ} (hd : d ∈ Set.range (thomsonMatrix α Q).mulVec) :
    thomsonMatrix α Q *ᵥ (M *ᵥ d) = d := by
  obtain ⟨u, rfl⟩ := hd
  rw [mulVec_mulVec, mulVec_mulVec, hM.1]

/-- Minimum-norm clause (`eq:supp-thomson-hstar`, `eq:supp-thomson-energy`).
For `d ∈ Ran 𝓛` and `u = M d` with `M = 𝓛†`, the correction
`h_* = R (u(y) - (Qu)(x))` is a feasible edge array; every feasible edge array
`h` satisfies `‖h‖² = ‖h_*‖² + ‖h - h_*‖²` (so `‖h_*‖ ≤ ‖h‖`, with equality only
for `h = h_*`); and `‖h_*‖²_{R⁻¹} = ⟨d, 𝓛† d⟩`. -/
theorem thomson_min_norm (hα : ∀ x, 0 < α x) (hQ : ∀ x y, 0 ≤ Q x y)
    (hQ1 : ∀ x, ∑ y, Q x y = 1) {M : Matrix Y Y ℝ}
    (hM : IsPenroseInverse (thomsonMatrix α Q) M) {d : Y → ℝ}
    (hd : d ∈ Set.range (thomsonMatrix α Q).mulVec) :
    let u := M *ᵥ d
    let hs := thomsonCorrection α Q u
    (SupportedOn Q hs ∧ (∀ x, srcMap hs x = 0) ∧ tgtMap hs = d) ∧
    (∀ h : X → Y → ℝ, SupportedOn Q h → (∀ x, srcMap h x = 0) → tgtMap h = d →
      invWeightNormSq (refCoupling α Q) h
        = invWeightNormSq (refCoupling α Q) hs
          + invWeightNormSq (refCoupling α Q) (fun x y => h x y - hs x y)) ∧
    (∀ h : X → Y → ℝ, SupportedOn Q h → (∀ x, srcMap h x = 0) → tgtMap h = d →
      invWeightNormSq (refCoupling α Q) hs ≤ invWeightNormSq (refCoupling α Q) h ∧
      (invWeightNormSq (refCoupling α Q) h ≤ invWeightNormSq (refCoupling α Q) hs →
        h = hs)) ∧
    invWeightNormSq (refCoupling α Q) hs = d ⬝ᵥ (M *ᵥ d) := by
  intro u hs
  have hu : thomsonMatrix α Q *ᵥ u = d := pinv_solves α Q hM hd
  have hfeas : SupportedOn Q hs ∧ (∀ x, srcMap hs x = 0) ∧ tgtMap hs = d :=
    ⟨thomsonCorrection_supported α Q u, thomsonCorrection_source_null α Q hQ1 u,
      (tgtMap_thomsonCorrection α Q hα u).trans hu⟩
  have hRnn : ∀ x y, 0 ≤ refCoupling α Q x y := fun x y => mul_nonneg (hα x).le (hQ x y)
  -- Pythagoras
  have hpyth : ∀ h : X → Y → ℝ, SupportedOn Q h → (∀ x, srcMap h x = 0) → tgtMap h = d →
      invWeightNormSq (refCoupling α Q) h
        = invWeightNormSq (refCoupling α Q) hs
          + invWeightNormSq (refCoupling α Q) (fun x y => h x y - hs x y) := by
    intro h hsupp hA hB
    set k : X → Y → ℝ := fun x y => h x y - hs x y with hk
    have hkA : ∀ x, srcMap k x = 0 := by
      intro x
      have e1 := hA x; have e2 := hfeas.2.1 x
      simp only [srcMap] at e1 e2 ⊢
      simp only [k, Finset.sum_sub_distrib, e1, e2, sub_zero]
    have hkB : tgtMap k = 0 := by
      funext y
      have := congrFun hB y; have h2 := congrFun hfeas.2.2 y
      simp only [tgtMap] at this h2
      simp [k, tgtMap, Finset.sum_sub_distrib, this, h2]
    -- cross term vanishes
    have hcross : ∑ x, ∑ y, hs x y * k x y / refCoupling α Q x y = 0 := by
      have : ∀ x y, hs x y * k x y / refCoupling α Q x y
          = (u y - rowAvg Q u x) * k x y := by
        intro x y
        simp only [hs, thomsonCorrection]
        by_cases h0 : refCoupling α Q x y = 0
        · have hq : Q x y = 0 := by simpa [refCoupling, (hα x).ne'] using h0
          simp [h0, k, hsupp x y hq, hfeas.1 x y hq]
        · field_simp
      simp only [this, sub_mul, Finset.sum_sub_distrib]
      have e1 : ∑ x, ∑ y, u y * k x y = ∑ y, u y * tgtMap k y := by
        rw [Finset.sum_comm]; simp [tgtMap, Finset.mul_sum]
      have e2 : ∑ x, ∑ y, rowAvg Q u x * k x y = ∑ x, rowAvg Q u x * srcMap k x := by
        simp [srcMap, Finset.mul_sum]
      rw [e1, e2, hkB]; simp [hkA]
    unfold invWeightNormSq
    have hpt : ∀ x y, h x y ^ 2 / refCoupling α Q x y
        = hs x y ^ 2 / refCoupling α Q x y + k x y ^ 2 / refCoupling α Q x y
          + 2 * (hs x y * k x y / refCoupling α Q x y) := by
      intro x y
      have : h x y = hs x y + k x y := by simp [k]
      rw [this]; ring
    simp only [hpt, Finset.sum_add_distrib, ← Finset.mul_sum, hcross, mul_zero, add_zero]
  refine ⟨hfeas, hpyth, ?_, ?_⟩
  · intro h hsupp hA hB
    have hp := hpyth h hsupp hA hB
    have hk0 : 0 ≤ invWeightNormSq (refCoupling α Q) (fun x y => h x y - hs x y) :=
      Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
        div_nonneg (sq_nonneg _) (hRnn x y)
    refine ⟨by linarith, fun hle => ?_⟩
    have hz : invWeightNormSq (refCoupling α Q) (fun x y => h x y - hs x y) = 0 := by
      linarith
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      div_nonneg (sq_nonneg _) (hRnn x y)).1 hz
    funext x y
    have hrow := (Finset.sum_eq_zero_iff_of_nonneg fun y _ =>
      div_nonneg (sq_nonneg _) (hRnn x y)).1 (hall x (Finset.mem_univ _)) y (Finset.mem_univ _)
    by_cases hq : Q x y = 0
    · rw [hsupp x y hq, hfeas.1 x y hq]
    · have hR : refCoupling α Q x y ≠ 0 := mul_ne_zero (hα x).ne' hq
      have : (h x y - hs x y) ^ 2 = 0 := by
        rcases div_eq_zero_iff.1 hrow with h1 | h1
        · exact h1
        · exact absurd h1 hR
      exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  · rw [invWeightNormSq_thomsonCorrection α Q hQ1, ← thomsonMatrix_mulVec, hu]
    exact dotProduct_comm _ _

/-- Leverage clause: if `|u(y) - (Qu)(x)| ≤ 1/2` on the admitted support and
`𝓛 u = d = β - ρ`, then `R + h_*` is nonnegative with source marginal `α` and
target marginal `β`. -/
theorem thomson_leverage (hα : ∀ x, 0 < α x) (hQ : ∀ x y, 0 ≤ Q x y)
    (hQ1 : ∀ x, ∑ y, Q x y = 1) (β u : Y → ℝ)
    (hu : thomsonMatrix α Q *ᵥ u = fun y => β y - targetMarginal α Q y)
    (hlev : ∀ x y, Q x y ≠ 0 → |u y - rowAvg Q u x| ≤ 1 / 2) :
    (∀ x y, 0 ≤ refCoupling α Q x y + thomsonCorrection α Q u x y) ∧
    (∀ x, ∑ y, (refCoupling α Q x y + thomsonCorrection α Q u x y) = α x) ∧
    (∀ y, ∑ x, (refCoupling α Q x y + thomsonCorrection α Q u x y) = β y) := by
  refine ⟨fun x y => ?_, fun x => ?_, fun y => ?_⟩
  · have heq : refCoupling α Q x y + thomsonCorrection α Q u x y
        = refCoupling α Q x y * (1 + (u y - rowAvg Q u x)) := by
      simp only [thomsonCorrection]; ring
    rw [heq]
    by_cases hq : Q x y = 0
    · simp [refCoupling, hq]
    · have := (abs_le.1 (hlev x y hq)).1
      exact mul_nonneg (mul_nonneg (hα x).le (hQ x y)) (by linarith)
  · rw [Finset.sum_add_distrib, thomsonCorrection_source_null α Q hQ1 u x, add_zero]
    simp only [refCoupling]; rw [← Finset.mul_sum, hQ1 x, mul_one]
  · rw [Finset.sum_add_distrib]
    have h1 := congrFun (tgtMap_thomsonCorrection α Q hα u) y
    rw [hu] at h1
    simp only [tgtMap] at h1
    rw [h1]
    simp only [targetMarginal, refCoupling]; ring

/-- The Moore–Penrose inverse `𝓛_{α,Q}^†` (unique by `IsPenroseInverse.unique`). -/
def thomsonPinv : Matrix Y Y ℝ :=
  symmPinv (thomsonMatrix α Q) (by
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
      thomsonMatrix_transpose α Q)

theorem thomsonPinv_isPenroseInverse :
    IsPenroseInverse (thomsonMatrix α Q) (thomsonPinv α Q) :=
  (symmPinv_spec _ _).1

/-- `thm:supp-chronological-thomson`.  Faithful source law `α > 0`, stochastic
comparator `Q`, `R = α Q`, `ρ = ∑_x R`, target law `β`, `d = β - ρ`;
`𝓛† = thomsonPinv`, `u = 𝓛† d`, `h_* = R (u(y) - (Qu)(x))`.
1. `B P_s B* = diag(ρ) - Qᵀ diag(α) Q` and it is positive semidefinite;
2. `⟨u, 𝓛 u⟩ = ∑_x α(x) Var_{Q(x,·)}(u)` for every `u`;
3. `A h = 0`, `B h = d` is solvable by an edge array iff `d ∈ Ran 𝓛`;
4. on that branch `h_*` is feasible and is the unique minimum-`R⁻¹`-norm
   solution, with `‖h_*‖² = ⟨d, 𝓛† d⟩`;
5. if moreover `|u(y) - (Qu)(x)| ≤ 1/2` on `𝓔`, then `R + h_* ≥ 0` with source
   marginal `α` and target marginal `β`. -/
theorem thm_supp_chronological_thomson (hα : ∀ x, 0 < α x) (hQ : ∀ x y, 0 ≤ Q x y)
    (hQ1 : ∀ x, ∑ y, Q x y = 1) (β : Y → ℝ) :
    let d : Y → ℝ := fun y => β y - targetMarginal α Q y
    let u := thomsonPinv α Q *ᵥ d
    let hs := thomsonCorrection α Q u
    (∀ g, tgtMap (sourceShort α Q (tgtAdj α Q g)) = thomsonMatrix α Q *ᵥ g) ∧
    (thomsonMatrix α Q).PosSemidef ∧
    (∀ v : Y → ℝ, v ⬝ᵥ (thomsonMatrix α Q *ᵥ v)
      = ∑ x, α x * ∑ y, Q x y * (v y - rowAvg Q v x) ^ 2) ∧
    ((∃ h : X → Y → ℝ, SupportedOn Q h ∧ (∀ x, srcMap h x = 0) ∧ tgtMap h = d) ↔
      d ∈ Set.range (thomsonMatrix α Q).mulVec) ∧
    (d ∈ Set.range (thomsonMatrix α Q).mulVec →
      (SupportedOn Q hs ∧ (∀ x, srcMap hs x = 0) ∧ tgtMap hs = d) ∧
      (∀ h : X → Y → ℝ, SupportedOn Q h → (∀ x, srcMap h x = 0) → tgtMap h = d →
        invWeightNormSq (refCoupling α Q) hs ≤ invWeightNormSq (refCoupling α Q) h ∧
        (invWeightNormSq (refCoupling α Q) h ≤ invWeightNormSq (refCoupling α Q) hs →
          h = hs)) ∧
      invWeightNormSq (refCoupling α Q) hs = d ⬝ᵥ (thomsonPinv α Q *ᵥ d) ∧
      ((∀ x y, Q x y ≠ 0 → |u y - rowAvg Q u x| ≤ 1 / 2) →
        (∀ x y, 0 ≤ refCoupling α Q x y + hs x y) ∧
        (∀ x, ∑ y, (refCoupling α Q x y + hs x y) = α x) ∧
        (∀ y, ∑ x, (refCoupling α Q x y + hs x y) = β y))) := by
  intro d u hs
  refine ⟨thomson_L_eq α Q hα, thomsonMatrix_posSemidef α Q (fun x => (hα x).le) hQ hQ1,
    thomson_variance_identity α Q hQ1, thomson_solvable_iff α Q hα hQ hQ1 d, fun hd => ?_⟩
  obtain ⟨hfeas, -, hmin, hE⟩ :=
    thomson_min_norm α Q hα hQ hQ1 (thomsonPinv_isPenroseInverse α Q) hd
  exact ⟨hfeas, hmin, hE, thomson_leverage α Q hα hQ hQ1 β u
    (pinv_solves α Q (thomsonPinv_isPenroseInverse α Q) hd)⟩

end

end ChronologicalThomson
end RenewalGeometry
