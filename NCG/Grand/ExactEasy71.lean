import NCG.Grand.ResistanceCoframe

/-!
# Exact EASY 71: resistance reconstruction and coframe calibration

The Moore--Penrose inverse is represented by its Hermitian Penrose equations.
This is intrinsic (and avoids choosing coordinates for a library `pinv`).  We
prove dagger involutivity, derive centering of the dagger from centering of the
connected Hessian, and assemble the exact double-centering reconstruction.
The second half proves that an equivariant router commutes with every physical
symmetry, so a scalar commutant forces the manuscript's coframe collapse.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- `K` is the Hermitian Moore--Penrose inverse of `H`. -/
def IsHermitianPenroseInverse {n : Type} [Fintype n]
    (H K : Matrix n n ℝ) : Prop :=
  Hᵀ = H ∧ Kᵀ = K
    ∧ H * K * H = H ∧ K * H * K = K
    ∧ (H * K)ᵀ = H * K

/-- The Hermitian Penrose relation is involutive. -/
theorem hermitianPenroseInverse_symm
    {n : Type} [Fintype n]
    {H K : Matrix n n ℝ} (h : IsHermitianPenroseInverse H K) :
    IsHermitianPenroseInverse K H := by
  rcases h with ⟨hHT, hKT, hHKH, hKHK, hHKT⟩
  have hcomm : H * K = K * H := by
    calc
      H * K = (H * K)ᵀ := hHKT.symm
      _ = Kᵀ * Hᵀ := Matrix.transpose_mul H K
      _ = K * H := by rw [hKT, hHT]
  refine ⟨hKT, hHT, hKHK, hHKH, ?_⟩
  rw [Matrix.transpose_mul, hHT, hKT, hcomm]

/-- Resistance entries associated with a centered Green matrix. -/
def resistanceMatrix {n : Type} [Fintype n]
    (K : Matrix n n ℝ) : Matrix n n ℝ :=
  fun i j => K i i + K j j - 2 * K i j

/-- Scalar rescaling of a Green matrix rescales every squared resistance. -/
theorem resistanceMatrix_smul {n : Type} [Fintype n]
    (t : ℝ) (K : Matrix n n ℝ) :
    resistanceMatrix (t • K) = t • resistanceMatrix K := by
  ext i j
  simp [resistanceMatrix]
  ring

/-- `thm:action-resistance-coframe`, exact Moore--Penrose and resistance half.
The connected-kernel condition is used through `H 1 = 0`, i.e. its row sums
vanish; the Penrose equations then force the dagger `K` to be centered too. -/
theorem action_resistance_pinv_exact
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (H K : Matrix n n ℝ) (hMP : IsHermitianPenroseInverse H K)
    (hHcenter : ∀ i, ∑ j, H i j = 0) :
    let P₀ : Matrix n n ℝ := fun i j =>
      (if i = j then 1 else 0) - ((Fintype.card n : ℝ))⁻¹
    let R := resistanceMatrix K
    K = (-((2 : ℝ)⁻¹)) • (P₀ * R * P₀)
      ∧ IsHermitianPenroseInverse K H := by
  rcases hMP with ⟨hHT, hKT, hHKH, hKHK, hHKT⟩
  have hcomm : H * K = K * H := by
    calc
      H * K = (H * K)ᵀ := hHKT.symm
      _ = Kᵀ * Hᵀ := Matrix.transpose_mul H K
      _ = K * H := by rw [hKT, hHT]
  have hKright : K = (K * K) * H := by
    calc
      K = K * H * K := hKHK.symm
      _ = K * (H * K) := by simp only [Matrix.mul_assoc]
      _ = K * (K * H) := by rw [hcomm]
      _ = (K * K) * H := by simp only [Matrix.mul_assoc]
  have hKcenter : ∀ i, ∑ j, K i j = 0 := by
    intro i
    rw [hKright]
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hHcenter, mul_zero]
    simp
  let P₀ : Matrix n n ℝ := fun i j =>
    (if i = j then 1 else 0) - ((Fintype.card n : ℝ))⁻¹
  let R : Matrix n n ℝ := resistanceMatrix K
  have hrec : ∀ i j, (P₀ * (R * P₀)) i j = -2 * K i j := by
    exact (action_resistance_reconstruction K hKT hKcenter).2 P₀ R
      (by intro i j; rfl) (by intro i j; rfl)
  change K = (-((2 : ℝ)⁻¹)) • (P₀ * R * P₀)
      ∧ IsHermitianPenroseInverse K H
  refine ⟨?_, hermitianPenroseInverse_symm
    ⟨hHT, hKT, hHKH, hKHK, hHKT⟩⟩
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [Matrix.mul_assoc]
  rw [hrec]
  ring

/-- Equivariance of both sources makes the canonical router commute with every
physical symmetry.  The adjoint intertwining equations are the unitary duals
of the displayed equivariance equations. -/
theorem equivariant_coframe_router_scalar
    {g w y : Type} [Fintype w] [Fintype y]
    [DecidableEq w] [DecidableEq y]
    (A C : Matrix y w ℂ) (Hi : Matrix w w ℂ)
    (Rw : g → Matrix w w ℂ) (Ry : g → Matrix y y ℂ)
    (hHi1 : (Aᴴ * A) * Hi = 1) (hHi2 : Hi * (Aᴴ * A) = 1)
    (hHiH : Hiᴴ = Hi)
    (hA : ∀ s, A * Rw s = Ry s * A)
    (hAstar : ∀ s, Aᴴ * Ry s = Rw s * Aᴴ)
    (hC : ∀ s, C * Rw s = Ry s * C)
    (hscalar : ∀ T : Matrix w w ℂ,
      (∀ s, T * Rw s = Rw s * T) → ∃ c : ℂ, T = c • 1)
    (hzero : Cᴴ * ((1 : Matrix y y ℂ) - A * Hi * Aᴴ) * C = 0) :
    ∃ c : ℂ, C = c • A
      ∧ Cᴴ * C = ((starRingEnd ℂ) c * c) • (Aᴴ * A) := by
  let T : Matrix w w ℂ := Hi * (Aᴴ * C)
  have hHcomm : ∀ s, (Aᴴ * A) * Rw s = Rw s * (Aᴴ * A) := by
    intro s
    calc
      (Aᴴ * A) * Rw s = Aᴴ * (A * Rw s) := by
        simp only [Matrix.mul_assoc]
      _ = Aᴴ * (Ry s * A) := by rw [hA s]
      _ = (Aᴴ * Ry s) * A := by simp only [Matrix.mul_assoc]
      _ = (Rw s * Aᴴ) * A := by rw [hAstar s]
      _ = Rw s * (Aᴴ * A) := by simp only [Matrix.mul_assoc]
  have hHicomm : ∀ s, Hi * Rw s = Rw s * Hi := by
    intro s
    calc
      Hi * Rw s = Hi * Rw s * ((Aᴴ * A) * Hi) := by
        rw [hHi1, Matrix.mul_one]
      _ = Hi * (Rw s * (Aᴴ * A)) * Hi := by
        simp only [Matrix.mul_assoc]
      _ = Hi * ((Aᴴ * A) * Rw s) * Hi := by rw [hHcomm s]
      _ = (Hi * (Aᴴ * A)) * Rw s * Hi := by
        simp only [Matrix.mul_assoc]
      _ = Rw s * Hi := by rw [hHi2, Matrix.one_mul]
  have hXcomm : ∀ s, (Aᴴ * C) * Rw s = Rw s * (Aᴴ * C) := by
    intro s
    calc
      (Aᴴ * C) * Rw s = Aᴴ * (C * Rw s) := by
        simp only [Matrix.mul_assoc]
      _ = Aᴴ * (Ry s * C) := by rw [hC s]
      _ = (Aᴴ * Ry s) * C := by simp only [Matrix.mul_assoc]
      _ = (Rw s * Aᴴ) * C := by rw [hAstar s]
      _ = Rw s * (Aᴴ * C) := by simp only [Matrix.mul_assoc]
  have hTcomm : ∀ s, T * Rw s = Rw s * T := by
    intro s
    dsimp [T]
    calc
      (Hi * (Aᴴ * C)) * Rw s = Hi * ((Aᴴ * C) * Rw s) := by
        simp only [Matrix.mul_assoc]
      _ = Hi * (Rw s * (Aᴴ * C)) := by rw [hXcomm s]
      _ = (Hi * Rw s) * (Aᴴ * C) := by simp only [Matrix.mul_assoc]
      _ = (Rw s * Hi) * (Aᴴ * C) := by rw [hHicomm s]
      _ = Rw s * (Hi * (Aᴴ * C)) := by simp only [Matrix.mul_assoc]
  obtain ⟨c, hc⟩ := hscalar T hTcomm
  rcases action_coframe_router A C Hi hHi1 hHi2 hHiH with
    ⟨_, _, _, _, hfactor, _, hcollapse⟩
  have hCA : C = A * (Hi * (Aᴴ * C)) := hfactor.mp hzero
  exact ⟨c, hcollapse c hc hCA⟩

end NCG
