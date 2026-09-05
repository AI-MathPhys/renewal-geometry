/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteSpectralizationBlockNormExact

/-!
# Finite weighted graph Hodge--Dirac spectralization

This is the finite algebraic core of `thm:GT-NCG-graph-spectralization`.
Weights are absorbed into orthonormal coordinates on the vertex and oriented
edge Hilbert spaces.  The Dirac square has the weighted Hodge Laplacian as its
zero-form block, and the commutator norm is exactly the supremum of the local
carre-du-champ energies.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace NCG.FiniteWeightedGraphHodgeDirac

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Square-root conductance in orthonormal vertex coordinates. -/
def edgeWeight (mass : V → ℝ) (conductance : V → V → ℝ)
    (x y : V) : ℝ :=
  Real.sqrt (conductance x y / mass x)

/-- Weighted incidence matrix in orthonormal coordinates. Each endpoint is
divided by its own vertex mass; a self-loop has zero differential. -/
def differential (mass : V → ℝ) (conductance : V → V → ℝ) :
    Matrix (V × V) V ℝ :=
  fun xy z =>
    (if z = xy.2 then edgeWeight mass (fun i j => conductance j i) xy.2 xy.1 else 0) -
      (if z = xy.1 then edgeWeight mass conductance xy.1 xy.2 else 0)

/-- Hodge--Dirac matrix on zero-forms plus oriented one-forms. -/
def dirac (mass : V → ℝ) (conductance : V → V → ℝ) :
    Matrix (V ⊕ (V × V)) (V ⊕ (V × V)) ℝ :=
  Matrix.fromBlocks 0 (differential mass conductance)ᵀ
    (differential mass conductance) 0

/-- The lower commutator block for multiplication by a real vertex function. -/
def lipschitzBlock (mass : V → ℝ) (conductance : V → V → ℝ)
    (f : V → ℝ) : Matrix (V × V) V ℝ :=
  fun xy z => if z = xy.1 then
    edgeWeight mass conductance xy.1 xy.2 * (f xy.2 - f xy.1) else 0

/-- Local carré-du-champ energy. -/
def localEnergy (mass : V → ℝ) (conductance : V → V → ℝ)
    (f : V → ℝ) (x : V) : ℝ :=
  ∑ y, (edgeWeight mass conductance x y * (f y - f x)) ^ 2

/-- Multiplication on zero-forms. -/
def vertexRepresentation (f : V → ℝ) : Matrix V V ℝ := Matrix.diagonal f

/-- Multiplication at the terminal endpoint on oriented one-forms. -/
def edgeRepresentation (f : V → ℝ) : Matrix (V × V) (V × V) ℝ :=
  Matrix.diagonal fun xy => f xy.2

/-- Graded representation on zero- and one-forms. -/
def representation (f : V → ℝ) :
    Matrix (V ⊕ (V × V)) (V ⊕ (V × V)) ℝ :=
  Matrix.fromBlocks (vertexRepresentation f) 0 0 (edgeRepresentation f)

/-- The zero-form block of the Hodge--Dirac square is `d^* d`. -/
theorem dirac_square_zeroForm_block
    (mass : V → ℝ) (conductance : V → V → ℝ) :
    dirac mass conductance * dirac mass conductance =
      Matrix.fromBlocks
        ((differential mass conductance)ᵀ * differential mass conductance) 0 0
        (differential mass conductance * (differential mass conductance)ᵀ) := by
  simp [dirac, Matrix.fromBlocks_multiply]

/-- The lower block of `[D,pi(f)]` is the weighted graph gradient of `f`
acting by multiplication on the initial vertex. -/
theorem differential_commutator_lower
    (mass : V → ℝ) (conductance : V → V → ℝ) (f : V → ℝ) :
    differential mass conductance * vertexRepresentation f -
        edgeRepresentation f * differential mass conductance =
      lipschitzBlock mass conductance f := by
  ext xy z
  change
    (differential mass conductance * Matrix.diagonal f) xy z -
        (Matrix.diagonal (fun xy : V × V => f xy.2) *
          differential mass conductance) xy z =
      lipschitzBlock mass conductance f xy z
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [lipschitzBlock]
  by_cases hzx : z = xy.1
  · subst z
    by_cases hloop : xy.1 = xy.2
    · simp [differential, hloop]
      ring
    · simp [differential, hloop]
      ring
  · by_cases hzy : z = xy.2
    · subst z
      by_cases hloop : xy.2 = xy.1
      · exact (hzx hloop).elim
      · simp [differential, hloop, hzx]
        ring
    · simp [differential, hzx, hzy]

/-- Exact graded commutator matrix. -/
theorem dirac_commutator
    (mass : V → ℝ) (conductance : V → V → ℝ) (f : V → ℝ) :
    dirac mass conductance * representation f -
        representation f * dirac mass conductance =
      Matrix.fromBlocks 0 (-(lipschitzBlock mass conductance f)ᵀ)
        (lipschitzBlock mass conductance f) 0 := by
  let d := differential mass conductance
  let B := lipschitzBlock mass conductance f
  let V0 := vertexRepresentation f
  let E1 := edgeRepresentation f
  have hlower : d * V0 - E1 * d = B :=
    differential_commutator_lower mass conductance f
  have hV0 : V0ᵀ = V0 := by
    ext i j
    by_cases hij : i = j
    · subst j
      rfl
    · have hji : j ≠ i := Ne.symm hij
      simp [V0, vertexRepresentation, Matrix.diagonal, hij, hji]
  have hE1 : E1ᵀ = E1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      rfl
    · have hji : j ≠ i := Ne.symm hij
      simp [E1, edgeRepresentation, Matrix.diagonal, hij, hji]
  have ht := congrArg Matrix.transpose hlower
  have hupper : dᵀ * E1 - V0 * dᵀ = -Bᵀ := by
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
      hV0, hE1] at ht
    calc
      dᵀ * E1 - V0 * dᵀ = -(V0 * dᵀ - dᵀ * E1) := by abel
      _ = -Bᵀ := by rw [ht]
  change Matrix.fromBlocks 0 dᵀ d 0 * Matrix.fromBlocks V0 0 0 E1 -
      Matrix.fromBlocks V0 0 0 E1 * Matrix.fromBlocks 0 dᵀ d 0 =
    Matrix.fromBlocks 0 (-Bᵀ) B 0
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp
  · simpa using congrFun (congrFun hupper i) j
  · simpa using congrFun (congrFun hlower i) j
  · simp

/-- The square-root edge weights recover the conductance-over-mass formula. -/
theorem localEnergy_eq_conductance_formula
    (mass : V → ℝ) (conductance : V → V → ℝ) (f : V → ℝ)
    (hmass : ∀ x, 0 < mass x) (hc : ∀ x y, 0 ≤ conductance x y)
    (x : V) :
    localEnergy mass conductance f x =
      ∑ y, conductance x y / mass x * (f y - f x) ^ 2 := by
  unfold localEnergy edgeWeight
  apply Finset.sum_congr rfl
  intro y hy
  rw [mul_pow, Real.sq_sqrt (div_nonneg (hc x y) (hmass x).le)]

/-- The squared Lipschitz-block norm is the sup norm of the local energy.
On a finite vertex set, the function norm on the right is literally the
maximum over vertices in (SP.18). -/
theorem norm_sq_lipschitzBlock
    (mass : V → ℝ) (conductance : V → V → ℝ) (f : V → ℝ) :
    ‖lipschitzBlock mass conductance f‖ ^ 2 =
      ‖localEnergy mass conductance f‖ := by
  have hgram :
      (lipschitzBlock mass conductance f)ᵀ *
          lipschitzBlock mass conductance f =
        Matrix.diagonal (localEnergy mass conductance f) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, lipschitzBlock,
      Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single i]
      · simp only [if_pos, Finset.mem_univ, localEnergy]
        apply Finset.sum_congr rfl
        intro y hy
        ring
      · intro x hx hxi
        apply Finset.sum_eq_zero
        intro y hy
        simp [lipschitzBlock, hxi.symm]
      · simp
    · rw [if_neg hij]
      rw [Fintype.sum_prod_type]
      apply Finset.sum_eq_zero
      intro x hx
      apply Finset.sum_eq_zero
      intro y hy
      by_cases hxi : i = x
      · by_cases hxj : j = x
        · exact (hij (hxi.trans hxj.symm)).elim
        · simp [hxi, hxj]
      · simp [hxi]
  calc
    ‖lipschitzBlock mass conductance f‖ ^ 2 =
        ‖lipschitzBlock mass conductance f‖ *
          ‖lipschitzBlock mass conductance f‖ := by ring
    _ = ‖(lipschitzBlock mass conductance f)ᵀ *
          lipschitzBlock mass conductance f‖ := by
      symm
      exact Matrix.l2_opNorm_conjTranspose_mul_self _
    _ = ‖Matrix.diagonal (localEnergy mass conductance f)‖ := by rw [hgram]
    _ = ‖localEnergy mass conductance f‖ := Matrix.l2_opNorm_diagonal _

/-- Combining the graded block formula with the off-diagonal norm theorem
gives the exact commutator seminorm formula. -/
theorem norm_sq_dirac_commutator
    (mass : V → ℝ) (conductance : V → V → ℝ) (f : V → ℝ) :
    ‖dirac mass conductance * representation f -
        representation f * dirac mass conductance‖ ^ 2 =
      ‖localEnergy mass conductance f‖ := by
  rw [dirac_commutator]
  rw [show (lipschitzBlock mass conductance f)ᵀ =
      (lipschitzBlock mass conductance f)ᴴ by
        exact (Matrix.conjTranspose_eq_transpose_of_trivial _).symm]
  change ‖NCG.FiniteSpectralizationBlockNormExact.offDiagonal
      (lipschitzBlock mass conductance f)‖ ^ 2 = _
  rw [NCG.FiniteSpectralizationBlockNormExact.norm_offDiagonal]
  exact norm_sq_lipschitzBlock mass conductance f

/-- Connectedness of the positive-conductance support, expressed without a
choice of paths or a separate graph structure. -/
def ConductanceConnected (conductance : V → V → ℝ) : Prop :=
  ∀ x y, Relation.ReflTransGen (fun a b => 0 < conductance a b) x y

/-- On connected positive support, the graph gradient vanishes exactly on
constant vertex functions. -/
theorem lipschitzBlock_eq_zero_iff_constant
    [Nonempty V]
    (mass : V → ℝ) (conductance : V → V → ℝ) (f : V → ℝ)
    (hmass : ∀ x, 0 < mass x)
    (hconnected : ConductanceConnected conductance) :
    lipschitzBlock mass conductance f = 0 ↔
      ∃ a : ℝ, ∀ x, f x = a := by
  constructor
  · intro hB
    have hedge : ∀ x y, 0 < conductance x y → f x = f y := by
      intro x y hxy
      have hz := congrFun (congrFun hB (x, y)) x
      simp only [lipschitzBlock, if_pos, Matrix.zero_apply] at hz
      have hw : 0 < edgeWeight mass conductance x y := by
        exact Real.sqrt_pos.2 (div_pos hxy (hmass x))
      have hdiff : f y - f x = 0 :=
        (mul_eq_zero.mp hz).resolve_left hw.ne'
      exact (sub_eq_zero.mp hdiff).symm
    let x0 : V := Classical.choice (inferInstance : Nonempty V)
    refine ⟨f x0, fun x => ?_⟩
    have hp := hconnected x x0
    induction hp using Relation.ReflTransGen.head_induction_on with
    | refl => rfl
    | @head a c hac hcb ih => exact (hedge a c hac).trans ih
  · rintro ⟨a, ha⟩
    ext xy z
    simp [lipschitzBlock, ha]

/-- The kernel clause of (SP.18): on connected support the genuine Dirac
commutator seminorm vanishes exactly for constants. -/
theorem dirac_commutator_norm_eq_zero_iff_constant
    [Nonempty V]
    (mass : V → ℝ) (conductance : V → V → ℝ) (f : V → ℝ)
    (hmass : ∀ x, 0 < mass x)
    (hconnected : ConductanceConnected conductance) :
    ‖dirac mass conductance * representation f -
        representation f * dirac mass conductance‖ = 0 ↔
      ∃ a : ℝ, ∀ x, f x = a := by
  rw [dirac_commutator]
  rw [show (lipschitzBlock mass conductance f)ᵀ =
      (lipschitzBlock mass conductance f)ᴴ by
        exact (Matrix.conjTranspose_eq_transpose_of_trivial _).symm]
  change ‖NCG.FiniteSpectralizationBlockNormExact.offDiagonal
      (lipschitzBlock mass conductance f)‖ = 0 ↔ _
  rw [NCG.FiniteSpectralizationBlockNormExact.norm_offDiagonal, norm_eq_zero]
  exact lipschitzBlock_eq_zero_iff_constant mass conductance f hmass hconnected

/-! ## Homogeneous spatial scaling -/

/-- The FLRW/de Sitter scaling sends vertex mass to `a^3 m` and edge
conductance to `a c`. -/
def scaledMass (a : ℝ) (mass : V → ℝ) : V → ℝ := fun x => a ^ 3 * mass x

def scaledConductance (a : ℝ) (conductance : V → V → ℝ) : V → V → ℝ :=
  fun x y => a * conductance x y

/-- Under cubic mass and linear conductance scaling, every orthonormal edge
weight scales by `a^{-1}`. -/
theorem edgeWeight_scaled
    (a : ℝ) (ha : 0 < a) (mass : V → ℝ) (conductance : V → V → ℝ)
    (hmass : ∀ x, 0 < mass x) (hc : ∀ x y, 0 ≤ conductance x y)
    (x y : V) :
    edgeWeight (scaledMass a mass) (scaledConductance a conductance) x y =
      a⁻¹ * edgeWeight mass conductance x y := by
  have hden : 0 < scaledMass a mass x := by
    exact mul_pos (pow_pos ha 3) (hmass x)
  have hnum : 0 ≤ scaledConductance a conductance x y :=
    mul_nonneg ha.le (hc x y)
  have hbase : 0 ≤ conductance x y / mass x :=
    div_nonneg (hc x y) (hmass x).le
  have hleftSq :
      edgeWeight (scaledMass a mass) (scaledConductance a conductance) x y ^ 2 =
        scaledConductance a conductance x y / scaledMass a mass x := by
    exact Real.sq_sqrt (div_nonneg hnum hden.le)
  have hrightSq : edgeWeight mass conductance x y ^ 2 =
      conductance x y / mass x := Real.sq_sqrt hbase
  have hsq :
      edgeWeight (scaledMass a mass) (scaledConductance a conductance) x y ^ 2 =
        (a⁻¹ * edgeWeight mass conductance x y) ^ 2 := by
    rw [hleftSq, mul_pow, hrightSq]
    unfold scaledMass scaledConductance
    field_simp
  have hleftNonneg :
      0 ≤ edgeWeight (scaledMass a mass) (scaledConductance a conductance) x y :=
    Real.sqrt_nonneg _
  have hrightNonneg : 0 ≤ a⁻¹ * edgeWeight mass conductance x y :=
    mul_nonneg (inv_nonneg.mpr ha.le) (Real.sqrt_nonneg _)
  nlinarith

/-- The finite weighted differential scales by `a^{-1}`. -/
theorem differential_scaled
    (a : ℝ) (ha : 0 < a) (mass : V → ℝ) (conductance : V → V → ℝ)
    (hmass : ∀ x, 0 < mass x) (hc : ∀ x y, 0 ≤ conductance x y) :
    differential (scaledMass a mass) (scaledConductance a conductance) =
      a⁻¹ • differential mass conductance := by
  have htarget (x y : V) :
      edgeWeight (scaledMass a mass) (fun i j => scaledConductance a conductance j i) x y =
        a⁻¹ * edgeWeight mass (fun i j => conductance j i) x y :=
    edgeWeight_scaled a ha mass (fun i j => conductance j i) hmass
      (fun x y => hc y x) x y
  ext xy z
  rw [Matrix.smul_apply]
  simp only [differential, htarget,
    edgeWeight_scaled a ha mass conductance hmass hc, smul_eq_mul]
  split_ifs <;> ring

/-- The graph Hodge--Dirac obeys the de Sitter spatial scaling law
`D_a = a^{-1} D_0`. -/
theorem dirac_scaled
    (a : ℝ) (ha : 0 < a) (mass : V → ℝ) (conductance : V → V → ℝ)
    (hmass : ∀ x, 0 < mass x) (hc : ∀ x y, 0 ≤ conductance x y) :
    dirac (scaledMass a mass) (scaledConductance a conductance) =
      a⁻¹ • dirac mass conductance := by
  rw [dirac, dirac, differential_scaled a ha mass conductance hmass hc]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks_smul, Matrix.transpose_smul]

/-- Consequently the graph Lipschitz seminorm scales by `a^{-1}`. -/
theorem dirac_commutator_norm_scaled
    (a : ℝ) (ha : 0 < a) (mass : V → ℝ) (conductance : V → V → ℝ)
    (hmass : ∀ x, 0 < mass x) (hc : ∀ x y, 0 ≤ conductance x y)
    (f : V → ℝ) :
    ‖dirac (scaledMass a mass) (scaledConductance a conductance) *
          representation f - representation f *
          dirac (scaledMass a mass) (scaledConductance a conductance)‖ =
      a⁻¹ * ‖dirac mass conductance * representation f -
        representation f * dirac mass conductance‖ := by
  rw [dirac_scaled a ha mass conductance hmass hc]
  simp only [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_inv, abs_of_pos ha]

/-- The graph Lipschitz seminorm defined by the actual Dirac commutator. -/
def graphLipschitz (mass : V → ℝ) (conductance : V → V → ℝ)
    (f : V → ℝ) : ℝ :=
  ‖dirac mass conductance * representation f -
    representation f * dirac mass conductance‖

theorem graphLipschitz_smul
    (mass : V → ℝ) (conductance : V → V → ℝ)
    (a : ℝ) (f : V → ℝ) :
    graphLipschitz mass conductance (a • f) =
      |a| * graphLipschitz mass conductance f := by
  have hrep : representation (a • f) = a • representation f := by
    have hv : vertexRepresentation (a • f) = a • vertexRepresentation f := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [vertexRepresentation]
      · simp [vertexRepresentation, Matrix.diagonal, hij]
    have he : edgeRepresentation (a • f) = a • edgeRepresentation f := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [edgeRepresentation]
      · simp [edgeRepresentation, Matrix.diagonal, hij]
    rw [representation, representation, hv, he, Matrix.fromBlocks_smul]
    simp
  unfold graphLipschitz
  rw [hrep]
  simp only [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, norm_smul,
    Real.norm_eq_abs]

theorem graphLipschitz_scaled
    (a : ℝ) (ha : 0 < a) (mass : V → ℝ) (conductance : V → V → ℝ)
    (hmass : ∀ x, 0 < mass x) (hc : ∀ x y, 0 ≤ conductance x y)
    (f : V → ℝ) :
    graphLipschitz (scaledMass a mass) (scaledConductance a conductance) f =
      a⁻¹ * graphLipschitz mass conductance f :=
  dirac_commutator_norm_scaled a ha mass conductance hmass hc f

/-- Values in the finite Connes variational problem between two vertices. -/
def distanceValues (mass : V → ℝ) (conductance : V → V → ℝ)
    (x y : V) : Set ℝ :=
  {r | ∃ f : V → ℝ, graphLipschitz mass conductance f ≤ 1 ∧
    r = |f x - f y|}

/-- Exact homogeneous scaling of the attained finite Connes distance.  This
is the finite part of (SP.20): `L_a=a^{-1}L_0` and `d_a=a d_0`. -/
theorem connesDistance_scaled_isGreatest
    (a : ℝ) (ha : 0 < a) (mass : V → ℝ) (conductance : V → V → ℝ)
    (hmass : ∀ x, 0 < mass x) (hc : ∀ x y, 0 ≤ conductance x y)
    (x y : V) (d : ℝ)
    (hd : IsGreatest (distanceValues mass conductance x y) d) :
    IsGreatest
      (distanceValues (scaledMass a mass) (scaledConductance a conductance) x y)
      (a * d) := by
  rcases hd.1 with ⟨f, hfLip, rfl⟩
  constructor
  · refine ⟨a • f, ?_, ?_⟩
    · rw [graphLipschitz_scaled a ha mass conductance hmass hc,
        graphLipschitz_smul, abs_of_pos ha]
      rw [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
      exact hfLip
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [show a * f x - a * f y = a * (f x - f y) by ring,
          abs_mul, abs_of_pos ha]
  · rintro r ⟨g, hgLip, rfl⟩
    have hbase : graphLipschitz mass conductance (a⁻¹ • g) ≤ 1 := by
      rw [graphLipschitz_smul, abs_inv, abs_of_pos ha]
      simpa [graphLipschitz_scaled a ha mass conductance hmass hc] using hgLip
    have hupper := hd.2 ⟨a⁻¹ • g, hbase, rfl⟩
    simp only [Pi.smul_apply, smul_eq_mul] at hupper
    rw [← mul_sub, abs_mul, abs_inv, abs_of_pos ha] at hupper
    have ha0 : 0 ≤ a := ha.le
    calc
      |g x - g y| = a * (a⁻¹ * |g x - g y|) := by
        rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
      _ ≤ a * |f x - f y| := mul_le_mul_of_nonneg_left hupper ha0

/-- The first equality in **(SP.20)** for the de Sitter scale factor
`a(t)=exp(Ht)`. -/
theorem deSitter_graphLipschitz
    (H t : ℝ) (mass : V → ℝ) (conductance : V → V → ℝ)
    (hmass : ∀ x, 0 < mass x) (hc : ∀ x y, 0 ≤ conductance x y)
    (f : V → ℝ) :
    graphLipschitz (scaledMass (Real.exp (H * t)) mass)
        (scaledConductance (Real.exp (H * t)) conductance) f =
      Real.exp (-H * t) * graphLipschitz mass conductance f := by
  rw [graphLipschitz_scaled (Real.exp (H * t)) (Real.exp_pos _) mass conductance
      hmass hc]
  congr 1
  rw [show -H * t = -(H * t) by ring, Real.exp_neg]

/-- The distance equality in **(SP.20)** for `a(t)=exp(Ht)`, stated in
the attained finite Connes variational problem. -/
theorem deSitter_connesDistance_isGreatest
    (H t : ℝ) (mass : V → ℝ) (conductance : V → V → ℝ)
    (hmass : ∀ x, 0 < mass x) (hc : ∀ x y, 0 ≤ conductance x y)
    (x y : V) (d : ℝ)
    (hd : IsGreatest (distanceValues mass conductance x y) d) :
    IsGreatest
      (distanceValues (scaledMass (Real.exp (H * t)) mass)
        (scaledConductance (Real.exp (H * t)) conductance) x y)
      (Real.exp (H * t) * d) :=
  connesDistance_scaled_isGreatest (Real.exp (H * t)) (Real.exp_pos _)
    mass conductance hmass hc x y d hd

end NCG.FiniteWeightedGraphHodgeDirac
