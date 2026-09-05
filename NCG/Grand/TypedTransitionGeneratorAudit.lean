/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.EdgeResolvedOccurrenceEndpointClosure
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Unsplit-generator audit of typed transitions

This file formalizes `prop:SM-typed-transition-audit`.  It differentiates the
actual compressed exponential curve, identifies its one-Kraus second-order
coefficient, and then develops the finite weighted type-potential audit.
-/

open Matrix

namespace NCG
namespace TypedTransitionGeneratorAudit

noncomputable section

/-- The unsplit full-cell unitary curve at real time. -/
def typedUnitaryCurve {A : Type*} [CStarAlgebra A]
    (G : A) (s : ℝ) : A :=
  NormedSpace.exp (s • ((-Complex.I) • G))

/-- The compressed transition corner from protected type `a` to type `b`. -/
def typedTransitionCorner {A : Type*} [CStarAlgebra A]
    (pB pA G : A) (s : ℝ) : A :=
  pB * typedUnitaryCurve G s * pA

/-- The finite-time one-Kraus typed transition subchannel. -/
def typedTransitionSubchannel {A : Type*} [CStarAlgebra A]
    (pB pA G X : A) (s : ℝ) : A :=
  typedTransitionCorner pB pA G s * X *
    star (typedTransitionCorner pB pA G s)

attribute [-instance] NormedSpace.complexToReal in
/-- The genuine second derivative of the compressed exponential subchannel.
The factor `2` is removed by the manuscript's prefactor `1/2`. -/
theorem typedTransitionSubchannel_secondDerivative
    {A : Type*} [CStarAlgebra A]
    (pB pA G X : A) (hBA : pB * pA = 0) :
    iteratedDeriv 2 (typedTransitionSubchannel pB pA G X) 0 =
      2 • ((pB * G * pA) * X * star (pB * G * pA)) := by
  let H : A := (-Complex.I) • G
  let K : ℝ → A := fun s => pB * NormedSpace.exp (s • H) * pA
  let K' : ℝ → A := fun s =>
    pB * (NormedSpace.exp (s • H) * H) * pA
  let Ψ : ℝ → A :=
    (fun s => K s * X) * fun s => star (K s)
  let Ψ' : ℝ → A :=
    ((fun s => K' s * X) * fun s => star (K s)) +
      ((fun s => K s * X) * fun s => star (K' s))
  have hExp : ∀ s : ℝ,
      HasDerivAt (fun t : ℝ => NormedSpace.exp (t • H))
        (NormedSpace.exp (s • H) * H) s := by
    intro s
    exact hasDerivAt_exp_smul_const H s
  have hK : ∀ s : ℝ, HasDerivAt K (K' s) s := by
    intro s
    simpa [K, K'] using ((hExp s).const_mul pB).mul_const pA
  have hPsi : ∀ s : ℝ, HasDerivAt Ψ (Ψ' s) s := by
    intro s
    exact (((hK s).mul_const X).mul (hK s).star)
  have hKprime0 : HasDerivAt K' (pB * H ^ 2 * pA) 0 := by
    have h := ((hExp 0).mul_const H).const_mul pB
    have h' := h.mul_const pA
    simpa [K', pow_two, NormedSpace.exp_zero, mul_assoc] using h'
  have hK0 : K 0 = 0 := by
    simp [K, NormedSpace.exp_zero, hBA]
  have hKprimeValue0 : K' 0 = pB * H * pA := by
    simp [K', NormedSpace.exp_zero]
  have hPsiPrime0 : HasDerivAt Ψ'
      (2 • ((pB * H * pA) * X * star (pB * H * pA))) 0 := by
    have hleft := ((hKprime0.mul_const X).mul (hK 0).star)
    have hright := (((hK 0).mul_const X).mul hKprime0.star)
    have hsum := hleft.add hright
    simpa [Ψ', hK0, hKprimeValue0, two_smul, add_assoc] using hsum
  have hderiv : deriv Ψ = Ψ' := by
    funext s
    exact (hPsi s).deriv
  have hsecond : iteratedDeriv 2 Ψ 0 =
      2 • ((pB * H * pA) * X * star (pB * H * pA)) := by
    rw [show iteratedDeriv 2 Ψ = deriv (deriv Ψ) by
      rw [iteratedDeriv_succ, iteratedDeriv_one], hderiv]
    exact hPsiPrime0.deriv
  have hphase : (pB * H * pA) * X * star (pB * H * pA) =
      (pB * G * pA) * X * star (pB * G * pA) := by
    simp only [H, mul_smul_comm, smul_mul_assoc, star_smul]
    rw [← mul_smul]
    norm_num
  have hfun : typedTransitionSubchannel pB pA G X = Ψ := by
    funext s
    rfl
  rw [hfun, hsecond, hphase]

/-- Rank-one Choi matrix of the map `X ↦ B X Bᴴ`, using column
vectorization. -/
def oneKrausChoi {n : Type*} [Fintype n]
    (B : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ :=
  Matrix.vecMulVec (fun p => B p.2 p.1)
    (star fun p => B p.2 p.1)

/-- The Choi trace of a one-Kraus transition is its Hilbert--Schmidt weight. -/
theorem oneKrausChoi_mass_eq_hilbertSchmidtSq
    {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix n n ℂ) :
    EdgeResolvedOccurrenceEndpointClosure.choiMass (oneKrausChoi B) =
      EdgeResolvedOccurrenceEndpointClosure.hilbertSchmidtSq B := by
  unfold EdgeResolvedOccurrenceEndpointClosure.choiMass
    EdgeResolvedOccurrenceEndpointClosure.hilbertSchmidtSq oneKrausChoi
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  apply congrArg Complex.re
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change B j i * star (B j i) = star (B j i) * B j i
  rw [mul_comm]

attribute [-instance] NormedSpace.complexToReal in
/-- The normalized-source probability curvature, for any complex-linear trace
functional with the cyclic property.  Matrix trace is the intended instance. -/
theorem normalizedTypeSource_probabilityCurvature
    {A : Type*} [CStarAlgebra A]
    (τ : A →ₗ[ℂ] ℂ) (hcyc : ∀ Y Z : A, τ (Y * Z) = τ (Z * Y))
    (pB pA G : A) (hBA : pB * pA = 0) (hpA : pA * pA = pA)
    (dA : ℝ) (hdA : dA ≠ 0) :
    (τ (iteratedDeriv 2
      (typedTransitionSubchannel pB pA G
        (((dA : ℂ)⁻¹) • pA)) 0)).re =
      (2 / dA) * (τ (star (pB * G * pA) * (pB * G * pA))).re := by
  rw [typedTransitionSubchannel_secondDerivative pB pA G _ hBA]
  let B := pB * G * pA
  have hBpA : B * pA = B := by
    simp only [B, mul_assoc, hpA]
  change (τ (2 • (B * (((dA : ℂ)⁻¹) • pA) * star B))).re =
    (2 / dA) * (τ (star B * B)).re
  rw [mul_smul_comm, hBpA, smul_mul_assoc]
  rw [two_smul, map_add, Complex.add_re]
  rw [τ.map_smul, hcyc B (star B)]
  simp [Complex.mul_re]
  field_simp
  ring

/-- Diagonal protected type potential in a concrete finite carrier. -/
def protectedTypePotential {n Ty : Type*} [Fintype n] [DecidableEq n]
    (typeOf : n → Ty) (x : Ty → ℝ) : Matrix n n ℂ :=
  Matrix.diagonal fun i => (x (typeOf i) : ℂ)

/-- Hilbert--Schmidt weight of the generator corner from type `a` to type
`b`, written directly in a protected coordinate basis. -/
def typedTransitionWeight {n Ty : Type*}
    [Fintype n] [Fintype Ty] [DecidableEq Ty]
    (typeOf : n → Ty) (G : Matrix n n ℂ) (a b : Ty) : ℝ :=
  ∑ i, ∑ j, if typeOf i = b ∧ typeOf j = a
    then Complex.normSq (G i j) else 0

/-- The commutator Hilbert--Schmidt energy is exactly the ordered weighted
type graph form.  Hermiticity later identifies the two orientations and turns
the prefactor `1/2` into the manuscript's sum over unordered edges. -/
theorem protectedTypePotential_commutatorEnergy
    {n Ty : Type*} [Fintype n] [DecidableEq n]
    [Fintype Ty] [DecidableEq Ty]
    (typeOf : n → Ty) (G : Matrix n n ℂ) (x : Ty → ℝ) :
    (1 / 2 : ℝ) *
        EdgeResolvedOccurrenceEndpointClosure.hilbertSchmidtSq
          (G * protectedTypePotential typeOf x -
            protectedTypePotential typeOf x * G) =
      (1 / 2 : ℝ) * ∑ a, ∑ b,
        typedTransitionWeight typeOf G a b * (x a - x b) ^ 2 := by
  classical
  let D := protectedTypePotential typeOf x
  have hentry : ∀ i j,
      (G * D - D * G) i j =
        ((x (typeOf j) - x (typeOf i) : ℝ) : ℂ) * G i j := by
    intro i j
    simp [D, protectedTypePotential, Matrix.mul_apply,
      Matrix.diagonal_apply]
    ring
  have hgraph : (∑ a, ∑ b,
      typedTransitionWeight typeOf G a b * (x a - x b) ^ 2) =
      ∑ i, ∑ j, Complex.normSq (G i j) *
        (x (typeOf j) - x (typeOf i)) ^ 2 := by
    unfold typedTransitionWeight
    simp_rw [Finset.sum_mul]
    let f := fun (a b : Ty) (i j : n) =>
      (if typeOf i = b ∧ typeOf j = a
        then Complex.normSq (G i j) else 0) * (x a - x b) ^ 2
    change (∑ a, ∑ b, ∑ i, ∑ j, f a b i j) = _
    calc
      _ = ∑ a, ∑ i, ∑ b, ∑ j, f a b i j := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
      _ = ∑ a, ∑ i, ∑ j, ∑ b, f a b i j := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = ∑ i, ∑ a, ∑ j, ∑ b, f a b i j := by
        rw [Finset.sum_comm]
      _ = ∑ i, ∑ j, ∑ a, ∑ b, f a b i j := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = ∑ i, ∑ j, Complex.normSq (G i j) *
          (x (typeOf j) - x (typeOf i)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_eq_single (typeOf j)]
        · rw [Finset.sum_eq_single (typeOf i)]
          · simp [f]
          · intro b _ hb
            unfold f
            rw [if_neg]
            · simp
            · intro h
              exact hb h.1.symm
          · intro hb
            exact absurd (Finset.mem_univ _) hb
        · intro a _ ha
          apply Finset.sum_eq_zero
          intro b _
          unfold f
          rw [if_neg]
          · simp
          · intro h
            exact ha h.2.symm
        · intro ha
          exact absurd (Finset.mem_univ _) ha
  change (1 / 2 : ℝ) *
      EdgeResolvedOccurrenceEndpointClosure.hilbertSchmidtSq
        (G * D - D * G) =
    (1 / 2 : ℝ) * ∑ a, ∑ b,
      typedTransitionWeight typeOf G a b * (x a - x b) ^ 2
  unfold EdgeResolvedOccurrenceEndpointClosure.hilbertSchmidtSq
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  simp_rw [hentry]
  rw [hgraph]
  rw [Finset.sum_comm]
  simp only [← Complex.reCLM_apply, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [Complex.normSq, Complex.mul_re]
  ring

/-- Five one-generation type labels in the order `Q,u,d,L,e`. -/
inductive StandardModelType
  | Q | u | d | L | e
  deriving DecidableEq

/-- The displayed three-edge type-potential quadratic form. -/
def fiveTypePotentialEnergy (a b c : ℝ)
    (x : StandardModelType → ℝ) : ℝ :=
  a * (x .Q - x .u) ^ 2 + b * (x .Q - x .d) ^ 2 +
    c * (x .L - x .e) ^ 2

/-- Reduced quark Hessian after deleting the `Q` row and column. -/
def reducedQuarkHessian (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2 * a, 0;
     0, 2 * b]

/-- Reduced lepton Hessian after deleting the `L` row and column. -/
def reducedLeptonHessian (c : ℝ) : Matrix (Fin 1) (Fin 1) ℝ :=
  !![2 * c]

/-- The two reduced determinants are exactly `4ab` and `2c`. -/
theorem fiveType_reducedHessian_determinants (a b c : ℝ) :
    (reducedQuarkHessian a b).det = 4 * a * b ∧
    (reducedLeptonHessian c).det = 2 * c := by
  constructor
  · simp [reducedQuarkHessian, Matrix.det_fin_two]
    ring
  · simp [reducedLeptonHessian]

/-- With all three displayed edge weights positive, the type-potential kernel
is exactly the quark-constant plus lepton-constant subspace. -/
theorem fiveTypePotentialEnergy_eq_zero_iff
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (x : StandardModelType → ℝ) :
    fiveTypePotentialEnergy a b c x = 0 ↔
      x .Q = x .u ∧ x .Q = x .d ∧ x .L = x .e := by
  unfold fiveTypePotentialEnergy
  constructor
  · intro h
    have hqu : 0 ≤ a * (x .Q - x .u) ^ 2 :=
      mul_nonneg ha.le (sq_nonneg _)
    have hqd : 0 ≤ b * (x .Q - x .d) ^ 2 :=
      mul_nonneg hb.le (sq_nonneg _)
    have hle : 0 ≤ c * (x .L - x .e) ^ 2 :=
      mul_nonneg hc.le (sq_nonneg _)
    have hqu0 : a * (x .Q - x .u) ^ 2 = 0 := by nlinarith
    have hqd0 : b * (x .Q - x .d) ^ 2 = 0 := by nlinarith
    have hle0 : c * (x .L - x .e) ^ 2 = 0 := by nlinarith
    have hquSq : (x .Q - x .u) ^ 2 = 0 :=
      (mul_eq_zero.mp hqu0).resolve_left ha.ne'
    have hqdSq : (x .Q - x .d) ^ 2 = 0 :=
      (mul_eq_zero.mp hqd0).resolve_left hb.ne'
    have hleSq : (x .L - x .e) ^ 2 = 0 :=
      (mul_eq_zero.mp hle0).resolve_left hc.ne'
    constructor
    · exact sub_eq_zero.mp (sq_eq_zero_iff.mp hquSq)
    constructor
    · exact sub_eq_zero.mp (sq_eq_zero_iff.mp hqdSq)
    · exact sub_eq_zero.mp (sq_eq_zero_iff.mp hleSq)
  · rintro ⟨hqu, hqd, hle⟩
    have hud : x .u = x .d := hqu.symm.trans hqd
    simp [hqu, hud, hle]

/-- Complete incidence positivity implies a nonzero typed route; the reverse
implication is strictly false, as witnessed by a single nonzero quark edge. -/
theorem completeIncidence_stronger_than_nonzeroRoute :
    (∀ a b c : ℝ, 0 < a → 0 < b → 0 < c → 0 < a + b + c) ∧
    (∃ a b c : ℝ, 0 < a + b + c ∧ ¬(0 < a ∧ 0 < b ∧ 0 < c)) := by
  constructor
  · intro a b c ha hb hc
    linarith
  · exact ⟨1, 0, 0, by norm_num, by norm_num⟩

end

end TypedTransitionGeneratorAudit
end NCG
