/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import NCG.Grand.FiniteCalibrationAndDynamicalCounterexamples

/-!
# Finite reflection positivity: Gram compiler and pushforward

Exact finite encodings of `def:SMST-quantum-cylinder`,
`thm:SMST-reflection-Gram` (QRP.2–QRP.4) and
`thm:SMST-reflection-pushforward` (QRP.4a–QRP.5).

* `ReflectionCylinder`: finite `Ω`, involutive reflection `θ`, nonnegative
  reflection-invariant weight `μ`; `osForm` is the Osterwalder–Schrader form
  (QRP.1), Hermitian (`osForm_star`);
* `reflectionGram` (QRP.2) is Hermitian, and reflection positivity on the
  span of a family `f` is equivalent to `reflectionGram ⪰ 0` (QRP.3,
  `reflection_positive_iff_gram_posSemidef`); a coefficient vector of
  negative Gram energy gives an explicit observable of negative reflected
  norm (`negative_observable_of_not_posSemidef`); positivity and rank of
  the Gram are basis independent under invertible change of basis
  (`gram_congruence_posSemidef_iff`, `gram_congruence_rank`);
* boundary decomposition `Ω = B × B`, `θ(a,b) = (b,a)`: on functions of the
  second coordinate the form is the boundary kernel `K(a,b) = μ(a,b)`
  (`osForm_boundary`), so reflection positivity there is `K ⪰ 0`
  (`boundary_reflection_positive_iff`);
* `nearest_posSemidef` (QRP.4): for a Jordan split `G = G₊ - G₋` the
  Hilbert–Schmidt distance from `G` to the PSD cone is attained at `G₊` with
  value `‖G₋‖²_HS`; `jordan_split_exists` provides the split from the
  continuous functional calculus;
* pushforward: Hadamard products of PSD kernels (`hadamard_posSemidef`,
  QRP.4a), reflected-square insertions (`reflected_square_posSemidef`),
  exact marginals `V^* K V` (`marginal_posSemidef`, QRP.5) and
  reflection-equivariant pushforward (`pushforward_reflection_positive`).
  The pointwise-positive-but-not-reflection-positive witness is
  `FiniteCalibrationAndDynamicalCounterexamples.pointwise_positive_not_reflection_positive`.

Scope: Sylvester's full inertia invariance is not in Mathlib; we record the
positivity and rank invariants, which are what QRP.3 uses.
-/

open Finset Matrix
open scoped ComplexOrder MatrixOrder

-- finiteness / decidability instances are used only inside proofs (CFC, sums)
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace NCG
namespace SMSTReflectionPositivity

/-- A finite oriented quantum cylinder: reflection `θ` and reflection-invariant
nonnegative weight `μ`. -/
structure ReflectionCylinder (Ω : Type*) where
  θ : Ω → Ω
  θ_invol : ∀ ω, θ (θ ω) = ω
  μ : Ω → ℝ
  μ_nonneg : ∀ ω, 0 ≤ μ ω
  μ_inv : ∀ ω, μ (θ ω) = μ ω

variable {Ω : Type*} [Fintype Ω]

/-- The Osterwalder–Schrader form (QRP.1). -/
def osForm (C : ReflectionCylinder Ω) (F G : Ω → ℂ) : ℂ :=
  ∑ ω, star (F (C.θ ω)) * G ω * (C.μ ω : ℂ)

/-- The reflection as a permutation of `Ω`. -/
def ReflectionCylinder.perm (C : ReflectionCylinder Ω) : Equiv.Perm Ω :=
  Function.Involutive.toPerm C.θ C.θ_invol

/-- **Hermitian symmetry** of the OS form. -/
theorem osForm_star (C : ReflectionCylinder Ω) (F G : Ω → ℂ) :
    star (osForm C F G) = osForm C G F := by
  unfold osForm
  rw [star_sum]
  have h : ∀ ω, star (star (F (C.θ ω)) * G ω * (C.μ ω : ℂ))
      = star (G ω) * F (C.θ ω) * (C.μ ω : ℂ) := by
    intro ω
    simp only [star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    ring
  simp only [h]
  -- reindex by the involution
  rw [← Equiv.sum_comp C.perm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have hp : C.perm ω = C.θ ω := rfl
  rw [hp, C.θ_invol, C.μ_inv]

theorem osForm_self_real (C : ReflectionCylinder Ω) (F : Ω → ℂ) :
    (osForm C F F).im = 0 := by
  have := congrArg Complex.im (osForm_star C F F)
  simp only [Complex.star_def, Complex.conj_im] at this
  linarith

/-- Sesquilinearity: conjugate-linear in the first slot, linear in the second. -/
theorem osForm_sum_left {ι : Type*} (C : ReflectionCylinder Ω) (s : Finset ι)
    (c : ι → ℂ) (f : ι → Ω → ℂ) (G : Ω → ℂ) :
    osForm C (∑ i ∈ s, c i • f i) G = ∑ i ∈ s, star (c i) * osForm C (f i) G := by
  unfold osForm
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_sum, star_mul',
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => Finset.sum_congr rfl fun i _ => by ring

theorem osForm_sum_right {ι : Type*} (C : ReflectionCylinder Ω) (s : Finset ι)
    (c : ι → ℂ) (F : Ω → ℂ) (f : ι → Ω → ℂ) :
    osForm C F (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i * osForm C F (f i) := by
  unfold osForm
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => Finset.sum_congr rfl fun i _ => by ring

/-! ### The reflection Gram (QRP.2, QRP.3) -/

/-- The reflection Gram matrix of a finite family of positive-time observables. -/
def reflectionGram {m : Type*} (C : ReflectionCylinder Ω) (f : m → Ω → ℂ) :
    Matrix m m ℂ :=
  fun i j => osForm C (f i) (f j)

theorem reflectionGram_isHermitian {m : Type*} (C : ReflectionCylinder Ω) (f : m → Ω → ℂ) :
    (reflectionGram C f).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, reflectionGram]
  exact osForm_star C (f j) (f i)

/-- The reflected norm of `∑ cᵢ fᵢ` is the Gram energy `c^* G c`. -/
theorem osForm_combination {m : Type*} [Fintype m] (C : ReflectionCylinder Ω)
    (f : m → Ω → ℂ) (c : m → ℂ) :
    osForm C (∑ i, c i • f i) (∑ i, c i • f i)
      = star c ⬝ᵥ (reflectionGram C f *ᵥ c) := by
  rw [osForm_sum_left]
  simp only [dotProduct, mulVec, Pi.star_apply, reflectionGram]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [osForm_sum_right, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => by ring

/-- Reflection positivity on the span of `f`. -/
def ReflectionPositiveOn (C : ReflectionCylinder Ω) (A : Set (Ω → ℂ)) : Prop :=
  ∀ F ∈ A, 0 ≤ osForm C F F

/-- **(QRP.3)**: reflection positivity on the span of the family is
positive semidefiniteness of the reflection Gram. -/
theorem reflection_positive_iff_gram_posSemidef {m : Type*} [Fintype m]
    (C : ReflectionCylinder Ω) (f : m → Ω → ℂ) :
    ReflectionPositiveOn C (Submodule.span ℂ (Set.range f) : Set (Ω → ℂ))
      ↔ (reflectionGram C f).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  constructor
  · intro h
    refine ⟨reflectionGram_isHermitian C f, fun c => ?_⟩
    rw [← osForm_combination]
    apply h
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rintro ⟨_, h⟩ F hF
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hF
    rw [osForm_combination]
    exact h c

/-- **Explicit negative observable**: if the Gram is not PSD, some coefficient
vector gives a positive-time observable of strictly negative reflected norm. -/
theorem negative_observable_of_not_posSemidef {m : Type*} [Fintype m]
    (C : ReflectionCylinder Ω) (f : m → Ω → ℂ)
    (h : ¬ (reflectionGram C f).PosSemidef) :
    ∃ c : m → ℂ, (osForm C (∑ i, c i • f i) (∑ i, c i • f i)).re < 0 := by
  rw [posSemidef_iff_dotProduct_mulVec] at h
  have h' : ¬ ∀ c : m → ℂ, 0 ≤ star c ⬝ᵥ (reflectionGram C f *ᵥ c) := by
    intro hc
    exact h ⟨reflectionGram_isHermitian C f, hc⟩
  push Not at h'
  obtain ⟨c, hc⟩ := h'
  refine ⟨c, ?_⟩
  rw [← osForm_combination] at hc
  have him := osForm_self_real C (∑ i, c i • f i)
  rw [Complex.le_def, not_and_or] at hc
  rcases hc with hre | him'
  · simpa using hre
  · exfalso
    apply him'
    simp [him]

/-- **Basis independence (positivity)**: a congruence by an invertible matrix
preserves positive semidefiniteness in both directions. -/
theorem gram_congruence_posSemidef_iff {m : Type*} [Fintype m] [DecidableEq m]
    (G P : Matrix m m ℂ) (hP : IsUnit P) :
    (Pᴴ * G * P).PosSemidef ↔ G.PosSemidef := by
  constructor
  · intro h
    have hinv := h.conjTranspose_mul_mul_same (P⁻¹)
    have hPP : P * P⁻¹ = 1 := mul_nonsing_inv P ((isUnit_iff_isUnit_det P).mp hP)
    have hPP' : P⁻¹ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, hPP, conjTranspose_one]
    have : P⁻¹ᴴ * (Pᴴ * G * P) * P⁻¹ = G := by
      calc P⁻¹ᴴ * (Pᴴ * G * P) * P⁻¹ = (P⁻¹ᴴ * Pᴴ) * G * (P * P⁻¹) := by
            simp only [Matrix.mul_assoc]
        _ = G := by rw [hPP', hPP, Matrix.one_mul, Matrix.mul_one]
    rwa [this] at hinv
  · intro h
    exact h.conjTranspose_mul_mul_same P

/-- **Basis independence (rank)**. -/
theorem gram_congruence_rank {m : Type*} [Fintype m] [DecidableEq m]
    (G P : Matrix m m ℂ) (hP : IsUnit P) :
    (Pᴴ * G * P).rank = G.rank := by
  have hdet : IsUnit P.det := (isUnit_iff_isUnit_det P).mp hP
  have hdetH : IsUnit Pᴴ.det := by
    rw [det_conjTranspose]; exact hdet.star
  rw [rank_mul_eq_left_of_isUnit_det _ _ hdet, rank_mul_eq_right_of_isUnit_det _ _ hdetH]

/-! ### Boundary decomposition -/

section Boundary

variable {B : Type*} [Fintype B]

/-- The boundary reflection `θ(a,b) = (b,a)` with a symmetric nonnegative weight. -/
def boundaryCylinder (μ : B → B → ℝ) (hμ : ∀ a b, 0 ≤ μ a b)
    (hsym : ∀ a b, μ b a = μ a b) : ReflectionCylinder (B × B) where
  θ p := (p.2, p.1)
  θ_invol _ := rfl
  μ p := μ p.1 p.2
  μ_nonneg p := hμ p.1 p.2
  μ_inv p := hsym p.1 p.2

/-- The boundary kernel `K(a,b) = μ(a,b)`. -/
def boundaryKernel (μ : B → B → ℝ) : Matrix B B ℂ := fun a b => (μ a b : ℂ)

/-- Positive-time functions depend on the second coordinate. -/
def liftBoundary (f : B → ℂ) : B × B → ℂ := fun p => f p.2

/-- On second-coordinate functions the OS form is the boundary kernel form. -/
theorem osForm_boundary (μ : B → B → ℝ) (hμ : ∀ a b, 0 ≤ μ a b)
    (hsym : ∀ a b, μ b a = μ a b) (f g : B → ℂ) :
    osForm (boundaryCylinder μ hμ hsym) (liftBoundary f) (liftBoundary g)
      = star f ⬝ᵥ (boundaryKernel μ *ᵥ g) := by
  unfold osForm boundaryCylinder liftBoundary boundaryKernel
  simp only [dotProduct, mulVec, Pi.star_apply, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

omit [Fintype B] in
theorem boundaryKernel_isHermitian (μ : B → B → ℝ) (hsym : ∀ a b, μ b a = μ a b) :
    (boundaryKernel μ).IsHermitian := by
  ext a b
  simp [boundaryKernel, hsym a b]

/-- **Boundary-kernel criterion**: reflection positivity on the second-coordinate
functions is `K ⪰ 0`. -/
theorem boundary_reflection_positive_iff (μ : B → B → ℝ) (hμ : ∀ a b, 0 ≤ μ a b)
    (hsym : ∀ a b, μ b a = μ a b) :
    (∀ f : B → ℂ, 0 ≤ osForm (boundaryCylinder μ hμ hsym) (liftBoundary f) (liftBoundary f))
      ↔ (boundaryKernel μ).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  constructor
  · intro h
    refine ⟨boundaryKernel_isHermitian μ hsym, fun f => ?_⟩
    rw [← osForm_boundary μ hμ hsym]
    exact h f
  · rintro ⟨_, h⟩ f
    rw [osForm_boundary μ hμ hsym]
    exact h f

end Boundary

/-! ### Nearest positive semidefinite matrix (QRP.4) -/

section Nearest

variable {m : Type*} [Fintype m]

/-- Squared Hilbert–Schmidt norm `‖A‖²_HS = Re tr(A^* A)`. -/
noncomputable def hsNormSq (A : Matrix m m ℂ) : ℝ := (trace (Aᴴ * A)).re

theorem hsNormSq_nonneg (A : Matrix m m ℂ) : 0 ≤ hsNormSq A := by
  unfold hsNormSq
  have := (posSemidef_conjTranspose_mul_self A).trace_nonneg
  exact (Complex.le_def.mp this).1

theorem hsNormSq_eq_sum (A : Matrix m m ℂ) : hsNormSq A = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  unfold hsNormSq
  simp only [trace, Matrix.diag, mul_apply, conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sq_norm,
    Complex.normSq_apply]
  ring

/-- The trace of a product of two PSD matrices is nonnegative. -/
theorem trace_mul_nonneg_of_posSemidef [DecidableEq m] {A B : Matrix m m ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (trace (A * B)).re := by
  have hA0 : (0 : Matrix m m ℂ) ≤ A := nonneg_iff_posSemidef.mpr hA
  have hs : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A hA0
  have hsq : (CFC.sqrt A).PosSemidef := nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have key : A * B = CFC.sqrt A * (CFC.sqrt A * B) := by rw [← Matrix.mul_assoc, hs]
  rw [key, trace_mul_comm]
  have hconj : CFC.sqrt A * B * CFC.sqrt A = (CFC.sqrt A)ᴴ * B * CFC.sqrt A := by
    rw [hsq.isHermitian.eq]
  rw [hconj]
  exact (Complex.le_def.mp (hB.conjTranspose_mul_mul_same _).trace_nonneg).1

/-- Hilbert–Schmidt expansion `‖X - Y‖² = ‖X‖² + ‖Y‖² - 2 Re tr(X^* Y)`. -/
theorem hsNormSq_sub (X Y : Matrix m m ℂ) :
    hsNormSq (X - Y) = hsNormSq X + hsNormSq Y - 2 * (trace (Xᴴ * Y)).re := by
  unfold hsNormSq
  have h : (X - Y)ᴴ * (X - Y) = Xᴴ * X + Yᴴ * Y - (Xᴴ * Y + Yᴴ * X) := by
    rw [conjTranspose_sub]
    simp only [sub_mul, mul_sub]
    abel
  rw [h, trace_sub, trace_add, trace_add]
  have hYX : (trace (Yᴴ * X)).re = (trace (Xᴴ * Y)).re := by
    have : trace (Yᴴ * X) = star (trace (Xᴴ * Y)) := by
      rw [← trace_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]
    rw [this, Complex.star_def, Complex.conj_re]
  simp only [Complex.sub_re, Complex.add_re]
  rw [hYX]
  ring

/-- **(QRP.4)**: for a Jordan split `G = G₊ - G₋` (both PSD, orthogonal
`G₊ G₋ = 0 = G₋ G₊`), the Hilbert–Schmidt distance from `G` to every PSD
matrix is at least `‖G₋‖²_HS`, with equality at `G₊`. -/
theorem nearest_posSemidef [DecidableEq m] (G Gp Gm : Matrix m m ℂ)
    (hsplit : G = Gp - Gm) (hGp : Gp.PosSemidef) (hGm : Gm.PosSemidef)
    (horth : Gp * Gm = 0) :
    (∀ H : Matrix m m ℂ, H.PosSemidef → hsNormSq Gm ≤ hsNormSq (G - H)) ∧
      hsNormSq (G - Gp) = hsNormSq Gm := by
  constructor
  · intro H hH
    have hGH : G - H = (Gp - H) - Gm := by rw [hsplit]; abel
    rw [hGH, hsNormSq_sub]
    have htr : (trace ((Gp - H)ᴴ * Gm)).re = -(trace (H * Gm)).re := by
      rw [conjTranspose_sub, sub_mul, trace_sub, hGp.isHermitian.eq, hH.isHermitian.eq,
        horth, trace_zero]
      simp
    rw [htr]
    have := trace_mul_nonneg_of_posSemidef hH hGm
    have := hsNormSq_nonneg (Gp - H)
    linarith
  · rw [hsplit, sub_sub_cancel_left]
    unfold hsNormSq
    rw [conjTranspose_neg, neg_mul, mul_neg, neg_neg]

/-- **Existence of the Jordan split** of a Hermitian matrix from the
continuous functional calculus: `G₊ = f₊(G)`, `G₋ = f₋(G)`. -/
theorem jordan_split_exists [DecidableEq m] (G : Matrix m m ℂ) (hG : G.IsHermitian) :
    ∃ Gp Gm : Matrix m m ℂ, G = Gp - Gm ∧ Gp.PosSemidef ∧ Gm.PosSemidef ∧
      Gp * Gm = 0 ∧ Gm * Gp = 0 := by
  have hsa : IsSelfAdjoint G := hG
  refine ⟨cfc (fun x : ℝ => max x 0) G, cfc (fun x : ℝ => max (-x) 0) G, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← cfc_sub (fun x : ℝ => max x 0) (fun x : ℝ => max (-x) 0) G]
    conv_lhs => rw [← cfc_id' ℝ G]
    congr 1
    funext x
    rcases le_or_gt 0 x with h | h
    · rw [max_eq_left h, max_eq_right (show -x ≤ 0 by linarith)]; ring
    · rw [max_eq_right h.le, max_eq_left (show 0 ≤ -x by linarith)]; ring
  · rw [← nonneg_iff_posSemidef]
    exact cfc_nonneg fun x _ => le_max_right _ _
  · rw [← nonneg_iff_posSemidef]
    exact cfc_nonneg fun x _ => le_max_right _ _
  · rw [← cfc_mul (fun x : ℝ => max x 0) (fun x : ℝ => max (-x) 0) G]
    have : (fun x : ℝ => max x 0 * max (-x) 0) = fun _ => (0 : ℝ) := by
      funext x
      rcases le_or_gt 0 x with h | h
      · rw [max_eq_right (show -x ≤ 0 by linarith)]; ring
      · rw [max_eq_right h.le]; ring
    rw [this, cfc_const_zero]
  · rw [← cfc_mul (fun x : ℝ => max (-x) 0) (fun x : ℝ => max x 0) G]
    have : (fun x : ℝ => max (-x) 0 * max x 0) = fun _ => (0 : ℝ) := by
      funext x
      rcases le_or_gt 0 x with h | h
      · rw [max_eq_right (show -x ≤ 0 by linarith)]; ring
      · rw [max_eq_right h.le]; ring
    rw [this, cfc_const_zero]

end Nearest

/-! ### Pushforward (QRP.4a, QRP.5) -/

section Pushforward

/-- **(QRP.4a)**: the entrywise product of PSD boundary kernels is PSD. -/
theorem hadamard_posSemidef {B : Type*} [Fintype B] {K H : Matrix B B ℂ}
    (hK : K.PosSemidef) (hH : H.PosSemidef) : (Matrix.hadamard K H).PosSemidef :=
  hK.hadamard hH

/-- A reflected-square insertion `H(a,b) = ∑ᵣ conj(hᵣ a) hᵣ b` is PSD. -/
theorem reflected_square_posSemidef {B R : Type*} [Fintype B] [Fintype R]
    (h : R → B → ℂ) :
    (Matrix.of fun a b => ∑ r, star (h r a) * h r b).PosSemidef := by
  have : (Matrix.of fun a b => ∑ r, star (h r a) * h r b)
      = (Matrix.of fun r a => h r a)ᴴ * Matrix.of fun r a => h r a := by
    ext a b
    simp [mul_apply]
  rw [this]
  exact posSemidef_conjTranspose_mul_self _

/-- The marginalization isometry `V : ℂ^B → ℂ^{B × F}`, `(Vf)(a,α) = f(a)`. -/
def marginalV (B F : Type*) [DecidableEq B] : Matrix (B × F) B ℂ :=
  fun p b => if p.1 = b then 1 else 0

set_option linter.flexible false in
/-- **(QRP.5)**: the exact marginal of a PSD reflected boundary kernel is
`V^* K V`, hence PSD, with entries `∑_{α,β} K_{(a,α),(b,β)}`. -/
theorem marginal_posSemidef {B F : Type*} [Fintype B] [Fintype F] [DecidableEq B]
    (K : Matrix (B × F) (B × F) ℂ) (hK : K.PosSemidef) :
    ((marginalV B F)ᴴ * K * marginalV B F).PosSemidef ∧
      ∀ a b, ((marginalV B F)ᴴ * K * marginalV B F) a b = ∑ α, ∑ β, K (a, α) (b, β) := by
  refine ⟨hK.conjTranspose_mul_mul_same _, fun a b => ?_⟩
  simp only [mul_apply, conjTranspose_apply, marginalV, Fintype.sum_prod_type]
  first
    | (simp [Finset.sum_ite_eq']; done)
    | (simp [Finset.sum_ite_eq']; exact Finset.sum_comm)

/-- **Reflection-equivariant pushforward**: if `π` intertwines the reflections
and `μ_X` is the pushforward of `μ_Y`, the OS form of `μ_X` on `F` is the OS
form of `μ_Y` on `F ∘ π`. -/
theorem osForm_pushforward {ΩY ΩX : Type*} [Fintype ΩY] [Fintype ΩX] [DecidableEq ΩX]
    (CY : ReflectionCylinder ΩY) (CX : ReflectionCylinder ΩX) (π : ΩY → ΩX)
    (hθ : ∀ y, π (CY.θ y) = CX.θ (π y))
    (hμ : ∀ x, CX.μ x = ∑ y ∈ univ.filter (fun y => π y = x), CY.μ y)
    (F G : ΩX → ℂ) :
    osForm CX F G = osForm CY (F ∘ π) (G ∘ π) := by
  unfold osForm
  simp only [Function.comp]
  rw [← Finset.sum_fiberwise univ π]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hμ x, Complex.ofReal_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  have hy' : π y = x := (Finset.mem_filter.mp hy).2
  rw [hθ, hy']

/-- Reflection positivity is preserved by reflection-equivariant pushforward
on any positive-time algebra whose pullback lies in the fine algebra. -/
theorem pushforward_reflection_positive {ΩY ΩX : Type*} [Fintype ΩY] [Fintype ΩX]
    [DecidableEq ΩX]
    (CY : ReflectionCylinder ΩY) (CX : ReflectionCylinder ΩX) (π : ΩY → ΩX)
    (hθ : ∀ y, π (CY.θ y) = CX.θ (π y))
    (hμ : ∀ x, CX.μ x = ∑ y ∈ univ.filter (fun y => π y = x), CY.μ y)
    (AX : Set (ΩX → ℂ)) (AY : Set (ΩY → ℂ)) (hpull : ∀ F ∈ AX, F ∘ π ∈ AY)
    (hY : ReflectionPositiveOn CY AY) : ReflectionPositiveOn CX AX := by
  intro F hF
  rw [osForm_pushforward CY CX π hθ hμ]
  exact hY _ (hpull F hF)

end Pushforward

end SMSTReflectionPositivity
end NCG
