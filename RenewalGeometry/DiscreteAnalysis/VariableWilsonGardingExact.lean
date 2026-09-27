/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.DiscreteAnalysis.FrozenWilsonGardingExact

/-!
# Variable-coefficient discrete Gårding estimate on the lattice torus

Paper `predictive_spectral_geometry`, label `thm:supp-general-Wilson-ellipticity`, the
variable-coefficient uniform graph estimate `eq:supp-general-Garding` (with the cutoff
commutator bound `eq:local-cutoff-commutator` and the discrete `H¹` norm `eq:discrete-H1-norm`),
built on the frozen estimate of `FrozenWilsonGardingExact`.

On the periodic lattice torus `(ℤ/nℤ)^d` (mesh `h`) the doubled Wilson operator with sampled
variable Clifford coefficients `ĉ^j(x)`,
`D̃ = ½ Σ_j (M_{ĉ^j} P_j + P_j M_{ĉ^j}) + ϖ Γ_⊥ W` (`varWilson`), is compared with its frozen
value `D̃_{x₀}` (`frozenWilson` with the coefficients `ĉ^j(x₀)`).  The discrete `ℓ²` norm is
realised as the Euclidean norm of the section (`eucl`, `gridNormSq_eq_norm_eucl_sq`), so that
the triangle inequality is available.

* `symmetricDifference_varMul` / `wilsonTerm_varMul`: the commutators of the symmetric
  difference and of the Wilson term with a (matrix-valued) multiplication operator are the
  shift commutators `matShiftCommutator` / `wilsonCommutator`, which contain the differences
  `δ(x + e_j) - δ(x)`.
* `norm_eucl_cutoffCommutator_le` (**`eq:local-cutoff-commutator`**): for a lattice cutoff `χ`
  with `|χ(x + he_j) - χ(x)| ≤ h K`, `‖[D̃, M_χ] u‖ ≤ d K (B + |ϖ| ‖Γ_⊥‖) ‖u‖`, cutoff-derivative
  times coefficient bounds, uniformly in `h`.
* `norm_eucl_symmetricDifference_le`: `‖P_j v‖ ≤ ‖h⁻¹(S_j - I) v‖`.
* `norm_eucl_freezeDifference_le`: on a patch where `‖ĉ^j(x) - ĉ^j(x₀)‖ ≤ ω`, with Lipschitz
  coefficients `‖ĉ^j(x + he_j) - ĉ^j(x)‖ ≤ h L`,
  `‖(D̃ - D̃_{x₀})(χ u)‖ ≤ ω Σ_j ‖h⁻¹(S_j - I)(χu)‖ + (d L / 2) ‖χ u‖` — the paper's
  `C ω_c(r) ‖·‖_{1,h} + C_r ‖·‖_h`.
* `variable_garding` (**`eq:supp-general-Garding`**): for a partition of unity `Σ_α χ_α² = 1` on
  the torus with frozen points `x_α`, uniformly elliptic Hermitian Clifford data at every `x_α`,
  and modulus of continuity `ω` on the patches small enough to be absorbed
  (`4 d ω² max(1, min(λ, ϖ²)⁻¹) ≤ 1`, the paper's "choose `r` once"),
  `‖u‖²_{1,h} ≤ C (‖D̃ u‖_h² + ‖u‖_h²)` with the explicit constant `gardingConstant`, which
  depends only on `d`, the number of patches, the cutoff-gradient bound `K`, the coefficient
  bounds `B, L`, `‖Γ_⊥‖`, `ϖ` and the ellipticity constant `λ` — not on `h` or `n`.

Disclosures.  The paper's "sections localized in the interior of the original chart" on the
"fixed smooth periodic extension" is the periodic torus itself here: every torus section is
admissible and the partition of unity lives on the torus.  Coefficient bounds are stated as
operator-norm bounds through `euclNormSq` (`‖M v‖² ≤ B² ‖v‖²`); the ordinary shifts are used
(`T^Ω_j - S_j = O(h)` is absorbed into `L`, as the paper's proof says).  The self-adjointness
remark is `varWilson_symmetric` (Hermitian coefficients make `D̃` symmetric for the grid inner
product).
-/

open Finset Matrix ZMod ComplexConjugate
open RenewalGeometry.LatticeTorusPlancherel RenewalGeometry.FrozenWilsonGarding

set_option linter.unusedSectionVars false

namespace RenewalGeometry.VariableWilsonGarding

variable {d n N : ℕ} [NeZero n]

/-! ### The Euclidean realisation of the discrete norm -/

/-- The section `u` viewed as a vector of `ℂ^{n^d N}`. -/
noncomputable def eucl (u : TorusSection d n N) : EuclideanSpace ℂ (Grid d n × Fin N) :=
  WithLp.toLp 2 (fun p => u p.1 p.2)

theorem eucl_add (u v : TorusSection d n N) : eucl (u + v) = eucl u + eucl v := rfl

theorem eucl_sub (u v : TorusSection d n N) : eucl (u - v) = eucl u - eucl v := rfl

theorem eucl_smul (c : ℂ) (u : TorusSection d n N) : eucl (c • u) = c • eucl u := rfl

theorem eucl_neg (u : TorusSection d n N) : eucl (-u) = -eucl u := rfl

theorem eucl_sum {ι : Type*} (s : Finset ι) (f : ι → TorusSection d n N) :
    eucl (∑ i ∈ s, f i) = ∑ i ∈ s, eucl (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, eucl_add, ih]

theorem norm_eucl_sq (u : TorusSection d n N) : ‖eucl u‖ ^ 2 = ∑ x, euclNormSq (u x) := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  rfl

/-- `‖u‖_h² = h^d ‖eucl u‖²`. -/
theorem gridNormSq_eq_norm_eucl_sq (h : ℝ) (u : TorusSection d n N) :
    gridNormSq h u = h ^ d * ‖eucl u‖ ^ 2 := by
  rw [gridNormSq, norm_eucl_sq]

theorem norm_eucl_le_of_sq_le {u : TorusSection d n N} {a : ℝ} (ha : 0 ≤ a)
    (hsq : ‖eucl u‖ ^ 2 ≤ a ^ 2) : ‖eucl u‖ ≤ a :=
  (pow_le_pow_iff_left₀ (norm_nonneg _) ha two_ne_zero).1 hsq

/-- Coordinate shifts are isometric. -/
theorem norm_eucl_shift (j : Fin d) (u : TorusSection d n N) :
    ‖eucl (shift j u)‖ = ‖eucl u‖ := by
  have h : ‖eucl (shift j u)‖ ^ 2 = ‖eucl u‖ ^ 2 := by
    rw [norm_eucl_sq, norm_eucl_sq]
    have hb : Function.Bijective (fun x : Grid d n => x + Pi.single j (1 : ZMod n)) :=
      (Equiv.addRight (Pi.single j (1 : ZMod n) : Grid d n)).bijective
    exact hb.sum_comp (fun x => euclNormSq (u x))
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

theorem norm_eucl_shiftAdj (j : Fin d) (u : TorusSection d n N) :
    ‖eucl (shiftAdj j u)‖ = ‖eucl u‖ := by
  have h : ‖eucl (shiftAdj j u)‖ ^ 2 = ‖eucl u‖ ^ 2 := by
    rw [norm_eucl_sq, norm_eucl_sq]
    have hb : Function.Bijective (fun x : Grid d n => x - Pi.single j (1 : ZMod n)) :=
      (Equiv.subRight (Pi.single j (1 : ZMod n) : Grid d n)).bijective
    exact hb.sum_comp (fun x => euclNormSq (u x))
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-! ### Multiplication operators -/

/-- Pointwise multiplication by a matrix field. -/
def varMul (c : Grid d n → Matrix (Fin N) (Fin N) ℂ) (u : TorusSection d n N) :
    TorusSection d n N :=
  fun x => c x *ᵥ u x

/-- Multiplication by a real lattice cutoff `χ`. -/
def cutoff (χ : Grid d n → ℝ) (u : TorusSection d n N) : TorusSection d n N :=
  fun x => ((χ x : ℝ) : ℂ) • u x

/-- The scalar matrix field `χ · I`. -/
def scalarField (χ : Grid d n → ℝ) : Grid d n → Matrix (Fin N) (Fin N) ℂ :=
  fun x => ((χ x : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)

theorem cutoff_eq_varMul (χ : Grid d n → ℝ) (u : TorusSection d n N) :
    cutoff χ u = varMul (scalarField χ) u := by
  funext x
  simp [cutoff, varMul, scalarField, Matrix.smul_mulVec]

theorem varMul_const (M : Matrix (Fin N) (Fin N) ℂ) (u : TorusSection d n N) :
    varMul (fun _ => M) u = matMul M u := rfl

theorem varMul_add (c : Grid d n → Matrix (Fin N) (Fin N) ℂ) (u v : TorusSection d n N) :
    varMul c (u + v) = varMul c u + varMul c v := by
  funext x; simp [varMul, Matrix.mulVec_add]

theorem varMul_sub (c : Grid d n → Matrix (Fin N) (Fin N) ℂ) (u v : TorusSection d n N) :
    varMul c (u - v) = varMul c u - varMul c v := by
  funext x; simp [varMul, Matrix.mulVec_sub]

theorem varMul_smul (c : Grid d n → Matrix (Fin N) (Fin N) ℂ) (a : ℂ) (u : TorusSection d n N) :
    varMul c (a • u) = a • varMul c u := by
  funext x; simp [varMul, Matrix.mulVec_smul]

theorem varMul_sum {ι : Type*} (c : Grid d n → Matrix (Fin N) (Fin N) ℂ) (s : Finset ι)
    (f : ι → TorusSection d n N) : varMul c (∑ i ∈ s, f i) = ∑ i ∈ s, varMul c (f i) := by
  funext x; simp [varMul, Matrix.mulVec_sum]

theorem sub_varMul (c c' : Grid d n → Matrix (Fin N) (Fin N) ℂ) (u : TorusSection d n N) :
    varMul c u - varMul c' u = varMul (c - c') u := by
  funext x; simp [varMul, Matrix.sub_mulVec]

/-- A matrix-field multiplication bounded on the support of the section. -/
theorem norm_eucl_varMul_le_of_support (c : Grid d n → Matrix (Fin N) (Fin N) ℂ) {B : ℝ}
    (hB : 0 ≤ B) (u : TorusSection d n N)
    (hc : ∀ x, u x ≠ 0 → ∀ v, euclNormSq (c x *ᵥ v) ≤ B ^ 2 * euclNormSq v) :
    ‖eucl (varMul c u)‖ ≤ B * ‖eucl u‖ := by
  refine norm_eucl_le_of_sq_le (by positivity) ?_
  rw [mul_pow, norm_eucl_sq, norm_eucl_sq, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  by_cases hx : u x = 0
  · simp [varMul, hx, euclNormSq]
  · exact hc x hx (u x)

theorem norm_eucl_varMul_le (c : Grid d n → Matrix (Fin N) (Fin N) ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hc : ∀ x v, euclNormSq (c x *ᵥ v) ≤ B ^ 2 * euclNormSq v) (u : TorusSection d n N) :
    ‖eucl (varMul c u)‖ ≤ B * ‖eucl u‖ :=
  norm_eucl_varMul_le_of_support c hB u fun x _ v => hc x v

theorem euclNormSq_scalarField_mulVec (χ : Grid d n → ℝ) (x : Grid d n) (v : Fin N → ℂ) :
    euclNormSq (scalarField χ x *ᵥ v) = χ x ^ 2 * euclNormSq v := by
  simp only [scalarField]
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, euclNormSq_smul, Complex.norm_real, Real.norm_eq_abs,
    sq_abs]

/-- `‖χ u‖ ≤ (sup |χ|) ‖u‖`. -/
theorem norm_eucl_cutoff_le (χ : Grid d n → ℝ) {A : ℝ} (hA : 0 ≤ A) (hχ : ∀ x, |χ x| ≤ A)
    (u : TorusSection d n N) : ‖eucl (cutoff χ u)‖ ≤ A * ‖eucl u‖ := by
  rw [cutoff_eq_varMul]
  refine norm_eucl_varMul_le _ hA (fun x v => ?_) u
  rw [euclNormSq_scalarField_mulVec]
  refine mul_le_mul_of_nonneg_right ?_ (euclNormSq_nonneg _)
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (hχ x) 2

/-- **Partition of unity**: `Σ_α ‖χ_α u‖² = ‖u‖²` when `Σ_α χ_α² = 1` pointwise. -/
theorem sum_norm_eucl_cutoff_sq {m : ℕ} (χ : Fin m → Grid d n → ℝ)
    (hχ : ∀ x, ∑ α, χ α x ^ 2 = 1) (u : TorusSection d n N) :
    ∑ α, ‖eucl (cutoff (χ α) u)‖ ^ 2 = ‖eucl u‖ ^ 2 := by
  simp only [norm_eucl_sq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [cutoff, euclNormSq_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    ← Finset.sum_mul, hχ x, one_mul]

/-- The weighted form: `Σ_α ‖(S_j χ_α) w‖² = ‖w‖²` for the shifted partition. -/
theorem sum_norm_eucl_cutoff_shift_sq {m : ℕ} (χ : Fin m → Grid d n → ℝ)
    (hχ : ∀ x, ∑ α, χ α x ^ 2 = 1) (j : Fin d) (w : TorusSection d n N) :
    ∑ α, ‖eucl (cutoff (fun x => χ α (x + Pi.single j 1)) w)‖ ^ 2 = ‖eucl w‖ ^ 2 :=
  sum_norm_eucl_cutoff_sq (fun α x => χ α (x + Pi.single j 1)) (fun _ => hχ _) w

/-! ### The variable-coefficient Wilson operator -/

/-- Sampled Clifford coefficient fields `x ↦ ĉ^j(x)`. -/
abbrev CoefficientField (d n N : ℕ) := Grid d n → Fin d → Matrix (Fin N) (Fin N) ℂ

/-- The `j`-th coefficient as a matrix field. -/
def coeff (c : CoefficientField d n N) (j : Fin d) : Grid d n → Matrix (Fin N) (Fin N) ℂ :=
  fun x => c x j

/-- The variable-coefficient doubled Wilson operator of `eq:supp-general-Wilson` on the torus:
`D̃ = ½ Σ_j (M_{ĉ^j} P_j + P_j M_{ĉ^j}) + ϖ Γ_⊥ W`, with sampled coefficients. -/
noncomputable def varWilson (h ϖ : ℝ) (c : CoefficientField d n N)
    (Γ : Matrix (Fin N) (Fin N) ℂ) (u : TorusSection d n N) : TorusSection d n N :=
  (2 : ℂ)⁻¹ • (∑ j, (varMul (coeff c j) (symmetricDifference h j u) +
      symmetricDifference h j (varMul (coeff c j) u))) +
    (ϖ : ℂ) • matMul Γ (wilsonTerm h u)

/-- With constant coefficients the operator is the frozen operator of
`FrozenWilsonGardingExact`. -/
theorem varWilson_const (h ϖ : ℝ) (c₀ : Fin d → Matrix (Fin N) (Fin N) ℂ)
    (Γ : Matrix (Fin N) (Fin N) ℂ) (u : TorusSection d n N) :
    varWilson h ϖ (fun _ => c₀) Γ u = frozenWilson h ϖ c₀ Γ u := by
  funext x
  simp only [varWilson, frozenWilson, Finset.sum_apply, Pi.add_apply, Pi.smul_apply]
  rfl

/-- The frozen operator at `x₀` is the variable operator with the frozen field. -/
theorem frozenWilson_eq_varWilson (h ϖ : ℝ) (c : CoefficientField d n N) (x₀ : Grid d n)
    (Γ : Matrix (Fin N) (Fin N) ℂ) (u : TorusSection d n N) :
    frozenWilson h ϖ (c x₀) Γ u = varWilson h ϖ (fun _ => c x₀) Γ u :=
  (varWilson_const h ϖ (c x₀) Γ u).symm

/-! ### Shift commutators -/

/-- The commutator `[P_j, M_δ] v = (2ih)⁻¹ [ (S_jδ - δ) S_j v - (S_j^*δ - δ) S_j^* v ]`
of the symmetric difference with a matrix-field multiplication. -/
noncomputable def matShiftCommutator (h : ℝ) (δ : Grid d n → Matrix (Fin N) (Fin N) ℂ)
    (j : Fin d) (v : TorusSection d n N) : TorusSection d n N :=
  (2 * Complex.I * (h : ℂ))⁻¹ •
    (varMul (fun x => δ (x + Pi.single j 1) - δ x) (shift j v) -
      varMul (fun x => δ (x - Pi.single j 1) - δ x) (shiftAdj j v))

/-- The commutator `[W, M_δ] v = -(2h)⁻¹ Σ_j [ (S_jδ - δ) S_j v + (S_j^*δ - δ) S_j^* v ]`
of the Wilson term with a matrix-field multiplication. -/
noncomputable def wilsonCommutator (h : ℝ) (δ : Grid d n → Matrix (Fin N) (Fin N) ℂ)
    (v : TorusSection d n N) : TorusSection d n N :=
  (2 * (h : ℂ))⁻¹ • ∑ j, (-(varMul (fun x => δ (x + Pi.single j 1) - δ x) (shift j v)) -
    varMul (fun x => δ (x - Pi.single j 1) - δ x) (shiftAdj j v))

/-- `P_j (M_δ v) = M_δ (P_j v) + [P_j, M_δ] v`. -/
theorem symmetricDifference_varMul (h : ℝ) (δ : Grid d n → Matrix (Fin N) (Fin N) ℂ)
    (j : Fin d) (v : TorusSection d n N) :
    symmetricDifference h j (varMul δ v) =
      varMul δ (symmetricDifference h j v) + matShiftCommutator h δ j v := by
  funext x
  simp only [symmetricDifference, varMul, matShiftCommutator, shift, shiftAdj, Pi.add_apply,
    Pi.smul_apply, Pi.sub_apply, Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.sub_mulVec]
  rw [← smul_add]
  congr 1
  abel

/-- `W (M_δ v) = M_δ (W v) + [W, M_δ] v`. -/
theorem wilsonTerm_varMul (h : ℝ) (δ : Grid d n → Matrix (Fin N) (Fin N) ℂ)
    (v : TorusSection d n N) :
    wilsonTerm h (varMul δ v) = varMul δ (wilsonTerm h v) + wilsonCommutator h δ v := by
  funext x
  simp only [wilsonTerm, varMul, wilsonCommutator, shift, shiftAdj, Pi.add_apply, Pi.smul_apply,
    Pi.sub_apply, Pi.neg_apply, Finset.sum_apply, Matrix.mulVec_smul, Matrix.mulVec_sum,
    Matrix.mulVec_sub, Matrix.sub_mulVec]
  rw [← smul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  abel

theorem symmetricDifference_sub (h : ℝ) (j : Fin d) (u v : TorusSection d n N) :
    symmetricDifference h j (u - v) =
      symmetricDifference h j u - symmetricDifference h j v := by
  funext x
  simp only [symmetricDifference, shift, shiftAdj, Pi.sub_apply, ← smul_sub]
  congr 1
  abel

theorem symmetricDifference_add (h : ℝ) (j : Fin d) (u v : TorusSection d n N) :
    symmetricDifference h j (u + v) =
      symmetricDifference h j u + symmetricDifference h j v := by
  funext x
  simp only [symmetricDifference, shift, shiftAdj, Pi.add_apply, ← smul_add]
  congr 1
  abel

/-- `P_j v = (2i)⁻¹ (∂_j v + S_j^* ∂_j v)` with `∂_j = h⁻¹(S_j - I)`. -/
theorem symmetricDifference_eq_forwardDifference (h : ℝ) (j : Fin d) (v : TorusSection d n N) :
    symmetricDifference h j v = (2 * Complex.I)⁻¹ •
      (forwardDifference h j v + shiftAdj j (forwardDifference h j v)) := by
  funext x
  simp only [symmetricDifference, forwardDifference, shift, shiftAdj, Pi.add_apply,
    Pi.smul_apply, sub_add_cancel]
  rw [smul_add, smul_smul, smul_smul, ← smul_add]
  have : (2 * Complex.I)⁻¹ * (h : ℂ)⁻¹ = (2 * Complex.I * (h : ℂ))⁻¹ := by
    ring
  rw [this]
  congr 1
  abel

/-- The discrete product rule `∂_j(χ u) = (S_j χ) ∂_j u + (∂_j χ) u`. -/
theorem forwardDifference_cutoff (h : ℝ) (j : Fin d) (χ : Grid d n → ℝ)
    (u : TorusSection d n N) :
    forwardDifference h j (cutoff χ u) =
      cutoff (fun x => χ (x + Pi.single j 1)) (forwardDifference h j u) +
        cutoff (fun x => (χ (x + Pi.single j 1) - χ x) / h) u := by
  funext x
  simp only [forwardDifference, cutoff, shift, Pi.add_apply]
  push_cast
  module

/-- `M_c (χ w) = χ (M_c w)`. -/
theorem varMul_cutoff (c : Grid d n → Matrix (Fin N) (Fin N) ℂ) (χ : Grid d n → ℝ)
    (w : TorusSection d n N) : varMul c (cutoff χ w) = cutoff χ (varMul c w) := by
  funext x
  simp [varMul, cutoff, Matrix.mulVec_smul]

theorem matMul_cutoff (Γ : Matrix (Fin N) (Fin N) ℂ) (χ : Grid d n → ℝ)
    (w : TorusSection d n N) : matMul Γ (cutoff χ w) = cutoff χ (matMul Γ w) :=
  varMul_cutoff (fun _ => Γ) χ w

theorem cutoff_add (χ : Grid d n → ℝ) (u v : TorusSection d n N) :
    cutoff χ (u + v) = cutoff χ u + cutoff χ v := by
  funext x; simp [cutoff, smul_add]

theorem cutoff_smul (χ : Grid d n → ℝ) (a : ℂ) (u : TorusSection d n N) :
    cutoff χ (a • u) = a • cutoff χ u := by
  funext x; simp [cutoff, smul_comm a]

theorem cutoff_sum {ι : Type*} (χ : Grid d n → ℝ) (s : Finset ι) (f : ι → TorusSection d n N) :
    cutoff χ (∑ i ∈ s, f i) = ∑ i ∈ s, cutoff χ (f i) := by
  funext x; simp [cutoff, Finset.smul_sum, Finset.sum_apply]

/-- The cutoff commutator `[D̃, M_χ] u` (`eq:local-cutoff-commutator`), as an explicit
combination of shift commutators. -/
noncomputable def cutoffCommutator (h ϖ : ℝ) (c : CoefficientField d n N)
    (Γ : Matrix (Fin N) (Fin N) ℂ) (χ : Grid d n → ℝ) (u : TorusSection d n N) :
    TorusSection d n N :=
  (2 : ℂ)⁻¹ • (∑ j, (varMul (coeff c j) (matShiftCommutator h (scalarField χ) j u) +
      matShiftCommutator h (scalarField χ) j (varMul (coeff c j) u))) +
    (ϖ : ℂ) • matMul Γ (wilsonCommutator h (scalarField χ) u)

theorem symmetricDifference_cutoff (h : ℝ) (χ : Grid d n → ℝ) (j : Fin d)
    (v : TorusSection d n N) :
    symmetricDifference h j (cutoff χ v) =
      cutoff χ (symmetricDifference h j v) + matShiftCommutator h (scalarField χ) j v := by
  rw [cutoff_eq_varMul, cutoff_eq_varMul, symmetricDifference_varMul]

theorem wilsonTerm_cutoff (h : ℝ) (χ : Grid d n → ℝ) (v : TorusSection d n N) :
    wilsonTerm h (cutoff χ v) =
      cutoff χ (wilsonTerm h v) + wilsonCommutator h (scalarField χ) v := by
  rw [cutoff_eq_varMul, cutoff_eq_varMul, wilsonTerm_varMul]

/-- **The cutoff commutator identity**: `D̃ (χ u) = χ (D̃ u) + [D̃, M_χ] u`. -/
theorem varWilson_cutoff (h ϖ : ℝ) (c : CoefficientField d n N) (Γ : Matrix (Fin N) (Fin N) ℂ)
    (χ : Grid d n → ℝ) (u : TorusSection d n N) :
    varWilson h ϖ c Γ (cutoff χ u) =
      cutoff χ (varWilson h ϖ c Γ u) + cutoffCommutator h ϖ c Γ χ u := by
  simp only [varWilson, cutoffCommutator, ← varMul_const, symmetricDifference_cutoff,
    wilsonTerm_cutoff, varMul_add, varMul_cutoff, cutoff_add, cutoff_smul, cutoff_sum,
    Finset.sum_add_distrib, smul_add]
  abel

/-- **Freezing identity**: `(D̃ - D̃_{x₀}) v = ½ Σ_j (M_{δ_j} P_j v + P_j M_{δ_j} v)` with
`δ_j = ĉ^j - ĉ^j(x₀)`. -/
theorem varWilson_sub_frozen (h ϖ : ℝ) (c : CoefficientField d n N) (x₀ : Grid d n)
    (Γ : Matrix (Fin N) (Fin N) ℂ) (v : TorusSection d n N) :
    varWilson h ϖ c Γ v - frozenWilson h ϖ (c x₀) Γ v =
      (2 : ℂ)⁻¹ • ∑ j, (varMul (coeff c j - coeff (fun _ => c x₀) j) (symmetricDifference h j v) +
        symmetricDifference h j (varMul (coeff c j - coeff (fun _ => c x₀) j) v)) := by
  rw [frozenWilson_eq_varWilson]
  simp only [varWilson, add_sub_add_right_eq_sub, ← smul_sub, ← Finset.sum_sub_distrib,
    ← sub_varMul, symmetricDifference_sub]
  congr 2
  funext j
  abel

/-! ### Norm bounds -/

theorem norm_inv_two_I_mul (h : ℝ) (hh : 0 < h) :
    ‖(2 * Complex.I * (h : ℂ))⁻¹‖ = (2 * h)⁻¹ := by
  rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hh, Complex.norm_ofNat, mul_one]

theorem norm_inv_two_mul (h : ℝ) (hh : 0 < h) : ‖(2 * (h : ℂ))⁻¹‖ = (2 * h)⁻¹ := by
  rw [norm_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh, Complex.norm_ofNat]

theorem norm_inv_two_I : ‖(2 * Complex.I)⁻¹‖ = (2 : ℝ)⁻¹ := by
  rw [norm_inv, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one]

theorem norm_inv_two : ‖((2 : ℂ)⁻¹)‖ = (2 : ℝ)⁻¹ := by
  rw [norm_inv, Complex.norm_ofNat]

/-- `‖P_j v‖ ≤ ‖h⁻¹(S_j - I) v‖`. -/
theorem norm_eucl_symmetricDifference_le (h : ℝ) (j : Fin d) (v : TorusSection d n N) :
    ‖eucl (symmetricDifference h j v)‖ ≤ ‖eucl (forwardDifference h j v)‖ := by
  rw [symmetricDifference_eq_forwardDifference, eucl_smul, norm_smul, norm_inv_two_I, eucl_add]
  calc (2 : ℝ)⁻¹ * ‖eucl (forwardDifference h j v) + eucl (shiftAdj j (forwardDifference h j v))‖
      ≤ (2 : ℝ)⁻¹ * (‖eucl (forwardDifference h j v)‖ +
          ‖eucl (shiftAdj j (forwardDifference h j v))‖) := by
        gcongr
        exact norm_add_le _ _
    _ = ‖eucl (forwardDifference h j v)‖ := by
        rw [norm_eucl_shiftAdj]; ring

theorem euclNormSq_neg (v : Fin N → ℂ) : euclNormSq (-v) = euclNormSq v := by
  simp [euclNormSq]

/-- Backward coefficient differences are bounded like forward ones. -/
theorem backward_bound_of_forward (δ : Grid d n → Matrix (Fin N) (Fin N) ℂ) (j : Fin d) {A : ℝ}
    (hδ : ∀ x w, euclNormSq ((δ (x + Pi.single j 1) - δ x) *ᵥ w) ≤ A ^ 2 * euclNormSq w)
    (x : Grid d n) (w : Fin N → ℂ) :
    euclNormSq ((δ (x - Pi.single j 1) - δ x) *ᵥ w) ≤ A ^ 2 * euclNormSq w := by
  have := hδ (x - Pi.single j 1) w
  rw [sub_add_cancel] at this
  rw [← neg_sub, Matrix.neg_mulVec, euclNormSq_neg]
  exact this

/-- `‖[P_j, M_δ] v‖ ≤ L ‖v‖` when `‖δ(x + e_j) - δ(x)‖ ≤ h L`. -/
theorem norm_eucl_matShiftCommutator_le (h : ℝ) (hh : 0 < h)
    (δ : Grid d n → Matrix (Fin N) (Fin N) ℂ) (j : Fin d) {L : ℝ} (hL : 0 ≤ L)
    (hδ : ∀ x w, euclNormSq ((δ (x + Pi.single j 1) - δ x) *ᵥ w) ≤ (h * L) ^ 2 * euclNormSq w)
    (v : TorusSection d n N) : ‖eucl (matShiftCommutator h δ j v)‖ ≤ L * ‖eucl v‖ := by
  have hhL : 0 ≤ h * L := by positivity
  rw [matShiftCommutator, eucl_smul, norm_smul, norm_inv_two_I_mul h hh, eucl_sub]
  calc (2 * h)⁻¹ * ‖eucl (varMul (fun x => δ (x + Pi.single j 1) - δ x) (shift j v)) -
        eucl (varMul (fun x => δ (x - Pi.single j 1) - δ x) (shiftAdj j v))‖
      ≤ (2 * h)⁻¹ * (h * L * ‖eucl (shift j v)‖ + h * L * ‖eucl (shiftAdj j v)‖) := by
        gcongr
        refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
        · exact norm_eucl_varMul_le _ hhL hδ _
        · exact norm_eucl_varMul_le _ hhL (backward_bound_of_forward δ j hδ) _
    _ = L * ‖eucl v‖ := by
        rw [norm_eucl_shift, norm_eucl_shiftAdj]
        field_simp
        ring

/-- `‖[W, M_δ] v‖ ≤ d L ‖v‖`. -/
theorem norm_eucl_wilsonCommutator_le (h : ℝ) (hh : 0 < h)
    (δ : Grid d n → Matrix (Fin N) (Fin N) ℂ) {L : ℝ} (hL : 0 ≤ L)
    (hδ : ∀ (j : Fin d) x w,
      euclNormSq ((δ (x + Pi.single j 1) - δ x) *ᵥ w) ≤ (h * L) ^ 2 * euclNormSq w)
    (v : TorusSection d n N) : ‖eucl (wilsonCommutator h δ v)‖ ≤ d * L * ‖eucl v‖ := by
  have hhL : 0 ≤ h * L := by positivity
  rw [wilsonCommutator, eucl_smul, norm_smul, norm_inv_two_mul h hh, eucl_sum]
  calc (2 * h)⁻¹ * ‖∑ j, eucl (-(varMul (fun x => δ (x + Pi.single j 1) - δ x) (shift j v)) -
        varMul (fun x => δ (x - Pi.single j 1) - δ x) (shiftAdj j v))‖
      ≤ (2 * h)⁻¹ * ∑ j : Fin d, (h * L * ‖eucl v‖ + h * L * ‖eucl v‖) := by
        gcongr
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [eucl_sub, eucl_neg]
        refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_neg, ← norm_eucl_shift j v]
          exact norm_eucl_varMul_le _ hhL (hδ j) _
        · rw [← norm_eucl_shiftAdj j v]
          exact norm_eucl_varMul_le _ hhL (backward_bound_of_forward δ j (hδ j)) _
    _ = d * L * ‖eucl v‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
        ring

/-! ### The cutoff commutator bound `eq:local-cutoff-commutator` -/

theorem euclNormSq_scalarField_sub_mulVec (χ : Grid d n → ℝ) (x y : Grid d n) (w : Fin N → ℂ) :
    euclNormSq ((scalarField χ y - scalarField χ x) *ᵥ w) = (χ y - χ x) ^ 2 * euclNormSq w := by
  have : scalarField (N := N) χ y - scalarField χ x = scalarField (fun _ => χ y - χ x) x := by
    simp only [scalarField]
    push_cast
    rw [sub_smul]
  rw [this, euclNormSq_scalarField_mulVec]

/-- **`eq:local-cutoff-commutator`**: for a lattice cutoff with
`|χ(x + h e_j) - χ(x)| ≤ h K` (`K` a bound on `‖∇χ‖_∞`), coefficient bound `B` and `‖Γ_⊥‖ ≤ G`,
`‖[D̃, M_χ] u‖ ≤ d K (B + |ϖ| G) ‖u‖`, uniformly in `h`. -/
theorem norm_eucl_cutoffCommutator_le (h ϖ : ℝ) (hh : 0 < h) (c : CoefficientField d n N)
    (Γ : Matrix (Fin N) (Fin N) ℂ) (χ : Grid d n → ℝ) {K B G : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hG : 0 ≤ G) (hgrad : ∀ (j : Fin d) x, |χ (x + Pi.single j 1) - χ x| ≤ h * K)
    (hc : ∀ x j w, euclNormSq (c x j *ᵥ w) ≤ B ^ 2 * euclNormSq w)
    (hΓ : ∀ w, euclNormSq (Γ *ᵥ w) ≤ G ^ 2 * euclNormSq w) (u : TorusSection d n N) :
    ‖eucl (cutoffCommutator h ϖ c Γ χ u)‖ ≤ d * K * (B + |ϖ| * G) * ‖eucl u‖ := by
  have hsf : ∀ (j : Fin d) (x : Grid d n) (w : Fin N → ℂ),
      euclNormSq ((scalarField χ (x + Pi.single j 1) - scalarField χ x) *ᵥ w) ≤
        (h * K) ^ 2 * euclNormSq w := by
    intro j x w
    rw [euclNormSq_scalarField_sub_mulVec]
    refine mul_le_mul_of_nonneg_right ?_ (euclNormSq_nonneg _)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hgrad j x) 2
  have hmsc : ∀ (j : Fin d) w, ‖eucl (matShiftCommutator h (scalarField χ) j w)‖ ≤ K * ‖eucl w‖ :=
    fun j w => norm_eucl_matShiftCommutator_le h hh _ j hK (hsf j) w
  have hwc : ‖eucl (wilsonCommutator h (scalarField χ) u)‖ ≤ d * K * ‖eucl u‖ :=
    norm_eucl_wilsonCommutator_le h hh _ hK hsf u
  have hvar : ∀ (j : Fin d) w, ‖eucl (varMul (coeff c j) w)‖ ≤ B * ‖eucl w‖ :=
    fun j w => norm_eucl_varMul_le _ hB (fun x v => hc x j v) w
  have hmat : ∀ w : TorusSection d n N, ‖eucl (matMul Γ w)‖ ≤ G * ‖eucl w‖ :=
    fun w => norm_eucl_varMul_le (fun _ => Γ) hG (fun _ v => hΓ v) w
  rw [cutoffCommutator, eucl_add, eucl_smul, eucl_smul, eucl_sum]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, norm_inv_two, Complex.norm_real, Real.norm_eq_abs]
  calc (2 : ℝ)⁻¹ * ‖∑ j, eucl (varMul (coeff c j) (matShiftCommutator h (scalarField χ) j u) +
        matShiftCommutator h (scalarField χ) j (varMul (coeff c j) u))‖ +
        |ϖ| * ‖eucl (matMul Γ (wilsonCommutator h (scalarField χ) u))‖
      ≤ (2 : ℝ)⁻¹ * ∑ j : Fin d, (B * (K * ‖eucl u‖) + K * (B * ‖eucl u‖)) +
        |ϖ| * (G * (d * K * ‖eucl u‖)) := by
        gcongr
        · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [eucl_add]
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · exact (hvar j _).trans (by gcongr; exact hmsc j u)
          · exact (hmsc j _).trans (by gcongr; exact hvar j u)
        · exact (hmat _).trans (by gcongr)
    _ = d * K * (B + |ϖ| * G) * ‖eucl u‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ### The freezing bound -/

/-- The one-step neighbourhood (in direction `j`) of the support of a cutoff: the points at
which `P_j (χ u)` can be nonzero. -/
def NearSupport (χ : Grid d n → ℝ) (j : Fin d) (x : Grid d n) : Prop :=
  χ (x + Pi.single j 1) ≠ 0 ∨ χ (x - Pi.single j 1) ≠ 0

theorem symmetricDifference_cutoff_eq_zero (h : ℝ) (χ : Grid d n → ℝ) (j : Fin d)
    (u : TorusSection d n N) (x : Grid d n) (hx : ¬ NearSupport χ j x) :
    symmetricDifference h j (cutoff χ u) x = 0 := by
  simp only [NearSupport, not_or, not_not] at hx
  simp [symmetricDifference, cutoff, shift, shiftAdj, hx.1, hx.2]

/-- **Freezing bound**: on the patch where the coefficients are within `ω` of their frozen value
`ĉ^j(x₀)` (the modulus of continuity `ω_c(r)`), and with Lipschitz coefficients
`‖ĉ^j(x + h e_j) - ĉ^j(x)‖ ≤ h L`,
`‖(D̃ - D̃_{x₀})(χ u)‖ ≤ ω Σ_j ‖h⁻¹(S_j - I)(χ u)‖ + (d L / 2) ‖χ u‖`. -/
theorem norm_eucl_freezeDifference_le (h ϖ : ℝ) (hh : 0 < h) (c : CoefficientField d n N)
    (x₀ : Grid d n) (Γ : Matrix (Fin N) (Fin N) ℂ) (χ : Grid d n → ℝ) {ω L : ℝ} (hω : 0 ≤ ω)
    (hL : 0 ≤ L)
    (hfreeze : ∀ (j : Fin d) x, NearSupport χ j x →
      ∀ w, euclNormSq ((c x j - c x₀ j) *ᵥ w) ≤ ω ^ 2 * euclNormSq w)
    (hLip : ∀ (j : Fin d) x w,
      euclNormSq ((c (x + Pi.single j 1) j - c x j) *ᵥ w) ≤ (h * L) ^ 2 * euclNormSq w)
    (u : TorusSection d n N) :
    ‖eucl (varWilson h ϖ c Γ (cutoff χ u) - frozenWilson h ϖ (c x₀) Γ (cutoff χ u))‖ ≤
      ω * ∑ j, ‖eucl (forwardDifference h j (cutoff χ u))‖ +
        d * L / 2 * ‖eucl (cutoff χ u)‖ := by
  set v := cutoff χ u with hv
  set δ : Fin d → Grid d n → Matrix (Fin N) (Fin N) ℂ :=
    fun j => coeff c j - coeff (fun _ => c x₀) j with hδ
  have hterm : ∀ j, varMul (δ j) (symmetricDifference h j v) +
      symmetricDifference h j (varMul (δ j) v) =
      (2 : ℂ) • varMul (δ j) (symmetricDifference h j v) + matShiftCommutator h (δ j) j v := by
    intro j
    rw [symmetricDifference_varMul, two_smul]
    abel
  have hbound : ∀ j, ‖eucl (varMul (δ j) (symmetricDifference h j v) +
      symmetricDifference h j (varMul (δ j) v))‖ ≤
      2 * (ω * ‖eucl (forwardDifference h j v)‖) + L * ‖eucl v‖ := by
    intro j
    rw [hterm j, eucl_add, eucl_smul]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Complex.norm_ofNat]
      gcongr
      calc ‖eucl (varMul (δ j) (symmetricDifference h j v))‖
          ≤ ω * ‖eucl (symmetricDifference h j v)‖ := by
            refine norm_eucl_varMul_le_of_support _ hω _ fun x hx w => ?_
            have hns : NearSupport χ j x := by
              by_contra hns
              exact hx (symmetricDifference_cutoff_eq_zero h χ j u x hns)
            simpa [hδ, coeff] using hfreeze j x hns w
        _ ≤ ω * ‖eucl (forwardDifference h j v)‖ := by
            gcongr
            exact norm_eucl_symmetricDifference_le h j v
    · refine norm_eucl_matShiftCommutator_le h hh _ j hL (fun x w => ?_) v
      have : δ j (x + Pi.single j 1) - δ j x = c (x + Pi.single j 1) j - c x j := by
        simp only [hδ, coeff, Pi.sub_apply]
        abel
      rw [this]
      exact hLip j x w
  rw [varWilson_sub_frozen, eucl_smul, norm_smul, norm_inv_two, eucl_sum]
  calc (2 : ℝ)⁻¹ * ‖∑ j, eucl (varMul (δ j) (symmetricDifference h j v) +
        symmetricDifference h j (varMul (δ j) v))‖
      ≤ (2 : ℝ)⁻¹ * ∑ j, (2 * (ω * ‖eucl (forwardDifference h j v)‖) + L * ‖eucl v‖) := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hbound j)
    _ = ω * ∑ j, ‖eucl (forwardDifference h j v)‖ + d * L / 2 * ‖eucl v‖ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum]
        ring

/-! ### Absorption -/

/-- The frozen Gårding constant `max(1, min(λ, ϖ²)⁻¹)` of `FrozenWilsonGarding.h1NormSq_le`. -/
noncomputable def frozenConstant (lam ϖ : ℝ) : ℝ := max 1 (min lam (ϖ ^ 2))⁻¹

theorem one_le_frozenConstant (lam ϖ : ℝ) : 1 ≤ frozenConstant lam ϖ := le_max_left _ _

theorem frozenConstant_nonneg (lam ϖ : ℝ) : 0 ≤ frozenConstant lam ϖ :=
  zero_le_one.trans (one_le_frozenConstant lam ϖ)

/-- Uniformly elliptic Hermitian doubled Clifford data at a frozen point: Hermitian
coefficients, the Clifford relations for some inverse metric `g` with
`λ|ξ|² ≤ ξᵀ g ξ ≤ Λ|ξ|²`. -/
def UniformlyElliptic (c₀ : Fin d → Matrix (Fin N) (Fin N) ℂ) (Γ : Matrix (Fin N) (Fin N) ℂ)
    (lam Lam : ℝ) : Prop :=
  (∀ j, (c₀ j)ᴴ = c₀ j) ∧ ∃ g : Matrix (Fin d) (Fin d) ℝ,
    FrozenWilsonSymbol.DoubledCliffordData c₀ Γ g ∧
    (∀ ξ : Fin d → ℝ, lam * ∑ j, ξ j ^ 2 ≤ ∑ j, ∑ k, g j k * (ξ j * ξ k)) ∧
    (∀ ξ : Fin d → ℝ, ∑ j, ∑ k, g j k * (ξ j * ξ k) ≤ Lam * ∑ j, ξ j ^ 2)

/-- The frozen estimate of `FrozenWilsonGardingExact` in Euclidean form (the cell weight
`h^d` cancels). -/
theorem frozen_estimate_eucl (h ϖ lam Lam : ℝ) (hh : 0 < h) (hlam : 0 < lam) (hϖ : ϖ ≠ 0)
    (hLam : 0 ≤ Lam) (c₀ : Fin d → Matrix (Fin N) (Fin N) ℂ) (Γ : Matrix (Fin N) (Fin N) ℂ)
    (hΓ : Γᴴ = Γ) (hell : UniformlyElliptic c₀ Γ lam Lam) (v : TorusSection d n N) :
    ‖eucl v‖ ^ 2 + ∑ j, ‖eucl (forwardDifference h j v)‖ ^ 2 ≤
      frozenConstant lam ϖ * (‖eucl (frozenWilson h ϖ c₀ Γ v)‖ ^ 2 + ‖eucl v‖ ^ 2) := by
  obtain ⟨hherm, g, hc, hlow, hup⟩ := hell
  have key := h1NormSq_le h ϖ lam Lam hh hlam hϖ hLam c₀ Γ g hc hherm hΓ hlow hup v
  unfold h1NormSq at key
  simp only [gridNormSq_eq_norm_eucl_sq, ← Finset.mul_sum] at key
  have hpos : 0 < h ^ d := by positivity
  rw [← mul_add, ← mul_add, mul_left_comm] at key
  exact le_of_mul_le_mul_left key hpos

/-- The absorption arithmetic of the paper's proof: from the frozen estimate
`V + G ≤ C₀ (X² + V)` with `X ≤ a + b + f + ω s`, `s² ≤ d G` and `4 d ω² C₀ ≤ 1`,
`G ≤ 12 C₀ (a² + b² + f²) + 2 C₀ V`. -/
theorem absorb_aux {G V a b f s ω C₀ X dd : ℝ} (hG : 0 ≤ G) (hV : 0 ≤ V)
    (hX : 0 ≤ X) (hC : 0 ≤ C₀) (hXle : X ≤ a + b + f + ω * s) (hs2 : s ^ 2 ≤ dd * G)
    (hfro : V + G ≤ C₀ * (X ^ 2 + V)) (habs : 4 * dd * ω ^ 2 * C₀ ≤ 1) :
    G ≤ 12 * C₀ * (a ^ 2 + b ^ 2 + f ^ 2) + 2 * C₀ * V := by
  have hX2 : X ^ 2 ≤ (a + b + f + ω * s) ^ 2 := pow_le_pow_left₀ hX hXle 2
  have h1 : (a + b + f + ω * s) ^ 2 ≤ 2 * (a + b + f) ^ 2 + 2 * (ω * s) ^ 2 := by
    nlinarith [sq_nonneg (a + b + f - ω * s)]
  have h2 : (a + b + f) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + f ^ 2) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - f), sq_nonneg (a - f)]
  have h3 : (ω * s) ^ 2 ≤ ω ^ 2 * (dd * G) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hs2 (sq_nonneg ω)
  have hQ : X ^ 2 ≤ 6 * (a ^ 2 + b ^ 2 + f ^ 2) + 2 * ω ^ 2 * dd * G := by nlinarith
  have h4 : V + G ≤ C₀ * (6 * (a ^ 2 + b ^ 2 + f ^ 2) + 2 * ω ^ 2 * dd * G + V) :=
    hfro.trans (by gcongr)
  have h5 : 0 ≤ 1 / 2 - 2 * C₀ * ω ^ 2 * dd := by nlinarith
  nlinarith [mul_nonneg hG h5]

/-- The coefficient of `‖u‖` in the cutoff commutator bound: `K' = d K (B + |ϖ| G)`. -/
noncomputable def commutatorConstant (d : ℕ) (ϖ K B G : ℝ) : ℝ := d * K * (B + |ϖ| * G)

/-- **One patch**: for `v = χ u`, the forward differences of `v` are controlled by the localized
Wilson image `χ (D̃ u)`, the commutator term and `v` itself, once the modulus of continuity has
been absorbed. -/
theorem patch_estimate (h ϖ lam Lam : ℝ) (hh : 0 < h) (hlam : 0 < lam) (hϖ : ϖ ≠ 0)
    (hLam : 0 ≤ Lam) (c : CoefficientField d n N) (Γ : Matrix (Fin N) (Fin N) ℂ) (hΓ : Γᴴ = Γ)
    (x₀ : Grid d n) (hell : UniformlyElliptic (c x₀) Γ lam Lam) (χ : Grid d n → ℝ)
    {ω K L B G : ℝ} (hω : 0 ≤ ω) (hK : 0 ≤ K) (hL : 0 ≤ L) (hB : 0 ≤ B) (hG : 0 ≤ G)
    (hgrad : ∀ (j : Fin d) x, |χ (x + Pi.single j 1) - χ x| ≤ h * K)
    (hc : ∀ x j w, euclNormSq (c x j *ᵥ w) ≤ B ^ 2 * euclNormSq w)
    (hΓb : ∀ w, euclNormSq (Γ *ᵥ w) ≤ G ^ 2 * euclNormSq w)
    (hfreeze : ∀ (j : Fin d) x, NearSupport χ j x →
      ∀ w, euclNormSq ((c x j - c x₀ j) *ᵥ w) ≤ ω ^ 2 * euclNormSq w)
    (hLip : ∀ (j : Fin d) x w,
      euclNormSq ((c (x + Pi.single j 1) j - c x j) *ᵥ w) ≤ (h * L) ^ 2 * euclNormSq w)
    (habs : 4 * d * ω ^ 2 * frozenConstant lam ϖ ≤ 1) (u : TorusSection d n N) :
    ∑ j, ‖eucl (forwardDifference h j (cutoff χ u))‖ ^ 2 ≤
      12 * frozenConstant lam ϖ * ‖eucl (cutoff χ (varWilson h ϖ c Γ u))‖ ^ 2 +
      12 * frozenConstant lam ϖ * (commutatorConstant d ϖ K B G * ‖eucl u‖) ^ 2 +
      (3 * frozenConstant lam ϖ * d ^ 2 * L ^ 2 + 2 * frozenConstant lam ϖ) *
        ‖eucl (cutoff χ u)‖ ^ 2 := by
  set v := cutoff χ u with hv
  set C₀ := frozenConstant lam ϖ with hC₀
  have hC : 0 ≤ C₀ := frozenConstant_nonneg lam ϖ
  -- the frozen estimate at `x₀`
  have hfro := frozen_estimate_eucl h ϖ lam Lam hh hlam hϖ hLam (c x₀) Γ hΓ hell v
  -- `‖D̃_{x₀} v‖ ≤ ‖χ D̃ u‖ + ‖[D̃, M_χ] u‖ + ω Σ_j ‖∂_j v‖ + (d L / 2) ‖v‖`
  have hXle : ‖eucl (frozenWilson h ϖ (c x₀) Γ v)‖ ≤
      ‖eucl (cutoff χ (varWilson h ϖ c Γ u))‖ + commutatorConstant d ϖ K B G * ‖eucl u‖ +
        d * L / 2 * ‖eucl v‖ + ω * ∑ j, ‖eucl (forwardDifference h j v)‖ := by
    have h1 : ‖eucl (frozenWilson h ϖ (c x₀) Γ v)‖ ≤ ‖eucl (varWilson h ϖ c Γ v)‖ +
        ‖eucl (varWilson h ϖ c Γ v - frozenWilson h ϖ (c x₀) Γ v)‖ := by
      have := norm_sub_le (eucl (varWilson h ϖ c Γ v))
        (eucl (varWilson h ϖ c Γ v) - eucl (frozenWilson h ϖ (c x₀) Γ v))
      rw [sub_sub_cancel, ← eucl_sub] at this
      exact this
    have h2 : ‖eucl (varWilson h ϖ c Γ v)‖ ≤ ‖eucl (cutoff χ (varWilson h ϖ c Γ u))‖ +
        commutatorConstant d ϖ K B G * ‖eucl u‖ := by
      rw [hv, varWilson_cutoff, eucl_add]
      exact (norm_add_le _ _).trans (add_le_add le_rfl
        (norm_eucl_cutoffCommutator_le h ϖ hh c Γ χ hK hB hG hgrad hc hΓb u))
    have h3 := norm_eucl_freezeDifference_le h ϖ hh c x₀ Γ χ hω hL hfreeze hLip u
    rw [← hv] at h3
    linarith
  have hs2 : (∑ j, ‖eucl (forwardDifference h j v)‖) ^ 2 ≤
      d * ∑ j, ‖eucl (forwardDifference h j v)‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
      (f := fun j => ‖eucl (forwardDifference h j v)‖)
    simpa using this
  have key := absorb_aux (G := ∑ j, ‖eucl (forwardDifference h j v)‖ ^ 2) (V := ‖eucl v‖ ^ 2)
    (a := ‖eucl (cutoff χ (varWilson h ϖ c Γ u))‖) (b := commutatorConstant d ϖ K B G * ‖eucl u‖)
    (f := d * L / 2 * ‖eucl v‖) (s := ∑ j, ‖eucl (forwardDifference h j v)‖) (ω := ω) (C₀ := C₀)
    (X := ‖eucl (frozenWilson h ϖ (c x₀) Γ v)‖) (dd := d)
    (Finset.sum_nonneg fun _ _ => by positivity) (by positivity) (norm_nonneg _) hC hXle hs2 hfro
    habs
  calc ∑ j, ‖eucl (forwardDifference h j v)‖ ^ 2
      ≤ 12 * C₀ * (‖eucl (cutoff χ (varWilson h ϖ c Γ u))‖ ^ 2 +
          (commutatorConstant d ϖ K B G * ‖eucl u‖) ^ 2 + (d * L / 2 * ‖eucl v‖) ^ 2) +
          2 * C₀ * ‖eucl v‖ ^ 2 := key
    _ = _ := by ring

/-- **Discrete product rule for the partition**: `Σ_j ‖∂_j u‖² ≤ 2 Σ_α Σ_j ‖∂_j(χ_α u)‖² +
2 d m K² ‖u‖²`, from `∂_j u = Σ_α (S_j χ_α)² ∂_j u` and `(S_jχ_α) ∂_j u = ∂_j(χ_α u) - (∂_jχ_α) u`. -/
theorem sum_norm_forwardDifference_sq_le (h : ℝ) (hh : 0 < h) {m : ℕ}
    (χ : Fin m → Grid d n → ℝ) (hpart : ∀ x, ∑ α, χ α x ^ 2 = 1) {K : ℝ} (hK : 0 ≤ K)
    (hgrad : ∀ α (j : Fin d) x, |χ α (x + Pi.single j 1) - χ α x| ≤ h * K)
    (u : TorusSection d n N) :
    ∑ j, ‖eucl (forwardDifference h j u)‖ ^ 2 ≤
      2 * ∑ α, ∑ j, ‖eucl (forwardDifference h j (cutoff (χ α) u))‖ ^ 2 +
        2 * d * m * K ^ 2 * ‖eucl u‖ ^ 2 := by
  have hj : ∀ j : Fin d, ‖eucl (forwardDifference h j u)‖ ^ 2 ≤
      ∑ α, (2 * ‖eucl (forwardDifference h j (cutoff (χ α) u))‖ ^ 2 + 2 * (K * ‖eucl u‖) ^ 2) := by
    intro j
    rw [← sum_norm_eucl_cutoff_shift_sq χ hpart j]
    refine Finset.sum_le_sum fun α _ => ?_
    have hid : cutoff (fun x => χ α (x + Pi.single j 1)) (forwardDifference h j u) =
        forwardDifference h j (cutoff (χ α) u) -
          cutoff (fun x => (χ α (x + Pi.single j 1) - χ α x) / h) u := by
      rw [forwardDifference_cutoff]
      abel
    rw [hid, eucl_sub]
    have hgb : ‖eucl (cutoff (fun x => (χ α (x + Pi.single j 1) - χ α x) / h) u)‖ ≤
        K * ‖eucl u‖ := by
      refine norm_eucl_cutoff_le _ hK (fun x => ?_) u
      rw [abs_div, abs_of_pos hh, div_le_iff₀ hh, mul_comm]
      exact hgrad α j x
    have htri := norm_sub_le (eucl (forwardDifference h j (cutoff (χ α) u)))
      (eucl (cutoff (fun x => (χ α (x + Pi.single j 1) - χ α x) / h) u))
    have hnn := norm_nonneg (eucl (forwardDifference h j (cutoff (χ α) u)) -
      eucl (cutoff (fun x => (χ α (x + Pi.single j 1) - χ α x) / h) u))
    nlinarith [sq_nonneg (‖eucl (forwardDifference h j (cutoff (χ α) u))‖ -
      ‖eucl (cutoff (fun x => (χ α (x + Pi.single j 1) - χ α x) / h) u)‖),
      norm_nonneg (eucl (forwardDifference h j (cutoff (χ α) u))),
      norm_nonneg (eucl (cutoff (fun x => (χ α (x + Pi.single j 1) - χ α x) / h) u))]
  calc ∑ j, ‖eucl (forwardDifference h j u)‖ ^ 2
      ≤ ∑ j : Fin d, ∑ α, (2 * ‖eucl (forwardDifference h j (cutoff (χ α) u))‖ ^ 2 +
          2 * (K * ‖eucl u‖) ^ 2) := Finset.sum_le_sum fun j _ => hj j
    _ = 2 * ∑ α, ∑ j, ‖eucl (forwardDifference h j (cutoff (χ α) u))‖ ^ 2 +
        2 * d * m * K ^ 2 * ‖eucl u‖ ^ 2 := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ← Finset.mul_sum]
        ring

/-- The explicit constant of `eq:supp-general-Garding`: depends on the dimension `d`, the number
of patches `m`, the cutoff-gradient bound `K`, the coefficient Lipschitz bound `L`, the coefficient
bound `B`, `‖Γ_⊥‖ ≤ G`, `ϖ` and the ellipticity constant `λ`, but not on `h` or `n`. -/
noncomputable def gardingConstant (d m : ℕ) (lam ϖ K L B G : ℝ) : ℝ :=
  24 * frozenConstant lam ϖ + 1 +
    24 * m * frozenConstant lam ϖ * commutatorConstant d ϖ K B G ^ 2 +
    6 * frozenConstant lam ϖ * d ^ 2 * L ^ 2 + 4 * frozenConstant lam ϖ + 2 * d * m * K ^ 2

/-- **`eq:supp-general-Garding`, variable coefficients (`thm:supp-general-Wilson-ellipticity`).**
Let `χ_α` (`α < m`) be a lattice partition of unity on the torus, `Σ_α χ_α² = 1`, with cutoff
gradients `|χ_α(x + h e_j) - χ_α(x)| ≤ h K`; let the sampled coefficients be bounded by `B`,
Lipschitz with constant `L`, and within the modulus of continuity `ω` of their frozen values
`ĉ^j(x_α)` on the (one-step enlarged) patch of `χ_α`, where the frozen data are Hermitian and
uniformly elliptic (`λ, Λ`); let `Γ_⊥` be Hermitian with `‖Γ_⊥‖ ≤ G`, `ϖ ≠ 0`, and let the
patches be fine enough that `4 d ω² max(1, min(λ, ϖ²)⁻¹) ≤ 1`.  Then, for every torus section,
`‖u‖²_{1,h} ≤ C (‖D̃ u‖_h² + ‖u‖_h²)` with `C = gardingConstant d m λ ϖ K L B G`, uniformly in
`h` and `n`. -/
theorem variable_garding (h ϖ lam Lam : ℝ) (hh : 0 < h) (hlam : 0 < lam) (hϖ : ϖ ≠ 0)
    (hLam : 0 ≤ Lam) (c : CoefficientField d n N) (Γ : Matrix (Fin N) (Fin N) ℂ) (hΓ : Γᴴ = Γ)
    {m : ℕ} (χ : Fin m → Grid d n → ℝ) (hpart : ∀ x, ∑ α, χ α x ^ 2 = 1)
    (x₀ : Fin m → Grid d n) (hell : ∀ α, UniformlyElliptic (c (x₀ α)) Γ lam Lam)
    {ω K L B G : ℝ} (hω : 0 ≤ ω) (hK : 0 ≤ K) (hL : 0 ≤ L) (hB : 0 ≤ B) (hG : 0 ≤ G)
    (hgrad : ∀ α (j : Fin d) x, |χ α (x + Pi.single j 1) - χ α x| ≤ h * K)
    (hc : ∀ x j w, euclNormSq (c x j *ᵥ w) ≤ B ^ 2 * euclNormSq w)
    (hΓb : ∀ w, euclNormSq (Γ *ᵥ w) ≤ G ^ 2 * euclNormSq w)
    (hfreeze : ∀ α (j : Fin d) x, NearSupport (χ α) j x →
      ∀ w, euclNormSq ((c x j - c (x₀ α) j) *ᵥ w) ≤ ω ^ 2 * euclNormSq w)
    (hLip : ∀ (j : Fin d) x w,
      euclNormSq ((c (x + Pi.single j 1) j - c x j) *ᵥ w) ≤ (h * L) ^ 2 * euclNormSq w)
    (habs : 4 * d * ω ^ 2 * frozenConstant lam ϖ ≤ 1) (u : TorusSection d n N) :
    h1NormSq h u ≤ gardingConstant d m lam ϖ K L B G *
      (gridNormSq h (varWilson h ϖ c Γ u) + gridNormSq h u) := by
  set C₀ := frozenConstant lam ϖ with hC₀
  set K' := commutatorConstant d ϖ K B G with hK'
  have hC : 0 ≤ C₀ := frozenConstant_nonneg lam ϖ
  have hK'0 : 0 ≤ K' := by
    rw [hK', commutatorConstant]
    positivity
  -- sum of the patch estimates
  have hpatch : ∑ α, ∑ j, ‖eucl (forwardDifference h j (cutoff (χ α) u))‖ ^ 2 ≤
      12 * C₀ * ‖eucl (varWilson h ϖ c Γ u)‖ ^ 2 +
        (12 * m * C₀ * K' ^ 2 + (3 * C₀ * d ^ 2 * L ^ 2 + 2 * C₀)) * ‖eucl u‖ ^ 2 := by
    calc ∑ α, ∑ j, ‖eucl (forwardDifference h j (cutoff (χ α) u))‖ ^ 2
        ≤ ∑ α, (12 * C₀ * ‖eucl (cutoff (χ α) (varWilson h ϖ c Γ u))‖ ^ 2 +
            12 * C₀ * (K' * ‖eucl u‖) ^ 2 +
            (3 * C₀ * d ^ 2 * L ^ 2 + 2 * C₀) * ‖eucl (cutoff (χ α) u)‖ ^ 2) :=
          Finset.sum_le_sum fun α _ => patch_estimate h ϖ lam Lam hh hlam hϖ hLam c Γ hΓ (x₀ α)
            (hell α) (χ α) hω hK hL hB hG (hgrad α) hc hΓb (hfreeze α) hLip habs u
      _ = 12 * C₀ * ∑ α, ‖eucl (cutoff (χ α) (varWilson h ϖ c Γ u))‖ ^ 2 +
            m * (12 * C₀ * (K' * ‖eucl u‖) ^ 2) +
            (3 * C₀ * d ^ 2 * L ^ 2 + 2 * C₀) * ∑ α, ‖eucl (cutoff (χ α) u)‖ ^ 2 := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, ← Finset.mul_sum]
      _ = _ := by
          rw [sum_norm_eucl_cutoff_sq χ hpart, sum_norm_eucl_cutoff_sq χ hpart]
          ring
  have hprod := sum_norm_forwardDifference_sq_le h hh χ hpart hK hgrad u
  have hX : 0 ≤ ‖eucl (varWilson h ϖ c Γ u)‖ ^ 2 := by positivity
  have hY : 0 ≤ ‖eucl u‖ ^ 2 := by positivity
  have key : ‖eucl u‖ ^ 2 + ∑ j, ‖eucl (forwardDifference h j u)‖ ^ 2 ≤
      gardingConstant d m lam ϖ K L B G *
        (‖eucl (varWilson h ϖ c Γ u)‖ ^ 2 + ‖eucl u‖ ^ 2) := by
    have h1 : 24 * C₀ * ‖eucl (varWilson h ϖ c Γ u)‖ ^ 2 ≤
        gardingConstant d m lam ϖ K L B G * ‖eucl (varWilson h ϖ c Γ u)‖ ^ 2 := by
      refine mul_le_mul_of_nonneg_right ?_ hX
      unfold gardingConstant
      rw [← hC₀, ← hK']
      have : 0 ≤ 24 * m * C₀ * K' ^ 2 + 6 * C₀ * d ^ 2 * L ^ 2 + 4 * C₀ + 2 * d * m * K ^ 2 := by
        positivity
      linarith
    have h2 : (1 + 2 * (12 * m * C₀ * K' ^ 2 + (3 * C₀ * d ^ 2 * L ^ 2 + 2 * C₀)) +
        2 * d * m * K ^ 2) * ‖eucl u‖ ^ 2 ≤
        gardingConstant d m lam ϖ K L B G * ‖eucl u‖ ^ 2 := by
      refine mul_le_mul_of_nonneg_right ?_ hY
      unfold gardingConstant
      rw [← hC₀, ← hK']
      linarith
    nlinarith
  have hpos : 0 ≤ h ^ d := by positivity
  calc h1NormSq h u
      = h ^ d * (‖eucl u‖ ^ 2 + ∑ j, ‖eucl (forwardDifference h j u)‖ ^ 2) := by
        unfold h1NormSq
        simp only [gridNormSq_eq_norm_eucl_sq, ← Finset.mul_sum, mul_add]
    _ ≤ h ^ d * (gardingConstant d m lam ϖ K L B G *
        (‖eucl (varWilson h ϖ c Γ u)‖ ^ 2 + ‖eucl u‖ ^ 2)) := by gcongr
    _ = gardingConstant d m lam ϖ K L B G *
        (gridNormSq h (varWilson h ϖ c Γ u) + gridNormSq h u) := by
        simp only [gridNormSq_eq_norm_eucl_sq]
        ring

/-! ### Self-adjointness (the symmetric placement of the coefficients) -/

/-- The grid inner product `⟨u, v⟩ = Σ_x ⟨u(x), v(x)⟩_{ℂ^N}` (antilinear in the first slot). -/
def gridInner (u v : TorusSection d n N) : ℂ := ∑ x, star (u x) ⬝ᵥ v x

theorem gridInner_add_left (u u' v : TorusSection d n N) :
    gridInner (u + u') v = gridInner u v + gridInner u' v := by
  simp [gridInner, add_dotProduct, Finset.sum_add_distrib]

theorem gridInner_add_right (u v v' : TorusSection d n N) :
    gridInner u (v + v') = gridInner u v + gridInner u v' := by
  simp [gridInner, dotProduct_add, Finset.sum_add_distrib]

theorem gridInner_sub_left (u u' v : TorusSection d n N) :
    gridInner (u - u') v = gridInner u v - gridInner u' v := by
  simp [gridInner, sub_dotProduct, Finset.sum_sub_distrib]

theorem gridInner_sub_right (u v v' : TorusSection d n N) :
    gridInner u (v - v') = gridInner u v - gridInner u v' := by
  simp [gridInner, dotProduct_sub, Finset.sum_sub_distrib]

theorem gridInner_smul_left (a : ℂ) (u v : TorusSection d n N) :
    gridInner (a • u) v = star a * gridInner u v := by
  simp [gridInner, smul_dotProduct, Finset.mul_sum]

theorem gridInner_smul_right (a : ℂ) (u v : TorusSection d n N) :
    gridInner u (a • v) = a * gridInner u v := by
  simp [gridInner, dotProduct_smul, Finset.mul_sum]

theorem gridInner_sum_left {ι : Type*} (s : Finset ι) (f : ι → TorusSection d n N)
    (v : TorusSection d n N) : gridInner (∑ i ∈ s, f i) v = ∑ i ∈ s, gridInner (f i) v := by
  simp only [gridInner, Finset.sum_apply, star_sum, sum_dotProduct]
  rw [Finset.sum_comm]

theorem gridInner_sum_right {ι : Type*} (s : Finset ι) (u : TorusSection d n N)
    (f : ι → TorusSection d n N) : gridInner u (∑ i ∈ s, f i) = ∑ i ∈ s, gridInner u (f i) := by
  simp only [gridInner, Finset.sum_apply, dotProduct_sum]
  rw [Finset.sum_comm]

/-- `S_j^* ` is the adjoint of `S_j`. -/
theorem gridInner_shift (j : Fin d) (u v : TorusSection d n N) :
    gridInner (shift j u) v = gridInner u (shiftAdj j v) := by
  simp only [gridInner, shift, shiftAdj]
  have hb : Function.Bijective (fun x : Grid d n => x + Pi.single j (1 : ZMod n)) :=
    (Equiv.addRight (Pi.single j (1 : ZMod n) : Grid d n)).bijective
  have := hb.sum_comp (fun x => star (u x) ⬝ᵥ v (x - Pi.single j 1))
  simp only [add_sub_cancel_right] at this
  exact this

/-- A pointwise Hermitian multiplication is symmetric. -/
theorem gridInner_varMul (c : Grid d n → Matrix (Fin N) (Fin N) ℂ) (hc : ∀ x, (c x)ᴴ = c x)
    (u v : TorusSection d n N) : gridInner (varMul c u) v = gridInner u (varMul c v) := by
  simp only [gridInner, varMul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hc x]

theorem conj_inv_two_I_mul (h : ℝ) :
    star ((2 * Complex.I * (h : ℂ))⁻¹) = -(2 * Complex.I * (h : ℂ))⁻¹ := by
  simp only [Complex.star_def, map_inv₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  ring

/-- `P_j` is symmetric. -/
theorem gridInner_symmetricDifference (h : ℝ) (j : Fin d) (u v : TorusSection d n N) :
    gridInner (symmetricDifference h j u) v = gridInner u (symmetricDifference h j v) := by
  have hl : symmetricDifference h j u = (2 * Complex.I * (h : ℂ))⁻¹ • (shift j u - shiftAdj j u) :=
    by funext x; rfl
  have hr : symmetricDifference h j v = (2 * Complex.I * (h : ℂ))⁻¹ • (shift j v - shiftAdj j v) :=
    by funext x; rfl
  have hadj : gridInner (shiftAdj j u) v = gridInner u (shift j v) := by
    have := gridInner_shift j (shiftAdj j u) (shift j v)
    have h1 : shift j (shiftAdj j u) = u := by
      funext x; simp [shift, shiftAdj]
    have h2 : shiftAdj j (shift j v) = v := by
      funext x; simp [shift, shiftAdj]
    rw [h1, h2] at this
    exact this.symm
  rw [hl, hr, gridInner_smul_left, gridInner_smul_right, conj_inv_two_I_mul, gridInner_sub_left,
    gridInner_sub_right, gridInner_shift, hadj]
  ring

/-- `W` is symmetric. -/
theorem gridInner_wilsonTerm (h : ℝ) (u v : TorusSection d n N) :
    gridInner (wilsonTerm h u) v = gridInner u (wilsonTerm h v) := by
  have hl : wilsonTerm h u = (2 * (h : ℂ))⁻¹ • ∑ j, ((2 : ℂ) • u - shift j u - shiftAdj j u) := by
    funext x; simp [wilsonTerm, Finset.sum_apply]
  have hr : wilsonTerm h v = (2 * (h : ℂ))⁻¹ • ∑ j, ((2 : ℂ) • v - shift j v - shiftAdj j v) := by
    funext x; simp [wilsonTerm, Finset.sum_apply]
  have hadj : ∀ j, gridInner (shiftAdj j u) v = gridInner u (shift j v) := by
    intro j
    have := gridInner_shift j (shiftAdj j u) (shift j v)
    have h1 : shift j (shiftAdj j u) = u := by
      funext x; simp [shift, shiftAdj]
    have h2 : shiftAdj j (shift j v) = v := by
      funext x; simp [shift, shiftAdj]
    rw [h1, h2] at this
    exact this.symm
  have hstar : star ((2 * (h : ℂ))⁻¹) = (2 * (h : ℂ))⁻¹ := by
    simp [Complex.conj_ofReal]
  rw [hl, hr, gridInner_smul_left, gridInner_smul_right, hstar, gridInner_sum_left,
    gridInner_sum_right]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gridInner_sub_left, gridInner_sub_left, gridInner_sub_right, gridInner_sub_right,
    gridInner_smul_left, gridInner_smul_right, gridInner_shift, hadj]
  have h2 : star (2 : ℂ) = 2 := by simp
  rw [h2]
  ring

/-- A constant matrix commutes with the Wilson term. -/
theorem matMul_wilsonTerm (h : ℝ) (Γ : Matrix (Fin N) (Fin N) ℂ) (v : TorusSection d n N) :
    matMul Γ (wilsonTerm h v) = wilsonTerm h (matMul Γ v) := by
  funext x
  simp only [matMul, wilsonTerm, shift, shiftAdj, Matrix.mulVec_smul, Matrix.mulVec_sum,
    Matrix.mulVec_sub]

/-- **Self-adjointness** (`thm:supp-general-Wilson-ellipticity`, last clause): with Hermitian
coefficients `ĉ^j(x)` and Hermitian `Γ_⊥`, the symmetric placement `½(M_{ĉ^j} P_j + P_j M_{ĉ^j})`
makes the finite operator `D̃` symmetric for the grid inner product, hence self-adjoint. -/
theorem varWilson_symmetric (h ϖ : ℝ) (c : CoefficientField d n N) (Γ : Matrix (Fin N) (Fin N) ℂ)
    (hc : ∀ x j, (c x j)ᴴ = c x j) (hΓ : Γᴴ = Γ) (u v : TorusSection d n N) :
    gridInner (varWilson h ϖ c Γ u) v = gridInner u (varWilson h ϖ c Γ v) := by
  have hcj : ∀ j, gridInner (varMul (coeff c j) u) v = gridInner u (varMul (coeff c j) v) :=
    fun j => gridInner_varMul (coeff c j) (fun x => hc x j) u v
  have hstar2 : star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by simp
  have hstarϖ : star ((ϖ : ℝ) : ℂ) = (ϖ : ℂ) := Complex.conj_ofReal ϖ
  simp only [varWilson, gridInner_add_left, gridInner_add_right, gridInner_smul_left,
    gridInner_smul_right, hstar2, hstarϖ, gridInner_sum_left, gridInner_sum_right]
  congr 2
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [gridInner_varMul (coeff c j) (fun x => hc x j), gridInner_symmetricDifference,
      gridInner_symmetricDifference, gridInner_varMul (coeff c j) (fun x => hc x j), add_comm]
  · rw [← varMul_const, gridInner_varMul (fun _ => Γ) (fun _ => hΓ), gridInner_wilsonTerm,
      varMul_const, matMul_wilsonTerm]

end RenewalGeometry.VariableWilsonGarding
