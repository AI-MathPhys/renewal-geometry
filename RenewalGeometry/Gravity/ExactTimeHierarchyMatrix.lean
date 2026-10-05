/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.ExactTimeHierarchy
import RenewalGeometry.Gravity.ExactScalarTraceReconstruction

/-!
# The time-derivative hierarchy for the actual matrix objects
(`thm:supp-exact-time-hierarchy`, `eq:supp-exact-time-sources`,
`eq:supp-exact-first-time-source`; emergent-spacetime manuscript)

`Gravity/ExactTimeHierarchy.lean` proves the hierarchy in an abstract normed algebra, under
derived-form hypotheses (`C`, `ζ` of class `C^r`, `H(t)` invertible, `E^*v = −χ`).  This file
derives all of them from the hypotheses of the manuscript and states the theorem for the actual
vectors `ζ, χ ∈ ℝ^k`, `v ∈ ℝ^n`:

* hypotheses (paper's): the remaining source `F(t) : Matrix n m ℝ` and the target `b(t)` are of
  class `C^r`, `F(t)` has full column rank (`det(F(t)ᵀF(t)) ≠ 0`) and the signed Gram
  `F(t)ᵀK₀⁻¹F(t)` is regular, at every time; `v(t)` is the physical response
  (`ExactScalarReconstruction.IsResponse`: `F(t)ᵀv(t) = b(t)`, `K₀v(t) ∈ Ran F(t)`);
* derived: `C^r` regularity of `(FᵀF)⁻¹`, `Π`, `w`, `C`, `ζ`, `χ` and `v`
  (`contDiff_gramInv` … `contDiff_reconstructed`), invertibility of `H(t)` (from
  `signedGram_isUnit_iff`), `v(t) = w(t) − 3(I − Π(t))Eχ(t)` and `E^*v(t) = −χ(t)` (from
  `response_eq`);
* `hierarchyVec`: the vector recursion of `eq:supp-exact-time-sources`,
  `χ_j = H⁻¹[ζ^{(j)} + 3 Σ_{ℓ=1}^j binom(j,ℓ) C^{(ℓ)} χ_{j−ℓ}]`;
* `hierarchyVec_eq_iteratedDeriv`: `χ_j = χ^{(j)}` for `j ≤ r` (transferred from the algebra
  theorem through the column embedding `x ↦ [x ⋯ x]`, `colLin`);
* **`exact_time_hierarchy`**: the full statement, `χ_j = χ^{(j)} = −E^*v^{(j)}` and, for
  `r ≥ 1`, `χ' = H⁻¹(ζ' + 3C'χ)`, `v' = w' + 3Π'Eχ − 3(I − Π)Eχ'`.

Conventions: `C^r` regularity of matrix-valued maps is taken with the `L∞`-operator norm
(`Matrix.Norms.Operator`); all norms on these finite-dimensional spaces are equivalent, so this
is the usual notion.  As in `ExactScalarTraceReconstruction`, the trace map is any isometry `E`
with `EᵀE = 1` (the paper's `Eτ = τI/√3`).
-/

open Matrix
open scoped Matrix.Norms.Operator

noncomputable section

namespace RenewalGeometry.ExactTimeHierarchyMatrix

open ExactScalarReconstruction ExactTimeHierarchy

/-! ### Calculus helpers in finite dimension -/

section helpers

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A bilinear map on finite-dimensional spaces, as a continuous bilinear map. -/
def bilinCLM [FiniteDimensional ℝ F] (B : E →ₗ[ℝ] F →ₗ[ℝ] G) : E →L[ℝ] F →L[ℝ] G :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (F →ₗ[ℝ] G) ≃ₗ[ℝ] (F →L[ℝ] G)).toLinearMap ∘ₗ B)

theorem contDiff_bilin [FiniteDimensional ℝ F] {r : WithTop ℕ∞} (B : E →ₗ[ℝ] F →ₗ[ℝ] G)
    {f : ℝ → E} {g : ℝ → F} (hf : ContDiff ℝ r f) (hg : ContDiff ℝ r g) :
    ContDiff ℝ r (fun t => B (f t) (g t)) :=
  ((bilinCLM B).contDiff.comp hf).clm_apply hg

theorem hasDerivAt_bilin [FiniteDimensional ℝ F] (B : E →ₗ[ℝ] F →ₗ[ℝ] G) {u : ℝ → E}
    {v : ℝ → F} {u' : E} {v' : F} {x : ℝ} (hu : HasDerivAt u u' x) (hv : HasDerivAt v v' x) :
    HasDerivAt (fun t => B (u t) (v t)) (B (u x) v' + B u' (v x)) x :=
  (bilinCLM B).hasDerivAt_of_bilinear (fun _ => hu) (fun _ => hv)

theorem contDiff_lin {r : WithTop ℕ∞} (L : E →ₗ[ℝ] F) {f : ℝ → E} (hf : ContDiff ℝ r f) :
    ContDiff ℝ r (fun t => L (f t)) :=
  (LinearMap.toContinuousLinearMap L).contDiff.comp hf

theorem hasDerivAt_lin (L : E →ₗ[ℝ] F) {f : ℝ → E} {f' : E} {x : ℝ}
    (hf : HasDerivAt f f' x) : HasDerivAt (fun t => L (f t)) (L f') x :=
  (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt x hf

theorem iteratedDeriv_lin (L : E →ₗ[ℝ] F) {f : ℝ → E} {t : ℝ} {j : ℕ}
    (hf : ContDiffAt ℝ j f t) :
    iteratedDeriv j (fun t => L (f t)) t = L (iteratedDeriv j f t) := by
  simp only [iteratedDeriv_eq_iteratedFDeriv]
  have h := (LinearMap.toContinuousLinearMap L).iteratedFDeriv_comp_left hf (i := j) le_rfl
  rw [show (fun t => L (f t)) = ⇑(LinearMap.toContinuousLinearMap L) ∘ f from rfl, h]
  rfl

end helpers

/-! ### Matrix bilinear maps -/

section matrixMaps

variable {a b c : Type} [Fintype a] [Fintype b] [Fintype c]

/-- Matrix multiplication as a bilinear map. -/
def mulBil : Matrix a b ℝ →ₗ[ℝ] Matrix b c ℝ →ₗ[ℝ] Matrix a c ℝ :=
  LinearMap.mk₂ ℝ (fun A B => A * B) Matrix.add_mul (fun s A B => Matrix.smul_mul s A B)
    Matrix.mul_add (fun s A B => Matrix.mul_smul A s B)

/-- Matrix–vector multiplication as a bilinear map. -/
def mulVecBil : Matrix a b ℝ →ₗ[ℝ] (b → ℝ) →ₗ[ℝ] (a → ℝ) :=
  LinearMap.mk₂ ℝ (fun A x => A *ᵥ x) Matrix.add_mulVec (fun s A x => Matrix.smul_mulVec s A x)
    Matrix.mulVec_add (fun s A x => Matrix.mulVec_smul A s x)

/-- Transposition as a linear map. -/
def transposeLin : Matrix a b ℝ →ₗ[ℝ] Matrix b a ℝ where
  toFun A := Aᵀ
  map_add' := Matrix.transpose_add
  map_smul' := Matrix.transpose_smul

/-- The column embedding `x ↦ [x ⋯ x]`. -/
def colLin : (a → ℝ) →ₗ[ℝ] Matrix a a ℝ where
  toFun x := Matrix.of fun i _ => x i
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- Its left inverse, the diagonal. -/
def diagLin : Matrix a a ℝ →ₗ[ℝ] (a → ℝ) where
  toFun X i := X i i
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

theorem diagLin_colLin (x : a → ℝ) : diagLin (colLin x) = x := by
  ext i; simp [diagLin, colLin]

theorem colLin_injective : Function.Injective (colLin : (a → ℝ) →ₗ[ℝ] Matrix a a ℝ) :=
  fun x y h => by rw [← diagLin_colLin x, h, diagLin_colLin]

theorem mul_colLin (A : Matrix a a ℝ) (x : a → ℝ) : A * colLin x = colLin (A *ᵥ x) := by
  ext i j
  simp [colLin, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem contDiff_mul {r : WithTop ℕ∞} {f : ℝ → Matrix a b ℝ} {g : ℝ → Matrix b c ℝ}
    (hf : ContDiff ℝ r f) (hg : ContDiff ℝ r g) : ContDiff ℝ r (fun t => f t * g t) :=
  contDiff_bilin mulBil hf hg

theorem contDiff_mulVec {r : WithTop ℕ∞} {f : ℝ → Matrix a b ℝ} {g : ℝ → b → ℝ}
    (hf : ContDiff ℝ r f) (hg : ContDiff ℝ r g) : ContDiff ℝ r (fun t => f t *ᵥ g t) :=
  contDiff_bilin mulVecBil hf hg

theorem contDiff_transpose {r : WithTop ℕ∞} {f : ℝ → Matrix a b ℝ} (hf : ContDiff ℝ r f) :
    ContDiff ℝ r (fun t => (f t)ᵀ) :=
  contDiff_lin transposeLin hf

end matrixMaps

/-! ### The vector hierarchy -/

section hierarchy

variable {k : Type} [Fintype k] [DecidableEq k]

/-- `H(t) = 2I − 3C(t)`. -/
def trOp (C : ℝ → Matrix k k ℝ) (t : ℝ) : Matrix k k ℝ := (2 : ℝ) • 1 - (3 : ℝ) • C t

/-- `χ(t) = H(t)⁻¹ ζ(t)`. -/
def trResp (C : ℝ → Matrix k k ℝ) (ζ : ℝ → k → ℝ) (t : ℝ) : k → ℝ := (trOp C t)⁻¹ *ᵥ ζ t

/-- **`eq:supp-exact-time-sources`**: `χ_0 = χ`,
`χ_j = H⁻¹[ζ^{(j)} + 3 Σ_{ℓ=1}^{j} binom(j,ℓ) C^{(ℓ)} χ_{j−ℓ}]` (sum indexed by `ℓ = l + 1`). -/
def hierarchyVec (C : ℝ → Matrix k k ℝ) (ζ : ℝ → k → ℝ) (t : ℝ) : ℕ → (k → ℝ)
  | 0 => trResp C ζ t
  | j + 1 => (trOp C t)⁻¹ *ᵥ (iteratedDeriv (j + 1) ζ t + 3 • ∑ l ∈ Finset.range (j + 1),
      ((j + 1).choose (l + 1)) • (iteratedDeriv (l + 1) C t *ᵥ hierarchyVec C ζ t (j - l)))
termination_by j => j
decreasing_by omega

theorem hierarchyVec_zero (C : ℝ → Matrix k k ℝ) (ζ : ℝ → k → ℝ) (t : ℝ) :
    hierarchyVec C ζ t 0 = trResp C ζ t := by
  rw [hierarchyVec]

theorem hierarchyVec_succ (C : ℝ → Matrix k k ℝ) (ζ : ℝ → k → ℝ) (t : ℝ) (j : ℕ) :
    hierarchyVec C ζ t (j + 1) = (trOp C t)⁻¹ *ᵥ (iteratedDeriv (j + 1) ζ t +
      3 • ∑ l ∈ Finset.range (j + 1),
        ((j + 1).choose (l + 1)) • (iteratedDeriv (l + 1) C t *ᵥ hierarchyVec C ζ t (j - l))) := by
  rw [hierarchyVec]

theorem traceOperator_eq_trOp (C : ℝ → Matrix k k ℝ) (t : ℝ) :
    traceOperator C t = trOp C t := by
  unfold traceOperator trOp
  congr 1
  · rw [two_smul, one_add_one_eq_two]
  · rw [← Nat.cast_ofNat (R := Matrix k k ℝ) (n := 3), ← nsmul_eq_mul,
      ← Nat.cast_smul_eq_nsmul ℝ]
    norm_num

theorem traceResponse_colLin (C : ℝ → Matrix k k ℝ) (ζ : ℝ → k → ℝ) (t : ℝ) :
    traceResponse C (fun t => colLin (ζ t)) t = colLin (trResp C ζ t) := by
  unfold traceResponse trResp
  rw [traceOperator_eq_trOp, ← Matrix.nonsing_inv_eq_ringInverse, mul_colLin]

theorem isUnit_traceOperator {C : ℝ → Matrix k k ℝ} {t : ℝ} (h : IsUnit (trOp C t).det) :
    IsUnit (traceOperator C t) := by
  rw [traceOperator_eq_trOp]
  exact (Matrix.isUnit_iff_isUnit_det _).mpr h

/-- `C^r` regularity of `χ = H⁻¹ζ`. -/
theorem contDiff_trResp {r : ℕ} (C : ℝ → Matrix k k ℝ) (ζ : ℝ → k → ℝ) (hC : ContDiff ℝ r C)
    (hζ : ContDiff ℝ r ζ) (hH : ∀ t, IsUnit (trOp C t).det) :
    ContDiff ℝ r (trResp C ζ) := by
  have h1 : ContDiff ℝ r (traceResponse C (fun t => colLin (ζ t))) :=
    contDiff_iff_contDiffAt.2 fun t => contDiffAt_traceResponse C _ t hC.contDiffAt
      (contDiff_lin colLin hζ).contDiffAt (isUnit_traceOperator (hH t))
  have h2 := contDiff_lin diagLin h1
  convert h2 using 1
  funext t
  rw [traceResponse_colLin, diagLin_colLin]

theorem colLin_hierarchyVec {r : ℕ} (C : ℝ → Matrix k k ℝ) (ζ : ℝ → k → ℝ)
    (hζ : ContDiff ℝ r ζ) (t : ℝ) (j : ℕ) (hj : j ≤ r) :
    colLin (hierarchyVec C ζ t j) = hierarchy C (fun t => colLin (ζ t)) t j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    cases j with
    | zero => rw [hierarchyVec_zero, hierarchy_zero, traceResponse_colLin]
    | succ j =>
      rw [hierarchyVec_succ, hierarchy_succ, traceOperator_eq_trOp,
        ← Matrix.nonsing_inv_eq_ringInverse, ← mul_colLin,
        iteratedDeriv_lin colLin (hζ.contDiffAt.of_le (by exact_mod_cast hj))]
      congr 1
      simp only [map_add, map_nsmul, map_sum]
      congr 1
      rw [nsmul_eq_mul, Nat.cast_ofNat]
      congr 1
      refine Finset.sum_congr rfl fun l hl => ?_
      have hl' := Finset.mem_range.mp hl
      rw [nsmul_eq_mul, ← mul_colLin, ih (j - l) (by omega) (by omega)]

/-- **`thm:supp-exact-time-hierarchy`, vector form**: `χ_j = χ^{(j)}` for `j ≤ r`. -/
theorem hierarchyVec_eq_iteratedDeriv {r : ℕ} (C : ℝ → Matrix k k ℝ) (ζ : ℝ → k → ℝ)
    (hC : ContDiff ℝ r C) (hζ : ContDiff ℝ r ζ) (hH : ∀ t, IsUnit (trOp C t).det) (t : ℝ)
    (j : ℕ) (hj : j ≤ r) :
    hierarchyVec C ζ t j = iteratedDeriv j (trResp C ζ) t := by
  apply colLin_injective
  have hχ := contDiff_trResp C ζ hC hζ hH
  rw [colLin_hierarchyVec C ζ hζ t j hj,
    hierarchy_eq_iteratedDeriv C _ hC (contDiff_lin colLin hζ)
      (fun t => isUnit_traceOperator (hH t)) t j hj]
  rw [show traceResponse C (fun t => colLin (ζ t)) = fun t => colLin (trResp C ζ t) from
    funext fun t => traceResponse_colLin C ζ t]
  exact iteratedDeriv_lin colLin (hχ.contDiffAt.of_le (by exact_mod_cast hj))

end hierarchy

/-! ### The actual objects: regularity -/

section objects

variable {n m k : Type} [Fintype n] [Fintype m] [Fintype k] [DecidableEq n] [DecidableEq m]
  [DecidableEq k]

theorem contDiff_gramInv {r : ℕ} (F : ℝ → Matrix n m ℝ) (hF : ContDiff ℝ r F)
    (hG : ∀ t, IsUnit ((F t)ᵀ * F t).det) :
    ContDiff ℝ r (fun t => ((F t)ᵀ * F t)⁻¹) := by
  have hFF : ContDiff ℝ r (fun t => (F t)ᵀ * F t) :=
    contDiff_mul (contDiff_transpose hF) hF
  rw [contDiff_iff_contDiffAt]
  intro t
  have hu : IsUnit ((F t)ᵀ * F t) := (Matrix.isUnit_iff_isUnit_det _).mpr (hG t)
  have h1 : ContDiffAt ℝ r Ring.inverse ((F t)ᵀ * F t) := by
    have := contDiffAt_ringInverse (𝕜 := ℝ) (n := r) hu.unit
    rwa [hu.unit_spec] at this
  have h2 := h1.comp t hFF.contDiffAt
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  exact Matrix.nonsing_inv_eq_ringInverse _

theorem contDiff_sourceProj {r : ℕ} (F : ℝ → Matrix n m ℝ) (hF : ContDiff ℝ r F)
    (hG : ∀ t, IsUnit ((F t)ᵀ * F t).det) :
    ContDiff ℝ r (fun t => sourceProj (F t)) :=
  contDiff_mul (contDiff_mul hF (contDiff_gramInv F hF hG)) (contDiff_transpose hF)

theorem contDiff_sourceResponse {r : ℕ} (F : ℝ → Matrix n m ℝ) (b : ℝ → m → ℝ)
    (hF : ContDiff ℝ r F) (hb : ContDiff ℝ r b) (hG : ∀ t, IsUnit ((F t)ᵀ * F t).det) :
    ContDiff ℝ r (fun t => sourceResponse (F t) (b t)) :=
  contDiff_mulVec hF (contDiff_mulVec (contDiff_gramInv F hF hG) hb)

theorem contDiff_traceCompression {r : ℕ} (F : ℝ → Matrix n m ℝ) (E : Matrix n k ℝ)
    (hF : ContDiff ℝ r F) (hG : ∀ t, IsUnit ((F t)ᵀ * F t).det) :
    ContDiff ℝ r (fun t => traceCompression (F t) E) :=
  contDiff_mul (contDiff_mul contDiff_const (contDiff_sourceProj F hF hG)) contDiff_const

theorem contDiff_traceSource {r : ℕ} (F : ℝ → Matrix n m ℝ) (E : Matrix n k ℝ)
    (b : ℝ → m → ℝ) (hF : ContDiff ℝ r F) (hb : ContDiff ℝ r b)
    (hG : ∀ t, IsUnit ((F t)ᵀ * F t).det) :
    ContDiff ℝ r (fun t => traceSource (F t) E (b t)) :=
  contDiff_mulVec contDiff_const (contDiff_sourceResponse F b hF hb hG)

theorem trOp_eq_traceOp (F : ℝ → Matrix n m ℝ) (E : Matrix n k ℝ) (t : ℝ) :
    trOp (fun t => traceCompression (F t) E) t = traceOp (F t) E := rfl

theorem trResp_eq_traceResponseVec (F : ℝ → Matrix n m ℝ) (E : Matrix n k ℝ)
    (b : ℝ → m → ℝ) (t : ℝ) :
    trResp (fun t => traceCompression (F t) E) (fun t => traceSource (F t) E (b t)) t
      = traceResponseVec (F t) E (b t) := rfl

theorem contDiff_traceResponseVec {r : ℕ} (F : ℝ → Matrix n m ℝ) (E : Matrix n k ℝ)
    (b : ℝ → m → ℝ) (hF : ContDiff ℝ r F) (hb : ContDiff ℝ r b)
    (hG : ∀ t, IsUnit ((F t)ᵀ * F t).det) (hH : ∀ t, IsUnit (traceOp (F t) E).det) :
    ContDiff ℝ r (fun t => traceResponseVec (F t) E (b t)) :=
  contDiff_trResp _ _ (contDiff_traceCompression F E hF hG) (contDiff_traceSource F E b hF hb hG)
    hH

theorem contDiff_reconstructed {r : ℕ} (F : ℝ → Matrix n m ℝ) (E : Matrix n k ℝ)
    (b : ℝ → m → ℝ) (hF : ContDiff ℝ r F) (hb : ContDiff ℝ r b)
    (hG : ∀ t, IsUnit ((F t)ᵀ * F t).det) (hH : ∀ t, IsUnit (traceOp (F t) E).det) :
    ContDiff ℝ r (fun t => reconstructed (F t) E (b t)) := by
  unfold reconstructed
  refine (contDiff_sourceResponse F b hF hb hG).sub (ContDiff.const_smul (3 : ℝ) ?_)
  exact contDiff_mulVec (contDiff_const.sub (contDiff_sourceProj F hF hG))
    (contDiff_mulVec contDiff_const (contDiff_traceResponseVec F E b hF hb hG hH))

/-! ### The theorem -/

/-- **`thm:supp-exact-time-hierarchy`** under the manuscript's hypotheses: `F(t)`, `b(t)` of
class `C^r` with full column rank and regular signed Gram at every time, and `v(t)` the physical
response.  Then `Π, w, C, ζ, χ, v` are `C^r`, `H(t)` is invertible, `E^*v = −χ`, the recursively
defined `χ_j` (`hierarchyVec`) satisfy `χ_j = χ^{(j)} = −E^*v^{(j)}` for `j ≤ r`, and for
`r ≥ 1`: `χ' = H⁻¹(ζ' + 3C'χ)` and `v' = w' + 3Π'Eχ − 3(I − Π)Eχ'`. -/
theorem exact_time_hierarchy {r : ℕ} (F : ℝ → Matrix n m ℝ) (b : ℝ → m → ℝ)
    (E : Matrix n k ℝ) (hE : Eᵀ * E = 1) (hF : ContDiff ℝ r F) (hb : ContDiff ℝ r b)
    (hrank : ∀ t, IsUnit ((F t)ᵀ * F t).det) (hgram : ∀ t, IsUnit (signedGram (F t) E).det)
    (v : ℝ → n → ℝ) (hv : ∀ t, IsResponse (F t) E (b t) (v t)) :
    let Pr := fun t => sourceProj (F t)
    let w := fun t => sourceResponse (F t) (b t)
    let C := fun t => traceCompression (F t) E
    let ζ := fun t => traceSource (F t) E (b t)
    let χ := fun t => traceResponseVec (F t) E (b t)
    -- regularity
    (ContDiff ℝ r Pr ∧ ContDiff ℝ r w ∧ ContDiff ℝ r C ∧ ContDiff ℝ r ζ ∧ ContDiff ℝ r χ ∧
      ContDiff ℝ r v) ∧
    -- invertibility of `H` and the reconstruction identities at every time
    (∀ t, IsUnit (traceOp (F t) E).det) ∧
    (∀ t, v t = reconstructed (F t) E (b t)) ∧ (∀ t, Eᵀ *ᵥ v t = -χ t) ∧
    -- the hierarchy
    (∀ t j, j ≤ r → hierarchyVec C ζ t j = iteratedDeriv j χ t ∧
      hierarchyVec C ζ t j = -(Eᵀ *ᵥ iteratedDeriv j v t)) ∧
    -- the first time source
    (1 ≤ r → ∀ t, deriv χ t = (traceOp (F t) E)⁻¹ *ᵥ (deriv ζ t + 3 • (deriv C t *ᵥ χ t)) ∧
      deriv v t = deriv w t + (3 : ℝ) • (deriv Pr t *ᵥ (E *ᵥ χ t))
        - (3 : ℝ) • ((1 - Pr t) *ᵥ (E *ᵥ deriv χ t))) := by
  intro Pr w C ζ χ
  have hH : ∀ t, IsUnit (traceOp (F t) E).det := fun t =>
    (signedGram_isUnit_iff (F t) E (hrank t)).mp (hgram t)
  have hresp : ∀ t, Eᵀ *ᵥ v t = -χ t ∧ v t = reconstructed (F t) E (b t) := fun t =>
    response_eq (F t) E (b t) (hrank t) hE (hH t) (v t) (hv t)
  have hvfun : v = fun t => reconstructed (F t) E (b t) := funext fun t => (hresp t).2
  have hPr : ContDiff ℝ r Pr := contDiff_sourceProj F hF hrank
  have hw : ContDiff ℝ r w := contDiff_sourceResponse F b hF hb hrank
  have hC : ContDiff ℝ r C := contDiff_traceCompression F E hF hrank
  have hζ : ContDiff ℝ r ζ := contDiff_traceSource F E b hF hb hrank
  have hχ : ContDiff ℝ r χ := contDiff_traceResponseVec F E b hF hb hrank hH
  have hvC : ContDiff ℝ r v := by rw [hvfun]; exact contDiff_reconstructed F E b hF hb hrank hH
  have hhier : ∀ t j, j ≤ r → hierarchyVec C ζ t j = iteratedDeriv j χ t := fun t j hj =>
    hierarchyVec_eq_iteratedDeriv C ζ hC hζ hH t j hj
  refine ⟨⟨hPr, hw, hC, hζ, hχ, hvC⟩, hH, fun t => (hresp t).2, fun t => (hresp t).1,
    fun t j hj => ⟨hhier t j hj, ?_⟩, fun hr t => ⟨?_, ?_⟩⟩
  · -- `χ_j = −E^* v^{(j)}`
    rw [hhier t j hj]
    have h1 := iteratedDeriv_lin (mulVecBil Eᵀ) (t := t) ((hvC.contDiffAt (x := t)).of_le (by exact_mod_cast hj))
    have hfun : (fun t => mulVecBil Eᵀ (v t)) = fun t => -χ t := funext fun t => (hresp t).1
    rw [hfun, iteratedDeriv_fun_neg] at h1
    change iteratedDeriv j χ t = -(mulVecBil Eᵀ (iteratedDeriv j v t))
    rw [← h1, neg_neg]
  · -- `χ' = H⁻¹(ζ' + 3C'χ)`
    have h := hhier t 1 hr
    rw [hierarchyVec_succ] at h
    simp only [iteratedDeriv_one, zero_add, Finset.range_one, Finset.sum_singleton,
      Nat.choose_self, one_smul, Nat.sub_self, hierarchyVec_zero] at h
    rw [← h]
    rfl
  · -- `v' = w' + 3Π'Eχ − 3(I − Π)Eχ'`
    have hr0 : (r : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
    have dPr : HasDerivAt Pr (deriv Pr t) t := ((hPr.differentiable hr0) t).hasDerivAt
    have dw : HasDerivAt w (deriv w t) t := ((hw.differentiable hr0) t).hasDerivAt
    have dχ : HasDerivAt χ (deriv χ t) t := ((hχ.differentiable hr0) t).hasDerivAt
    have d1 := (hasDerivAt_const t (1 : Matrix n n ℝ)).sub dPr
    have d2 : HasDerivAt (fun s => E *ᵥ χ s) (E *ᵥ deriv χ t) t :=
      hasDerivAt_lin (mulVecBil E) dχ
    have d3 := hasDerivAt_bilin mulVecBil d1 d2
    have d4 := dw.sub (d3.const_smul (3 : ℝ))
    have d5 := d4.congr_of_eventuallyEq (f₁ := v) (Filter.Eventually.of_forall fun s => by
      rw [hvfun]; rfl)
    rw [d5.deriv]
    simp only [Pi.sub_apply, mulVecBil, LinearMap.mk₂_apply, Matrix.neg_mulVec, smul_add,
      smul_neg, zero_sub]
    abel

/-! ### Non-vacuity -/

/-- Example data: `F(t) = (1, 1 + t²)ᵀ` (one source column in `ℝ²`), trace isometry
`E = e₀`. -/
def exF (t : ℝ) : Matrix (Fin 2) (Fin 1) ℝ :=
  Matrix.of ![![1], ![0]] + (1 + t ^ 2) • Matrix.of ![![0], ![1]]

def exE : Matrix (Fin 2) (Fin 1) ℝ := Matrix.of ![![1], ![0]]

theorem exE_isometry : exEᵀ * exE = 1 := by
  ext i j; fin_cases i; fin_cases j; simp [exE, Matrix.mul_apply, Fin.sum_univ_two]

theorem exF_rank (t : ℝ) : IsUnit ((exF t)ᵀ * exF t).det := by
  rw [isUnit_iff_ne_zero, Matrix.det_unique]
  simp [exF, Matrix.mul_apply, Fin.sum_univ_two]
  positivity

theorem exF_signedGram (t : ℝ) : IsUnit (signedGram (exF t) exE).det := by
  rw [isUnit_iff_ne_zero, Matrix.det_unique, signedGram_eq]
  simp [exF, exE, Matrix.mul_apply, Fin.sum_univ_two]
  nlinarith [sq_nonneg t, sq_nonneg (t ^ 2)]

theorem exF_contDiff : ContDiff ℝ 2 exF := by
  unfold exF
  exact contDiff_const.add ((contDiff_const.add (contDiff_id.pow 2)).smul contDiff_const)

/-- The hypotheses of `exact_time_hierarchy` are jointly satisfiable with a genuinely
time-dependent source: the hierarchy holds up to order two for `F(t) = (1, 1 + t²)ᵀ`,
`b = 1`, `E = e₀`. -/
example (t : ℝ) :
    hierarchyVec (fun t => traceCompression (exF t) exE) (fun t => traceSource (exF t) exE 1) t 2
      = -(exEᵀ *ᵥ iteratedDeriv 2 (fun t => reconstructed (exF t) exE 1) t) := by
  have h := exact_time_hierarchy (r := 2) exF (fun _ => 1) exE exE_isometry exF_contDiff
    contDiff_const exF_rank exF_signedGram (fun t => reconstructed (exF t) exE 1)
    (fun t => reconstructed_isResponse (exF t) exE 1 (exF_rank t) exE_isometry
      ((signedGram_isUnit_iff (exF t) exE (exF_rank t)).mp (exF_signedGram t)))
  exact (h.2.2.2.2.1 t 2 le_rfl).2

end objects

end RenewalGeometry.ExactTimeHierarchyMatrix
