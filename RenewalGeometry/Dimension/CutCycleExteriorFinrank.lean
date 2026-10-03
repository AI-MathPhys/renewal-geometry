/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Dimension.CompleteGraphCutCycleDecompositionExact

/-!
# Cut–cycle decomposition of `C₁(K_N)` with kernel and dimensions derived
  (`thm:supp-cut-cycle`, emergent-spacetime manuscript)

Signed-edge realization of `C₁(K_N) = Λ²ℝᴺ`: the edge space `edgeSpace N` is the space of
antisymmetric `N × N` real matrices, the signed edge `[i → j]` is the wedge
`e_i ∧ e_j = e_i e_jᵀ - e_j e_iᵀ` (`wedge`), and the boundary is the column-sum map
`(∂A)_j = Σ_i A_{ij}` (`boundary`), so that `∂(e_i ∧ e_j) = e_j - e_i` exactly as in the paper
(`boundary_wedge_single`).  `W_N = meanZero N` is the mean-zero hyperplane,
`u₀ = N^{-1/2} 𝟙`, `cutSpace N = u₀ ∧ W_N` and `cycleSpace N = Λ²W_N` is the span of the
wedges of two mean-zero vectors.

Proved (for `N ≥ 1`):

* `boundary_wedge`: `∂(x ∧ y) = (Σx) y - (Σy) x`; `boundary_wedge_u0`: `∂(u₀ ∧ w) = √N w`
  for `w ∈ W_N` (`eq:supp-boundary-action`, first identity).
* `edgeSpace_inf_ker_boundary`: `Ker ∂ = Λ²W_N` (second identity), proved by the explicit
  expansion `A = ½ Σ_{i,j} A_{ij} (e_i - e_0) ∧ (e_j - e_0)` of a boundary-free current.
* `map_boundary_edgeSpace`: `Ran ∂ = W_N`.
* `cutSpace_isCompl`, `cutSpace_sup_cycleSpace`, `cutSpace_inf_cycleSpace`,
  `edgeInner_cut_cycle`: `C₁(K_N) = u₀ ∧ W_N ⊕ Λ²W_N`, an orthogonal direct sum for the edge
  (Frobenius) pairing (`eq:supp-cut-cycle`).
* `wedgeU0_injOn`, `finrank_cutSpace`: `w ↦ u₀ ∧ w` is injective on `W_N`, so
  `u₀ ∧ W_N ≅ W_N`.
* `finrank_meanZero`: `dim W_N = N - 1`; `finrank_edgeSpace`: `dim C₁(K_N) = C(N,2)` (via the
  coordinates `A ↦ (A_{ij})_{i<j}`); `finrank_range_boundary`: `dim Ran ∂ = N - 1`;
  `finrank_cycleSpace`: `dim Ker ∂ = C(N-1,2)` (rank–nullity, `eq:supp-cut-cycle-dim`);
  `finrank_cycleSpace_eq_exteriorPower`: `dim Λ²W_N = dim ⋀²(W_N)` (Mathlib exterior square).
* `cut_cycle_decomposition` collects everything.
-/

open Matrix Module

namespace RenewalGeometry
namespace CutCycleExterior

variable (N : ℕ)

/-- The coordinate-sum functional `x ↦ Σ_i x_i`. -/
def coordSum : (Fin N → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, x i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

/-- The mean-zero hyperplane `W_N = {x : Σ x_i = 0}`. -/
def meanZero : Submodule ℝ (Fin N → ℝ) := LinearMap.ker (coordSum N)

/-- The signed edge space `C₁(K_N) = Λ²ℝᴺ`, realized as antisymmetric matrices. -/
def edgeSpace : Submodule ℝ (Matrix (Fin N) (Fin N) ℝ) where
  carrier := {A | Aᵀ = -A}
  zero_mem' := by simp
  add_mem' {A B} hA hB := by
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.transpose_add, hA, hB, neg_add]
  smul_mem' c A hA := by
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.transpose_smul, hA, smul_neg]

/-- The boundary `(∂A)_j = Σ_i A_{ij}` (an edge `i → j` contributes `e_j - e_i`). -/
def boundary : Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] (Fin N → ℝ) where
  toFun A := fun j => ∑ i, A i j
  map_add' A B := by funext j; simp [Finset.sum_add_distrib]
  map_smul' c A := by funext j; simp [Finset.mul_sum]

variable {N}

/-- The wedge `x ∧ y = x yᵀ - y xᵀ`. -/
def wedge (x y : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ := vecMulVec x y - vecMulVec y x

/-- `y ↦ x ∧ y` as a linear map. -/
def wedgeLeft (x : Fin N → ℝ) : (Fin N → ℝ) →ₗ[ℝ] Matrix (Fin N) (Fin N) ℝ where
  toFun y := wedge x y
  map_add' y z := by ext i j; simp [wedge, vecMulVec_apply]; ring
  map_smul' c y := by ext i j; simp [wedge, vecMulVec_apply]; ring

/-- The normalized constant vector `u₀ = N^{-1/2} 𝟙`. -/
noncomputable def u0 : Fin N → ℝ := fun _ => (Real.sqrt N)⁻¹

variable (N)

/-- The cut space `u₀ ∧ W_N`. -/
noncomputable def cutSpace : Submodule ℝ (Matrix (Fin N) (Fin N) ℝ) :=
  (meanZero N).map (wedgeLeft u0)

/-- The cycle space `Λ²W_N`: the span of the wedges of two mean-zero vectors. -/
def cycleSpace : Submodule ℝ (Matrix (Fin N) (Fin N) ℝ) :=
  Submodule.span ℝ {A | ∃ w ∈ meanZero N, ∃ w' ∈ meanZero N, A = wedge w w'}

variable {N}

theorem mem_meanZero {x : Fin N → ℝ} : x ∈ meanZero N ↔ ∑ i, x i = 0 := Iff.rfl

theorem mem_edgeSpace {A : Matrix (Fin N) (Fin N) ℝ} : A ∈ edgeSpace N ↔ Aᵀ = -A := Iff.rfl

theorem boundary_apply (A : Matrix (Fin N) (Fin N) ℝ) (j : Fin N) :
    boundary N A j = ∑ i, A i j := rfl

theorem wedge_mem_edgeSpace (x y : Fin N → ℝ) : wedge x y ∈ edgeSpace N := by
  rw [mem_edgeSpace]
  ext i j
  simp [wedge, vecMulVec_apply]
  ring

/-- `∂(x ∧ y) = (Σx) y - (Σy) x`. -/
theorem boundary_wedge (x y : Fin N → ℝ) :
    boundary N (wedge x y) = (∑ i, x i) • y - (∑ i, y i) • x := by
  funext j
  simp only [boundary_apply, wedge, Matrix.sub_apply, vecMulVec_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib, ← Finset.sum_mul]

/-- Paper sign convention: `∂(e_i ∧ e_j) = e_j - e_i`. -/
theorem boundary_wedge_single (i j : Fin N) :
    boundary N (wedge (Pi.single i 1) (Pi.single j 1)) = Pi.single j 1 - Pi.single i 1 := by
  rw [boundary_wedge]
  simp

theorem sum_u0 (hN : 1 ≤ N) : ∑ i : Fin N, u0 i = Real.sqrt N := by
  simp only [u0, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (by positivity)
  field_simp
  linarith [hsq]

/-- `eq:supp-boundary-action`: `∂(u₀ ∧ w) = √N w` for `w ∈ W_N`. -/
theorem boundary_wedge_u0 (hN : 1 ≤ N) {w : Fin N → ℝ} (hw : w ∈ meanZero N) :
    boundary N (wedge u0 w) = Real.sqrt N • w := by
  rw [boundary_wedge, sum_u0 hN, mem_meanZero.mp hw, zero_smul, sub_zero]

/-- A boundary-free current also has zero row sums (by antisymmetry). -/
theorem rowSum_eq_zero {A : Matrix (Fin N) (Fin N) ℝ} (hA : A ∈ edgeSpace N)
    (hb : boundary N A = 0) (i : Fin N) : ∑ j, A i j = 0 := by
  have h : ∑ k, A k i = 0 := by
    have := congrFun hb i
    simpa [boundary_apply] using this
  have hA' := mem_edgeSpace.mp hA
  calc ∑ j, A i j = ∑ j, -A j i := Finset.sum_congr rfl fun j _ => by
          have := congrFun (congrFun hA' j) i
          simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
          linarith
    _ = 0 := by rw [Finset.sum_neg_distrib, h, neg_zero]

theorem sum_boundary_eq_zero {A : Matrix (Fin N) (Fin N) ℝ} (hA : A ∈ edgeSpace N) :
    ∑ j, boundary N A j = 0 := by
  have hA' := mem_edgeSpace.mp hA
  simp only [boundary_apply]
  have hswap : ∑ j, ∑ i, A i j = ∑ i, ∑ j, A i j := Finset.sum_comm
  have hneg : ∑ j, ∑ i, A i j = -∑ i, ∑ j, A i j := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := congrFun (congrFun hA' j) i
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
    linarith
  linarith

theorem wedge_meanZero_boundary {w w' : Fin N → ℝ} (hw : w ∈ meanZero N)
    (hw' : w' ∈ meanZero N) : boundary N (wedge w w') = 0 := by
  rw [boundary_wedge, mem_meanZero.mp hw, mem_meanZero.mp hw', zero_smul, zero_smul,
    sub_zero]

theorem cycleSpace_le : cycleSpace N ≤ edgeSpace N ⊓ LinearMap.ker (boundary N) := by
  rw [cycleSpace, Submodule.span_le]
  rintro A ⟨w, hw, w', hw', rfl⟩
  exact ⟨wedge_mem_edgeSpace w w', LinearMap.mem_ker.mpr (wedge_meanZero_boundary hw hw')⟩

/-- The reference-vertex differences `e_i - e_0`. -/
def refDiff (hN : 1 ≤ N) (i : Fin N) : Fin N → ℝ :=
  Pi.single i 1 - Pi.single ⟨0, hN⟩ 1

theorem refDiff_mem (hN : 1 ≤ N) (i : Fin N) : refDiff hN i ∈ meanZero N := by
  rw [mem_meanZero]
  simp [refDiff, Finset.sum_sub_distrib]

theorem sum_mul_refDiff (hN : 1 ≤ N) (f : Fin N → ℝ) (l : Fin N) :
    ∑ j, f j * refDiff hN j l
      = f l - ((Pi.single (⟨0, hN⟩ : Fin N) (1 : ℝ) : Fin N → ℝ) l) * ∑ j, f j := by
  simp only [refDiff, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  congr 1
  · simp [Pi.single_apply, eq_comm]
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

/-- `Ker ∂ = Λ²W_N` (`eq:supp-boundary-action`, second identity). -/
theorem edgeSpace_inf_ker_boundary (hN : 1 ≤ N) :
    edgeSpace N ⊓ LinearMap.ker (boundary N) = cycleSpace N := by
  refine le_antisymm ?_ cycleSpace_le
  rintro A ⟨hA, hb⟩
  have hb' : boundary N A = 0 := LinearMap.mem_ker.mp hb
  have hrow := rowSum_eq_zero hA hb'
  have hcol : ∀ j, ∑ i, A i j = 0 := fun j => congrFun hb' j
  have hA' := mem_edgeSpace.mp hA
  have hexp : A = ∑ i, ∑ j, (A i j / 2) • wedge (refDiff hN i) (refDiff hN j) := by
    ext k l
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, wedge, Matrix.sub_apply,
      vecMulVec_apply]
    have h1 : ∀ i, ∑ j, A i j / 2 * (refDiff hN i k * refDiff hN j l)
        = refDiff hN i k * (A i l / 2) := by
      intro i
      have := sum_mul_refDiff hN (fun j => A i j / 2) l
      have hs : ∑ j, A i j / 2 = 0 := by rw [← Finset.sum_div, hrow i, zero_div]
      rw [hs, mul_zero, sub_zero] at this
      rw [← this, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have h2 : ∀ i, ∑ j, A i j / 2 * (refDiff hN j k * refDiff hN i l)
        = refDiff hN i l * (A i k / 2) := by
      intro i
      have := sum_mul_refDiff hN (fun j => A i j / 2) k
      have hs : ∑ j, A i j / 2 = 0 := by rw [← Finset.sum_div, hrow i, zero_div]
      rw [hs, mul_zero, sub_zero] at this
      rw [← this, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hsplit : ∀ i, ∑ j, A i j / 2 * (refDiff hN i k * refDiff hN j l
        - refDiff hN j k * refDiff hN i l)
        = refDiff hN i k * (A i l / 2) - refDiff hN i l * (A i k / 2) := by
      intro i
      rw [← h1, ← h2, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_sub_distrib]
    have e1 := sum_mul_refDiff hN (fun i => A i l / 2) k
    have e2 := sum_mul_refDiff hN (fun i => A i k / 2) l
    have hs1 : ∑ i, A i l / 2 = 0 := by rw [← Finset.sum_div, hcol l, zero_div]
    have hs2 : ∑ i, A i k / 2 = 0 := by rw [← Finset.sum_div, hcol k, zero_div]
    rw [hs1, mul_zero, sub_zero] at e1
    rw [hs2, mul_zero, sub_zero] at e2
    have e1' : ∑ i, refDiff hN i k * (A i l / 2) = A k l / 2 := by
      rw [← e1]; exact Finset.sum_congr rfl fun i _ => by ring
    have e2' : ∑ i, refDiff hN i l * (A i k / 2) = A l k / 2 := by
      rw [← e2]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1', e2']
    have hlk : A l k = -A k l := by
      have := congrFun (congrFun hA' k) l
      simpa [Matrix.transpose_apply] using this
    rw [hlk]
    ring
  rw [hexp]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  exact Submodule.smul_mem _ _ (Submodule.subset_span
    ⟨refDiff hN i, refDiff_mem hN i, refDiff hN j, refDiff_mem hN j, rfl⟩)

theorem cycleSpace_le_edgeSpace : cycleSpace N ≤ edgeSpace N :=
  cycleSpace_le.trans inf_le_left

/-- `Ran ∂ = W_N`. -/
theorem map_boundary_edgeSpace (hN : 1 ≤ N) :
    (edgeSpace N).map (boundary N) = meanZero N := by
  apply le_antisymm
  · rintro _ ⟨A, hA, rfl⟩
    exact sum_boundary_eq_zero hA
  · intro w hw
    refine ⟨wedge (fun _ => (N : ℝ)⁻¹) w, wedge_mem_edgeSpace _ _, ?_⟩
    have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hN)
    change boundary N (wedge _ w) = w
    rw [boundary_wedge, mem_meanZero.mp hw, zero_smul, sub_zero]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hNne]

/-- `dim W_N = N - 1`. -/
theorem finrank_meanZero (hN : 1 ≤ N) : finrank ℝ (meanZero N) = N - 1 := by
  have hsurj : LinearMap.range (coordSum N) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro t
    refine ⟨Pi.single ⟨0, hN⟩ t, ?_⟩
    simp [coordSum]
  have h := (coordSum N).finrank_range_add_finrank_ker
  rw [hsurj, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h
  change finrank ℝ (LinearMap.ker (coordSum N)) = N - 1
  omega

/-- Strictly ordered index pairs `i < j` (the unoriented edges of `K_N`). -/
abbrev OrderedPair (N : ℕ) := {p : Fin N × Fin N // p.1 < p.2}

theorem card_orderedPair : Fintype.card (OrderedPair N) = N.choose 2 := by
  rw [Fintype.card_subtype]
  simpa using Fintype.card_product_filter_lt (α := Fin N)

/-- Upper-triangular coordinates of a signed edge current. -/
def edgeCoords : edgeSpace N →ₗ[ℝ] (OrderedPair N → ℝ) where
  toFun A := fun p => (A : Matrix (Fin N) (Fin N) ℝ) p.1.1 p.1.2
  map_add' A B := by funext p; simp
  map_smul' c A := by funext p; simp

theorem edgeCoords_bijective : Function.Bijective (edgeCoords (N := N)) := by
  constructor
  · intro A B hAB
    have hdiff : ∀ i j : Fin N, i < j →
        (A : Matrix (Fin N) (Fin N) ℝ) i j = (B : Matrix (Fin N) (Fin N) ℝ) i j :=
      fun i j hij => congrFun hAB ⟨(i, j), hij⟩
    have hA := mem_edgeSpace.mp A.2
    have hB := mem_edgeSpace.mp B.2
    apply Subtype.ext
    ext i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · exact hdiff i j hij
    · have h1 := congrFun (congrFun hA i) i
      have h2 := congrFun (congrFun hB i) i
      simp only [Matrix.transpose_apply, Matrix.neg_apply] at h1 h2
      linarith
    · have h1 := congrFun (congrFun hA i) j
      have h2 := congrFun (congrFun hB i) j
      simp only [Matrix.transpose_apply, Matrix.neg_apply] at h1 h2
      have := hdiff j i hij
      linarith
  · intro f
    let M : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun i j =>
      if h : i < j then f ⟨(i, j), h⟩ else if h' : j < i then -f ⟨(j, i), h'⟩ else 0
    have hM : M ∈ edgeSpace N := by
      rw [mem_edgeSpace]
      ext i j
      simp only [Matrix.transpose_apply, Matrix.neg_apply, M, Matrix.of_apply]
      rcases lt_trichotomy i j with hij | rfl | hij
      · simp [hij, not_lt.mpr hij.le]
      · simp
      · simp [hij, not_lt.mpr hij.le]
    refine ⟨⟨M, hM⟩, ?_⟩
    funext p
    simp [edgeCoords, M, Matrix.of_apply, p.2]

/-- `dim C₁(K_N) = C(N, 2)`. -/
theorem finrank_edgeSpace : finrank ℝ (edgeSpace N) = N.choose 2 := by
  rw [(LinearEquiv.ofBijective _ edgeCoords_bijective).finrank_eq, Module.finrank_fintype_fun_eq_card,
    card_orderedPair]

/-- `dim Ran ∂ = N - 1`. -/
theorem finrank_range_boundary (hN : 1 ≤ N) :
    finrank ℝ ((edgeSpace N).map (boundary N)) = N - 1 := by
  rw [map_boundary_edgeSpace hN, finrank_meanZero hN]

/-- `dim Ker ∂ = dim Λ²W_N = C(N-1, 2)` (rank–nullity). -/
theorem finrank_cycleSpace (hN : 1 ≤ N) : finrank ℝ (cycleSpace N) = (N - 1).choose 2 := by
  set f := (boundary N).domRestrict (edgeSpace N)
  have hrn := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, finrank_range_boundary hN, finrank_edgeSpace,
    LinearMap.ker_domRestrict] at hrn
  have hker : finrank ℝ ((LinearMap.ker (boundary N)).comap (edgeSpace N).subtype)
      = finrank ℝ (cycleSpace N) := by
    rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype,
      edgeSpace_inf_ker_boundary hN]
  rw [hker] at hrn
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hc : (M + 1).choose 2 = M + M.choose 2 := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
  rw [hc] at hrn
  simp only [Nat.add_sub_cancel] at hrn ⊢
  omega

/-- `Λ²W_N` has the dimension of the Mathlib exterior square `⋀²(W_N)`. -/
theorem finrank_cycleSpace_eq_exteriorPower (hN : 1 ≤ N) :
    finrank ℝ (cycleSpace N) = finrank ℝ (⋀[ℝ]^2 (meanZero N)) := by
  rw [finrank_cycleSpace hN, exteriorPower.finrank_eq, finrank_meanZero hN]

/-- `w ↦ u₀ ∧ w` is injective on `W_N`. -/
theorem wedgeU0_injOn (hN : 1 ≤ N) {w w' : Fin N → ℝ} (hw : w ∈ meanZero N)
    (hw' : w' ∈ meanZero N) (h : wedge u0 w = wedge u0 w') : w = w' := by
  have h1 := boundary_wedge_u0 hN hw
  have h2 := boundary_wedge_u0 hN hw'
  rw [h] at h1
  rw [h1] at h2
  have hs : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
  exact (smul_right_injective _ hs h2.symm).symm

/-- `dim (u₀ ∧ W_N) = N - 1` (`u₀ ∧ W_N ≅ W_N`). -/
theorem finrank_cutSpace (hN : 1 ≤ N) : finrank ℝ (cutSpace N) = N - 1 := by
  have hinj : Function.Injective ((wedgeLeft (u0 (N := N))).domRestrict (meanZero N)) := by
    intro a b hab
    exact Subtype.ext (wedgeU0_injOn hN a.2 b.2 hab)
  rw [cutSpace, ← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj,
    finrank_meanZero hN]

theorem cutSpace_le_edgeSpace : cutSpace N ≤ edgeSpace N := by
  rintro _ ⟨w, _, rfl⟩
  exact wedge_mem_edgeSpace _ _

theorem cutSpace_inf_cycleSpace (hN : 1 ≤ N) : cutSpace N ⊓ cycleSpace N = ⊥ := by
  rw [eq_bot_iff]
  rintro A ⟨⟨w, hw, rfl⟩, hc⟩
  have hb : boundary N (wedge u0 w) = 0 :=
    LinearMap.mem_ker.mp ((cycleSpace_le hc).2)
  rw [boundary_wedge_u0 hN hw] at hb
  have hs : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
  have hw0 : w = 0 := (smul_eq_zero.mp hb).resolve_left hs
  rw [Submodule.mem_bot]
  subst hw0
  ext i j
  simp [wedge]

theorem cutSpace_sup_cycleSpace (hN : 1 ≤ N) : cutSpace N ⊔ cycleSpace N = edgeSpace N := by
  apply le_antisymm (sup_le cutSpace_le_edgeSpace cycleSpace_le_edgeSpace)
  intro A hA
  have hs : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
  set w : Fin N → ℝ := (Real.sqrt N)⁻¹ • boundary N A with hwdef
  have hw : w ∈ meanZero N := by
    rw [mem_meanZero, hwdef]
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, sum_boundary_eq_zero hA, mul_zero]
  have hcut : wedge u0 w ∈ cutSpace N := ⟨w, hw, rfl⟩
  have hbd : boundary N (wedge u0 w) = boundary N A := by
    rw [boundary_wedge_u0 hN hw, hwdef, smul_smul, mul_inv_cancel₀ hs, one_smul]
  have hcyc : A - wedge u0 w ∈ cycleSpace N := by
    rw [← edgeSpace_inf_ker_boundary hN]
    refine Submodule.mem_inf.mpr ⟨Submodule.sub_mem _ hA (wedge_mem_edgeSpace _ _), ?_⟩
    rw [LinearMap.mem_ker, map_sub, hbd, sub_self]
  have : A = wedge u0 w + (A - wedge u0 w) := by abel
  rw [this]
  exact Submodule.add_mem_sup hcut hcyc

/-- `eq:supp-cut-cycle`: `C₁(K_N) = u₀ ∧ W_N ⊕ Λ²W_N` inside the matrix space. -/
theorem cutSpace_isCompl (hN : 1 ≤ N) :
    cutSpace N ⊓ cycleSpace N = ⊥ ∧ cutSpace N ⊔ cycleSpace N = edgeSpace N :=
  ⟨cutSpace_inf_cycleSpace hN, cutSpace_sup_cycleSpace hN⟩

/-- The two summands are orthogonal for the edge (Frobenius) pairing. -/
theorem edgeInner_cut_cycle (hN : 1 ≤ N) {A C : Matrix (Fin N) (Fin N) ℝ}
    (hA : A ∈ cutSpace N) (hC : C ∈ cycleSpace N) :
    CompleteGraphCutCycle.edgeInner A C = 0 := by
  obtain ⟨w, _, rfl⟩ := hA
  obtain ⟨hCe, hCb⟩ := cycleSpace_le hC
  have hrow : CompleteGraphCutCycle.boundary C = 0 := by
    funext i
    simpa [CompleteGraphCutCycle.boundary, Matrix.mulVec, dotProduct] using
      rowSum_eq_zero hCe (LinearMap.mem_ker.mp hCb) i
  exact CompleteGraphCutCycle.wedge_orthogonal_cycle hN w C (mem_edgeSpace.mp hCe) hrow

/-- **`thm:supp-cut-cycle`.**  For `N ≥ 1`: `C₁(K_N) = u₀ ∧ W_N ⊕ Λ²W_N` (orthogonal),
`∂(u₀ ∧ w) = √N w`, `Ker ∂ = Λ²W_N`, `Ran ∂ = W_N`, `u₀ ∧ ·` is injective on `W_N`, and
`dim Ran ∂ = N - 1`, `dim Ker ∂ = C(N-1, 2)`, with `dim C₁(K_N) = C(N,2)`. -/
theorem cut_cycle_decomposition (hN : 1 ≤ N) :
    (cutSpace N ⊓ cycleSpace N = ⊥ ∧ cutSpace N ⊔ cycleSpace N = edgeSpace N) ∧
    (∀ A ∈ cutSpace N, ∀ C ∈ cycleSpace N, CompleteGraphCutCycle.edgeInner A C = 0) ∧
    (∀ w ∈ meanZero N, boundary N (wedge u0 w) = Real.sqrt N • w) ∧
    edgeSpace N ⊓ LinearMap.ker (boundary N) = cycleSpace N ∧
    (edgeSpace N).map (boundary N) = meanZero N ∧
    (∀ w ∈ meanZero N, ∀ w' ∈ meanZero N, wedge u0 w = wedge u0 w' → w = w') ∧
    finrank ℝ ((edgeSpace N).map (boundary N)) = N - 1 ∧
    finrank ℝ (cycleSpace N) = (N - 1).choose 2 ∧
    finrank ℝ (cutSpace N) = N - 1 ∧
    finrank ℝ (edgeSpace N) = N.choose 2 :=
  ⟨cutSpace_isCompl hN, fun _ hA _ hC => edgeInner_cut_cycle hN hA hC,
    fun _ hw => boundary_wedge_u0 hN hw, edgeSpace_inf_ker_boundary hN,
    map_boundary_edgeSpace hN, fun _ hw _ hw' h => wedgeU0_injOn hN hw hw' h,
    finrank_range_boundary hN, finrank_cycleSpace hN, finrank_cutSpace hN, finrank_edgeSpace⟩

/-- Non-vacuity at `N = 4`: the cycle space is three-dimensional and nonzero. -/
example : finrank ℝ (cycleSpace 4) = 3 := by
  rw [finrank_cycleSpace (by norm_num)]; decide

end CutCycleExterior
end RenewalGeometry
