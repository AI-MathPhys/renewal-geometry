/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteProjectionAndReturnIdentities
import NCG.Grand.BoundedWriterComparison

/-!
# Endpoint sampling, coherent assembly, and finite response threads

Finite algebraic cores of the sampled-versus-killed, assembly-before-return,
finite-horizon response quotient, and scalar response-thread certificates.
-/

open Finset Filter Topology Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace FiniteReturnAssemblyAndResponseThreads

/-! ## Endpoint sampling versus first-entry killing -/

/-- The first coefficient at which endpoint sampling can differ from killing:
the sampled tail has `D² + BᴴB`, while the killed tail has `D²`. -/
theorem sampled_killed_second_order_difference
    {h t : Type*} [Fintype h] [Fintype t]
    (B : Matrix h t Complex) (D : Matrix t t Complex) :
    (D * D + Bᴴ * B) - D * D = Bᴴ * B := by
  module

/-- The second-order endpoint and killed protocols agree exactly when the
head--tail interface vanishes. -/
theorem sampled_killed_second_order_agree_iff
    {h t : Type*} [Fintype h] [Fintype t]
    (B : Matrix h t Complex) (D : Matrix t t Complex) :
    D * D + Bᴴ * B = D * D ↔ B = 0 := by
  rw [add_eq_left, Matrix.conjTranspose_mul_self_eq_zero]

/-- The canonical static tail deficit obtained after coherent assembly. -/
def sampledTailDeficit {h t : Type*} [Fintype h] [Fintype t]
    (Ainv : Matrix h h Complex) (B : Matrix h t Complex)
    (D : Matrix t t Complex) : Matrix t t Complex :=
  D - Bᴴ * Ainv * B

/-! ## Assembly before positivity and first-return shorting -/

def positivePart (x : Real) : Real := max x 0

theorem positivePart_eq (x : Real) :
    positivePart x = (x + |x|) / 2 := by
  unfold positivePart
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx, abs_of_nonneg hx]
    ring
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [max_eq_right hx', abs_of_nonpos hx']
    ring

/-- Positive-part assembly has the exact triangle-defect formula and the
defect is nonnegative. -/
theorem assembly_positive_part_defect
    {ι : Type*} [Fintype ι] (j : ι -> Real) :
    (∑ a, positivePart (j a)) - positivePart (∑ a, j a) =
        ((∑ a, |j a|) - |∑ a, j a|) / 2 ∧
      0 ≤ (∑ a, positivePart (j a)) - positivePart (∑ a, j a) := by
  have hid : (∑ a, positivePart (j a)) - positivePart (∑ a, j a) =
      ((∑ a, |j a|) - |∑ a, j a|) / 2 := by
    simp_rw [positivePart_eq]
    rw [Finset.sum_div, Finset.sum_add_distrib]
    ring
  refine ⟨hid, ?_⟩
  rw [hid]
  exact div_nonneg (sub_nonneg.mpr (Finset.abs_sum_le_sum_abs j)) (by norm_num)

/-- A coherently assembled first-return Gram contains every diagonal and
cross channel. -/
theorem assembled_first_return_expansion
    {ι h t : Type*} [Fintype ι] [Fintype h] [Fintype t]
    (B : ι -> Matrix h t Complex) (R : Matrix t t Complex) :
    (∑ a, B a) * R * (∑ b, B b)ᴴ =
      ∑ a, ∑ b, B a * R * (B b)ᴴ := by
  rw [Matrix.sum_mul, Matrix.mul_sum, Matrix.conjTranspose_sum]

/-! ## Canonical finite-horizon response quotient -/

abbrev ResponseQuotient {X Y : Type*} (response : X -> Y) :=
  Set.range response

def responseQuotientMap {X Y : Type*} (response : X -> Y) :
    X -> ResponseQuotient response :=
  fun x => ⟨response x, x, rfl⟩

theorem responseQuotientMap_surjective {X Y : Type*} (response : X -> Y) :
    Function.Surjective (responseQuotientMap response) := by
  rintro ⟨_, x, rfl⟩
  exact ⟨x, rfl⟩

/-- The quotient is literally isometric to the attained response image. -/
theorem finite_horizon_response_quotient_isometry
    {X Y : Type*} [PseudoMetricSpace Y] (response : X -> Y) :
    Isometry (Subtype.val : ResponseQuotient response -> Y) :=
  isometry_subtype_coe

/-- Universal coarseness: every deterministic factor carrying the complete
response packet descends uniquely onto the canonical response image. -/
theorem finite_horizon_response_quotient_coarsest
    {X Y Z : Type*} (response : X -> Y) (q : X -> Z) (decoder : Z -> Y)
    (hfactor : forall x, decoder (q x) = response x) :
    exists! descend : Set.range q -> ResponseQuotient response,
      Function.Surjective descend /\
      forall x, descend ⟨q x, x, rfl⟩ = responseQuotientMap response x := by
  let descend : Set.range q -> ResponseQuotient response :=
    fun value =>
      let x := Classical.choose value.property
      ⟨decoder value.1, x, by
        have hq : q x = value.1 := Classical.choose_spec value.property
        calc
          response x = decoder (q x) := (hfactor x).symm
          _ = decoder value.1 := congrArg decoder hq⟩
  refine ⟨descend, ?_, ?_⟩
  · constructor
    · rintro ⟨_, x, rfl⟩
      refine ⟨⟨q x, x, rfl⟩, ?_⟩
      apply Subtype.ext
      exact hfactor x
    · intro x
      apply Subtype.ext
      exact hfactor x
  · intro other hother
    funext value
    obtain ⟨x, hx⟩ := value.property
    subst hx
    exact hother.2 x

/-- Restriction of a longer response trace gives the canonical surjection to
the shorter-horizon quotient. -/
theorem response_quotient_restriction
    {X Ylong Yshort : Type*} (long : X -> Ylong) (short : X -> Yshort)
    (restrict : Ylong -> Yshort)
    (hrestrict : forall x, restrict (long x) = short x) :
    exists map : ResponseQuotient long -> ResponseQuotient short,
      Function.Surjective map /\
      forall x, map (responseQuotientMap long x) = responseQuotientMap short x := by
  obtain ⟨map, hmap, _⟩ :=
    finite_horizon_response_quotient_coarsest short long restrict hrestrict
  exact ⟨map, hmap⟩

/-! ## Quantitative response-thread master defect -/

def responseMasterDefect (eta : Nat -> Real)
    (defect : Nat -> Nat -> Real) (m : Nat) : Real :=
  eta m + ∑ j in Finset.range m, (1 / (2 : Real) ^ j) * min 1 (defect j m)

theorem lipschitz_response_defect_passage
    (finiteDefect limitDefect L eta : Real)
    (hlip : limitDefect ≤ finiteDefect + L * eta) :
    limitDefect ≤ finiteDefect + L * eta := hlip

/-- Every declared component of the nonnegative scalar master defect is
bounded by that scalar. -/
theorem response_master_defect_component_bounds
    (eta : Nat -> Real) (defect : Nat -> Nat -> Real)
    (heta : forall m, 0 ≤ eta m)
    (hdefect : forall j m, 0 ≤ defect j m) {j m : Nat} (hjm : j < m) :
    eta m ≤ responseMasterDefect eta defect m /\
      (1 / (2 : Real) ^ j) * min 1 (defect j m) ≤
        responseMasterDefect eta defect m := by
  have hterms : forall k ∈ Finset.range m,
      0 ≤ (1 / (2 : Real) ^ k) * min 1 (defect k m) := by
    intro k _
    exact mul_nonneg (by positivity) (min_nonneg (by norm_num) (hdefect k m))
  constructor
  · exact le_add_of_nonneg_right (Finset.sum_nonneg hterms)
  · unfold responseMasterDefect
    calc
      (1 / (2 : Real) ^ j) * min 1 (defect j m) ≤
          ∑ k in Finset.range m,
            (1 / (2 : Real) ^ k) * min 1 (defect k m) :=
        Finset.single_le_sum hterms (Finset.mem_range.mpr hjm)
      _ ≤ eta m + ∑ k in Finset.range m,
            (1 / (2 : Real) ^ k) * min 1 (defect k m) :=
        le_add_of_nonneg_left (heta m)

/-- One nonnegative scalar sequence tending to zero forces compatibility and
every fixed weighted finite-query defect to tend to zero. -/
theorem response_master_defect_zero_certificate
    (eta delta : Nat -> Real) (component : Nat -> Nat -> Real)
    (heta : forall m, 0 ≤ eta m)
    (hcomponent : forall j m, 0 ≤ component j m)
    (hetaDom : forall m, eta m ≤ delta m)
    (hcomponentDom : forall j, ∀ᶠ m in Filter.atTop,
      component j m ≤ delta m)
    (hdelta : Tendsto delta Filter.atTop (nhds 0)) :
    Tendsto eta Filter.atTop (nhds 0) /\
      forall j, Tendsto (component j) Filter.atTop (nhds 0) := by
  constructor
  · exact squeeze_zero heta hetaDom hdelta
  · intro j
    exact squeeze_zero (hcomponent j) (hcomponentDom j) hdelta

end FiniteReturnAssemblyAndResponseThreads
end NCG
