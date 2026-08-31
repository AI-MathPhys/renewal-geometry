/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.HorizonTransport
import NCG.Grand.QuantumCylinderInverseLimitExact
import NCG.Grand.AFInductiveLimitState

/-!
# Renewal horizon infinite path and AF cylinder state

This file closes the measure/AF layer of `thm:renewal-horizon-transport`.
The consistent matrix-product word probabilities are assembled into an actual
Ionescu--Tulcea probability on infinite marked paths, with the prescribed
finite word laws and uniqueness.  The same weights define compatible positive
states on the finite commutative cylinder algebras.
-/

open Matrix MeasureTheory ProbabilityTheory Finset
open NCG.QuantumCylinderInverseLimit
open scoped ComplexOrder

noncomputable section

namespace NCG
namespace RenewalHorizonInfinitePathExact

abbrev Word (ι : Type*) (n : ℕ) := Fin n → ι

def forgetLast {ι : Type*} (n : ℕ) : Word ι (n + 1) → Word ι n :=
  Fin.init

theorem sum_words_snoc {ι R : Type*} [Fintype ι]
    [AddCommMonoid R] (n : ℕ) (F : Word ι (n + 1) → R) :
    ∑ z, F z = ∑ w : Word ι n, ∑ a : ι, F (Fin.snoc w a) := by
  let e := Fin.snocEquiv (fun _ : Fin (n + 1) => ι)
  have h := Fintype.sum_equiv e (fun p : ι × Word ι n => F (e p)) F
    (fun _ => rfl)
  calc
    ∑ z, F z = ∑ p : ι × Word ι n, F (e p) := h.symm
    _ = ∑ a : ι, ∑ w : Word ι n, F (Fin.snoc w a) := by
      rw [Fintype.sum_prod_type]
      rfl
    _ = ∑ w : Word ι n, ∑ a : ι, F (Fin.snoc w a) := Finset.sum_comm

theorem branchWordProd_entry_nonneg
    {ι d : Type*} [Fintype d] [DecidableEq d]
    (T : ι → Matrix d d ℝ) (hT : ∀ a i j, 0 ≤ T a i j)
    {n : ℕ} (w : Word ι n) (i j : d) :
    0 ≤ branchWordProd T w i j := by
  unfold branchWordProd
  have hlist : ∀ L : List (Matrix d d ℝ),
      (∀ A ∈ L, ∀ r c, 0 ≤ A r c) → ∀ r c, 0 ≤ L.prod r c := by
    intro L hL
    induction L with
    | nil =>
        intro r c
        simp only [List.prod_nil]
        rw [Matrix.one_apply]
        split <;> positivity
    | cons A L ih =>
        intro r c
        simp only [List.prod_cons, Matrix.mul_apply]
        exact Finset.sum_nonneg fun k _ =>
          mul_nonneg (hL A (by simp) r k)
            (ih (fun B hB => hL B (by simp [hB])) k c)
  exact hlist _ (fun A hA => by
    rw [List.mem_ofFn] at hA
    obtain ⟨k, rfl⟩ := hA
    exact hT (w k)) i j

theorem branchCylP_nonneg
    {ι d : Type*} [Fintype d] [DecidableEq d]
    (T : ι → Matrix d d ℝ) (α : d → ℝ)
    (hT : ∀ a i j, 0 ≤ T a i j) (hα : ∀ i, 0 ≤ α i)
    {n : ℕ} (w : Word ι n) : 0 ≤ branchCylP T α w := by
  unfold branchCylP
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (hα i)
  rw [Matrix.mulVec, dotProduct]
  exact Finset.sum_nonneg fun j _ => by
    simpa using branchWordProd_entry_nonneg T hT w i j

/-- The compatible family of renewal word probabilities. -/
noncomputable def renewalWordFamily
    {ι d : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
    [Fintype d] [DecidableEq d]
    (T : ι → Matrix d d ℝ) (M : Matrix d d ℝ) (α : d → ℝ)
    (hT : ∀ a i j, 0 ≤ T a i j) (hα0 : ∀ i, 0 ≤ α i)
    (hsum : ∑ a, T a = M)
    (hrow : M *ᵥ (fun _ => 1) = fun _ => 1)
    (hα1 : α ⬝ᵥ (fun _ => 1) = 1) :
    CompatibleFamily (fun n => forgetLast (ι := ι) n) where
  ν n := branchCylP T α
  nonneg n w := branchCylP_nonneg T α hT hα0 w
  sum_eq_one := (renewal_horizon_transport T M α hsum hrow hα1).2
  compat n := by
    funext w
    unfold QuantumCylinderProjectiveLimit.push
    rw [Finset.sum_filter]
    calc
      (∑ z : Word ι (n + 1),
          if forgetLast n z = w then branchCylP T α z else 0) =
        ∑ u : Word ι n, ∑ a : ι,
          if u = w then branchCylP T α (Fin.snoc u a) else 0 := by
            rw [sum_words_snoc]
            simp only [forgetLast, Fin.init_snoc]
      _ = ∑ a : ι, branchCylP T α (Fin.snoc w a) := by simp
      _ = branchCylP T α w :=
        (renewal_horizon_transport T M α hsum hrow hα1).1 n w

/-- The unique infinite marked renewal path law. -/
noncomputable def renewalPathLaw
    {ι d : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
    [Fintype d] [DecidableEq d]
    (T : ι → Matrix d d ℝ) (M : Matrix d d ℝ) (α : d → ℝ)
    (hT : ∀ a i j, 0 ≤ T a i j) (hα0 : ∀ i, 0 ≤ α i)
    (hsum : ∑ a, T a = M)
    (hrow : M *ᵥ (fun _ => 1) = fun _ => 1)
    (hα1 : α ⬝ᵥ (fun _ => 1) = 1) : Measure (∀ n, Word ι n) :=
  inverseLimit (renewalWordFamily T M α hT hα0 hsum hrow hα1)

instance renewalPathLaw_isProbability
    {ι d : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
    [Fintype d] [DecidableEq d]
    (T : ι → Matrix d d ℝ) (M : Matrix d d ℝ) (α : d → ℝ)
    (hT : ∀ a i j, 0 ≤ T a i j) (hα0 : ∀ i, 0 ≤ α i)
    (hsum : ∑ a, T a = M)
    (hrow : M *ᵥ (fun _ => 1) = fun _ => 1)
    (hα1 : α ⬝ᵥ (fun _ => 1) = 1) :
    IsProbabilityMeasure (renewalPathLaw T M α hT hα0 hsum hrow hα1) := by
  unfold renewalPathLaw
  infer_instance

theorem renewalPathLaw_coordinate
    {ι d : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
    [Fintype d] [DecidableEq d]
    (T : ι → Matrix d d ℝ) (M : Matrix d d ℝ) (α : d → ℝ)
    (hT : ∀ a i j, 0 ≤ T a i j) (hα0 : ∀ i, 0 ≤ α i)
    (hsum : ∑ a, T a = M)
    (hrow : M *ᵥ (fun _ => 1) = fun _ => 1)
    (hα1 : α ⬝ᵥ (fun _ => 1) = 1) (n : ℕ) :
    (renewalPathLaw T M α hT hα0 hsum hrow hα1).map (fun ω => ω n) =
      discrete (branchCylP T α : Word ι n → ℝ) :=
  inverseLimit_map_eval (renewalWordFamily T M α hT hα0 hsum hrow hα1) n

theorem renewalPathLaw_unique
    {ι d : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
    [Fintype d] [DecidableEq d]
    (T : ι → Matrix d d ℝ) (M : Matrix d d ℝ) (α : d → ℝ)
    (hT : ∀ a i j, 0 ≤ T a i j) (hα0 : ∀ i, 0 ≤ α i)
    (hsum : ∑ a, T a = M)
    (hrow : M *ᵥ (fun _ => 1) = fun _ => 1)
    (hα1 : α ⬝ᵥ (fun _ => 1) = 1)
    (Q : Measure (∀ n, Word ι n))
    (hQ : ∀ n, Q.map (fun ω => ω n) =
      discrete (branchCylP T α : Word ι n → ℝ))
    (hrel : ∀ᵐ ω ∂Q, ∀ n, forgetLast n (ω (n + 1)) = ω n) :
    Q = renewalPathLaw T M α hT hα0 hsum hrow hα1 :=
  inverseLimit_unique (renewalWordFamily T M α hT hα0 hsum hrow hα1) Q hQ hrel

/-! ## The commutative AF cylinder algebra -/

abbrev Stage (ι : Type*) (n : ℕ) := Word ι n → ℂ

def restrictWord {ι : Type*} {n m : ℕ} (h : n ≤ m) (w : Word ι m) : Word ι n :=
  fun i => w (Fin.castLE h i)

theorem restrictWord_self {ι : Type*} (n : ℕ) (w : Word ι n) :
    restrictWord le_rfl w = w := by
  funext i
  rfl

theorem restrictWord_comp {ι : Type*} {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (w : Word ι k) :
    restrictWord hij (restrictWord hjk w) = restrictWord (hij.trans hjk) w := by
  funext a
  rfl

def cylinderMap {ι : Type*} (n m : ℕ) (h : n ≤ m) :
    Stage ι n →⋆ₐ[ℂ] Stage ι m where
  toFun f := f ∘ restrictWord h
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

theorem cylinderMap_self {ι : Type*} (n : ℕ) (f : Stage ι n) :
    cylinderMap n n le_rfl f = f := by
  funext w
  rfl

theorem cylinderMap_comp {ι : Type*} {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (f : Stage ι i) :
    cylinderMap j k hjk (cylinderMap i j hij f) =
      cylinderMap i k (hij.trans hjk) f := by
  funext w
  rfl

theorem restrictWord_surjective {ι : Type*} [Nonempty ι] {n m : ℕ} (h : n ≤ m) :
    Function.Surjective (restrictWord (ι := ι) h) := by
  intro y
  let a₀ : ι := Classical.choice inferInstance
  let x : Word ι m := fun j =>
    if hj : j.val < n then y ⟨j.val, hj⟩ else a₀
  refine ⟨x, ?_⟩
  funext i
  simp [restrictWord, x]

theorem cylinderMap_norm {ι : Type*} [Fintype ι] [Nonempty ι]
    (n m : ℕ) (h : n ≤ m) (f : Stage ι n) :
    ‖cylinderMap n m h f‖ = ‖f‖ := by
  exact (restrictWord_surjective h).pi_norm_comp f

/-- The matrix-product expectation on the length-`n` cylinder algebra. -/
def localExpectation {ι d : Type*} [Fintype ι] [Fintype d]
    [DecidableEq d] (T : ι → Matrix d d ℝ) (α : d → ℝ)
    (n : ℕ) (f : Stage ι n) : ℂ :=
  ∑ w : Word ι n, (branchCylP T α w : ℂ) * f w

theorem localExpectation_succ
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (T : ι → Matrix d d ℝ) (M : Matrix d d ℝ) (α : d → ℝ)
    (hsum : ∑ a, T a = M)
    (hrow : M *ᵥ (fun _ => 1) = fun _ => 1)
    (hα1 : α ⬝ᵥ (fun _ => 1) = 1)
    (n : ℕ) (f : Stage ι n) :
    localExpectation T α (n + 1)
        (cylinderMap n (n + 1) (Nat.le_succ n) f) =
      localExpectation T α n f := by
  rw [localExpectation, localExpectation, sum_words_snoc]
  apply Finset.sum_congr rfl
  intro w hw
  have hcyl (a : ι) :
      cylinderMap n (n + 1) (Nat.le_succ n) f (Fin.snoc w a) = f w := by
    change f (restrictWord (Nat.le_succ n) (Fin.snoc w a)) = f w
    congr 1
    funext i
    unfold restrictWord
    rw [show Fin.castLE (Nat.le_succ n) i = i.castSucc by rfl]
    simp
  simp_rw [hcyl]
  rw [← Finset.sum_mul]
  congr 1
  exact_mod_cast (renewal_horizon_transport T M α hsum hrow hα1).1 n w

theorem localExpectation_compatible
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (T : ι → Matrix d d ℝ) (M : Matrix d d ℝ) (α : d → ℝ)
    (hsum : ∑ a, T a = M)
    (hrow : M *ᵥ (fun _ => 1) = fun _ => 1)
    (hα1 : α ⬝ᵥ (fun _ => 1) = 1)
    {n m : ℕ} (h : n ≤ m) (f : Stage ι n) :
    localExpectation T α m (cylinderMap n m h f) =
      localExpectation T α n f := by
  induction m, h using Nat.le_induction with
  | base => rw [cylinderMap_self]
  | succ m hnm ih =>
      rw [show cylinderMap n (m + 1) (hnm.trans (Nat.le_succ m)) f =
          cylinderMap m (m + 1) (Nat.le_succ m) (cylinderMap n m hnm f) by
        exact (cylinderMap_comp hnm (Nat.le_succ m) f).symm]
      exact (localExpectation_succ T M α hsum hrow hα1 m _).trans ih

def localExpectationLinearMap
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (T : ι → Matrix d d ℝ) (α : d → ℝ) (n : ℕ) :
    Stage ι n →ₗ[ℂ] ℂ where
  toFun := localExpectation T α n
  map_add' f g := by
    simp only [localExpectation, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' z f := by
    simp only [localExpectation, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w hw
    ring

theorem norm_localExpectation_le
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (T : ι → Matrix d d ℝ) (M : Matrix d d ℝ) (α : d → ℝ)
    (hT : ∀ a i j, 0 ≤ T a i j) (hα0 : ∀ i, 0 ≤ α i)
    (hsum : ∑ a, T a = M)
    (hrow : M *ᵥ (fun _ => 1) = fun _ => 1)
    (hα1 : α ⬝ᵥ (fun _ => 1) = 1)
    (n : ℕ) (f : Stage ι n) :
    ‖localExpectation T α n f‖ ≤ ‖f‖ := by
  calc
    ‖∑ w : Word ι n, (branchCylP T α w : ℂ) * f w‖
        ≤ ∑ w : Word ι n, ‖(branchCylP T α w : ℂ) * f w‖ :=
          norm_sum_le _ _
    _ = ∑ w : Word ι n, branchCylP T α w * ‖f w‖ := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (branchCylP_nonneg T α hT hα0 w)]
    _ ≤ ∑ w : Word ι n, branchCylP T α w * ‖f‖ := by
      apply Finset.sum_le_sum
      intro w hw
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm f w)
        (branchCylP_nonneg T α hT hα0 w)
    _ = ‖f‖ := by
      rw [← Finset.sum_mul,
        (renewal_horizon_transport T M α hsum hrow hα1).2 n, one_mul]

def localExpectationCLM
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (T : ι → Matrix d d ℝ) (M : Matrix d d ℝ) (α : d → ℝ)
    (hT : ∀ a i j, 0 ≤ T a i j) (hα0 : ∀ i, 0 ≤ α i)
    (hsum : ∑ a, T a = M)
    (hrow : M *ᵥ (fun _ => 1) = fun _ => 1)
    (hα1 : α ⬝ᵥ (fun _ => 1) = 1) (n : ℕ) :
    Stage ι n →L[ℂ] ℂ :=
  (localExpectationLinearMap T α n).mkContinuous 1 fun f => by
    change ‖localExpectation T α n f‖ ≤ 1 * ‖f‖
    simpa using norm_localExpectation_le T M α hT hα0 hsum hrow hα1 n f

theorem localExpectation_one
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (T : ι → Matrix d d ℝ) (M : Matrix d d ℝ) (α : d → ℝ)
    (hsum : ∑ a, T a = M)
    (hrow : M *ᵥ (fun _ => 1) = fun _ => 1)
    (hα1 : α ⬝ᵥ (fun _ => 1) = 1) (n : ℕ) :
    localExpectation T α n 1 = 1 := by
  rw [localExpectation]
  simp only [Pi.one_apply, mul_one]
  norm_cast
  exact (renewal_horizon_transport T M α hsum hrow hα1).2 n

theorem localExpectation_star_mul_self_nonneg
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (T : ι → Matrix d d ℝ) (α : d → ℝ)
    (hT : ∀ a i j, 0 ≤ T a i j) (hα0 : ∀ i, 0 ≤ α i)
    (n : ℕ) (f : Stage ι n) :
    0 ≤ localExpectation T α n (star f * f) := by
  have hreal : localExpectation T α n (star f * f) =
      ((∑ w : Word ι n,
        branchCylP T α w * Complex.normSq (f w) : ℝ) : ℂ) := by
    rw [localExpectation]
    push_cast
    apply Finset.sum_congr rfl
    intro w hw
    simp [Complex.normSq_eq_conj_mul_self]
  rw [hreal]
  exact_mod_cast Finset.sum_nonneg fun w _ =>
    mul_nonneg (branchCylP_nonneg T α hT hα0 w) (Complex.normSq_nonneg _)

def localState
    {ι d : Type*} [Fintype ι] [Nonempty ι] [Fintype d] [DecidableEq d]
    (T : ι → Matrix d d ℝ) (M : Matrix d d ℝ) (α : d → ℝ)
    (hT : ∀ a i j, 0 ≤ T a i j) (hα0 : ∀ i, 0 ≤ α i)
    (hsum : ∑ a, T a = M)
    (hrow : M *ᵥ (fun _ => 1) = fun _ => 1)
    (hα1 : α ⬝ᵥ (fun _ => 1) = 1) (n : ℕ) :
    NCG.PreCStarState (Stage ι n) where
  toContinuousLinearMap := localExpectationCLM T M α hT hα0 hsum hrow hα1 n
  map_one := localExpectation_one T M α hsum hrow hα1 n
  map_star_mul_self_nonneg := localExpectation_star_mul_self_nonneg T α hT hα0 n
  norm_eq_one := by
    apply le_antisymm
    · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro f
      change ‖localExpectation T α n f‖ ≤ 1 * ‖f‖
      simpa using norm_localExpectation_le T M α hT hα0 hsum hrow hα1 n f
    · calc
        1 = ‖localExpectationCLM T M α hT hα0 hsum hrow hα1 n
              (1 : Stage ι n)‖ := by
          rw [show localExpectationCLM T M α hT hα0 hsum hrow hα1 n
              (1 : Stage ι n) = 1 from
            localExpectation_one T M α hsum hrow hα1 n]
          exact norm_one.symm
        _ ≤ ‖localExpectationCLM T M α hT hα0 hsum hrow hα1 n‖ *
              ‖(1 : Stage ι n)‖ :=
          (localExpectationCLM T M α hT hα0 hsum hrow hα1 n).le_opNorm 1
        _ = ‖localExpectationCLM T M α hT hα0 hsum hrow hα1 n‖ := by simp

instance stageDirectedSystem (ι : Type*) :
    DirectedSystem (Stage ι) (fun i j h => cylinderMap i j h) where
  map_self := cylinderMap_self
  map_map _k _j _i hij hjk f := cylinderMap_comp hij hjk f

instance stageIsometricSystem (ι : Type*) [Fintype ι] [Nonempty ι] :
    PreCStarDirectLimit.IsometricSystem
      (fun i j h => cylinderMap (ι := ι) i j h) where
  norm_map := cylinderMap_norm

def compatibleRenewalState
    {ι d : Type*} [Fintype ι] [Nonempty ι] [Fintype d] [DecidableEq d]
    (T : ι → Matrix d d ℝ) (M : Matrix d d ℝ) (α : d → ℝ)
    (hT : ∀ a i j, 0 ≤ T a i j) (hα0 : ∀ i, 0 ≤ α i)
    (hsum : ∑ a, T a = M)
    (hrow : M *ᵥ (fun _ => 1) = fun _ => 1)
    (hα1 : α ⬝ᵥ (fun _ => 1) = 1) :
    PreCStarDirectLimit.CompatibleState
      (fun i j h => cylinderMap (ι := ι) i j h) where
  state := localState T M α hT hα0 hsum hrow hα1
  compatible _i _j hij f := localExpectation_compatible T M α hsum hrow hα1 hij f

abbrev QuasilocalAlgebra (ι : Type*) [Fintype ι] [Nonempty ι] :=
  PreCStarDirectLimit.Completion
    (fun i j h => cylinderMap (ι := ι) i j h)

def quasilocalRenewalState
    {ι d : Type*} [Fintype ι] [Nonempty ι] [Fintype d] [DecidableEq d]
    (T : ι → Matrix d d ℝ) (M : Matrix d d ℝ) (α : d → ℝ)
    (hT : ∀ a i j, 0 ≤ T a i j) (hα0 : ∀ i, 0 ≤ α i)
    (hsum : ∑ a, T a = M)
    (hrow : M *ᵥ (fun _ => 1) = fun _ => 1)
    (hα1 : α ⬝ᵥ (fun _ => 1) = 1) :
    QuasilocalAlgebra ι →ₚ[ℂ] ℂ :=
  (compatibleRenewalState T M α hT hα0 hsum hrow hα1).completionPositiveLinearMap

@[simp] theorem quasilocalRenewalState_of
    {ι d : Type*} [Fintype ι] [Nonempty ι] [Fintype d] [DecidableEq d]
    (T : ι → Matrix d d ℝ) (M : Matrix d d ℝ) (α : d → ℝ)
    (hT : ∀ a i j, 0 ≤ T a i j) (hα0 : ∀ i, 0 ≤ α i)
    (hsum : ∑ a, T a = M)
    (hrow : M *ᵥ (fun _ => 1) = fun _ => 1)
    (hα1 : α ⬝ᵥ (fun _ => 1) = 1)
    (n : ℕ) (f : Stage ι n) :
    quasilocalRenewalState T M α hT hα0 hsum hrow hα1
        (PreCStarDirectLimit.completionOf
          (fun i j h => cylinderMap (ι := ι) i j h) n f) =
      localExpectation T α n f := by
  exact NCG.PreCStarDirectLimit.CompatibleState.completionPositiveLinearMap_of
    (compatibleRenewalState T M α hT hα0 hsum hrow hα1) n f

theorem quasilocalRenewalState_unique
    {ι d : Type*} [Fintype ι] [Nonempty ι] [Fintype d] [DecidableEq d]
    (T : ι → Matrix d d ℝ) (M : Matrix d d ℝ) (α : d → ℝ)
    (hT : ∀ a i j, 0 ≤ T a i j) (hα0 : ∀ i, 0 ≤ α i)
    (hsum : ∑ a, T a = M)
    (hrow : M *ᵥ (fun _ => 1) = fun _ => 1)
    (hα1 : α ⬝ᵥ (fun _ => 1) = 1)
    (φ : QuasilocalAlgebra ι →ₚ[ℂ] ℂ)
    (hφ : ∀ n (f : Stage ι n),
      φ (PreCStarDirectLimit.completionOf
        (fun i j h => cylinderMap (ι := ι) i j h) n f) =
        localExpectation T α n f) :
    φ = quasilocalRenewalState T M α hT hα0 hsum hrow hα1 := by
  exact NCG.PreCStarDirectLimit.CompatibleState.completionPositiveLinearMap_unique
    (compatibleRenewalState T M α hT hα0 hsum hrow hα1) φ hφ

/-! ## Exact null-support quotient -/

/-- The real quadratic energy associated to a finite cylinder state. -/
def localEnergy {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (T : ι → Matrix d d ℝ) (α : d → ℝ) (n : ℕ) (f : Stage ι n) : ℝ :=
  ∑ w : Word ι n, branchCylP T α w * Complex.normSq (f w)

theorem localEnergy_eq_zero_iff
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (T : ι → Matrix d d ℝ) (α : d → ℝ)
    (hT : ∀ a i j, 0 ≤ T a i j) (hα0 : ∀ i, 0 ≤ α i)
    (n : ℕ) (f : Stage ι n) :
    localEnergy T α n f = 0 ↔
      ∀ w, branchCylP T α w ≠ 0 → f w = 0 := by
  constructor
  · intro hzero w hw
    have hterm :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun u _ =>
        mul_nonneg (branchCylP_nonneg T α hT hα0 u)
          (Complex.normSq_nonneg _))).mp hzero w (Finset.mem_univ w)
    have hnorm : Complex.normSq (f w) = 0 :=
      (mul_eq_zero.mp hterm).resolve_left hw
    exact Complex.normSq_eq_zero.mp hnorm
  · intro hsupp
    unfold localEnergy
    apply Finset.sum_eq_zero
    intro w hw
    by_cases hp : branchCylP T α w = 0
    · simp [hp]
    · simp [hsupp w hp]

/-- Vanishing of the state norm is exactly vanishing on every positive-weight
word.  Thus zero-probability cylinders, and only those cylinders, form the
finite-stage GNS null space. -/
theorem localState_null_iff
    {ι d : Type*} [Fintype ι] [Nonempty ι] [Fintype d] [DecidableEq d]
    (T : ι → Matrix d d ℝ) (M : Matrix d d ℝ) (α : d → ℝ)
    (hT : ∀ a i j, 0 ≤ T a i j) (hα0 : ∀ i, 0 ≤ α i)
    (hsum : ∑ a, T a = M)
    (hrow : M *ᵥ (fun _ => 1) = fun _ => 1)
    (hα1 : α ⬝ᵥ (fun _ => 1) = 1)
    (n : ℕ) (f : Stage ι n) :
    localState T M α hT hα0 hsum hrow hα1 n (star f * f) = 0 ↔
      ∀ w, branchCylP T α w ≠ 0 → f w = 0 := by
  have hstate :
      localState T M α hT hα0 hsum hrow hα1 n (star f * f) =
        ((localEnergy T α n f : ℝ) : ℂ) := by
    change localExpectation T α n (star f * f) = _
    rw [localExpectation]
    rw [localEnergy]
    push_cast
    apply Finset.sum_congr rfl
    intro w hw
    simp [Complex.normSq_eq_conj_mul_self]
  rw [hstate]
  norm_cast
  exact localEnergy_eq_zero_iff T α hT hα0 n f

/-- Two cylinder observables represent the same null-support quotient class
when they agree on every word having positive probability. -/
def NullEquivalent {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (T : ι → Matrix d d ℝ) (α : d → ℝ) (n : ℕ)
    (f g : Stage ι n) : Prop :=
  ∀ w, branchCylP T α w ≠ 0 → f w = g w

def nullSupportSetoid {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (T : ι → Matrix d d ℝ) (α : d → ℝ) (n : ℕ) : Setoid (Stage ι n) where
  r := NullEquivalent T α n
  iseqv := by
    constructor
    · intro f w hw
      rfl
    · intro f g hfg w hw
      exact (hfg w hw).symm
    · intro f g h hfg hgh w hw
      exact (hfg w hw).trans (hgh w hw)

abbrev NullSupportQuotient
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (T : ι → Matrix d d ℝ) (α : d → ℝ) (n : ℕ) :=
  Quotient (nullSupportSetoid T α n)

def nullSupportZero
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (T : ι → Matrix d d ℝ) (α : d → ℝ) (n : ℕ) :
    NullSupportQuotient T α n :=
  Quotient.mk _ (0 : Stage ι n)

/-- The state energy descends to the null-support quotient. -/
def quotientEnergy
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (T : ι → Matrix d d ℝ) (α : d → ℝ) (n : ℕ) :
    NullSupportQuotient T α n → ℝ :=
  Quotient.lift (localEnergy T α n) (by
    intro f g hfg
    unfold localEnergy
    apply Finset.sum_congr rfl
    intro w hw
    by_cases hp : branchCylP T α w = 0
    · simp [hp]
    · rw [hfg w hp])

/-- Faithfulness after quotienting null support: the descended state energy
vanishes only at the zero quotient class. -/
theorem quotientEnergy_faithful
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (T : ι → Matrix d d ℝ) (α : d → ℝ)
    (hT : ∀ a i j, 0 ≤ T a i j) (hα0 : ∀ i, 0 ≤ α i)
    (n : ℕ) (q : NullSupportQuotient T α n) :
    quotientEnergy T α n q = 0 ↔ q = nullSupportZero T α n := by
  induction q using Quotient.inductionOn with
  | _ f =>
      constructor
      · intro hf
        apply Quotient.sound
        intro w hw
        simpa using (localEnergy_eq_zero_iff T α hT hα0 n f).mp hf w hw
      · intro hf
        rw [hf]
        change localEnergy T α n (0 : Stage ι n) = 0
        simp [localEnergy]

/-! ## Fixed two-state predictor under horizon extension -/

/-- The two canonical phase laws, viewed as coordinate point masses. -/
def phaseBasis (i : Fin 2) : Fin 2 → ℝ :=
  fun j => if j = i then 1 else 0

/-- The full future response function of a phase state.  Its domain includes
every finite resolved continuation word, independently of an observation
horizon. -/
def phaseResponse (i : Fin 2) (n : ℕ) (w : Word (Fin 5) n) : ℝ :=
  branchCylP renBranch (phaseBasis i) w

/-- One-step response panel used to certify that the two phase responses are
genuinely distinct predictive directions. -/
def oneStepPhaseResponse (i : Fin 2) (a : Fin 5) : ℝ :=
  ∑ j : Fin 2, renBranch a i j

/-- The two response functions are linearly independent: the `hh` branch
reads the first phase and the `pp` branch reads the second.  This is the exact
rank-two minimality certificate for the fixed active predictor. -/
theorem two_phase_responses_minimal :
    ∀ c₀ c₁ : ℝ,
      (∀ a : Fin 5,
        c₀ * oneStepPhaseResponse 0 a +
          c₁ * oneStepPhaseResponse 1 a = 0) →
      c₀ = 0 ∧ c₁ = 0 := by
  intro c₀ c₁ h
  have hhh := h 0
  have hpp := h 2
  simp [oneStepPhaseResponse, renBranch, Fin.sum_univ_two] at hhh hpp
  constructor <;> linarith

/-- The rank witness above is the length-one restriction of the full
matrix-product phase response, not a separate surrogate panel. -/
theorem phaseResponse_oneStep (i : Fin 2) (a : Fin 5) :
    phaseResponse i 1 (fun _ => a) = oneStepPhaseResponse i a := by
  fin_cases i <;> fin_cases a <;>
    norm_num [phaseResponse, oneStepPhaseResponse, phaseBasis, branchCylP,
      branchWordProd, renBranch, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      List.ofFn_succ, List.ofFn_zero]

/-- Horizon extension does not relabel or compress either predictive phase. -/
def phaseHorizonMap {n m : ℕ} (_h : n ≤ m) : Fin 2 → Fin 2 := id

/-- Every writer already present at the old endpoint is transported by the
literal identity map. -/
def oldEndpointWriterHorizonMap {Writer : Type*} {n m : ℕ} (_h : n ≤ m) :
    Writer → Writer := id

@[simp] theorem phaseHorizonMap_apply {n m : ℕ} (h : n ≤ m) (i : Fin 2) :
    phaseHorizonMap h i = i := rfl

@[simp] theorem oldEndpointWriterHorizonMap_apply
    {Writer : Type*} {n m : ℕ} (h : n ≤ m) (x : Writer) :
    oldEndpointWriterHorizonMap h x = x := rfl

/-- Exact predictor part of horizon transport: both complete phase response
functions are unchanged, the phase-state map is the identity, and the same is
true for an arbitrary old endpoint writer type. -/
theorem two_state_predictor_strict_horizon_identity
    {Writer : Type*} {n m : ℕ} (h : n ≤ m) :
    (∀ i : Fin 2, phaseHorizonMap h i = i ∧
      ∀ k (w : Word (Fin 5) k),
        phaseResponse (phaseHorizonMap h i) k w = phaseResponse i k w) ∧
    (∀ x : Writer, oldEndpointWriterHorizonMap h x = x) := by
  constructor
  · intro i
    exact ⟨rfl, fun _ _ => rfl⟩
  · intro x
    rfl

end RenewalHorizonInfinitePathExact
end NCG
