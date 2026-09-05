/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AFInductiveLimitState
import NCG.Grand.RenewalProfileFieldExact

/-!
# Countable renewal-product AF and quasilocal state

This is the concrete AF-tower instance required by
`thm:concrete-renewal-continuum-profile`.  The finite stages are cylinder
function C-star algebras on independent two-state cells.  Restriction
pullbacks are proved isometric, the renewal product states are proved
compatible and faithful at every finite screen, and the completed inductive
limit carries their unique quasilocal extension with contractive GNS
representation and exact on-site factorization.
-/

open scoped ComplexOrder

noncomputable section

namespace NCG.RenewalProductAF

abbrev Configuration (n : ℕ) := Fin n → Fin 2
abbrev Stage (n : ℕ) := Configuration n → ℂ

def restrictConfiguration {n m : ℕ} (h : n ≤ m)
    (x : Configuration m) : Configuration n :=
  fun i => x (Fin.castLE h i)

theorem restrictConfiguration_self (n : ℕ) (x : Configuration n) :
    restrictConfiguration le_rfl x = x := by
  funext i
  rfl

theorem restrictConfiguration_comp {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (x : Configuration k) :
    restrictConfiguration hij (restrictConfiguration hjk x) =
      restrictConfiguration (hij.trans hjk) x := by
  funext a
  rfl

def cylinderMap (n m : ℕ) (h : n ≤ m) : Stage n →⋆ₐ[ℂ] Stage m where
  toFun f := f ∘ restrictConfiguration h
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

theorem cylinderMap_self (n : ℕ) (f : Stage n) :
    cylinderMap n n le_rfl f = f := by
  funext x
  rfl

theorem cylinderMap_comp {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (f : Stage i) :
    cylinderMap j k hjk (cylinderMap i j hij f) =
      cylinderMap i k (hij.trans hjk) f := by
  funext x
  rfl

theorem restrictConfiguration_surjective {n m : ℕ} (h : n ≤ m) :
    Function.Surjective (restrictConfiguration h) := by
  intro y
  let x : Configuration m := fun j =>
    if hj : j.val < n then y ⟨j.val, hj⟩ else 0
  refine ⟨x, ?_⟩
  funext i
  simp [restrictConfiguration, x]

theorem cylinderMap_norm (n m : ℕ) (h : n ≤ m) (f : Stage n) :
    ‖cylinderMap n m h f‖ = ‖f‖ := by
  exact (restrictConfiguration_surjective h).pi_norm_comp f

def localExpectation (n : ℕ) (f : Stage n) : ℂ :=
  ∑ x : Configuration n, (RenewalField.w x : ℂ) * f x

theorem localExpectation_succ (n : ℕ) (f : Stage n) :
    localExpectation (n + 1) (cylinderMap n (n + 1) (Nat.le_succ n) f) =
      localExpectation n f := by
  classical
  let e := Fin.snocEquiv (fun _ : Fin (n + 1) => Fin 2)
  have hsum :
      (∑ p : Fin 2 × Configuration n,
        (RenewalField.w (e p) : ℂ) *
          cylinderMap n (n + 1) (Nat.le_succ n) f (e p)) =
      ∑ x : Configuration (n + 1),
        (RenewalField.w x : ℂ) *
          cylinderMap n (n + 1) (Nat.le_succ n) f x := by
    exact Fintype.sum_equiv e _ _ fun p => rfl
  rw [localExpectation, localExpectation, ← hsum]
  rw [Fintype.sum_prod_type]
  change (∑ b : Fin 2, ∑ y : Configuration n,
      (RenewalField.w (Fin.snoc y b) : ℂ) *
        cylinderMap n (n + 1) (Nat.le_succ n) f (Fin.snoc y b)) =
    ∑ x : Configuration n, (RenewalField.w x : ℂ) * f x
  have hweight (b : Fin 2) (y : Configuration n) :
      RenewalField.w (Fin.snoc y b) = RenewalField.w y * RenewalWalsh.piw b := by
    simp [RenewalField.w, Fin.prod_univ_castSucc]
  simp_rw [hweight]
  have hcyl (b : Fin 2) (y : Configuration n) :
      cylinderMap n (n + 1) (Nat.le_succ n) f (Fin.snoc y b) = f y := by
    change f (restrictConfiguration (Nat.le_succ n) (Fin.snoc y b)) = f y
    congr 1
    funext i
    have hi : Fin.castLE (Nat.le_succ n) i = i.castSucc := by
      apply Fin.ext
      rfl
    simp [restrictConfiguration, hi]
  simp_rw [hcyl]
  rw [show (∑ b : Fin 2, ∑ y : Configuration n,
      ((RenewalField.w y * RenewalWalsh.piw b : ℝ) : ℂ) * f y) =
      ∑ b : Fin 2, (RenewalWalsh.piw b : ℂ) *
        ∑ y : Configuration n, (RenewalField.w y : ℂ) * f y by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      push_cast
      ring]
  rw [← Finset.sum_mul]
  norm_num [RenewalWalsh.piw, Fin.sum_univ_two]

theorem localExpectation_compatible {n m : ℕ} (h : n ≤ m) (f : Stage n) :
    localExpectation m (cylinderMap n m h f) = localExpectation n f := by
  induction m, h using Nat.le_induction with
  | base => rw [cylinderMap_self]
  | succ m hnm ih =>
      rw [show cylinderMap n (m + 1) (hnm.trans (Nat.le_succ m)) f =
          cylinderMap m (m + 1) (Nat.le_succ m) (cylinderMap n m hnm f) by
        exact (cylinderMap_comp hnm (Nat.le_succ m) f).symm]
      exact (localExpectation_succ m _).trans ih

def localExpectationLinearMap (n : ℕ) : Stage n →ₗ[ℂ] ℂ where
  toFun := localExpectation n
  map_add' f g := by
    unfold localExpectation
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' z f := by
    unfold localExpectation
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    calc
      (∑ x, (RenewalField.w x : ℂ) * (z * f x)) =
          ∑ x, z * ((RenewalField.w x : ℂ) * f x) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            ring
      _ = z * ∑ x, (RenewalField.w x : ℂ) * f x := by
            rw [Finset.mul_sum]

theorem norm_localExpectation_le (n : ℕ) (f : Stage n) :
    ‖localExpectation n f‖ ≤ ‖f‖ := by
  calc
    ‖∑ x : Configuration n, (RenewalField.w x : ℂ) * f x‖
        ≤ ∑ x : Configuration n, ‖(RenewalField.w x : ℂ) * f x‖ :=
          norm_sum_le _ _
    _ = ∑ x : Configuration n, RenewalField.w x * ‖f x‖ := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (RenewalField.w_nonneg x)]
    _ ≤ ∑ x : Configuration n, RenewalField.w x * ‖f‖ := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm f x)
        (RenewalField.w_nonneg x)
    _ = ‖f‖ := by
      rw [← Finset.sum_mul, RenewalField.weight_total, one_mul]

def localExpectationCLM (n : ℕ) : Stage n →L[ℂ] ℂ :=
  (localExpectationLinearMap n).mkContinuous 1 fun f => by
    change ‖localExpectation n f‖ ≤ 1 * ‖f‖
    simpa using norm_localExpectation_le n f

theorem localExpectation_one (n : ℕ) : localExpectation n 1 = 1 := by
  unfold localExpectation
  simp only [Pi.one_apply, mul_one]
  exact_mod_cast RenewalField.weight_total (m := n)

theorem localExpectation_star_mul_self_nonneg (n : ℕ) (f : Stage n) :
    0 ≤ localExpectation n (star f * f) := by
  have hreal : localExpectation n (star f * f) =
      ((∑ x : Configuration n,
        RenewalField.w x * Complex.normSq (f x) : ℝ) : ℂ) := by
    rw [localExpectation]
    push_cast
    apply Finset.sum_congr rfl
    intro x hx
    simp [Complex.normSq_eq_conj_mul_self]
  rw [hreal]
  exact_mod_cast Finset.sum_nonneg fun x _ =>
    mul_nonneg (RenewalField.w_nonneg x) (Complex.normSq_nonneg _)

def localState (n : ℕ) : NCG.PreCStarState (Stage n) where
  toContinuousLinearMap := localExpectationCLM n
  map_one := localExpectation_one n
  map_star_mul_self_nonneg := localExpectation_star_mul_self_nonneg n
  norm_eq_one := by
    apply le_antisymm
    · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro f
      change ‖localExpectation n f‖ ≤ 1 * ‖f‖
      simpa using norm_localExpectation_le n f
    · calc
        1 = ‖localExpectationCLM n (1 : Stage n)‖ := by
          rw [show localExpectationCLM n (1 : Stage n) = 1 from localExpectation_one n]
          exact norm_one.symm
        _ ≤ ‖localExpectationCLM n‖ * ‖(1 : Stage n)‖ :=
          (localExpectationCLM n).le_opNorm 1
        _ = ‖localExpectationCLM n‖ := by simp

instance stageDirectedSystem :
    DirectedSystem Stage (fun i j h => cylinderMap i j h) where
  map_self := cylinderMap_self
  map_map k j i hij hjk f := cylinderMap_comp hij hjk f

instance stageIsometricSystem :
    PreCStarDirectLimit.IsometricSystem (fun i j h => cylinderMap i j h) where
  norm_map := cylinderMap_norm

def compatibleProductState :
    PreCStarDirectLimit.CompatibleState (fun i j h => cylinderMap i j h) where
  state := localState
  compatible i j hij f := by
    exact localExpectation_compatible hij f

theorem localState_faithful (n : ℕ) (f : Stage n)
    (hf : localState n (star f * f) = 0) : f = 0 := by
  have hsum : ∑ x : Configuration n,
      RenewalField.w x * Complex.normSq (f x) = 0 := by
    have hreal := localExpectation_star_mul_self_nonneg n f
    have heq : localExpectation n (star f * f) =
        ((∑ x : Configuration n,
          RenewalField.w x * Complex.normSq (f x) : ℝ) : ℂ) := by
      rw [localExpectation]
      push_cast
      apply Finset.sum_congr rfl
      intro x hx
      simp [Complex.normSq_eq_conj_mul_self]
    change localExpectation n (star f * f) = 0 at hf
    rw [heq] at hf
    exact_mod_cast hf
  funext x
  have hx := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ =>
      mul_nonneg (RenewalField.w_nonneg y) (Complex.normSq_nonneg _))).mp
    hsum x (Finset.mem_univ x)
  have hwpos : 0 < RenewalField.w x := by
    apply Finset.prod_pos
    intro i hi
    have hpiwpos : ∀ b : Fin 2, 0 < RenewalWalsh.piw b := by
      intro b
      fin_cases b <;> norm_num [RenewalWalsh.piw]
    exact hpiwpos (x i)
  have hz : Complex.normSq (f x) = 0 := (mul_eq_zero.mp hx).resolve_left hwpos.ne'
  exact Complex.normSq_eq_zero.mp hz

abbrev QuasilocalAlgebra :=
  PreCStarDirectLimit.Completion (fun i j h => cylinderMap i j h)

def quasilocalProductState : QuasilocalAlgebra →ₚ[ℂ] ℂ :=
  compatibleProductState.completionPositiveLinearMap

@[simp] theorem quasilocalProductState_of (n : ℕ) (f : Stage n) :
    quasilocalProductState
      (PreCStarDirectLimit.completionOf (fun i j h => cylinderMap i j h) n f) =
      localExpectation n f := by
  exact compatibleProductState.completionPositiveLinearMap_of n f

theorem quasilocalProductState_unique
    (φ : QuasilocalAlgebra →ₚ[ℂ] ℂ)
    (hφ : ∀ n (f : Stage n),
      φ (PreCStarDirectLimit.completionOf
        (fun i j h => cylinderMap i j h) n f) = localExpectation n f) :
    φ = quasilocalProductState := by
  exact compatibleProductState.completionPositiveLinearMap_unique φ hφ

theorem quasilocalGNSRepresentation_norm_le (a : QuasilocalAlgebra) :
    ‖compatibleProductState.completionGNSRepresentation a‖ ≤ ‖a‖ := by
  exact compatibleProductState.norm_completionGNSRepresentation_apply_le a

/-- Exact on-site locality of the countable product state, already visible at
every finite screen. -/
theorem localExpectation_twoSite_factorization {n : ℕ}
    (g h : Fin 2 → ℝ) (i j : Fin n) (hij : i ≠ j) :
    localExpectation n (fun x => ((g (x i) * h (x j) : ℝ) : ℂ)) =
      ((∑ b, RenewalWalsh.piw b * g b : ℝ) : ℂ) *
        ((∑ b, RenewalWalsh.piw b * h b : ℝ) : ℂ) := by
  have hr := RenewalField.expect_pair g h i j hij
  have hcast :
      localExpectation n (fun x => ((g (x i) * h (x j) : ℝ) : ℂ)) =
        ((RenewalField.expect (fun x => g (x i) * h (x j)) : ℝ) : ℂ) := by
    unfold localExpectation RenewalField.expect
    push_cast <;> rfl
  rw [hcast, hr]
  push_cast <;> rfl

theorem quasilocalProductState_twoSite_factorization {n : ℕ}
    (g h : Fin 2 → ℝ) (i j : Fin n) (hij : i ≠ j) :
    quasilocalProductState
      (PreCStarDirectLimit.completionOf
        (fun i j h => cylinderMap i j h) n
        (fun x => ((g (x i) * h (x j) : ℝ) : ℂ))) =
      ((∑ b, RenewalWalsh.piw b * g b : ℝ) : ℂ) *
        ((∑ b, RenewalWalsh.piw b * h b : ℝ) : ℂ) := by
  rw [quasilocalProductState_of]
  exact localExpectation_twoSite_factorization g h i j hij

/-- The concrete AF/quasilocal closure proposition for the independent
renewal regulator.  Naming the proposition lets larger certificates include
it without confusing the proposition with its proof term. -/
def ConcreteRenewalProductAFProfile : Prop :=
    (∀ n m (h : n ≤ m), Isometry (cylinderMap n m h))
      ∧ (∀ n, ∀ f : Stage n,
          quasilocalProductState
            (PreCStarDirectLimit.completionOf
              (fun i j h => cylinderMap i j h) n f) = localExpectation n f)
      ∧ (∀ φ : QuasilocalAlgebra →ₚ[ℂ] ℂ,
          (∀ n (f : Stage n),
            φ (PreCStarDirectLimit.completionOf
              (fun i j h => cylinderMap i j h) n f) = localExpectation n f) →
          φ = quasilocalProductState)
      ∧ (∀ n (f : Stage n), localState n (star f * f) = 0 → f = 0)
      ∧ (∀ a : QuasilocalAlgebra,
          ‖compatibleProductState.completionGNSRepresentation a‖ ≤ ‖a‖)

/-- Concrete AF/quasilocal closure for the independent renewal regulator. -/
theorem concreteRenewalProductAF_profile : ConcreteRenewalProductAFProfile := by
  refine ⟨fun n m h => ?_, fun n f => quasilocalProductState_of n f,
    quasilocalProductState_unique, localState_faithful,
    quasilocalGNSRepresentation_norm_le⟩
  exact (AddMonoidHomClass.isometry_iff_norm (cylinderMap n m h)).mpr
    (cylinderMap_norm n m h)

end NCG.RenewalProductAF

end
