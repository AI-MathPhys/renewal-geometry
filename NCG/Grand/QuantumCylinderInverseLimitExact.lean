/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.QuantumCylinderProjectiveLimitExact

/-!
# The inverse-limit cylinder probability of a compatible tower

Machinery for the last clause of `thm:SMST-quantum-projective-limit`: a projectively
compatible family of probability vectors `ν n` on finite cylinders `Ω n` (with cutoff maps
`π n : Ω (n+1) → Ω n`, `(π n)_* ν (n+1) = ν n`) has a unique inverse-limit cylinder probability,
i.e. a probability measure on `Π n, Ω n` with coordinate laws `ν n`, supported on the inverse-limit
relations `π n (ω (n+1)) = ω n`.

The construction is the Ionescu–Tulcea trajectory measure of the conditional kernels
`κ n x = ν (n+1)(· | π n · = x n)`, started from `ν 0`.

* `discrete v` is the measure `∑ ω, v ω • δ_ω` of a weight vector;
* `cond ν n a` is the conditional law of `ν (n+1)` on the fibre of `a`;
* `inverseLimit ν` is the trajectory measure; `inverseLimit_map_eval` (coordinate laws),
  `isProbabilityMeasure_inverseLimit`.
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology
open ProbabilityTheory.Kernel Preorder
open NCG.QuantumCylinderProjectiveLimit

namespace NCG
namespace QuantumCylinderInverseLimit

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-! ### Discrete measures of weight vectors -/

/-- The measure `∑ a, v a • δ_a` of a nonnegative weight vector on a finite type. -/
noncomputable def discrete {A : Type*} [Fintype A] [MeasurableSpace A] (v : A → ℝ) : Measure A :=
  ∑ a, ENNReal.ofReal (v a) • Measure.dirac a

theorem discrete_apply {A : Type*} [Fintype A] [MeasurableSpace A] (v : A → ℝ) {s : Set A}
    (hs : MeasurableSet s) :
    discrete v s = ∑ a, ENNReal.ofReal (v a) * s.indicator 1 a := by
  unfold discrete
  rw [Measure.finsetSum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' a hs, smul_eq_mul]

theorem discrete_singleton {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (v : A → ℝ) (a : A) :
    discrete v {a} = ENNReal.ofReal (v a) := by
  rw [discrete_apply v (measurableSet_singleton a), Finset.sum_eq_single a]
  · rw [Set.indicator_of_mem (Set.mem_singleton a), Pi.one_apply, mul_one]
  · intro b _ hb
    rw [Set.indicator_of_notMem (by simpa using hb), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem discrete_univ {A : Type*} [Fintype A] [MeasurableSpace A] (v : A → ℝ) :
    discrete v Set.univ = ∑ a, ENNReal.ofReal (v a) := by
  rw [discrete_apply v MeasurableSet.univ]
  simp

instance {A : Type*} [Fintype A] [MeasurableSpace A] (v : A → ℝ) :
    IsFiniteMeasure (discrete v) :=
  ⟨by rw [discrete_univ]; exact ENNReal.sum_lt_top.mpr fun a _ => ENNReal.ofReal_lt_top⟩

theorem isProbabilityMeasure_discrete {A : Type*} [Fintype A] [MeasurableSpace A] {v : A → ℝ}
    (hv : ∀ a, 0 ≤ v a) (h1 : ∑ a, v a = 1) : IsProbabilityMeasure (discrete v) :=
  ⟨by rw [discrete_univ, ← ENNReal.ofReal_sum_of_nonneg fun a _ => hv a, h1, ENNReal.ofReal_one]⟩

/-- The pushforward of a discrete measure is the discrete measure of the pushed weights. -/
theorem discrete_map {A B : Type*} [Fintype A] [Fintype B] [MeasurableSpace A] [MeasurableSpace B]
    [DiscreteMeasurableSpace A] [MeasurableSingletonClass B] [DecidableEq B] (v : A → ℝ)
    (hv : ∀ a, 0 ≤ v a) (f : A → B) : (discrete v).map f = discrete (push f v) := by
  refine Measure.ext_of_singleton fun b => ?_
  rw [Measure.map_apply (Measurable.of_discrete) (measurableSet_singleton b),
    discrete_singleton, discrete_apply v (MeasurableSet.of_discrete)]
  unfold push
  rw [ENNReal.ofReal_sum_of_nonneg fun a _ => hv a, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : f a = b <;> simp [h]

/-- The integral of a function against a discrete measure is a finite weighted sum. -/
theorem lintegral_discrete {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (v : A → ℝ) (g : A → ENNReal) :
    ∫⁻ a, g a ∂(discrete v) = ∑ a, ENNReal.ofReal (v a) * g a := by
  unfold discrete
  rw [lintegral_finsetSum_measure]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

/-! ### Conditional kernels of a compatible tower -/

variable {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)] [∀ n, DecidableEq (Ω n)]
  [∀ n, MeasurableSpace (Ω n)] [∀ n, DiscreteMeasurableSpace (Ω n)]

/-- A projectively compatible family of probability vectors on the cutoff tower. -/
structure CompatibleFamily (π : ∀ n, Ω (n + 1) → Ω n) where
  /-- the probability vectors -/
  ν : ∀ n, Ω n → ℝ
  nonneg : ∀ n ω, 0 ≤ ν n ω
  sum_eq_one : ∀ n, ∑ ω, ν n ω = 1
  compat : ∀ n, push (π n) (ν (n + 1)) = ν n

variable {π : ∀ n, Ω (n + 1) → Ω n} (F : CompatibleFamily π)

theorem CompatibleFamily.nonempty (F : CompatibleFamily π) (n : ℕ) : Nonempty (Ω n) := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := F.sum_eq_one n
  rw [Finset.univ_eq_empty, Finset.sum_empty] at this
  exact zero_ne_one this

theorem CompatibleFamily.card_pos (F : CompatibleFamily π) (n : ℕ) : 0 < Fintype.card (Ω n) :=
  @Fintype.card_pos _ _ (F.nonempty n)

/-- The conditional law of `ν (n+1)` on the fibre of `a`, with the uniform law as a default on
`ν n`-null points. -/
noncomputable def cond (n : ℕ) (a : Ω n) : Ω (n + 1) → ℝ :=
  if F.ν n a = 0 then fun _ => (Fintype.card (Ω (n + 1)) : ℝ)⁻¹
  else fun b => if π n b = a then F.ν (n + 1) b / F.ν n a else 0

theorem cond_nonneg (n : ℕ) (a : Ω n) (b : Ω (n + 1)) : 0 ≤ cond F n a b := by
  unfold cond
  split_ifs with h1
  · positivity
  · dsimp only
    split_ifs
    · exact div_nonneg (F.nonneg _ _) (F.nonneg _ _)
    · exact le_rfl

theorem sum_cond (n : ℕ) (a : Ω n) : ∑ b, cond F n a b = 1 := by
  unfold cond
  split_ifs with h
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast (F.card_pos (n + 1)).ne')
  · rw [← Finset.sum_filter, ← Finset.sum_div]
    have := congrFun (F.compat n) a
    unfold push at this
    rw [this]
    exact div_self h

theorem cond_eq_zero_of_ne (n : ℕ) {a : Ω n} (ha : F.ν n a ≠ 0) {b : Ω (n + 1)}
    (hb : π n b ≠ a) : cond F n a b = 0 := by
  unfold cond
  rw [if_neg ha, if_neg hb]

/-- `ν (n+1) b = ∑ a, ν n a * cond n a b`: the conditional laws reassemble `ν (n+1)`. -/
theorem sum_mul_cond (n : ℕ) (b : Ω (n + 1)) : ∑ a, F.ν n a * cond F n a b = F.ν (n + 1) b := by
  have hpush : F.ν n (π n b) = ∑ b' ∈ univ.filter (fun b' => π n b' = π n b), F.ν (n + 1) b' := by
    have := congrFun (F.compat n) (π n b)
    unfold push at this
    exact this.symm
  rw [Finset.sum_eq_single (π n b)]
  · unfold cond
    split_ifs with h
    · -- the fibre of `π n b` is `ν n`-null, hence `ν (n+1) b = 0`
      rw [h, zero_mul]
      have hb0 : F.ν (n + 1) b = 0 := by
        have hsum : ∑ b' ∈ univ.filter (fun b' => π n b' = π n b), F.ν (n + 1) b' = 0 := by
          rw [← hpush, h]
        have := (Finset.sum_eq_zero_iff_of_nonneg fun b' _ => F.nonneg (n + 1) b').mp hsum b
          (by simp)
        exact this
      rw [hb0]
    · dsimp only
      rw [if_pos rfl, mul_div_cancel₀ _ h]
  · intro a _ ha
    unfold cond
    split_ifs with h
    · rw [h, zero_mul]
    · dsimp only
      rw [if_neg (Ne.symm ha), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The discrete conditional law is a probability measure. -/
theorem isProbabilityMeasure_discrete_cond (n : ℕ) (a : Ω n) :
    IsProbabilityMeasure (discrete (cond F n a)) :=
  isProbabilityMeasure_discrete (cond_nonneg F n a) (sum_cond F n a)

/-- The conditional transition kernel `κ n x = ν (n+1)(· | fibre of x n)`. -/
noncomputable def condKernel (n : ℕ) : Kernel (Π i : Iic n, Ω i) (Ω (n + 1)) :=
  Kernel.ofFunOfCountable fun x => discrete (cond F n (x ⟨n, mem_Iic.mpr le_rfl⟩))

theorem condKernel_apply (n : ℕ) (x : Π i : Iic n, Ω i) :
    condKernel F n x = discrete (cond F n (x ⟨n, mem_Iic.mpr le_rfl⟩)) := rfl

instance (n : ℕ) : IsMarkovKernel (condKernel F n) :=
  ⟨fun _ => isProbabilityMeasure_discrete_cond F n _⟩

/-! ### The trajectory measure -/

/-- The initial point of the trajectory space determined by `a : Ω 0`. -/
def initialPoint (a : Ω 0) : Π i : Iic 0, Ω i :=
  fun i => cast (congrArg Ω (Nat.le_zero.mp (mem_Iic.mp i.2)).symm) a

theorem initialPoint_apply (a : Ω 0) : initialPoint (Ω := Ω) a ⟨0, mem_Iic.mpr le_rfl⟩ = a := rfl

/-- The initial law `ν 0` on the trajectory space up to time `0`. -/
noncomputable def initialLaw : Measure (Π i : Iic 0, Ω i) :=
  (discrete (F.ν 0)).map initialPoint

instance : IsProbabilityMeasure (initialLaw F) := by
  haveI := isProbabilityMeasure_discrete (F.nonneg 0) (F.sum_eq_one 0)
  exact Measure.isProbabilityMeasure_map (Measurable.of_discrete).aemeasurable

/-- **The inverse-limit cylinder probability**: the Ionescu–Tulcea trajectory measure of the
conditional kernels started from `ν 0`. -/
noncomputable def inverseLimit : Measure (Π n, Ω n) :=
  traj (condKernel F) 0 ∘ₘ initialLaw F

instance isProbabilityMeasure_inverseLimit : IsProbabilityMeasure (inverseLimit F) := by
  unfold inverseLimit
  infer_instance

/-- The law of the trajectory up to time `n`. -/
noncomputable def partialLaw (n : ℕ) : Measure (Π i : Iic n, Ω i) :=
  (inverseLimit F).map (frestrictLe n)

theorem partialLaw_eq (n : ℕ) :
    partialLaw F n = partialTraj (condKernel F) 0 n ∘ₘ initialLaw F := by
  unfold partialLaw inverseLimit
  rw [Measure.map_comp _ _ (measurable_frestrictLe n), traj_map_frestrictLe]

theorem partialLaw_succ (n : ℕ) :
    partialLaw F (n + 1) = partialTraj (condKernel F) n (n + 1) ∘ₘ partialLaw F n := by
  rw [partialLaw_eq, partialLaw_eq, partialTraj_succ_eq_comp (Nat.zero_le n), Measure.comp_assoc]

/-- The coordinate law at time `n`, read off the partial law. -/
theorem map_eval_eq (n : ℕ) :
    (inverseLimit F).map (fun ω => ω n)
      = (partialLaw F n).map (fun x => x ⟨n, mem_Iic.mpr le_rfl⟩) := by
  unfold partialLaw
  rw [Measure.map_map (measurable_pi_apply _) (measurable_frestrictLe n)]
  rfl

/-- Composing a kernel that depends only on the last coordinate. -/
theorem comp_partialLaw_succ (n : ℕ) :
    (condKernel F n) ∘ₘ partialLaw F n
      = Measure.bind ((partialLaw F n).map (fun x => x ⟨n, mem_Iic.mpr le_rfl⟩))
          (fun a => discrete (cond F n a)) := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _),
    Measure.bind_apply hs (Measurable.of_discrete).aemeasurable,
    lintegral_map (Measurable.of_discrete) (measurable_pi_apply _)]
  rfl

/-- The bind of a discrete law against the conditional laws is the next discrete law. -/
theorem bind_discrete_cond (n : ℕ) :
    Measure.bind (discrete (F.ν n)) (fun a => discrete (cond F n a)) = discrete (F.ν (n + 1)) := by
  refine Measure.ext_of_singleton fun b => ?_
  rw [Measure.bind_apply (measurableSet_singleton b) (Measurable.of_discrete).aemeasurable,
    lintegral_discrete, discrete_singleton]
  simp_rw [discrete_singleton]
  rw [← sum_mul_cond F n b, ENNReal.ofReal_sum_of_nonneg
    fun a _ => mul_nonneg (F.nonneg n a) (cond_nonneg F n a b)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ENNReal.ofReal_mul (F.nonneg n a)]

/-- **Coordinate laws**: the `n`-th coordinate of the inverse-limit probability has law `ν n`. -/
theorem inverseLimit_map_eval (n : ℕ) :
    (inverseLimit F).map (fun ω => ω n) = discrete (F.ν n) := by
  induction n with
  | zero =>
    rw [map_eval_eq, partialLaw_eq, partialTraj_self, Measure.id_comp]
    unfold initialLaw
    rw [Measure.map_map (measurable_pi_apply _) (Measurable.of_discrete)]
    have : (fun x : Π i : Iic 0, Ω i => x ⟨0, mem_Iic.mpr le_rfl⟩) ∘ initialPoint = id := by
      funext a
      rfl
    rw [this, Measure.map_id]
  | succ n ih =>
    rw [map_eval_eq, partialLaw_succ, Measure.map_comp _ _ (measurable_pi_apply _),
      map_partialTraj_succ_self, comp_partialLaw_succ, ← map_eval_eq, ih, bind_discrete_cond]

/-! ### Support on the inverse-limit relations -/

/-- The relation event `π n (y (n+1)) = y n` on the partial trajectory space. -/
def relSet (π : ∀ n, Ω (n + 1) → Ω n) (n : ℕ) : Set (Π i : Iic (n + 1), Ω i) :=
  {y | π n (y ⟨n + 1, mem_Iic.mpr le_rfl⟩) = y ⟨n, mem_Iic.mpr (Nat.le_succ n)⟩}

/-- Given a trajectory `z` up to time `n` with `ν n (z n) ≠ 0`, the next step lies in the fibre
of `z n` almost surely. -/
theorem partialTraj_relSet_compl (n : ℕ) (z : Π i : Iic n, Ω i)
    (hz : F.ν n (z ⟨n, mem_Iic.mpr le_rfl⟩) ≠ 0) :
    partialTraj (condKernel F) n (n + 1) z (relSet π n)ᶜ = 0 := by
  set a := z ⟨n, mem_Iic.mpr le_rfl⟩ with ha
  have hsub : (relSet π n)ᶜ ⊆
      {y | frestrictLe₂ (Nat.le_succ n) y ≠ z} ∪ {y | π n (y ⟨n + 1, mem_Iic.mpr le_rfl⟩) ≠ a} := by
    intro y hy
    by_cases h : frestrictLe₂ (Nat.le_succ n) y = z
    · right
      have : y ⟨n, mem_Iic.mpr (Nat.le_succ n)⟩ = a := by
        rw [ha, ← h]
        rfl
      simp only [relSet, Set.mem_compl_iff, Set.mem_setOf_eq] at hy
      rw [this] at hy
      exact hy
    · left
      exact h
  refine measure_mono_null hsub (measure_union_null ?_ ?_)
  · have h1 := congrFun
      (congrArg DFunLike.coe (partialTraj_succ_map_frestrictLe₂ (κ := condKernel F) n n)) z
    rw [Kernel.map_apply _ (measurable_frestrictLe₂ _), partialTraj_self, Kernel.id_apply] at h1
    change partialTraj (condKernel F) n (n + 1) z (frestrictLe₂ (Nat.le_succ n) ⁻¹' {y' | y' ≠ z})
      = 0
    rw [← Measure.map_apply (measurable_frestrictLe₂ _) (MeasurableSet.of_discrete), h1,
      Measure.dirac_apply' _ (MeasurableSet.of_discrete)]
    simp
  · have h2 := congrFun (congrArg DFunLike.coe (map_partialTraj_succ_self (κ := condKernel F) n)) z
    rw [Kernel.map_apply _ (measurable_pi_apply _)] at h2
    change partialTraj (condKernel F) n (n + 1) z
      ((fun y : Π i : Iic (n + 1), Ω i => y ⟨n + 1, mem_Iic.mpr le_rfl⟩) ⁻¹' {b | π n b ≠ a}) = 0
    rw [← Measure.map_apply (measurable_pi_apply _) (MeasurableSet.of_discrete), h2,
      condKernel_apply, discrete_apply _ (MeasurableSet.of_discrete)]
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hb : π n b = a
    · simp [hb]
    · rw [cond_eq_zero_of_ne F n hz hb, ENNReal.ofReal_zero, zero_mul]

/-- The `ν n`-null points are not visited at time `n`. -/
theorem ae_partialLaw_ne_zero (n : ℕ) :
    ∀ᵐ z ∂(partialLaw F n), F.ν n (z ⟨n, mem_Iic.mpr le_rfl⟩) ≠ 0 := by
  rw [ae_iff]
  have h : (partialLaw F n).map (fun x : Π i : Iic n, Ω i => x ⟨n, mem_Iic.mpr le_rfl⟩)
      {a | F.ν n a = 0} = 0 := by
    rw [← map_eval_eq, inverseLimit_map_eval, discrete_apply _ (MeasurableSet.of_discrete)]
    refine Finset.sum_eq_zero fun a _ => ?_
    by_cases ha : F.ν n a = 0
    · rw [ha, ENNReal.ofReal_zero, zero_mul]
    · rw [Set.indicator_of_notMem (by simpa using ha), mul_zero]
  rw [Measure.map_apply (measurable_pi_apply _) (MeasurableSet.of_discrete)] at h
  simpa using h

theorem partialLaw_relSet_compl (n : ℕ) : partialLaw F (n + 1) (relSet π n)ᶜ = 0 := by
  rw [partialLaw_succ, Measure.bind_apply (MeasurableSet.of_discrete) (Kernel.aemeasurable _)]
  refine (lintegral_congr_ae ((ae_partialLaw_ne_zero F n).mono fun z hz => ?_)).trans
    lintegral_zero
  exact partialTraj_relSet_compl F n z hz

/-- **Support**: the inverse-limit probability is carried by the inverse-limit relations. -/
theorem inverseLimit_ae_rel : ∀ᵐ ω ∂(inverseLimit F), ∀ n, π n (ω (n + 1)) = ω n := by
  rw [ae_all_iff]
  intro n
  rw [ae_iff]
  have h : inverseLimit F (frestrictLe (n + 1) ⁻¹' (relSet π n)ᶜ) = 0 := by
    rw [← Measure.map_apply (measurable_frestrictLe _) (MeasurableSet.of_discrete)]
    exact partialLaw_relSet_compl F n
  convert h using 2
  ext ω
  simp [relSet, frestrictLe_apply]

/-! ### Uniqueness -/

/-- The finite-dimensional family induced by the compatible marginals. -/
noncomputable def cylinderFamily (J : Finset ℕ) : Measure (Π j : J, Ω j) :=
  (discrete (F.ν (J.sup id))).map
    (fun x => fun j : J => πLe π (Finset.le_sup (f := id) j.2) x)

instance (J : Finset ℕ) : IsFiniteMeasure (cylinderFamily F J) := by
  unfold cylinderFamily
  infer_instance

/-- Along the inverse-limit relations, every coordinate is the composed cutoff of any later one. -/
theorem ae_πLe_eq (Q : Measure (Π n, Ω n)) (hrel : ∀ᵐ ω ∂Q, ∀ n, π n (ω (n + 1)) = ω n) :
    ∀ᵐ ω ∂Q, ∀ m n (h : m ≤ n), πLe π h (ω n) = ω m := by
  filter_upwards [hrel] with ω hω
  intro m n h
  induction n, h using Nat.le_induction with
  | base => rw [πLe_self]; rfl
  | succ n hmn ih => rw [πLe_succ π hmn, Function.comp_apply, hω n, ih]

/-- Any probability on `Π n, Ω n` with coordinate laws `ν n`, carried by the inverse-limit
relations, is a projective limit of the induced cylinder family. -/
theorem isProjectiveLimit_of (Q : Measure (Π n, Ω n))
    (hQ : ∀ n, Q.map (fun ω => ω n) = discrete (F.ν n))
    (hrel : ∀ᵐ ω ∂Q, ∀ n, π n (ω (n + 1)) = ω n) :
    IsProjectiveLimit Q (cylinderFamily F) := by
  intro J
  have heq : (J.restrict : (Π n, Ω n) → Π j : J, Ω j)
      =ᵐ[Q] fun ω => (fun j : J => πLe π (Finset.le_sup (f := id) j.2) (ω (J.sup id))) := by
    filter_upwards [ae_πLe_eq Q hrel] with ω hω
    funext j
    rw [hω]
    rfl
  rw [Measure.map_congr heq, cylinderFamily, ← hQ (J.sup id),
    Measure.map_map (Measurable.of_discrete) (measurable_pi_apply _)]
  rfl

/-- **Uniqueness of the inverse-limit cylinder probability.** -/
theorem inverseLimit_unique (Q : Measure (Π n, Ω n))
    (hQ : ∀ n, Q.map (fun ω => ω n) = discrete (F.ν n))
    (hrel : ∀ᵐ ω ∂Q, ∀ n, π n (ω (n + 1)) = ω n) :
    Q = inverseLimit F :=
  (isProjectiveLimit_of F Q hQ hrel).unique
    (isProjectiveLimit_of F (inverseLimit F) (inverseLimit_map_eval F) (inverseLimit_ae_rel F))

end QuantumCylinderInverseLimit
end NCG
