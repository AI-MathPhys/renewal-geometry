/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallWeakProduct
import RenewalGeometry.Analysis.BallSobolevExp

/-!
# The linearised Coulomb operator with rough tangential coefficients is an isomorphism
  `H⁵_N,0(B) → H³_0(B)` (stage D1c of the ball rendering of Uhlenbeck's small-energy theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

Notation (all on the ball `B = B_r(c) ⊂ ℝ⁴`, real `N`-component fields):
* `lapS η = Σ_ν ∂_ν∂_ν η` (`H⁵ → H³`), `divS a = Σ_ν ∂_ν a_ν` (`H⁴ → H³`), `meanS F = ∫_B F`;
* `IsNeumannS η` — the weak Neumann condition (`∇η` weakly tangential with divergence `Δη`);
* `IsTangentialS a` — `a` weakly tangential with divergence `divS a`;
* `linOpS A η = (lapS η_k + Σ_l divS (A^{kl} η_l))_k` — the linearised Coulomb operator
  `η ↦ d^*(dη + [a, η])` written in a real basis (`A_ν^{kl}` = matrix of `-ad a_ν`), with
  coefficients `A_ν^{kl} ∈ H⁴(B)`.

Main results:
* `weak_linOpS` — the weak (Lax–Milgram) formulation of `linOpS`: for `η` Neumann, `A^{kl}`
  tangential and every mean-zero `ζ ∈ H¹(B)^N`,
  `a_D(η, ζ) + p(η, ζ) = -Σ_k ⟨(linOpS A η)_k, ζ_k⟩` (no boundary terms);
* `linOpS_injective` — uniqueness for `Σ ‖A‖_{L⁴} ≤ δ`;
* `exists_linOpS_eq` — **existence with `H⁵` regularity**: for every mean-zero `f ∈ H³(B)^N`
  there is a mean-zero Neumann `η ∈ H⁵(B)^N` with `linOpS A η = f` (Lax–Milgram
  `linearized_neumann_ball`, then the elliptic bootstrap `H¹ → H² → … → H⁵` with
  `neumann_Hk_weak`, the mixed product estimate `memHk_mul_gen` and the weak product rule).
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallAlg

open SobolevOpen BallReg SobAlg

set_option linter.unusedSectionVars false

section Ops

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)]

instance instFact3 : Fact (3 ≤ 3) := ⟨le_rfl⟩
instance instFact4 : Fact (3 ≤ 4) := ⟨by norm_num⟩
instance instFact5 : Fact (3 ≤ 5) := ⟨by norm_num⟩

/-- The integral over the ball. -/
def meanS {s : ℕ} [Fact (3 ≤ s)] (F : SobAlg c r s) : ℝ := ∫ x in euclBall c r, fn F x

/-- The Laplacian `H⁵(B) → H³(B)`. -/
def lapS (η : SobAlg c r 5) : SobAlg c r 3 := ∑ ν, derS ν (derS ν η)

/-- The divergence of a vector field `H⁴(B)⁴ → H³(B)`. -/
def divS (a : Fin 4 → SobAlg c r 4) : SobAlg c r 3 := ∑ ν, derS ν (a ν)

/-- **The weak Neumann condition** for `η ∈ H⁵(B)`. -/
def IsNeumannS (η : SobAlg c r 5) : Prop :=
  IsWeakTangential c r (fun ν => fn (derS ν η)) (fn (lapS η))

/-- **Weakly tangential vector fields** in `H⁴(B)⁴`. -/
def IsTangentialS (a : Fin 4 → SobAlg c r 4) : Prop :=
  IsWeakTangential c r (fun ν => fn (a ν)) (fn (divS a))

/-- **The linearised Coulomb operator** with coefficients `A_ν^{kl} ∈ H⁴(B)`. -/
def linOpS {N : ℕ} (A : Fin 4 → Fin N → Fin N → SobAlg c r 4) (η : Fin N → SobAlg c r 5) :
    Fin N → SobAlg c r 3 :=
  fun k => lapS (η k) + ∑ l, divS (fun ν => A ν k l * restrS (by norm_num) (η l))

/-- `H³(B)` elements are essentially bounded. -/
theorem exists_ae_bound_fn {s : ℕ} [Fact (3 ≤ s)] (F : SobAlg c r s) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂(volume.restrict (euclBall c r)), |fn F x| ≤ M := by
  obtain ⟨M, hM⟩ := ae_abs_le_of_memHk3 c r hr.out ((memHk_fn F).mono (Fact.out))
  exact ⟨max M 0, le_max_right _ _, hM.mono fun x hx => hx.trans (le_max_left _ _)⟩

theorem memLp_four_fn {s : ℕ} [Fact (3 ≤ s)] (F : SobAlg c r s) :
    MemLp (fn F) 4 (volume.restrict (euclBall c r)) := by
  have hfin := isFiniteMeasure_restrict_euclBall c hr.out.le
  obtain ⟨M, -, hM⟩ := exists_ae_bound_fn F
  exact MemLp.of_bound (memLp_fn F).aestronglyMeasurable M (hM.mono fun x hx => by
    rwa [Real.norm_eq_abs])

theorem fn_lapS (η : SobAlg c r 5) :
    fn (lapS η) =ᵐ[volume.restrict (euclBall c r)] fun x => ∑ ν, fn (derS ν (derS ν η)) x :=
  fn_sum _ _

theorem fn_divS (a : Fin 4 → SobAlg c r 4) :
    fn (divS a) =ᵐ[volume.restrict (euclBall c r)] fun x => ∑ ν, fn (derS ν (a ν)) x :=
  fn_sum _ _

end Ops

/-! ### From `H^s(B)` elements to `H¹(B)` elements -/

section ToH1

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)]

/-- The `H¹(B)` graph `(F, ∂_1 F, …, ∂_4 F)` of an element of `H⁵(B)`. -/
def toH1 (η : SobAlg c r 5) : H1Amb c r :=
  WithLp.toLp 2 fun k => match k with
    | none => (memLp_fn η).toLp (fn η)
    | some ν => (memLp_fn (derS ν η)).toLp (fn (derS ν η))

theorem toH1_none (η : SobAlg c r 5) : toH1 η none = (memLp_fn η).toLp (fn η) := rfl

theorem toH1_some (η : SobAlg c r 5) (ν : Fin 4) :
    toH1 η (some ν) = (memLp_fn (derS ν η)).toLp (fn (derS ν η)) := rfl

theorem toH1_mem (η : SobAlg c r 5) : toH1 η ∈ H1B c r := by
  have hm : MemHk (euclBall c r) 1 (((memLp_fn η).toLp (fn η) : L2B c r) : (Fin 4 → ℝ) → ℝ) :=
    ((memHk_fn η).mono (by norm_num)).congr_ae (memLp_fn η).coeFn_toLp.symm
  obtain ⟨Fh, hFh, h0⟩ := exists_H1B_of_memHk c r hm
  convert hFh using 1
  refine PiLp.ext fun k => ?_
  cases k with
  | none => exact h0.symm
  | some ν =>
    have h1 := hasWeakPartialR_of_H1B c r hFh ν
    rw [h0] at h1
    have h2 : HasWeakPartialR (euclBall c r) ν
        ((((memLp_fn η).toLp (fn η) : L2B c r)) : (Fin 4 → ℝ) → ℝ)
        (((memLp_fn (derS ν η)).toLp (fn (derS ν η)) : L2B c r) : (Fin 4 → ℝ) → ℝ) :=
      (weak_derS ν η).congr_ae c r (memLp_fn η).coeFn_toLp.symm
        (memLp_fn (derS ν η)).coeFn_toLp.symm
    exact weakR_unique c r ν h2 h1

theorem meanCLM_toH1 (η : SobAlg c r 5) : meanCLM c r (toH1 η) = meanS η := by
  rw [meanCLM_apply, inner_oneB, toH1_none, meanS]
  exact integral_congr_ae (memLp_fn η).coeFn_toLp

theorem toH1_none_ae (η : SobAlg c r 5) :
    ((toH1 η none : L2B c r) : (Fin 4 → ℝ) → ℝ) =ᵐ[volume.restrict (euclBall c r)] fn η :=
  (memLp_fn η).coeFn_toLp

theorem toH1_some_ae (η : SobAlg c r 5) (ν : Fin 4) :
    ((toH1 η (some ν) : L2B c r) : (Fin 4 → ℝ) → ℝ) =ᵐ[volume.restrict (euclBall c r)]
      fn (derS ν η) :=
  (memLp_fn (derS ν η)).coeFn_toLp

end ToH1

/-! ### The weak formulation of `linOpS` -/

section WeakForm

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)]

/-- Derivatives commute with restriction (a.e. equality of the function components). -/
theorem fn_derS_restrS (ν : Fin 4) (η : SobAlg c r 5) :
    fn (derS ν (restrS (s := 5) (s' := 4) (by norm_num) η)) =ᵐ[volume.restrict (euclBall c r)]
      fn (derS ν η) := by
  have h1 := weak_derS ν (restrS (s := 5) (s' := 4) (by norm_num) η)
  rw [fn_restrS] at h1
  have := weakR_ae_eq (isOpen_euclBall c r) h1 (weak_derS ν η) (memLp_fn _) (memLp_fn _)
  rw [EventuallyEq, ae_restrict_iff' (measurableSet_euclBall c r)]
  exact this

/-- The divergence of `A η` (Leibniz rule). -/
theorem fn_divS_mul (A : Fin 4 → SobAlg c r 4) (η : SobAlg c r 5) :
    fn (divS (fun ν => A ν * restrS (by norm_num) η)) =ᵐ[volume.restrict (euclBall c r)]
      fun x => fn (divS A) x * fn η x + ∑ ν, fn (A ν) x * fn (derS ν η) x := by
  have h1 := fn_divS (fun ν => A ν * restrS (s := 5) (s' := 4) (by norm_num) η)
  have h2 := fn_divS A
  have h3 : ∀ᵐ x ∂(volume.restrict (euclBall c r)), ∀ ν,
      fn (derS ν (A ν * restrS (s := 5) (s' := 4) (by norm_num) η)) x =
        fn (derS ν (A ν)) x * fn η x + fn (A ν) x * fn (derS ν η) x := by
    rw [ae_all_iff]
    intro ν
    rw [derS_mul ν (A ν) (restrS (s := 5) (s' := 4) (by norm_num) η)]
    filter_upwards [fn_add (derS ν (A ν) * restrS (Nat.le_succ 3)
        (restrS (s := 5) (s' := 4) (by norm_num) η))
        (restrS (Nat.le_succ 3) (A ν) * derS ν (restrS (s := 5) (s' := 4) (by norm_num) η)),
      fn_mul (derS ν (A ν)) (restrS (Nat.le_succ 3) (restrS (s := 5) (s' := 4) (by norm_num) η)),
      fn_mul (restrS (Nat.le_succ 3) (A ν)) (derS ν (restrS (s := 5) (s' := 4) (by norm_num) η)),
      fn_derS_restrS ν η]
      with x e1 e2 e3 e4
    rw [e1, e2, e3, fn_restrS, fn_restrS, fn_restrS, e4]
  filter_upwards [h1, h2, h3] with x e1 e2 e3
  rw [e1, e2, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ν _ => e3 ν

theorem fn_linOpS {N : ℕ} (A : Fin 4 → Fin N → Fin N → SobAlg c r 4) (η : Fin N → SobAlg c r 5)
    (k : Fin N) :
    fn (linOpS A η k) =ᵐ[volume.restrict (euclBall c r)] fun x => fn (lapS (η k)) x +
      ∑ l, (fn (divS (fun ν => A ν k l)) x * fn (η l) x +
        ∑ ν, fn (A ν k l) x * fn (derS ν (η l)) x) := by
  have h1 := fn_add (lapS (η k)) (∑ l, divS (fun ν => A ν k l * restrS (by norm_num) (η l)))
  have h2 := fn_sum Finset.univ (fun l => divS (fun ν => A ν k l * restrS (s := 5) (s' := 4)
    (by norm_num) (η l)))
  have h3 : ∀ᵐ x ∂(volume.restrict (euclBall c r)), ∀ l,
      fn (divS (fun ν => A ν k l * restrS (s := 5) (s' := 4) (by norm_num) (η l))) x =
        fn (divS (fun ν => A ν k l)) x * fn (η l) x +
          ∑ ν, fn (A ν k l) x * fn (derS ν (η l)) x := by
    rw [ae_all_iff]; exact fun l => fn_divS_mul (fun ν => A ν k l) (η l)
  filter_upwards [h1, h2, h3] with x e1 e2 e3
  show fn (lapS (η k) + ∑ l, divS (fun ν => A ν k l * restrS (by norm_num) (η l))) x = _
  rw [e1, e2]
  congr 1
  exact Finset.sum_congr rfl fun l _ => e3 l

/-- A common essential bound for a finite family of `H³(B)` elements. -/
theorem exists_common_bound {ι : Type*} [Fintype ι] {s : ℕ} [Fact (3 ≤ s)]
    (F : ι → SobAlg c r s) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i, ∀ᵐ x ∂(volume.restrict (euclBall c r)), |fn (F i) x| ≤ M := by
  choose M hM0 hM using fun i => exists_ae_bound_fn (F i)
  refine ⟨∑ i, M i, Finset.sum_nonneg fun i _ => hM0 i, fun i => (hM i).mono fun x hx =>
    hx.trans (Finset.single_le_sum (f := M) (fun j _ => hM0 j) (Finset.mem_univ i))⟩

/-- **The weak formulation of the linearised operator** (one component): for `η_l` Neumann,
`A^{kl}` tangential and every `y ∈ H¹(B)`,
`Σ_ν ∫ ∂_νη_k y_ν + Σ_l Σ_ν ∫ A_ν^{kl} η_l y_ν = -∫ (linOpS A η)_k y₀`. -/
theorem weak_linOpS {N : ℕ} {A : Fin 4 → Fin N → Fin N → SobAlg c r 4}
    (htan : ∀ k l, IsTangentialS (fun ν => A ν k l)) {η : Fin N → SobAlg c r 5}
    (hN : ∀ k, IsNeumannS (η k)) (k : Fin N) {y : H1Amb c r} (hy : y ∈ H1B c r) :
    (∑ ν, ∫ x in euclBall c r, fn (derS ν (η k)) x * (y (some ν) : (Fin 4 → ℝ) → ℝ) x) +
      ∑ l, ∑ ν, ∫ x in euclBall c r, fn (A ν k l) x * fn (η l) x *
        (y (some ν) : (Fin 4 → ℝ) → ℝ) x =
      -∫ x in euclBall c r, fn (linOpS A η k) x * (y none : (Fin 4 → ℝ) → ℝ) x := by
  set μB := volume.restrict (euclBall c r)
  -- bounds
  obtain ⟨M1, hM10, hM1⟩ := exists_common_bound (fun p : Fin 4 => derS p (η k))
  obtain ⟨M2, hM20, hM2⟩ := exists_common_bound (fun _ : Unit => lapS (η k))
  obtain ⟨M3, hM30, hM3⟩ := exists_common_bound (fun p : Fin 4 × Fin N => A p.1 k p.2)
  obtain ⟨M4, hM40, hM4⟩ := exists_common_bound (fun l : Fin N => divS (fun ν => A ν k l))
  -- the Neumann part, with the constant test field `1`
  have hNk := (hN k).integral_H1B c r (M := max M1 M2) (le_max_of_le_left hM10)
    (fun ν => (memLp_fn _).aestronglyMeasurable) (memLp_fn _).aestronglyMeasurable
    (fun ν => (hM1 ν).mono fun x hx => hx.trans (le_max_left _ _))
    ((hM2 ()).mono fun x hx => hx.trans (le_max_right _ _)) (oneH_mem c r) y hy
  have hone : ((oneH c r none : L2B c r) : (Fin 4 → ℝ) → ℝ) =ᵐ[μB] fun _ => 1 := by
    show ((oneB c r : L2B c r) : (Fin 4 → ℝ) → ℝ) =ᵐ[μB] fun _ => 1
    exact (memLp_const (1 : ℝ)).coeFn_toLp
  have hzero : ∀ ν, ((oneH c r (some ν) : L2B c r) : (Fin 4 → ℝ) → ℝ) =ᵐ[μB] fun _ => 0 :=
    fun ν => by
      show (((0 : L2B c r)) : (Fin 4 → ℝ) → ℝ) =ᵐ[μB] fun _ => 0
      exact Lp.coeFn_zero _ _ _
  have eN1 : ∀ ν, ∫ x in euclBall c r, fn (derS ν (η k)) x *
      ((oneH c r none : L2B c r) : (Fin 4 → ℝ) → ℝ) x * (y (some ν) : (Fin 4 → ℝ) → ℝ) x =
        ∫ x in euclBall c r, fn (derS ν (η k)) x * (y (some ν) : (Fin 4 → ℝ) → ℝ) x := by
    intro ν
    refine integral_congr_ae ?_
    filter_upwards [hone] with x hx
    rw [hx, mul_one]
  have hzero' : ∀ᵐ x ∂μB, ∀ ν, ((oneH c r (some ν) : L2B c r) : (Fin 4 → ℝ) → ℝ) x = 0 := by
    rw [ae_all_iff]; exact hzero
  have eN2 : ∫ x in euclBall c r, (fn (lapS (η k)) x *
      ((oneH c r none : L2B c r) : (Fin 4 → ℝ) → ℝ) x +
        ∑ ν, fn (derS ν (η k)) x * ((oneH c r (some ν) : L2B c r) : (Fin 4 → ℝ) → ℝ) x) *
          (y none : (Fin 4 → ℝ) → ℝ) x =
      ∫ x in euclBall c r, fn (lapS (η k)) x * (y none : (Fin 4 → ℝ) → ℝ) x := by
    refine integral_congr_ae ?_
    filter_upwards [hone, hzero'] with x hx hx'
    simp [hx, hx']
  simp only [eN1, eN2] at hNk
  -- the coupling part
  have hC : ∀ l, ∑ ν, ∫ x in euclBall c r, fn (A ν k l) x * fn (η l) x *
      (y (some ν) : (Fin 4 → ℝ) → ℝ) x =
      -∫ x in euclBall c r, (fn (divS (fun ν => A ν k l)) x * fn (η l) x +
        ∑ ν, fn (A ν k l) x * fn (derS ν (η l)) x) * (y none : (Fin 4 → ℝ) → ℝ) x := by
    intro l
    have h := (htan k l).integral_H1B c r (M := max M3 M4) (le_max_of_le_left hM30)
      (fun ν => (memLp_fn _).aestronglyMeasurable) (memLp_fn _).aestronglyMeasurable
      (fun ν => (hM3 (ν, l)).mono fun x hx => hx.trans (le_max_left _ _))
      ((hM4 l).mono fun x hx => hx.trans (le_max_right _ _)) (toH1_mem (η l)) y hy
    have e1 : ∀ ν, ∫ x in euclBall c r, fn (A ν k l) x *
        ((toH1 (η l) none : L2B c r) : (Fin 4 → ℝ) → ℝ) x * (y (some ν) : (Fin 4 → ℝ) → ℝ) x =
          ∫ x in euclBall c r, fn (A ν k l) x * fn (η l) x *
            (y (some ν) : (Fin 4 → ℝ) → ℝ) x := by
      intro ν
      refine integral_congr_ae ?_
      filter_upwards [toH1_none_ae (η l)] with x hx
      rw [hx]
    have hs : ∀ᵐ x ∂μB, ∀ ν, ((toH1 (η l) (some ν) : L2B c r) : (Fin 4 → ℝ) → ℝ) x =
        fn (derS ν (η l)) x := by
      rw [ae_all_iff]; exact toH1_some_ae (η l)
    have e2 : ∫ x in euclBall c r, (fn (divS (fun ν => A ν k l)) x *
        ((toH1 (η l) none : L2B c r) : (Fin 4 → ℝ) → ℝ) x +
          ∑ ν, fn (A ν k l) x * ((toH1 (η l) (some ν) : L2B c r) : (Fin 4 → ℝ) → ℝ) x) *
            (y none : (Fin 4 → ℝ) → ℝ) x =
        ∫ x in euclBall c r, (fn (divS (fun ν => A ν k l)) x * fn (η l) x +
          ∑ ν, fn (A ν k l) x * fn (derS ν (η l)) x) * (y none : (Fin 4 → ℝ) → ℝ) x := by
      refine integral_congr_ae ?_
      filter_upwards [toH1_none_ae (η l), hs] with x hx hx'
      simp only [hx, hx']
    simp only [e1, e2] at h
    exact h
  -- assemble
  have hint : ∀ {F : (Fin 4 → ℝ) → ℝ}, MemLp F 2 μB →
      Integrable (fun x => F x * (y none : (Fin 4 → ℝ) → ℝ) x) μB := fun hF =>
    integrable_mul_of_memLp_two c r hF (Lp.memLp _)
  have hDl : ∀ l, MemLp (fun x => fn (divS (fun ν => A ν k l)) x * fn (η l) x +
      ∑ ν, fn (A ν k l) x * fn (derS ν (η l)) x) 2 μB := fun l =>
    (memLp_bdd_mul c r (memLp_fn _).aestronglyMeasurable (hM4 l) (memLp_fn _)).add
      (memLp_finsetSum _ fun ν _ => memLp_bdd_mul c r (memLp_fn _).aestronglyMeasurable
        (hM3 (ν, l)) (memLp_fn _))
  have eLin : ∫ x in euclBall c r, fn (linOpS A η k) x * (y none : (Fin 4 → ℝ) → ℝ) x =
      (∫ x in euclBall c r, fn (lapS (η k)) x * (y none : (Fin 4 → ℝ) → ℝ) x) +
        ∑ l, ∫ x in euclBall c r, (fn (divS (fun ν => A ν k l)) x * fn (η l) x +
          ∑ ν, fn (A ν k l) x * fn (derS ν (η l)) x) * (y none : (Fin 4 → ℝ) → ℝ) x := by
    rw [← integral_finsetSum _ fun l _ => hint (hDl l),
      ← integral_add (hint (memLp_fn _)) (integrable_finsetSum _ fun l _ => hint (hDl l))]
    refine integral_congr_ae ?_
    filter_upwards [fn_linOpS A η k] with x hx
    rw [hx, add_mul, Finset.sum_mul]
  rw [hNk, Finset.sum_congr rfl fun l _ => hC l, eLin, Finset.sum_neg_distrib]
  ring

end WeakForm

/-! ### The Lax–Milgram formulation on `H¹₀(B)^N` -/

section LaxMilgram

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {N : ℕ}

/-- The coefficient functions. -/
def coefFn (A : Fin 4 → Fin N → Fin N → SobAlg c r 4) : Fin 4 → Fin N → Fin N →
    (Fin 4 → ℝ) → ℝ := fun ν k l => fn (A ν k l)

theorem memLp_coefFn (A : Fin 4 → Fin N → Fin N → SobAlg c r 4) (ν : Fin 4) (k l : Fin N) :
    MemLp (coefFn A ν k l) 4 (volume.restrict (euclBall c r)) := memLp_four_fn _

/-- The coupling term as an integral. -/
theorem inner_mulCLM_sobCLM {a : (Fin 4 → ℝ) → ℝ} (ha : MemLp a 4 (volume.restrict (euclBall c r)))
    (x : H1B0 c r) (g : L2B c r) :
    ⟪mulCLM c r ha (sobCLM c r x), g⟫ = ∫ z in euclBall c r,
      a z * ((x : H1Amb c r) none : (Fin 4 → ℝ) → ℝ) z * (g : (Fin 4 → ℝ) → ℝ) z := by
  have h1 : (mulCLM c r ha (sobCLM c r x) : (Fin 4 → ℝ) → ℝ) =ᵐ[volume.restrict (euclBall c r)]
      fun y => a y * (sobCLM c r x : (Fin 4 → ℝ) → ℝ) y :=
    ((Lp.memLp (sobCLM c r x)).mul' ha).coeFn_toLp
  have h2 : (sobCLM c r x : (Fin 4 → ℝ) → ℝ) =ᵐ[volume.restrict (euclBall c r)]
      (((x : H1Amb c r) none : L2B c r) : (Fin 4 → ℝ) → ℝ) := (memLp_four_H1B c r x).coeFn_toLp
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [h1, h2] with y e1 e2
  rw [e1, e2]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- The `H¹₀(B)^N` element of a mean-zero field in `H⁵(B)^N`. -/
def toXi (η : Fin N → SobAlg c r 5) (hm : ∀ k, meanS (η k) = 0) : XiB c r N :=
  WithLp.toLp 2 fun k => ⟨toH1 (η k), toH1_mem (η k), by
    show meanCLM c r (toH1 (η k)) = 0
    rw [meanCLM_toH1, hm k]⟩

theorem toXi_apply (η : Fin N → SobAlg c r 5) (hm : ∀ k, meanS (η k) = 0) (k : Fin N) :
    ((toXi η hm k : H1B0 c r) : H1Amb c r) = toH1 (η k) := rfl

/-- **The weak (Lax–Milgram) equation satisfied by a Neumann field.** -/
theorem weak_toXi {A : Fin 4 → Fin N → Fin N → SobAlg c r 4}
    (htan : ∀ k l, IsTangentialS (fun ν => A ν k l)) {η : Fin N → SobAlg c r 5}
    (hN : ∀ k, IsNeumannS (η k)) (hm : ∀ k, meanS (η k) = 0) (ζ : XiB c r N) :
    dirFormN c r N (toXi η hm) ζ + couplingN c r N (memLp_coefFn A) (toXi η hm) ζ =
      -∑ k, ∫ x in euclBall c r, fn (linOpS A η k) x *
        (((ζ k : H1B0 c r) : H1Amb c r) none : (Fin 4 → ℝ) → ℝ) x := by
  rw [dirFormN_apply, couplingN_apply, ← Finset.sum_neg_distrib]
  have hk : ∀ k, dirForm c r (toXi η hm k) (ζ k) + ∑ ν, ∑ l,
      ⟪mulCLM c r (memLp_coefFn A ν k l) (sobCLM c r (toXi η hm l)), derivL c r ν (ζ k)⟫ =
        -∫ x in euclBall c r, fn (linOpS A η k) x *
          (((ζ k : H1B0 c r) : H1Amb c r) none : (Fin 4 → ℝ) → ℝ) x := by
    intro k
    rw [← weak_linOpS htan hN k (ζ k).2.1, dirForm_apply, Finset.sum_comm]
    congr 1
    · refine Finset.sum_congr rfl fun ν _ => ?_
      rw [toXi_apply, toH1_some, inner_toLp_left]
    · refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun ν _ => ?_
      rw [inner_mulCLM_sobCLM, toXi_apply]
      refine integral_congr_ae ?_
      filter_upwards [toH1_none_ae (η l)] with x hx
      rw [hx]; rfl
  rw [← Finset.sum_congr rfl fun k _ => hk k, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]

/-- **Uniqueness for the linearised operator** (`Σ ‖A‖_{L⁴} ≤ δ`): a mean-zero Neumann field
`η ∈ H⁵(B)^N` with `linOpS A η = 0` vanishes. -/
theorem linOpS_injective : ∃ δ : ℝ, 0 < δ ∧ ∀ (A : Fin 4 → Fin N → Fin N → SobAlg c r 4),
    (∀ k l, IsTangentialS (fun ν => A ν k l)) →
    ∑ ν, ∑ k, ∑ l, (eLpNorm (fn (A ν k l)) 4 (volume.restrict (euclBall c r))).toReal ≤ δ →
    ∀ η : Fin N → SobAlg c r 5, (∀ k, IsNeumannS (η k)) → ∀ hm : (∀ k, meanS (η k) = 0),
      linOpS A η = 0 → η = 0 := by
  obtain ⟨δ, hδ, hLM⟩ := linearized_neumann_ball c r N
  refine ⟨δ, hδ, fun A htan hsmall η hN hm h0 => ?_⟩
  obtain ⟨ξ, -, huniq⟩ := hLM (coefFn A) (memLp_coefFn A) hsmall 0
  have hz' : ∀ (ζ : XiB c r N) k, ∫ x in euclBall c r, fn (linOpS A η k) x *
      (((ζ k : H1B0 c r) : H1Amb c r) none : (Fin 4 → ℝ) → ℝ) x = 0 := fun ζ k => by
    rw [h0]
    refine (integral_congr_ae ?_).trans (integral_zero _ _)
    filter_upwards [fn_zero (c := c) (r := r) (s := 3)] with x hx
    simp [hx]
  have h1 := huniq (toXi η hm) fun ζ => by
    rw [weak_toXi htan hN hm ζ, Finset.sum_congr rfl fun k _ => hz' ζ k]
    simp
  have h2 := huniq 0 fun ζ => by simp
  have h3 : toXi η hm = 0 := h1.trans h2.symm
  funext k
  refine ext_fn ?_
  have h4 : toH1 (η k) none = 0 := by
    have := congrArg (fun z : XiB c r N => (((z k : H1B0 c r) : H1Amb c r) none)) h3
    simpa [toXi_apply] using this
  rw [toH1_none] at h4
  have h5 := (memLp_fn (η k)).coeFn_toLp
  rw [h4] at h5
  filter_upwards [h5, Lp.coeFn_zero ℝ 2 (volume.restrict (euclBall c r)),
    fn_zero (c := c) (r := r) (s := 5)] with x e1 e2 e3
  rw [← e1, e2, Pi.zero_apply]
  exact e3.symm

end LaxMilgram

/-! ### Existence and the elliptic bootstrap -/

section Existence

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {N : ℕ}

/-- The load `ζ ↦ -Σ_k ⟨f_k, ζ_k⟩`. -/
def loadN (f : Fin N → SobAlg c r 3) : XiB c r N →L[ℝ] ℝ :=
  -∑ k, (innerSL ℝ ((memLp_fn (f k)).toLp (fn (f k)))).comp
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin 4) => L2B c r) none).comp
      ((H1B0 c r).subtypeL.comp (compXi c r N k)))

theorem loadN_apply (f : Fin N → SobAlg c r 3) (ζ : XiB c r N) :
    loadN f ζ = -∑ k, ⟪(memLp_fn (f k)).toLp (fn (f k)), ((ζ k : H1B0 c r) : H1Amb c r) none⟫ := by
  simp [loadN, ContinuousLinearMap.sum_apply, compXi]

/-- The divergence data `div(A^{kl}) x₀ + Σ_ν A_ν^{kl} x_ν`. -/
def divData (A : Fin 4 → Fin N → Fin N → SobAlg c r 4) (k l : Fin N) (x : H1Amb c r) :
    (Fin 4 → ℝ) → ℝ := fun z => fn (divS (fun ν => A ν k l)) z * (x none : (Fin 4 → ℝ) → ℝ) z +
  ∑ ν, fn (A ν k l) z * (x (some ν) : (Fin 4 → ℝ) → ℝ) z

theorem memLp_divData (A : Fin 4 → Fin N → Fin N → SobAlg c r 4) (k l : Fin N) (x : H1Amb c r) :
    MemLp (divData A k l x) 2 (volume.restrict (euclBall c r)) := by
  obtain ⟨M4, -, hM4⟩ := exists_ae_bound_fn (divS (fun ν => A ν k l))
  obtain ⟨M3, -, hM3⟩ := exists_common_bound (fun ν : Fin 4 => A ν k l)
  exact (memLp_bdd_mul c r (memLp_fn _).aestronglyMeasurable hM4 (Lp.memLp _)).add
    (memLp_finsetSum _ fun ν _ => memLp_bdd_mul c r (memLp_fn _).aestronglyMeasurable (hM3 ν)
      (Lp.memLp _))

/-- The Neumann data of the `k`-th component of a weak solution. -/
def compData (A : Fin 4 → Fin N → Fin N → SobAlg c r 4) (f : Fin N → SobAlg c r 3)
    (ξ : XiB c r N) (k : Fin N) : L2B c r :=
  (memLp_fn (f k)).toLp (fn (f k)) -
    ∑ l, (memLp_divData A k l ((ξ l : H1B0 c r) : H1Amb c r)).toLp
      (divData A k l ((ξ l : H1B0 c r) : H1Amb c r))

/-- The tangential integration by parts in terms of `divData`. -/
theorem integral_divData {A : Fin 4 → Fin N → Fin N → SobAlg c r 4}
    (htan : ∀ k l, IsTangentialS (fun ν => A ν k l)) (k l : Fin N) {x : H1Amb c r}
    (hx : x ∈ H1B c r) {y : H1Amb c r} (hy : y ∈ H1B c r) :
    ∑ ν, ∫ z in euclBall c r, fn (A ν k l) z * (x none : (Fin 4 → ℝ) → ℝ) z *
      (y (some ν) : (Fin 4 → ℝ) → ℝ) z =
      -∫ z in euclBall c r, divData A k l x z * (y none : (Fin 4 → ℝ) → ℝ) z := by
  obtain ⟨M3, hM30, hM3⟩ := exists_common_bound (fun ν : Fin 4 => A ν k l)
  obtain ⟨M4, hM40, hM4⟩ := exists_ae_bound_fn (divS (fun ν => A ν k l))
  exact (htan k l).integral_H1B c r (M := max M3 M4) (le_max_of_le_left hM30)
    (fun ν => (memLp_fn _).aestronglyMeasurable) (memLp_fn _).aestronglyMeasurable
    (fun ν => (hM3 ν).mono fun x hx => hx.trans (le_max_left _ _))
    (hM4.mono fun x hx => hx.trans (le_max_right _ _)) hx y hy

/-- **Each component of a weak solution is a Neumann solution** with data
`f_k - Σ_l div(A^{kl} ξ_l)`. -/
theorem component_eq_sol {A : Fin 4 → Fin N → Fin N → SobAlg c r 4}
    (htan : ∀ k l, IsTangentialS (fun ν => A ν k l)) {f : Fin N → SobAlg c r 3} {ξ : XiB c r N}
    (hξ : ∀ ζ : XiB c r N, dirFormN c r N ξ ζ + couplingN c r N (memLp_coefFn A) ξ ζ = loadN f ζ)
    (k : Fin N) : ξ k = solCLM c r (compData A f ξ k) := by
  refine neumann_H1B0_unique c r (F := compData A f ξ k) (fun y => ?_) (solCLM_spec c r _)
  have h := hξ (singleXi c r N k y)
  rw [dirFormN_apply, couplingN_apply, loadN_apply] at h
  have hs : ∀ k', singleXi c r N k y k' = if k' = k then y else 0 := fun k' =>
    singleXi_apply c r N k k' y
  simp only [hs] at h
  have e1 : ∑ k', dirForm c r (ξ k') (if k' = k then y else 0) = dirForm c r (ξ k) y := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  have e3 : ∑ k', ⟪(memLp_fn (f k')).toLp (fn (f k')),
      (((if k' = k then y else 0 : H1B0 c r)) : H1Amb c r) none⟫ =
      ⟪(memLp_fn (f k)).toLp (fn (f k)), ((y : H1B0 c r) : H1Amb c r) none⟫ := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  have e4 : ∑ ν, ∑ k', ∑ l, ⟪mulCLM c r (memLp_coefFn A ν k' l) (sobCLM c r (ξ l)),
      derivL c r ν (if k' = k then y else 0)⟫ =
        ∑ l, -∫ z in euclBall c r, divData A k l ((ξ l : H1B0 c r) : H1Amb c r) z *
          (((y : H1B0 c r) : H1Amb c r) none : (Fin 4 → ℝ) → ℝ) z := by
    have hν : ∀ ν, ∑ k', ∑ l, ⟪mulCLM c r (memLp_coefFn A ν k' l) (sobCLM c r (ξ l)),
        derivL c r ν (if k' = k then y else 0)⟫ =
          ∑ l, ∫ z in euclBall c r, fn (A ν k l) z *
            ((((ξ l : H1B0 c r) : H1Amb c r) none : L2B c r) : (Fin 4 → ℝ) → ℝ) z *
              ((((y : H1B0 c r) : H1Amb c r) (some ν) : L2B c r) : (Fin 4 → ℝ) → ℝ) z := by
      intro ν
      rw [Finset.sum_eq_single k]
      · simp only [if_true]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [inner_mulCLM_sobCLM]
        rfl
      · intro b _ hb; simp [hb]
      · simp
    rw [Finset.sum_congr rfl fun ν _ => hν ν, Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => integral_divData htan k l (ξ l).2.1 y.2.1
  rw [e1, e3, e4] at h
  rw [loadCLM_apply, compData, inner_sub_left, sum_inner]
  have e5 : ∀ l, ⟪(memLp_divData A k l ((ξ l : H1B0 c r) : H1Amb c r)).toLp
      (divData A k l ((ξ l : H1B0 c r) : H1Amb c r)), ((y : H1B0 c r) : H1Amb c r) none⟫ =
        ∫ z in euclBall c r, divData A k l ((ξ l : H1B0 c r) : H1Amb c r) z *
          (((y : H1B0 c r) : H1Amb c r) none : (Fin 4 → ℝ) → ℝ) z := fun l =>
    inner_toLp_left c r _ _
  simp only [e5]
  rw [Finset.sum_neg_distrib] at h
  linarith

/-- **Regularity of the divergence data**: if `x₀ ∈ H^{t+1}(B)`, `t ≤ 3`, then
`div(A^{kl}) x₀ + Σ_ν A_ν^{kl} x_ν ∈ H^t(B)` (it is `Σ_ν ∂_ν(A_ν^{kl} x₀)` and
`A_ν^{kl} x₀ ∈ H^{t+1}(B)` by the mixed product estimate). -/
theorem memHk_divData (A : Fin 4 → Fin N → Fin N → SobAlg c r 4) (k l : Fin N) {t : ℕ}
    (ht : t ≤ 3) {x : H1Amb c r} (hx : x ∈ H1B c r)
    (hxt : MemHk (euclBall c r) (t + 1) (x none : (Fin 4 → ℝ) → ℝ)) :
    MemHk (euclBall c r) t (divData A k l x) := by
  set μB := volume.restrict (euclBall c r)
  have hterm : ∀ ν, MemHk (euclBall c r) t (fun z => fn (derS ν (A ν k l)) z *
      (x none : (Fin 4 → ℝ) → ℝ) z + fn (A ν k l) z * (x (some ν) : (Fin 4 → ℝ) → ℝ) z) := by
    intro ν
    have hu4 : MemHk (euclBall c r) 4 (fn (A ν k l)) := memHk_fn _
    have hP := memHk_mul_gen c r hr.out (p := 4) (t := t + 1) (by norm_num) (by omega) hu4 hxt
    have hw := hasWeakPartialR_mul c r (i := ν) (hu4.mono (by norm_num)) (hxt.mono (by omega))
      (memLp_fn (derS ν (A ν k l))) (Lp.memLp (x (some ν))) (weak_derS ν (A ν k l))
      (hasWeakPartialR_of_H1B c r hx ν)
    obtain ⟨M1, -, hM1⟩ := exists_ae_bound_fn (derS ν (A ν k l))
    obtain ⟨M2, -, hM2⟩ := exists_ae_bound_fn (A ν k l)
    have hL : MemLp (fun z => fn (derS ν (A ν k l)) z * (x none : (Fin 4 → ℝ) → ℝ) z +
        fn (A ν k l) z * (x (some ν) : (Fin 4 → ℝ) → ℝ) z) 2 μB :=
      (memLp_bdd_mul c r (memLp_fn _).aestronglyMeasurable hM1 (Lp.memLp _)).add
        (memLp_bdd_mul c r (memLp_fn _).aestronglyMeasurable hM2 (Lp.memLp _))
    exact hP.deriv (isOpen_euclBall c r) hw hL
  refine (MemHk.sum' Finset.univ fun ν _ => hterm ν).congr_ae ?_
  filter_upwards [fn_divS (fun ν => A ν k l)] with z hz
  simp only [divData, hz, Finset.sum_mul, ← Finset.sum_add_distrib]

/-- The function component of `compData`. -/
theorem compData_ae (A : Fin 4 → Fin N → Fin N → SobAlg c r 4) (f : Fin N → SobAlg c r 3)
    (ξ : XiB c r N) (k : Fin N) :
    ((compData A f ξ k : L2B c r) : (Fin 4 → ℝ) → ℝ) =ᵐ[volume.restrict (euclBall c r)]
      fun z => fn (f k) z - ∑ l, divData A k l ((ξ l : H1B0 c r) : H1Amb c r) z := by
  have h1 := Lp.coeFn_sub ((memLp_fn (f k)).toLp (fn (f k)))
    (∑ l, (memLp_divData A k l ((ξ l : H1B0 c r) : H1Amb c r)).toLp
      (divData A k l ((ξ l : H1B0 c r) : H1Amb c r)))
  have h2 := coeFn_finset_sum c r Finset.univ fun l =>
    (memLp_divData A k l ((ξ l : H1B0 c r) : H1Amb c r)).toLp
      (divData A k l ((ξ l : H1B0 c r) : H1Amb c r))
  have h3 : ∀ᵐ z ∂(volume.restrict (euclBall c r)), ∀ l,
      ((memLp_divData A k l ((ξ l : H1B0 c r) : H1Amb c r)).toLp
        (divData A k l ((ξ l : H1B0 c r) : H1Amb c r)) : (Fin 4 → ℝ) → ℝ) z =
          divData A k l ((ξ l : H1B0 c r) : H1Amb c r) z := by
    rw [ae_all_iff]; exact fun l => (memLp_divData _ _ _ _).coeFn_toLp
  filter_upwards [h1, h2, h3, (memLp_fn (f k)).coeFn_toLp] with z e1 e2 e3 e4
  rw [compData, e1, Pi.sub_apply, e2, e4]
  simp only [e3]

/-- **The elliptic bootstrap**: every component of the weak solution lies in `H⁵(B)`. -/
theorem memHk5_of_weak {A : Fin 4 → Fin N → Fin N → SobAlg c r 4}
    (htan : ∀ k l, IsTangentialS (fun ν => A ν k l)) {f : Fin N → SobAlg c r 3} {ξ : XiB c r N}
    (hξ : ∀ ζ : XiB c r N, dirFormN c r N ξ ζ + couplingN c r N (memLp_coefFn A) ξ ζ = loadN f ζ)
    (k : Fin N) :
    MemHk (euclBall c r) 5 ((((ξ k : H1B0 c r) : H1Amb c r) none : L2B c r) :
      (Fin 4 → ℝ) → ℝ) := by
  have hstep : ∀ t, t ≤ 3 → (∀ l, MemHk (euclBall c r) (t + 1)
      ((((ξ l : H1B0 c r) : H1Amb c r) none : L2B c r) : (Fin 4 → ℝ) → ℝ)) →
      ∀ k, MemHk (euclBall c r) (t + 2)
        ((((ξ k : H1B0 c r) : H1Amb c r) none : L2B c r) : (Fin 4 → ℝ) → ℝ) := by
    intro t ht hl k
    have hF : MemHk (euclBall c r) t ((compData A f ξ k : L2B c r) : (Fin 4 → ℝ) → ℝ) := by
      refine (((memHk_fn (f k)).mono ht).sub (MemHk.sum' Finset.univ fun l _ =>
        memHk_divData A k l ht (ξ l).2.1 (hl l))).congr_ae ?_
      filter_upwards [compData_ae A f ξ k] with z hz
      rw [hz]
    have hsol := neumann_Hk_weak c r t hF
    have e : (((ξ k : H1B0 c r) : H1Amb c r) none : (Fin 4 → ℝ) → ℝ) =
        solFn c r (compData A f ξ k) := by
      simp only [solFn]; rw [← component_eq_sol htan hξ k]
    rw [e]; exact hsol
  have h1 : ∀ l, MemHk (euclBall c r) 1
      ((((ξ l : H1B0 c r) : H1Amb c r) none : L2B c r) : (Fin 4 → ℝ) → ℝ) := fun l =>
    ⟨Lp.memLp _, fun ν => ⟨_, hasWeakPartialR_of_H1B c r (ξ l).2.1 ν, Lp.memLp _⟩⟩
  have h2 := hstep 0 (by norm_num) h1
  have h3 := hstep 1 (by norm_num) h2
  have h4 := hstep 2 (by norm_num) h3
  exact hstep 3 le_rfl h4 k

/-- Two `L²(B)` functions with the same integrals against all test functions agree a.e. -/
theorem ae_eq_of_integral_test {g1 g2 : (Fin 4 → ℝ) → ℝ}
    (h1 : MemLp g1 2 (volume.restrict (euclBall c r)))
    (h2 : MemLp g2 2 (volume.restrict (euclBall c r)))
    (h : ∀ φ, IsTest (euclBall c r) φ → ∫ x, φ x * g1 x = ∫ x, φ x * g2 x) :
    g1 =ᵐ[volume.restrict (euclBall c r)] g2 := by
  have hw1 : HasWeakPartialR (euclBall c r) 0 (fun _ => (0 : ℝ)) (fun x => g1 x - g2 x) := by
    intro φ hφ
    simp only [mul_zero, integral_zero, mul_sub]
    rw [integral_sub (integrable_test_mul hφ h1) (integrable_test_mul hφ h2), h φ hφ, sub_self,
      neg_zero]
  have hw2 : HasWeakPartialR (euclBall c r) 0 (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) := by
    intro φ hφ; simp
  have := weakR_ae_eq (isOpen_euclBall c r) hw1 hw2 (h1.sub h2) (memLp_const 0)
  rw [EventuallyEq, ae_restrict_iff' (measurableSet_euclBall c r)]
  filter_upwards [this] with x hx hxB
  exact sub_eq_zero.mp (hx hxB)

/-- The integral of the divergence data vanishes (test with the constant `1`). -/
theorem integral_divData_eq_zero {A : Fin 4 → Fin N → Fin N → SobAlg c r 4}
    (htan : ∀ k l, IsTangentialS (fun ν => A ν k l)) (k l : Fin N) {x : H1Amb c r}
    (hx : x ∈ H1B c r) : ∫ z in euclBall c r, divData A k l x z = 0 := by
  have h := integral_divData htan k l hx (oneH_mem c r)
  have hzero : ∀ ν, ((oneH c r (some ν) : L2B c r) : (Fin 4 → ℝ) → ℝ) =ᵐ[volume.restrict
      (euclBall c r)] fun _ => 0 := fun ν => by
    show (((0 : L2B c r)) : (Fin 4 → ℝ) → ℝ) =ᵐ[_] fun _ => 0
    exact Lp.coeFn_zero _ _ _
  have hone : ((oneH c r none : L2B c r) : (Fin 4 → ℝ) → ℝ) =ᵐ[volume.restrict (euclBall c r)]
      fun _ => 1 := by
    show ((oneB c r : L2B c r) : (Fin 4 → ℝ) → ℝ) =ᵐ[_] fun _ => 1
    exact (memLp_const (1 : ℝ)).coeFn_toLp
  have eL : ∀ ν, ∫ z in euclBall c r, fn (A ν k l) z * (x none : (Fin 4 → ℝ) → ℝ) z *
      ((oneH c r (some ν) : L2B c r) : (Fin 4 → ℝ) → ℝ) z = 0 := fun ν => by
    refine (integral_congr_ae ?_).trans (integral_zero _ _)
    filter_upwards [hzero ν] with z hz
    simp [hz]
  have eR : ∫ z in euclBall c r, divData A k l x z * ((oneH c r none : L2B c r) :
      (Fin 4 → ℝ) → ℝ) z = ∫ z in euclBall c r, divData A k l x z := by
    refine integral_congr_ae ?_
    filter_upwards [hone] with z hz
    simp [hz]
  simp only [eL, Finset.sum_const_zero, eR] at h
  linarith

set_option maxHeartbeats 1000000 in
/-- **Existence for the linearised operator with `H⁵` regularity** (`Σ ‖A‖_{L⁴} ≤ δ`, the same
`δ` as in `linOpS_injective`): for every mean-zero `f ∈ H³(B)^N` there is a mean-zero Neumann
`η ∈ H⁵(B)^N` with `linOpS A η = f`. -/
theorem exists_linOpS_eq : ∃ δ : ℝ, 0 < δ ∧ ∀ (A : Fin 4 → Fin N → Fin N → SobAlg c r 4),
    (∀ k l, IsTangentialS (fun ν => A ν k l)) →
    ∑ ν, ∑ k, ∑ l, (eLpNorm (fn (A ν k l)) 4 (volume.restrict (euclBall c r))).toReal ≤ δ →
    ∀ f : Fin N → SobAlg c r 3, (∀ k, meanS (f k) = 0) →
      ∃ η : Fin N → SobAlg c r 5, (∀ k, IsNeumannS (η k)) ∧ (∀ k, meanS (η k) = 0) ∧
        linOpS A η = f := by
  obtain ⟨δ, hδ, hLM⟩ := linearized_neumann_ball c r N
  refine ⟨δ, hδ, fun A htan hsmall f hf => ?_⟩
  obtain ⟨ξ, hξ, -⟩ := hLM (coefFn A) (memLp_coefFn A) hsmall (loadN f)
  have h5 := memHk5_of_weak htan hξ
  -- the `H⁵` elements
  choose J hJ hJae using fun k => exists_mem_HsB_of_memHk c r (h5 k)
  obtain ⟨η, hηdef⟩ : ∃ η : Fin N → SobAlg c r 5, η = fun k => ofJet ⟨J k, hJ k⟩ := ⟨_, rfl⟩
  have hfn : ∀ k, fn (η k) =ᵐ[volume.restrict (euclBall c r)]
      (((ξ k : H1B0 c r) : H1Amb c r) none : (Fin 4 → ℝ) → ℝ) :=
    fun k => by rw [hηdef]; exact hJae k
  have hder : ∀ k ν, fn (derS ν (η k)) =ᵐ[volume.restrict (euclBall c r)]
      (((ξ k : H1B0 c r) : H1Amb c r) (some ν) : (Fin 4 → ℝ) → ℝ) := by
    intro k ν
    have h1 := (weak_derS ν (η k)).congr_ae c r (hfn k) EventuallyEq.rfl
    have := weakR_ae_eq (isOpen_euclBall c r) h1 (hasWeakPartialR_of_H1B c r (ξ k).2.1 ν)
      (memLp_fn _) (Lp.memLp _)
    rw [EventuallyEq, ae_restrict_iff' (measurableSet_euclBall c r)]
    exact this
  have hmean : ∀ k, meanS (η k) = 0 := by
    intro k
    have h0 : meanCLM c r ((ξ k : H1B0 c r) : H1Amb c r) = 0 := (ξ k).2.2
    rw [meanCLM_apply, inner_oneB] at h0
    rw [meanS, integral_congr_ae (hfn k)]
    exact h0
  -- the Laplacian of the components
  obtain ⟨F, hFdef⟩ : ∃ F : Fin N → L2B c r, F = fun k => compData A f ξ k := ⟨_, rfl⟩
  have hcomp : ∀ k, ξ k = solCLM c r (F k) := fun k => by
    rw [hFdef]; exact component_eq_sol htan hξ k
  have hlap : ∀ k, fn (lapS (η k)) =ᵐ[volume.restrict (euclBall c r)] solRhs c r (F k) := by
    intro k
    refine ae_eq_of_integral_test (memLp_fn _) (memLp_solRhs c r (F k)) fun φ hφ => ?_
    have h1 := solCLM_weak_test c r (F k) hφ
    have h2 : ∀ ν, ∫ x, pd φ ν x * fn (derS ν (η k)) x =
        -∫ x, φ x * fn (derS ν (derS ν (η k))) x := fun ν => weak_derS ν (derS ν (η k)) φ hφ
    have e1 : ∀ ν, ∫ x, pd φ ν x * solGrad c r (F k) ν x = ∫ x, pd φ ν x * fn (derS ν (η k)) x := by
      intro ν
      rw [integral_test_eq_setIntegral c r (isTest_pd hφ ν),
        integral_test_eq_setIntegral c r (isTest_pd hφ ν)]
      refine integral_congr_ae ?_
      filter_upwards [hder k ν] with x hx
      simp only [solGrad, ← hcomp k, hx]
    simp only [e1, h2, Finset.sum_neg_distrib] at h1
    rw [← neg_inj, ← h1, integral_test_eq_setIntegral c r hφ]
    simp only [integral_test_eq_setIntegral c r hφ]
    rw [← integral_finsetSum _ fun ν _ => (integrable_test_mul hφ (memLp_fn _)).integrableOn]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [fn_lapS (η k)] with x hx
    rw [hx, Finset.mul_sum]
  -- the Neumann condition
  have hNeu : ∀ k, IsNeumannS (η k) := by
    intro k φ hφ
    have hy := graphC1_mem c r ⟨φ, show φ ∈ C1fun from hφ⟩
    have h1 := solCLM_weak c r (F k) hy
    simp only [graphC1_some, graphC1_none, meanCLM_graph] at h1
    have eL : ∀ ν, ⟪((solCLM c r (F k) : H1B0 c r) : H1Amb c r) (some ν),
        (memLp_ball_pd_of_C1 c r hφ ν).toLp (pd φ ν)⟫ =
          ∫ x in euclBall c r, fn (derS ν (η k)) x * pd φ ν x := by
      intro ν
      rw [real_inner_comm, inner_toLp_left]
      refine integral_congr_ae ?_
      filter_upwards [hder k ν] with x hx
      rw [hx, hcomp k, mul_comm]
    have eR : ⟪F k, (memLp_ball_of_C1 c r hφ).toLp φ⟫ = ∫ x in euclBall c r, φ x * F k x := by
      rw [real_inner_comm, inner_toLp_left]
    simp only [eL, eR] at h1
    show ∑ ν, ∫ x in euclBall c r, fn (derS ν (η k)) x * pd φ ν x =
      -∫ x in euclBall c r, fn (lapS (η k)) x * φ x
    rw [h1]
    have hiF : IntegrableOn (fun x => φ x * F k x) (euclBall c r) :=
      integrable_mul_of_memLp_two c r (memLp_ball_of_C1 c r hφ) (Lp.memLp _)
    have hi1 : IntegrableOn φ (euclBall c r) :=
      integrableOn_euclBall hr.out.le hφ.continuous
    have e2 : ∫ x in euclBall c r, fn (lapS (η k)) x * φ x =
        ∫ x in euclBall c r, solRhs c r (F k) x * φ x := by
      refine integral_congr_ae ?_
      filter_upwards [hlap k] with x hx
      rw [hx]
    rw [e2]
    simp only [solRhs, sub_mul]
    rw [integral_sub ((integrable_mul_of_memLp_two c r (Lp.memLp _) (memLp_ball_of_C1 c r hφ)))
      (hi1.const_mul _), integral_const_mul]
    have e3 : ∫ x in euclBall c r, F k x * φ x = ∫ x in euclBall c r, φ x * F k x := by
      congr 1; funext x; ring
    rw [e3]
    ring
  refine ⟨η, hNeu, hmean, ?_⟩
  funext k
  refine ext_fn ?_
  -- the average of the Neumann data vanishes
  have hFk := compData_ae A f ξ k
  rw [← show F k = compData A f ξ k by rw [hFdef]] at hFk
  have hintF : ∫ x in euclBall c r, F k x = 0 := by
    rw [integral_congr_ae hFk, integral_sub (integrable_of_memLp_two c r (memLp_fn _))
      (integrable_finsetSum _ fun l _ => integrable_of_memLp_two c r (memLp_divData _ _ _ _)),
      integral_finsetSum _ fun l _ => integrable_of_memLp_two c r (memLp_divData _ _ _ _)]
    simp only [integral_divData_eq_zero htan k _ (ξ _).2.1, Finset.sum_const_zero, sub_zero]
    exact hf k
  have havg : avgB c r (F k) = 0 := by rw [avgB, inner_oneB, hintF, mul_zero]
  have hξl : ∀ᵐ z ∂(volume.restrict (euclBall c r)), ∀ l, fn (η l) z =
      ((((ξ l : H1B0 c r) : H1Amb c r) none : L2B c r) : (Fin 4 → ℝ) → ℝ) z := by
    rw [ae_all_iff]; exact hfn
  have hξd : ∀ᵐ z ∂(volume.restrict (euclBall c r)), ∀ l ν, fn (derS ν (η l)) z =
      ((((ξ l : H1B0 c r) : H1Amb c r) (some ν) : L2B c r) : (Fin 4 → ℝ) → ℝ) z := by
    rw [ae_all_iff]; intro l; rw [ae_all_iff]; exact hder l
  filter_upwards [fn_linOpS A η k, hlap k, hFk, hξl, hξd] with z e1 e2 e3 e4 e5
  rw [e1, e2]
  simp only [solRhs, havg, sub_zero, e3, e4, e5]
  simp only [divData]
  ring

end Existence

end RenewalGeometry.BallAnalysis.BallAlg
