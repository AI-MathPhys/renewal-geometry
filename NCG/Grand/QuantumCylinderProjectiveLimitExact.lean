/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SMSTReflectionPositivityExact

/-!
# Summable cutoff correction and reflection-positive projective limit

Machinery for `thm:SMST-quantum-projective-limit` (QRP.6) on the finite oriented quantum
cylinders of `def:SMST-quantum-cylinder`: finite cylinder sets `Ω n`, cutoff maps
`π n : Ω (n+1) → Ω n`, probability vectors `μ n`, and the total-variation defects
`δ n = ‖(π n)_* μ (n+1) - μ n‖_TV`.

* `tv` is the total-variation norm `∑ |σ ω|`; `tv_isGreatest` identifies it with
  `sup_{‖f‖∞ ≤ 1} |∑ f σ|`;
* `push` is the pushforward of a weight vector, `tv_push_le` its `1`-Lipschitz property;
* `πLe h : Ω n → Ω m` (`m ≤ n`) is the composed cutoff map;
* `marg m n = (π_{n,m})_* μ n` viewed in `ℓ¹(Ω m)`; summable defects make it Cauchy
  (`cauchySeq_marg`) with limit `limMarg m`, a probability vector
  (`limMarg_nonneg`, `sum_limMarg`), exactly projectively compatible (`push_limMarg`),
  and with the boxed bound `‖μ̄_m - μ_m‖_TV ≤ ∑_{j ≥ m} δ_j` (`tv_limMarg_le`, QRP.6);
* `limMarg_reflection_positive`: if every `μ n` is reflection positive on a positive-time
  algebra pulled back along reflection-equivariant cutoff maps, every limit marginal is
  reflection positive on the corresponding finite positive-time algebra.
-/

open Filter Topology Finset
open NCG.SMSTReflectionPositivity
open scoped ComplexOrder

namespace NCG
namespace QuantumCylinderProjectiveLimit

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-! ### Total variation on a finite cylinder -/

/-- The total-variation norm of a signed weight on a finite cylinder. -/
def tv {Ω : Type*} [Fintype Ω] (σ : Ω → ℝ) : ℝ := ∑ ω, |σ ω|

theorem tv_nonneg {Ω : Type*} [Fintype Ω] (σ : Ω → ℝ) : 0 ≤ tv σ :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem tv_sub_comm {Ω : Type*} [Fintype Ω] (u v : Ω → ℝ) : tv (u - v) = tv (v - u) := by
  unfold tv
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp [abs_sub_comm]

/-- `|∑ f σ| ≤ ‖σ‖_TV` for `‖f‖∞ ≤ 1`. -/
theorem abs_sum_le_tv {Ω : Type*} [Fintype Ω] (σ f : Ω → ℝ) (hf : ∀ ω, |f ω| ≤ 1) :
    |∑ ω, f ω * σ ω| ≤ tv σ := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ω _ => ?_)
  rw [abs_mul]
  calc |f ω| * |σ ω| ≤ 1 * |σ ω| := mul_le_mul_of_nonneg_right (hf ω) (abs_nonneg _)
    _ = |σ ω| := one_mul _

/-- The sign function attains the total variation. -/
theorem sum_sign_mul {Ω : Type*} [Fintype Ω] (σ : Ω → ℝ) :
    ∑ ω, SignType.sign (σ ω) * σ ω = tv σ := by
  unfold tv
  refine Finset.sum_congr rfl fun ω _ => ?_
  rcases lt_trichotomy (σ ω) 0 with h | h | h
  · rw [sign_neg h, abs_of_neg h]; simp
  · rw [h]; simp
  · rw [sign_pos h, abs_of_pos h]; simp

theorem abs_sign_le_one (x : ℝ) : |((SignType.sign x : SignType) : ℝ)| ≤ 1 := by
  cases SignType.sign x <;> simp

/-- **Total variation as a supremum**: `‖σ‖_TV = sup_{‖f‖∞ ≤ 1} |∑ f σ|`. -/
theorem tv_isGreatest {Ω : Type*} [Fintype Ω] (σ : Ω → ℝ) :
    IsGreatest {x | ∃ f : Ω → ℝ, (∀ ω, |f ω| ≤ 1) ∧ x = |∑ ω, f ω * σ ω|} (tv σ) := by
  refine ⟨⟨fun ω => SignType.sign (σ ω), fun ω => abs_sign_le_one _, ?_⟩, ?_⟩
  · rw [sum_sign_mul, abs_of_nonneg (tv_nonneg σ)]
  · rintro x ⟨f, hf, rfl⟩
    exact abs_sum_le_tv σ f hf

/-! ### Pushforward of weights -/

/-- The pushforward of a weight vector along a map between finite cylinders. -/
def push {A B : Type*} [Fintype A] [DecidableEq B] (f : A → B) (v : A → ℝ) : B → ℝ :=
  fun b => ∑ a ∈ univ.filter (fun a => f a = b), v a

theorem push_id {A : Type*} [Fintype A] [DecidableEq A] (v : A → ℝ) : push id v = v := by
  funext b
  simp [push, Finset.filter_eq']

theorem push_comp {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [DecidableEq C] (f : A → B) (g : B → C) (v : A → ℝ) :
    push g (push f v) = push (g ∘ f) v := by
  funext c
  simp only [push, Function.comp]
  rw [← Finset.sum_biUnion]
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext a
    simp
  · intro b _ b' _ hbb'
    rw [Function.onFun, Finset.disjoint_left]
    intro a ha ha'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ha'
    exact hbb' (ha ▸ ha')

theorem push_sub {A B : Type*} [Fintype A] [DecidableEq B] (f : A → B) (u v : A → ℝ) :
    push f (u - v) = push f u - push f v := by
  funext b
  simp [push, Finset.sum_sub_distrib]

theorem sum_push {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B] (f : A → B) (v : A → ℝ) :
    ∑ b, push f v b = ∑ a, v a := by
  unfold push
  exact Finset.sum_fiberwise _ _ _

theorem push_nonneg {A B : Type*} [Fintype A] [DecidableEq B] (f : A → B) {v : A → ℝ}
    (hv : ∀ a, 0 ≤ v a) (b : B) : 0 ≤ push f v b :=
  Finset.sum_nonneg fun a _ => hv a

/-- The pushforward is `1`-Lipschitz for total variation. -/
theorem tv_push_le {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B] (f : A → B)
    (σ : A → ℝ) : tv (push f σ) ≤ tv σ := by
  unfold tv push
  calc ∑ b, |∑ a ∈ univ.filter (fun a => f a = b), σ a|
      ≤ ∑ b, ∑ a ∈ univ.filter (fun a => f a = b), |σ a| :=
        Finset.sum_le_sum fun b _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a, |σ a| := Finset.sum_fiberwise _ _ _

/-- The pushforward of a reflection-invariant weight along an equivariant map is invariant. -/
theorem push_reflection_invariant {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (f : A → B) (θA : A → A) (θB : B → B) (hθA : ∀ a, θA (θA a) = a) (hθB : ∀ b, θB (θB b) = b)
    (hθ : ∀ a, f (θA a) = θB (f a)) (v : A → ℝ) (hv : ∀ a, v (θA a) = v a) (b : B) :
    push f v (θB b) = push f v b := by
  unfold push
  have hbij : ∀ a ∈ univ.filter (fun a => f a = b), θA a ∈ univ.filter (fun a => f a = θB b) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [hθ, ha]
  symm
  refine Finset.sum_nbij θA hbij ?_ ?_ ?_
  · intro a _ a' _ h
    have := congrArg θA h
    rwa [hθA, hθA] at this
  · intro a' ha'
    simp only [Finset.mem_univ, true_and, Finset.coe_filter, Set.mem_setOf_eq,
      Set.mem_image] at ha' ⊢
    refine ⟨θA a', ?_, hθA a'⟩
    rw [hθ, ha', hθB]
  · intro a _
    rw [hv]

/-! ### The cutoff tower -/

variable {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)] [∀ n, DecidableEq (Ω n)]

/-- The composed cutoff map `π_{n,m} : Ω n → Ω m` for `m ≤ n`. -/
def πLe (π : ∀ n, Ω (n + 1) → Ω n) {m n : ℕ} (h : m ≤ n) : Ω n → Ω m :=
  Nat.leRecOn (C := fun k => Ω k → Ω m) h (fun {k} g => g ∘ π k) id

theorem πLe_self (π : ∀ n, Ω (n + 1) → Ω n) (m : ℕ) : πLe π (le_refl m) = id :=
  Nat.leRecOn_self _

theorem πLe_succ (π : ∀ n, Ω (n + 1) → Ω n) {m n : ℕ} (h1 : m ≤ n) (h2 : m ≤ n + 1) :
    πLe π h2 = πLe π h1 ∘ π n :=
  Nat.leRecOn_succ h1 _

/-- Left peeling: `π_{n,m} = π_m ∘ π_{n,m+1}`. -/
theorem πLe_succ_left (π : ∀ n, Ω (n + 1) → Ω n) (m : ℕ) :
    ∀ n (h2 : m + 1 ≤ n), πLe π (le_trans (Nat.le_succ m) h2) = π m ∘ πLe π h2 := by
  intro n h2
  induction n, h2 using Nat.le_induction with
  | base =>
    rw [πLe_succ π (le_refl m), πLe_self, πLe_self]
    rfl
  | succ n hmn ih =>
    rw [πLe_succ π (le_trans (Nat.le_succ m) hmn), πLe_succ π hmn, ih]
    rfl

/-- Reflection equivariance of the cutoff maps passes to the composed maps. -/
theorem πLe_equivariant (π : ∀ n, Ω (n + 1) → Ω n) (θ : ∀ n, Ω n → Ω n)
    (hθ : ∀ n ω, π n (θ (n + 1) ω) = θ n (π n ω)) (m : ℕ) :
    ∀ n (h : m ≤ n) (ω : Ω n), πLe π h (θ n ω) = θ m (πLe π h ω) := by
  intro n h ω
  induction n, h using Nat.le_induction with
  | base => rw [πLe_self]; rfl
  | succ n hmn ih =>
    rw [πLe_succ π hmn, Function.comp_apply, Function.comp_apply, hθ, ih]

/-- The total-variation defect `δ n = ‖(π n)_* μ (n+1) - μ n‖_TV`. -/
def defect (π : ∀ n, Ω (n + 1) → Ω n) (μ : ∀ n, Ω n → ℝ) (n : ℕ) : ℝ :=
  tv (push (π n) (μ (n + 1)) - μ n)

theorem defect_nonneg (π : ∀ n, Ω (n + 1) → Ω n) (μ : ∀ n, Ω n → ℝ) (n : ℕ) :
    0 ≤ defect π μ n := tv_nonneg _

/-- The pushed marginal `(π_{n,m})_* μ n` on `Ω m` (for `n ≥ m`; `μ m` itself for `n < m`),
as a point of `ℓ¹(Ω m)`. -/
noncomputable def marg (π : ∀ n, Ω (n + 1) → Ω n) (μ : ∀ n, Ω n → ℝ) (m n : ℕ) :
    PiLp 1 (fun _ : Ω m => ℝ) :=
  if h : m ≤ n then WithLp.toLp 1 (push (πLe π h) (μ n)) else WithLp.toLp 1 (μ m)

theorem marg_of_le (π : ∀ n, Ω (n + 1) → Ω n) (μ : ∀ n, Ω n → ℝ) {m n : ℕ} (h : m ≤ n) :
    marg π μ m n = WithLp.toLp 1 (push (πLe π h) (μ n)) := dif_pos h

theorem marg_of_lt (π : ∀ n, Ω (n + 1) → Ω n) (μ : ∀ n, Ω n → ℝ) {m n : ℕ} (h : n < m) :
    marg π μ m n = WithLp.toLp 1 (μ m) := dif_neg (not_le.mpr h)

theorem marg_self (π : ∀ n, Ω (n + 1) → Ω n) (μ : ∀ n, Ω n → ℝ) (m : ℕ) :
    marg π μ m m = WithLp.toLp 1 (μ m) := by
  rw [marg_of_le π μ (le_refl m), πLe_self, push_id]

/-- The `ℓ¹` distance is the total variation. -/
theorem dist_toLp_eq_tv {A : Type*} [Fintype A] (u v : A → ℝ) :
    dist (WithLp.toLp 1 u : PiLp 1 (fun _ : A => ℝ)) (WithLp.toLp 1 v) = tv (u - v) := by
  rw [PiLp.dist_eq_of_L1]
  unfold tv
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Real.dist_eq]

/-- Adjacent pushed marginals differ by at most the defect. -/
theorem dist_marg_succ (π : ∀ n, Ω (n + 1) → Ω n) (μ : ∀ n, Ω n → ℝ) (m n : ℕ) :
    dist (marg π μ m n) (marg π μ m (n + 1)) ≤ defect π μ n := by
  rcases le_or_gt m n with h | h
  · rw [marg_of_le π μ h, marg_of_le π μ (le_trans h (Nat.le_succ n)), dist_toLp_eq_tv,
      πLe_succ π h, ← push_comp, ← push_sub]
    exact (tv_push_le _ _).trans (le_of_eq (tv_sub_comm _ _))
  · rcases lt_or_eq_of_le (Nat.succ_le_of_lt h) with h' | h'
    · rw [marg_of_lt π μ h, marg_of_lt π μ h', dist_self]
      exact defect_nonneg π μ n
    · subst h'
      rw [marg_of_lt π μ h, marg_self, dist_self]
      exact defect_nonneg π μ n

/-- Summable defects make the pushed marginals Cauchy. -/
theorem cauchySeq_marg (π : ∀ n, Ω (n + 1) → Ω n) (μ : ∀ n, Ω n → ℝ)
    (hδ : Summable (defect π μ)) (m : ℕ) : CauchySeq (marg π μ m) :=
  cauchySeq_of_dist_le_of_summable (defect π μ) (dist_marg_succ π μ m) hδ

/-- The limit marginal `μ̄_m`. -/
noncomputable def limMarg (π : ∀ n, Ω (n + 1) → Ω n) (μ : ∀ n, Ω n → ℝ)
    (hδ : Summable (defect π μ)) (m : ℕ) : PiLp 1 (fun _ : Ω m => ℝ) :=
  Classical.choose (cauchySeq_tendsto_of_complete (cauchySeq_marg π μ hδ m))

theorem tendsto_marg (π : ∀ n, Ω (n + 1) → Ω n) (μ : ∀ n, Ω n → ℝ)
    (hδ : Summable (defect π μ)) (m : ℕ) :
    Tendsto (marg π μ m) atTop (𝓝 (limMarg π μ hδ m)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete (cauchySeq_marg π μ hδ m))

/-- **(QRP.6)**: `‖μ̄_m - μ_m‖_TV ≤ ∑_{j ≥ m} δ_j`. -/
theorem tv_limMarg_le (π : ∀ n, Ω (n + 1) → Ω n) (μ : ∀ n, Ω n → ℝ)
    (hδ : Summable (defect π μ)) (m : ℕ) :
    tv (μ m - WithLp.ofLp (limMarg π μ hδ m)) ≤ ∑' j, defect π μ (m + j) := by
  have h := dist_le_tsum_of_dist_le_of_tendsto (defect π μ) (dist_marg_succ π μ m) hδ
    (tendsto_marg π μ hδ m) m
  rw [marg_self] at h
  calc tv (μ m - WithLp.ofLp (limMarg π μ hδ m))
      = dist (WithLp.toLp 1 (μ m) : PiLp 1 (fun _ : Ω m => ℝ)) (limMarg π μ hδ m) := by
        rw [← dist_toLp_eq_tv]
    _ ≤ ∑' j, defect π μ (m + j) := h

/-- Coordinates of the limit marginal are limits of the pushed coordinates. -/
theorem tendsto_marg_apply (π : ∀ n, Ω (n + 1) → Ω n) (μ : ∀ n, Ω n → ℝ)
    (hδ : Summable (defect π μ)) (m : ℕ) (ω : Ω m) :
    Tendsto (fun n => marg π μ m n ω) atTop (𝓝 (limMarg π μ hδ m ω)) :=
  ((PiLp.continuous_apply 1 _ ω).tendsto _).comp (tendsto_marg π μ hδ m)

theorem marg_apply_nonneg (π : ∀ n, Ω (n + 1) → Ω n) (μ : ∀ n, Ω n → ℝ)
    (hμ : ∀ n ω, 0 ≤ μ n ω) (m n : ℕ) (ω : Ω m) : 0 ≤ marg π μ m n ω := by
  rcases le_or_gt m n with h | h
  · rw [marg_of_le π μ h]
    exact push_nonneg _ (hμ n) ω
  · rw [marg_of_lt π μ h]
    exact hμ m ω

theorem sum_marg (π : ∀ n, Ω (n + 1) → Ω n) (μ : ∀ n, Ω n → ℝ)
    (hμ1 : ∀ n, ∑ ω, μ n ω = 1) (m n : ℕ) : ∑ ω, marg π μ m n ω = 1 := by
  rcases le_or_gt m n with h | h
  · rw [marg_of_le π μ h]
    change ∑ ω, push (πLe π h) (μ n) ω = 1
    rw [sum_push, hμ1]
  · rw [marg_of_lt π μ h]
    exact hμ1 m

/-- The limit marginal is nonnegative when the `μ n` are. -/
theorem limMarg_nonneg (π : ∀ n, Ω (n + 1) → Ω n) (μ : ∀ n, Ω n → ℝ)
    (hμ : ∀ n ω, 0 ≤ μ n ω) (hδ : Summable (defect π μ)) (m : ℕ) (ω : Ω m) :
    0 ≤ limMarg π μ hδ m ω :=
  ge_of_tendsto' (tendsto_marg_apply π μ hδ m ω) fun n => marg_apply_nonneg π μ hμ m n ω

/-- The limit marginal has total mass one when the `μ n` are probabilities. -/
theorem sum_limMarg (π : ∀ n, Ω (n + 1) → Ω n) (μ : ∀ n, Ω n → ℝ)
    (hμ1 : ∀ n, ∑ ω, μ n ω = 1) (hδ : Summable (defect π μ)) (m : ℕ) :
    ∑ ω, limMarg π μ hδ m ω = 1 := by
  have h : Tendsto (fun n => ∑ ω, marg π μ m n ω) atTop (𝓝 (∑ ω, limMarg π μ hδ m ω)) :=
    tendsto_finsetSum _ fun ω _ => tendsto_marg_apply π μ hδ m ω
  refine tendsto_nhds_unique h ?_
  simp_rw [sum_marg π μ hμ1 m]
  exact tendsto_const_nhds

/-- The pushforward, as a continuous map of `ℓ¹` spaces. -/
theorem continuous_push_toLp {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B] (f : A → B) :
    Continuous fun x : PiLp 1 (fun _ : A => ℝ) =>
      (WithLp.toLp 1 (push f (WithLp.ofLp x)) : PiLp 1 (fun _ : B => ℝ)) := by
  refine (PiLp.continuous_toLp 1 _).comp ?_
  refine continuous_pi fun b => ?_
  unfold push
  exact continuous_finsetSum _ fun a _ => (PiLp.continuous_apply 1 _ a)

/-- **Exact projective compatibility**: `(π m)_* μ̄_{m+1} = μ̄_m`. -/
theorem push_limMarg (π : ∀ n, Ω (n + 1) → Ω n) (μ : ∀ n, Ω n → ℝ)
    (hδ : Summable (defect π μ)) (m : ℕ) :
    push (π m) (WithLp.ofLp (limMarg π μ hδ (m + 1))) = WithLp.ofLp (limMarg π μ hδ m) := by
  have h1 : Tendsto (fun n => (WithLp.toLp 1 (push (π m) (WithLp.ofLp (marg π μ (m + 1) n))) :
      PiLp 1 (fun _ : Ω m => ℝ))) atTop
      (𝓝 (WithLp.toLp 1 (push (π m) (WithLp.ofLp (limMarg π μ hδ (m + 1)))))) :=
    ((continuous_push_toLp (π m)).tendsto _).comp (tendsto_marg π μ hδ (m + 1))
  have h2 : ∀ n, m + 1 ≤ n → (WithLp.toLp 1 (push (π m) (WithLp.ofLp (marg π μ (m + 1) n))) :
      PiLp 1 (fun _ : Ω m => ℝ)) = marg π μ m n := by
    intro n hn
    rw [marg_of_le π μ hn, marg_of_le π μ (le_trans (Nat.le_succ m) hn), WithLp.ofLp_toLp,
      push_comp, ← πLe_succ_left]
  have h3 : Tendsto (fun n => marg π μ m n) atTop
      (𝓝 (WithLp.toLp 1 (push (π m) (WithLp.ofLp (limMarg π μ hδ (m + 1)))))) := by
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop (m + 1)] with n hn
    exact h2 n hn
  have := tendsto_nhds_unique h3 (tendsto_marg π μ hδ m)
  have := congrArg WithLp.ofLp this
  simpa using this

/-! ### Reflection positivity of the limit marginals -/

/-- A tower of finite oriented quantum cylinders with reflection-equivariant cutoff maps. -/
structure CylinderTower (Ω : ℕ → Type*) where
  /-- the cutoff maps -/
  π : ∀ n, Ω (n + 1) → Ω n
  /-- the cylinders (reflections and weights) -/
  C : ∀ n, ReflectionCylinder (Ω n)
  /-- reflection equivariance of the cutoff maps -/
  equivariant : ∀ n ω, π n ((C (n + 1)).θ ω) = (C n).θ (π n ω)

variable (T : CylinderTower Ω)

/-- The weights of the tower. -/
def CylinderTower.μ : ∀ n, Ω n → ℝ := fun n => (T.C n).μ

/-- The pushed marginals are reflection invariant. -/
theorem marg_reflection_invariant (m n : ℕ) (ω : Ω m) :
    marg T.π T.μ m n ((T.C m).θ ω) = marg T.π T.μ m n ω := by
  rcases le_or_gt m n with h | h
  · rw [marg_of_le T.π T.μ h]
    change push (πLe T.π h) (T.μ n) ((T.C m).θ ω) = push (πLe T.π h) (T.μ n) ω
    exact push_reflection_invariant (πLe T.π h) (T.C n).θ (T.C m).θ (T.C n).θ_invol
      (T.C m).θ_invol (πLe_equivariant T.π (fun n => (T.C n).θ) T.equivariant m n h)
      (T.μ n) (T.C n).μ_inv ω
  · rw [marg_of_lt T.π T.μ h]
    exact (T.C m).μ_inv ω

/-- The pushed marginal as a reflection cylinder on `Ω m`. -/
noncomputable def margCylinder (m n : ℕ) : ReflectionCylinder (Ω m) where
  θ := (T.C m).θ
  θ_invol := (T.C m).θ_invol
  μ := WithLp.ofLp (marg T.π T.μ m n)
  μ_nonneg := marg_apply_nonneg T.π T.μ (fun n => (T.C n).μ_nonneg) m n
  μ_inv := marg_reflection_invariant T m n

/-- The limit marginal is reflection invariant. -/
theorem limMarg_reflection_invariant (hδ : Summable (defect T.π T.μ)) (m : ℕ) (ω : Ω m) :
    limMarg T.π T.μ hδ m ((T.C m).θ ω) = limMarg T.π T.μ hδ m ω := by
  have h1 := tendsto_marg_apply T.π T.μ hδ m ((T.C m).θ ω)
  have h2 := tendsto_marg_apply T.π T.μ hδ m ω
  simp_rw [marg_reflection_invariant T m _ ω] at h1
  exact tendsto_nhds_unique h1 h2

/-- The limit marginal as a reflection cylinder on `Ω m`. -/
noncomputable def limCylinder (hδ : Summable (defect T.π T.μ)) (m : ℕ) :
    ReflectionCylinder (Ω m) where
  θ := (T.C m).θ
  θ_invol := (T.C m).θ_invol
  μ := WithLp.ofLp (limMarg T.π T.μ hδ m)
  μ_nonneg := limMarg_nonneg T.π T.μ (fun n => (T.C n).μ_nonneg) hδ m
  μ_inv := limMarg_reflection_invariant T hδ m

/-- The OS form of the pushed marginals converges to that of the limit marginal. -/
theorem tendsto_osForm_margCylinder (hδ : Summable (defect T.π T.μ)) (m : ℕ) (F G : Ω m → ℂ) :
    Tendsto (fun n => osForm (margCylinder T m n) F G) atTop
      (𝓝 (osForm (limCylinder T hδ m) F G)) := by
  unfold osForm
  refine tendsto_finsetSum _ fun ω _ => ?_
  refine Tendsto.const_mul _ ?_
  exact (Complex.continuous_ofReal.tendsto _).comp (tendsto_marg_apply T.π T.μ hδ m ω)

/-- Each pushed marginal is reflection positive on a positive-time algebra pulled back along
the composed cutoff maps. -/
theorem margCylinder_reflection_positive (A : ∀ n, Set (Ω n → ℂ))
    (hpull : ∀ m n (h : m ≤ n), ∀ F ∈ A m, F ∘ πLe T.π h ∈ A n)
    (hRP : ∀ n, ReflectionPositiveOn (T.C n) (A n)) (m n : ℕ) :
    ReflectionPositiveOn (margCylinder T m n) (A m) := by
  rcases le_or_gt m n with h | h
  · refine pushforward_reflection_positive (T.C n) (margCylinder T m n) (πLe T.π h)
      (πLe_equivariant T.π (fun n => (T.C n).θ) T.equivariant m n h) ?_ (A m) (A n)
      (hpull m n h) (hRP n)
    intro x
    simp only [margCylinder, marg_of_le T.π T.μ h, WithLp.ofLp_toLp]
    rfl
  · have : margCylinder T m n = T.C m := by
      simp only [margCylinder, marg_of_lt T.π T.μ h, WithLp.ofLp_toLp]
      rfl
    rw [this]
    exact hRP m

/-- **Reflection positivity of the limit marginals.** -/
theorem limMarg_reflection_positive (hδ : Summable (defect T.π T.μ)) (A : ∀ n, Set (Ω n → ℂ))
    (hpull : ∀ m n (h : m ≤ n), ∀ F ∈ A m, F ∘ πLe T.π h ∈ A n)
    (hRP : ∀ n, ReflectionPositiveOn (T.C n) (A n)) (m : ℕ) :
    ReflectionPositiveOn (limCylinder T hδ m) (A m) := by
  intro F hF
  have hlim := tendsto_osForm_margCylinder T hδ m F F
  refine isClosed_Ici.mem_of_tendsto hlim (Eventually.of_forall fun n => ?_)
  exact margCylinder_reflection_positive T A hpull hRP m n F hF

end QuantumCylinderProjectiveLimit
end NCG
