/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.IteratedDerivBounds

/-!
# Uniform derivative bounds: Faà di Bruno composition, the derivative bootstrap and inversion
  (infrastructure for `lem:supp-initial-calculus`, `lem:supp-initial-range`,
  `thm:supp-action-prepared-chart`; emergent-spacetime manuscript)

All statements are in arbitrary real normed spaces, with **explicit constants** that depend only
on the displayed data, so that a family of maps (e.g. indexed by the cutoff) with uniform input
constants gets uniform output constants.  `DerivBound f U K M` is the predicate of
`IteratedDerivBounds.lean` (`f` is `C^∞` on `U` and `‖D^k f‖ ≤ M` on `U` for `k ≤ K`).

* `derivBound_comp` (**Faà di Bruno**): if `DerivBound g V K M_g`, `DerivBound f U K M_f` and
  `f(U) ⊆ V` (`U`, `V` open), then `DerivBound (g ∘ f) U K (K! M_g max(1, M_f)^K)`
  (Mathlib's `norm_iteratedFDerivWithin_comp_le`).
* `derivBound_congrOn`, `derivBound_of_fderiv`: congruence on an open set; a bound on `Df` up to
  order `K` and on `f` give a bound on `f` up to order `K + 1`.
* `derivBound_of_hasFDerivAt_eq` (**derivative bootstrap**): if `f` is differentiable on an open
  bounded set `U ⊆ B̄(0, R)` with `Df(x) = Ψ(x, f x)`, where `DerivBound Ψ V K M_Ψ` on an open
  `V ∋ (x, f x)`, and `‖f‖ ≤ M₀` on `U`, then `f` is `C^∞` on `U` and
  `DerivBound f U (K + 1) (bootC M_Ψ M₀ R (K + 1))`, with the explicit recursive constants `bootC`.
* `norm_inverse_le_two`, `hasFDerivAt_inverse_of_norm_sub_one_lt`, `derivBound_inverse`: in a
  complete normed algebra with `‖1‖ ≤ 1`, `Ring.inverse` satisfies `‖S⁻¹‖ ≤ 2` and
  `DerivBound Ring.inverse (B(1, ½)) K (invC K)` with an explicit constant (bootstrap of
  `D(S⁻¹) = -S⁻¹ (·) S⁻¹`).
* `norm_fderiv_sub_le_of_derivBound`, `norm_fderiv_fderiv_sub_le_of_derivBound`: Lipschitz bounds
  of `Df` and `D²f` on convex sets from bounds of order `2` and `3`.
-/

open Set Filter Topology Metric
open scoped ContDiff Nat

namespace RenewalGeometry.UniformDerivBounds

open IteratedDerivBounds

noncomputable section

set_option linter.unusedSectionVars false

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-! ### Composition, congruence, and one more derivative -/

/-- **Faà di Bruno composition bound.** -/
theorem derivBound_comp {g : F → G} {f : E → F} {U : Set E} {V : Set F} {K : ℕ} {Mg Mf : ℝ}
    (hg : DerivBound g V K Mg) (hV : IsOpen V) (hf : DerivBound f U K Mf) (hU : IsOpen U)
    (hmaps : MapsTo f U V) :
    DerivBound (fun x => g (f x)) U K (K ! * Mg * max 1 Mf ^ K) := by
  refine ⟨hg.contDiffOn.comp hf.contDiffOn hmaps, fun x hx k hk => ?_⟩
  have hMg : 0 ≤ Mg := hg.nonneg (hmaps hx)
  have hD1 : (1 : ℝ) ≤ max 1 Mf := le_max_left _ _
  have h := norm_iteratedFDerivWithin_comp_le (n := k) (N := ∞) hg.contDiffOn hf.contDiffOn
    (by exact_mod_cast le_top) hV.uniqueDiffOn hU.uniqueDiffOn hmaps hx (C := Mg)
    (D := max 1 Mf)
    (fun i hi => by
      rw [iteratedFDerivWithin_of_isOpen i hV (hmaps hx)]
      exact hg.bound _ (hmaps hx) i (hi.trans hk))
    (fun i hi1 hi => by
      rw [iteratedFDerivWithin_of_isOpen i hU hx]
      refine (hf.bound x hx i (hi.trans hk)).trans ?_
      calc Mf ≤ max 1 Mf := le_max_right _ _
        _ = max 1 Mf ^ 1 := (pow_one _).symm
        _ ≤ max 1 Mf ^ i := pow_le_pow_right₀ hD1 hi1)
  rw [iteratedFDerivWithin_of_isOpen k hU hx] at h
  refine h.trans ?_
  have hfac : (k ! : ℝ) ≤ K ! := by exact_mod_cast Nat.factorial_le hk
  have hpow : max 1 Mf ^ k ≤ max 1 Mf ^ K := pow_le_pow_right₀ hD1 hk
  have h0 : (0 : ℝ) ≤ max 1 Mf ^ k := by positivity
  have h0' : (0 : ℝ) ≤ (k ! : ℝ) := by positivity
  calc (k ! : ℝ) * Mg * max 1 Mf ^ k ≤ K ! * Mg * max 1 Mf ^ K := by gcongr

/-- Congruence on an open set. -/
theorem derivBound_congrOn {f g : E → F} {U : Set E} {K : ℕ} {M : ℝ} (h : DerivBound f U K M)
    (hU : IsOpen U) (hfg : ∀ x ∈ U, f x = g x) : DerivBound g U K M := by
  refine ⟨h.contDiffOn.congr fun x hx => (hfg x hx).symm, fun x hx k hk => ?_⟩
  have heq : f =ᶠ[𝓝 x] g := Filter.eventually_of_mem (hU.mem_nhds hx) hfg
  rw [← (heq.iteratedFDeriv ℝ k).eq_of_nhds]
  exact h.bound x hx k hk

/-- Bounds on `Df` up to order `K` and on `f` give bounds on `f` up to order `K + 1`. -/
theorem derivBound_of_fderiv {f : E → F} {U : Set E} {K : ℕ} {M₀ M₁ : ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hf0 : ∀ x ∈ U, ‖f x‖ ≤ M₀)
    (hd : DerivBound (fderiv ℝ f) U K M₁) : DerivBound f U (K + 1) (max M₀ M₁) := by
  refine ⟨hf, fun x hx k hk => ?_⟩
  rcases k with _ | k
  · rw [norm_iteratedFDeriv_zero]; exact (hf0 x hx).trans (le_max_left _ _)
  · rw [← norm_iteratedFDeriv_fderiv]
    exact (hd.bound x hx k (by omega)).trans (le_max_right _ _)

/-- The graph map `x ↦ (x, f x)` on a bounded set. -/
theorem derivBound_graph {f : E → F} {U : Set E} {K : ℕ} {M R : ℝ} (hf : DerivBound f U K M)
    (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ closedBall 0 R) (hM : 0 ≤ M) :
    DerivBound (fun x => (x, f x)) U K (max 1 R + M) := by
  have hid : DerivBound (fun x => ContinuousLinearMap.id ℝ E x) U K (max 1 R) := by
    refine (DerivBound.clm (ContinuousLinearMap.id ℝ E) hR hUR K).mono le_rfl ?_
    calc ‖ContinuousLinearMap.id ℝ E‖ * max 1 R ≤ 1 * max 1 R :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_id_le) (by positivity)
      _ = max 1 R := one_mul _
  exact hid.prod hf hU (by positivity) hM

/-! ### The derivative bootstrap -/

/-- The explicit constants of the derivative bootstrap. -/
def bootC (MΨ M₀ R : ℝ) : ℕ → ℝ
  | 0 => M₀
  | k + 1 => max (bootC MΨ M₀ R k) (k ! * MΨ * max 1 (max 1 R + bootC MΨ M₀ R k) ^ k)

theorem bootC_le_succ (MΨ M₀ R : ℝ) (k : ℕ) : bootC MΨ M₀ R k ≤ bootC MΨ M₀ R (k + 1) :=
  le_max_left _ _

theorem bootC_mono (MΨ M₀ R : ℝ) : Monotone (bootC MΨ M₀ R) :=
  monotone_nat_of_le_succ (bootC_le_succ MΨ M₀ R)

theorem le_bootC (MΨ M₀ R : ℝ) (k : ℕ) : M₀ ≤ bootC MΨ M₀ R k :=
  bootC_mono MΨ M₀ R (Nat.zero_le k)

/-- **Derivative bootstrap.**  If `Df(x) = Ψ(x, f x)` on an open set `U ⊆ B̄(0, R)`, where `Ψ`
has derivative bounds of order `K` on an open set containing the graph, and `‖f‖ ≤ M₀` on `U`,
then `f` is `C^∞` on `U` with explicit derivative bounds of order `K + 1`. -/
theorem derivBound_of_hasFDerivAt_eq {f : E → F} {U : Set E} (hU : IsOpen U) {R : ℝ}
    (hR : 0 ≤ R) (hUR : U ⊆ closedBall 0 R) {V : Set (E × F)} (hV : IsOpen V)
    {Ψ : E × F → (E →L[ℝ] F)} {K : ℕ} {MΨ M₀ : ℝ} (hΨ : DerivBound Ψ V K MΨ)
    (hmaps : ∀ x ∈ U, (x, f x) ∈ V) (hf : ∀ x ∈ U, HasFDerivAt f (Ψ (x, f x)) x)
    (hf0 : ∀ x ∈ U, ‖f x‖ ≤ M₀) (hM₀ : 0 ≤ M₀) :
    DerivBound f U (K + 1) (bootC MΨ M₀ R (K + 1)) := by
  -- smoothness
  have hcont : ContDiffOn ℝ ∞ f U := by
    rw [contDiffOn_infty]
    intro n
    induction n with
    | zero =>
      exact contDiffOn_zero.2 fun x hx => (hf x hx).continuousAt.continuousWithinAt
    | succ n ih =>
      have e : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
      rw [e, contDiffOn_succ_iff_fderiv_of_isOpen hU]
      refine ⟨fun x hx => (hf x hx).differentiableAt.differentiableWithinAt, ?_, ?_⟩
      · intro h; exact absurd h (by simp)
      · have hpair : ContDiffOn ℝ n (fun x => (x, f x)) U := contDiffOn_id.prodMk ih
        have hcomp : ContDiffOn ℝ n (fun x => Ψ (x, f x)) U :=
          (hΨ.contDiffOn.of_le (by exact_mod_cast le_top)).comp hpair fun x hx => hmaps x hx
        exact hcomp.congr fun x hx => (hf x hx).fderiv
  have hM : ∀ k, 0 ≤ bootC MΨ M₀ R k := fun k => hM₀.trans (le_bootC MΨ M₀ R k)
  have key : ∀ k, k ≤ K + 1 → DerivBound f U k (bootC MΨ M₀ R k) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨hcont, fun x hx j hj => ?_⟩
      obtain rfl : j = 0 := Nat.le_zero.mp hj
      rw [norm_iteratedFDeriv_zero]
      exact hf0 x hx
    | succ k ih =>
      intro hk
      have hk' : k ≤ K := by omega
      have h1 := ih (by omega)
      have h2 := derivBound_graph h1 hU hR hUR (hM k)
      have h3 := derivBound_comp (hΨ.mono hk' le_rfl) hV h2 hU fun x hx => hmaps x hx
      have h4 : DerivBound (fderiv ℝ f) U k _ :=
        derivBound_congrOn h3 hU fun x hx => (hf x hx).fderiv.symm
      have h5 := derivBound_of_fderiv hcont hf0 h4
      refine h5.mono le_rfl ?_
      exact max_le ((le_bootC MΨ M₀ R k).trans (le_max_left _ _)) (le_max_right _ _)
  exact key (K + 1) le_rfl

/-! ### Lipschitz bounds of `Df`, `D²f` -/

/-- `Df` is `M`-Lipschitz on a convex open set where `‖D²f‖ ≤ M`. -/
theorem norm_fderiv_sub_le_of_derivBound {f : E → F} {U : Set E} {K : ℕ} {M : ℝ}
    (hf : DerivBound f U (K + 2) M) (hU : IsOpen U) (hc : Convex ℝ U) {x y : E} (hx : x ∈ U)
    (hy : y ∈ U) : ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ M * ‖x - y‖ := by
  have h1 : DerivBound (fderiv ℝ f) U (K + 1) M := hf.fderiv hU
  exact hc.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (h1.contDiffAt hU hz).differentiableAt (by simp))
    (fun z hz => h1.norm_fderiv_le (by omega) hz) hy hx

/-- `D²f` is `M`-Lipschitz on a convex open set where `‖D³f‖ ≤ M`. -/
theorem norm_fderiv_fderiv_sub_le_of_derivBound {f : E → F} {U : Set E} {K : ℕ} {M : ℝ}
    (hf : DerivBound f U (K + 3) M) (hU : IsOpen U) (hc : Convex ℝ U) {x y : E} (hx : x ∈ U)
    (hy : y ∈ U) : ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ M * ‖x - y‖ :=
  norm_fderiv_sub_le_of_derivBound (hf.fderiv hU) hU hc hx hy

/-- The second iterated derivative is `M`-Lipschitz on a convex open set where `‖D³f‖ ≤ M`
(stated with `iteratedFDeriv`, so that no operator norm on nested continuous linear maps is
needed, e.g. on subspaces). -/
theorem norm_iteratedFDeriv_two_sub_le_of_derivBound {f : E → F} {U : Set E} {K : ℕ} {M : ℝ}
    (hf : DerivBound f U (K + 3) M) (hU : IsOpen U) (hc : Convex ℝ U) {x y : E} (hx : x ∈ U)
    (hy : y ∈ U) : ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ ≤ M * ‖x - y‖ := by
  have hdiffW : DifferentiableOn ℝ (iteratedFDerivWithin ℝ 2 f U) U :=
    hf.contDiffOn.differentiableOn_iteratedFDerivWithin
      (by
        show ((2 : ℕ∞) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_lt_coe.2 (ENat.natCast_lt_top 2))
      hU.uniqueDiffOn
  have hd : ∀ z ∈ U, DifferentiableAt ℝ (iteratedFDeriv ℝ 2 f) z := by
    intro z hz
    have h1 : DifferentiableAt ℝ (iteratedFDerivWithin ℝ 2 f U) z :=
      hdiffW.differentiableAt (hU.mem_nhds hz)
    have heq : iteratedFDerivWithin ℝ 2 f U =ᶠ[𝓝 z] iteratedFDeriv ℝ 2 f :=
      Filter.eventually_of_mem (hU.mem_nhds hz) fun w hw => iteratedFDerivWithin_of_isOpen 2 hU hw
    exact h1.congr_of_eventuallyEq heq.symm
  exact hc.norm_image_sub_le_of_norm_fderiv_le hd
    (fun z hz => by
      rw [norm_fderiv_iteratedFDeriv]
      exact hf.bound z hz 3 (by omega)) hy hx

/-! ### Inversion near the identity -/

section Inverse

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]

local notation "𝔄" => Z →L[ℝ] Z

theorem norm_one_endo_le : ‖(1 : 𝔄)‖ ≤ 1 := ContinuousLinearMap.norm_id_le

theorem exists_unit_of_norm_sub_one_lt {S : 𝔄} (hS : ‖S - 1‖ < 1) : ∃ u : 𝔄ˣ, (u : 𝔄) = S :=
  ⟨Units.oneSub (1 - S) (by rwa [norm_sub_rev]), by simp⟩

/-- `‖S⁻¹‖ ≤ 2` for `‖S - 1‖ ≤ ½` (in a complete normed algebra with `‖1‖ ≤ 1`). -/
theorem norm_inverse_le_two {S : 𝔄} (hS : ‖S - 1‖ ≤ 1 / 2) :
    ‖Ring.inverse S‖ ≤ 2 := by
  obtain ⟨u, rfl⟩ := exists_unit_of_norm_sub_one_lt (S := S) (by linarith)
  rw [Ring.inverse_unit]
  set w : 𝔄 := ((u⁻¹ : 𝔄ˣ) : 𝔄) with hwdef
  have huw : (u : 𝔄) * w = 1 := u.mul_inv
  have hw : w = 1 + (1 - (u : 𝔄)) * w := by
    calc w = (u : 𝔄) * w + (1 - (u : 𝔄)) * w := by rw [sub_mul, one_mul]; abel
      _ = 1 + (1 - (u : 𝔄)) * w := by rw [huw]
  have hs : ‖1 - (u : 𝔄)‖ ≤ 1 / 2 := by rwa [norm_sub_rev]
  have h2 : ‖w‖ ≤ 1 + 1 / 2 * ‖w‖ := by
    calc ‖w‖ = ‖1 + (1 - (u : 𝔄)) * w‖ := by rw [← hw]
      _ ≤ ‖(1 : 𝔄)‖ + ‖(1 - (u : 𝔄)) * w‖ := norm_add_le _ _
      _ ≤ 1 + ‖1 - (u : 𝔄)‖ * ‖w‖ := add_le_add norm_one_endo_le (norm_mul_le _ _)
      _ ≤ 1 + 1 / 2 * ‖w‖ := by gcongr
  linarith

/-- The derivative of `Ring.inverse` near `1`: `D(S⁻¹) = -S⁻¹ (·) S⁻¹`. -/
theorem hasFDerivAt_inverse_of_norm_sub_one_lt {S : 𝔄} (hS : ‖S - 1‖ < 1) :
    HasFDerivAt Ring.inverse
      (-(ContinuousLinearMap.mulLeftRight ℝ 𝔄 (Ring.inverse S) (Ring.inverse S))) S := by
  obtain ⟨u, rfl⟩ := exists_unit_of_norm_sub_one_lt hS
  rw [Ring.inverse_unit]
  exact hasFDerivAt_ringInverse u

/-- The constant of `derivBound_inverse`. -/
def invC (K : ℕ) : ℝ := bootC (2 ^ K * 3 * 3) 2 (3 / 2) (K + 1)

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 1024 in
/-- **Uniform derivative bounds for inversion** on the ball `B(1, ½)`. -/
theorem derivBound_inverse (K : ℕ) :
    DerivBound (Ring.inverse : 𝔄 → 𝔄) (ball 1 (1 / 2)) (K + 1) (invC K) := by
  have hB : ‖ContinuousLinearMap.mulLeftRight ℝ 𝔄‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_mulLeftRight_le ℝ 𝔄
  have hsnd : DerivBound (fun p : 𝔄 × 𝔄 => ContinuousLinearMap.snd ℝ 𝔄 𝔄 p) (ball 0 3) K 3 := by
    refine (DerivBound.clm _ (by norm_num : (0 : ℝ) ≤ 3) ball_subset_closedBall K).mono le_rfl ?_
    have hs : ‖ContinuousLinearMap.snd ℝ 𝔄 𝔄‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ℝ 𝔄 𝔄
    have hm : max (1 : ℝ) 3 = 3 := by norm_num
    rw [hm]
    nlinarith [norm_nonneg (ContinuousLinearMap.snd ℝ 𝔄 𝔄)]
  have hΨ := (DerivBound.bilinear (H := 𝔄 →L[ℝ] 𝔄) hsnd hsnd isOpen_ball
    (ContinuousLinearMap.mulLeftRight ℝ 𝔄) (by norm_num) (by norm_num)).neg
  have hΨ' : DerivBound (fun p : 𝔄 × 𝔄 =>
      -(ContinuousLinearMap.mulLeftRight ℝ 𝔄 p.2 p.2)) (ball 0 3) K (2 ^ K * 3 * 3) := by
    refine hΨ.mono le_rfl ?_
    have h0 : 0 ≤ (2 : ℝ) ^ K * 3 * 3 := by positivity
    have : ‖ContinuousLinearMap.mulLeftRight ℝ 𝔄‖ * 2 ^ K * 3 * 3 =
        ‖ContinuousLinearMap.mulLeftRight ℝ 𝔄‖ * (2 ^ K * 3 * 3) := by ring
    rw [this]
    nlinarith [norm_nonneg (ContinuousLinearMap.mulLeftRight ℝ 𝔄)]
  have hnS : ∀ S ∈ ball (1 : 𝔄) (1 / 2), ‖S‖ ≤ 3 / 2 := by
    intro S hS
    rw [mem_ball, dist_eq_norm] at hS
    calc ‖S‖ = ‖(S - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖S - 1‖ + ‖(1 : 𝔄)‖ := norm_add_le _ _
      _ ≤ 3 / 2 := by linarith [norm_one_endo_le (Z := Z)]
  refine derivBound_of_hasFDerivAt_eq isOpen_ball (R := 3 / 2) (by norm_num) ?_ isOpen_ball hΨ'
    ?_ ?_ ?_ (by norm_num)
  · intro S hS
    exact mem_closedBall_zero_iff.mpr (hnS S hS)
  · intro S hS
    have hS' : ‖S - 1‖ ≤ 1 / 2 := by rw [mem_ball, dist_eq_norm] at hS; exact hS.le
    rw [mem_ball_zero_iff, Prod.norm_def]
    refine max_lt ?_ ?_
    · linarith [hnS S hS]
    · linarith [norm_inverse_le_two hS']
  · intro S hS
    have hS' : ‖S - 1‖ < 1 := by
      rw [mem_ball, dist_eq_norm] at hS; linarith
    exact hasFDerivAt_inverse_of_norm_sub_one_lt hS'
  · intro S hS
    have hS' : ‖S - 1‖ ≤ 1 / 2 := by rw [mem_ball, dist_eq_norm] at hS; exact hS.le
    exact norm_inverse_le_two hS'

end Inverse

end

end RenewalGeometry.UniformDerivBounds
