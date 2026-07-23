/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.ClassicalAffinity

/-!
# The Curie–Weiss renewal orientation model: measure, channel, and
independence witnesses

Covers, from `manuscripts/renewal_emergence/renewal_emergence.tex`:

* `def:cw-renewal-measure` — the finite-volume orientation measure
  `μ_{N,λ,h}(η) ∝ exp(N(λ m²/2 + h m))`, deck invariant at zero
  field;
* `def:cw-heat-bath` — the single-cell heat-bath renewal channel
  with conditional weights `q_i(s|η_{-i})`;
* `prop:cw-quadratic-modular-weight` — the stationary log-density is
  the quadratic collective modular Hamiltonian
  `λ M²/(2N) + h M − log Z`, and the local modular ratio
  `log(q_i(+)/q_i(−)) = 2(λ M_{-i}/N + h)` depends on the
  surrounding magnetization;
* `thm:no-affinity-orientation-implication` — neither implication
  between a nonzero affinity class and a nonzero order parameter
  holds: a biased two-sheet reversible chain has `m ≠ 0` with all
  affinities zero, while the product of a driven three-cycle with a
  symmetric two-sheet chain has nonzero cycle affinity with `m = 0`.
-/

namespace NCG.Upstream

open NCG

/-! ## `def:cw-renewal-measure` -/

/-- The spin value of a cell orientation. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem spin_true : spin true = 1 := rfl
@[simp] theorem spin_false : spin false = -1 := rfl

variable (N : ℕ)

/-- The total orientation `M_N(η) = ∑ η_i`. -/
def magSum (η : Fin N → Bool) : ℝ := ∑ i, spin (η i)

/-- **Definition `def:cw-renewal-measure` (Gibbs weight)**:
`exp(λ M²/(2N) + h M)` (which is `exp(N(λ m²/2 + h m))`). -/
noncomputable def cwWeight (lam h : ℝ) (η : Fin N → Bool) : ℝ :=
  Real.exp (lam / (2 * N) * (magSum N η) ^ 2 + h * magSum N η)

/-- The partition function `Z_{N,λ,h}`. -/
noncomputable def cwPartition (lam h : ℝ) : ℝ :=
  ∑ η : Fin N → Bool, cwWeight N lam h η

/-- **Definition `def:cw-renewal-measure`**: the finite-volume
orientation measure. -/
noncomputable def cwMeasure (lam h : ℝ) (η : Fin N → Bool) : ℝ :=
  cwWeight N lam h η / cwPartition N lam h

theorem cwWeight_pos (lam h : ℝ) (η : Fin N → Bool) :
    0 < cwWeight N lam h η := Real.exp_pos _

theorem cwPartition_pos (lam h : ℝ) : 0 < cwPartition N lam h :=
  Finset.sum_pos (fun η _ => cwWeight_pos N lam h η)
    ⟨fun _ => true, Finset.mem_univ _⟩

/-- The deck transformation flips every cell. -/
def deckFlip (η : Fin N → Bool) : Fin N → Bool := fun i => !(η i)

theorem magSum_deckFlip (η : Fin N → Bool) :
    magSum N (deckFlip N η) = -magSum N η := by
  unfold magSum deckFlip
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases η i <;> simp

/-- **Definition `def:cw-renewal-measure` (deck invariance at zero
field)**: the quadratic term rewards coherence but prefers neither
sheet. -/
theorem cwWeight_deck_invariant (lam : ℝ) (η : Fin N → Bool) :
    cwWeight N lam 0 (deckFlip N η) = cwWeight N lam 0 η := by
  unfold cwWeight
  rw [magSum_deckFlip]
  ring_nf

/-! ## `def:cw-heat-bath` -/

/-- The residual magnetization `M_{-i}(η) = M_N(η) − η_i`. -/
def magRes (η : Fin N → Bool) (i : Fin N) : ℝ :=
  magSum N η - spin (η i)

/-- **Definition `def:cw-heat-bath` (conditional weights)**:
`q_i(s|η_{-i}) = e^{s(λ M_{-i}/N + h)}/(2 cosh(λ M_{-i}/N + h))`. -/
noncomputable def cwCond (lam h : ℝ) (η : Fin N → Bool) (i : Fin N)
    (s : Bool) : ℝ :=
  Real.exp (spin s * (lam * magRes N η i / N + h))
    / (2 * Real.cosh (lam * magRes N η i / N + h))

/-- **Definition `def:cw-heat-bath`**: the single-cell heat-bath
renewal channel on observables — choose a cell uniformly and return
it to the conditional minimal predictive state. -/
noncomputable def cwHeatBath (lam h : ℝ)
    (f : (Fin N → Bool) → ℝ) (η : Fin N → Bool) : ℝ :=
  (1 / N) * ∑ i, ∑ s : Bool,
    cwCond N lam h η i s * f (Function.update η i s)

/-- The conditional weights are strictly positive and normalized. -/
theorem cwCond_pos (lam h : ℝ) (η : Fin N → Bool) (i : Fin N)
    (s : Bool) : 0 < cwCond N lam h η i s := by
  unfold cwCond
  have hc : 0 < Real.cosh (lam * magRes N η i / N + h) :=
    Real.cosh_pos _
  positivity

theorem cwCond_sum (lam h : ℝ) (η : Fin N → Bool) (i : Fin N) :
    ∑ s : Bool, cwCond N lam h η i s = 1 := by
  unfold cwCond
  rw [Fintype.sum_bool, spin_true, spin_false, one_mul, neg_one_mul]
  set x : ℝ := lam * magRes N η i / N + h with hx
  rw [Real.cosh_eq]
  have he1 : (0 : ℝ) < Real.exp x + Real.exp (-x) := by positivity
  field_simp

/-! ## `prop:cw-quadratic-modular-weight` -/

/-- **Proposition `prop:cw-quadratic-modular-weight` (collective
modular Hamiltonian)**: the stationary log-density is quadratic in
the collective orientation,
`log ρ = λ M²/(2N) + h M − log Z` — not affine in an additive
renewal depth for `λ ≠ 0`. -/
theorem cw_log_density (lam h : ℝ) (η : Fin N → Bool) :
    Real.log (cwMeasure N lam h η)
      = lam / (2 * N) * (magSum N η) ^ 2 + h * magSum N η
        - Real.log (cwPartition N lam h) := by
  unfold cwMeasure cwWeight
  rw [Real.log_div (Real.exp_ne_zero _) (cwPartition_pos N lam h).ne',
    Real.log_exp]

/-- **Proposition `prop:cw-quadratic-modular-weight` (local modular
ratio)**: the modular ratio of redrawing one cell depends on the
surrounding magnetization —
`log(q_i(+)/q_i(−)) = 2(λ M_{-i}/N + h)`, so no
configuration-independent modular exponent exists unless `λ = 0` or
the magnetization is frozen. -/
theorem cw_modular_ratio (lam h : ℝ) (η : Fin N → Bool) (i : Fin N) :
    Real.log (cwCond N lam h η i true / cwCond N lam h η i false)
      = 2 * (lam * magRes N η i / N + h) := by
  set x : ℝ := lam * magRes N η i / N + h with hx
  have hc : (0 : ℝ) < 2 * Real.cosh x := by
    have := Real.cosh_pos x
    positivity
  have hratio : cwCond N lam h η i true / cwCond N lam h η i false
      = Real.exp (2 * x) := by
    unfold cwCond
    rw [spin_true, spin_false, one_mul, ← hx]
    rw [div_div_div_cancel_right₀]
    · rw [← Real.exp_sub]
      congr 1
      ring
    · exact hc.ne'
  rw [hratio, Real.log_exp]

/-! ## `thm:cw-finite-renewal` -/

theorem spin_sq (b : Bool) : spin b ^ 2 = 1 := by
  cases b <;> norm_num [spin]

theorem spin_not (b : Bool) : spin (!b) = -spin b := by
  cases b <;> simp [spin]

theorem cwMeasure_pos (lam h : ℝ) (η : Fin N → Bool) :
    0 < cwMeasure N lam h η :=
  div_pos (cwWeight_pos N lam h η) (cwPartition_pos N lam h)

theorem magSum_update (η : Fin N → Bool) (i : Fin N) (s : Bool) :
    magSum N (Function.update η i s)
      = magSum N η - spin (η i) + spin s := by
  unfold magSum
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i),
    ← Finset.sum_erase_add Finset.univ (fun j => spin (η j))
      (Finset.mem_univ i), Function.update_self]
  have herase : ∑ j ∈ Finset.univ.erase i,
      spin (Function.update η i s j)
      = ∑ j ∈ Finset.univ.erase i, spin (η j) :=
    Finset.sum_congr rfl fun j hj => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [herase]
  ring

theorem magRes_update (η : Fin N → Bool) (i : Fin N) (s : Bool) :
    magRes N (Function.update η i s) i = magRes N η i := by
  unfold magRes
  rw [magSum_update, Function.update_self]
  ring

/-- **Theorem `thm:cw-finite-renewal` (reversibility)**: single-cell
detailed balance of the heat-bath weights with respect to the
Curie-Weiss orientation measure. -/
theorem cw_detailed_balance (lam h : ℝ) (η : Fin N → Bool)
    (i : Fin N) (s : Bool) :
    cwMeasure N lam h η * cwCond N lam h η i s
      = cwMeasure N lam h (Function.update η i s)
        * cwCond N lam h (Function.update η i s) i (η i) := by
  unfold cwMeasure cwCond
  rw [magRes_update]
  rw [div_mul_div_comm, div_mul_div_comm]
  congr 1
  unfold cwWeight
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [magSum_update]
  have hs := spin_sq s
  have he := spin_sq (η i)
  unfold magRes
  linear_combination (lam / (2 * (N : ℝ))) * (he - hs)

/-- The heat-bath renewal kernel as a transition matrix. -/
noncomputable def cwKernel (lam h : ℝ) (η η' : Fin N → Bool) : ℝ :=
  (1 / N) * ∑ i, ∑ s : Bool, cwCond N lam h η i s
    * (if η' = Function.update η i s then 1 else 0)

theorem cwKernel_nonneg (lam h : ℝ) (η η' : Fin N → Bool) :
    0 ≤ cwKernel N lam h η η' := by
  unfold cwKernel
  refine mul_nonneg (by positivity) ?_
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun s _ => ?_
  refine mul_nonneg (cwCond_pos N lam h η i s).le ?_
  split <;> norm_num

/-- **Theorem `thm:cw-finite-renewal` (stochasticity)**: the kernel
rows are probability vectors. -/
theorem cwKernel_rowsum (hN : 0 < N) (lam h : ℝ) (η : Fin N → Bool) :
    ∑ η', cwKernel N lam h η η' = 1 := by
  unfold cwKernel
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hin : ∀ i : Fin N, ∑ η' : Fin N → Bool, ∑ s : Bool,
      cwCond N lam h η i s
        * (if η' = Function.update η i s then 1 else 0) = 1 := by
    intro i
    rw [Finset.sum_comm]
    have hs : ∀ s : Bool, ∑ η' : Fin N → Bool,
        cwCond N lam h η i s
          * (if η' = Function.update η i s then 1 else 0)
        = cwCond N lam h η i s := by
      intro s
      rw [← Finset.mul_sum]
      simp
    rw [Finset.sum_congr rfl fun s _ => hs s]
    exact cwCond_sum N lam h η i
  rw [Finset.sum_congr rfl fun i _ => hin i, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    one_div, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN.ne')]

/-- Every single-cell replacement has positive kernel weight. -/
theorem cwKernel_update_pos (hN : 0 < N) (lam h : ℝ)
    (η : Fin N → Bool) (i : Fin N) (s : Bool) :
    0 < cwKernel N lam h η (Function.update η i s) := by
  unfold cwKernel
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  refine mul_pos (by positivity) ?_
  refine Finset.sum_pos' (fun i' _ => Finset.sum_nonneg fun s' _ =>
    mul_nonneg (cwCond_pos N lam h η i' s').le
      (by split <;> norm_num)) ⟨i, Finset.mem_univ i, ?_⟩
  refine Finset.sum_pos' (fun s' _ =>
    mul_nonneg (cwCond_pos N lam h η i s').le
      (by split <;> norm_num)) ⟨s, Finset.mem_univ s, ?_⟩
  rw [if_pos rfl, mul_one]
  exact cwCond_pos N lam h η i s

/-- **Theorem `thm:cw-finite-renewal` (aperiodicity input)**: the
kernel has positive diagonal. -/
theorem cwKernel_diag_pos (hN : 0 < N) (lam h : ℝ)
    (η : Fin N → Bool) (i : Fin N) :
    0 < cwKernel N lam h η η := by
  have h1 := cwKernel_update_pos N hN lam h η i (η i)
  rwa [Function.update_eq_self] at h1

/-- **Theorem `thm:cw-finite-renewal` (unitality)**: the heat-bath
channel is unital. -/
theorem cwHeatBath_one (hN : 0 < N) (lam h : ℝ) (η : Fin N → Bool) :
    cwHeatBath N lam h (fun _ => 1) η = 1 := by
  unfold cwHeatBath
  simp only [mul_one]
  rw [Finset.sum_congr rfl fun i _ => cwCond_sum N lam h η i,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, one_div,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN.ne')]

/-- **Theorem `thm:cw-finite-renewal` (positivity)**: the heat-bath
channel is positive; on the commutative algebra of observables this
is the operational (completely) positive requirement. -/
theorem cwHeatBath_nonneg (lam h : ℝ) (f : (Fin N → Bool) → ℝ)
    (hf : ∀ ζ, 0 ≤ f ζ) (η : Fin N → Bool) :
    0 ≤ cwHeatBath N lam h f η := by
  unfold cwHeatBath
  refine mul_nonneg (by positivity) ?_
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun s _ =>
    mul_nonneg (cwCond_pos N lam h η i s).le (hf _)

/-- The channel is the observable action of the kernel. -/
theorem cwHeatBath_eq_kernel (lam h : ℝ) (f : (Fin N → Bool) → ℝ)
    (η : Fin N → Bool) :
    cwHeatBath N lam h f η
      = ∑ η', cwKernel N lam h η η' * f η' := by
  unfold cwHeatBath cwKernel
  have h1 : ∀ η' : Fin N → Bool,
      ((1 / (N : ℝ)) * ∑ i, ∑ s : Bool, cwCond N lam h η i s
        * (if η' = Function.update η i s then 1 else 0)) * f η'
      = (1 / (N : ℝ)) * ∑ i, ∑ s : Bool, cwCond N lam h η i s
        * (if η' = Function.update η i s then f η' else 0) := by
    intro η'
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun sb _ => ?_
    rw [mul_assoc]
    congr 1
    split <;> ring
  rw [Finset.sum_congr rfl fun η' _ => h1 η', ← Finset.mul_sum]
  congr 1
  symm
  calc ∑ η' : Fin N → Bool, ∑ i : Fin N, ∑ sb : Bool,
        cwCond N lam h η i sb
          * (if η' = Function.update η i sb then f η' else 0)
      = ∑ i : Fin N, ∑ η' : Fin N → Bool, ∑ sb : Bool,
          cwCond N lam h η i sb
            * (if η' = Function.update η i sb then f η' else 0) :=
        Finset.sum_comm
    _ = ∑ i : Fin N, ∑ sb : Bool, ∑ η' : Fin N → Bool,
          cwCond N lam h η i sb
            * (if η' = Function.update η i sb then f η' else 0) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i : Fin N, ∑ sb : Bool, cwCond N lam h η i sb
          * f (Function.update η i sb) := by
        refine Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun sb _ => ?_
        rw [← Finset.mul_sum]
        congr 1
        simp

set_option maxHeartbeats 1600000 in
-- the involution reindexing over the configuration space needs
-- more room than the default limit
/-- **Theorem `thm:cw-finite-renewal` (stationarity)**: the
Curie-Weiss orientation measure is stationary for the heat-bath
kernel. -/
theorem cwKernel_stationary (hN : 0 < N) (lam h : ℝ)
    (η' : Fin N → Bool) :
    ∑ η, cwMeasure N lam h η * cwKernel N lam h η η'
      = cwMeasure N lam h η' := by
  unfold cwKernel
  have hstep : ∀ i : Fin N,
      ∑ η : Fin N → Bool, ∑ s : Bool,
        cwMeasure N lam h η * cwCond N lam h η i s
          * (if η' = Function.update η i s then 1 else 0)
      = cwMeasure N lam h η' := by
    intro i
    set G : (Fin N → Bool) × Bool → ℝ := fun q =>
      cwMeasure N lam h q.1 * cwCond N lam h q.1 i q.2
        * (if η' = q.1 then 1 else 0) with hG
    set Φ : (Fin N → Bool) × Bool → (Fin N → Bool) × Bool :=
      fun q => (Function.update q.1 i q.2, q.1 i) with hPhi
    have hinv : Function.Involutive Φ := by
      intro q
      simp only [hPhi]
      refine Prod.ext ?_ ?_
      · show Function.update (Function.update q.1 i q.2) i (q.1 i)
          = q.1
        rw [Function.update_idem, Function.update_eq_self]
      · show (Function.update q.1 i q.2) i = q.2
        rw [Function.update_self]
    calc ∑ η : Fin N → Bool, ∑ s : Bool,
          cwMeasure N lam h η * cwCond N lam h η i s
            * (if η' = Function.update η i s then 1 else 0)
        = ∑ η : Fin N → Bool, ∑ s : Bool, G (Φ (η, s)) := by
          refine Finset.sum_congr rfl fun η _ =>
            Finset.sum_congr rfl fun sb _ => ?_
          simp only [hG, hPhi]
          rw [cw_detailed_balance N lam h η i sb]
      _ = ∑ q : (Fin N → Bool) × Bool, G (Φ q) :=
          (Fintype.sum_prod_type
            (fun q : (Fin N → Bool) × Bool => G (Φ q))).symm
      _ = ∑ q : (Fin N → Bool) × Bool, G q :=
          hinv.bijective.sum_comp G
      _ = ∑ ζ : Fin N → Bool, ∑ t : Bool, G (ζ, t) :=
          Fintype.sum_prod_type G
      _ = cwMeasure N lam h η' := by
          have hz : ∀ ζ : Fin N → Bool,
              ∑ t : Bool, G (ζ, t)
              = cwMeasure N lam h ζ * (if η' = ζ then 1 else 0) := by
            intro ζ
            simp only [hG]
            rw [show ∑ t : Bool, cwMeasure N lam h ζ
                  * cwCond N lam h ζ i t * (if η' = ζ then 1 else 0)
                = (cwMeasure N lam h ζ * (if η' = ζ then 1 else 0))
                  * ∑ t : Bool, cwCond N lam h ζ i t from by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun t _ => by ring]
            rw [cwCond_sum, mul_one]
          rw [Finset.sum_congr rfl fun ζ _ => hz ζ]
          rw [Finset.sum_eq_single η']
          · rw [if_pos rfl, mul_one]
          · intro ζ _ hζ
            rw [if_neg fun hc => hζ hc.symm, mul_zero]
          · intro habs
            exact absurd (Finset.mem_univ _) habs
  have hpull : ∀ η : Fin N → Bool, cwMeasure N lam h η
      * ((1 / (N : ℝ)) * ∑ i, ∑ s : Bool, cwCond N lam h η i s
        * (if η' = Function.update η i s then 1 else 0))
      = (1 / (N : ℝ)) * ∑ i, ∑ s : Bool,
        cwMeasure N lam h η * cwCond N lam h η i s
          * (if η' = Function.update η i s then 1 else 0) := by
    intro η
    rw [← mul_assoc, mul_comm (cwMeasure N lam h η) (1 / (N : ℝ)),
      mul_assoc, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun sb _ => ?_
    ring
  rw [Finset.sum_congr rfl fun η _ => hpull η, ← Finset.mul_sum,
    Finset.sum_comm]
  rw [Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, one_div,
    ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'),
    one_mul]

/-- **Theorem `thm:cw-finite-renewal` (irreducibility)**: any two
configurations are joined by a positive-weight kernel path obtained
by re-drawing cells one at a time. -/
theorem cwKernel_reachable (hN : 0 < N) (lam h : ℝ)
    (η η' : Fin N → Bool) :
    ∃ (M : ℕ) (γ : ℕ → (Fin N → Bool)),
      γ 0 = η ∧ γ M = η'
        ∧ ∀ k < M, 0 < cwKernel N lam h (γ k) (γ (k + 1)) := by
  refine ⟨N, fun k => fun j => if (j : ℕ) < k then η' j else η j,
    ?_, ?_, ?_⟩
  · funext j
    simp
  · funext j
    simp [j.isLt]
  · intro k hk
    have hupdate : (fun j : Fin N =>
        if (j : ℕ) < k + 1 then η' j else η j)
        = Function.update
            (fun j : Fin N => if (j : ℕ) < k then η' j else η j)
            ⟨k, hk⟩ (η' ⟨k, hk⟩) := by
      funext j
      by_cases hj : j = (⟨k, hk⟩ : Fin N)
      · subst hj
        rw [Function.update_self, if_pos (by simp)]
      · rw [Function.update_of_ne hj]
        have hne : (j : ℕ) ≠ k := fun hc => hj (Fin.ext hc)
        by_cases hlt : (j : ℕ) < k
        · rw [if_pos hlt, if_pos (Nat.lt_succ_of_lt hlt)]
        · rw [if_neg hlt, if_neg (by omega)]
    show 0 < cwKernel N lam h
      (fun j : Fin N => if (j : ℕ) < k then η' j else η j)
      (fun j : Fin N => if (j : ℕ) < k + 1 then η' j else η j)
    rw [hupdate]
    exact cwKernel_update_pos N hN lam h _ _ _

/-- **Theorem `thm:cw-finite-renewal` (unique stationary law)**: any
positive stationary law of the heat-bath kernel is proportional to
the Curie-Weiss orientation measure, by the ratio-minimum argument. -/
theorem cw_stationary_unique (hN : 0 < N) (lam h : ℝ)
    (m : (Fin N → Bool) → ℝ) (hm : ∀ η, 0 < m η)
    (hms : ∀ η', ∑ η, m η * cwKernel N lam h η η' = m η') :
    ∃ c : ℝ, 0 < c ∧ ∀ η, m η = c * cwMeasure N lam h η :=
  stationary_unique (cwKernel N lam h) (cwMeasure N lam h)
    (cwKernel_nonneg N lam h) (cwKernel_rowsum N hN lam h)
    (cwMeasure_pos N lam h) (cwKernel_stationary N hN lam h)
    m hm hms (fun η η' => cwKernel_reachable N hN lam h η η')

/-! ### Deck covariance at zero field -/

theorem magRes_deckFlip (η : Fin N → Bool) (i : Fin N) :
    magRes N (deckFlip N η) i = -magRes N η i := by
  unfold magRes
  rw [magSum_deckFlip]
  have hsp : spin (deckFlip N η i) = -spin (η i) := by
    unfold deckFlip
    exact spin_not (η i)
  rw [hsp]
  ring

theorem cwCond_deckFlip (lam : ℝ) (η : Fin N → Bool) (i : Fin N)
    (s : Bool) :
    cwCond N lam 0 (deckFlip N η) i s = cwCond N lam 0 η i (!s) := by
  unfold cwCond
  rw [magRes_deckFlip, spin_not]
  rw [show lam * -magRes N η i / N + 0
      = -(lam * magRes N η i / N + 0) from by ring]
  rw [Real.cosh_neg]
  congr 2
  ring

theorem update_deckFlip (η : Fin N → Bool) (i : Fin N) (s : Bool) :
    Function.update (deckFlip N η) i s
      = deckFlip N (Function.update η i (!s)) := by
  funext j
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self]
    unfold deckFlip
    rw [Function.update_self, Bool.not_not]
  · rw [Function.update_of_ne hj]
    unfold deckFlip
    rw [Function.update_of_ne hj]

/-- **Theorem `thm:cw-finite-renewal` (deck covariance)**: at zero
field the heat-bath channel commutes with the global deck flip. -/
theorem cwHeatBath_deck_covariant (lam : ℝ)
    (f : (Fin N → Bool) → ℝ) (η : Fin N → Bool) :
    cwHeatBath N lam 0 f (deckFlip N η)
      = cwHeatBath N lam 0 (fun ζ => f (deckFlip N ζ)) η := by
  unfold cwHeatBath
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  calc ∑ s : Bool, cwCond N lam 0 (deckFlip N η) i s
        * f (Function.update (deckFlip N η) i s)
      = ∑ s : Bool, cwCond N lam 0 η i (!s)
        * f (deckFlip N (Function.update η i (!s))) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [cwCond_deckFlip, update_deckFlip]
    _ = ∑ s : Bool, cwCond N lam 0 η i s
        * f (deckFlip N (Function.update η i s)) := by
        rw [Fintype.sum_bool, Fintype.sum_bool]
        simp only [Bool.not_true, Bool.not_false]
        exact add_comm _ _

/-! ## `thm:no-affinity-orientation-implication` -/

section Independence

/-- **Theorem `thm:no-affinity-orientation-implication` (orientation
without affinity)**: the biased two-sheet chain is exactly
reversible — every edge affinity vanishes — yet its stationary
deck-odd order parameter is nonzero whenever the bias is
nontrivial. -/
theorem orientation_without_affinity (a b : ℝ) (ha : 0 < a)
    (hb : 0 < b) (hab : a ≠ b) :
    ∃ (p : Bool → Bool → ℝ) (π : Bool → ℝ) (J : Bool → ℝ),
      (∀ x, 0 < π x)
      ∧ (∀ x, ∑ y, p x y = 1)
      ∧ (∀ x y, π x * p x y = π y * p y x)
      ∧ (∀ x y, edgeAff p π x y = 0)
      ∧ (∑ x, π x * J x) ≠ 0 := by
  have hsum : (0 : ℝ) < a + b := by positivity
  refine ⟨fun x y => if x = y then (if x then 1 - a else 1 - b)
      else (if x then a else b),
    fun x => if x then b / (a + b) else a / (a + b),
    fun x => if x then 1 else -1, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    cases x <;> simp <;> positivity
  · intro x
    rw [Fintype.sum_bool]
    cases x <;> simp <;> ring
  · intro x y
    cases x <;> cases y <;> simp <;> field_simp <;> ring
  · intro x y
    apply edgeAff_eq_zero_of_balanced
    intro x' y'
    cases x' <;> cases y' <;> simp <;> field_simp <;> ring
  · rw [Fintype.sum_bool]
    have key : b / (a + b) * 1 + a / (a + b) * (-1) ≠ 0 := by
      intro hzero
      have h2 : (b - a) / (a + b) = 0 := by
        rw [sub_div]
        linarith
      rw [div_eq_zero_iff] at h2
      rcases h2 with h | h
      · exact hab (by linarith)
      · linarith
    simpa using key

/-- The product of the driven three-cycle with the symmetric
two-sheet chain. -/
noncomputable def prodKernel (a b σ : ℝ) :
    (ZMod 3 × Bool) → (ZMod 3 × Bool) → ℝ :=
  fun x y =>
    (if y.1 = x.1 + 1 then a else if y.1 = x.1 - 1 then b
      else 1 - a - b)
    * (if y.2 = x.2 then 1 - σ else σ)

theorem prodKernel_forward (a b σ : ℝ) (v : ZMod 3) :
    prodKernel a b σ (v, true) (v + 1, true) = a * (1 - σ) := by
  unfold prodKernel
  rw [if_pos rfl, if_pos rfl]

theorem prodKernel_backward (a b σ : ℝ) (v : ZMod 3) :
    prodKernel a b σ (v + 1, true) (v, true) = b * (1 - σ) := by
  unfold prodKernel
  have h1 : ¬(v = v + 1 + 1) := by revert v; decide
  have h2 : v = v + 1 - 1 := by revert v; decide
  rw [if_neg h1, if_pos h2, if_pos rfl]

/-- **Theorem `thm:no-affinity-orientation-implication` (affinity
without orientation)**: the product of a driven three-cycle with a
symmetric two-sheet chain has uniform-product stationary law, zero
deck-odd order parameter, and a directed cycle of affinity
`3 log(a/b) ≠ 0` — nonzero circulation with no selected sheet. -/
theorem affinity_without_orientation (a b σ : ℝ) (ha : 0 < a)
    (hb : 0 < b) (hab : a ≠ b) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ (π : (ZMod 3 × Bool) → ℝ) (J : (ZMod 3 × Bool) → ℝ)
      (γ : ℕ → (ZMod 3 × Bool)) (M : ℕ),
      (∀ x, 0 < π x)
      ∧ (∑ x, π x * J x) = 0
      ∧ γ M = γ 0
      ∧ (∀ k < M, 0 < prodKernel a b σ (γ k) (γ (k + 1)))
      ∧ pathAff (prodKernel a b σ) π γ M = 3 * Real.log (a / b)
      ∧ pathAff (prodKernel a b σ) π γ M ≠ 0 := by
  have h1σ : (0 : ℝ) < 1 - σ := by linarith
  set πu : (ZMod 3 × Bool) → ℝ := fun _ => 1 / 6 with hπu
  set γc : ℕ → (ZMod 3 × Bool) := fun k => ((k : ZMod 3), true)
    with hγc
  have hcast : ∀ k : ℕ, (((k + 1 : ℕ)) : ZMod 3)
      = ((k : ℕ) : ZMod 3) + 1 := by
    intro k
    push_cast
    ring
  have hedge : ∀ v : ZMod 3,
      edgeAff (prodKernel a b σ) πu (v, true) (v + 1, true)
        = Real.log (a / b) := by
    intro v
    unfold edgeAff
    rw [prodKernel_forward, prodKernel_backward]
    congr 1
    simp only [hπu]
    rw [div_eq_div_iff (by positivity) hb.ne']
    ring
  have hval : pathAff (prodKernel a b σ) πu γc 3
      = 3 * Real.log (a / b) := by
    unfold pathAff
    have hterm : ∀ k ∈ Finset.range 3,
        edgeAff (prodKernel a b σ) πu (γc k) (γc (k + 1))
          = Real.log (a / b) := by
      intro k _
      simp only [hγc]
      rw [hcast k]
      exact hedge _
    rw [Finset.sum_congr rfl hterm, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    norm_num
  have hlog : Real.log (a / b) ≠ 0 := by
    intro h0
    have hpos : 0 < a / b := div_pos ha hb
    have h1 := Real.exp_log hpos
    rw [h0, Real.exp_zero] at h1
    have h2 : a / b = 1 := h1.symm
    rw [div_eq_one_iff_eq hb.ne'] at h2
    exact hab h2
  refine ⟨πu, fun x => if x.2 then 1 else -1, γc, 3,
    ?_, ?_, ?_, ?_, hval, ?_⟩
  · intro x
    norm_num [hπu]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [Fintype.sum_bool]
    norm_num [hπu]
  · simp only [hγc]
    decide
  · intro k hk
    simp only [hγc]
    rw [hcast k, prodKernel_forward]
    exact mul_pos ha h1σ
  · rw [hval]
    exact mul_ne_zero (by norm_num) hlog

end Independence

end NCG.Upstream
