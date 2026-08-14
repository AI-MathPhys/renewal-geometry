/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.ProjectionPersistenceTradeoff
import NCG.Grand.AtlasIsoperimetry

/-!
# Actual short-cylinder and local-update audit of the cubic regulator
  (`thm:renewal-interchange-actual-audit`,
  Gran-Tensor manuscript)

The one-direction modulated interchange regulator on
`V_N = (ℤ/N)³` (`def:modulated-renewal-interchange`):
local renewal flips `H → P` at `a = 4λ/5` and `P → H` at
`b = 2λ/3`, all nearest-neighbour swaps at rate `κN²`,
and each positive `e₁` swap modulated by
`1 + θφ(η_{x+2e₁})`.  Every actual compiler output is
proved explicit:

* **(A1)** the endpoint translations commute, have order
  `N`, act transitively, and close the four-translation
  relation; with masses `h³` and conductances `κh` and
  `κ ≥ 1` the boxed Cartesian axis floor evaluates to
  exactly `κ/16`, and the proved mixed-fiber cut
  inequality instantiates to `(κ/16)·mass^{2/3} ≤ h·cut`;
* **(A2)** the private-phase count `K_N` is exactly
  lumpable: the boxed quotient generator
  `(𝓛F)(k) = a(N³−k)[F(k+1)−F(k)] + bk[F(k−1)−F(k)]`
  for every `F`, `η`, and every modulation, with the
  boxed binomial `(6/11, 5/11)` law in exact detailed
  balance and stationary;
* **(A3)** the boxed extensive product action
  `𝓐(η) = −∑ log π_{η_x}` closes the boxed local
  detailed-balance identity
  `log(q/q̃) + 𝓐(η') − 𝓐(η) = 0` on every primitive
  flip and on every unmodulated or modulated swap;
* **(A4)** the point-readable field record has
  cardinality `2^{N³}`, and no fixed finite bank of
  bounded pattern counts injects once
  `(M+1)^B < 2^{N³}`;
* **(A5)** the nonlinear operator
  `φ_{x+2e₁}(I − S_{x,x+e₁})` sends one-site Walsh
  functions to two-site monomials, grows the primitive
  chain `{0, 2e₁, …, 2ne₁}` at every `n`, and escapes
  every site window missing `x + 2e₁`: no
  cutoff-independent finite pattern radius is closed;
* **(A6)** the count-quotient Gibbs data: the boxed
  reference-complexity term `H_N = N³ log 2`, the bare
  action minimized at `k = N³`, and the binomial mean
  `∑ k·Pr(K=k) = (6/11)N³` behind `K_N/N³ → 6/11`.

The almost-sure limit `K_N/N³ → 6/11` beyond its exact
mean identity, and the OU/reaction–diffusion continuum
clause, are the manuscript's stochastic-limit layer.
-/

open Finset

namespace NCG
namespace InterchangeAudit

open FlipInterchange

variable {N : ℕ} [NeZero N]

/-- Private-phase count `K_N(η) = #{x : η_x = P}`. -/
def countP (η : Config N) : ℕ :=
  (Finset.univ.filter fun x => η x = true).card

/-- Real-valued renewal flip rates (`H → P` at `4λ/5`,
`P → H` at `2λ/3`). -/
noncomputable def flipRateR (lam : ℝ) (s : Bool) : ℝ :=
  if s then 2 * lam / 3 else 4 * lam / 5

/-- One-direction nonlinear modulation factor: positive
`e₁` edges carry `1 + θφ(η_{x+2e₁})`. -/
noncomputable def modFactor (θ : ℝ) (φm : Bool → ℝ)
    (η : Config N) (x : Site N) (j : Fin 3) : ℝ :=
  if j = 0 then 1 + θ * φm (η (x + 2 • unitVec 0)) else 1

/-- Modulated swap rate on the directed edge `(x, x+e_j)`. -/
noncomputable def swapRate (kappa θ : ℝ) (φm : Bool → ℝ)
    (η : Config N) (x : Site N) (j : Fin 3) : ℝ :=
  kappa * (N : ℝ) ^ 2 * modFactor θ φm η x j

/-- The modulated flip–interchange generator of
`def:modulated-renewal-interchange`. -/
noncomputable def genA (lam kappa θ : ℝ) (φm : Bool → ℝ)
    (f : Config N → ℝ) (η : Config N) : ℝ :=
  (∑ x, flipRateR lam (η x) * (f (flipAt η x) - f η))
  + ∑ x, ∑ j : Fin 3, swapRate kappa θ φm η x j *
      (f (swapAt η x (x + unitVec j)) - f η)

/-- The boxed lumped quotient generator
`a(M−k)[F(k+1)−F(k)] + bk[F(k−1)−F(k)]`. -/
noncomputable def quotGen (lam : ℝ) (M : ℕ) (F : ℕ → ℝ)
    (k : ℕ) : ℝ :=
  4 * lam / 5 * ((M : ℝ) - k) * (F (k + 1) - F k)
    + 2 * lam / 3 * k * (F (k - 1) - F k)

/-- The boxed binomial stationary law
`Pr(K = k) = C(M,k)(6/11)^k(5/11)^{M−k}`. -/
noncomputable def binomLaw (M k : ℕ) : ℝ :=
  (M.choose k : ℝ) * (6 / 11) ^ k * (5 / 11) ^ (M - k)

/-- The boxed extensive product action
`𝓐_N(η) = −∑_x log π_{η_x}`. -/
noncomputable def action (η : Config N) : ℝ :=
  -∑ x, Real.log (if η x then (6 : ℝ) / 11 else 5 / 11)

section Count

omit [NeZero N] in
private theorem swapAt_eq_comp (η : Config N) (x y : Site N) :
    swapAt η x y = η ∘ (Equiv.swap x y) := by
  funext z
  simp only [swapAt, Function.comp_apply, Equiv.swap_apply_def]
  by_cases hzx : z = x
  · rw [if_pos hzx, if_pos hzx]
  · rw [if_neg hzx, if_neg hzx]
    by_cases hzy : z = y
    · rw [if_pos hzy, if_pos hzy]
    · rw [if_neg hzy, if_neg hzy]

private theorem countP_swap (η : Config N) (x y : Site N) :
    countP (swapAt η x y) = countP η := by
  unfold countP
  rw [swapAt_eq_comp]
  rw [Finset.card_filter, Finset.card_filter]
  exact Equiv.sum_comp (Equiv.swap x y)
    (fun z => if η z = true then 1 else 0)

private theorem countP_flip_true (η : Config N) (x : Site N)
    (hx : η x = true) :
    countP (flipAt η x) + 1 = countP η := by
  unfold countP flipAt
  have hfilter : (Finset.univ.filter fun z =>
      Function.update η x (!(η x)) z = true)
      = (Finset.univ.filter fun z => η z = true).erase x := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_erase,
      Finset.mem_univ, true_and]
    by_cases hzx : z = x
    · subst hzx
      rw [Function.update_self, hx]
      simp
    · rw [Function.update_of_ne hzx]
      simp [hzx]
  rw [hfilter]
  rw [Finset.card_erase_of_mem
    (by simp [Finset.mem_filter, hx])]
  have hmem : 0 < (Finset.univ.filter fun z =>
      η z = true).card :=
    Finset.card_pos.mpr ⟨x, by simp [Finset.mem_filter, hx]⟩
  omega

private theorem countP_flip_false (η : Config N) (x : Site N)
    (hx : η x = false) :
    countP (flipAt η x) = countP η + 1 := by
  unfold countP flipAt
  have hfilter : (Finset.univ.filter fun z =>
      Function.update η x (!(η x)) z = true)
      = insert x (Finset.univ.filter fun z => η z = true) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_insert,
      Finset.mem_univ, true_and]
    by_cases hzx : z = x
    · subst hzx
      rw [Function.update_self, hx]
      simp
    · rw [Function.update_of_ne hzx]
      simp [hzx]
  rw [hfilter, Finset.card_insert_of_notMem
    (by simp [Finset.mem_filter, hx])]

private theorem card_site (N : ℕ) [NeZero N] :
    Fintype.card (Site N) = N ^ 3 := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

private theorem countP_le (η : Config N) :
    countP η ≤ N ^ 3 := by
  calc countP η ≤ Fintype.card (Site N) :=
        (Finset.card_filter_le _ _).trans
          (by rw [Finset.card_univ])
    _ = N ^ 3 := card_site N

private theorem card_false_sites (η : Config N) :
    ((Finset.univ.filter fun x => ¬(η x = true)).card : ℝ)
      = ((N ^ 3 : ℕ) : ℝ) - countP η := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Site N)))
    (p := fun x => η x = true)
  rw [Finset.card_univ, card_site N] at hsplit
  have hcard : (Finset.univ.filter fun x => ¬(η x = true)).card
      = N ^ 3 - countP η := by
    unfold countP
    omega
  rw [hcard, Nat.cast_sub (countP_le η)]

end Count

section A2

/-- **(A2), boxed quotient generator**: the private-phase
count is exactly lumpable — for every observable of the
count, every configuration, and every admissible
modulation, the modulated generator acts through the boxed
birth–death quotient
`a(N³−k)[F(k+1)−F(k)] + bk[F(k−1)−F(k)]`. -/
theorem count_lumpable (lam kappa θ : ℝ) (φm : Bool → ℝ)
    (F : ℕ → ℝ) (η : Config N) :
    genA lam kappa θ φm (fun ξ => F (countP ξ)) η
      = quotGen lam (N ^ 3) F (countP η) := by
  unfold genA
  have hswap : ∑ x, ∑ j : Fin 3,
      swapRate kappa θ φm η x j *
        (F (countP (swapAt η x (x + unitVec j)))
          - F (countP η)) = 0 := by
    refine Finset.sum_eq_zero fun x _ =>
      Finset.sum_eq_zero fun j _ => ?_
    rw [countP_swap, sub_self, mul_zero]
  rw [hswap, add_zero]
  have hterm : ∀ x : Site N,
      flipRateR lam (η x) *
        (F (countP (flipAt η x)) - F (countP η))
      = if η x = true
          then 2 * lam / 3 * (F (countP η - 1) - F (countP η))
          else 4 * lam / 5 * (F (countP η + 1) - F (countP η)) := by
    intro x
    by_cases hx : η x = true
    · rw [if_pos hx]
      have hc : countP (flipAt η x) = countP η - 1 := by
        have := countP_flip_true η x hx
        omega
      rw [hc]
      unfold flipRateR
      rw [hx, if_pos rfl]
    · rw [if_neg hx]
      have hx' : η x = false := by
        cases h : η x
        · rfl
        · exact absurd h hx
      rw [countP_flip_false η x hx']
      unfold flipRateR
      rw [hx', if_neg (by simp)]
  rw [Finset.sum_congr rfl fun x _ => hterm x]
  rw [Finset.sum_ite]
  rw [Finset.sum_const, Finset.sum_const]
  unfold quotGen
  have hk : (((Finset.univ.filter fun x =>
      η x = true).card : ℕ) : ℝ) = (countP η : ℝ) := by
    unfold countP
    norm_num
  rw [nsmul_eq_mul, nsmul_eq_mul, card_false_sites]
  rw [hk]
  ring

/-- **(A2), boxed binomial law, detailed balance**: the
birth–death quotient rates satisfy exact detailed balance
against `Pr(K = k) = C(N³,k)(6/11)^k(5/11)^{N³−k}`. -/
theorem binom_detailed_balance (lam : ℝ) (M k : ℕ)
    (hk : k < M) :
    4 * lam / 5 * ((M : ℝ) - k) * binomLaw M k
      = 2 * lam / 3 * ((k : ℝ) + 1) * binomLaw M (k + 1) := by
  unfold binomLaw
  have hch : ((M.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1)
      = ((M.choose k : ℕ) : ℝ) * ((M : ℝ) - (k : ℝ)) := by
    have := Nat.choose_succ_right_eq M k
    have hcast := congrArg (fun t : ℕ => (t : ℝ)) this
    push_cast [Nat.cast_sub hk.le] at hcast
    linarith [hcast]
  have hsub : M - k = (M - (k + 1)) + 1 := by omega
  rw [hsub, pow_succ]
  linear_combination
    (-(4 * lam / 11 * (6 / 11 : ℝ) ^ k
      * (5 / 11 : ℝ) ^ (M - (k + 1)))) * hch

/-- **(A2), stationarity**: the boxed binomial law is
stationary for the boxed quotient generator. -/
theorem binom_stationary (lam : ℝ) (M : ℕ) (F : ℕ → ℝ) :
    ∑ k ∈ Finset.range (M + 1),
      binomLaw M k * quotGen lam M F k = 0 := by
  have hsplit : ∀ k,
      binomLaw M k * quotGen lam M F k
        = binomLaw M k * (4 * lam / 5 * ((M : ℝ) - k)
            * (F (k + 1) - F k))
          + binomLaw M k * (2 * lam / 3 * (k : ℝ)
            * (F (k - 1) - F k)) := by
    intro k
    unfold quotGen
    ring
  rw [Finset.sum_congr rfl fun k _ => hsplit k,
    Finset.sum_add_distrib]
  have ha : ∑ k ∈ Finset.range (M + 1),
      binomLaw M k * (4 * lam / 5 * ((M : ℝ) - k)
        * (F (k + 1) - F k))
      = ∑ k ∈ Finset.range M,
        binomLaw M k * (4 * lam / 5 * ((M : ℝ) - k)
          * (F (k + 1) - F k)) := by
    rw [Finset.sum_range_succ]
    simp only [sub_self, mul_zero, zero_mul, add_zero]
  have hb : ∑ k ∈ Finset.range (M + 1),
      binomLaw M k * (2 * lam / 3 * (k : ℝ)
        * (F (k - 1) - F k))
      = ∑ k ∈ Finset.range M,
        binomLaw M (k + 1) * (2 * lam / 3 * ((k : ℝ) + 1)
          * (F k - F (k + 1))) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show (k + 1) - 1 = k from by omega]
    push_cast
    ring
  rw [ha, hb, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hklt : k < M := Finset.mem_range.mp hk
  have hDB := binom_detailed_balance lam M k hklt
  linear_combination (F (k + 1) - F k) * hDB

end A2

section A3

private theorem action_diff_flip (η : Config N) (x : Site N) :
    action (flipAt η x) - action η
      = Real.log (if η x then (6 : ℝ) / 11 else 5 / 11)
        - Real.log (if !(η x) then (6 : ℝ) / 11 else 5 / 11) := by
  unfold action flipAt
  rw [show -∑ z, Real.log (if Function.update η x (!(η x)) z
        then (6 : ℝ) / 11 else 5 / 11)
      - -∑ z, Real.log (if η z then (6 : ℝ) / 11 else 5 / 11)
    = -(∑ z, (Real.log (if Function.update η x (!(η x)) z
        then (6 : ℝ) / 11 else 5 / 11)
      - Real.log (if η z then (6 : ℝ) / 11 else 5 / 11)))
    from by rw [Finset.sum_sub_distrib]; ring]
  rw [Finset.sum_eq_single x
    (fun z _ hz => by rw [Function.update_of_ne hz]; ring)
    (fun h => absurd (Finset.mem_univ x) h)]
  rw [Function.update_self]
  ring

private theorem action_diff_flip_false (η : Config N)
    (x : Site N) (hx : η x = false) :
    action (flipAt η x) - action η
      = Real.log ((5 : ℝ) / 11) - Real.log ((6 : ℝ) / 11) := by
  have hd := action_diff_flip η x
  rw [hx] at hd
  simpa using hd

private theorem action_diff_flip_true (η : Config N)
    (x : Site N) (hx : η x = true) :
    action (flipAt η x) - action η
      = Real.log ((6 : ℝ) / 11) - Real.log ((5 : ℝ) / 11) := by
  have hd := action_diff_flip η x
  rw [hx] at hd
  simpa using hd

/-- **(A3), boxed flip detailed balance**: on every
primitive phase flip,
`log(q(η,η')/q(η',η)) + 𝓐(η') − 𝓐(η) = 0`. -/
theorem flip_detailed_balance (lam : ℝ) (hlam : 0 < lam)
    (η : Config N) (x : Site N) :
    Real.log (flipRateR lam (η x) / flipRateR lam (!(η x)))
      + action (flipAt η x) - action η = 0 := by
  cases hx : η x
  · have hd := action_diff_flip_false η x hx
    simp only [Bool.not_false]
    unfold flipRateR
    rw [if_neg (by decide), if_pos rfl]
    rw [show (4 * lam / 5) / (2 * lam / 3) = (6 : ℝ) / 5 from by
      rw [div_eq_div_iff (by positivity) (by norm_num)]
      ring]
    rw [show (Real.log ((6:ℝ)/5)
        + action (flipAt η x) - action η)
      = Real.log ((6:ℝ)/5) + (action (flipAt η x) - action η)
      from by ring, hd]
    rw [Real.log_div (by norm_num) (by norm_num),
      Real.log_div (by norm_num) (by norm_num),
      Real.log_div (by norm_num) (by norm_num)]
    ring
  · have hd := action_diff_flip_true η x hx
    simp only [Bool.not_true]
    unfold flipRateR
    rw [if_pos rfl, if_neg (by decide)]
    rw [show (2 * lam / 3) / (4 * lam / 5) = (5 : ℝ) / 6 from by
      rw [div_eq_div_iff (by positivity) (by norm_num)]
      ring]
    rw [show (Real.log ((5:ℝ)/6)
        + action (flipAt η x) - action η)
      = Real.log ((5:ℝ)/6) + (action (flipAt η x) - action η)
      from by ring, hd]
    rw [Real.log_div (by norm_num) (by norm_num),
      Real.log_div (by norm_num) (by norm_num),
      Real.log_div (by norm_num) (by norm_num)]
    ring

private theorem action_swap (η : Config N) (x y : Site N) :
    action (swapAt η x y) = action η := by
  unfold action
  rw [swapAt_eq_comp]
  congr 1
  exact Equiv.sum_comp (Equiv.swap x y)
    (fun z => Real.log (if η z then (6 : ℝ) / 11 else 5 / 11))

omit [NeZero N] in
private theorem swapRate_symm (kappa θ : ℝ) (φm : Bool → ℝ)
    (hN : 2 < N) (η : Config N) (x : Site N) (j : Fin 3) :
    swapRate kappa θ φm (swapAt η x (x + unitVec j)) x j
      = swapRate kappa θ φm η x j := by
  unfold swapRate modFactor
  by_cases hj : j = 0
  · subst hj
    rw [if_pos rfl, if_pos rfl]
    have h2ne : (x + 2 • unitVec 0 : Site N) ≠ x := by
      intro h
      have h0 := congrFun h 0
      simp only [Pi.add_apply, Pi.smul_apply, unitVec,
        Pi.single_eq_same] at h0
      have hb : (2 : ℕ) • (1 : ZMod N) = 0 :=
        add_left_cancel (show x 0 + (2 : ℕ) • (1 : ZMod N)
          = x 0 + 0 from by rw [add_zero]; exact h0)
      have hb' : ((2 : ℕ) : ZMod N) = 0 := by
        rw [← mul_one ((2 : ℕ) : ZMod N), ← nsmul_eq_mul]
        exact hb
      have hval := congrArg ZMod.val hb'
      rw [ZMod.val_cast_of_lt hN, ZMod.val_zero] at hval
      omega
    have h1ne : (x + 2 • unitVec 0 : Site N)
        ≠ x + unitVec 0 := by
      intro h
      have h0 := congrFun h 0
      simp only [Pi.add_apply, Pi.smul_apply, unitVec,
        Pi.single_eq_same] at h0
      have hb : ((2 : ℕ) : ZMod N) = ((1 : ℕ) : ZMod N) := by
        rw [Nat.cast_one, ← mul_one ((2 : ℕ) : ZMod N),
          ← nsmul_eq_mul]
        exact add_left_cancel h0
      have hval := congrArg ZMod.val hb
      rw [ZMod.val_cast_of_lt hN,
        ZMod.val_cast_of_lt (by omega : 1 < N)] at hval
      omega
    congr 2
    unfold swapAt
    rw [if_neg h2ne, if_neg h1ne]
  · rw [if_neg hj, if_neg hj]

/-- **(A3), boxed swap detailed balance**: on every
unmodulated or modulated swap, the forward and reverse
rates agree, the product action is preserved, and the
boxed identity `log(q/q̃) + 𝓐(η') − 𝓐(η) = 0` holds. -/
theorem swap_detailed_balance (kappa θ : ℝ) (φm : Bool → ℝ)
    (hN : 2 < N) (hkappa : 0 < kappa)
    (hmod : ∀ s, 0 < 1 + θ * φm s)
    (η : Config N) (x : Site N) (j : Fin 3) :
    Real.log (swapRate kappa θ φm η x j /
        swapRate kappa θ φm (swapAt η x (x + unitVec j)) x j)
      + action (swapAt η x (x + unitVec j)) - action η = 0 := by
  rw [swapRate_symm kappa θ φm hN, action_swap]
  have hpos : 0 < swapRate kappa θ φm η x j := by
    unfold swapRate modFactor
    have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by
      have : (0 : ℝ) < (N : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
      positivity
    by_cases hj : j = 0
    · rw [if_pos hj]
      exact mul_pos (mul_pos hkappa hN2) (hmod _)
    · rw [if_neg hj]
      rw [mul_one]
      exact mul_pos hkappa hN2
  rw [div_self hpos.ne', Real.log_one]
  ring

end A3

section A1

omit [NeZero N] in
/-- **(A1), translation relations**: the endpoint
translations commute, have order `N`, act transitively,
and close the four-translation relation `T₁T₂T₃T₄ = I`. -/
theorem endpoint_translations (j j' : Fin 3) (x y : Site N) :
    (∀ z : Site N, z + unitVec j + unitVec j'
        = z + unitVec j' + unitVec j)
    ∧ N • (unitVec j : Site N) = 0
    ∧ (∃ v : Site N, x + v = y)
    ∧ unitVec 0 + unitVec 1 + unitVec 2
        + (-(unitVec 0 + unitVec 1 + unitVec 2) : Site N)
      = 0 := by
  refine ⟨fun z => add_right_comm z _ _, ?_,
    ⟨y - x, by rw [add_sub_cancel]⟩, add_neg_cancel _⟩
  funext i
  rw [Pi.smul_apply, Pi.zero_apply]
  by_cases hi : i = j
  · subst hi
    rw [unitVec, Pi.single_eq_same, nsmul_eq_mul, mul_one,
      ZMod.natCast_self]
  · rw [unitVec, Pi.single_eq_of_ne hi, smul_zero]

/-- **(A1), boxed axis floor value**: with masses `h³`,
conductances `κh`, and `κ ≥ 1`, the proved Cartesian axis
floor `c₋δ_κ/m₊^{2/3}` evaluates to exactly `κ/16`. -/
theorem axis_floor_kappa_sixteenth (κ : ℝ) (hκ : 1 ≤ κ) :
    κ * (16 * max 1 (2 ^ (-(1 : ℝ) / 3) * κ⁻¹) ^ 2)⁻¹
        / (1 : ℝ) ^ ((2 : ℝ) / 3)
      = κ / 16 := by
  have hmax : max 1 (2 ^ (-(1 : ℝ) / 3) * κ⁻¹) = 1 := by
    rw [max_eq_left]
    have h2 : (2 : ℝ) ^ (-(1 : ℝ) / 3) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos
        (by norm_num) (by norm_num)
    have hinv : κ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hκ
    calc (2 : ℝ) ^ (-(1 : ℝ) / 3) * κ⁻¹
        ≤ 1 * 1 := mul_le_mul h2 hinv
          (inv_nonneg.mpr (by linarith)) zero_le_one
      _ = 1 := one_mul 1
  rw [hmax, Real.one_rpow, one_pow, mul_one, div_one,
    ← div_eq_mul_inv]

/-- **(A1), boxed cut inequality `I_N ≥ κ/16`**: the exact
instantiation of the proved mixed-fiber Cartesian cut
bound with equal side lengths, masses `m₊ = 1` (in units
`h³`), conductances `c₋ = κ` (in units `h`), and the
`δ = 1/16` mixed-fiber constant of `κ ≥ 1`. -/
theorem axis_cut_bound (κ cardA massA cutCapacity h : ℝ)
    (hκ : 1 ≤ κ) (hh : 0 < h) (hcard : 0 ≤ cardA)
    (hmass0 : 0 ≤ massA)
    (hmass : massA ≤ h ^ 3 * cardA)
    (hmixed : κ * h * (1 / 16 * cardA ^ ((2 : ℝ) / 3))
      ≤ cutCapacity) :
    κ / 16 * massA ^ ((2 : ℝ) / 3) ≤ h * cutCapacity := by
  have hbound := cartesian_cut_bound_of_mixedFibers
    cardA massA cutCapacity h κ 1 (1 / 16) hh
    (by linarith) one_pos (by norm_num) hcard hmass0
    (by rw [one_mul]; exact hmass) hmixed
  rw [Real.one_rpow, div_one] at hbound
  calc κ / 16 * massA ^ ((2 : ℝ) / 3)
      = κ * (1 / 16) * massA ^ ((2 : ℝ) / 3) := by ring
    _ ≤ h * cutCapacity := hbound

end A1

section A4

/-- **(A4), point-readable field cardinality**: the minimal
future-separated field record is the full configuration
space, of cardinality `2^{N³}`. -/
theorem field_record_cardinality :
    Fintype.card (Config N) = 2 ^ (N ^ 3) := by
  rw [Fintype.card_fun, card_site N, Fintype.card_bool]

/-- **(A4), no finite pattern bank**: a fixed finite bank
of bounded pattern counts cannot represent the
point-readable field once `(M+1)^B < 2^{N³}`. -/
theorem no_finite_pattern_bank {B M : ℕ}
    (bank : Config N → Fin B → Fin (M + 1))
    (hcard : (M + 1) ^ B < 2 ^ (N ^ 3)) :
    ¬ Function.Injective bank := by
  intro hinj
  have hle := Fintype.card_le_of_injective bank hinj
  rw [field_record_cardinality, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin] at hle
  omega

end A4

section A5

/-- The site `m·e₁` on the axis chain. -/
def siteOf (N : ℕ) (m : ℕ) : Site N :=
  Pi.single 0 ((m : ℕ) : ZMod N)

/-- The nonlinear modulated operator
`φ_{x+2e₁}(I − S_{x,x+e₁})` on observables. -/
noncomputable def modOp (φm : Bool → ℝ) (x : Site N)
    (f : Config N → ℝ) (η : Config N) : ℝ :=
  φm (η (x + 2 • unitVec 0)) *
    (f η - f (swapAt η x (x + unitVec 0)))

/-- The primitive product chain on `{0, 2e₁, …, 2ne₁}`. -/
noncomputable def chainW (φm : Bool → ℝ) (n : ℕ)
    (η : Config N) : ℝ :=
  ∏ j ∈ Finset.range (n + 1), φm (η (siteOf N (2 * j)))

omit [NeZero N] in
private theorem siteOf_ne {a b : ℕ} (ha : a < N) (hb : b < N)
    (hab : a ≠ b) : siteOf N a ≠ siteOf N b := by
  intro h
  have h0 := congrFun h 0
  unfold siteOf at h0
  rw [Pi.single_eq_same, Pi.single_eq_same] at h0
  have hval := congrArg ZMod.val h0
  rw [ZMod.val_cast_of_lt ha, ZMod.val_cast_of_lt hb] at hval
  exact hab hval

omit [NeZero N] in
private theorem siteOf_add_one (m : ℕ) :
    siteOf N m + unitVec 0 = siteOf N (m + 1) := by
  funext i
  rw [Pi.add_apply]
  by_cases hi : i = 0
  · subst hi
    unfold siteOf unitVec
    rw [Pi.single_eq_same, Pi.single_eq_same,
      Pi.single_eq_same]
    push_cast
    ring
  · unfold siteOf unitVec
    rw [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi,
      Pi.single_eq_of_ne hi, add_zero]

omit [NeZero N] in
private theorem siteOf_add_two (m : ℕ) :
    siteOf N m + 2 • unitVec 0 = siteOf N (m + 2) := by
  funext i
  rw [Pi.add_apply, Pi.smul_apply]
  by_cases hi : i = 0
  · subst hi
    unfold siteOf unitVec
    rw [Pi.single_eq_same, Pi.single_eq_same,
      Pi.single_eq_same, nsmul_eq_mul, mul_one]
    push_cast
    ring
  · unfold siteOf unitVec
    rw [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi,
      Pi.single_eq_of_ne hi, smul_zero, add_zero]

omit [NeZero N] in
/-- **(A5), one-site Walsh to two-site monomials**: the
operator `φ_{x+2e₁}(I − S_{x,x+e₁})` sends the one-site
Walsh function at `x` to a difference of two-site
monomials. -/
theorem walsh_two_site (φm : Bool → ℝ) (x : Site N)
    (η : Config N) :
    modOp φm x (fun ξ => φm (ξ x)) η
      = φm (η x) * φm (η (x + 2 • unitVec 0))
        - φm (η (x + unitVec 0)) * φm (η (x + 2 • unitVec 0)) := by
  unfold modOp
  beta_reduce
  rw [show swapAt η x (x + unitVec 0) x = η (x + unitVec 0)
    from by unfold swapAt; rw [if_pos rfl]]
  ring

omit [NeZero N] in
/-- **(A5), primitive chain growth**: under primitive
closure the operator grows the product chain
`{0, 2e₁, …, 2ne₁}` to `{0, …, 2(n+1)e₁}` at every `n`
(for every cutoff `N > 2n+2`) — no cutoff-independent
finite pattern radius is closed. -/
theorem chain_growth (φm : Bool → ℝ) (n : ℕ)
    (hN : 2 * n + 2 < N) (η : Config N) :
    modOp φm (siteOf N (2 * n)) (chainW φm n) η
      = chainW φm (n + 1) η
        - (∏ j ∈ Finset.range n, φm (η (siteOf N (2 * j))))
          * φm (η (siteOf N (2 * n + 1)))
          * φm (η (siteOf N (2 * n + 2))) := by
  unfold modOp
  rw [siteOf_add_two, siteOf_add_one]
  have hswap : chainW φm n
      (swapAt η (siteOf N (2 * n)) (siteOf N (2 * n + 1)))
      = (∏ j ∈ Finset.range n, φm (η (siteOf N (2 * j))))
        * φm (η (siteOf N (2 * n + 1))) := by
    unfold chainW
    rw [Finset.prod_range_succ]
    congr 1
    · refine Finset.prod_congr rfl fun j hj => ?_
      have hjn : j < n := Finset.mem_range.mp hj
      congr 1
      unfold swapAt
      rw [if_neg (siteOf_ne (by omega) (by omega) (by omega)),
        if_neg (siteOf_ne (by omega) (by omega) (by omega))]
    · congr 1
      unfold swapAt
      rw [if_pos rfl]
  rw [hswap]
  have hlast : chainW φm (n + 1) η
      = chainW φm n η * φm (η (siteOf N (2 * n + 2))) := by
    unfold chainW
    rw [Finset.prod_range_succ]
    rw [show 2 * (n + 1) = 2 * n + 2 from by ring]
  rw [hlast]
  ring

omit [NeZero N] in
private theorem add_unit_ne (hN : 2 < N) (x : Site N) :
    x + unitVec 0 ≠ x := by
  intro h
  have h0 := congrFun h 0
  rw [Pi.add_apply, unitVec, Pi.single_eq_same] at h0
  have hb : (1 : ZMod N) = 0 :=
    add_left_cancel (show x 0 + 1 = x 0 + 0 from by
      rw [add_zero]; exact h0)
  have hval := congrArg ZMod.val hb
  rw [show (1 : ZMod N) = ((1 : ℕ) : ZMod N) from by
      push_cast; rfl] at hb
  have hval' := congrArg ZMod.val hb
  rw [ZMod.val_cast_of_lt (by omega : 1 < N),
    ZMod.val_zero] at hval'
  omega

omit [NeZero N] in
private theorem add_two_unit_ne (hN : 2 < N) (x : Site N) :
    x + 2 • unitVec 0 ≠ x := by
  intro h
  have h0 := congrFun h 0
  rw [Pi.add_apply, Pi.smul_apply, unitVec,
    Pi.single_eq_same] at h0
  have hb : (2 : ℕ) • (1 : ZMod N) = 0 :=
    add_left_cancel (show x 0 + (2 : ℕ) • (1 : ZMod N)
      = x 0 + 0 from by rw [add_zero]; exact h0)
  have hb' : ((2 : ℕ) : ZMod N) = 0 := by
    rw [← mul_one ((2 : ℕ) : ZMod N), ← nsmul_eq_mul]
    exact hb
  have hval := congrArg ZMod.val hb'
  rw [ZMod.val_cast_of_lt hN, ZMod.val_zero] at hval
  omega

omit [NeZero N] in
private theorem add_two_unit_ne_add_one (hN : 2 < N)
    (x : Site N) : x + 2 • unitVec 0 ≠ x + unitVec 0 := by
  intro h
  have h0 := congrFun h 0
  rw [Pi.add_apply, Pi.add_apply, Pi.smul_apply, unitVec,
    Pi.single_eq_same] at h0
  have hb : ((2 : ℕ) : ZMod N) = ((1 : ℕ) : ZMod N) := by
    rw [Nat.cast_one, ← mul_one ((2 : ℕ) : ZMod N),
      ← nsmul_eq_mul]
    exact add_left_cancel h0
  have hval := congrArg ZMod.val hb
  rw [ZMod.val_cast_of_lt hN,
    ZMod.val_cast_of_lt (by omega : 1 < N)] at hval
  omega

omit [NeZero N] in
/-- **(A5), window escape**: the modulated operator leaves
every site window `S` that misses `x + 2e₁` — witnessed by
two configurations agreeing on `S` with different images.
Hence no finite pattern radius is closed under the
complete local field dynamics. -/
theorem window_escape (hN : 2 < N) (φm : Bool → ℝ)
    (hφ : φm true ≠ φm false) (S : Finset (Site N))
    (x : Site N) (_hxS : x ∈ S)
    (hx2 : x + 2 • unitVec 0 ∉ S) :
    ∃ η η' : Config N, (∀ z ∈ S, η z = η' z)
      ∧ modOp φm x (fun ξ => φm (ξ x)) η
        ≠ modOp φm x (fun ξ => φm (ξ x)) η' := by
  classical
  set η : Config N := fun z => if z = x then true else false
    with hη
  set η' : Config N :=
    Function.update η (x + 2 • unitVec 0) true with hη'
  have hagree : ∀ z ∈ S, η z = η' z := by
    intro z hz
    rw [hη', Function.update_of_ne
      (fun h => hx2 (by rw [← h]; exact hz))]
  have hηx : η x = true := by rw [hη]; exact if_pos rfl
  have hηe : η (x + unitVec 0) = false := by
    rw [hη]
    exact if_neg (add_unit_ne hN x)
  have hη2 : η (x + 2 • unitVec 0) = false := by
    rw [hη]
    exact if_neg (add_two_unit_ne hN x)
  have hη'x : η' x = true := by
    rw [hη', Function.update_of_ne
      (fun h => add_two_unit_ne hN x h.symm)]
    exact hηx
  have hη'e : η' (x + unitVec 0) = false := by
    rw [hη', Function.update_of_ne
      (fun h => add_two_unit_ne_add_one hN x h.symm)]
    exact hηe
  have hη'2 : η' (x + 2 • unitVec 0) = true := by
    rw [hη']
    exact Function.update_self _ _ _
  refine ⟨η, η', hagree, ?_⟩
  rw [walsh_two_site, walsh_two_site, hηx, hηe, hη2,
    hη'x, hη'e, hη'2]
  intro h
  apply hφ
  have h0 : (φm true - φm false) ^ 2 = 0 := by
    linear_combination -h
  have h1 := (pow_eq_zero_iff
    (by norm_num : (2 : ℕ) ≠ 0)).mp h0
  exact sub_eq_zero.mp h1

end A5

section A6

/-- The bare count-quotient action
`𝓐_N(k) = −(M−k)log(5/11) − k·log(6/11)`. -/
noncomputable def countAction (M k : ℕ) : ℝ :=
  -(((M : ℝ) - k) * Real.log (5 / 11))
    - k * Real.log (6 / 11)

/-- **(A6), boxed reference complexity**: the Gibbs
reference weight `w_N(k) = C(N³,k)` carries
`H_N = log ∑_k C(N³,k) = N³ log 2`. -/
theorem reference_complexity (M : ℕ) :
    Real.log (∑ k ∈ Finset.range (M + 1),
        ((M.choose k : ℕ) : ℝ))
      = M * Real.log 2 := by
  have hsum : ∑ k ∈ Finset.range (M + 1),
      ((M.choose k : ℕ) : ℝ) = ((2 ^ M : ℕ) : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast congrArg (fun t : ℕ => (t : ℝ))
      (Nat.sum_range_choose M)
  rw [hsum]
  push_cast
  rw [Real.log_pow]

/-- **(A6), bare action minimized at `k = N³`**. -/
theorem bare_action_min (M k : ℕ) (hk : k ≤ M) :
    countAction M M ≤ countAction M k := by
  unfold countAction
  have hlog : Real.log ((5 : ℝ) / 11)
      < Real.log ((6 : ℝ) / 11) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have hMk : (0 : ℝ) ≤ (M : ℝ) - k := by
    have := (Nat.cast_le (α := ℝ)).mpr hk
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hlog.le hMk]

/-- **(A6), binomial mean**: the exact mean identity
`∑_k k·Pr(K = k) = (6/11)·N³` behind `K_N/N³ → 6/11`. -/
theorem binom_mean (M : ℕ) :
    ∑ k ∈ Finset.range (M + 1), (k : ℝ) * binomLaw M k
      = 6 / 11 * M := by
  cases M with
  | zero => simp [binomLaw]
  | succ m =>
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    have hbin : ∑ i ∈ Finset.range (m + 1),
        ((m.choose i : ℕ) : ℝ) * (6 / 11) ^ i
          * (5 / 11) ^ (m - i) = 1 := by
      have h := add_pow ((6 : ℝ) / 11) (5 / 11) m
      rw [show ((6 : ℝ) / 11 + 5 / 11) = 1 from by norm_num,
        one_pow] at h
      calc ∑ i ∈ Finset.range (m + 1),
            ((m.choose i : ℕ) : ℝ) * (6 / 11) ^ i
              * (5 / 11) ^ (m - i)
          = ∑ i ∈ Finset.range (m + 1),
            ((6 : ℝ) / 11) ^ i * (5 / 11) ^ (m - i)
              * ((m.choose i : ℕ) : ℝ) :=
            Finset.sum_congr rfl fun i _ => by ring
        _ = 1 := h.symm
    have hstep : ∀ i ∈ Finset.range (m + 1),
        ((i + 1 : ℕ) : ℝ) * binomLaw (m + 1) (i + 1)
          = 6 / 11 * ((m + 1 : ℕ) : ℝ)
            * (((m.choose i : ℕ) : ℝ) * (6 / 11) ^ i
              * (5 / 11) ^ (m - i)) := by
      intro i _
      unfold binomLaw
      have hch : ((m + 1 : ℕ) : ℝ) * ((m.choose i : ℕ) : ℝ)
          = (((m + 1).choose (i + 1) : ℕ) : ℝ)
            * ((i + 1 : ℕ) : ℝ) := by
        exact_mod_cast congrArg (fun t : ℕ => (t : ℝ))
          (Nat.add_one_mul_choose_eq m i)
      have hexp : (m + 1) - (i + 1) = m - i := by omega
      rw [hexp, pow_succ]
      push_cast at hch ⊢
      linear_combination
        (-(((6 : ℝ) / 11) ^ i * (6 / 11)
          * ((5 : ℝ) / 11) ^ (m - i))) * hch
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, hbin,
      mul_one]

end A6

end InterchangeAudit
end NCG
