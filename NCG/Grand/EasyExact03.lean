/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.EasyExact02
import NCG.Grand.TraceExpDerivative

/-!
# Easy exact records, batch 03 (Gran-Tensor manuscript)

Exact formalizations of the following manuscript records:

* `thm:SMYM-derefresh` — exact removal of the auxiliary refresh (CYD.3–CYD.7).
* `cth:SMYM-refresh-gap` — the parent refresh is not Yang–Mills coercivity.
* `cth:SMST-static-Weyl-no-clock` — static Weyl law does not determine the
  transfer clock (BS.12a).
* `thm:SMST-positive-time-transport-rectangle` — delayed-source transport
  rectangle (PT.14–PT.15).
* `cor:SMST-electromagnetic-scalar-branch` — exact scalar-aggregation branch.
* `cth:SMST-electromagnetic-phase-sum` — equal total phase need not give
  equal current (EMR.14).
* `thm:SMST-routed-electromagnetic-transport` — exact routed-source and
  routed-form transport (EMR.23–EMR.24).
* `cth:SMST-mixed-C-irredundant` — the auxiliary mixed row is irredundant
  (DMC.16).
* `cth:SMST-five-matrices-not-weighted` — the five unweighted matrices do not
  determine the weighted panels (DMC.28).
* `cth:SMST-positive-time-high-energy-escape` — base noncollapse without an
  energy row permits delayed collapse.
* `cth:SMST-resistance-clock-not-OS-clock` — static twist data do not
  identify the physical OS clock (PT.21).

Rendering conventions are described in the docstring of each section.
-/

open Matrix Finset
open NCG.SourceCoercivityInfluence
open scoped ComplexOrder ENNReal

namespace NCG

/-! ### Refresh calculus: exponentials of idempotent-coupled generators

Shared helpers for the CYD and BS records: the stationary reset kernel
`R(x,y) = μ(y)`, the exponential of a scaled idempotent, and absorption of
annihilating factors by matrix exponentials. -/

namespace RefreshCalculus

variable {k : Type*} [Fintype k] [DecidableEq k]

/-- The stationary reset kernel `R f = (∫ f dμ) 𝟙`, as the matrix
`R(x,y) = μ(y)`. -/
def resetKernel (μ : k → ℝ) : Matrix k k ℝ :=
  Matrix.of fun _ y => μ y

omit [DecidableEq k] in
/-- The reset kernel of a probability weight is idempotent. -/
theorem resetKernel_idem {μ : k → ℝ} (hprob : ∑ x, μ x = 1) :
    resetKernel μ * resetKernel μ = resetKernel μ := by
  ext x y
  simp only [Matrix.mul_apply, resetKernel, Matrix.of_apply]
  rw [← Finset.sum_mul, hprob, one_mul]

open scoped Matrix.Norms.Operator in
/-- The exponential of a scaled idempotent:
`exp(sE) = 1 + (eˢ - 1)E` whenever `E² = E`. -/
theorem exp_smul_idem {E : Matrix k k ℝ} (hE : E * E = E) (s : ℝ) :
    NormedSpace.exp (s • E) = 1 + (Real.exp s - 1) • E := by
  have hpow : ∀ n : ℕ, E ^ (n + 1) = E := by
    intro n
    induction n with
    | zero => rw [zero_add, pow_one]
    | succ n ih => rw [pow_succ, ih, hE]
  have hfun : ∀ n : ℕ, ((n.factorial : ℝ))⁻¹ • (s • E) ^ n
      = (((n.factorial : ℝ))⁻¹ * s ^ n) • E ^ n := by
    intro n
    rw [smul_pow, smul_smul]
  have hsum0 : Summable fun n : ℕ => ((n.factorial : ℝ))⁻¹ • (s • E) ^ n :=
    NormedSpace.expSeries_summable' (𝕂 := ℝ) (s • E)
  have hsum1 : Summable fun n : ℕ => (((n.factorial : ℝ))⁻¹ * s ^ n) • E ^ n :=
    hsum0.congr hfun
  have hs0 : Summable fun n : ℕ => ((n.factorial : ℝ))⁻¹ * s ^ n := by
    have h := NormedSpace.expSeries_summable' (𝕂 := ℝ) (s : ℝ)
    exact h.congr fun n => smul_eq_mul _ _
  have hs1 : Summable fun n : ℕ => (((n + 1).factorial : ℝ))⁻¹ * s ^ (n + 1) :=
    (summable_nat_add_iff 1).2 hs0
  have hscalar : ∑' n : ℕ, (((n + 1).factorial : ℝ))⁻¹ * s ^ (n + 1)
      = Real.exp s - 1 := by
    have hre : Real.exp s = ∑' n : ℕ, ((n.factorial : ℝ))⁻¹ * s ^ n := by
      rw [Real.exp_eq_exp_ℝ, congrFun (NormedSpace.exp_eq_tsum (𝕂 := ℝ) (𝔸 := ℝ)) s]
      exact tsum_congr fun n => smul_eq_mul _ _
    rw [hs0.tsum_eq_zero_add] at hre
    have h0 : ((Nat.factorial 0 : ℝ))⁻¹ * s ^ 0 = 1 := by norm_num [Nat.factorial]
    rw [h0] at hre
    linarith
  calc NormedSpace.exp (s • E)
      = ∑' n : ℕ, ((n.factorial : ℝ))⁻¹ • (s • E) ^ n :=
        congrFun (NormedSpace.exp_eq_tsum (𝕂 := ℝ)) (s • E)
    _ = ∑' n : ℕ, (((n.factorial : ℝ))⁻¹ * s ^ n) • E ^ n := tsum_congr hfun
    _ = (((Nat.factorial 0 : ℝ))⁻¹ * s ^ 0) • E ^ 0
        + ∑' n : ℕ, ((((n + 1).factorial : ℝ))⁻¹ * s ^ (n + 1)) • E ^ (n + 1) :=
        hsum1.tsum_eq_zero_add
    _ = 1 + ∑' n : ℕ, ((((n + 1).factorial : ℝ))⁻¹ * s ^ (n + 1)) • E := by
        rw [tsum_congr fun n => by rw [hpow n]]
        norm_num [Nat.factorial]
    _ = 1 + (∑' n : ℕ, (((n + 1).factorial : ℝ))⁻¹ * s ^ (n + 1)) • E := by
        rw [hs1.tsum_smul_const]
    _ = 1 + (Real.exp s - 1) • E := by rw [hscalar]

open scoped Matrix.Norms.Operator in
/-- A matrix exponential absorbs right factors annihilated by the exponent:
`A B = 0` implies `exp(A) B = B`. -/
theorem exp_mul_of_mul_eq_zero {A B : Matrix k k ℝ} (h : A * B = 0) :
    NormedSpace.exp A * B = B := by
  have hsum0 : Summable fun n : ℕ => ((n.factorial : ℝ))⁻¹ • A ^ n :=
    NormedSpace.expSeries_summable' (𝕂 := ℝ) A
  have hterm : ∀ n : ℕ, (((n.factorial : ℝ))⁻¹ • A ^ n) * B
      = ((n.factorial : ℝ))⁻¹ • (A ^ n * B) := fun n => smul_mul_assoc _ _ _
  have hzero : ∀ n : ℕ, A ^ (n + 1) * B = 0 := by
    intro n
    rw [pow_succ, Matrix.mul_assoc, h, Matrix.mul_zero]
  have hsum1 : Summable fun n : ℕ => ((n.factorial : ℝ))⁻¹ • (A ^ n * B) :=
    (hsum0.mul_right B).congr hterm
  calc NormedSpace.exp A * B
      = (∑' n : ℕ, ((n.factorial : ℝ))⁻¹ • A ^ n) * B := by
        rw [congrFun (NormedSpace.exp_eq_tsum (𝕂 := ℝ)) A]
    _ = ∑' n : ℕ, (((n.factorial : ℝ))⁻¹ • A ^ n) * B := (hsum0.tsum_mul_right B).symm
    _ = ∑' n : ℕ, ((n.factorial : ℝ))⁻¹ • (A ^ n * B) := tsum_congr hterm
    _ = ((Nat.factorial 0 : ℝ))⁻¹ • (A ^ 0 * B)
        + ∑' n : ℕ, ((((n + 1).factorial : ℝ))⁻¹ • (A ^ (n + 1) * B)) :=
        hsum1.tsum_eq_zero_add
    _ = B := by
        rw [tsum_congr fun n => by rw [hzero n, smul_zero]]
        rw [tsum_zero, add_zero, pow_zero, Matrix.one_mul]
        norm_num [Nat.factorial]

open scoped Matrix.Norms.Operator in
/-- A matrix exponential absorbs left factors annihilated by the exponent:
`B A = 0` implies `B exp(A) = B`. -/
theorem mul_exp_of_mul_eq_zero {A B : Matrix k k ℝ} (h : B * A = 0) :
    B * NormedSpace.exp A = B := by
  have hsum0 : Summable fun n : ℕ => ((n.factorial : ℝ))⁻¹ • A ^ n :=
    NormedSpace.expSeries_summable' (𝕂 := ℝ) A
  have hterm : ∀ n : ℕ, B * (((n.factorial : ℝ))⁻¹ • A ^ n)
      = ((n.factorial : ℝ))⁻¹ • (B * A ^ n) := fun n => mul_smul_comm _ _ _
  have hzero : ∀ n : ℕ, B * A ^ (n + 1) = 0 := by
    intro n
    induction n with
    | zero => rw [zero_add, pow_one, h]
    | succ n ih => rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.zero_mul]
  have hsum1 : Summable fun n : ℕ => ((n.factorial : ℝ))⁻¹ • (B * A ^ n) :=
    (hsum0.mul_left B).congr hterm
  calc B * NormedSpace.exp A
      = B * ∑' n : ℕ, ((n.factorial : ℝ))⁻¹ • A ^ n := by
        rw [congrFun (NormedSpace.exp_eq_tsum (𝕂 := ℝ)) A]
    _ = ∑' n : ℕ, B * (((n.factorial : ℝ))⁻¹ • A ^ n) := (hsum0.tsum_mul_left B).symm
    _ = ∑' n : ℕ, ((n.factorial : ℝ))⁻¹ • (B * A ^ n) := tsum_congr hterm
    _ = ((Nat.factorial 0 : ℝ))⁻¹ • (B * A ^ 0)
        + ∑' n : ℕ, ((((n + 1).factorial : ℝ))⁻¹ • (B * A ^ (n + 1))) :=
        hsum1.tsum_eq_zero_add
    _ = B := by
        rw [tsum_congr fun n => by rw [hzero n, smul_zero]]
        rw [tsum_zero, add_zero, pow_zero, Matrix.mul_one]
        norm_num [Nat.factorial]

end RefreshCalculus

/-! ### `thm:SMYM-derefresh` — Exact removal of the auxiliary refresh

Rendering: the reflected parent field space at one cutoff is a finite state
space `Ω` with stationary probability weight `μ`.  The local generator is a
finite reversible Markov generator matrix `L` (zero row sums, `μ`-detailed
balance); the parent generator is `ρ(R-1) + L` with `R` the stationary reset
kernel, exactly as in (CYD.1), and both semigroups are literal matrix
exponentials.  The carré-du-champ of a kernel `P` and a vector writer
`F : Ω → ℂ^d` is the finite sum `Γ_P(F)(x) = Σ_y P(x,y)(F y - F x)(F y - F x)^*`.
The coefficient bank `J` is a real isometry with range in `Ran Q`
(rendered as `R J = 0`).  The final sentence (invariance of the normalized
polar innovation) is rendered by the exact leakage scaling
`L^par = e^{-ρt} L^loc` together with trace-normalized proportionality of the
two lag-two innovations. -/

namespace Derefresh

open RefreshCalculus

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
variable {μ : Ω → ℝ} {L : Matrix Ω Ω ℝ}

/-- The local semigroup `P^loc(t) = e^{tL}`. -/
noncomputable def locSemigroup (L : Matrix Ω Ω ℝ) (t : ℝ) : Matrix Ω Ω ℝ :=
  NormedSpace.exp (t • L)

/-- The parent semigroup `P^par(t) = e^{t(ρ(R-1)+L)}` of (CYD.1). -/
noncomputable def parSemigroup (μ : Ω → ℝ) (L : Matrix Ω Ω ℝ) (ρ t : ℝ) :
    Matrix Ω Ω ℝ :=
  NormedSpace.exp (t • (ρ • (resetKernel μ - 1) + L))

section Identities

variable (hprob : ∑ x, μ x = 1) (hrow : ∀ x, ∑ y, L x y = 0)
  (hrev : ∀ x y, μ x * L x y = μ y * L y x)

omit [DecidableEq Ω] in
include hrow in
/-- A zero-row-sum generator annihilates the reset kernel on the right. -/
theorem gen_mul_reset : L * resetKernel μ = 0 := by
  ext x y
  simp only [Matrix.mul_apply, resetKernel, Matrix.of_apply, Matrix.zero_apply]
  rw [← Finset.sum_mul, hrow, zero_mul]

omit [DecidableEq Ω] in
include hrow hrev in
/-- A reversible zero-row-sum generator preserves `μ`: the reset kernel
annihilates it on the left. -/
theorem reset_mul_gen : resetKernel μ * L = 0 := by
  ext x y
  simp only [Matrix.mul_apply, resetKernel, Matrix.of_apply, Matrix.zero_apply]
  calc ∑ z, μ z * L z y
      = ∑ z, μ y * L y z := Finset.sum_congr rfl fun z _ => hrev z y
    _ = μ y * ∑ z, L y z := (Finset.mul_sum _ _ _).symm
    _ = 0 := by rw [hrow, mul_zero]

include hrow in
/-- The local semigroup fixes the reset kernel on the right. -/
theorem loc_mul_reset (t : ℝ) :
    locSemigroup L t * resetKernel μ = resetKernel μ := by
  refine exp_mul_of_mul_eq_zero ?_
  rw [smul_mul_assoc, gen_mul_reset hrow, smul_zero]

include hrow hrev in
/-- The reset kernel absorbs the local semigroup on the left. -/
theorem reset_mul_loc (t : ℝ) :
    resetKernel μ * locSemigroup L t = resetKernel μ := by
  refine mul_exp_of_mul_eq_zero ?_
  rw [mul_smul_comm, reset_mul_gen hrow hrev, smul_zero]

include hprob hrow hrev in
/-- The convex-kernel form of the de-refreshing identity:
`P^par(t) = e^{-ρt} P^loc(t) + (1 - e^{-ρt}) R`. -/
theorem par_convex (ρ t : ℝ) :
    parSemigroup μ L ρ t
      = Real.exp (-(ρ * t)) • locSemigroup L t
        + (1 - Real.exp (-(ρ * t))) • resetKernel μ := by
  have hsplit : t • (ρ • (resetKernel μ - 1) + L)
      = t • L + (-(ρ * t)) • ((1 : Matrix Ω Ω ℝ) - resetKernel μ) := by
    module
  have hLR : L * resetKernel μ = resetKernel μ * L := by
    rw [gen_mul_reset hrow, reset_mul_gen hrow hrev]
  have hcomm : Commute (t • L)
      ((-(ρ * t)) • ((1 : Matrix Ω Ω ℝ) - resetKernel μ)) := by
    apply Commute.smul_left
    apply Commute.smul_right
    unfold Commute SemiconjBy
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hLR]
  have hidem : ((1 : Matrix Ω Ω ℝ) - resetKernel μ)
      * ((1 : Matrix Ω Ω ℝ) - resetKernel μ)
      = (1 : Matrix Ω Ω ℝ) - resetKernel μ := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      resetKernel_idem hprob]
    abel
  calc parSemigroup μ L ρ t
      = NormedSpace.exp (t • L
          + (-(ρ * t)) • ((1 : Matrix Ω Ω ℝ) - resetKernel μ)) := by
        rw [parSemigroup, hsplit]
    _ = locSemigroup L t
        * NormedSpace.exp ((-(ρ * t)) • ((1 : Matrix Ω Ω ℝ) - resetKernel μ)) :=
        Matrix.exp_add_of_commute _ _ hcomm
    _ = locSemigroup L t * ((1 : Matrix Ω Ω ℝ)
        + (Real.exp (-(ρ * t)) - 1) • ((1 : Matrix Ω Ω ℝ) - resetKernel μ)) := by
        rw [exp_smul_idem hidem]
    _ = locSemigroup L t + (Real.exp (-(ρ * t)) - 1)
        • (locSemigroup L t - resetKernel μ) := by
        rw [Matrix.mul_add, Matrix.mul_one, mul_smul_comm, Matrix.mul_sub,
          Matrix.mul_one, loc_mul_reset hrow]
    _ = Real.exp (-(ρ * t)) • locSemigroup L t
        + (1 - Real.exp (-(ρ * t))) • resetKernel μ := by module

include hprob hrow hrev in
/-- The parent semigroup fixes the reset kernel on the right. -/
theorem par_mul_reset (ρ t : ℝ) :
    parSemigroup μ L ρ t * resetKernel μ = resetKernel μ := by
  rw [par_convex hprob hrow hrev, Matrix.add_mul, smul_mul_assoc, smul_mul_assoc,
    loc_mul_reset hrow, resetKernel_idem hprob]
  module

include hprob hrow hrev in
/-- The reset kernel absorbs the parent semigroup on the left. -/
theorem reset_mul_par (ρ t : ℝ) :
    resetKernel μ * parSemigroup μ L ρ t = resetKernel μ := by
  rw [par_convex hprob hrow hrev, Matrix.mul_add, mul_smul_comm, mul_smul_comm,
    reset_mul_loc hrow hrev, resetKernel_idem hprob]
  module

include hprob hrow hrev in
/-- **(CYD.3)**: exact removal of the auxiliary refresh:
`P^par(t) = R + e^{-ρt} Q P^loc(t) Q` with `Q = 1 - R`. -/
theorem derefresh_forward (ρ t : ℝ) :
    parSemigroup μ L ρ t
      = resetKernel μ
        + Real.exp (-(ρ * t)) • (((1 : Matrix Ω Ω ℝ) - resetKernel μ)
            * locSemigroup L t * ((1 : Matrix Ω Ω ℝ) - resetKernel μ)) := by
  have hQPQ : ((1 : Matrix Ω Ω ℝ) - resetKernel μ) * locSemigroup L t
      * ((1 : Matrix Ω Ω ℝ) - resetKernel μ)
      = locSemigroup L t - resetKernel μ := by
    calc ((1 : Matrix Ω Ω ℝ) - resetKernel μ) * locSemigroup L t
        * ((1 : Matrix Ω Ω ℝ) - resetKernel μ)
        = (locSemigroup L t - resetKernel μ)
          * ((1 : Matrix Ω Ω ℝ) - resetKernel μ) := by
          rw [Matrix.sub_mul, Matrix.one_mul, reset_mul_loc hrow hrev]
      _ = locSemigroup L t - resetKernel μ := by
          rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, loc_mul_reset hrow,
            resetKernel_idem hprob, sub_self, sub_zero]
  rw [hQPQ, par_convex hprob hrow hrev]
  module

include hprob hrow hrev in
/-- **(CYD.4)**: the inverse de-refreshing identity:
`P^loc(t) = R + e^{ρt} Q P^par(t) Q` with `Q = 1 - R`. -/
theorem derefresh_inverse (ρ t : ℝ) :
    locSemigroup L t
      = resetKernel μ
        + Real.exp (ρ * t) • (((1 : Matrix Ω Ω ℝ) - resetKernel μ)
            * parSemigroup μ L ρ t * ((1 : Matrix Ω Ω ℝ) - resetKernel μ)) := by
  have hQPQ : ((1 : Matrix Ω Ω ℝ) - resetKernel μ) * parSemigroup μ L ρ t
      * ((1 : Matrix Ω Ω ℝ) - resetKernel μ)
      = Real.exp (-(ρ * t)) • (locSemigroup L t - resetKernel μ) := by
    calc ((1 : Matrix Ω Ω ℝ) - resetKernel μ) * parSemigroup μ L ρ t
        * ((1 : Matrix Ω Ω ℝ) - resetKernel μ)
        = (parSemigroup μ L ρ t - resetKernel μ)
          * ((1 : Matrix Ω Ω ℝ) - resetKernel μ) := by
          rw [Matrix.sub_mul, Matrix.one_mul, reset_mul_par hprob hrow hrev]
      _ = parSemigroup μ L ρ t - resetKernel μ := by
          rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul,
            par_mul_reset hprob hrow hrev, resetKernel_idem hprob, sub_self, sub_zero]
      _ = Real.exp (-(ρ * t)) • (locSemigroup L t - resetKernel μ) := by
          rw [par_convex hprob hrow hrev]
          module
  rw [hQPQ, smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]
  abel

/-- The finite carré-du-champ of a kernel `P` and a vector writer `F`:
`Γ_P(F)(x) = Σ_y P(x,y) (F y - F x)(F y - F x)^*`. -/
noncomputable def carre {d : Type*} (P : Matrix Ω Ω ℝ) (F : Ω → d → ℂ)
    (x : Ω) : Matrix d d ℂ :=
  ∑ y, P x y • Matrix.vecMulVec (F y - F x) (star (F y - F x))

include hprob hrow hrev in
/-- **(CYD.5)**: the pointwise convex carré-du-champ split
`Γ_{P^par(t)}(F) = a Γ_{P^loc(t)}(F) + (1-a) Γ_R(F)`, `a = e^{-ρt}`;
the local carré-du-champ writer is reconstructed by subtracting the explicit
stationary-reset term. -/
theorem carre_split {d : Type*} (ρ t : ℝ) (F : Ω → d → ℂ) (x : Ω) :
    carre (parSemigroup μ L ρ t) F x
      = Real.exp (-(ρ * t)) • carre (locSemigroup L t) F x
        + (1 - Real.exp (-(ρ * t))) • carre (resetKernel μ) F x := by
  unfold carre
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hentry : parSemigroup μ L ρ t x y
      = Real.exp (-(ρ * t)) * locSemigroup L t x y
        + (1 - Real.exp (-(ρ * t))) * resetKernel μ x y := by
    rw [par_convex hprob hrow hrev]
    simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hentry, add_smul, mul_smul, mul_smul]

include hrow hrev in
/-- The reset kernel absorbs every power of the local semigroup on the left. -/
theorem reset_mul_locPow (t : ℝ) (n : ℕ) :
    resetKernel μ * locSemigroup L t ^ n = resetKernel μ := by
  induction n with
  | zero => rw [pow_zero, Matrix.mul_one]
  | succ n ih => rw [pow_succ, ← Matrix.mul_assoc, ih, reset_mul_loc hrow hrev]

include hrow in
/-- Every power of the local semigroup fixes the reset kernel on the right. -/
theorem locPow_mul_reset (t : ℝ) (n : ℕ) :
    locSemigroup L t ^ n * resetKernel μ = resetKernel μ := by
  induction n with
  | zero => rw [pow_zero, Matrix.one_mul]
  | succ n ih => rw [pow_succ, Matrix.mul_assoc, loc_mul_reset hrow, ih]

include hprob hrow hrev in
/-- Powers of the parent semigroup collapse onto rescaled powers of the local
semigroup plus a reset component. -/
theorem par_pow (ρ t : ℝ) (n : ℕ) :
    parSemigroup μ L ρ t ^ n
      = Real.exp (-(ρ * t)) ^ n • locSemigroup L t ^ n
        + (1 - Real.exp (-(ρ * t)) ^ n) • resetKernel μ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, par_convex hprob hrow hrev]
      rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul, ← pow_succ, ← pow_succ']
      rw [locPow_mul_reset hrow, reset_mul_loc hrow hrev, resetKernel_idem hprob]
      match_scalars <;> ring

section Moments

variable {E' : Type*} [Fintype E'] [DecidableEq E'] {J : Matrix Ω E' ℝ}

omit [Fintype E'] in
include hprob hrow hrev in
/-- **(CYD.6)**: for an isometry `J` into `Ran Q`, the compressed moments
rescale exactly: `M_k^loc = e^{kρt} M_k^par`. -/
theorem moment_rescale (ρ t : ℝ) (_hiso : Jᵀ * J = 1)
    (hRJ : resetKernel μ * J = 0) (n : ℕ) :
    Jᵀ * locSemigroup L t ^ n * J
      = Real.exp (ρ * t) ^ n • (Jᵀ * parSemigroup μ L ρ t ^ n * J) := by
  rw [par_pow hprob hrow hrev, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.mul_assoc (Jᵀ) (resetKernel μ) J, hRJ, Matrix.mul_zero, smul_zero,
    add_zero, smul_smul, ← mul_pow, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
    one_pow, one_smul]

include hprob hrow hrev in
/-- **(CYD.7)**: the lag-two memory innovations rescale by `e^{2ρt}`. -/
theorem innovation_rescale (ρ t : ℝ) (hiso : Jᵀ * J = 1)
    (hRJ : resetKernel μ * J = 0) :
    Jᵀ * locSemigroup L t ^ 2 * J
      - (Jᵀ * locSemigroup L t * J) * (Jᵀ * locSemigroup L t * J)
      = Real.exp (ρ * t) ^ 2 •
        (Jᵀ * parSemigroup μ L ρ t ^ 2 * J
          - (Jᵀ * parSemigroup μ L ρ t * J) * (Jᵀ * parSemigroup μ L ρ t * J)) := by
  have h2 := moment_rescale hprob hrow hrev ρ t hiso hRJ 2
  have h1 := moment_rescale hprob hrow hrev ρ t hiso hRJ 1
  rw [pow_one, pow_one, pow_one] at h1
  rw [h2, h1, smul_mul_smul_comm, smul_sub]
  match_scalars <;> ring

omit [DecidableEq E'] in
include hprob hrow hrev in
/-- The leakage operator acquires the single scalar `e^{-ρt}` under
refreshing. -/
theorem leak_scale (ρ t : ℝ) (hRJ : resetKernel μ * J = 0) :
    ((1 : Matrix Ω Ω ℝ) - J * Jᵀ) * parSemigroup μ L ρ t * J
      = Real.exp (-(ρ * t))
        • (((1 : Matrix Ω Ω ℝ) - J * Jᵀ) * locSemigroup L t * J) := by
  rw [par_convex hprob hrow hrev, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.mul_assoc ((1 : Matrix Ω Ω ℝ) - J * Jᵀ) (resetKernel μ) J, hRJ,
    Matrix.mul_zero, smul_zero, add_zero]

include hprob hrow hrev in
/-- The normalized polar innovation is unchanged by de-refreshing:
the trace-normalized lag-two innovations of the parent and local packets are
proportional with the same constant on both sides. -/
theorem polar_innovation_invariant (ρ t : ℝ) (hiso : Jᵀ * J = 1)
    (hRJ : resetKernel μ * J = 0) :
    (Jᵀ * parSemigroup μ L ρ t ^ 2 * J
        - (Jᵀ * parSemigroup μ L ρ t * J) * (Jᵀ * parSemigroup μ L ρ t * J)).trace •
      (Jᵀ * locSemigroup L t ^ 2 * J
        - (Jᵀ * locSemigroup L t * J) * (Jᵀ * locSemigroup L t * J))
    = (Jᵀ * locSemigroup L t ^ 2 * J
        - (Jᵀ * locSemigroup L t * J) * (Jᵀ * locSemigroup L t * J)).trace •
      (Jᵀ * parSemigroup μ L ρ t ^ 2 * J
        - (Jᵀ * parSemigroup μ L ρ t * J) * (Jᵀ * parSemigroup μ L ρ t * J)) := by
  rw [innovation_rescale hprob hrow hrev ρ t hiso hRJ, trace_smul]
  match_scalars <;> ring

end Moments

end Identities

end Derefresh

/-! ### `cth:SMYM-refresh-gap` — The parent refresh is not Yang–Mills coercivity

Rendering: on a finite state space with nonnegative stationary weight `μ`,
a reversible Markov generator `L` (zero row sums, nonnegative off-diagonal
rates, `μ`-detailed balance) has nonnegative centred Dirichlet energy, so the
refreshed generator `ρ(R-1) + L` satisfies the quadratic-form bound
`⟨f, -L^par f⟩_μ ≥ ρ ⟨f, f⟩_μ` for every `μ`-centred `f` — for **every**
such local generator and every `ρ > 0`.  The zero generator on the uniform
two-point space is an admissible reversible generator whose centred Dirichlet
energy vanishes on the nonzero centred vector `(1,-1)` (centred gap `0`),
witnessing that the refresh gap carries no local coercivity information. -/

namespace RefreshGap

open RefreshCalculus

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
variable {μ : Ω → ℝ} {L : Matrix Ω Ω ℝ}

/-- The `μ`-weighted quadratic form `⟨f, A f⟩_μ = Σ_x μ(x) f(x) (A f)(x)`. -/
def quadratic (μ : Ω → ℝ) (A : Matrix Ω Ω ℝ) (f : Ω → ℝ) : ℝ :=
  ∑ x, μ x * (f x * (A *ᵥ f) x)

variable (hrow : ∀ x, ∑ y, L x y = 0)
  (hrev : ∀ x y, μ x * L x y = μ y * L y x)

omit [DecidableEq Ω] in
include hrow hrev in
/-- The Dirichlet-form identity for a reversible zero-row-sum generator:
`⟨f, -L f⟩_μ = ½ Σ_{x,y} μ(x) L(x,y) (f(y) - f(x))²`. -/
theorem quadratic_gen_eq (f : Ω → ℝ) :
    -(quadratic μ L f)
      = (1 / 2) * ∑ x, ∑ y, μ x * L x y * (f y - f x) ^ 2 := by
  have hexp : quadratic μ L f = ∑ x, ∑ y, μ x * L x y * (f x * f y) := by
    unfold quadratic
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  have h1 : ∑ x, ∑ y, μ x * L x y * f y ^ 2 = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun y _ => ?_
    have hz : ∑ x, μ x * L x y = 0 := by
      calc ∑ x, μ x * L x y
          = ∑ x, μ y * L y x := Finset.sum_congr rfl fun x _ => hrev x y
        _ = μ y * ∑ x, L y x := (Finset.mul_sum _ _ _).symm
        _ = 0 := by rw [hrow, mul_zero]
    calc ∑ x, μ x * L x y * f y ^ 2
        = (∑ x, μ x * L x y) * f y ^ 2 := (Finset.sum_mul _ _ _).symm
      _ = 0 := by rw [hz, zero_mul]
  have h2 : ∑ x, ∑ y, μ x * L x y * f x ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    calc ∑ y, μ x * L x y * f x ^ 2
        = (μ x * f x ^ 2) * ∑ y, L x y := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ => by ring
      _ = 0 := by rw [hrow, mul_zero]
  have key : ∑ x, ∑ y, (μ x * L x y * (f y - f x) ^ 2
      + 2 * (μ x * L x y * (f x * f y)))
      = ∑ x, ∑ y, (μ x * L x y * f y ^ 2 + μ x * L x y * f x ^ 2) :=
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  simp only [Finset.sum_add_distrib] at key
  rw [h1, h2] at key
  have hpull : ∑ x, ∑ y, 2 * (μ x * L x y * (f x * f y))
      = 2 * ∑ x, ∑ y, μ x * L x y * (f x * f y) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => (Finset.mul_sum _ _ _).symm
  rw [hpull, ← hexp] at key
  linarith [key]

omit [DecidableEq Ω] in
include hrow hrev in
/-- Nonnegativity of the centred Dirichlet energy of a reversible Markov
generator. -/
theorem quadratic_gen_nonneg (hoff : ∀ x y, x ≠ y → 0 ≤ L x y)
    (hμ : ∀ x, 0 ≤ μ x) (f : Ω → ℝ) :
    0 ≤ -(quadratic μ L f) := by
  rw [quadratic_gen_eq hrow hrev]
  refine mul_nonneg (by norm_num) ?_
  refine Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_
  by_cases hxy : x = y
  · subst hxy
    simp
  · have h1 := hoff x y hxy
    have h2 := hμ x
    positivity

include hrow hrev in
/-- **`cth:SMYM-refresh-gap`**: for every reversible Markov generator and
every `ρ > 0`, the refreshed generator dominates `ρ` on the centred space:
`⟨f, -(ρ(R-1)+L) f⟩_μ ≥ ρ ⟨f, f⟩_μ` for `μ`-centred `f`. -/
theorem refresh_gap (hoff : ∀ x y, x ≠ y → 0 ≤ L x y) (hμ : ∀ x, 0 ≤ μ x)
    {ρ : ℝ} (_hρ : 0 < ρ) (f : Ω → ℝ) (hc : ∑ x, μ x * f x = 0) :
    ρ * ∑ x, μ x * f x ^ 2
      ≤ quadratic μ (-(ρ • (resetKernel μ - 1) + L)) f := by
  have hR : (resetKernel μ *ᵥ f) = 0 := by
    funext x
    simp only [Matrix.mulVec, dotProduct, resetKernel, Matrix.of_apply, Pi.zero_apply]
    exact hc
  have hsplit : ∀ x, ((-(ρ • (resetKernel μ - 1) + L)) *ᵥ f) x
      = ρ * f x - (L *ᵥ f) x := by
    intro x
    rw [Matrix.neg_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec, hR]
    simp only [Pi.neg_apply, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.zero_apply,
      Matrix.one_mulVec, smul_eq_mul]
    ring
  have hq : quadratic μ (-(ρ • (resetKernel μ - 1) + L)) f
      = ρ * (∑ x, μ x * f x ^ 2) - quadratic μ L f := by
    unfold quadratic
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hsplit x]
    ring
  have hpos := quadratic_gen_nonneg hrow hrev hoff hμ f
  rw [hq]
  linarith

/-- The uniform two-point law. -/
noncomputable def unifTwo : Fin 2 → ℝ := fun _ => 1 / 2

/-- The centred spin witness `(1, -1)`. -/
def spinF : Fin 2 → ℝ := ![1, -1]

/-- The zero generator on the uniform two-point space is an admissible
reversible Markov generator (zero rows, detailed balance, nonnegative rates)
whose centred Dirichlet energy vanishes on the nonzero centred unit vector
`(1,-1)`: its centred gap is zero, while `refresh_gap` still applies for
every `ρ > 0`. -/
theorem zero_gap_witness :
    (∀ x, ∑ y, (0 : Matrix (Fin 2) (Fin 2) ℝ) x y = 0) ∧
    (∀ x y, unifTwo x * (0 : Matrix (Fin 2) (Fin 2) ℝ) x y
        = unifTwo y * (0 : Matrix (Fin 2) (Fin 2) ℝ) y x) ∧
    (∀ x y, x ≠ y → 0 ≤ (0 : Matrix (Fin 2) (Fin 2) ℝ) x y) ∧
    (∑ x, unifTwo x * spinF x = 0) ∧ spinF ≠ 0 ∧
    -(quadratic unifTwo (0 : Matrix (Fin 2) (Fin 2) ℝ) spinF) = 0 ∧
    ∑ x, unifTwo x * spinF x ^ 2 = 1 := by
  refine ⟨fun x => by simp, fun x y => by simp, fun x y _ => le_refl _, ?_, ?_, ?_, ?_⟩
  · simp [Fin.sum_univ_two, unifTwo, spinF]
  · intro h
    have h0 := congrFun h 0
    simp [spinF] at h0
  · unfold quadratic
    simp
  · simp [Fin.sum_univ_two, unifTwo, spinF]
    norm_num

end RefreshGap

/-! ### `cth:SMST-static-Weyl-no-clock` — Static Weyl law and the transfer clock

Rendering: the rate-`a` flip process on `{-1,+1}` is the finite Markov chain
with generator `[[-a,a],[a,-a]] = 2a(R - 1)` (with `R` the uniform reset
kernel) and transfer semigroup the literal matrix exponential.  We prove: the
transfer matrix in closed form; stationarity of the uniform law and
stochasticity of the rows; the one-time static characteristic
`Φ(t) = ½e^{it} + ½e^{-it} = cos t` for every rate `a` (manifestly
`a`-independent); the boxed lag correlation (BS.12a)
`E[X₀ X_τ] = Σ_{x,y} π(x) x P_τ(x,y) y = e^{-2aτ}` (the two-time law of the
stationary chain is rendered as `π ⊗ P_τ`); and the generator eigenvalue
`2a` on the nonzero spin vector. -/

namespace StaticWeylClock

open RefreshCalculus

/-- The spin observable `X : {0,1} → {1,-1}`. -/
def spinVal : Fin 2 → ℝ := ![1, -1]

/-- The rate-`a` flip generator `2a (R - 1) = [[-a,a],[a,-a]]`. -/
noncomputable def flipGen (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (2 * a) • (resetKernel (fun _ => 1 / 2) - 1)

/-- The flip generator in matrix form. -/
theorem flipGen_eq (a : ℝ) : flipGen a = !![-a, a; a, -a] := by
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [flipGen, resetKernel] <;> ring

/-- The transfer semigroup `P_τ = e^{τ Q_a}`. -/
noncomputable def transfer (a τ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  NormedSpace.exp (τ • flipGen a)

/-- The transfer semigroup in closed convex form. -/
theorem transfer_eq (a τ : ℝ) :
    transfer a τ
      = Real.exp (-(2 * a * τ)) • 1
        + (1 - Real.exp (-(2 * a * τ))) • resetKernel (fun _ => (1 : ℝ) / 2) := by
  have hprob : ∑ _x : Fin 2, ((1 : ℝ) / 2) = 1 := by
    simp
  have hidem : ((1 : Matrix (Fin 2) (Fin 2) ℝ) - resetKernel (fun _ => (1 : ℝ) / 2))
      * ((1 : Matrix (Fin 2) (Fin 2) ℝ) - resetKernel (fun _ => (1 : ℝ) / 2))
      = (1 : Matrix (Fin 2) (Fin 2) ℝ) - resetKernel (fun _ => (1 : ℝ) / 2) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      resetKernel_idem hprob]
    abel
  have hsm : τ • flipGen a
      = (-(2 * a * τ)) • ((1 : Matrix (Fin 2) (Fin 2) ℝ)
          - resetKernel (fun _ => (1 : ℝ) / 2)) := by
    unfold flipGen
    module
  rw [transfer, hsm, exp_smul_idem hidem]
  module

/-- The transfer matrix entries: `(1 ± e^{-2aτ})/2`. -/
theorem transfer_apply (a τ : ℝ) (x y : Fin 2) :
    transfer a τ x y
      = if x = y then (1 + Real.exp (-(2 * a * τ))) / 2
        else (1 - Real.exp (-(2 * a * τ))) / 2 := by
  rw [transfer_eq]
  fin_cases x <;> fin_cases y <;>
    simp [resetKernel] <;> ring

/-- The uniform law is stationary for the flip transfer at every rate. -/
theorem uniform_stationary (a τ : ℝ) :
    (fun _ => (1 : ℝ) / 2) ᵥ* transfer a τ = fun _ => (1 : ℝ) / 2 := by
  funext y
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  fin_cases y <;> rw [transfer_apply, transfer_apply] <;> norm_num <;> ring

/-- The flip transfer is stochastic (rows sum to one) at every rate. -/
theorem transfer_stochastic (a τ : ℝ) :
    transfer a τ *ᵥ (fun _ => (1 : ℝ)) = fun _ => (1 : ℝ) := by
  funext x
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  fin_cases x <;> rw [transfer_apply, transfer_apply] <;> norm_num <;> ring

/-- The one-time static characteristic functional of the rate-`a` chain. -/
noncomputable def staticChar (_a : ℝ) (t : ℝ) : ℂ :=
  ∑ x, ((1 : ℂ) / 2) * Complex.exp ((t : ℂ) * (spinVal x : ℝ) * Complex.I)

/-- For every rate `a`, the complete one-time characteristic functional is
`Φ(t) = cos t`. -/
theorem staticChar_eq_cos (a t : ℝ) : staticChar a t = Complex.cos t := by
  unfold staticChar
  rw [Fin.sum_univ_two]
  have h0 : ((spinVal 0 : ℝ) : ℂ) = 1 := by norm_num [spinVal]
  have h1 : ((spinVal 1 : ℝ) : ℂ) = -1 := by norm_num [spinVal]
  rw [h0, h1]
  have e0 : (t : ℂ) * 1 * Complex.I = (t : ℂ) * Complex.I := by ring
  have e1 : (t : ℂ) * (-1) * Complex.I = (-(t : ℂ)) * Complex.I := by ring
  rw [e0, e1, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  ring

/-- The static characteristic functional is independent of the rate. -/
theorem staticChar_indep (a a' t : ℝ) : staticChar a t = staticChar a' t := by
  rw [staticChar_eq_cos, staticChar_eq_cos]

/-- The stationary two-time correlation `E[X₀ X_τ]` of the rate-`a` chain. -/
noncomputable def lagCorrelation (a τ : ℝ) : ℝ :=
  ∑ x, ∑ y, (1 / 2) * spinVal x * transfer a τ x y * spinVal y

/-- **(BS.12a)**: `E[X₀ X_τ] = e^{-2aτ}` — the lag Weyl kernel depends on the
rate `a` although the complete static law does not. -/
theorem lag_correlation (a τ : ℝ) : lagCorrelation a τ = Real.exp (-(2 * a * τ)) := by
  unfold lagCorrelation
  simp only [Fin.sum_univ_two, transfer_apply, spinVal]
  norm_num
  ring

/-- The nonzero generator eigenvalue is `2a`: `(-Q_a) X = 2a X` on the
nonzero spin vector. -/
theorem generator_eigenvalue (a : ℝ) :
    (-(flipGen a)) *ᵥ spinVal = (2 * a) • spinVal ∧ spinVal ≠ 0 := by
  constructor
  · funext x
    fin_cases x <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, flipGen_eq, spinVal] <;> ring
  · intro h
    have h0 := congrFun h 0
    simp [spinVal] at h0

end StaticWeylClock

/-! ### `thm:SMST-positive-time-transport-rectangle` — Delayed-source transport

Rendering: at four consecutive cutoffs, the delayed semigroups `P_{i,t}`,
carrier transports `U_i`, coefficient transports `V_i` and source banks
`Ψ_i` are finite complex matrices at one fixed physical delay `t` (the
identities are pointwise in `t`).  With the entrance and semigroup defects
of (PT.13), the delayed-source defect
`D_i(t) = P_{i+1,t}Ψ_{i+1}V_i - U_iP_{i,t}Ψ_i` satisfies the boxed identity
(PT.14), and the four-cutoff direct defect telescopes as in (PT.15).  The
transport of a strict delayed Gram floor by small complete defects is
rendered quantitatively by the exact positive-splitting bound
`(Y+D)ᴴ(Y+D) ⪰ ((1-θ)m - (θ⁻¹-1)ε²)·1` for every `θ ∈ (0,1]`, given
`YᴴY ⪰ m·1` and `DᴴD ⪯ ε²·1`; a one-dimensional witness shows that a
vanishing direct endpoint defect does not make the adjacent defects small. -/

namespace TransportRect

section Rectangle

variable {h₁ h₂ h₃ h₄ e₁ e₂ e₃ e₄ : Type*}
variable [Fintype h₁] [Fintype h₂] [Fintype h₃] [Fintype h₄]
variable [Fintype e₂] [Fintype e₃] [Fintype e₄]

/-- **(PT.14)**: the delayed-source defect is
`D_i(t) = P_{i+1,t}A_i + S_i(t)Ψ_i`, with `A_i = Ψ_{i+1}V_i - U_iΨ_i` and
`S_i(t) = P_{i+1,t}U_i - U_iP_{i,t}`. -/
theorem delayed_defect (P₁ : Matrix h₁ h₁ ℂ) (P₂ : Matrix h₂ h₂ ℂ)
    (Ψ₁ : Matrix h₁ e₁ ℂ) (Ψ₂ : Matrix h₂ e₂ ℂ) (U₁ : Matrix h₂ h₁ ℂ)
    (V₁ : Matrix e₂ e₁ ℂ) :
    P₂ * Ψ₂ * V₁ - U₁ * P₁ * Ψ₁
      = P₂ * (Ψ₂ * V₁ - U₁ * Ψ₁) + (P₂ * U₁ - U₁ * P₁) * Ψ₁ := by
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

/-- **(PT.15)**: for four consecutive cutoffs the direct delayed defect
telescopes: `D_{4:1}(t) = D₃(t)V_{3:1} + U₃D₂(t)V_{2:1} + U₃U₂D₁(t)`. -/
theorem transport_rectangle (P₁ : Matrix h₁ h₁ ℂ) (P₂ : Matrix h₂ h₂ ℂ)
    (P₃ : Matrix h₃ h₃ ℂ) (P₄ : Matrix h₄ h₄ ℂ)
    (Ψ₁ : Matrix h₁ e₁ ℂ) (Ψ₂ : Matrix h₂ e₂ ℂ) (Ψ₃ : Matrix h₃ e₃ ℂ)
    (Ψ₄ : Matrix h₄ e₄ ℂ)
    (U₁ : Matrix h₂ h₁ ℂ) (U₂ : Matrix h₃ h₂ ℂ) (U₃ : Matrix h₄ h₃ ℂ)
    (V₁ : Matrix e₂ e₁ ℂ) (V₂ : Matrix e₃ e₂ ℂ) (V₃ : Matrix e₄ e₃ ℂ) :
    P₄ * Ψ₄ * (V₃ * V₂ * V₁) - (U₃ * U₂ * U₁) * P₁ * Ψ₁
      = (P₄ * Ψ₄ * V₃ - U₃ * P₃ * Ψ₃) * (V₂ * V₁)
        + U₃ * (P₃ * Ψ₃ * V₂ - U₂ * P₂ * Ψ₂) * V₁
        + U₃ * U₂ * (P₂ * Ψ₂ * V₁ - U₁ * P₁ * Ψ₁) := by
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

end Rectangle

section Floor

variable {k e : Type*} [Fintype k] [Finite e] [DecidableEq e]

/-- Summable complete delayed defects transport every strict delayed Gram
floor: for `θ ∈ (0,1]`, a floor `YᴴY ⪰ m·1` and a defect bound
`DᴴD ⪯ ε²·1` give `(Y+D)ᴴ(Y+D) ⪰ ((1-θ)m - (θ⁻¹-1)ε²)·1` exactly. -/
theorem floor_transport (Y D : Matrix k e ℂ) (m ε θ : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hfloor : (Yᴴ * Y - m • (1 : Matrix e e ℂ)).PosSemidef)
    (hdef : (ε ^ 2 • (1 : Matrix e e ℂ) - Dᴴ * D).PosSemidef) :
    ((Y + D)ᴴ * (Y + D)
      - ((1 - θ) * m - (θ⁻¹ - 1) * ε ^ 2) • (1 : Matrix e e ℂ)).PosSemidef := by
  have := Fintype.ofFinite e
  set s : ℝ := Real.sqrt θ with hs
  set r : ℝ := Real.sqrt θ⁻¹ with hr
  have hss : s * s = θ := Real.mul_self_sqrt hθ0.le
  have hrr : r * r = θ⁻¹ := Real.mul_self_sqrt (by positivity)
  have hsr : s * r = 1 := by
    rw [hs, hr, Real.sqrt_inv]
    exact mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hθ0))
  have hkey : (Y + D)ᴴ * (Y + D)
      - ((1 - θ) * m - (θ⁻¹ - 1) * ε ^ 2) • (1 : Matrix e e ℂ)
      = (1 - θ) • (Yᴴ * Y - m • (1 : Matrix e e ℂ))
        + (θ⁻¹ - 1) • (ε ^ 2 • (1 : Matrix e e ℂ) - Dᴴ * D)
        + (s • Y + r • D)ᴴ * (s • Y + r • D) := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, star_trivial,
      Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
    match_scalars
    · linear_combination -hss
    · linear_combination -hsr
    · linear_combination -hsr
    · linear_combination -hrr
    · ring
  rw [hkey]
  have h1 : (0 : ℝ) ≤ 1 - θ := by linarith
  have h2 : (0 : ℝ) ≤ θ⁻¹ - 1 := by
    have : (1 : ℝ) ≤ θ⁻¹ := (one_le_inv₀ hθ0).mpr hθ1
    linarith
  exact ((hfloor.smul h1).add (hdef.smul h2)).add
    (posSemidef_conjTranspose_mul_self _)

/-- A vanishing direct endpoint defect does not make adjacent defects small:
on one-dimensional data with unit transports and semigroups and source banks
`Ψ = (0, 1, 0, 0)`, the direct four-cutoff defect vanishes while the first
adjacent defect is `1 ≠ 0`. -/
theorem endpoint_defect_witness :
    ((1 : Matrix (Fin 1) (Fin 1) ℂ) * (0 : Matrix (Fin 1) (Fin 1) ℂ) * (1 * 1 * 1)
        - (1 * 1 * 1) * (1 : Matrix (Fin 1) (Fin 1) ℂ) * (0 : Matrix (Fin 1) (Fin 1) ℂ)
        = 0)
      ∧ (1 : Matrix (Fin 1) (Fin 1) ℂ) * (1 : Matrix (Fin 1) (Fin 1) ℂ) * 1
          - 1 * (1 : Matrix (Fin 1) (Fin 1) ℂ) * (0 : Matrix (Fin 1) (Fin 1) ℂ) ≠ 0 := by
  constructor
  · simp
  · intro h
    have h0 := congrFun (congrFun h 0) 0
    simp at h0

end Floor

end TransportRect

/-! ### `thm:SMST-routed-electromagnetic-transport` — Routed transport

Rendering: the raw coefficient transports `U_i`, physical-bank transports
`V_i`, carrier transports `𝖳_i`, syntheses `B_i`, routers `R_i` and raw
positive forms `C_i` at two adjacent cutoffs are finite complex matrices,
with the defects `A_i^R = R_{i+1}V_i - U_iR_i` and
`A_i^B = B_{i+1}U_i - 𝖳_iB_i` of (EMR.22).  (EMR.23) and (EMR.24) are exact
matrix identities; the same-history averaged and delayed-KMS/OS-kernel
versions are proved by instantiating the identity at every history weight
and every kernel delay; exact path blocking makes `A_i^R = 0`; and a
one-dimensional separately refitted coarse twist has `A_i^R ≠ 0`. -/

namespace RoutedTransport

variable {p₁ p₂ r₁ r₂ k₁ k₂ : Type*}
variable [Fintype p₁] [Fintype p₂] [Fintype r₁] [Fintype r₂] [Fintype k₁] [Fintype k₂]

omit [Fintype p₁] [Fintype k₂] in
/-- **(EMR.23)**: the physical source defect decomposes exactly as
`B_{i+1}R_{i+1}V_i - 𝖳_iB_iR_i = A_i^B R_i + B_{i+1} A_i^R`. -/
theorem routed_source_defect (B₁ : Matrix k₁ r₁ ℂ) (B₂ : Matrix k₂ r₂ ℂ)
    (T₁ : Matrix k₂ k₁ ℂ) (U₁ : Matrix r₂ r₁ ℂ) (V₁ : Matrix p₂ p₁ ℂ)
    (R₁ : Matrix r₁ p₁ ℂ) (R₂ : Matrix r₂ p₂ ℂ) :
    B₂ * R₂ * V₁ - T₁ * B₁ * R₁
      = (B₂ * U₁ - T₁ * B₁) * R₁ + B₂ * (R₂ * V₁ - U₁ * R₁) := by
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

omit [Fintype p₁] in
/-- **(EMR.24)**: the routed-form congruence expansion for a raw positive
form `C_i`. -/
theorem routed_form_congruence (U₁ : Matrix r₂ r₁ ℂ) (V₁ : Matrix p₂ p₁ ℂ)
    (R₁ : Matrix r₁ p₁ ℂ) (R₂ : Matrix r₂ p₂ ℂ)
    (C₁ : Matrix r₁ r₁ ℂ) (C₂ : Matrix r₂ r₂ ℂ) :
    V₁ᴴ * R₂ᴴ * C₂ * R₂ * V₁ - R₁ᴴ * C₁ * R₁
      = R₁ᴴ * (U₁ᴴ * C₂ * U₁ - C₁) * R₁
        + R₁ᴴ * U₁ᴴ * C₂ * (R₂ * V₁ - U₁ * R₁)
        + (R₂ * V₁ - U₁ * R₁)ᴴ * C₂ * (U₁ * R₁)
        + (R₂ * V₁ - U₁ * R₁)ᴴ * C₂ * (R₂ * V₁ - U₁ * R₁) := by
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_assoc]
  abel

omit [Fintype p₁] in
/-- (EMR.24) after same-history averaging: the identity persists under any
finite weighted average over unquenched histories. -/
theorem routed_form_congruence_averaged {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (U₁ : ι → Matrix r₂ r₁ ℂ) (V₁ : ι → Matrix p₂ p₁ ℂ)
    (R₁ : ι → Matrix r₁ p₁ ℂ) (R₂ : ι → Matrix r₂ p₂ ℂ)
    (C₁ : ι → Matrix r₁ r₁ ℂ) (C₂ : ι → Matrix r₂ r₂ ℂ) :
    ∑ ω, w ω • ((V₁ ω)ᴴ * (R₂ ω)ᴴ * C₂ ω * R₂ ω * V₁ ω - (R₁ ω)ᴴ * C₁ ω * R₁ ω)
      = ∑ ω, w ω •
        ((R₁ ω)ᴴ * ((U₁ ω)ᴴ * C₂ ω * U₁ ω - C₁ ω) * R₁ ω
          + (R₁ ω)ᴴ * (U₁ ω)ᴴ * C₂ ω * (R₂ ω * V₁ ω - U₁ ω * R₁ ω)
          + (R₂ ω * V₁ ω - U₁ ω * R₁ ω)ᴴ * C₂ ω * (U₁ ω * R₁ ω)
          + (R₂ ω * V₁ ω - U₁ ω * R₁ ω)ᴴ * C₂ ω * (R₂ ω * V₁ ω - U₁ ω * R₁ ω)) :=
  Finset.sum_congr rfl fun ω _ => by
    rw [routed_form_congruence]

omit [Fintype p₁] in
/-- (EMR.24) for every delayed KMS/OS kernel: the identity holds at every
delay of arbitrary kernel families `C_i(s)`. -/
theorem routed_form_congruence_delayed (U₁ : Matrix r₂ r₁ ℂ) (V₁ : Matrix p₂ p₁ ℂ)
    (R₁ : Matrix r₁ p₁ ℂ) (R₂ : Matrix r₂ p₂ ℂ)
    (K₁ : ℝ → Matrix r₁ r₁ ℂ) (K₂ : ℝ → Matrix r₂ r₂ ℂ) (s : ℝ) :
    V₁ᴴ * R₂ᴴ * K₂ s * R₂ * V₁ - R₁ᴴ * K₁ s * R₁
      = R₁ᴴ * (U₁ᴴ * K₂ s * U₁ - K₁ s) * R₁
        + R₁ᴴ * U₁ᴴ * K₂ s * (R₂ * V₁ - U₁ * R₁)
        + (R₂ * V₁ - U₁ * R₁)ᴴ * K₂ s * (U₁ * R₁)
        + (R₂ * V₁ - U₁ * R₁)ᴴ * K₂ s * (R₂ * V₁ - U₁ * R₁) :=
  routed_form_congruence U₁ V₁ R₁ R₂ (K₁ s) (K₂ s)

omit [Fintype p₁] [Fintype r₂] in
/-- Exact path blocking gives `A_i^R = 0`: when the routed coefficients are
transported by the primitive jet cocycle, the routing defect vanishes. -/
theorem blocking_defect_zero {U₁ : Matrix r₂ r₁ ℂ} {V₁ : Matrix p₂ p₁ ℂ}
    {R₁ : Matrix r₁ p₁ ℂ} {R₂ : Matrix r₂ p₂ ℂ}
    (hblock : R₂ * V₁ = U₁ * R₁) :
    R₂ * V₁ - U₁ * R₁ = 0 :=
  sub_eq_zero_of_eq hblock

/-- A separately refitted coarse twist need not have `A_i^R = 0`: the
one-dimensional refit `R_{i+1} = 2`, `R_i = U_i = V_i = 1` has defect
`1 ≠ 0`. -/
theorem refit_witness :
    !![(2 : ℂ)] * !![(1 : ℂ)] - !![(1 : ℂ)] * !![(1 : ℂ)] ≠ 0 := by
  intro h
  have h0 := congrFun (congrFun h 0) 0
  norm_num [Matrix.mul_apply] at h0

end RoutedTransport

/-! ### `cor:SMST-electromagnetic-scalar-branch` — Exact scalar aggregation

Rendering: an `m`-link path carries unitary internal holonomies
`U₁, …, U_m` and self-adjoint charge frames `Q₀, …, Q_{m-1}` at the source
vertices, all `0`-indexed; `P_j = U₁⋯U_j` and the routed charges are
`Q̃_{j+1} = P_j Q_j P_j^*`.  The first-jet router is the (EMR.7) formula
`𝒥_γ(u) = Σ_j u_j Q̃_j`.  We prove: the aggregation identity
`𝒥_γ(u) = (Σ u_j) Q₀` for every phase bank holds exactly when every routed
charge equals `Q₀`, and (for unitary holonomies) exactly when the charge
frame is the reverse parallel transport of `Q₀` along the path — covariant
constancy.  The final sentence of the corollary (a coarse scalar twist is a
different physical source outside this branch) is witnessed by
`cth:SMST-electromagnetic-phase-sum` below. -/

namespace ChargeRouter

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The partial holonomy products `P_j = U₁ ⋯ U_j`, `0`-indexed:
`pathProd U 0 = 1` and `pathProd U (j+1) = pathProd U j * U j`. -/
def pathProd (U : ℕ → Matrix d d ℂ) : ℕ → Matrix d d ℂ
  | 0 => 1
  | j + 1 => pathProd U j * U j

/-- The routed charge `Q̃_{j+1} = P_j Q_j P_j^*` of the `(j+1)`-st link. -/
def routedCharge (U Q : ℕ → Matrix d d ℂ) (j : ℕ) : Matrix d d ℂ :=
  pathProd U j * Q j * (pathProd U j)ᴴ

/-- The first-jet router `𝒥_γ(u) = Σ_j u_j Q̃_j` of (EMR.7) on an `m`-link
path. -/
def router (U Q : ℕ → Matrix d d ℂ) (m : ℕ) (u : ℕ → ℂ) : Matrix d d ℂ :=
  ∑ j ∈ Finset.range m, u j • routedCharge U Q j

/-- Partial holonomy products of unitary links are unitary. -/
theorem pathProd_unitary {U : ℕ → Matrix d d ℂ}
    (hU : ∀ j, (U j)ᴴ * U j = 1 ∧ U j * (U j)ᴴ = 1) (n : ℕ) :
    (pathProd U n)ᴴ * pathProd U n = 1
      ∧ pathProd U n * (pathProd U n)ᴴ = 1 := by
  induction n with
  | zero => simp [pathProd]
  | succ n ih =>
      constructor
      · calc (pathProd U (n + 1))ᴴ * pathProd U (n + 1)
            = (U n)ᴴ * ((pathProd U n)ᴴ * pathProd U n) * U n := by
              simp only [pathProd, Matrix.conjTranspose_mul, Matrix.mul_assoc]
          _ = 1 := by
              rw [ih.1, Matrix.mul_one]
              exact (hU n).1
      · calc pathProd U (n + 1) * (pathProd U (n + 1))ᴴ
            = pathProd U n * (U n * (U n)ᴴ) * (pathProd U n)ᴴ := by
              simp only [pathProd, Matrix.conjTranspose_mul, Matrix.mul_assoc]
          _ = 1 := by
              rw [(hU n).2, Matrix.mul_one, ih.2]

/-- **`cor:SMST-electromagnetic-scalar-branch`**: the scalar aggregation
`𝒥_γ(u) = (Σ_j u_j) Q₀` holds for every phase bank exactly when every
routed charge equals `Q₀`. -/
theorem scalar_aggregation_iff (U Q : ℕ → Matrix d d ℂ) (m : ℕ)
    (Q₀ : Matrix d d ℂ) :
    (∀ u : ℕ → ℂ, router U Q m u = (∑ j ∈ Finset.range m, u j) • Q₀)
      ↔ ∀ j < m, routedCharge U Q j = Q₀ := by
  constructor
  · intro h j hj
    have hu := h fun k => if k = j then 1 else 0
    rw [router] at hu
    simp only [ite_smul, one_smul, zero_smul] at hu
    rw [Finset.sum_ite_eq' (Finset.range m) j, Finset.sum_ite_eq' (Finset.range m) j] at hu
    have hmem : j ∈ Finset.range m := Finset.mem_range.mpr hj
    simp only [hmem, ite_true, one_smul] at hu
    exact hu
  · intro h u
    rw [router, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [h j (Finset.mem_range.mp hj)]

/-- The aggregation branch is exactly covariant constancy of the charge
frame along the path: for unitary holonomies, `Q̃_j = Q₀` for every link iff
each frame `Q_j` is the reverse parallel transport `P_j^* Q₀ P_j`. -/
theorem covariantly_constant_iff {U : ℕ → Matrix d d ℂ}
    (hU : ∀ j, (U j)ᴴ * U j = 1 ∧ U j * (U j)ᴴ = 1)
    (Q : ℕ → Matrix d d ℂ) (m : ℕ) (Q₀ : Matrix d d ℂ) :
    (∀ j < m, routedCharge U Q j = Q₀)
      ↔ ∀ j < m, Q j = (pathProd U j)ᴴ * Q₀ * pathProd U j := by
  have key : ∀ j, routedCharge U Q j = Q₀
      ↔ Q j = (pathProd U j)ᴴ * Q₀ * pathProd U j := by
    intro j
    obtain ⟨h1, h2⟩ := pathProd_unitary hU j
    constructor
    · intro h
      rw [← h, routedCharge]
      calc Q j
          = (pathProd U j)ᴴ * pathProd U j * Q j
            * ((pathProd U j)ᴴ * pathProd U j) := by
            rw [h1, Matrix.one_mul, Matrix.mul_one]
        _ = (pathProd U j)ᴴ * (pathProd U j * Q j * (pathProd U j)ᴴ)
            * pathProd U j := by
            simp only [Matrix.mul_assoc]
    · intro h
      rw [routedCharge, h]
      calc pathProd U j * ((pathProd U j)ᴴ * Q₀ * pathProd U j) * (pathProd U j)ᴴ
          = pathProd U j * (pathProd U j)ᴴ * Q₀
            * (pathProd U j * (pathProd U j)ᴴ) := by
            simp only [Matrix.mul_assoc]
        _ = Q₀ := by rw [h2, Matrix.one_mul, Matrix.mul_one]
  exact ⟨fun h j hj => (key j).1 (h j hj), fun h j hj => (key j).2 (h j hj)⟩

end ChargeRouter

/-! ### `cth:SMST-electromagnetic-phase-sum` — Equal phase, unequal current

Rendering: the two-link Pauli witness of (EMR.14).  The first holonomy is
the literal matrix exponential `U₁ = e^{-iπσ₂/4}` (proved by explicit
diagonalization of `σ₂`), the second is the identity, and the charge
`Q = σ₃` is retained at both source vertices.  The phase banks
`u = (1,0)` and `v = (0,1)` have equal scalar sums, while the (EMR.7)
routers are `𝒥_γ(u) = σ₃` and `𝒥_γ(v) = σ₁`, with
`‖σ₃ - σ₁‖ = √2` in the `L²` operator norm, vanishing exact mixed Hermitian
contact `½{σ₃, σ₁} = 0`, and naive scalar aggregation `Q² = 1`.
Throughout, `2^{-1/2}` is rendered as `√2/2`. -/

namespace PhaseSum

open ChargeRouter

/-- The Pauli matrix `σ₁`. -/
def pauli1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli matrix `σ₂`. -/
def pauli2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The Pauli matrix `σ₃`. -/
def pauli3 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The rotation entry `2^{-1/2}`, rendered as `√2/2`. -/
noncomputable def rotEntry : ℂ := ((Real.sqrt 2 / 2 : ℝ) : ℂ)

/-- The rotation `e^{-iπσ₂/4}` in closed form. -/
noncomputable def rotU : Matrix (Fin 2) (Fin 2) ℂ :=
  !![rotEntry, -rotEntry; rotEntry, rotEntry]

/-- The rotation entry is the real cast of `√2/2`. -/
theorem rotEntry_def : rotEntry = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := rfl

/-- The square of the rotation entry: `(√2/2)² = 1/2`. -/
theorem rotEntry_sq : rotEntry * rotEntry = 1 / 2 := by
  rw [rotEntry_def, ← Complex.ofReal_mul]
  have h : (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = 1 / 2 := by
    rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [h]
  norm_num

/-- The rotation entry is real. -/
theorem rotEntry_star : (starRingEnd ℂ) rotEntry = rotEntry :=
  Complex.conj_ofReal _

/-- The diagonalizing frame of `σ₂`. -/
def vFrame : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; Complex.I, -Complex.I]

/-- The inverse diagonalizing frame of `σ₂`. -/
noncomputable def wFrame : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • !![1, -Complex.I; 1, Complex.I]

/-- The frame and its inverse multiply to one. -/
theorem vFrame_mul_wFrame : vFrame * wFrame = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [vFrame, wFrame, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff] <;> ring

set_option linter.flexible false in -- branch-dependent entry normal forms, closed by ring below
/-- **`U₁` is the literal calibrated exponential** `e^{-iπσ₂/4}`. -/
theorem rotU_exp :
    NormedSpace.exp ((((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I) • pauli2) = rotU := by
  have hVW := vFrame_mul_wFrame
  have hWV : wFrame * vFrame = 1 := mul_eq_one_comm.mp hVW
  have hV : IsUnit vFrame := ⟨⟨vFrame, wFrame, hVW, hWV⟩, rfl⟩
  have hVinv : vFrame⁻¹ = wFrame := Matrix.inv_eq_right_inv hVW
  set z : ℂ := ((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I with hz
  have hconj : z • pauli2 = vFrame * Matrix.diagonal ![z, -z] * vFrame⁻¹ := by
    rw [hVinv]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [vFrame, wFrame, pauli2, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Fin.sum_univ_two, Matrix.diagonal_apply] <;> ring
  have hzval : NormedSpace.exp z = rotEntry - rotEntry * Complex.I := by
    rw [rotEntry_def, ← congrFun Complex.exp_eq_exp_ℂ z, hz, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
      Real.cos_pi_div_four, Real.sin_pi_div_four]
    push_cast
    ring
  have hznval : NormedSpace.exp (-z) = rotEntry + rotEntry * Complex.I := by
    have hneg : -z = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I := by
      rw [hz]
      push_cast
      ring
    rw [rotEntry_def, hneg, ← congrFun Complex.exp_eq_exp_ℂ _, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
      Real.sin_pi_div_four]
  rw [hconj, Matrix.exp_conj _ _ hV, Matrix.exp_diagonal, hVinv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [vFrame, wFrame, rotU, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, Matrix.diagonal_apply, hzval, hznval] <;>
    first
      | ring1
      | linear_combination rotEntry * Complex.I_sq
      | linear_combination (-rotEntry) * Complex.I_sq

set_option linter.flexible false in -- branch-dependent entry normal forms, closed by ring below
/-- The rotation is unitary. -/
theorem rotU_unitary : rotUᴴ * rotU = 1 ∧ rotU * rotUᴴ = 1 := by
  have hc := rotEntry_sq
  constructor <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotU, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply, rotEntry_star] <;>
      first
        | ring1
        | linear_combination 2 * hc

set_option linter.flexible false in -- branch-dependent entry normal forms, closed by ring below
/-- The first holonomy rotates `σ₃` to `σ₁`. -/
theorem rotU_conj_pauli3 : rotU * pauli3 * rotUᴴ = pauli1 := by
  have hc := rotEntry_sq
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotU, pauli3, pauli1, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, rotEntry_star] <;>
    first
      | ring1
      | linear_combination 2 * hc

/-- The two-link holonomy bank: `U₁ = e^{-iπσ₂/4}`, `U₂ = 1`. -/
noncomputable def linkU : ℕ → Matrix (Fin 2) (Fin 2) ℂ :=
  fun j => if j = 0 then rotU else 1

/-- The retained charge bank: `Q = σ₃` at both source vertices. -/
def linkQ : ℕ → Matrix (Fin 2) (Fin 2) ℂ := fun _ => pauli3

/-- The phase bank `u = (1, 0)`. -/
def uBank : ℕ → ℂ := fun j => if j = 0 then 1 else 0

/-- The phase bank `v = (0, 1)`. -/
def vBank : ℕ → ℂ := fun j => if j = 1 then 1 else 0

/-- The scalar phase sums of the two banks agree. -/
theorem phase_sums_agree :
    ∑ j ∈ Finset.range 2, uBank j = 1
      ∧ ∑ j ∈ Finset.range 2, vBank j = 1 := by
  constructor <;> simp [uBank, vBank]

/-- The routed charges of the two links: `Q̃₁ = σ₃` and `Q̃₂ = σ₁`. -/
theorem routed_charges :
    routedCharge linkU linkQ 0 = pauli3 ∧ routedCharge linkU linkQ 1 = pauli1 := by
  constructor
  · simp [routedCharge, pathProd, linkQ]
  · have hpath : pathProd linkU 1 = rotU := by
      simp [pathProd, linkU]
    rw [routedCharge, hpath]
    exact rotU_conj_pauli3

/-- **(EMR.14), router values**: `𝒥_γ(u) = σ₃` and `𝒥_γ(v) = σ₁`. -/
theorem router_values :
    router linkU linkQ 2 uBank = pauli3 ∧ router linkU linkQ 2 vBank = pauli1 := by
  obtain ⟨h0, h1⟩ := routed_charges
  constructor <;>
  · rw [router, Finset.sum_range_succ, Finset.sum_range_succ, Finset.range_zero,
      Finset.sum_empty, h0, h1]
    simp [uBank, vBank]

open scoped Matrix.Norms.L2Operator in
/-- **(EMR.14), norm gap**: `‖𝒥_γ(u) - 𝒥_γ(v)‖ = √2` in the `L²` operator
norm. -/
theorem router_norm_gap :
    ‖router linkU linkQ 2 uBank - router linkU linkQ 2 vBank‖ = Real.sqrt 2 := by
  obtain ⟨hu, hv⟩ := router_values
  rw [hu, hv]
  have hXX : (pauli3 - pauli1)ᴴ * (pauli3 - pauli1)
      = (2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauli3, pauli1, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply] <;> ring
  have hone : ‖(1 : Matrix (Fin 2) (Fin 2) ℂ)‖ = 1 := by
    have hcs := Matrix.l2_opNorm_conjTranspose_mul_self (1 : Matrix (Fin 2) (Fin 2) ℂ)
    rw [Matrix.conjTranspose_one, Matrix.mul_one] at hcs
    have hne : (1 : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0 := by
      intro h
      have h0 := congrFun (congrFun h 0) 0
      simp at h0
    have hn : ‖(1 : Matrix (Fin 2) (Fin 2) ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr hne
    have h' : ‖(1 : Matrix (Fin 2) (Fin 2) ℂ)‖ * 1
        = ‖(1 : Matrix (Fin 2) (Fin 2) ℂ)‖ * ‖(1 : Matrix (Fin 2) (Fin 2) ℂ)‖ := by
      rw [mul_one]
      exact hcs
    exact (mul_left_cancel₀ hn h').symm
  have h2 : ‖pauli3 - pauli1‖ * ‖pauli3 - pauli1‖ = 2 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hXX, norm_smul, hone]
    simp
  calc ‖pauli3 - pauli1‖
      = Real.sqrt (‖pauli3 - pauli1‖ * ‖pauli3 - pauli1‖) :=
        (Real.sqrt_mul_self (norm_nonneg _)).symm
    _ = Real.sqrt 2 := by rw [h2]

/-- **(EMR.14), zero mixed contact**: the exact mixed Hermitian contact
`½{𝒥_γ(u), 𝒥_γ(v)}` vanishes, while a naively aggregated scalar source
assigns `Q² = 1`. -/
theorem mixed_contact_zero :
    (1 / 2 : ℂ) • (router linkU linkQ 2 uBank * router linkU linkQ 2 vBank
        + router linkU linkQ 2 vBank * router linkU linkQ 2 uBank) = 0
      ∧ pauli3 * pauli3 = 1 := by
  obtain ⟨hu, hv⟩ := router_values
  rw [hu, hv]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauli3, pauli1]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauli3, Matrix.mul_apply, Fin.sum_univ_two]

end PhaseSum

/-! ### `cth:SMST-mixed-C-irredundant` — The auxiliary mixed row is irredundant

Rendering: on `ℂ³` with `M = diag(μ₁,μ₂,μ₃)` (real multiplier values),
`A(1) = 2^{-1/2}(e₁+e₂)`, `F₀(1) = 2^{-1/2}(e₁-e₂)`, `F₁(1) = e₃` and
`Y = MA`, the two cards `(A,F₀)` and `(A,F₁)` are compared through the
DMC.15 reconstruction with the spectral Moore–Penrose pseudo-inverse:
`G = E - D^*S^†D`, `C = T^F - D^*S^†T` and
`ℝ = U - T^*S^†T - C^*G^†C`.  Both cards have identical
`(S, D, E, T, U, G)`, while (DMC.16) gives `C₀ = (μ₁-μ₂)/2`, `ℝ₀ = 0`,
`C₁ = 0`, `ℝ₁ = (μ₁-μ₂)²/4`; for `μ₁ ≠ μ₂` the mixed rows and residuals
of the two cards genuinely differ.  The literal-Duhamel-fibre clause is the
strict-monotonicity statement that any strictly monotone calibrated
multiplier takes distinct values `μ₁ ≠ μ₂` at distinct right energies.
`2^{-1/2}` is rendered as `√2/2`. -/

namespace MixedCIrr

open PhaseSum in
/-- The saturated primitive entrance `A(1) = 2^{-1/2}(e₁+e₂)`. -/
noncomputable def entA : Matrix (Fin 3) (Fin 1) ℂ := !![rotEntry; rotEntry; 0]

open PhaseSum in
/-- The auxiliary prior column `F₀(1) = 2^{-1/2}(e₁-e₂)`. -/
noncomputable def entF0 : Matrix (Fin 3) (Fin 1) ℂ := !![rotEntry; -rotEntry; 0]

/-- The auxiliary prior column `F₁(1) = e₃`. -/
def entF1 : Matrix (Fin 3) (Fin 1) ℂ := !![0; 0; 1]

/-- The diagonal calibrated multiplier `M = diag(μ₁, μ₂, μ₃)`. -/
def diagM (μ₁ μ₂ μ₃ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal ![(μ₁ : ℂ), (μ₂ : ℂ), (μ₃ : ℂ)]

/-- The target synthesis `Y = MA`. -/
noncomputable def targY (μ₁ μ₂ μ₃ : ℝ) : Matrix (Fin 3) (Fin 1) ℂ :=
  diagM μ₁ μ₂ μ₃ * entA

open PhaseSum in
/-- The target column in closed form. -/
theorem targY_eq (μ₁ μ₂ μ₃ : ℝ) :
    targY μ₁ μ₂ μ₃ = !![(μ₁ : ℂ) * rotEntry; (μ₂ : ℂ) * rotEntry; 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [targY, diagM, entA, Matrix.mul_apply, Matrix.diagonal_apply]

open PhaseSum in
/-- The saturated `S`-block: `S = A^*A = 1`. -/
theorem gram_S : entAᴴ * entA = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [entA, Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply,
    rotEntry_star]
  linear_combination 2 * rotEntry_sq

/-- The pseudo-inverse of the saturated `S`-block is `1`. -/
theorem pinvS_eq :
    pinv (posSemidef_conjTranspose_mul_self entA).1 = 1 := by
  rw [pinv_congr gram_S (posSemidef_conjTranspose_mul_self entA).1
    Matrix.isHermitian_one, pinv_one]

open PhaseSum in
/-- The mixed prior block of card `0` vanishes: `D₀ = A^*F₀ = 0`. -/
theorem gram_D0 : entAᴴ * entF0 = 0 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [entA, entF0, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.conjTranspose_apply, rotEntry_star]

/-- The mixed prior block of card `1` vanishes: `D₁ = A^*F₁ = 0`. -/
theorem gram_D1 : entAᴴ * entF1 = 0 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [entA, entF1, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.conjTranspose_apply]

open PhaseSum in
/-- The prior Gram of card `0`: `E₀ = F₀^*F₀ = 1`. -/
theorem gram_E0 : entF0ᴴ * entF0 = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [entF0, Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply,
    rotEntry_star]
  linear_combination 2 * rotEntry_sq

/-- The prior Gram of card `1`: `E₁ = F₁^*F₁ = 1`. -/
theorem gram_E1 : entF1ᴴ * entF1 = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [entF1, Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply]

open PhaseSum in
/-- The shared entrance row `T = A^*Y = (μ₁+μ₂)/2`. -/
theorem gram_T (μ₁ μ₂ μ₃ : ℝ) :
    entAᴴ * targY μ₁ μ₂ μ₃ = (((μ₁ + μ₂) / 2 : ℝ) : ℂ) • 1 := by
  rw [targY_eq]
  ext i j
  fin_cases i
  fin_cases j
  simp [entA, Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply,
    rotEntry_star]
  linear_combination ((μ₁ : ℂ) + (μ₂ : ℂ)) * rotEntry_sq

open PhaseSum in
/-- The shared target Gram `U = Y^*Y = (μ₁²+μ₂²)/2`. -/
theorem gram_U (μ₁ μ₂ μ₃ : ℝ) :
    (targY μ₁ μ₂ μ₃)ᴴ * targY μ₁ μ₂ μ₃ = (((μ₁ ^ 2 + μ₂ ^ 2) / 2 : ℝ) : ℂ) • 1 := by
  rw [targY_eq]
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply,
    rotEntry_star, map_mul, Complex.conj_ofReal]
  linear_combination ((μ₁ : ℂ) ^ 2 + (μ₂ : ℂ) ^ 2) * rotEntry_sq

open PhaseSum in
/-- The mixed prior–target row of card `0`: `T^F₀ = F₀^*Y = (μ₁-μ₂)/2`. -/
theorem gram_TF0 (μ₁ μ₂ μ₃ : ℝ) :
    entF0ᴴ * targY μ₁ μ₂ μ₃ = (((μ₁ - μ₂) / 2 : ℝ) : ℂ) • 1 := by
  rw [targY_eq]
  ext i j
  fin_cases i
  fin_cases j
  simp [entF0, Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply,
    rotEntry_star]
  linear_combination ((μ₁ : ℂ) - (μ₂ : ℂ)) * rotEntry_sq

/-- The mixed prior–target row of card `1` vanishes: `T^F₁ = F₁^*Y = 0`. -/
theorem gram_TF1 (μ₁ μ₂ μ₃ : ℝ) : entF1ᴴ * targY μ₁ μ₂ μ₃ = 0 := by
  rw [targY_eq]
  ext i j
  fin_cases i
  fin_cases j
  simp [entF1, Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply]

/-- The reconstructed residualized prior Gram `G = E - D^*S^†D` of a card. -/
noncomputable def gramG (F : Matrix (Fin 3) (Fin 1) ℂ) : Matrix (Fin 1) (Fin 1) ℂ :=
  Fᴴ * F - (entAᴴ * F)ᴴ * pinv (posSemidef_conjTranspose_mul_self entA).1
    * (entAᴴ * F)

/-- The reconstructed mixed row `C = T^F - D^*S^†T` of a card (DMC.15). -/
noncomputable def rowC (μ₁ μ₂ μ₃ : ℝ) (F : Matrix (Fin 3) (Fin 1) ℂ) :
    Matrix (Fin 1) (Fin 1) ℂ :=
  Fᴴ * targY μ₁ μ₂ μ₃
    - (entAᴴ * F)ᴴ * pinv (posSemidef_conjTranspose_mul_self entA).1
      * (entAᴴ * targY μ₁ μ₂ μ₃)

/-- The complete residual `ℝ = U - T^*S^†T - C^*G^†C` of a card (DMC.13,
DMC.15). -/
noncomputable def resR (μ₁ μ₂ μ₃ : ℝ) (F : Matrix (Fin 3) (Fin 1) ℂ)
    (hG : (gramG F).IsHermitian) : Matrix (Fin 1) (Fin 1) ℂ :=
  (targY μ₁ μ₂ μ₃)ᴴ * targY μ₁ μ₂ μ₃
    - (entAᴴ * targY μ₁ μ₂ μ₃)ᴴ * pinv (posSemidef_conjTranspose_mul_self entA).1
      * (entAᴴ * targY μ₁ μ₂ μ₃)
    - (rowC μ₁ μ₂ μ₃ F)ᴴ * pinv hG * rowC μ₁ μ₂ μ₃ F

/-- The residualized prior Gram is Hermitian (it is a Schur residual). -/
theorem gramG_isHermitian (F : Matrix (Fin 3) (Fin 1) ℂ) :
    (gramG F).IsHermitian := by
  rw [gramG, schur_residual_eq]
  exact (one_sub_colProj_gram_posSemidef entA F).1

/-- The residualized prior Grams of both cards are `1`. -/
theorem gramG_values : gramG entF0 = 1 ∧ gramG entF1 = 1 := by
  constructor
  · rw [gramG, gram_D0]
    simp [gram_E0]
  · rw [gramG, gram_D1]
    simp [gram_E1]

/-- **(DMC.16), mixed rows**: `C₀ = (μ₁-μ₂)/2` and `C₁ = 0`. -/
theorem rowC_values (μ₁ μ₂ μ₃ : ℝ) :
    rowC μ₁ μ₂ μ₃ entF0 = (((μ₁ - μ₂) / 2 : ℝ) : ℂ) • 1
      ∧ rowC μ₁ μ₂ μ₃ entF1 = 0 := by
  constructor
  · rw [rowC, gram_D0, gram_TF0]
    simp
  · rw [rowC, gram_D1, gram_TF1]
    simp

/-- The pseudo-inverses of the two prior Grams are `1`. -/
theorem pinvG_values :
    pinv (gramG_isHermitian entF0) = 1 ∧ pinv (gramG_isHermitian entF1) = 1 := by
  constructor
  · rw [pinv_congr gramG_values.1 (gramG_isHermitian entF0) Matrix.isHermitian_one,
      pinv_one]
  · rw [pinv_congr gramG_values.2 (gramG_isHermitian entF1) Matrix.isHermitian_one,
      pinv_one]

/-- **(DMC.16), residuals**: `ℝ₀ = 0` and `ℝ₁ = (μ₁-μ₂)²/4`. -/
theorem resR_values (μ₁ μ₂ μ₃ : ℝ) :
    resR μ₁ μ₂ μ₃ entF0 (gramG_isHermitian entF0) = 0
      ∧ resR μ₁ μ₂ μ₃ entF1 (gramG_isHermitian entF1)
        = (((μ₁ - μ₂) ^ 2 / 4 : ℝ) : ℂ) • 1 := by
  constructor
  · rw [resR, gram_U, gram_T, (rowC_values μ₁ μ₂ μ₃).1, pinvS_eq, pinvG_values.1]
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.mul_one,
      smul_mul_assoc, mul_smul_comm, smul_smul, Complex.star_def,
      Complex.conj_ofReal]
    match_scalars
    ring
  · rw [resR, gram_U, gram_T, (rowC_values μ₁ μ₂ μ₃).2, pinvS_eq, pinvG_values.2]
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Matrix.conjTranspose_zero, Matrix.mul_one,
      Matrix.mul_zero, sub_zero, smul_mul_assoc, mul_smul_comm, smul_smul,
      Complex.star_def, Complex.conj_ofReal]
    match_scalars
    ring

/-- **`cth:SMST-mixed-C-irredundant`**: the two cards have identical
`(S, D, E, T, U, G)`, but for `μ₁ ≠ μ₂` the mixed rows and complete
residuals differ — the mixed primitive–target row cannot be inferred from
the four marginal matrices. -/
theorem mixed_row_irredundant {μ₁ μ₂ : ℝ} (μ₃ : ℝ) (h : μ₁ ≠ μ₂) :
    rowC μ₁ μ₂ μ₃ entF0 ≠ rowC μ₁ μ₂ μ₃ entF1
      ∧ resR μ₁ μ₂ μ₃ entF0 (gramG_isHermitian entF0)
        ≠ resR μ₁ μ₂ μ₃ entF1 (gramG_isHermitian entF1) := by
  have hd : ((μ₁ - μ₂ : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact sub_ne_zero_of_ne h
  constructor
  · rw [(rowC_values μ₁ μ₂ μ₃).1, (rowC_values μ₁ μ₂ μ₃).2]
    intro hcontra
    have h00 := congrFun (congrFun hcontra 0) 0
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
      Matrix.zero_apply] at h00
    apply hd
    have : ((μ₁ - μ₂) / 2 : ℝ) = 0 := by exact_mod_cast h00
    have h2 : (μ₁ - μ₂ : ℝ) = 0 := by linarith
    exact_mod_cast congrArg Complex.ofReal h2
  · rw [(resR_values μ₁ μ₂ μ₃).1, (resR_values μ₁ μ₂ μ₃).2]
    intro hcontra
    have h00 := congrFun (congrFun hcontra.symm 0) 0
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
      Matrix.zero_apply] at h00
    have hr : ((μ₁ - μ₂) ^ 2 / 4 : ℝ) = 0 := by exact_mod_cast h00
    have h2 : (μ₁ - μ₂ : ℝ) = 0 := by
      have := sq_eq_zero_iff.mp (by linarith : (μ₁ - μ₂ : ℝ) ^ 2 = 0)
      exact this
    apply hd
    exact_mod_cast congrArg Complex.ofReal h2

/-- The literal-Duhamel-fibre clause: a strictly monotone calibrated
multiplier takes distinct values at distinct right energies, so the witness
is realized with `μᵢ = m_{β,τ}(λ, rᵢ)` on any card with `r₁ ≠ r₂`. -/
theorem calibrated_fibre_instantiation (f : ℝ → ℝ)
    (hf : StrictMono f ∨ StrictAnti f) {r₁ r₂ : ℝ} (h : r₁ ≠ r₂) :
    f r₁ ≠ f r₂ := by
  rcases hf with hf | hf
  · exact fun hc => h (hf.injective hc)
  · exact fun hc => h (hf.injective hc)

end MixedCIrr

/-! ### `cth:SMST-resistance-clock-not-OS-clock` — Static twist vs OS clock

Rendering: the retained boundary state is a weight `π : ℤ → ℝ≥0∞` on the
command-generator spectrum (`N e_n = n e_n`), and a clock with spectrum
`c : ℤ → ℝ` carries the spectral-memory measure
`Σ = Σ_n n² π(n) δ_{c(n)}` of (PT.19), a literal `MeasureTheory.Measure`.
For the rescaled clocks `C_a = aC` with `C e_n = (n²/2) e_n` we prove the
boxed laws (PT.21): `Σ_a = (λ ↦ aλ)_* Σ₁`; the zero-mass Stieltjes response
`𝓕(0) = ∫ λ⁻¹ dΣ` scales by `a⁻¹`; and the time memory
`𝓜(t) = ∫ e^{-tλ} dΣ` satisfies `𝓜_a(t) = 𝓜₁(at)`.  The static data
(the boundary law `π` itself, hence every static characteristic) is shared
by construction, and the twist stiffness — the total memory mass
`Σ_a(ℝ) = Σ n²π(n)` of (PT.18) — is proved `a`-independent.  The final
clause is the two-card witness: boundary state `π(±1) = 1/2` with clocks of
spectra `{1,1}` and `{1/2,3/2}` has equal total memory mass and first
exterior-energy moment but zero-mass responses `1 ≠ 4/3`. -/

namespace ResistanceClock

open MeasureTheory

/-- The spectral-memory measure `Σ = Σ_n n² π(n) δ_{c(n)}` of a boundary
state `π` and clock spectrum `c` (PT.19). -/
noncomputable def memoryMeasure (π : ℤ → ℝ≥0∞) (c : ℤ → ℝ) : Measure ℝ :=
  Measure.sum fun n : ℤ =>
    (ENNReal.ofReal ((n : ℝ) ^ 2) * π n) • Measure.dirac (c n)

/-- The clock spectrum `n ↦ a n²/2` of the rescaled clock `C_a = aC`. -/
noncomputable def clockSpec (a : ℝ) : ℤ → ℝ := fun n => a * ((n : ℝ) ^ 2 / 2)

/-- The spectral-memory measure `Σ_a` of the clock `C_a`. -/
noncomputable def sigmaClock (π : ℤ → ℝ≥0∞) (a : ℝ) : Measure ℝ :=
  memoryMeasure π (clockSpec a)

/-- The zero-mass Stieltjes response `𝓕(0) = ∫ λ⁻¹ dΣ`. -/
noncomputable def zeroResponse (μm : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ x, (ENNReal.ofReal x)⁻¹ ∂μm

/-- The complete time memory `𝓜(t) = ∫ e^{-tλ} dΣ`. -/
noncomputable def timeMemory (μm : Measure ℝ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (Real.exp (-(t * x))) ∂μm

/-- The first exterior-energy moment `∫ λ dΣ`. -/
noncomputable def firstMoment (μm : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal x ∂μm

/-- **(PT.21), spectral measure**: `Σ_a = (λ ↦ aλ)_* Σ₁`. -/
theorem sigma_pushforward (π : ℤ → ℝ≥0∞) (a : ℝ) :
    sigmaClock π a = Measure.map (fun x => a * x) (sigmaClock π 1) := by
  rw [sigmaClock, sigmaClock, memoryMeasure, memoryMeasure,
    Measure.map_sum (measurable_const_mul a).aemeasurable]
  congr 1
  funext n
  rw [Measure.map_smul, Measure.map_dirac]
  have hc : clockSpec a n = a * clockSpec 1 n := by
    simp [clockSpec]
  rw [hc]

/-- The lintegral of a function against the memory measure. -/
theorem lintegral_memoryMeasure (π : ℤ → ℝ≥0∞) (c : ℤ → ℝ) (g : ℝ → ℝ≥0∞) :
    ∫⁻ x, g x ∂(memoryMeasure π c)
      = ∑' n : ℤ, (ENNReal.ofReal ((n : ℝ) ^ 2) * π n) * g (c n) := by
  rw [memoryMeasure, lintegral_sum_measure]
  congr 1
  funext n
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

/-- **(PT.21), zero-mass response**: `𝓕_a(0) = a⁻¹ 𝓕₁(0)` for `a > 0`. -/
theorem zero_response_scaling (π : ℤ → ℝ≥0∞) {a : ℝ} (ha : 0 < a) :
    zeroResponse (sigmaClock π a)
      = (ENNReal.ofReal a)⁻¹ * zeroResponse (sigmaClock π 1) := by
  rw [zeroResponse, zeroResponse, sigmaClock, sigmaClock, lintegral_memoryMeasure,
    lintegral_memoryMeasure, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [clockSpec]
  · have hx : (0 : ℝ) < (n : ℝ) ^ 2 / 2 := by
      have : ((n : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr hn
      positivity
    have hsplit : ENNReal.ofReal (clockSpec a n)
        = ENNReal.ofReal a * ENNReal.ofReal ((n : ℝ) ^ 2 / 2) := by
      rw [clockSpec, ENNReal.ofReal_mul ha.le]
    have hone : ENNReal.ofReal (clockSpec 1 n) = ENNReal.ofReal ((n : ℝ) ^ 2 / 2) := by
      rw [clockSpec, one_mul]
    rw [hsplit, hone, ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top)
      (Or.inl ENNReal.ofReal_ne_top)]
    ring

/-- **(PT.21), time memory**: `𝓜_a(t) = 𝓜₁(at)`. -/
theorem time_memory_scaling (π : ℤ → ℝ≥0∞) (a t : ℝ) :
    timeMemory (sigmaClock π a) t = timeMemory (sigmaClock π 1) (a * t) := by
  rw [timeMemory, timeMemory, sigmaClock, sigmaClock, lintegral_memoryMeasure,
    lintegral_memoryMeasure]
  refine tsum_congr fun n => ?_
  have h : t * clockSpec a n = a * t * clockSpec 1 n := by
    simp [clockSpec]
    ring
  rw [h]

/-- The total memory mass (the static twist stiffness of PT.18)
is `Σ_n n² π(n)`. -/
theorem memory_mass (π : ℤ → ℝ≥0∞) (c : ℤ → ℝ) :
    memoryMeasure π c Set.univ = ∑' n : ℤ, ENNReal.ofReal ((n : ℝ) ^ 2) * π n := by
  rw [memoryMeasure, Measure.sum_apply _ MeasurableSet.univ]
  refine tsum_congr fun n => ?_
  rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]

/-- The static twist stiffness is identical for every clock rescaling:
`Σ_a(ℝ) = Σ₁(ℝ)` for all `a`. -/
theorem stiffness_static (π : ℤ → ℝ≥0∞) (a : ℝ) :
    sigmaClock π a Set.univ = sigmaClock π 1 Set.univ := by
  rw [sigmaClock, sigmaClock, memory_mass, memory_mass]

/-- The witness boundary state `π(±1) = 1/2`. -/
noncomputable def witState : ℤ → ℝ≥0∞ := fun n =>
  if n = 1 ∨ n = -1 then ENNReal.ofReal (1 / 2) else 0

/-- The first witness clock spectrum: `c ≡ 1` on the retained modes. -/
def clockA : ℤ → ℝ := fun _ => 1

/-- The second witness clock spectrum: `1/2` at `n = 1`, `3/2` elsewhere. -/
noncomputable def clockB : ℤ → ℝ := fun n => if n = 1 then 1 / 2 else 3 / 2

/-- The memory tsum of a witness card collapses to the two retained modes. -/
theorem witness_tsum (c : ℤ → ℝ) (g : ℝ → ℝ≥0∞) :
    ∑' n : ℤ, (ENNReal.ofReal ((n : ℝ) ^ 2) * witState n) * g (c n)
      = ENNReal.ofReal (1 / 2) * g (c 1) + ENNReal.ofReal (1 / 2) * g (c (-1)) := by
  have hsum : ∑' n : ℤ, (ENNReal.ofReal ((n : ℝ) ^ 2) * witState n) * g (c n)
      = ∑ n ∈ ({1, -1} : Finset ℤ),
        (ENNReal.ofReal ((n : ℝ) ^ 2) * witState n) * g (c n) := by
    refine tsum_eq_sum fun n hn => ?_
    have h1 : n ≠ 1 := fun hc => hn (by simp [hc])
    have h2 : n ≠ -1 := fun hc => hn (by simp [hc])
    simp [witState, h1, h2]
  rw [hsum, Finset.sum_insert (by norm_num), Finset.sum_singleton]
  norm_num [witState]

/-- The zero-mass response of a witness card in closed form. -/
theorem witness_zeroResponse (c : ℤ → ℝ) :
    zeroResponse (memoryMeasure witState c)
      = ENNReal.ofReal (1 / 2) * (ENNReal.ofReal (c 1))⁻¹
        + ENNReal.ofReal (1 / 2) * (ENNReal.ofReal (c (-1)))⁻¹ := by
  rw [zeroResponse, lintegral_memoryMeasure]
  exact witness_tsum c fun x => (ENNReal.ofReal x)⁻¹

/-- The first exterior-energy moment of a witness card in closed form. -/
theorem witness_firstMoment (c : ℤ → ℝ) :
    firstMoment (memoryMeasure witState c)
      = ENNReal.ofReal (1 / 2) * ENNReal.ofReal (c 1)
        + ENNReal.ofReal (1 / 2) * ENNReal.ofReal (c (-1)) := by
  rw [firstMoment, lintegral_memoryMeasure]
  exact witness_tsum c fun x => ENNReal.ofReal x

/-- **Equal total memory mass and first exterior-energy moment do not
determine `𝓕(0)`**: the two witness cards have the same mass and moment,
but zero-mass responses `1 ≠ 4/3`. -/
theorem mass_moment_not_determine_response :
    memoryMeasure witState clockA Set.univ = memoryMeasure witState clockB Set.univ
      ∧ firstMoment (memoryMeasure witState clockA)
          = firstMoment (memoryMeasure witState clockB)
      ∧ zeroResponse (memoryMeasure witState clockA)
          ≠ zeroResponse (memoryMeasure witState clockB) := by
  have hcA1 : clockA 1 = 1 := rfl
  have hcA2 : clockA (-1) = 1 := rfl
  have hcB1 : clockB 1 = 1 / 2 := by norm_num [clockB]
  have hcB2 : clockB (-1) = 3 / 2 := by norm_num [clockB]
  refine ⟨?_, ?_, ?_⟩
  · rw [memory_mass, memory_mass]
  · rw [witness_firstMoment, witness_firstMoment, hcA1, hcA2, hcB1, hcB2,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    congr 1
    norm_num
  · have hA : zeroResponse (memoryMeasure witState clockA) = ENNReal.ofReal 1 := by
      rw [witness_zeroResponse, hcA1, hcA2, ENNReal.ofReal_one, inv_one, mul_one,
        ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      norm_num
    have hB : zeroResponse (memoryMeasure witState clockB)
        = ENNReal.ofReal (4 / 3) := by
      rw [witness_zeroResponse, hcB1, hcB2, ← ENNReal.ofReal_inv_of_pos (by norm_num),
        ← ENNReal.ofReal_inv_of_pos (by norm_num),
        ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      norm_num
    rw [hA, hB, Ne, ENNReal.ofReal_eq_ofReal_iff (by norm_num) (by norm_num)]
    norm_num

end ResistanceClock

/-! ### `cth:SMST-positive-time-high-energy-escape` — Delayed collapse

Rendering: a bank is a sequence of finite-dimensional Hermitian Hamiltonians
`H_n` with finite source banks `Ψ_n`, and delayed Grams
`G_{t,n} = Ψ_n^* e^{-2tH_n} Ψ_n` (PT.1).  We prove the general clause at
this finite generality: whenever `G_{0,n} ⪰ I` and
`λ_min(G_{t₀,n}) → 0` at a fixed delay `t₀ > 0`, there are unit coefficient
vectors whose normalized spectral measures (the eigenbasis weight
distributions of `ψ_n = Ψ_n c_n` under `H_n`) escape every bounded energy
interval: the normalized mass of `{|λ| ≤ R}` tends to `0` for every `R`.
The witness bank is one-dimensional, `H_n = n` and `Ψ_n = 1`, with
`G_{0,n} = I` and minimal delayed eigenvalue `e^{-2t₀n} → 0`. -/

namespace HighEnergyEscape

open Filter NCG.TraceExp

/-- The rectangular adjoint move for dot products. -/
theorem dot_adjoint_rect {k ι : Type} [Fintype k] [Fintype ι]
    (E : Matrix k ι ℂ) (x : k → ℂ) (y : ι → ℂ) :
    star x ⬝ᵥ (E *ᵥ y) = star (Eᴴ *ᵥ x) ⬝ᵥ y := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_sum, star_mul',
    Matrix.conjTranspose_apply, star_star, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

section SpectralWeights

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The eigenbasis spectral weight of a vector `v` at the `i`-th eigenvalue
of a Hermitian matrix: `w_i = |⟨u_i, v⟩|²`. -/
noncomputable def specWeight {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (v : ι → ℂ) (i : ι) : ℝ :=
  ‖((hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *ᵥ v) i‖ ^ 2

/-- Spectral weights are nonnegative. -/
theorem specWeight_nonneg {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (v : ι → ℂ) (i : ι) : 0 ≤ specWeight hA v i := by
  unfold specWeight
  positivity

/-- Quadratic forms of Hermitian exponentials in spectral-weight form:
`⟨v, e^{cA} v⟩ = Σ_i e^{cλᵢ} w_i`. -/
theorem dot_exp_eig {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (v : ι → ℂ)
    (co : ℝ) :
    star v ⬝ᵥ (NormedSpace.exp (co • A) *ᵥ v)
      = ((∑ i, Real.exp (co * hA.eigenvalues i) * specWeight hA v i : ℝ) : ℂ) := by
  rw [exp_smul_hermitian A hA co, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    dot_adjoint_rect]
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.ofReal_exp, specWeight]
  have hswap : star (((hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *ᵥ v) i)
      * (((Real.exp (co * hA.eigenvalues i) : ℝ) : ℂ)
        * ((hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *ᵥ v) i)
      = ((Real.exp (co * hA.eigenvalues i) : ℝ) : ℂ)
        * (star (((hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *ᵥ v) i)
          * ((hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *ᵥ v) i) := by ring
  rw [hswap, Complex.star_def, Complex.conj_mul']
  push_cast
  ring

/-- The total spectral weight is the squared length of the vector. -/
theorem dot_self_eq_weights {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (v : ι → ℂ) :
    star v ⬝ᵥ v = ((∑ i, specWeight hA v i : ℝ) : ℂ) := by
  have h := dot_exp_eig hA v 0
  rw [zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec] at h
  simpa using h

/-- The minimal eigenvalue of a Hermitian matrix on a nonempty carrier. -/
noncomputable def minEig {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hne : (Finset.univ : Finset ι).Nonempty) : ℝ :=
  Finset.univ.inf' hne hA.eigenvalues

/-- A unit eigenvector realizing the minimal eigenvalue. -/
theorem exists_min_eigvector {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hne : (Finset.univ : Finset ι).Nonempty) :
    ∃ v : ι → ℂ, star v ⬝ᵥ v = 1
      ∧ star v ⬝ᵥ (A *ᵥ v) = ((minEig hA hne : ℝ) : ℂ) := by
  obtain ⟨i₀, -, hmin⟩ := Finset.exists_mem_eq_inf' hne hA.eigenvalues
  refine ⟨⇑(hA.eigenvectorBasis i₀), ?_, ?_⟩
  · have hnorm : ‖hA.eigenvectorBasis i₀‖ = 1 :=
      (hA.eigenvectorBasis).orthonormal.1 i₀
    rw [EuclideanSpace.norm_eq] at hnorm
    have hsq : ∑ i, ‖hA.eigenvectorBasis i₀ i‖ ^ 2 = 1 := by
      have := Real.sqrt_eq_one.mp hnorm
      simpa using this
    rw [star_dot_self_eq_sum_sq, hsq, Complex.ofReal_one]
  · rw [hA.mulVec_eigenvectorBasis i₀]
    have hunit : star ⇑(hA.eigenvectorBasis i₀) ⬝ᵥ ⇑(hA.eigenvectorBasis i₀)
        = 1 := by
      have hnorm : ‖hA.eigenvectorBasis i₀‖ = 1 :=
        (hA.eigenvectorBasis).orthonormal.1 i₀
      rw [EuclideanSpace.norm_eq] at hnorm
      have hsq : ∑ i, ‖hA.eigenvectorBasis i₀ i‖ ^ 2 = 1 := by
        have := Real.sqrt_eq_one.mp hnorm
        simpa using this
      rw [star_dot_self_eq_sum_sq, hsq, Complex.ofReal_one]
    rw [dotProduct_smul, hunit, Complex.real_smul, mul_one, minEig, hmin]

end SpectralWeights

section EscapeGeneral

/-- The delayed source Gram `G_t = Ψ^* e^{-2tH} Ψ` of (PT.1). -/
noncomputable def delayedGram {k ι : Type} [Fintype k] [Fintype ι]
    [DecidableEq k] (H : Matrix k k ℂ) (Ψ : Matrix k ι ℂ) (t : ℝ) :
    Matrix ι ι ℂ :=
  Ψᴴ * NormedSpace.exp ((-(2 * t)) • H) * Ψ

/-- The delayed Gram of a Hermitian Hamiltonian is Hermitian. -/
theorem delayedGram_isHermitian {k ι : Type} [Fintype k] [Fintype ι]
    [DecidableEq k] {H : Matrix k k ℂ} (hH : H.IsHermitian)
    (Ψ : Matrix k ι ℂ) (t : ℝ) : (delayedGram H Ψ t).IsHermitian := by
  have hexp : (NormedSpace.exp ((-(2 * t)) • H)).IsHermitian :=
    (hH.smul (star_trivial (-(2 * t)))).exp
  unfold delayedGram Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hexp.eq, Matrix.mul_assoc]

/-- The base Gram is the undelayed source Gram: `G_0 = Ψ^*Ψ`. -/
theorem delayedGram_zero {k ι : Type} [Fintype k] [Fintype ι] [DecidableEq k]
    (H : Matrix k k ℂ) (Ψ : Matrix k ι ℂ) :
    delayedGram H Ψ 0 = Ψᴴ * Ψ := by
  unfold delayedGram
  rw [show (-(2 * (0 : ℝ))) = (0 : ℝ) by norm_num, zero_smul,
    NormedSpace.exp_zero, Matrix.mul_one]

/-- **`cth:SMST-positive-time-high-energy-escape`, general clause**: whenever
a bank has `G_{0,n} ⪰ I` but `λ_min(G_{t₀,n}) → 0` at a fixed delay
`t₀ > 0`, there are unit coefficient vectors whose normalized spectral
measures escape every bounded energy interval. -/
theorem energy_escape {d e : ℕ → ℕ} (he : ∀ n, 0 < e n)
    (H : ∀ n, Matrix (Fin (d n)) (Fin (d n)) ℂ) (hH : ∀ n, (H n).IsHermitian)
    (Ψ : ∀ n, Matrix (Fin (d n)) (Fin (e n)) ℂ)
    (hbase : ∀ n, ((Ψ n)ᴴ * Ψ n - 1).PosSemidef)
    {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hcollapse : Tendsto
      (fun n => minEig (delayedGram_isHermitian (hH n) (Ψ n) t₀)
        (Finset.univ_nonempty_iff.mpr ⟨⟨0, he n⟩⟩))
      atTop (nhds 0)) :
    ∃ c : ∀ n, Fin (e n) → ℂ,
      (∀ n, star (c n) ⬝ᵥ c n = 1) ∧
      ∀ R : ℝ, Tendsto
        (fun n =>
          (∑ i ∈ Finset.univ.filter (fun i => |(hH n).eigenvalues i| ≤ R),
              specWeight (hH n) (Ψ n *ᵥ c n) i)
            / ∑ i, specWeight (hH n) (Ψ n *ᵥ c n) i)
        atTop (nhds 0) := by
  classical
  choose c hunit hray using fun n =>
    exists_min_eigvector (delayedGram_isHermitian (hH n) (Ψ n) t₀)
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, he n⟩⟩)
  refine ⟨c, hunit, fun R => ?_⟩
  set μ : ℕ → ℝ := fun n =>
    minEig (delayedGram_isHermitian (hH n) (Ψ n) t₀)
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, he n⟩⟩) with hμ
  -- total spectral weight is at least one
  have htot : ∀ n, 1 ≤ ∑ i, specWeight (hH n) (Ψ n *ᵥ c n) i := by
    intro n
    have hpsd := (hbase n).dotProduct_mulVec_nonneg (c n)
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, hunit n,
      ← Matrix.mulVec_mulVec, dot_adjoint_rect,
      Matrix.conjTranspose_conjTranspose,
      dot_self_eq_weights (hH n) (Ψ n *ᵥ c n)] at hpsd
    have hcast : ((∑ i, specWeight (hH n) (Ψ n *ᵥ c n) i : ℝ) : ℂ) - 1
        = (((∑ i, specWeight (hH n) (Ψ n *ᵥ c n) i - 1 : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [hcast] at hpsd
    have := Complex.zero_le_real.mp hpsd
    linarith
  -- the delayed Rayleigh quotient equals the minimal eigenvalue
  have hminid : ∀ n, ∑ i, Real.exp ((-(2 * t₀)) * (hH n).eigenvalues i)
      * specWeight (hH n) (Ψ n *ᵥ c n) i = μ n := by
    intro n
    have h := hray n
    simp only [delayedGram] at h
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dot_adjoint_rect,
      Matrix.conjTranspose_conjTranspose,
      dot_exp_eig (hH n) (Ψ n *ᵥ c n) (-(2 * t₀))] at h
    exact_mod_cast h
  -- squeeze the normalized interval mass
  have hub : ∀ n,
      (∑ i ∈ Finset.univ.filter (fun i => |(hH n).eigenvalues i| ≤ R),
          specWeight (hH n) (Ψ n *ᵥ c n) i)
        / (∑ i, specWeight (hH n) (Ψ n *ᵥ c n) i)
      ≤ Real.exp (2 * t₀ * R) * μ n := by
    intro n
    have h1 : (∑ i ∈ Finset.univ.filter (fun i => |(hH n).eigenvalues i| ≤ R),
        specWeight (hH n) (Ψ n *ᵥ c n) i)
        ≤ Real.exp (2 * t₀ * R) * μ n := by
      rw [← hminid n, Finset.mul_sum]
      calc ∑ i ∈ Finset.univ.filter (fun i => |(hH n).eigenvalues i| ≤ R),
            specWeight (hH n) (Ψ n *ᵥ c n) i
          ≤ ∑ i ∈ Finset.univ.filter (fun i => |(hH n).eigenvalues i| ≤ R),
            Real.exp (2 * t₀ * R)
              * (Real.exp ((-(2 * t₀)) * (hH n).eigenvalues i)
                * specWeight (hH n) (Ψ n *ᵥ c n) i) := by
            refine Finset.sum_le_sum fun i hi => ?_
            have hle : (hH n).eigenvalues i ≤ R :=
              (abs_le.mp (Finset.mem_filter.mp hi).2).2
            have hexp1 : 1 ≤ Real.exp (2 * t₀ * R)
                * Real.exp ((-(2 * t₀)) * (hH n).eigenvalues i) := by
              rw [← Real.exp_add]
              have harg : 0 ≤ 2 * t₀ * R + (-(2 * t₀)) * (hH n).eigenvalues i := by
                nlinarith
              exact Real.one_le_exp harg
            have hw := specWeight_nonneg (hH n) (Ψ n *ᵥ c n) i
            nlinarith
        _ ≤ ∑ i, Real.exp (2 * t₀ * R)
              * (Real.exp ((-(2 * t₀)) * (hH n).eigenvalues i)
                * specWeight (hH n) (Ψ n *ᵥ c n) i) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.filter_subset _ _) fun i _ _ => ?_
            have hw := specWeight_nonneg (hH n) (Ψ n *ᵥ c n) i
            positivity
    calc (∑ i ∈ Finset.univ.filter (fun i => |(hH n).eigenvalues i| ≤ R),
          specWeight (hH n) (Ψ n *ᵥ c n) i)
        / (∑ i, specWeight (hH n) (Ψ n *ᵥ c n) i)
        ≤ ∑ i ∈ Finset.univ.filter (fun i => |(hH n).eigenvalues i| ≤ R),
          specWeight (hH n) (Ψ n *ᵥ c n) i :=
          div_le_self (Finset.sum_nonneg fun i _ =>
            specWeight_nonneg (hH n) (Ψ n *ᵥ c n) i) (htot n)
      _ ≤ Real.exp (2 * t₀ * R) * μ n := h1
  have hlb : ∀ n, 0 ≤
      (∑ i ∈ Finset.univ.filter (fun i => |(hH n).eigenvalues i| ≤ R),
          specWeight (hH n) (Ψ n *ᵥ c n) i)
        / (∑ i, specWeight (hH n) (Ψ n *ᵥ c n) i) := by
    intro n
    have h1 : (0:ℝ) ≤ ∑ i ∈ Finset.univ.filter (fun i => |(hH n).eigenvalues i| ≤ R),
        specWeight (hH n) (Ψ n *ᵥ c n) i :=
      Finset.sum_nonneg fun i _ => specWeight_nonneg (hH n) (Ψ n *ᵥ c n) i
    have h2 : (0:ℝ) ≤ ∑ i, specWeight (hH n) (Ψ n *ᵥ c n) i :=
      Finset.sum_nonneg fun i _ => specWeight_nonneg (hH n) (Ψ n *ᵥ c n) i
    positivity
  have hlim : Tendsto (fun n => Real.exp (2 * t₀ * R) * μ n) atTop (nhds 0) := by
    have := hcollapse.const_mul (Real.exp (2 * t₀ * R))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim hlb hub

end EscapeGeneral

section Witness

/-- The one-dimensional witness bank Hamiltonian `H_n = (n)`. -/
def witH (n : ℕ) : Matrix (Fin 1) (Fin 1) ℂ :=
  Matrix.diagonal fun _ => (n : ℂ)

/-- The witness Hamiltonians are Hermitian. -/
theorem witH_isHermitian (n : ℕ) : (witH n).IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  fin_cases i
  fin_cases j
  simp [witH, Matrix.conjTranspose_apply]

/-- The witness base Grams satisfy `G_{0,n} ⪰ I` (with equality). -/
theorem wit_base :
    (((1 : Matrix (Fin 1) (Fin 1) ℂ))ᴴ * 1 - 1).PosSemidef := by
  rw [Matrix.conjTranspose_one, Matrix.mul_one, sub_self]
  exact Matrix.PosSemidef.zero

/-- The witness delayed Gram in closed form: `G_{t,n} = (e^{-2tn})`. -/
theorem wit_gram (t : ℝ) (n : ℕ) :
    delayedGram (witH n) (1 : Matrix (Fin 1) (Fin 1) ℂ) t
      = Matrix.diagonal fun _ => Complex.exp (((-(2 * t)) : ℂ) * n) := by
  unfold delayedGram
  rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hsm : (-(2 * t)) • witH n
      = Matrix.diagonal fun _ : Fin 1 => ((-(2 * t) : ℝ) : ℂ) * (n : ℂ) := by
    ext i j
    fin_cases i
    fin_cases j
    simp [witH, Complex.real_smul]
  rw [hsm, Matrix.exp_diagonal]
  congr 1
  funext i
  rw [Pi.coe_exp, ← congrFun Complex.exp_eq_exp_ℂ]
  norm_num

/-- The minimal delayed eigenvalue of the witness bank is `e^{-2tn}`. -/
theorem wit_minEig (t : ℝ) (n : ℕ) :
    minEig (delayedGram_isHermitian (witH_isHermitian n)
        (1 : Matrix (Fin 1) (Fin 1) ℂ) t)
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, one_pos⟩⟩)
      = Real.exp ((-(2 * t)) * n) := by
  set hG := delayedGram_isHermitian (witH_isHermitian n)
    (1 : Matrix (Fin 1) (Fin 1) ℂ) t with hGdef
  have htr := hG.trace_eq_sum_eigenvalues
  have htr2 : (delayedGram (witH n) (1 : Matrix (Fin 1) (Fin 1) ℂ) t).trace
      = ((Real.exp ((-(2 * t)) * n) : ℝ) : ℂ) := by
    rw [wit_gram t n, Matrix.trace_diagonal, Fin.sum_univ_one, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [htr2, Fin.sum_univ_one] at htr
  have heig : hG.eigenvalues 0 = Real.exp ((-(2 * t)) * n) := by
    have h5 := congrArg Complex.re htr
    simp only [Complex.ofReal_re] at h5
    exact h5.symm
  refine le_antisymm (by rw [← heig]; exact Finset.inf'_le _ (Finset.mem_univ 0)) ?_
  refine Finset.le_inf' _ _ fun b _ => ?_
  have hb : b = 0 := Subsingleton.elim b 0
  rw [hb, heig]

/-- The witness collapse: `λ_min(G_{t₀,n}) = e^{-2t₀n} → 0` for `t₀ > 0`. -/
theorem wit_collapse {t₀ : ℝ} (ht₀ : 0 < t₀) :
    Tendsto
      (fun n => minEig (delayedGram_isHermitian (witH_isHermitian n)
          (1 : Matrix (Fin 1) (Fin 1) ℂ) t₀)
        (Finset.univ_nonempty_iff.mpr ⟨⟨0, one_pos⟩⟩))
      atTop (nhds 0) := by
  have hval : ∀ n : ℕ, minEig (delayedGram_isHermitian (witH_isHermitian n)
      (1 : Matrix (Fin 1) (Fin 1) ℂ) t₀)
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, one_pos⟩⟩)
      = Real.exp (-(2 * t₀)) ^ n := by
    intro n
    rw [wit_minEig t₀ n]
    rw [show (-(2 * t₀)) * (n : ℝ) = (n : ℝ) * (-(2 * t₀)) by ring,
      Real.exp_nat_mul]
  simp only [hval]
  refine tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_nonneg _) ?_
  rw [Real.exp_lt_one_iff]
  linarith

/-- **`cth:SMST-positive-time-high-energy-escape`, witness clause**: the
one-dimensional bank `H_n = n`, `Ψ_n = 1` has `G_{0,n} ⪰ I`, collapsing
delayed minimal eigenvalues, and hence unit coefficient vectors with
escaping normalized spectral measures. -/
theorem one_dim_bank_escape {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ∃ c : ∀ _ : ℕ, Fin 1 → ℂ,
      (∀ n, star (c n) ⬝ᵥ c n = 1) ∧
      ∀ R : ℝ, Tendsto
        (fun n =>
          (∑ i ∈ Finset.univ.filter
              (fun i => |(witH_isHermitian n).eigenvalues i| ≤ R),
              specWeight (witH_isHermitian n) ((1 : Matrix (Fin 1) (Fin 1) ℂ) *ᵥ c n) i)
            / ∑ i, specWeight (witH_isHermitian n) ((1 : Matrix (Fin 1) (Fin 1) ℂ) *ᵥ c n) i)
        atTop (nhds 0) :=
  energy_escape (fun _ => one_pos) witH witH_isHermitian (fun _ => 1)
    (fun _ => wit_base) ht₀ (wit_collapse ht₀)

end Witness

end HighEnergyEscape

/-! ### `cth:SMST-five-matrices-not-weighted` — Weighted panels not determined

Rendering: on `ℝ²` with `A(1) = e₁` and `F(1) = e₂`, the two cards are the
symmetric matrices `M_j = [[a,c],[c,b_j]]` with common `a = 2r/3`, small
common `c = r/6 > 0` and `b₀ = a ≠ b₁ = a - 2c`, whose spectra lie in
`(0,r)`.  The calibrated multiplier `f` is abstract: strictly monotone with
nonnegative preimages covering `(0,r)` (its range hypothesis).  The fibres
are literal: each `M_j` carries an explicit spectral resolution
`M_j = λ⁺P⁺ + λ⁻P⁻` (orthogonal symmetric idempotents summing to `1`,
built from Cayley–Hamilton), `H_j` is defined spectrally from chosen
nonnegative `f`-preimages of the eigenvalues, and applying `f` spectrally to
`H_j` recovers `M_j`.  Both cards have the same target `Y = M_jA = (a,c)`,
hence the same five matrices (DMC.28) `S = 1`, `T = a`, `U = a² + c²`,
`G = 1`, `C = c` and the same exact prior absorption `c²`; but the weighted
panels `⟨e₂, (1+H_j)^{2t} e₂⟩` (spectral real powers, `t > 0`) differ. -/

namespace FiveMatrixWeighted

/-! #### Generic 2×2 spectral resolutions -/

section Spectral2

variable (p q b lp lm : ℝ)

/-- The symmetric card matrix `M = [[p,q],[q,b]]`. -/
def symMat : Matrix (Fin 2) (Fin 2) ℝ := !![p, q; q, b]

/-- The upper spectral projection `(λ⁺-λ⁻)⁻¹(M - λ⁻)`. -/
noncomputable def projP : Matrix (Fin 2) (Fin 2) ℝ :=
  (lp - lm)⁻¹ • (symMat p q b - lm • 1)

/-- The lower spectral projection `(λ⁺-λ⁻)⁻¹(λ⁺ - M)`. -/
noncomputable def projM : Matrix (Fin 2) (Fin 2) ℝ :=
  (lp - lm)⁻¹ • (lp • (1 : Matrix (Fin 2) (Fin 2) ℝ) - symMat p q b)

variable {p q b lp lm}

section CH

variable (hsum : lp + lm = p + b) (hprod : lp * lm = p * b - q ^ 2)

set_option linter.flexible false in -- branch-dependent entry normal forms, closed per branch
include hsum hprod in
/-- Cayley–Hamilton for the card matrix with prescribed spectrum. -/
theorem cayley : (symMat p q b - lp • 1) * (symMat p q b - lm • 1) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
    first
      | linear_combination (-p) * hsum + hprod
      | linear_combination (-q) * hsum
      | linear_combination (-b) * hsum + hprod

/-- Shifted copies of a square matrix commute. -/
theorem shifted_comm {k : Type} [Fintype k] [DecidableEq k]
    (A : Matrix k k ℝ) (a c : ℝ) :
    (A - a • 1) * (A - c • 1) = (A - c • 1) * (A - a • 1) := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, smul_mul_assoc, mul_smul_comm,
    Matrix.mul_one, Matrix.one_mul]
  match_scalars <;> ring

include hsum hprod in
/-- Cayley–Hamilton with the factors reversed. -/
theorem cayley' : (symMat p q b - lm • 1) * (symMat p q b - lp • 1) = 0 := by
  rw [← shifted_comm]
  exact cayley hsum hprod

end CH

section Resolution

variable (hlt : lm < lp)

include hlt in
/-- The spectral projections resolve the identity. -/
theorem proj_sum : projP p q b lp lm + projM p q b lp lm = 1 := by
  have hne : lp - lm ≠ 0 := sub_ne_zero_of_ne hlt.ne'
  unfold projP projM
  match_scalars <;> field_simp <;> ring1

include hlt in
/-- The eigenvalue recombination `λ⁺P⁺ + λ⁻P⁻ = M`. -/
theorem proj_recomb :
    lp • projP p q b lp lm + lm • projM p q b lp lm = symMat p q b := by
  have hne : lp - lm ≠ 0 := sub_ne_zero_of_ne hlt.ne'
  unfold projP projM
  match_scalars <;> field_simp <;> ring

include hlt in
/-- The lower projection is the complement of the upper one. -/
theorem projM_eq : projM p q b lp lm = 1 - projP p q b lp lm := by
  rw [← proj_sum (p := p) (q := q) (b := b) hlt]
  abel

variable (hsum : lp + lm = p + b) (hprod : lp * lm = p * b - q ^ 2)

include hsum hprod hlt in
/-- The upper spectral projection is idempotent. -/
theorem projP_idem :
    projP p q b lp lm * projP p q b lp lm = projP p q b lp lm := by
  have hne : lp - lm ≠ 0 := sub_ne_zero_of_ne hlt.ne'
  have hdecomp : symMat p q b - lm • 1
      = (symMat p q b - lp • 1) + (lp - lm) • 1 := by module
  have hsq : (symMat p q b - lm • 1) * (symMat p q b - lm • 1)
      = (lp - lm) • (symMat p q b - lm • 1) := by
    calc (symMat p q b - lm • 1) * (symMat p q b - lm • 1)
        = ((symMat p q b - lp • 1) + (lp - lm) • 1)
          * (symMat p q b - lm • 1) := by rw [← hdecomp]
      _ = (symMat p q b - lp • 1) * (symMat p q b - lm • 1)
          + (lp - lm) • (symMat p q b - lm • 1) := by
          rw [Matrix.add_mul, smul_mul_assoc, Matrix.one_mul]
      _ = (lp - lm) • (symMat p q b - lm • 1) := by
          rw [cayley hsum hprod, zero_add]
  unfold projP
  rw [smul_mul_assoc, Matrix.mul_smul, hsq, smul_smul, smul_smul]
  congr 1
  field_simp

include hsum hprod hlt in
/-- The spectral projections are orthogonal. -/
theorem projP_mul_projM : projP p q b lp lm * projM p q b lp lm = 0 := by
  rw [projM_eq hlt, Matrix.mul_sub, Matrix.mul_one, projP_idem hlt hsum hprod,
    sub_self]

include hsum hprod hlt in
/-- The spectral projections are orthogonal (reversed order). -/
theorem projM_mul_projP : projM p q b lp lm * projP p q b lp lm = 0 := by
  rw [projM_eq hlt, Matrix.sub_mul, Matrix.one_mul, projP_idem hlt hsum hprod,
    sub_self]

include hsum hprod hlt in
/-- The lower spectral projection is idempotent. -/
theorem projM_idem :
    projM p q b lp lm * projM p q b lp lm = projM p q b lp lm := by
  rw [projM_eq hlt, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul,
    Matrix.one_mul, projP_idem hlt hsum hprod]
  abel

/-- The card matrix is symmetric. -/
theorem symMat_transpose : (symMat p q b)ᵀ = symMat p q b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symMat]

/-- The upper spectral projection is symmetric. -/
theorem projP_transpose : (projP p q b lp lm)ᵀ = projP p q b lp lm := by
  unfold projP
  rw [Matrix.transpose_smul, Matrix.transpose_sub, symMat_transpose,
    Matrix.transpose_smul, Matrix.transpose_one]

/-- The lower spectral projection is symmetric. -/
theorem projM_transpose : (projM p q b lp lm)ᵀ = projM p q b lp lm := by
  unfold projM
  rw [Matrix.transpose_smul, Matrix.transpose_sub, symMat_transpose,
    Matrix.transpose_smul, Matrix.transpose_one]

/-- The `e₂`-entry of a spectrally weighted panel. -/
theorem panel_entry (w1 w2 : ℝ) :
    (w1 • projP p q b lp lm + w2 • projM p q b lp lm) 1 1
      = (lp - lm)⁻¹ * (w1 * (b - lm) + w2 * (lp - b)) := by
  simp [projP, projM, symMat]
  ring

end Resolution

end Spectral2

/-! #### The shared unweighted packet (DMC.28) -/

section UnweightedCard

variable (p q b : ℝ)

/-- The entrance column `A(1) = e₁`. -/
def colE1 : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

/-- The prior column `F(1) = e₂`. -/
def colE2 : Matrix (Fin 2) (Fin 1) ℝ := !![0; 1]

/-- The target column `Y = MA` is the first column `(p, q)` of the card. -/
theorem card_target : symMat p q b * colE1 = !![p; q] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symMat, colE1, Matrix.mul_apply, Fin.sum_univ_two]

/-- `S = A^TA = 1`. -/
theorem card_S : colE1ᵀ * colE1 = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [colE1, Matrix.mul_apply, Fin.sum_univ_two]

/-- `D = A^TF = 0`. -/
theorem card_D : colE1ᵀ * colE2 = 0 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [colE1, colE2, Matrix.mul_apply, Fin.sum_univ_two]

/-- `E = F^TF = 1`. -/
theorem card_E : colE2ᵀ * colE2 = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [colE2, Matrix.mul_apply, Fin.sum_univ_two]

/-- **(DMC.28)**: `T = A^TY = p`. -/
theorem card_T : colE1ᵀ * (symMat p q b * colE1) = p • 1 := by
  rw [card_target]
  ext i j
  fin_cases i
  fin_cases j
  simp [colE1, Matrix.mul_apply, Fin.sum_univ_two]

/-- **(DMC.28)**: `U = Y^TY = p² + q²`. -/
theorem card_U :
    (symMat p q b * colE1)ᵀ * (symMat p q b * colE1) = (p ^ 2 + q ^ 2) • 1 := by
  rw [card_target]
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- **(DMC.28)**: the residualized prior Gram `G = E - D^TS⁻¹D = 1`. -/
theorem card_G :
    colE2ᵀ * colE2 - (colE1ᵀ * colE2)ᵀ * (colE1ᵀ * colE1)⁻¹ * (colE1ᵀ * colE2)
      = 1 := by
  rw [card_D, card_E]
  simp

/-- **(DMC.28)**: the mixed row `C = F^TY - D^TS⁻¹T = q`. -/
theorem card_C :
    colE2ᵀ * (symMat p q b * colE1)
      - (colE1ᵀ * colE2)ᵀ * (colE1ᵀ * colE1)⁻¹ * (colE1ᵀ * (symMat p q b * colE1))
      = q • 1 := by
  rw [card_D, card_target]
  ext i j
  fin_cases i
  fin_cases j
  simp [colE2, Matrix.mul_apply, Fin.sum_univ_two]

/-- The entrance range projection `P_A = AA^T` (symmetric, idempotent,
fixing `A`), and the residualized prior `N = (1-P_A)F = F`. -/
theorem card_projA :
    (colE1 * colE1ᵀ)ᵀ = colE1 * colE1ᵀ
      ∧ (colE1 * colE1ᵀ) * (colE1 * colE1ᵀ) = colE1 * colE1ᵀ
      ∧ (colE1 * colE1ᵀ) * colE1 = colE1
      ∧ ((1 : Matrix (Fin 2) (Fin 2) ℝ) - colE1 * colE1ᵀ) * colE2 = colE2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [colE1, colE2, Matrix.mul_apply, Matrix.vecMul, dotProduct,
          Fin.sum_univ_two, Matrix.one_apply]

/-- The exact prior absorption `𝔸 = Y^T P_N Y = q²` with `P_N = NN^T`. -/
theorem card_absorption :
    (symMat p q b * colE1)ᵀ * (colE2 * colE2ᵀ) * (symMat p q b * colE1)
      = q ^ 2 • 1 := by
  rw [card_target]
  ext i j
  fin_cases i
  fin_cases j
  simp [colE2, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  ring

end UnweightedCard

/-- **(DMC.28), shared packet**: the two cards `b₀ = 2r/3` and `b₁ = r/3`
(common `p = 2r/3`, `q = r/6`) have the same target column and hence
identical five matrices `(S,T,U,G,C)` and identical exact prior
absorption. -/
theorem cards_share_unweighted (r : ℝ) :
    symMat (2 * r / 3) (r / 6) (2 * r / 3) * colE1
        = symMat (2 * r / 3) (r / 6) (r / 3) * colE1
      ∧ colE1ᵀ * (symMat (2 * r / 3) (r / 6) (2 * r / 3) * colE1)
        = colE1ᵀ * (symMat (2 * r / 3) (r / 6) (r / 3) * colE1)
      ∧ (symMat (2 * r / 3) (r / 6) (2 * r / 3) * colE1)ᵀ
          * (symMat (2 * r / 3) (r / 6) (2 * r / 3) * colE1)
        = (symMat (2 * r / 3) (r / 6) (r / 3) * colE1)ᵀ
          * (symMat (2 * r / 3) (r / 6) (r / 3) * colE1)
      ∧ colE2ᵀ * (symMat (2 * r / 3) (r / 6) (2 * r / 3) * colE1)
          - (colE1ᵀ * colE2)ᵀ * (colE1ᵀ * colE1)⁻¹
            * (colE1ᵀ * (symMat (2 * r / 3) (r / 6) (2 * r / 3) * colE1))
        = colE2ᵀ * (symMat (2 * r / 3) (r / 6) (r / 3) * colE1)
          - (colE1ᵀ * colE2)ᵀ * (colE1ᵀ * colE1)⁻¹
            * (colE1ᵀ * (symMat (2 * r / 3) (r / 6) (r / 3) * colE1))
      ∧ (symMat (2 * r / 3) (r / 6) (2 * r / 3) * colE1)ᵀ
          * (colE2 * colE2ᵀ) * (symMat (2 * r / 3) (r / 6) (2 * r / 3) * colE1)
        = (symMat (2 * r / 3) (r / 6) (r / 3) * colE1)ᵀ
          * (colE2 * colE2ᵀ) * (symMat (2 * r / 3) (r / 6) (r / 3) * colE1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [card_target, card_target]
  · rw [card_T, card_T]
  · rw [card_U, card_U]
  · rw [card_C, card_C]
  · rw [card_absorption, card_absorption]

/-! #### Calibrated preimages and the weighted panels -/

open Classical in
/-- A chosen nonnegative preimage of `y` under the calibrated multiplier. -/
noncomputable def preim (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  if h : ∃ x, 0 ≤ x ∧ f x = y then h.choose else 0

/-- The chosen preimage is a genuine nonnegative preimage when one exists. -/
theorem preim_spec {f : ℝ → ℝ} {y : ℝ} (h : ∃ x, 0 ≤ x ∧ f x = y) :
    0 ≤ preim f y ∧ f (preim f y) = y := by
  unfold preim
  split
  case isTrue h' => exact h'.choose_spec
  case isFalse h' => exact absurd h h'

/-- The spectrally defined right Hamiltonian `H = f⁻¹(M)` of a card. -/
noncomputable def specH (f : ℝ → ℝ) (p q b lp lm : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  preim f lp • projP p q b lp lm + preim f lm • projM p q b lp lm

/-- The weighted panel `⟨e₂, (1+H)^{2t} e₂⟩` of a card, applied spectrally
through the resolution of `H`. -/
noncomputable def panel (f : ℝ → ℝ) (t p q b lp lm : ℝ) : ℝ :=
  ((1 + preim f lp) ^ (2 * t) • projP p q b lp lm
    + (1 + preim f lm) ^ (2 * t) • projM p q b lp lm) 1 1

/-- The fibres are literal: `H` is symmetric with the card's spectral
resolution and eigenvalues the chosen `f`-preimages, and applying `f`
spectrally to `H` recovers the card matrix `M = f(H)`. -/
theorem specH_literal (f : ℝ → ℝ) {p q b lp lm : ℝ} (hlt : lm < lp)
    (hp : ∃ x, 0 ≤ x ∧ f x = lp) (hm : ∃ x, 0 ≤ x ∧ f x = lm) :
    (specH f p q b lp lm)ᵀ = specH f p q b lp lm
      ∧ specH f p q b lp lm
        = preim f lp • projP p q b lp lm + preim f lm • projM p q b lp lm
      ∧ 0 ≤ preim f lp ∧ 0 ≤ preim f lm
      ∧ f (preim f lp) • projP p q b lp lm + f (preim f lm) • projM p q b lp lm
        = symMat p q b := by
  refine ⟨?_, rfl, (preim_spec hp).1, (preim_spec hm).1, ?_⟩
  · unfold specH
    rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul,
      projP_transpose, projM_transpose]
  · rw [(preim_spec hp).2, (preim_spec hm).2]
    exact proj_recomb hlt

/-- The order-and-positivity comparison at the core of the witness. -/
theorem panel_compare {s w1p w1m w0p w0m : ℝ} (hs : 1 < s)
    (h1 : w1m < w0m) (h2 : w0m < w1p) (h3 : w1p < w0p) :
    (w1p * (s - 1) + w1m * (s + 1)) / (2 * s) < (w0p + w0m) / 2 := by
  have hs0 : (0 : ℝ) < s := lt_trans one_pos hs
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [mul_pos hs0 (sub_pos.mpr h3), mul_pos hs0 (sub_pos.mpr h1),
    h1.trans h2]

/-- `√2` is strictly between `1` and `2`. -/
theorem sqrt_two_bounds : 1 < Real.sqrt 2 ∧ Real.sqrt 2 < 2 := by
  have h2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have h0 := Real.sqrt_nonneg 2
  constructor <;> nlinarith

/-- The lower eigenvalue of the second card. -/
noncomputable def lmB (r : ℝ) : ℝ := r / 2 - r / 6 * Real.sqrt 2

/-- The upper eigenvalue of the second card. -/
noncomputable def lpB (r : ℝ) : ℝ := r / 2 + r / 6 * Real.sqrt 2

/-- **`cth:SMST-five-matrices-not-weighted`, weighted clause**: for every
strictly monotone calibrated multiplier `f` with nonnegative preimages
covering `(0,r)` and every `t > 0`, the two cards (which share the whole
unweighted packet by `cards_share_unweighted`) have different weighted
panels `⟨e₂,(1+H_j)^{2t}e₂⟩`. -/
theorem weighted_panels_differ (f : ℝ → ℝ)
    (hf : StrictMono f ∨ StrictAnti f) {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (hrange : ∀ y, 0 < y → y < r → ∃ x, 0 ≤ x ∧ f x = y) :
    panel f t (2 * r / 3) (r / 6) (2 * r / 3) (5 * r / 6) (r / 2)
      ≠ panel f t (2 * r / 3) (r / 6) (r / 3) (lpB r) (lmB r) := by
  obtain ⟨hs1, hs2⟩ := sqrt_two_bounds
  have hs0 : (0 : ℝ) < Real.sqrt 2 := lt_trans one_pos hs1
  -- the four eigenvalues, ordered and inside `(0, r)`
  have hlm1 : 0 < lmB r ∧ lmB r < r := by
    unfold lmB
    constructor <;> nlinarith
  have hlm0 : (0 : ℝ) < r / 2 ∧ r / 2 < r := by constructor <;> nlinarith
  have hlp1 : 0 < lpB r ∧ lpB r < r := by
    unfold lpB
    constructor <;> nlinarith
  have hlp0 : (0 : ℝ) < 5 * r / 6 ∧ 5 * r / 6 < r := by
    constructor <;> nlinarith
  have hord1 : lmB r < r / 2 := by unfold lmB; nlinarith
  have hord2 : r / 2 < lpB r := by unfold lpB; nlinarith
  have hord3 : lpB r < 5 * r / 6 := by unfold lpB; nlinarith
  -- chosen preimages
  have hex_lm1 := hrange (lmB r) hlm1.1 hlm1.2
  have hex_lm0 := hrange (r / 2) hlm0.1 hlm0.2
  have hex_lp1 := hrange (lpB r) hlp1.1 hlp1.2
  have hex_lp0 := hrange (5 * r / 6) hlp0.1 hlp0.2
  obtain ⟨hnn_lm1, hval_lm1⟩ := preim_spec hex_lm1
  obtain ⟨hnn_lm0, hval_lm0⟩ := preim_spec hex_lm0
  obtain ⟨hnn_lp1, hval_lp1⟩ := preim_spec hex_lp1
  obtain ⟨hnn_lp0, hval_lp0⟩ := preim_spec hex_lp0
  -- panel closed forms
  have h20 : (0:ℝ) < 2 * t := by linarith
  set wlm1 : ℝ := (1 + preim f (lmB r)) ^ (2 * t) with hwlm1
  set wlm0 : ℝ := (1 + preim f (r / 2)) ^ (2 * t) with hwlm0
  set wlp1 : ℝ := (1 + preim f (lpB r)) ^ (2 * t) with hwlp1
  set wlp0 : ℝ := (1 + preim f (5 * r / 6)) ^ (2 * t) with hwlp0
  have hpanel0 : panel f t (2 * r / 3) (r / 6) (2 * r / 3) (5 * r / 6) (r / 2)
      = (wlp0 + wlm0) / 2 := by
    rw [panel, panel_entry, ← hwlp0, ← hwlm0]
    have hden : (5 * r / 6 - r / 2) = r / 3 := by ring
    rw [hden]
    have hr3 : (r : ℝ) / 3 ≠ 0 := by positivity
    field_simp
    ring
  have hpanel1 : panel f t (2 * r / 3) (r / 6) (r / 3) (lpB r) (lmB r)
      = (wlp1 * (Real.sqrt 2 - 1) + wlm1 * (Real.sqrt 2 + 1))
        / (2 * Real.sqrt 2) := by
    rw [panel, panel_entry, ← hwlp1, ← hwlm1]
    have hden : lpB r - lmB r = r / 3 * Real.sqrt 2 := by unfold lpB lmB; ring
    have hb1 : r / 3 - lmB r = r / 6 * (Real.sqrt 2 - 1) := by unfold lmB; ring
    have hb2 : lpB r - r / 3 = r / 6 * (Real.sqrt 2 + 1) := by unfold lpB; ring
    rw [hden, hb1, hb2]
    have hrne : (r : ℝ) ≠ 0 := hr.ne'
    have hsne : Real.sqrt 2 ≠ 0 := hs0.ne'
    field_simp
    ring
  rw [hpanel0, hpanel1]
  -- monotone order transfer to the preimages and the rpow weights
  have hcmp : ∀ {u v : ℝ}, 0 ≤ u → u < v →
      (1 + u) ^ (2 * t) < (1 + v) ^ (2 * t) := by
    intro u v hu huv
    exact Real.rpow_lt_rpow (by linarith) (by linarith) h20
  rcases hf with hmono | hanti
  · have hlt1 : preim f (lmB r) < preim f (r / 2) := by
      by_contra hc
      push Not at hc
      have := hmono.monotone hc
      rw [hval_lm1, hval_lm0] at this
      linarith
    have hlt2 : preim f (r / 2) < preim f (lpB r) := by
      by_contra hc
      push Not at hc
      have := hmono.monotone hc
      rw [hval_lm0, hval_lp1] at this
      linarith
    have hlt3 : preim f (lpB r) < preim f (5 * r / 6) := by
      by_contra hc
      push Not at hc
      have := hmono.monotone hc
      rw [hval_lp1, hval_lp0] at this
      linarith
    have hw1 : wlm1 < wlm0 := hcmp hnn_lm1 hlt1
    have hw2 : wlm0 < wlp1 := hcmp hnn_lm0 hlt2
    have hw3 : wlp1 < wlp0 := hcmp hnn_lp1 hlt3
    exact (panel_compare hs1 hw1 hw2 hw3).ne'
  · have hlt1 : preim f (r / 2) < preim f (lmB r) := by
      by_contra hc
      push Not at hc
      have := hanti.antitone hc
      rw [hval_lm1, hval_lm0] at this
      linarith
    have hlt2 : preim f (lpB r) < preim f (r / 2) := by
      by_contra hc
      push Not at hc
      have := hanti.antitone hc
      rw [hval_lm0, hval_lp1] at this
      linarith
    have hlt3 : preim f (5 * r / 6) < preim f (lpB r) := by
      by_contra hc
      push Not at hc
      have := hanti.antitone hc
      rw [hval_lp1, hval_lp0] at this
      linarith
    have hw1 : wlm0 < wlm1 := hcmp hnn_lm0 hlt1
    have hw2 : wlp1 < wlm0 := hcmp hnn_lp1 hlt2
    have hw3 : wlp0 < wlp1 := hcmp hnn_lp0 hlt3
    have hneg := panel_compare hs1 (neg_lt_neg hw1) (neg_lt_neg hw2)
      (neg_lt_neg hw3)
    have hrew : (-wlp1 * (Real.sqrt 2 - 1) + -wlm1 * (Real.sqrt 2 + 1))
        / (2 * Real.sqrt 2)
        = -((wlp1 * (Real.sqrt 2 - 1) + wlm1 * (Real.sqrt 2 + 1))
          / (2 * Real.sqrt 2)) := by
      rw [← neg_div]
      ring_nf
    have hrew2 : (-wlp0 + -wlm0) / 2 = -((wlp0 + wlm0) / 2) := by ring
    rw [hrew, hrew2] at hneg
    have : (wlp0 + wlm0) / 2
        < (wlp1 * (Real.sqrt 2 - 1) + wlm1 * (Real.sqrt 2 + 1))
          / (2 * Real.sqrt 2) := by linarith
    exact this.ne

/-- The spectral data of the two witness cards: eigenvalue sums, products
and strict gaps, so both cards carry genuine spectral resolutions. -/
theorem witness_spectra {r : ℝ} (hr : 0 < r) :
    (5 * r / 6 + r / 2 = 2 * r / 3 + 2 * r / 3
        ∧ 5 * r / 6 * (r / 2) = 2 * r / 3 * (2 * r / 3) - (r / 6) ^ 2
        ∧ r / 2 < 5 * r / 6)
      ∧ (lpB r + lmB r = 2 * r / 3 + r / 3
        ∧ lpB r * lmB r = 2 * r / 3 * (r / 3) - (r / 6) ^ 2
        ∧ lmB r < lpB r) := by
  obtain ⟨hs1, -⟩ := sqrt_two_bounds
  have h2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  refine ⟨⟨by ring, by ring, by nlinarith⟩, ⟨?_, ?_, ?_⟩⟩
  · unfold lpB lmB
    ring
  · unfold lpB lmB
    nlinarith
  · unfold lpB lmB
    nlinarith

end FiveMatrixWeighted

end NCG
