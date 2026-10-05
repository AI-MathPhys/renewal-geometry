/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.TorusFourierTruncation

/-!
# Banach contraction for the conformal Hamiltonian (Lichnerowicz-type) equation on `𝕋³`

Generic infrastructure and the scalar core of `prop:generated-initial` (Einstein–Standard-Model
action-closure manuscript, `app:generated-dynamics`).  The Cauchy surface is `Σ = 𝕋³` (the
manuscript's setting for this construction); Sobolev norms are the trigonometric norms
`‖F‖_{H^r} = sn r F` of `TorusSobolevTransfer` (for which `H^r`, `r ≥ 2`, is an algebra).

* `exists_unique_fixedPoint_ball`, `norm_fixedPoint_le`, `norm_sub_fixedPoint_le`: Banach
  contraction on a closed ball of a complete normed space, with the a-priori bound
  `‖x*‖ ≤ ‖T0‖/(1-κ)` and the perturbation bound `‖x* - y*‖ ≤ ‖T y* - T' y*‖/(1-κ)`.
* `AlgNorm`: a submultiplicative (up to `K`) size functional on a commutative `ℂ`-algebra, with
  the power and Taylor-remainder estimates `pow_le`, `pow_sub_pow_le`, `gpow_sub_le`
  (`(1+u)^k - 1 - ku` is Lipschitz with constant `O(M)` on the `M`-ball).
* `ofSeq`: the isometry `ℓ²(ℤ³) ≅ H^s(𝕋³)` (`s ≥ 2`), `a ↦ Σ_n a(n) W_s(n)^{-1/2} e_n`, which
  makes `H^s` complete; `sobAlg r`: the subalgebra `H^r ∩ C(𝕋³)` (`r ≥ 2`) of `C(𝕋³, ℂ)` with
  its `AlgNorm` (`sobNorm`); `exists_fixedPoint_sn`: Banach contraction in `H^s ∩ C⁰`.
* Fourier multipliers: the Laplacian `lap` (`Δ : H^{r+2} → H^r`, `lap_spec`) and
  **`L_*⁻¹ = (-8Δ + μ_*)⁻¹ : H^r → H^{r+2}`** with `‖L_*⁻¹ f‖_{H^{r+2}} ≤ min(8, μ_*)⁻¹ ‖f‖_{H^r}`
  (`Linv_spec`, `L_Linv`, `Linv_L`: `L_*` is an isomorphism `H^{r+2} → H^r`, including the zero
  Fourier mode); conjugation (`conjCT_*`).
* The conformal Hamiltonian equation `eq:generated-Hamiltonian` (`HamiltonianEq`, `hamRes`), its
  multiplied form `L_* u = Φ(u)` (`hamRes_mul`, polynomial nonlinearity, `PhiA`), the map
  `𝒯 = L_*⁻¹ Φ` (`Tmap`) and its projected version `𝒯_N = P_N 𝒯` (`TmapN`): `Tmap_ball`
  (a `1/2`-contraction of the `H^{r+2}` ball for small sources), **`lichnerowicz_solution`**
  (existence, uniqueness, `‖w - 1‖_{H^{r+2}} ≤ C η`, `1/2 < w < 3/2`), `fixed_regular`
  (higher regularity), **`finite_conformal`** (projected fixed point in `Ran P_N`, rate
  `O(‖S_N - S‖ + N^{-p})`, residual `O(N^{-p})`), `norm_hamRes_le` (pointwise residual bound).
* **`ConstrainedInitialSolver`** (the hypotheses of `ass:constrained-initial-solver`) and
  **`ConstrainedInitialSolver.generated_initial`**, **`…generated_initial_finite`**
  (`prop:generated-initial`); non-vacuity `exampleSolver`.
-/

open Finset Filter Topology UnitAddTorus Metric
open scoped BigOperators Real ComplexConjugate

namespace RenewalGeometry.LichnerowiczContraction

open TorusFourierTruncation TorusSobolevTransfer PeriodicGridSobolev PeriodicGridSobolev.Sampling
  PeriodicGridSobolev.Composition

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : MeasureTheory.IsProbabilityMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)

noncomputable section

/-! ### Banach contraction on a closed ball -/

section Banach

variable {X : Type*} [NormedAddCommGroup X] [CompleteSpace X]

/-- **Banach contraction on the closed ball `‖x‖ ≤ ρ`**: a self-map of the ball which is a
`κ`-contraction there (`κ < 1`) has exactly one fixed point in the ball. -/
theorem exists_unique_fixedPoint_ball {T : X → X} {ρ κ : ℝ} (hρ : 0 ≤ ρ) (hκ0 : 0 ≤ κ)
    (hκ1 : κ < 1) (hmaps : ∀ x, ‖x‖ ≤ ρ → ‖T x‖ ≤ ρ)
    (hlip : ∀ x y, ‖x‖ ≤ ρ → ‖y‖ ≤ ρ → ‖T x - T y‖ ≤ κ * ‖x - y‖) :
    ∃ x, ‖x‖ ≤ ρ ∧ T x = x ∧ ∀ y, ‖y‖ ≤ ρ → T y = y → y = x := by
  set s := closedBall (0 : X) ρ with hsdef
  have hs : ∀ x, x ∈ s ↔ ‖x‖ ≤ ρ := fun x => by simp [hsdef]
  have hmaps' : Set.MapsTo T s s := fun x hx => (hs _).2 (hmaps x ((hs x).1 hx))
  have : CompleteSpace s := isClosed_closedBall.completeSpace_coe
  have : Nonempty s := ⟨⟨0, (hs 0).2 (by simpa using hρ)⟩⟩
  have hc : ContractingWith ⟨κ, hκ0⟩ (hmaps'.restrict T s s) := by
    refine ⟨by exact_mod_cast hκ1, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    exact hlip _ _ ((hs _).1 x.2) ((hs _).1 y.2)
  have hfix := ContractingWith.fixedPoint_isFixedPt (f := hmaps'.restrict T s s) hc
  refine ⟨(ContractingWith.fixedPoint _ hc).1, (hs _).1 (ContractingWith.fixedPoint _ hc).2,
    congrArg Subtype.val hfix, fun y hy hTy => ?_⟩
  have := ContractingWith.fixedPoint_unique (f := hmaps'.restrict T s s) hc
    (x := ⟨y, (hs _).2 hy⟩) (Subtype.ext hTy)
  exact congrArg Subtype.val this

/-- A-priori bound for a fixed point of a `κ`-contraction: `‖x*‖ ≤ ‖T 0‖ / (1 - κ)`. -/
theorem norm_fixedPoint_le {T : X → X} {κ : ℝ} (hκ1 : κ < 1) {x : X} (hx : T x = x)
    (hlip : ‖T x - T 0‖ ≤ κ * ‖x - 0‖) : ‖x‖ ≤ ‖T 0‖ / (1 - κ) := by
  rw [le_div_iff₀ (by linarith)]
  have h1 : ‖x‖ ≤ ‖T x - T 0‖ + ‖T 0‖ := by
    calc ‖x‖ = ‖(T x - T 0) + T 0‖ := by rw [sub_add_cancel, hx]
      _ ≤ _ := norm_add_le _ _
  rw [sub_zero] at hlip
  nlinarith

/-- Perturbation of fixed points: `‖x - y‖ ≤ ‖T y - T' y‖ / (1 - κ)` for `T x = x`, `T' y = y`. -/
theorem norm_sub_fixedPoint_le {T T' : X → X} {κ : ℝ} (hκ1 : κ < 1) {x y : X} (hx : T x = x)
    (hy : T' y = y) (hlip : ‖T x - T y‖ ≤ κ * ‖x - y‖) :
    ‖x - y‖ ≤ ‖T y - T' y‖ / (1 - κ) := by
  rw [le_div_iff₀ (by linarith)]
  have h1 : ‖x - y‖ ≤ ‖T x - T y‖ + ‖T y - T' y‖ := by
    calc ‖x - y‖ = ‖(T x - T y) + (T y - T' y)‖ := by rw [hx, hy]; abel_nf
      _ ≤ _ := norm_add_le _ _
  nlinarith

end Banach

/-! ### Submultiplicative size functionals on commutative algebras -/

/-- A size functional `ν` on a commutative `ℂ`-algebra, subadditive, absolutely homogeneous and
submultiplicative up to a constant `K ≥ 1` (the `H^r(𝕋³)` norm, `r ≥ 2`, on `H^r ∩ C⁰`). -/
structure AlgNorm (R : Type*) [CommRing R] [Algebra ℂ R] where
  /-- the size functional -/
  ν : R → ℝ
  /-- the algebra constant -/
  K : ℝ
  one_le_K : 1 ≤ K
  nonneg : ∀ x, 0 ≤ ν x
  add_le : ∀ x y, ν (x + y) ≤ ν x + ν y
  smul_eq : ∀ (c : ℂ) x, ν (c • x) = ‖c‖ * ν x
  mul_le : ∀ x y, ν (x * y) ≤ K * ν x * ν y
  one_le : ν 1 ≤ 1

namespace AlgNorm

variable {R : Type*} [CommRing R] [Algebra ℂ R] (N : AlgNorm R)

theorem zero_eq : N.ν 0 = 0 := by
  have := N.smul_eq 0 0
  rw [zero_smul, norm_zero, zero_mul] at this
  exact this

theorem neg_eq (x : R) : N.ν (-x) = N.ν x := by
  have := N.smul_eq (-1) x
  rw [neg_one_smul, norm_neg, norm_one, one_mul] at this
  exact this

theorem sub_le (x y : R) : N.ν (x - y) ≤ N.ν x + N.ν y := by
  rw [sub_eq_add_neg]; exact (N.add_le _ _).trans (by rw [N.neg_eq])

theorem sub_comm' (x y : R) : N.ν (x - y) = N.ν (y - x) := by
  rw [← N.neg_eq, neg_sub]

theorem nsmul_le (k : ℕ) (x : R) : N.ν (k • x) ≤ k * N.ν x := by
  induction k with
  | zero => simp [N.zero_eq]
  | succ k ih =>
    rw [succ_nsmul]
    refine (N.add_le _ _).trans ?_
    push_cast; linarith

theorem mul_le' {x y : R} {a b : ℝ} (hx : N.ν x ≤ a) (hy : N.ν y ≤ b) :
    N.ν (x * y) ≤ N.K * a * b := by
  refine (N.mul_le x y).trans ?_
  have hK : 0 ≤ N.K := by linarith [N.one_le_K]
  have := N.nonneg x; have := N.nonneg y
  have : N.K * N.ν x ≤ N.K * a := mul_le_mul_of_nonneg_left hx hK
  calc N.K * N.ν x * N.ν y ≤ N.K * a * N.ν y := mul_le_mul_of_nonneg_right this (N.nonneg y)
    _ ≤ N.K * a * b := mul_le_mul_of_nonneg_left hy (by nlinarith [N.nonneg x])

/-- `ν(x^k) ≤ (K max(1, ν x))^k`. -/
theorem pow_le (x : R) (k : ℕ) : N.ν (x ^ k) ≤ (N.K * max 1 (N.ν x)) ^ k := by
  induction k with
  | zero => simpa using N.one_le
  | succ k ih =>
    rw [pow_succ, pow_succ]
    refine (N.mul_le _ _).trans ?_
    have h1 : N.ν x ≤ max 1 (N.ν x) := le_max_right _ _
    have hK := N.one_le_K
    have h0 := N.nonneg (x ^ k)
    calc N.K * N.ν (x ^ k) * N.ν x ≤ N.K * N.ν (x ^ k) * max 1 (N.ν x) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = N.ν (x ^ k) * (N.K * max 1 (N.ν x)) := by ring
      _ ≤ (N.K * max 1 (N.ν x)) ^ k * (N.K * max 1 (N.ν x)) :=
          mul_le_mul_of_nonneg_right ih (by positivity)

theorem pow_le_of_le {x : R} {M : ℝ} (hx : N.ν x ≤ M) (k : ℕ) :
    N.ν (x ^ k) ≤ (N.K * max 1 M) ^ k := by
  refine (N.pow_le x k).trans (pow_le_pow_left₀
    (mul_nonneg (by linarith [N.one_le_K]) (zero_le_one.trans (le_max_left _ _))) ?_ k)
  exact mul_le_mul_of_nonneg_left (max_le_max le_rfl hx) (by linarith [N.one_le_K])

/-- **Lipschitz bound for powers**: `ν(x^k - y^k) ≤ k (K max(1,M))^k ν(x - y)` on the `M`-ball. -/
theorem pow_sub_pow_le {x y : R} {M : ℝ} (hx : N.ν x ≤ M) (hy : N.ν y ≤ M) (k : ℕ) :
    N.ν (x ^ k - y ^ k) ≤ k * (N.K * max 1 M) ^ k * N.ν (x - y) := by
  set B := N.K * max 1 M with hB
  have hK := N.one_le_K
  have hB1 : 1 ≤ B := by
    rw [hB]; nlinarith [le_max_left 1 M]
  have hKM : N.K * M ≤ B := mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)
  induction k with
  | zero => simp [N.zero_eq]
  | succ k ih =>
    have e : x ^ (k + 1) - y ^ (k + 1) = x * (x ^ k - y ^ k) + (x - y) * y ^ k := by ring
    rw [e]
    refine (N.add_le _ _).trans ?_
    have h1 : N.ν (x * (x ^ k - y ^ k)) ≤ B * (k * B ^ k * N.ν (x - y)) := by
      refine (N.mul_le' hx ih).trans (le_of_eq_of_le rfl ?_)
      exact mul_le_mul_of_nonneg_right hKM (by have := N.nonneg (x - y); positivity)
    have h2 : N.ν ((x - y) * y ^ k) ≤ N.K * N.ν (x - y) * B ^ k :=
      N.mul_le' le_rfl (N.pow_le_of_le hy k)
    have hKB : N.K ≤ B := by
      rw [hB]; nlinarith [le_max_left 1 M]
    have h3 : N.ν ((x - y) * y ^ k) ≤ B ^ (k + 1) * N.ν (x - y) := by
      refine h2.trans ?_
      have := N.nonneg (x - y)
      calc N.K * N.ν (x - y) * B ^ k ≤ B * N.ν (x - y) * B ^ k := by gcongr
        _ = B ^ (k + 1) * N.ν (x - y) := by ring
    calc _ ≤ B * (k * B ^ k * N.ν (x - y)) + B ^ (k + 1) * N.ν (x - y) := add_le_add h1 h3
      _ = ((k + 1 : ℕ) : ℝ) * B ^ (k + 1) * N.ν (x - y) := by push_cast; ring

/-- The second-order Taylor remainder `g_k(u) = (1 + u)^k - 1 - k u`. -/
def gpow (k : ℕ) (u : R) : R := (1 + u) ^ k - 1 - k • u

/-- The first-order remainder `f_k(u) = (1 + u)^k - 1`. -/
def fpow (k : ℕ) (u : R) : R := (1 + u) ^ k - 1

theorem gpow_zero_arg (k : ℕ) : gpow k (0 : R) = 0 := by simp [gpow]

theorem fpow_zero_arg (k : ℕ) : fpow k (0 : R) = 0 := by simp [fpow]

theorem gpow_succ (k : ℕ) (u : R) :
    gpow (k + 1) u = (1 + u) * gpow k u + k • (u * u) := by
  simp only [gpow, nsmul_eq_mul]; push_cast; ring

/-- The constants of the Taylor-remainder estimate. -/
def cg (K : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => 3 * K * cg K k + 2 * k * K

theorem cg_nonneg {K : ℝ} (hK : 0 ≤ K) : ∀ k, 0 ≤ cg K k
  | 0 => le_rfl
  | k + 1 => by
    have := cg_nonneg hK k
    simp only [cg]; positivity

/-- **Quadratic Taylor remainder**: on the ball `ν ≤ M ≤ 1`,
`ν(g_k(u) - g_k(v)) ≤ c_k M ν(u - v)`. -/
theorem gpow_sub_le {u v : R} {M : ℝ} (hM : M ≤ 1) (hu : N.ν u ≤ M) (hv : N.ν v ≤ M) (k : ℕ) :
    N.ν (gpow k u - gpow k v) ≤ cg N.K k * M * N.ν (u - v) := by
  have hK := N.one_le_K
  have hM0 : 0 ≤ M := (N.nonneg u).trans hu
  induction k generalizing u v with
  | zero => simp [gpow, N.zero_eq, cg]
  | succ k ih =>
    have hc := cg_nonneg (by linarith : 0 ≤ N.K) k
    have hd := N.nonneg (u - v)
    have e : gpow (k + 1) u - gpow (k + 1) v =
        ((1 + u) * (gpow k u - gpow k v) + (u - v) * gpow k v) + k • ((u + v) * (u - v)) := by
      rw [gpow_succ, gpow_succ]; simp only [nsmul_eq_mul]; ring
    rw [e]
    have h1u : N.ν (1 + u) ≤ 2 := (N.add_le _ _).trans (by linarith [N.one_le])
    -- three pieces
    have p1 : N.ν ((1 + u) * (gpow k u - gpow k v)) ≤ N.K * 2 * (cg N.K k * M * N.ν (u - v)) :=
      N.mul_le' h1u (ih hu hv)
    have hgv : N.ν (gpow k v) ≤ cg N.K k * M * M := by
      have := ih (u := v) (v := 0) hv (by rw [N.zero_eq]; exact hM0)
      rw [gpow_zero_arg, sub_zero, sub_zero] at this
      exact this.trans (mul_le_mul_of_nonneg_left hv (by positivity))
    have p2 : N.ν ((u - v) * gpow k v) ≤ N.K * N.ν (u - v) * (cg N.K k * M * M) :=
      N.mul_le' le_rfl hgv
    have huv : N.ν (u + v) ≤ 2 * M := (N.add_le _ _).trans (by linarith)
    have p3 : N.ν (k • ((u + v) * (u - v))) ≤ k * (N.K * (2 * M) * N.ν (u - v)) :=
      (N.nsmul_le _ _).trans (mul_le_mul_of_nonneg_left (N.mul_le' huv le_rfl) (by positivity))
    have hMM : M * M ≤ M := by nlinarith
    calc _ ≤ N.ν ((1 + u) * (gpow k u - gpow k v) + (u - v) * gpow k v) +
          N.ν (k • ((u + v) * (u - v))) := N.add_le _ _
      _ ≤ (N.ν ((1 + u) * (gpow k u - gpow k v)) + N.ν ((u - v) * gpow k v)) +
          N.ν (k • ((u + v) * (u - v))) := add_le_add (N.add_le _ _) le_rfl
      _ ≤ N.K * 2 * (cg N.K k * M * N.ν (u - v)) + N.K * N.ν (u - v) * (cg N.K k * M * M) +
          k * (N.K * (2 * M) * N.ν (u - v)) := add_le_add (add_le_add p1 p2) p3
      _ ≤ N.K * 2 * (cg N.K k * M * N.ν (u - v)) + N.K * N.ν (u - v) * (cg N.K k * M) +
          k * (N.K * (2 * M) * N.ν (u - v)) := by
          gcongr
          exact mul_le_of_le_one_right (by positivity) hM
      _ = cg N.K (k + 1) * M * N.ν (u - v) := by simp only [cg]; ring

/-- First-order remainder, Lipschitz form: `ν(f_k(u) - f_k(v)) ≤ k (2K)^k ν(u - v)` on the ball
`ν ≤ M ≤ 1`. -/
theorem fpow_sub_le {u v : R} {M : ℝ} (hM : M ≤ 1) (hu : N.ν u ≤ M) (hv : N.ν v ≤ M) (k : ℕ) :
    N.ν (fpow k u - fpow k v) ≤ k * (2 * N.K) ^ k * N.ν (u - v) := by
  have h1u : N.ν (1 + u) ≤ 2 := (N.add_le _ _).trans (by linarith [N.one_le])
  have h1v : N.ν (1 + v) ≤ 2 := (N.add_le _ _).trans (by linarith [N.one_le])
  have e : fpow k u - fpow k v = (1 + u) ^ k - (1 + v) ^ k := by simp only [fpow]; ring
  rw [e]
  refine (N.pow_sub_pow_le h1u h1v k).trans (le_of_eq ?_)
  have : max 1 (2 : ℝ) = 2 := by norm_num
  rw [this, show (1 + u) - (1 + v) = u - v by ring]
  ring

theorem fpow_le {u : R} {M : ℝ} (hM : M ≤ 1) (hu : N.ν u ≤ M) (k : ℕ) :
    N.ν (fpow k u) ≤ k * (2 * N.K) ^ k * N.ν u := by
  have h0 : N.ν (0 : R) ≤ M := by rw [N.zero_eq]; exact (N.nonneg u).trans hu
  have := N.fpow_sub_le hM hu h0 k
  rwa [fpow_zero_arg, sub_zero, sub_zero] at this

theorem onepow_le {u : R} {M : ℝ} (hM : M ≤ 1) (hu : N.ν u ≤ M) (k : ℕ) :
    N.ν ((1 + u) ^ k) ≤ (2 * N.K) ^ k := by
  have h1u : N.ν (1 + u) ≤ 2 := (N.add_le _ _).trans (by linarith [N.one_le])
  refine (N.pow_le_of_le h1u k).trans (le_of_eq ?_)
  rw [show max 1 (2 : ℝ) = 2 by norm_num, mul_comm]

/-- The right-hand side of the conformal Hamiltonian equation multiplied by `w⁷`
(`w = 1 + x`, `D` standing for `Δx`):
`Φ = G g₈(x) + B g₄(x) - C g₁₂(x) + δA + δB (1+x)⁴ + Y (1+x)⁶ + 8 ((1+x)⁷ - 1) D`. -/
def PhiA (G B C : ℝ) (δA δB Y x D : R) : R :=
  (G : ℂ) • gpow 8 x + (B : ℂ) • gpow 4 x - (C : ℂ) • gpow 12 x + δA + δB * (1 + x) ^ 4 +
    Y * (1 + x) ^ 6 + (8 : ℂ) • (fpow 7 x * D)

theorem map_PhiA {S : Type*} [CommRing S] [Algebra ℂ S] (φ : R →ₐ[ℂ] S) (G B C : ℝ)
    (δA δB Y x D : R) :
    φ (PhiA G B C δA δB Y x D) = PhiA G B C (φ δA) (φ δB) (φ Y) (φ x) (φ D) := by
  simp only [PhiA, gpow, fpow, map_add, map_sub, map_mul, map_smul, map_pow, map_nsmul, map_one]

theorem PhiA_zero (G B C : ℝ) (δA δB Y : R) : PhiA G B C δA δB Y 0 0 = δA + δB + Y := by
  simp [PhiA, gpow, fpow]

theorem PhiA_sub_eq (G B C : ℝ) (δA δB Y x y Dx Dy : R) :
    PhiA G B C δA δB Y x Dx - PhiA G B C δA δB Y y Dy =
      ((((G : ℂ) • (gpow 8 x - gpow 8 y) + (B : ℂ) • (gpow 4 x - gpow 4 y)) +
        (-(C : ℂ)) • (gpow 12 x - gpow 12 y)) +
        (δB * (fpow 4 x - fpow 4 y) + Y * (fpow 6 x - fpow 6 y))) +
        (8 : ℂ) • ((fpow 7 x - fpow 7 y) * Dx + fpow 7 y * (Dx - Dy)) := by
  simp only [PhiA, gpow, fpow, Algebra.smul_def, map_neg]
  ring

theorem PhiA_src_sub_eq (G B C : ℝ) (δA δB Y δA' δB' Y' x D : R) :
    PhiA G B C δA δB Y x D - PhiA G B C δA' δB' Y' x D =
      (δA - δA') + ((δB - δB') * (1 + x) ^ 4 + (Y - Y') * (1 + x) ^ 6) := by
  simp only [PhiA]; ring

/-- The Lipschitz constant of `Φ`. -/
def lipC (K G B C : ℝ) : ℝ :=
  1 + |G| * cg K 8 + |B| * cg K 4 + |C| * cg K 12 + 336 * K * (2 * K) ^ 7 +
    6 * K * (2 * K) ^ 6 + 4 * K * (2 * K) ^ 4

theorem one_le_lipC {K : ℝ} (hK : 0 ≤ K) (G B C : ℝ) : 1 ≤ lipC K G B C := by
  unfold lipC
  have := cg_nonneg hK 8; have := cg_nonneg hK 4; have := cg_nonneg hK 12
  have : 0 ≤ |G| * cg K 8 := by positivity
  have : 0 ≤ |B| * cg K 4 := by positivity
  have : 0 ≤ |C| * cg K 12 := by positivity
  have : 0 ≤ 336 * K * (2 * K) ^ 7 := by positivity
  have : 0 ≤ 6 * K * (2 * K) ^ 6 := by positivity
  have : 0 ≤ 4 * K * (2 * K) ^ 4 := by positivity
  linarith

/-- **Lipschitz estimate for `Φ`** on the ball `ν(x), ν(y) ≤ M ≤ 1`, `ν(Δx) ≤ 3M`:
`ν(Φ(x, Δx) - Φ(y, Δy)) ≤ L (M + ν(δB) + ν(Y)) d` when `ν(x - y) ≤ d`, `ν(Δx - Δy) ≤ 3d`. -/
theorem PhiA_sub_le (G B C : ℝ) (δA δB Y : R) {x y Dx Dy : R} {M d : ℝ} (hM : M ≤ 1)
    (hx : N.ν x ≤ M) (hy : N.ν y ≤ M) (hDx : N.ν Dx ≤ 3 * M) (hxy : N.ν (x - y) ≤ d)
    (hD : N.ν (Dx - Dy) ≤ 3 * d) :
    N.ν (PhiA G B C δA δB Y x Dx - PhiA G B C δA δB Y y Dy) ≤
      lipC N.K G B C * (M + N.ν δB + N.ν Y) * d := by
  have hK := N.one_le_K
  have hK0 : 0 ≤ N.K := by linarith
  have hM0 : 0 ≤ M := (N.nonneg x).trans hx
  have hd0 : 0 ≤ d := (N.nonneg _).trans hxy
  have hB0 := N.nonneg δB
  have hY0 := N.nonneg Y
  have c8 := cg_nonneg hK0 8; have c4 := cg_nonneg hK0 4; have c12 := cg_nonneg hK0 12
  rw [PhiA_sub_eq]
  -- the six pieces
  have p1 : N.ν ((G : ℂ) • (gpow 8 x - gpow 8 y)) ≤ |G| * cg N.K 8 * M * d := by
    rw [N.smul_eq, Complex.norm_real, Real.norm_eq_abs]
    have := (N.gpow_sub_le hM hx hy 8).trans
      (mul_le_mul_of_nonneg_left hxy (by positivity))
    calc |G| * N.ν (gpow 8 x - gpow 8 y) ≤ |G| * (cg N.K 8 * M * d) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = _ := by ring
  have p2 : N.ν ((B : ℂ) • (gpow 4 x - gpow 4 y)) ≤ |B| * cg N.K 4 * M * d := by
    rw [N.smul_eq, Complex.norm_real, Real.norm_eq_abs]
    have := (N.gpow_sub_le hM hx hy 4).trans
      (mul_le_mul_of_nonneg_left hxy (by positivity))
    calc |B| * N.ν (gpow 4 x - gpow 4 y) ≤ |B| * (cg N.K 4 * M * d) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = _ := by ring
  have p3 : N.ν ((-(C : ℂ)) • (gpow 12 x - gpow 12 y)) ≤ |C| * cg N.K 12 * M * d := by
    rw [N.smul_eq, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    have := (N.gpow_sub_le hM hx hy 12).trans
      (mul_le_mul_of_nonneg_left hxy (by positivity))
    calc |C| * N.ν (gpow 12 x - gpow 12 y) ≤ |C| * (cg N.K 12 * M * d) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = _ := by ring
  have hf : ∀ k : ℕ, N.ν (fpow k x - fpow k y) ≤ k * (2 * N.K) ^ k * d := fun k =>
    (N.fpow_sub_le hM hx hy k).trans (mul_le_mul_of_nonneg_left hxy (by positivity))
  have p4 : N.ν (δB * (fpow 4 x - fpow 4 y)) ≤ 4 * N.K * (2 * N.K) ^ 4 * N.ν δB * d := by
    refine (N.mul_le' le_rfl (hf 4)).trans (le_of_eq ?_); push_cast; ring
  have p5 : N.ν (Y * (fpow 6 x - fpow 6 y)) ≤ 6 * N.K * (2 * N.K) ^ 6 * N.ν Y * d := by
    refine (N.mul_le' le_rfl (hf 6)).trans (le_of_eq ?_); push_cast; ring
  have hf7y : N.ν (fpow 7 y) ≤ 7 * (2 * N.K) ^ 7 * M := by
    have := N.fpow_le hM hy 7
    push_cast at this
    exact this.trans (mul_le_mul_of_nonneg_left hy (by positivity))
  have p6 : N.ν ((8 : ℂ) • ((fpow 7 x - fpow 7 y) * Dx + fpow 7 y * (Dx - Dy))) ≤
      336 * N.K * (2 * N.K) ^ 7 * M * d := by
    rw [N.smul_eq]
    have q1 : N.ν ((fpow 7 x - fpow 7 y) * Dx) ≤ N.K * (7 * (2 * N.K) ^ 7 * d) * (3 * M) := by
      have := hf 7; push_cast at this; exact N.mul_le' this hDx
    have q2 : N.ν (fpow 7 y * (Dx - Dy)) ≤ N.K * (7 * (2 * N.K) ^ 7 * M) * (3 * d) :=
      N.mul_le' hf7y hD
    have := (N.add_le _ _).trans (add_le_add q1 q2)
    calc ‖(8 : ℂ)‖ * N.ν ((fpow 7 x - fpow 7 y) * Dx + fpow 7 y * (Dx - Dy))
        ≤ 8 * (N.K * (7 * (2 * N.K) ^ 7 * d) * (3 * M) +
            N.K * (7 * (2 * N.K) ^ 7 * M) * (3 * d)) := by
          rw [show ‖(8 : ℂ)‖ = 8 by norm_num]
          exact mul_le_mul_of_nonneg_left this (by norm_num)
      _ = 336 * N.K * (2 * N.K) ^ 7 * M * d := by ring
  have hsum := (N.add_le _ _).trans (add_le_add ((N.add_le _ _).trans (add_le_add
    ((N.add_le _ _).trans (add_le_add ((N.add_le _ _).trans (add_le_add p1 p2)) p3))
    ((N.add_le _ _).trans (add_le_add p4 p5)))) p6)
  refine hsum.trans ?_
  unfold lipC
  have e1 : 0 ≤ |G| * cg N.K 8 := by positivity
  have e2 : 0 ≤ |B| * cg N.K 4 := by positivity
  have e3 : 0 ≤ |C| * cg N.K 12 := by positivity
  have e4 : 0 ≤ 336 * N.K * (2 * N.K) ^ 7 := by positivity
  have e5 : 0 ≤ 6 * N.K * (2 * N.K) ^ 6 := by positivity
  have e6 : 0 ≤ 4 * N.K * (2 * N.K) ^ 4 := by positivity
  set L := 1 + |G| * cg N.K 8 + |B| * cg N.K 4 + |C| * cg N.K 12 + 336 * N.K * (2 * N.K) ^ 7 +
    6 * N.K * (2 * N.K) ^ 6 + 4 * N.K * (2 * N.K) ^ 4 with hL
  have hMd : 0 ≤ M * d := mul_nonneg hM0 hd0
  have hBd : 0 ≤ N.ν δB * d := mul_nonneg hB0 hd0
  have hYd : 0 ≤ N.ν Y * d := mul_nonneg hY0 hd0
  have : |G| * cg N.K 8 * M * d + |B| * cg N.K 4 * M * d + |C| * cg N.K 12 * M * d +
      (4 * N.K * (2 * N.K) ^ 4 * N.ν δB * d + 6 * N.K * (2 * N.K) ^ 6 * N.ν Y * d) +
      336 * N.K * (2 * N.K) ^ 7 * M * d ≤ L * (M * d) + L * (N.ν δB * d) + L * (N.ν Y * d) := by
    have h1 : (|G| * cg N.K 8 + |B| * cg N.K 4 + |C| * cg N.K 12 + 336 * N.K * (2 * N.K) ^ 7) *
        (M * d) ≤ L * (M * d) := mul_le_mul_of_nonneg_right (by linarith) hMd
    have h2 : (4 * N.K * (2 * N.K) ^ 4) * (N.ν δB * d) ≤ L * (N.ν δB * d) :=
      mul_le_mul_of_nonneg_right (by linarith) hBd
    have h3 : (6 * N.K * (2 * N.K) ^ 6) * (N.ν Y * d) ≤ L * (N.ν Y * d) :=
      mul_le_mul_of_nonneg_right (by linarith) hYd
    nlinarith
  calc _ ≤ L * (M * d) + L * (N.ν δB * d) + L * (N.ν Y * d) := this
    _ = L * (M + N.ν δB + N.ν Y) * d := by ring

theorem PhiA_zero_le (G B C : ℝ) (δA δB Y : R) :
    N.ν (PhiA G B C δA δB Y 0 0) ≤ N.ν δA + N.ν δB + N.ν Y := by
  rw [PhiA_zero]
  exact (N.add_le _ _).trans (add_le_add (N.add_le _ _) le_rfl)

/-- The source constant. -/
def srcC (K : ℝ) : ℝ := 1 + K * (2 * K) ^ 4 + K * (2 * K) ^ 6

/-- **Source dependence of `Φ`**. -/
theorem PhiA_src_sub_le (G B C : ℝ) (δA δB Y δA' δB' Y' : R) {x D : R} {M : ℝ} (hM : M ≤ 1)
    (hx : N.ν x ≤ M) :
    N.ν (PhiA G B C δA δB Y x D - PhiA G B C δA' δB' Y' x D) ≤
      srcC N.K * (N.ν (δA - δA') + N.ν (δB - δB') + N.ν (Y - Y')) := by
  have hK := N.one_le_K
  rw [PhiA_src_sub_eq]
  have h4 := N.mul_le' (le_refl (N.ν (δB - δB'))) (N.onepow_le hM hx 4)
  have h6 := N.mul_le' (le_refl (N.ν (Y - Y'))) (N.onepow_le hM hx 6)
  have hs := (N.add_le (δA - δA') _).trans
    (add_le_add le_rfl ((N.add_le _ _).trans (add_le_add h4 h6)))
  refine hs.trans ?_
  unfold srcC
  have a0 := N.nonneg (δA - δA'); have b0 := N.nonneg (δB - δB'); have y0 := N.nonneg (Y - Y')
  have k4 : 0 ≤ N.K * (2 * N.K) ^ 4 := by positivity
  have k6 : 0 ≤ N.K * (2 * N.K) ^ 6 := by positivity
  nlinarith [mul_nonneg k4 a0, mul_nonneg k4 y0, mul_nonneg k6 a0, mul_nonneg k6 b0]

end AlgNorm

/-! ### The `ℓ²` model of `H^s(𝕋³)` -/

/-- `ℓ²(ℤ³)`. -/
abbrev L2 := lp (fun _ : Fin 3 → ℤ => ℂ) 2

theorem summable_sq_lp (a : L2) : Summable fun n => ‖a n‖ ^ 2 := by
  have h := (memℓp_gen_iff (p := 2) (by norm_num)).1 (lp.memℓp a)
  simpa [Real.rpow_two] using h

/-- The weighted Fourier series `a ↦ Σ_n a(n) W_s(n)^{-1/2} e_n`, an isometry of `ℓ²(ℤ³)` onto the
continuous `H^s` functions (`s ≥ 2`). -/
def ofSeq (s : ℕ) (a : L2) : CT :=
  TorusSobolev.fourierSum fun n => a n / ((Real.sqrt (trigWeight s n) : ℝ) : ℂ)

theorem summable_ofSeq_coeff {s : ℕ} (hs : 2 ≤ s) (a : L2) :
    Summable fun n => ‖a n / ((Real.sqrt (trigWeight s n) : ℝ) : ℂ)‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (((summable_sq_lp a).add (summable_inv_trigWeight s hs)).mul_left (1 / 2))
  have hW := trigWeight_pos s n
  have hsp := Real.sqrt_pos.mpr hW
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  set t := Real.sqrt (trigWeight s n) with ht
  have hW' : (trigWeight s n)⁻¹ = (t⁻¹) ^ 2 := by rw [inv_pow, ht, Real.sq_sqrt hW.le]
  rw [hW', div_eq_mul_inv]
  nlinarith [sq_nonneg (‖a n‖ - t⁻¹)]

theorem mFourierCoeff_ofSeq {s : ℕ} (hs : 2 ≤ s) (a : L2) (n : Fin 3 → ℤ) :
    mFourierCoeff ⇑(ofSeq s a) n = a n / ((Real.sqrt (trigWeight s n) : ℝ) : ℂ) :=
  TorusSobolev.mFourierCoeff_fourierSum (summable_ofSeq_coeff hs a) n

theorem weight_mul_ofSeq_coeff {s : ℕ} (hs : 2 ≤ s) (a : L2) (n : Fin 3 → ℤ) :
    trigWeight s n * ‖mFourierCoeff ⇑(ofSeq s a) n‖ ^ 2 = ‖a n‖ ^ 2 := by
  have hW := trigWeight_pos s n
  rw [mFourierCoeff_ofSeq hs, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt hW.le]
  field_simp

theorem memH_ofSeq {s : ℕ} (hs : 2 ≤ s) (a : L2) : MemH s ⇑(ofSeq s a) := by
  unfold MemH
  simp only [weight_mul_ofSeq_coeff hs]
  exact summable_sq_lp a

theorem wseq_ofSeq {s : ℕ} (hs : 2 ≤ s) (a : L2) (h) : wseq s (ofSeq s a) h = a := by
  ext n
  rw [wseq_apply, mFourierCoeff_ofSeq hs]
  have hsp := Real.sqrt_pos.mpr (trigWeight_pos s n)
  have : ((Real.sqrt (trigWeight s n) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsp.ne'
  field_simp

theorem sn_eq_norm_wseq (s : ℕ) (F : CT) (h) : sn s ⇑F = ‖wseq s F h‖ := by
  rw [norm_wseq]; rfl

/-- `ofSeq` is an isometry: `‖ofSeq a‖_{H^s} = ‖a‖_{ℓ²}`. -/
theorem sn_ofSeq {s : ℕ} (hs : 2 ≤ s) (a : L2) : sn s ⇑(ofSeq s a) = ‖a‖ := by
  rw [sn_eq_norm_wseq s _ (memH_ofSeq hs a), wseq_ofSeq hs]

theorem ofSeq_wseq {s : ℕ} (hs : 2 ≤ s) (F : CT) (hF : MemH s ⇑F) :
    ofSeq s (wseq s F hF) = F := by
  refine coeff_ext fun n => ?_
  rw [mFourierCoeff_ofSeq hs, wseq_apply]
  have hsp := Real.sqrt_pos.mpr (trigWeight_pos s n)
  have : ((Real.sqrt (trigWeight s n) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsp.ne'
  field_simp

theorem ofSeq_sub {s : ℕ} (hs : 2 ≤ s) (a b : L2) : ofSeq s (a - b) = ofSeq s a - ofSeq s b := by
  refine coeff_ext fun n => ?_
  rw [mFourierCoeff_sub', mFourierCoeff_ofSeq hs, mFourierCoeff_ofSeq hs, mFourierCoeff_ofSeq hs]
  simp only [lp.coeFn_sub, Pi.sub_apply]
  ring

theorem sn_ofSeq_sub {s : ℕ} (hs : 2 ≤ s) (a b : L2) :
    sn s ⇑(ofSeq s a - ofSeq s b) = ‖a - b‖ := by
  rw [← ofSeq_sub hs, sn_ofSeq hs]

theorem wseq_sub' (s : ℕ) (F G : CT) (hF hG hFG) :
    wseq s F hF - wseq s G hG = wseq s (F - G) hFG := by
  ext n
  simp only [lp.coeFn_sub, Pi.sub_apply, wseq_apply, mFourierCoeff_sub']
  ring

/-- The weighted coefficient sequence of an `H^s` function (`0` outside `H^s`). -/
def toSeq (s : ℕ) (F : CT) : L2 := by
  classical exact if h : MemH s ⇑F then wseq s F h else 0

theorem toSeq_eq {s : ℕ} {F : CT} (h : MemH s ⇑F) : toSeq s F = wseq s F h := by
  unfold toSeq; simp [h]

theorem norm_toSeq_sub {s : ℕ} {F G : CT} (hF : MemH s ⇑F) (hG : MemH s ⇑G) :
    ‖toSeq s F - toSeq s G‖ = sn s ⇑(F - G) := by
  rw [toSeq_eq hF, toSeq_eq hG, wseq_sub' s F G hF hG (memH_sub hF hG),
    ← sn_eq_norm_wseq]

theorem norm_toSeq {s : ℕ} {F : CT} (hF : MemH s ⇑F) : ‖toSeq s F‖ = sn s ⇑F := by
  rw [toSeq_eq hF, ← sn_eq_norm_wseq]

theorem ofSeq_toSeq {s : ℕ} (hs : 2 ≤ s) {F : CT} (hF : MemH s ⇑F) : ofSeq s (toSeq s F) = F := by
  rw [toSeq_eq hF, ofSeq_wseq hs]

theorem toSeq_ofSeq {s : ℕ} (hs : 2 ≤ s) (a : L2) : toSeq s (ofSeq s a) = a := by
  rw [toSeq_eq (memH_ofSeq hs a), wseq_ofSeq hs]

/-! ### Constants and the Sobolev algebra `H^r ∩ C⁰`, `r ≥ 2` -/

theorem algebraMap_eq_const (c : ℂ) :
    algebraMap ℂ CT c = ContinuousMap.const (UnitAddTorus (Fin 3)) c := by
  ext x; simp

theorem memH_const (r : ℕ) (c : ℂ) :
    MemH r ⇑(ContinuousMap.const (UnitAddTorus (Fin 3)) c) := by
  unfold MemH
  refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
  rw [mFourierCoeff_const]; simp_all

theorem trigSobSq_const (r : ℕ) (c : ℂ) :
    trigSobSq r ⇑(ContinuousMap.const (UnitAddTorus (Fin 3)) c) = ‖c‖ ^ 2 := by
  unfold trigSobSq
  rw [tsum_eq_single 0 fun n hn => by rw [mFourierCoeff_const]; simp [hn]]
  rw [mFourierCoeff_const]; simp [trigWeight_zero_freq]

theorem sn_const (r : ℕ) (c : ℂ) : sn r ⇑(ContinuousMap.const (UnitAddTorus (Fin 3)) c) = ‖c‖ := by
  rw [sn, trigSobSq_const, Real.sqrt_sq (norm_nonneg _)]

/-- The subalgebra `H^r ∩ C⁰` of `C(𝕋³, ℂ)`, `r ≥ 2`. -/
def sobAlg (r : ℕ) (hr : 2 ≤ r) : Subalgebra ℂ CT where
  carrier := {F | MemH r ⇑F}
  mul_mem' := fun {F G} hF hG => ((memH_mul r hr).choose_spec.2 F G hF hG).1
  add_mem' := fun hF hG => memH_add hF hG
  algebraMap_mem' := fun c => by
    show MemH r ⇑(algebraMap ℂ CT c)
    rw [algebraMap_eq_const]; exact memH_const r c

theorem mem_sobAlg {r : ℕ} {hr : 2 ≤ r} {F : CT} : F ∈ sobAlg r hr ↔ MemH r ⇑F := Iff.rfl

/-- The algebra constant `K_r ≥ 1` of `H^r(𝕋³)`. -/
def algK (r : ℕ) (hr : 2 ≤ r) : ℝ := max 1 (memH_mul r hr).choose

theorem one_le_algK (r : ℕ) (hr : 2 ≤ r) : 1 ≤ algK r hr := le_max_left _ _

theorem sn_mul_le {r : ℕ} (hr : 2 ≤ r) {F G : CT} (hF : MemH r ⇑F) (hG : MemH r ⇑G) :
    sn r ⇑(F * G) ≤ algK r hr * sn r ⇑F * sn r ⇑G := by
  refine ((memH_mul r hr).choose_spec.2 F G hF hG).2.trans ?_
  have := sn_nonneg r ⇑F; have := sn_nonneg r ⇑G
  gcongr
  exact le_max_right _ _

/-- The `H^r` norm as an `AlgNorm` on `H^r ∩ C⁰`. -/
def sobNorm (r : ℕ) (hr : 2 ≤ r) : AlgNorm (sobAlg r hr) where
  ν x := sn r ⇑(x : CT)
  K := algK r hr
  one_le_K := one_le_algK r hr
  nonneg x := sn_nonneg _ _
  add_le x y := by
    rw [Subalgebra.coe_add]; exact sn_add_le' x.2 y.2
  smul_eq c x := by
    rw [Subalgebra.coe_smul]; exact sn_smul r c _
  mul_le x y := by
    rw [Subalgebra.coe_mul]; exact sn_mul_le hr x.2 y.2
  one_le := by
    rw [Subalgebra.coe_one]
    have : (1 : CT) = ContinuousMap.const _ 1 := rfl
    rw [this, sn_const]; simp

/-! ### Fourier multipliers: the Laplacian and `L_*⁻¹` -/

/-- The Fourier Laplacian `Δ F = Σ_n (-|2πn|²) F̂(n) e_n`. -/
def lap (F : CT) : CT := fmul (fun n => -((lapSym n : ℝ) : ℂ)) F

theorem summable_lap {r : ℕ} (hr : 2 ≤ r) {u : CT} (hu : MemH (r + 2) ⇑u) :
    Summable fun n => ‖-((lapSym n : ℝ) : ℂ) * mFourierCoeff ⇑u n‖ := by
  refine summable_norm_of_trigWeight hr (Summable.of_nonneg_of_le
    (fun n => mul_nonneg (trigWeight_nonneg _ _) (sq_nonneg _)) (fun n => ?_) (hu.mul_left 9))
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (lapSym_nonneg n),
    mul_pow, ← mul_assoc, mul_comm (trigWeight r n), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (lapSym_sq_mul_trigWeight_le r n) (sq_nonneg _)

theorem mFourierCoeff_lap {r : ℕ} (hr : 2 ≤ r) {u : CT} (hu : MemH (r + 2) ⇑u) (n : Fin 3 → ℤ) :
    mFourierCoeff ⇑(lap u) n = -((lapSym n : ℝ) : ℂ) * mFourierCoeff ⇑u n :=
  mFourierCoeff_fmul (summable_lap hr hu) n

/-- `Δ : H^{r+2} → H^r` with `‖Δu‖_{H^r} ≤ 3‖u‖_{H^{r+2}}`. -/
theorem lap_spec {r : ℕ} (hr : 2 ≤ r) {u : CT} (hu : MemH (r + 2) ⇑u) :
    MemH r ⇑(lap u) ∧ sn r ⇑(lap u) ≤ 3 * sn (r + 2) ⇑u := by
  have hpt : ∀ n, trigWeight r n * ‖mFourierCoeff ⇑(lap u) n‖ ^ 2 ≤
      9 * (trigWeight (r + 2) n * ‖mFourierCoeff ⇑u n‖ ^ 2) := by
    intro n
    rw [mFourierCoeff_lap hr hu, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (lapSym_nonneg n), mul_pow, ← mul_assoc, mul_comm (trigWeight r n),
      ← mul_assoc]
    refine (mul_le_mul_of_nonneg_right (lapSym_sq_mul_trigWeight_le r n) (sq_nonneg _)).trans
      (le_of_eq (by ring))
  have hs : MemH r ⇑(lap u) := Summable.of_nonneg_of_le
    (fun n => mul_nonneg (trigWeight_nonneg _ _) (sq_nonneg _)) hpt (hu.mul_left 9)
  refine ⟨hs, ?_⟩
  unfold sn
  rw [show (3 : ℝ) = Real.sqrt 9 by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
    ← Real.sqrt_mul (by norm_num)]
  refine Real.sqrt_le_sqrt ?_
  unfold trigSobSq
  rw [← tsum_mul_left]
  exact hs.tsum_le_tsum hpt (hu.mul_left 9)

/-- The symbol `λ(n) = 8|2πn|² + μ` of `L_* = -8Δ + μ`. -/
def lamSym (μ : ℝ) (n : Fin 3 → ℤ) : ℝ := 8 * lapSym n + μ

theorem lamSym_pos {μ : ℝ} (hμ : 0 < μ) (n : Fin 3 → ℤ) : 0 < lamSym μ n := by
  unfold lamSym; have := lapSym_nonneg n; linarith

theorem lamSym_ge (μ : ℝ) (n : Fin 3 → ℤ) :
    min 8 μ * (1 + lapSym n) ≤ lamSym μ n := by
  unfold lamSym
  have h1 : min 8 μ ≤ 8 := min_le_left _ _
  have h2 : min 8 μ ≤ μ := min_le_right _ _
  have := lapSym_nonneg n
  nlinarith

/-- The inverse `L_*⁻¹ f = Σ_n λ(n)⁻¹ f̂(n) e_n` (`λ(n) ≥ μ > 0`, including the zero mode). -/
def Linv (μ : ℝ) (F : CT) : CT := fmul (fun n => (((lamSym μ n)⁻¹ : ℝ) : ℂ)) F

theorem summable_Linv {r : ℕ} (hr : 2 ≤ r) {μ : ℝ} (hμ : 0 < μ) {f : CT} (hf : MemH r ⇑f) :
    Summable fun n => ‖(((lamSym μ n)⁻¹ : ℝ) : ℂ) * mFourierCoeff ⇑f n‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((summable_norm_of_trigWeight hr hf).mul_left μ⁻¹)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (lamSym_pos hμ n).le)]
  refine mul_le_mul_of_nonneg_right (inv_anti₀ hμ ?_) (norm_nonneg _)
  unfold lamSym; have := lapSym_nonneg n; linarith

theorem mFourierCoeff_Linv {r : ℕ} (hr : 2 ≤ r) {μ : ℝ} (hμ : 0 < μ) {f : CT} (hf : MemH r ⇑f)
    (n : Fin 3 → ℤ) :
    mFourierCoeff ⇑(Linv μ f) n = (((lamSym μ n)⁻¹ : ℝ) : ℂ) * mFourierCoeff ⇑f n :=
  mFourierCoeff_fmul (summable_Linv hr hμ hf) n

/-- **`L_*⁻¹ : H^r → H^{r+2}`** with `‖L_*⁻¹ f‖_{H^{r+2}} ≤ min(8, μ)⁻¹ ‖f‖_{H^r}`. -/
theorem Linv_spec {r : ℕ} (hr : 2 ≤ r) {μ : ℝ} (hμ : 0 < μ) {f : CT} (hf : MemH r ⇑f) :
    MemH (r + 2) ⇑(Linv μ f) ∧ sn (r + 2) ⇑(Linv μ f) ≤ (min 8 μ)⁻¹ * sn r ⇑f := by
  have hm : 0 < min 8 μ := lt_min (by norm_num) hμ
  have hpt : ∀ n, trigWeight (r + 2) n * ‖mFourierCoeff ⇑(Linv μ f) n‖ ^ 2 ≤
      ((min 8 μ) ^ 2)⁻¹ * (trigWeight r n * ‖mFourierCoeff ⇑f n‖ ^ 2) := by
    intro n
    have hl := lamSym_pos hμ n
    have hge := lamSym_ge μ n
    have h1 := trigWeight_add_two_le r n
    have hS := lapSym_nonneg n
    rw [mFourierCoeff_Linv hr hμ hf, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hl.le), mul_pow]
    have hW := trigWeight_nonneg r n
    have hc := sq_nonneg ‖mFourierCoeff ⇑f n‖
    have key : trigWeight (r + 2) n * ((lamSym μ n)⁻¹) ^ 2 ≤ ((min 8 μ) ^ 2)⁻¹ * trigWeight r n := by
      rw [inv_pow, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
      calc trigWeight (r + 2) n ≤ (1 + lapSym n) ^ 2 * trigWeight r n := h1
        _ = ((min 8 μ) ^ 2)⁻¹ * trigWeight r n * (min 8 μ * (1 + lapSym n)) ^ 2 := by
            field_simp
        _ ≤ ((min 8 μ) ^ 2)⁻¹ * trigWeight r n * lamSym μ n ^ 2 := by
            gcongr
    calc trigWeight (r + 2) n * ((lamSym μ n)⁻¹ ^ 2 * ‖mFourierCoeff ⇑f n‖ ^ 2)
        = (trigWeight (r + 2) n * ((lamSym μ n)⁻¹) ^ 2) * ‖mFourierCoeff ⇑f n‖ ^ 2 := by ring
      _ ≤ (((min 8 μ) ^ 2)⁻¹ * trigWeight r n) * ‖mFourierCoeff ⇑f n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right key hc
      _ = _ := by ring
  have hs : MemH (r + 2) ⇑(Linv μ f) := Summable.of_nonneg_of_le
    (fun n => mul_nonneg (trigWeight_nonneg _ _) (sq_nonneg _)) hpt (hf.mul_left _)
  refine ⟨hs, ?_⟩
  unfold sn
  rw [show (min 8 μ)⁻¹ = Real.sqrt (((min 8 μ) ^ 2)⁻¹) by
    rw [Real.sqrt_inv, Real.sqrt_sq hm.le], ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  unfold trigSobSq
  rw [← tsum_mul_left]
  exact hs.tsum_le_tsum hpt (hf.mul_left _)

/-- `L_*` applied to `L_*⁻¹ f` returns `f`: `-8Δ(L_*⁻¹f) + μ L_*⁻¹f = f`. -/
theorem L_Linv {r : ℕ} (hr : 2 ≤ r) {μ : ℝ} (hμ : 0 < μ) {f : CT} (hf : MemH r ⇑f) :
    (-8 : ℂ) • lap (Linv μ f) + (μ : ℂ) • Linv μ f = f := by
  have hL := (Linv_spec hr hμ hf).1
  refine coeff_ext fun n => ?_
  rw [Sampling.mFourierCoeff_add, mFourierCoeff_smul', mFourierCoeff_smul',
    mFourierCoeff_lap hr hL, mFourierCoeff_Linv hr hμ hf, smul_eq_mul, smul_eq_mul]
  have hl := (lamSym_pos hμ n).ne'
  have : ((lamSym μ n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hl
  unfold lamSym at this ⊢
  push_cast at this ⊢
  field_simp

/-- `L_*⁻¹` applied to `L_* u` returns `u` for `u ∈ H^{r+2}`. -/
theorem Linv_L {r : ℕ} (hr : 2 ≤ r) {μ : ℝ} (hμ : 0 < μ) {u : CT} (hu : MemH (r + 2) ⇑u)
    (hLu : MemH r ⇑((-8 : ℂ) • lap u + (μ : ℂ) • u)) :
    Linv μ ((-8 : ℂ) • lap u + (μ : ℂ) • u) = u := by
  refine coeff_ext fun n => ?_
  rw [mFourierCoeff_Linv hr hμ hLu, Sampling.mFourierCoeff_add, mFourierCoeff_smul',
    mFourierCoeff_smul', mFourierCoeff_lap hr hu, smul_eq_mul, smul_eq_mul]
  have hl := (lamSym_pos hμ n).ne'
  have : ((lamSym μ n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hl
  unfold lamSym at this ⊢
  push_cast at this ⊢
  field_simp

/-! ### Complex conjugation -/

/-- The pointwise complex conjugate of a continuous function on `𝕋³`. -/
def conjCT (F : CT) : CT := ⟨fun y => conj (F y), Complex.continuous_conj.comp F.continuous⟩

@[simp] theorem conjCT_apply (F : CT) (y : UnitAddTorus (Fin 3)) : conjCT F y = conj (F y) := rfl

theorem mFourierCoeff_conjCT (F : CT) (n : Fin 3 → ℤ) :
    mFourierCoeff ⇑(conjCT F) n = conj (mFourierCoeff ⇑F (-n)) := by
  unfold mFourierCoeff
  rw [← integral_conj]
  congr 1
  funext y
  simp only [conjCT, ContinuousMap.coe_mk, smul_eq_mul, map_mul, neg_neg, mFourier_neg]

theorem trigWeight_neg' (r : ℕ) (n : Fin 3 → ℤ) : trigWeight r (-n) = trigWeight r n := by
  simp [trigWeight, tsymSq]

theorem memH_conjCT {r : ℕ} {F : CT} (hF : MemH r ⇑F) :
    MemH r ⇑(conjCT F) ∧ sn r ⇑(conjCT F) = sn r ⇑F := by
  have e : ∀ n, trigWeight r n * ‖mFourierCoeff ⇑(conjCT F) n‖ ^ 2 =
      (fun m => trigWeight r m * ‖mFourierCoeff ⇑F m‖ ^ 2) (Equiv.neg (Fin 3 → ℤ) n) := by
    intro n
    simp [mFourierCoeff_conjCT, trigWeight_neg']
  have hs : MemH r ⇑(conjCT F) := by
    unfold MemH; simp only [e]; exact (Equiv.neg (Fin 3 → ℤ)).summable_iff.mpr hF
  refine ⟨hs, ?_⟩
  unfold sn trigSobSq
  simp only [e]
  rw [(Equiv.neg (Fin 3 → ℤ)).tsum_eq (fun m => trigWeight r m * ‖mFourierCoeff ⇑F m‖ ^ 2)]

theorem conjCT_conjCT (F : CT) : conjCT (conjCT F) = F := by ext y; simp

theorem conjCT_add (F G : CT) : conjCT (F + G) = conjCT F + conjCT G := by ext y; simp

theorem conjCT_sub (F G : CT) : conjCT (F - G) = conjCT F - conjCT G := by ext y; simp

theorem conjCT_mul (F G : CT) : conjCT (F * G) = conjCT F * conjCT G := by ext y; simp

theorem conjCT_pow (F : CT) (k : ℕ) : conjCT (F ^ k) = conjCT F ^ k := by ext y; simp

theorem conjCT_smul_real (c : ℝ) (F : CT) : conjCT ((c : ℂ) • F) = (c : ℂ) • conjCT F := by
  ext y; simp

theorem conjCT_one : conjCT 1 = 1 := by ext y; simp

theorem conjCT_nsmul (k : ℕ) (F : CT) : conjCT (k • F) = k • conjCT F := by ext y; simp

/-- Conjugation commutes with a real even Fourier multiplier. -/
theorem conjCT_fmul {m : (Fin 3 → ℤ) → ℝ} (hm : ∀ n, m (-n) = m n) {F : CT}
    (h : Summable fun n => ‖((m n : ℝ) : ℂ) * mFourierCoeff ⇑F n‖) :
    conjCT (fmul (fun n => ((m n : ℝ) : ℂ)) F) = fmul (fun n => ((m n : ℝ) : ℂ)) (conjCT F) := by
  have h2 : Summable fun n => ‖((m n : ℝ) : ℂ) * mFourierCoeff ⇑(conjCT F) n‖ := by
    have := (Equiv.neg (Fin 3 → ℤ)).summable_iff.mpr h
    refine this.congr fun n => ?_
    simp [mFourierCoeff_conjCT, hm]
  refine coeff_ext fun n => ?_
  rw [mFourierCoeff_conjCT, mFourierCoeff_fmul h, mFourierCoeff_fmul h2, mFourierCoeff_conjCT,
    map_mul, Complex.conj_ofReal, hm]

theorem conjCT_lap {r : ℕ} (hr : 2 ≤ r) {u : CT} (hu : MemH (r + 2) ⇑u) :
    conjCT (lap u) = lap (conjCT u) := by
  have e : (fun n : Fin 3 → ℤ => -((lapSym n : ℝ) : ℂ)) = fun n => ((-lapSym n : ℝ) : ℂ) := by
    funext n; push_cast; ring
  unfold lap
  rw [e]
  refine conjCT_fmul (m := fun n => -lapSym n) (fun n => by simp [lapSym_neg]) ?_
  simpa [e] using summable_lap hr hu

theorem conjCT_Linv {r : ℕ} (hr : 2 ≤ r) {μ : ℝ} (hμ : 0 < μ) {f : CT} (hf : MemH r ⇑f) :
    conjCT (Linv μ f) = Linv μ (conjCT f) :=
  conjCT_fmul (m := fun n => (lamSym μ n)⁻¹) (fun n => by simp [lamSym, lapSym_neg])
    (summable_Linv hr hμ hf)

/-! ### Linearity of the multipliers -/

theorem lap_sub {r : ℕ} (hr : 2 ≤ r) {u v : CT} (hu : MemH (r + 2) ⇑u) (hv : MemH (r + 2) ⇑v) :
    lap u - lap v = lap (u - v) := by
  refine coeff_ext fun n => ?_
  rw [mFourierCoeff_sub', mFourierCoeff_lap hr hu, mFourierCoeff_lap hr hv,
    mFourierCoeff_lap hr (memH_sub hu hv), mFourierCoeff_sub']
  ring

theorem lap_add {r : ℕ} (hr : 2 ≤ r) {u v : CT} (hu : MemH (r + 2) ⇑u) (hv : MemH (r + 2) ⇑v) :
    lap (u + v) = lap u + lap v := by
  refine coeff_ext fun n => ?_
  rw [Sampling.mFourierCoeff_add, mFourierCoeff_lap hr hu, mFourierCoeff_lap hr hv,
    mFourierCoeff_lap hr (memH_add hu hv), Sampling.mFourierCoeff_add]
  ring

theorem lap_const {r : ℕ} (hr : 2 ≤ r) (c : ℂ) :
    lap (ContinuousMap.const (UnitAddTorus (Fin 3)) c) = 0 := by
  refine coeff_ext fun n => ?_
  rw [mFourierCoeff_lap hr (memH_const _ c), mFourierCoeff_const, ContinuousMap.coe_zero,
    mFourierCoeff_zero']
  split_ifs with h
  · subst h; simp [lapSym]
  · simp

theorem lap_zero {r : ℕ} (hr : 2 ≤ r) : lap (0 : CT) = 0 := by
  have := lap_const hr 0
  rwa [show ContinuousMap.const (UnitAddTorus (Fin 3)) (0 : ℂ) = 0 from rfl] at this

theorem Linv_sub {r : ℕ} (hr : 2 ≤ r) {μ : ℝ} (hμ : 0 < μ) {f g : CT} (hf : MemH r ⇑f)
    (hg : MemH r ⇑g) : Linv μ f - Linv μ g = Linv μ (f - g) := by
  refine coeff_ext fun n => ?_
  rw [mFourierCoeff_sub', mFourierCoeff_Linv hr hμ hf, mFourierCoeff_Linv hr hμ hg,
    mFourierCoeff_Linv hr hμ (memH_sub hf hg), mFourierCoeff_sub']
  ring

theorem ofSeq_zero {s : ℕ} (hs : 2 ≤ s) : ofSeq s 0 = 0 := by
  have := ofSeq_sub hs 0 0
  rwa [sub_zero, sub_self] at this

/-! ### The Lichnerowicz map -/

/-- The data of the scalar conformal equation: background coefficients `A, G, B`, the constant
`C` fixed by the background constraint and `μ`, plus the source coefficients `δA, δB, Y`. -/
structure LichData where
  /-- `A_*⁰` -/
  A : ℝ
  /-- `G_*⁰` -/
  G : ℝ
  /-- `B_*⁰` -/
  B : ℝ
  /-- `C_*⁰` -/
  C : ℝ
  /-- `μ_*` -/
  μ : ℝ
  /-- the background constraint fixing `C_*⁰` (the unperturbed equation holds at `w = 1`) -/
  hC : C = A + G + B
  /-- `μ_* = 12 A_*⁰ + 4 G_*⁰ + 8 B_*⁰` (eq:generated-Lstar) -/
  hμ : μ = 12 * A + 4 * G + 8 * B
  /-- `μ_* > 0` -/
  μ_pos : 0 < μ

/-- The residual `-8 ΔW - (A + a) W⁻⁷ - G W - (B + b) W⁻³ - y W⁻¹ + C W⁵` of the conformal
Hamiltonian equation at a point (`lapW` standing for `ΔW`). -/
def hamRes (D : LichData) (a b y W lapW : ℂ) : ℂ :=
  -8 * lapW - ((D.A : ℂ) + a) * W⁻¹ ^ 7 - (D.G : ℂ) * W - ((D.B : ℂ) + b) * W⁻¹ ^ 3 - y * W⁻¹ +
    (D.C : ℂ) * W ^ 5

/-- **The conformal Hamiltonian equation** `eq:generated-Hamiltonian` for a continuous conformal
factor `w` on `𝕋³` (pointwise, `Δ` the Fourier Laplacian, `𝖠 = A + δA`, `𝖡 = B + δB`):
`-8Δw - 𝖠 w⁻⁷ - G w - 𝖡 w⁻³ - 𝖸 w⁻¹ + C w⁵ = 0`. -/
def HamiltonianEq (D : LichData) (δA δB Y w : CT) : Prop :=
  ∀ x, hamRes D (δA x) (δB x) (Y x) (w x) (lap w x) = 0

/-- The pointwise algebra: `w⁷ × (Hamiltonian residual) = L_* u - Φ(u)` (`w = 1 + u`). -/
theorem hamRes_mul (D : LichData) {x Dx a b y : ℂ} (hw : 1 + x ≠ 0) :
    hamRes D a b y (1 + x) Dx * (1 + x) ^ 7 =
      (-8 * Dx + (D.μ : ℂ) * x) - AlgNorm.PhiA D.G D.B D.C a b y x Dx := by
  have hC : (D.C : ℂ) = D.A + D.G + D.B := by exact_mod_cast D.hC
  have hμ : (D.μ : ℂ) = 12 * D.A + 4 * D.G + 8 * D.B := by exact_mod_cast D.hμ
  simp only [hamRes, AlgNorm.PhiA, AlgNorm.gpow, AlgNorm.fpow, smul_eq_mul, nsmul_eq_mul]
  rw [hC, hμ]
  field_simp
  push_cast
  ring

theorem hamRes_eq_zero_iff (D : LichData) {x Dx a b y : ℂ} (hw : 1 + x ≠ 0) :
    hamRes D a b y (1 + x) Dx = 0 ↔
      -8 * Dx + (D.μ : ℂ) * x = AlgNorm.PhiA D.G D.B D.C a b y x Dx := by
  have h := hamRes_mul D (Dx := Dx) (a := a) (b := b) (y := y) hw
  constructor
  · intro h0
    rw [h0, zero_mul] at h
    exact (sub_eq_zero.mp h.symm)
  · intro h1
    rw [h1, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero _ hw)

/-- **Banach contraction in `H^s(𝕋³) ∩ C⁰`** (`s ≥ 2`), through the isometry with `ℓ²(ℤ³)`:
a map of continuous functions preserving `H^s`, mapping the `H^s` ball of radius `M` into itself
and `κ`-contracting there (`κ < 1`) has a unique fixed point in the ball, with
`‖u*‖_{H^s} ≤ ‖T 0‖_{H^s} / (1 - κ)`. -/
theorem exists_fixedPoint_sn {s : ℕ} (hs : 2 ≤ s) (T : CT → CT)
    (hT : ∀ u : CT, MemH s ⇑u → MemH s ⇑(T u)) {M κ : ℝ} (hM : 0 ≤ M) (hκ0 : 0 ≤ κ)
    (hκ1 : κ < 1) (hmaps : ∀ u : CT, MemH s ⇑u → sn s ⇑u ≤ M → sn s ⇑(T u) ≤ M)
    (hlip : ∀ u v : CT, MemH s ⇑u → MemH s ⇑v → sn s ⇑u ≤ M → sn s ⇑v ≤ M →
      sn s ⇑(T u - T v) ≤ κ * sn s ⇑(u - v)) :
    ∃ u : CT, MemH s ⇑u ∧ sn s ⇑u ≤ M ∧ T u = u ∧ sn s ⇑u ≤ sn s ⇑(T 0) / (1 - κ) ∧
      ∀ v : CT, MemH s ⇑v → sn s ⇑v ≤ M → T v = v → v = u := by
  set Tq : L2 → L2 := fun a => toSeq s (T (ofSeq s a)) with hTq
  have hmem : ∀ a, MemH s ⇑(T (ofSeq s a)) := fun a => hT _ (memH_ofSeq hs a)
  have hmaps' : ∀ a : L2, ‖a‖ ≤ M → ‖Tq a‖ ≤ M := by
    intro a ha
    rw [hTq, norm_toSeq (hmem a)]
    exact hmaps _ (memH_ofSeq hs a) (by rw [sn_ofSeq hs]; exact ha)
  have hlip' : ∀ a b : L2, ‖a‖ ≤ M → ‖b‖ ≤ M → ‖Tq a - Tq b‖ ≤ κ * ‖a - b‖ := by
    intro a b ha hb
    rw [hTq, norm_toSeq_sub (hmem a) (hmem b), ← sn_ofSeq_sub hs]
    exact hlip _ _ (memH_ofSeq hs a) (memH_ofSeq hs b) (by rw [sn_ofSeq hs]; exact ha)
      (by rw [sn_ofSeq hs]; exact hb)
  obtain ⟨a, ha, hfix, huniq⟩ := exists_unique_fixedPoint_ball hM hκ0 hκ1 hmaps' hlip'
  have hTu : T (ofSeq s a) = ofSeq s a := by
    have := congrArg (ofSeq s) hfix
    rw [hTq] at this
    simp only at this
    rwa [ofSeq_toSeq hs (hmem a)] at this
  refine ⟨ofSeq s a, memH_ofSeq hs a, by rw [sn_ofSeq hs]; exact ha, hTu, ?_, ?_⟩
  · have h0 : ‖Tq 0‖ = sn s ⇑(T 0) := by
      rw [hTq]; simp only; rw [ofSeq_zero hs, norm_toSeq (hT 0 (memH_zero s))]
    have hb := norm_fixedPoint_le hκ1 hfix (by
      rw [sub_zero]; exact hlip' a 0 ha (by simpa using hM) |>.trans (by rw [sub_zero]))
    rw [sn_ofSeq hs, ← h0]; exact hb
  · intro v hv hvM hTv
    have hb : Tq (toSeq s v) = toSeq s v := by
      rw [hTq]; simp only; rw [ofSeq_toSeq hs hv, hTv]
    have := huniq (toSeq s v) (by rw [norm_toSeq hv]; exact hvM) hb
    rw [← ofSeq_toSeq hs hv, this]

/-- Perturbation of fixed points in `H^s`: if `T u = u`, `T' u' = u'` and `T` is a
`κ`-contraction between them, `‖u - u'‖_{H^s} ≤ ‖T u' - T' u'‖_{H^s} / (1 - κ)`. -/
theorem sn_sub_fixedPoint_le {s : ℕ} {T T' : CT → CT} {u u' : CT} {κ : ℝ} (hκ1 : κ < 1)
    (hu : T u = u) (hu' : T' u' = u') (hmu : MemH s ⇑(T u - T u'))
    (hmu' : MemH s ⇑(T u' - T' u')) (hlip : sn s ⇑(T u - T u') ≤ κ * sn s ⇑(u - u')) :
    sn s ⇑(u - u') ≤ sn s ⇑(T u' - T' u') / (1 - κ) := by
  rw [le_div_iff₀ (by linarith)]
  have h1 : sn s ⇑(u - u') ≤ sn s ⇑(T u - T u') + sn s ⇑(T u' - T' u') := by
    have e : u - u' = (T u - T u') + (T u' - T' u') := by rw [hu, hu']; abel
    rw [e]; exact sn_add_le' hmu hmu'
  nlinarith

theorem conj_PhiA (G B C : ℝ) (a b y x D : ℂ) :
    conj (AlgNorm.PhiA G B C a b y x D) =
      AlgNorm.PhiA G B C (conj a) (conj b) (conj y) (conj x) (conj D) := by
  simp [AlgNorm.PhiA, AlgNorm.gpow, AlgNorm.fpow, map_add, map_sub, map_mul, map_pow,
    Complex.conj_ofReal, map_ofNat]

variable (D : LichData)

/-- The right-hand side `Φ(u)` on `C(𝕋³, ℂ)`. -/
def PhiF (δA δB Y u : CT) : CT := AlgNorm.PhiA D.G D.B D.C δA δB Y u (lap u)

/-- **The Lichnerowicz fixed-point map** `𝒯(u) = L_*⁻¹ Φ(u)`. -/
def Tmap (δA δB Y u : CT) : CT := Linv D.μ (PhiF D δA δB Y u)

theorem PhiF_apply (δA δB Y u : CT) (x : UnitAddTorus (Fin 3)) :
    PhiF D δA δB Y u x = AlgNorm.PhiA D.G D.B D.C (δA x) (δB x) (Y x) (u x) (lap u x) :=
  AlgNorm.map_PhiA (ContinuousMap.evalAlgHom ℂ ℂ x) D.G D.B D.C δA δB Y u (lap u)

/-- The constant `min(8, μ)⁻¹` of `L_*⁻¹ : H^r → H^{r+2}`. -/
def cL : ℝ := (min 8 D.μ)⁻¹

theorem cL_pos : 0 < cL D := inv_pos.mpr (lt_min (by norm_num) D.μ_pos)

variable (r : ℕ) (hr : 2 ≤ r)
include hr

/-- `Φ(u)` as an element of the algebra `H^r ∩ C⁰`. -/
def PhiS {δA δB Y u : CT} (hA : MemH r ⇑δA) (hB : MemH r ⇑δB) (hY : MemH r ⇑Y)
    (hu : MemH (r + 2) ⇑u) : sobAlg r hr :=
  AlgNorm.PhiA D.G D.B D.C (⟨δA, hA⟩ : sobAlg r hr) ⟨δB, hB⟩ ⟨Y, hY⟩
    ⟨u, memH_mono (by omega) hu⟩ ⟨lap u, (lap_spec hr hu).1⟩

theorem coe_PhiS {δA δB Y u : CT} (hA : MemH r ⇑δA) (hB : MemH r ⇑δB) (hY : MemH r ⇑Y)
    (hu : MemH (r + 2) ⇑u) : ((PhiS D r hr hA hB hY hu : sobAlg r hr) : CT) = PhiF D δA δB Y u := by
  have := AlgNorm.map_PhiA (sobAlg r hr).val D.G D.B D.C (⟨δA, hA⟩ : sobAlg r hr) ⟨δB, hB⟩
    ⟨Y, hY⟩ ⟨u, memH_mono (by omega) hu⟩ ⟨lap u, (lap_spec hr hu).1⟩
  simp only [Subalgebra.coe_val] at this
  exact this

theorem memH_PhiF {δA δB Y u : CT} (hA : MemH r ⇑δA) (hB : MemH r ⇑δB) (hY : MemH r ⇑Y)
    (hu : MemH (r + 2) ⇑u) : MemH r ⇑(PhiF D δA δB Y u) := by
  rw [← coe_PhiS D r hr hA hB hY hu]; exact (PhiS D r hr hA hB hY hu).2

theorem memH_Tmap {δA δB Y u : CT} (hA : MemH r ⇑δA) (hB : MemH r ⇑δB) (hY : MemH r ⇑Y)
    (hu : MemH (r + 2) ⇑u) : MemH (r + 2) ⇑(Tmap D δA δB Y u) :=
  (Linv_spec hr D.μ_pos (memH_PhiF D r hr hA hB hY hu)).1

/-- The Lipschitz constant of `Φ` on `H^r`. -/
def lipL : ℝ := AlgNorm.lipC (algK r hr) D.G D.B D.C

theorem one_le_lipL : 1 ≤ lipL D r hr :=
  AlgNorm.one_le_lipC (by linarith [one_le_algK r hr]) _ _ _

/-- **Lipschitz estimate for `𝒯`** on the `H^{r+2}` ball of radius `M ≤ 1`:
`‖𝒯u - 𝒯v‖_{H^{r+2}} ≤ c_L L (M + ‖δB‖ + ‖Y‖) ‖u - v‖_{H^{r+2}}`. -/
theorem Tmap_sub_le {δA δB Y u v : CT} (hA : MemH r ⇑δA) (hB : MemH r ⇑δB) (hY : MemH r ⇑Y)
    (hu : MemH (r + 2) ⇑u) (hv : MemH (r + 2) ⇑v) {M : ℝ} (hM : M ≤ 1)
    (huM : sn (r + 2) ⇑u ≤ M) (hvM : sn (r + 2) ⇑v ≤ M) :
    sn (r + 2) ⇑(Tmap D δA δB Y u - Tmap D δA δB Y v) ≤
      cL D * lipL D r hr * (M + sn r ⇑δB + sn r ⇑Y) * sn (r + 2) ⇑(u - v) := by
  have hPu := memH_PhiF D r hr hA hB hY hu
  have hPv := memH_PhiF D r hr hA hB hY hv
  unfold Tmap
  rw [Linv_sub hr D.μ_pos hPu hPv]
  refine (Linv_spec hr D.μ_pos (memH_sub hPu hPv)).2.trans ?_
  set N := sobNorm r hr
  have hmono : ∀ {F : CT}, MemH (r + 2) ⇑F → sn r ⇑F ≤ sn (r + 2) ⇑F :=
    fun hF => sn_mono' (by omega) hF
  have key := N.PhiA_sub_le D.G D.B D.C (⟨δA, hA⟩ : sobAlg r hr) ⟨δB, hB⟩ ⟨Y, hY⟩
    (x := ⟨u, memH_mono (by omega) hu⟩) (y := ⟨v, memH_mono (by omega) hv⟩)
    (Dx := ⟨lap u, (lap_spec hr hu).1⟩) (Dy := ⟨lap v, (lap_spec hr hv).1⟩)
    (d := sn (r + 2) ⇑(u - v)) hM ((hmono hu).trans huM) ((hmono hv).trans hvM)
    (by
      show sn r ⇑(lap u) ≤ 3 * M
      exact (lap_spec hr hu).2.trans (by linarith))
    (by
      show sn r ⇑(u - v) ≤ sn (r + 2) ⇑(u - v)
      exact hmono (memH_sub hu hv))
    (by
      show sn r ⇑(lap u - lap v) ≤ 3 * sn (r + 2) ⇑(u - v)
      rw [lap_sub hr hu hv]; exact (lap_spec hr (memH_sub hu hv)).2)
  have e : (PhiS D r hr hA hB hY hu - PhiS D r hr hA hB hY hv : sobAlg r hr) =
      (⟨PhiF D δA δB Y u - PhiF D δA δB Y v, memH_sub hPu hPv⟩ : sobAlg r hr) := by
    apply Subtype.ext
    rw [Subalgebra.coe_sub, coe_PhiS, coe_PhiS]
  have key' : sn r ⇑(PhiF D δA δB Y u - PhiF D δA δB Y v) ≤
      lipL D r hr * (M + sn r ⇑δB + sn r ⇑Y) * sn (r + 2) ⇑(u - v) := by
    have := key
    unfold PhiS at e
    rw [e] at this
    exact this
  have hc := (cL_pos D).le
  calc (min 8 D.μ)⁻¹ * sn r ⇑(PhiF D δA δB Y u - PhiF D δA δB Y v)
      ≤ cL D * (lipL D r hr * (M + sn r ⇑δB + sn r ⇑Y) * sn (r + 2) ⇑(u - v)) :=
        mul_le_mul_of_nonneg_left key' hc
    _ = _ := by ring

theorem PhiF_zero (δA δB Y : CT) : PhiF D δA δB Y 0 = δA + δB + Y := by
  unfold PhiF; rw [lap_zero hr, AlgNorm.PhiA_zero]

theorem sn_Tmap_zero_le {δA δB Y : CT} (hA : MemH r ⇑δA) (hB : MemH r ⇑δB) (hY : MemH r ⇑Y) :
    sn (r + 2) ⇑(Tmap D δA δB Y 0) ≤ cL D * (sn r ⇑δA + sn r ⇑δB + sn r ⇑Y) := by
  unfold Tmap
  rw [PhiF_zero D r hr]
  have hs : MemH r ⇑(δA + δB + Y) := memH_add (memH_add hA hB) hY
  refine (Linv_spec hr D.μ_pos hs).2.trans (mul_le_mul_of_nonneg_left ?_ (cL_pos D).le)
  exact (sn_add_le' (memH_add hA hB) hY).trans (add_le_add (sn_add_le' hA hB) le_rfl)

/-- The radius of the contraction ball in `H^{r+2}`. -/
def rad : ℝ :=
  min (min 1 (1 / (4 * cL D * lipL D r hr))) (1 / (4 * (Real.sqrt cEmb + 1)))

/-- The smallness threshold for the sources in `H^r`. -/
def eps : ℝ := min (rad D r hr) (rad D r hr / (2 * cL D))

theorem rad_pos : 0 < rad D r hr := by
  have h1 := cL_pos D; have h2 := one_le_lipL D r hr
  unfold rad
  refine lt_min (lt_min one_pos (by positivity)) (by positivity)

theorem rad_le_one : rad D r hr ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)

theorem eps_pos : 0 < eps D r hr := by
  have h1 := rad_pos D r hr; have h2 := cL_pos D
  unfold eps; exact lt_min h1 (by positivity)

theorem cL_lip_rad_le : cL D * lipL D r hr * rad D r hr ≤ 1 / 4 := by
  have h1 := cL_pos D; have h2 := one_le_lipL D r hr
  have h3 : rad D r hr ≤ 1 / (4 * cL D * lipL D r hr) := (min_le_left _ _).trans (min_le_right _ _)
  have h4 : 0 < cL D * lipL D r hr := by positivity
  calc cL D * lipL D r hr * rad D r hr ≤ cL D * lipL D r hr * (1 / (4 * cL D * lipL D r hr)) :=
        mul_le_mul_of_nonneg_left h3 h4.le
    _ = 1 / 4 := by field_simp

theorem sup_lt_half {u : CT} (hu : MemH (r + 2) ⇑u) (huM : sn (r + 2) ⇑u ≤ rad D r hr)
    (x : UnitAddTorus (Fin 3)) : ‖u x‖ < 1 / 2 := by
  have h1 := norm_apply_le_sn (r + 2) (by omega) u hu x
  have hc := Real.sqrt_nonneg cEmb
  have h2 : rad D r hr ≤ 1 / (4 * (Real.sqrt cEmb + 1)) := min_le_right _ _
  have h3 : Real.sqrt cEmb * rad D r hr ≤ Real.sqrt cEmb * (1 / (4 * (Real.sqrt cEmb + 1))) :=
    mul_le_mul_of_nonneg_left h2 hc
  have h4 : Real.sqrt cEmb * (1 / (4 * (Real.sqrt cEmb + 1))) < 1 / 2 := by
    rw [mul_one_div, div_lt_iff₀ (by positivity)]; nlinarith
  calc ‖u x‖ ≤ Real.sqrt cEmb * sn (r + 2) ⇑u := h1
    _ ≤ Real.sqrt cEmb * rad D r hr := mul_le_mul_of_nonneg_left huM hc
    _ < 1 / 2 := lt_of_le_of_lt h3 h4

theorem one_add_ne_zero_of_lt_half {z : ℂ} (hz : ‖z‖ < 1 / 2) : 1 + z ≠ 0 := by
  intro h
  have : z = -1 := by linear_combination h
  rw [this, norm_neg, norm_one] at hz; norm_num at hz

/-- **`𝒯` is a `1/2`-contraction of the `H^{r+2}` ball of radius `rad`** for sources with
`‖δA‖ + ‖δB‖ + ‖Y‖ ≤ eps` in `H^r`, and `‖𝒯 0‖_{H^{r+2}} ≤ c_L (‖δA‖ + ‖δB‖ + ‖Y‖)`. -/
theorem Tmap_ball {δA δB Y : CT} (hA : MemH r ⇑δA) (hB : MemH r ⇑δB)
    (hY : MemH r ⇑Y) (hη : sn r ⇑δA + sn r ⇑δB + sn r ⇑Y ≤ eps D r hr) :
    ∃ κ : ℝ, 0 ≤ κ ∧ κ ≤ 1 / 2 ∧
      (∀ u : CT, MemH (r + 2) ⇑u → sn (r + 2) ⇑u ≤ rad D r hr →
        sn (r + 2) ⇑(Tmap D δA δB Y u) ≤ rad D r hr) ∧
      (∀ u v : CT, MemH (r + 2) ⇑u → MemH (r + 2) ⇑v → sn (r + 2) ⇑u ≤ rad D r hr →
        sn (r + 2) ⇑v ≤ rad D r hr →
        sn (r + 2) ⇑(Tmap D δA δB Y u - Tmap D δA δB Y v) ≤ κ * sn (r + 2) ⇑(u - v)) ∧
      sn (r + 2) ⇑(Tmap D δA δB Y 0) ≤ cL D * (sn r ⇑δA + sn r ⇑δB + sn r ⇑Y) := by
  set M := rad D r hr
  set η := sn r ⇑δA + sn r ⇑δB + sn r ⇑Y with hηdef
  have hM0 := rad_pos D r hr
  have hM1 := rad_le_one D r hr
  have hcl := cL_pos D
  have hL := one_le_lipL D r hr
  have hη0 : 0 ≤ η := by have := sn_nonneg r ⇑δA; have := sn_nonneg r ⇑δB;
                         have := sn_nonneg r ⇑Y; positivity
  have hηM : η ≤ M := hη.trans (min_le_left _ _)
  have hηc : cL D * η ≤ M / 2 := by
    have : η ≤ M / (2 * cL D) := hη.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this; linarith
  set κ := cL D * lipL D r hr * (M + η) with hκ
  have hκ12 : κ ≤ 1 / 2 := by
    have h1 := cL_lip_rad_le D r hr
    have h2 : cL D * lipL D r hr * η ≤ cL D * lipL D r hr * M :=
      mul_le_mul_of_nonneg_left hηM (by positivity)
    rw [hκ, mul_add]; linarith
  have hκ0 : 0 ≤ κ := by positivity
  have hBY : sn r ⇑δB + sn r ⇑Y ≤ η := by have := sn_nonneg r ⇑δA; rw [hηdef]; linarith
  have hlip : ∀ u v : CT, MemH (r + 2) ⇑u → MemH (r + 2) ⇑v → sn (r + 2) ⇑u ≤ M →
      sn (r + 2) ⇑v ≤ M →
      sn (r + 2) ⇑(Tmap D δA δB Y u - Tmap D δA δB Y v) ≤ κ * sn (r + 2) ⇑(u - v) := by
    intro u v hu hv huM hvM
    refine (Tmap_sub_le D r hr hA hB hY hu hv hM1 huM hvM).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (sn_nonneg _ _)
    rw [hκ]
    refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h0 := sn_Tmap_zero_le D r hr hA hB hY
  have hmaps : ∀ u : CT, MemH (r + 2) ⇑u → sn (r + 2) ⇑u ≤ M →
      sn (r + 2) ⇑(Tmap D δA δB Y u) ≤ M := by
    intro u hu huM
    have hT0 := memH_Tmap D r hr hA hB hY (memH_zero (r + 2))
    have hTu := memH_Tmap D r hr hA hB hY hu
    have h1 := hlip u 0 hu (memH_zero _) huM (by
      have : sn (r + 2) ⇑(0 : CT) = 0 := by
        simp [sn, trigSobSq, mFourierCoeff_zero']
      rw [this]; exact hM0.le)
    rw [sub_zero] at h1
    calc sn (r + 2) ⇑(Tmap D δA δB Y u)
        = sn (r + 2) ⇑((Tmap D δA δB Y u - Tmap D δA δB Y 0) + Tmap D δA δB Y 0) := by
          rw [sub_add_cancel]
      _ ≤ sn (r + 2) ⇑(Tmap D δA δB Y u - Tmap D δA δB Y 0) + sn (r + 2) ⇑(Tmap D δA δB Y 0) :=
          sn_add_le' (memH_sub hTu hT0) hT0
      _ ≤ κ * sn (r + 2) ⇑u + cL D * η := add_le_add h1 h0
      _ ≤ (1 / 2) * M + M / 2 := add_le_add
          (mul_le_mul hκ12 huM (sn_nonneg _ _) (by norm_num)) hηc
      _ = M := by ring
  exact ⟨κ, hκ0, hκ12, hmaps, hlip, h0⟩

theorem sn_zero' (s : ℕ) : sn s ⇑(0 : CT) = 0 := by
  simp [sn, trigSobSq, mFourierCoeff_zero']

/-- **Existence and uniqueness of the fixed point of `𝒯`** in the `H^{r+2}` ball of radius
`rad`, for sources with `‖δA‖ + ‖δB‖ + ‖Y‖ ≤ eps` in `H^r`, with the bound
`‖u‖_{H^{r+2}} ≤ 2 c_L (‖δA‖ + ‖δB‖ + ‖Y‖)`. -/
theorem exists_fixedPoint_Tmap {δA δB Y : CT} (hA : MemH r ⇑δA) (hB : MemH r ⇑δB)
    (hY : MemH r ⇑Y) (hη : sn r ⇑δA + sn r ⇑δB + sn r ⇑Y ≤ eps D r hr) :
    ∃ u : CT, MemH (r + 2) ⇑u ∧ sn (r + 2) ⇑u ≤ rad D r hr ∧ Tmap D δA δB Y u = u ∧
      sn (r + 2) ⇑u ≤ 2 * cL D * (sn r ⇑δA + sn r ⇑δB + sn r ⇑Y) ∧
      ∀ v : CT, MemH (r + 2) ⇑v → sn (r + 2) ⇑v ≤ rad D r hr → Tmap D δA δB Y v = v → v = u := by
  obtain ⟨κ, hκ0, hκ12, hmaps, hlip, h0⟩ := Tmap_ball D r hr hA hB hY hη
  have hcl := cL_pos D
  have hη0 : 0 ≤ sn r ⇑δA + sn r ⇑δB + sn r ⇑Y := by
    have := sn_nonneg r ⇑δA; have := sn_nonneg r ⇑δB; have := sn_nonneg r ⇑Y; positivity
  obtain ⟨u, hu, huM, hfix, hbound, huniq⟩ := exists_fixedPoint_sn (s := r + 2) (by omega)
    (Tmap D δA δB Y) (fun u hu => memH_Tmap D r hr hA hB hY hu) (rad_pos D r hr).le hκ0
    (by linarith) hmaps hlip
  refine ⟨u, hu, huM, hfix, ?_, huniq⟩
  refine hbound.trans ?_
  rw [div_le_iff₀ (by linarith)]
  have h2 : 2 * cL D * (sn r ⇑δA + sn r ⇑δB + sn r ⇑Y) * (1 - κ) ≥
      2 * cL D * (sn r ⇑δA + sn r ⇑δB + sn r ⇑Y) * (1 / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

/-- The projected map `𝒯_N = P_N ∘ 𝒯`. -/
def TmapN (N : ℕ) (δA δB Y u : CT) : CT := proj N (Tmap D δA δB Y u)

/-- **The projected contraction**: `𝒯_N = P_N 𝒯` has a unique fixed point in the same ball, with
the same bound; it lies in `Ran P_N` (a trigonometric polynomial: finite data). -/
theorem exists_fixedPoint_TmapN (N : ℕ) {δA δB Y : CT} (hA : MemH r ⇑δA) (hB : MemH r ⇑δB)
    (hY : MemH r ⇑Y) (hη : sn r ⇑δA + sn r ⇑δB + sn r ⇑Y ≤ eps D r hr) :
    ∃ u : CT, MemH (r + 2) ⇑u ∧ sn (r + 2) ⇑u ≤ rad D r hr ∧ TmapN D N δA δB Y u = u ∧
      proj N u = u ∧ sn (r + 2) ⇑u ≤ 2 * cL D * (sn r ⇑δA + sn r ⇑δB + sn r ⇑Y) ∧
      ∀ v : CT, MemH (r + 2) ⇑v → sn (r + 2) ⇑v ≤ rad D r hr → TmapN D N δA δB Y v = v →
        v = u := by
  obtain ⟨κ, hκ0, hκ12, hmaps, hlip, h0⟩ := Tmap_ball D r hr hA hB hY hη
  have hcl := cL_pos D
  have hη0 : 0 ≤ sn r ⇑δA + sn r ⇑δB + sn r ⇑Y := by
    have := sn_nonneg r ⇑δA; have := sn_nonneg r ⇑δB; have := sn_nonneg r ⇑Y; positivity
  have hmapsN : ∀ u : CT, MemH (r + 2) ⇑u → sn (r + 2) ⇑u ≤ rad D r hr →
      sn (r + 2) ⇑(TmapN D N δA δB Y u) ≤ rad D r hr := fun u hu huM =>
    (sn_proj_le N (memH_Tmap D r hr hA hB hY hu)).trans (hmaps u hu huM)
  have hlipN : ∀ u v : CT, MemH (r + 2) ⇑u → MemH (r + 2) ⇑v → sn (r + 2) ⇑u ≤ rad D r hr →
      sn (r + 2) ⇑v ≤ rad D r hr →
      sn (r + 2) ⇑(TmapN D N δA δB Y u - TmapN D N δA δB Y v) ≤ κ * sn (r + 2) ⇑(u - v) := by
    intro u v hu hv huM hvM
    unfold TmapN
    rw [← proj_sub]
    exact (sn_proj_le N (memH_sub (memH_Tmap D r hr hA hB hY hu)
      (memH_Tmap D r hr hA hB hY hv))).trans (hlip u v hu hv huM hvM)
  obtain ⟨u, hu, huM, hfix, hbound, huniq⟩ := exists_fixedPoint_sn (s := r + 2) (by omega)
    (TmapN D N δA δB Y) (fun u _ => memH_proj _ _ _) (rad_pos D r hr).le hκ0
    (by linarith) hmapsN hlipN
  refine ⟨u, hu, huM, hfix, ?_, ?_, huniq⟩
  · rw [← hfix]; unfold TmapN; rw [proj_proj]
  · refine hbound.trans ?_
    have h0' : sn (r + 2) ⇑(TmapN D N δA δB Y 0) ≤ cL D * (sn r ⇑δA + sn r ⇑δB + sn r ⇑Y) :=
      (sn_proj_le N (memH_Tmap D r hr hA hB hY (memH_zero _))).trans h0
    rw [div_le_iff₀ (by linarith)]
    have h2 : 2 * cL D * (sn r ⇑δA + sn r ⇑δB + sn r ⇑Y) * (1 - κ) ≥
        2 * cL D * (sn r ⇑δA + sn r ⇑δB + sn r ⇑Y) * (1 / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith

/-! ### From the fixed point to the conformal equation and back -/

/-- `w = 1 + u` has the same Fourier Laplacian as `u`. -/
theorem lap_one_add {u : CT} (hu : MemH (r + 2) ⇑u) : lap (1 + u) = lap u := by
  have h1 : (1 : CT) = ContinuousMap.const _ 1 := rfl
  rw [lap_add hr (by rw [h1]; exact memH_const _ 1) hu, h1, lap_const hr, zero_add]

/-- A fixed point of `𝒯` with small sup norm solves the conformal Hamiltonian equation. -/
theorem hamiltonianEq_of_fixed {δA δB Y u : CT} (hA : MemH r ⇑δA) (hB : MemH r ⇑δB)
    (hY : MemH r ⇑Y) (hu : MemH (r + 2) ⇑u) (hfix : Tmap D δA δB Y u = u)
    (hsmall : ∀ x, ‖u x‖ < 1 / 2) : HamiltonianEq D δA δB Y (1 + u) := by
  have hP := memH_PhiF D r hr hA hB hY hu
  have hL := L_Linv hr D.μ_pos hP
  have hT : Linv D.μ (PhiF D δA δB Y u) = u := hfix
  rw [hT] at hL
  intro x
  have hx := congrArg (fun F : CT => F x) hL
  simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul] at hx
  rw [PhiF_apply] at hx
  rw [lap_one_add r hr hu]
  simp only [ContinuousMap.add_apply, ContinuousMap.one_apply]
  exact (hamRes_eq_zero_iff D (one_add_ne_zero_of_lt_half r hr (hsmall x))).2 hx

/-- Conversely, a solution `w = 1 + u` with small sup norm is a fixed point of `𝒯`. -/
theorem fixed_of_hamiltonianEq {δA δB Y u : CT} (hA : MemH r ⇑δA) (hB : MemH r ⇑δB)
    (hY : MemH r ⇑Y) (hu : MemH (r + 2) ⇑u) (hsmall : ∀ x, ‖u x‖ < 1 / 2)
    (hE : HamiltonianEq D δA δB Y (1 + u)) : Tmap D δA δB Y u = u := by
  have hP := memH_PhiF D r hr hA hB hY hu
  have hfun : (-8 : ℂ) • lap u + (D.μ : ℂ) • u = PhiF D δA δB Y u := by
    ext x
    have := hE x
    rw [lap_one_add r hr hu] at this
    simp only [ContinuousMap.add_apply, ContinuousMap.one_apply] at this
    have h := (hamRes_eq_zero_iff D (one_add_ne_zero_of_lt_half r hr (hsmall x))).1 this
    simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]
    rw [PhiF_apply]; exact h
  unfold Tmap
  rw [← hfun]
  exact Linv_L hr D.μ_pos hu (by rw [hfun]; exact hP)

/-- Conjugation commutes with `𝒯` for real sources. -/
theorem conjCT_Tmap {δA δB Y u : CT} (hA : MemH r ⇑δA) (hB : MemH r ⇑δB) (hY : MemH r ⇑Y)
    (hAr : conjCT δA = δA) (hBr : conjCT δB = δB) (hYr : conjCT Y = Y) (hu : MemH (r + 2) ⇑u) :
    conjCT (Tmap D δA δB Y u) = Tmap D δA δB Y (conjCT u) := by
  unfold Tmap
  rw [conjCT_Linv hr D.μ_pos (memH_PhiF D r hr hA hB hY hu)]
  congr 1
  ext x
  rw [conjCT_apply, PhiF_apply, PhiF_apply, conj_PhiA, ← conjCT_lap hr hu]
  simp only [conjCT_apply]
  rw [← conjCT_apply δA, ← conjCT_apply δB, ← conjCT_apply Y, hAr, hBr, hYr]

/-! ### The scalar part of `prop:generated-initial` -/

/-- **Constructive solution of the conformal Hamiltonian equation** (`eq:generated-Hamiltonian`,
`eq:generated-w-bound`): for sources with `‖δA‖_{H^r} + ‖δB‖_{H^r} + ‖Y‖_{H^r} ≤ eps` there is a
solution `w ∈ H^{r+2}` with `‖w - 1‖_{H^{r+2}} ≤ 2 c_L (‖δA‖ + ‖δB‖ + ‖Y‖)`, `|w - 1| < 1/2`,
unique among `H^{r+2}` solutions with `‖w - 1‖_{H^{r+2}} ≤ rad`; for real sources `w` is real
with `1/2 < w < 3/2`. -/
theorem lichnerowicz_solution {δA δB Y : CT} (hA : MemH r ⇑δA) (hB : MemH r ⇑δB)
    (hY : MemH r ⇑Y) (hη : sn r ⇑δA + sn r ⇑δB + sn r ⇑Y ≤ eps D r hr) :
    ∃ w : CT, MemH (r + 2) ⇑w ∧ HamiltonianEq D δA δB Y w ∧
      sn (r + 2) ⇑(w - 1) ≤ 2 * cL D * (sn r ⇑δA + sn r ⇑δB + sn r ⇑Y) ∧
      (∀ x, ‖w x - 1‖ < 1 / 2) ∧
      (∀ w' : CT, MemH (r + 2) ⇑w' → sn (r + 2) ⇑(w' - 1) ≤ rad D r hr →
        HamiltonianEq D δA δB Y w' → w' = w) ∧
      (conjCT δA = δA → conjCT δB = δB → conjCT Y = Y →
        ∀ x, (w x).im = 0 ∧ 1 / 2 < (w x).re ∧ (w x).re < 3 / 2) := by
  obtain ⟨u, hu, huM, hfix, hbound, huniq⟩ := exists_fixedPoint_Tmap D r hr hA hB hY hη
  have hsmall := sup_lt_half D r hr hu huM
  have h1 : MemH (r + 2) ⇑(1 : CT) := memH_const (r + 2) 1
  have hw1 : (1 + u) - 1 = u := add_sub_cancel_left 1 u
  refine ⟨1 + u, memH_add h1 hu, hamiltonianEq_of_fixed D r hr hA hB hY hu hfix hsmall, ?_, ?_,
    ?_, ?_⟩
  · rw [hw1]; exact hbound
  · intro x
    have : (1 + u) x - 1 = u x := by simp
    rw [this]; exact hsmall x
  · intro w' hw' hw'M hE
    have hu' : MemH (r + 2) ⇑(w' - 1) := memH_sub hw' h1
    have hw'eq : w' = 1 + (w' - 1) := by abel
    rw [hw'eq] at hE
    have hfix' := fixed_of_hamiltonianEq D r hr hA hB hY hu' (sup_lt_half D r hr hu' hw'M) hE
    have := huniq _ hu' hw'M hfix'
    rw [hw'eq, this]
  · intro hAr hBr hYr x
    have hv := memH_conjCT hu
    have hconj : conjCT u = u := huniq _ hv.1 (by rw [hv.2]; exact huM) (by
      rw [← conjCT_Tmap D r hr hA hB hY hAr hBr hYr hu, hfix])
    have him : (u x).im = 0 := by
      have := congrArg (fun F : CT => F x) hconj
      simp only [conjCT_apply] at this
      exact Complex.conj_eq_iff_im.mp this
    have hre : |(u x).re| < 1 / 2 := lt_of_le_of_lt (Complex.abs_re_le_norm _) (hsmall x)
    have hre' := abs_lt.mp hre
    simp only [ContinuousMap.add_apply, ContinuousMap.one_apply, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im, him]
    refine ⟨by ring, by linarith, by linarith⟩

/-- **Higher regularity of the fixed point**: if the sources lie in `H^{r+p}` and are small there
(`η_{r+p} ≤ eps_{r+p}`, `η_{r+p} ≤ eps_r`, `2 c_L η_{r+p} ≤ rad_r`), the fixed point of the
`H^{r+2}` ball lies in `H^{r+p+2}` with `‖u‖_{H^{r+p+2}} ≤ 2 c_L η_{r+p}`. -/
theorem fixed_regular (p : ℕ) {δA δB Y : CT} (hA : MemH (r + p) ⇑δA) (hB : MemH (r + p) ⇑δB)
    (hY : MemH (r + p) ⇑Y)
    (hηp : sn (r + p) ⇑δA + sn (r + p) ⇑δB + sn (r + p) ⇑Y ≤ eps D (r + p) (by omega))
    (hηr : sn (r + p) ⇑δA + sn (r + p) ⇑δB + sn (r + p) ⇑Y ≤ eps D r hr)
    (hηrad : 2 * cL D * (sn (r + p) ⇑δA + sn (r + p) ⇑δB + sn (r + p) ⇑Y) ≤ rad D r hr)
    {v : CT} (hv : MemH (r + 2) ⇑v) (hvM : sn (r + 2) ⇑v ≤ rad D r hr)
    (hfix : Tmap D δA δB Y v = v) :
    MemH (r + p + 2) ⇑v ∧
      sn (r + p + 2) ⇑v ≤ 2 * cL D * (sn (r + p) ⇑δA + sn (r + p) ⇑δB + sn (r + p) ⇑Y) := by
  have hle : r ≤ r + p := by omega
  have hA' := memH_mono hle hA; have hB' := memH_mono hle hB; have hY' := memH_mono hle hY
  have hηr' : sn r ⇑δA + sn r ⇑δB + sn r ⇑Y ≤ eps D r hr := by
    have := sn_mono' hle hA; have := sn_mono' hle hB; have := sn_mono' hle hY; linarith
  obtain ⟨u', hu', hu'M, hfix', hbound', -⟩ :=
    exists_fixedPoint_Tmap D (r + p) (by omega) hA hB hY hηp
  obtain ⟨u, -, -, -, -, huniq⟩ := exists_fixedPoint_Tmap D r hr hA' hB' hY' hηr'
  have hu'2 : MemH (r + 2) ⇑u' := memH_mono (by omega) hu'
  have hu'r : sn (r + 2) ⇑u' ≤ rad D r hr :=
    (sn_mono' (by omega) hu').trans (hbound'.trans hηrad)
  have e1 := huniq _ hu'2 hu'r hfix'
  have e2 := huniq _ hv hvM hfix
  rw [e2, ← e1]
  exact ⟨hu', hbound'⟩

/-- `‖Φ_S(u) - Φ_{S'}(u)‖_{H^r} ≤ srcC (‖δA - δA'‖ + ‖δB - δB'‖ + ‖Y - Y'‖)` on the unit ball. -/
theorem PhiF_src_sub_le {δA δB Y δA' δB' Y' u : CT} (hA : MemH r ⇑δA) (hB : MemH r ⇑δB)
    (hY : MemH r ⇑Y) (hA' : MemH r ⇑δA') (hB' : MemH r ⇑δB') (hY' : MemH r ⇑Y')
    (hu : MemH (r + 2) ⇑u) (huM : sn (r + 2) ⇑u ≤ 1) :
    sn r ⇑(PhiF D δA δB Y u - PhiF D δA' δB' Y' u) ≤
      AlgNorm.srcC (algK r hr) * (sn r ⇑(δA - δA') + sn r ⇑(δB - δB') + sn r ⇑(Y - Y')) := by
  set N := sobNorm r hr
  have key := N.PhiA_src_sub_le D.G D.B D.C (⟨δA, hA⟩ : sobAlg r hr) ⟨δB, hB⟩ ⟨Y, hY⟩
    ⟨δA', hA'⟩ ⟨δB', hB'⟩ ⟨Y', hY'⟩ (x := ⟨u, memH_mono (by omega) hu⟩)
    (D := ⟨lap u, (lap_spec hr hu).1⟩) (M := 1) le_rfl
    ((sn_mono' (by omega) hu).trans huM)
  have e : (PhiS D r hr hA hB hY hu - PhiS D r hr hA' hB' hY' hu : sobAlg r hr) =
      (⟨PhiF D δA δB Y u - PhiF D δA' δB' Y' u,
        memH_sub (memH_PhiF D r hr hA hB hY hu) (memH_PhiF D r hr hA' hB' hY' hu)⟩ :
        sobAlg r hr) := by
    apply Subtype.ext
    rw [Subalgebra.coe_sub, coe_PhiS, coe_PhiS]
  unfold PhiS at e
  rw [e] at key
  exact key

/-- `‖Φ(u) - Φ(v)‖_{H^r}` on the ball (the `H^r` part of `Tmap_sub_le`). -/
theorem PhiF_sub_le {δA δB Y u v : CT} (hA : MemH r ⇑δA) (hB : MemH r ⇑δB) (hY : MemH r ⇑Y)
    (hu : MemH (r + 2) ⇑u) (hv : MemH (r + 2) ⇑v) {M : ℝ} (hM : M ≤ 1)
    (huM : sn (r + 2) ⇑u ≤ M) (hvM : sn (r + 2) ⇑v ≤ M) :
    sn r ⇑(PhiF D δA δB Y u - PhiF D δA δB Y v) ≤
      lipL D r hr * (M + sn r ⇑δB + sn r ⇑Y) * sn (r + 2) ⇑(u - v) := by
  set N := sobNorm r hr
  have hmono : ∀ {F : CT}, MemH (r + 2) ⇑F → sn r ⇑F ≤ sn (r + 2) ⇑F :=
    fun hF => sn_mono' (by omega) hF
  have key := N.PhiA_sub_le D.G D.B D.C (⟨δA, hA⟩ : sobAlg r hr) ⟨δB, hB⟩ ⟨Y, hY⟩
    (x := ⟨u, memH_mono (by omega) hu⟩) (y := ⟨v, memH_mono (by omega) hv⟩)
    (Dx := ⟨lap u, (lap_spec hr hu).1⟩) (Dy := ⟨lap v, (lap_spec hr hv).1⟩)
    (d := sn (r + 2) ⇑(u - v)) hM ((hmono hu).trans huM) ((hmono hv).trans hvM)
    (by
      show sn r ⇑(lap u) ≤ 3 * M
      exact (lap_spec hr hu).2.trans (by linarith))
    (by
      show sn r ⇑(u - v) ≤ sn (r + 2) ⇑(u - v)
      exact hmono (memH_sub hu hv))
    (by
      show sn r ⇑(lap u - lap v) ≤ 3 * sn (r + 2) ⇑(u - v)
      rw [lap_sub hr hu hv]; exact (lap_spec hr (memH_sub hu hv)).2)
  have e : (PhiS D r hr hA hB hY hu - PhiS D r hr hA hB hY hv : sobAlg r hr) =
      (⟨PhiF D δA δB Y u - PhiF D δA δB Y v,
        memH_sub (memH_PhiF D r hr hA hB hY hu) (memH_PhiF D r hr hA hB hY hv)⟩ :
        sobAlg r hr) := by
    apply Subtype.ext
    rw [Subalgebra.coe_sub, coe_PhiS, coe_PhiS]
  unfold PhiS at e
  rw [e] at key
  exact key

/-- Conjugation commutes with the Fourier truncation. -/
theorem conjCT_proj (N : ℕ) (F : CT) : conjCT (proj N F) = proj N (conjCT F) := by
  refine coeff_ext fun n => ?_
  rw [mFourierCoeff_conjCT, mFourierCoeff_proj, mFourierCoeff_proj, mFourierCoeff_conjCT]
  have : (-n ∈ TorusFourierTruncation.box N) ↔ (n ∈ TorusFourierTruncation.box N) := by
    simp [TorusFourierTruncation.mem_box]
  by_cases h : n ∈ TorusFourierTruncation.box N
  · simp [h, this.mpr h]
  · have h' : -n ∉ TorusFourierTruncation.box N := fun h' => h (this.mp h')
    simp [h, h']

/-- Higher regularity of the projected fixed point (as `fixed_regular`). -/
theorem fixedN_regular (p N : ℕ) {δA δB Y : CT} (hA : MemH (r + p) ⇑δA)
    (hB : MemH (r + p) ⇑δB) (hY : MemH (r + p) ⇑Y)
    (hηp : sn (r + p) ⇑δA + sn (r + p) ⇑δB + sn (r + p) ⇑Y ≤ eps D (r + p) (by omega))
    (hηr : sn (r + p) ⇑δA + sn (r + p) ⇑δB + sn (r + p) ⇑Y ≤ eps D r hr)
    (hηrad : 2 * cL D * (sn (r + p) ⇑δA + sn (r + p) ⇑δB + sn (r + p) ⇑Y) ≤ rad D r hr)
    {v : CT} (hv : MemH (r + 2) ⇑v) (hvM : sn (r + 2) ⇑v ≤ rad D r hr)
    (hfix : TmapN D N δA δB Y v = v) :
    MemH (r + p + 2) ⇑v ∧
      sn (r + p + 2) ⇑v ≤ 2 * cL D * (sn (r + p) ⇑δA + sn (r + p) ⇑δB + sn (r + p) ⇑Y) := by
  have hle : r ≤ r + p := by omega
  have hA' := memH_mono hle hA; have hB' := memH_mono hle hB; have hY' := memH_mono hle hY
  have hηr' : sn r ⇑δA + sn r ⇑δB + sn r ⇑Y ≤ eps D r hr := by
    have := sn_mono' hle hA; have := sn_mono' hle hB; have := sn_mono' hle hY; linarith
  obtain ⟨u', hu', hu'M, hfix', -, hbound', -⟩ :=
    exists_fixedPoint_TmapN D (r + p) (by omega) N hA hB hY hηp
  obtain ⟨u, -, -, -, -, -, huniq⟩ := exists_fixedPoint_TmapN D r hr N hA' hB' hY' hηr'
  have hu'2 : MemH (r + 2) ⇑u' := memH_mono (by omega) hu'
  have hu'r : sn (r + 2) ⇑u' ≤ rad D r hr :=
    (sn_mono' (by omega) hu').trans (hbound'.trans hηrad)
  have e1 := huniq _ hu'2 hu'r hfix'
  have e2 := huniq _ hv hvM hfix
  rw [e2, ← e1]
  exact ⟨hu', hbound'⟩

/-- The two-level smallness threshold (sources small in `H^{r+p}`). -/
def epsP (p : ℕ) : ℝ :=
  min (eps D (r + p) (by omega)) (min (eps D r hr) (rad D r hr / (2 * cL D)))

theorem epsP_pos (p : ℕ) : 0 < epsP D r hr p := by
  have h1 := eps_pos D (r + p) (by omega); have h2 := eps_pos D r hr
  have h3 := rad_pos D r hr; have h4 := cL_pos D
  unfold epsP
  exact lt_min h1 (lt_min h2 (by positivity))

theorem epsP_le_one (p : ℕ) : epsP D r hr p ≤ 1 :=
  (min_le_right _ _).trans ((min_le_left _ _).trans
    ((min_le_left _ _).trans (rad_le_one D r hr)))

/-- The residual constant `2 L_{r+p} + 1`. -/
def resB (p : ℕ) : ℝ := 2 * lipL D (r + p) (by omega) + 1

/-- **Finite (spectrally projected) conformal factors** (finite part of `prop:generated-initial`).
Let the exact sources `S = (δA, δB, Y)` and the finite-solver sources `S_N` lie in `H^{r+p}` with
`η_{r+p} ≤ epsP`.  Then the exact fixed point `u` (`w = 1 + u`) and the projected fixed point
`u_N = P_N 𝒯_{S_N}(u_N) ∈ Ran P_N` (`w_N = 1 + u_N`, a trigonometric polynomial) exist, are unique
in the `H^{r+2}` ball, are bounded in `H^{r+p+2}` uniformly in `N`, and
* `‖u_N - u‖_{H^{r+2}} ≤ 2 (c_L C_src ‖S_N - S‖_{H^r} + N^{-p} 2 c_L η_{r+p}(S))`;
* the multiplied Hamiltonian residual `L_* u_N - Φ_{S_N}(u_N) = (P_N - I) Φ_{S_N}(u_N)` is
  `≤ N^{-p} (2 L_{r+p} + 1)` in `H^r`. -/
theorem finite_conformal (p N : ℕ) (hN : 1 ≤ N) {δA δB Y δAN δBN YN : CT}
    (hA : MemH (r + p) ⇑δA) (hB : MemH (r + p) ⇑δB) (hY : MemH (r + p) ⇑Y)
    (hAN : MemH (r + p) ⇑δAN) (hBN : MemH (r + p) ⇑δBN) (hYN : MemH (r + p) ⇑YN)
    (hη : sn (r + p) ⇑δA + sn (r + p) ⇑δB + sn (r + p) ⇑Y ≤ epsP D r hr p)
    (hηN : sn (r + p) ⇑δAN + sn (r + p) ⇑δBN + sn (r + p) ⇑YN ≤ epsP D r hr p) :
    ∃ u uN : CT,
      (MemH (r + p + 2) ⇑u ∧ Tmap D δA δB Y u = u ∧ sn (r + 2) ⇑u ≤ rad D r hr ∧
        sn (r + p + 2) ⇑u ≤ 2 * cL D * (sn (r + p) ⇑δA + sn (r + p) ⇑δB + sn (r + p) ⇑Y) ∧
        ∀ v : CT, MemH (r + 2) ⇑v → sn (r + 2) ⇑v ≤ rad D r hr → Tmap D δA δB Y v = v →
          v = u) ∧
      (MemH (r + p + 2) ⇑uN ∧ proj N uN = uN ∧ TmapN D N δAN δBN YN uN = uN ∧
        sn (r + 2) ⇑uN ≤ rad D r hr ∧
        sn (r + p + 2) ⇑uN ≤ 2 * cL D * (sn (r + p) ⇑δAN + sn (r + p) ⇑δBN + sn (r + p) ⇑YN) ∧
        ∀ v : CT, MemH (r + 2) ⇑v → sn (r + 2) ⇑v ≤ rad D r hr →
          TmapN D N δAN δBN YN v = v → v = uN) ∧
      sn (r + 2) ⇑(uN - u) ≤ 2 * (cL D * AlgNorm.srcC (algK r hr) *
          (sn r ⇑(δAN - δA) + sn r ⇑(δBN - δB) + sn r ⇑(YN - Y)) +
          ((N : ℝ) ^ p)⁻¹ * (2 * cL D * (sn (r + p) ⇑δA + sn (r + p) ⇑δB + sn (r + p) ⇑Y))) ∧
      sn r ⇑((-8 : ℂ) • lap uN + (D.μ : ℂ) • uN - PhiF D δAN δBN YN uN) ≤
        ((N : ℝ) ^ p)⁻¹ * resB D r hr p := by
  have hle : r ≤ r + p := by omega
  have hcl := cL_pos D
  have hrad1 := rad_le_one D r hr
  -- level-`r` data
  have hlev : ∀ {F G H : CT}, MemH (r + p) ⇑F → MemH (r + p) ⇑G → MemH (r + p) ⇑H →
      sn (r + p) ⇑F + sn (r + p) ⇑G + sn (r + p) ⇑H ≤ epsP D r hr p →
      (sn (r + p) ⇑F + sn (r + p) ⇑G + sn (r + p) ⇑H ≤ eps D (r + p) (by omega)) ∧
      (sn (r + p) ⇑F + sn (r + p) ⇑G + sn (r + p) ⇑H ≤ eps D r hr) ∧
      (2 * cL D * (sn (r + p) ⇑F + sn (r + p) ⇑G + sn (r + p) ⇑H) ≤ rad D r hr) ∧
      (sn r ⇑F + sn r ⇑G + sn r ⇑H ≤ eps D r hr) := by
    intro F G H hF hG hH h
    have h1 : epsP D r hr p ≤ eps D (r + p) (by omega) := min_le_left _ _
    have h2 : epsP D r hr p ≤ eps D r hr := (min_le_right _ _).trans (min_le_left _ _)
    have h3 : epsP D r hr p ≤ rad D r hr / (2 * cL D) :=
      (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨h.trans h1, h.trans h2, ?_, ?_⟩
    · have := h.trans h3
      rw [le_div_iff₀ (by positivity)] at this; linarith
    · have := sn_mono' hle hF; have := sn_mono' hle hG; have := sn_mono' hle hH
      linarith [h.trans h2]
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hlev hA hB hY hη
  obtain ⟨hq1, hq2, hq3, hq4⟩ := hlev hAN hBN hYN hηN
  have hA' := memH_mono hle hA; have hB' := memH_mono hle hB; have hY' := memH_mono hle hY
  have hAN' := memH_mono hle hAN; have hBN' := memH_mono hle hBN; have hYN' := memH_mono hle hYN
  obtain ⟨u, hu, huM, hfix, -, huniq⟩ := exists_fixedPoint_Tmap D r hr hA' hB' hY' hp4
  obtain ⟨uN, huN, huNM, hfixN, hprojN, -, huniqN⟩ :=
    exists_fixedPoint_TmapN D r hr N hAN' hBN' hYN' hq4
  obtain ⟨hureg, hubd⟩ := fixed_regular D r hr p hA hB hY hp1 hp2 hp3 hu huM hfix
  obtain ⟨huNreg, huNbd⟩ := fixedN_regular D r hr p N hAN hBN hYN hq1 hq2 hq3 huN huNM hfixN
  refine ⟨u, uN, ⟨hureg, hfix, huM, hubd, huniq⟩, ⟨huNreg, hprojN, hfixN, huNM, huNbd, huniqN⟩,
    ?_, ?_⟩
  · -- the rate
    obtain ⟨κ, hκ0, hκ12, -, hlipN, -⟩ := Tmap_ball D r hr hAN' hBN' hYN' hq4
    have hTu := memH_Tmap D r hr hA' hB' hY' hu
    have hTNu := memH_Tmap D r hr hAN' hBN' hYN' hu
    have hTNuN := memH_Tmap D r hr hAN' hBN' hYN' huN
    have hlipNN : sn (r + 2) ⇑(TmapN D N δAN δBN YN uN - TmapN D N δAN δBN YN u) ≤
        κ * sn (r + 2) ⇑(uN - u) := by
      unfold TmapN; rw [← proj_sub]
      exact (sn_proj_le N (memH_sub hTNuN hTNu)).trans (hlipN uN u huN hu huNM huM)
    have hb := sn_sub_fixedPoint_le (T := TmapN D N δAN δBN YN) (T' := Tmap D δA δB Y)
      (by linarith) hfixN hfix (memH_sub (memH_proj _ _ _) (memH_proj _ _ _))
      (memH_sub (memH_proj _ _ _) hTu) hlipNN
    -- the defect `P_N 𝒯_{S_N} u - 𝒯_S u`
    have e : TmapN D N δAN δBN YN u - Tmap D δA δB Y u =
        proj N (Tmap D δAN δBN YN u - Tmap D δA δB Y u) - (u - proj N u) := by
      unfold TmapN; rw [proj_sub, hfix]; abel
    have hsrc : sn (r + 2) ⇑(Tmap D δAN δBN YN u - Tmap D δA δB Y u) ≤
        cL D * AlgNorm.srcC (algK r hr) *
          (sn r ⇑(δAN - δA) + sn r ⇑(δBN - δB) + sn r ⇑(YN - Y)) := by
      unfold Tmap
      have hP1 := memH_PhiF D r hr hAN' hBN' hYN' hu
      have hP2 := memH_PhiF D r hr hA' hB' hY' hu
      rw [Linv_sub hr D.μ_pos hP1 hP2]
      refine (Linv_spec hr D.μ_pos (memH_sub hP1 hP2)).2.trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (PhiF_src_sub_le D r hr hAN' hBN' hYN' hA' hB' hY' hu
        (huM.trans hrad1)) hcl.le
    have htail : sn (r + 2) ⇑(u - proj N u) ≤
        ((N : ℝ) ^ p)⁻¹ * (2 * cL D * (sn (r + p) ⇑δA + sn (r + p) ⇑δB + sn (r + p) ⇑Y)) := by
      have hu' : MemH (r + 2 + p) ⇑u := by rw [show r + 2 + p = r + p + 2 by omega]; exact hureg
      refine (sn_sub_proj_le_pow (r := r + 2) (p := p) hN hu').trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [show r + 2 + p = r + p + 2 by omega]; exact hubd
    have hdef : sn (r + 2) ⇑(TmapN D N δAN δBN YN u - Tmap D δA δB Y u) ≤
        cL D * AlgNorm.srcC (algK r hr) *
          (sn r ⇑(δAN - δA) + sn r ⇑(δBN - δB) + sn r ⇑(YN - Y)) +
        ((N : ℝ) ^ p)⁻¹ * (2 * cL D * (sn (r + p) ⇑δA + sn (r + p) ⇑δB + sn (r + p) ⇑Y)) := by
      rw [e]
      refine (sn_sub_le' (memH_proj _ _ _) (memH_sub hu (memH_proj _ _ _))).trans
        (add_le_add ((sn_proj_le N (memH_sub hTNu hTu)).trans hsrc) htail)
    refine hb.trans ?_
    rw [div_le_iff₀ (by linarith)]
    have hnn : 0 ≤ cL D * AlgNorm.srcC (algK r hr) *
          (sn r ⇑(δAN - δA) + sn r ⇑(δBN - δB) + sn r ⇑(YN - Y)) +
        ((N : ℝ) ^ p)⁻¹ * (2 * cL D * (sn (r + p) ⇑δA + sn (r + p) ⇑δB + sn (r + p) ⇑Y)) :=
      (sn_nonneg _ _).trans hdef
    nlinarith
  · -- the residual
    have hrp : 2 ≤ r + p := by omega
    have hΦ : MemH (r + p) ⇑(PhiF D δAN δBN YN uN) := by
      have := memH_PhiF D (r + p) hrp hAN hBN hYN (by
        rw [show r + p + 2 = r + p + 2 from rfl]; exact huNreg)
      exact this
    have hΦr : MemH r ⇑(PhiF D δAN δBN YN uN) := memH_mono hle hΦ
    have huNeq : uN = Linv D.μ (proj N (PhiF D δAN δBN YN uN)) := by
      conv_lhs => rw [← hfixN]
      unfold TmapN Tmap Linv
      exact proj_fmul N (summable_Linv hr D.μ_pos hΦr)
    have hLu : (-8 : ℂ) • lap uN + (D.μ : ℂ) • uN = proj N (PhiF D δAN δBN YN uN) := by
      have := L_Linv hr D.μ_pos (memH_proj r N (PhiF D δAN δBN YN uN))
      rw [← huNeq] at this; exact this
    rw [hLu]
    have e : proj N (PhiF D δAN δBN YN uN) - PhiF D δAN δBN YN uN =
        -(PhiF D δAN δBN YN uN - proj N (PhiF D δAN δBN YN uN)) := by abel
    rw [e, sn_neg]
    refine (sn_sub_proj_le_pow (r := r) (p := p) hN hΦ).trans
      (mul_le_mul_of_nonneg_left ?_ (by positivity))
    -- `‖Φ(u_N)‖_{H^{r+p}} ≤ 2 L + 1`
    have hηN1 : sn (r + p) ⇑δAN + sn (r + p) ⇑δBN + sn (r + p) ⇑YN ≤ 1 :=
      hηN.trans (epsP_le_one D r hr p)
    have huN1 : sn (r + p + 2) ⇑uN ≤ 1 := huNbd.trans (hq3.trans hrad1)
    have h0 : sn (r + p + 2) ⇑(0 : CT) ≤ 1 := by rw [sn_zero' r hr]; norm_num
    have hd := PhiF_sub_le D (r + p) hrp hAN hBN hYN huNreg (memH_zero _) le_rfl huN1 h0
    rw [sub_zero, PhiF_zero D (r + p) hrp] at hd
    have hz : MemH (r + p) ⇑(δAN + δBN + YN) := memH_add (memH_add hAN hBN) hYN
    have hs0 : sn (r + p) ⇑(δAN + δBN + YN) ≤ 1 :=
      ((sn_add_le' (memH_add hAN hBN) hYN).trans
        (add_le_add (sn_add_le' hAN hBN) le_rfl)).trans hηN1
    have hL := one_le_lipL D (r + p) hrp
    have hpos : 0 ≤ sn (r + p) ⇑δAN := sn_nonneg _ _
    have e2 : PhiF D δAN δBN YN uN =
        (PhiF D δAN δBN YN uN - (δAN + δBN + YN)) + (δAN + δBN + YN) := by abel
    rw [e2]
    have hm1 : MemH (r + p) ⇑(PhiF D δAN δBN YN uN - (δAN + δBN + YN)) := memH_sub hΦ hz
    refine (sn_add_le' hm1 hz).trans ?_
    unfold resB
    have hBY : 1 + sn (r + p) ⇑δBN + sn (r + p) ⇑YN ≤ 2 := by linarith
    have h3 : lipL D (r + p) hrp * (1 + sn (r + p) ⇑δBN + sn (r + p) ⇑YN) *
        sn (r + p + 2) ⇑uN ≤ lipL D (r + p) hrp * 2 * 1 := by
      have := sn_nonneg (r + p + 2) ⇑uN
      have : 0 ≤ 1 + sn (r + p) ⇑δBN + sn (r + p) ⇑YN := by
        have := sn_nonneg (r + p) ⇑δBN; have := sn_nonneg (r + p) ⇑YN; linarith
      gcongr
    linarith

/-- Conjugation commutes with the projected map for real sources. -/
theorem conjCT_TmapN (N : ℕ) {δA δB Y u : CT} (hA : MemH r ⇑δA) (hB : MemH r ⇑δB)
    (hY : MemH r ⇑Y) (hAr : conjCT δA = δA) (hBr : conjCT δB = δB) (hYr : conjCT Y = Y)
    (hu : MemH (r + 2) ⇑u) :
    conjCT (TmapN D N δA δB Y u) = TmapN D N δA δB Y (conjCT u) := by
  unfold TmapN
  rw [conjCT_proj r hr, conjCT_Tmap D r hr hA hB hY hAr hBr hYr hu]

/-- A fixed point of a conjugation-equivariant map which is unique in the ball is real. -/
theorem im_eq_zero_of_unique {T : CT → CT} {u : CT} (hu : MemH (r + 2) ⇑u)
    (huM : sn (r + 2) ⇑u ≤ rad D r hr) (hfix : T u = u)
    (hconjT : conjCT (T u) = T (conjCT u))
    (huniq : ∀ v : CT, MemH (r + 2) ⇑v → sn (r + 2) ⇑v ≤ rad D r hr → T v = v → v = u)
    (x : UnitAddTorus (Fin 3)) : (u x).im = 0 := by
  have hv := memH_conjCT hu
  have hconj : conjCT u = u := huniq _ hv.1 (by rw [hv.2]; exact huM) (by rw [← hconjT, hfix])
  have := congrArg (fun F : CT => F x) hconj
  simp only [conjCT_apply] at this
  exact Complex.conj_eq_iff_im.mp this

/-- **Pointwise bound for the conformal Hamiltonian residual** of `w = 1 + u` (`|u| < 1/2`):
`|-8Δw - 𝖠 w⁻⁷ - G w - 𝖡 w⁻³ - 𝖸 w⁻¹ + C w⁵| ≤ 2⁷ √c_emb ‖L_* u - Φ(u)‖_{H^r}`. -/
theorem norm_hamRes_le {δA δB Y u : CT} (hu : MemH (r + 2) ⇑u) (hsmall : ∀ x, ‖u x‖ < 1 / 2)
    (hρ : MemH r ⇑((-8 : ℂ) • lap u + (D.μ : ℂ) • u - PhiF D δA δB Y u))
    (x : UnitAddTorus (Fin 3)) :
    ‖hamRes D (δA x) (δB x) (Y x) ((1 + u) x) (lap (1 + u) x)‖ ≤
      2 ^ 7 * (Real.sqrt cEmb *
        sn r ⇑((-8 : ℂ) • lap u + (D.μ : ℂ) • u - PhiF D δA δB Y u)) := by
  set ρ := (-8 : ℂ) • lap u + (D.μ : ℂ) • u - PhiF D δA δB Y u with hρdef
  have hw := one_add_ne_zero_of_lt_half r hr (hsmall x)
  have hmul := hamRes_mul D (Dx := lap u x) (a := δA x) (b := δB x) (y := Y x) hw
  have hρx : ρ x = (-8 * lap u x + (D.μ : ℂ) * u x) -
      AlgNorm.PhiA D.G D.B D.C (δA x) (δB x) (Y x) (u x) (lap u x) := by
    rw [hρdef]
    simp only [ContinuousMap.sub_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply,
      smul_eq_mul]
    rw [PhiF_apply]
  rw [lap_one_add r hr hu]
  simp only [ContinuousMap.add_apply, ContinuousMap.one_apply]
  rw [← hρx] at hmul
  have hw1 : 1 / 2 ≤ ‖1 + u x‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-u x)
    rw [sub_neg_eq_add, norm_one, norm_neg] at this
    linarith [hsmall x]
  have hpos : 0 < ‖1 + u x‖ := by linarith
  have hb := norm_apply_le_sn r hr ρ hρ x
  have h1 : ‖hamRes D (δA x) (δB x) (Y x) (1 + u x) (lap u x)‖ * ‖1 + u x‖ ^ 7 = ‖ρ x‖ := by
    rw [← norm_pow, ← norm_mul, hmul]
  have h2 : (1 / 2 : ℝ) ^ 7 ≤ ‖1 + u x‖ ^ 7 := pow_le_pow_left₀ (by norm_num) hw1 7
  have h3 := norm_nonneg (hamRes D (δA x) (δB x) (Y x) (1 + u x) (lap u x))
  have h4 : ‖hamRes D (δA x) (δB x) (Y x) (1 + u x) (lap u x)‖ * (1 / 2) ^ 7 ≤ ‖ρ x‖ := by
    rw [← h1]; exact mul_le_mul_of_nonneg_left h2 h3
  nlinarith

end

/-! ### `ass:constrained-initial-solver` and `prop:generated-initial` -/

/-- **Interface of `ass:constrained-initial-solver`** for the scalar conformal equation at Sobolev
order `r` (seeds `σ, χ` measured in `H^{r+1}`, sources in `H^r`), with `p` additional seed
derivatives.  The fields are what the assumption supplies:
* the compatible Gauss and vector-momentum solves turn a seed into the (real) source coefficients
  `δA, δB, Y` of the scalar equation (`srcA`, `srcB`, `srcY`), with the source bound
  `eq:generated-source-small` `‖δA‖ + ‖δB‖ + ‖Y‖ ≤ C (‖σ‖² + ‖χ‖²)` (`src_small`, and at order
  `r + p`, `src_smallP`; `seedSq` stands for `‖σ‖²_{H^{r+1}} + ‖χ‖²_{H^{r+1}}`);
* the conformal identities: once the Gauss and vector solutions are inserted, the complete
  Einstein, gauge and matter initial constraints of the assembled tuple (`Constraints σ w`) are
  equivalent to the scalar equation `eq:generated-Hamiltonian` for the conformal factor
  (`conformal`);
* the finite solvers (Fourier projection of the seeds followed by the finite compatible elliptic
  solves) produce sources `srcAN N σ, …` with the cutoff-uniform bounds and the approximation
  estimate `‖S_N - S‖_{H^r} ≤ C_fin (seed size) N^{-p}` (`fin_rate`). -/
structure ConstrainedInitialSolver (D : LichData) (r p : ℕ) (Seed : Type*) where
  /-- `‖σ‖²_{H^{r+1}} + ‖χ‖²_{H^{r+1}}` -/
  seedSq : Seed → ℝ
  /-- the same with `p` additional derivatives -/
  seedSqP : Seed → ℝ
  seedSq_nonneg : ∀ σ, 0 ≤ seedSq σ
  seedSq_le : ∀ σ, seedSq σ ≤ seedSqP σ
  /-- source coefficient `δ𝖠` -/
  srcA : Seed → CT
  /-- source coefficient `δ𝖡` -/
  srcB : Seed → CT
  /-- source coefficient `𝖸` -/
  srcY : Seed → CT
  src_real : ∀ σ, conjCT (srcA σ) = srcA σ ∧ conjCT (srcB σ) = srcB σ ∧ conjCT (srcY σ) = srcY σ
  src_mem : ∀ σ, MemH (r + p) ⇑(srcA σ) ∧ MemH (r + p) ⇑(srcB σ) ∧ MemH (r + p) ⇑(srcY σ)
  /-- the constant of `eq:generated-source-small` -/
  Csrc : ℝ
  Csrc_nonneg : 0 ≤ Csrc
  src_small : ∀ σ, sn r ⇑(srcA σ) + sn r ⇑(srcB σ) + sn r ⇑(srcY σ) ≤ Csrc * seedSq σ
  src_smallP : ∀ σ,
    sn (r + p) ⇑(srcA σ) + sn (r + p) ⇑(srcB σ) + sn (r + p) ⇑(srcY σ) ≤ Csrc * seedSqP σ
  /-- the complete initial constraints of the tuple built from the seed and the conformal
  factor -/
  Constraints : Seed → CT → Prop
  /-- the conformal identities -/
  conformal : ∀ σ (w : CT), (∀ x, w x ≠ 0) →
    (Constraints σ w ↔ HamiltonianEq D (srcA σ) (srcB σ) (srcY σ) w)
  /-- finite-solver source `δ𝖠_N` -/
  srcAN : ℕ → Seed → CT
  /-- finite-solver source `δ𝖡_N` -/
  srcBN : ℕ → Seed → CT
  /-- finite-solver source `𝖸_N` -/
  srcYN : ℕ → Seed → CT
  fin_real : ∀ N σ, conjCT (srcAN N σ) = srcAN N σ ∧ conjCT (srcBN N σ) = srcBN N σ ∧
    conjCT (srcYN N σ) = srcYN N σ
  fin_mem : ∀ N σ, MemH (r + p) ⇑(srcAN N σ) ∧ MemH (r + p) ⇑(srcBN N σ) ∧
    MemH (r + p) ⇑(srcYN N σ)
  fin_smallP : ∀ N σ, sn (r + p) ⇑(srcAN N σ) + sn (r + p) ⇑(srcBN N σ) +
    sn (r + p) ⇑(srcYN N σ) ≤ Csrc * seedSqP σ
  /-- the constant of the finite approximation estimate -/
  Cfin : ℝ
  Cfin_nonneg : 0 ≤ Cfin
  fin_rate : ∀ N σ, 1 ≤ N → sn r ⇑(srcAN N σ - srcA σ) + sn r ⇑(srcBN N σ - srcB σ) +
    sn r ⇑(srcYN N σ - srcY σ) ≤ Cfin * seedSqP σ * ((N : ℝ) ^ p)⁻¹

namespace ConstrainedInitialSolver

variable {D : LichData} {r p : ℕ} {Seed : Type*} (S : ConstrainedInitialSolver D r p Seed)

/-- **`prop:generated-initial`, exact part** (`Σ = 𝕋³`).  Under `ass:constrained-initial-solver`,
for `r ≥ 2` there are `ε, ρ > 0`, `C ≥ 0` such that every seed with `‖σ‖² + ‖χ‖² ≤ ε` determines a
conformal factor `w ∈ H^{r+2}` solving `eq:generated-Hamiltonian`, unique in the `H^{r+2}`
neighbourhood `‖w - 1‖_{H^{r+2}} ≤ ρ` of one, with `‖w - 1‖_{H^{r+2}} ≤ C (‖σ‖² + ‖χ‖²)` and
`1/2 < w < 3/2` (`eq:generated-w-bound`); the assembled tuple satisfies the complete initial
constraints. -/
theorem generated_initial (hr : 2 ≤ r) :
    ∃ ε > 0, ∃ ρ > 0, ∃ C ≥ 0, ∀ σ : Seed, S.seedSq σ ≤ ε →
      ∃ w : CT, MemH (r + 2) ⇑w ∧ HamiltonianEq D (S.srcA σ) (S.srcB σ) (S.srcY σ) w ∧
        S.Constraints σ w ∧ sn (r + 2) ⇑(w - 1) ≤ C * S.seedSq σ ∧
        (∀ x, (w x).im = 0 ∧ 1 / 2 < (w x).re ∧ (w x).re < 3 / 2) ∧
        ∀ w' : CT, MemH (r + 2) ⇑w' → sn (r + 2) ⇑(w' - 1) ≤ ρ →
          HamiltonianEq D (S.srcA σ) (S.srcB σ) (S.srcY σ) w' → w' = w := by
  have hcs := S.Csrc_nonneg
  have he := eps_pos D r hr
  have hcl := cL_pos D
  refine ⟨eps D r hr / (S.Csrc + 1), by positivity, rad D r hr, rad_pos D r hr,
    2 * cL D * S.Csrc, by positivity, fun σ hσ => ?_⟩
  obtain ⟨hA, hB, hY⟩ := S.src_mem σ
  have hle : r ≤ r + p := by omega
  have hA' := memH_mono hle hA; have hB' := memH_mono hle hB; have hY' := memH_mono hle hY
  have hη : sn r ⇑(S.srcA σ) + sn r ⇑(S.srcB σ) + sn r ⇑(S.srcY σ) ≤ eps D r hr := by
    refine (S.src_small σ).trans ?_
    have h1 : S.Csrc * S.seedSq σ ≤ S.Csrc * (eps D r hr / (S.Csrc + 1)) :=
      mul_le_mul_of_nonneg_left hσ hcs
    have h2 : S.Csrc * (eps D r hr / (S.Csrc + 1)) ≤ eps D r hr := by
      rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
    linarith
  obtain ⟨w, hw, hE, hbd, hsmall, huniq, hreal⟩ := lichnerowicz_solution D r hr hA' hB' hY' hη
  obtain ⟨hAr, hBr, hYr⟩ := S.src_real σ
  refine ⟨w, hw, hE, ?_, ?_, hreal hAr hBr hYr, huniq⟩
  · refine (S.conformal σ w fun x h => ?_).2 hE
    have := hsmall x; rw [h, zero_sub, norm_neg, norm_one] at this; norm_num at this
  · refine hbd.trans ?_
    have := S.src_small σ
    have h2 : 0 ≤ 2 * cL D := by positivity
    calc 2 * cL D * (sn r ⇑(S.srcA σ) + sn r ⇑(S.srcB σ) + sn r ⇑(S.srcY σ))
        ≤ 2 * cL D * (S.Csrc * S.seedSq σ) := mul_le_mul_of_nonneg_left this h2
      _ = _ := by ring

/-- **`prop:generated-initial`, finite part** (`Σ = 𝕋³`).  If the seeds have `p` additional
derivatives, the finite construction (projected seeds, finite compatible solves, projected
contraction `w_N = 1 + u_N`, `u_N = P_N L_*⁻¹ Φ_{S_N}(u_N)`) gives finite conformal factors
`w_N ∈ Ran P_N` (trigonometric polynomials), real with `1/2 < w_N < 3/2`, with the cutoff-uniform
bound `‖w_N - 1‖_{H^{r+p+2}} ≤ C (seed size)` and the rate
`‖w_N - w‖_{H^{r+2}} ≤ C (seed size) N^{-p}` (the scalar component of
`eq:generated-initial-rate`), and the scalar Hamiltonian residual of `w_N` is `O(N^{-p})`
uniformly on `𝕋³`.  No spacetime solution is used. -/
theorem generated_initial_finite (hr : 2 ≤ r) :
    ∃ ε > 0, ∃ C ≥ 0, ∀ σ : Seed, S.seedSqP σ ≤ ε →
      ∃ w : CT, MemH (r + p + 2) ⇑w ∧ HamiltonianEq D (S.srcA σ) (S.srcB σ) (S.srcY σ) w ∧
        S.Constraints σ w ∧ sn (r + p + 2) ⇑(w - 1) ≤ C * S.seedSqP σ ∧
        (∀ x, (w x).im = 0 ∧ 1 / 2 < (w x).re ∧ (w x).re < 3 / 2) ∧
        ∀ N : ℕ, 1 ≤ N → ∃ wN : CT, proj N wN = wN ∧ MemH (r + p + 2) ⇑wN ∧
          sn (r + p + 2) ⇑(wN - 1) ≤ C * S.seedSqP σ ∧
          sn (r + 2) ⇑(wN - w) ≤ C * S.seedSqP σ * ((N : ℝ) ^ p)⁻¹ ∧
          (∀ x, (wN x).im = 0 ∧ 1 / 2 < (wN x).re ∧ (wN x).re < 3 / 2) ∧
          ∀ x, ‖hamRes D (S.srcAN N σ x) (S.srcBN N σ x) (S.srcYN N σ x) (wN x) (lap wN x)‖ ≤
            C * ((N : ℝ) ^ p)⁻¹ := by
  have hcs := S.Csrc_nonneg
  have hcf := S.Cfin_nonneg
  have he := epsP_pos D r hr p
  have hcl := cL_pos D
  have hK := one_le_algK r hr
  have hsrcC : 0 ≤ AlgNorm.srcC (algK r hr) := by unfold AlgNorm.srcC; positivity
  have hres : 0 ≤ resB D r hr p := by
    have := one_le_lipL D (r + p) (by omega); unfold resB; linarith
  set C₁ := 2 * cL D * S.Csrc
  set C₂ := 2 * (cL D * AlgNorm.srcC (algK r hr) * S.Cfin + 2 * cL D * S.Csrc)
  set C₃ := 2 ^ 7 * (Real.sqrt cEmb * resB D r hr p)
  have h1 : 0 ≤ C₁ := by positivity
  have h2 : 0 ≤ C₂ := by positivity
  have h3 : 0 ≤ C₃ := by positivity
  refine ⟨epsP D r hr p / (S.Csrc + 1), by positivity, C₁ + C₂ + C₃, by positivity,
    fun σ hσ => ?_⟩
  obtain ⟨hA, hB, hY⟩ := S.src_mem σ
  obtain ⟨hAr, hBr, hYr⟩ := S.src_real σ
  have hsmallP : ∀ {a : ℝ}, a ≤ S.Csrc * S.seedSqP σ → a ≤ epsP D r hr p := by
    intro a ha
    refine ha.trans ?_
    have h1 : S.Csrc * S.seedSqP σ ≤ S.Csrc * (epsP D r hr p / (S.Csrc + 1)) :=
      mul_le_mul_of_nonneg_left hσ hcs
    have h2 : S.Csrc * (epsP D r hr p / (S.Csrc + 1)) ≤ epsP D r hr p := by
      rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have hη := hsmallP (S.src_smallP σ)
  have hle : r ≤ r + p := by omega
  have hA' := memH_mono hle hA; have hB' := memH_mono hle hB; have hY' := memH_mono hle hY
  have hseed0 : 0 ≤ S.seedSqP σ := (S.seedSq_nonneg σ).trans (S.seedSq_le σ)
  -- the exact solution, through `finite_conformal` at `N = 1`
  obtain ⟨hAN1, hBN1, hYN1⟩ := S.fin_mem 1 σ
  obtain ⟨u, -, ⟨hureg, hfix, huM, hubd, huniq⟩, -, -, -⟩ := finite_conformal D r hr p 1 le_rfl
    hA hB hY hAN1 hBN1 hYN1 hη (hsmallP (S.fin_smallP 1 σ))
  have hu := memH_mono (by omega : r + 2 ≤ r + p + 2) hureg
  have hsm := sup_lt_half D r hr hu huM
  have hE := hamiltonianEq_of_fixed D r hr hA' hB' hY' hu hfix hsm
  have hureal := im_eq_zero_of_unique D r hr hu huM hfix
    (conjCT_Tmap D r hr hA' hB' hY' hAr hBr hYr hu) huniq
  have hrealw : ∀ (v : CT), (∀ x, (v x).im = 0) → (∀ x, ‖v x‖ < 1 / 2) →
      ∀ x, ((1 + v) x).im = 0 ∧ 1 / 2 < ((1 + v) x).re ∧ ((1 + v) x).re < 3 / 2 := by
    intro v him hs x
    have hre' := abs_lt.mp (lt_of_le_of_lt (Complex.abs_re_le_norm (v x)) (hs x))
    simp only [ContinuousMap.add_apply, ContinuousMap.one_apply, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im, him x]
    exact ⟨by ring, by linarith, by linarith⟩
  have hw1 : (1 + u) - 1 = u := add_sub_cancel_left 1 u
  have hmem1 : MemH (r + p + 2) ⇑(1 : CT) := memH_const _ 1
  refine ⟨1 + u, memH_add hmem1 hureg, hE, ?_, ?_, hrealw u hureal hsm, fun N hN => ?_⟩
  · refine (S.conformal σ (1 + u) fun x h => ?_).2 hE
    have := hsm x
    have e : u x = -1 := by
      have : (1 + u) x = 1 + u x := rfl
      rw [this] at h; linear_combination h
    rw [e, norm_neg, norm_one] at this; norm_num at this
  · rw [hw1]
    refine hubd.trans ?_
    have := S.src_smallP σ
    calc 2 * cL D * (sn (r + p) ⇑(S.srcA σ) + sn (r + p) ⇑(S.srcB σ) + sn (r + p) ⇑(S.srcY σ))
        ≤ 2 * cL D * (S.Csrc * S.seedSqP σ) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = C₁ * S.seedSqP σ := by ring
      _ ≤ (C₁ + C₂ + C₃) * S.seedSqP σ := by gcongr; linarith
  -- the finite conformal factor
  obtain ⟨hAN, hBN, hYN⟩ := S.fin_mem N σ
  obtain ⟨hANr, hBNr, hYNr⟩ := S.fin_real N σ
  have hAN' := memH_mono hle hAN; have hBN' := memH_mono hle hBN; have hYN' := memH_mono hle hYN
  obtain ⟨u', uN, ⟨hu'reg, hfix', hu'M, -, -⟩, ⟨huNreg, hprojN, hfixN, huNM, huNbd, huniqN⟩,
    hrate, hresid⟩ := finite_conformal D r hr p N hN hA hB hY hAN hBN hYN hη
      (hsmallP (S.fin_smallP N σ))
  have hu'u : u' = u := huniq u' (memH_mono (by omega) hu'reg) hu'M hfix'
  rw [hu'u] at hrate
  have huN := memH_mono (by omega : r + 2 ≤ r + p + 2) huNreg
  have hsmN := sup_lt_half D r hr huN huNM
  have hη2 := S.src_smallP σ
  have hηN2 := S.fin_smallP N σ
  have hrateS := S.fin_rate N σ hN
  have hNp : 0 < ((N : ℝ) ^ p)⁻¹ := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  refine ⟨1 + uN, ?_, memH_add hmem1 huNreg, ?_, ?_, ?_, ?_⟩
  · -- `w_N ∈ Ran P_N`
    have hc : proj N (1 : CT) = 1 := by
      refine coeff_ext fun n => ?_
      rw [mFourierCoeff_proj]
      have h1 : (1 : CT) = ContinuousMap.const _ 1 := rfl
      rw [h1, mFourierCoeff_const]
      split_ifs with hb hn hn
      · rfl
      · rfl
      · exact absurd (hn ▸ (TorusFourierTruncation.mem_box.mpr fun i => by simp)) hb
      · rfl
    rw [proj_add, hc, hprojN]
  · rw [add_sub_cancel_left]
    refine huNbd.trans ?_
    calc 2 * cL D * (sn (r + p) ⇑(S.srcAN N σ) + sn (r + p) ⇑(S.srcBN N σ) +
          sn (r + p) ⇑(S.srcYN N σ))
        ≤ 2 * cL D * (S.Csrc * S.seedSqP σ) := mul_le_mul_of_nonneg_left hηN2 (by positivity)
      _ = C₁ * S.seedSqP σ := by ring
      _ ≤ (C₁ + C₂ + C₃) * S.seedSqP σ := by gcongr; linarith
  · have e : (1 + uN) - (1 + u) = uN - u := by abel
    rw [e]
    refine hrate.trans ?_
    have hA2 : 2 * cL D * (sn (r + p) ⇑(S.srcA σ) + sn (r + p) ⇑(S.srcB σ) +
        sn (r + p) ⇑(S.srcY σ)) ≤ 2 * cL D * (S.Csrc * S.seedSqP σ) :=
      mul_le_mul_of_nonneg_left hη2 (by positivity)
    have hB2 : cL D * AlgNorm.srcC (algK r hr) * (sn r ⇑(S.srcAN N σ - S.srcA σ) +
        sn r ⇑(S.srcBN N σ - S.srcB σ) + sn r ⇑(S.srcYN N σ - S.srcY σ)) ≤
        cL D * AlgNorm.srcC (algK r hr) * (S.Cfin * S.seedSqP σ * ((N : ℝ) ^ p)⁻¹) :=
      mul_le_mul_of_nonneg_left hrateS (by positivity)
    calc 2 * (cL D * AlgNorm.srcC (algK r hr) * (sn r ⇑(S.srcAN N σ - S.srcA σ) +
          sn r ⇑(S.srcBN N σ - S.srcB σ) + sn r ⇑(S.srcYN N σ - S.srcY σ)) +
          ((N : ℝ) ^ p)⁻¹ * (2 * cL D * (sn (r + p) ⇑(S.srcA σ) + sn (r + p) ⇑(S.srcB σ) +
            sn (r + p) ⇑(S.srcY σ))))
        ≤ 2 * (cL D * AlgNorm.srcC (algK r hr) * (S.Cfin * S.seedSqP σ * ((N : ℝ) ^ p)⁻¹) +
          ((N : ℝ) ^ p)⁻¹ * (2 * cL D * (S.Csrc * S.seedSqP σ))) := by
          gcongr
      _ = C₂ * S.seedSqP σ * ((N : ℝ) ^ p)⁻¹ := by ring
      _ ≤ (C₁ + C₂ + C₃) * S.seedSqP σ * ((N : ℝ) ^ p)⁻¹ := by
          gcongr; linarith
  · have him := im_eq_zero_of_unique D r hr huN huNM hfixN
      (conjCT_TmapN D r hr N hAN' hBN' hYN' hANr hBNr hYNr huN) huniqN
    exact hrealw uN him hsmN
  · intro x
    have hρ : MemH r ⇑((-8 : ℂ) • lap uN + (D.μ : ℂ) • uN - PhiF D (S.srcAN N σ) (S.srcBN N σ)
        (S.srcYN N σ) uN) :=
      memH_sub (memH_add (memH_smul _ (lap_spec hr huN).1) (memH_smul _ (memH_mono (by omega) huN)))
        (memH_PhiF D r hr hAN' hBN' hYN' huN)
    refine (norm_hamRes_le D r hr huN hsmN hρ x).trans ?_
    have hb : 2 ^ 7 * (Real.sqrt cEmb * sn r ⇑((-8 : ℂ) • lap uN + (D.μ : ℂ) • uN -
        PhiF D (S.srcAN N σ) (S.srcBN N σ) (S.srcYN N σ) uN)) ≤
        2 ^ 7 * (Real.sqrt cEmb * (((N : ℝ) ^ p)⁻¹ * resB D r hr p)) := by
      gcongr
    refine hb.trans ?_
    calc 2 ^ 7 * (Real.sqrt cEmb * (((N : ℝ) ^ p)⁻¹ * resB D r hr p))
        = C₃ * ((N : ℝ) ^ p)⁻¹ := by ring
      _ ≤ (C₁ + C₂ + C₃) * ((N : ℝ) ^ p)⁻¹ := by gcongr; linarith

end ConstrainedInitialSolver

/-! ### Non-vacuity -/

/-- A background with `A = 1`, `G = B = 0` (so `C = 1`, `μ = 12`). -/
def exampleData : LichData where
  A := 1
  G := 0
  B := 0
  C := 1
  μ := 12
  hC := by norm_num
  hμ := by norm_num
  μ_pos := by norm_num

theorem sn_zero_CT (s : ℕ) : sn s ⇑(0 : CT) = 0 := by
  simp [sn, trigSobSq, mFourierCoeff_zero']

/-- **Non-vacuity of `ConstrainedInitialSolver`** with nonzero sources: seeds `σ ∈ ℝ`, constant
real source `δA = σ²`, `δB = Y = 0`, the exact solver as finite solver, and the scalar equation
as the constraint system. -/
noncomputable def exampleSolver (r p : ℕ) : ConstrainedInitialSolver exampleData r p ℝ where
  seedSq σ := σ ^ 2
  seedSqP σ := σ ^ 2
  seedSq_nonneg σ := sq_nonneg σ
  seedSq_le _ := le_rfl
  srcA σ := ContinuousMap.const _ ((σ ^ 2 : ℝ) : ℂ)
  srcB _ := 0
  srcY _ := 0
  src_real σ := ⟨by ext; simp, by ext; simp, by ext; simp⟩
  src_mem σ := ⟨memH_const _ _, memH_zero _, memH_zero _⟩
  Csrc := 1
  Csrc_nonneg := zero_le_one
  src_small σ := by
    rw [sn_const, sn_zero_CT, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg σ)]
    simp
  src_smallP σ := by
    rw [sn_const, sn_zero_CT, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg σ)]
    simp
  Constraints σ w := HamiltonianEq exampleData (ContinuousMap.const _ ((σ ^ 2 : ℝ) : ℂ)) 0 0 w
  conformal _ _ _ := Iff.rfl
  srcAN _ σ := ContinuousMap.const _ ((σ ^ 2 : ℝ) : ℂ)
  srcBN _ _ := 0
  srcYN _ _ := 0
  fin_real _ σ := ⟨by ext; simp, by ext; simp, by ext; simp⟩
  fin_mem _ σ := ⟨memH_const _ _, memH_zero _, memH_zero _⟩
  fin_smallP _ σ := by
    rw [sn_const, sn_zero_CT, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg σ)]
    simp
  Cfin := 0
  Cfin_nonneg := le_rfl
  fin_rate _ _ _ := by simp only [sub_self, sn_zero_CT]; norm_num

/-- The hypotheses of `prop:generated-initial` are jointly satisfiable with nonzero sources, and
the conclusion is then available. -/
example : ∃ ε > 0, ∃ ρ > 0, ∃ C ≥ 0, ∀ σ : ℝ, (exampleSolver 2 1).seedSq σ ≤ ε →
    ∃ w : CT, MemH (2 + 2) ⇑w ∧
      HamiltonianEq exampleData ((exampleSolver 2 1).srcA σ) 0 0 w ∧
      (exampleSolver 2 1).Constraints σ w ∧ sn (2 + 2) ⇑(w - 1) ≤ C * σ ^ 2 ∧
      (∀ x, (w x).im = 0 ∧ 1 / 2 < (w x).re ∧ (w x).re < 3 / 2) ∧
      ∀ w' : CT, MemH (2 + 2) ⇑w' → sn (2 + 2) ⇑(w' - 1) ≤ ρ →
        HamiltonianEq exampleData ((exampleSolver 2 1).srcA σ) 0 0 w' → w' = w :=
  (exampleSolver 2 1).generated_initial le_rfl

end RenewalGeometry.LichnerowiczContraction
