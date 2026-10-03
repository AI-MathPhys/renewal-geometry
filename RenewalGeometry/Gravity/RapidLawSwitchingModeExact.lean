/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.RapidLawSwitching
import RenewalGeometry.Gravity.SupplementLawMultiplierExact

/-!
# Rapid switching is not included: the corner mode of the actual law family
  (`prop:supp-law-switching`, `eq:supp-law-dispersion`, `eq:supp-law-family`,
  `eq:supp-law-laplacian`; emergent-spacetime manuscript)

`RenewalGeometry.Gravity.RapidLawSwitching` treats the abstract oscillator `q'' = -Ω² q`; there
`cornerFrequencySq σ ℓ h = ℓ (1 + σ h² ℓ)` is a *definition*.  This file derives the dispersion
relation from the law family and links the oscillator to the writer.

## The law family on a Fourier mode

On the periodic grid `(hℤ/ℤ)³ = (ZMod N)³` (`h = 1/N`) the flat linearised scalar law of
`eq:supp-law-family` with mark `B = σ I` (`a = I`, `c^{ij} = δ^{ij}` so that
`Σ D_i^-(c^{ij} D_j^+ q) = -Λ_h q`, linearised: `𝖪_b v`, `𝖦_h` dropped) is
`q_t = v`, `v_t = -Λ_h q - σ h² Λ_h² q` (`flatLaw`), with `Λ_h = -Σ_i D_i^- D_i^+` the grid
Laplacian of `RenewalGeometry.Gravity.SupplementLawMultiplierExact` (`gridLaplacian`).

* `fourierMode k` — the grid Fourier mode `e_k(n) = exp(2πi k·n/N)` (an additive character).
* `gridLaplacian_fourierMode` — **the Fourier symbol**: `Λ_h e_k = ℓ_h(k) e_k` with
  `ℓ_h(k) = 4h⁻² Σ_i sin²(π h k_i)` (`laplaceSymbol`).
* `flatLaw_fourierMode` — **`eq:supp-law-dispersion` derived**: the law acts on `e_k` by
  `-Ω_{σ,h}(k)²` with `Ω² = ℓ_h(k)(1 + σ h² ℓ_h(k))`.
* `modeSolution_isLawSolution` — `(c(t) e_k, c'(t) e_k)` with the oscillator `c` solves the law;
  `lawSolution_unique` — solutions of the (linear, Lipschitz) law are unique.
* `law_quarter_transfer` — **the transfer matrix is the solution map**: every solution of the law
  with data `(a e_k, b e_k)` is at the quarter period `(T *ᵥ (a, b)) · e_k`,
  `T = [[0, Ω⁻¹], [-Ω, 0]]`.
* `law_switching_cycles` — for any switched history (law `σ₁` held a quarter period, then `σ₂`,
  repeated, with continuous state), the corner-mode state after `n` cycles is
  `(T₂T₁)ⁿ *ᵥ (a, b)`, and `two_step_pow_basis_amplitude` gives modulus `ρⁿ`,
  `ρ = max(Ω₁/Ω₂, Ω₂/Ω₁)`, for a unit initial datum.

## The ultraviolet corner on odd grids

For `N = 2m + 1`, `h = 1/N`, the corner mode `k = (m, m, m)` has
`h² ℓ_h(k) = 12 sin²(π m/(2m+1))`: `cornerSymbol_lt_twelve` (never `= 12` on odd grids),
`cornerSymbol_ge_nine`, `tendsto_cornerSymbol` (`→ 12`).  For distinct admissible marks
(`|σᵢ| < 1/24`, the open writer ball for the flat chart `c = I`, `c_* = 1`):
`corner_ratio_separated` — `Ω₁²/Ω₂²` stays uniformly separated from `1` for all large `m`;
`rapid_switching_not_included` — **`prop:supp-law-switching`**: there are `c, C, K > 0` and `m₀`
such that on every odd grid `m ≥ m₀` the two quarter periods sum to at most `K h`, and the
switched history on a slab `[0, T]` (`⌊T/(τ₁ + τ₂)⌋` full cycles) amplifies a unit corner-mode
datum by at least `C exp(c T / h)`.
-/

open scoped BigOperators Real
open Filter Topology Set Matrix

namespace RenewalGeometry
namespace LawSwitchingMode

open LawMultiplier

variable {N : ℕ} [NeZero N]

/-! ### Grid Fourier modes and the symbol of `Λ_h` -/

/-- The grid Fourier mode `e_k(n) = exp(2πi Σ_i k_i n_i / N)` on `(ZMod N)³`. -/
noncomputable def fourierMode (k : Fin 3 → ℤ) (n : PeriodicGrid N) : ℂ :=
  ZMod.stdAddChar (∑ i, (k i : ZMod N) * n i)

theorem sum_mul_add_single (k : Fin 3 → ℤ) (n : PeriodicGrid N) (j : Fin 3) (s : ZMod N) :
    ∑ i, (k i : ZMod N) * (n + (Pi.single j s : PeriodicGrid N)) i = ∑ i, (k i : ZMod N) * n i + (k j : ZMod N) * s := by
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij; simp [Pi.single_apply, hij]
  · simp

theorem fourierMode_add_step (k : Fin 3 → ℤ) (n : PeriodicGrid N) (j : Fin 3) :
    fourierMode k (n + unitStep N j) = ZMod.stdAddChar (k j : ZMod N) * fourierMode k n := by
  unfold fourierMode unitStep
  rw [sum_mul_add_single, mul_one, AddChar.map_add_eq_mul, mul_comm]

theorem fourierMode_sub_step (k : Fin 3 → ℤ) (n : PeriodicGrid N) (j : Fin 3) :
    fourierMode k (n - unitStep N j) = ZMod.stdAddChar (-(k j : ZMod N)) * fourierMode k n := by
  unfold fourierMode unitStep
  rw [sub_eq_add_neg, ← Pi.single_neg, sum_mul_add_single, AddChar.map_add_eq_mul, mul_comm,
    mul_neg, mul_one]

/-- `ω + ω⁻¹ - 2 = -4 sin²(π j/N)` for `ω = exp(2πi j/N)`. -/
theorem stdAddChar_add_neg_sub_two (j : ℤ) :
    ZMod.stdAddChar (j : ZMod N) + ZMod.stdAddChar (-(j : ZMod N)) - 2
      = ((-4 * Real.sin (π * j / N) ^ 2 : ℝ) : ℂ) := by
  set θ : ℝ := 2 * π * j / N with hθ
  have e1 : ZMod.stdAddChar (j : ZMod N) = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [ZMod.stdAddChar_coe, hθ]; push_cast; ring_nf
  have e2 : ZMod.stdAddChar (-(j : ZMod N)) = Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) := by
    rw [show (-(j : ZMod N)) = ((-j : ℤ) : ZMod N) by push_cast; ring, ZMod.stdAddChar_coe, hθ]
    push_cast; ring_nf
  rw [e1, e2, Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
  have hc : Real.cos θ = 1 - 2 * Real.sin (π * j / N) ^ 2 := by
    rw [show θ = 2 * (π * j / N) by rw [hθ]; ring, Real.cos_two_mul, Real.cos_sq']
    ring
  rw [hc]
  push_cast
  ring

/-- The grid spacing `h = 1/N`. -/
noncomputable def spacing (N : ℕ) : ℝ := (N : ℝ)⁻¹

/-- The symbol `ℓ_h(k)` of the mode `k` at `h = 1/N`. -/
noncomputable def modeSymbol (N : ℕ) (k : Fin 3 → ℤ) : ℝ :=
  laplaceSymbol (spacing N) (fun i => (k i : ℝ))

/-- **The Fourier symbol of `Λ_h`**: `Λ_h e_k = ℓ_h(k) e_k` on `(ZMod N)³`, `h = 1/N`. -/
theorem gridLaplacian_fourierMode (k : Fin 3 → ℤ) (x : PeriodicGrid N) :
    gridLaplacian (spacing N) (unitStep N) (fourierMode k) x
      = (modeSymbol N k : ℂ) * fourierMode k x := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  unfold gridLaplacian backwardDiff forwardDiff
  simp only [sub_add_cancel, fourierMode_add_step, fourierMode_sub_step, Complex.real_smul]
  have hterm : ∀ i : Fin 3,
      ((spacing N)⁻¹ : ℂ) * (((spacing N)⁻¹ : ℂ) *
          (ZMod.stdAddChar (k i : ZMod N) * fourierMode k x - fourierMode k x) -
        ((spacing N)⁻¹ : ℂ) * (fourierMode k x -
          ZMod.stdAddChar (-(k i : ZMod N)) * fourierMode k x))
      = ((N : ℝ) : ℂ) ^ 2 * ((-4 * Real.sin (π * (k i) / N) ^ 2 : ℝ) : ℂ) * fourierMode k x := by
    intro i
    rw [← stdAddChar_add_neg_sub_two (N := N) (k i)]
    simp only [spacing, Complex.ofReal_inv, inv_inv]
    ring
  push_cast at hterm ⊢
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  unfold modeSymbol laplaceSymbol spacing
  push_cast
  rw [inv_inv, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (π : ℂ) * (N : ℂ)⁻¹ * (k i : ℂ) = π * (k i) / N := by ring
  rw [this]
  ring

/-! ### The flat linearised law on the grid -/

/-- `Λ_h` as an `ℝ`-linear map on complex grid arrays. -/
noncomputable def lapLin (N : ℕ) [NeZero N] :
    (PeriodicGrid N → ℂ) →ₗ[ℝ] (PeriodicGrid N → ℂ) where
  toFun := gridLaplacian (spacing N) (unitStep N)
  map_add' u v := by
    funext x
    simp only [gridLaplacian, backwardDiff, forwardDiff, Pi.add_apply, Complex.real_smul]
    rw [← neg_add, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  map_smul' c u := by
    funext x
    simp only [gridLaplacian, backwardDiff, forwardDiff, Pi.smul_apply, RingHom.id_apply,
      Complex.real_smul]
    rw [mul_neg, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring

/-- **The flat linearised law** of `eq:supp-law-family` with mark `B = σ I`:
`v_t = -Λ_h q - σ h² Λ_h² q` (`a = I`, `c = I`, `h = 1/N`). -/
noncomputable def flatLaw (N : ℕ) [NeZero N] (σ : ℝ) :
    (PeriodicGrid N → ℂ) →ₗ[ℝ] (PeriodicGrid N → ℂ) :=
  -lapLin N - (σ * spacing N ^ 2) • (lapLin N ∘ₗ lapLin N)

theorem lapLin_fourierMode (k : Fin 3 → ℤ) :
    lapLin N (fourierMode k) = modeSymbol N k • fourierMode k := by
  funext x
  show gridLaplacian (spacing N) (unitStep N) (fourierMode k) x = _
  rw [gridLaplacian_fourierMode, Pi.smul_apply, Complex.real_smul]

/-- **`eq:supp-law-dispersion`, derived**: the flat law acts on the Fourier mode `e_k` by
`-Ω_{σ,h}(k)²` with `Ω² = ℓ_h(k) (1 + σ h² ℓ_h(k))`. -/
theorem flatLaw_fourierMode (σ : ℝ) (k : Fin 3 → ℤ) :
    flatLaw N σ (fourierMode k)
      = -cornerFrequencySq σ (modeSymbol N k) (spacing N) • fourierMode k := by
  unfold flatLaw cornerFrequencySq
  simp only [LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, lapLin_fourierMode, map_smul, smul_smul]
  rw [← neg_smul, ← sub_smul]
  congr 1
  ring

/-! ### Solutions of the law, uniqueness and the quarter-period transfer -/

/-- `(q, p)` solves the law `σ` on `[0, τ]`: `q' = p`, `p' = flatLaw σ q`. -/
def IsLawSolution (N : ℕ) [NeZero N] (σ : ℝ) (q p : ℝ → PeriodicGrid N → ℂ) (τ : ℝ) : Prop :=
  ∀ t ∈ Icc 0 τ, HasDerivAt q (p t) t ∧ HasDerivAt p (flatLaw N σ (q t)) t

/-- The law as a continuous linear vector field on the state space `(q, p)`. -/
noncomputable def lawField (N : ℕ) [NeZero N] (σ : ℝ) :
    (PeriodicGrid N → ℂ) × (PeriodicGrid N → ℂ) →L[ℝ] (PeriodicGrid N → ℂ) × (PeriodicGrid N → ℂ) :=
  (ContinuousLinearMap.snd ℝ _ _).prod
    ((LinearMap.toContinuousLinearMap (flatLaw N σ)).comp (ContinuousLinearMap.fst ℝ _ _))

theorem lawField_apply (σ : ℝ) (y : (PeriodicGrid N → ℂ) × (PeriodicGrid N → ℂ)) :
    lawField N σ y = (y.2, flatLaw N σ y.1) := rfl

/-- **Uniqueness**: two solutions of the law `σ` on `[0, τ]` with the same initial state agree
on `[0, τ]` (the law is linear, hence Lipschitz, on the finite-dimensional state space). -/
theorem lawSolution_unique (σ τ : ℝ) {q p q' p' : ℝ → PeriodicGrid N → ℂ}
    (h : IsLawSolution N σ q p τ) (h' : IsLawSolution N σ q' p' τ)
    (hq : q 0 = q' 0) (hp : p 0 = p' 0) :
    ∀ t ∈ Icc 0 τ, q t = q' t ∧ p t = p' t := by
  have hder : ∀ {q p : ℝ → PeriodicGrid N → ℂ}, IsLawSolution N σ q p τ → ∀ t ∈ Icc 0 τ,
      HasDerivAt (fun t => (q t, p t)) (lawField N σ (q t, p t)) t := by
    intro q p hs t ht
    exact (hs t ht).1.prodMk (hs t ht).2
  have heq := ODE_solution_unique (v := fun _ => lawField N σ) (K := ‖lawField N σ‖₊)
    (f := fun t => (q t, p t)) (g := fun t => (q' t, p' t)) (a := 0) (b := τ)
    (fun _ => (lawField N σ).lipschitz)
    (fun t ht => (hder h t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hder h t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => (hder h' t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hder h' t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (by simp [hq, hp])
  intro t ht
  have := heq ht
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

/-- The mode solution `(c(t) e_k, c'(t) e_k)` with `c` the oscillator of frequency
`Ω = √(Ω²)` and data `(a, b)`. -/
theorem modeSolution_isLawSolution (σ : ℝ) (k : Fin 3 → ℤ)
    (hpos : 0 < cornerFrequencySq σ (modeSymbol N k) (spacing N)) (a b τ : ℝ) :
    IsLawSolution N σ
      (fun t => oscillatorSolution (Real.sqrt (cornerFrequencySq σ (modeSymbol N k) (spacing N)))
        a b t • fourierMode k)
      (fun t => oscillatorVelocity (Real.sqrt (cornerFrequencySq σ (modeSymbol N k) (spacing N)))
        a b t • fourierMode k) τ := by
  set Ω := Real.sqrt (cornerFrequencySq σ (modeSymbol N k) (spacing N)) with hΩ
  have hΩ0 : Ω ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hΩsq : Ω ^ 2 = cornerFrequencySq σ (modeSymbol N k) (spacing N) := Real.sq_sqrt hpos.le
  intro t _
  refine ⟨(oscillatorSolution_hasDerivAt Ω a b t hΩ0).smul_const _, ?_⟩
  have h := (oscillatorVelocity_hasDerivAt Ω a b t).smul_const (fourierMode (N := N) k)
  refine h.congr_deriv ?_
  rw [map_smul, flatLaw_fourierMode, smul_smul, hΩsq]
  congr 1
  ring

/-- **The transfer matrix is the solution map of the law** (`prop:supp-law-switching`): every
solution of the law `σ` on `[0, π/(2Ω)]` with initial state `(a e_k, b e_k)` reaches
`((T *ᵥ (a, b))₀ e_k, (T *ᵥ (a, b))₁ e_k)` at the quarter period, `T = quarterPeriodTransfer Ω`,
`Ω = Ω_{σ,h}(k)`. -/
theorem law_quarter_transfer (σ : ℝ) (k : Fin 3 → ℤ)
    (hpos : 0 < cornerFrequencySq σ (modeSymbol N k) (spacing N)) (a b : ℝ)
    {q p : ℝ → PeriodicGrid N → ℂ}
    (hsol : IsLawSolution N σ q p
      (quarterPeriod (Real.sqrt (cornerFrequencySq σ (modeSymbol N k) (spacing N)))))
    (hq0 : q 0 = a • fourierMode k) (hp0 : p 0 = b • fourierMode k) :
    let Ω := Real.sqrt (cornerFrequencySq σ (modeSymbol N k) (spacing N))
    q (quarterPeriod Ω) = (quarterPeriodTransfer Ω *ᵥ ![a, b]) 0 • fourierMode k ∧
    p (quarterPeriod Ω) = (quarterPeriodTransfer Ω *ᵥ ![a, b]) 1 • fourierMode k := by
  intro Ω
  have hΩpos : 0 < Ω := Real.sqrt_pos.mpr hpos
  have hτ : 0 ≤ quarterPeriod Ω := by unfold quarterPeriod; positivity
  have hmode := modeSolution_isLawSolution σ k hpos a b (quarterPeriod Ω)
  have huniq := lawSolution_unique σ (quarterPeriod Ω) hsol hmode
    (by simp [hq0, oscillatorSolution_zero]) (by simp [hp0, oscillatorVelocity_zero])
    (quarterPeriod Ω) ⟨hτ, le_rfl⟩
  rw [huniq.1, huniq.2, quarterPeriodTransfer_mulVec Ω a b hΩpos.ne']
  constructor <;> simp [Ω]


/-! ### Switched histories -/

theorem vec_two_eq (s : Fin 2 → ℝ) : s = ![s 0, s 1] := by
  ext i; fin_cases i <;> rfl

/-- **Switched histories.**  Let law `σ₁` be held on `[0, τ₁]` and then law `σ₂` on
`[0, τ₂]` (`τᵢ = π/(2Ωᵢ)` the quarter periods of the mode `k`), repeatedly, with the state
carried over at each switch: `(qa n, pa n)` solves law `σ₁`, `(qb n, pb n)` solves law `σ₂`,
`(qb n, pb n)(0) = (qa n, pa n)(τ₁)`, `(qa (n+1), pa (n+1))(0) = (qb n, pb n)(τ₂)`.  If the
initial state is `(s₀ 0 · e_k, s₀ 1 · e_k)`, then after `n` cycles the state is
`((Pⁿ *ᵥ s₀)₀ e_k, (Pⁿ *ᵥ s₀)₁ e_k)` with `P = T(Ω₂) T(Ω₁)`. -/
theorem law_switching_cycles (σ₁ σ₂ : ℝ) (k : Fin 3 → ℤ)
    (h₁ : 0 < cornerFrequencySq σ₁ (modeSymbol N k) (spacing N))
    (h₂ : 0 < cornerFrequencySq σ₂ (modeSymbol N k) (spacing N))
    (qa pa qb pb : ℕ → ℝ → PeriodicGrid N → ℂ)
    (hsa : ∀ n, IsLawSolution N σ₁ (qa n) (pa n)
      (quarterPeriod (Real.sqrt (cornerFrequencySq σ₁ (modeSymbol N k) (spacing N)))))
    (hsb : ∀ n, IsLawSolution N σ₂ (qb n) (pb n)
      (quarterPeriod (Real.sqrt (cornerFrequencySq σ₂ (modeSymbol N k) (spacing N)))))
    (hab : ∀ n, qb n 0 = qa n (quarterPeriod (Real.sqrt (cornerFrequencySq σ₁ (modeSymbol N k)
        (spacing N)))) ∧
      pb n 0 = pa n (quarterPeriod (Real.sqrt (cornerFrequencySq σ₁ (modeSymbol N k) (spacing N)))))
    (hba : ∀ n, qa (n + 1) 0 = qb n (quarterPeriod (Real.sqrt (cornerFrequencySq σ₂
        (modeSymbol N k) (spacing N)))) ∧
      pa (n + 1) 0 = pb n (quarterPeriod (Real.sqrt (cornerFrequencySq σ₂ (modeSymbol N k)
        (spacing N)))))
    (s₀ : Fin 2 → ℝ) (hq0 : qa 0 0 = s₀ 0 • fourierMode k) (hp0 : pa 0 0 = s₀ 1 • fourierMode k) :
    ∀ n, qa n 0 = (((quarterPeriodTransfer (Real.sqrt (cornerFrequencySq σ₂ (modeSymbol N k)
        (spacing N))) * quarterPeriodTransfer (Real.sqrt (cornerFrequencySq σ₁ (modeSymbol N k)
        (spacing N)))) ^ n) *ᵥ s₀) 0 • fourierMode k ∧
      pa n 0 = (((quarterPeriodTransfer (Real.sqrt (cornerFrequencySq σ₂ (modeSymbol N k)
        (spacing N))) * quarterPeriodTransfer (Real.sqrt (cornerFrequencySq σ₁ (modeSymbol N k)
        (spacing N)))) ^ n) *ᵥ s₀) 1 • fourierMode k := by
  set T₁ := quarterPeriodTransfer (Real.sqrt (cornerFrequencySq σ₁ (modeSymbol N k) (spacing N)))
  set T₂ := quarterPeriodTransfer (Real.sqrt (cornerFrequencySq σ₂ (modeSymbol N k) (spacing N)))
  intro n
  induction n with
  | zero => simp [hq0, hp0]
  | succ n ih =>
    set s := ((T₂ * T₁) ^ n) *ᵥ s₀ with hs
    have hA := law_quarter_transfer σ₁ k h₁ (s 0) (s 1) (hsa n) ih.1 ih.2
    have hB := law_quarter_transfer σ₂ k h₂ ((T₁ *ᵥ ![s 0, s 1]) 0) ((T₁ *ᵥ ![s 0, s 1]) 1)
      (hsb n) ((hab n).1.trans hA.1) ((hab n).2.trans hA.2)
    have key : ((T₂ * T₁) ^ (n + 1)) *ᵥ s₀
        = T₂ *ᵥ ![(T₁ *ᵥ ![s 0, s 1]) 0, (T₁ *ᵥ ![s 0, s 1]) 1] := by
      rw [← vec_two_eq, ← vec_two_eq, Matrix.mulVec_mulVec, pow_succ', ← Matrix.mulVec_mulVec]
    rw [key, (hba n).1, (hba n).2]
    exact hB

/-- The `n`-cycle amplitude: for the unit datum `e₀` or `e₁` (whichever matches the larger
ratio), one component of `Pⁿ *ᵥ s₀` has modulus `ρⁿ`, `ρ = max(Ω₁/Ω₂, Ω₂/Ω₁)`. -/
theorem two_step_pow_basis_amplitude (Ω₁ Ω₂ : ℝ) (h₁ : 0 < Ω₁) (h₂ : 0 < Ω₂) :
    ∃ i : Fin 2, ∀ n : ℕ,
      |(((quarterPeriodTransfer Ω₂ * quarterPeriodTransfer Ω₁) ^ n) *ᵥ Pi.single i 1) i|
        = max (Ω₁ / Ω₂) (Ω₂ / Ω₁) ^ n := by
  have hP : ∀ n, (quarterPeriodTransfer Ω₂ * quarterPeriodTransfer Ω₁) ^ n
      = Matrix.diagonal (![-(Ω₁ / Ω₂), -(Ω₂ / Ω₁)] ^ n) := by
    intro n; rw [quarterPeriodTransfer_two_step, Matrix.diagonal_pow]
  rcases le_total (Ω₂ / Ω₁) (Ω₁ / Ω₂) with hle | hle
  · refine ⟨0, fun n => ?_⟩
    rw [hP, Matrix.mulVec_diagonal, max_eq_left hle]
    simp [abs_pow, abs_of_pos (div_pos h₁ h₂)]
  · refine ⟨1, fun n => ?_⟩
    rw [hP, Matrix.mulVec_diagonal, max_eq_right hle]
    simp [abs_pow, abs_of_pos (div_pos h₂ h₁)]

/-! ### The ultraviolet corner on odd grids -/

/-- The corner mode `k = (m, m, m)` of the odd grid `N = 2m + 1`. -/
def cornerMode (m : ℕ) : Fin 3 → ℤ := fun _ => m

/-- `h² ℓ_h(k_corner) = 12 sin²(π m/(2m+1))`. -/
theorem cornerSymbol_eq (m : ℕ) :
    spacing (2 * m + 1) ^ 2 * modeSymbol (2 * m + 1) (cornerMode m)
      = 12 * Real.sin (π * m / (2 * m + 1)) ^ 2 := by
  unfold modeSymbol laplaceSymbol spacing cornerMode
  have hN : ((2 * m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [Fin.sum_univ_three]
  have : π * (((2 * m + 1 : ℕ) : ℝ))⁻¹ * ((m : ℤ) : ℝ) = π * m / (2 * m + 1) := by
    push_cast; ring
  simp only [this]
  field_simp
  ring

theorem corner_angle_bounds {m : ℕ} (hm : 1 ≤ m) :
    π / 3 ≤ π * m / (2 * m + 1) ∧ π * m / (2 * m + 1) < π / 2 := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpos : (0 : ℝ) < 2 * m + 1 := by positivity
  constructor
  · rw [le_div_iff₀ hpos]; nlinarith [Real.pi_pos]
  · rw [div_lt_iff₀ hpos]; nlinarith [Real.pi_pos]

/-- On odd grids the corner symbol never reaches `12`: `h² ℓ_h(k_corner) < 12`. -/
theorem cornerSymbol_lt_twelve {m : ℕ} (hm : 1 ≤ m) :
    spacing (2 * m + 1) ^ 2 * modeSymbol (2 * m + 1) (cornerMode m) < 12 := by
  rw [cornerSymbol_eq]
  obtain ⟨h1, h2⟩ := corner_angle_bounds hm
  have hs : Real.sin (π * m / (2 * m + 1)) < 1 := by
    have := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos]) le_rfl h2
    rwa [Real.sin_pi_div_two] at this
  have hs0 : 0 ≤ Real.sin (π * m / (2 * m + 1)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  nlinarith

/-- `h² ℓ_h(k_corner) ≥ 9` for `m ≥ 1`. -/
theorem cornerSymbol_ge_nine {m : ℕ} (hm : 1 ≤ m) :
    9 ≤ spacing (2 * m + 1) ^ 2 * modeSymbol (2 * m + 1) (cornerMode m) := by
  rw [cornerSymbol_eq]
  obtain ⟨h1, h2⟩ := corner_angle_bounds hm
  have hs : Real.sin (π / 3) ≤ Real.sin (π * m / (2 * m + 1)) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) h2.le h1
  rw [Real.sin_pi_div_three] at hs
  have h3 : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hs0 : 0 ≤ Real.sqrt 3 / 2 := by positivity
  nlinarith [pow_le_pow_left₀ hs0 hs 2]

/-- **The corner is reached in the limit**: `h² ℓ_h(k_corner) → 12` along odd grids. -/
theorem tendsto_cornerSymbol :
    Tendsto (fun m : ℕ => spacing (2 * m + 1) ^ 2 * modeSymbol (2 * m + 1) (cornerMode m))
      atTop (𝓝 12) := by
  simp_rw [cornerSymbol_eq]
  have hlim : Tendsto (fun m : ℕ => π * m / (2 * m + 1)) atTop (𝓝 (π / 2)) := by
    have hden : Tendsto (fun m : ℕ => 2 * (m : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _
        (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
    have h1 : Tendsto (fun m : ℕ => (2 * (m : ℝ) + 1)⁻¹) atTop (𝓝 0) := hden.inv_tendsto_atTop
    have h2 := (tendsto_const_nhds (x := π / 2)).sub (h1.const_mul (π / 2))
    rw [mul_zero, sub_zero] at h2
    refine h2.congr fun m => ?_
    have hpos : (0 : ℝ) < 2 * m + 1 := by positivity
    field_simp
    ring
  have := (((Real.continuous_sin.tendsto _).comp hlim).pow 2).const_mul 12
  rw [Real.sin_pi_div_two] at this
  simpa using this

/-! ### Admissible marks and the frequencies at the corner -/

/-- `1 + σ x ≥ 1/2` for `|σ| < 1/24`, `0 ≤ x ≤ 12` (the open writer ball for the flat chart). -/
theorem one_add_mul_ge_half {σ x : ℝ} (hσ : |σ| < 1 / 24) (hx0 : 0 ≤ x) (hx : x ≤ 12) :
    1 / 2 ≤ 1 + σ * x := by
  have := abs_lt.mp hσ
  nlinarith

/-- The corner frequency `Ω_{σ,h}(k_corner)` of the odd grid `2m + 1`. -/
noncomputable def cornerOmega (σ : ℝ) (m : ℕ) : ℝ :=
  Real.sqrt (cornerFrequencySq σ (modeSymbol (2 * m + 1) (cornerMode m)) (spacing (2 * m + 1)))

theorem modeSymbol_corner_eq (m : ℕ) :
    modeSymbol (2 * m + 1) (cornerMode m) =
      (spacing (2 * m + 1) ^ 2 * modeSymbol (2 * m + 1) (cornerMode m)) *
        ((2 * m + 1 : ℕ) : ℝ) ^ 2 := by
  have hN : ((2 * m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  unfold spacing
  field_simp

/-- `Ω² ≥ 4 N²` at the corner (`N = 2m + 1`, `m ≥ 1`, admissible `σ`). -/
theorem cornerFrequencySq_ge {σ : ℝ} (hσ : |σ| < 1 / 24) {m : ℕ} (hm : 1 ≤ m) :
    4 * ((2 * m + 1 : ℕ) : ℝ) ^ 2 ≤
      cornerFrequencySq σ (modeSymbol (2 * m + 1) (cornerMode m)) (spacing (2 * m + 1)) := by
  set x := spacing (2 * m + 1) ^ 2 * modeSymbol (2 * m + 1) (cornerMode m) with hx
  have hx9 := cornerSymbol_ge_nine hm
  have hx12 := (cornerSymbol_lt_twelve hm).le
  rw [← hx] at hx9 hx12
  have hhalf := one_add_mul_ge_half hσ (by linarith) hx12
  have hN2 : 0 < ((2 * m + 1 : ℕ) : ℝ) ^ 2 := by positivity
  unfold cornerFrequencySq
  rw [show σ * spacing (2 * m + 1) ^ 2 * modeSymbol (2 * m + 1) (cornerMode m) = σ * x by
    rw [hx]; ring, modeSymbol_corner_eq, ← hx]
  have : 9 * (1 / 2) ≤ x * (1 + σ * x) := mul_le_mul hx9 hhalf (by norm_num) (by linarith)
  nlinarith

theorem cornerFrequencySq_pos {σ : ℝ} (hσ : |σ| < 1 / 24) {m : ℕ} (hm : 1 ≤ m) :
    0 < cornerFrequencySq σ (modeSymbol (2 * m + 1) (cornerMode m)) (spacing (2 * m + 1)) := by
  have := cornerFrequencySq_ge hσ hm
  have : (0 : ℝ) < 4 * ((2 * m + 1 : ℕ) : ℝ) ^ 2 := by positivity
  linarith

theorem cornerOmega_pos {σ : ℝ} (hσ : |σ| < 1 / 24) {m : ℕ} (hm : 1 ≤ m) :
    0 < cornerOmega σ m :=
  Real.sqrt_pos.mpr (cornerFrequencySq_pos hσ hm)

/-- The quarter period at the corner is `O(h)`: `π/(2Ω) ≤ (π/4) h`. -/
theorem cornerQuarterPeriod_le {σ : ℝ} (hσ : |σ| < 1 / 24) {m : ℕ} (hm : 1 ≤ m) :
    quarterPeriod (cornerOmega σ m) ≤ π / 4 * spacing (2 * m + 1) := by
  have hN : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by positivity
  have hΩ : 2 * ((2 * m + 1 : ℕ) : ℝ) ≤ cornerOmega σ m := by
    unfold cornerOmega
    rw [show 2 * ((2 * m + 1 : ℕ) : ℝ) = Real.sqrt (4 * ((2 * m + 1 : ℕ) : ℝ) ^ 2) by
      rw [show 4 * ((2 * m + 1 : ℕ) : ℝ) ^ 2 = (2 * ((2 * m + 1 : ℕ) : ℝ)) ^ 2 by ring,
        Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (cornerFrequencySq_ge hσ hm)
  unfold quarterPeriod spacing
  rw [div_le_iff₀ (by linarith)]
  have hinv : 0 < (((2 * m + 1 : ℕ) : ℝ))⁻¹ := inv_pos.mpr hN
  have : π / 4 * (((2 * m + 1 : ℕ) : ℝ))⁻¹ * (2 * (2 * ((2 * m + 1 : ℕ) : ℝ))) = π := by
    field_simp; ring
  have hmono : π / 4 * (((2 * m + 1 : ℕ) : ℝ))⁻¹ * (2 * (2 * ((2 * m + 1 : ℕ) : ℝ)))
      ≤ π / 4 * (((2 * m + 1 : ℕ) : ℝ))⁻¹ * (2 * cornerOmega σ m) := by
    apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

/-- The squared corner frequency ratio is `(1 + σ₁ x)/(1 + σ₂ x)`, `x = h² ℓ`. -/
theorem cornerRatio_eq {σ₁ σ₂ : ℝ} (hσ₁ : |σ₁| < 1 / 24) (hσ₂ : |σ₂| < 1 / 24) {m : ℕ}
    (hm : 1 ≤ m) :
    cornerOmega σ₁ m ^ 2 / cornerOmega σ₂ m ^ 2 =
      (1 + σ₁ * (spacing (2 * m + 1) ^ 2 * modeSymbol (2 * m + 1) (cornerMode m))) /
        (1 + σ₂ * (spacing (2 * m + 1) ^ 2 * modeSymbol (2 * m + 1) (cornerMode m))) := by
  have hℓ : 0 < modeSymbol (2 * m + 1) (cornerMode m) := by
    rw [modeSymbol_corner_eq]
    have := cornerSymbol_ge_nine hm
    have : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) ^ 2 := by positivity
    positivity
  unfold cornerOmega
  rw [Real.sq_sqrt (cornerFrequencySq_pos hσ₁ hm).le, Real.sq_sqrt (cornerFrequencySq_pos hσ₂ hm).le]
  unfold cornerFrequencySq
  rw [mul_div_mul_left _ _ hℓ.ne']
  ring_nf

/-- **Uniform separation at the corner**: for distinct admissible marks there are `δ > 0` and
`m₀` with `|Ω₁²/Ω₂² - 1| ≥ δ` for all odd grids `m ≥ m₀` (the ratio tends to
`(1 + 12σ₁)/(1 + 12σ₂) ≠ 1`). -/
theorem corner_ratio_separated {σ₁ σ₂ : ℝ} (hσ₁ : |σ₁| < 1 / 24) (hσ₂ : |σ₂| < 1 / 24)
    (hne : σ₁ ≠ σ₂) :
    ∃ δ > 0, ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m ≥ m₀,
      δ ≤ |cornerOmega σ₁ m ^ 2 / cornerOmega σ₂ m ^ 2 - 1| := by
  have h₂ : 0 < 1 + 12 * σ₂ := by have := abs_lt.mp hσ₂; linarith
  set R := (1 + 12 * σ₁) / (1 + 12 * σ₂) with hR
  have hR1 : R ≠ 1 := by
    rw [hR, Ne, div_eq_one_iff_eq h₂.ne']
    intro h; exact hne (by linarith)
  have hδ : 0 < |R - 1| / 2 := by have := abs_pos.mpr (sub_ne_zero.mpr hR1); linarith
  have hlim : Tendsto (fun m : ℕ =>
      (1 + σ₁ * (spacing (2 * m + 1) ^ 2 * modeSymbol (2 * m + 1) (cornerMode m))) /
        (1 + σ₂ * (spacing (2 * m + 1) ^ 2 * modeSymbol (2 * m + 1) (cornerMode m)))) atTop
      (𝓝 R) := by
    have hx := tendsto_cornerSymbol
    have := ((hx.const_mul σ₁).const_add 1).div ((hx.const_mul σ₂).const_add 1)
      (by rw [mul_comm]; linarith)
    rw [hR, show 1 + 12 * σ₁ = 1 + σ₁ * 12 by ring, show 1 + 12 * σ₂ = 1 + σ₂ * 12 by ring]
    exact this
  have hev := (hlim.sub_const 1).abs.eventually (lt_mem_nhds (show |R - 1| / 2 < |R - 1| by
    linarith))
  obtain ⟨m₁, hm₁⟩ := eventually_atTop.mp hev
  refine ⟨|R - 1| / 2, hδ, max m₁ 1, le_max_right _ _, fun m hm => ?_⟩
  rw [cornerRatio_eq hσ₁ hσ₂ (le_trans (le_max_right _ _) hm)]
  exact (hm₁ m (le_trans (le_max_left _ _) hm)).le

/-- From `|r² - 1| ≥ δ` to `max(r, r⁻¹) ≥ √(1 + δ)`. -/
theorem max_ratio_ge {Ω₁ Ω₂ δ : ℝ} (h₁ : 0 < Ω₁) (h₂ : 0 < Ω₂) (hδ : 0 < δ)
    (hsep : δ ≤ |Ω₁ ^ 2 / Ω₂ ^ 2 - 1|) :
    Real.sqrt (1 + δ) ≤ max (Ω₁ / Ω₂) (Ω₂ / Ω₁) := by
  have hr : 0 < Ω₁ / Ω₂ := div_pos h₁ h₂
  have hr' : Ω₂ / Ω₁ = (Ω₁ / Ω₂)⁻¹ := by rw [inv_div]
  have hsq : Ω₁ ^ 2 / Ω₂ ^ 2 = (Ω₁ / Ω₂) ^ 2 := by rw [div_pow]
  rw [hsq] at hsep
  rw [Real.sqrt_le_left (by positivity)]
  rcases le_or_gt 0 ((Ω₁ / Ω₂) ^ 2 - 1) with hpos | hneg
  · rw [abs_of_nonneg hpos] at hsep
    have : 1 + δ ≤ (Ω₁ / Ω₂) ^ 2 := by linarith
    calc 1 + δ ≤ (Ω₁ / Ω₂) ^ 2 := this
      _ ≤ max (Ω₁ / Ω₂) (Ω₂ / Ω₁) ^ 2 :=
        pow_le_pow_left₀ hr.le (le_max_left _ _) 2
  · rw [abs_of_neg hneg] at hsep
    set r := Ω₁ / Ω₂
    have hr2 : r ^ 2 ≤ 1 - δ := by linarith
    have hr2pos : 0 < r ^ 2 := by positivity
    have hinv : 1 + δ ≤ (r⁻¹) ^ 2 := by
      rw [inv_pow, le_inv_comm₀ (by linarith) hr2pos]
      calc r ^ 2 ≤ 1 - δ := hr2
        _ ≤ (1 + δ)⁻¹ := by
          rw [le_inv_comm₀ (by linarith) (by linarith)]
          rw [inv_eq_one_div, le_div_iff₀ (by linarith)]
          nlinarith
    calc 1 + δ ≤ (r⁻¹) ^ 2 := hinv
      _ ≤ max r (Ω₂ / Ω₁) ^ 2 := by
          rw [hr']; exact pow_le_pow_left₀ (inv_pos.mpr hr).le (le_max_right _ _) 2

/-! ### `prop:supp-law-switching` -/

/-- **`prop:supp-law-switching` (rapid switching is not included).**  Let `σ₁ ≠ σ₂` be two
scalar marks in the admissible interval `|σᵢ| < 1/24` (the open writer ball `‖B‖ < b₀ < c_*/24`
for the flat chart `c = I`).  There are constants `c, C > 0` and `m₀` such that on every odd grid
`N = 2m + 1 ≥ 2m₀ + 1` (`h = 1/N`), for the corner mode `k = (m, m, m)` of the law family:
* the two quarter periods sum to at most `(π/2) h`;
* for every slab length `T > 0` there is a unit corner-mode datum `s₀ ∈ {(1,0), (0,1)}` such that
  every switched history (`σ₁` and `σ₂` each held for its quarter period, state carried over)
  starting from `(s₀ 0 · e_k, s₀ 1 · e_k)` completes `n = ⌊T/(τ₁ + τ₂)⌋` cycles inside `[0, T]`
  and then has a corner-mode coefficient `α` (of the field or of its velocity) with
  `|α| ≥ C exp(c T / h)`. -/
theorem rapid_switching_not_included {σ₁ σ₂ : ℝ} (hσ₁ : |σ₁| < 1 / 24) (hσ₂ : |σ₂| < 1 / 24)
    (hne : σ₁ ≠ σ₂) :
    ∃ c > 0, ∃ C > 0, ∃ m₀ : ℕ, ∀ m ≥ m₀,
      quarterPeriod (cornerOmega σ₁ m) + quarterPeriod (cornerOmega σ₂ m)
        ≤ π / 2 * spacing (2 * m + 1) ∧
      ∀ T > 0, ∃ i : Fin 2,
        ∀ qa pa qb pb : ℕ → ℝ → PeriodicGrid (2 * m + 1) → ℂ,
        (∀ n, IsLawSolution (2 * m + 1) σ₁ (qa n) (pa n) (quarterPeriod (cornerOmega σ₁ m))) →
        (∀ n, IsLawSolution (2 * m + 1) σ₂ (qb n) (pb n) (quarterPeriod (cornerOmega σ₂ m))) →
        (∀ n, qb n 0 = qa n (quarterPeriod (cornerOmega σ₁ m)) ∧
          pb n 0 = pa n (quarterPeriod (cornerOmega σ₁ m))) →
        (∀ n, qa (n + 1) 0 = qb n (quarterPeriod (cornerOmega σ₂ m)) ∧
          pa (n + 1) 0 = pb n (quarterPeriod (cornerOmega σ₂ m))) →
        qa 0 0 = (Pi.single i (1 : ℝ) : Fin 2 → ℝ) 0 • fourierMode (cornerMode m) →
        pa 0 0 = (Pi.single i (1 : ℝ) : Fin 2 → ℝ) 1 • fourierMode (cornerMode m) →
        let n := ⌊T / (quarterPeriod (cornerOmega σ₁ m) + quarterPeriod (cornerOmega σ₂ m))⌋₊
        (n : ℝ) * (quarterPeriod (cornerOmega σ₁ m) + quarterPeriod (cornerOmega σ₂ m)) ≤ T ∧
        ∃ α : ℝ, C * Real.exp (c * T / spacing (2 * m + 1)) ≤ |α| ∧
          ((i = 0 ∧ qa n 0 = α • fourierMode (cornerMode m)) ∨
           (i = 1 ∧ pa n 0 = α • fourierMode (cornerMode m))) := by
  obtain ⟨δ, hδ, m₀, hm₀, hsep⟩ := corner_ratio_separated hσ₁ hσ₂ hne
  set ρ₀ := Real.sqrt (1 + δ) with hρ₀
  have hρ₀1 : 1 < ρ₀ := by
    rw [hρ₀, Real.lt_sqrt (by norm_num)]
    linarith
  have hlog : 0 < Real.log ρ₀ := Real.log_pos hρ₀1
  refine ⟨Real.log ρ₀ / (π / 2), by positivity, ρ₀⁻¹, by positivity, m₀, fun m hm => ?_⟩
  have hm1 : 1 ≤ m := le_trans hm₀ hm
  have hΩ₁ := cornerOmega_pos hσ₁ hm1
  have hΩ₂ := cornerOmega_pos hσ₂ hm1
  have hsp : 0 < spacing (2 * m + 1) := by unfold spacing; positivity
  set τ := quarterPeriod (cornerOmega σ₁ m) + quarterPeriod (cornerOmega σ₂ m) with hτ
  have hτpos : 0 < τ := by
    rw [hτ]; unfold quarterPeriod; positivity
  have hτle : τ ≤ π / 2 * spacing (2 * m + 1) := by
    have := cornerQuarterPeriod_le hσ₁ hm1
    have := cornerQuarterPeriod_le hσ₂ hm1
    rw [hτ]; linarith
  refine ⟨hτle, fun T hT => ?_⟩
  obtain ⟨i, hi⟩ := two_step_pow_basis_amplitude (cornerOmega σ₁ m) (cornerOmega σ₂ m) hΩ₁ hΩ₂
  refine ⟨i, fun qa pa qb pb hsa hsb hab hba hq0 hp0 => ?_⟩
  intro n
  have hcyc := law_switching_cycles σ₁ σ₂ (cornerMode m) (cornerFrequencySq_pos hσ₁ hm1)
    (cornerFrequencySq_pos hσ₂ hm1) qa pa qb pb hsa hsb hab hba (Pi.single i 1) hq0 hp0 n
  have hρ : ρ₀ ≤ max (cornerOmega σ₁ m / cornerOmega σ₂ m) (cornerOmega σ₂ m / cornerOmega σ₁ m) :=
    max_ratio_ge hΩ₁ hΩ₂ hδ (hsep m hm)
  -- the number of cycles
  have hn1 : (n : ℝ) * τ ≤ T := by
    have := Nat.floor_le (div_pos hT hτpos).le
    rw [le_div_iff₀ hτpos] at this
    exact this
  have hn2 : T / τ - 1 ≤ n := by
    have := Nat.lt_floor_add_one (T / τ)
    linarith
  have hTn : T / (π / 2 * spacing (2 * m + 1)) - 1 ≤ n := by
    have : T / (π / 2 * spacing (2 * m + 1)) ≤ T / τ :=
      div_le_div_of_nonneg_left hT.le hτpos hτle
    linarith
  -- amplitude
  set α := (((quarterPeriodTransfer (cornerOmega σ₂ m) * quarterPeriodTransfer (cornerOmega σ₁ m))
    ^ n) *ᵥ Pi.single i 1) i with hα
  have hαabs : |α| = max (cornerOmega σ₁ m / cornerOmega σ₂ m)
      (cornerOmega σ₂ m / cornerOmega σ₁ m) ^ n := hi n
  have hρn : ρ₀ ^ n ≤ |α| := by
    rw [hαabs]; exact pow_le_pow_left₀ (by linarith) hρ n
  have hexp : ρ₀⁻¹ * Real.exp (Real.log ρ₀ / (π / 2) * T / spacing (2 * m + 1)) ≤ ρ₀ ^ n := by
    have hρpos : 0 < ρ₀ := by linarith
    rw [show ρ₀ ^ n = Real.exp (n * Real.log ρ₀) by
      rw [Real.exp_nat_mul, Real.exp_log hρpos], show ρ₀⁻¹ = Real.exp (-Real.log ρ₀) by
      rw [Real.exp_neg, Real.exp_log hρpos], ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : Real.log ρ₀ / (π / 2) * T / spacing (2 * m + 1)
        = Real.log ρ₀ * (T / (π / 2 * spacing (2 * m + 1))) := by
      field_simp
    rw [this]
    nlinarith
  refine ⟨hn1, α, hexp.trans hρn, ?_⟩
  fin_cases i
  · left
    refine ⟨rfl, ?_⟩
    rw [hcyc.1]
    rfl
  · right
    refine ⟨rfl, ?_⟩
    rw [hcyc.2]
    rfl

end LawSwitchingMode
end RenewalGeometry
