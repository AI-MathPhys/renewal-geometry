/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.HarmonicWriterLocalityExact

/-!
# The open harmonic writer on the periodic grid and its exact energy identity
  (`eq:main-open-writer`, `eq:main-harmonic-normal-row`, `eq:supp-open-energy`,
  `eq:supp-open-commuted-row`, `eq:supp-open-energy-identity`; emergent-spacetime manuscript)

On the periodic grid `(ℤ/N)³` with mesh `h = 1/N` and real arrays:

* `Dp`, `Dm`, `D0`: the differences of `eq:main-open-differences` (the generic `fwd`, `bwd`,
  `ctr` of `HarmonicWriter` at the grid steps `e_i`); summation by parts `sum_mul_Dm`
  (`(D_i⁺)* = -D_i⁻`) and `sum_mul_D0` (`(D_i⁰)* = -D_i⁰`).
* `skewArr`, `divArr`: the skew transport `𝖪_b` and the divergence flux with coefficient arrays,
  identified with the writer's (`skewTransport_eq`, `divergenceFlux_eq`); the skew cancellation
  `⟨v, 𝖪_b v⟩_h = 0` (`sum_mul_skewArr`) and the summation by parts of the divergence
  (`sum_mul_divArr`).
* `energy`, `hasDerivAt_energy` (**exact energy identity**, `eq:supp-open-energy-identity` for one
  multi-index, multi-component record): if `q_t = v` and `R` is defined by the commuted row
  `a v_t = Σ D_i⁻(c^{ij} D_j⁺ q) - 𝖪_b v + R` (`eq:supp-open-commuted-row`, with symmetric
  `c^{ij}`), then `d/dt 𝓔 = ½⟨v, ȧ v⟩ + ½Σ⟨D_i⁺q, ċ^{ij} D_j⁺ q⟩ + ⟨q, v⟩ + ⟨v, R⟩`.
* `harmA`, `harmB`, `harmC`: the harmonic normal-row coefficients `a = -g^{00}`, `b^i = -g^{0i}`,
  `c^{ij} = g^{ij}` of `eq:main-harmonic-normal-row` (`g = η + q`, inverse of the `4 × 4` record);
  `harm_minkowski`: at flat data `a = 1`, `b = 0`, `c = I`.
* `openWriterAcceleration`: the open writer `eq:main-open-writer` on the grid, with these
  coefficients, compensator differentials the Fréchet derivatives of `c^{ij}` and `b^i`
  (`eq:main-open-compensator`), and the first-jet source `F` as a parameter (the manuscript does
  not display its formula).

The `h`-uniform remainder bound `eq:supp-open-remainder` (hence `thm:supp-open-energy`) is not
covered.
-/

open scoped BigOperators
open Finset

namespace RenewalGeometry.OpenWriterEnergy

open HarmonicWriter RootParityConnector

noncomputable section

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N]

/-! ### Difference operators on real periodic arrays -/

/-- `D_i⁺` on real arrays of the periodic grid, mesh `h = 1/N`. -/
abbrev Dp (i : Fin 3) (u : Grid N → ℝ) : Grid N → ℝ := fwd (N : ℝ)⁻¹ (e N) i u

/-- `D_i⁻` on real arrays. -/
abbrev Dm (i : Fin 3) (u : Grid N → ℝ) : Grid N → ℝ := bwd (N : ℝ)⁻¹ (e N) i u

/-- `D_i⁰` on real arrays. -/
abbrev D0 (i : Fin 3) (u : Grid N → ℝ) : Grid N → ℝ := ctr (N : ℝ)⁻¹ (e N) i u

theorem Dp_apply (i : Fin 3) (u : Grid N → ℝ) (x : Grid N) :
    Dp i u x = N * (u (x + e N i) - u x) := by
  simp [Dp, fwd, smul_eq_mul]

theorem Dm_apply (i : Fin 3) (u : Grid N → ℝ) (x : Grid N) :
    Dm i u x = N * (u x - u (x - e N i)) := by
  simp [Dm, bwd, smul_eq_mul]

theorem D0_apply (i : Fin 3) (u : Grid N → ℝ) (x : Grid N) :
    D0 i u x = (Dp i u x + Dm i u x) / 2 := by
  simp only [D0, ctr, smul_eq_mul]; simp only [Dp, Dm]; ring

theorem sum_comp_add (f : Grid N → ℝ) (a : Grid N) : ∑ x, f (x + a) = ∑ x, f x :=
  Fintype.sum_equiv (Equiv.addRight a) _ _ (fun _ => rfl)

theorem sum_comp_sub (f : Grid N → ℝ) (a : Grid N) : ∑ x, f (x - a) = ∑ x, f x :=
  Fintype.sum_equiv (Equiv.subRight a) _ _ (fun _ => rfl)

/-- **Summation by parts** (`(D_i⁺)* = -D_i⁻`). -/
theorem sum_mul_Dm (i : Fin 3) (u w : Grid N → ℝ) :
    ∑ x, u x * Dm i w x = -∑ x, Dp i u x * w x := by
  simp only [Dm_apply, Dp_apply]
  have h1 : ∑ x, u x * w (x - e N i) = ∑ x, u (x + e N i) * w x := by
    rw [← sum_comp_add (fun x => u x * w (x - e N i)) (e N i)]
    simp
  have h2 : ∑ x, u x * (N * (w x - w (x - e N i))) =
      N * ∑ x, u x * w x - N * ∑ x, u x * w (x - e N i) := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun x _ => by ring
  have h3 : ∑ x, N * (u (x + e N i) - u x) * w x =
      N * ∑ x, u (x + e N i) * w x - N * ∑ x, u x * w x := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun x _ => by ring
  rw [h2, h3, h1]
  ring

/-- `(D_i⁰)* = -D_i⁰`. -/
theorem sum_mul_D0 (i : Fin 3) (u w : Grid N → ℝ) :
    ∑ x, u x * D0 i w x = -∑ x, D0 i u x * w x := by
  have hp : ∑ x, u x * Dp i w x = -∑ x, Dm i u x * w x := by
    have := sum_mul_Dm i w u
    rw [show ∑ x, w x * Dm i u x = ∑ x, Dm i u x * w x from
      sum_congr rfl fun x _ => mul_comm _ _,
      show ∑ x, Dp i w x * u x = ∑ x, u x * Dp i w x from
      sum_congr rfl fun x _ => mul_comm _ _] at this
    linarith
  have hm := sum_mul_Dm i u w
  have e1 : ∑ x, u x * D0 i w x = (∑ x, u x * Dp i w x + ∑ x, u x * Dm i w x) / 2 := by
    rw [← sum_add_distrib, sum_div]
    exact sum_congr rfl fun x _ => by rw [D0_apply]; ring
  have e2 : ∑ x, D0 i u x * w x = (∑ x, Dp i u x * w x + ∑ x, Dm i u x * w x) / 2 := by
    rw [← sum_add_distrib, sum_div]
    exact sum_congr rfl fun x _ => by rw [D0_apply]; ring
  rw [e1, e2, hp, hm]
  ring

/-- The skew transport with coefficient arrays,
`𝖪_b v = Σ_i (M_{b^i} D_i⁰ + D_i⁰ M_{b^i}) v` (`eq:main-open-skew-transport`). -/
def skewArr (b : Fin 3 → Grid N → ℝ) (v : Grid N → ℝ) (x : Grid N) : ℝ :=
  ∑ i, (b i x * D0 i v x + D0 i (fun y => b i y * v y) x)

/-- The writer's skew transport is `skewArr` with the coefficient arrays `b^i(g(x))`. -/
theorem skewTransport_eq (b : Fin 3 → ℝ → ℝ) (η : ℝ) (q v : Grid N → ℝ) (x : Grid N) :
    skewTransport b η (N : ℝ)⁻¹ (e N) q v x = skewArr (fun i y => b i (η + q y)) v x := by
  simp [skewTransport, skewArr, smul_eq_mul]

/-- **Skew cancellation** `⟨v, 𝖪_b v⟩_h = 0`. -/
theorem sum_mul_skewArr (b : Fin 3 → Grid N → ℝ) (v : Grid N → ℝ) :
    ∑ x, v x * skewArr b v x = 0 := by
  simp only [skewArr, mul_sum, mul_add]
  rw [sum_comm]
  refine sum_eq_zero fun i _ => ?_
  rw [sum_add_distrib, sum_mul_D0]
  have : ∑ x, D0 i v x * (b i x * v x) = ∑ x, v x * (b i x * D0 i v x) :=
    sum_congr rfl fun x _ => by ring
  rw [this]; ring

/-- The divergence flux with coefficient arrays, `Σ_{ij} D_i⁻(c^{ij} D_j⁺ q)`. -/
def divArr (c : Fin 3 → Fin 3 → Grid N → ℝ) (q : Grid N → ℝ) (x : Grid N) : ℝ :=
  ∑ i, ∑ j, Dm i (fun y => c i j y * Dp j q y) x

/-- The writer's divergence flux is `divArr` with the coefficient arrays `c^{ij}(g(x))`. -/
theorem divergenceFlux_eq (c : Fin 3 → Fin 3 → ℝ → ℝ) (η : ℝ) (q : Grid N → ℝ) (x : Grid N) :
    divergenceFlux c η (N : ℝ)⁻¹ (e N) q x = divArr (fun i j y => c i j (η + q y)) q x := by
  simp [divergenceFlux, divArr, smul_eq_mul]

/-- **Summation by parts of the divergence** `⟨v, Σ D_i⁻(c^{ij}D_j⁺q)⟩ = -Σ⟨D_i⁺v, c^{ij}D_j⁺q⟩`. -/
theorem sum_mul_divArr (c : Fin 3 → Fin 3 → Grid N → ℝ) (q v : Grid N → ℝ) :
    ∑ x, v x * divArr c q x = -∑ i, ∑ j, ∑ x, Dp i v x * (c i j x * Dp j q x) := by
  simp only [divArr, mul_sum]
  rw [sum_comm]
  simp only [← sum_neg_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_mul_Dm i v (fun y => c i j y * Dp j q y), ← sum_neg_distrib]

/-! ### The shifted energy and its exact time derivative -/

/-- The quadratic energy of `eq:supp-open-energy` for one multi-index (multi-component record
`q, v : ι → grid`, mass array `a`, symmetric spatial coefficient arrays `c^{ij}`):
`½ Σ_μ [⟨v_μ, a v_μ⟩_h + Σ_{ij} ⟨D_i⁺q_μ, c^{ij} D_j⁺q_μ⟩_h + ‖q_μ‖_h²]`. -/
def energy {ι : Type*} [Fintype ι] (a : Grid N → ℝ) (c : Fin 3 → Fin 3 → Grid N → ℝ)
    (q v : ι → Grid N → ℝ) : ℝ :=
  ((N : ℝ) ^ 3)⁻¹ * (1 / 2) * ∑ μ, ∑ x, (v μ x * (a x * v μ x) +
    ∑ i, ∑ j, Dp i (q μ) x * (c i j x * Dp j (q μ) x) + q μ x ^ 2)

theorem hasDerivAt_Dp {q v : ℝ → Grid N → ℝ} {t : ℝ}
    (hq : ∀ x, HasDerivAt (fun s => q s x) (v t x) t) (i : Fin 3) (x : Grid N) :
    HasDerivAt (fun s => Dp i (q s) x) (Dp i (v t) x) t := by
  simp only [Dp_apply]
  exact ((hq (x + e N i)).sub (hq x)).const_mul _

/-- **Exact energy identity** (`eq:supp-open-energy-identity`, one multi-index).  Let
`t ↦ (q(t), v(t))` be a differentiable multi-component record with `q_t = v`, let `a(t)`,
`c^{ij}(t) = c^{ji}(t)`, `b^i(t)` be differentiable coefficient arrays, and let the residual
`R` be defined by the commuted mass row
`a v_t = Σ_{ij} D_i⁻(c^{ij} D_j⁺ q) - 𝖪_b v + R` (`eq:supp-open-commuted-row`).  Then
`d/dt 𝓔 = ½⟨v, ȧ v⟩ + ½ Σ_{ij}⟨D_i⁺q, ċ^{ij} D_j⁺q⟩ + ⟨q, v⟩ + ⟨v, R⟩`: summation by parts
cancels the divergence against the derivative of the spatial energy and
`⟨v, 𝖪_b v⟩ = 0`. -/
theorem hasDerivAt_energy {ι : Type*} [Fintype ι] (q v : ℝ → ι → Grid N → ℝ)
    (a : ℝ → Grid N → ℝ) (c : ℝ → Fin 3 → Fin 3 → Grid N → ℝ) (b : Fin 3 → Grid N → ℝ)
    (vt : ι → Grid N → ℝ) (at' : Grid N → ℝ) (ct : Fin 3 → Fin 3 → Grid N → ℝ)
    (R : ι → Grid N → ℝ) (t : ℝ)
    (hq : ∀ μ x, HasDerivAt (fun s => q s μ x) (v t μ x) t)
    (hv : ∀ μ x, HasDerivAt (fun s => v s μ x) (vt μ x) t)
    (ha : ∀ x, HasDerivAt (fun s => a s x) (at' x) t)
    (hc : ∀ i j x, HasDerivAt (fun s => c s i j x) (ct i j x) t)
    (hsym : ∀ i j x, c t i j x = c t j i x)
    (hrow : ∀ μ x, a t x * vt μ x = divArr (c t) (q t μ) x - skewArr b (v t μ) x + R μ x) :
    HasDerivAt (fun s => energy (a s) (c s) (q s) (v s))
      (((N : ℝ) ^ 3)⁻¹ * ∑ μ, ∑ x, ((1 / 2) * (v t μ x * (at' x * v t μ x)) +
        (1 / 2) * ∑ i, ∑ j, Dp i (q t μ) x * (ct i j x * Dp j (q t μ) x) +
        q t μ x * v t μ x + v t μ x * R μ x)) t := by
  -- derivative of each summand
  have hterm : ∀ μ x, HasDerivAt (fun s => v s μ x * (a s x * v s μ x) +
      ∑ i, ∑ j, Dp i (q s μ) x * (c s i j x * Dp j (q s μ) x) + q s μ x ^ 2)
      (vt μ x * (a t x * v t μ x) + v t μ x * (at' x * v t μ x + a t x * vt μ x) +
        ∑ i, ∑ j, (Dp i (v t μ) x * (c t i j x * Dp j (q t μ) x) +
          Dp i (q t μ) x * (ct i j x * Dp j (q t μ) x + c t i j x * Dp j (v t μ) x)) +
        2 * q t μ x * v t μ x) t := by
    intro μ x
    have h1 := (hv μ x).mul ((ha x).mul (hv μ x))
    have h2 : HasDerivAt (fun s => ∑ i, ∑ j, Dp i (q s μ) x * (c s i j x * Dp j (q s μ) x))
        (∑ i, ∑ j, (Dp i (v t μ) x * (c t i j x * Dp j (q t μ) x) +
          Dp i (q t μ) x * (ct i j x * Dp j (q t μ) x + c t i j x * Dp j (v t μ) x))) t := by
      refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
      exact (hasDerivAt_Dp (q := fun s => q s μ) (v := fun s => v s μ) (hq μ) i x).mul
        ((hc i j x).mul (hasDerivAt_Dp (q := fun s => q s μ) (v := fun s => v s μ) (hq μ) j x))
    have h3 := (hq μ x).pow 2
    refine ((h1.add h2).add h3).congr_deriv ?_
    norm_num
  have hE : HasDerivAt (fun s => energy (a s) (c s) (q s) (v s))
      (((N : ℝ) ^ 3)⁻¹ * (1 / 2) * ∑ μ, ∑ x,
        (vt μ x * (a t x * v t μ x) + v t μ x * (at' x * v t μ x + a t x * vt μ x) +
        ∑ i, ∑ j, (Dp i (v t μ) x * (c t i j x * Dp j (q t μ) x) +
          Dp i (q t μ) x * (ct i j x * Dp j (q t μ) x + c t i j x * Dp j (v t μ) x)) +
        2 * q t μ x * v t μ x)) t := by
    unfold energy
    exact (HasDerivAt.fun_sum fun μ _ => HasDerivAt.fun_sum fun x _ => hterm μ x).const_mul _
  refine hE.congr_deriv ?_
  -- algebra: use the row, skew cancellation and summation by parts
  have hrow' : ∀ μ, ∑ x, v t μ x * (a t x * vt μ x) =
      -∑ i, ∑ j, ∑ x, Dp i (v t μ) x * (c t i j x * Dp j (q t μ) x) + ∑ x, v t μ x * R μ x := by
    intro μ
    simp only [hrow, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib, sum_mul_divArr,
      sum_mul_skewArr, sub_zero]
  have hsymsum : ∀ μ, ∑ x, ∑ i, ∑ j, Dp i (q t μ) x * (c t i j x * Dp j (v t μ) x) =
      ∑ i, ∑ j, ∑ x, Dp i (v t μ) x * (c t i j x * Dp j (q t μ) x) := by
    intro μ
    calc ∑ x, ∑ i, ∑ j, Dp i (q t μ) x * (c t i j x * Dp j (v t μ) x)
        = ∑ x, ∑ i, ∑ j, Dp i (v t μ) x * (c t i j x * Dp j (q t μ) x) := by
          refine sum_congr rfl fun x _ => ?_
          rw [sum_comm]
          exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [hsym j i x]; ring
      _ = ∑ i, ∑ j, ∑ x, Dp i (v t μ) x * (c t i j x * Dp j (q t μ) x) := by
          rw [sum_comm]
          exact sum_congr rfl fun i _ => sum_comm
  have key : ∀ μ, ∑ x, (vt μ x * (a t x * v t μ x) + v t μ x * (at' x * v t μ x + a t x * vt μ x) +
        ∑ i, ∑ j, (Dp i (v t μ) x * (c t i j x * Dp j (q t μ) x) +
          Dp i (q t μ) x * (ct i j x * Dp j (q t μ) x + c t i j x * Dp j (v t μ) x)) +
        2 * q t μ x * v t μ x) =
      2 * ∑ x, ((1 / 2) * (v t μ x * (at' x * v t μ x)) +
        (1 / 2) * ∑ i, ∑ j, Dp i (q t μ) x * (ct i j x * Dp j (q t μ) x) +
        q t μ x * v t μ x + v t μ x * R μ x) := by
    intro μ
    set S1 : Grid N → ℝ := fun x => ∑ i, ∑ j, Dp i (v t μ) x * (c t i j x * Dp j (q t μ) x)
    set S2 : Grid N → ℝ := fun x => ∑ i, ∑ j, Dp i (q t μ) x * (ct i j x * Dp j (q t μ) x)
    set S3 : Grid N → ℝ := fun x => ∑ i, ∑ j, Dp i (q t μ) x * (c t i j x * Dp j (v t μ) x)
    have hpt : ∀ x, (vt μ x * (a t x * v t μ x) + v t μ x * (at' x * v t μ x + a t x * vt μ x) +
        ∑ i, ∑ j, (Dp i (v t μ) x * (c t i j x * Dp j (q t μ) x) +
          Dp i (q t μ) x * (ct i j x * Dp j (q t μ) x + c t i j x * Dp j (v t μ) x)) +
        2 * q t μ x * v t μ x) =
        2 * (v t μ x * (a t x * vt μ x)) + v t μ x * (at' x * v t μ x) + S1 x + S2 x + S3 x +
          2 * (q t μ x * v t μ x) := by
      intro x
      simp only [S1, S2, S3, mul_add, sum_add_distrib]
      ring
    have hS1 : ∑ x, S1 x = ∑ i, ∑ j, ∑ x, Dp i (v t μ) x * (c t i j x * Dp j (q t μ) x) := by
      simp only [S1]
      rw [sum_comm]
      exact sum_congr rfl fun i _ => sum_comm
    rw [sum_congr rfl fun x _ => hpt x]
    simp only [sum_add_distrib, ← mul_sum]
    rw [hrow' μ, hS1, show ∑ x, S3 x = _ from hsymsum μ]
    simp only [S2, mul_add, sum_add_distrib, ← mul_sum]
    ring
  simp only [key, ← mul_sum]
  ring


/-! ### The concrete harmonic coefficient chart and the open writer -/

/-- A metric record at a site: a `4 × 4` array `g_{μν}` (the ten-component records are the
symmetric ones). -/
abbrev MetricRec := Fin 4 → Fin 4 → ℝ

/-- The Minkowski metric `η = diag(-1, 1, 1, 1)`. -/
def minkowski : MetricRec := fun i j => if i = j then (if i = 0 then -1 else 1) else 0

/-- Harmonic normal-row mass coefficient `a(g) = -g^{00}` (`eq:main-harmonic-normal-row`). -/
def harmA (g : MetricRec) : ℝ := -((Matrix.of g)⁻¹ 0 0)

/-- Harmonic normal-row transport coefficient `b^i(g) = -g^{0i}`. -/
def harmB (i : Fin 3) (g : MetricRec) : ℝ := -((Matrix.of g)⁻¹ 0 i.succ)

/-- Harmonic normal-row spatial coefficient `c^{ij}(g) = g^{ij}`. -/
def harmC (i j : Fin 3) (g : MetricRec) : ℝ := (Matrix.of g)⁻¹ i.succ j.succ

/-- **The open writer** `eq:main-open-writer` on the odd periodic grid, mesh `h = 1/N`: the
acceleration `v_t = a(g)⁻¹[Σ_{ij} D_i⁻(c^{ij}(g) D_j⁺ q) - 𝖪_b v + 𝖦_h(q, v)]` of the
record `q = g - η`, with the harmonic coefficients `a = -g^{00}`, `b^i = -g^{0i}`,
`c^{ij} = g^{ij}`, the compensator `𝖦_h` of `eq:main-open-compensator` whose coefficient
differentials are the Fréchet derivatives of `c^{ij}` and `b^i`, and first-jet source `F`
(the analytic first-jet source of the harmonic-reduced vacuum Ricci equation). -/
def openWriterAcceleration (F : MetricRec → MetricRec × (Fin 3 → MetricRec) → MetricRec)
    (q v : Grid N → MetricRec) (x : Grid N) : MetricRec :=
  writerAcceleration harmA harmC harmB F (fun i j g w => fderiv ℝ (harmC i j) g w)
    (fun i g w => fderiv ℝ (harmB i) g w) minkowski (N : ℝ)⁻¹ (e N) q v x

theorem minkowski_inv : (Matrix.of minkowski)⁻¹ = Matrix.of minkowski := by
  have h : Matrix.of minkowski * Matrix.of minkowski = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [minkowski, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply]
  exact Matrix.inv_eq_left_inv h

/-- At flat data the chart is the flat regulator: `a(η) = 1`, `b(η) = 0`, `c(η) = I`. -/
theorem harm_minkowski :
    harmA minkowski = 1 ∧ (∀ i, harmB i minkowski = 0) ∧
      ∀ i j, harmC i j minkowski = if i = j then 1 else 0 := by
  refine ⟨?_, fun i => ?_, fun i j => ?_⟩
  · simp [harmA, minkowski_inv, minkowski, Matrix.of_apply]
  · simp only [harmB, minkowski_inv]
    fin_cases i <;> simp [minkowski, Matrix.of_apply]
  · simp only [harmC, minkowski_inv]
    fin_cases i <;> fin_cases j <;> simp [minkowski, Matrix.of_apply]

end

end RenewalGeometry.OpenWriterEnergy
