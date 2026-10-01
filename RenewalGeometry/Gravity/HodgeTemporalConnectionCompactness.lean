/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.PeriodicGridAubinLions
import RenewalGeometry.Gravity.PeriodicConnectionHodgeIdentity

/-!
# Finite Hodge–temporal criterion for connection compactness
  (`thm:main-hodge-connection`, `ass:main-connection-compactness`; emergent-spacetime manuscript)
-/

open MeasureTheory Filter Topology Set

noncomputable section

set_option linter.unusedSectionVars false

namespace RenewalGeometry.HodgeConnection

open PeriodicGridSobolev GridAubinLions

variable {N : ℕ} [NeZero N]

/-- The grid Hodge identity in the `PeriodicGridSobolev` calculus (`lem:supp-connection-hodge`,
`eq:supp-discrete-hodge-identity`): for a complex periodic one-cochain `u`,
`Σ_{i,j} ‖D_i⁺u_j‖_h² = Σ_{i<j} ‖D_i⁺u_j - D_j⁺u_i‖_h² + ‖Σ_i D_i⁻u_i‖_h²`. -/
theorem hodge_identity (u : Fin 3 → Grid N → ℂ) :
    ∑ i, ∑ j, gridNormSq (Dp i (u j)) =
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), gridNormSq (Dp i (u j) - Dp j (u i)) +
        gridNormSq (∑ i, Dm i (u i)) := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hfw : ∀ i (w : Grid N → ℂ),
      LawMultiplier.forwardDiff (1 / (N : ℝ)) (LawMultiplier.unitStep N i) w = Dp i w := by
    intro i w
    funext x
    simp only [LawMultiplier.forwardDiff, Dp_apply, LawMultiplier.unitStep,
      PeriodicGridSobolev.unit, one_div, inv_inv, Complex.real_smul, Complex.ofReal_natCast]
  have hbw : ∀ i (w : Grid N → ℂ),
      LawMultiplier.backwardDiff (1 / (N : ℝ)) (LawMultiplier.unitStep N i) w = Dm i w := by
    intro i w
    funext x
    simp only [LawMultiplier.backwardDiff, Dm_apply, LawMultiplier.unitStep,
      PeriodicGridSobolev.unit, one_div, inv_inv, Complex.real_smul, Complex.ofReal_natCast]
  have hnorm : ∀ w : Grid N → ℂ, LawMultiplier.gridNormSq (1 / (N : ℝ)) w = gridNormSq w := by
    intro w
    simp only [LawMultiplier.gridNormSq, PeriodicGridSobolev.gridNormSq, one_div, inv_pow]
  have h := PeriodicHodge.periodic_discrete_hodge_identity (F := ℂ) N (1 / (N : ℝ)) u
  simp only [hfw, hbw, hnorm] at h
  convert h using 3

/-! ### Space-time norms of the finite connection -/

variable {d : ℕ}

/-- The time-integrated norm `‖f‖_{L²_t} = (∫₀ᵀ f)^{1/2}` of a pointwise squared grid norm
`f(t)`: this is the `L²_{t,h}` norm used in `eq:main-connection-hodge-budget`. -/
def l2t (T : ℝ) (f : ℝ → ℝ) : ℝ := Real.sqrt (∫ t in Ioc 0 T, f t)

/-- Squared grid norm of the full connection `(A_0, A)` at time `t` (internal components `a`). -/
def connSq (A0 : ℝ → Fin d → Grid N → ℂ) (A : ℝ → Fin 3 → Fin d → Grid N → ℂ) (t : ℝ) : ℝ :=
  ∑ a, gridNormSq (A0 t a) + ∑ i, ∑ a, gridNormSq (A t i a)

/-- Squared grid norm `Σ_{i<j} ‖F_{ij}‖_h²` of a spatial two-form at time `t`. -/
def twoFormSq (F : ℝ → Fin 3 → Fin 3 → Fin d → Grid N → ℂ) (t : ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), ∑ a, gridNormSq (F t i j a)

/-- The discrete codifferential `δ_h A = -Σ_i D_i⁻ A_i` (`eq:main-connection-hodge`). -/
def codiff (A : ℝ → Fin 3 → Fin d → Grid N → ℂ) (t : ℝ) (a : Fin d) : Grid N → ℂ :=
  -∑ i, Dm i (A t i a)

/-- The discrete curl `(d_h A)_{ij} = D_i⁺ A_j - D_j⁺ A_i` (`eq:main-connection-hodge`). -/
def curl (A : ℝ → Fin 3 → Fin d → Grid N → ℂ) (t : ℝ) (i j : Fin 3) (a : Fin d) : Grid N → ℂ :=
  Dp i (A t j a) - Dp j (A t i a)

/-- Squared grid norm of `δ_h A` at time `t`. -/
def codiffSq (A : ℝ → Fin 3 → Fin d → Grid N → ℂ) (t : ℝ) : ℝ :=
  ∑ a, gridNormSq (codiff A t a)

/-- Squared grid norm of `D⁺A_0` at time `t`. -/
def gradTemporalSq (A0 : ℝ → Fin d → Grid N → ℂ) (t : ℝ) : ℝ :=
  ∑ i, ∑ a, gridNormSq (Dp i (A0 t a))

/-- `‖A‖²_{L⁴_{t,h}} = (∫₀ᵀ h³ Σ_x |A(t,x)|⁴ dt)^{1/2}` with `|A|² = Σ_{i,a} |A_{i,a}|²`. -/
def l4Sq (T : ℝ) (A : ℝ → Fin 3 → Fin d → Grid N → ℂ) : ℝ :=
  Real.sqrt (∫ t in Ioc 0 T, ((N : ℝ) ^ 3)⁻¹ * ∑ x, (∑ i, ∑ a, ‖A t i a x‖ ^ 2) ^ 2)

/-- Squared `H⁻¹(𝕋³)` norm of the interpolated time derivative `∂ₜ 𝓘_h(A_0, A)` at time `t`,
given grid time-derivative arrays `G0, G`. -/
def dtNegSq (G0 : ℝ → Fin d → Grid N → ℂ) (G : ℝ → Fin 3 → Fin d → Grid N → ℂ) (t : ℝ) : ℝ :=
  ∑ a, trigNegSq 1 (interp (G0 t a)) + ∑ i, ∑ a, trigNegSq 1 (interp (G t i a))

/-- The full connection `(A_0, A)` as one family of components `(μ, a)`: `μ = none` is the
temporal coefficient, `μ = some i` the spatial coefficient `A_i`. -/
def fullConn (A0 : ℝ → Fin d → Grid N → ℂ) (A : ℝ → Fin 3 → Fin d → Grid N → ℂ) :
    ℝ → Option (Fin 3) × Fin d → Grid N → ℂ
  | t, (none, a) => A0 t a
  | t, (some i, a) => A t i a

theorem sum_fullConn {M : Type*} [AddCommMonoid M] (A0 : ℝ → Fin d → Grid N → ℂ)
    (A : ℝ → Fin 3 → Fin d → Grid N → ℂ) (t : ℝ) (f : (Grid N → ℂ) → M) :
    ∑ μa, f (fullConn A0 A t μa) = ∑ a, f (A0 t a) + ∑ i, ∑ a, f (A t i a) := by
  rw [Fintype.sum_prod_type, Fintype.sum_option]
  rfl

theorem fullConn_isGridW12Rep {T : ℝ} {A0 G0 : ℝ → Fin d → Grid N → ℂ}
    {A G : ℝ → Fin 3 → Fin d → Grid N → ℂ}
    (hW0 : ∀ a, IsGridW12Rep T (fun t => A0 t a) (fun t => G0 t a))
    (hW : ∀ i a, IsGridW12Rep T (fun t => A t i a) (fun t => G t i a)) :
    ∀ μa, IsGridW12Rep T (fun t => fullConn A0 A t μa) (fun t => fullConn G0 G t μa)
  | (none, a) => hW0 a
  | (some i, a) => hW i a

theorem gridNormSq_neg (u : Grid N → ℂ) : gridNormSq (-u) = gridNormSq u := by
  rw [← gridNorm_sq, gridNorm_neg, gridNorm_sq]

theorem gridNormSq_sub_add_le (u v w : Grid N → ℂ) :
    gridNormSq (u - v + w) ≤ 3 * (gridNormSq u + gridNormSq v + gridNormSq w) := by
  have h1 : gridNorm (u - v + w) ≤ gridNorm u + gridNorm v + gridNorm w :=
    (gridNorm_add_le _ _).trans (by linarith [gridNorm_sub_le u v])
  have h0 := gridNorm_nonneg (u - v + w)
  rw [← gridNorm_sq, ← gridNorm_sq, ← gridNorm_sq, ← gridNorm_sq]
  have := gridNorm_nonneg u
  have := gridNorm_nonneg v
  have := gridNorm_nonneg w
  nlinarith [mul_self_le_mul_self h0 h1, sq_nonneg (gridNorm u - gridNorm v),
    sq_nonneg (gridNorm u - gridNorm w), sq_nonneg (gridNorm v - gridNorm w)]

/-- Pointwise Hodge–incidence bound: if the curl obeys the incidence
`d_h A = R - Q + ε` at time `t`, then the spatial `H¹_h` energy of the full connection is bounded
by `‖(A_0, A)‖² + ‖D⁺A_0‖² + ‖δ_h A‖² + 3(‖R‖² + ‖Q‖² + ‖ε‖²)`. -/
theorem energy_le_of_incidence (A0 : ℝ → Fin d → Grid N → ℂ)
    (A : ℝ → Fin 3 → Fin d → Grid N → ℂ) (R Q E : ℝ → Fin 3 → Fin 3 → Fin d → Grid N → ℂ)
    (t : ℝ) (hinc : ∀ i j, i < j → ∀ a, curl A t i j a = R t i j a - Q t i j a + E t i j a) :
    ∑ μa, (gridNormSq (fullConn A0 A t μa) + coordForm (fullConn A0 A t μa)) ≤
      connSq A0 A t + gradTemporalSq A0 t + codiffSq A t +
        3 * (twoFormSq R t + twoFormSq Q t + twoFormSq E t) := by
  rw [sum_fullConn A0 A t (fun u => gridNormSq u + coordForm u)]
  simp only [Finset.sum_add_distrib]
  -- Hodge on each internal component
  have hodge : ∀ a, ∑ j, coordForm (A t j a) =
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), gridNormSq (curl A t i j a) +
        gridNormSq (codiff A t a) := by
    intro a
    have h := hodge_identity (fun j => A t j a)
    simp only [coordForm]
    rw [Finset.sum_comm, h, codiff, gridNormSq_neg]
    rfl
  have hcurl : ∀ a, ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      gridNormSq (curl A t i j a) ≤
        3 * (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
          (gridNormSq (R t i j a) + gridNormSq (Q t i j a) + gridNormSq (E t i j a))) := by
    intro a
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [hinc i j (Finset.mem_filter.1 hj).2 a]
    exact gridNormSq_sub_add_le _ _ _
  have hA0 : ∑ a, coordForm (A0 t a) = gradTemporalSq A0 t := by
    simp only [gradTemporalSq, coordForm]
    exact Finset.sum_comm
  have hsw : ∑ i, ∑ a, coordForm (A t i a) = ∑ a, ∑ j, coordForm (A t j a) := Finset.sum_comm
  have htwo : ∀ F : ℝ → Fin 3 → Fin 3 → Fin d → Grid N → ℂ, ∑ a, ∑ i,
      ∑ j ∈ Finset.univ.filter (fun j => i < j), gridNormSq (F t i j a) = twoFormSq F t := by
    intro F
    simp only [twoFormSq]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  have hsplit : ∑ a, ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      (gridNormSq (R t i j a) + gridNormSq (Q t i j a) + gridNormSq (E t i j a)) =
      twoFormSq R t + twoFormSq Q t + twoFormSq E t := by
    simp only [Finset.sum_add_distrib, htwo]
  rw [hA0, hsw]
  simp only [hodge, Finset.sum_add_distrib]
  have hsum3 : ∑ a, ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      gridNormSq (curl A t i j a) ≤ 3 * (twoFormSq R t + twoFormSq Q t + twoFormSq E t) := by
    rw [← hsplit, Finset.mul_sum]
    exact Finset.sum_le_sum fun a _ => hcurl a
  have hc : ∑ a, gridNormSq (codiff A t a) = codiffSq A t := rfl
  have hconn : ∑ a, gridNormSq (A0 t a) + ∑ i, ∑ a, gridNormSq (A t i a) = connSq A0 A t := rfl
  linarith

theorem integral_le_sq_of_l2t_le {T : ℝ} {f : ℝ → ℝ} (hf : ∀ t, 0 ≤ f t) {C : ℝ}
    (h : l2t T f ≤ C) : ∫ t in Ioc 0 T, f t ≤ C ^ 2 := by
  have h0 : 0 ≤ ∫ t in Ioc 0 T, f t := integral_nonneg hf
  have := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rwa [Real.sq_sqrt h0] at this

theorem l2t_nonneg (T : ℝ) (f : ℝ → ℝ) : 0 ≤ l2t T f := Real.sqrt_nonneg _

theorem l4Sq_nonneg (T : ℝ) (A : ℝ → Fin 3 → Fin d → Grid N → ℂ) : 0 ≤ l4Sq T A :=
  Real.sqrt_nonneg _

theorem twoFormSq_nonneg (F : ℝ → Fin 3 → Fin 3 → Fin d → Grid N → ℂ) (t : ℝ) :
    0 ≤ twoFormSq F t :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    gridNormSq_nonneg _

/-! ### The Hodge–temporal compactness criterion -/

theorem continuousOn_comp_linear {T : ℝ} {u : ℝ → Grid N → ℂ} (hu : ContinuousOn u (Icc 0 T))
    (L : Module.End ℂ (Grid N → ℂ)) : ContinuousOn (fun t => gridNormSq (L (u t))) (Icc 0 T) :=
  continuous_gridNormSq.comp_continuousOn (L.continuous_of_finiteDimensional.comp_continuousOn hu)

/-- **Finite Hodge–temporal sufficient criterion** (`thm:main-hodge-connection`).

Regulators `m` carry periodic grids with `N m` points per axis (`h = 1/N m`, any `N m`), a
temporal coefficient `A0 m t a` and spatial coefficients `A m t i a` (`i : Fin 3`, internal
coordinates `a : Fin d` of a positive coefficient inner product, all in one common
trivialization), with weak time derivatives `G0`, `G` (every grid value `W^{1,2}(0,T)`).
Assume, uniformly in `m`:
* the incidence `d_h A = R^{sp} - 𝒬(A) + ε` (`eq:main-connection-hodge-incidence`) for
  `i < j` at every `t ∈ (0,T]`, with `R, 𝒬, ε ∈ L²_{t,h}` and the product bound
  `‖𝒬‖_{L²_{t,h}} ≤ C_𝒬 ‖A‖²_{L⁴_{t,h}}`;
* the budget `eq:main-connection-hodge-budget`:
  `‖(A_0,A)‖ + ‖R‖ + ‖A‖²_{L⁴} + ‖ε‖ + ‖δ_h A‖ + ‖D⁺A_0‖ + ‖∂ₜ 𝓘_h(A_0,A)‖_{L²_t H⁻¹_x} ≤ C_K`.
Then the interpolated full connections `𝓘_h(A_0, A)` are relatively compact in
`L²((0,T] × 𝕋³)`: some subsequence converges in `L²` to a limit `Ω`, component by component. -/
theorem hodge_connection_compactness {N : ℕ → ℕ} [∀ m, NeZero (N m)] {T : ℝ} (hT : 0 < T)
    (A0 G0 : ∀ m, ℝ → Fin d → Grid (N m) → ℂ) (A G : ∀ m, ℝ → Fin 3 → Fin d → Grid (N m) → ℂ)
    (hW0 : ∀ m a, IsGridW12Rep T (fun t => A0 m t a) (fun t => G0 m t a))
    (hW : ∀ m i a, IsGridW12Rep T (fun t => A m t i a) (fun t => G m t i a))
    (R Q E : ∀ m, ℝ → Fin 3 → Fin 3 → Fin d → Grid (N m) → ℂ)
    (hinc : ∀ m, ∀ t ∈ Ioc 0 T, ∀ i j, i < j → ∀ a,
      curl (A m) t i j a = R m t i j a - Q m t i j a + E m t i j a)
    (hR : ∀ m, IntegrableOn (twoFormSq (R m)) (Ioc 0 T))
    (hQ : ∀ m, IntegrableOn (twoFormSq (Q m)) (Ioc 0 T))
    (hE : ∀ m, IntegrableOn (twoFormSq (E m)) (Ioc 0 T))
    {CQ CK : ℝ} (hprod : ∀ m, l2t T (twoFormSq (Q m)) ≤ CQ * l4Sq T (A m))
    (hbudget : ∀ m, l2t T (connSq (A0 m) (A m)) + l2t T (twoFormSq (R m)) + l4Sq T (A m) +
      l2t T (twoFormSq (E m)) + l2t T (codiffSq (A m)) + l2t T (gradTemporalSq (A0 m)) +
      l2t T (dtNegSq (G0 m) (G m)) ≤ CK) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Ω : Option (Fin 3) × Fin d → ℝ × UnitAddTorus (Fin 3) → ℂ,
      ∀ μa, MemLp (Ω μa) 2 (cylMeasure T) ∧
        Tendsto (fun m => ∫ p, ‖field (fun t => fullConn (A0 (φ m)) (A (φ m)) t μa) p -
          Ω μa p‖ ^ 2 ∂cylMeasure T) atTop (𝓝 0) := by
  have hWf : ∀ m μa, IsGridW12Rep T (fun t => fullConn (A0 m) (A m) t μa)
      (fun t => fullConn (G0 m) (G m) t μa) := fun m =>
    fullConn_isGridW12Rep (hW0 m) (hW m)
  -- individual budget terms
  have hb : ∀ m, l2t T (connSq (A0 m) (A m)) ≤ CK ∧ l2t T (twoFormSq (R m)) ≤ CK ∧
      l4Sq T (A m) ≤ CK ∧ l2t T (twoFormSq (E m)) ≤ CK ∧ l2t T (codiffSq (A m)) ≤ CK ∧
      l2t T (gradTemporalSq (A0 m)) ≤ CK ∧ l2t T (dtNegSq (G0 m) (G m)) ≤ CK := by
    intro m
    have := hbudget m
    have h1 := l2t_nonneg T (connSq (A0 m) (A m))
    have h2 := l2t_nonneg T (twoFormSq (R m))
    have h3 := l4Sq_nonneg T (A m)
    have h4 := l2t_nonneg T (twoFormSq (E m))
    have h5 := l2t_nonneg T (codiffSq (A m))
    have h6 := l2t_nonneg T (gradTemporalSq (A0 m))
    have h7 := l2t_nonneg T (dtNegSq (G0 m) (G m))
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  have hQb : ∀ m, l2t T (twoFormSq (Q m)) ≤ |CQ| * CK := by
    intro m
    have h3 := (hb m).2.2.1
    have hl := l4Sq_nonneg T (A m)
    calc l2t T (twoFormSq (Q m)) ≤ CQ * l4Sq T (A m) := hprod m
      _ ≤ |CQ| * l4Sq T (A m) := mul_le_mul_of_nonneg_right (le_abs_self _) hl
      _ ≤ |CQ| * CK := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
  -- the spatial `L²_t H¹_h` budget
  set B : ℝ := CK ^ 2 + CK ^ 2 + CK ^ 2 + 3 * (CK ^ 2 + (|CQ| * CK) ^ 2 + CK ^ 2) with hBdef
  have hB : ∀ m, ∫ t in Ioc 0 T, ∑ μa, (gridNormSq (fullConn (A0 m) (A m) t μa) +
      coordForm (fullConn (A0 m) (A m) t μa)) ≤ B := by
    intro m
    have hc0 : ∀ a, ContinuousOn (fun t => A0 m t a) (Icc 0 T) := fun a =>
      (hW0 m a).continuousOn
    have hc : ∀ i a, ContinuousOn (fun t => A m t i a) (Icc 0 T) := fun i a =>
      (hW m i a).continuousOn
    have iconn : IntegrableOn (connSq (A0 m) (A m)) (Ioc 0 T) := by
      refine integrableOn_of_continuousOn ?_
      exact (continuousOn_finsetSum _ fun a _ => continuous_gridNormSq.comp_continuousOn
        (hc0 a)).add (continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun a _ =>
          continuous_gridNormSq.comp_continuousOn (hc i a))
    have igrad : IntegrableOn (gradTemporalSq (A0 m)) (Ioc 0 T) :=
      integrableOn_of_continuousOn (continuousOn_finsetSum _ fun i _ =>
        continuousOn_finsetSum _ fun a _ => continuousOn_comp_linear (hc0 a) (Dp i))
    have icod : IntegrableOn (codiffSq (A m)) (Ioc 0 T) := by
      refine integrableOn_of_continuousOn (continuousOn_finsetSum _ fun a _ => ?_)
      exact continuous_gridNormSq.comp_continuousOn ((continuousOn_finsetSum _ fun i _ =>
        (Dm i).continuous_of_finiteDimensional.comp_continuousOn (hc i a)).neg)
    have ilhs : IntegrableOn (fun t => ∑ μa, (gridNormSq (fullConn (A0 m) (A m) t μa) +
        coordForm (fullConn (A0 m) (A m) t μa))) (Ioc 0 T) :=
      integrableOn_of_continuousOn (continuousOn_finsetSum _ fun μa _ =>
        (continuous_gridNormSq.comp_continuousOn (hWf m μa).continuousOn).add
          (continuous_coordForm.comp_continuousOn (hWf m μa).continuousOn))
    have irhs : IntegrableOn (fun t => connSq (A0 m) (A m) t + gradTemporalSq (A0 m) t +
        codiffSq (A m) t + 3 * (twoFormSq (R m) t + twoFormSq (Q m) t + twoFormSq (E m) t))
        (Ioc 0 T) :=
      ((iconn.add igrad).add icod).add (((hR m).add (hQ m)).add (hE m) |>.const_mul 3)
    have hmono := setIntegral_mono_on ilhs irhs measurableSet_Ioc fun t ht =>
      energy_le_of_incidence (A0 m) (A m) (R m) (Q m) (E m) t (hinc m t ht)
    refine hmono.trans ?_
    have iX : IntegrableOn (fun t => connSq (A0 m) (A m) t + gradTemporalSq (A0 m) t +
        codiffSq (A m) t) (Ioc 0 T) := (iconn.add igrad).add icod
    have iX2 : IntegrableOn (fun t => connSq (A0 m) (A m) t + gradTemporalSq (A0 m) t)
        (Ioc 0 T) := iconn.add igrad
    have iY : IntegrableOn (fun t => twoFormSq (R m) t + twoFormSq (Q m) t + twoFormSq (E m) t)
        (Ioc 0 T) := ((hR m).add (hQ m)).add (hE m)
    have iY2 : IntegrableOn (fun t => twoFormSq (R m) t + twoFormSq (Q m) t)
        (Ioc 0 T) := (hR m).add (hQ m)
    have iY3 : IntegrableOn (fun t => 3 * (twoFormSq (R m) t + twoFormSq (Q m) t +
        twoFormSq (E m) t)) (Ioc 0 T) := iY.const_mul 3
    have s1 := integral_add iX iY3
    have s2 := integral_add iX2 icod
    have s3 := integral_add iconn igrad
    have s4 := integral_add iY2 (hE m)
    have s5 := integral_add (hR m) (hQ m)
    have s6 := integral_const_mul (μ := volume.restrict (Ioc 0 T)) (3 : ℝ)
      (fun t => twoFormSq (R m) t + twoFormSq (Q m) t + twoFormSq (E m) t)
    beta_reduce at s1 s2 s3 s4 s5 s6
    rw [s1, s2, s3, s6, s4, s5]
    have nconn : ∀ t, 0 ≤ connSq (A0 m) (A m) t := fun t =>
      add_nonneg (Finset.sum_nonneg fun _ _ => gridNormSq_nonneg _)
        (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => gridNormSq_nonneg _)
    have ngrad : ∀ t, 0 ≤ gradTemporalSq (A0 m) t := fun t =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => gridNormSq_nonneg _
    have ncod : ∀ t, 0 ≤ codiffSq (A m) t := fun t =>
      Finset.sum_nonneg fun _ _ => gridNormSq_nonneg _
    have e1 := integral_le_sq_of_l2t_le nconn (hb m).1
    have e2 := integral_le_sq_of_l2t_le (twoFormSq_nonneg (R m)) (hb m).2.1
    have e3 := integral_le_sq_of_l2t_le (twoFormSq_nonneg (Q m)) (hQb m)
    have e4 := integral_le_sq_of_l2t_le (twoFormSq_nonneg (E m)) (hb m).2.2.2.1
    have e5 := integral_le_sq_of_l2t_le ncod (hb m).2.2.2.2.1
    have e6 := integral_le_sq_of_l2t_le ngrad (hb m).2.2.2.2.2.1
    rw [hBdef]
    linarith
  -- the temporal `L²_t H⁻¹_x` budget
  have hB1 : ∀ m, ∫ t in Ioc 0 T, ∑ μa, trigNegSq 1 (interp (fullConn (G0 m) (G m) t μa)) ≤
      CK ^ 2 := by
    intro m
    have e : ∀ t, ∑ μa, trigNegSq 1 (interp (fullConn (G0 m) (G m) t μa)) =
        dtNegSq (G0 m) (G m) t := fun t =>
      sum_fullConn (G0 m) (G m) t (fun u => trigNegSq 1 (interp u))
    simp only [e]
    refine integral_le_sq_of_l2t_le (fun t => ?_) (hb m).2.2.2.2.2.2
    exact add_nonneg (Finset.sum_nonneg fun _ _ => trigNegSq_nonneg _ _)
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => trigNegSq_nonneg _ _)
  exact gridAubinLions_limit hT (fun m => fullConn (A0 m) (A m)) (fun m => fullConn (G0 m) (G m))
    hWf 1 hB hB1

/-! ### Bundled hypotheses, the common subsequence on an exhaustion -/

/-- The hypothesis packet of `thm:main-hodge-connection` on the cylinder `(0,T] × 𝕋³`, uniformly
over the regulators `m`: `W^{1,2}` time representations, the incidence
`eq:main-connection-hodge-incidence` with its product bound, `L²_{t,h}` integrability of
`R, 𝒬, ε`, and the budget `eq:main-connection-hodge-budget` with constant `C_K`. -/
structure HodgeTemporalBudget {N : ℕ → ℕ} [∀ m, NeZero (N m)] (T CQ CK : ℝ)
    (A0 G0 : ∀ m, ℝ → Fin d → Grid (N m) → ℂ) (A G : ∀ m, ℝ → Fin 3 → Fin d → Grid (N m) → ℂ)
    (R Q E : ∀ m, ℝ → Fin 3 → Fin 3 → Fin d → Grid (N m) → ℂ) : Prop where
  w12_temporal : ∀ m a, IsGridW12Rep T (fun t => A0 m t a) (fun t => G0 m t a)
  w12_spatial : ∀ m i a, IsGridW12Rep T (fun t => A m t i a) (fun t => G m t i a)
  incidence : ∀ m, ∀ t ∈ Ioc 0 T, ∀ i j, i < j → ∀ a,
    curl (A m) t i j a = R m t i j a - Q m t i j a + E m t i j a
  integrable_R : ∀ m, IntegrableOn (twoFormSq (R m)) (Ioc 0 T)
  integrable_Q : ∀ m, IntegrableOn (twoFormSq (Q m)) (Ioc 0 T)
  integrable_E : ∀ m, IntegrableOn (twoFormSq (E m)) (Ioc 0 T)
  product : ∀ m, l2t T (twoFormSq (Q m)) ≤ CQ * l4Sq T (A m)
  budget : ∀ m, l2t T (connSq (A0 m) (A m)) + l2t T (twoFormSq (R m)) + l4Sq T (A m) +
    l2t T (twoFormSq (E m)) + l2t T (codiffSq (A m)) + l2t T (gradTemporalSq (A0 m)) +
    l2t T (dtNegSq (G0 m) (G m)) ≤ CK

/-- The hypothesis packet is stable under passing to a subsequence of regulators. -/
theorem HodgeTemporalBudget.comp {N : ℕ → ℕ} [∀ m, NeZero (N m)] {T CQ CK : ℝ}
    {A0 G0 : ∀ m, ℝ → Fin d → Grid (N m) → ℂ} {A G : ∀ m, ℝ → Fin 3 → Fin d → Grid (N m) → ℂ}
    {R Q E : ∀ m, ℝ → Fin 3 → Fin 3 → Fin d → Grid (N m) → ℂ}
    (h : HodgeTemporalBudget T CQ CK A0 G0 A G R Q E) (ψ : ℕ → ℕ) :
    HodgeTemporalBudget (N := fun m => N (ψ m)) T CQ CK (fun m => A0 (ψ m)) (fun m => G0 (ψ m))
      (fun m => A (ψ m)) (fun m => G (ψ m)) (fun m => R (ψ m)) (fun m => Q (ψ m))
      (fun m => E (ψ m)) where
  w12_temporal m := h.w12_temporal (ψ m)
  w12_spatial m := h.w12_spatial (ψ m)
  incidence m := h.incidence (ψ m)
  integrable_R m := h.integrable_R (ψ m)
  integrable_Q m := h.integrable_Q (ψ m)
  integrable_E m := h.integrable_E (ψ m)
  product m := h.product (ψ m)
  budget m := h.budget (ψ m)

/-- `thm:main-hodge-connection`, bundled form: under the hypothesis packet on `(0,T] × 𝕋³`,
a subsequence of the interpolated full connections converges in `L²((0,T] × 𝕋³)`. -/
theorem HodgeTemporalBudget.compact {N : ℕ → ℕ} [∀ m, NeZero (N m)] {T CQ CK : ℝ}
    (hT : 0 < T)
    {A0 G0 : ∀ m, ℝ → Fin d → Grid (N m) → ℂ} {A G : ∀ m, ℝ → Fin 3 → Fin d → Grid (N m) → ℂ}
    {R Q E : ∀ m, ℝ → Fin 3 → Fin 3 → Fin d → Grid (N m) → ℂ}
    (h : HodgeTemporalBudget T CQ CK A0 G0 A G R Q E) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Ω : Option (Fin 3) × Fin d → ℝ × UnitAddTorus (Fin 3) → ℂ,
      ∀ μa, MemLp (Ω μa) 2 (cylMeasure T) ∧
        Tendsto (fun m => ∫ p, ‖field (fun t => fullConn (A0 (φ m)) (A (φ m)) t μa) p -
          Ω μa p‖ ^ 2 ∂cylMeasure T) atTop (𝓝 0) :=
  hodge_connection_compactness hT A0 G0 A G h.w12_temporal h.w12_spatial R Q E h.incidence
    h.integrable_R h.integrable_Q h.integrable_E h.product h.budget

/-- **Diagonal extraction.**  Let `P j` (`j ∈ ℕ`) be properties of index maps such that every
strictly monotone `ψ` has a further subsequence `ψ ∘ τ` with `P j`, and such that `P j` passes to
any `ψ'` that eventually equals `ψ ∘ σ` with `σ → ∞`.  Then a single strictly monotone `φ`
satisfies every `P j`. -/
theorem exists_strictMono_forall_of_diag (P : ℕ → (ℕ → ℕ) → Prop)
    (hext : ∀ j (ψ : ℕ → ℕ), StrictMono ψ → ∃ τ : ℕ → ℕ, StrictMono τ ∧ P j (ψ ∘ τ))
    (htail : ∀ j (ψ ψ' : ℕ → ℕ), P j ψ → (∃ σ : ℕ → ℕ, Tendsto σ atTop atTop ∧
      ∀ᶠ n in atTop, ψ' n = ψ (σ n)) → P j ψ') :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ j, P j φ := by
  classical
  -- `next j ψ` refines `ψ` so that `P j` holds
  let next : ℕ → {ψ : ℕ → ℕ // StrictMono ψ} → {ψ : ℕ → ℕ // StrictMono ψ} := fun j ψ =>
    ⟨ψ.1 ∘ Classical.choose (hext j ψ.1 ψ.2),
      ψ.2.comp (Classical.choose_spec (hext j ψ.1 ψ.2)).1⟩
  have hnext : ∀ j ψ, P j (next j ψ).1 := fun j ψ => (Classical.choose_spec (hext j ψ.1 ψ.2)).2
  let seq : ℕ → {ψ : ℕ → ℕ // StrictMono ψ} := fun j =>
    Nat.rec (next 0 ⟨id, strictMono_id⟩) (fun j ψ => next (j + 1) ψ) j
  have hseq0 : seq 0 = next 0 ⟨id, strictMono_id⟩ := rfl
  have hseqs : ∀ j, seq (j + 1) = next (j + 1) (seq j) := fun j => rfl
  have hP : ∀ j, P j (seq j).1 := by
    intro j
    cases j with
    | zero => rw [hseq0]; exact hnext 0 _
    | succ j => rw [hseqs]; exact hnext (j + 1) _
  -- `seq (j + k)` is a subsequence of `seq j`
  have hsub : ∀ j k, ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ (seq (j + k)).1 = (seq j).1 ∘ ρ := by
    intro j k
    induction k with
    | zero => exact ⟨id, strictMono_id, rfl⟩
    | succ k ih =>
      obtain ⟨ρ, hρ, e⟩ := ih
      refine ⟨ρ ∘ Classical.choose (hext (j + k + 1) (seq (j + k)).1 (seq (j + k)).2),
        hρ.comp (Classical.choose_spec (hext (j + k + 1) (seq (j + k)).1
          (seq (j + k)).2)).1, ?_⟩
      rw [← Nat.add_assoc, hseqs]
      change (seq (j + k)).1 ∘ _ = _
      funext x
      exact congrFun e _
  refine ⟨fun n => (seq n).1 n, ?_, fun j => ?_⟩
  · refine strictMono_nat_of_lt_succ fun n => ?_
    change (seq n).1 n < (seq (n + 1)).1 (n + 1)
    rw [hseqs]
    change (seq n).1 n < (seq n).1 (Classical.choose (hext (n + 1) (seq n).1 (seq n).2) (n + 1))
    refine (seq n).2 ?_
    have := (Classical.choose_spec (hext (n + 1) (seq n).1 (seq n).2)).1.id_le (n + 1)
    exact lt_of_lt_of_le (Nat.lt_succ_self n) this
  · have hex : ∀ n, j ≤ n → ∃ r, n ≤ r ∧ (seq n).1 n = (seq j).1 r := by
      intro n hn
      obtain ⟨ρ, hρ, e⟩ := hsub j (n - j)
      rw [Nat.add_sub_cancel' hn] at e
      exact ⟨ρ n, hρ.id_le n, by rw [e]; rfl⟩
    let σ : ℕ → ℕ := fun n => if h : j ≤ n then Classical.choose (hex n h) else 0
    refine htail j (seq j).1 _ (hP j) ⟨σ, ?_, ?_⟩
    · refine tendsto_atTop_mono' atTop ?_ tendsto_id
      filter_upwards [eventually_ge_atTop j] with n hn
      simp only [σ, dif_pos hn, id]
      exact (Classical.choose_spec (hex n hn)).1
    · filter_upwards [eventually_ge_atTop j] with n hn
      simp only [σ, dif_pos hn]
      exact (Classical.choose_spec (hex n hn)).2

/-- **`thm:main-hodge-connection` with `ass:main-connection-compactness`** (common subsequence on
a countable cylinder exhaustion).  If the hypothesis packet holds on every cylinder
`(0, T j] × 𝕋³` of a countable family (e.g. an exhaustion `T j ↑ ∞`), with constants
`C_𝒬(j), C_K(j)`, then one subsequence of the interpolated full connections converges in
`L²((0, T j] × 𝕋³)` for every `j`. -/
theorem hodge_connection_exhaustion {N : ℕ → ℕ} [∀ m, NeZero (N m)] {T CQ CK : ℕ → ℝ}
    (hT : ∀ j, 0 < T j)
    {A0 G0 : ∀ m, ℝ → Fin d → Grid (N m) → ℂ} {A G : ∀ m, ℝ → Fin 3 → Fin d → Grid (N m) → ℂ}
    {R Q E : ∀ m, ℝ → Fin 3 → Fin 3 → Fin d → Grid (N m) → ℂ}
    (h : ∀ j, HodgeTemporalBudget (T j) (CQ j) (CK j) A0 G0 A G R Q E) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ j,
      ∃ Ω : Option (Fin 3) × Fin d → ℝ × UnitAddTorus (Fin 3) → ℂ,
        ∀ μa, MemLp (Ω μa) 2 (cylMeasure (T j)) ∧
          Tendsto (fun m => ∫ p, ‖field (fun t => fullConn (A0 (φ m)) (A (φ m)) t μa) p -
            Ω μa p‖ ^ 2 ∂cylMeasure (T j)) atTop (𝓝 0) := by
  refine exists_strictMono_forall_of_diag (fun j φ =>
    ∃ Ω : Option (Fin 3) × Fin d → ℝ × UnitAddTorus (Fin 3) → ℂ,
      ∀ μa, MemLp (Ω μa) 2 (cylMeasure (T j)) ∧
        Tendsto (fun m => ∫ p, ‖field (fun t => fullConn (A0 (φ m)) (A (φ m)) t μa) p -
          Ω μa p‖ ^ 2 ∂cylMeasure (T j)) atTop (𝓝 0)) ?_ ?_
  · intro j ψ _
    obtain ⟨τ, hτ, Ω, hΩ⟩ := ((h j).comp ψ).compact (hT j)
    exact ⟨τ, hτ, Ω, hΩ⟩
  · rintro j ψ ψ' ⟨Ω, hΩ⟩ ⟨σ, hσ, he⟩
    refine ⟨Ω, fun μa => ⟨(hΩ μa).1, ?_⟩⟩
    have h2 := (hΩ μa).2.comp hσ
    refine h2.congr' ?_
    filter_upwards [he] with n hn
    simp only [Function.comp_apply]
    rw [hn]

/-- Non-vacuity of the hypothesis packet: the zero connection on any grid sequence satisfies it
with any `C_K ≥ 0`. -/
example (T : ℝ) : HodgeTemporalBudget (d := 1) (N := fun _ => 3) T 0 0
    (fun _ _ _ _ => 0) (fun _ _ _ _ => 0) (fun _ _ _ _ _ => 0) (fun _ _ _ _ _ => 0)
    (fun _ _ _ _ _ _ => 0) (fun _ _ _ _ _ _ => 0) (fun _ _ _ _ _ _ => 0) where
  w12_temporal _ _ _ := ⟨MemLp.zero', fun t _ => by simp⟩
  w12_spatial _ _ _ _ := ⟨MemLp.zero', fun t _ => by simp⟩
  incidence _ _ _ _ _ _ _ := by simp [curl]
  integrable_R _ := by simp [twoFormSq, PeriodicGridSobolev.gridNormSq]
  integrable_Q _ := by simp [twoFormSq, PeriodicGridSobolev.gridNormSq]
  integrable_E _ := by simp [twoFormSq, PeriodicGridSobolev.gridNormSq]
  product _ := by simp [l2t, twoFormSq, PeriodicGridSobolev.gridNormSq]
  budget _ := by
    simp [l2t, l4Sq, connSq, twoFormSq, codiffSq, codiff, gradTemporalSq, dtNegSq, trigNegSq,
      PeriodicGridSobolev.gridNormSq]

end RenewalGeometry.HodgeConnection
