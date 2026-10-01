/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.OpenWriterGridBridge
import RenewalGeometry.Gravity.OpenWriterHarmonicChart

/-!
# All-component shifted nonlinear energy of the open writer
  (`thm:supp-open-energy`, `eq:supp-open-energy`, `eq:supp-open-commuted-row`,
  `eq:supp-open-remainder`, `eq:supp-open-energy-inequality`; emergent-spacetime manuscript)

The ten-component record `X = (q, v)` (symmetric `4 × 4` arrays on `(ℤ/N)³`, `h = 1/N`) evolves by
the open writer `eq:main-open-writer` with the harmonic coefficients `a = -g^{00}`,
`b^i = -g^{0i}`, `c^{ij} = g^{ij}` and the explicit harmonic first-jet source
(`OpenWriterChart.harmonicWriterAcceleration`).  With `a_α = S^α a`, `c_α = S^α c`,
`q_α = D^α q`, `v_α = D^α v` the shifted energy is (`eq:supp-open-energy`)
`𝓔_{s,h} = ½ Σ_{|α| ≤ s} [⟨v_α, a_α v_α⟩_h + Σ_{ij}⟨D_i⁺q_α, c_α^{ij} D_j⁺q_α⟩_h + ‖q_α‖_h²]`
(`shiftedEnergy`, summed over the ten upper components), and
`‖X‖²_{X^s_h} = ‖q‖²_{s+1,h} + ‖v‖²_{s,h}` (`Xsq`).

Main result `open_energy_inequality` (**`thm:supp-open-energy`**): for every `s ≥ 3` (the
manuscript takes `s ≥ 11`) there are a chart radius `δ > 0` and a constant `C`, both independent of
`N`, such that every solution of the writer (`q_t = v`, `v_t` the writer acceleration on the ten
components, symmetric records) whose state at time `t` lies in the chart `‖X‖_{X^s_h} ≤ δ`
satisfies, at `t`, `d/dt 𝓔_{s,h} ≤ C 𝓔_{s,h} + C 𝓔_{s,h}^{3/2}`; moreover
`¼‖X‖²_{X^s_h} ≤ 𝓔_{s,h}` (energy equivalence, lower half).

Proof structure: exact energy identity (`OpenWriterEnergy.hasDerivAt_energy`) for each
multi-index with the remainder `𝖱_α` of the commuted row; `𝖱_α = rowRem` by
`CommutedRow.commuted_row`; `‖𝖱_α‖_h ≤ C ‖X‖²` (`eq:supp-open-remainder`) from
`CommutedRow.rowRem_norm_le`, the discrete Moser estimates (`Moser.moser_composition_order`) for
`a, a⁻¹, b, c` (order one) and the compensator (order two, `OpenWriterChart`) and the bound
`‖v_t‖_{s-1,h} ≤ C ‖X‖`; the coefficient time derivatives are bounded pointwise by the uniform
embedding `H²_h ⊂ ℓ^∞`.
-/

open Finset Filter Topology
open scoped BigOperators

namespace RenewalGeometry.OpenWriterEnergyEstimate

open RootParityConnector OpenWriterGridBridge OpenWriterChart OpenWriterEnergy HarmonicWriter

noncomputable section

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N]

/-! ### Ten-component records and their norms -/

/-- The ten upper index pairs `μ ≤ ν` of a symmetric record. -/
abbrev Upper := {p : Fin 4 × Fin 4 // p.1 ≤ p.2}

/-- The `(μ, ν)` component array of a record array. -/
def comp (u : Grid N → MetricRec) (μ ν : Fin 4) : Grid N → ℝ := fun x => u x μ ν

/-- A record array is symmetric (ten-component). -/
def IsSymRec (u : Grid N → MetricRec) : Prop := ∀ x μ ν, u x μ ν = u x ν μ

/-- The upper representative of an index pair. -/
def upperOf (μ ν : Fin 4) : Upper :=
  if h : μ ≤ ν then ⟨(μ, ν), h⟩ else ⟨(ν, μ), le_of_lt (not_le.mp h)⟩

theorem comp_upperOf {u : Grid N → MetricRec} (hu : IsSymRec u) (μ ν : Fin 4) :
    comp u (upperOf μ ν).1.1 (upperOf μ ν).1.2 = comp u μ ν := by
  unfold upperOf
  split_ifs with h
  · rfl
  · funext x; exact hu x ν μ

/-- `‖X‖²_{X^s_h} = ‖q‖²_{s+1,h} + ‖v‖²_{s,h}` over the ten components
(`eq:supp-open-norms`). -/
def Xsq (s : ℕ) (q v : Grid N → MetricRec) : ℝ :=
  ∑ κ : Upper, (PeriodicGridSobolev.sobSq (s + 1) (cx (comp q κ.1.1 κ.1.2)) +
    PeriodicGridSobolev.sobSq s (cx (comp v κ.1.1 κ.1.2)))

def Xnorm (s : ℕ) (q v : Grid N → MetricRec) : ℝ := Real.sqrt (Xsq s q v)

theorem Xsq_nonneg (s : ℕ) (q v : Grid N → MetricRec) : 0 ≤ Xsq s q v :=
  sum_nonneg fun _ _ => add_nonneg (PeriodicGridSobolev.sobSq_nonneg _ _)
    (PeriodicGridSobolev.sobSq_nonneg _ _)

theorem Xnorm_nonneg (s : ℕ) (q v : Grid N → MetricRec) : 0 ≤ Xnorm s q v := Real.sqrt_nonneg _

theorem Xnorm_sq (s : ℕ) (q v : Grid N → MetricRec) : Xnorm s q v ^ 2 = Xsq s q v :=
  Real.sq_sqrt (Xsq_nonneg s q v)

theorem sobSq_q_le_Xsq (s : ℕ) {q : Grid N → MetricRec} (hq : IsSymRec q) (v : Grid N → MetricRec)
    (μ ν : Fin 4) {r : ℕ} (hr : r ≤ s + 1) :
    PeriodicGridSobolev.sobSq r (cx (comp q μ ν)) ≤ Xsq s q v := by
  rw [← comp_upperOf hq μ ν]
  refine (PeriodicGridSobolev.sobSq_mono hr _).trans ?_
  refine le_trans ?_ (single_le_sum (f := fun κ : Upper =>
    PeriodicGridSobolev.sobSq (s + 1) (cx (comp q κ.1.1 κ.1.2)) +
    PeriodicGridSobolev.sobSq s (cx (comp v κ.1.1 κ.1.2)))
    (fun _ _ => add_nonneg (PeriodicGridSobolev.sobSq_nonneg _ _)
      (PeriodicGridSobolev.sobSq_nonneg _ _)) (mem_univ (upperOf μ ν)))
  exact le_add_of_nonneg_right (PeriodicGridSobolev.sobSq_nonneg _ _)

theorem sobSq_v_le_Xsq (s : ℕ) (q : Grid N → MetricRec) {v : Grid N → MetricRec} (hv : IsSymRec v)
    (μ ν : Fin 4) {r : ℕ} (hr : r ≤ s) :
    PeriodicGridSobolev.sobSq r (cx (comp v μ ν)) ≤ Xsq s q v := by
  rw [← comp_upperOf hv μ ν]
  refine (PeriodicGridSobolev.sobSq_mono hr _).trans ?_
  refine le_trans ?_ (single_le_sum (f := fun κ : Upper =>
    PeriodicGridSobolev.sobSq (s + 1) (cx (comp q κ.1.1 κ.1.2)) +
    PeriodicGridSobolev.sobSq s (cx (comp v κ.1.1 κ.1.2)))
    (fun _ _ => add_nonneg (PeriodicGridSobolev.sobSq_nonneg _ _)
      (PeriodicGridSobolev.sobSq_nonneg _ _)) (mem_univ (upperOf μ ν)))
  exact le_add_of_nonneg_left (PeriodicGridSobolev.sobSq_nonneg _ _)

theorem sobNorm_q_le (s : ℕ) {q : Grid N → MetricRec} (hq : IsSymRec q) (v : Grid N → MetricRec)
    (μ ν : Fin 4) {r : ℕ} (hr : r ≤ s + 1) :
    PeriodicGridSobolev.sobNorm r (cx (comp q μ ν)) ≤ Xnorm s q v :=
  Real.sqrt_le_sqrt (sobSq_q_le_Xsq s hq v μ ν hr)

theorem sobNorm_v_le (s : ℕ) (q : Grid N → MetricRec) {v : Grid N → MetricRec} (hv : IsSymRec v)
    (μ ν : Fin 4) {r : ℕ} (hr : r ≤ s) :
    PeriodicGridSobolev.sobNorm r (cx (comp v μ ν)) ≤ Xnorm s q v :=
  Real.sqrt_le_sqrt (sobSq_v_le_Xsq s q hv μ ν hr)

/-! ### Coordinates of records and site jets -/

/-- The entry basis of `4 × 4` records. -/
def bM : Module.Basis (Σ _ : Fin 4, Fin 4) ℝ MetricRec :=
  Pi.basis fun _ : Fin 4 => Pi.basisFun ℝ (Fin 4)

theorem bM_repr (g : MetricRec) (k : Σ _ : Fin 4, Fin 4) : bM.repr g k = g k.1 k.2 := by
  simp [bM, Pi.basis_repr, Pi.basisFun_repr]

theorem coordArr_bM (u : Grid N → MetricRec) (k : Σ _ : Fin 4, Fin 4) :
    PeriodicGridSobolev.Moser.coordArr bM u k = cx (comp u k.1 k.2) := by
  funext x; simp [PeriodicGridSobolev.Moser.coordArr, bM_repr, comp]

/-- The entry basis of the site-jet space `(q, v, D⁺q)`. -/
def bJ : Module.Basis ((Σ _ : Fin 4, Fin 4) ⊕ ((Σ _ : Fin 4, Fin 4) ⊕
    (Σ _ : Fin 3, Σ _ : Fin 4, Fin 4))) ℝ JetSpace :=
  bM.prod (bM.prod (Pi.basis fun _ : Fin 3 => bM))

/-- The site-jet array `x ↦ (q(x), v(x), D⁺q(x))`. -/
def jetArr (q v : Grid N → MetricRec) : Grid N → JetSpace :=
  fun x => (q x, v x, fun i => fwd (N : ℝ)⁻¹ (e N) i q x)

theorem comp_fwd (q : Grid N → MetricRec) (i : Fin 3) (μ ν : Fin 4) :
    comp (fun x => fwd (N : ℝ)⁻¹ (e N) i q x) μ ν = OpenWriterEnergy.Dp i (comp q μ ν) := by
  funext x
  simp [comp, fwd, OpenWriterEnergy.Dp, smul_eq_mul]

theorem coordSum_le_card {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (r : ℕ) (b : Module.Basis ι ℝ E) (u : Grid N → E) (M : ℝ)
    (h : ∀ j, PeriodicGridSobolev.sobNorm r (PeriodicGridSobolev.Moser.coordArr b u j) ≤ M) :
    PeriodicGridSobolev.Moser.coordSum r b u ≤ Fintype.card ι * M := by
  unfold PeriodicGridSobolev.Moser.coordSum
  calc ∑ j, PeriodicGridSobolev.sobNorm r (PeriodicGridSobolev.Moser.coordArr b u j)
      ≤ ∑ _j : ι, M := sum_le_sum fun j _ => h j
    _ = Fintype.card ι * M := by simp

theorem coordSum_bM_q_le (s : ℕ) {q : Grid N → MetricRec} (hq : IsSymRec q)
    (v : Grid N → MetricRec) {r : ℕ} (hr : r ≤ s + 1) :
    PeriodicGridSobolev.Moser.coordSum r bM q ≤ 16 * Xnorm s q v := by
  have := coordSum_le_card r bM q (Xnorm s q v) fun k => by
    rw [coordArr_bM]; exact sobNorm_q_le s hq v _ _ hr
  simpa using this

theorem coordSum_bM_v_le (s : ℕ) (q : Grid N → MetricRec) {v : Grid N → MetricRec}
    (hv : IsSymRec v) {r : ℕ} (hr : r ≤ s) :
    PeriodicGridSobolev.Moser.coordSum r bM v ≤ 16 * Xnorm s q v := by
  have := coordSum_le_card r bM v (Xnorm s q v) fun k => by
    rw [coordArr_bM]; exact sobNorm_v_le s q hv _ _ hr
  simpa using this

theorem coordSum_bJ_le (s : ℕ) {q v : Grid N → MetricRec} (hq : IsSymRec q) (hv : IsSymRec v) :
    PeriodicGridSobolev.Moser.coordSum s bJ (jetArr q v) ≤ 80 * Xnorm s q v := by
  have := coordSum_le_card s bJ (jetArr q v) (Xnorm s q v) fun k => by
    rcases k with k | k | ⟨i, k⟩
    · have e : PeriodicGridSobolev.Moser.coordArr bJ (jetArr q v) (Sum.inl k) =
          cx (comp q k.1 k.2) := by
        funext x
        simp [PeriodicGridSobolev.Moser.coordArr, bJ, Module.Basis.prod_repr_inl, bM_repr,
          jetArr, comp]
      rw [e]; exact sobNorm_q_le s hq v _ _ (by omega)
    · have e : PeriodicGridSobolev.Moser.coordArr bJ (jetArr q v) (Sum.inr (Sum.inl k)) =
          cx (comp v k.1 k.2) := by
        funext x
        simp [PeriodicGridSobolev.Moser.coordArr, bJ, Module.Basis.prod_repr_inr,
          Module.Basis.prod_repr_inl, bM_repr, jetArr, comp]
      rw [e]; exact sobNorm_v_le s q hv _ _ le_rfl
    · have e : PeriodicGridSobolev.Moser.coordArr bJ (jetArr q v) (Sum.inr (Sum.inr ⟨i, k⟩)) =
          PeriodicGridSobolev.Dp i (cx (comp q k.1 k.2)) := by
        rw [← cx_Dp, ← comp_fwd]
        funext x
        simp [PeriodicGridSobolev.Moser.coordArr, bJ, Module.Basis.prod_repr_inr, Pi.basis_repr,
          bM_repr, jetArr, comp]
      rw [e]
      exact (PeriodicGridSobolev.CommutedRow.sobNorm_Dp_le s i _).trans (sobNorm_q_le s hq v _ _ le_rfl)
  simpa using this

/-! ### Coefficient arrays and the writer row -/

/-- `a(g)` along a record array, `g = η + q`. -/
def aArr (q : Grid N → MetricRec) : Grid N → ℝ := fun x => harmA (minkowski + q x)

/-- `c^{ij}(g)` along a record array. -/
def cArr (q : Grid N → MetricRec) (i j : Fin 3) : Grid N → ℝ := fun x => harmC i j (minkowski + q x)

/-- `b^i(g)` along a record array. -/
def bArr (q : Grid N → MetricRec) (i : Fin 3) : Grid N → ℝ := fun x => harmB i (minkowski + q x)

/-- The compensator array `𝖦_h(q, v)`. -/
def Garr (q v : Grid N → MetricRec) : Grid N → MetricRec := fun x => compensatorMap (jetArr q v x)

/-- **The writer row, componentwise**: `a v_t = Σ D_i⁻(c^{ij} D_j⁺ q) - 𝖪_b v + 𝖦_h`. -/
theorem writer_row (q v : Grid N → MetricRec) (x : Grid N) (μ ν : Fin 4) (ha : aArr q x ≠ 0) :
    aArr q x * comp (harmonicWriterAcceleration q v) μ ν x =
      divArr (cArr q) (comp q μ ν) x - skewArr (bArr q) (comp v μ ν) x +
        comp (Garr q v) μ ν x := by
  have e1 : comp (harmonicWriterAcceleration q v) μ ν x = (aArr q x)⁻¹ *
      writerRhs harmC harmB harmonicSource (fun i j g w => fderiv ℝ (harmC i j) g w)
        (fun i g w => fderiv ℝ (harmB i) g w) minkowski (N : ℝ)⁻¹ (e N) q v x μ ν := by
    simp [comp, harmonicWriterAcceleration, openWriterAcceleration, writerAcceleration, aArr]
  rw [e1, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  have h1 : divergenceFlux harmC minkowski (N : ℝ)⁻¹ (e N) q x μ ν = divArr (cArr q) (comp q μ ν) x := by
    simp only [divergenceFlux, divArr, Finset.sum_apply]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    simp only [bwd, fwd, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, OpenWriterEnergy.Dm_apply,
      OpenWriterEnergy.Dp_apply, cArr, comp, inv_inv]
  have h2 : skewTransport harmB minkowski (N : ℝ)⁻¹ (e N) q v x μ ν =
      skewArr (bArr q) (comp v μ ν) x := by
    simp only [skewTransport, skewArr, Finset.sum_apply, Pi.add_apply]
    refine sum_congr rfl fun i _ => ?_
    simp only [ctr, fwd, bwd, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul,
      OpenWriterEnergy.D0_apply, OpenWriterEnergy.Dm_apply, OpenWriterEnergy.Dp_apply, bArr,
      comp, inv_inv]
    ring
  have h3 : compensator harmonicSource (fun i j g w => fderiv ℝ (harmC i j) g w)
      (fun i g w => fderiv ℝ (harmB i) g w) minkowski (N : ℝ)⁻¹ (e N) q v x μ ν =
      comp (Garr q v) μ ν x := by
    rw [compensator_eq]; rfl
  simp only [writerRhs, Pi.add_apply, Pi.sub_apply]
  rw [h1, h2, h3]

/-- The complex form of the writer row. -/
theorem writer_row_cx (q v : Grid N → MetricRec) (μ ν : Fin 4) (ha : ∀ x, aArr q x ≠ 0) :
    cx (aArr q) * cx (comp (harmonicWriterAcceleration q v) μ ν) =
      ∑ i, ∑ j, PeriodicGridSobolev.Dm i (cx (cArr q i j) *
          PeriodicGridSobolev.Dp j (cx (comp q μ ν))) -
        ∑ i, (cx (bArr q i) * PeriodicGridSobolev.D0 i (cx (comp v μ ν)) +
          PeriodicGridSobolev.D0 i (cx (bArr q i) * cx (comp v μ ν))) +
        cx (comp (Garr q v) μ ν) := by
  rw [← cx_mul, ← cx_divArr, ← cx_skewArr, ← cx_sub, ← cx_add]
  congr 1
  funext x
  exact writer_row q v x μ ν (ha x)

/-- The remainder `𝖱_α` of the commuted row, defined so that the row holds exactly. -/
def Rrow (α : Fin 3 → ℕ) (q v : Grid N → MetricRec) (μ ν : Fin 4) : Grid N → ℝ :=
  fun x => SαR α (aArr q) x * DαR α (comp (harmonicWriterAcceleration q v) μ ν) x
    - divArr (fun i j => SαR α (cArr q i j)) (DαR α (comp q μ ν)) x
    + skewArr (fun i => SαR α (bArr q i)) (DαR α (comp v μ ν)) x

/-- `𝖱_α` is the explicit commutator remainder `rowRem` (`eq:supp-open-commuted-row`). -/
theorem cx_Rrow (α : Fin 3 → ℕ) (q v : Grid N → MetricRec) (μ ν : Fin 4)
    (ha : ∀ x, aArr q x ≠ 0) :
    cx (Rrow α q v μ ν) = PeriodicGridSobolev.CommutedRow.rowRem α (cx (aArr q))
      (cx (comp (harmonicWriterAcceleration q v) μ ν)) (cx (comp v μ ν)) (cx (comp q μ ν))
      (cx (comp (Garr q v) μ ν)) (fun i j => cx (cArr q i j)) (fun i => cx (bArr q i)) := by
  have hrow := PeriodicGridSobolev.CommutedRow.commuted_row α _ _ _ _ _
    (fun i j => cx (cArr q i j)) (fun i => cx (bArr q i)) (writer_row_cx q v μ ν ha)
  have e : Rrow α q v μ ν = (fun x => SαR α (aArr q) x *
      DαR α (comp (harmonicWriterAcceleration q v) μ ν) x)
      - divArr (fun i j => SαR α (cArr q i j)) (DαR α (comp q μ ν))
      + skewArr (fun i => SαR α (bArr q i)) (DαR α (comp v μ ν)) := by
    funext x; simp [Rrow]
  rw [e, cx_add, cx_sub, cx_fun_mul, cx_divArr, cx_skewArr, cx_SαR, cx_DαR]
  simp only [cx_SαR, cx_DαR]
  rw [hrow]
  abel

/-! ### The shifted energy and its exact time derivative -/

/-- **The shifted energy** `𝓔_{s,h}` of `eq:supp-open-energy` over the ten components. -/
def shiftedEnergy (s : ℕ) (q v : Grid N → MetricRec) : ℝ :=
  ∑ α ∈ PeriodicGridSobolev.multiIndices s,
    energy (SαR α (aArr q)) (fun i j => SαR α (cArr q i j))
      (fun κ : Upper => DαR α (comp q κ.1.1 κ.1.2)) (fun κ : Upper => DαR α (comp v κ.1.1 κ.1.2))

/-- `ȧ = Da(g)[v]` along the record. -/
def adot (q v : Grid N → MetricRec) : Grid N → ℝ :=
  fun x => fderiv ℝ harmA (minkowski + q x) (v x)

/-- `ċ^{ij} = Dc^{ij}(g)[v]` along the record. -/
def cdot (q v : Grid N → MetricRec) (i j : Fin 3) : Grid N → ℝ :=
  fun x => fderiv ℝ (harmC i j) (minkowski + q x) (v x)

/-- The right-hand side of the exact energy identity `eq:supp-open-energy-identity`. -/
def energyRate (s : ℕ) (q v : Grid N → MetricRec) : ℝ :=
  ∑ α ∈ PeriodicGridSobolev.multiIndices s, ((N : ℝ) ^ 3)⁻¹ * ∑ κ : Upper, ∑ x,
    ((1 / 2) * (DαR α (comp v κ.1.1 κ.1.2) x * (SαR α (adot q v) x * DαR α (comp v κ.1.1 κ.1.2) x)) +
      (1 / 2) * ∑ i, ∑ j, OpenWriterEnergy.Dp i (DαR α (comp q κ.1.1 κ.1.2)) x *
        (SαR α (cdot q v i j) x * OpenWriterEnergy.Dp j (DαR α (comp q κ.1.1 κ.1.2)) x) +
      DαR α (comp q κ.1.1 κ.1.2) x * DαR α (comp v κ.1.1 κ.1.2) x +
      DαR α (comp v κ.1.1 κ.1.2) x * Rrow α q v κ.1.1 κ.1.2 x)

theorem minkowski_symm (μ ν : Fin 4) : minkowski μ ν = minkowski ν μ := by
  unfold minkowski; split_ifs <;> simp_all

/-- **Exact energy identity** for the shifted energy along a writer solution. -/
theorem hasDerivAt_shiftedEnergy (s : ℕ) (q v : ℝ → Grid N → MetricRec) (t : ℝ)
    (hsym : IsSymRec (q t))
    (hq : ∀ x, HasDerivAt (fun τ => q τ x) (v t x) t)
    (hv : ∀ x (κ : Upper), HasDerivAt (fun τ => v τ x κ.1.1 κ.1.2)
      (harmonicWriterAcceleration (q t) (v t) x κ.1.1 κ.1.2) t)
    (hdA : ∀ x, DifferentiableAt ℝ harmA (minkowski + q t x))
    (hdC : ∀ x i j, DifferentiableAt ℝ (harmC i j) (minkowski + q t x)) :
    HasDerivAt (fun τ => shiftedEnergy s (q τ) (v τ)) (energyRate s (q t) (v t)) t := by
  unfold shiftedEnergy energyRate
  refine HasDerivAt.fun_sum fun α _ => ?_
  have hg : ∀ y, HasDerivAt (fun τ => minkowski + q τ y) (v t y) t := fun y =>
    (hq y).const_add minkowski
  have hcomp : ∀ (μ ν : Fin 4) x, HasDerivAt (fun τ => comp (q τ) μ ν x) (comp (v t) μ ν x) t := by
    intro μ ν x
    have h1 := hasDerivAt_pi.1 (hq x) μ
    exact hasDerivAt_pi.1 h1 ν
  refine hasDerivAt_energy (fun τ (κ : Upper) => DαR α (comp (q τ) κ.1.1 κ.1.2))
    (fun τ (κ : Upper) => DαR α (comp (v τ) κ.1.1 κ.1.2)) (fun τ => SαR α (aArr (q τ)))
    (fun τ i j => SαR α (cArr (q τ) i j)) (fun i => SαR α (bArr (q t) i))
    (fun κ => DαR α (comp (harmonicWriterAcceleration (q t) (v t)) κ.1.1 κ.1.2))
    (SαR α (adot (q t) (v t))) (fun i j => SαR α (cdot (q t) (v t) i j))
    (fun κ => Rrow α (q t) (v t) κ.1.1 κ.1.2) t ?_ ?_ ?_ ?_ ?_ ?_
  · intro κ x
    exact hasDerivAt_DαR (fun y => hcomp κ.1.1 κ.1.2 y) α x
  · intro κ x
    exact hasDerivAt_DαR (u := fun τ => comp (v τ) κ.1.1 κ.1.2) (fun y => hv y κ) α x
  · intro x
    exact (hdA (x + svec α)).hasFDerivAt.comp_hasDerivAt t (hg (x + svec α))
  · intro i j x
    exact (hdC (x + svec α) i j).hasFDerivAt.comp_hasDerivAt t (hg (x + svec α))
  · intro i j x
    simp only [SαR, cArr]
    refine harmC_symm _ (fun μ ν => ?_) i j
    simp only [Pi.add_apply]
    rw [minkowski_symm, hsym]
  · intro κ x
    simp only [Rrow]
    ring

/-! ### Uniform constants -/

/-- Uniformization of `(δ, C)`-statements over a finite family. -/
theorem uniformize {ι : Type*} [Fintype ι] (P : ι → ℝ → ℝ → Prop)
    (hmono : ∀ i δ δ' C C', 0 < δ' → δ' ≤ δ → C ≤ C' → P i δ C → P i δ' C')
    (h : ∀ i, ∃ δ > 0, ∃ C ≥ 0, P i δ C) : ∃ δ > 0, ∃ C ≥ 0, ∀ i, P i δ C := by
  classical
  choose δf hδ Cf hC hP using h
  set T : Finset ℝ := insert 1 (univ.image δf)
  have hT : T.Nonempty := insert_nonempty _ _
  have hpos : 0 < T.min' hT := by
    rw [Finset.lt_min'_iff]
    intro y hy
    rcases mem_insert.mp hy with rfl | hy
    · exact one_pos
    · obtain ⟨i, -, rfl⟩ := mem_image.mp hy; exact hδ i
  refine ⟨T.min' hT, hpos, ∑ i, Cf i, sum_nonneg fun i _ => hC i, fun i => ?_⟩
  refine hmono i (δf i) _ (Cf i) _ hpos (T.min'_le _ (mem_insert_of_mem (mem_image_of_mem _
    (mem_univ i)))) (single_le_sum (fun j _ => hC j) (mem_univ i)) (hP i)

/-- Local chart bounds for an analytic coefficient: near `c` it is differentiable, its derivative
is bounded by `‖DA(c)‖ + 1`, and it is `θ`-close to `A(c)`. -/
theorem eventually_chart {A : MetricRec → ℝ} {c : MetricRec} (hA : AnalyticAt ℝ A c) {θ : ℝ}
    (hθ : 0 < θ) :
    ∀ᶠ g in 𝓝 c, DifferentiableAt ℝ A g ∧ ‖fderiv ℝ A g‖ ≤ ‖fderiv ℝ A c‖ + 1 ∧
      |A g - A c| ≤ θ := by
  have h1 : ∀ᶠ g in 𝓝 c, DifferentiableAt ℝ A g :=
    hA.eventually_analyticAt.mono fun g hg => hg.differentiableAt
  have h2 : ∀ᶠ g in 𝓝 c, ‖fderiv ℝ A g - fderiv ℝ A c‖ < 1 := by
    have := hA.fderiv.continuousAt.eventually (Metric.ball_mem_nhds (fderiv ℝ A c) one_pos)
    exact this.mono fun g hg => by simpa [dist_eq_norm] using hg
  have h3 : ∀ᶠ g in 𝓝 c, |A g - A c| < θ := by
    have := hA.continuousAt.eventually (Metric.ball_mem_nhds (A c) hθ)
    exact this.mono fun g hg => by simpa [Real.dist_eq] using hg
  filter_upwards [h1, h2, h3] with g hg1 hg2 hg3
  refine ⟨hg1, ?_, hg3.le⟩
  have := norm_sub_norm_le (fderiv ℝ A g) (fderiv ℝ A c)
  linarith

/-- The pointwise chart: near Minkowski, `a ≥ ½`, `|c^{ij} - δ^{ij}| ≤ 1/18`, and `a`, `c^{ij}`
are differentiable with bounded derivatives. -/
theorem exists_chart :
    ∃ ε > 0, ∃ M ≥ 0, ∀ g : MetricRec, ‖g - minkowski‖ < ε →
      (DifferentiableAt ℝ harmA g ∧ ‖fderiv ℝ harmA g‖ ≤ M ∧ |harmA g - 1| ≤ 1 / 2) ∧
      ∀ i j, DifferentiableAt ℝ (harmC i j) g ∧ ‖fderiv ℝ (harmC i j) g‖ ≤ M ∧
        |harmC i j g - (if i = j then 1 else 0)| ≤ 1 / 18 := by
  set M := ‖fderiv ℝ harmA minkowski‖ + 1 + ∑ i, ∑ j, (‖fderiv ℝ (harmC i j) minkowski‖ + 1)
  have hA := eventually_chart analyticAt_harmA (θ := 1 / 2) (by norm_num)
  have hC : ∀ᶠ g in 𝓝 minkowski, ∀ i j, DifferentiableAt ℝ (harmC i j) g ∧
      ‖fderiv ℝ (harmC i j) g‖ ≤ ‖fderiv ℝ (harmC i j) minkowski‖ + 1 ∧
      |harmC i j g - harmC i j minkowski| ≤ 1 / 18 := by
    rw [eventually_all]; intro i; rw [eventually_all]; intro j
    exact eventually_chart (analyticAt_harmC i j) (by norm_num)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hA.and hC)
  have hterm : ∀ i j, ‖fderiv ℝ (harmC i j) minkowski‖ + 1 ≤ M := by
    intro i j
    have h1 : ‖fderiv ℝ (harmC i j) minkowski‖ + 1 ≤
        ∑ j', (‖fderiv ℝ (harmC i j') minkowski‖ + 1) :=
      single_le_sum (f := fun j' => ‖fderiv ℝ (harmC i j') minkowski‖ + 1)
        (fun _ _ => by positivity) (mem_univ j)
    have h2 : ∑ j', (‖fderiv ℝ (harmC i j') minkowski‖ + 1) ≤
        ∑ i', ∑ j', (‖fderiv ℝ (harmC i' j') minkowski‖ + 1) :=
      single_le_sum (f := fun i' => ∑ j', (‖fderiv ℝ (harmC i' j') minkowski‖ + 1))
        (fun _ _ => sum_nonneg fun _ _ => by positivity) (mem_univ i)
    have : 0 ≤ ‖fderiv ℝ harmA minkowski‖ + 1 := by positivity
    simp only [M]; linarith
  refine ⟨ε, hε, M, by positivity, fun g hg => ?_⟩
  obtain ⟨⟨ha1, ha2, ha3⟩, hc⟩ := hball (by rw [dist_eq_norm]; exact hg)
  have hsum : 0 ≤ ∑ i, ∑ j, (‖fderiv ℝ (harmC i j) minkowski‖ + 1) :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => by positivity
  refine ⟨⟨ha1, by simp only [M]; linarith, by rwa [harm_minkowski.1] at ha3⟩, fun i j => ?_⟩
  obtain ⟨hc1, hc2, hc3⟩ := hc i j
  refine ⟨hc1, hc2.trans (hterm i j), ?_⟩
  rwa [harm_minkowski.2.2 i j] at hc3

/-- The Moser difference array of a coefficient along a record. -/
theorem moser_array_eq (A : MetricRec → ℝ) (q : Grid N → MetricRec) :
    (fun x => ((A (minkowski + q x) - A minkowski : ℝ) : ℂ)) =
      cx (fun x => A (minkowski + q x)) - fun _ => ((A minkowski : ℝ) : ℂ) := by
  funext x; simp [cx]

/-- Uniform order-one Moser bounds for all the scalar coefficients of the chart, at order `r`. -/
theorem moser_coefficients (r : ℕ) (hr : 2 ≤ r) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (q : Grid N → MetricRec),
      PeriodicGridSobolev.Moser.coordSum r bM q ≤ δ →
      PeriodicGridSobolev.sobNorm r (cx (fun x => harmA (minkowski + q x)) - fun _ => (1 : ℂ))
          ≤ C * PeriodicGridSobolev.Moser.coordSum r bM q ∧
      PeriodicGridSobolev.sobNorm r
          (cx (fun x => (harmA (minkowski + q x))⁻¹) - fun _ => (1 : ℂ))
          ≤ C * PeriodicGridSobolev.Moser.coordSum r bM q ∧
      (∀ i j, PeriodicGridSobolev.sobNorm r (cx (fun x => harmC i j (minkowski + q x)) -
          fun _ => ((if i = j then 1 else 0 : ℝ) : ℂ))
          ≤ C * PeriodicGridSobolev.Moser.coordSum r bM q) ∧
      ∀ i, PeriodicGridSobolev.sobNorm r (cx (fun x => harmB i (minkowski + q x)) -
          fun _ => (0 : ℂ)) ≤ C * PeriodicGridSobolev.Moser.coordSum r bM q := by
  -- the thirteen coefficient maps, indexed by `Fin 2 ⊕ (Fin 3 × Fin 3 ⊕ Fin 3)`
  let F : Fin 2 ⊕ (Fin 3 × Fin 3 ⊕ Fin 3) → MetricRec → ℝ
    | Sum.inl 0 => harmA
    | Sum.inl 1 => fun g => (harmA g)⁻¹
    | Sum.inr (Sum.inl ij) => harmC ij.1 ij.2
    | Sum.inr (Sum.inr i) => harmB i
  have hF : ∀ k, AnalyticAt ℝ (F k) minkowski := by
    rintro (k | ij | i)
    · fin_cases k
      · exact analyticAt_harmA
      · exact analyticAt_harmA_inv
    · exact analyticAt_harmC ij.1 ij.2
    · exact analyticAt_harmB i
  obtain ⟨δ, hδ, C, hC, h⟩ := uniformize (fun k δ C => ∀ (N : ℕ) [NeZero N]
      (q : Grid N → MetricRec), PeriodicGridSobolev.Moser.coordSum r bM q ≤ δ →
      PeriodicGridSobolev.sobNorm r (fun x => ((F k (minkowski + q x) - F k minkowski : ℝ) : ℂ))
        ≤ C * PeriodicGridSobolev.Moser.coordSum r bM q ^ 1)
    (fun k δ δ' C C' _ hδ' hC' hP N _ q hq => (hP N q (hq.trans hδ')).trans (by
      gcongr; exact pow_nonneg (PeriodicGridSobolev.Moser.coordSum_nonneg _ _ _) _))
    (fun k => PeriodicGridSobolev.Moser.moser_analyticAt_order r hr bM (hF k) 1 le_rfl
      (fun _ _ n h1 h2 => absurd h2 (by omega)))
  refine ⟨δ, hδ, C, hC, fun N _ q hq => ⟨?_, ?_, fun i j => ?_, fun i => ?_⟩⟩
  · have := h (Sum.inl 0) N q hq
    simp only [F, pow_one] at this
    convert this using 2
    funext x; simp [cx, harm_minkowski.1]
  · have := h (Sum.inl 1) N q hq
    simp only [F, pow_one] at this
    convert this using 2
    funext x; simp [cx, harm_minkowski.1]
  · have := h (Sum.inr (Sum.inl (i, j))) N q hq
    simp only [F, pow_one] at this
    convert this using 2
    funext x; simp [cx, harm_minkowski.2.2 i j]
  · have := h (Sum.inr (Sum.inr i)) N q hq
    simp only [F, pow_one] at this
    convert this using 2
    funext x; simp [cx, harm_minkowski.2.1 i]

/-- Uniform order-two Moser bound for the compensator (`m = 2`). -/
theorem moser_compensator (r : ℕ) (hr : 2 ≤ r) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (w : Grid N → JetSpace),
      PeriodicGridSobolev.Moser.coordSum r bJ w ≤ δ → ∀ μ ν : Fin 4,
      PeriodicGridSobolev.sobNorm r (cx (fun x => compensatorMap (w x) μ ν))
        ≤ C * PeriodicGridSobolev.Moser.coordSum r bJ w ^ 2 := by
  obtain ⟨δ, hδ, C, hC, h⟩ := uniformize (ι := Fin 4 × Fin 4) (fun k δ C => ∀ (N : ℕ) [NeZero N]
      (w : Grid N → JetSpace), PeriodicGridSobolev.Moser.coordSum r bJ w ≤ δ →
      PeriodicGridSobolev.sobNorm r (fun x =>
        ((compensatorMap (0 + w x) k.1 k.2 - compensatorMap 0 k.1 k.2 : ℝ) : ℂ))
        ≤ C * PeriodicGridSobolev.Moser.coordSum r bJ w ^ 2)
    (fun k δ δ' C C' _ hδ' hC' hP N _ w hw => (hP N w (hw.trans hδ')).trans (by
      gcongr; try exact pow_nonneg (PeriodicGridSobolev.Moser.coordSum_nonneg _ _ _) _))
    (fun k => PeriodicGridSobolev.Moser.moser_analyticAt_order (A := fun w : JetSpace =>
      compensatorMap w k.1 k.2) r hr bJ (analyticAt_compensatorMap k.1 k.2 0) 2 (by norm_num)
      (fun p hp n h1 h2 => by
        obtain rfl : n = 1 := by omega
        exact compensator_series_one_eq_zero k.1 k.2 p hp))
  refine ⟨δ, hδ, C, hC, fun N _ w hw μ ν => ?_⟩
  have := h (μ, ν) N w hw
  simp only [zero_add, compensatorMap_zero, sub_zero] at this
  exact this

/-! ### Fixed-time estimates -/

theorem avg_le {f g : Grid N → ℝ} (h : ∀ x, f x ≤ g x) :
    ((N : ℝ) ^ 3)⁻¹ * ∑ x, f x ≤ ((N : ℝ) ^ 3)⁻¹ * ∑ x, g x := by
  have : (0 : ℝ) ≤ ((N : ℝ) ^ 3)⁻¹ := by positivity
  exact mul_le_mul_of_nonneg_left (sum_le_sum fun x _ => h x) this

theorem avg_sq (u : Grid N → ℝ) :
    ((N : ℝ) ^ 3)⁻¹ * ∑ x, u x ^ 2 = PeriodicGridSobolev.gridNorm (cx u) ^ 2 := by
  rw [PeriodicGridSobolev.gridNorm_sq, gridNormSq_cx]

theorem const_mul_eq_smul (d : ℂ) (w : Grid N → ℂ) : (fun _ => d) * w = d • w := by
  funext x; simp

/-- Product with a coefficient close to a constant `d` with `‖d‖ ≤ 1`. -/
theorem sobNorm_coef_mul_le (r : ℕ) (hr : 2 ≤ r) (c w : Grid N → ℂ) (d : ℂ) (hd : ‖d‖ ≤ 1)
    (hc : PeriodicGridSobolev.sobNorm r (c - fun _ => d) ≤ 1) :
    PeriodicGridSobolev.sobNorm r (c * w) ≤
      (PeriodicGridSobolev.Moser.algConst r + 1) * PeriodicGridSobolev.sobNorm r w := by
  have e : c * w = (c - fun _ => d) * w + d • w := by
    rw [← const_mul_eq_smul, ← add_mul, sub_add_cancel]
  rw [e]
  have h1 := PeriodicGridSobolev.Moser.sobNorm_mul_le r hr (c - fun _ => d) w
  have h2 := PeriodicGridSobolev.Moser.sobNorm_smul r d w
  have hw := PeriodicGridSobolev.Moser.sobNorm_nonneg r w
  have hA := PeriodicGridSobolev.Moser.algConst_pos r
  refine (PeriodicGridSobolev.Moser.sobNorm_add_le r _ _).trans ?_
  rw [h2]
  have : PeriodicGridSobolev.Moser.algConst r * PeriodicGridSobolev.sobNorm r (c - fun _ => d) *
      PeriodicGridSobolev.sobNorm r w ≤ PeriodicGridSobolev.Moser.algConst r * 1 *
      PeriodicGridSobolev.sobNorm r w := by gcongr
  nlinarith

/-- **The right-hand side of the writer row is bounded in `H^{s-1}_h`.** -/
theorem rhs_bound (s : ℕ) (hs : 3 ≤ s) (Wq Wv G : Grid N → ℂ) (c : Fin 3 → Fin 3 → Grid N → ℂ)
    (b : Fin 3 → Grid N → ℂ) (d : Fin 3 → Fin 3 → ℂ) (hd : ∀ i j, ‖d i j‖ ≤ 1) (X K : ℝ)
    (hc : ∀ i j, PeriodicGridSobolev.sobNorm s (c i j - fun _ => d i j) ≤ 1)
    (hb : ∀ i, PeriodicGridSobolev.sobNorm s (b i - fun _ => 0) ≤ 1)
    (hq : ∀ j, PeriodicGridSobolev.sobNorm s (PeriodicGridSobolev.Dp j Wq) ≤ X)
    (hv : PeriodicGridSobolev.sobNorm s Wv ≤ X) (hG : PeriodicGridSobolev.sobNorm s G ≤ K * X) :
    PeriodicGridSobolev.sobNorm (s - 1)
      (∑ i, ∑ j, PeriodicGridSobolev.Dm i (c i j * PeriodicGridSobolev.Dp j Wq) -
        ∑ i, (b i * PeriodicGridSobolev.D0 i Wv + PeriodicGridSobolev.D0 i (b i * Wv)) + G) ≤
      (9 * (PeriodicGridSobolev.Moser.algConst s + 1) +
        3 * PeriodicGridSobolev.Moser.algConst (s - 1) +
        3 * PeriodicGridSobolev.Moser.algConst s + K) * X := by
  open PeriodicGridSobolev PeriodicGridSobolev.Moser PeriodicGridSobolev.CommutedRow in
  have hs1 : s - 1 + 1 = s := by omega
  have hb' : ∀ i, sobNorm s (b i) ≤ 1 := fun i => by
    have e : (b i - fun _ => (0 : ℂ)) = b i := by funext x; simp
    have := hb i; rwa [e] at this
  have hbm : ∀ i, sobNorm (s - 1) (b i) ≤ 1 := fun i => (sobNorm_mono (by omega) _).trans (hb' i)
  have hX : 0 ≤ X := (sobNorm_nonneg _ _).trans hv
  have t1 : ∀ i j, sobNorm (s - 1) (Dm i (c i j * Dp j Wq)) ≤ (algConst s + 1) * X := by
    intro i j
    have := sobNorm_Dm_le (s - 1) i (c i j * Dp j Wq)
    rw [hs1] at this
    refine this.trans ((sobNorm_coef_mul_le s (by omega) _ _ _ (hd i j) (hc i j)).trans ?_)
    have := algConst_pos s
    gcongr
    exact hq j
  have t2 : ∀ i, sobNorm (s - 1) (b i * D0 i Wv) ≤ algConst (s - 1) * X := by
    intro i
    refine (sobNorm_mul_le (s - 1) (by omega) _ _).trans ?_
    have h0 := sobNorm_D0_le (s - 1) i Wv
    rw [hs1] at h0
    have := algConst_pos (s - 1)
    calc algConst (s - 1) * sobNorm (s - 1) (b i) * sobNorm (s - 1) (D0 i Wv)
        ≤ algConst (s - 1) * 1 * X := by
          gcongr
          · exact sobNorm_nonneg _ _
          · exact hbm i
          · exact h0.trans hv
      _ = algConst (s - 1) * X := by ring
  have t3 : ∀ i, sobNorm (s - 1) (D0 i (b i * Wv)) ≤ algConst s * X := by
    intro i
    have h0 := sobNorm_D0_le (s - 1) i (b i * Wv)
    rw [hs1] at h0
    refine h0.trans ((sobNorm_mul_le s (by omega) _ _).trans ?_)
    have := algConst_pos s
    calc algConst s * sobNorm s (b i) * sobNorm s Wv ≤ algConst s * 1 * X := by
          gcongr
          · exact sobNorm_nonneg _ _
          · exact hb' i
      _ = algConst s * X := by ring
  have t4 : sobNorm (s - 1) G ≤ K * X := (sobNorm_mono (by omega) _).trans hG
  calc sobNorm (s - 1) (∑ i, ∑ j, Dm i (c i j * Dp j Wq) -
        ∑ i, (b i * D0 i Wv + D0 i (b i * Wv)) + G)
      ≤ ∑ i, ∑ j, sobNorm (s - 1) (Dm i (c i j * Dp j Wq)) +
        ∑ i, (sobNorm (s - 1) (b i * D0 i Wv) + sobNorm (s - 1) (D0 i (b i * Wv))) +
        sobNorm (s - 1) G := by
        refine (sobNorm_add_le _ _ _).trans (add_le_add ?_ le_rfl)
        refine (sobNorm_sub_le _ _ _).trans (add_le_add ?_ ?_)
        · exact (sobNorm_sum_le _ _ _).trans (sum_le_sum fun i _ => sobNorm_sum_le _ _ _)
        · exact (sobNorm_sum_le _ _ _).trans (sum_le_sum fun i _ => sobNorm_add_le _ _ _)
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, (algConst s + 1) * X +
        ∑ _i : Fin 3, (algConst (s - 1) * X + algConst s * X) + K * X := by
        gcongr with i _ j _ i _ i _
        · exact t1 i j
        · exact t2 i
        · exact t3 i
    _ = _ := by simp; ring

/-! ### Pointwise quadratic forms -/

theorem abs_mul_mul_le (a b c K : ℝ) (hb : |b| ≤ K) : |a * (b * c)| ≤ K * ((a ^ 2 + c ^ 2) / 2) := by
  have hK : 0 ≤ K := (abs_nonneg b).trans hb
  rw [abs_mul, abs_mul]
  have h1 : |a| * |c| ≤ (a ^ 2 + c ^ 2) / 2 := by
    nlinarith [sq_nonneg (|a| - |c|), sq_abs a, sq_abs c]
  calc |a| * (|b| * |c|) = |b| * (|a| * |c|) := by ring
    _ ≤ K * ((a ^ 2 + c ^ 2) / 2) := mul_le_mul hb h1 (by positivity) hK

theorem sum_sum_sq_half (d : Fin 3 → ℝ) :
    ∑ i, ∑ j, (d i ^ 2 + d j ^ 2) / 2 = 3 * ∑ i, d i ^ 2 := by
  simp only [Fin.sum_univ_three]; ring

theorem quad_upper (d : Fin 3 → ℝ) (c : Fin 3 → Fin 3 → ℝ) (K : ℝ) (hc : ∀ i j, |c i j| ≤ K) :
    ∑ i, ∑ j, d i * (c i j * d j) ≤ 3 * K * ∑ i, d i ^ 2 := by
  calc ∑ i, ∑ j, d i * (c i j * d j) ≤ ∑ i, ∑ j, K * ((d i ^ 2 + d j ^ 2) / 2) :=
        sum_le_sum fun i _ => sum_le_sum fun j _ =>
          (le_abs_self _).trans (abs_mul_mul_le _ _ _ _ (hc i j))
    _ = K * ∑ i, ∑ j, (d i ^ 2 + d j ^ 2) / 2 := by simp only [mul_sum]
    _ = 3 * K * ∑ i, d i ^ 2 := by rw [sum_sum_sq_half]; ring

theorem quad_lower (d : Fin 3 → ℝ) (c : Fin 3 → Fin 3 → ℝ)
    (hc : ∀ i j, |c i j - (if i = j then 1 else 0)| ≤ 1 / 18) :
    (1 / 2) * ∑ i, d i ^ 2 ≤ ∑ i, ∑ j, d i * (c i j * d j) := by
  have hsplit : ∑ i, ∑ j, d i * (c i j * d j) = ∑ i, d i ^ 2 +
      ∑ i, ∑ j, d i * ((c i j - (if i = j then 1 else 0)) * d j) := by
    simp only [Fin.sum_univ_three]
    simp
    ring
  have hlow : -(1 / 18 * (3 * ∑ i, d i ^ 2)) ≤
      ∑ i, ∑ j, d i * ((c i j - (if i = j then 1 else 0)) * d j) := by
    rw [← sum_sum_sq_half, mul_sum, ← sum_neg_distrib]
    refine sum_le_sum fun i _ => ?_
    rw [mul_sum, ← sum_neg_distrib]
    refine sum_le_sum fun j _ => ?_
    exact neg_le_of_abs_le (abs_mul_mul_le _ _ _ _ (hc i j))
  have : 0 ≤ ∑ i, d i ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  linarith

/-! ### The fixed-time estimates -/

theorem gridNorm_cx_DαR_le {r : ℕ} {α : Fin 3 → ℕ} (h : PeriodicGridSobolev.deg α ≤ r)
    (u : Grid N → ℝ) :
    PeriodicGridSobolev.gridNorm (cx (DαR α u)) ≤ PeriodicGridSobolev.sobNorm r (cx u) := by
  rw [cx_DαR]; exact PeriodicGridSobolev.CommutedRow.gridNorm_Dα_le_sobNorm h _

theorem gridNorm_cx_Dp_DαR_le {r : ℕ} {α : Fin 3 → ℕ} (h : PeriodicGridSobolev.deg α + 1 ≤ r)
    (i : Fin 3) (u : Grid N → ℝ) :
    PeriodicGridSobolev.gridNorm (cx (OpenWriterEnergy.Dp i (DαR α u))) ≤
      PeriodicGridSobolev.sobNorm r (cx u) := by
  rw [Dp_DαR]
  exact gridNorm_cx_DαR_le (by rw [PeriodicGridSobolev.deg_add_single]; exact h) u

attribute [local irreducible] harmA harmB harmC compensatorMap

set_option maxHeartbeats 4000000 in
/-- **Fixed-time estimates** in the chart: differentiability of the coefficients, the lower
energy bound `¼‖X‖² ≤ 𝓔` and the bound `d𝓔/dt ≤ K‖X‖² + K‖X‖³` of the right-hand side of the
energy identity, with `δ`, `K` independent of the mesh. -/
theorem static_bounds (s : ℕ) (hs : 3 ≤ s) :
    ∃ δ > 0, ∃ K ≥ 0, ∀ (N : ℕ) [NeZero N] (q v : Grid N → MetricRec), IsSymRec q → IsSymRec v →
      Xnorm s q v ≤ δ →
      (∀ x, DifferentiableAt ℝ harmA (minkowski + q x)) ∧
      (∀ x i j, DifferentiableAt ℝ (harmC i j) (minkowski + q x)) ∧
      Xsq s q v / 4 ≤ shiftedEnergy s q v ∧
      energyRate s q v ≤ K * Xsq s q v + K * Xnorm s q v ^ 3 := by
  open PeriodicGridSobolev.Moser in
  obtain ⟨ε, hε, M, hM, hchart⟩ := exists_chart
  obtain ⟨δ1, hδ1, C1, hC1, hm1⟩ := moser_coefficients (s - 1) (by omega)
  obtain ⟨δ2, hδ2, C2, hC2, hm2⟩ := moser_coefficients s (by omega)
  obtain ⟨δ3, hδ3, C3, hC3, hm3⟩ := moser_coefficients (s + 1) (by omega)
  obtain ⟨δG, hδG, CG, hCG, hmG⟩ := moser_compensator s (by omega)
  obtain ⟨Cr, hCr, hrow⟩ := PeriodicGridSobolev.CommutedRow.rowRem_norm_le s hs
  set Bm : ℝ := 1 + ∑ j, ‖bM j‖ with hBm
  have hBm1 : 1 ≤ Bm := by
    have : 0 ≤ ∑ j, ‖bM j‖ := sum_nonneg fun _ _ => norm_nonneg _
    linarith
  have hBj : ∀ j, ‖bM j‖ ≤ Bm := fun j => by
    have := single_le_sum (f := fun j => ‖bM j‖) (fun _ _ => norm_nonneg _) (mem_univ j)
    linarith
  set sK := Real.sqrt PeriodicGridSobolev.Kprod
  have hsK : 0 ≤ sK := Real.sqrt_nonneg _
  set L : ℝ := Bm * sK * 16 + 1
  have hL : 0 < L := by positivity
  set Cs : ℝ := C1 + C2 + C3 + 1
  have hCs : 0 < Cs := by positivity
  set δ : ℝ := min (min 1 (ε / (2 * L))) (min (min (δ1 / 16) (δ2 / 16))
    (min (δ3 / 16) (min (δG / 80) (1 / (16 * Cs)))))
  have hδpos : 0 < δ := by
    simp only [δ, lt_min_iff]; refine ⟨⟨one_pos, by positivity⟩, ⟨by positivity, by positivity⟩,
      by positivity, by positivity, by positivity⟩
  -- constants
  set As := algConst s
  set As1 := algConst (s - 1)
  set K1 : ℝ := M * (Bm * sK * 16)
  set KG : ℝ := CG * 6400
  set K2 : ℝ := (As1 + 1) * (9 * (As + 1) + 3 * As1 + 3 * As + KG)
  set K3 : ℝ := Cr * (16 * C2 * K2 + 9 * (16 * C3) + 3 * (16 * C3)) + KG
  set cM : ℝ := ((PeriodicGridSobolev.multiIndices s).card : ℝ)
  set cU : ℝ := (Fintype.card Upper : ℝ)
  set K : ℝ := cM * cU * (1 + 5 * K1 + K3)
  have hAs := algConst_pos s
  have hAs1 := algConst_pos (s - 1)
  have hK1 : 0 ≤ K1 := by positivity
  have hKG : 0 ≤ KG := by positivity
  have hK2 : 0 ≤ K2 := by positivity
  have hK3 : 0 ≤ K3 := by positivity
  refine ⟨δ, hδpos, K, by positivity, fun N _ q v hq hv hX => ?_⟩
  set X := Xnorm s q v with hXdef
  have hX0 : 0 ≤ X := Xnorm_nonneg s q v
  have hδ1' : δ ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hδε : δ ≤ ε / (2 * L) := (min_le_left _ _).trans (min_le_right _ _)
  have hδd1 : δ ≤ δ1 / 16 :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδd2 : δ ≤ δ2 / 16 :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδd3 : δ ≤ δ3 / 16 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδdG : δ ≤ δG / 80 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hδCs : δ ≤ 1 / (16 * Cs) := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hX1 : X ≤ 1 := hX.trans hδ1'
  have hXs : 16 * Cs * X ≤ 1 := by
    have := hX.trans hδCs
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hC1X : C1 * (16 * X) ≤ 1 := by nlinarith
  have hC2X : C2 * (16 * X) ≤ 1 := by nlinarith
  have hC3X : C3 * (16 * X) ≤ 1 := by nlinarith
  -- pointwise chart
  have hqy : ∀ y, ‖q y‖ < ε := by
    intro y
    have h1 := norm_le_coordSum bM hBj q y
    have h2 := coordSum_bM_q_le s hq v (r := 2) (by omega)
    have h3 : L * X ≤ ε / 2 := by
      have := hX.trans hδε
      rw [le_div_iff₀ (by positivity)] at this
      linarith
    have h4 : Bm * (sK * PeriodicGridSobolev.Moser.coordSum 2 bM q) ≤ L * X := by
      calc Bm * (sK * PeriodicGridSobolev.Moser.coordSum 2 bM q) ≤ Bm * (sK * (16 * X)) := by
            gcongr
        _ ≤ L * X := by simp only [L]; nlinarith
    linarith
  have hvy : ∀ y, ‖v y‖ ≤ Bm * sK * 16 * X := by
    intro y
    have h1 := norm_le_coordSum bM hBj v y
    have h2 := coordSum_bM_v_le s q hv (r := 2) (by omega)
    calc ‖v y‖ ≤ Bm * (sK * PeriodicGridSobolev.Moser.coordSum 2 bM v) := h1
      _ ≤ Bm * (sK * (16 * X)) := by gcongr
      _ = Bm * sK * 16 * X := by ring
  have hch : ∀ y, _ := fun y => hchart (minkowski + q y) (by rw [add_sub_cancel_left]; exact hqy y)
  have hdA : ∀ x, DifferentiableAt ℝ harmA (minkowski + q x) := fun x => (hch x).1.1
  have hdC : ∀ x i j, DifferentiableAt ℝ (harmC i j) (minkowski + q x) := fun x i j =>
    ((hch x).2 i j).1
  have ha_half : ∀ x, 1 / 2 ≤ aArr q x := fun x => by
    have := (hch x).1.2.2; simp only [aArr]; rw [abs_le] at this; linarith
  have ha_ne : ∀ x, aArr q x ≠ 0 := fun x => by have := ha_half x; positivity
  have hadot : ∀ x, |adot q v x| ≤ K1 * X := by
    intro x
    have h1 := (fderiv ℝ harmA (minkowski + q x)).le_opNorm (v x)
    rw [Real.norm_eq_abs] at h1
    refine h1.trans ?_
    calc ‖fderiv ℝ harmA (minkowski + q x)‖ * ‖v x‖ ≤ M * (Bm * sK * 16 * X) :=
          mul_le_mul (hch x).1.2.1 (hvy x) (norm_nonneg _) hM
      _ = K1 * X := by simp only [K1]; ring
  have hcdot : ∀ x i j, |cdot q v i j x| ≤ K1 * X := by
    intro x i j
    have h1 := (fderiv ℝ (harmC i j) (minkowski + q x)).le_opNorm (v x)
    rw [Real.norm_eq_abs] at h1
    refine h1.trans ?_
    calc ‖fderiv ℝ (harmC i j) (minkowski + q x)‖ * ‖v x‖ ≤ M * (Bm * sK * 16 * X) :=
          mul_le_mul ((hch x).2 i j).2.1 (hvy x) (norm_nonneg _) hM
      _ = K1 * X := by simp only [K1]; ring
  -- Moser bounds
  have hcs1 : PeriodicGridSobolev.Moser.coordSum (s - 1) bM q ≤ 16 * X :=
    coordSum_bM_q_le s hq v (by omega)
  have hcs2 : PeriodicGridSobolev.Moser.coordSum s bM q ≤ 16 * X :=
    coordSum_bM_q_le s hq v (by omega)
  have hcs3 : PeriodicGridSobolev.Moser.coordSum (s + 1) bM q ≤ 16 * X :=
    coordSum_bM_q_le s hq v le_rfl
  have hM1 := hm1 N q (hcs1.trans (by linarith [hX.trans hδd1]))
  have hM2 := hm2 N q (hcs2.trans (by linarith [hX.trans hδd2]))
  have hM3 := hm3 N q (hcs3.trans (by linarith [hX.trans hδd3]))
  have hcJ := coordSum_bJ_le s hq hv
  have hMG := hmG N (jetArr q v) (hcJ.trans (by linarith [hX.trans hδdG]))
  have hcs1' := PeriodicGridSobolev.Moser.coordSum_nonneg (s - 1) bM q
  have hcs2' := PeriodicGridSobolev.Moser.coordSum_nonneg s bM q
  have hcs3' := PeriodicGridSobolev.Moser.coordSum_nonneg (s + 1) bM q
  have hainv : PeriodicGridSobolev.sobNorm (s - 1)
      (cx (fun x => (harmA (minkowski + q x))⁻¹) - fun _ => (1 : ℂ)) ≤ C1 * (16 * X) :=
    hM1.2.1.trans (by gcongr)
  have ha_s : PeriodicGridSobolev.sobNorm s (cx (aArr q) - fun _ => (1 : ℂ)) ≤ C2 * (16 * X) :=
    hM2.1.trans (by gcongr)
  have hc_s1 : ∀ i j, PeriodicGridSobolev.sobNorm (s + 1) (cx (cArr q i j) -
      fun _ => ((if i = j then 1 else 0 : ℝ) : ℂ)) ≤ C3 * (16 * X) := fun i j =>
    (hM3.2.2.1 i j).trans (by gcongr)
  have hb_s1 : ∀ i, PeriodicGridSobolev.sobNorm (s + 1) (cx (bArr q i) - fun _ => (0 : ℂ)) ≤
      C3 * (16 * X) := fun i => (hM3.2.2.2 i).trans (by gcongr)
  have hG : ∀ μ ν, PeriodicGridSobolev.sobNorm s (cx (comp (Garr q v) μ ν)) ≤ KG * X ^ 2 := by
    intro μ ν
    refine (hMG μ ν).trans ?_
    have := PeriodicGridSobolev.Moser.coordSum_nonneg s bJ (jetArr q v)
    calc CG * PeriodicGridSobolev.Moser.coordSum s bJ (jetArr q v) ^ 2 ≤ CG * (80 * X) ^ 2 := by
          gcongr
      _ = KG * X ^ 2 := by simp only [KG]; ring
  -- the acceleration in `H^{s-1}_h`
  have haccel : ∀ μ ν, PeriodicGridSobolev.sobNorm (s - 1)
      (cx (comp (harmonicWriterAcceleration q v) μ ν)) ≤ K2 * X := by
    intro μ ν
    have hrw := writer_row_cx q v μ ν ha_ne
    have e : cx (comp (harmonicWriterAcceleration q v) μ ν) =
        cx (fun x => (harmA (minkowski + q x))⁻¹) *
          (cx (aArr q) * cx (comp (harmonicWriterAcceleration q v) μ ν)) := by
      funext x
      simp only [Pi.mul_apply, cx_apply]
      rw [← mul_assoc, ← Complex.ofReal_mul, show (harmA (minkowski + q x))⁻¹ * aArr q x = 1 from
        inv_mul_cancel₀ (ha_ne x), Complex.ofReal_one, one_mul]
    rw [e, hrw]
    refine (sobNorm_coef_mul_le (s - 1) (by omega) _ _ 1 (by simp)
      (hainv.trans (by nlinarith))).trans ?_
    have hR := rhs_bound s hs (cx (comp q μ ν)) (cx (comp v μ ν)) (cx (comp (Garr q v) μ ν))
      (fun i j => cx (cArr q i j)) (fun i => cx (bArr q i))
      (fun i j => ((if i = j then 1 else 0 : ℝ) : ℂ)) (fun i j => by split_ifs <;> simp) X KG
      (fun i j => (PeriodicGridSobolev.Moser.sobNorm_mono (by omega) _).trans
        ((hc_s1 i j).trans (by nlinarith)))
      (fun i => (PeriodicGridSobolev.Moser.sobNorm_mono (by omega) _).trans
        ((hb_s1 i).trans (by nlinarith)))
      (fun j => (PeriodicGridSobolev.CommutedRow.sobNorm_Dp_le s j _).trans
        (sobNorm_q_le s hq v μ ν le_rfl))
      (sobNorm_v_le s q hv μ ν le_rfl)
      ((hG μ ν).trans (by
        have hXX : X ^ 2 ≤ X := by nlinarith
        exact mul_le_mul_of_nonneg_left hXX hKG))
    calc (As1 + 1) * PeriodicGridSobolev.sobNorm (s - 1) _ ≤ (As1 + 1) *
          ((9 * (As + 1) + 3 * As1 + 3 * As + KG) * X) := by gcongr
      _ = K2 * X := by simp only [K2]; ring
  -- the remainder of the commuted row
  have hRrow : ∀ α ∈ PeriodicGridSobolev.multiIndices s, ∀ μ ν,
      PeriodicGridSobolev.gridNorm (cx (Rrow α q v μ ν)) ≤ K3 * X ^ 2 := by
    intro α hα μ ν
    rw [PeriodicGridSobolev.mem_multiIndices] at hα
    rw [cx_Rrow α q v μ ν ha_ne]
    refine (hrow N α hα _ _ _ _ _ _ _ 1 (fun i j => ((if i = j then 1 else 0 : ℝ) : ℂ))
      (fun _ => 0)).trans ?_
    have t1 : PeriodicGridSobolev.sobNorm s (cx (aArr q) - fun _ => (1 : ℂ)) *
        PeriodicGridSobolev.sobNorm (s - 1) (cx (comp (harmonicWriterAcceleration q v) μ ν)) ≤
        C2 * (16 * X) * (K2 * X) :=
      mul_le_mul ha_s (haccel μ ν) (PeriodicGridSobolev.Moser.sobNorm_nonneg _ _) (by positivity)
    have t2 : ∑ i, ∑ j, PeriodicGridSobolev.sobNorm (s + 1) (cx (cArr q i j) -
        fun _ => ((if i = j then 1 else 0 : ℝ) : ℂ)) *
        PeriodicGridSobolev.sobNorm (s + 1) (cx (comp q μ ν)) ≤
        ∑ _i : Fin 3, ∑ _j : Fin 3, C3 * (16 * X) * X :=
      sum_le_sum fun i _ => sum_le_sum fun j _ => mul_le_mul (hc_s1 i j)
        (sobNorm_q_le s hq v μ ν le_rfl) (PeriodicGridSobolev.Moser.sobNorm_nonneg _ _)
        (by positivity)
    have t3 : ∑ i, PeriodicGridSobolev.sobNorm (s + 1) (cx (bArr q i) - fun _ => (0 : ℂ)) *
        PeriodicGridSobolev.sobNorm s (cx (comp v μ ν)) ≤ ∑ _i : Fin 3, C3 * (16 * X) * X :=
      sum_le_sum fun i _ => mul_le_mul (hb_s1 i) (sobNorm_v_le s q hv μ ν le_rfl)
        (PeriodicGridSobolev.Moser.sobNorm_nonneg _ _) (by positivity)
    have t4 := hG μ ν
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at t2 t3
    have hsum := add_le_add (add_le_add t1 t2) t3
    have := mul_le_mul_of_nonneg_left hsum hCr
    calc _ ≤ Cr * (C2 * (16 * X) * (K2 * X) + (3 : ℕ) * ((3 : ℕ) * (C3 * (16 * X) * X)) +
          (3 : ℕ) * (C3 * (16 * X) * X)) + KG * X ^ 2 := by linarith
      _ = K3 * X ^ 2 := by simp only [K3]; push_cast; ring
  -- per-index norms
  have hvα : ∀ α ∈ PeriodicGridSobolev.multiIndices s, ∀ μ ν,
      PeriodicGridSobolev.gridNorm (cx (DαR α (comp v μ ν))) ≤ X := fun α hα μ ν =>
    (gridNorm_cx_DαR_le (PeriodicGridSobolev.mem_multiIndices.mp hα) _).trans
      (sobNorm_v_le s q hv μ ν le_rfl)
  have hqα : ∀ α ∈ PeriodicGridSobolev.multiIndices s, ∀ μ ν,
      PeriodicGridSobolev.gridNorm (cx (DαR α (comp q μ ν))) ≤ X := fun α hα μ ν =>
    (gridNorm_cx_DαR_le (PeriodicGridSobolev.mem_multiIndices.mp hα) _).trans
      (sobNorm_q_le s hq v μ ν (by omega))
  have hdα : ∀ α ∈ PeriodicGridSobolev.multiIndices s, ∀ μ ν i,
      PeriodicGridSobolev.gridNorm (cx (OpenWriterEnergy.Dp i (DαR α (comp q μ ν)))) ≤ X :=
    fun α hα μ ν i => (gridNorm_cx_Dp_DαR_le (by
      have := PeriodicGridSobolev.mem_multiIndices.mp hα; omega) i _).trans
      (sobNorm_q_le s hq v μ ν le_rfl)
  refine ⟨hdA, hdC, ?_, ?_⟩
  · -- lower energy bound
    have hper : ∀ α ∈ PeriodicGridSobolev.multiIndices s,
        (1 / 4) * ∑ κ : Upper, (PeriodicGridSobolev.gridNorm (cx (DαR α (comp v κ.1.1 κ.1.2))) ^ 2 +
          ∑ i, PeriodicGridSobolev.gridNorm (cx (OpenWriterEnergy.Dp i
            (DαR α (comp q κ.1.1 κ.1.2)))) ^ 2 +
          PeriodicGridSobolev.gridNorm (cx (DαR α (comp q κ.1.1 κ.1.2))) ^ 2) ≤
        energy (SαR α (aArr q)) (fun i j => SαR α (cArr q i j))
          (fun κ : Upper => DαR α (comp q κ.1.1 κ.1.2))
          (fun κ : Upper => DαR α (comp v κ.1.1 κ.1.2)) := by
      intro α _
      unfold energy
      have hpt : ∀ (κ : Upper) x, (1 / 2) * (DαR α (comp v κ.1.1 κ.1.2) x ^ 2 +
          ∑ i, OpenWriterEnergy.Dp i (DαR α (comp q κ.1.1 κ.1.2)) x ^ 2 +
          DαR α (comp q κ.1.1 κ.1.2) x ^ 2) ≤
          DαR α (comp v κ.1.1 κ.1.2) x * (SαR α (aArr q) x * DαR α (comp v κ.1.1 κ.1.2) x) +
          ∑ i, ∑ j, OpenWriterEnergy.Dp i (DαR α (comp q κ.1.1 κ.1.2)) x *
            (SαR α (cArr q i j) x * OpenWriterEnergy.Dp j (DαR α (comp q κ.1.1 κ.1.2)) x) +
          DαR α (comp q κ.1.1 κ.1.2) x ^ 2 := by
        intro κ x
        have h1 : (1 / 2) * DαR α (comp v κ.1.1 κ.1.2) x ^ 2 ≤
            DαR α (comp v κ.1.1 κ.1.2) x * (SαR α (aArr q) x * DαR α (comp v κ.1.1 κ.1.2) x) := by
          have := ha_half (x + svec α)
          have e : SαR α (aArr q) x = aArr q (x + svec α) := rfl
          rw [e]; nlinarith [sq_nonneg (DαR α (comp v κ.1.1 κ.1.2) x)]
        have h2 := quad_lower (fun i => OpenWriterEnergy.Dp i (DαR α (comp q κ.1.1 κ.1.2)) x)
          (fun i j => SαR α (cArr q i j) x) (fun i j => ((hch (x + svec α)).2 i j).2.2)
        have h3 := sq_nonneg (DαR α (comp q κ.1.1 κ.1.2) x)
        linarith
      have hN : (0 : ℝ) ≤ ((N : ℝ) ^ 3)⁻¹ := by positivity
      calc (1 / 4) * ∑ κ : Upper, _ = ((N : ℝ) ^ 3)⁻¹ * (1 / 2) * ∑ κ : Upper, ∑ x,
            (1 / 2) * (DαR α (comp v κ.1.1 κ.1.2) x ^ 2 +
            ∑ i, OpenWriterEnergy.Dp i (DαR α (comp q κ.1.1 κ.1.2)) x ^ 2 +
            DαR α (comp q κ.1.1 κ.1.2) x ^ 2) := by
            rw [mul_assoc, mul_sum, mul_sum, mul_sum]
            refine sum_congr rfl fun κ _ => ?_
            simp only [← avg_sq, ← mul_sum, sum_add_distrib, mul_add]
            rw [sum_comm (s := univ) (t := univ) (f := fun x i =>
              OpenWriterEnergy.Dp i (DαR α (comp q κ.1.1 κ.1.2)) x ^ 2)]
            simp only [mul_sum]
            ring
        _ ≤ _ := by
            gcongr with κ _ x _
            exact hpt κ x
    calc Xsq s q v / 4 ≤ (1 / 4) * ∑ κ : Upper, ∑ α ∈ PeriodicGridSobolev.multiIndices s,
          (PeriodicGridSobolev.gridNorm (cx (DαR α (comp v κ.1.1 κ.1.2))) ^ 2 +
            ∑ i, PeriodicGridSobolev.gridNorm (cx (OpenWriterEnergy.Dp i
              (DαR α (comp q κ.1.1 κ.1.2)))) ^ 2 +
            PeriodicGridSobolev.gridNorm (cx (DαR α (comp q κ.1.1 κ.1.2))) ^ 2) := by
          rw [Xsq, div_eq_mul_inv, mul_comm, show (4 : ℝ)⁻¹ = 1 / 4 by norm_num]
          gcongr with κ _
          have hc := PeriodicGridSobolev.CommutedRow.sobSq_succ_le_shifted s (cx (comp q κ.1.1 κ.1.2))
          have hv' : PeriodicGridSobolev.sobSq s (cx (comp v κ.1.1 κ.1.2)) = ∑ α ∈
              PeriodicGridSobolev.multiIndices s,
              PeriodicGridSobolev.gridNorm (cx (DαR α (comp v κ.1.1 κ.1.2))) ^ 2 := by
            unfold PeriodicGridSobolev.sobSq
            refine sum_congr rfl fun α _ => ?_
            rw [cx_DαR, PeriodicGridSobolev.gridNorm_sq]
          have hq' : ∑ α ∈ PeriodicGridSobolev.multiIndices s,
              (PeriodicGridSobolev.gridNormSq (PeriodicGridSobolev.Dα α (cx (comp q κ.1.1 κ.1.2))) +
              ∑ i, PeriodicGridSobolev.gridNormSq (PeriodicGridSobolev.Dp i
                (PeriodicGridSobolev.Dα α (cx (comp q κ.1.1 κ.1.2))))) =
              ∑ α ∈ PeriodicGridSobolev.multiIndices s,
              (∑ i, PeriodicGridSobolev.gridNorm (cx (OpenWriterEnergy.Dp i
                (DαR α (comp q κ.1.1 κ.1.2)))) ^ 2 +
              PeriodicGridSobolev.gridNorm (cx (DαR α (comp q κ.1.1 κ.1.2))) ^ 2) := by
            refine sum_congr rfl fun α _ => ?_
            simp only [cx_Dp, cx_DαR, PeriodicGridSobolev.gridNorm_sq]
            ring
          calc _ ≤ (∑ α ∈ PeriodicGridSobolev.multiIndices s,
                (∑ i, PeriodicGridSobolev.gridNorm (cx (OpenWriterEnergy.Dp i
                  (DαR α (comp q κ.1.1 κ.1.2)))) ^ 2 +
                PeriodicGridSobolev.gridNorm (cx (DαR α (comp q κ.1.1 κ.1.2))) ^ 2)) +
                ∑ α ∈ PeriodicGridSobolev.multiIndices s,
                PeriodicGridSobolev.gridNorm (cx (DαR α (comp v κ.1.1 κ.1.2))) ^ 2 :=
                add_le_add (hc.trans (le_of_eq hq')) (le_of_eq hv')
            _ = _ := by rw [← sum_add_distrib]; exact sum_congr rfl fun _ _ => by ring
      _ = ∑ α ∈ PeriodicGridSobolev.multiIndices s, (1 / 4) * ∑ κ : Upper,
          (PeriodicGridSobolev.gridNorm (cx (DαR α (comp v κ.1.1 κ.1.2))) ^ 2 +
            ∑ i, PeriodicGridSobolev.gridNorm (cx (OpenWriterEnergy.Dp i
              (DαR α (comp q κ.1.1 κ.1.2)))) ^ 2 +
            PeriodicGridSobolev.gridNorm (cx (DαR α (comp q κ.1.1 κ.1.2))) ^ 2) := by
          rw [sum_comm, mul_sum]
      _ ≤ shiftedEnergy s q v := sum_le_sum hper
  · -- the energy rate
    have hper : ∀ α ∈ PeriodicGridSobolev.multiIndices s, ∀ κ : Upper,
        ((N : ℝ) ^ 3)⁻¹ * ∑ x,
          ((1 / 2) * (DαR α (comp v κ.1.1 κ.1.2) x * (SαR α (adot q v) x *
            DαR α (comp v κ.1.1 κ.1.2) x)) +
          (1 / 2) * ∑ i, ∑ j, OpenWriterEnergy.Dp i (DαR α (comp q κ.1.1 κ.1.2)) x *
            (SαR α (cdot q v i j) x * OpenWriterEnergy.Dp j (DαR α (comp q κ.1.1 κ.1.2)) x) +
          DαR α (comp q κ.1.1 κ.1.2) x * DαR α (comp v κ.1.1 κ.1.2) x +
          DαR α (comp v κ.1.1 κ.1.2) x * Rrow α q v κ.1.1 κ.1.2 x) ≤
        X ^ 2 + (5 * K1 + K3) * X ^ 3 := by
      intro α hα κ
      set vα := DαR α (comp v κ.1.1 κ.1.2)
      set qα := DαR α (comp q κ.1.1 κ.1.2)
      set R := Rrow α q v κ.1.1 κ.1.2
      have hN : (0 : ℝ) ≤ ((N : ℝ) ^ 3)⁻¹ := by positivity
      have hpt : ∀ x, (1 / 2) * (vα x * (SαR α (adot q v) x * vα x)) +
          (1 / 2) * ∑ i, ∑ j, OpenWriterEnergy.Dp i qα x *
            (SαR α (cdot q v i j) x * OpenWriterEnergy.Dp j qα x) ≤
          (1 / 2) * (K1 * X) * vα x ^ 2 +
            (3 / 2) * (K1 * X) * ∑ i, OpenWriterEnergy.Dp i qα x ^ 2 := by
        intro x
        have h1 : vα x * (SαR α (adot q v) x * vα x) ≤ K1 * X * vα x ^ 2 := by
          have := hadot (x + svec α)
          have e : SαR α (adot q v) x = adot q v (x + svec α) := rfl
          rw [e]
          have h := (le_abs_self _).trans (abs_mul_mul_le (vα x) (adot q v (x + svec α)) (vα x)
            _ this)
          linarith
        have h2 := quad_upper (fun i => OpenWriterEnergy.Dp i qα x)
          (fun i j => SαR α (cdot q v i j) x) (K1 * X) (fun i j => hcdot (x + svec α) i j)
        linarith
      have e4 : ((N : ℝ) ^ 3)⁻¹ * ∑ x,
          ((1 / 2) * (vα x * (SαR α (adot q v) x * vα x)) +
          (1 / 2) * ∑ i, ∑ j, OpenWriterEnergy.Dp i qα x *
            (SαR α (cdot q v i j) x * OpenWriterEnergy.Dp j qα x) +
          qα x * vα x + vα x * R x) =
          ((N : ℝ) ^ 3)⁻¹ * ∑ x, ((1 / 2) * (vα x * (SαR α (adot q v) x * vα x)) +
            (1 / 2) * ∑ i, ∑ j, OpenWriterEnergy.Dp i qα x *
              (SαR α (cdot q v i j) x * OpenWriterEnergy.Dp j qα x)) +
          ((N : ℝ) ^ 3)⁻¹ * ∑ x, qα x * vα x + ((N : ℝ) ^ 3)⁻¹ * ∑ x, vα x * R x := by
        simp only [← mul_add, ← sum_add_distrib]
      rw [e4]
      have b1 : ((N : ℝ) ^ 3)⁻¹ * ∑ x, ((1 / 2) * (vα x * (SαR α (adot q v) x * vα x)) +
            (1 / 2) * ∑ i, ∑ j, OpenWriterEnergy.Dp i qα x *
              (SαR α (cdot q v i j) x * OpenWriterEnergy.Dp j qα x)) ≤
          (1 / 2) * (K1 * X) * X ^ 2 + (3 / 2) * (K1 * X) * (3 * X ^ 2) := by
        refine (avg_le hpt).trans ?_
        have e : ((N : ℝ) ^ 3)⁻¹ * ∑ x, ((1 / 2) * (K1 * X) * vα x ^ 2 +
            (3 / 2) * (K1 * X) * ∑ i, OpenWriterEnergy.Dp i qα x ^ 2) =
            (1 / 2) * (K1 * X) * PeriodicGridSobolev.gridNorm (cx vα) ^ 2 +
            (3 / 2) * (K1 * X) * ∑ i, PeriodicGridSobolev.gridNorm
              (cx (OpenWriterEnergy.Dp i qα)) ^ 2 := by
          simp only [← avg_sq, sum_add_distrib, mul_add, ← mul_sum]
          rw [sum_comm (s := univ) (t := univ) (f := fun x i => OpenWriterEnergy.Dp i qα x ^ 2)]
          simp only [mul_sum]
          ring
        rw [e]
        have hv2 : PeriodicGridSobolev.gridNorm (cx vα) ^ 2 ≤ X ^ 2 :=
          pow_le_pow_left₀ (PeriodicGridSobolev.gridNorm_nonneg _) (hvα α hα _ _) 2
        have hd2 : ∑ i, PeriodicGridSobolev.gridNorm (cx (OpenWriterEnergy.Dp i qα)) ^ 2 ≤
            3 * X ^ 2 := by
          calc ∑ i, PeriodicGridSobolev.gridNorm (cx (OpenWriterEnergy.Dp i qα)) ^ 2 ≤
                ∑ _i : Fin 3, X ^ 2 := sum_le_sum fun i _ =>
                pow_le_pow_left₀ (PeriodicGridSobolev.gridNorm_nonneg _) (hdα α hα _ _ i) 2
            _ = 3 * X ^ 2 := by simp
        have : 0 ≤ K1 * X := by positivity
        gcongr
      have b2 : ((N : ℝ) ^ 3)⁻¹ * ∑ x, qα x * vα x ≤ X * X :=
        (le_abs_self _).trans ((abs_inner_le qα vα).trans
          (mul_le_mul (hqα α hα _ _) (hvα α hα _ _) (PeriodicGridSobolev.gridNorm_nonneg _) hX0))
      have b3 : ((N : ℝ) ^ 3)⁻¹ * ∑ x, vα x * R x ≤ X * (K3 * X ^ 2) :=
        (le_abs_self _).trans ((abs_inner_le vα R).trans
          (mul_le_mul (hvα α hα _ _) (hRrow α hα _ _) (PeriodicGridSobolev.gridNorm_nonneg _) hX0))
      nlinarith
    have hX2 : 0 ≤ X ^ 2 := sq_nonneg X
    have hX3 : 0 ≤ X ^ 3 := pow_nonneg hX0 3
    calc energyRate s q v ≤ ∑ _α ∈ PeriodicGridSobolev.multiIndices s, ∑ _κ : Upper,
          (X ^ 2 + (5 * K1 + K3) * X ^ 3) := by
          unfold energyRate
          refine sum_le_sum fun α hα => ?_
          rw [mul_sum]
          exact sum_le_sum fun κ _ => hper α hα κ
      _ = cM * cU * (X ^ 2 + (5 * K1 + K3) * X ^ 3) := by
          simp only [sum_const, card_univ, nsmul_eq_mul, cM, cU]; ring
      _ ≤ K * Xsq s q v + K * Xnorm s q v ^ 3 := by
          have hXsq : Xsq s q v = X ^ 2 := (Xnorm_sq s q v).symm
          rw [hXsq]
          have key : K * X ^ 2 + K * X ^ 3 - cM * cU * (X ^ 2 + (5 * K1 + K3) * X ^ 3) =
              cM * cU * ((5 * K1 + K3) * X ^ 2 + X ^ 3) := by
            rw [show K = cM * cU * (1 + 5 * K1 + K3) from rfl]; ring
          have : 0 ≤ cM * cU * ((5 * K1 + K3) * X ^ 2 + X ^ 3) := by positivity
          linarith

/-! ### The nonlinear energy inequality -/

theorem rpow_three_halves {E : ℝ} (hE : 0 ≤ E) : E ^ ((3 : ℝ) / 2) = E * Real.sqrt E := by
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add' hE (by norm_num), Real.rpow_one,
    Real.sqrt_eq_rpow]

/-- **`thm:supp-open-energy`** (all-component shifted nonlinear energy).  For every `s ≥ 3`
(in particular the manuscript's `s ≥ 11`) there are a chart radius `δ > 0` and a constant
`C ≥ 0`, independent of the mesh `h = 1/N`, such that for every `N`, every ten-component record
history `t ↦ (q(t), v(t))` solving the open writer `eq:main-open-writer` (with the harmonic
coefficients and the explicit harmonic first-jet source) at time `t`
(`q_t = v`, `v_t` = writer acceleration on the ten components, symmetric records) and lying at
time `t` in the fixed chart `‖X‖_{X^s_h} ≤ δ`:
* the shifted energy `𝓔_{s,h}` (`eq:supp-open-energy`) is differentiable at `t`, with derivative
  the right-hand side `energyRate` of the exact identity `eq:supp-open-energy-identity`;
* `¼ ‖X‖²_{X^s_h} ≤ 𝓔_{s,h}` (energy equivalence, lower half);
* `d/dt 𝓔_{s,h} ≤ C 𝓔_{s,h} + C 𝓔_{s,h}^{3/2}` (`eq:supp-open-energy-inequality`). -/
theorem open_energy_inequality (s : ℕ) (hs : 3 ≤ s) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (q v : ℝ → Grid N → MetricRec) (t : ℝ),
      IsSymRec (q t) → IsSymRec (v t) →
      (∀ x, HasDerivAt (fun τ => q τ x) (v t x) t) →
      (∀ x (κ : Upper), HasDerivAt (fun τ => v τ x κ.1.1 κ.1.2)
        (harmonicWriterAcceleration (q t) (v t) x κ.1.1 κ.1.2) t) →
      Xnorm s (q t) (v t) ≤ δ →
      HasDerivAt (fun τ => shiftedEnergy s (q τ) (v τ)) (energyRate s (q t) (v t)) t ∧
      Xsq s (q t) (v t) / 4 ≤ shiftedEnergy s (q t) (v t) ∧
      energyRate s (q t) (v t) ≤ C * shiftedEnergy s (q t) (v t) +
        C * shiftedEnergy s (q t) (v t) ^ ((3 : ℝ) / 2) := by
  obtain ⟨δ, hδ, K, hK, hstat⟩ := static_bounds s hs
  refine ⟨δ, hδ, 8 * K, by positivity, fun N _ q v t hqs hvs hq hv hX => ?_⟩
  obtain ⟨hdA, hdC, hlow, hrate⟩ := hstat N (q t) (v t) hqs hvs hX
  refine ⟨hasDerivAt_shiftedEnergy s q v t hqs hq hv hdA hdC, hlow, ?_⟩
  set E := shiftedEnergy s (q t) (v t)
  set X := Xnorm s (q t) (v t)
  have hX0 : 0 ≤ X := Xnorm_nonneg _ _ _
  have hXsq : Xsq s (q t) (v t) = X ^ 2 := (Xnorm_sq _ _ _).symm
  have hE0 : 0 ≤ E := le_trans (by rw [hXsq]; positivity) hlow
  have hX2 : X ^ 2 ≤ 4 * E := by rw [← hXsq]; linarith
  have hXs : X ≤ 2 * Real.sqrt E := by
    have : X = Real.sqrt (X ^ 2) := (Real.sqrt_sq hX0).symm
    rw [this, show 2 * Real.sqrt E = Real.sqrt (4 * E) by
      rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
    exact Real.sqrt_le_sqrt hX2
  have hX3 : X ^ 3 ≤ 8 * (E * Real.sqrt E) := by
    have h1 : X ^ 3 ≤ (2 * Real.sqrt E) ^ 3 := pow_le_pow_left₀ hX0 hXs 3
    have h2 : (2 * Real.sqrt E) ^ 3 = 8 * (Real.sqrt E ^ 2 * Real.sqrt E) := by ring
    rw [Real.sq_sqrt hE0] at h2
    linarith
  rw [rpow_three_halves hE0]
  rw [hXsq] at hrate
  have : K * X ^ 3 ≤ K * (8 * (E * Real.sqrt E)) := mul_le_mul_of_nonneg_left hX3 hK
  have : K * X ^ 2 ≤ K * (4 * E) := mul_le_mul_of_nonneg_left hX2 hK
  have hsq : 0 ≤ E * Real.sqrt E := mul_nonneg hE0 (Real.sqrt_nonneg _)
  nlinarith

/-- The flat record is a (global) solution of the writer: the writer acceleration vanishes at
`q = v = 0`. -/
theorem harmonicWriterAcceleration_zero (x : Grid N) :
    harmonicWriterAcceleration (0 : Grid N → MetricRec) 0 x = 0 := by
  have h := writer_row (0 : Grid N → MetricRec) 0 x
  have ha : aArr (0 : Grid N → MetricRec) x ≠ 0 := by
    simp only [aArr, Pi.zero_apply, add_zero, harm_minkowski.1]; norm_num
  funext μ ν
  have hG : comp (Garr (0 : Grid N → MetricRec) 0) μ ν x = 0 := by
    have : jetArr (0 : Grid N → MetricRec) 0 x = 0 := by
      simp [jetArr, fwd]; rfl
    simp only [comp, Garr, this, compensatorMap_zero]
  have hdiv : divArr (cArr (0 : Grid N → MetricRec)) (comp 0 μ ν) x = 0 := by
    simp [divArr, comp, OpenWriterEnergy.Dm_apply, OpenWriterEnergy.Dp_apply]
  have hskew : skewArr (bArr (0 : Grid N → MetricRec)) (comp 0 μ ν) x = 0 := by
    simp [skewArr, comp, OpenWriterEnergy.D0_apply, OpenWriterEnergy.Dm_apply,
      OpenWriterEnergy.Dp_apply]
  have := h μ ν ha
  rw [hG, hdiv, hskew] at this
  simp only [sub_zero, add_zero, mul_eq_zero] at this
  rcases this with h1 | h1
  · exact absurd h1 ha
  · exact h1

/-- Non-vacuity: the flat history `q = v = 0` satisfies every hypothesis of
`open_energy_inequality`. -/
example (s : ℕ) (hs : 3 ≤ s) : True := by
  obtain ⟨δ, hδ, C, hC, h⟩ := open_energy_inequality s hs
  have hX : Xnorm s (0 : Grid 5 → MetricRec) 0 ≤ δ := by
    have : Xsq s (0 : Grid 5 → MetricRec) 0 = 0 := by
      unfold Xsq
      refine sum_eq_zero fun κ _ => ?_
      have e : cx (comp (0 : Grid 5 → MetricRec) κ.1.1 κ.1.2) = 0 := by funext x; simp [comp]
      rw [e]
      simp [PeriodicGridSobolev.sobSq, PeriodicGridSobolev.gridNormSq]
    rw [Xnorm, this, Real.sqrt_zero]; exact hδ.le
  have := h 5 (fun _ => 0) (fun _ => 0) 0 (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun x => hasDerivAt_const _ _)
    (fun x κ => by
      rw [harmonicWriterAcceleration_zero]
      exact hasDerivAt_const _ _) hX
  trivial

end

end RenewalGeometry.OpenWriterEnergyEstimate
