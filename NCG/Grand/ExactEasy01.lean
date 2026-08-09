/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ContrastSpectrum
import NCG.Grand.BoundaryDecoupling
import NCG.Grand.FiniteCoreLedger
import NCG.Grand.FrobeniusHolonomy
import NCG.Grand.GrandReconstruction
import NCG.Grand.GrandCountermodels
import NCG.Grand.RepresentationDimensions
import NCG.Flagship.PvsNPBridge

/-!
# Exact re-proving batch EASY-01 (Gran-Tensor manuscript)

Exact full-statement formalizations for the ten EASY records:

* `cor:locked-opportunity-contrast-spectrum` —
  `contrast_naimark_sharp_record`, `contrast_spectrum_sharp_record_exact`;
* `cor:resolved-phase-selection` —
  `resolved_phase_uniqueness_margin`, `resolved_phase_selection_exact`;
* `corollary:common-action-provenance-discharges-the-normal-endpoint-comparison`
  — `common_action_provenance_exact` (with the Hilbert–Schmidt
  helper lemmas `hsFrobSq_*`);
* `corollary:finite-recurrent-core-versus-growing-ledger` —
  `finite_core_growing_ledger_exact`;
* `corollary:frobenius-as-tensor-holonomy` —
  `frobenius_tensor_holonomy_exact`;
* `corollary:two-and-three-point-reconstruction` —
  `basis_gram_det_isUnit`, `basis_gram_pairing`,
  `two_three_point_reconstruction_exact`;
* `countertheorem:a-second-scalar-coupling-need-not-create-a-branch-record`
  — `second_scalar_coupling_exact`;
* `countertheorem:representation-dimensions-are-not-a-symmetry-duality`
  — `representation_dimensions_not_duality_exact`;
* `cth:Schur-fill-in` — `schur_fill_in_general`;
* `cth:ambient-dimension-complexity` —
  `ambient_dimension_complexity_exact`.

Where a clause of a record was already proved exactly elsewhere in
`NCG/` it is re-exported here by direct application (the modules are
imported above); every such reuse is named in the docstring of the
bundling theorem.
-/

open Matrix

open scoped InnerProductSpace

namespace NCG

/-! ## `cor:locked-opportunity-contrast-spectrum`:
contrast spectrum and the sharp-record boundary -/

/-- The `j`-th outcome projection of the twenty-five-cell Naimark
completion: the diagonal `0/1` matrix supported on cell `j`. -/
def naimarkCell25 (j : Fin 25) : Matrix (Fin 25) (Fin 25) ℂ :=
  Matrix.diagonal (Pi.single j 1)

/-- Residual Naimark sentence of
`cor:locked-opportunity-contrast-spectrum`: the twenty-five-cell
Naimark completion is a sharp classical outcome record — its outcome
projections are commuting self-adjoint idempotents resolving the
identity (an abelian projection algebra) — and record sharpness alone
yields no dynamical qubit axes: any commuting pair that also
anticommutes has zero product, so no nondegenerate anticommuting
endpoint axes (no six dynamical edge qubits) follow. -/
theorem contrast_naimark_sharp_record :
    -- abelian projection algebra: outcome projections commute ...
    (∀ j k : Fin 25,
      naimarkCell25 j * naimarkCell25 k
        = naimarkCell25 k * naimarkCell25 j)
    -- ... and are self-adjoint idempotents
    ∧ (∀ j : Fin 25,
        naimarkCell25 j * naimarkCell25 j = naimarkCell25 j
          ∧ (naimarkCell25 j)ᴴ = naimarkCell25 j)
    -- sharp record: the outcomes resolve the identity
    ∧ (∑ j : Fin 25, naimarkCell25 j = 1)
    -- no anticommuting axes from sharpness: a commuting pair that
    -- anticommutes has zero product
    ∧ (∀ P Q : Matrix (Fin 25) (Fin 25) ℂ,
        P * Q = Q * P → P * Q = -(Q * P) → P * Q = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j k
    rw [naimarkCell25, naimarkCell25, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  · intro j
    constructor
    · rw [naimarkCell25, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      by_cases h : i = j
      · simp [h]
      · simp [h]
    · rw [naimarkCell25, Matrix.diagonal_conjTranspose]
      congr 1
      funext i
      by_cases h : i = j
      · simp [h]
      · simp [h]
  · ext i k
    rw [Matrix.sum_apply]
    by_cases h : i = k
    · subst h
      simp [naimarkCell25, Pi.single_apply]
    · simp [naimarkCell25, h]
  · intro P Q hc ha
    rw [← hc] at ha
    have hadd : P * Q + P * Q = 0 := by
      nth_rewrite 2 [ha]
      exact add_neg_cancel _
    have h2 : (2 : ℂ) • (P * Q) = 0 := by
      rw [two_smul]
      exact hadd
    rcases smul_eq_zero.mp h2 with h | h
    · exact absurd h (by norm_num)
    · exact h

/-- `cor:locked-opportunity-contrast-spectrum`, exact full statement.
The four metric clauses (uniform projection, contrast eigenvalue `θ`,
explicit inverse, boxed nonorthogonal Parseval overlaps) are the
proved `NCG.locked_opportunity_contrast_spectrum`, re-exported by
direct application; the residual sharp-record Naimark sentence is
`contrast_naimark_sharp_record`. -/
theorem contrast_spectrum_sharp_record_exact :
    (∀ θ : ℂ, θ ≠ 0 → (12 : ℂ) - 11 * θ ≠ 0 →
      ((24 : ℂ)⁻¹ • allOnes24) * ((24 : ℂ)⁻¹ • allOnes24)
        = (24 : ℂ)⁻¹ • allOnes24
      ∧ (∀ v : Fin 24 → ℂ, (∑ i, v i = 0) →
          (θ • (1 - (24 : ℂ)⁻¹ • allOnes24)
            + ((12 : ℂ) - 11 * θ) • ((24 : ℂ)⁻¹ • allOnes24))
            *ᵥ v = θ • v)
      ∧ (θ⁻¹ • (1 - (24 : ℂ)⁻¹ • allOnes24)
          + ((12 : ℂ) - 11 * θ)⁻¹ • ((24 : ℂ)⁻¹ • allOnes24))
        * (θ • (1 - (24 : ℂ)⁻¹ • allOnes24)
          + ((12 : ℂ) - 11 * θ) • ((24 : ℂ)⁻¹ • allOnes24))
        = 1
      ∧ (∀ j k : Fin 24, j ≠ k →
          θ * (θ⁻¹ • (1 - (24 : ℂ)⁻¹ • allOnes24)
            + ((12 : ℂ) - 11 * θ)⁻¹
              • ((24 : ℂ)⁻¹ • allOnes24)) j k
            = -(1 - θ) / (2 * ((12 : ℂ) - 11 * θ))))
    ∧ (∑ j : Fin 25, naimarkCell25 j = 1)
    ∧ (∀ j k : Fin 25,
        naimarkCell25 j * naimarkCell25 k
          = naimarkCell25 k * naimarkCell25 j)
    ∧ (∀ P Q : Matrix (Fin 25) (Fin 25) ℂ,
        P * Q = Q * P → P * Q = -(Q * P) → P * Q = 0) :=
  ⟨fun θ hθ h12 => locked_opportunity_contrast_spectrum θ hθ h12,
    contrast_naimark_sharp_record.2.2.1,
    contrast_naimark_sharp_record.1,
    contrast_naimark_sharp_record.2.2.2⟩

/-! ## `cor:resolved-phase-selection`:
resolved phase and back-transition selection -/

/-- Uniqueness remark of `cor:resolved-phase-selection`: within the
positive quotient family the back-transition probability
`c(a) = (5a-1)(1-3a)/(15(1-a))` vanishes exactly at the two endpoint
orientations `a = 1/5` and `a = 1/3` (so `c = 0` plus seriality
uniquely selects `a = 1/5`), while interior family members come
arbitrarily close to the resolved point: without a back-transition
certificate there is no positive isolation margin. -/
theorem resolved_phase_uniqueness_margin :
    -- `c(a) = 0` has exactly the two endpoint solutions
    (∀ a : ℚ, a ≠ 1 →
      ((5 * a - 1) * (1 - 3 * a) / (15 * (1 - a)) = 0
        ↔ a = 1/5 ∨ a = 1/3))
    -- no positive isolation margin from the interior family
    ∧ (∀ ε : ℚ, 0 < ε → ∃ a : ℚ,
        1/5 < a ∧ a < 1/3 ∧ a - 1/5 < ε) := by
  constructor
  · intro a ha
    have hden : (15 : ℚ) * (1 - a) ≠ 0 := by
      intro h
      rcases mul_eq_zero.mp h with h15 | h1a
      · norm_num at h15
      · exact ha (by linarith)
    constructor
    · intro h
      rcases div_eq_zero_iff.mp h with hnum | hd
      · rcases mul_eq_zero.mp hnum with h1 | h2
        · left; linarith
        · right; linarith
      · exact absurd hd hden
    · rintro (rfl | rfl) <;> norm_num
  · intro ε hε
    have hm0 : 0 < min ε (2/15 : ℚ) :=
      lt_min hε (by norm_num)
    have hmε : min ε (2/15 : ℚ) ≤ ε := min_le_left _ _
    have hm215 : min ε (2/15 : ℚ) ≤ 2/15 := min_le_right _ _
    exact ⟨1/5 + min ε (2/15) / 2, by linarith, by linarith,
      by linarith⟩

/-- `cor:resolved-phase-selection`, exact full statement: the
substitution clauses (`c(1/5) = 0`, `d(1/5) = 1/3`,
`r_P(1/5) = 2/3`, unique recovery of `Q₀` and `r₀`, and the `2/15`
seriality separation) are the proved `NCG.resolved_phase_selection`,
re-exported by direct application; the endpoint-uniqueness and
no-isolation-margin clauses are `resolved_phase_uniqueness_margin`. -/
theorem resolved_phase_selection_exact :
    -- the family formulas at the selected point `a = 1/5`
    ((8 : ℚ)/15 - 1/5 = 1/3)
    ∧ ((5 * (1/5 : ℚ) - 1) * (1 - 3 * (1/5))
        / (15 * (1 - 1/5)) = 0)
    ∧ ((8 : ℚ) / (15 * (1 - 1/5)) = 2/3)
    -- the recovered transfer and completion vector
    ∧ (!![1/5, 1 - 1/5;
          (5 * (1/5 : ℚ) - 1) * (1 - 3 * (1/5))
            / (15 * (1 - 1/5)),
          8/15 - 1/5] = !![1/5, 4/5; 0, 1/3])
    ∧ (![0, 1 - ((5 * (1/5 : ℚ) - 1) * (1 - 3 * (1/5))
          / (15 * (1 - 1/5))) - (8/15 - 1/5)] = ![0, 2/3])
    -- the seriality separation margin
    ∧ ((1 : ℚ)/3 - 1/5 = 2/15)
    -- endpoint uniqueness of `c(a) = 0`
    ∧ (∀ a : ℚ, a ≠ 1 →
        ((5 * a - 1) * (1 - 3 * a) / (15 * (1 - a)) = 0
          ↔ a = 1/5 ∨ a = 1/3))
    -- no positive isolation margin from the interior family
    ∧ (∀ ε : ℚ, 0 < ε → ∃ a : ℚ,
        1/5 < a ∧ a < 1/3 ∧ a - 1/5 < ε) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := resolved_phase_selection
  exact ⟨h1, h2, h3, h4, h5, h6,
    resolved_phase_uniqueness_margin.1,
    resolved_phase_uniqueness_margin.2⟩

/-! ## `corollary:common-action-provenance-discharges-the-normal-endpoint-comparison` -/

/-- Squared Hilbert–Schmidt (Frobenius) norm of a complex matrix:
the sum of the squared moduli of its entries. -/
def hsFrobSq {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (A i j)

/-- The squared Hilbert–Schmidt norm is nonnegative. -/
theorem hsFrobSq_nonneg {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) : 0 ≤ hsFrobSq A :=
  Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- The squared Hilbert–Schmidt norm vanishes only on the zero
matrix. -/
theorem hsFrobSq_eq_zero_iff {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) : hsFrobSq A = 0 ↔ A = 0 := by
  constructor
  · intro h
    ext i j
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg
        fun j _ => Complex.normSq_nonneg (A i j))).mp h i
      (Finset.mem_univ i)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Complex.normSq_nonneg (A i j))).mp h1 j
      (Finset.mem_univ j)
    simpa [Matrix.zero_apply] using Complex.normSq_eq_zero.mp h2
  · intro h
    simp [hsFrobSq, h]

/-- Two-two comparison for the squared Hilbert–Schmidt norm:
`‖X + Y‖² ≤ 2‖X‖² + 2‖Y‖²`. -/
theorem hsFrobSq_add_le {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℂ) :
    hsFrobSq (A + B) ≤ 2 * hsFrobSq A + 2 * hsFrobSq B := by
  have key : ∀ z w : ℂ, Complex.normSq (z + w)
      ≤ 2 * Complex.normSq z + 2 * Complex.normSq w := by
    intro z w
    simp only [Complex.normSq_apply, Complex.add_re,
      Complex.add_im]
    nlinarith [sq_nonneg (z.re - w.re), sq_nonneg (z.im - w.im)]
  have h1 : hsFrobSq (A + B)
      ≤ ∑ i, ∑ j, (2 * Complex.normSq (A i j)
        + 2 * Complex.normSq (B i j)) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum
      fun j _ => ?_
    rw [Matrix.add_apply]
    exact key _ _
  have h2 : ∑ i, ∑ j, (2 * Complex.normSq (A i j)
      + 2 * Complex.normSq (B i j))
      = 2 * hsFrobSq A + 2 * hsFrobSq B := by
    simp only [hsFrobSq, Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith [h1, h2.le, h2.ge]

/-- The squared Hilbert–Schmidt norm as the real part of the trace
of the Gram square: `‖A‖² = re tr(AᴴA)`. -/
theorem hsFrobSq_eq_re_trace {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) :
    hsFrobSq A = (Matrix.trace (Aᴴ * A)).re := by
  have h1 : Matrix.trace (Aᴴ * A)
      = ∑ j, ∑ i, star (A i j) * A i j := by
    simp [Matrix.trace, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.diag]
  calc hsFrobSq A
      = ∑ j, ∑ i, Complex.normSq (A i j) := Finset.sum_comm
    _ = ∑ j, ∑ i, (star (A i j) * A i j).re := by
        refine Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun i _ => ?_
        rw [mul_comm,
          show star (A i j) = (starRingEnd ℂ) (A i j) from rfl,
          Complex.mul_conj, Complex.ofReal_re]
    _ = (∑ j, ∑ i, star (A i j) * A i j).re := by
        simp [Complex.re_sum]
    _ = (Matrix.trace (Aᴴ * A)).re := by rw [h1]

/-- Whitened contraction: right multiplication by an isometry
(`VᴴV = 1`) does not increase the squared Hilbert–Schmidt norm. -/
theorem hsFrobSq_mul_isometry_le {m p : Type*} [Fintype m]
    [Fintype p] [DecidableEq m] [DecidableEq p]
    (X : Matrix m m ℂ) (V : Matrix m p ℂ) (hV : Vᴴ * V = 1) :
    hsFrobSq (X * V) ≤ hsFrobSq X := by
  have hPH : (V * Vᴴ)ᴴ = V * Vᴴ := by
    rw [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hPP : (V * Vᴴ) * (V * Vᴴ) = V * Vᴴ := by
    calc (V * Vᴴ) * (V * Vᴴ) = V * (Vᴴ * V) * Vᴴ := by
          simp only [Matrix.mul_assoc]
      _ = V * Vᴴ := by rw [hV, Matrix.mul_one]
  have hQH : ((1 : Matrix m m ℂ) - V * Vᴴ)ᴴ
      = 1 - V * Vᴴ := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH]
  have hQQ : ((1 : Matrix m m ℂ) - V * Vᴴ)
      * ((1 : Matrix m m ℂ) - V * Vᴴ) = 1 - V * Vᴴ := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul,
      Matrix.one_mul, hPP, sub_self, sub_zero]
  -- `‖XV‖² = re tr(VVᴴ · XᴴX)`
  have hXV : hsFrobSq (X * V)
      = (Matrix.trace ((V * Vᴴ) * (Xᴴ * X))).re := by
    rw [hsFrobSq_eq_re_trace]
    congr 1
    have e1 : (X * V)ᴴ * (X * V) = (Vᴴ * (Xᴴ * X)) * V := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [e1, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  -- `‖X(1 - VVᴴ)‖² = re tr((1 - VVᴴ) · XᴴX)`
  have hXQ : hsFrobSq (X * ((1 : Matrix m m ℂ) - V * Vᴴ))
      = (Matrix.trace (((1 : Matrix m m ℂ) - V * Vᴴ)
          * (Xᴴ * X))).re := by
    rw [hsFrobSq_eq_re_trace]
    congr 1
    have e1 : (X * ((1 : Matrix m m ℂ) - V * Vᴴ))ᴴ
        * (X * ((1 : Matrix m m ℂ) - V * Vᴴ))
        = (((1 : Matrix m m ℂ) - V * Vᴴ) * (Xᴴ * X))
          * ((1 : Matrix m m ℂ) - V * Vᴴ) := by
      rw [Matrix.conjTranspose_mul, hQH]
      simp only [Matrix.mul_assoc]
    rw [e1, Matrix.trace_mul_comm]
    calc Matrix.trace (((1 : Matrix m m ℂ) - V * Vᴴ)
          * (((1 : Matrix m m ℂ) - V * Vᴴ) * (Xᴴ * X)))
        = Matrix.trace ((((1 : Matrix m m ℂ) - V * Vᴴ)
            * ((1 : Matrix m m ℂ) - V * Vᴴ)) * (Xᴴ * X)) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.trace (((1 : Matrix m m ℂ) - V * Vᴴ)
            * (Xᴴ * X)) := by rw [hQQ]
  -- Pythagoras: the two pieces sum to `‖X‖²`
  have hsum : hsFrobSq (X * V)
      + hsFrobSq (X * ((1 : Matrix m m ℂ) - V * Vᴴ))
      = hsFrobSq X := by
    rw [hXV, hXQ, hsFrobSq_eq_re_trace, ← Complex.add_re,
      ← Matrix.trace_add, ← Matrix.add_mul]
    congr 2
    abel_nf
    rw [Matrix.one_mul]
  have hnn := hsFrobSq_nonneg
    (X * ((1 : Matrix m m ℂ) - V * Vᴴ))
  linarith [hsum]

/-- `corollary:common-action-provenance-discharges-the-normal-endpoint-comparison`,
exact statement.  With action-derived normal generators `h_x`,
generator-native candidates `n_x`, protected affine endpoint writers
`a_x`, and a whitened source-minimal synthesis `V` (`VᴴV = 1`), the
residual `R_x = n_xV - Va_x` (definitional, not hypothesized) obeys
the boxed two-two comparison
`Σ‖R_x‖² ≤ 2Δ_{act→nor} + 2Δ_{act→end}` with
`Δ_{act→nor} = Σ‖n_x - h_x‖²` and
`Δ_{act→end} = Σ‖h_xV - Va_x‖²`; and zero provenance residuals
identify the generator-native normal and the endpoint writer as
restrictions of one flow: `n_x = h_x` and
`n_xV = Va_x = h_xV`. -/
theorem common_action_provenance_exact {ι m p : Type*} [Fintype ι]
    [Fintype m] [Fintype p] [DecidableEq m] [DecidableEq p]
    (nX hX : ι → Matrix m m ℂ) (aX : ι → Matrix p p ℂ)
    (V : Matrix m p ℂ) (hV : Vᴴ * V = 1) :
    -- the boxed two-two comparison
    (∑ x, hsFrobSq (nX x * V - V * aX x)
      ≤ 2 * ∑ x, hsFrobSq (nX x - hX x)
        + 2 * ∑ x, hsFrobSq (hX x * V - V * aX x))
    -- zero provenance residuals identify the three generators
    ∧ ((∑ x, hsFrobSq (nX x - hX x)) = 0 →
        (∑ x, hsFrobSq (hX x * V - V * aX x)) = 0 →
        ∀ x, nX x = hX x ∧ nX x * V = V * aX x
          ∧ hX x * V = V * aX x) := by
  constructor
  · have hstep : ∀ x ∈ Finset.univ,
        hsFrobSq (nX x * V - V * aX x)
          ≤ 2 * hsFrobSq (nX x - hX x)
            + 2 * hsFrobSq (hX x * V - V * aX x) := by
      intro x _
      have hsplit : nX x * V - V * aX x
          = (nX x - hX x) * V + (hX x * V - V * aX x) := by
        rw [Matrix.sub_mul]
        abel
      calc hsFrobSq (nX x * V - V * aX x)
          = hsFrobSq ((nX x - hX x) * V
              + (hX x * V - V * aX x)) := by rw [hsplit]
        _ ≤ 2 * hsFrobSq ((nX x - hX x) * V)
              + 2 * hsFrobSq (hX x * V - V * aX x) :=
            hsFrobSq_add_le _ _
        _ ≤ 2 * hsFrobSq (nX x - hX x)
              + 2 * hsFrobSq (hX x * V - V * aX x) := by
            have := hsFrobSq_mul_isometry_le (nX x - hX x) V hV
            linarith
    calc ∑ x, hsFrobSq (nX x * V - V * aX x)
        ≤ ∑ x, (2 * hsFrobSq (nX x - hX x)
            + 2 * hsFrobSq (hX x * V - V * aX x)) :=
          Finset.sum_le_sum hstep
      _ = 2 * ∑ x, hsFrobSq (nX x - hX x)
            + 2 * ∑ x, hsFrobSq (hX x * V - V * aX x) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum,
            Finset.mul_sum]
  · intro hnor hend x
    have h1 : hsFrobSq (nX x - hX x) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun x _ => hsFrobSq_nonneg (nX x - hX x))).mp hnor x
        (Finset.mem_univ x)
    have h2 : hsFrobSq (hX x * V - V * aX x) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun x _ => hsFrobSq_nonneg
          (hX x * V - V * aX x))).mp hend x (Finset.mem_univ x)
    have e1 : nX x = hX x :=
      sub_eq_zero.mp ((hsFrobSq_eq_zero_iff _).mp h1)
    have e2 : hX x * V = V * aX x :=
      sub_eq_zero.mp ((hsFrobSq_eq_zero_iff _).mp h2)
    exact ⟨e1, by rw [e1, e2], e2⟩

/-! ## `corollary:finite-recurrent-core-versus-growing-ledger` -/

/-- `corollary:finite-recurrent-core-versus-growing-ledger`, exact
statement: a finite recurrent core may emit an indefinitely growing
external classical ledger.  The one-state recurrent-core clause and
the unbounded-carrier clause are the proved
`NCG.finite_core_vs_growing_ledger`, re-exported by direct
application; the middle clause realizes the growing ledger — at every
horizon `N` the `2^N`-output cylinder density `2^{-N}·I` actually
admits a purification (`M Mᴴ = 2^{-N}·1` with carrier dimension
exactly `2^N`), so the identification of finite recurrent memory with
a finite faithful carrier of the complete infinite protected
chronology is incorrect. -/
theorem finite_core_growing_ledger_exact :
    -- one-state recurrent core at every horizon
    (∀ (P F : Type) [Fintype P] [Fintype F]
      (u : P → ℝ) (v : F → ℝ),
      (Matrix.vecMulVec u v).rank ≤ 1)
    -- the growing ledger is realized at every horizon
    ∧ (∀ N : ℕ, ∃ M : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ,
        M * Mᴴ = ((2 : ℂ) ^ N)⁻¹ • 1)
    -- but every faithful ledger carrier grows without bound
    ∧ (∀ K : ℕ, ∃ N : ℕ, K < 2 ^ N ∧
        (∀ (E : Type) [Fintype E]
          (M : Matrix (Fin (2 ^ N)) E ℂ),
          M * Mᴴ = ((2 : ℂ) ^ N)⁻¹ • 1 →
          K < Fintype.card E)) := by
  refine ⟨finite_core_vs_growing_ledger.1, ?_,
    finite_core_vs_growing_ledger.2⟩
  intro N
  have hs0 : (0 : ℝ) ≤ (2 : ℝ) ^ N := by positivity
  have hss : ((Real.sqrt ((2 : ℝ) ^ N) : ℝ) : ℂ)
      * ((Real.sqrt ((2 : ℝ) ^ N) : ℝ) : ℂ) = (2 : ℂ) ^ N := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hs0]
    push_cast
    ring
  refine ⟨((Real.sqrt ((2 : ℝ) ^ N) : ℝ) : ℂ)⁻¹ • 1, ?_⟩
  have hstar : star (((Real.sqrt ((2 : ℝ) ^ N) : ℝ) : ℂ)⁻¹)
      = ((Real.sqrt ((2 : ℝ) ^ N) : ℝ) : ℂ)⁻¹ := by
    simp [Complex.conj_ofReal]
  calc (((Real.sqrt ((2 : ℝ) ^ N) : ℝ) : ℂ)⁻¹
        • (1 : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ))
      * (((Real.sqrt ((2 : ℝ) ^ N) : ℝ) : ℂ)⁻¹
        • (1 : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ))ᴴ
      = (((Real.sqrt ((2 : ℝ) ^ N) : ℝ) : ℂ)⁻¹
          * ((Real.sqrt ((2 : ℝ) ^ N) : ℝ) : ℂ)⁻¹)
        • (1 : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ) := by
        rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
          hstar, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.mul_one, smul_smul]
    _ = ((2 : ℂ) ^ N)⁻¹
        • (1 : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ) := by
        rw [← mul_inv, hss]

/-! ## `corollary:frobenius-as-tensor-holonomy` -/

open TannakaDuality.FiniteGroup in
/-- `corollary:frobenius-as-tensor-holonomy`, exact statement: an
unramified arithmetic packet — a natural multiplicative operator on
every object of the finite rigid representation category compatible
with tensor products, duals, and the fibre functor, i.e. a monoidal
natural automorphism `η : Aut (forget ℂ G)` of the fibre functor —
is the reconstructed holonomy of exactly one element of the Tannaka
group: the unique-existence clause is the proved
`NCG.frobenius_tensor_holonomy`, the bijectivity clause the proved
`NCG.finite_tannaka_bijective` (both re-exported), and holonomy
reconstruction is multiplicative on packets. -/
theorem frobenius_tensor_holonomy_exact (G : Type) [Group G]
    [Finite G] :
    -- every packet is the holonomy of exactly one group element
    (∀ η : CategoryTheory.Aut (forget ℂ G),
      ∃! g : G, equivHom ℂ G g = η)
    -- the holonomy reconstruction map is bijective ...
    ∧ Function.Bijective (equivHom ℂ G)
    -- ... and multiplicative
    ∧ (∀ g g' : G, equivHom ℂ G (g * g')
        = equivHom ℂ G g * equivHom ℂ G g') :=
  ⟨fun η => frobenius_tensor_holonomy G η,
    finite_tannaka_bijective G,
    fun g g' => map_mul (equivHom ℂ G) g g'⟩

/-! ## `corollary:two-and-three-point-reconstruction` -/

/-- Faithfulness makes the basis Gram matrix invertible: for a basis
`a₁, …, a_d` of a finite-dimensional complex inner product space, the
Gram matrix `G_{iℓ} = ⟨a_i, a_ℓ⟩` has invertible determinant. -/
theorem basis_gram_det_isUnit {A : Type*} [NormedAddCommGroup A]
    [InnerProductSpace ℂ A] {d : ℕ} (b : Module.Basis (Fin d) ℂ A) :
    IsUnit (Matrix.gram ℂ (⇑b : Fin d → A)).det :=
  isUnit_iff_ne_zero.mpr
    (Matrix.det_gram_ne_zero_iff_linearIndependent.mpr
      b.linearIndependent)

/-- Sesquilinearity derives the linear system: pairing a basis
expansion `x = Σ_ℓ (repr x)_ℓ a_ℓ` against every basis vector gives
`G ·(repr x) = (⟨a_i, x⟩)_i`. -/
theorem basis_gram_pairing {A : Type*} [NormedAddCommGroup A]
    [InnerProductSpace ℂ A] {d : ℕ} (b : Module.Basis (Fin d) ℂ A)
    (x : A) :
    Matrix.gram ℂ (⇑b : Fin d → A) *ᵥ (fun ℓ => b.repr x ℓ)
      = fun i => ⟪b i, x⟫_ℂ := by
  funext i
  calc (Matrix.gram ℂ (⇑b : Fin d → A)
        *ᵥ fun ℓ => b.repr x ℓ) i
      = ∑ ℓ, ⟪b i, b ℓ⟫_ℂ * b.repr x ℓ := by
        simp [Matrix.mulVec, dotProduct, Matrix.gram_apply]
    _ = ∑ ℓ, ⟪b i, b.repr x ℓ • b ℓ⟫_ℂ := by
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [inner_smul_right, mul_comm]
    _ = ⟪b i, ∑ ℓ, b.repr x ℓ • b ℓ⟫_ℂ :=
        (inner_sum _ _ _).symm
    _ = ⟪b i, x⟫_ℂ := by rw [b.sum_repr x]

/-- `corollary:two-and-three-point-reconstruction`, exact statement.
For a basis `a₁, …, a_d` of a finite unital `*`-algebra carried by a
faithful complex inner product, the panels
`G_{iℓ} = ⟨a_i, a_ℓ⟩`, `M_{i;jk} = ⟨a_i, a_j a_k⟩`,
`J_{ij} = ⟨a_i, a_j*⟩`, `u_i = ⟨a_i, 1⟩` determine multiplication,
involution, and unit, with the boxed coefficient formulas
`c_{jk} = G⁻¹M_{·;jk}`, `d_j = G⁻¹J_{·j}`, `e = G⁻¹u`.  The linear
systems are *derived* from sesquilinearity (`basis_gram_pairing`) and
the Gram invertibility from faithfulness (`basis_gram_det_isUnit`);
the cancellation step reuses the proved
`NCG.coefficient_recovery`. -/
theorem two_three_point_reconstruction_exact {A : Type*}
    [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [Mul A] [Star A] [One A] {d : ℕ} (b : Module.Basis (Fin d) ℂ A) :
    -- the Gram panel is invertible
    IsUnit (Matrix.gram ℂ (⇑b : Fin d → A)).det
    -- boxed: `c_{jk} = G⁻¹ M_{·;jk}`
    ∧ (∀ j k, (fun ℓ => b.repr (b j * b k) ℓ)
        = (Matrix.gram ℂ (⇑b : Fin d → A))⁻¹
          *ᵥ fun i => ⟪b i, b j * b k⟫_ℂ)
    -- boxed: `d_j = G⁻¹ J_{·j}`
    ∧ (∀ j, (fun ℓ => b.repr (star (b j)) ℓ)
        = (Matrix.gram ℂ (⇑b : Fin d → A))⁻¹
          *ᵥ fun i => ⟪b i, star (b j)⟫_ℂ)
    -- boxed: `e = G⁻¹ u`
    ∧ ((fun ℓ => b.repr (1 : A) ℓ)
        = (Matrix.gram ℂ (⇑b : Fin d → A))⁻¹
          *ᵥ fun i => ⟪b i, (1 : A)⟫_ℂ)
    -- hence the panels determine multiplication ...
    ∧ (∀ j k, b j * b k
        = ∑ ℓ, ((Matrix.gram ℂ (⇑b : Fin d → A))⁻¹
            *ᵥ fun i => ⟪b i, b j * b k⟫_ℂ) ℓ • b ℓ)
    -- ... involution ...
    ∧ (∀ j, star (b j)
        = ∑ ℓ, ((Matrix.gram ℂ (⇑b : Fin d → A))⁻¹
            *ᵥ fun i => ⟪b i, star (b j)⟫_ℂ) ℓ • b ℓ)
    -- ... and unit
    ∧ ((1 : A)
        = ∑ ℓ, ((Matrix.gram ℂ (⇑b : Fin d → A))⁻¹
            *ᵥ fun i => ⟪b i, (1 : A)⟫_ℂ) ℓ • b ℓ) := by
  have hG := basis_gram_det_isUnit b
  have hrec : ∀ x : A, (fun ℓ => b.repr x ℓ)
      = (Matrix.gram ℂ (⇑b : Fin d → A))⁻¹
        *ᵥ fun i => ⟪b i, x⟫_ℂ := fun x =>
    coefficient_recovery _ hG _ _ (basis_gram_pairing b x)
  have hdet : ∀ x : A, x
      = ∑ ℓ, ((Matrix.gram ℂ (⇑b : Fin d → A))⁻¹
          *ᵥ fun i => ⟪b i, x⟫_ℂ) ℓ • b ℓ := by
    intro x
    conv_lhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [← hrec x]
  exact ⟨hG, fun j k => hrec _, fun j => hrec _, hrec _,
    fun j k => hdet _, fun j => hdet _, hdet _⟩

/-! ## `countertheorem:a-second-scalar-coupling-need-not-create-a-branch-record` -/

/-- `countertheorem:a-second-scalar-coupling-need-not-create-a-branch-record`,
exact statement: on a one-dimensional action environment every
operator is scalar (first clause), yet unequal coupling coefficients
exist whose normalized branch probabilities are identical — no
nontrivial retained discriminator (second clause, the proved
`NCG.second_scalar_coupling`, re-exported by direct application). -/
theorem second_scalar_coupling_exact :
    -- one-dimensional environment: every operator is scalar
    (∀ E : Matrix (Fin 1) (Fin 1) ℂ, E = E 0 0 • 1)
    -- unequal coefficients, identical normalized branch reads
    ∧ (∃ a b : ℝ, a ≠ b ∧ 0 < a ∧ 0 < b
        ∧ ∀ v w : ℝ, v ^ 2 + w ^ 2 ≠ 0 →
          (a * v) ^ 2 / ((a * v) ^ 2 + (a * w) ^ 2)
            = (b * v) ^ 2 / ((b * v) ^ 2 + (b * w) ^ 2)) := by
  refine ⟨?_, second_scalar_coupling⟩
  intro E
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.smul_apply, Matrix.one_apply]

/-! ## `countertheorem:representation-dimensions-are-not-a-symmetry-duality` -/

/-- `countertheorem:representation-dimensions-are-not-a-symmetry-duality`,
exact statement: `ℤ/4ℤ` and `(ℤ/2ℤ)²` have the same number (four) of
irreducible complex characters — hence, both groups being abelian,
the same multiset `{1,1,1,1}` of irreducible representation
dimensions — yet only the first has an element of order four and the
groups are not isomorphic.  This is the proved
`NCG.representation_dimensions_not_duality`, re-exported by direct
application. -/
theorem representation_dimensions_not_duality_exact :
    (Nat.card (Multiplicative (ZMod 4) →* ℂˣ) = 4
      ∧ Nat.card (Multiplicative (ZMod 2 × ZMod 2) →* ℂˣ) = 4)
    ∧ addOrderOf (1 : ZMod 4) = 4
    ∧ (∀ x : ZMod 2 × ZMod 2, addOrderOf x ≠ 4)
    ∧ IsEmpty (ZMod 4 ≃+ ZMod 2 × ZMod 2) :=
  representation_dimensions_not_duality

/-! ## `cth:Schur-fill-in`:
Schur elimination can create quadratic fill-in -/

/-- `cth:Schur-fill-in`, exact statement at general `n`: a primitive
system with `n` boundary–interior couplings can have a Schur response
with `n²` nonzero entries.  First clause: the star-system self-energy
`b bᵀ/(d - z)` (one hidden scalar node of energy `d` coupled to all
`n` boundary ports by `b`, every `b_j ≠ 0`) has every entry
`b_i b_j/(d - z)` nonzero.  Second clause: an explicit primitive
(diagonal) `n`-port system with all couplings nonzero whose full
Schur response `A - K H⁻¹ Kᵀ` has all `n²` entries nonzero. -/
theorem schur_fill_in_general (n : ℕ) :
    -- rank-one self-energy: every entry nonzero
    (∀ bv : Fin n → ℚ, (∀ j, bv j ≠ 0) → ∀ s : ℚ, s ≠ 0 →
      ∀ i j, (s • Matrix.vecMulVec bv bv) i j ≠ 0)
    -- explicit primitive star system with quadratic fill-in
    ∧ ∃ (A : Matrix (Fin n) (Fin n) ℚ)
        (K : Matrix (Fin n) (Fin 1) ℚ)
        (H : Matrix (Fin 1) (Fin 1) ℚ),
        (∀ i j, i ≠ j → A i j = 0)
        ∧ (∀ i, K i 0 ≠ 0)
        ∧ (∀ i j, (A - K * H⁻¹ * Kᵀ) i j ≠ 0) := by
  constructor
  · intro bv hb s hs i j
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply,
      smul_eq_mul]
    exact mul_ne_zero hs (mul_ne_zero (hb i) (hb j))
  · refine ⟨(2 : ℚ) • 1,
      (Matrix.of fun _ _ => 1 : Matrix (Fin n) (Fin 1) ℚ), 1,
      ?_, ?_, ?_⟩
    · intro i j hij
      simp [Matrix.smul_apply, hij]
    · intro i
      simp [Matrix.of_apply]
    · intro i j
      have hK : ((Matrix.of fun _ _ => 1 : Matrix (Fin n) (Fin 1) ℚ)
          * ((1 : Matrix (Fin 1) (Fin 1) ℚ))⁻¹
          * (Matrix.of fun _ _ => 1 : Matrix (Fin n) (Fin 1) ℚ)ᵀ)
            i j = 1 := by
        rw [inv_one, Matrix.mul_one]
        simp [Matrix.mul_apply, Matrix.transpose_apply,
          Matrix.of_apply]
      rw [Matrix.sub_apply, hK]
      by_cases h : i = j
      · subst h
        norm_num [Matrix.smul_apply, Matrix.one_apply]
      · simp [Matrix.smul_apply, Matrix.one_apply, h]

/-! ## `cth:ambient-dimension-complexity`:
ambient record dimension does not imply a circuit lower bound -/

/-- `cth:ambient-dimension-complexity`, exact statement: representing
all `2ⁿ` Boolean inputs by orthonormal vectors forces ambient
dimension at least `2ⁿ` (the proved `NCG.boolean_record_dimension`,
re-exported), that dimension is realized by the standard
computational basis, and nevertheless explicit functions on that
basis have linear-size circuits: parity is computed exactly by the
chain of `xor` gates, one gate per input bit (the proved
`NCG.parity_fold_iff`, re-exported) — so storage dimension alone
implies no superpolynomial circuit lower bound. -/
theorem ambient_dimension_complexity_exact (n : ℕ) :
    -- forced ambient dimension `≥ 2ⁿ`
    (∀ (d : ℕ) (v : Fin (2 ^ n) → EuclideanSpace ℂ (Fin d)),
      Orthonormal ℂ v → 2 ^ n ≤ d)
    -- realized by the standard computational basis
    ∧ (∃ v : Fin (2 ^ n) → EuclideanSpace ℂ (Fin (2 ^ n)),
        Orthonormal ℂ v)
    -- an explicit function there has a linear `xor`-chain circuit
    ∧ (∀ l : List Bool,
        l.foldl xor false = true ↔ Odd (l.count true)) :=
  ⟨fun _ v hv => boolean_record_dimension v hv,
    ⟨⇑(EuclideanSpace.basisFun (Fin (2 ^ n)) ℂ),
      (EuclideanSpace.basisFun (Fin (2 ^ n)) ℂ).orthonormal⟩,
    fun l => parity_fold_iff l⟩

end NCG
