/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.OperatorLimits.HilbertBasisDiagonalSelfAdjoint
import RenewalGeometry.OperatorLimits.CompatibleStableAtlasNormResolvent
import RenewalGeometry.Continuum.TorusCellEmbeddingMultidim
import RenewalGeometry.DiscreteAnalysis.CovariantWilsonGardingExact

/-!
# The flat periodic spin torus: an unconditional compatible stable atlas

Paper `predictive_spectral_geometry`, label `cor:supp-flat-torus-spin` (and clause (ii) of
`thm:summary-spin`).

Data: the torus `M = ℝᵈ/ℤᵈ` with a constant flat (inverse) metric `g` (positive definite),
the periodic (trivial) spin structure, constant Hermitian Clifford coefficients
`c^j ∈ M_M(ℂ)` with `c^j c^k + c^k c^j = 2 g^{jk}`, trivial spin parallel transport, the doubled
coefficients `ĉ^j = c^j ⊗ σ₁`, `Γ_⊥ = I ⊗ σ₂` on `ℂ^M ⊗ ℂ² = ℂ^{M·2}` and a Wilson parameter
`ϖ ≠ 0`.

Continuum side.
* `SpinorL2 d K = ⊕_{a<K} L²(𝕋ᵈ)`: the space `L²(𝕋ᵈ; ℂ^K)` of doubled spinor fields, realised
  through their components in the standard basis of `ℂ^K` (`K = M·2`).
* `modeVec k v = e^{2πi k·x} v`; `symbol c k = Σ_j 2π k_j ĉ^j` is the Fourier symbol of
  `D̂ = Σ_j ĉ^j (-i ∂_j)`.  Diagonalising the Hermitian symbol fibrewise gives a Hilbert basis
  `eigBasis` of `SpinorL2` (`modeVec k (eigenvector)`), and `dirac` is the self-adjoint operator
  diagonal in it (`HilbertBasisDiagonal.data`), with `dirac_modeVec`:
  `D̂ (e^{2πik·x} v) = e^{2πik·x} (Σ_j 2πk_j ĉ^j) v`.  The trigonometric polynomials
  (`HilbertBasisDiagonal.core`) form a core.
* `sobolev : ℓ² → SpinorL2`, `a ↦ Σ (1 + |k|²)^{-1/2} a_{k,i} e_{k,i}`: the embedding
  `H¹ ↪ L²` (the Fourier `H¹`-norm `Σ (1 + |k|²) |f̂(k)|²` is the `ℓ²` norm of `a`), compact
  (`isCompactOperator_sobolev`, Rellich).
-/

open MeasureTheory Set Finset ComplexConjugate UnitAddTorus Filter Topology Matrix
open scoped BigOperators Real ENNReal InnerProductSpace lp

noncomputable section

namespace RenewalGeometry.FlatTorusSpinAtlas

open LatticeTorusPlancherel TorusCellEmbedding

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Scalar `L²(𝕋ᵈ)` with the Haar probability measure. -/
abbrev L2T (d : ℕ) := Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d)))

/-- `L²(𝕋ᵈ; ℂ^K)`, through the components in the standard basis of `ℂ^K`. -/
abbrev SpinorL2 (d K : ℕ) := PiLp 2 (fun _ : Fin K => L2T d)

/-- The fibre `ℂ^K`. -/
abbrev Fiber (K : ℕ) := EuclideanSpace ℂ (Fin K)

variable {d K : ℕ}

/-! ### Plane waves with values in the fibre -/

/-- The plane wave `x ↦ e^{2πi k·x} v`. -/
def modeVec (k : Fin d → ℤ) (v : Fiber K) : SpinorL2 d K :=
  WithLp.toLp 2 fun a => v a • mFourierLp 2 k

theorem modeVec_apply (k : Fin d → ℤ) (v : Fiber K) (a : Fin K) :
    modeVec k v a = v a • mFourierLp 2 k := rfl

theorem modeVec_add (k : Fin d → ℤ) (v w : Fiber K) :
    modeVec k (v + w) = modeVec k v + modeVec k w := by
  ext1 a
  simp only [modeVec_apply, PiLp.add_apply, add_smul]

theorem modeVec_smul (k : Fin d → ℤ) (c : ℂ) (v : Fiber K) :
    modeVec k (c • v) = c • modeVec k v := by
  ext1 a
  simp only [modeVec_apply, PiLp.smul_apply, smul_eq_mul, mul_smul]

theorem modeVec_sum {ι : Type*} (s : Finset ι) (k : Fin d → ℤ) (v : ι → Fiber K) :
    modeVec k (∑ i ∈ s, v i) = ∑ i ∈ s, modeVec k (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    ext1 a
    simp [modeVec_apply]
  | insert i s hi ih => rw [sum_insert hi, sum_insert hi, modeVec_add, ih]

theorem inner_fiber (v w : Fiber K) : ⟪v, w⟫_ℂ = ∑ a, conj (v a) * w a := by
  rw [PiLp.inner_apply]
  exact sum_congr rfl fun a _ => RCLike.inner_apply' _ _

theorem inner_modeVec (k k' : Fin d → ℤ) (v w : Fiber K) :
    ⟪modeVec k v, modeVec k' w⟫_ℂ = if k = k' then ⟪v, w⟫_ℂ else 0 := by
  have hF := orthonormal_mFourier (d := Fin d)
  rw [orthonormal_iff_ite] at hF
  rw [PiLp.inner_apply]
  simp only [modeVec_apply, inner_smul_left, inner_smul_right]
  split_ifs with h
  · subst h
    rw [inner_fiber]
    refine sum_congr rfl fun a _ => ?_
    rw [hF, ite_eq_left rfl]
    ring
  · simp [hF, h]

theorem inner_modeVec_left (k : Fin d → ℤ) (v : Fiber K) (f : SpinorL2 d K) :
    ⟪modeVec k v, f⟫_ℂ = ∑ a, conj (v a) * ⟪mFourierLp 2 k, f a⟫_ℂ := by
  rw [PiLp.inner_apply]
  simp only [modeVec_apply, inner_smul_left]

/-! ### The Fourier symbol of the doubled Dirac operator -/

/-- The symbol `σ(k) = Σ_j 2π k_j ĉ^j` of `D̂ = Σ_j ĉ^j (-i∂_j)` on `e^{2πik·x}`. -/
def symbol (c : Fin d → Matrix (Fin K) (Fin K) ℂ) (k : Fin d → ℤ) : Matrix (Fin K) (Fin K) ℂ :=
  ∑ j, ((2 * π * k j : ℝ) : ℂ) • c j

theorem symbol_isHermitian {c : Fin d → Matrix (Fin K) (Fin K) ℂ} (hc : ∀ j, (c j)ᴴ = c j)
    (k : Fin d → ℤ) : (symbol c k).IsHermitian := by
  unfold symbol IsHermitian
  simp only [conjTranspose_sum, conjTranspose_smul, hc, Complex.star_def, Complex.conj_ofReal]

section continuum

variable {c : Fin d → Matrix (Fin K) (Fin K) ℂ} (hc : ∀ j, (c j)ᴴ = c j)

/-- An orthonormal eigenbasis of the symbol at `k`. -/
def evec (k : Fin d → ℤ) (i : Fin K) : Fiber K := (symbol_isHermitian hc k).eigenvectorBasis i

/-- The eigenvalues of the symbol at `k`. -/
def eval (k : Fin d → ℤ) (i : Fin K) : ℝ := (symbol_isHermitian hc k).eigenvalues i

theorem symbol_mulVec_evec (k : Fin d → ℤ) (i : Fin K) :
    symbol c k *ᵥ (evec hc k i : Fin K → ℂ) = (eval hc k i : ℂ) • (evec hc k i : Fin K → ℂ) := by
  have := (symbol_isHermitian hc k).mulVec_eigenvectorBasis i
  rw [evec, eval, this]
  ext a
  simp [Complex.real_smul]

/-- Spectral decomposition in the fibre: `σ(k) v = Σ_i λ_i ⟪u_i, v⟫ u_i`. -/
theorem symbol_mulVec_eq (k : Fin d → ℤ) (v : Fiber K) :
    WithLp.toLp 2 (symbol c k *ᵥ (v : Fin K → ℂ)) =
      ∑ i, ((eval hc k i : ℂ) * ⟪evec hc k i, v⟫_ℂ) • evec hc k i := by
  have hv := (symbol_isHermitian hc k).eigenvectorBasis.sum_repr' v
  apply WithLp.ofLp_injective
  rw [WithLp.ofLp_toLp, WithLp.ofLp_sum]
  conv_lhs => rw [← hv]
  rw [WithLp.ofLp_sum, mulVec_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [WithLp.ofLp_smul, mulVec_smul, WithLp.ofLp_smul]
  change ⟪evec hc k i, v⟫_ℂ • (symbol c k *ᵥ (evec hc k i : Fin K → ℂ)) = _
  rw [symbol_mulVec_evec, smul_smul, mul_comm]

/-! ### The eigenbasis of `L²(𝕋ᵈ; ℂ^K)` -/

/-- The joint index `(k, i)`: frequency and eigenvector of the symbol. -/
abbrev Idx (d K : ℕ) := (Fin d → ℤ) × Fin K

/-- The eigenmodes `e^{2πik·x} u_i(k)`. -/
def eigVec (p : Idx d K) : SpinorL2 d K := modeVec p.1 (evec hc p.1 p.2)

theorem orthonormal_eigVec : Orthonormal ℂ (eigVec hc) := by
  rw [orthonormal_iff_ite]
  rintro ⟨k, i⟩ ⟨k', i'⟩
  simp only [eigVec, inner_modeVec, Prod.mk.injEq]
  by_cases hk : k = k'
  · subst hk
    have := (symbol_isHermitian hc k).eigenvectorBasis.orthonormal
    rw [orthonormal_iff_ite] at this
    simp only [ite_true, true_and, evec, this]
  · simp [hk]

/-- `e^{2πik·x} v` is a finite combination of eigenmodes. -/
theorem modeVec_eq_sum (k : Fin d → ℤ) (v : Fiber K) :
    modeVec k v = ∑ i, ⟪evec hc k i, v⟫_ℂ • eigVec hc (k, i) := by
  conv_lhs => rw [← (symbol_isHermitian hc k).eigenvectorBasis.sum_repr' v]
  rw [modeVec_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [modeVec_smul]
  rfl

theorem eq_zero_of_inner_mFourier {f : L2T d} (h : ∀ k, ⟪mFourierLp 2 k, f⟫_ℂ = 0) : f = 0 := by
  apply (mFourierBasis (d := Fin d)).repr.injective
  ext k
  rw [mFourierBasis.repr_apply_apply, coe_mFourierBasis, h k, map_zero]
  rfl

theorem eigVec_complete : (Submodule.span ℂ (Set.range (eigVec hc)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  rw [Submodule.mem_orthogonal] at hf
  have h0 : ∀ p, ⟪eigVec hc p, f⟫_ℂ = 0 := fun p =>
    hf _ (Submodule.subset_span ⟨p, rfl⟩)
  have hmode : ∀ k (v : Fiber K), ⟪modeVec k v, f⟫_ℂ = 0 := by
    intro k v
    rw [modeVec_eq_sum hc k v, sum_inner]
    exact sum_eq_zero fun i _ => by rw [inner_smul_left, h0, mul_zero]
  ext1 a
  refine eq_zero_of_inner_mFourier fun k => ?_
  have := hmode k (EuclideanSpace.single a 1)
  rw [inner_modeVec_left, sum_eq_single a] at this
  · simpa using this
  · intro b _ hb; simp [hb]
  · simp

/-- **The eigenbasis** of `L²(𝕋ᵈ; ℂ^K)` diagonalising the doubled Dirac operator. -/
def eigBasis : HilbertBasis (Idx d K) ℂ (SpinorL2 d K) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_eigVec hc) (eigVec_complete hc)

theorem eigBasis_apply (p : Idx d K) : eigBasis hc p = eigVec hc p := by
  rw [eigBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

/-- The eigenvalue of the eigenmode `(k, i)`. -/
def evalIdx (p : Idx d K) : ℝ := eval hc p.1 p.2

/-- **The doubled continuum Dirac operator `D̂ = Σ_j ĉ^j (-i∂_j)`** on `L²(𝕋ᵈ; ℂ^K)`, as a
self-adjoint operator presented by its resolvents. -/
def dirac : SelfAdjointResolventData (SpinorL2 d K) :=
  HilbertBasisDiagonal.data (eigBasis hc) (evalIdx hc)

/-- The trigonometric polynomials (finite combinations of plane waves). -/
def trigCore : Submodule ℂ (SpinorL2 d K) := HilbertBasisDiagonal.core (eigBasis hc)

theorem modeVec_mem_trigCore (k : Fin d → ℤ) (v : Fiber K) : modeVec k v ∈ trigCore hc := by
  rw [modeVec_eq_sum hc]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  rw [← eigBasis_apply]
  exact Submodule.subset_span ⟨(k, i), rfl⟩

theorem trigCore_le_domain : trigCore hc ≤ (dirac hc).op.domain :=
  HilbertBasisDiagonal.core_le_domain _ _

/-- **`D̂` on plane waves**: `D̂ (e^{2πik·x} v) = e^{2πik·x} (Σ_j 2πk_j ĉ^j) v`. -/
theorem dirac_modeVec (k : Fin d → ℤ) (v : Fiber K) :
    (dirac hc).op ⟨modeVec k v, trigCore_le_domain hc (modeVec_mem_trigCore hc k v)⟩ =
      modeVec k (WithLp.toLp 2 (symbol c k *ᵥ (v : Fin K → ℂ))) := by
  classical
  have hsum : modeVec k v = ∑ p ∈ (Finset.univ : Finset (Fin K)).image (fun i => (k, i)),
      (fun p : Idx d K => if p.1 = k then ⟪evec hc k p.2, v⟫_ℂ else 0) p • eigBasis hc p := by
    rw [sum_image (fun i _ j _ h => by simpa using h), modeVec_eq_sum hc]
    refine sum_congr rfl fun i _ => ?_
    simp [eigBasis_apply]
  have hmem : (∑ p ∈ (Finset.univ : Finset (Fin K)).image (fun i => (k, i)),
      (fun p : Idx d K => if p.1 = k then ⟪evec hc k p.2, v⟫_ℂ else 0) p • eigBasis hc p) ∈
      HilbertBasisDiagonal.domain (eigBasis hc) (evalIdx hc) := by
    rw [← hsum]; exact trigCore_le_domain hc (modeVec_mem_trigCore hc k v)
  have key := HilbertBasisDiagonal.diagOp_finsum (eigBasis hc) (evalIdx hc) _ _ hmem
  have hsub : (⟨modeVec k v, trigCore_le_domain hc (modeVec_mem_trigCore hc k v)⟩ :
      (dirac hc).op.domain) = ⟨_, hmem⟩ := Subtype.ext hsum
  calc (dirac hc).op ⟨modeVec k v, trigCore_le_domain hc (modeVec_mem_trigCore hc k v)⟩
      = (dirac hc).op ⟨_, hmem⟩ := congrArg _ hsub
    _ = _ := key
    _ = _ := by
      rw [sum_image (fun i _ j _ h => by simpa using h), symbol_mulVec_eq hc, modeVec_sum]
      refine sum_congr rfl fun i _ => ?_
      simp only [ite_true, eigBasis_apply, eigVec, evalIdx, modeVec_smul]

/-! ### `D̂` is the differential operator `Σ_j ĉ^j (-i∂_j)` on plane waves -/

/-- `∂_j e^{2πik·y} = 2πi k_j e^{2πik·y}` (derivative along the `j`-th coordinate circle). -/
theorem hasDerivAt_mFourier_line (k : Fin d → ℤ) (j : Fin d) (y : UnitAddTorus (Fin d)) :
    HasDerivAt (fun t : ℝ => mFourier k (y + Pi.single j ((t : ℝ) : UnitAddCircle)))
      (2 * π * Complex.I * (k j : ℂ) * mFourier k y) 0 := by
  have e : (fun t : ℝ => mFourier k (y + Pi.single j ((t : ℝ) : UnitAddCircle))) =
      fun t : ℝ => mFourier k y * Complex.exp (2 * π * Complex.I * (k j : ℂ) * (t : ℂ)) := by
    funext t
    rw [mFourier_add_apply']
    congr 1
    simp only [mFourier, ContinuousMap.coe_mk]
    rw [Finset.prod_eq_single j]
    · rw [Pi.single_eq_same, fourier_coe_apply]
      congr 1
      push_cast
      ring
    · intro i _ hi
      rw [Pi.single_eq_of_ne hi, fourier_apply, smul_zero, AddCircle.toCircle_zero, Circle.coe_one]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [e]
  have h1 : HasDerivAt (fun t : ℝ => 2 * π * Complex.I * (k j : ℂ) * (t : ℂ))
      (2 * π * Complex.I * (k j : ℂ)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul (2 * π * Complex.I * (k j : ℂ))
  have h2 := (h1.cexp).const_mul (mFourier k y)
  simpa [mul_comm, mul_left_comm, mul_assoc] using h2

/-- **`D̂` acts on plane waves as `Σ_j ĉ^j (-i ∂_j)`**: at every point, with
`∂_j e^{2πik·y} = 2πi k_j e^{2πik·y}` (`hasDerivAt_mFourier_line`),
`Σ_j ĉ^j (-i ∂_j)(e^{2πik·y} v) = e^{2πik·y} σ(k) v`. -/
theorem sum_dirac_differential (c : Fin d → Matrix (Fin K) (Fin K) ℂ) (k : Fin d → ℤ)
    (v : Fin K → ℂ) (y : UnitAddTorus (Fin d)) :
    ∑ j, c j *ᵥ ((-Complex.I) • ((2 * π * Complex.I * (k j : ℂ) * mFourier k y) • v)) =
      mFourier k y • (symbol c k *ᵥ v) := by
  rw [symbol, Matrix.sum_mulVec, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.smul_mulVec, smul_smul, smul_smul]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ### The Sobolev space `H¹` and the compact embedding -/

/-- The `H¹` weight `1 + |k|²`. -/
def sobWeight (k : Fin d → ℤ) : ℝ := 1 + ∑ j, ((k j : ℤ) : ℝ) ^ 2

theorem one_le_sobWeight (k : Fin d → ℤ) : 1 ≤ sobWeight k := by
  unfold sobWeight
  have : 0 ≤ ∑ j, ((k j : ℤ) : ℝ) ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  linarith

theorem sobWeight_pos (k : Fin d → ℤ) : 0 < sobWeight k := one_pos.trans_le (one_le_sobWeight k)

/-- The multiplier `(1 + |k|²)^{-1/2}`. -/
def sobMult (p : Idx d K) : ℂ := ((Real.sqrt (sobWeight p.1))⁻¹ : ℝ)

theorem norm_sobMult_le (p : Idx d K) : ‖sobMult p‖ ≤ 1 := by
  rw [sobMult, Complex.norm_real, Real.norm_eq_abs, abs_inv,
    abs_of_pos (Real.sqrt_pos.2 (sobWeight_pos p.1))]
  exact inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 (one_le_sobWeight p.1))

theorem finite_sobWeight_le (R : ℝ) : {k : Fin d → ℤ | sobWeight k ≤ R}.Finite := by
  set N : ℕ := ⌈R⌉₊
  refine (Set.Finite.pi (t := fun _ : Fin d => (Set.Icc (-(N : ℤ)) N))
    (fun _ => Set.finite_Icc _ _)).subset ?_
  intro k hk i _
  simp only [Set.mem_ofPred_eq] at hk
  have hR1 : 1 ≤ R := (one_le_sobWeight k).trans hk
  have hki : ((k i : ℤ) : ℝ) ^ 2 ≤ R := by
    have : ((k i : ℤ) : ℝ) ^ 2 ≤ ∑ j, ((k j : ℤ) : ℝ) ^ 2 :=
      single_le_sum (f := fun j => ((k j : ℤ) : ℝ) ^ 2) (fun _ _ => sq_nonneg _) (mem_univ i)
    unfold sobWeight at hk
    linarith
  have habs : |((k i : ℤ) : ℝ)| ≤ N := by
    have h1 : |((k i : ℤ) : ℝ)| ≤ |((k i : ℤ) : ℝ)| ^ 2 ∨ |((k i : ℤ) : ℝ)| < 1 := by
      by_cases h : 1 ≤ |((k i : ℤ) : ℝ)|
      · left; nlinarith
      · right; linarith
    have hR : R ≤ N := Nat.le_ceil R
    rcases h1 with h1 | h1
    · rw [sq_abs] at h1; linarith
    · have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      linarith
  have habs' : |k i| ≤ (N : ℤ) := by exact_mod_cast habs
  exact ⟨by linarith [neg_abs_le (k i)], le_trans (le_abs_self _) habs'⟩

theorem tendsto_sobMult : Tendsto (sobMult (d := d) (K := K)) cofinite (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero, Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_cofinite]
  refine ((finite_sobWeight_le ((ε⁻¹) ^ 2)).prod (Set.finite_univ (α := Fin K))).subset ?_
  rintro ⟨k, i⟩ hp
  simp only [Set.mem_ofPred_eq, dist_zero_right, norm_norm, not_lt] at hp
  refine ⟨?_, Set.mem_univ _⟩
  simp only [Set.mem_ofPred_eq]
  rw [sobMult, Complex.norm_real, Real.norm_eq_abs, abs_inv,
    abs_of_pos (Real.sqrt_pos.2 (sobWeight_pos k))] at hp
  have hs := Real.sqrt_pos.2 (sobWeight_pos k)
  have h1 : Real.sqrt (sobWeight k) ≤ ε⁻¹ := by
    rw [le_inv_comm₀ hs hε]
    exact hp
  have h2 := Real.sq_sqrt (sobWeight_pos k).le
  nlinarith [Real.sqrt_nonneg (sobWeight k)]

/-- **The Sobolev embedding `H¹ ↪ L²`**: `a ↦ Σ_{k,i} (1 + |k|²)^{-1/2} a_{k,i} e_{k,i}`;
the `ℓ²` norm of `a` is the Fourier `H¹` norm of the image. -/
def sobolev : ℓ²(Idx d K, ℂ) →L[ℂ] SpinorL2 d K :=
  (eigBasis hc).repr.symm.toLinearIsometry.toContinuousLinearMap ∘L
    HilbertBasisDiagonal.mulCLM sobMult norm_sobMult_le

/-- **Rellich**: the embedding `H¹ ↪ L²` is compact. -/
theorem isCompactOperator_sobolev : IsCompactOperator (sobolev hc) := by
  classical
  exact (HilbertBasisDiagonal.isCompactOperator_mulCLM sobMult norm_sobMult_le
    tendsto_sobMult).clm_comp (eigBasis hc).repr.symm.toLinearIsometry.toContinuousLinearMap

end continuum

/-! ### The stage spaces and the piecewise-constant embedding -/

section stage

open FrozenWilsonGarding VariableWilsonGarding

variable {m : ℕ} [NeZero m]

/-- The stage space `ℓ²((ℤ/m)ᵈ; ℂ^K)` (unweighted; the physical lattice section is
`m^{d/2} v`, whose `h^d`-weighted norm is `‖v‖`). -/
abbrev Stage (d K m : ℕ) := EuclideanSpace ℂ (Grid d m × Fin K)

/-- The `a`-th component of a stage vector. -/
def comp (v : Stage d K m) (a : Fin K) : EuclideanSpace ℂ (Grid d m) :=
  WithLp.toLp 2 fun x => v (x, a)

theorem comp_apply (v : Stage d K m) (a : Fin K) (x : Grid d m) : comp v a x = v (x, a) := rfl

theorem comp_add (v w : Stage d K m) (a : Fin K) : comp (v + w) a = comp v a + comp w a := rfl

theorem comp_smul (c : ℂ) (v : Stage d K m) (a : Fin K) : comp (c • v) a = c • comp v a := rfl

theorem norm_sq_stage (v : Stage d K m) : ‖v‖ ^ 2 = ∑ a, ‖comp v a‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Finset.sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [EuclideanSpace.norm_sq_eq]
  rfl

theorem norm_sq_spinor (f : SpinorL2 d K) : ‖f‖ ^ 2 = ∑ a, ‖f a‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 _ f

/-- The piecewise-constant embedding, componentwise. -/
def embedLin (d K m : ℕ) [NeZero m] : Stage d K m →ₗ[ℂ] SpinorL2 d K where
  toFun v := WithLp.toLp 2 fun a => pcEmbedding d m (comp v a)
  map_add' v w := by
    ext1 a
    simp only [PiLp.add_apply, comp_add, map_add]
  map_smul' c v := by
    ext1 a
    simp only [PiLp.smul_apply, comp_smul, map_smul, RingHom.id_apply]

/-- **The isometric piecewise-constant embedding `𝒥⁰_h : ℓ²((ℤ/m)ᵈ; ℂ^K) → L²(𝕋ᵈ; ℂ^K)`**. -/
def embed (d K m : ℕ) [NeZero m] : Stage d K m →ₗᵢ[ℂ] SpinorL2 d K where
  toLinearMap := embedLin d K m
  norm_map' v := by
    have h : ‖embedLin d K m v‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [norm_sq_spinor, norm_sq_stage]
      refine sum_congr rfl fun a _ => ?_
      change ‖pcEmbedding d m (comp v a)‖ ^ 2 = _
      rw [LinearIsometry.norm_map]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

theorem embed_apply (v : Stage d K m) (a : Fin K) :
    embed d K m v a = pcEmbedding d m (comp v a) := rfl

/-- The adjoint `(𝒥⁰_h)^*`: componentwise cell coefficients. -/
theorem embed_adjoint_apply (f : SpinorL2 d K) :
    ContinuousLinearMap.adjoint (embed d K m).toContinuousLinearMap f =
      WithLp.toLp 2 fun p : Grid d m × Fin K =>
        ContinuousLinearMap.adjoint (pcEmbedding d m).toContinuousLinearMap (f p.2) p.1 := by
  apply ext_inner_left ℂ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_right, PiLp.inner_apply, PiLp.inner_apply,
    Fintype.sum_prod_type, Finset.sum_comm]
  refine sum_congr rfl fun a _ => ?_
  change ⟪pcEmbedding d m (comp v a), f a⟫_ℂ = _
  rw [← LinearIsometry.coe_toContinuousLinearMap, ← ContinuousLinearMap.adjoint_inner_right,
    PiLp.inner_apply]
  rfl

theorem comp_embed_adjoint (f : SpinorL2 d K) (a : Fin K) :
    comp (ContinuousLinearMap.adjoint (embed d K m).toContinuousLinearMap f) a =
      ContinuousLinearMap.adjoint (pcEmbedding d m).toContinuousLinearMap (f a) := by
  rw [embed_adjoint_apply]
  rfl

theorem tendsto_spinor {F : ℕ → SpinorL2 d K} {f : SpinorL2 d K}
    (h : ∀ a, Tendsto (fun n => F n a) atTop (𝓝 (f a))) : Tendsto F atTop (𝓝 f) := by
  have hc := (PiLp.continuous_toLp 2 (fun _ : Fin K => L2T d)).tendsto (WithLp.ofLp f)
  have := hc.comp (tendsto_pi_nhds.2 h)
  simpa only [Function.comp_def, WithLp.toLp_ofLp] using this

/-- **(A1)**: `𝒥⁰_h (𝒥⁰_h)^* → I` strongly on `L²(𝕋ᵈ; ℂ^K)`. -/
theorem tendsto_embed_adjoint (f : SpinorL2 d K) :
    Tendsto (fun n : ℕ => embed d K (n + 1)
      (ContinuousLinearMap.adjoint (embed d K (n + 1)).toContinuousLinearMap f)) atTop (𝓝 f) := by
  refine tendsto_spinor fun a => ?_
  simp only [embed_apply, comp_embed_adjoint]
  exact tendsto_pcEmbedding_adjoint (f a)

/-! ### The lattice operator -/

/-- The lattice section of a stage vector (unscaled). -/
def toSec (v : Stage d K m) : TorusSection d m K := fun x a => v (x, a)

theorem eucl_toSec (v : Stage d K m) : eucl (toSec v) = v := rfl

theorem toSec_eucl (u : TorusSection d m K) : toSec (eucl u) = u := rfl

variable (h ϖ : ℝ) (c : Fin d → Matrix (Fin K) (Fin K) ℂ) (Γ : Matrix (Fin K) (Fin K) ℂ)

theorem eq_of_dftVec_eq {f g : TorusSection d m K} (H : ∀ ℓ, dftVec f ℓ = dftVec g ℓ) :
    f = g := by
  funext x a
  rw [← dft_inversion' (fun y => f y a) x, ← dft_inversion' (fun y => g y a) x]
  refine sum_congr rfl fun ℓ _ => ?_
  have := congrFun (H ℓ) a
  simp only [dftVec] at this
  rw [this]

theorem frozenWilson_add (hh : h ≠ 0) (u w : TorusSection d m K) :
    frozenWilson h ϖ c Γ (u + w) = frozenWilson h ϖ c Γ u + frozenWilson h ϖ c Γ w := by
  refine eq_of_dftVec_eq fun ℓ => ?_
  rw [dftVec_add, dftVec_frozenWilson h ϖ hh, dftVec_frozenWilson h ϖ hh,
    dftVec_frozenWilson h ϖ hh, dftVec_add, mulVec_add]

theorem frozenWilson_smul (hh : h ≠ 0) (a : ℂ) (u : TorusSection d m K) :
    frozenWilson h ϖ c Γ (a • u) = a • frozenWilson h ϖ c Γ u := by
  refine eq_of_dftVec_eq fun ℓ => ?_
  rw [dftVec_smul, dftVec_frozenWilson h ϖ hh, dftVec_frozenWilson h ϖ hh, dftVec_smul,
    mulVec_smul]

theorem inv_mesh_ne_zero : (m : ℝ)⁻¹ ≠ 0 := inv_ne_zero n_pos.ne'

/-- The frozen doubled Wilson operator `D^W_{g,h}` on the stage space. -/
def stageLin (d K m : ℕ) [NeZero m] (ϖ : ℝ) (c : Fin d → Matrix (Fin K) (Fin K) ℂ)
    (Γ : Matrix (Fin K) (Fin K) ℂ) : Stage d K m →ₗ[ℂ] Stage d K m where
  toFun v := eucl (frozenWilson (m : ℝ)⁻¹ ϖ c Γ (toSec v))
  map_add' v w := by
    change eucl (frozenWilson _ ϖ c Γ (toSec v + toSec w)) = _
    rw [frozenWilson_add _ _ _ _ inv_mesh_ne_zero]; rfl
  map_smul' a v := by
    change eucl (frozenWilson _ ϖ c Γ (a • toSec v)) = _
    rw [frozenWilson_smul _ _ _ _ inv_mesh_ne_zero]; rfl

/-- **The lattice Wilson operator `D^W_{g,h}`** (mesh `h = 1/m`) as a bounded operator. -/
def stage (d K m : ℕ) [NeZero m] (ϖ : ℝ) (c : Fin d → Matrix (Fin K) (Fin K) ℂ)
    (Γ : Matrix (Fin K) (Fin K) ℂ) : Stage d K m →L[ℂ] Stage d K m :=
  LinearMap.toContinuousLinearMap (stageLin d K m ϖ c Γ)

theorem stage_apply (v : Stage d K m) :
    stage d K m ϖ c Γ v = eucl (frozenWilson (m : ℝ)⁻¹ ϖ c Γ (toSec v)) := rfl

theorem gridInner_eq_inner (u w : TorusSection d m K) : gridInner u w = ⟪eucl u, eucl w⟫_ℂ := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, gridInner]
  refine sum_congr rfl fun x _ => ?_
  simp only [dotProduct, Pi.star_apply, RCLike.star_def]
  refine sum_congr rfl fun a _ => ?_
  rw [RCLike.inner_apply']
  rfl

/-- **Self-adjointness** of the lattice operator (symmetric placement of the coefficients). -/
theorem isSelfAdjoint_stage (hc : ∀ j, (c j)ᴴ = c j) (hΓ : Γᴴ = Γ) :
    IsSelfAdjoint (stage d K m ϖ c Γ) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro v w
  change ⟪stage d K m ϖ c Γ v, w⟫_ℂ = ⟪v, stage d K m ϖ c Γ w⟫_ℂ
  rw [stage_apply, stage_apply, ← eucl_toSec w, ← eucl_toSec v, toSec_eucl, toSec_eucl,
    ← gridInner_eq_inner, ← gridInner_eq_inner]
  have key := CovariantWilsonGarding.covVarWilson_symmetric (m : ℝ)⁻¹ ϖ (fun _ => c)
    (fun _ _ => 1) Γ (fun _ j => hc j) hΓ (fun _ _ => by rw [Matrix.mul_one, Matrix.one_mul])
    (toSec v) (toSec w)
  rwa [CovariantWilsonGarding.covVarWilson_one, CovariantWilsonGarding.covVarWilson_one,
    varWilson_const, varWilson_const] at key

/-! ### The discrete first-order norm and the Gårding estimate -/

/-- The physical lattice section `u = m^{d/2} v` (cell weight `h^d`). -/
def phys (v : Stage d K m) : TorusSection d m K := ((scale m d : ℝ) : ℂ) • toSec v

/-- The discrete `H¹` norm `‖u‖_{1,h}` of `eq:discrete-H1-norm` of the physical section. -/
def discreteNorm (d K m : ℕ) [NeZero m] (v : Stage d K m) : ℝ :=
  Real.sqrt (h1NormSq (m : ℝ)⁻¹ (phys v))

theorem gridNormSq_smul (hh : ℝ) (a : ℂ) (u : TorusSection d m K) :
    gridNormSq hh (a • u) = ‖a‖ ^ 2 * gridNormSq hh u := by
  simp only [gridNormSq, Pi.smul_apply, euclNormSq_smul, Finset.mul_sum]
  refine sum_congr rfl fun x _ => ?_
  ring

theorem weight_mul_scale_sq : ((m : ℝ)⁻¹) ^ d * scale m d ^ 2 = 1 := by
  rw [scale_sq, inv_pow, inv_mul_cancel₀ (pow_pos n_pos d).ne']

theorem gridNormSq_phys (u : TorusSection d m K) :
    gridNormSq (m : ℝ)⁻¹ (((scale m d : ℝ) : ℂ) • u) = ‖eucl u‖ ^ 2 := by
  rw [gridNormSq_smul, gridNormSq_eq_norm_eucl_sq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos scale_pos, ← mul_assoc, mul_comm (scale m d ^ 2), weight_mul_scale_sq, one_mul]

/-- **(A2), the global graph estimate** `‖u‖_{1,h} ≤ C (‖D_h u‖_h + ‖u‖_h)` on the flat torus,
from the constant-coefficient Fourier estimate (`FrozenWilsonGarding.h1NormSq_le`). -/
theorem discreteNorm_le (lam Lam : ℝ) (hlam : 0 < lam) (hϖ : ϖ ≠ 0) (hLam : 0 ≤ Lam)
    (g : Matrix (Fin d) (Fin d) ℝ) (hcl : FrozenWilsonSymbol.DoubledCliffordData c Γ g)
    (hc : ∀ j, (c j)ᴴ = c j) (hΓ : Γᴴ = Γ)
    (hlow : ∀ ξ : Fin d → ℝ, lam * ∑ j, ξ j ^ 2 ≤ ∑ j, ∑ k, g j k * (ξ j * ξ k))
    (hup : ∀ ξ : Fin d → ℝ, ∑ j, ∑ k, g j k * (ξ j * ξ k) ≤ Lam * ∑ j, ξ j ^ 2)
    (v : Stage d K m) :
    discreteNorm d K m v ≤
      Real.sqrt (max 1 (min lam (ϖ ^ 2))⁻¹) * (‖stage d K m ϖ c Γ v‖ + ‖v‖) := by
  have hh : (0 : ℝ) < (m : ℝ)⁻¹ := inv_pos.2 n_pos
  have key := h1NormSq_le (m : ℝ)⁻¹ ϖ lam Lam hh hlam hϖ hLam c Γ g hcl hc hΓ hlow hup (phys v)
  have hD : gridNormSq (m : ℝ)⁻¹ (frozenWilson (m : ℝ)⁻¹ ϖ c Γ (phys v)) =
      ‖stage d K m ϖ c Γ v‖ ^ 2 := by
    rw [phys, frozenWilson_smul _ _ _ _ inv_mesh_ne_zero, gridNormSq_phys]
    rfl
  have hu : gridNormSq (m : ℝ)⁻¹ (phys v) = ‖v‖ ^ 2 := by
    rw [phys, gridNormSq_phys, eucl_toSec]
  rw [hD, hu] at key
  have hC : 0 ≤ max 1 (min lam (ϖ ^ 2))⁻¹ := zero_le_one.trans (le_max_left _ _)
  unfold discreteNorm
  rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ ‖stage d K m ϖ c Γ v‖ + ‖v‖), ← Real.sqrt_mul hC]
  refine Real.sqrt_le_sqrt (key.trans ?_)
  refine mul_le_mul_of_nonneg_left ?_ hC
  nlinarith [norm_nonneg (stage d K m ϖ c Γ v), norm_nonneg v]

end stage

/-! ### Discrete Fourier coefficients and the reconstruction `I_h` -/

section reconstruction

open FrozenWilsonGarding VariableWilsonGarding FrozenWilsonSymbol

variable {m : ℕ} [NeZero m]

theorem phys_add (v w : Stage d K m) : phys (v + w) = phys v + phys w := by
  funext x a
  simp only [phys, toSec, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  change _ * (v (x, a) + w (x, a)) = _
  ring

theorem phys_smul (b : ℂ) (v : Stage d K m) : phys (b • v) = b • phys v := by
  funext x a
  simp only [phys, toSec, Pi.smul_apply, smul_eq_mul]
  change _ * (b * v (x, a)) = _
  ring

/-- The discrete Fourier coefficients `û(ℓ) ∈ ℂ^K` of the physical section. -/
def coef (v : Stage d K m) (ℓ : Grid d m) : Fiber K := WithLp.toLp 2 (dftVec (phys v) ℓ)

theorem coef_apply (v : Stage d K m) (ℓ : Grid d m) (a : Fin K) :
    coef v ℓ a = ((scale m d : ℝ) : ℂ) * dft (fun x => v (x, a)) ℓ := by
  change dftVec (phys v) ℓ a = _
  have : (fun x => phys v x a) = ((scale m d : ℝ) : ℂ) • fun x => v (x, a) := by
    funext x; rfl
  simp only [dftVec]
  rw [this, dft_smul, smul_eq_mul]

theorem coef_add (v w : Stage d K m) (ℓ : Grid d m) : coef (v + w) ℓ = coef v ℓ + coef w ℓ := by
  simp only [coef, phys_add, dftVec_add]; rfl

theorem coef_smul (b : ℂ) (v : Stage d K m) (ℓ : Grid d m) : coef (b • v) ℓ = b • coef v ℓ := by
  simp only [coef, phys_smul, dftVec_smul]; rfl

/-- Fourier expansion of a component: `v_a = Σ_ℓ û_a(ℓ) · modeSample ℓ̃`. -/
theorem comp_eq_sum (v : Stage d K m) (a : Fin K) :
    comp v a = ∑ ℓ, coef v ℓ a • modeSample m (signedRep ℓ) := by
  have hs : ((scale m d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (scale_pos (n := m) (d := d)).ne'
  ext x
  rw [comp_apply, ← dft_inversion' (fun y => v (y, a)) x]
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine sum_congr rfl fun ℓ _ => ?_
  rw [modeSample_apply, zcast_signedRep, coef_apply]
  field_simp

theorem embed_eq_sum (v : Stage d K m) (a : Fin K) :
    embed d K m v a = ∑ ℓ, coef v ℓ a • pcEmbedding d m (modeSample m (signedRep ℓ)) := by
  rw [embed_apply, comp_eq_sum, map_sum]
  simp only [LinearIsometry.map_smul]

/-- The trigonometric reconstruction `Σ_ℓ e^{2πi ℓ̃·x} û(ℓ)` of a lattice section. -/
def interp (v : Stage d K m) : SpinorL2 d K := ∑ ℓ, modeVec (signedRep ℓ) (coef v ℓ)

theorem interp_apply (v : Stage d K m) (a : Fin K) :
    interp v a = ∑ ℓ, coef v ℓ a • mFourierLp 2 (signedRep ℓ) := by
  simp only [interp, WithLp.ofLp_sum, Finset.sum_apply]
  rfl

theorem interp_sub_embed_apply (v : Stage d K m) (a : Fin K) :
    (interp v - embed d K m v) a = ∑ ℓ, coef v ℓ a • modeError ℓ := by
  rw [PiLp.sub_apply, interp_apply, embed_eq_sum, ← sum_sub_distrib]
  simp only [modeError, smul_sub]

theorem norm_sq_interp_sub_embed (v : Stage d K m) :
    ‖interp v - embed d K m v‖ ^ 2 = ∑ ℓ, ‖coef v ℓ‖ ^ 2 * ‖modeError (n := m) ℓ‖ ^ 2 := by
  rw [norm_sq_spinor]
  simp_rw [interp_sub_embed_apply, norm_sum_modeError_sq]
  rw [sum_comm]
  refine sum_congr rfl fun ℓ _ => ?_
  rw [← sum_mul, EuclideanSpace.norm_sq_eq]

/-! ### Parseval and the discrete first-order norm in Fourier variables -/

theorem norm_sq_coef (v : Stage d K m) (ℓ : Grid d m) :
    ‖coef v ℓ‖ ^ 2 = euclNormSq (dftVec (phys v) ℓ) := by
  rw [EuclideanSpace.norm_sq_eq]; rfl

theorem mesh_pow_mul : ((m : ℝ)⁻¹) ^ d * (m : ℝ) ^ d = 1 := by
  rw [inv_pow, inv_mul_cancel₀ (pow_pos n_pos d).ne']

theorem gridNormSq_phys_eq (v : Stage d K m) : gridNormSq (m : ℝ)⁻¹ (phys v) = ‖v‖ ^ 2 := by
  rw [phys, gridNormSq_phys, eucl_toSec]

/-- **Parseval**: `‖v‖² = Σ_ℓ |û(ℓ)|²`. -/
theorem norm_sq_eq_sum_coef (v : Stage d K m) : ‖v‖ ^ 2 = ∑ ℓ, ‖coef v ℓ‖ ^ 2 := by
  rw [← gridNormSq_phys_eq, gridNormSq, sum_euclNormSq_eq, ← mul_assoc, mesh_pow_mul, one_mul]
  simp_rw [norm_sq_coef]

theorem sum_fwd_eq (v : Stage d K m) :
    ∑ j, gridNormSq (m : ℝ)⁻¹ (forwardDifference (m : ℝ)⁻¹ j (phys v)) =
      ∑ ℓ, (2 * (m : ℝ) ^ 2 * wilsonScalar (angle ℓ)) * ‖coef v ℓ‖ ^ 2 := by
  rw [sum_gridNormSq_forwardDifference _ (inv_pos.2 n_pos), mesh_pow_mul, one_mul]
  simp_rw [norm_sq_coef, inv_pow, inv_inv]

theorem gridNormSq_nonneg' (hh : ℝ) (hh0 : 0 ≤ hh) (u : TorusSection d m K) :
    0 ≤ gridNormSq hh u :=
  mul_nonneg (pow_nonneg hh0 _) (sum_nonneg fun _ _ => euclNormSq_nonneg _)

/-- `‖u‖²_{1,h} = Σ_ℓ (1 + 2h⁻² s(θ_ℓ)) |û(ℓ)|²`. -/
theorem discreteNorm_sq (v : Stage d K m) :
    discreteNorm d K m v ^ 2 =
      ∑ ℓ, (1 + 2 * (m : ℝ) ^ 2 * wilsonScalar (angle ℓ)) * ‖coef v ℓ‖ ^ 2 := by
  have hh : (0 : ℝ) ≤ (m : ℝ)⁻¹ := (inv_pos.2 n_pos).le
  have hnn : 0 ≤ h1NormSq (m : ℝ)⁻¹ (phys v) :=
    add_nonneg (gridNormSq_nonneg' _ hh _) (sum_nonneg fun _ _ => gridNormSq_nonneg' _ hh _)
  rw [discreteNorm, Real.sq_sqrt hnn, h1NormSq, sum_fwd_eq, gridNormSq_phys_eq,
    norm_sq_eq_sum_coef, ← sum_add_distrib]
  refine sum_congr rfl fun ℓ _ => ?_
  ring

theorem discreteNorm_nonneg (v : Stage d K m) : 0 ≤ discreteNorm d K m v := Real.sqrt_nonneg _

/-- The forward-difference symbol on the signed frequency: `16 ℓ̃² ≤ 2m²(1 - cos(2π ℓ/m))`. -/
theorem sixteen_mul_sq_le (a : ZMod m) :
    16 * ((a.valMinAbs : ℤ) : ℝ) ^ 2 ≤
      2 * (m : ℝ) ^ 2 * (1 - Real.cos (2 * π * (a.val : ℝ) / m)) := by
  have hm := n_pos (n := m)
  set t : ℤ := a.valMinAbs with ht
  have hχ1 : ZMod.stdAddChar a = Complex.exp (Complex.I * ((2 * π * (a.val : ℝ) / m : ℝ) : ℂ)) :=
    stdAddChar_eq_exp a
  have hχ2 : ZMod.stdAddChar a = Complex.exp (Complex.I * ((2 * π * (t : ℝ) / m : ℝ) : ℂ)) := by
    conv_lhs => rw [← a.coe_valMinAbs]
    rw [ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  have e1 : ‖ZMod.stdAddChar a - 1‖ ^ 2 = 2 * (1 - Real.cos (2 * π * (a.val : ℝ) / m)) := by
    rw [hχ1]; exact norm_exp_I_mul_sub_one_sq _
  have e2 : ‖ZMod.stdAddChar a - 1‖ = 2 * |Real.sin (π * t / m)| := by
    rw [hχ2, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_two]
    congr 3
    ring
  have hta : |(t : ℝ)| * 2 ≤ m := by
    have h := a.valMinAbs_mem_Ioc
    have h2 : |a.valMinAbs| * 2 ≤ (m : ℤ) := by
      rcases h with ⟨h1, h2⟩
      rcases abs_cases a.valMinAbs with ⟨h3, _⟩ | ⟨h3, _⟩ <;> rw [h3] <;> omega
    exact_mod_cast h2
  set y : ℝ := π * t / m with hy
  have hyabs : |y| = π * |(t : ℝ)| / m := by
    rw [hy, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hm]
  have hyle : |y| ≤ π / 2 := by
    rw [hyabs, div_le_iff₀ hm]
    nlinarith [Real.pi_pos]
  have hsin : 2 / π * |y| ≤ |Real.sin y| := by
    rcases le_total 0 y with h0 | h0
    · rw [abs_of_nonneg h0]
      have := Real.mul_le_sin h0 (by rwa [abs_of_nonneg h0] at hyle)
      exact this.trans (le_abs_self _)
    · rw [abs_of_nonpos h0]
      have := Real.mul_le_sin (neg_nonneg.mpr h0) (by rwa [abs_of_nonpos h0] at hyle)
      rw [Real.sin_neg] at this
      exact this.trans (neg_le_abs _)
  have h4 : 4 * |(t : ℝ)| ≤ (m : ℝ) * ‖ZMod.stdAddChar a - 1‖ := by
    rw [e2]
    calc 4 * |(t : ℝ)| = (m : ℝ) * (2 * (2 / π * |y|)) := by
          rw [hyabs]; field_simp; ring
      _ ≤ (m : ℝ) * (2 * |Real.sin y|) := by gcongr
  have h5 : 16 * (t : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 * ‖ZMod.stdAddChar a - 1‖ ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) h4 2
    rw [mul_pow, sq_abs, mul_pow] at this
    linarith
  rw [e1] at h5
  linarith

theorem sixteen_mul_sum_sq_le (ℓ : Grid d m) :
    16 * ∑ j, ((signedRep ℓ j : ℤ) : ℝ) ^ 2 ≤ 2 * (m : ℝ) ^ 2 * wilsonScalar (angle ℓ) := by
  rw [mul_sum, wilsonScalar, mul_sum]
  exact sum_le_sum fun j _ => sixteen_mul_sq_le (ℓ j)

theorem sobWeight_signedRep_le (ℓ : Grid d m) :
    sobWeight (signedRep ℓ) ≤ 1 + 2 * (m : ℝ) ^ 2 * wilsonScalar (angle ℓ) := by
  have h := sixteen_mul_sum_sq_le ℓ
  have h0 : 0 ≤ ∑ j, ((signedRep ℓ j : ℤ) : ℝ) ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  unfold sobWeight
  linarith

/-- The reconstruction error constant `ε_h = π √d / (2m)`. -/
def reconError (d m : ℕ) : ℝ := π * Real.sqrt d / (2 * m)

/-- **(A1), the reconstruction error**: `‖I_h u - 𝒥⁰_h u‖ ≤ ε_h ‖u‖_{1,h}`. -/
theorem norm_interp_sub_embed_le (v : Stage d K m) :
    ‖interp v - embed d K m v‖ ≤ reconError d m * discreteNorm d K m v := by
  have hm := n_pos (n := m)
  have hsq : ‖interp v - embed d K m v‖ ^ 2 ≤ (reconError d m * discreteNorm d K m v) ^ 2 := by
    rw [norm_sq_interp_sub_embed, mul_pow, discreteNorm_sq, mul_sum]
    refine sum_le_sum fun ℓ _ => ?_
    have hw := norm_modeError_le (n := m) ℓ
    have hcs : (∑ i, |((signedRep ℓ i : ℤ) : ℝ)|) ^ 2 ≤ d * ∑ i, ((signedRep ℓ i : ℤ) : ℝ) ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
        (f := fun i => |((signedRep ℓ i : ℤ) : ℝ)|)
      simpa [sq_abs] using this
    have hsym := sixteen_mul_sum_sq_le ℓ
    have hs0 : 0 ≤ wilsonScalar (angle ℓ) := wilsonScalar_nonneg _
    have hw2 : ‖modeError (n := m) ℓ‖ ^ 2 ≤ (reconError d m) ^ 2 *
        (1 + 2 * (m : ℝ) ^ 2 * wilsonScalar (angle ℓ)) := by
      have h1 : ‖modeError (n := m) ℓ‖ ^ 2 ≤
          (2 * π * (∑ i, |((signedRep ℓ i : ℤ) : ℝ)|) / m) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hw 2
      refine h1.trans ?_
      set S := ∑ i, |((signedRep ℓ i : ℤ) : ℝ)|
      have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      have hS : 16 * S ^ 2 ≤ d * (1 + 2 * (m : ℝ) ^ 2 * wilsonScalar (angle ℓ)) := by
        have h2 : 16 * S ^ 2 ≤ d * (16 * ∑ i, ((signedRep ℓ i : ℤ) : ℝ) ^ 2) := by nlinarith
        nlinarith
      calc (2 * π * S / m) ^ 2 = π ^ 2 / (4 * (m : ℝ) ^ 2) * (16 * S ^ 2) := by
            field_simp; ring
        _ ≤ π ^ 2 / (4 * (m : ℝ) ^ 2) * (d * (1 + 2 * (m : ℝ) ^ 2 * wilsonScalar (angle ℓ))) := by
            gcongr
        _ = (reconError d m) ^ 2 * (1 + 2 * (m : ℝ) ^ 2 * wilsonScalar (angle ℓ)) := by
            rw [reconError, div_pow, mul_pow, mul_pow, Real.sq_sqrt hd]
            field_simp
            ring
    calc ‖coef v ℓ‖ ^ 2 * ‖modeError (n := m) ℓ‖ ^ 2
        ≤ ‖coef v ℓ‖ ^ 2 * ((reconError d m) ^ 2 *
          (1 + 2 * (m : ℝ) ^ 2 * wilsonScalar (angle ℓ))) :=
          mul_le_mul_of_nonneg_left hw2 (sq_nonneg _)
      _ = _ := by ring
  have h0 : 0 ≤ reconError d m * discreteNorm d K m v :=
    mul_nonneg (by unfold reconError; positivity) (discreteNorm_nonneg v)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) h0 two_ne_zero).1 hsq

theorem tendsto_reconError : Tendsto (fun n : ℕ => reconError d (n + 1)) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (π * Real.sqrt d / 2)
  rw [mul_zero] at h
  refine h.congr fun n => ?_
  rw [reconError]
  push_cast
  field_simp

end reconstruction

/-! ### The reconstruction into `H¹` -/

section sobolevReconstruction

variable {c : Fin d → Matrix (Fin K) (Fin K) ℂ} (hc : ∀ j, (c j)ᴴ = c j)
variable {m : ℕ} [NeZero m]

/-- The index of the eigenmode `(ℓ̃, i)`. -/
def recIdx (p : Grid d m × Fin K) : Idx d K := (signedRep p.1, p.2)

theorem recIdx_injective : Function.Injective (recIdx (d := d) (K := K) (m := m)) := by
  rintro ⟨ℓ, i⟩ ⟨ℓ', i'⟩ h
  simp only [recIdx, Prod.mk.injEq] at h
  have := congrArg (zcast m) h.1
  rw [zcast_signedRep, zcast_signedRep] at this
  rw [this, h.2]

/-- The `H¹` coordinates `(1 + |ℓ̃|²)^{1/2} ⟪u_i(ℓ̃), û(ℓ)⟫` of the reconstruction. -/
def recCoef (v : Stage d K m) (p : Grid d m × Fin K) : ℂ :=
  ((Real.sqrt (sobWeight (signedRep p.1)) : ℝ) : ℂ) * ⟪evec hc (signedRep p.1) p.2, coef v p.1⟫_ℂ

theorem orthonormal_single_recIdx :
    Orthonormal ℂ fun p : Grid d m × Fin K =>
      (lp.single (E := fun _ : Idx d K => ℂ) 2 (recIdx p) (1 : ℂ)) := by
  classical
  have h0 : Orthonormal ℂ fun q : Idx d K =>
      (lp.single (E := fun _ : Idx d K => ℂ) 2 q (1 : ℂ)) := by
    rw [orthonormal_iff_ite]
    intro p q
    rw [lp.inner_single_left, lp.single_apply, Pi.single_apply]
    by_cases h : p = q
    · subst h; simp
    · simp [h]
  exact h0.comp _ recIdx_injective

/-- **The reconstruction `I_h : ℓ²((ℤ/m)ᵈ; ℂ^K) → H¹`** (trigonometric interpolation, in the
`H¹` coordinates). -/
def recLin (d K m : ℕ) [NeZero m] {c : Fin d → Matrix (Fin K) (Fin K) ℂ}
    (hc : ∀ j, (c j)ᴴ = c j) : Stage d K m →ₗ[ℂ] ℓ²(Idx d K, ℂ) where
  toFun v := ∑ p, recCoef hc v p • lp.single (E := fun _ : Idx d K => ℂ) 2 (recIdx p) (1 : ℂ)
  map_add' v w := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun p _ => ?_
    rw [← add_smul, recCoef, recCoef, recCoef, coef_add, inner_add_right, mul_add]
  map_smul' b v := by
    rw [smul_sum]
    refine sum_congr rfl fun p _ => ?_
    rw [smul_smul, recCoef, recCoef, coef_smul, inner_smul_right, RingHom.id_apply]
    ring_nf

theorem recLin_apply (v : Stage d K m) :
    recLin d K m hc v =
      ∑ p, recCoef hc v p • lp.single (E := fun _ : Idx d K => ℂ) 2 (recIdx p) (1 : ℂ) := rfl

theorem norm_sq_recLin (v : Stage d K m) :
    ‖recLin d K m hc v‖ ^ 2 = ∑ ℓ, sobWeight (signedRep ℓ) * ‖coef v ℓ‖ ^ 2 := by
  have h := (orthonormal_single_recIdx (d := d) (K := K) (m := m)).inner_sum
    (recCoef hc v) (recCoef hc v) Finset.univ
  have hre : ‖recLin d K m hc v‖ ^ 2 = ∑ p, ‖recCoef hc v p‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
    rw [recLin_apply, h, map_sum]
    refine sum_congr rfl fun p _ => ?_
    rw [RCLike.conj_mul]
    norm_cast
  rw [hre, Fintype.sum_prod_type]
  refine sum_congr rfl fun ℓ _ => ?_
  simp only [recCoef, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (sobWeight_pos _).le, ← mul_sum]
  congr 1
  have hb := (symbol_isHermitian hc (signedRep ℓ)).eigenvectorBasis
  rw [← (symbol_isHermitian hc (signedRep ℓ)).eigenvectorBasis.repr.norm_map (coef v ℓ),
    EuclideanSpace.norm_sq_eq]
  refine sum_congr rfl fun i _ => ?_
  rw [OrthonormalBasis.repr_apply_apply]
  rfl

theorem norm_recLin_le (v : Stage d K m) : ‖recLin d K m hc v‖ ≤ 1 * discreteNorm d K m v := by
  have hsq : ‖recLin d K m hc v‖ ^ 2 ≤ discreteNorm d K m v ^ 2 := by
    rw [norm_sq_recLin, discreteNorm_sq]
    exact sum_le_sum fun ℓ _ =>
      mul_le_mul_of_nonneg_right (sobWeight_signedRep_le ℓ) (sq_nonneg _)
  rw [one_mul]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (discreteNorm_nonneg v) two_ne_zero).1 hsq

theorem mulCLM_single (q : Idx d K) (b : ℂ) :
    HilbertBasisDiagonal.mulCLM sobMult norm_sobMult_le
      (lp.single (E := fun _ : Idx d K => ℂ) 2 q b) =
      lp.single (E := fun _ : Idx d K => ℂ) 2 q (sobMult q * b) := by
  classical
  ext p
  rw [HilbertBasisDiagonal.mulCLM_apply, lp.single_apply, lp.single_apply, Pi.single_apply,
    Pi.single_apply]
  split_ifs with h
  · subst h; rfl
  · simp

/-- `I_h u` is the trigonometric reconstruction: `sobolev (I_h u) = Σ_ℓ e^{2πiℓ̃·x} û(ℓ)`. -/
theorem sobolev_recLin (v : Stage d K m) : sobolev hc (recLin d K m hc v) = interp v := by
  classical
  rw [recLin_apply, map_sum]
  have hterm : ∀ p : Grid d m × Fin K,
      sobolev hc (recCoef hc v p • lp.single 2 (recIdx p) (1 : ℂ)) =
        ⟪evec hc (signedRep p.1) p.2, coef v p.1⟫_ℂ • eigVec hc (recIdx p) := by
    intro p
    rw [map_smul, sobolev, ContinuousLinearMap.comp_apply, mulCLM_single, mul_one]
    simp only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
    rw [show (lp.single 2 (recIdx p) (sobMult (recIdx p)) : ℓ²(Idx d K, ℂ)) =
      sobMult (recIdx p) • lp.single 2 (recIdx p) (1 : ℂ) by
        rw [← lp.single_smul, smul_eq_mul, mul_one]]
    rw [map_smul, HilbertBasis.repr_symm_single, eigBasis_apply, smul_smul, recCoef, sobMult]
    congr 1
    simp only [recIdx]
    have hs := Real.sqrt_pos.2 (sobWeight_pos (signedRep p.1))
    have hs' : ((Real.sqrt (sobWeight (signedRep p.1)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    push_cast
    field_simp
  simp_rw [hterm]
  rw [Fintype.sum_prod_type, interp]
  refine sum_congr rfl fun ℓ _ => ?_
  rw [modeVec_eq_sum hc]
  rfl

end sobolevReconstruction

/-! ### Lattice plane waves and the consistency condition (A3) -/

section consistency

open FrozenWilsonGarding VariableWilsonGarding FrozenWilsonSymbol

variable {m : ℕ} [NeZero m]

theorem sum_conj_latticeChar_mul (ℓ ℓ₀ : Grid d m) :
    ∑ x, conj (latticeChar ℓ x) * latticeChar ℓ₀ x = if ℓ = ℓ₀ then (m : ℂ) ^ d else 0 := by
  have h : ∀ x : Grid d m, conj (latticeChar ℓ x) * latticeChar ℓ₀ x =
      latticeChar (ℓ₀ - ℓ) x := by
    intro x
    rw [latticeChar_comm (ℓ₀ - ℓ) x, latticeChar_sub_right, latticeChar_comm x ℓ₀,
      latticeChar_comm x ℓ, mul_comm]
  simp_rw [h]
  have hs : ∑ x : Grid d m, latticeChar (ℓ₀ - ℓ) x = ∑ x : Grid d m, latticeChar x (ℓ₀ - ℓ) :=
    sum_congr rfl fun x _ => latticeChar_comm _ _
  rw [hs, sum_latticeChar]
  by_cases hl : ℓ = ℓ₀
  · rw [ite_eq_left (by rw [hl, sub_self]), ite_eq_left hl]
  · rw [ite_eq_right (fun e => hl (sub_eq_zero.1 e).symm), ite_eq_right hl]

/-- The DFT of a lattice plane wave is a Kronecker delta. -/
theorem dftVec_planeWave (ℓ₀ : Grid d m) (w : Fin K → ℂ) (ℓ : Grid d m) :
    dftVec (fun x => latticeChar ℓ₀ x • w) ℓ = if ℓ = ℓ₀ then w else 0 := by
  have hn : ((m : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne m))
  funext a
  simp only [dftVec, dft, Pi.smul_apply, smul_eq_mul]
  have : ∑ x : Grid d m, conj (latticeChar ℓ x) * (latticeChar ℓ₀ x * w a) =
      (∑ x, conj (latticeChar ℓ x) * latticeChar ℓ₀ x) * w a := by
    rw [sum_mul]; exact sum_congr rfl fun x _ => by ring
  rw [this, sum_conj_latticeChar_mul]
  split_ifs with h
  · rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  · simp

/-- **The lattice operator on a plane wave of the torus** acts by the frozen symbol. -/
theorem frozenWilson_planeWave_torus (h ϖ : ℝ) (hh : h ≠ 0)
    (c : Fin d → Matrix (Fin K) (Fin K) ℂ) (Γ : Matrix (Fin K) (Fin K) ℂ)
    (ℓ₀ : Grid d m) (w : Fin K → ℂ) :
    frozenWilson h ϖ c Γ (fun x => latticeChar ℓ₀ x • w) =
      fun x => latticeChar ℓ₀ x • (frozenSymbol h ϖ c Γ (angle ℓ₀) *ᵥ w) := by
  refine eq_of_dftVec_eq fun ℓ => ?_
  rw [dftVec_frozenWilson h ϖ hh, dftVec_planeWave, dftVec_planeWave]
  split_ifs with hl
  · subst hl; rfl
  · exact mulVec_zero _

/-- The stage plane wave `(x, a) ↦ w_a · m^{-d/2} e^{2πi k·x/m}`. -/
def stageWave (m : ℕ) [NeZero m] (k : Fin d → ℤ) (w : Fiber K) : Stage d K m :=
  WithLp.toLp 2 fun p => w p.2 * modeSample m k p.1

theorem toSec_stageWave (k : Fin d → ℤ) (w : Fiber K) :
    toSec (stageWave m k w) =
      ((scale m d : ℝ) : ℂ)⁻¹ • fun x => latticeChar (zcast m k) x • (w : Fin K → ℂ) := by
  funext x a
  simp only [toSec, stageWave, PiLp.toLp_apply, modeSample_apply, Pi.smul_apply, smul_eq_mul]
  change w a * (_ * _) = _
  ring

theorem stage_stageWave (ϖ : ℝ) (c : Fin d → Matrix (Fin K) (Fin K) ℂ)
    (Γ : Matrix (Fin K) (Fin K) ℂ) (k : Fin d → ℤ) (w : Fiber K) :
    stage d K m ϖ c Γ (stageWave m k w) =
      stageWave m k (WithLp.toLp 2
        (frozenSymbol (m : ℝ)⁻¹ ϖ c Γ (angle (zcast m k)) *ᵥ (w : Fin K → ℂ))) := by
  rw [stage_apply, toSec_stageWave, frozenWilson_smul _ _ _ _ inv_mesh_ne_zero,
    frozenWilson_planeWave_torus _ _ inv_mesh_ne_zero]
  ext p
  simp only [eucl, stageWave, PiLp.toLp_apply, Pi.smul_apply, smul_eq_mul, modeSample_apply]
  change _ * (latticeChar (zcast m k) p.1 * _) = _ * (_ * _)
  ring

theorem comp_stageWave (k : Fin d → ℤ) (w : Fiber K) (a : Fin K) :
    comp (stageWave m k w) a = w a • modeSample m k := by
  ext x
  rfl

theorem embed_stageWave (k : Fin d → ℤ) (w : Fiber K) :
    embed d K m (stageWave m k w) =
      WithLp.toLp 2 fun a => w a • pcEmbedding d m (modeSample m k) := by
  ext1 a
  rw [embed_apply, comp_stageWave, LinearIsometry.map_smul]

/-- **The samples `S_h = (𝒥⁰_h)^*` of a plane wave are a lattice plane wave**:
`(𝒥⁰_h)^* (e^{2πik·x} v) = γ_h(k) · stageWave k v`. -/
theorem embed_adjoint_modeVec (k : Fin d → ℤ) (v : Fiber K) :
    ContinuousLinearMap.adjoint (embed d K m).toContinuousLinearMap (modeVec k v) =
      modeFactor m k • stageWave m k v := by
  rw [embed_adjoint_apply]
  ext p
  simp only [PiLp.smul_apply, smul_eq_mul, stageWave, modeVec_apply, map_smul,
    pcEmbedding_adjoint_mode]
  change v p.2 * (modeFactor m k * modeSample m k p.1) = _
  ring

/-! ### The symbol limit -/

theorem tendsto_mul_sin_div (a : ℝ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) * Real.sin (a / ((n : ℝ) + 1))) atTop (𝓝 a) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : Tendsto (fun n : ℕ => |a| ^ 3 * (1 / ((n : ℝ) + 1))) atTop (𝓝 (|a| ^ 3 * 0)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.const_mul _
  rw [mul_zero] at hb
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hb
  have hev : ∀ᶠ n : ℕ in atTop, |a| ≤ (n : ℝ) + 1 := by
    obtain ⟨N, hN⟩ := exists_nat_ge |a|
    exact eventually_atTop.2 ⟨N, fun n hn => hN.trans (by exact_mod_cast Nat.le_succ_of_le hn)⟩
  filter_upwards [hev] with n hn
  have hM : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set x := a / ((n : ℝ) + 1)
  have hx : |x| ≤ 1 := by
    rw [abs_div, abs_of_pos hM, div_le_one hM]; exact hn
  have hsb := Real.sin_bound hx
  have hx3 : |x ^ 3 / 6| ≤ |x| ^ 3 / 6 := by rw [abs_div, abs_pow]; norm_num
  have hx5 : |x| ^ 5 ≤ |x| ^ 3 := pow_le_pow_of_le_one (abs_nonneg _) hx (by norm_num)
  have hsx : |Real.sin x - x| ≤ |x| ^ 3 := by
    have : Real.sin x - x = (Real.sin x - (x - x ^ 3 / 6)) - x ^ 3 / 6 := by ring
    rw [this]
    refine (abs_sub _ _).trans ?_
    have : 0 ≤ |x| ^ 3 := by positivity
    linarith
  rw [Real.norm_eq_abs]
  have e : ((n : ℝ) + 1) * Real.sin x - a = ((n : ℝ) + 1) * (Real.sin x - x) := by
    simp only [x]; field_simp
  rw [e, abs_mul, abs_of_pos hM]
  calc ((n : ℝ) + 1) * |Real.sin x - x| ≤ ((n : ℝ) + 1) * |x| ^ 3 := by gcongr
    _ = |a| ^ 3 / ((n : ℝ) + 1) ^ 2 := by
        simp only [x]; rw [abs_div, abs_of_pos hM]; field_simp
    _ ≤ |a| ^ 3 * (1 / ((n : ℝ) + 1)) := by
        rw [div_le_iff₀ (by positivity)]
        have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
        field_simp
        nlinarith [pow_nonneg (abs_nonneg a) 3]

theorem tendsto_mul_one_sub_cos_div (a : ℝ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) * (1 - Real.cos (a / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
  have hb : Tendsto (fun n : ℕ => a ^ 2 / 2 * (1 / ((n : ℝ) + 1))) atTop (𝓝 (a ^ 2 / 2 * 0)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.const_mul _
  rw [mul_zero] at hb
  refine squeeze_zero (fun n => mul_nonneg (by positivity)
    (sub_nonneg.2 (Real.cos_le_one _))) (fun n => ?_) hb
  have hM : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h := Real.one_sub_sq_div_two_le_cos (x := a / ((n : ℝ) + 1))
  calc ((n : ℝ) + 1) * (1 - Real.cos (a / ((n : ℝ) + 1)))
      ≤ ((n : ℝ) + 1) * ((a / ((n : ℝ) + 1)) ^ 2 / 2) := by gcongr; linarith
    _ = a ^ 2 / 2 * (1 / ((n : ℝ) + 1)) := by field_simp

theorem angle_zcast_eq (k : Fin d → ℤ) (j : Fin d) :
    ∃ t : ℤ, angle (zcast m k) j = 2 * π * (k j : ℝ) / m - t * (2 * π) := by
  refine ⟨k j / (m : ℤ), ?_⟩
  have hm := n_pos (n := m)
  have hv : (((k j : ZMod m)).val : ℤ) = k j - m * (k j / (m : ℤ)) := by
    rw [ZMod.val_intCast, Int.emod_def]
  have hv' : (((k j : ZMod m)).val : ℝ) = (k j : ℝ) - m * ((k j / (m : ℤ) : ℤ) : ℝ) := by
    exact_mod_cast hv
  simp only [angle, zcast]
  rw [hv']
  field_simp

theorem sin_angle_zcast (k : Fin d → ℤ) (j : Fin d) :
    Real.sin (angle (zcast m k) j) = Real.sin (2 * π * (k j : ℝ) / m) := by
  obtain ⟨t, ht⟩ := angle_zcast_eq (m := m) k j
  rw [ht, Real.sin_sub_int_mul_two_pi]

theorem cos_angle_zcast (k : Fin d → ℤ) (j : Fin d) :
    Real.cos (angle (zcast m k) j) = Real.cos (2 * π * (k j : ℝ) / m) := by
  obtain ⟨t, ht⟩ := angle_zcast_eq (m := m) k j
  rw [ht, Real.cos_sub_int_mul_two_pi]

theorem frozenSymbol_zcast_eq (ϖ : ℝ) (c : Fin d → Matrix (Fin K) (Fin K) ℂ)
    (Γ : Matrix (Fin K) (Fin K) ℂ) (k : Fin d → ℤ) :
    frozenSymbol (m : ℝ)⁻¹ ϖ c Γ (angle (zcast m k)) =
      ∑ j, (((m : ℝ) * Real.sin (2 * π * (k j : ℝ) / m) : ℝ) : ℂ) • c j +
        ((ϖ * ∑ j, (m : ℝ) * (1 - Real.cos (2 * π * (k j : ℝ) / m)) : ℝ) : ℂ) • Γ := by
  unfold frozenSymbol wilsonScalar
  simp only [sin_angle_zcast, cos_angle_zcast, smul_add, Finset.smul_sum, smul_smul]
  congr 1
  · refine sum_congr rfl fun j _ => ?_
    congr 1
    push_cast
    simp only [inv_inv]
  · congr 1
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine sum_congr rfl fun j _ => ?_
    simp only [inv_inv]
    ring

/-- **The frozen symbol converges to the continuum symbol**:
`q_h(2πk h) → Σ_j 2πk_j ĉ^j` as `h → 0` (the Wilson term is `O(h)` on each fixed mode). -/
theorem tendsto_frozenSymbol (ϖ : ℝ) (c : Fin d → Matrix (Fin K) (Fin K) ℂ)
    (Γ : Matrix (Fin K) (Fin K) ℂ) (k : Fin d → ℤ) :
    Tendsto (fun n : ℕ => frozenSymbol ((n + 1 : ℕ) : ℝ)⁻¹ ϖ c Γ (angle (zcast (n + 1) k)))
      atTop (𝓝 (symbol c k)) := by
  simp_rw [frozenSymbol_zcast_eq]
  have hlim : symbol c k = ∑ j, (((2 * π * (k j : ℝ)) : ℝ) : ℂ) • c j +
      ((ϖ * ∑ _j : Fin d, (0 : ℝ) : ℝ) : ℂ) • Γ := by
    simp [symbol]
  rw [hlim]
  refine Tendsto.add (tendsto_finsetSum _ fun j _ => ?_) ?_
  · refine Tendsto.smul_const ?_ _
    refine (Complex.continuous_ofReal.tendsto _).comp ?_
    have := tendsto_mul_sin_div (2 * π * (k j : ℝ))
    refine this.congr fun n => ?_
    push_cast
    ring_nf
  · refine Tendsto.smul_const ?_ _
    refine (Complex.continuous_ofReal.tendsto _).comp ?_
    refine Tendsto.const_mul _ (tendsto_finsetSum _ fun j _ => ?_)
    have := tendsto_mul_one_sub_cos_div (2 * π * (k j : ℝ))
    refine this.congr fun n => ?_
    push_cast
    ring_nf

theorem tendsto_mulVec_apply {A : ℕ → Matrix (Fin K) (Fin K) ℂ} {B : Matrix (Fin K) (Fin K) ℂ}
    (hA : Tendsto A atTop (𝓝 B)) (w : Fin K → ℂ) (a : Fin K) :
    Tendsto (fun n => (A n *ᵥ w) a) atTop (𝓝 ((B *ᵥ w) a)) := by
  simp only [mulVec, dotProduct]
  refine tendsto_finsetSum _ fun b _ => Tendsto.mul_const _ ?_
  have h1 := (continuous_apply a).tendsto B |>.comp hA
  exact ((continuous_apply b).tendsto (B a)).comp h1

variable (ϖ : ℝ) (c : Fin d → Matrix (Fin K) (Fin K) ℂ) (Γ : Matrix (Fin K) (Fin K) ℂ)

/-- **(A3) on a plane wave**: `𝒥⁰_h D_h (𝒥⁰_h)^* (e^{2πik·x} v) → e^{2πik·x} σ(k) v`. -/
theorem tendsto_embed_stage_adjoint_modeVec (k : Fin d → ℤ) (v : Fiber K) :
    Tendsto (fun n : ℕ => embed d K (n + 1) (stage d K (n + 1) ϖ c Γ
      (ContinuousLinearMap.adjoint (embed d K (n + 1)).toContinuousLinearMap (modeVec k v))))
      atTop (𝓝 (modeVec k (WithLp.toLp 2 (symbol c k *ᵥ (v : Fin K → ℂ))))) := by
  refine tendsto_spinor fun a => ?_
  have e : ∀ n : ℕ, embed d K (n + 1) (stage d K (n + 1) ϖ c Γ
      (ContinuousLinearMap.adjoint (embed d K (n + 1)).toContinuousLinearMap (modeVec k v))) a =
      (modeFactor (n + 1) k * (frozenSymbol ((n + 1 : ℕ) : ℝ)⁻¹ ϖ c Γ
        (angle (zcast (n + 1) k)) *ᵥ (v : Fin K → ℂ)) a) •
          pcEmbedding d (n + 1) (modeSample (n + 1) k) := by
    intro n
    rw [embed_adjoint_modeVec, map_smul, stage_stageWave, LinearIsometry.map_smul,
      embed_stageWave, PiLp.smul_apply, PiLp.toLp_apply, smul_smul]
  simp_rw [e]
  rw [modeVec_apply]
  have h1 := tendsto_modeFactor (d := d) k
  have h2 := tendsto_mulVec_apply (tendsto_frozenSymbol ϖ c Γ k) (v : Fin K → ℂ) a
  have h3 := tendsto_pcEmbedding_mode (d := d) k
  have := (h1.mul h2).smul h3
  rw [one_mul] at this
  exact this

end consistency

/-! ### (A3) on the whole core -/

section coreConsistency

variable {c : Fin d → Matrix (Fin K) (Fin K) ℂ} (hc : ∀ j, (c j)ᴴ = c j)
variable (ϖ : ℝ) (Γ : Matrix (Fin K) (Fin K) ℂ)

/-- **(A3)**: for every trigonometric polynomial `ψ`,
`𝒥⁰_h D_h (𝒥⁰_h)^* ψ → D̂ ψ`. -/
theorem tendsto_embed_stage_adjoint_core (ψ : SpinorL2 d K) (hψ : ψ ∈ trigCore hc) :
    Tendsto (fun n : ℕ => embed d K (n + 1) (stage d K (n + 1) ϖ c Γ
      (ContinuousLinearMap.adjoint (embed d K (n + 1)).toContinuousLinearMap ψ))) atTop
      (𝓝 ((dirac hc).op ⟨ψ, trigCore_le_domain hc hψ⟩)) := by
  induction hψ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨k, i⟩, rfl⟩ := hx
    have he : eigBasis hc (k, i) = modeVec k (evec hc k i) := eigBasis_apply hc _
    have hval : (⟨eigBasis hc (k, i), trigCore_le_domain hc (Submodule.subset_span ⟨(k, i), rfl⟩)⟩ :
        (dirac hc).op.domain) =
        ⟨modeVec k (evec hc k i), trigCore_le_domain hc (modeVec_mem_trigCore hc k _)⟩ :=
      Subtype.ext he
    rw [hval, dirac_modeVec, he]
    exact tendsto_embed_stage_adjoint_modeVec ϖ c Γ k _
  | zero =>
    have h0 : (⟨0, trigCore_le_domain hc (Submodule.zero_mem _)⟩ : (dirac hc).op.domain) = 0 :=
      rfl
    rw [h0, LinearPMap.map_zero]
    simp
  | add x y hx hy ihx ihy =>
    have hxy : (⟨x + y, trigCore_le_domain hc (Submodule.add_mem _ hx hy)⟩ :
        (dirac hc).op.domain) =
        ⟨x, trigCore_le_domain hc hx⟩ + ⟨y, trigCore_le_domain hc hy⟩ := rfl
    rw [hxy, LinearPMap.map_add]
    simpa only [map_add] using ihx.add ihy
  | smul a x hx ihx =>
    have hax : (⟨a • x, trigCore_le_domain hc (Submodule.smul_mem _ a hx)⟩ :
        (dirac hc).op.domain) = a • ⟨x, trigCore_le_domain hc hx⟩ := rfl
    rw [hax, LinearPMap.map_smul]
    simpa only [map_smul] using ihx.const_smul a

end coreConsistency

/-! ### The atlas -/

section atlas

open FrozenWilsonGarding FrozenWilsonSymbol

/-- The input data of `cor:supp-flat-torus-spin` in doubled form: Hermitian doubled Clifford
coefficients `ĉ^j` and normal generator `Γ_⊥` for a constant inverse metric `g` with
ellipticity constants `0 < λ ≤ Λ`, and a Wilson parameter `ϖ ≠ 0`.  (These are hypotheses on
the input data only; `ofUndoubled` builds them from undoubled Clifford data and a positive
definite metric.) -/
structure DoubledFlatData (d K : ℕ) where
  /-- The doubled Clifford coefficients `ĉ^j`. -/
  c : Fin d → Matrix (Fin K) (Fin K) ℂ
  /-- The normal generator `Γ_⊥`. -/
  Γ : Matrix (Fin K) (Fin K) ℂ
  /-- The constant inverse metric `g^{jk}`. -/
  g : Matrix (Fin d) (Fin d) ℝ
  /-- The Wilson parameter. -/
  ϖ : ℝ
  lam : ℝ
  Lam : ℝ
  herm : ∀ j, (c j)ᴴ = c j
  normal_herm : Γᴴ = Γ
  clifford : DoubledCliffordData c Γ g
  lam_pos : 0 < lam
  Lam_nonneg : 0 ≤ Lam
  wilson_ne : ϖ ≠ 0
  low : ∀ ξ : Fin d → ℝ, lam * ∑ j, ξ j ^ 2 ≤ ∑ j, ∑ k, g j k * (ξ j * ξ k)
  up : ∀ ξ : Fin d → ℝ, ∑ j, ∑ k, g j k * (ξ j * ξ k) ≤ Lam * ∑ j, ξ j ^ 2

variable (D : DoubledFlatData d K)

/-- **The flat periodic spin torus is a compatible stable atlas** (`def:stable-spin-atlas`):
`ℋ = L²(𝕋ᵈ; ℂ^K)`, `D̂ = Σ_j ĉ^j (-i∂_j)`, smooth core = trigonometric polynomials,
`V = H¹` with the compact Rellich embedding, `ℋ_h = ℓ²((ℤ/(n+1))ᵈ; ℂ^K)`, `D_h` = the
doubled Wilson operator `eq:supp-general-Wilson` with constant coefficients and trivial
transport, `W_h = 𝒥⁰_h`, `I_h` the trigonometric reconstruction, `S_h = (𝒥⁰_h)^*`.  Every
field is derived. -/
def atlas : CompatibleStableAtlas (SpinorL2 d K) ℓ²(Idx d K, ℂ) (fun n => Stage d K (n + 1)) where
  limit := dirac D.herm
  core := trigCore D.herm
  core_le := trigCore_le_domain D.herm
  core_dense := HilbertBasisDiagonal.core_dense (eigBasis D.herm) (evalIdx D.herm)
  sobolev := sobolev D.herm
  sobolev_compact := isCompactOperator_sobolev D.herm
  embed n := embed d K (n + 1)
  stage n := stage d K (n + 1) D.ϖ D.c D.Γ
  stage_selfAdjoint n := isSelfAdjoint_stage D.ϖ D.c D.Γ D.herm D.normal_herm
  embed_adjoint_tendsto := tendsto_embed_adjoint
  discreteNorm n := discreteNorm d K (n + 1)
  discreteNorm_nonneg n u := discreteNorm_nonneg u
  reconstruct n := recLin d K (n + 1) D.herm
  reconstructConst := 1
  reconstructConst_nonneg := zero_le_one
  norm_reconstruct_le n u := norm_recLin_le D.herm u
  reconstructError n := reconError d (n + 1)
  reconstructError_nonneg n := by unfold reconError; positivity
  reconstructError_tendsto := tendsto_reconError
  norm_sobolev_reconstruct_sub_embed_le n u := by
    rw [sobolev_recLin]
    exact norm_interp_sub_embed_le u
  graphConst := Real.sqrt (max 1 (min D.lam (D.ϖ ^ 2))⁻¹)
  graphConst_nonneg := Real.sqrt_nonneg _
  discreteNorm_le n u := discreteNorm_le D.ϖ D.c D.Γ D.lam D.Lam D.lam_pos D.wilson_ne
    D.Lam_nonneg D.g D.clifford D.herm D.normal_herm D.low D.up u
  sample n ψ := ContinuousLinearMap.adjoint (embed d K (n + 1)).toContinuousLinearMap ψ
  embed_sample_tendsto ψ := tendsto_embed_adjoint (ψ : SpinorL2 d K)
  embed_stage_sample_tendsto ψ :=
    tendsto_embed_stage_adjoint_core D.herm D.ϖ D.Γ (ψ : SpinorL2 d K) ψ.2

/-- **`cor:supp-flat-torus-spin`, eq:supp-flat-torus-resolvent** (doubled-data form):
`‖𝒥⁰_h (D^W_{g,h} - z)⁻¹ (𝒥⁰_h)^* - (D̂ - z)⁻¹‖ → 0` for every non-real `z`, where
`(D^W_{g,h} - z)⁻¹ = Ring.inverse (D^W_{g,h} - z)`. -/
theorem flatTorus_norm_resolvent {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun n : ℕ =>
      ‖(embed d K (n + 1)).toContinuousLinearMap ∘L
          Ring.inverse (stage d K (n + 1) D.ϖ D.c D.Γ - z • (1 : Stage d K (n + 1) →L[ℂ] _)) ∘L
          ContinuousLinearMap.adjoint (embed d K (n + 1)).toContinuousLinearMap -
        (dirac D.herm).resolvent z hz‖) atTop (𝓝 0) :=
  (atlas D).tendsto_norm_embeddedResolvent_sub hz

end atlas

/-! ### From undoubled Clifford data and a positive definite metric -/

section undoubled

open FrozenWilsonSymbol CovariantWilsonGarding

theorem quadForm_eq (g : Matrix (Fin d) (Fin d) ℝ) (ξ : Fin d → ℝ) :
    ∑ j, ∑ k, g j k * (ξ j * ξ k) = star ξ ⬝ᵥ (g *ᵥ ξ) := by
  simp only [dotProduct, mulVec, Pi.star_apply, star_trivial, Finset.mul_sum]
  refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  ring

/-- A positive definite matrix is uniformly elliptic. -/
theorem exists_lower_bound_of_posDef (g : Matrix (Fin d) (Fin d) ℝ) (hg : g.PosDef) :
    ∃ lam > 0, ∀ ξ : Fin d → ℝ, lam * ∑ j, ξ j ^ 2 ≤ ∑ j, ∑ k, g j k * (ξ j * ξ k) := by
  set Q : (Fin d → ℝ) → ℝ := fun ξ => ∑ j, ∑ k, g j k * (ξ j * ξ k) with hQ
  have hQc : Continuous Q := by
    simp only [hQ]; fun_prop
  set S : Set (Fin d → ℝ) := {ξ | ∑ j, ξ j ^ 2 = 1}
  rcases isEmpty_or_nonempty (Fin d) with hd | hd
  · refine ⟨1, one_pos, fun ξ => ?_⟩
    simp
  have hSc : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact isClosed_eq (by fun_prop) continuous_const
    · refine (Metric.isBounded_closedBall (x := (0 : Fin d → ℝ)) (r := 1)).subset ?_
      intro ξ hξ
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
      intro j
      have hj : ξ j ^ 2 ≤ ∑ i, ξ i ^ 2 :=
        single_le_sum (f := fun i => ξ i ^ 2) (fun _ _ => sq_nonneg _) (mem_univ j)
      rw [hξ] at hj
      rw [Real.norm_eq_abs]
      nlinarith [abs_nonneg (ξ j), sq_abs (ξ j)]
  obtain ⟨j0⟩ := hd
  have hSne : S.Nonempty := ⟨Pi.single j0 1, by simp [S, Pi.single_apply]⟩
  obtain ⟨ξ₀, hξ₀, hmin⟩ := hSc.exists_isMinOn hSne hQc.continuousOn
  have hξ₀ne : ξ₀ ≠ 0 := by
    intro h; simp [S, h] at hξ₀
  have hpos : 0 < Q ξ₀ := by
    change 0 < ∑ j, ∑ k, g j k * (ξ₀ j * ξ₀ k)
    rw [quadForm_eq]; exact hg.dotProduct_mulVec_pos hξ₀ne
  refine ⟨Q ξ₀, hpos, fun ξ => ?_⟩
  by_cases hξ : ξ = 0
  · subst hξ; simp
  set r := Real.sqrt (∑ j, ξ j ^ 2)
  have hsum : 0 < ∑ j, ξ j ^ 2 := by
    obtain ⟨j, hj⟩ : ∃ j, ξ j ≠ 0 := by
      by_contra hc; push Not at hc; exact hξ (funext hc)
    exact lt_of_lt_of_le (by positivity) (single_le_sum (f := fun i => ξ i ^ 2)
      (fun _ _ => sq_nonneg _) (mem_univ j))
  have hr : 0 < r := Real.sqrt_pos.2 hsum
  have hr2 : r ^ 2 = ∑ j, ξ j ^ 2 := Real.sq_sqrt hsum.le
  have hη : r⁻¹ • ξ ∈ S := by
    simp only [S, Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, mul_pow, ← mul_sum, inv_pow, hr2]
    exact inv_mul_cancel₀ hsum.ne'
  have h1 : Q ξ₀ ≤ Q (r⁻¹ • ξ) := hmin hη
  simp only [hQ, Pi.smul_apply, smul_eq_mul] at h1
  have h2 : ∑ j, ∑ k, g j k * (r⁻¹ * ξ j * (r⁻¹ * ξ k)) =
      (r ^ 2)⁻¹ * ∑ j, ∑ k, g j k * (ξ j * ξ k) := by
    rw [mul_sum]; refine sum_congr rfl fun j _ => ?_
    rw [mul_sum]; refine sum_congr rfl fun k _ => ?_
    field_simp
  rw [h2, hr2] at h1
  have := mul_le_mul_of_nonneg_left h1 hsum.le
  rw [← mul_assoc, mul_inv_cancel₀ hsum.ne', one_mul] at this
  simp only [hQ] at this ⊢
  linarith

theorem exists_upper_bound (g : Matrix (Fin d) (Fin d) ℝ) :
    ∃ Lam ≥ 0, ∀ ξ : Fin d → ℝ, ∑ j, ∑ k, g j k * (ξ j * ξ k) ≤ Lam * ∑ j, ξ j ^ 2 := by
  refine ⟨∑ j, ∑ k, |g j k|, by positivity, fun ξ => ?_⟩
  have hξ' : ∀ j k, |ξ j * ξ k| ≤ ∑ i, ξ i ^ 2 := by
    intro j k
    have hj := single_le_sum (f := fun i => ξ i ^ 2) (fun _ _ => sq_nonneg _) (mem_univ j)
    have hk := single_le_sum (f := fun i => ξ i ^ 2) (fun _ _ => sq_nonneg _) (mem_univ k)
    rw [abs_mul]
    nlinarith [sq_nonneg (|ξ j| - |ξ k|), sq_abs (ξ j), sq_abs (ξ k)]
  rw [sum_mul]
  refine sum_le_sum fun j _ => ?_
  rw [sum_mul]
  refine sum_le_sum fun k _ => ?_
  calc g j k * (ξ j * ξ k) ≤ |g j k| * |ξ j * ξ k| := by
        rw [← abs_mul]; exact le_abs_self _
    _ ≤ |g j k| * ∑ i, ξ i ^ 2 := mul_le_mul_of_nonneg_left (hξ' j k) (abs_nonneg _)

/-- **The doubled data of `cor:supp-flat-torus-spin` from the paper's input data**: Hermitian
Clifford coefficients `c^j` on `ℂ^M` with `c^j c^k + c^k c^j = 2 g^{jk} I` for a positive
definite constant inverse metric `g`, the fixed doubled convention `ĉ^j = c^j ⊗ σ₁`,
`Γ_⊥ = I ⊗ σ₂` (`eq:supp-doubled-clifford`), and a Wilson parameter `ϖ > 0`. -/
def ofUndoubled {M : ℕ} (c₀ : Fin d → Matrix (Fin M) (Fin M) ℂ) (g : Matrix (Fin d) (Fin d) ℝ)
    (hherm : ∀ j, (c₀ j)ᴴ = c₀ j)
    (hcl : ∀ j k, c₀ j * c₀ k + c₀ k * c₀ j =
      ((2 * g j k : ℝ) : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))
    (hg : g.PosDef) (ϖ : ℝ) (hϖ : 0 < ϖ) : DoubledFlatData d (M * 2) where
  c j := dbl (c₀ j) σ₁
  Γ := dbl 1 σ₂
  g := g
  ϖ := ϖ
  lam := (exists_lower_bound_of_posDef g hg).choose
  Lam := (exists_upper_bound g).choose
  herm j := by rw [dbl_conjTranspose, hherm, σ₁_conjTranspose]
  normal_herm := by rw [dbl_conjTranspose, Matrix.conjTranspose_one, σ₂_conjTranspose]
  clifford := doubled_cliffordData c₀ g hcl
  lam_pos := (exists_lower_bound_of_posDef g hg).choose_spec.1
  Lam_nonneg := (exists_upper_bound g).choose_spec.1
  wilson_ne := hϖ.ne'
  low := (exists_lower_bound_of_posDef g hg).choose_spec.2
  up := (exists_upper_bound g).choose_spec.2

/-- **`cor:supp-flat-torus-spin`** (unconditional periodic flat-spin norm-resolvent convergence).
Let `𝕋ᵈ = ℝᵈ/ℤᵈ` carry a constant flat metric (inverse metric `g`, positive definite) and the
periodic spin structure, with constant Hermitian Clifford coefficients `c^j`
(`c^j c^k + c^k c^j = 2 g^{jk}`), trivial spin transport, the uniform lattice `h = 1/(n+1)`,
and the doubled Wilson operator `D^W_{g,h}` of `eq:supp-general-Wilson` with `ϖ > 0`.  With the
isometric piecewise-constant embedding `𝒥⁰_h`, for every `z ∉ ℝ`,
`‖𝒥⁰_h (D^W_{g,h} - z)⁻¹ (𝒥⁰_h)^* - (D̂_M - z)⁻¹‖ → 0`, `D̂_M = Σ_j (c^j ⊗ σ₁)(-i∂_j)`. -/
theorem flatTorusSpin_norm_resolvent {M : ℕ} (c₀ : Fin d → Matrix (Fin M) (Fin M) ℂ)
    (g : Matrix (Fin d) (Fin d) ℝ) (hherm : ∀ j, (c₀ j)ᴴ = c₀ j)
    (hcl : ∀ j k, c₀ j * c₀ k + c₀ k * c₀ j =
      ((2 * g j k : ℝ) : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))
    (hg : g.PosDef) (ϖ : ℝ) (hϖ : 0 < ϖ) {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun n : ℕ =>
      ‖(embed d (M * 2) (n + 1)).toContinuousLinearMap ∘L
          Ring.inverse (stage d (M * 2) (n + 1) ϖ (fun j => dbl (c₀ j) σ₁) (dbl 1 σ₂) -
            z • (1 : Stage d (M * 2) (n + 1) →L[ℂ] _)) ∘L
          ContinuousLinearMap.adjoint (embed d (M * 2) (n + 1)).toContinuousLinearMap -
        (dirac (ofUndoubled c₀ g hherm hcl hg ϖ hϖ).herm).resolvent z hz‖) atTop (𝓝 0) :=
  flatTorus_norm_resolvent (ofUndoubled c₀ g hherm hcl hg ϖ hϖ) hz

/-- The continuum operator of `flatTorusSpin_norm_resolvent` is the doubled Dirac operator:
on `e^{2πik·x} v` it acts by `Σ_j 2πk_j (c^j ⊗ σ₁) v`. -/
theorem flatTorusSpin_dirac_modeVec {M : ℕ} (c₀ : Fin d → Matrix (Fin M) (Fin M) ℂ)
    (g : Matrix (Fin d) (Fin d) ℝ) (hherm : ∀ j, (c₀ j)ᴴ = c₀ j)
    (hcl : ∀ j k, c₀ j * c₀ k + c₀ k * c₀ j =
      ((2 * g j k : ℝ) : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))
    (hg : g.PosDef) (ϖ : ℝ) (hϖ : 0 < ϖ) (k : Fin d → ℤ) (v : Fiber (M * 2)) :
    (dirac (ofUndoubled c₀ g hherm hcl hg ϖ hϖ).herm).op
      ⟨modeVec k v, trigCore_le_domain _ (modeVec_mem_trigCore _ k v)⟩ =
      modeVec k (WithLp.toLp 2 ((∑ j, ((2 * π * k j : ℝ) : ℂ) • dbl (c₀ j) σ₁) *ᵥ
        (v : Fin (M * 2) → ℂ))) :=
  dirac_modeVec _ k v

end undoubled

/-! ### Non-vacuity: Pauli matrices on the flat two-torus -/

section nonvacuity

open CovariantWilsonGarding

/-- The Clifford coefficients `c^1 = σ₁`, `c^2 = σ₂` of the flat two-torus with `g = I`. -/
def pauliCoeff : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ := ![σ₁, σ₂]

theorem pauliCoeff_herm : ∀ j, (pauliCoeff j)ᴴ = pauliCoeff j := by
  intro j
  fin_cases j
  · exact σ₁_conjTranspose
  · exact σ₂_conjTranspose

theorem pauliCoeff_clifford : ∀ j k, pauliCoeff j * pauliCoeff k + pauliCoeff k * pauliCoeff j =
    ((2 * (1 : Matrix (Fin 2) (Fin 2) ℝ) j k : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  intro j k
  fin_cases j <;> fin_cases k
  · simp [pauliCoeff, σ₁_mul_σ₁, two_smul]
  · simp only [pauliCoeff, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Fin.mk_one,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [add_comm, σ₂_mul_σ₁_add]
    simp
  · simp only [pauliCoeff, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Fin.mk_one,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [σ₂_mul_σ₁_add]
    simp
  · simp [pauliCoeff, σ₂_mul_σ₂, two_smul]

/-- **Non-vacuity of `flatTorusSpin_norm_resolvent`**: the flat two-torus with the Pauli
Clifford coefficients, the doubled module `ℂ² ⊗ ℂ²`, `ϖ = 1` and `z = i`. -/
example : Tendsto (fun n : ℕ =>
      ‖(embed 2 (2 * 2) (n + 1)).toContinuousLinearMap ∘L
          Ring.inverse (stage 2 (2 * 2) (n + 1) 1 (fun j => dbl (pauliCoeff j) σ₁) (dbl 1 σ₂) -
            Complex.I • (1 : Stage 2 (2 * 2) (n + 1) →L[ℂ] _)) ∘L
          ContinuousLinearMap.adjoint (embed 2 (2 * 2) (n + 1)).toContinuousLinearMap -
        (dirac (ofUndoubled pauliCoeff 1 pauliCoeff_herm pauliCoeff_clifford Matrix.PosDef.one 1
          one_pos).herm).resolvent Complex.I (by simp)‖) atTop (𝓝 0) :=
  flatTorusSpin_norm_resolvent pauliCoeff 1 pauliCoeff_herm pauliCoeff_clifford
    Matrix.PosDef.one 1 one_pos (by simp)

end nonvacuity

end RenewalGeometry.FlatTorusSpinAtlas
