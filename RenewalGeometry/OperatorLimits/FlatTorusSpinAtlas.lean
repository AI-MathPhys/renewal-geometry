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
    rw [hF, if_pos rfl]
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
    simp only [if_true, true_and, evec, this]
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
      simp only [if_true, eigBasis_apply, eigVec, evalIdx, modeVec_smul]

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
  simp only [Set.mem_setOf_eq] at hk
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
  simp only [Set.mem_setOf_eq, dist_zero_right, norm_norm, not_lt] at hp
  refine ⟨?_, Set.mem_univ _⟩
  simp only [Set.mem_setOf_eq]
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

end RenewalGeometry.FlatTorusSpinAtlas
