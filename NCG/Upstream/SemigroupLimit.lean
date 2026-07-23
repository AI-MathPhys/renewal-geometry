/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.StablePointer
import NCG.Upstream.ShrunkEffects

/-!
# The monitoring semigroup converges to the stable conditional expectation

The semigroup packaging of Theorem `thm:stable-pointer-selection`
(clauses (ii)/(iv), `manuscripts/renewal_emergence/renewal_emergence.tex`): the finite-dimensional
spectral calculus of a self-adjoint negative-semidefinite generator.

**Abstract layer** (any finite-dimensional complex inner product
space): `exp_apply_eigen` (the Banach-algebra exponential acts on
eigenvectors by the scalar exponential), `exp_smul_eigen` (real-time
scaling), `exp_fixes_of_zero` (kernel vectors are fixed),
`exp_smul_semigroup` (the semigroup law), `funct_exp_invariant` (any
functional annihilating the generator — the trace — is invariant),
and the main convergence `symm_dissipative_exp_tendsto`: for a
symmetric `T` with `re⟪x, Tx⟫ ≤ 0`, the semigroup `e^{tT}` converges
pointwise (hence in norm, in finite dimension) to a map `P` landing
in `ker T` with defect orthogonal to `ker T` — the orthogonal
projection onto the fixed space, unique with these properties
(`proj_unique`).

**Hilbert–Schmidt layer**: `Matrix E E ℂ` carries the Frobenius
inner product `⟪X, Y⟫ = Tr(XᴴY)` (`hsCore`, a local
`InnerProductSpace.ofCore` instance built from the trace identities
of `NCG/Upstream/StablePointer.lean`); the dissipator is the
symmetric dissipative linear map `dissipatorL`, and
`dissipator_exp_tendsto_stable` packages clause (iv): `e^{tℒ}`
converges to the Hilbert–Schmidt orthogonal projection onto
`ker ℒ` — the nondemolition stable algebra `ℱ_E` by
`dissipator_eq_zero_iff_mem_stable` — while fixing `ℱ_E` pointwise,
satisfying the semigroup law, and preserving the trace.  Complete
positivity of `e^{tℒ}` is the remaining scoped clause of (ii).
-/

namespace NCG.Upstream

open Filter Module Matrix Nat

/-! ## Abstract layer -/

section Abstract

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable [FiniteDimensional ℂ V]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- The exponential applied at a vector, as a series. -/
theorem exp_apply_tsum (A : V →L[ℂ] V) (x : V) :
    NormedSpace.exp A x = ∑' n : ℕ, (n !⁻¹ : ℂ) • ((A ^ n) x) := by
  have hexpA : NormedSpace.exp A = ∑' n : ℕ, (n !⁻¹ : ℂ) • A ^ n :=
    congrFun (NormedSpace.exp_eq_tsum ℂ) A
  have hsummable : Summable fun n : ℕ => (n !⁻¹ : ℂ) • A ^ n :=
    NormedSpace.expSeries_summable' (𝕂 := ℂ) A
  have heval : (∑' n : ℕ, (n !⁻¹ : ℂ) • A ^ n) x
      = ∑' n : ℕ, ((n !⁻¹ : ℂ) • A ^ n) x :=
    (ContinuousLinearMap.apply ℂ V x).map_tsum hsummable
  rw [hexpA, heval]
  exact tsum_congr fun n => by
    rw [ContinuousLinearMap.smul_apply]

/-- The exponential acts on eigenvectors by the scalar
exponential. -/
theorem exp_apply_eigen {A : V →L[ℂ] V} {x : V} {c : ℂ}
    (h : A x = c • x) :
    NormedSpace.exp A x = NormedSpace.exp c • x := by
  have hpow : ∀ n : ℕ, (A ^ n) x = c ^ n • x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_succ]
      have h1 : (A ^ n * A) x = (A ^ n) (A x) := rfl
      rw [h1, h, map_smul, ih, smul_smul, mul_comm]
  rw [exp_apply_tsum]
  have hterm : ∀ n : ℕ, (n !⁻¹ : ℂ) • ((A ^ n) x)
      = ((n !⁻¹ : ℂ) * c ^ n) • x := by
    intro n
    rw [hpow n, smul_smul]
  rw [tsum_congr hterm]
  have hsc : Summable fun n : ℕ => (n !⁻¹ : ℂ) * c ^ n := by
    have h2 := NormedSpace.expSeries_summable' (𝕂 := ℂ) c
    simpa [smul_eq_mul] using h2
  have h4 : (∑' n : ℕ, ((n !⁻¹ : ℂ) * c ^ n) • x)
      = (∑' n : ℕ, (n !⁻¹ : ℂ) * c ^ n) • x :=
    ((ContinuousLinearMap.toSpanSingleton ℂ x).map_tsum hsc).symm
  rw [h4]
  congr 1
  have h3 : NormedSpace.exp c = ∑' n : ℕ, (n !⁻¹ : ℂ) • c ^ n :=
    congrFun (NormedSpace.exp_eq_tsum ℂ) c
  rw [h3]
  simp [smul_eq_mul]

/-- Real-time eigenvector scaling: `e^{tT} x = e^{tμ} x`. -/
theorem exp_smul_eigen {T : V →L[ℂ] V} {x : V} {μ : ℝ}
    (h : T x = ((μ : ℝ) : ℂ) • x) (t : ℝ) :
    NormedSpace.exp (t • T) x
      = (((Real.exp (t * μ) : ℝ) : ℂ)) • x := by
  have h1 : (t • T) x = ((t * μ : ℝ) : ℂ) • x := by
    rw [ContinuousLinearMap.smul_apply, h, ← smul_assoc]
    congr 1
    rw [Complex.real_smul, Complex.ofReal_mul]
  rw [exp_apply_eigen h1]
  congr 1
  rw [← Complex.exp_eq_exp_ℂ, ← Complex.ofReal_exp]

/-- Kernel vectors are fixed by the semigroup. -/
theorem exp_fixes_of_zero {T : V →L[ℂ] V} {x : V} (h : T x = 0)
    (t : ℝ) : NormedSpace.exp (t • T) x = x := by
  have h1 : T x = ((0 : ℝ) : ℂ) • x := by
    rw [h]
    simp
  rw [exp_smul_eigen h1 t]
  simp

/-- The semigroup law `D_{s+t} = D_s D_t`. -/
theorem exp_smul_semigroup (T : V →L[ℂ] V) (s t : ℝ) :
    NormedSpace.exp ((s + t) • T)
      = NormedSpace.exp (s • T) * NormedSpace.exp (t • T) := by
  letI : NormedAlgebra ℚ (V →L[ℂ] V) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  rw [add_smul]
  exact NormedSpace.exp_add_of_commute
    (((Commute.refl T).smul_left s).smul_right t)

/-- Any continuous functional annihilating the generator — the
trace — is invariant under the semigroup. -/
theorem funct_exp_invariant {A : V →L[ℂ] V} (f : V →L[ℂ] ℂ)
    (hf : ∀ y, f (A y) = 0) (x : V) :
    f (NormedSpace.exp A x) = f x := by
  rw [exp_apply_tsum]
  have hsummable : Summable fun n : ℕ =>
      (n !⁻¹ : ℂ) • ((A ^ n) x) := by
    have h1 := NormedSpace.expSeries_summable' (𝕂 := ℂ) A
    have h2 := h1.map
      (ContinuousLinearMap.apply ℂ V x).toLinearMap.toAddMonoidHom
      (ContinuousLinearMap.apply ℂ V x).continuous
    exact h2.congr fun n => rfl
  rw [f.map_tsum hsummable]
  have hterm : ∀ n : ℕ, f ((n !⁻¹ : ℂ) • ((A ^ n) x))
      = if n = 0 then f x else 0 := by
    intro n
    rw [map_smul]
    cases n with
    | zero => simp
    | succ n =>
      have h3 : (A ^ (n + 1)) x = A ((A ^ n) x) := by
        have h4 : A ^ (n + 1) = A * A ^ n := pow_succ' A n
        rw [h4]
        rfl
      rw [h3, hf, smul_zero, if_neg (Nat.succ_ne_zero n)]
  rw [tsum_congr hterm, tsum_ite_eq]

section Convergence

variable {T : V →ₗ[ℂ] V} (hT : T.IsSymmetric)
variable (hdiss : ∀ x : V, (inner ℂ x (T x) : ℂ).re ≤ 0)

/-- The continuous version of the generator. -/
noncomputable def clm (T : V →ₗ[ℂ] V) : V →L[ℂ] V :=
  LinearMap.toContinuousLinearMap T

theorem clm_apply (T : V →ₗ[ℂ] V) (x : V) : clm T x = T x := rfl

/-- **Uniqueness of the orthogonal projection characterization**:
two vectors in the kernel whose defects from `x` are orthogonal to
the kernel coincide — "the unique trace-preserving conditional
expectation" clause in orthogonal form. -/
theorem proj_unique {x y z : V} (hy : T y = 0) (hz : T z = 0)
    (hyo : ∀ k, T k = 0 → (inner ℂ (x - y) k : ℂ) = 0)
    (hzo : ∀ k, T k = 0 → (inner ℂ (x - z) k : ℂ) = 0) : y = z := by
  have hker : T (y - z) = 0 := by
    rw [map_sub, hy, hz, sub_zero]
  have h1 := hyo (y - z) hker
  have h2 := hzo (y - z) hker
  have h3 : (inner ℂ (y - z) (y - z) : ℂ) = 0 := by
    have h5 : (inner ℂ ((x - z) - (x - y)) (y - z) : ℂ) = 0 := by
      rw [inner_sub_left, h2, h1, sub_zero]
    have h4 : (x - z) - (x - y) = y - z := by abel
    rwa [h4] at h5
  exact sub_eq_zero.mp (inner_self_eq_zero.mp h3)

include hT hdiss in
/-- **The spectral convergence** (`thm:stable-pointer-selection`
(iv), abstract form): the semigroup of a symmetric dissipative
generator converges pointwise to a map `P` with values in `ker T`
whose defect is orthogonal to `ker T` — the orthogonal projection
onto the fixed space. -/
theorem symm_dissipative_exp_tendsto :
    ∃ P : V → V,
      (∀ x, Tendsto (fun t : ℝ => NormedSpace.exp (t • clm T) x)
        atTop (nhds (P x)))
      ∧ (∀ x, T (P x) = 0)
      ∧ (∀ x k, T k = 0 → (inner ℂ (x - P x) k : ℂ) = 0) := by
  classical
  set n := Module.finrank ℂ V with hn
  have hn' : Module.finrank ℂ V = n := rfl
  set b := hT.eigenvectorBasis hn' with hb
  set μ := hT.eigenvalues hn' with hμ
  have hbev : ∀ i, T (b i) = ((μ i : ℝ) : ℂ) • b i := fun i =>
    hT.apply_eigenvectorBasis hn' i
  have hμle : ∀ i, μ i ≤ 0 := by
    intro i
    have h1 : (inner ℂ (b i) (T (b i)) : ℂ) = ((μ i : ℝ) : ℂ) := by
      rw [hbev i, inner_smul_right]
      have h2 : (inner ℂ (b i) (b i) : ℂ) = 1 := by
        rw [inner_self_eq_norm_sq_to_K]
        rw [b.orthonormal.1 i]
        norm_num
      rw [h2, mul_one]
    have h3 := hdiss (b i)
    rw [h1] at h3
    simpa using h3
  -- the candidate projection
  set P : V → V := fun x => ∑ i ∈ Finset.univ.filter (fun i => μ i = 0),
    (inner ℂ (b i) x : ℂ) • b i with hP
  refine ⟨P, ?_, ?_, ?_⟩
  · -- pointwise convergence
    intro x
    have hx : x = ∑ i, (inner ℂ (b i) x : ℂ) • b i :=
      (b.sum_repr' x).symm
    have hexp : ∀ t : ℝ, NormedSpace.exp (t • clm T) x
        = ∑ i, (inner ℂ (b i) x : ℂ)
            • (((Real.exp (t * μ i) : ℝ) : ℂ)) • b i := by
      intro t
      conv_lhs => rw [hx]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul]
      congr 1
      exact exp_smul_eigen (by rw [clm_apply, hbev i]) t
    have hlim : ∀ i : Fin n, Tendsto (fun t : ℝ =>
        (inner ℂ (b i) x : ℂ)
          • (((Real.exp (t * μ i) : ℝ) : ℂ)) • b i) atTop
        (nhds (if μ i = 0 then (inner ℂ (b i) x : ℂ) • b i else 0)) := by
      intro i
      by_cases hμi : μ i = 0
      · rw [if_pos hμi]
        have h1 : (fun t : ℝ => (inner ℂ (b i) x : ℂ)
            • (((Real.exp (t * μ i) : ℝ) : ℂ)) • b i)
            = fun _ => (inner ℂ (b i) x : ℂ) • b i := by
          funext t
          rw [hμi, mul_zero, Real.exp_zero]
          norm_num
        rw [h1]
        exact tendsto_const_nhds
      · rw [if_neg hμi]
        have hμneg : μ i < 0 := lt_of_le_of_ne (hμle i) hμi
        have h1 : Tendsto (fun t : ℝ => t * μ i) atTop atBot :=
          tendsto_id.atTop_mul_const_of_neg hμneg
        have h2 : Tendsto (fun t : ℝ => Real.exp (t * μ i)) atTop
            (nhds 0) := Real.tendsto_exp_atBot.comp h1
        have h3 : Tendsto (fun t : ℝ =>
            (inner ℂ (b i) x : ℂ)
              • (((Real.exp (t * μ i) : ℝ) : ℂ)) • b i) atTop
            (nhds ((inner ℂ (b i) x : ℂ)
              • (((0 : ℝ) : ℂ)) • b i)) := by
          refine Tendsto.smul_const ?_ _ |>.const_smul _
          exact (Complex.continuous_ofReal.tendsto 0).comp h2
        simpa using h3
    have hsum := tendsto_finset_sum Finset.univ fun i _ => hlim i
    have hPsum : P x = ∑ i, (if μ i = 0
        then (inner ℂ (b i) x : ℂ) • b i else 0) := by
      rw [hP]
      exact Finset.sum_filter _ _
    rw [← hPsum] at hsum
    exact Tendsto.congr (fun t => (hexp t).symm) hsum
  · -- the limit lands in the kernel
    intro x
    rw [hP, map_sum]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_filter] at hi
    rw [map_smul, hbev i, hi.2]
    simp
  · -- the defect is orthogonal to the kernel
    intro x k hk
    have hbk : ∀ i, μ i ≠ 0 → (inner ℂ (b i) k : ℂ) = 0 := by
      intro i hμi
      have h1 : (inner ℂ (T (b i)) k : ℂ)
          = (inner ℂ (b i) (T k) : ℂ) := hT (b i) k
      rw [hk, inner_zero_right, hbev i, inner_smul_left,
        Complex.conj_ofReal] at h1
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd (Complex.ofReal_eq_zero.mp h2) hμi
      · exact h2
    have hx : x = ∑ i, (inner ℂ (b i) x : ℂ) • b i :=
      (b.sum_repr' x).symm
    have hdefect : x - P x
        = ∑ i ∈ Finset.univ.filter (fun i => ¬ μ i = 0),
            (inner ℂ (b i) x : ℂ) • b i := by
      have h1 := Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i => μ i = 0) (fun i => (inner ℂ (b i) x : ℂ) • b i)
      have h2 : P x = ∑ i ∈ Finset.univ.filter (fun i => μ i = 0),
          (inner ℂ (b i) x : ℂ) • b i := rfl
      rw [h2]
      nth_rewrite 1 [hx]
      rw [← h1]
      abel
    rw [hdefect, sum_inner]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_filter] at hi
    rw [inner_smul_left, hbk i hi.2, mul_zero]

end Convergence

end Abstract

/-! ## The Hilbert–Schmidt layer -/

section HS

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The Frobenius (Hilbert–Schmidt) inner-product core on
`Matrix E E ℂ`: `⟪X, Y⟫ = Tr(XᴴY)`. -/
noncomputable def hsCore : InnerProductSpace.Core ℂ (Matrix E E ℂ) where
  inner X Y := (Xᴴ * Y).trace
  conj_inner_symm X Y := by
    show star ((Yᴴ * X).trace) = (Xᴴ * Y).trace
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  re_inner_nonneg X := by
    show 0 ≤ ((Xᴴ * X).trace).re
    rw [trace_conjTranspose_mul_self_eq]
    rw [Complex.ofReal_re]
    exact Finset.sum_nonneg fun d _ =>
      Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  definite X h := eq_zero_of_trace_conjTranspose_mul_self h
  add_left X Y Z := by
    show ((X + Y)ᴴ * Z).trace = (Xᴴ * Z).trace + (Yᴴ * Z).trace
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.trace_add]
  smul_left X Y r := by
    show ((r • X)ᴴ * Y).trace = (starRingEnd ℂ) r * (Xᴴ * Y).trace
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.trace_smul]
    rfl

noncomputable local instance : NormedAddCommGroup (Matrix E E ℂ) :=
  hsCore.toNormedAddCommGroup

noncomputable local instance : TopologicalSpace (Matrix E E ℂ) :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

noncomputable local instance : InnerProductSpace ℂ (Matrix E E ℂ) :=
  InnerProductSpace.ofCore hsCore.toCore

theorem hs_inner_def (X Y : Matrix E E ℂ) :
    (inner ℂ X Y : ℂ) = (Xᴴ * Y).trace := rfl

theorem comm_add_right' (A X Y : Matrix E E ℂ) :
    comm A (X + Y) = comm A X + comm A Y := by
  simp only [comm, Matrix.mul_add, Matrix.add_mul]
  abel

/-- The dissipator as a `ℂ`-linear map. -/
noncomputable def dissipatorL {m : Type*} [Fintype m]
    (A : m → Matrix E E ℂ) :
    Matrix E E ℂ →ₗ[ℂ] Matrix E E ℂ where
  toFun := dissipator A
  map_add' X Y := by
    unfold dissipator
    rw [← smul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [comm_add_right' (A j) X Y, comm_add_right']
  map_smul' c X := by
    unfold dissipator
    simp only [RingHom.id_apply]
    rw [smul_comm]
    congr 1
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [comm_smul_right, comm_smul_right]

theorem dissipatorL_apply {m : Type*} [Fintype m]
    (A : m → Matrix E E ℂ) (X : Matrix E E ℂ) :
    dissipatorL A X = dissipator A X := rfl

/-- The dissipator is Hilbert–Schmidt symmetric. -/
theorem dissipatorL_isSymmetric {m : Type*} [Fintype m]
    {A : m → Matrix E E ℂ} (hA : ∀ j, (A j)ᴴ = A j) :
    (dissipatorL A).IsSymmetric := by
  intro X Y
  show ((dissipator A X)ᴴ * Y).trace = (Xᴴ * dissipator A Y).trace
  exact hsInner_dissipator_symm hA X Y

/-- The dissipator is dissipative for the Hilbert–Schmidt pairing. -/
theorem dissipatorL_dissipative {m : Type*} [Fintype m]
    {A : m → Matrix E E ℂ} (hA : ∀ j, (A j)ᴴ = A j)
    (X : Matrix E E ℂ) :
    ((inner ℂ X (dissipatorL A X) : ℂ)).re ≤ 0 := by
  rw [hs_inner_def, dissipatorL_apply, hsInner_dissipator_self hA]
  have h1 : ∀ j, ((comm (A j) X)ᴴ * comm (A j) X).trace
      = ((∑ d : E, ∑ i : E,
          Complex.normSq (comm (A j) X i d) : ℝ) : ℂ) := fun j =>
    trace_conjTranspose_mul_self_eq _
  rw [Finset.sum_congr rfl fun j _ => h1 j]
  rw [← Complex.ofReal_sum]
  have h2 : (0 : ℝ) ≤ ∑ j, ∑ d : E, ∑ i : E,
      Complex.normSq (comm (A j) X i d) :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun d _ =>
      Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have h3 : (-(1 / 2 : ℂ)
      * ((∑ j, ∑ d : E, ∑ i : E,
          Complex.normSq (comm (A j) X i d) : ℝ) : ℂ)).re
      = -(1 / 2) * (∑ j, ∑ d : E, ∑ i : E,
          Complex.normSq (comm (A j) X i d)) := by
    rw [show (-(1 / 2 : ℂ)) = (((-(1 / 2) : ℝ)) : ℂ) from by
      norm_num, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [h3]
  nlinarith

/-- **Theorem `thm:stable-pointer-selection` (iv), packaged**: the
monitoring semigroup `e^{tℒ}` converges pointwise to the
Hilbert–Schmidt orthogonal projection onto the fixed space `ker ℒ`
(the nondemolition stable algebra under the generator-spanning
hypotheses of `dissipator_eq_zero_iff_mem_stable`), fixes the fixed
space, obeys the semigroup law, and preserves the trace. -/
theorem dissipator_exp_tendsto_stable {m : Type*} [Fintype m]
    {A : m → Matrix E E ℂ} (hA : ∀ j, (A j)ᴴ = A j) :
    ∃ P : Matrix E E ℂ → Matrix E E ℂ,
      (∀ X, Filter.Tendsto
        (fun t : ℝ => NormedSpace.exp (t • clm (dissipatorL A)) X)
        Filter.atTop (nhds (P X)))
      ∧ (∀ X, dissipator A (P X) = 0)
      ∧ (∀ X K, dissipator A K = 0 →
          (inner ℂ (X - P X) K : ℂ) = 0)
      ∧ (∀ K, dissipator A K = 0 → ∀ t : ℝ,
          NormedSpace.exp (t • clm (dissipatorL A)) K = K)
      ∧ (∀ s t : ℝ, NormedSpace.exp ((s + t) • clm (dissipatorL A))
          = NormedSpace.exp (s • clm (dissipatorL A))
            * NormedSpace.exp (t • clm (dissipatorL A)))
      ∧ (∀ (t : ℝ) (X : Matrix E E ℂ),
          (NormedSpace.exp (t • clm (dissipatorL A)) X).trace
            = X.trace) := by
  obtain ⟨P, hconv, hker, horth⟩ :=
    symm_dissipative_exp_tendsto (dissipatorL_isSymmetric hA)
      (dissipatorL_dissipative hA)
  refine ⟨P, hconv, hker, horth, ?_, ?_, ?_⟩
  · intro K hK t
    exact exp_fixes_of_zero (show clm (dissipatorL A) K = 0 from hK) t
  · intro s t
    exact exp_smul_semigroup _ s t
  · intro t X
    -- the trace functional annihilates the scaled generator
    set f : Matrix E E ℂ →L[ℂ] ℂ :=
      LinearMap.toContinuousLinearMap (Matrix.traceLinearMap E ℂ ℂ)
      with hfdef
    have hf : ∀ Y, f ((t • clm (dissipatorL A)) Y) = 0 := by
      intro Y
      show ((t • clm (dissipatorL A)) Y).trace = 0
      have h1 : (t • clm (dissipatorL A)) Y
          = t • dissipator A Y := rfl
      rw [h1, Matrix.trace_smul, trace_dissipator, smul_zero]
    exact funct_exp_invariant f hf X

end HS

end NCG.Upstream
