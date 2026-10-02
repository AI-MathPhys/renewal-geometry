/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Spectralization.ReconstructionCategories
import RenewalGeometry.Spectralization.SpectralCompressionsSequential
import RenewalGeometry.Certificates.ToeplitzSpectralTripleExact

open NCG
/-!
# Essential images of the reconstruction functors

Paper `predictive_spectral_geometry` (revised 1 Oct 2026), labels `thm:essential-image` and
`thm:summary-finite` (clause (iii)), with the categories and functors of
`def:reconstruction-categories` encoded in `ReconstructionCategories.lean`.

* **Finite spectral screens are spectral projections**
  (`range_diracSpectralScreen_eq_spectralSubspace`): the finite resolvent screen attached to a
  finite set `s` of resolvent eigenvalues is the orthogonal projection onto the span of the
  Dirac eigenvectors with eigenvalue in `{λ ∈ ℝ | (λ - i)⁻¹ ∈ s}`.
* **Strong line** (`strongReconstruction_essImage`): every object of `Spec_cpt^sep` lies in the
  essential image of `𝔖_cpt^{strong,cal}`; in fact every spectral projection sequence
  `P_n ↑ I` satisfies the strong conditions `eq:strong-compression-topology`
  (`isStrongCompression_of_spectralProjectionSequence`).
* **Norm line** (`normReconstruction_essImage_iff`): a separable triple lies in the essential
  image of `𝔖_cpt^{norm,cal}` iff some spectral projection sequence `P_n ↑ I` has
  `‖[P_n, π(a)]‖ → 0` for every `a ∈ 𝒜_D` (`SpectralCommutatorDecay`), and this class coincides
  with the spectral quasidiagonality of `thm:spectral-compressions`
  (`spectralCommutatorDecay_iff_spectrallyQuasidiagonal`, finite spectral screens of
  `SpectralCompressionsSequential.lean`).  The windowed, `J`/`γ`-equivariant variant
  `IsSpectrallyQuasidiagonal` of `ReconstructionCategories.lean` is contained in it
  (`isSpectrallyQuasidiagonal_essImage_norm`).
* **Properness** (`toeplitzObject_not_essImage_norm`): the Toeplitz triple (number operator,
  `𝒜_D = alg(I, S, S*)`) is a separable compact-resolvent object in the strong essential image
  but not in the norm essential image (it also serves as a non-vacuity witness for
  `CompactMarkedObject`).
* `essential_image` bundles `thm:essential-image`; `summary_finite_marked` bundles clauses
  (ii)–(iii) of `thm:summary-finite` for marked triples.

Scope remark.  The sources of (C2)/(C3) use arbitrary finite-rank spectral projections
`1_{B_n}(D)`, while `IsSpectrallyQuasidiagonal` uses symmetric windows `1_{[-R,R]}(D)` with
`J`/`γ` equivariance.  The norm essential image is therefore identified with the screen form of
spectral quasidiagonality used in `thm:spectral-compressions`; the windowed form is contained in
it (`sqdProperty_le_essImage_norm`).
-/

open CategoryTheory Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RenewalGeometry.EssentialImageReconstruction

open RenewalGeometry.ReconstructionCategories
open RenewalGeometry.SpectralCompressionsSequential
open RenewalGeometry.CompactResolventDiracSpectralScreensExact
open RenewalGeometry.CompactNormalFiniteSpectralScreensExact

/-! ### Finite resolvent screens are spectral projections of `D` -/

section Screens

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The Dirac eigenvalues `λ ∈ ℝ` whose resolvent eigenvalue `(λ - i)⁻¹` lies in `s`. -/
def screenEigenvalues (s : Finset ℂ) : Set ℝ := {l | ((l : ℂ) - Complex.I)⁻¹ ∈ s}

/-- Eigenvalues of the symmetric operator `D` are real. -/
theorem dirac_eigenvalue_im_eq_zero (S : SpectralTriple A H) (x : S.dirac.domain) (c : ℂ)
    (hx : (x : H) ≠ 0) (h : S.dirac x = c • (x : H)) : c.im = 0 := by
  have hsym := S.symmetric x x
  rw [h, inner_smul_left, inner_smul_right] at hsym
  have hne : ⟪(x : H), (x : H)⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hx
  have hc : (starRingEnd ℂ) c = c := mul_right_cancel₀ hne hsym
  exact Complex.conj_eq_iff_im.mp hc

/-- A resolvent eigenvector with eigenvalue `μ ≠ 0` is a Dirac eigenvector with eigenvalue
`μ⁻¹ + i`. -/
theorem dirac_apply_of_resolvent_eigen (S : SpectralTriple A H) {μ : ℂ} {x : H}
    (hx : S.resolvent x = μ • x) (hμ : μ ≠ 0) (hxD : x ∈ S.dirac.domain) :
    S.dirac ⟨x, hxD⟩ = (μ⁻¹ + Complex.I) • x := by
  have hright := S.resolvent_right_inverse x
  have hsub : (⟨S.resolvent x, S.resolvent_mem_domain x⟩ : S.dirac.domain) =
      μ • (⟨x, hxD⟩ : S.dirac.domain) := Subtype.ext (by simp [hx])
  rw [hsub, LinearPMap.map_smul, hx] at hright
  have h1 : μ • (S.dirac ⟨x, hxD⟩ - Complex.I • x) = x := by
    rw [smul_sub, smul_comm μ Complex.I x]
    exact hright
  have h2 : S.dirac ⟨x, hxD⟩ - Complex.I • x = μ⁻¹ • x := (eq_inv_smul_iff₀ hμ).mpr h1
  rw [add_smul, ← h2, sub_add_cancel]

/-- A Dirac eigenvector with real eigenvalue `l` is a resolvent eigenvector with eigenvalue
`(l - i)⁻¹`. -/
theorem resolvent_apply_of_dirac_eigen (S : SpectralTriple A H) {x : H}
    (hxD : x ∈ S.dirac.domain) {l : ℝ} (h : S.dirac ⟨x, hxD⟩ = (l : ℂ) • x) :
    S.resolvent x = ((l : ℂ) - Complex.I)⁻¹ • x := by
  have hleft := S.resolvent_left_inverse ⟨x, hxD⟩
  have hne : (l : ℂ) - Complex.I ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
  change S.resolvent (S.dirac ⟨x, hxD⟩ - Complex.I • x) = x at hleft
  rw [h, ← sub_smul, map_smul] at hleft
  exact (eq_inv_smul_iff₀ hne).mpr hleft

/-- **Finite resolvent screens are spectral projections of `D`**: the range of the screen
attached to a finite set `s` of resolvent eigenvalues is the span of the Dirac eigenvectors
with eigenvalue in `screenEigenvalues s`. -/
theorem range_diracSpectralScreen_eq_spectralSubspace {ι : Type*}
    (S : MarkedCompactTriple A H ι) (s : Finset ℂ) :
    LinearMap.range (diracSpectralScreen S.toSpectralTriple s).toLinearMap =
      S.spectralSubspace (screenEigenvalues s) := by
  change LinearMap.range (spectralScreen S.resolvent S.resolvent_isCompact
      (resolvent_injective S.toSpectralTriple) s).toLinearMap = _
  rw [spectralScreen_range]
  apply le_antisymm
  · refine Finset.sup_le fun μ hμs => ?_
    intro x hx
    by_cases hx0 : x = 0
    · rw [hx0]; exact Submodule.zero_mem _
    have hRx : S.resolvent x = μ • x := Module.End.mem_eigenspace_iff.mp hx
    have hμ : μ ≠ 0 := by
      rintro rfl
      apply hx0
      apply resolvent_injective S.toSpectralTriple
      rw [hRx, zero_smul, map_zero]
    have hxD : x ∈ S.dirac.domain := resolventEigenspace_le_diracDomain S.toSpectralTriple μ hx
    have hD := dirac_apply_of_resolvent_eigen S.toSpectralTriple hRx hμ hxD
    have him : (μ⁻¹ + Complex.I).im = 0 :=
      dirac_eigenvalue_im_eq_zero S.toSpectralTriple ⟨x, hxD⟩ _ hx0 hD
    have hreal : (((μ⁻¹ + Complex.I).re : ℝ) : ℂ) = μ⁻¹ + Complex.I :=
      Complex.ext (by simp) (by simpa using him.symm)
    refine Submodule.subset_span ⟨hxD, (μ⁻¹ + Complex.I).re, ?_, ?_⟩
    · change ((((μ⁻¹ + Complex.I).re : ℝ) : ℂ) - Complex.I)⁻¹ ∈ s
      rw [hreal, add_sub_cancel_right, inv_inv]
      exact hμs
    · rw [hreal]; exact hD
  · refine Submodule.span_le.mpr ?_
    rintro x ⟨hxD, l, hl, hD⟩
    have hR := resolvent_apply_of_dirac_eigen S.toSpectralTriple hxD hD
    exact Finset.le_sup (f := fun μ => Module.End.eigenspace S.resolvent.toLinearMap μ) hl
      (Module.End.mem_eigenspace_iff.mpr hR)

end Screens

/-! ### Spectral projection sequences and the strong line -/

section Sequences

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {ι : Type*}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {S : MarkedCompactTriple A H ι}

theorem spectralProjectionSequence_idem (P : S.SpectralProjectionSequence) (n : ℕ) :
    P.P n * P.P n = P.P n :=
  (P.spectral n).1.isIdempotentElem.eq

theorem spectralProjectionSequence_star (P : S.SpectralProjectionSequence) (n : ℕ) :
    star (P.P n) = P.P n :=
  (P.spectral n).1.isSelfAdjoint.star_eq

theorem spectralProjectionSequence_norm_le (P : S.SpectralProjectionSequence) (n : ℕ) :
    ‖P.P n‖ ≤ 1 :=
  IsStarProjection.norm_le _ (P.spectral n).1

/-- Along a spectral projection sequence, `y_n → z` implies `P_n y_n → z`. -/
theorem spectralProjectionSequence_tendsto_apply_of_tendsto (P : S.SpectralProjectionSequence)
    {y : ℕ → H} {z : H} (hy : Tendsto y atTop (𝓝 z)) :
    Tendsto (fun n => P.P n (y n)) atTop (𝓝 z) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at hy ⊢
  have h2 := tendsto_iff_norm_sub_tendsto_zero.mp (P.tendsto_id z)
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using hy.add h2)
  calc ‖P.P n (y n) - z‖ = ‖P.P n (y n - z) + (P.P n z - z)‖ := by rw [map_sub]; abel_nf
    _ ≤ ‖P.P n (y n - z)‖ + ‖P.P n z - z‖ := norm_add_le _ _
    _ ≤ ‖y n - z‖ + ‖P.P n z - z‖ := by
        gcongr
        exact ((P.P n).le_of_opNorm_le (spectralProjectionSequence_norm_le P n) _).trans_eq
          (one_mul _)

/-- Every bounded operator is recovered strongly by its compressions `P_n T P_n`. -/
theorem spectralProjectionSequence_tendsto_compress (P : S.SpectralProjectionSequence)
    (T : H →L[ℂ] H) (ξ : H) :
    Tendsto (fun n => MarkedCompactTriple.compress (P.P n) T ξ) atTop (𝓝 (T ξ)) :=
  spectralProjectionSequence_tendsto_apply_of_tendsto P
    ((T.continuous.tendsto ξ).comp (P.tendsto_id ξ))

/-- **Strong compression (`eq:strong-compression-topology`) along every spectral projection
sequence**: compressed algebra elements, commutator extensions, resolvents and declared marks
converge strongly, and product defects tend strongly to zero. -/
theorem isStrongCompression_of_spectralProjectionSequence (P : S.SpectralProjectionSequence) :
    S.IsStrongCompression P := by
  refine ⟨fun a _ ξ => spectralProjectionSequence_tendsto_compress P _ ξ,
    fun a _ T _ ξ => spectralProjectionSequence_tendsto_compress P T ξ,
    fun z _ Rz _ ξ => spectralProjectionSequence_tendsto_compress P Rz ξ,
    fun a _ b _ ξ => ?_, fun i ξ => spectralProjectionSequence_tendsto_compress P _ ξ⟩
  have h1 := spectralProjectionSequence_tendsto_compress P (S.rep (a * b)) ξ
  have h2 : Tendsto (fun n => P.P n (S.rep a (P.P n (S.rep b (P.P n ξ))))) atTop
      (𝓝 (S.rep a (S.rep b ξ))) :=
    spectralProjectionSequence_tendsto_apply_of_tendsto P
      (((S.rep a).continuous.tendsto _).comp
        (spectralProjectionSequence_tendsto_compress P (S.rep b) ξ))
  have h3 := h1.sub h2
  have hlim : S.rep (a * b) ξ - S.rep a (S.rep b ξ) = 0 := by
    rw [map_mul, ContinuousLinearMap.mul_apply, sub_self]
  rw [hlim] at h3
  exact Tendsto.congr (fun n => by simp [MarkedCompactTriple.compress]) h3

/-- The spectral projection sequence of a monotone family of finite resolvent screens
converging strongly to the identity. -/
def screenProjectionSequence (S : MarkedCompactTriple A H ι) (s : ℕ → Finset ℂ)
    (hmono : Monotone s)
    (hconv : ∀ x, Tendsto (fun n => diracSpectralScreen S.toSpectralTriple (s n) x) atTop (𝓝 x)) :
    S.SpectralProjectionSequence where
  P n := diracSpectralScreen S.toSpectralTriple (s n)
  spectral n := ⟨ContinuousLinearMap.isStarProjection_iff_isSymmetricProjection.mpr
      (diracSpectralScreen_isSymmetricProjection _ _),
    screenEigenvalues (s n), range_diracSpectralScreen_eq_spectralSubspace S (s n)⟩
  finiteRank n := diracSpectralScreen_range_finiteDimensional _ _
  commutes n x hx := ⟨diracSpectralScreen_mem_domain _ _ ⟨x, hx⟩,
    diracSpectralScreen_commutes_dirac _ _ ⟨x, hx⟩⟩
  mono _ _ hmn := screen_range_mono _ (hmono hmn)
  tendsto_id := hconv

/-- Every separable marked compact-resolvent triple admits a spectral projection sequence
`P_n ↑ I` (`thm:spectral-compressions`, sequential screens). -/
theorem nonempty_spectralProjectionSequence (X : CompactMarkedObject A ι) :
    Nonempty X.triple.SpectralProjectionSequence := by
  obtain ⟨s, hmono, hconv⟩ := exists_monotone_screens X.triple.toSpectralTriple
  exact ⟨screenProjectionSequence X.triple s hmono hconv⟩

/-- The (C2) source object built from a spectral projection sequence (strong compression holds
automatically), with recorded commutant-coordinate functionals of dimension `0`. -/
def strongCompressionObjectOf (X : CompactMarkedObject A ι)
    (P : X.triple.SpectralProjectionSequence) : StrongCompressionObject A ι where
  obj := X
  P := P
  strong := isStrongCompression_of_spectralProjectionSequence P
  cdim _ := 0
  coordinates _ := 0

/-- **Strong line of `thm:essential-image`**: `EssIm(𝔖_cpt^{strong,cal}) = Spec_cpt^sep`. -/
theorem strongReconstruction_essImage (X : CompactMarkedObject A ι) :
    (strongReconstruction (A := A) (ι := ι)).essImage X := by
  obtain ⟨P⟩ := nonempty_spectralProjectionSequence X
  exact ⟨strongCompressionObjectOf X P, ⟨Iso.refl _⟩⟩

/-- The norm-multiplicative defect along a spectral projection sequence in C⋆-algebra form. -/
theorem compression_defect_eq (P : S.SpectralProjectionSequence) (a b : A) (n : ℕ) :
    P.P n ∘L S.rep (a * b) ∘L P.P n - P.P n ∘L S.rep a ∘L P.P n ∘L S.rep b ∘L P.P n =
      SpectralCompression.compress (P.P n) (S.rep a * S.rep b) -
        SpectralCompression.compress (P.P n) (S.rep a) *
          SpectralCompression.compress (P.P n) (S.rep b) := by
  have hPP : ∀ y, P.P n (P.P n y) = P.P n y := fun y => by
    rw [← ContinuousLinearMap.mul_apply, spectralProjectionSequence_idem]
  ext x
  simp [SpectralCompression.compress, hPP]

/-- **Norm multiplicativity ↔ commutator decay on `𝒜_D`** for a spectral projection sequence
(`thm:spectral-compressions`, in the categories of `def:reconstruction-categories`). -/
theorem isNormMultiplicativeCompression_iff (P : S.SpectralProjectionSequence) :
    S.IsNormMultiplicativeCompression P ↔
      ∀ a ∈ S.smoothAlgebra,
        Tendsto (fun n => ‖P.P n * S.rep a - S.rep a * P.P n‖) atTop (𝓝 0) := by
  have key := SpectralCompression.normMultiplicativeOn_iff_commutatorDecayOn (fun n => P.P n)
    atTop (S.rep '' (S.smoothAlgebra : Set A))
    (by
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨star a, star_mem ha, map_star S.rep a⟩)
    (spectralProjectionSequence_idem P) (spectralProjectionSequence_star P)
  constructor
  · rintro ⟨_, hnorm⟩ a ha
    refine key.mp ?_ (S.rep a) ⟨a, ha, rfl⟩
    rintro _ ⟨a', ha', rfl⟩ _ ⟨b', hb', rfl⟩
    simpa only [compression_defect_eq] using hnorm a' ha' b' hb'
  · intro h
    refine ⟨isStrongCompression_of_spectralProjectionSequence P, fun a ha b hb => ?_⟩
    have := key.mpr (by
      rintro _ ⟨a', ha', rfl⟩
      exact h a' ha') (S.rep a) ⟨a, ha, rfl⟩ (S.rep b) ⟨b, hb, rfl⟩
    simpa only [compression_defect_eq] using this

end Sequences

/-! ### Transport of spectral projection sequences along unitary equivalences -/

section Transport

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {ι : Type*}
variable {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
variable {S : MarkedCompactTriple A H ι} {S' : MarkedCompactTriple A H' ι}

/-- Unitary conjugation preserves orthogonal projections. -/
theorem isStarProjection_conjOp (U : H ≃ₗᵢ[ℂ] H') {P : H →L[ℂ] H} (hP : IsStarProjection P) :
    IsStarProjection (conjOp U P) := by
  have hidem : ∀ z, P (P z) = P z := fun z => by
    rw [← ContinuousLinearMap.mul_apply, hP.isIdempotentElem.eq]
  have hsym : (P : H →ₗ[ℂ] H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hP.isSelfAdjoint
  refine ⟨?_, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun x y => ?_⟩
  · show conjOp U P * conjOp U P = conjOp U P
    ext x
    simp [conjOp, hidem]
  · show ⟪U (P (U.symm x)), y⟫_ℂ = ⟪x, U (P (U.symm y))⟫_ℂ
    conv_lhs => rw [← U.apply_symm_apply y]
    conv_rhs => rw [← U.apply_symm_apply x]
    rw [LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map]
    exact hsym (U.symm x) (U.symm y)

theorem range_conjOp (U : H ≃ₗᵢ[ℂ] H') (P : H →L[ℂ] H) :
    LinearMap.range (conjOp U P).toLinearMap =
      (LinearMap.range P.toLinearMap).map (U.toLinearEquiv : H →ₗ[ℂ] H') := by
  ext y
  simp only [LinearMap.mem_range, Submodule.mem_map]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨P (U.symm x), ⟨U.symm x, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨U z, by simp [conjOp]⟩

theorem norm_conjOp_le (U : H ≃ₗᵢ[ℂ] H') (T : H →L[ℂ] H) : ‖conjOp U T‖ ≤ ‖T‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) fun y => by
    show ‖U (T (U.symm y))‖ ≤ ‖T‖ * ‖y‖
    rw [LinearIsometryEquiv.norm_map]
    calc ‖T (U.symm y)‖ ≤ ‖T‖ * ‖U.symm y‖ := T.le_opNorm _
      _ = ‖T‖ * ‖y‖ := by rw [LinearIsometryEquiv.norm_map]

/-- A unitary equivalence maps spectral subspaces into spectral subspaces. -/
theorem map_spectralSubspace_le (e : CompactUnitaryEquivalence S S') (B : Set ℝ) :
    (S.spectralSubspace B).map (e.U.toLinearEquiv : H →ₗ[ℂ] H') ≤ S'.spectralSubspace B := by
  rw [MarkedCompactTriple.spectralSubspace, Submodule.map_span]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨x, ⟨hxD, l, hl, hD⟩, rfl⟩
  refine Submodule.subset_span ⟨(e.domain x).mp hxD, l, hl, ?_⟩
  show S'.dirac ⟨e.U x, _⟩ = (l : ℂ) • e.U x
  rw [e.dirac x hxD, hD, map_smul]

/-- A unitary equivalence maps `1_B(D) H` onto `1_B(D') H'`. -/
theorem map_spectralSubspace (e : CompactUnitaryEquivalence S S') (B : Set ℝ) :
    (S.spectralSubspace B).map (e.U.toLinearEquiv : H →ₗ[ℂ] H') = S'.spectralSubspace B := by
  refine le_antisymm (map_spectralSubspace_le e B) fun y hy => ?_
  have h := map_spectralSubspace_le e.symm B (Submodule.mem_map.mpr ⟨y, hy, rfl⟩)
  exact Submodule.mem_map.mpr ⟨e.U.symm y, h, e.U.apply_symm_apply y⟩

/-- Transport of a spectral projection sequence `P_n ↦ U P_n U⁻¹` along a unitary
equivalence. -/
def spectralProjectionSequenceTransport (e : CompactUnitaryEquivalence S S')
    (P : S.SpectralProjectionSequence) : S'.SpectralProjectionSequence where
  P n := conjOp e.U (P.P n)
  spectral n := by
    obtain ⟨hP, B, hB⟩ := P.spectral n
    exact ⟨isStarProjection_conjOp e.U hP, B, by rw [range_conjOp, hB, map_spectralSubspace]⟩
  finiteRank n := by
    rw [range_conjOp]
    have := P.finiteRank n
    infer_instance
  commutes n x hx := by
    have hx0 : e.U.symm x ∈ S.dirac.domain :=
      (e.domain _).mpr (by rw [LinearIsometryEquiv.apply_symm_apply]; exact hx)
    obtain ⟨h1, h2⟩ := P.commutes n (e.U.symm x) hx0
    refine ⟨(e.domain _).mp h1, ?_⟩
    have hD' : S'.dirac ⟨x, hx⟩ = e.U (S.dirac ⟨e.U.symm x, hx0⟩) := by
      rw [← e.dirac _ hx0]
      congr 1
      exact Subtype.ext (by simp)
    show S'.dirac ⟨e.U (P.P n (e.U.symm x)), _⟩ = e.U (P.P n (e.U.symm (S'.dirac ⟨x, hx⟩)))
    rw [e.dirac _ h1, h2, hD', LinearIsometryEquiv.symm_apply_apply]
  mono m n hmn := by
    show LinearMap.range (conjOp e.U (P.P m)).toLinearMap ≤
      LinearMap.range (conjOp e.U (P.P n)).toLinearMap
    rw [range_conjOp, range_conjOp]
    exact Submodule.map_mono (P.mono hmn)
  tendsto_id x := by
    have := ((e.U : H →L[ℂ] H').continuous.tendsto _).comp (P.tendsto_id (e.U.symm x))
    have hx : (e.U : H →L[ℂ] H') (e.U.symm x) = x := e.U.apply_symm_apply x
    rw [hx] at this
    exact this

theorem conjOp_commutator (e : CompactUnitaryEquivalence S S') (P : H →L[ℂ] H) (a : A) :
    conjOp e.U P * S'.rep a - S'.rep a * conjOp e.U P = conjOp e.U (P * S.rep a - S.rep a * P) := by
  ext y
  have h1 : S'.rep a y = e.U (S.rep a (e.U.symm y)) := by
    rw [e.rep, LinearIsometryEquiv.apply_symm_apply]
  have h2 : S'.rep a (e.U (P (e.U.symm y))) = e.U (S.rep a (P (e.U.symm y))) := (e.rep _ _).symm
  simp only [conjOp, ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_coe'', map_sub] at h2 ⊢
  rw [h1, h2, LinearIsometryEquiv.symm_apply_apply]

/-- Commutator decay `‖[P_n, π(a)]‖ → 0` on `𝒜_D` is transported along unitary equivalences. -/
theorem commutatorDecay_transport (e : CompactUnitaryEquivalence S S')
    (P : S.SpectralProjectionSequence)
    (h : ∀ a ∈ S.smoothAlgebra,
      Tendsto (fun n => ‖P.P n * S.rep a - S.rep a * P.P n‖) atTop (𝓝 0)) :
    ∀ a ∈ S'.smoothAlgebra, Tendsto (fun n =>
      ‖(spectralProjectionSequenceTransport e P).P n * S'.rep a -
        S'.rep a * (spectralProjectionSequenceTransport e P).P n‖) atTop (𝓝 0) := by
  intro a ha
  rw [e.smooth] at ha
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) (h a ha)
  show ‖conjOp e.U (P.P n) * S'.rep a - S'.rep a * conjOp e.U (P.P n)‖ ≤ _
  rw [conjOp_commutator]
  exact norm_conjOp_le _ _

end Transport

/-! ### The norm line -/

section NormLine

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {ι : Type*}

/-- Existence of a spectral projection sequence `P_n ↑ I` (in the sense of (C2)) with
`‖[P_n, π(a)]‖ → 0` for every `a ∈ 𝒜_D`. -/
def SpectralCommutatorDecay (X : CompactMarkedObject A ι) : Prop :=
  ∃ P : X.triple.SpectralProjectionSequence, ∀ a ∈ X.triple.smoothAlgebra,
    Tendsto (fun n => ‖P.P n * X.triple.rep a - X.triple.rep a * P.P n‖) atTop (𝓝 0)

/-- **Norm line of `thm:essential-image`, in the categories of
`def:reconstruction-categories`**: a separable compact-resolvent triple lies in the essential
image of `𝔖_cpt^{norm,cal}` iff some spectral projection sequence `P_n ↑ I` has
`‖[P_n, π(a)]‖ → 0` on `𝒜_D`. -/
theorem normReconstruction_essImage_iff (X : CompactMarkedObject A ι) :
    (normReconstruction (A := A) (ι := ι)).essImage X ↔ SpectralCommutatorDecay X := by
  constructor
  · rintro ⟨Y, ⟨f⟩⟩
    have hdec := (isNormMultiplicativeCompression_iff Y.obj.P).mp Y.property
    let e : CompactUnitaryEquivalence Y.obj.obj.triple X.triple := f.hom
    exact ⟨spectralProjectionSequenceTransport e Y.obj.P,
      commutatorDecay_transport e Y.obj.P hdec⟩
  · rintro ⟨P, hP⟩
    exact ⟨⟨strongCompressionObjectOf X P, (isNormMultiplicativeCompression_iff P).mpr hP⟩,
      ⟨Iso.refl _⟩⟩

/-- The windowed, `J`/`γ`-equivariant spectral quasidiagonality of
`ReconstructionCategories.lean` implies commutator decay along a spectral projection
sequence. -/
theorem spectralCommutatorDecay_of_isSpectrallyQuasidiagonal {X : CompactMarkedObject A ι}
    (h : X.triple.IsSpectrallyQuasidiagonal) : SpectralCommutatorDecay X :=
  let ⟨P, _, hP, _⟩ := h
  ⟨P, hP⟩

/-- `Spec_cpt^sqd` (windowed, equivariant form) lies in the norm essential image. -/
theorem isSpectrallyQuasidiagonal_essImage_norm {X : CompactMarkedObject A ι}
    (h : X.triple.IsSpectrallyQuasidiagonal) :
    (normReconstruction (A := A) (ι := ι)).essImage X :=
  (normReconstruction_essImage_iff X).mpr (spectralCommutatorDecay_of_isSpectrallyQuasidiagonal h)

theorem sqdProperty_le_essImage_norm :
    sqdProperty (A := A) (ι := ι) ≤ (normReconstruction (A := A) (ι := ι)).essImage :=
  fun _ h => isSpectrallyQuasidiagonal_essImage_norm h

end NormLine

/-! ### Reconciliation with the screen form of spectral quasidiagonality -/

section Reconcile

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {ι : Type*}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The spectral projection sequence attached to a screen sequence of
`SpectralCompressionsSequential.lean`. -/
def ofScreenSequence (S : MarkedCompactTriple A H ι) (P : ℕ → H →L[ℂ] H)
    (hP : IsScreenSequence S.toSpectralTriple P) : S.SpectralProjectionSequence where
  P := P
  spectral n := by
    obtain ⟨s, hs⟩ := hP.1 n
    rw [hs]
    exact ⟨ContinuousLinearMap.isStarProjection_iff_isSymmetricProjection.mpr
      (diracSpectralScreen_isSymmetricProjection _ _),
      screenEigenvalues s, range_diracSpectralScreen_eq_spectralSubspace S s⟩
  finiteRank n := by
    obtain ⟨s, hs⟩ := hP.1 n
    rw [hs]
    exact diracSpectralScreen_range_finiteDimensional _ _
  commutes n x hx := by
    obtain ⟨s, hs⟩ := hP.1 n
    rw [hs]
    exact ⟨diracSpectralScreen_mem_domain _ _ ⟨x, hx⟩,
      diracSpectralScreen_commutes_dirac _ _ ⟨x, hx⟩⟩
  mono := monotone_nat_of_le_succ fun n => by
    rintro _ ⟨y, rfl⟩
    refine ⟨P n y, ?_⟩
    show (P (n + 1) * P n) y = P n y
    rw [hP.2.1 n]
  tendsto_id := hP.2.2

/-- Nonzero resolvent eigenvectors with eigenvalue `(l - i)⁻¹`, `l ∈ B`, lie in `1_B(D) H`. -/
theorem mem_spectralSubspace_of_resolvent_eigen (S : MarkedCompactTriple A H ι) {B : Set ℝ}
    {l : ℝ} (hl : l ∈ B) {x : H}
    (hx : x ∈ Module.End.eigenspace S.resolvent.toLinearMap (((l : ℂ) - Complex.I)⁻¹)) :
    x ∈ S.spectralSubspace B := by
  have hne : (l : ℂ) - Complex.I ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
  have hRx : S.resolvent x = ((l : ℂ) - Complex.I)⁻¹ • x := Module.End.mem_eigenspace_iff.mp hx
  have hxD : x ∈ S.dirac.domain := resolventEigenspace_le_diracDomain S.toSpectralTriple _ hx
  have hD := dirac_apply_of_resolvent_eigen S.toSpectralTriple hRx (inv_ne_zero hne) hxD
  rw [inv_inv, sub_add_cancel] at hD
  exact Submodule.subset_span ⟨hxD, l, hl, hD⟩

/-- **Finite-dimensional spectral subspaces are finite resolvent screens**: if `1_B(D) H` is
finite-dimensional then it is the sum of finitely many resolvent eigenspaces. -/
theorem exists_finset_spectralSubspace_eq (S : MarkedCompactTriple A H ι) (B : Set ℝ)
    [FiniteDimensional ℂ (S.spectralSubspace B)] :
    ∃ s : Finset ℂ, S.spectralSubspace B = spectralScreenSubspace S.resolvent s := by
  classical
  let R : Module.End ℂ H := S.resolvent.toLinearMap
  let E : Set ℂ := {μ | ∃ l ∈ B, μ = ((l : ℂ) - Complex.I)⁻¹ ∧ Module.End.eigenspace R μ ≠ ⊥}
  have hv : ∀ μ : E, ∃ v, R.HasEigenvector μ v := by
    rintro ⟨μ, l, hl, rfl, hne⟩
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact ⟨v, Module.End.hasEigenvector_iff.mpr ⟨hv, hv0⟩⟩
  choose v hvE using hv
  have hlin : LinearIndependent ℂ v := Module.End.eigenvectors_linearIndependent R E v hvE
  have hvmem : ∀ μ : E, v μ ∈ S.spectralSubspace B := by
    intro μ
    obtain ⟨l, hl, hμl, -⟩ := μ.2
    have h1 := (Module.End.hasEigenvector_iff.mp (hvE μ)).1
    rw [hμl] at h1
    exact mem_spectralSubspace_of_resolvent_eigen S hl h1
  let v' : E → S.spectralSubspace B := fun μ => ⟨v μ, hvmem μ⟩
  have hlin' : LinearIndependent ℂ v' :=
    LinearIndependent.of_comp (S.spectralSubspace B).subtype hlin
  have hfin : E.Finite := Set.finite_coe_iff.mp hlin'.finite
  refine ⟨hfin.toFinset, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.mpr ?_
    rintro x ⟨hxD, l, hl, hD⟩
    by_cases hx0 : x = 0
    · rw [hx0]; exact Submodule.zero_mem _
    have hR := resolvent_apply_of_dirac_eigen S.toSpectralTriple hxD hD
    have hxe : x ∈ Module.End.eigenspace R (((l : ℂ) - Complex.I)⁻¹) :=
      Module.End.mem_eigenspace_iff.mpr hR
    have hmem : ((l : ℂ) - Complex.I)⁻¹ ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact ⟨l, hl, rfl, fun hbot => hx0 (by rw [hbot] at hxe; exact hxe)⟩
    exact Finset.le_sup (f := fun μ => Module.End.eigenspace R μ) hmem hxe
  · refine Finset.sup_le fun μ hμ => ?_
    rw [Set.Finite.mem_toFinset] at hμ
    obtain ⟨l, hl, rfl, -⟩ := hμ
    exact fun x hx => mem_spectralSubspace_of_resolvent_eigen S hl hx

/-- A star projection fixes its range. -/
theorem isStarProjection_apply_of_mem_range {P : H →L[ℂ] H} (hP : IsStarProjection P) {y : H}
    (hy : y ∈ LinearMap.range P.toLinearMap) : P y = y := by
  obtain ⟨z, rfl⟩ := hy
  show (P * P) z = P z
  rw [hP.isIdempotentElem.eq]

/-- Every spectral projection sequence of a marked compact triple is a sequence of finite
resolvent screens in the sense of `SpectralCompressionsSequential.lean`. -/
theorem isScreenSequence_of_spectralProjectionSequence {S : MarkedCompactTriple A H ι}
    (P : S.SpectralProjectionSequence) : IsScreenSequence S.toSpectralTriple P.P := by
  refine ⟨fun n => ?_, fun n => ?_, P.tendsto_id⟩
  · obtain ⟨hP, B, hB⟩ := P.spectral n
    have := P.finiteRank n
    rw [hB] at this
    obtain ⟨s, hs⟩ := exists_finset_spectralSubspace_eq S B
    refine ⟨s, (ContinuousLinearMap.IsStarProjection.ext_iff hP
      (ContinuousLinearMap.isStarProjection_iff_isSymmetricProjection.mpr
        (diracSpectralScreen_isSymmetricProjection _ _))).mpr ?_⟩
    change LinearMap.range (P.P n).toLinearMap = LinearMap.range (spectralScreen S.resolvent
      S.resolvent_isCompact (resolvent_injective S.toSpectralTriple) s).toLinearMap
    rw [spectralScreen_range, hB, hs]
  · ext x
    show P.P (n + 1) (P.P n x) = P.P n x
    exact isStarProjection_apply_of_mem_range (P.spectral (n + 1)).1
      (P.mono (Nat.le_succ n) (LinearMap.mem_range_self _ x))

/-- **Reconciliation**: commutator decay along a spectral projection sequence of
`def:reconstruction-categories` is exactly the spectral quasidiagonality
`SpectralCompressionsSequential.SpectrallyQuasidiagonal` under which `thm:spectral-compressions`
is proved. -/
theorem spectralCommutatorDecay_iff_spectrallyQuasidiagonal (X : CompactMarkedObject A ι) :
    SpectralCommutatorDecay X ↔ SpectrallyQuasidiagonal X.triple.toSpectralTriple := by
  constructor
  · rintro ⟨P, hP⟩
    exact ⟨P.P, isScreenSequence_of_spectralProjectionSequence P, hP⟩
  · rintro ⟨P, hP, hdec⟩
    exact ⟨ofScreenSequence X.triple P hP, hdec⟩

/-- **Norm line of `thm:essential-image`**: `EssIm(𝔖_cpt^{norm,cal})` is exactly the class of
spectrally quasidiagonal separable triples of `thm:spectral-compressions`. -/
theorem normReconstruction_essImage_iff_spectrallyQuasidiagonal (X : CompactMarkedObject A ι) :
    (normReconstruction (A := A) (ι := ι)).essImage X ↔
      SpectrallyQuasidiagonal X.triple.toSpectralTriple :=
  (normReconstruction_essImage_iff X).trans (spectralCommutatorDecay_iff_spectrallyQuasidiagonal X)

end Reconcile

/-! ### Properness: the Toeplitz object -/

section Toeplitz

open RenewalGeometry.ToeplitzScreenObstruction

/-- The Toeplitz smooth algebra `𝒜_D = alg(I, S, S*)`, used as coordinate algebra. -/
abbrev ToeplitzSmoothAlgebra : Type :=
  ↥(StarAlgebra.adjoin ℂ ({unilateralShift} : Set (ToeplitzScreenObstruction.H →L[ℂ]
    ToeplitzScreenObstruction.H)))

/-- The Toeplitz triple as a marked compact-resolvent triple: `alg(I, S, S*)` represented on
`ℓ²(ℕ)` by inclusion, the number operator as Dirac operator, `𝒜_D` the whole coordinate
algebra (so the density requirement holds trivially), no grading, no real structure, and
zero declared bounded marks. -/
def toeplitzMarkedTriple (ι : Type*) :
    MarkedCompactTriple ToeplitzSmoothAlgebra ToeplitzScreenObstruction.H ι where
  rep := (StarAlgebra.adjoin ℂ ({unilateralShift} : Set (ToeplitzScreenObstruction.H →L[ℂ]
    ToeplitzScreenObstruction.H))).subtype
  dirac := numberOperator
  dense_domain := numberOperator_dense_domain
  symmetric := toeplitz_numberOperator_symmetric
  compact_resolvent := toeplitzTriple.compact_resolvent
  smoothAlgebra := ⊤
  lipschitz a _ := toeplitzTriple.lipschitz a a.2
  smooth_dense a := subset_closure ⟨a, trivial, rfl⟩
  grading := none
  grading_spec g h := by cases h
  real := none
  real_dirac R h := by cases h
  real_grading R g h := by cases h
  mark _ := 0

/-- The Toeplitz object of `Spec_cpt^sep`. -/
abbrev toeplitzObject (ι : Type*) : CompactMarkedObject ToeplitzSmoothAlgebra ι where
  H := ToeplitzScreenObstruction.H
  triple := toeplitzMarkedTriple ι

/-- Every nonzero spectral projection of the Toeplitz triple has `‖[P, S]‖ ≥ 1`. -/
theorem toeplitzMarkedTriple_one_le_norm_commutator (ι : Type*)
    (P : (toeplitzMarkedTriple ι).SpectralProjectionSequence) (n : ℕ) (hn : P.P n ≠ 0) :
    1 ≤ ‖P.P n * unilateralShift - unilateralShift * P.P n‖ := by
  have := P.finiteRank n
  exact one_le_norm_commutator_of_finiteRank_idempotent_commutes_numberOperator (P.P n)
    (fun k => (P.commutes n _ (basisVector_mem_numberOperatorDomain k)).1)
    (fun k => (P.commutes n _ (basisVector_mem_numberOperatorDomain k)).2)
    (spectralProjectionSequence_idem P n) hn

/-- Along every spectral projection sequence of the Toeplitz triple, `‖[P_n, S]‖ ↛ 0`. -/
theorem toeplitzMarkedTriple_not_tendsto (ι : Type*)
    (P : (toeplitzMarkedTriple ι).SpectralProjectionSequence) :
    ¬ Tendsto (fun n => ‖P.P n * unilateralShift - unilateralShift * P.P n‖) atTop (𝓝 0) := by
  intro hS
  have hne : ∀ᶠ n in atTop, P.P n ≠ 0 := by
    filter_upwards [(P.tendsto_id (basisVector 0)).eventually (Metric.ball_mem_nhds _ one_pos)]
      with n hn hzero
    rw [hzero, ContinuousLinearMap.zero_apply] at hn
    rw [dist_zero_left, norm_basisVector] at hn
    exact lt_irrefl _ hn
  have hge : ∀ᶠ n in atTop, 1 ≤ ‖P.P n * unilateralShift - unilateralShift * P.P n‖ := by
    filter_upwards [hne] with n hn
    exact toeplitzMarkedTriple_one_le_norm_commutator ι P n hn
  have hlt := hS.eventually (gt_mem_nhds one_pos)
  obtain ⟨n, h1, h2⟩ := (hge.and hlt).exists
  exact absurd h1 (not_le.mpr h2)

/-- No spectral projection sequence of the Toeplitz triple has `‖[P_n, S]‖ → 0`. -/
theorem toeplitzObject_not_spectralCommutatorDecay (ι : Type*) :
    ¬ SpectralCommutatorDecay (toeplitzObject ι) := by
  intro h
  obtain ⟨P, hdec⟩ := h
  have h2 := hdec ⟨unilateralShift, StarAlgebra.subset_adjoin ℂ _ (Set.mem_singleton _)⟩
    trivial
  exact toeplitzMarkedTriple_not_tendsto ι P h2

/-- The Toeplitz object is not in the essential image of `𝔖_cpt^{norm,cal}`. -/
theorem toeplitzObject_not_essImage_norm (ι : Type*) :
    ¬ (normReconstruction (A := ToeplitzSmoothAlgebra) (ι := ι)).essImage (toeplitzObject ι) :=
  fun h => toeplitzObject_not_spectralCommutatorDecay ι ((normReconstruction_essImage_iff _).mp h)

/-- The Toeplitz object is not spectrally quasidiagonal (windowed, equivariant form). -/
theorem toeplitzObject_not_isSpectrallyQuasidiagonal (ι : Type*) :
    ¬ (toeplitzObject ι).triple.IsSpectrallyQuasidiagonal :=
  fun h => toeplitzObject_not_spectralCommutatorDecay ι
    (spectralCommutatorDecay_of_isSpectrallyQuasidiagonal h)

/-- The Toeplitz object is not spectrally quasidiagonal in the screen form of
`thm:spectral-compressions`. -/
theorem toeplitzObject_not_spectrallyQuasidiagonal (ι : Type*) :
    ¬ SpectrallyQuasidiagonal (toeplitzObject ι).triple.toSpectralTriple :=
  fun h => toeplitzObject_not_spectralCommutatorDecay ι
    ((spectralCommutatorDecay_iff_spectrallyQuasidiagonal _).mpr h)

end Toeplitz

/-! ### `thm:essential-image` -/

section Main

/-- **`thm:essential-image`** (Reconstruction classes and their essential images), with the
categories and reconstruction functors of `def:reconstruction-categories`:

1. `EssIm(𝔖_fin^cal) = Spec_fin`;
2. `EssIm(𝔖_cpt^{strong,cal}) = Spec_cpt^sep`;
3. `EssIm(𝔖_cpt^{norm,cal}) = Spec_cpt^sqd`, with spectral quasidiagonality in the form of
   `thm:spectral-compressions` (`SpectralCompressionsSequential.SpectrallyQuasidiagonal`:
   finite spectral screens `P_n ↑ I` with `‖[P_n, π(a)]‖ → 0` on `𝒜_D`); the windowed,
   `J`/`γ`-equivariant form `IsSpectrallyQuasidiagonal` is contained in this image;
4. the inclusion `Spec_cpt^sqd ⊊ Spec_cpt^sep` is strict: for every mark type the Toeplitz
   object lies in the strong but not in the norm essential image. -/
theorem essential_image {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    {ι : Type*} :
    (∀ S : FiniteMarkedObject A ι, (finiteReconstruction (A := A) (ι := ι)).essImage S) ∧
    (∀ X : CompactMarkedObject A ι, (strongReconstruction (A := A) (ι := ι)).essImage X) ∧
    (∀ X : CompactMarkedObject A ι, (normReconstruction (A := A) (ι := ι)).essImage X ↔
      SpectrallyQuasidiagonal X.triple.toSpectralTriple) ∧
    (∀ X : CompactMarkedObject A ι, X.triple.IsSpectrallyQuasidiagonal →
      (normReconstruction (A := A) (ι := ι)).essImage X) ∧
    ((strongReconstruction (A := ToeplitzSmoothAlgebra) (ι := ι)).essImage (toeplitzObject ι) ∧
      ¬ (normReconstruction (A := ToeplitzSmoothAlgebra) (ι := ι)).essImage
        (toeplitzObject ι) ∧
      ¬ SpectrallyQuasidiagonal (toeplitzObject ι).triple.toSpectralTriple) :=
  ⟨finiteReconstruction_essImage, strongReconstruction_essImage,
    normReconstruction_essImage_iff_spectrallyQuasidiagonal,
    fun _ h => isSpectrallyQuasidiagonal_essImage_norm h,
    strongReconstruction_essImage _, toeplitzObject_not_essImage_norm ι,
    toeplitzObject_not_spectrallyQuasidiagonal ι⟩

end Main

/-! ### `thm:summary-finite`, clauses (ii)–(iii) for marked triples -/

section Summary

open RenewalGeometry.MarkedCommutantCoordinates

/-- **`thm:summary-finite`, clauses (ii) (commutant fibre) and (iii)** for marked spectral
triples, with the categories of `def:reconstruction-categories`:

* (ii) a fixed commutator derivation (with the symmetry marks) determines the compatible Dirac
  operator exactly modulo the compatible commutant `c_S`;
* (iii) every finite marked triple carries injective real linear commutant coordinates with
  exactly `q_S = dim_ℝ c_S` components which, together with the represented commutator data,
  recover the triple; fewer than `q_S` coordinates never suffice;
* (iii) the three essential images `EssIm(𝔖_fin^cal) = Spec_fin`,
  `EssIm(𝔖_cpt^{strong,cal}) = Spec_cpt^sep`, `EssIm(𝔖_cpt^{norm,cal}) = Spec_cpt^sqd`
  (spectral quasidiagonality as in `thm:spectral-compressions`), and the strictness
  `Spec_cpt^sqd ⊊ Spec_cpt^sep` witnessed by the Toeplitz object. -/
theorem summary_finite_marked {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    {ι : Type*} :
    (∀ (K : Type) [Fintype K] [DecidableEq K] (S : MarkedFiniteSpectralTriple A K ι)
      (X : Matrix K K ℂ),
      S.IsCompatibleImplementer X ↔ ∃ C ∈ S.commutantSpace, X = S.dirac + C) ∧
    (∀ (K : Type) [Fintype K] [DecidableEq K] (S : MarkedFiniteSpectralTriple A K ι),
      ∃ α : S.CommutantCoordinateMap S.commutantDim, Function.Injective α ∧
        ∀ S' : MarkedFiniteSpectralTriple A K ι, S.SameCommutatorData S' →
          α (S.commutantProjectionMem S'.dirac) = α (S.commutantProjectionMem S.dirac) →
            S' = S) ∧
    (∀ (K : Type) [Fintype K] [DecidableEq K] (S : MarkedFiniteSpectralTriple A K ι) (m : ℕ),
      m < S.commutantDim → ∀ α : S.CommutantCoordinateMap m,
        ∃ S' : MarkedFiniteSpectralTriple A K ι, S.SameCommutatorData S' ∧ S' ≠ S ∧
          α (S.commutantProjectionMem S'.dirac) = α (S.commutantProjectionMem S.dirac)) ∧
    (∀ S : FiniteMarkedObject A ι, (finiteReconstruction (A := A) (ι := ι)).essImage S) ∧
    (∀ X : CompactMarkedObject A ι, (strongReconstruction (A := A) (ι := ι)).essImage X) ∧
    (∀ X : CompactMarkedObject A ι, (normReconstruction (A := A) (ι := ι)).essImage X ↔
      SpectrallyQuasidiagonal X.triple.toSpectralTriple) ∧
    ((strongReconstruction (A := ToeplitzSmoothAlgebra) (ι := ι)).essImage (toeplitzObject ι) ∧
      ¬ (normReconstruction (A := ToeplitzSmoothAlgebra) (ι := ι)).essImage
        (toeplitzObject ι)) := by
  refine ⟨fun K _ _ S X => S.isCompatibleImplementer_iff_exists X, fun K _ _ S => ?_,
    fun K _ _ S m hm α => S.finite_calibrated_recovery_sharp hm α,
    finiteReconstruction_essImage, strongReconstruction_essImage,
    normReconstruction_essImage_iff_spectrallyQuasidiagonal,
    strongReconstruction_essImage _, toeplitzObject_not_essImage_norm ι⟩
  obtain ⟨α, hα⟩ := exists_separating_coordinates (⟨K, S⟩ : FiniteMarkedObject A ι)
  exact ⟨α, hα, fun S' h hc => (S.finite_calibrated_recovery h).2.2 _ α hα hc⟩

end Summary

end RenewalGeometry.EssentialImageReconstruction
