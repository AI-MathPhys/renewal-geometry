/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.SqrtPolar

/-!
# Positive-packet compact-orbit decomposition and the
  finite phase-free orbit audit
  (`thm:SM-positive-packet-orbit` and
  `cor:SM-finite-positive-packet-orbit`,
  Gran-Tensor manuscript)

* `sm_positive_packet_orbit` (finite control group): for
  a unitary representation `ρ` of a finite group and a
  positive packet `J ⪰ 0`, the orbit average
  `𝓕_J = |G|⁻¹ Σ_g ρ(g) J ρ(g)ᴴ`
  (i) is positive semidefinite,
  (ii) is exactly `ρ`-equivariant,
  (iii) obeys the boxed kernel/range law
      `𝓕_J x = 0 ⟺ ∀ g, J (ρ(g)ᴴ x) = 0` — the
      orthocomplement form of
      `Ran 𝓕_J = Span{ρ(g) Ran J}` —
  (iv) and the boxed exhaustion criterion: the orbit
      exhausts the carrier (`𝓕_J ≻ 0`) **iff** no
      nonzero vector is annihilated by the whole control
      orbit; a kernel vector is an explicit admissible
      direction the orbit misses.

* `sm_finite_positive_packet_orbit` (the boxed finite
  quadrature): the orbit average is an exact finite
  positive quadrature
  `𝓕_J = Σ_{ℓ<L} w_ℓ ρ(g_ℓ) J ρ(g_ℓ)ᴴ` with
  `L ≤ (dim 𝒟)² + 1` — Carathéodory inside the real
  Hermitian subspace, whose dimension is at most
  `(dim 𝒟)²` by the explicit diagonal/upper-triangle
  real coordinates.

The Haar-integral form for a continuous compact group
and the isotypic refinement
`𝓕_J = ⊕ d_λ⁻¹ I ⊗ B_λ(J)` with its frame-floor
formula (Schur's lemma on the multiplicity-free
decomposition) are the manuscript's compact/
representation layer; the finite clauses proved here are
its complete finite-orbit content.
-/

open Matrix Finset Module
open scoped ComplexOrder MatrixOrder

set_option linter.unusedDecidableInType false

namespace NCG

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Vanishing of the PSD form kills the vector. -/
private lemma psd_form_zero {J : Matrix n n ℂ}
    (hJ : J.PosSemidef) {y : n → ℂ}
    (h : star y ⬝ᵥ (J *ᵥ y) = 0) : J *ᵥ y = 0 := by
  have hg := gram_realization_inner (CFC.sqrt J) y y
  rw [sqrt_isHermitian, sqrt_mul_self_eq J hJ] at hg
  have h0 := dotProduct_star_self_eq_zero.mp (hg.trans h)
  exact (sqrt_mulVec_eq_zero_iff hJ y).mp h0

/-- `thm:SM-positive-packet-orbit` (finite control
group): positivity, equivariance, the boxed kernel/range
law, and the boxed exhaustion criterion. -/
theorem sm_positive_packet_orbit {G : Type*} [Group G]
    [Fintype G] (ρ : G → Matrix n n ℂ)
    (hρmul : ∀ g h, ρ (g * h) = ρ g * ρ h)
    (J : Matrix n n ℂ) (hJ : J.PosSemidef) :
    -- (i) the orbit average is PSD
    ((((Fintype.card G : ℂ))⁻¹ •
        ∑ g : G, ρ g * J * (ρ g)ᴴ).PosSemidef)
    -- (ii) exact equivariance
    ∧ (∀ h : G, ρ h * (((Fintype.card G : ℂ))⁻¹ •
          ∑ g : G, ρ g * J * (ρ g)ᴴ) * (ρ h)ᴴ
        = ((Fintype.card G : ℂ))⁻¹ •
          ∑ g : G, ρ g * J * (ρ g)ᴴ)
    -- (iii) the boxed kernel/range law
    ∧ (∀ x : n → ℂ,
        ((((Fintype.card G : ℂ))⁻¹ •
          ∑ g : G, ρ g * J * (ρ g)ᴴ) *ᵥ x = 0
        ↔ ∀ g : G, J *ᵥ ((ρ g)ᴴ *ᵥ x) = 0))
    -- (iv) the boxed exhaustion criterion
    ∧ ((∀ x : n → ℂ, x ≠ 0 →
          ∃ g : G, J *ᵥ ((ρ g)ᴴ *ᵥ x) ≠ 0)
        ↔ (((Fintype.card G : ℂ))⁻¹ •
            ∑ g : G, ρ g * J * (ρ g)ᴴ).PosDef) := by
  have hcne : ((Fintype.card G : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr
      Fintype.card_ne_zero
  have hscalar : (0 : ℂ) ≤ ((Fintype.card G : ℂ))⁻¹ := by
    rw [show ((Fintype.card G : ℂ))
      = (((Fintype.card G : ℝ)) : ℂ) by push_cast; rfl]
    rw [← Complex.ofReal_inv, Complex.zero_le_real]
    positivity
  -- the sum of orbit conjugations is PSD
  have hsum : (∑ g : G, ρ g * J * (ρ g)ᴴ).PosSemidef :=
    Matrix.posSemidef_sum Finset.univ
      (fun g _ => hJ.mul_mul_conjTranspose_same (ρ g))
  have hF : ((((Fintype.card G : ℂ))⁻¹ •
      ∑ g : G, ρ g * J * (ρ g)ᴴ)).PosSemidef :=
    hsum.smul hscalar
  -- the form expands over the orbit
  have hform : ∀ x : n → ℂ,
      star x ⬝ᵥ ((∑ g : G, ρ g * J * (ρ g)ᴴ) *ᵥ x)
      = ∑ g : G, star ((ρ g)ᴴ *ᵥ x) ⬝ᵥ
          (J *ᵥ ((ρ g)ᴴ *ᵥ x)) := by
    intro x
    rw [Matrix.sum_mulVec, dotProduct_sum]
    apply Finset.sum_congr rfl
    intro g _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [Matrix.dotProduct_mulVec (star x) (ρ g)]
    congr 1
    rw [Matrix.star_mulVec,
      Matrix.conjTranspose_conjTranspose]
  -- the boxed kernel law
  have hker : ∀ x : n → ℂ,
      ((((Fintype.card G : ℂ))⁻¹ •
        ∑ g : G, ρ g * J * (ρ g)ᴴ) *ᵥ x = 0
      ↔ ∀ g : G, J *ᵥ ((ρ g)ᴴ *ᵥ x) = 0) := by
    intro x
    constructor
    · intro hFx g
      have hform0 : star x ⬝ᵥ
          (((((Fintype.card G : ℂ))⁻¹ •
            ∑ g : G, ρ g * J * (ρ g)ᴴ)) *ᵥ x) = 0 := by
        rw [hFx, dotProduct_zero]
      rw [Matrix.smul_mulVec, dotProduct_smul,
        smul_eq_mul] at hform0
      have hsum0 : star x ⬝ᵥ
          ((∑ g : G, ρ g * J * (ρ g)ᴴ) *ᵥ x) = 0 := by
        rcases mul_eq_zero.mp hform0 with h | h
        · exact absurd h (inv_ne_zero hcne)
        · exact h
      rw [hform] at hsum0
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg
        (fun g _ => hJ.dotProduct_mulVec_nonneg
          ((ρ g)ᴴ *ᵥ x))).mp hsum0 g (Finset.mem_univ g)
      exact psd_form_zero hJ hterm
    · intro hall
      have hterms : ∀ g : G,
          (ρ g * J * (ρ g)ᴴ) *ᵥ x = 0 := by
        intro g
        rw [← Matrix.mulVec_mulVec,
          ← Matrix.mulVec_mulVec, hall g,
          Matrix.mulVec_zero]
      rw [Matrix.smul_mulVec, Matrix.sum_mulVec]
      rw [Finset.sum_congr rfl fun g _ => hterms g]
      simp only [Finset.sum_const_zero, smul_zero]
  refine ⟨hF, ?_, hker, ?_⟩
  · -- (ii) equivariance
    intro h
    have key : ∀ g : G,
        ρ h * (ρ g * J * (ρ g)ᴴ) * (ρ h)ᴴ
        = ρ (h * g) * J * (ρ (h * g))ᴴ := by
      intro g
      rw [hρmul, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    calc ρ h * (((Fintype.card G : ℂ))⁻¹ •
          ∑ g : G, ρ g * J * (ρ g)ᴴ) * (ρ h)ᴴ
        = ((Fintype.card G : ℂ))⁻¹ •
          (ρ h * (∑ g : G, ρ g * J * (ρ g)ᴴ)
            * (ρ h)ᴴ) := by
          rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = ((Fintype.card G : ℂ))⁻¹ •
          ∑ g : G, ρ h * (ρ g * J * (ρ g)ᴴ)
            * (ρ h)ᴴ := by
          rw [Finset.mul_sum, Finset.sum_mul]
      _ = ((Fintype.card G : ℂ))⁻¹ •
          ∑ g : G, ρ g * J * (ρ g)ᴴ := by
          congr 1
          exact Fintype.sum_equiv (Equiv.mulLeft h)
            _ _ (fun g => key g)
  · -- (iv) exhaustion criterion
    constructor
    · intro hex
      apply Matrix.PosDef.of_dotProduct_mulVec_pos hF.1
      intro x hx
      rcases eq_or_lt_of_le
          (hF.dotProduct_mulVec_nonneg x) with heq | hlt
      · exfalso
        have hFx : (((Fintype.card G : ℂ))⁻¹ •
            ∑ g : G, ρ g * J * (ρ g)ᴴ) *ᵥ x = 0 :=
          psd_form_zero hF heq.symm
        obtain ⟨g, hg⟩ := hex x hx
        exact hg ((hker x).mp hFx g)
      · exact hlt
    · intro hpd x hx
      by_contra hno
      push Not at hno
      have hFx : (((Fintype.card G : ℂ))⁻¹ •
          ∑ g : G, ρ g * J * (ρ g)ᴴ) *ᵥ x = 0 :=
        (hker x).mpr hno
      have := hpd.dotProduct_mulVec_pos hx
      rw [hFx, dotProduct_zero] at this
      exact lt_irrefl _ this

section Caratheodory

variable {d : ℕ}

/-- The Hermitian real coordinates: diagonal and upper
real parts, and strictly-upper imaginary parts. -/
private def hermCoords :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℝ]
      (Fin d × Fin d → ℝ) where
  toFun M p :=
    if p.1 ≤ p.2 then (M p.1 p.2).re
    else (M p.2 p.1).im
  map_add' M N := by
    funext p
    by_cases h : p.1 ≤ p.2 <;>
      simp [h, Matrix.add_apply]
  map_smul' r M := by
    funext p
    by_cases h : p.1 ≤ p.2 <;>
      simp [h, Matrix.smul_apply, Complex.real_smul]

/-- The Hermitian coordinates are injective on
self-adjoint matrices. -/
private lemma hermCoords_injective
    {M : Matrix (Fin d) (Fin d) ℂ}
    (hM : M.IsHermitian) (h : hermCoords M = 0) :
    M = 0 := by
  have hsym : ∀ i j, M j i = star (M i j) := by
    intro i j
    have h2 := congrFun (congrFun hM.eq i) j
    rw [Matrix.conjTranspose_apply] at h2
    have h3 := congrArg star h2
    rw [star_star] at h3
    exact h3
  ext i j
  rcases le_or_gt i j with hij | hij
  · -- upper entries: real part from `(i,j)`,
    -- imaginary part from `(j,i)` or hermiticity
    have hre := congrFun h (i, j)
    simp only [hermCoords, LinearMap.coe_mk,
      AddHom.coe_mk, if_pos hij, Pi.zero_apply] at hre
    rcases eq_or_lt_of_le hij with rfl | hlt
    · -- diagonal: imaginary part vanishes by
      -- hermiticity
      have hdiag := hsym i i
      have him : (M i i).im = 0 := by
        have := congrArg Complex.im hdiag
        simp only [Complex.star_def,
          Complex.conj_im] at this
        linarith
      apply Complex.ext
      · simpa using hre
      · simpa using him
    · have him := congrFun h (j, i)
      simp only [hermCoords, LinearMap.coe_mk,
        AddHom.coe_mk, if_neg (not_le.mpr hlt),
        Pi.zero_apply] at him
      apply Complex.ext
      · simpa using hre
      · simpa using him
  · -- lower entries by hermiticity
    have hupper : M j i = 0 := by
      have hre := congrFun h (j, i)
      have him := congrFun h (i, j)
      simp only [hermCoords, LinearMap.coe_mk,
        AddHom.coe_mk, if_pos (le_of_lt hij),
        if_neg (not_le.mpr hij),
        Pi.zero_apply] at hre him
      apply Complex.ext
      · simpa using hre
      · simpa using him
    rw [hsym j i, hupper]
    simp

/-- `cor:SM-finite-positive-packet-orbit` (the boxed
Carathéodory quadrature `L ≤ (dim 𝒟)² + 1`). -/
theorem sm_finite_positive_packet_orbit {G : Type*}
    [Group G] [Fintype G]
    (ρ : G → Matrix (Fin d) (Fin d) ℂ)
    (J : Matrix (Fin d) (Fin d) ℂ) (hJ : J.PosSemidef) :
    ∃ (L : ℕ) (w : Fin L → ℝ) (g : Fin L → G),
      L ≤ d ^ 2 + 1
      ∧ (∀ ℓ, 0 ≤ w ℓ) ∧ (∑ ℓ, w ℓ = 1)
      ∧ ((Fintype.card G : ℂ))⁻¹ •
          (∑ k : G, ρ k * J * (ρ k)ᴴ)
        = ∑ ℓ, w ℓ • (ρ (g ℓ) * J * (ρ (g ℓ))ᴴ) := by
  classical
  set S : Set (Matrix (Fin d) (Fin d) ℂ) :=
    Set.range fun k : G => ρ k * J * (ρ k)ᴴ with hS
  -- every orbit point is Hermitian
  have hSherm : ∀ M ∈ S, M.IsHermitian := by
    rintro M ⟨k, rfl⟩
    exact (hJ.mul_mul_conjTranspose_same (ρ k)).1
  -- the average lies in the convex hull of the orbit
  have hcardR : (0 : ℝ) < (Fintype.card G : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hmem : ((Fintype.card G : ℂ))⁻¹ •
      (∑ k : G, ρ k * J * (ρ k)ᴴ)
      ∈ convexHull ℝ S := by
    have hcm := Finset.centerMass_mem_convexHull
      (t := (Finset.univ : Finset G))
      (w := fun _ => ((Fintype.card G : ℝ))⁻¹)
      (z := fun k => ρ k * J * (ρ k)ᴴ)
      (fun _ _ => by positivity)
      (by
        rw [Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
        positivity)
      (fun k _ => show ρ k * J * (ρ k)ᴴ ∈ S from
        ⟨k, rfl⟩)
    have hcm' : (Finset.univ : Finset G).centerMass
        (fun _ => ((Fintype.card G : ℝ))⁻¹)
        (fun k => ρ k * J * (ρ k)ᴴ)
        = ((Fintype.card G : ℂ))⁻¹ •
          (∑ k : G, ρ k * J * (ρ k)ᴴ) := by
      rw [Finset.centerMass]
      rw [Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_inv_cancel₀
          (ne_of_gt (by positivity)),
        inv_one, one_smul, ← Finset.smul_sum]
      ext i j
      simp only [Matrix.smul_apply, Complex.real_smul]
      push_cast
      ring
    rw [← hcm']
    exact hcm
  -- Carathéodory: an affinely independent sub-quadrature
  rw [convexHull_eq_union] at hmem
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨t, hts, hai, hFt⟩ := hmem
  -- the cardinality bound through the Hermitian subspace
  have htcard : t.card ≤ d ^ 2 + 1 := by
    rcases Finset.eq_empty_or_nonempty t with rfl | hne
    · simp
    · haveI : Nonempty ↥t := hne.to_subtype
      have h1 := hai.finrank_vectorSpan_add_one
      rw [Fintype.card_coe] at h1
      -- the vector span sits inside the Hermitian
      -- subspace, whose rank is at most `d²`
      set W : Submodule ℝ (Matrix (Fin d) (Fin d) ℂ) :=
        selfAdjoint.submodule ℝ
          (Matrix (Fin d) (Fin d) ℂ) with hW
      have hWle : vectorSpan ℝ
          (Set.range ((↑) : ↥t →
            Matrix (Fin d) (Fin d) ℂ)) ≤ W := by
        rw [vectorSpan_def, Submodule.span_le]
        rintro v ⟨a, ha, b, hb, rfl⟩
        rw [Subtype.range_coe] at ha hb
        have haS := hSherm a (hts ha)
        have hbS := hSherm b (hts hb)
        have hsa : IsSelfAdjoint (a - b) := by
          have h5 : (a - b)ᴴ = a - b := by
            rw [Matrix.conjTranspose_sub, haS.eq,
              hbS.eq]
          exact h5
        simp only [vsub_eq_sub]
        exact hsa
      have hWrank : finrank ℝ W ≤ d ^ 2 := by
        have hinj : Function.Injective
            ((hermCoords).comp W.subtype) := by
          intro x y hxy
          apply Subtype.ext
          have hdiff : hermCoords
              (W.subtype x - W.subtype y) = 0 := by
            rw [map_sub]
            simp only [LinearMap.comp_apply] at hxy
            rw [sub_eq_zero]
            exact hxy
          have hherm :
              (W.subtype x - W.subtype y).IsHermitian := by
            have hx : IsSelfAdjoint (W.subtype x) := x.2
            have hy : IsSelfAdjoint (W.subtype y) := y.2
            have h5 : (W.subtype x - W.subtype y)ᴴ
                = W.subtype x - W.subtype y := by
              rw [Matrix.conjTranspose_sub,
                ← Matrix.star_eq_conjTranspose,
                ← Matrix.star_eq_conjTranspose,
                hx.star_eq, hy.star_eq]
            exact h5
          have := hermCoords_injective hherm hdiff
          exact sub_eq_zero.mp this
        calc finrank ℝ W
            ≤ finrank ℝ (Fin d × Fin d → ℝ) :=
              LinearMap.finrank_le_finrank_of_injective
                hinj
          _ = d ^ 2 := by
              rw [finrank_pi]
              simp [sq]
      have h2 : finrank ℝ (vectorSpan ℝ
          (Set.range ((↑) : ↥t →
            Matrix (Fin d) (Fin d) ℂ)))
          ≤ d ^ 2 :=
        le_trans (Submodule.finrank_mono hWle) hWrank
      omega
  -- extract the weights on the finite quadrature
  rw [Finset.convexHull_eq] at hFt
  obtain ⟨w, hw0, hw1, hwc⟩ := hFt
  rw [Finset.centerMass_eq_of_sum_1 _ _ hw1] at hwc
  -- choose orbit representatives for the points of `t`
  have hrep : ∀ y : ↥t, ∃ k : G,
      ρ k * J * (ρ k)ᴴ = (y : Matrix _ _ ℂ) := by
    intro y
    have := hts y.2
    rw [hS] at this
    obtain ⟨k, hk⟩ := this
    exact ⟨k, hk⟩
  choose rep hrep' using hrep
  -- reindex along `Fin t.card`
  refine ⟨t.card,
    fun ℓ => w ((t.equivFin.symm ℓ : ↥t) :
      Matrix (Fin d) (Fin d) ℂ),
    fun ℓ => rep (t.equivFin.symm ℓ),
    htcard, ?_, ?_, ?_⟩
  · intro ℓ
    exact hw0 _ (t.equivFin.symm ℓ).2
  · calc (∑ ℓ : Fin t.card,
        w ((t.equivFin.symm ℓ : ↥t) :
          Matrix (Fin d) (Fin d) ℂ))
        = ∑ y : ↥t, w (y : Matrix (Fin d) (Fin d) ℂ) :=
          Equiv.sum_comp t.equivFin.symm
            (fun y : ↥t => w (y : Matrix _ _ ℂ))
      _ = ∑ y ∈ t, w y :=
          Finset.sum_coe_sort t (fun y => w y)
      _ = 1 := hw1
  · rw [← hwc]
    simp only [id_eq]
    calc (∑ y ∈ t, w y • y)
        = ∑ y : ↥t, w (y : Matrix (Fin d) (Fin d) ℂ)
            • (y : Matrix (Fin d) (Fin d) ℂ) :=
          (Finset.sum_coe_sort t
            (fun y => w y • y)).symm
      _ = ∑ ℓ : Fin t.card,
            w ((t.equivFin.symm ℓ : ↥t) :
              Matrix (Fin d) (Fin d) ℂ)
            • ((t.equivFin.symm ℓ : ↥t) :
              Matrix (Fin d) (Fin d) ℂ) :=
          (Equiv.sum_comp t.equivFin.symm
            (fun y : ↥t =>
              w (y : Matrix (Fin d) (Fin d) ℂ)
              • (y : Matrix (Fin d) (Fin d) ℂ))).symm
      _ = _ := by
          apply Finset.sum_congr rfl
          intro ℓ _
          rw [hrep']

end Caratheodory

end NCG
