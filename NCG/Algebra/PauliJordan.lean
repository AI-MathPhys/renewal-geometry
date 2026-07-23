/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Algebra.SpinFactor

/-!
# The Pauli isomorphism `JSpin(ℝ³) ≅ M₂(ℂ)_sa`

The rank-two classification endpoint of
`thm:two-path-complex-face` (`manuscripts/renewal_emergence/renewal_emergence.tex`): the
three-dimensional spin factor is Jordan-isomorphic to the Hermitian
`2 × 2` complex matrices with the symmetrized product
`A ∘ B = ½(AB + BA)`.

The isomorphism is the Pauli parametrization

`φ(s, v) = s·1 + v₀σ₁ + v₁σ₂ + v₂σ₃
        = !![s + v₂, v₀ − i v₁; v₀ + i v₁, s − v₂]`.

* `pauliMap_hermitian` — the image is Hermitian;
* `pauliMap_surj_hermitian` — every Hermitian matrix arises;
* `pauliMap_injective` — the parametrization is injective;
* `pauliMap_one` — `φ(1) = 1`;
* `pauliMap_add` / `pauliMap_smul` — real linearity;
* `pauliMap_spinMul` — **the Jordan isomorphism law**
  `φ(x ∘ y) = ½(φx·φy + φy·φx)`, by the Pauli anticommutation
  relations.

Together with `NCG/Algebra/SpinFactor.lean` this realizes the unique
rank-two Euclidean Jordan algebra with two-dimensional coherence
space concretely as `M₂(ℂ)_sa`.
-/

namespace NCG.Jordan

open Matrix RealInnerProductSpace

/-- The symmetrized (Jordan) matrix product. -/
noncomputable def jordanMul (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (A * B + B * A)

/-- The Pauli parametrization of the three-dimensional spin
factor. -/
noncomputable def pauliMap (x : ℝ × EuclideanSpace ℝ (Fin 3)) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![(x.1 : ℂ) + (x.2 2 : ℝ),
      (x.2 0 : ℝ) - (x.2 1 : ℝ) * Complex.I;
     (x.2 0 : ℝ) + (x.2 1 : ℝ) * Complex.I,
      (x.1 : ℂ) - (x.2 2 : ℝ)]

/-- The image of the Pauli parametrization is Hermitian. -/
theorem pauliMap_hermitian (x : ℝ × EuclideanSpace ℝ (Fin 3)) :
    (pauliMap x)ᴴ = pauliMap x := by
  unfold pauliMap
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, Complex.ext_iff]

/-- `φ(1) = 1`. -/
theorem pauliMap_one :
    pauliMap (spinOne : ℝ × EuclideanSpace ℝ (Fin 3)) = 1 := by
  unfold pauliMap spinOne
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp []

/-- Real additivity. -/
theorem pauliMap_add (x y : ℝ × EuclideanSpace ℝ (Fin 3)) :
    pauliMap (x + y) = pauliMap x + pauliMap y := by
  unfold pauliMap
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Prod.fst_add, Prod.snd_add, Complex.ext_iff] <;> ring

/-- Injectivity of the Pauli parametrization. -/
theorem pauliMap_injective : Function.Injective
    (pauliMap : ℝ × EuclideanSpace ℝ (Fin 3) → _) := by
  intro x y h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h11 := congrFun (congrFun h 1) 1
  simp only [pauliMap, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val',
    Matrix.empty_val', Matrix.cons_val_fin_one,
    Complex.ext_iff, Complex.add_re,
    Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one,
    sub_zero, add_zero, zero_sub] at h00 h01 h11
  obtain ⟨ha, -⟩ := h00
  obtain ⟨hb, -⟩ := h11
  obtain ⟨hc, hd⟩ := h01
  have hs : x.1 = y.1 := by linarith
  refine Prod.ext hs ?_
  ext i
  fin_cases i
  · change x.2 0 = y.2 0
    linarith
  · change x.2 1 = y.2 1
    have hd' : -(x.2 1) = -(y.2 1) := by
      simpa using hd
    linarith
  · change x.2 2 = y.2 2
    linarith

/-- Surjectivity onto the Hermitian matrices. -/
theorem pauliMap_surj_hermitian (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : Aᴴ = A) :
    ∃ x : ℝ × EuclideanSpace ℝ (Fin 3), pauliMap x = A := by
  have h00 := congrFun (congrFun hA 0) 0
  have h11 := congrFun (congrFun hA 1) 1
  have h01 := congrFun (congrFun hA 0) 1
  rw [Matrix.conjTranspose_apply] at h00 h11 h01
  have him00 : (A 0 0).im = 0 := by
    have h1 := congrArg Complex.im h00
    rw [Complex.star_def, Complex.conj_im] at h1
    linarith
  have him11 : (A 1 1).im = 0 := by
    have h1 := congrArg Complex.im h11
    rw [Complex.star_def, Complex.conj_im] at h1
    linarith
  have hre01 : (A 0 1).re = (A 1 0).re := by
    have h1 := congrArg Complex.re h01
    rw [Complex.star_def, Complex.conj_re] at h1
    exact h1.symm
  have him01 : (A 0 1).im = -(A 1 0).im := by
    have h1 := congrArg Complex.im h01
    rw [Complex.star_def, Complex.conj_im] at h1
    exact h1.symm
  refine ⟨(((A 0 0).re + (A 1 1).re) / 2,
    WithLp.toLp 2 ![(A 1 0).re, (A 1 0).im,
      ((A 0 0).re - (A 1 1).re) / 2]), ?_⟩
  unfold pauliMap
  conv_rhs => rw [Matrix.eta_fin_two A]
  ext i j
  fin_cases i <;> fin_cases j <;>
  · simp only [Fin.zero_eta, Fin.mk_one, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
      ]
    rw [Complex.ext_iff]
    constructor <;>
    · try simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
        him00, him11, hre01, him01, mul_zero,
        mul_one, sub_zero, add_zero, zero_add, zero_sub,
        ]
      try ring
      try rfl

/-- **The Jordan isomorphism law**: the Pauli parametrization turns
the spin product into the symmetrized matrix product —
`φ(x ∘ y) = ½(φx·φy + φy·φx)`, by the Pauli anticommutation
relations `σᵢσⱼ + σⱼσᵢ = 2δᵢⱼ`. -/
theorem pauliMap_spinMul (x y : ℝ × EuclideanSpace ℝ (Fin 3)) :
    pauliMap (spinMul x y) = jordanMul (pauliMap x) (pauliMap y) := by
  obtain ⟨s, v⟩ := x
  obtain ⟨t, w⟩ := y
  have hinner : ⟪(v : EuclideanSpace ℝ (Fin 3)), w⟫
      = v 0 * w 0 + v 1 * w 1 + v 2 * w 2 := by
    rw [PiLp.inner_apply, Fin.sum_univ_three]
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
    ring
  unfold jordanMul
  rw [show (1 / 2 : ℂ) = (2 : ℂ)⁻¹ by norm_num, eq_comm,
    inv_smul_eq_iff₀ (by norm_num : (2 : ℂ) ≠ 0)]
  unfold pauliMap spinMul
  ext i j
  fin_cases i <;> fin_cases j <;>
  · simp only [hinner, Matrix.smul_apply, Matrix.add_apply,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
      PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul]
    rw [Complex.ext_iff]
    push_cast
    constructor <;>
    · simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
      ring

end NCG.Jordan
