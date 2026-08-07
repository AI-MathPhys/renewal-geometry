/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Global cylinder descent and compatible future forms
  (`thm:global-cylinder-descent`, `thm:compatible-future-forms`,
   Gran-Tensor manuscript)

* `polar_isometry_composition`: clause (G2) — the square-root
  polar isometries compose strictly:
  `W₁√R_m = √R_n J₁` and `W₂√R_n = √R_p J₂` give
  `(W₂W₁)√R_m = √R_p (J₂J₁)`, so the support-completed process
  algebras form the raw directed system;
* `innovation_gram_identity`: clause (G6), the boxed joint-source
  innovation identity — `S_{a,n}j_a = I S_{a,m} + η_a` with `I`
  isometric and `η ⊥ I𝓗_m` give
  `j_a* G_{ab,n} j_b = G_{ab,m} + η_a*η_b`;
* `exact_compression_of_zero_innovation`: the zero-innovation
  branch — vanishing innovations give exact joint-source
  compression `j_a* G_{ab,n} j_b = G_{ab,m}`;
* `compatible_form_isometry`: form compatibility
  `⟪ιa, ιb⟫ = ⟪a, b⟫` makes each connecting map isometric, so the
  stage norms cohere on the Hilbert direct limit;
* `bounded_action_of_uniform_bound`: the boxed module-bound
  criterion (sufficiency) — a uniform bound
  `‖L_a x‖ ≤ β·‖x‖` on a dense exhaustion `⋃ₘ D_m` extends to
  `‖L_a‖ ≤ β` on the limit;
* `uniform_bound_of_bounded_action`: necessity — a bounded limit
  action bounds every stage norm by `‖L_a‖`, so
  `β_𝔤(a) = sup_m ‖L_{ι(a)}‖ < ∞`.

Rendering disclosed: the reconstruction clauses (G1), (G3)–(G5),
(G7) (record surjections, rank-gain bookkeeping, tail ideal, and
the order-unit state extension) and the direct-limit completion
itself are the manuscript's cylinder bookkeeping; the strict
polar composition, the innovation Gram identity, and the
two-sided module-bound criterion are proved here.
-/

open Matrix

namespace NCG

section Cylinder

variable {s hm hn hp : Type*} [Fintype s] [Fintype hm]
  [Fintype hn] [Fintype hp] [DecidableEq hm]

omit [DecidableEq hm] in
/-- Clause (G2): strict composition of the square-root polar
isometries — `W₁√R_m = √R_n J₁` and `W₂√R_n = √R_p J₂` compose to
`(W₂W₁)√R_m = √R_p (J₂J₁)`. -/
theorem polar_isometry_composition
    (Rm : Matrix hm hm ℂ) (Rn : Matrix hn hn ℂ)
    (Rp : Matrix hp hp ℂ)
    (W₁ J₁ : Matrix hn hm ℂ) (W₂ J₂ : Matrix hp hn ℂ)
    (h₁ : W₁ * Rm = Rn * J₁) (h₂ : W₂ * Rn = Rp * J₂) :
    (W₂ * W₁) * Rm = Rp * (J₂ * J₁) := by
  calc (W₂ * W₁) * Rm
      = W₂ * (W₁ * Rm) := by rw [Matrix.mul_assoc]
    _ = W₂ * (Rn * J₁) := by rw [h₁]
    _ = (W₂ * Rn) * J₁ := by rw [Matrix.mul_assoc]
    _ = (Rp * J₂) * J₁ := by rw [h₂]
    _ = Rp * (J₂ * J₁) := by rw [Matrix.mul_assoc]

/-- Clause (G6), boxed: the joint-source innovation identity.
With `S_{a,n}j_a = I S_{a,m} + η_a`, `I` isometric, and both
innovations orthogonal to `I𝓗_m`, the compressed new Gram matrix
is the old Gram plus the innovation Gram:
`j_a* (S_{a,n}* S_{b,n}) j_b = S_{a,m}* S_{b,m} + η_a*η_b`. -/
theorem innovation_gram_identity
    (San Sbn ηa ηb : Matrix hn s ℂ) (Sam Sbm : Matrix hm s ℂ)
    (I : Matrix hn hm ℂ) (ja jb : Matrix s s ℂ)
    (hiso : Iᴴ * I = 1)
    (ha : San * ja = I * Sam + ηa)
    (hb : Sbn * jb = I * Sbm + ηb)
    (hoa : Iᴴ * ηa = 0) (hob : Iᴴ * ηb = 0) :
    jaᴴ * (Sanᴴ * Sbn) * jb = Samᴴ * Sbm + ηaᴴ * ηb := by
  have haI : ηaᴴ * I = 0 := by
    have := congrArg Matrix.conjTranspose hoa
    simpa [Matrix.conjTranspose_mul] using this
  have key : jaᴴ * (Sanᴴ * Sbn) * jb
      = (San * ja)ᴴ * (Sbn * jb) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [key, ha, hb]
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.add_mul, Matrix.mul_add]
  have h1 : Samᴴ * Iᴴ * (I * Sbm) = Samᴴ * Sbm := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Iᴴ I Sbm, hiso,
      Matrix.one_mul]
  have h2 : Samᴴ * Iᴴ * ηb = 0 := by
    rw [Matrix.mul_assoc, hob, Matrix.mul_zero]
  have h3 : ηaᴴ * (I * Sbm) = 0 := by
    rw [← Matrix.mul_assoc, haI, Matrix.zero_mul]
  rw [h1, h2, h3]
  abel

/-- Zero-innovation branch: exact joint-source compression. -/
theorem exact_compression_of_zero_innovation
    (San Sbn : Matrix hn s ℂ) (Sam Sbm : Matrix hm s ℂ)
    (I : Matrix hn hm ℂ) (ja jb : Matrix s s ℂ)
    (hiso : Iᴴ * I = 1)
    (ha : San * ja = I * Sam) (hb : Sbn * jb = I * Sbm) :
    jaᴴ * (Sanᴴ * Sbn) * jb = Samᴴ * Sbm := by
  have h := innovation_gram_identity San Sbn 0 0 Sam Sbm I ja jb
    hiso (by simpa using ha) (by simpa using hb)
    (Matrix.mul_zero _) (Matrix.mul_zero _)
  simpa using h

end Cylinder

section FutureForms

open scoped InnerProductSpace

/-- Compatible GNS forms make the connecting maps isometric:
`⟪ιa, ιb⟫ = ⟪a, b⟫` gives `‖ιa‖ = ‖a‖`, so the stage norms cohere
on the direct limit. -/
theorem compatible_form_isometry
    {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B]
    (ι : A →ₗ[ℂ] B)
    (hcomp : ∀ a b : A, ⟪ι a, ι b⟫_ℂ = ⟪a, b⟫_ℂ) (a : A) :
    ‖ι a‖ = ‖a‖ := by
  have h := hcomp a a
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
    at h
  have h' : (‖ι a‖ : ℝ) ^ 2 = ‖a‖ ^ 2 := by exact_mod_cast h
  calc ‖ι a‖ = Real.sqrt (‖ι a‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖a‖ ^ 2) := by rw [h']
    _ = ‖a‖ := Real.sqrt_sq (norm_nonneg _)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Boxed module-bound criterion, sufficiency: the uniform stage
bound `β_𝔤(a) < ∞` extends the action boundedly to the direct
limit — a bound `‖T x‖ ≤ β‖x‖` on a dense exhaustion `⋃ₘ D_m`
gives `‖T‖ ≤ β`. -/
theorem bounded_action_of_uniform_bound (T : E →L[ℂ] E)
    (β : ℝ) (hβ : 0 ≤ β) (D : ℕ → Set E)
    (hdense : Dense (⋃ m, D m))
    (hbd : ∀ m, ∀ x ∈ D m, ‖T x‖ ≤ β * ‖x‖) : ‖T‖ ≤ β := by
  refine T.opNorm_le_bound hβ fun x => ?_
  have hx : x ∈ closure (⋃ m, D m) := hdense x
  have hclosed : IsClosed {y : E | ‖T y‖ ≤ β * ‖y‖} :=
    isClosed_le (by fun_prop) (by fun_prop)
  refine hclosed.closure_subset_iff.mpr ?_ hx
  rintro y hy
  rcases Set.mem_iUnion.mp hy with ⟨m, hm⟩
  exact hbd m y hm

/-- Necessity: a bounded limit action bounds every stage — each
`x` in any stage satisfies `‖T x‖ ≤ ‖T‖·‖x‖`, so
`β_𝔤(a) ≤ ‖L_a‖ < ∞`. -/
theorem uniform_bound_of_bounded_action (T : E →L[ℂ] E)
    (D : ℕ → Set E) :
    ∀ m, ∀ x ∈ D m, ‖T x‖ ≤ ‖T‖ * ‖x‖ :=
  fun _ x _ => T.le_opNorm x

end FutureForms

end NCG
