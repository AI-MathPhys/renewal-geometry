/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Spectralization.CanonicalFiniteDiracExact
import RenewalGeometry.Commutant.FiniteAnchorOperatorNormExact

/-!
# Finite-Dirac relation space and fixed-generator closure
  (`def:finite-dirac-relation-space`, `prop:finite-dirac`)

`def:finite-dirac-relation-space` and `prop:finite-dirac` of the spacetime–gauge duality
manuscript.  On the common carrier `ℂ^n` with grading `Γ` and a typed resolution of the
identity `(P_t)_t`, the represented relations are a declared set `Rel` of typed pairs
`(t, t')` (the fermionic Yukawa incidence relations determined by the matter packet, together
with the declared Majorana relation `(ν, ν)` when the neutral and charge-conjugate sectors are
represented; `Rel` is data of the packet and is only required to be symmetric).

* `relationSpace Γ P Rel` = `𝔇_F`: the linear subspace of the Hilbert–Schmidt space
  `EuclideanSpace ℂ (n × n)` (realized through `matrixL2`/`l2Matrix`) of grading-odd operators
  `Γ X Γ = −X` whose typed blocks `P_t X P_{t'}` vanish off `Rel`;
* `relationSpace_star_mem`: `𝔇_F` is `*`-closed (for symmetric `Rel`); it is
  finite-dimensional (`instFiniteDimensional_relationSpace`);
* `relationProjection` = `Π_F^D`, the Hilbert–Schmidt orthogonal projection onto `𝔇_F`
  (`Submodule.starProjection`);
* `canonicalFiniteDirac` = `D_F^can = Π_F^D D̃_F` and
  `relationDefect` = `Δ_F^rel = ‖(I − Π_F^D) D̃_F‖²_HS` (`eq:finite-dirac-relation-defect`);
* `finiteDirac_eq_canonical_iff`: **`eq:finite-dirac-exact-relation`**
  `D̃_F = D_F^can ⟺ Δ_F^rel = 0`;
* `infDist_finiteDirac_relationSpace`: **`eq:finite-dirac-distance`**
  `dist_HS(D̃_F, 𝔇_F) = √Δ_F^rel`;
* `nonzero_admitted_of_relationDefect_zero`: if `Δ_F^rel = 0` and `‖D_F^can‖_HS > 0`, the
  complete odd component of the generator is a nonzero admitted (relation-supported) operator;
* `canonicalFiniteDirac_typed_blocks`: the typed coefficient blocks
  `P_t D_F^can P_{t'}` recover `D_F^can`, vanish off the declared relations, and `D_F^can` is
  grading-odd;
* `fixed_generator_finite_dirac_closure`: the assembled `prop:finite-dirac`.

Rendering disclosed: the generation-frame sentences of `prop:finite-dirac` ("in any generation
factorization of `thm:common-generation-factor` the typed blocks are ordinary generation
matrices, expressed in the common frame under the common-ancestry conditions") are
cross-references to that proposition's coordinate identifications and are not restated here;
the typed blocks are exhibited as matrices `P_t D_F^can P_{t'}`.  The remark that
odd-provenance completeness is not required is reflected in the absence of any such
hypothesis.
-/

open Matrix

namespace RenewalGeometry
namespace CanonicalFiniteDirac

variable {n : Type*} [Fintype n] [DecidableEq n] {τ : Type*}

@[simp] theorem l2Matrix_zero {m k : Type*} [Fintype m] [Fintype k] :
    l2Matrix (0 : EuclideanSpace ℂ (m × k)) = 0 := by
  ext i j
  simp [l2Matrix]

theorem l2Matrix_sub {m k : Type*} [Fintype m] [Fintype k] (x y : EuclideanSpace ℂ (m × k)) :
    l2Matrix (x - y) = l2Matrix x - l2Matrix y := by
  ext i j
  simp [l2Matrix]

@[simp] theorem matrixL2_zero {m k : Type*} [Fintype m] [Fintype k] :
    matrixL2 (0 : Matrix m k ℂ) = 0 := by
  ext ij
  simp [matrixL2]

/-- **`def:finite-dirac-relation-space`**: the finite-Dirac relation space `𝔇_F`, the linear
subspace of the Hilbert–Schmidt space of grading-odd operators whose typed blocks are supported
only on the declared relation set `Rel`. -/
def relationSpace (Γ : Matrix n n ℂ) (P : τ → Matrix n n ℂ) (Rel : Set (τ × τ)) :
    Submodule ℂ (EuclideanSpace ℂ (n × n)) where
  carrier := {x | Γ * l2Matrix x * Γ = -l2Matrix x ∧
    ∀ t t', (t, t') ∉ Rel → P t * l2Matrix x * P t' = 0}
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨?_, fun t t' h => ?_⟩
    · rw [l2Matrix_add, Matrix.mul_add, Matrix.add_mul, hx1, hy1, neg_add]
    · rw [l2Matrix_add, Matrix.mul_add, Matrix.add_mul, hx2 t t' h, hy2 t t' h, add_zero]
  zero_mem' := by
    refine ⟨?_, fun t t' _ => ?_⟩ <;> simp
  smul_mem' := by
    rintro a x ⟨hx1, hx2⟩
    refine ⟨?_, fun t t' h => ?_⟩
    · rw [l2Matrix_smul, Matrix.mul_smul, Matrix.smul_mul, hx1, smul_neg]
    · rw [l2Matrix_smul, Matrix.mul_smul, Matrix.smul_mul, hx2 t t' h, smul_zero]

theorem mem_relationSpace_iff (Γ : Matrix n n ℂ) (P : τ → Matrix n n ℂ) (Rel : Set (τ × τ))
    (x : EuclideanSpace ℂ (n × n)) :
    x ∈ relationSpace Γ P Rel ↔
      Γ * l2Matrix x * Γ = -l2Matrix x ∧
        ∀ t t', (t, t') ∉ Rel → P t * l2Matrix x * P t' = 0 :=
  Iff.rfl

/-- `𝔇_F` is `*`-closed: for self-adjoint `Γ`, self-adjoint type projectors and a symmetric
relation set, the adjoint of a relation-supported odd operator is relation-supported and odd. -/
theorem relationSpace_star_mem (Γ : Matrix n n ℂ) (hΓ : Γᴴ = Γ) (P : τ → Matrix n n ℂ)
    (hP : ∀ t, (P t)ᴴ = P t) (Rel : Set (τ × τ))
    (hRel : ∀ t t', (t, t') ∈ Rel → (t', t) ∈ Rel)
    {x : EuclideanSpace ℂ (n × n)} (hx : x ∈ relationSpace Γ P Rel) :
    matrixL2 (l2Matrix x)ᴴ ∈ relationSpace Γ P Rel := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨?_, fun t t' h => ?_⟩
  · rw [l2Matrix_matrixL2]
    have := congrArg Matrix.conjTranspose h1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hΓ, Matrix.conjTranspose_neg] at this
    simpa only [Matrix.mul_assoc] using this
  · rw [l2Matrix_matrixL2]
    have h' : (t', t) ∉ Rel := fun hm => h (hRel t' t hm)
    have := congrArg Matrix.conjTranspose (h2 t' t h')
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hP, hP,
      Matrix.conjTranspose_zero] at this
    simpa only [Matrix.mul_assoc] using this

/-- `𝔇_F` is finite-dimensional. -/
instance instFiniteDimensional_relationSpace (Γ : Matrix n n ℂ) (P : τ → Matrix n n ℂ)
    (Rel : Set (τ × τ)) : FiniteDimensional ℂ (relationSpace Γ P Rel) :=
  inferInstance

/-- `Π_F^D`: the Hilbert–Schmidt orthogonal projection onto `𝔇_F`. -/
noncomputable def relationProjection (Γ : Matrix n n ℂ) (P : τ → Matrix n n ℂ)
    (Rel : Set (τ × τ)) : EuclideanSpace ℂ (n × n) →L[ℂ] EuclideanSpace ℂ (n × n) :=
  (relationSpace Γ P Rel).starProjection

/-- The projected generator `Π_F^D D̃_F` in the Hilbert–Schmidt space. -/
noncomputable def canonicalFiniteDiracL2 (Γ : Matrix n n ℂ) (P : τ → Matrix n n ℂ)
    (Rel : Set (τ × τ)) (A : Matrix n n ℂ) : EuclideanSpace ℂ (n × n) :=
  relationProjection Γ P Rel (matrixL2 (finiteDirac Γ A))

/-- `D_F^can = Π_F^D D̃_F` as a matrix (`eq:finite-dirac-relation-defect`). -/
noncomputable def canonicalFiniteDirac (Γ : Matrix n n ℂ) (P : τ → Matrix n n ℂ)
    (Rel : Set (τ × τ)) (A : Matrix n n ℂ) : Matrix n n ℂ :=
  l2Matrix (canonicalFiniteDiracL2 Γ P Rel A)

/-- `Δ_F^rel = ‖(I − Π_F^D) D̃_F‖²_HS` (`eq:finite-dirac-relation-defect`). -/
noncomputable def relationDefect (Γ : Matrix n n ℂ) (P : τ → Matrix n n ℂ)
    (Rel : Set (τ × τ)) (A : Matrix n n ℂ) : ℝ :=
  ‖matrixL2 (finiteDirac Γ A) - canonicalFiniteDiracL2 Γ P Rel A‖ ^ 2

theorem relationDefect_nonneg (Γ : Matrix n n ℂ) (P : τ → Matrix n n ℂ) (Rel : Set (τ × τ))
    (A : Matrix n n ℂ) : 0 ≤ relationDefect Γ P Rel A :=
  sq_nonneg _

/-- The projected generator lies in `𝔇_F`. -/
theorem canonicalFiniteDiracL2_mem (Γ : Matrix n n ℂ) (P : τ → Matrix n n ℂ)
    (Rel : Set (τ × τ)) (A : Matrix n n ℂ) :
    canonicalFiniteDiracL2 Γ P Rel A ∈ relationSpace Γ P Rel :=
  Submodule.starProjection_apply_mem _ _

/-- `D̃_F = D_F^can` in matrix form iff in Hilbert–Schmidt form. -/
theorem finiteDirac_eq_canonical_iff_L2 (Γ : Matrix n n ℂ) (P : τ → Matrix n n ℂ)
    (Rel : Set (τ × τ)) (A : Matrix n n ℂ) :
    finiteDirac Γ A = canonicalFiniteDirac Γ P Rel A ↔
      matrixL2 (finiteDirac Γ A) = canonicalFiniteDiracL2 Γ P Rel A := by
  constructor
  · intro h
    rw [h, canonicalFiniteDirac, matrixL2_l2Matrix]
  · intro h
    rw [canonicalFiniteDirac, ← h, l2Matrix_matrixL2]

/-- **`eq:finite-dirac-exact-relation`.**  `D̃_F = D_F^can ⟺ Δ_F^rel = 0`; equivalently
`D̃_F ∈ 𝔇_F`. -/
theorem finiteDirac_eq_canonical_iff (Γ : Matrix n n ℂ) (P : τ → Matrix n n ℂ)
    (Rel : Set (τ × τ)) (A : Matrix n n ℂ) :
    finiteDirac Γ A = canonicalFiniteDirac Γ P Rel A ↔ relationDefect Γ P Rel A = 0 := by
  rw [finiteDirac_eq_canonical_iff_L2, relationDefect, sq_eq_zero_iff, norm_eq_zero,
    sub_eq_zero]

/-- `Δ_F^rel = 0` exactly when `D̃_F` lies in the relation space. -/
theorem relationDefect_eq_zero_iff_mem (Γ : Matrix n n ℂ) (P : τ → Matrix n n ℂ)
    (Rel : Set (τ × τ)) (A : Matrix n n ℂ) :
    relationDefect Γ P Rel A = 0 ↔ matrixL2 (finiteDirac Γ A) ∈ relationSpace Γ P Rel := by
  rw [relationDefect, sq_eq_zero_iff, norm_eq_zero, sub_eq_zero, eq_comm]
  exact Submodule.starProjection_eq_self_iff

/-- **`eq:finite-dirac-distance`.**  `dist_HS(D̃_F, 𝔇_F) = √Δ_F^rel`. -/
theorem infDist_finiteDirac_relationSpace (Γ : Matrix n n ℂ) (P : τ → Matrix n n ℂ)
    (Rel : Set (τ × τ)) (A : Matrix n n ℂ) :
    Metric.infDist (matrixL2 (finiteDirac Γ A)) (relationSpace Γ P Rel : Set _) =
      Real.sqrt (relationDefect Γ P Rel A) := by
  rw [relationDefect, Real.sqrt_sq (norm_nonneg _), canonicalFiniteDiracL2, relationProjection,
    Submodule.starProjection_minimal, Metric.infDist_eq_iInf]
  exact iInf_congr fun y => dist_eq_norm _ _

/-- If `Δ_F^rel = 0` and `‖D_F^can‖_HS > 0`, the complete odd component `D̃_F` of the
generator is a nonzero relation-supported (admitted) finite-Dirac operator. -/
theorem nonzero_admitted_of_relationDefect_zero (Γ : Matrix n n ℂ) (P : τ → Matrix n n ℂ)
    (Rel : Set (τ × τ)) (A : Matrix n n ℂ) (hΔ : relationDefect Γ P Rel A = 0)
    (hpos : 0 < ‖canonicalFiniteDiracL2 Γ P Rel A‖) :
    finiteDirac Γ A = canonicalFiniteDirac Γ P Rel A
    ∧ matrixL2 (finiteDirac Γ A) ∈ relationSpace Γ P Rel
    ∧ finiteDirac Γ A ≠ 0 := by
  have heq := (finiteDirac_eq_canonical_iff Γ P Rel A).mpr hΔ
  have hL2 := (finiteDirac_eq_canonical_iff_L2 Γ P Rel A).mp heq
  refine ⟨heq, (relationDefect_eq_zero_iff_mem Γ P Rel A).mp hΔ, fun h0 => ?_⟩
  rw [← hL2, h0, matrixL2_zero, norm_zero] at hpos
  exact lt_irrefl _ hpos

/-- The typed coefficient blocks of `D_F^can`: they recover `D_F^can` from a typed resolution
of the identity, vanish off the declared relations, and `D_F^can` is grading-odd. -/
theorem canonicalFiniteDirac_typed_blocks [Fintype τ] (Γ : Matrix n n ℂ)
    (P : τ → Matrix n n ℂ) (hsum : ∑ t, P t = 1) (Rel : Set (τ × τ)) (A : Matrix n n ℂ) :
    canonicalFiniteDirac Γ P Rel A =
        ∑ t, ∑ t', P t * canonicalFiniteDirac Γ P Rel A * P t'
    ∧ (∀ t t', (t, t') ∉ Rel → P t * canonicalFiniteDirac Γ P Rel A * P t' = 0)
    ∧ Γ * canonicalFiniteDirac Γ P Rel A * Γ = -canonicalFiniteDirac Γ P Rel A := by
  obtain ⟨hodd, hsupp⟩ := canonicalFiniteDiracL2_mem Γ P Rel A
  refine ⟨?_, hsupp, hodd⟩
  calc canonicalFiniteDirac Γ P Rel A
      = (∑ t, P t) * canonicalFiniteDirac Γ P Rel A * (∑ t', P t') := by
        rw [hsum, Matrix.one_mul, Matrix.mul_one]
    _ = ∑ t, ∑ t', P t * canonicalFiniteDirac Γ P Rel A * P t' := by
        rw [Finset.sum_mul, Finset.sum_mul]
        simp_rw [Finset.mul_sum]

/-- **`prop:finite-dirac` (Fixed-generator finite-Dirac closure), assembled.**  For the
self-adjoint generator `A` with grading `Γ`, typed resolution `(P_t)` and declared relation
set `Rel`: `D̃_F = D_F^can ⟺ Δ_F^rel = 0` (`eq:finite-dirac-exact-relation`);
`dist_HS(D̃_F, 𝔇_F) = √Δ_F^rel` (`eq:finite-dirac-distance`); if `Δ_F^rel = 0` and
`‖D_F^can‖_HS > 0` the complete odd component is a nonzero admitted finite-Dirac operator;
and the typed coefficient blocks `P_t D_F^can P_{t'}` recover `D_F^can`, are supported on the
declared relations, with `D_F^can` grading-odd.  No odd-provenance completeness is assumed. -/
theorem fixed_generator_finite_dirac_closure [Fintype τ] (Γ : Matrix n n ℂ)
    (P : τ → Matrix n n ℂ) (hsum : ∑ t, P t = 1) (Rel : Set (τ × τ)) (A : Matrix n n ℂ) :
    (finiteDirac Γ A = canonicalFiniteDirac Γ P Rel A ↔ relationDefect Γ P Rel A = 0)
    ∧ Metric.infDist (matrixL2 (finiteDirac Γ A)) (relationSpace Γ P Rel : Set _) =
        Real.sqrt (relationDefect Γ P Rel A)
    ∧ (relationDefect Γ P Rel A = 0 → 0 < ‖canonicalFiniteDiracL2 Γ P Rel A‖ →
        finiteDirac Γ A = canonicalFiniteDirac Γ P Rel A
        ∧ matrixL2 (finiteDirac Γ A) ∈ relationSpace Γ P Rel
        ∧ finiteDirac Γ A ≠ 0)
    ∧ (canonicalFiniteDirac Γ P Rel A =
          ∑ t, ∑ t', P t * canonicalFiniteDirac Γ P Rel A * P t'
        ∧ (∀ t t', (t, t') ∉ Rel → P t * canonicalFiniteDirac Γ P Rel A * P t' = 0)
        ∧ Γ * canonicalFiniteDirac Γ P Rel A * Γ = -canonicalFiniteDirac Γ P Rel A) :=
  ⟨finiteDirac_eq_canonical_iff Γ P Rel A,
    infDist_finiteDirac_relationSpace Γ P Rel A,
    nonzero_admitted_of_relationDefect_zero Γ P Rel A,
    canonicalFiniteDirac_typed_blocks Γ P hsum Rel A⟩

end CanonicalFiniteDirac
end RenewalGeometry
