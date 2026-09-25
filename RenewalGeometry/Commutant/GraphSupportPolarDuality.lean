/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Commutant.SupportPolarActionAlgebra
import RenewalGeometry.Commutant.TypedMultiplicityAlgebra
import RenewalGeometry.Commutant.Bicommutant

/-!
# Exact support-polar duality on a multi-vertex incidence graph

Covers `thm:support-polar` of the spacetime–gauge duality paper.

On the total multiplicity carrier `𝓜 = ⊕_λ M_λ` (the sigma type `TotalCarrier M` of
`SupportPolarActionAlgebra`), with vertex projections `Z_λ`, arbitrary rectangular
(possibly singular, rank-deficient or zero) incidence maps `F_e` and their polar partial
isometries `U_e`, the typed multiplicity algebra `M_type` acts by the block-diagonal
matrices `⊕_λ R_λ` (`multiplicityCarrierAlgebra`).  We prove

* `matCommutant_supportPolarAlgebra`: `(O_F^sup)' = M_type`;
* `matCommutant_multiplicityCarrierAlgebra`: `M_type' = O_F^sup`
  (`eq:support-polar-duality`);
* `incidence_support_polar_equality`: `C^*(Z_λ, F_e, F_e^*) = O_F^sup`
  (`eq:incidence-support-polar-equality`);
* `exact_support_polar_duality`: the three clauses together.

The proof follows the paper: commuting with the vertex projections makes an operator
block diagonal (`eq_blockDiagonal'_of_commute_vertexProjection`), and on every edge the
commutation with `F_e^*F_e, U_e, U_e^*` is the singular polar-edge equivalence
`polar_edge_singular` (`lem:polar-edge`), whose support hypothesis is derived from the
polar identities in `support_commute_of_polar_data`.  The reverse identities are the
finite bicommutant theorem `double_commutant`; the equality of the incidence and
support-polar algebras follows because both are star-closed unital algebras with the same
commutant `M_type`, so no polynomial functional calculus is needed.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace RenewalGeometry

set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

/-! ### Support projections of singular polar data -/

section SupportCommute

variable {E H : Type*} [Fintype E] [DecidableEq E] [Fintype H]

/-- The support projection `UᴴU` of singular polar data `F = U P`, `P² = FᴴF`,
`U UᴴU = U`, `P Pd = Pd P = UᴴU` commutes with every matrix commuting with `P²`.
This supplies the support hypothesis of `polar_edge_singular` from the polar identities
alone. -/
theorem support_commute_of_polar_data (F U : Matrix H E ℂ) (P Pd : Matrix E E ℂ)
    (hP : P.PosSemidef) (hFUP : F = U * P) (hPP : P * P = Fᴴ * F)
    (hUp : U * (Uᴴ * U) = U) (hPd1 : P * Pd = Uᴴ * U) (hPd2 : Pd * P = Uᴴ * U)
    (R : Matrix E E ℂ) (hR : R * (P * P) = (P * P) * R) :
    R * (Uᴴ * U) = (Uᴴ * U) * R := by
  set p := Uᴴ * U with hp
  have hPH : Pᴴ = P := hP.isHermitian
  have hpH : pᴴ = p := by
    rw [hp, conjTranspose_mul, conjTranspose_conjTranspose]
  have hpp : p * p = p := by
    rw [hp, Matrix.mul_assoc, hUp]
  have hRP : R * P = P * R := commute_of_commute_sq hP hR
  -- `P p P = P P`
  have hPpP : P * p * P = P * P := by
    rw [hPP, hFUP, conjTranspose_mul, hPH, hp]
    simp only [Matrix.mul_assoc]
  -- `p P = P`: the range of `P` lies in the range of `p`
  have hpP : p * P = P := by
    have h1 : ((1 - p) * P)ᴴ * ((1 - p) * P) = 0 := by
      rw [conjTranspose_mul, hPH, conjTranspose_sub, conjTranspose_one, hpH]
      have h11 : (1 - p) * ((1 - p) * P) = (1 - p) * P := by
        rw [← Matrix.mul_assoc, sub_mul, one_mul, mul_sub, mul_one, hpp, sub_self, sub_zero]
      rw [Matrix.mul_assoc, h11, sub_mul, one_mul, mul_sub, ← Matrix.mul_assoc, hPpP, sub_self]
    have h2 := Matrix.conjTranspose_mul_self_eq_zero.mp h1
    rw [sub_mul, one_mul, sub_eq_zero] at h2
    exact h2.symm
  -- any `S` commuting with `P` satisfies `S p = p S p`
  have key : ∀ S : Matrix E E ℂ, S * P = P * S → S * p = p * (S * p) := by
    intro S hS
    have e1 : S * p = P * S * Pd := by
      rw [← hPd1, ← Matrix.mul_assoc, hS]
    have e2 : p * (S * p) = P * S * Pd := by
      rw [e1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hpP]
    rw [e2]
    exact e1
  have hRHP : Rᴴ * P = P * Rᴴ := by
    have h := congrArg conjTranspose hRP
    rw [conjTranspose_mul, conjTranspose_mul, hPH] at h
    exact h.symm
  have h2 := key R hRP
  have h3 := key Rᴴ hRHP
  have h3' : p * R = p * R * p := by
    have h := congrArg conjTranspose h3
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hpH] at h
    exact h
  rw [h2, ← Matrix.mul_assoc, ← h3']

end SupportCommute

namespace GraphLoadedEdgeCommutant

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
variable (M : V → Type*) [∀ v, Fintype (M v)] [∀ v, DecidableEq (M v)]
variable (F : ∀ ⦃u v⦄, G.Adj u v → Matrix (M v) (M u) ℂ)

/-! ### Block calculus on the total carrier -/

/-- The diagonal `(v, v)` block of a matrix on the total carrier. -/
def diagBlock (X : Matrix (TotalCarrier M) (TotalCarrier M) ℂ) (v : V) :
    Matrix (M v) (M v) ℂ :=
  fun i j => X ⟨v, i⟩ ⟨v, j⟩

theorem blockEmbed_apply_eq {u v : V} (A : Matrix (M v) (M u) ℂ) (i : M v) (j : M u) :
    blockEmbed M A ⟨v, i⟩ ⟨u, j⟩ = A i j := by
  simp [blockEmbed]

theorem blockEmbed_apply_ne {u v : V} (A : Matrix (M v) (M u) ℂ) (p q : TotalCarrier M)
    (h : p.1 ≠ v ∨ q.1 ≠ u) : blockEmbed M A p q = 0 := by
  rcases h with h | h <;> simp [blockEmbed, h]

theorem blockEmbed_injective {u v : V} {A B : Matrix (M v) (M u) ℂ}
    (h : blockEmbed M A = blockEmbed M B) : A = B := by
  ext i j
  have := congrFun (congrFun h ⟨v, i⟩) ⟨u, j⟩
  rwa [blockEmbed_apply_eq, blockEmbed_apply_eq] at this

theorem blockDiagonal'_mul_apply (R : ∀ v, Matrix (M v) (M v) ℂ)
    (Y : Matrix (TotalCarrier M) (TotalCarrier M) ℂ) (k : V) (i : M k) (q : TotalCarrier M) :
    (blockDiagonal' R * Y) ⟨k, i⟩ q = ∑ m, R k i m * Y ⟨k, m⟩ q := by
  rw [Matrix.mul_apply, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Finset.sum_eq_single k]
  · exact Finset.sum_congr rfl fun m _ => by rw [blockDiagonal'_apply_eq]
  · intro l _ hl
    exact Finset.sum_eq_zero fun m _ => by
      rw [blockDiagonal'_apply_ne _ _ _ (Ne.symm hl), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem mul_blockDiagonal'_apply (R : ∀ v, Matrix (M v) (M v) ℂ)
    (Y : Matrix (TotalCarrier M) (TotalCarrier M) ℂ) (p : TotalCarrier M) (k : V) (j : M k) :
    (Y * blockDiagonal' R) p ⟨k, j⟩ = ∑ m, Y p ⟨k, m⟩ * R k m j := by
  rw [Matrix.mul_apply, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Finset.sum_eq_single k]
  · exact Finset.sum_congr rfl fun m _ => by rw [blockDiagonal'_apply_eq]
  · intro l _ hl
    exact Finset.sum_eq_zero fun m _ => by
      rw [blockDiagonal'_apply_ne _ _ _ hl, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Left multiplication of a corner block by a block-diagonal matrix. -/
theorem blockDiagonal'_mul_blockEmbed {u v : V} (R : ∀ v, Matrix (M v) (M v) ℂ)
    (A : Matrix (M v) (M u) ℂ) :
    blockDiagonal' R * blockEmbed M A = blockEmbed M (R v * A) := by
  ext ⟨k, i⟩ ⟨k', j⟩
  rw [blockDiagonal'_mul_apply]
  by_cases hk : k = v
  · subst hk
    by_cases hk' : k' = u
    · subst hk'
      rw [blockEmbed_apply_eq, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun m _ => by rw [blockEmbed_apply_eq]
    · rw [blockEmbed_apply_ne M _ _ _ (Or.inr hk')]
      exact Finset.sum_eq_zero fun m _ => by
        rw [blockEmbed_apply_ne M _ _ _ (Or.inr hk'), mul_zero]
  · rw [blockEmbed_apply_ne M _ _ _ (Or.inl hk)]
    exact Finset.sum_eq_zero fun m _ => by
      rw [blockEmbed_apply_ne M _ _ _ (Or.inl hk), mul_zero]

/-- Right multiplication of a corner block by a block-diagonal matrix. -/
theorem blockEmbed_mul_blockDiagonal' {u v : V} (R : ∀ v, Matrix (M v) (M v) ℂ)
    (A : Matrix (M v) (M u) ℂ) :
    blockEmbed M A * blockDiagonal' R = blockEmbed M (A * R u) := by
  ext ⟨k, i⟩ ⟨k', j⟩
  rw [mul_blockDiagonal'_apply]
  by_cases hk' : k' = u
  · subst hk'
    by_cases hk : k = v
    · subst hk
      rw [blockEmbed_apply_eq, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun m _ => by rw [blockEmbed_apply_eq]
    · rw [blockEmbed_apply_ne M _ _ _ (Or.inl hk)]
      exact Finset.sum_eq_zero fun m _ => by
        rw [blockEmbed_apply_ne M _ _ _ (Or.inl hk), zero_mul]
  · rw [blockEmbed_apply_ne M _ _ _ (Or.inr hk')]
    exact Finset.sum_eq_zero fun m _ => by
      rw [blockEmbed_apply_ne M _ _ _ (Or.inr hk'), zero_mul]

/-- Products of corner blocks. -/
theorem blockEmbed_mul_blockEmbed {u v w : V} (A : Matrix (M w) (M v) ℂ)
    (B : Matrix (M v) (M u) ℂ) :
    blockEmbed M A * blockEmbed M B = blockEmbed M (A * B) := by
  ext ⟨k, i⟩ ⟨k', j⟩
  rw [Matrix.mul_apply, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Finset.sum_eq_single v]
  · by_cases hk : k = w
    · subst hk
      by_cases hk' : k' = u
      · subst hk'
        rw [blockEmbed_apply_eq, Matrix.mul_apply]
        exact Finset.sum_congr rfl fun m _ => by rw [blockEmbed_apply_eq, blockEmbed_apply_eq]
      · rw [blockEmbed_apply_ne M _ _ _ (Or.inr hk')]
        exact Finset.sum_eq_zero fun m _ => by
          rw [blockEmbed_apply_ne M B _ _ (Or.inr hk'), mul_zero]
    · rw [blockEmbed_apply_ne M _ _ _ (Or.inl hk)]
      exact Finset.sum_eq_zero fun m _ => by
        rw [blockEmbed_apply_ne M A _ _ (Or.inl hk), zero_mul]
  · intro l _ hl
    exact Finset.sum_eq_zero fun m _ => by
      rw [blockEmbed_apply_ne M A _ _ (Or.inr hl), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Adjoints of corner blocks. -/
theorem blockEmbed_conjTranspose {u v : V} (A : Matrix (M v) (M u) ℂ) :
    (blockEmbed M A)ᴴ = blockEmbed M Aᴴ := by
  ext ⟨k, i⟩ ⟨k', j⟩
  rw [conjTranspose_apply]
  by_cases hk : k = u
  · subst hk
    by_cases hk' : k' = v
    · subst hk'
      rw [blockEmbed_apply_eq, blockEmbed_apply_eq, conjTranspose_apply]
    · rw [blockEmbed_apply_ne M _ _ _ (Or.inl hk'), blockEmbed_apply_ne M _ _ _ (Or.inr hk'),
        star_zero]
  · rw [blockEmbed_apply_ne M _ _ _ (Or.inr hk), blockEmbed_apply_ne M _ _ _ (Or.inl hk),
      star_zero]

/-- A block-diagonal matrix commutes with the corner block `A : M_u → M_v` iff
`R_v A = A R_u`. -/
theorem blockDiagonal'_commute_blockEmbed_iff {u v : V} (R : ∀ v, Matrix (M v) (M v) ℂ)
    (A : Matrix (M v) (M u) ℂ) :
    blockDiagonal' R * blockEmbed M A = blockEmbed M A * blockDiagonal' R ↔
      R v * A = A * R u := by
  rw [blockDiagonal'_mul_blockEmbed, blockEmbed_mul_blockDiagonal']
  exact ⟨blockEmbed_injective M, fun h => by rw [h]⟩

/-- Block-diagonal matrices commute with the vertex projections. -/
theorem blockDiagonal'_commute_vertexProjection (R : ∀ v, Matrix (M v) (M v) ℂ) (v : V) :
    blockDiagonal' R * vertexProjection M v = vertexProjection M v * blockDiagonal' R := by
  ext ⟨k, i⟩ ⟨k', j⟩
  unfold vertexProjection
  rw [mul_diagonal, diagonal_mul]
  by_cases hk : k = k'
  · subst hk
    exact mul_comm _ _
  · rw [blockDiagonal'_apply_ne _ _ _ hk, mul_zero, zero_mul]

/-- Commuting with every vertex projection `Z_λ` forces block-diagonal form. -/
theorem eq_blockDiagonal'_of_commute_vertexProjection
    (X : Matrix (TotalCarrier M) (TotalCarrier M) ℂ)
    (h : ∀ v, X * vertexProjection M v = vertexProjection M v * X) :
    X = blockDiagonal' (diagBlock M X) := by
  ext ⟨k, i⟩ ⟨k', j⟩
  by_cases hk : k = k'
  · subst hk
    rw [blockDiagonal'_apply_eq]
    rfl
  · rw [blockDiagonal'_apply_ne _ _ _ hk]
    have hentry := congrFun (congrFun (h k') ⟨k, i⟩) ⟨k', j⟩
    unfold vertexProjection at hentry
    rw [mul_diagonal, diagonal_mul] at hentry
    simpa [hk] using hentry

/-! ### The multiplicity algebra on the total carrier -/

/-- `M_type` represented on the total multiplicity carrier `𝓜 = ⊕_λ M_λ`: the
block-diagonal matrices `⊕_λ R_λ` with `(R_λ)` in the typed multiplicity algebra. -/
def multiplicityCarrierAlgebra : Set (Matrix (TotalCarrier M) (TotalCarrier M) ℂ) :=
  (Matrix.blockDiagonal' : (∀ v, Matrix (M v) (M v) ℂ) → _) ''
    (typedMultiplicityAlgebra G M F : Set (∀ v, Matrix (M v) (M v) ℂ))

/-- On one edge, commuting with `F_e^*F_e`, `U_e` and `U_e^*` (on the carrier) is
exactly the pair of typed intertwining equations (`lem:polar-edge`). -/
theorem blockDiagonal'_commute_edge_generators_iff (R : ∀ v, Matrix (M v) (M v) ℂ)
    {u v : V} (h : G.Adj u v) :
    (blockDiagonal' R * supportMetric G M F h = supportMetric G M F h * blockDiagonal' R ∧
      blockDiagonal' R * polarOp G M F h = polarOp G M F h * blockDiagonal' R ∧
      blockDiagonal' R * (polarOp G M F h)ᴴ = (polarOp G M F h)ᴴ * blockDiagonal' R) ↔
    (R v * F h = F h * R u ∧ R u * (F h)ᴴ = (F h)ᴴ * R v) := by
  obtain ⟨P, Pd, hP, hFUP, hPP, hUp, hPd1, hPd2⟩ := polarIsometry_spec (F h)
  have hsupp := support_commute_of_polar_data (F h) (polarIsometry (F h)) P Pd hP hFUP hPP hUp
    hPd1 hPd2
  have hmetric : supportMetric G M F h = blockEmbed M ((F h)ᴴ * F h) := by
    rw [supportMetric, incidenceOp, blockEmbed_conjTranspose, blockEmbed_mul_blockEmbed]
  rw [hmetric, polarOp, blockEmbed_conjTranspose, blockDiagonal'_commute_blockEmbed_iff,
    blockDiagonal'_commute_blockEmbed_iff, blockDiagonal'_commute_blockEmbed_iff]
  have hpe := (polar_edge_singular (F h) (polarIsometry (F h)) P Pd (R u) (R v) hP hFUP hPP hUp
    hPd1 hPd2 hsupp).1
  rw [hPP] at hpe
  exact hpe.symm

/-- The generator set of the support-polar algebra is star-closed. -/
theorem supportPolarGenerators_starClosed :
    ∀ x ∈ supportPolarGenerators G M F, xᴴ ∈ supportPolarGenerators G M F := by
  rintro x (((⟨v, rfl⟩ | ⟨u, v, h, rfl⟩) | ⟨u, v, h, rfl⟩) | ⟨u, v, h, rfl⟩)
  · rw [vertexProjection_conjTranspose]
    exact Or.inl (Or.inl (Or.inl ⟨v, rfl⟩))
  · have : (supportMetric G M F h)ᴴ = supportMetric G M F h := by
      rw [supportMetric, conjTranspose_mul, conjTranspose_conjTranspose]
    rw [this]
    exact Or.inl (Or.inl (Or.inr ⟨u, v, h, rfl⟩))
  · exact Or.inr ⟨u, v, h, rfl⟩
  · rw [conjTranspose_conjTranspose]
    exact Or.inl (Or.inr ⟨u, v, h, rfl⟩)

/-- **Generator commutant of the support-polar presentation.**
`{Z_λ, F_e^*F_e, U_e, U_e^*}' = M_type` on the total multiplicity carrier. -/
theorem matCommutant_supportPolarGenerators :
    matCommutant (supportPolarGenerators G M F) = multiplicityCarrierAlgebra G M F := by
  ext X
  constructor
  · intro hX
    have hZ : ∀ v, X * vertexProjection M v = vertexProjection M v * X :=
      fun v => hX _ (Or.inl (Or.inl (Or.inl ⟨v, rfl⟩)))
    have hXeq := eq_blockDiagonal'_of_commute_vertexProjection M X hZ
    refine ⟨diagBlock M X, ?_, hXeq.symm⟩
    rw [SetLike.mem_coe, mem_typedMultiplicityAlgebra]
    intro u v h
    have h1 := hX _ (Or.inl (Or.inl (Or.inr ⟨u, v, h, rfl⟩)))
    have h2 := hX _ (Or.inl (Or.inr ⟨u, v, h, rfl⟩))
    have h3 := hX _ (Or.inr ⟨u, v, h, rfl⟩)
    rw [hXeq] at h1 h2 h3
    exact (blockDiagonal'_commute_edge_generators_iff G M F _ h).mp ⟨h1, h2, h3⟩
  · rintro ⟨R, hR, rfl⟩ a ha
    rw [SetLike.mem_coe, mem_typedMultiplicityAlgebra] at hR
    rcases ha with ((⟨v, rfl⟩ | ⟨u, v, h, rfl⟩) | ⟨u, v, h, rfl⟩) | ⟨u, v, h, rfl⟩
    · exact blockDiagonal'_commute_vertexProjection M R v
    · exact ((blockDiagonal'_commute_edge_generators_iff G M F R h).mpr (hR h)).1
    · exact ((blockDiagonal'_commute_edge_generators_iff G M F R h).mpr (hR h)).2.1
    · exact ((blockDiagonal'_commute_edge_generators_iff G M F R h).mpr (hR h)).2.2

end GraphLoadedEdgeCommutant

/-! ### Commutants of generated star algebras -/

section StarAdjoinCommutant

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The commutant of the star algebra generated by a star-closed set is the commutant of
the set. -/
theorem matCommutant_starAlgebra_adjoin (S : Set (Matrix n n ℂ)) (hS : ∀ x ∈ S, xᴴ ∈ S) :
    matCommutant ((StarAlgebra.adjoin ℂ S : StarSubalgebra ℂ (Matrix n n ℂ)) :
        Set (Matrix n n ℂ)) = matCommutant S := by
  ext T
  constructor
  · intro hT a ha
    exact hT a (StarAlgebra.subset_adjoin ℂ S ha)
  · intro hT a ha
    suffices h : T * a = a * T ∧ T * aᴴ = aᴴ * T from h.1
    induction ha using StarAlgebra.adjoin_induction with
    | mem x hx => exact ⟨hT x hx, hT _ (hS x hx)⟩
    | algebraMap r =>
      refine ⟨(Algebra.commutes r T).symm, ?_⟩
      rw [Algebra.algebraMap_eq_smul_one, conjTranspose_smul, conjTranspose_one, smul_mul_assoc,
        mul_smul_comm, one_mul, mul_one]
    | add x y _ _ hx hy =>
      exact ⟨by rw [mul_add, add_mul, hx.1, hy.1],
        by rw [conjTranspose_add, mul_add, add_mul, hx.2, hy.2]⟩
    | mul x y _ _ hx hy =>
      exact ⟨by rw [← mul_assoc, hx.1, mul_assoc, hy.1, ← mul_assoc],
        by rw [conjTranspose_mul, ← mul_assoc, hy.2, mul_assoc, hx.2, ← mul_assoc]⟩
    | star x _ hx =>
      simp only [Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose]
      exact ⟨hx.2, hx.1⟩

/-- The finite bicommutant identity for a star subalgebra of matrices. -/
theorem matCommutant_matCommutant_starSubalgebra (A : StarSubalgebra ℂ (Matrix n n ℂ)) :
    matCommutant (matCommutant (A : Set (Matrix n n ℂ))) = (A : Set (Matrix n n ℂ)) := by
  ext T
  constructor
  · intro hT
    exact double_commutant A.toSubalgebra (fun a ha => A.star_mem' ha) T hT
  · intro hT b hb
    exact (hb T hT).symm

end StarAdjoinCommutant

namespace GraphLoadedEdgeCommutant

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
variable (M : V → Type*) [∀ v, Fintype (M v)] [∀ v, DecidableEq (M v)]
variable (F : ∀ ⦃u v⦄, G.Adj u v → Matrix (M v) (M u) ℂ)

/-- **`(O_F^sup)' = M_type`** (first identity of `eq:support-polar-duality`), for arbitrary
rectangular, singular, rank-deficient or zero incidence maps. -/
theorem matCommutant_supportPolarAlgebra :
    matCommutant ((supportPolarAlgebra G M F : StarSubalgebra ℂ _) : Set _) =
      multiplicityCarrierAlgebra G M F := by
  rw [supportPolarAlgebra,
    matCommutant_starAlgebra_adjoin _ (supportPolarGenerators_starClosed G M F),
    matCommutant_supportPolarGenerators]

/-- **`M_type' = O_F^sup`** (second identity of `eq:support-polar-duality`), by finite
bicommutant closure. -/
theorem matCommutant_multiplicityCarrierAlgebra :
    matCommutant (multiplicityCarrierAlgebra G M F) =
      ((supportPolarAlgebra G M F : StarSubalgebra ℂ _) : Set _) := by
  rw [← matCommutant_supportPolarAlgebra, matCommutant_matCommutant_starSubalgebra]

/-! ### The incidence presentation `C^*(Z_λ, F_e, F_e^*)` -/

/-- The generator set `{Z_λ, F_e, F_e^*}` of the incidence presentation. -/
def incidenceGenerators : Set (Matrix (TotalCarrier M) (TotalCarrier M) ℂ) :=
  Set.range (vertexProjection M) ∪
    {X | ∃ (u v : V) (h : G.Adj u v), X = incidenceOp G M F h} ∪
    {X | ∃ (u v : V) (h : G.Adj u v), X = (incidenceOp G M F h)ᴴ}

/-- The incidence algebra `C^*(Z_λ, F_e, F_e^* : λ, e) ⊆ B(𝓜)`. -/
def incidenceAlgebra : StarSubalgebra ℂ (Matrix (TotalCarrier M) (TotalCarrier M) ℂ) :=
  StarAlgebra.adjoin ℂ (incidenceGenerators G M F)

theorem incidenceGenerators_starClosed :
    ∀ x ∈ incidenceGenerators G M F, xᴴ ∈ incidenceGenerators G M F := by
  rintro x ((⟨v, rfl⟩ | ⟨u, v, h, rfl⟩) | ⟨u, v, h, rfl⟩)
  · rw [vertexProjection_conjTranspose]
    exact Or.inl (Or.inl ⟨v, rfl⟩)
  · exact Or.inr ⟨u, v, h, rfl⟩
  · rw [conjTranspose_conjTranspose]
    exact Or.inl (Or.inr ⟨u, v, h, rfl⟩)

/-- The generator commutant of the incidence presentation is `M_type` (this is the
edge-commutant identity `thm:edge-commutant` on the multiplicity carrier). -/
theorem matCommutant_incidenceGenerators :
    matCommutant (incidenceGenerators G M F) = multiplicityCarrierAlgebra G M F := by
  ext X
  constructor
  · intro hX
    have hZ : ∀ v, X * vertexProjection M v = vertexProjection M v * X :=
      fun v => hX _ (Or.inl (Or.inl ⟨v, rfl⟩))
    have hXeq := eq_blockDiagonal'_of_commute_vertexProjection M X hZ
    refine ⟨diagBlock M X, ?_, hXeq.symm⟩
    rw [SetLike.mem_coe, mem_typedMultiplicityAlgebra]
    intro u v h
    have h1 := hX _ (Or.inl (Or.inr ⟨u, v, h, rfl⟩))
    have h2 := hX _ (Or.inr ⟨u, v, h, rfl⟩)
    rw [hXeq, incidenceOp] at h1 h2
    rw [blockEmbed_conjTranspose] at h2
    exact ⟨(blockDiagonal'_commute_blockEmbed_iff M _ _).mp h1,
      (blockDiagonal'_commute_blockEmbed_iff M _ _).mp h2⟩
  · rintro ⟨R, hR, rfl⟩ a ha
    rw [SetLike.mem_coe, mem_typedMultiplicityAlgebra] at hR
    rcases ha with (⟨v, rfl⟩ | ⟨u, v, h, rfl⟩) | ⟨u, v, h, rfl⟩
    · exact blockDiagonal'_commute_vertexProjection M R v
    · exact (blockDiagonal'_commute_blockEmbed_iff M _ _).mpr (hR h).1
    · rw [incidenceOp, blockEmbed_conjTranspose]
      exact (blockDiagonal'_commute_blockEmbed_iff M _ _).mpr (hR h).2

/-- **`eq:incidence-support-polar-equality`.**  `C^*(Z_λ, F_e, F_e^*) = O_F^sup`: the
incidence and support-polar presentations generate the same star algebra, because both are
star-closed unital algebras with the common commutant `M_type`. -/
theorem incidence_support_polar_equality :
    incidenceAlgebra G M F = supportPolarAlgebra G M F := by
  apply SetLike.coe_injective
  have h1 : matCommutant ((incidenceAlgebra G M F : StarSubalgebra ℂ _) : Set _) =
      multiplicityCarrierAlgebra G M F := by
    rw [incidenceAlgebra,
      matCommutant_starAlgebra_adjoin _ (incidenceGenerators_starClosed G M F),
      matCommutant_incidenceGenerators]
  rw [← matCommutant_matCommutant_starSubalgebra (incidenceAlgebra G M F), h1,
    ← matCommutant_supportPolarAlgebra, matCommutant_matCommutant_starSubalgebra]

/-- **Exact support-polar duality (`thm:support-polar`).**  For arbitrary rectangular,
singular, rank-deficient or zero incidence maps on a finite multi-vertex incidence graph,
`M_type = (O_F^sup)'`, `O_F^sup = M_type'` and `C^*(Z_λ, F_e, F_e^*) = O_F^sup`. -/
theorem exact_support_polar_duality :
    multiplicityCarrierAlgebra G M F =
        matCommutant ((supportPolarAlgebra G M F : StarSubalgebra ℂ _) : Set _) ∧
      ((supportPolarAlgebra G M F : StarSubalgebra ℂ _) : Set _) =
        matCommutant (multiplicityCarrierAlgebra G M F) ∧
      incidenceAlgebra G M F = supportPolarAlgebra G M F :=
  ⟨(matCommutant_supportPolarAlgebra G M F).symm,
    (matCommutant_multiplicityCarrierAlgebra G M F).symm,
    incidence_support_polar_equality G M F⟩

end GraphLoadedEdgeCommutant

end RenewalGeometry
