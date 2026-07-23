/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Algebra.PauliJordan
import NCG.Algebra.CircleSelection
import NCG.Upstream.SharpPurification

/-!
# The two-path complex face and the Jordan/operational assembly

The assembly layer of the Jordan cluster
(`thm:two-path-complex-face`, `cor:pairwise-complex-type`,
`thm:complex-algebra`, `thm:operational-diagonalization`,
`thm:operational-jordan` of `manuscripts/renewal_emergence/renewal_emergence.tex`).

* `spin_assoc_inner` — spin factors are **Euclidean** Jordan
  algebras: spin multiplication operators are symmetric for the
  natural pairing `⟪(s,v),(t,w)⟫ = st + ⟪v,w⟫`;
* `spinMul_isometry_congr` — the spin product transports along any
  linear isometry of the coherence space;
* `TwoPathFaceDatum` / `TwoPathFaceDatum.finrank_eq_two` — the (O4)
  face presentation (balanced pure states = unit sphere of `J_ij`
  with a transitive continuous action of the monothetic connected
  phase group by isometries) forces **`dim J_ij = 2`**;
* `two_path_face_complex` — **the face classification**: the
  rank-two face `JSpin(ℝ ⊕ J_ij)` is Jordan-isomorphic to
  `M₂(ℂ)_sa` (Hermitian-bijective, unital, additive, Jordan
  multiplicative), by transport to `JSpin(ℝ³)` and the Pauli
  isomorphism;
* `two_path_complex_face` — the umbrella statement of the theorem;
* `JordanMatrixType` / `coherence_dim_two_selects_complex` — the
  Jordan–von Neumann–Wigner selection (`cor:pairwise-complex-type`):
  among the simple Euclidean types with pairwise Peirce dimensions
  `1, 2, 4, 8`, coherence dimension two selects exactly the complex
  type;
* `coherence_flow_velocity` — the coherence-plane phase flow
  `t ↦ e^{ist(a₁−a₂)/2}·b` has angular velocity `s(a₁−a₂)/2`, the
  velocity matched by the proved `lem:phase-velocity` rigidity
  (`thm:complex-algebra`, associative-orientation clause);
* `OperationalJordanModel` / `OperationalDiagonalization` — faithful
  statement interfaces for `thm:operational-jordan` and
  `thm:operational-diagonalization`: an embedding of the state space
  into the cone of a formally real Euclidean Jordan algebra, with
  spectral decompositions in Jordan frames.
-/

namespace NCG.Jordan

open Module Matrix RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ## Spin factors are Euclidean -/

/-- The natural pairing of the spin factor `ℝ ⊕ V`. -/
noncomputable def spinInner (x y : ℝ × V) : ℝ :=
  x.1 * y.1 + ⟪x.2, y.2⟫

/-- **Spin factors are Euclidean**: spin multiplication operators
are symmetric for the natural pairing. -/
theorem spin_assoc_inner (x y z : ℝ × V) :
    spinInner (spinMul x y) z = spinInner y (spinMul x z) := by
  obtain ⟨s, v⟩ := x
  obtain ⟨t, w⟩ := y
  obtain ⟨r, u⟩ := z
  unfold spinInner spinMul
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_comm w v]
  ring

/-- The spin product transports along linear isometries of the
coherence space. -/
theorem spinMul_isometry_congr {V₂ : Type*} [NormedAddCommGroup V₂]
    [InnerProductSpace ℝ V₂] (f : V ≃ₗᵢ[ℝ] V₂) (x y : ℝ × V) :
    spinMul ((x.1, f x.2)) ((y.1, f y.2))
      = ((spinMul x y).1, f (spinMul x y).2) := by
  unfold spinMul
  refine Prod.ext ?_ ?_
  · simp only
    rw [f.inner_map_map]
  · simp only [map_add, map_smul]

/-! ## The two-path face -/

/-- **The (O4) face presentation** (`thm:two-path-complex-face`
hypothesis interface): the balanced pure states of the nonclassical
Peirce coherence space `J_ij` form its unit sphere and carry an
effective transitive continuous action of the compact connected
one-dimensional phase group — a monothetic connected topological
group — by isometries. -/
structure TwoPathFaceDatum (G : Type*) [Group G] [TopologicalSpace G]
    [PreconnectedSpace G] (Jc : Type*) [NormedAddCommGroup Jc]
    [InnerProductSpace ℝ Jc] [FiniteDimensional ℝ Jc] where
  /-- The phase action on the coherence space. -/
  ρ : G →* (Jc ≃ₗᵢ[ℝ] Jc)
  /-- Continuity of the action. -/
  cont : ∀ x : Jc, Continuous fun g => ρ g x
  /-- The phase group is monothetic (true of the circle). -/
  mono : ∃ g₀ : G, Dense ((Subgroup.zpowers g₀ : Subgroup G) : Set G)
  /-- Transitivity on the balanced pure states. -/
  trans : ∀ x y : Jc, ‖x‖ = 1 → ‖y‖ = 1 → ∃ g, ρ g x = y
  /-- Nonclassicality: the coherence space is nonzero. -/
  nonclassical : 0 < finrank ℝ Jc

/-- **`thm:two-path-complex-face`, dimension clause**: every
nonclassical Peirce coherence space is two-dimensional. -/
theorem TwoPathFaceDatum.finrank_eq_two {G : Type*} [Group G]
    [TopologicalSpace G] [PreconnectedSpace G] {Jc : Type*}
    [NormedAddCommGroup Jc] [InnerProductSpace ℝ Jc]
    [FiniteDimensional ℝ Jc] (D : TwoPathFaceDatum G Jc) :
    finrank ℝ Jc = 2 :=
  circle_dimension_selection D.ρ D.cont D.mono D.trans D.nonclassical

/-- **`thm:two-path-complex-face`, face classification**: the
rank-two face `JSpin(ℝ ⊕ J_ij)` over a two-dimensional coherence
space is Jordan-isomorphic to `M₂(ℂ)_sa`: there is a map to complex
`2 × 2` matrices that is a bijection onto the Hermitian matrices,
unital, additive, and intertwines the spin product with the
symmetrized matrix product. -/
theorem two_path_face_complex {Jc : Type*} [NormedAddCommGroup Jc]
    [InnerProductSpace ℝ Jc] [FiniteDimensional ℝ Jc]
    (hJc : finrank ℝ Jc = 2) :
    ∃ φ : (ℝ × WithLp 2 (ℝ × Jc)) → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ x, (φ x)ᴴ = φ x)
      ∧ Function.Injective φ
      ∧ (∀ A, Aᴴ = A → ∃ x, φ x = A)
      ∧ φ spinOne = 1
      ∧ (∀ x y, φ (x + y) = φ x + φ y)
      ∧ ∀ x y, φ (spinMul x y) = jordanMul (φ x) (φ y) := by
  -- the traceless part `ℝ(p₁ − p₂) ⊕ J_ij` is three-dimensional
  have hW3 : finrank ℝ (WithLp 2 (ℝ × Jc)) = 3 := by
    rw [(WithLp.linearEquiv 2 ℝ (ℝ × Jc)).finrank_eq]
    rw [Module.finrank_prod, hJc, Module.finrank_self]
  -- transport to `ℝ³` by an orthonormal basis
  set f : WithLp 2 (ℝ × Jc) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    ((stdOrthonormalBasis ℝ (WithLp 2 (ℝ × Jc))).reindex
      (finCongr hW3)).repr with hf
  refine ⟨fun x => pauliMap (x.1, f x.2), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact pauliMap_hermitian _
  · intro x y hxy
    have h1 := pauliMap_injective hxy
    rw [Prod.mk.injEq] at h1
    exact Prod.ext h1.1 (f.injective h1.2)
  · intro A hA
    obtain ⟨x', hx'⟩ := pauliMap_surj_hermitian A hA
    refine ⟨(x'.1, f.symm x'.2), ?_⟩
    simp only [LinearIsometryEquiv.apply_symm_apply]
    exact hx'
  · dsimp only
    have h1 : ((spinOne : ℝ × WithLp 2 (ℝ × Jc)).1,
        f (spinOne : ℝ × WithLp 2 (ℝ × Jc)).2)
        = (spinOne : ℝ × EuclideanSpace ℝ (Fin 3)) := by
      unfold spinOne
      exact Prod.ext rfl (map_zero f)
    rw [h1]
    exact pauliMap_one
  · intro x y
    dsimp only
    have h1 : ((x + y).1, f (x + y).2)
        = (x.1, f x.2) + (y.1, f y.2) := by
      refine Prod.ext rfl ?_
      simp only [Prod.snd_add, map_add]
    rw [h1]
    exact pauliMap_add _ _
  · intro x y
    dsimp only
    rw [← spinMul_isometry_congr f x y]
    exact pauliMap_spinMul _ _

/-- **Theorem `thm:two-path-complex-face`** (umbrella): under the
(O4) face presentation, the coherence space is two-dimensional and
the rank-two face is Jordan-isomorphic to `M₂(ℂ)_sa`. -/
theorem two_path_complex_face {G : Type*} [Group G]
    [TopologicalSpace G] [PreconnectedSpace G] {Jc : Type*}
    [NormedAddCommGroup Jc] [InnerProductSpace ℝ Jc]
    [FiniteDimensional ℝ Jc] (D : TwoPathFaceDatum G Jc) :
    finrank ℝ Jc = 2
    ∧ ∃ φ : (ℝ × WithLp 2 (ℝ × Jc)) → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ x, (φ x)ᴴ = φ x)
      ∧ Function.Injective φ
      ∧ (∀ A, Aᴴ = A → ∃ x, φ x = A)
      ∧ φ spinOne = 1
      ∧ (∀ x y, φ (x + y) = φ x + φ y)
      ∧ ∀ x y, φ (spinMul x y) = jordanMul (φ x) (φ y) :=
  ⟨D.finrank_eq_two, two_path_face_complex D.finrank_eq_two⟩

/-! ## The Jordan–von Neumann–Wigner selection -/

/-- The simple Euclidean Jordan matrix types of the JvNW
classification. -/
inductive JordanMatrixType
  | real
  | complex
  | quaternionic
  | octonionic
deriving DecidableEq

/-- The pairwise Peirce coherence dimension of each type. -/
def JordanMatrixType.coherenceDim : JordanMatrixType → ℕ
  | real => 1
  | complex => 2
  | quaternionic => 4
  | octonionic => 8

/-- **`cor:pairwise-complex-type`, selection**: coherence dimension
two selects exactly the complex matrix type among the JvNW simple
Euclidean types. -/
theorem coherence_dim_two_selects_complex (t : JordanMatrixType)
    (h : t.coherenceDim = 2) : t = JordanMatrixType.complex := by
  cases t <;> simp_all [JordanMatrixType.coherenceDim]

/-! ## The associative-orientation phase flow -/

/-- **The coherence-plane flow velocity**
(`thm:complex-algebra`, orientation clause): in a frame
diagonalizing `a`, the unitary flow `e^{sita/2}` rotates the `ij`
coherence entry as `t ↦ e^{ist(a_i−a_j)/2}·b`, with angular velocity
`s(a_i − a_j)/2` — exactly the velocity forced by the proved
pairwise phase rigidity (`lem:phase-velocity`). -/
theorem coherence_flow_velocity (s a₁ a₂ : ℝ) (b : ℂ) :
    HasDerivAt
      (fun t : ℝ =>
        Complex.exp (Complex.I * (s * (a₁ - a₂) / 2) * t) * b)
      (Complex.I * (s * (a₁ - a₂) / 2) * b) 0 := by
  set c : ℂ := Complex.I * (s * (a₁ - a₂) / 2) with hc
  have h1 : HasDerivAt (fun t : ℝ => ((t : ℝ) : ℂ)) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have h2 : HasDerivAt (fun t : ℝ => c * ((t : ℝ) : ℂ)) c 0 := by
    have h3 := h1.const_mul c
    simpa using h3
  have h4 := h2.cexp
  have h5 : Complex.exp (c * ((0 : ℝ) : ℂ)) = 1 := by
    simp
  rw [h5, one_mul] at h4
  have h6 := h4.mul_const b
  convert h6 using 2

/-! ## Operational interfaces -/

/-- **Statement interface for `thm:operational-jordan`**: an
operationally irreducible predictive sector is order-embedded in the
cone of squares of a finite-dimensional formally real (Euclidean)
Jordan algebra, with the cone reached by the states up to
normalization.  The Barnum–Lee–Scandolo–Selby reconstruction proof
is the scoped literature input; the target Jordan-algebra layer is
the one built in `NCG/Algebra/SpinFactor.lean`. -/
structure OperationalJordanModel (State : Type*) (J : Type*)
    [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [FiniteDimensional ℝ J] where
  /-- The Jordan product. -/
  mul : J → J → J
  /-- The Jordan unit. -/
  one : J
  /-- Commutativity. -/
  comm : ∀ x y, mul x y = mul y x
  /-- Bilinearity (addition, left slot). -/
  add_left : ∀ x y z, mul (x + y) z = mul x z + mul y z
  /-- Bilinearity (scalars, left slot). -/
  smul_left : ∀ (c : ℝ) (x y), mul (c • x) y = c • mul x y
  /-- Unitality. -/
  mul_one : ∀ x, mul x one = x
  /-- The Jordan identity. -/
  jordan : ∀ x y, mul (mul x y) (mul x x) = mul x (mul y (mul x x))
  /-- Euclidean structure: multiplications are symmetric. -/
  assoc_inner : ∀ x y z, ⟪mul x y, z⟫ = ⟪y, mul x z⟫
  /-- Formal reality. -/
  formally_real : ∀ x y, mul x x + mul y y = 0 → x = 0 ∧ y = 0
  /-- The order embedding of the states. -/
  embed : State → J
  /-- Injectivity (states are separated). -/
  embed_injective : Function.Injective embed
  /-- States land in the positive cone. -/
  embed_cone : ∀ ρ, ∃ x, embed ρ = mul x x
  /-- The cone is reached by the states up to normalization. -/
  cone_reached : ∀ x : J, ∃ (ρ : State) (c : ℝ),
    0 ≤ c ∧ c • embed ρ = mul x x

/-- **Statement interface for `thm:operational-diagonalization`**:
every state decomposes as a finite convex combination over a Jordan
frame — pairwise orthogonal idempotents — of the reconstructed
algebra; these are the operational spectral decompositions into
perfectly distinguishable pure states (the Chiribella–Scandolo
theorem is the scoped literature input). -/
def OperationalDiagonalization {State : Type*} {J : Type*}
    [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [FiniteDimensional ℝ J]
    (M : OperationalJordanModel State J) : Prop :=
  ∀ ρ : State, ∃ (r : ℕ) (p : Fin r → ℝ) (q : Fin r → J),
    (∀ i, 0 < p i)
    ∧ (∀ i, M.mul (q i) (q i) = q i)
    ∧ (∀ i j, i ≠ j → M.mul (q i) (q j) = 0)
    ∧ M.embed ρ = ∑ i, p i • q i

end NCG.Jordan
