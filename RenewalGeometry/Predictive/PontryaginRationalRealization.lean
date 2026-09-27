/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Analysis.ResolventNeumannSeries
import RenewalGeometry.Predictive.RationalHermitianHankelForm
import RenewalGeometry.Predictive.HankelMinimality
import RenewalGeometry.Krein.SignedHaynsworthInertia

/-!
# Finite Pontryagin realizations of rational Hermitian dynamic functions

Paper `predictive_spectral_geometry`, labels `thm:supp-complete-rational-Krein`
(this file and `RationalKreinCanonicalRealization.lean`), with the negative-index
compression monotonicity used by `thm:supp-fibre-RG`.

A *finite Pontryagin realization* (`PontryaginRealization H N`) is a finite
dimensional Hilbert space `N` (the Hilbert majorant of the paper) carrying

* a Gram operator `J = J*`, invertible, defining the indefinite form
  `[x, y] = ⟪x, J y⟫` (`form`),
* a state operator `A` which is `J`-self-adjoint, `J A = A* J`,
* a source `Γ : H → N`.

Its output is `Γ⁺ = Γ* J`, its Laurent coefficients (Markov parameters) are
`M_n = Γ* J Aⁿ Γ` (`markov`, Hermitian by `markov_adjoint`) and its transfer
function is `Q(z) = Γ* J (A - z)⁻¹ Γ` (`transfer`).

Main results of this file:

* `transfer_eq_laurent` (`eq:supp-rational-realization`): for `‖A‖ < ‖z‖` the
  transfer function is the Laurent series `-∑ M_n z^{-n-1}` of
  `def:supp-rational-Hermitian`, i.e. `Q(z) = Γ⁺ (A - z)⁻¹ Γ` as an identity of
  functions on the region where the Laurent series is defined (rational
  continuation is the identity theorem for the two rational sides).
* `inner_nevanlinnaKernel` (`eq:supp-Nevanlinna-kernel`): the Nevanlinna kernel
  `N_Q(z, w) = (Q(z) - Q(w)*)/(z - w̄)` is the Pontryagin Gram of the
  resolvent-source vectors, `⟪u, N_Q(z,w) v⟫ = [(A - z̄)⁻¹ Γ u, (A - w̄)⁻¹ Γ v]`.
* `negIndex`: the negative index of a form (largest dimension of a negative
  definite subspace) with `negIndex_pullback_le` (a compression / congruence
  cannot increase the negative index — the mechanism of the paper's
  "every finite kernel Gram is a compression of the Pontryagin form") and
  `negIndex_pullback_eq_of_surjective`.
* `negInertia_kernelGram_eq_negIndex_pullback`: the negative inertia of a finite
  kernel Gram matrix equals the negative index of the pulled-back Pontryagin form.
* `negInertia_kernelGram_le_negIndex`: every finite kernel Gram (points in the
  upper half-plane, inside the resolvent set) has at most `negIndex form`
  negative eigenvalues.
-/

open scoped InnerProductSpace InnerProduct
open Filter Topology Matrix

noncomputable section

namespace RenewalGeometry

/-! ## Negative index of a form -/

section NegIndex

variable {N : Type*} [AddCommGroup N] [Module ℂ N]

/-- A subspace on which the form `B` is negative definite. -/
def IsNegativeSubspace (B : N → N → ℂ) (V : Submodule ℂ N) : Prop :=
  ∀ v ∈ V, v ≠ 0 → (B v v).re < 0

/-- The negative index of a form: the largest dimension of a negative definite
subspace (the number of negative squares of a Hermitian form; the Pontryagin
index of `thm:supp-complete-rational-Krein`). -/
noncomputable def negIndex (B : N → N → ℂ) : ℕ :=
  sSup {d | ∃ V : Submodule ℂ N, IsNegativeSubspace B V ∧ Module.finrank ℂ V = d}

theorem isNegativeSubspace_bot (B : N → N → ℂ) : IsNegativeSubspace B ⊥ :=
  fun v hv hv0 => absurd ((Submodule.mem_bot ℂ).mp hv) hv0

variable [FiniteDimensional ℂ N]

theorem negIndex_bddAbove (B : N → N → ℂ) :
    BddAbove {d | ∃ V : Submodule ℂ N, IsNegativeSubspace B V ∧ Module.finrank ℂ V = d} := by
  refine ⟨Module.finrank ℂ N, ?_⟩
  rintro d ⟨V, _, rfl⟩
  exact Submodule.finrank_le V

theorem finrank_le_negIndex {B : N → N → ℂ} {V : Submodule ℂ N} (hV : IsNegativeSubspace B V) :
    Module.finrank ℂ V ≤ negIndex B :=
  le_csSup (negIndex_bddAbove B) ⟨V, hV, rfl⟩

theorem negIndex_le {B : N → N → ℂ} {m : ℕ}
    (h : ∀ V : Submodule ℂ N, IsNegativeSubspace B V → Module.finrank ℂ V ≤ m) :
    negIndex B ≤ m := by
  refine csSup_le ⟨0, ⊥, isNegativeSubspace_bot B, finrank_bot ℂ N⟩ ?_
  rintro d ⟨V, hV, rfl⟩
  exact h V hV

theorem negIndex_le_finrank (B : N → N → ℂ) : negIndex B ≤ Module.finrank ℂ N :=
  negIndex_le fun V _ => Submodule.finrank_le V

/-- The pullback of a form along a linear map (a compression/congruence). -/
def pullbackForm {W : Type*} [AddCommGroup W] [Module ℂ W] (B : N → N → ℂ) (f : W →ₗ[ℂ] N) :
    W → W → ℂ :=
  fun x y => B (f x) (f y)

/-- **Compression monotonicity.**  Pulling a form back along a linear map cannot
increase its negative index (the form is assumed to vanish at the origin, as any
sesquilinear form does). -/
theorem negIndex_pullback_le {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (B : N → N → ℂ) (h0 : B 0 0 = 0) (f : W →ₗ[ℂ] N) :
    negIndex (pullbackForm B f) ≤ negIndex B := by
  apply negIndex_le
  intro V hV
  have hinj : Function.Injective (f.domRestrict V) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨v, hv⟩ hfv
    by_contra hne
    have hv0 : v ≠ 0 := fun h => hne (Subtype.ext h)
    have hneg := hV v hv hv0
    have hfv' : f v = 0 := hfv
    simp only [pullbackForm, hfv', h0, Complex.zero_re, lt_self_iff_false] at hneg
  have hmap : IsNegativeSubspace B (V.map f) := by
    rintro w hw hw0
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact hw0 (map_zero f)
    exact hV v hv hv0
  calc Module.finrank ℂ V = Module.finrank ℂ (LinearMap.range (f.domRestrict V)) :=
        (LinearMap.finrank_range_of_inj hinj).symm
    _ = Module.finrank ℂ (V.map f) := by rw [LinearMap.range_domRestrict]
    _ ≤ negIndex B := finrank_le_negIndex hmap

/-- Pulling back along a surjective linear map preserves the negative index. -/
theorem negIndex_pullback_eq_of_surjective {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (B : N → N → ℂ) (h0 : B 0 0 = 0) (f : W →ₗ[ℂ] N)
    (hf : LinearMap.range f = ⊤) :
    negIndex (pullbackForm B f) = negIndex B := by
  refine le_antisymm (negIndex_pullback_le B h0 f) ?_
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective f hf
  have hg' : ∀ v, f (g v) = v := fun v => LinearMap.congr_fun hg v
  apply negIndex_le
  intro V hV
  have hginj : Function.Injective (g.domRestrict V) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨v, hv⟩ hgv
    have hgv' : g v = 0 := hgv
    have : v = 0 := by rw [← hg' v, hgv', map_zero]
    exact Subtype.ext this
  have hmap : IsNegativeSubspace (pullbackForm B f) (V.map g) := by
    rintro w hw hw0
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact hw0 (map_zero g)
    simpa [pullbackForm, hg'] using hV v hv hv0
  calc Module.finrank ℂ V = Module.finrank ℂ (LinearMap.range (g.domRestrict V)) :=
        (LinearMap.finrank_range_of_inj hginj).symm
    _ = Module.finrank ℂ (V.map g) := by rw [LinearMap.range_domRestrict]
    _ ≤ negIndex (pullbackForm B f) := finrank_le_negIndex hmap

/-- Pulling back along a linear equivalence preserves the negative index. -/
theorem negIndex_pullback_equiv {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (B : N → N → ℂ) (h0 : B 0 0 = 0) (e : W ≃ₗ[ℂ] N) :
    negIndex (pullbackForm B (e : W →ₗ[ℂ] N)) = negIndex B :=
  negIndex_pullback_eq_of_surjective B h0 _ (LinearEquiv.range e)

end NegIndex

/-- The matrix negative inertia of `Krein/SignedHaynsworthInertia` is the
negative index of the matrix form `(v, w) ↦ star v ⬝ᵥ (G *ᵥ w)`. -/
theorem negInertia_eq_negIndex {n : Type} [Fintype n] [DecidableEq n] (G : Matrix n n ℂ) :
    negInertia G = negIndex (fun v w : n → ℂ => star v ⬝ᵥ (G *ᵥ w)) := by
  unfold negInertia posInertia negIndex
  congr 1
  ext d
  constructor
  · rintro ⟨V, hV, rfl⟩
    refine ⟨V, ?_, rfl⟩
    intro v hv hv0
    have := hV v hv hv0
    simp only [quadForm, Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re] at this
    linarith
  · rintro ⟨V, hV, rfl⟩
    refine ⟨V, ?_, rfl⟩
    intro v hv hv0
    have := hV v hv hv0
    simp only [quadForm, Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re]
    linarith

/-! ## Finite Pontryagin realizations -/

/-- **A finite Pontryagin realization** (`thm:supp-complete-rational-Krein`):
a Hilbert majorant `N` with an invertible self-adjoint Gram operator `J`
(indefinite form `[x, y] = ⟪x, J y⟫`), a `J`-self-adjoint state operator `A`
(`J A = A* J`) and a source `Γ : H → N`.  The output is `Γ⁺ = Γ* J`. -/
structure PontryaginRealization (H N : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N] where
  /-- The state operator `A`. -/
  A : N →L[ℂ] N
  /-- The source `Γ`. -/
  Γ : H →L[ℂ] N
  /-- The Gram operator `J` of the indefinite form. -/
  J : N →L[ℂ] N
  /-- `J = J*`. -/
  J_selfAdjoint : IsSelfAdjoint J
  /-- `J` is invertible (the form is nondegenerate). -/
  J_isUnit : IsUnit J
  /-- `A` is `J`-self-adjoint: `J A = A* J`. -/
  J_mul_A : J * A = star A * J

namespace PontryaginRealization

variable {H N : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N]
variable (P : PontryaginRealization H N)

/-- The indefinite (Pontryagin) form `[x, y] = ⟪x, J y⟫`. -/
def form (x y : N) : ℂ := ⟪x, P.J y⟫_ℂ

/-- The output `Γ⁺ = Γ* J`. -/
noncomputable def output : N →L[ℂ] H := P.Γ† ∘L P.J

/-- The Laurent coefficients (Markov parameters) `M_n = Γ* J Aⁿ Γ`. -/
noncomputable def markov (n : ℕ) : H →L[ℂ] H := ((P.Γ† ∘L P.J) ∘L P.A ^ n) ∘L P.Γ

/-- The transfer function `Q(z) = Γ* J (A - z)⁻¹ Γ` (`eq:supp-rational-realization`). -/
noncomputable def transfer (z : ℂ) : H →L[ℂ] H :=
  ((P.Γ† ∘L P.J) ∘L Ring.inverse (P.A - algebraMap ℂ (N →L[ℂ] N) z)) ∘L P.Γ

/-- The resolvent-source vector `(A - z)⁻¹ Γ h`. -/
noncomputable def resolventSource (z : ℂ) (h : H) : N :=
  Ring.inverse (P.A - algebraMap ℂ (N →L[ℂ] N) z) (P.Γ h)

theorem J_adjoint : P.J† = P.J := ContinuousLinearMap.isSelfAdjoint_iff'.mp P.J_selfAdjoint

theorem J_comp_A : P.J ∘L P.A = P.A† ∘L P.J := by
  have := P.J_mul_A
  rwa [ContinuousLinearMap.star_eq_adjoint] at this

@[simp] theorem form_zero_left (y : N) : P.form 0 y = 0 := by simp [form]

@[simp] theorem form_zero_right (x : N) : P.form x 0 = 0 := by simp [form]

theorem form_add_left (x x' y : N) : P.form (x + x') y = P.form x y + P.form x' y := by
  simp [form, inner_add_left]

theorem form_add_right (x y y' : N) : P.form x (y + y') = P.form x y + P.form x y' := by
  simp [form, inner_add_right]

theorem form_smul_left (c : ℂ) (x y : N) : P.form (c • x) y = starRingEnd ℂ c * P.form x y := by
  simp [form, inner_smul_left, mul_comm]

theorem form_smul_right (c : ℂ) (x y : N) : P.form x (c • y) = c * P.form x y := by
  simp [form, inner_smul_right]

theorem form_sum_left {ι : Type*} (s : Finset ι) (x : ι → N) (y : N) :
    P.form (∑ i ∈ s, x i) y = ∑ i ∈ s, P.form (x i) y := by
  simp [form, sum_inner]

theorem form_sum_right {ι : Type*} (s : Finset ι) (x : N) (y : ι → N) :
    P.form x (∑ i ∈ s, y i) = ∑ i ∈ s, P.form x (y i) := by
  simp [form, inner_sum]

/-- Hermitian symmetry of the Pontryagin form. -/
theorem form_conj_symm (x y : N) : P.form y x = starRingEnd ℂ (P.form x y) := by
  unfold form
  rw [← inner_conj_symm]
  congr 1
  conv_lhs => rw [← P.J_adjoint]
  rw [ContinuousLinearMap.adjoint_inner_left]

/-- The form is nondegenerate: `[x, y] = 0` for all `x` forces `y = 0`. -/
theorem eq_zero_of_form_eq_zero {y : N} (h : ∀ x, P.form x y = 0) : y = 0 := by
  have hJ : P.J y = 0 := by
    apply ext_inner_left ℂ
    intro v
    simpa [form] using h v
  obtain ⟨u, hu⟩ := P.J_isUnit
  have := congrArg (fun T : N →L[ℂ] N => T y) (Units.inv_mul u)
  simp only [mul_apply_eq_comp, one_apply_eq_self] at this
  rw [hu, hJ, map_zero] at this
  exact this.symm

/-- `A` is symmetric for the Pontryagin form. -/
theorem form_A_left (x y : N) : P.form (P.A x) y = P.form x (P.A y) := by
  unfold form
  rw [← ContinuousLinearMap.adjoint_inner_right]
  congr 1
  change (P.A† ∘L P.J) y = (P.J ∘L P.A) y
  rw [P.J_comp_A]

theorem form_pow_A_left (n : ℕ) (x y : N) : P.form ((P.A ^ n) x) y = P.form x ((P.A ^ n) y) := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp, mul_apply_eq_comp, form_A_left, ih,
        ← mul_apply_eq_comp, ← mul_apply_eq_comp, ← pow_succ, ← pow_succ']

/-- The Markov parameters read the Pontryagin form on the power-cyclic vectors:
`⟪u, M_{i+j} v⟫ = [Aⁱ Γ u, Aʲ Γ v]`. -/
theorem inner_markov (i j : ℕ) (u v : H) :
    ⟪u, P.markov (i + j) v⟫_ℂ = P.form ((P.A ^ i) (P.Γ u)) ((P.A ^ j) (P.Γ v)) := by
  rw [form_pow_A_left]
  unfold markov form
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  congr 2
  rw [← mul_apply_eq_comp, ← pow_add]

/-- The Markov parameters are Hermitian (`eq:supp-rational-Laurent`, `M_n = M_n*`). -/
theorem markov_adjoint (n : ℕ) : (P.markov n)† = P.markov n := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro u v
  rw [← inner_conj_symm]
  have h1 : ⟪v, P.markov n u⟫_ℂ = P.form ((P.A ^ 0) (P.Γ v)) ((P.A ^ n) (P.Γ u)) := by
    rw [← inner_markov, zero_add]
  have h2 : ⟪u, P.markov n v⟫_ℂ = P.form ((P.A ^ 0) (P.Γ u)) ((P.A ^ n) (P.Γ v)) := by
    rw [← inner_markov, zero_add]
  rw [h1, h2, pow_zero, one_apply_eq_self, one_apply_eq_self, ← form_pow_A_left,
    form_conj_symm, starRingEnd_self_apply]

theorem markov_isSymmetric (n : ℕ) : (P.markov n : H →ₗ[ℂ] H).IsSymmetric := by
  intro u v
  have := ContinuousLinearMap.adjoint_inner_left (P.markov n) v u
  rw [P.markov_adjoint] at this
  simpa using this

/-- The continuous linear map `X ↦ Γ* J X Γ` on the operator algebra. -/
noncomputable def sandwich : (N →L[ℂ] N) →L[ℂ] (H →L[ℂ] H) :=
  ((ContinuousLinearMap.compL ℂ H N H).flip P.Γ).comp
    (ContinuousLinearMap.compL ℂ N N H (P.Γ† ∘L P.J))

@[simp] theorem sandwich_apply (X : N →L[ℂ] N) :
    P.sandwich X = ((P.Γ† ∘L P.J) ∘L X) ∘L P.Γ := by
  simp [sandwich, ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]

/-- **`eq:supp-rational-realization`.**  For `‖A‖ < ‖z‖` the transfer function
`Γ* J (A - z)⁻¹ Γ` is the Laurent series `-∑_{n ≥ 0} M_n z^{-n-1}` of
`def:supp-rational-Hermitian` built from the Markov parameters. -/
theorem transfer_eq_laurent [FiniteDimensional ℂ H] {z : ℂ} (hz : ‖P.A‖ < ‖z‖) :
    P.transfer z = laurentDynamicFunction (fun n => (P.markov n : H →ₗ[ℂ] H)) z := by
  have hcoe : ∀ n, LinearMap.toContinuousLinearMap ((P.markov n : H →ₗ[ℂ] H)) = P.markov n := by
    intro n
    ext x
    simp
  unfold laurentDynamicFunction
  simp_rw [hcoe]
  have hsum := summable_resolvent_neumann P.A hz
  have h1 : P.transfer z = P.sandwich (Ring.inverse (P.A - algebraMap ℂ (N →L[ℂ] N) z)) := by
    rw [sandwich_apply]; rfl
  rw [h1, inverse_sub_algebraMap_eq_neg_tsum P.A hz, map_neg, P.sandwich.map_tsum hsum]
  congr 1
  apply tsum_congr
  intro n
  rw [map_smul, sandwich_apply]
  rfl

/-! ### Resolvents and adjoints -/

/-- `star (A - z) = A* - z̄`. -/
theorem star_sub_algebraMap (z : ℂ) :
    star (P.A - algebraMap ℂ (N →L[ℂ] N) z) = P.A† - algebraMap ℂ (N →L[ℂ] N) (starRingEnd ℂ z) := by
  rw [star_sub, ContinuousLinearMap.star_eq_adjoint, Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one, star_smul, star_one]
  rfl

/-- `J (A - z̄) = star (A - z) J`. -/
theorem J_mul_sub_conj (z : ℂ) :
    P.J * (P.A - algebraMap ℂ (N →L[ℂ] N) (starRingEnd ℂ z)) =
      star (P.A - algebraMap ℂ (N →L[ℂ] N) z) * P.J := by
  rw [star_sub_algebraMap, mul_sub, sub_mul, ← ContinuousLinearMap.star_eq_adjoint, P.J_mul_A,
    Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]

/-- `A - z̄` is a unit whenever `A - z` is (conjugation by `J` and the star). -/
theorem isUnit_sub_conj {z : ℂ} (hz : IsUnit (P.A - algebraMap ℂ (N →L[ℂ] N) z)) :
    IsUnit (P.A - algebraMap ℂ (N →L[ℂ] N) (starRingEnd ℂ z)) := by
  obtain ⟨u, hu⟩ := P.J_isUnit
  have hstar : IsUnit (star (P.A - algebraMap ℂ (N →L[ℂ] N) z)) := isUnit_star.mpr hz
  have hprod : IsUnit ((u⁻¹ : (N →L[ℂ] N)ˣ) * (star (P.A - algebraMap ℂ (N →L[ℂ] N) z) * u)) :=
    (Units.isUnit_units_mul _ _).mpr ((Units.isUnit_mul_units _ _).mpr hstar)
  have heq : ((u⁻¹ : (N →L[ℂ] N)ˣ) : N →L[ℂ] N) * (star (P.A - algebraMap ℂ (N →L[ℂ] N) z) * u) =
      P.A - algebraMap ℂ (N →L[ℂ] N) (starRingEnd ℂ z) := by
    rw [hu, ← P.J_mul_sub_conj, ← mul_assoc, ← hu, Units.inv_mul, one_mul]
  rwa [heq] at hprod

/-- `(A - z)⁻¹* J = J (A - z̄)⁻¹` whenever `A - z` is a unit. -/
theorem star_inverse_mul_J {z : ℂ} (hz : IsUnit (P.A - algebraMap ℂ (N →L[ℂ] N) z)) :
    star (Ring.inverse (P.A - algebraMap ℂ (N →L[ℂ] N) z)) * P.J =
      P.J * Ring.inverse (P.A - algebraMap ℂ (N →L[ℂ] N) (starRingEnd ℂ z)) := by
  set X := P.A - algebraMap ℂ (N →L[ℂ] N) z with hX
  set Y := P.A - algebraMap ℂ (N →L[ℂ] N) (starRingEnd ℂ z) with hY
  have hYu : IsUnit Y := P.isUnit_sub_conj hz
  have h1 : star (Ring.inverse X) * star X = 1 := by
    rw [← star_mul, Ring.mul_inverse_cancel X hz, star_one]
  have h2 : P.J = star X * P.J * Ring.inverse Y := by
    rw [← P.J_mul_sub_conj, mul_assoc, Ring.mul_inverse_cancel Y hYu, mul_one]
  calc star (Ring.inverse X) * P.J = star (Ring.inverse X) * (star X * P.J * Ring.inverse Y) := by
        rw [← h2]
    _ = (star (Ring.inverse X) * star X) * (P.J * Ring.inverse Y) := by
        simp only [mul_assoc]
    _ = P.J * Ring.inverse Y := by rw [h1, one_mul]

/-- The adjoint of the transfer function: `Q(w)* = Γ* J (A - w̄)⁻¹ Γ`. -/
theorem transfer_adjoint {w : ℂ} (hw : IsUnit (P.A - algebraMap ℂ (N →L[ℂ] N) w)) :
    (P.transfer w)† = P.transfer (starRingEnd ℂ w) := by
  unfold transfer
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint, P.J_adjoint]
  have := P.star_inverse_mul_J hw
  rw [ContinuousLinearMap.star_eq_adjoint] at this
  change (P.Γ† ∘L ((Ring.inverse (P.A - algebraMap ℂ (N →L[ℂ] N) w))† ∘L P.J)) ∘L P.Γ = _
  rw [← ContinuousLinearMap.mul_def, this, ContinuousLinearMap.mul_def]
  rfl

/-- The Nevanlinna kernel `N_Q(z, w) = (Q(z) - Q(w)*)/(z - w̄)` of a matrix
function `Q` (`eq:supp-Nevanlinna-kernel`). -/
noncomputable def nevanlinnaKernel (Q : ℂ → H →L[ℂ] H) (z w : ℂ) : H →L[ℂ] H :=
  (z - starRingEnd ℂ w)⁻¹ • (Q z - (Q w)†)

/-- **`eq:supp-Nevanlinna-kernel` as a Pontryagin Gram.**  For `z ≠ w̄` in the
resolvent set, `⟪u, N_Q(z, w) v⟫ = [(A - z̄)⁻¹ Γ u, (A - w̄)⁻¹ Γ v]`. -/
theorem inner_nevanlinnaKernel {z w : ℂ} (hz : IsUnit (P.A - algebraMap ℂ (N →L[ℂ] N) z))
    (hw : IsUnit (P.A - algebraMap ℂ (N →L[ℂ] N) w)) (hzw : z ≠ starRingEnd ℂ w) (u v : H) :
    ⟪u, nevanlinnaKernel P.transfer z w v⟫_ℂ =
      P.form (P.resolventSource (starRingEnd ℂ z) u) (P.resolventSource (starRingEnd ℂ w) v) := by
  set Rz := Ring.inverse (P.A - algebraMap ℂ (N →L[ℂ] N) z) with hRz
  set Rw' := Ring.inverse (P.A - algebraMap ℂ (N →L[ℂ] N) (starRingEnd ℂ w)) with hRw'
  have hw' : IsUnit (P.A - algebraMap ℂ (N →L[ℂ] N) (starRingEnd ℂ w)) := P.isUnit_sub_conj hw
  have hdiff : P.transfer z - (P.transfer w)† = (z - starRingEnd ℂ w) • P.sandwich (Rz * Rw') := by
    rw [P.transfer_adjoint hw]
    have : P.transfer z - P.transfer (starRingEnd ℂ w) = P.sandwich (Rz - Rw') := by
      rw [map_sub, sandwich_apply, sandwich_apply]; rfl
    rw [this, resolvent_sub_resolvent P.A hz hw', map_smul]
  have hne : z - starRingEnd ℂ w ≠ 0 := sub_ne_zero.mpr hzw
  unfold nevanlinnaKernel
  rw [hdiff, smul_smul, inv_mul_cancel₀ hne, one_smul, sandwich_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
  have hstar := P.star_inverse_mul_J hz
  rw [ContinuousLinearMap.star_eq_adjoint] at hstar
  have hstar' : (Rz†) (P.J (P.Γ u)) = P.J (Ring.inverse
      (P.A - algebraMap ℂ (N →L[ℂ] N) (starRingEnd ℂ z)) (P.Γ u)) := by
    have := congrArg (fun T : N →L[ℂ] N => T (P.Γ u)) hstar
    simpa [mul_apply_eq_comp] using this
  calc ⟪P.Γ u, P.J (Rz (Rw' (P.Γ v)))⟫_ℂ = ⟪P.J (P.Γ u), Rz (Rw' (P.Γ v))⟫_ℂ := by
        conv_lhs => rw [← P.J_adjoint]
        rw [ContinuousLinearMap.adjoint_inner_right]
    _ = ⟪(Rz†) (P.J (P.Γ u)), Rw' (P.Γ v)⟫_ℂ := by
        rw [ContinuousLinearMap.adjoint_inner_left]
    _ = ⟪P.J (Ring.inverse (P.A - algebraMap ℂ (N →L[ℂ] N) (starRingEnd ℂ z)) (P.Γ u)),
          Rw' (P.Γ v)⟫_ℂ := by rw [hstar']
    _ = P.form (P.resolventSource (starRingEnd ℂ z) u) (P.resolventSource (starRingEnd ℂ w) v) := by
        unfold form resolventSource
        conv_lhs => rw [← P.J_adjoint]
        rw [ContinuousLinearMap.adjoint_inner_left]

/-! ### Kernel Grams as compressions of the Pontryagin form -/

/-- The Gram matrix of a kernel `K` at points `z i` with vectors `h i`:
`G i j = ⟪h i, K (z i) (z j) (h j)⟫`. -/
noncomputable def kernelGram (K : ℂ → ℂ → H →L[ℂ] H) {ι : Type*} [Fintype ι]
    (z : ι → ℂ) (h : ι → H) : Matrix ι ι ℂ :=
  Matrix.of fun i j => ⟪h i, K (z i) (z j) (h j)⟫_ℂ

/-- The linear combination map `c ↦ ∑ c i • x i` of a finite family. -/
noncomputable def combinationMap {ι : Type*} [Fintype ι] (x : ι → N) : (ι → ℂ) →ₗ[ℂ] N :=
  Fintype.linearCombination ℂ x

theorem combinationMap_apply {ι : Type*} [Fintype ι] (x : ι → N) (c : ι → ℂ) :
    combinationMap x c = ∑ i, c i • x i :=
  Fintype.linearCombination_apply ℂ x c

/-- The Pontryagin form on linear combinations is the matrix form of the Gram
matrix `G i j = [x i, x j]`. -/
theorem form_combination (ι : Type*) [Fintype ι] (x : ι → N) (c d : ι → ℂ) :
    P.form (combinationMap x c) (combinationMap x d) =
      star c ⬝ᵥ ((Matrix.of fun i j => P.form (x i) (x j)) *ᵥ d) := by
  rw [combinationMap_apply, combinationMap_apply, form_sum_left]
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [form_smul_left, form_sum_right, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [form_smul_right]
  simp only [Complex.star_def]
  ring

/-- The negative inertia of a Gram matrix of the Pontryagin form on a finite
family `x` is the negative index of the form pulled back along `c ↦ ∑ c i • x i`. -/
theorem negInertia_gram_eq_negIndex_pullback {ι : Type} [Fintype ι] [DecidableEq ι] (x : ι → N) :
    negInertia (Matrix.of fun i j => P.form (x i) (x j)) =
      negIndex (pullbackForm P.form (combinationMap x)) := by
  rw [negInertia_eq_negIndex]
  congr 1
  funext c d
  rw [pullbackForm, form_combination]

/-- **Every finite kernel Gram is a compression of the Pontryagin form**: for
points `z i` in the upper half-plane and in the resolvent set, the Nevanlinna
kernel Gram is the Gram of the form on the resolvent-source vectors
`(A - z̄ᵢ)⁻¹ Γ hᵢ`. -/
theorem kernelGram_eq_gram_resolventSource {ι : Type*} [Fintype ι] (z : ι → ℂ) (h : ι → H)
    (hupper : ∀ i, 0 < (z i).im) (hunit : ∀ i, IsUnit (P.A - algebraMap ℂ (N →L[ℂ] N) (z i))) :
    kernelGram (nevanlinnaKernel P.transfer) z h =
      Matrix.of fun i j => P.form (P.resolventSource (starRingEnd ℂ (z i)) (h i))
        (P.resolventSource (starRingEnd ℂ (z j)) (h j)) := by
  ext i j
  simp only [kernelGram, Matrix.of_apply]
  apply P.inner_nevanlinnaKernel (hunit i) (hunit j)
  intro heq
  have h1 := hupper i
  have h2 := hupper j
  rw [heq, Complex.conj_im] at h1
  linarith

/-- The negative inertia of a Nevanlinna kernel Gram (upper half-plane points in
the resolvent set) is the negative index of the compressed Pontryagin form. -/
theorem negInertia_kernelGram_eq_negIndex_pullback {ι : Type} [Fintype ι] [DecidableEq ι]
    (z : ι → ℂ) (h : ι → H) (hupper : ∀ i, 0 < (z i).im)
    (hunit : ∀ i, IsUnit (P.A - algebraMap ℂ (N →L[ℂ] N) (z i))) :
    negInertia (kernelGram (nevanlinnaKernel P.transfer) z h) =
      negIndex (pullbackForm P.form
        (combinationMap fun i => P.resolventSource (starRingEnd ℂ (z i)) (h i))) := by
  rw [P.kernelGram_eq_gram_resolventSource z h hupper hunit,
    negInertia_gram_eq_negIndex_pullback]

/-- **Compression bound.**  Every finite Nevanlinna kernel Gram has at most
`negIndex form` negative eigenvalues. -/
theorem negInertia_kernelGram_le_negIndex [FiniteDimensional ℂ N] {ι : Type} [Fintype ι]
    [DecidableEq ι] (z : ι → ℂ) (h : ι → H) (hupper : ∀ i, 0 < (z i).im)
    (hunit : ∀ i, IsUnit (P.A - algebraMap ℂ (N →L[ℂ] N) (z i))) :
    negInertia (kernelGram (nevanlinnaKernel P.transfer) z h) ≤ negIndex P.form := by
  rw [P.negInertia_kernelGram_eq_negIndex_pullback z h hupper hunit]
  exact negIndex_pullback_le P.form (P.form_zero_left 0) _

/-! ### Source cyclicity and the resolvent-source span

The paper's "power-cyclic span equals resolvent-source span" (source
minimality): the source vectors lie in the closed span of the resolvent-source
vectors along any ray to infinity, and that span is `A`-invariant. -/

/-- Source cyclicity (minimality of a Pontryagin realization): the power-cyclic
span of `Γ H` is the whole state space. -/
def IsCyclic : Prop :=
  Submodule.span ℂ (Set.range fun p : ℕ × H => (P.A ^ p.1) (P.Γ p.2)) = ⊤

/-- The span of the resolvent-source vectors `(A - w)⁻¹ Γ h` over `w ∈ D`. -/
def resolventSourceSpan (D : Set ℂ) : Submodule ℂ N :=
  Submodule.span ℂ (Set.range fun p : D × H => P.resolventSource (p.1 : ℂ) p.2)

theorem resolventSource_mem_span {D : Set ℂ} {w : ℂ} (hw : w ∈ D) (h : H) :
    P.resolventSource w h ∈ P.resolventSourceSpan D :=
  Submodule.subset_span ⟨(⟨w, hw⟩, h), rfl⟩

/-- `A (A - w)⁻¹ Γ h = Γ h + w (A - w)⁻¹ Γ h`. -/
theorem A_resolventSource {w : ℂ} (hw : IsUnit (P.A - algebraMap ℂ (N →L[ℂ] N) w)) (h : H) :
    P.A (P.resolventSource w h) = P.Γ h + w • P.resolventSource w h := by
  have h1 := Ring.mul_inverse_cancel _ hw
  set R := Ring.inverse (P.A - algebraMap ℂ (N →L[ℂ] N) w) with hR
  have h2 : P.A * R = 1 + w • R := by
    rw [← h1, sub_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, sub_add_cancel]
  have := congrArg (fun T : N →L[ℂ] N => T (P.Γ h)) h2
  simpa [mul_apply_eq_comp, resolventSource] using this

theorem norm_one_le : ‖(1 : N →L[ℂ] N)‖ ≤ 1 := ContinuousLinearMap.norm_id_le

variable [FiniteDimensional ℂ N]

/-- The source vectors lie in the resolvent-source span whenever `D` contains a
ray `-t i`, `t ≥ t₀`, to infinity (limit `-w (A - w)⁻¹ Γ h → Γ h`). -/
theorem Γ_mem_resolventSourceSpan {D : Set ℂ} (t₀ : ℝ) (ht₀ : ‖P.A‖ < t₀)
    (hD : ∀ t : ℝ, t₀ ≤ t → -((t : ℂ)) * Complex.I ∈ D) (h : H) :
    P.Γ h ∈ P.resolventSourceSpan D := by
  set w : ℕ → ℂ := fun k => -((((k : ℝ) + t₀ : ℝ) : ℂ)) * Complex.I with hw
  have hpos : ∀ k : ℕ, 0 ≤ (k : ℝ) + t₀ := fun k => by
    have := norm_nonneg P.A
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hnorm : ∀ k : ℕ, ‖w k‖ = (k : ℝ) + t₀ := by
    intro k
    show ‖-((((k : ℝ) + t₀ : ℝ) : ℂ)) * Complex.I‖ = (k : ℝ) + t₀
    rw [norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hpos k)]
  have hwD : ∀ k, w k ∈ D := fun k => hD _ (by
    have := Nat.cast_nonneg (α := ℝ) k
    linarith)
  have htend_norm : Tendsto (fun k => ‖w k‖) atTop atTop := by
    simp_rw [hnorm]
    exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hop := tendsto_neg_smul_inverse_sub_algebraMap P.A norm_one_le w htend_norm
  have hev := ((ContinuousLinearMap.apply ℂ N (P.Γ h)).continuous.tendsto _).comp hop
  have htend : Tendsto (fun k => (-(w k)) • P.resolventSource (w k) h) atTop (𝓝 (P.Γ h)) := by
    refine hev.congr ?_
    intro k
    simp [resolventSource]
  have hmem : ∀ k, (-(w k)) • P.resolventSource (w k) h ∈ P.resolventSourceSpan D :=
    fun k => Submodule.smul_mem _ _ (P.resolventSource_mem_span (hwD k) h)
  exact (Submodule.closed_of_finiteDimensional (P.resolventSourceSpan D)).mem_of_tendsto htend
    (Eventually.of_forall hmem)

/-- The resolvent-source span is `A`-invariant once it contains the sources. -/
theorem A_mem_resolventSourceSpan {D : Set ℂ}
    (hD : ∀ w ∈ D, IsUnit (P.A - algebraMap ℂ (N →L[ℂ] N) w))
    (hΓ : ∀ h, P.Γ h ∈ P.resolventSourceSpan D) {x : N} (hx : x ∈ P.resolventSourceSpan D) :
    P.A x ∈ P.resolventSourceSpan D := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨⟨⟨w, hw⟩, h⟩, rfl⟩ := hx
      show P.A (P.resolventSource w h) ∈ _
      rw [P.A_resolventSource (hD w hw)]
      exact Submodule.add_mem _ (hΓ h) (Submodule.smul_mem _ _ (P.resolventSource_mem_span hw h))
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-- **Resolvent-source span = power-cyclic span.**  For a source-cyclic
realization the resolvent-source vectors over a ray to infinity span the
whole state space. -/
theorem resolventSourceSpan_eq_top (hcyc : P.IsCyclic) {D : Set ℂ}
    (hD : ∀ w ∈ D, IsUnit (P.A - algebraMap ℂ (N →L[ℂ] N) w))
    (hΓ : ∀ h, P.Γ h ∈ P.resolventSourceSpan D) :
    P.resolventSourceSpan D = ⊤ := by
  apply top_unique
  rw [← hcyc, Submodule.span_le]
  rintro _ ⟨⟨n, h⟩, rfl⟩
  show (P.A ^ n) (P.Γ h) ∈ _
  induction n with
  | zero => simpa using hΓ h
  | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp]
      exact P.A_mem_resolventSourceSpan hD hΓ ih

/-- From a spanning set one extracts a finite spanning family. -/
theorem exists_finite_spanning_family {s : Set N} (hs : Submodule.span ℂ s = ⊤) :
    ∃ (ι : Type) (_ : Fintype ι) (x : ι → N),
      (∀ i, x i ∈ s) ∧ Submodule.span ℂ (Set.range x) = ⊤ := by
  classical
  let b := Module.finBasis ℂ N
  have hb : ∀ k, b k ∈ Submodule.span ℂ s := fun k => hs ▸ Submodule.mem_top
  choose n f g hfg using fun k => Submodule.mem_span_set'.mp (hb k)
  refine ⟨Σ k, Fin (n k), inferInstance, fun p => (g p.1 p.2 : N), fun p => (g p.1 p.2).2, ?_⟩
  apply top_unique
  rw [← b.span_eq, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  rw [← hfg k]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨k, i⟩, rfl⟩)

/-- **Attainment of the negative index by a kernel Gram.**  For a source-cyclic
realization there is a finite family of upper-half-plane points `z i` (with
`z̄ i` in a prescribed lower-half-plane set `D` containing a ray to infinity)
and vectors `h i` whose Nevanlinna kernel Gram has exactly `negIndex form`
negative eigenvalues. -/
theorem exists_kernelGram_negInertia_eq (hcyc : P.IsCyclic) (t₀ : ℝ) (ht₀ : ‖P.A‖ < t₀)
    (D : Set ℂ) (hDim : ∀ w ∈ D, w.im < 0)
    (hDu : ∀ w ∈ D, IsUnit (P.A - algebraMap ℂ (N →L[ℂ] N) w))
    (hD : ∀ t : ℝ, t₀ ≤ t → -((t : ℂ)) * Complex.I ∈ D) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (z : ι → ℂ) (h : ι → H),
      (∀ i, starRingEnd ℂ (z i) ∈ D) ∧
      negInertia (kernelGram (nevanlinnaKernel P.transfer) z h) = negIndex P.form := by
  classical
  have hΓ : ∀ h, P.Γ h ∈ P.resolventSourceSpan D := fun h =>
    P.Γ_mem_resolventSourceSpan t₀ ht₀ hD h
  have htop := P.resolventSourceSpan_eq_top hcyc hDu hΓ
  obtain ⟨ι, hι, x, hxs, hxspan⟩ := exists_finite_spanning_family htop
  choose p hp using fun i => hxs i
  refine ⟨ι, hι, inferInstance, fun i => starRingEnd ℂ ((p i).1 : ℂ), fun i => (p i).2,
    fun i => by simpa using (p i).1.2, ?_⟩
  have hupper : ∀ i, 0 < (starRingEnd ℂ ((p i).1 : ℂ)).im := by
    intro i
    rw [Complex.conj_im]
    have := hDim _ (p i).1.2
    linarith
  have hunit : ∀ i, IsUnit (P.A - algebraMap ℂ (N →L[ℂ] N) (starRingEnd ℂ ((p i).1 : ℂ))) :=
    fun i => P.isUnit_sub_conj (hDu _ (p i).1.2)
  rw [P.negInertia_kernelGram_eq_negIndex_pullback _ _ hupper hunit]
  have hfam : (fun i => P.resolventSource (starRingEnd ℂ (starRingEnd ℂ ((p i).1 : ℂ))) (p i).2) =
      x := by
    funext i
    rw [starRingEnd_self_apply]
    exact hp i
  rw [hfam]
  apply negIndex_pullback_eq_of_surjective P.form (P.form_zero_left 0)
  rw [combinationMap, Fintype.range_linearCombination, hxspan]

/-- The number of negative squares of a kernel on a domain `D`: the supremum of
the negative inertia of its finite Gram matrices at points of `D`
(`thm:supp-complete-rational-Krein`, "the Nevanlinna kernel has exactly that
many negative squares"). -/
noncomputable def negSquares (K : ℂ → ℂ → H →L[ℂ] H) (D : Set ℂ) : ℕ :=
  sSup {κ | ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (z : ι → ℂ) (h : ι → H),
    (∀ i, z i ∈ D) ∧ negInertia (kernelGram K z h) = κ}

theorem negSquares_le {K : ℂ → ℂ → H →L[ℂ] H} {D : Set ℂ} {m : ℕ}
    (hm : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (z : ι → ℂ) (h : ι → H),
      (∀ i, z i ∈ D) → negInertia (kernelGram K z h) ≤ m) :
    negSquares K D ≤ m := by
  refine csSup_le ⟨_, PEmpty, inferInstance, inferInstance, fun i => i.elim, fun i => i.elim,
    fun i => i.elim, rfl⟩ ?_
  rintro κ ⟨ι, _, _, z, h, hz, rfl⟩
  exact hm ι z h hz

theorem le_negSquares {K : ℂ → ℂ → H →L[ℂ] H} {D : Set ℂ} {m : ℕ}
    (hbdd : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (z : ι → ℂ) (h : ι → H),
      (∀ i, z i ∈ D) → negInertia (kernelGram K z h) ≤ m)
    (ι : Type) [Fintype ι] [DecidableEq ι] (z : ι → ℂ) (h : ι → H) (hz : ∀ i, z i ∈ D)
    (hκ : negInertia (kernelGram K z h) = m) :
    m ≤ negSquares K D := by
  refine le_csSup ⟨m, ?_⟩ ⟨ι, inferInstance, inferInstance, z, h, hz, hκ⟩
  rintro κ ⟨ι', _, _, z', h', hz', rfl⟩
  exact hbdd ι' z' h' hz'

/-- The upper half-plane part of the resolvent set of `A`. -/
def upperResolventSet : Set ℂ :=
  {z | 0 < z.im ∧ IsUnit (P.A - algebraMap ℂ (N →L[ℂ] N) z)}

/-- **Negative squares of the Nevanlinna kernel.**  For a source-cyclic finite
Pontryagin realization, the Nevanlinna kernel of its transfer function on the
upper half-plane (inside the resolvent set) has exactly `negIndex form`
negative squares. -/
theorem negSquares_transfer_eq_negIndex (hcyc : P.IsCyclic) :
    negSquares (nevanlinnaKernel P.transfer) P.upperResolventSet = negIndex P.form := by
  have hbdd : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (z : ι → ℂ) (h : ι → H),
      (∀ i, z i ∈ P.upperResolventSet) →
        negInertia (kernelGram (nevanlinnaKernel P.transfer) z h) ≤ negIndex P.form := by
    intro ι _ _ z h hz
    exact P.negInertia_kernelGram_le_negIndex z h (fun i => (hz i).1) (fun i => (hz i).2)
  apply le_antisymm (negSquares_le hbdd)
  set D : Set ℂ := {w | w.im < 0 ∧ IsUnit (P.A - algebraMap ℂ (N →L[ℂ] N) w)} with hDdef
  have hDim : ∀ w ∈ D, w.im < 0 := fun w hw => hw.1
  have hDu : ∀ w ∈ D, IsUnit (P.A - algebraMap ℂ (N →L[ℂ] N) w) := fun w hw => hw.2
  have hD : ∀ t : ℝ, ‖P.A‖ + 1 ≤ t → -((t : ℂ)) * Complex.I ∈ D := by
    intro t ht
    have hApos := norm_nonneg P.A
    refine ⟨?_, ?_⟩
    · simp only [Complex.mul_im, Complex.neg_re, Complex.ofReal_re, Complex.I_im, mul_one,
        Complex.neg_im, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
      linarith
    · apply isUnit_sub_algebraMap_of_norm_lt
      rw [norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith)]
      linarith
  obtain ⟨ι, _, _, z, h, hz, hκ⟩ :=
    P.exists_kernelGram_negInertia_eq hcyc (‖P.A‖ + 1) (by linarith) D hDim hDu hD
  refine le_negSquares hbdd ι z h ?_ hκ
  intro i
  have h1 := (hz i).1
  have h2 := P.isUnit_sub_conj (hz i).2
  rw [Complex.conj_im] at h1
  rw [starRingEnd_self_apply] at h2
  exact ⟨by linarith, h2⟩

end PontryaginRealization

end RenewalGeometry

end
