/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AtomicReset

/-!
# Atomic resets on finite generating ordered cones

This module supplies the ordered-cone and completely-positive clauses of
`thm:atomic-reset-characterization`.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Kronecker

namespace NCG

/-- A convex cone which generates its ambient real vector space. -/
structure GeneratingCone (V : Type*) [AddCommGroup V] [Module ℝ V] where
  carrier : Set V
  zero_mem : 0 ∈ carrier
  add_mem : ∀ {x y}, x ∈ carrier → y ∈ carrier → x + y ∈ carrier
  smul_mem : ∀ {a : ℝ} (ha : 0 ≤ a) {x}, x ∈ carrier → a • x ∈ carrier
  generating : ∀ x : V, ∃ p ∈ carrier, ∃ q ∈ carrier, x = p - q

/-- A strictly positive normalization functional on a generating cone. -/
structure StrictConeFunctional {V : Type*} [AddCommGroup V] [Module ℝ V]
    (C : GeneratingCone V) where
  toLinearMap : V →ₗ[ℝ] ℝ
  nonneg : ∀ {x}, x ∈ C.carrier → 0 ≤ toLinearMap x
  pos : ∀ {x}, x ∈ C.carrier → x ≠ 0 → 0 < toLinearMap x

instance {V : Type*} [AddCommGroup V] [Module ℝ V] {C : GeneratingCone V} :
    CoeFun (StrictConeFunctional C) (fun _ => V → ℝ) :=
  ⟨fun u => u.toLinearMap⟩

/-- Positivity of a linear branch between the two ordered spaces. -/
def ConePositive {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (CV : GeneratingCone V)
    (CW : GeneratingCone W) (R : V →ₗ[ℝ] W) : Prop :=
  ∀ ⦃x⦄, x ∈ CV.carrier → R x ∈ CW.carrier

/-- Every occurring positive input has the same normalized output `ω`. -/
def HasCommonNormalizedOutput {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (CV : GeneratingCone V)
    {CW : GeneratingCone W} (u : StrictConeFunctional CW)
    (R : V →ₗ[ℝ] W) (ω : W) : Prop :=
  ∀ ⦃x⦄, x ∈ CV.carrier → R x ≠ 0 →
    (u (R x))⁻¹ • R x = ω

/-- Atomic factorization by a positive functional and one normalized output. -/
def HasPositiveAtomicFactorization {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (CV : GeneratingCone V)
    (CW : GeneratingCone W) (u : StrictConeFunctional CW)
    (R : V →ₗ[ℝ] W) : Prop :=
  ∃ (ℓ : V →ₗ[ℝ] ℝ) (ω : W), ℓ ≠ 0
    ∧ (∀ ⦃x⦄, x ∈ CV.carrier → 0 ≤ ℓ x)
    ∧ ω ∈ CW.carrier ∧ u ω = 1 ∧ ω ≠ 0
    ∧ ∀ x, R x = ℓ x • ω

private theorem normalized_output_on_cone {V W : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (CV : GeneratingCone V) {CW : GeneratingCone W}
    (u : StrictConeFunctional CW) (R : V →ₗ[ℝ] W) (ω : W)
    (hRpos : ConePositive CV CW R)
    (hω : u ω = 1) (hcommon : HasCommonNormalizedOutput CV u R ω)
    {x : V} (hx : x ∈ CV.carrier) : R x = u (R x) • ω := by
  by_cases hRx : R x = 0
  · rw [hRx]
    simp
  · have hu : u (R x) ≠ 0 := ne_of_gt (u.pos (hRpos hx) hRx)
    have h := hcommon hx hRx
    calc
      R x = u (R x) • ((u (R x))⁻¹ • R x) := by
        rw [smul_smul, mul_inv_cancel₀ hu, one_smul]
      _ = u (R x) • ω := by rw [h]

/-- A common normalized output on the positive cone extends, by generation,
to the atomic formula on the whole ordered space. -/
theorem commonNormalizedOutput_atomic {V W : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (CV : GeneratingCone V) (CW : GeneratingCone W)
    (u : StrictConeFunctional CW) (R : V →ₗ[ℝ] W)
    (hRpos : ConePositive CV CW R) (hR0 : R ≠ 0)
    (ω : W) (hωC : ω ∈ CW.carrier) (hω : u ω = 1)
    (hcommon : HasCommonNormalizedOutput CV u R ω) :
    HasPositiveAtomicFactorization CV CW u R := by
  let ℓ : V →ₗ[ℝ] ℝ := u.toLinearMap.comp R
  have hformula : ∀ x, R x = ℓ x • ω := by
    intro x
    obtain ⟨p, hp, q, hq, rfl⟩ := CV.generating x
    rw [map_sub, map_sub]
    rw [normalized_output_on_cone CV u R ω hRpos hω hcommon hp,
      normalized_output_on_cone CV u R ω hRpos hω hcommon hq]
    exact (sub_smul _ _ _).symm
  have hω0 : ω ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hω
    norm_num at hω
  have hℓ0 : ℓ ≠ 0 := by
    intro hz
    apply hR0
    ext x
    rw [hformula x, hz]
    simp
  refine ⟨ℓ, ω, hℓ0, ?_, hωC, hω, hω0, hformula⟩
  intro x hx
  exact u.nonneg (hRpos hx)

/-- An atomic factorization has genuine linear rank one. -/
theorem positiveAtomicFactorization_rank_one {V W : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (CV : GeneratingCone V) (CW : GeneratingCone W)
    (u : StrictConeFunctional CW) (R : V →ₗ[ℝ] W)
    (hatom : HasPositiveAtomicFactorization CV CW u R) :
    Module.finrank ℝ R.range = 1 := by
  obtain ⟨ℓ, ω, hℓ0, _, _, _, hω0, hformula⟩ := hatom
  have hex : ∃ x, ℓ x ≠ 0 := by
    by_contra h
    push Not at h
    apply hℓ0
    ext x
    simpa using h x
  obtain ⟨x0, hx0⟩ := hex
  have hωrange : ω ∈ R.range := by
    refine ⟨(ℓ x0)⁻¹ • x0, ?_⟩
    rw [hformula, map_smul]
    simp [smul_eq_mul, hx0]
  let y : R.range := ⟨ω, hωrange⟩
  have hy : y ≠ 0 := by
    intro h
    apply hω0
    exact Subtype.ext_iff.mp h
  apply finrank_eq_one y hy
  intro z
  obtain ⟨x, hx⟩ := z.property
  refine ⟨ℓ x, ?_⟩
  apply Subtype.ext
  change ℓ x • ω = z.1
  rw [← hx]
  exact (hformula x).symm

/-- Conversely, positivity and rank one construct the normalized positive
output and the positive coefficient functional `u ∘ R`. -/
theorem rankOne_positive_atomic {V W : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (CV : GeneratingCone V) (CW : GeneratingCone W)
    (u : StrictConeFunctional CW) (R : V →ₗ[ℝ] W)
    (hRpos : ConePositive CV CW R) (hR0 : R ≠ 0)
    (hrank : Module.finrank ℝ R.range = 1) :
    HasPositiveAtomicFactorization CV CW u R := by
  have hex : ∃ x, R x ≠ 0 := by
    by_contra h
    push Not at h
    apply hR0
    ext x
    exact h x
  obtain ⟨x, hx⟩ := hex
  obtain ⟨p, hp, q, hq, hpq⟩ := CV.generating x
  have hsub : R p - R q ≠ 0 := by
    rwa [← map_sub, ← hpq]
  have hpos : (R p ≠ 0 ∧ p ∈ CV.carrier) ∨
      (R q ≠ 0 ∧ q ∈ CV.carrier) := by
    by_cases hRp : R p = 0
    · right
      refine ⟨?_, hq⟩
      intro hRq
      exact hsub (by rw [hRp, hRq, sub_zero])
    · exact Or.inl ⟨hRp, hp⟩
  obtain ⟨p0, hp0, hRp0⟩ : ∃ p0, p0 ∈ CV.carrier ∧ R p0 ≠ 0 := by
    rcases hpos with h | h
    · exact ⟨p, h.2, h.1⟩
    · exact ⟨q, h.2, h.1⟩
  let a : ℝ := u (R p0)
  have ha : 0 < a := u.pos (hRpos hp0) hRp0
  let ω : W := a⁻¹ • R p0
  let ℓ : V →ₗ[ℝ] ℝ := u.toLinearMap.comp R
  have hωC : ω ∈ CW.carrier :=
    CW.smul_mem (inv_nonneg.mpr ha.le) (hRpos hp0)
  have hωnorm : u ω = 1 := by
    change u.toLinearMap (a⁻¹ • R p0) = 1
    rw [map_smul]
    change a⁻¹ * a = 1
    exact inv_mul_cancel₀ (ne_of_gt ha)
  have hω0 : ω ≠ 0 := by
    exact smul_ne_zero (inv_ne_zero (ne_of_gt ha)) hRp0
  have hformula : ∀ x, R x = ℓ x • ω := by
    intro z
    let yR : R.range := ⟨R p0, ⟨p0, rfl⟩⟩
    let zR : R.range := ⟨R z, ⟨z, rfl⟩⟩
    have hyR : yR ≠ 0 := by
      intro h
      apply hRp0
      exact Subtype.ext_iff.mp h
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hrank hyR zR
    have hcW : c • R p0 = R z := congrArg Subtype.val hc
    have hca : c * a = ℓ z := by
      have h := congrArg u.toLinearMap hcW
      simpa [a, ℓ, map_smul, smul_eq_mul] using h
    symm
    change ℓ z • (a⁻¹ • R p0) = R z
    rw [smul_smul, ← hcW]
    congr 1
    field_simp [ne_of_gt ha] at hca ⊢
    linarith
  have hℓ0 : ℓ ≠ 0 := by
    intro h
    have := congrArg (fun f : V →ₗ[ℝ] ℝ => f p0) h
    change a = 0 at this
    exact (ne_of_gt ha) this
  refine ⟨ℓ, ω, hℓ0, ?_, hωC, hωnorm, hω0, hformula⟩
  intro z hz
  exact u.nonneg (hRpos hz)

/-- Full ordered-space equivalence of normalized decoupling, positive atomic
factorization, and rank one. -/
theorem atomicReset_orderedCone_characterization {V W : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (CV : GeneratingCone V) (CW : GeneratingCone W)
    (u : StrictConeFunctional CW) (R : V →ₗ[ℝ] W)
    (hRpos : ConePositive CV CW R) (hR0 : R ≠ 0) :
    (∃ ω, ω ∈ CW.carrier ∧ u ω = 1 ∧
        HasCommonNormalizedOutput CV u R ω)
      ↔ HasPositiveAtomicFactorization CV CW u R
        ∧ Module.finrank ℝ R.range = 1 := by
  constructor
  · rintro ⟨ω, hωC, hω, hcommon⟩
    have ha := commonNormalizedOutput_atomic CV CW u R hRpos hR0
      ω hωC hω hcommon
    exact ⟨ha, positiveAtomicFactorization_rank_one CV CW u R ha⟩
  · rintro ⟨hatom, _⟩
    obtain ⟨ℓ, ω, hℓ0, hℓpos, hωC, hω, hω0, hformula⟩ := hatom
    refine ⟨ω, hωC, hω, ?_⟩
    intro x hx hRx
    have hℓx : ℓ x ≠ 0 := by
      intro h
      apply hRx
      rw [hformula, h]
      simp
    have huRx : u (R x) = ℓ x := by
      rw [hformula, map_smul, hω]
      simp [smul_eq_mul]
    rw [huRx, hformula, smul_smul, inv_mul_cancel₀ hℓx, one_smul]

/-! ## Completely positive matrix-algebra specialization -/

/-- The matrix-algebra atomic branch with effect `E` and output state `ω`. -/
noncomputable def matrixAtomicReset {n w : Type*} [Fintype n]
    (E : Matrix n n ℂ) (ω : Matrix w w ℂ) :
    Matrix n n ℂ →ₗ[ℂ] Matrix w w ℂ :=
  { toFun := fun X => (E * X).trace • ω
    map_add' := by
      intro X Y
      simp [Matrix.mul_add, add_smul]
    map_smul' := by
      intro c X
      simp [Matrix.mul_smul, smul_smul] }

theorem matrixAtomicReset_apply {n w : Type*} [Fintype n]
    (E : Matrix n n ℂ) (ω : Matrix w w ℂ) (X : Matrix n n ℂ) :
    matrixAtomicReset E ω X = (E * X).trace • ω := rfl

/-- For positive `E` and `ω`, the Choi operator is the positive Kronecker
product `Eᵀ ⊗ ω`.  Trace normalization makes the input effect unique. -/
theorem cpMatrixAtomicReset_choi_and_unique {n w : Type*}
    [Fintype n] [DecidableEq n] [Fintype w]
    (E : Matrix n n ℂ) (ω : Matrix w w ℂ)
    (hE : E.PosSemidef) (hω : ω.PosSemidef) (htr : ω.trace = 1) :
    (Eᵀ ⊗ₖ ω).PosSemidef
      ∧ (∀ X, matrixAtomicReset E ω X = (E * X).trace • ω)
      ∧ (∀ F : Matrix n n ℂ,
          (∀ X, matrixAtomicReset F ω X = matrixAtomicReset E ω X) → F = E) := by
  have hEt : Eᵀ.PosSemidef := Matrix.posSemidef_transpose_iff.mpr hE
  refine ⟨hEt.kronecker hω, fun X => rfl, ?_⟩
  intro F hFE
  let ℓE : Matrix n n ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun X => (E * X).trace
      map_add' := by intros; simp [Matrix.mul_add]
      map_smul' := by intros; simp [Matrix.mul_smul] }
  obtain ⟨E0, hE0, huniq⟩ :=
    (atomic_reset_characterization (n := n) (w := w)).2.2 ℓE
  have hE0E : E0 = E := (huniq E (fun X => rfl)).symm
  have hF : ∀ X, ℓE X = (F * X).trace := by
    intro X
    have h := congrArg Matrix.trace (hFE X)
    change (E * X).trace = (F * X).trace
    simpa [matrixAtomicReset_apply, Matrix.trace_smul, htr,
      smul_eq_mul] using h.symm
  exact (huniq F hF).trans hE0E

end NCG
