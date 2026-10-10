/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeClosureClosed
import RenewalGeometry.Continuum.ActualJetKatoRealization

/-!
# Symmetric principal matrices for the slab data of a native model

Einstein–Standard-Model action-closure manuscript, `prop:coupled-bootstrap` ("positive symmetric
actual-jet system", "fixed positive component norm") as used in `thm:native-closure`.

The symmetric-hyperbolic coordinate condition of `prop:coupled-bootstrap` (the principal matrices
`𝒜^j(g)` are symmetric in the state coordinates) is discharged for the slab data
`SlabData.toSMData M δ` of every slab model `M`:

* **`exists_clifford_invariant_form`** (generic): for every Clifford frame `(c_a)` acting on a
  finite-dimensional real vector space there is a positive-definite symmetric bilinear form for
  which every generator `c_a` is orthogonal (iterated averaging `b ↦ b + b(c_a·, c_a·)`; the
  sign `c_ac_b = -c_bc_a` cancels in a bilinear form).
* **`exists_lorentz_unitary_form`** (generic): for a Lorentzian Clifford frame
  (`c₀² = 1`, `c_i² = -1`) such a form makes `c₀` self-adjoint and the `c_i` skew-adjoint — the
  Clifford unitarity relations of `ActualJetKato.UnitaryForms`.
* `exists_pos_form` (generic): positive-definite symmetric forms exist on finite-dimensional real
  spaces.
* **`unitaryForms_slab`** — the slab data carry unitary block forms (Frobenius form on `gl(m)`, a
  positive form on the Higgs space, Clifford-invariant forms on the spinor and co-spinor spaces).
* **`slabX`** — the fixed orthonormal state coordinates of the slab model, **`slabX_orth`**
  (orthonormal for the positive block inner product `ipState`), and **`slabX_symm`** — the
  principal matrices `Aco (toSMData M δ) (slabX M)` are symmetric for every margin `δ`.
-/

open Finset

noncomputable section

namespace RenewalGeometry.SlabSymmetric

open TwistedHalfRicci ActualJetWriter ActualJetSystem ActualJetSmooth CoupledBootstrap SlabData
  NativeDensity NativeModel

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

/-! ### Generic: positive forms and Clifford-invariant forms -/

section Generic

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [FiniteDimensional ℝ X]

/-- **Positive-definite symmetric forms exist** on a finite-dimensional real vector space
(`Σ_i x_i y_i` in a basis). -/
theorem exists_pos_form : ∃ b : X →ₗ[ℝ] X →ₗ[ℝ] ℝ,
    (∀ x y, b x y = b y x) ∧ ∀ x, x ≠ 0 → 0 < b x x := by
  classical
  set bs := Module.finBasis ℝ X
  refine ⟨∑ i, (LinearMap.mul ℝ ℝ).compl₁₂ (bs.coord i) (bs.coord i), fun x y => ?_,
    fun x hx => ?_⟩
  · simp only [LinearMap.sum_apply, LinearMap.compl₁₂_apply,
      LinearMap.mul_apply', mul_comm]
  · simp only [LinearMap.sum_apply, LinearMap.compl₁₂_apply,
      LinearMap.mul_apply']
    have hex : ∃ i, bs.coord i x ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx ((bs.forall_coord_eq_zero_iff).1 h)
    obtain ⟨i, hi⟩ := hex
    exact lt_of_lt_of_le (mul_self_pos.2 hi)
      (Finset.single_le_sum (f := fun j => bs.coord j x * bs.coord j x)
        (fun j _ => mul_self_nonneg _) (Finset.mem_univ i))

variable {ι : Type*} [DecidableEq ι]

/-- `c_a² = -ε_a` for the generators of a Clifford frame. -/
theorem clifford_sq (Fr : CliffordFrame ι (Module.End ℝ X)) (a : ι) :
    Fr.c a * Fr.c a = (-Fr.ε a) • (1 : Module.End ℝ X) := by
  have h := Fr.anticomm a a
  simp only [if_true] at h
  have h2 : (2 : ℝ) • (Fr.c a * Fr.c a) = (2 : ℝ) • ((-Fr.ε a) • (1 : Module.End ℝ X)) := by
    rw [two_smul, h, smul_smul]; ring_nf
  exact smul_right_injective _ (two_ne_zero) h2

/-- Distinct generators anticommute. -/
theorem clifford_anti (Fr : CliffordFrame ι (Module.End ℝ X)) {a b : ι} (hab : a ≠ b) :
    Fr.c a * Fr.c b = -(Fr.c b * Fr.c a) := by
  have h := Fr.anticomm a b
  simp only [hab, if_false, mul_zero, zero_smul] at h
  exact eq_neg_of_add_eq_zero_left h

/-- The averaged form `b(x, y) + b(cx, cy)`. -/
def avgForm (b : X →ₗ[ℝ] X →ₗ[ℝ] ℝ) (c : Module.End ℝ X) : X →ₗ[ℝ] X →ₗ[ℝ] ℝ :=
  b + b.compl₁₂ c c

theorem avgForm_apply (b : X →ₗ[ℝ] X →ₗ[ℝ] ℝ) (c : Module.End ℝ X) (x y : X) :
    avgForm b c x y = b x y + b (c x) (c y) := rfl

/-- **Clifford-invariant forms**: for every Clifford frame acting on a finite-dimensional real
space there is a positive-definite symmetric form for which every generator is orthogonal. -/
theorem exists_clifford_invariant_form [Fintype ι] (Fr : CliffordFrame ι (Module.End ℝ X)) :
    ∃ b : X →ₗ[ℝ] X →ₗ[ℝ] ℝ, (∀ x y, b x y = b y x) ∧ (∀ x, x ≠ 0 → 0 < b x x) ∧
      ∀ a x y, b (Fr.c a x) (Fr.c a y) = b x y := by
  classical
  suffices H : ∀ s : Finset ι, ∃ b : X →ₗ[ℝ] X →ₗ[ℝ] ℝ, (∀ x y, b x y = b y x) ∧
      (∀ x, x ≠ 0 → 0 < b x x) ∧ ∀ a ∈ s, ∀ x y, b (Fr.c a x) (Fr.c a y) = b x y by
    obtain ⟨b, h1, h2, h3⟩ := H Finset.univ
    exact ⟨b, h1, h2, fun a => h3 a (Finset.mem_univ a)⟩
  intro s
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨b, h1, h2⟩ := exists_pos_form (X := X)
    exact ⟨b, h1, h2, fun a ha => absurd ha (Finset.notMem_empty a)⟩
  | insert a s has ih =>
    obtain ⟨b, h1, h2, h3⟩ := ih
    have hnn : ∀ x, 0 ≤ b x x := fun x => by
      by_cases hx : x = 0
      · simp [hx]
      · exact (h2 x hx).le
    have hsq : ∀ x, Fr.c a (Fr.c a x) = (-Fr.ε a) • x := fun x => by
      have := congrArg (fun T : Module.End ℝ X => T x) (clifford_sq Fr a)
      simpa using this
    refine ⟨avgForm b (Fr.c a), fun x y => ?_, fun x hx => ?_, fun a' ha' x y => ?_⟩
    · rw [avgForm_apply, avgForm_apply, h1, h1 (Fr.c a x)]
    · rw [avgForm_apply]
      exact add_pos_of_pos_of_nonneg (h2 x hx) (hnn _)
    · rw [avgForm_apply, avgForm_apply]
      rcases Finset.mem_insert.1 ha' with rfl | ha's
      · rw [hsq, hsq]
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
        linear_combination (b x y) * Fr.sign_sq a'
      · have hne : a ≠ a' := fun h => has (h ▸ ha's)
        have hanti : ∀ z, Fr.c a (Fr.c a' z) = -(Fr.c a' (Fr.c a z)) := fun z => by
          have := congrArg (fun T : Module.End ℝ X => T z) (clifford_anti Fr hne)
          simpa using this
        rw [h3 a' ha's, hanti, hanti]
        simp only [map_neg, LinearMap.neg_apply, neg_neg, h3 a' ha's]

/-- **Clifford unitarity for a Lorentzian frame** (`c₀² = 1`, `c_i² = -1`): a positive-definite
symmetric form for which `c₀` is self-adjoint and the spatial generators are skew-adjoint. -/
theorem exists_lorentz_unitary_form (Fr : CliffordFrame (Fin 4) (Module.End ℝ X))
    (hL : IsLorentzian Fr) :
    ∃ b : X →ₗ[ℝ] X →ₗ[ℝ] ℝ, (∀ x y, b x y = b y x) ∧ (∀ x, x ≠ 0 → 0 < b x x) ∧
      (∀ x y, b (Fr.c 0 • x) y = b x (Fr.c 0 • y)) ∧
      ∀ (i : Fin 3) x y, b (Fr.c i.succ • x) y = -b x (Fr.c i.succ • y) := by
  obtain ⟨b, h1, h2, h3⟩ := exists_clifford_invariant_form Fr
  have hsq : ∀ a x, Fr.c a (Fr.c a x) = (-Fr.ε a) • x := fun a x => by
    have := congrArg (fun T : Module.End ℝ X => T x) (clifford_sq Fr a)
    simpa using this
  have key : ∀ a x y, b (Fr.c a x) y = -Fr.ε a * b x (Fr.c a y) := fun a x y => by
    have := h3 a (Fr.c a x) y
    rw [hsq, map_smul, LinearMap.smul_apply, smul_eq_mul] at this
    exact this.symm
  refine ⟨b, h1, h2, fun x y => ?_, fun i x y => ?_⟩
  · change b (Fr.c 0 x) y = b x (Fr.c 0 y)
    rw [key, hL.1]; ring
  · change b (Fr.c i.succ x) y = -b x (Fr.c i.succ y)
    rw [key, hL.2 i]; ring

end Generic

/-! ### The unitary block forms of the slab data -/

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]
variable {m : ℕ} (M : SlabModel 𝔄 𝓗 𝓢 m)

/-- **The slab data carry unitary block forms**: the Frobenius form on `gl(m)`, a positive form on
the Higgs space and Clifford-unitary forms on the spinor and co-spinor spaces, for every margin
`δ` (the Clifford frames of `toSMData M δ` do not depend on `δ`). -/
theorem exists_unitaryForms_slab : ∃ (bV : HSp M →ₗ[ℝ] HSp M →ₗ[ℝ] ℝ)
    (bS : 𝓢 →ₗ[ℝ] 𝓢 →ₗ[ℝ] ℝ) (bS' : CoSpinor 𝓢 →ₗ[ℝ] CoSpinor 𝓢 →ₗ[ℝ] ℝ),
    ∀ δ, ActualJetKato.UnitaryForms (toSMData M δ) (ActualJetKato.frob m) bV bS bS' := by
  obtain ⟨bV, hV1, hV2⟩ := exists_pos_form (X := HSp M)
  obtain ⟨bS, hS1, hS2, hS3, hS4⟩ := exists_lorentz_unitary_form (diracD M).Fr (diracD M).lorentz
  obtain ⟨bS', hS1', hS2', hS3', hS4'⟩ :=
    exists_lorentz_unitary_form (diracDb M).Fr (diracDb M).lorentz
  exact ⟨bV, bS, bS', fun δ =>
    { symG := fun x y => by simp only [ActualJetKato.frob_apply, mul_comm]
      symV := hV1
      symS := hS1
      symS' := hS1'
      posG := ActualJetKato.frob_pos
      posV := hV2
      posS := hS2
      posS' := hS2'
      c0 := hS3
      ci := hS4
      c0b := hS3'
      cib := hS4' }⟩

/-- The state space of the slab data. -/
abbrev SState := StateP m (HSp M) 𝓢 (CoSpinor 𝓢)

/-- **Orthonormal state coordinates exist**: coordinates `eX : ℝ^n ≃ StateP` orthonormal for the
positive block inner product `ipState` of unitary block forms of the slab data. -/
theorem exists_slab_coords : ∃ eX : (Fin (ActualJetKato.dimS m (HSp M) 𝓢 (CoSpinor 𝓢)) → ℝ) ≃L[ℝ]
      SState M, ∃ (bV : HSp M →ₗ[ℝ] HSp M →ₗ[ℝ] ℝ) (bS : 𝓢 →ₗ[ℝ] 𝓢 →ₗ[ℝ] ℝ)
      (bS' : CoSpinor 𝓢 →ₗ[ℝ] CoSpinor 𝓢 →ₗ[ℝ] ℝ),
      (∀ δ, ActualJetKato.UnitaryForms (toSMData M δ) (ActualJetKato.frob m) bV bS bS') ∧
      ∀ v w, ipState (ActualJetKato.frob m) bV bS bS' (ofP (eX v)) (ofP (eX w)) =
        ∑ i, v i * w i := by
  obtain ⟨bV, bS, bS', hU⟩ := exists_unitaryForms_slab M
  obtain ⟨κ, hκ⟩ := ActualJetKato.exists_state_coords (hU 1)
  exact ⟨κ.symm.toContinuousLinearEquiv, bV, bS, bS', hU, hκ⟩

/-- **The fixed orthonormal state coordinates of a slab model** (the paper's "fixed positive
component norm" of the actual-jet state). -/
def slabX : (Fin (ActualJetKato.dimS m (HSp M) 𝓢 (CoSpinor 𝓢)) → ℝ) ≃L[ℝ] SState M :=
  Classical.choose (exists_slab_coords M)

/-- `slabX` is orthonormal for the positive block inner product of unitary block forms. -/
theorem slabX_orth : ∃ (bV : HSp M →ₗ[ℝ] HSp M →ₗ[ℝ] ℝ) (bS : 𝓢 →ₗ[ℝ] 𝓢 →ₗ[ℝ] ℝ)
      (bS' : CoSpinor 𝓢 →ₗ[ℝ] CoSpinor 𝓢 →ₗ[ℝ] ℝ),
      (∀ δ, ActualJetKato.UnitaryForms (toSMData M δ) (ActualJetKato.frob m) bV bS bS') ∧
      ∀ v w, ipState (ActualJetKato.frob m) bV bS bS' (ofP (slabX M v)) (ofP (slabX M w)) =
        ∑ i, v i * w i :=
  Classical.choose_spec (exists_slab_coords M)

/-- **The principal matrices of the slab data are symmetric in the coordinates `slabX`**
(`hAsym` of `prop:coupled-bootstrap` / `thm:native-closure`), for every margin `δ`. -/
theorem slabX_symm (δ : ℝ) (j : Fin 3) (a b : Fin (ActualJetKato.dimS m (HSp M) 𝓢 (CoSpinor 𝓢)))
    (v : Fin (ActualJetKato.dimS m (HSp M) 𝓢 (CoSpinor 𝓢)) → ℝ) :
    Aco (toSMData M δ) (slabX M) j a b v = Aco (toSMData M δ) (slabX M) j b a v := by
  obtain ⟨bV, bS, bS', hU, hX⟩ := slabX_orth M
  exact Aco_symm (toSMData M δ) (slabX M) (ActualJetKato.frob m) bV bS bS' (hU δ).c0 (hU δ).ci
    (hU δ).c0b (hU δ).cib hX j a b v

/-- **Orthonormal coordinates for any unitary block forms give symmetric principal matrices**
(the coordinate-free form of `slabX_symm`). -/
theorem symm_of_orth {n : ℕ} (eX : (Fin n → ℝ) ≃L[ℝ] SState M) {δ : ℝ}
    {bV : HSp M →ₗ[ℝ] HSp M →ₗ[ℝ] ℝ} {bS : 𝓢 →ₗ[ℝ] 𝓢 →ₗ[ℝ] ℝ}
    {bS' : CoSpinor 𝓢 →ₗ[ℝ] CoSpinor 𝓢 →ₗ[ℝ] ℝ} {bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ}
    (hU : ActualJetKato.UnitaryForms (toSMData M δ) bG bV bS bS')
    (hX : ∀ v w, ipState bG bV bS bS' (ofP (eX v)) (ofP (eX w)) = ∑ i, v i * w i) :
    ∀ j a b v, Aco (toSMData M δ) eX j a b v = Aco (toSMData M δ) eX j b a v :=
  fun j a b v => Aco_symm (toSMData M δ) eX bG bV bS bS' hU.c0 hU.ci hU.c0b hU.cib hX j a b v

end RenewalGeometry.SlabSymmetric

end
