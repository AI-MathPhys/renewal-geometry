/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Algebra.MatrixKrausExistence
/-!
# Compression defects and simultaneous unitary completion of CP maps

Paper label: `prop:ncg-compression-defect` (predictive spectral geometry).

## Compression by an isometry (API on `Matrix h k ℂ`)

For an isometry `V : ℂᵏ → ℂʰ` (`Vᴴ V = 1`), `P = V Vᴴ` (`CompressionDefect.rangeProj`),
`Q = 1 − P` (`CompressionDefect.defectProj`) and `κ(b) = Vᴴ b V`
(`CompressionDefect.compress`):

* `compress_mul_sub_mul`: `κ(ab) − κ(a)κ(b) = Vᴴ a Q b V`;
* `compress_star_mul_sub_mul`: `κ(aᴴa) − κ(a)ᴴκ(a) = (QaV)ᴴ(QaV)`, and
  `compress_star_mul_sub_mul_posSemidef`: it is `⪰ 0`;
* `compress_conjTranspose`, `compress_one`, `compress_add`, `compress_smul`: `κ` is a unital
  `*`-preserving linear map;
* `compress_multiplicative_iff_commute`: on a unital `*`-subalgebra `𝒞`, `κ` is multiplicative
  iff `P` commutes with (i.e. reduces) every element of `𝒞`;
* `exists_starAlgHom_iff_commute`: `κ|𝒞` is a unital `*`-homomorphism iff `P` reduces `𝒞`.

## Simultaneous unitary completion

* `exists_unitary_extension_of_isometry`: an isometry `V : ℂ^X → ℂ^{Y ⊕ X}` is the `X`-column
  block of a unitary on `ℂ^{Y ⊕ X}` (orthonormal basis extension);
* `IsTraceNonincreasing`, `kraus_sum_le_one`: a CP trace-nonincreasing map has Kraus operators
  with `∑ Wᴴ W ⪯ 1`;
* `exists_unitary_completion`: one CP trace-nonincreasing map `T : M_n → M_m` is
  `T(X) = ∑_k O_k U J X Jᴴ Uᴴ O_kᴴ` with `U` unitary, `J` the isometric embedding of the input
  next to a finite ancilla, and `O_k` the coisometric read-outs of the output register
  tensored with the `k`-th ancilla basis state;
* `exists_simultaneous_unitary_completion`: **the first claim of the proposition** — a finite
  family `(T_i)` of CP trace-nonincreasing maps (arbitrary finite dimensions) is completed by a
  single unitary (the controlled direct sum `⊕_i U_i`, control register `i`) with isometric,
  mutually orthogonal input embeddings `J_i` and coisometric output read-outs `O_{i,k}`.
-/

namespace RenewalGeometry
namespace CompressionDefect

open Matrix
open scoped ComplexOrder

section Compression

variable {h k : Type*} [Fintype h] [Fintype k] [DecidableEq h] [DecidableEq k]

/-- The compression `κ(b) = Vᴴ b V`. -/
def compress (V : Matrix h k ℂ) (b : Matrix h h ℂ) : Matrix k k ℂ := Vᴴ * b * V

/-- The range projection `P = V Vᴴ`. -/
def rangeProj (V : Matrix h k ℂ) : Matrix h h ℂ := V * Vᴴ

/-- The defect projection `Q = 1 − V Vᴴ`. -/
def defectProj (V : Matrix h k ℂ) : Matrix h h ℂ := 1 - V * Vᴴ

theorem compress_apply (V : Matrix h k ℂ) (b : Matrix h h ℂ) : compress V b = Vᴴ * b * V := rfl

theorem rangeProj_conjTranspose (V : Matrix h k ℂ) : (rangeProj V)ᴴ = rangeProj V := by
  simp [rangeProj, conjTranspose_mul]

theorem rangeProj_mul_self {V : Matrix h k ℂ} (hV : Vᴴ * V = 1) :
    rangeProj V * rangeProj V = rangeProj V := by
  rw [rangeProj, Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ, hV, Matrix.one_mul]

theorem defectProj_conjTranspose (V : Matrix h k ℂ) : (defectProj V)ᴴ = defectProj V := by
  simp [defectProj, conjTranspose_mul]

theorem defectProj_mul_self {V : Matrix h k ℂ} (hV : Vᴴ * V = 1) :
    defectProj V * defectProj V = defectProj V := by
  have hP := rangeProj_mul_self hV
  simp only [rangeProj] at hP
  rw [defectProj, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, hP, sub_self, sub_zero]

theorem defectProj_mul_isometry {V : Matrix h k ℂ} (hV : Vᴴ * V = 1) :
    defectProj V * V = 0 := by
  rw [defectProj, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hV, Matrix.mul_one,
    sub_self]

theorem compress_one {V : Matrix h k ℂ} (hV : Vᴴ * V = 1) : compress V 1 = 1 := by
  rw [compress, Matrix.mul_one, hV]

theorem compress_conjTranspose (V : Matrix h k ℂ) (a : Matrix h h ℂ) :
    compress V aᴴ = (compress V a)ᴴ := by
  simp [compress, conjTranspose_mul, Matrix.mul_assoc]

theorem compress_add (V : Matrix h k ℂ) (a b : Matrix h h ℂ) :
    compress V (a + b) = compress V a + compress V b := by
  simp [compress, Matrix.mul_add, Matrix.add_mul]

theorem compress_smul (V : Matrix h k ℂ) (c : ℂ) (a : Matrix h h ℂ) :
    compress V (c • a) = c • compress V a := by
  simp [compress, Matrix.mul_smul, Matrix.smul_mul]

/-- **Compression defect** (`eq:ncg-compression-square-defect`, first identity):
`κ(ab) − κ(a)κ(b) = Vᴴ a Q b V`. -/
theorem compress_mul_sub_mul (V : Matrix h k ℂ) (a b : Matrix h h ℂ) :
    compress V (a * b) - compress V a * compress V b = Vᴴ * a * defectProj V * b * V := by
  simp only [compress, defectProj, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.mul_assoc]

/-- **Square defect** (`eq:ncg-compression-square-defect`, second identity):
`κ(aᴴa) − κ(a)ᴴκ(a) = (QaV)ᴴ(QaV)`. -/
theorem compress_star_mul_sub_mul {V : Matrix h k ℂ} (hV : Vᴴ * V = 1) (a : Matrix h h ℂ) :
    compress V (aᴴ * a) - (compress V a)ᴴ * compress V a
      = (defectProj V * a * V)ᴴ * (defectProj V * a * V) := by
  rw [← compress_conjTranspose, compress_mul_sub_mul]
  have hQ : (defectProj V)ᴴ * defectProj V = defectProj V := by
    rw [defectProj_conjTranspose, defectProj_mul_self hV]
  calc Vᴴ * aᴴ * defectProj V * a * V
      = Vᴴ * aᴴ * ((defectProj V)ᴴ * defectProj V) * a * V := by rw [hQ]
    _ = (defectProj V * a * V)ᴴ * (defectProj V * a * V) := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]

/-- The square defect is positive semidefinite (Kadison–Schwarz for compressions). -/
theorem compress_star_mul_sub_mul_posSemidef {V : Matrix h k ℂ} (hV : Vᴴ * V = 1)
    (a : Matrix h h ℂ) :
    (compress V (aᴴ * a) - (compress V a)ᴴ * compress V a).PosSemidef := by
  rw [compress_star_mul_sub_mul hV]
  exact posSemidef_conjTranspose_mul_self _

/-- The square defect vanishes iff the corner `Q a V` vanishes. -/
theorem compress_star_mul_eq_iff {V : Matrix h k ℂ} (hV : Vᴴ * V = 1) (a : Matrix h h ℂ) :
    compress V (aᴴ * a) = (compress V a)ᴴ * compress V a ↔ defectProj V * a * V = 0 := by
  rw [← sub_eq_zero, compress_star_mul_sub_mul hV, conjTranspose_mul_self_eq_zero]

/-- `Q a V = 0` iff `Q a P = 0`. -/
theorem defect_corner_eq_zero_iff {V : Matrix h k ℂ} (hV : Vᴴ * V = 1) (a : Matrix h h ℂ) :
    defectProj V * a * V = 0 ↔ defectProj V * a * rangeProj V = 0 := by
  constructor
  · intro h0
    rw [rangeProj, ← Matrix.mul_assoc, h0, Matrix.zero_mul]
  · intro h0
    have := congrArg (· * V) h0
    simp only [rangeProj, Matrix.mul_assoc, hV, Matrix.mul_one, Matrix.zero_mul] at this
    simpa [Matrix.mul_assoc] using this

/-- For a `*`-closed set, the vanishing of all corners `Q c P` is equivalent to `P`
commuting with every element (`P` reduces the set). -/
theorem corners_eq_zero_iff_commute {V : Matrix h k ℂ} (hV : Vᴴ * V = 1)
    (𝒞 : StarSubalgebra ℂ (Matrix h h ℂ)) :
    (∀ c ∈ 𝒞, defectProj V * c * rangeProj V = 0) ↔ ∀ c ∈ 𝒞, Commute (rangeProj V) c := by
  have hd : defectProj V = 1 - rangeProj V := rfl
  have hPh := rangeProj_conjTranspose V
  have hPP := rangeProj_mul_self hV
  constructor
  · intro h0 c hc
    have e1 := h0 c hc
    rw [hd, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at e1
    have e2 := h0 (star c) (star_mem hc)
    rw [hd, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero,
      star_eq_conjTranspose] at e2
    have e3 := congrArg conjTranspose e2
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hPh] at e3
    -- e1 : c P = P c P,  e3 : P c = P (c P)
    change rangeProj V * c = c * rangeProj V
    rw [e3, e1, Matrix.mul_assoc, ← Matrix.mul_assoc, hPP]
  · intro hc c hcC
    rw [hd, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul, (hc c hcC).eq, Matrix.mul_assoc,
      hPP, sub_self]

/-- **Multiplicativity criterion** (`prop:ncg-compression-defect`): the compression is
multiplicative on a unital `*`-subalgebra `𝒞` iff `P = V Vᴴ` reduces `𝒞`. -/
theorem compress_multiplicative_iff_commute {V : Matrix h k ℂ} (hV : Vᴴ * V = 1)
    (𝒞 : StarSubalgebra ℂ (Matrix h h ℂ)) :
    (∀ a ∈ 𝒞, ∀ b ∈ 𝒞, compress V (a * b) = compress V a * compress V b) ↔
      ∀ c ∈ 𝒞, Commute (rangeProj V) c := by
  rw [← corners_eq_zero_iff_commute hV]
  constructor
  · intro hmul c hc
    rw [← defect_corner_eq_zero_iff hV, ← compress_star_mul_eq_iff hV, ← compress_conjTranspose]
    have := hmul (star c) (star_mem hc) c hc
    rwa [star_eq_conjTranspose] at this
  · intro h0 a _ b hb
    rw [← sub_eq_zero, compress_mul_sub_mul]
    have hb' := (defect_corner_eq_zero_iff hV b).2 (h0 b hb)
    have : Vᴴ * a * defectProj V * b * V = Vᴴ * a * (defectProj V * b * V) := by
      simp only [Matrix.mul_assoc]
    rw [this, hb', Matrix.mul_zero]

/-- **Proposition `prop:ncg-compression-defect`, `*`-homomorphism criterion**: the
compression `κ(b) = Vᴴ b V` restricts to a unital `*`-homomorphism on the unital
`*`-subalgebra `𝒞` iff `P = V Vᴴ` reduces `𝒞`. -/
theorem exists_starAlgHom_iff_commute {V : Matrix h k ℂ} (hV : Vᴴ * V = 1)
    (𝒞 : StarSubalgebra ℂ (Matrix h h ℂ)) :
    (∃ φ : 𝒞 →⋆ₐ[ℂ] Matrix k k ℂ, ∀ c : 𝒞, φ c = compress V c) ↔
      ∀ c ∈ 𝒞, Commute (rangeProj V) c := by
  rw [← compress_multiplicative_iff_commute hV]
  constructor
  · rintro ⟨φ, hφ⟩ a ha b hb
    have := map_mul φ ⟨a, ha⟩ ⟨b, hb⟩
    rw [hφ, hφ, hφ] at this
    exact this
  · intro hmul
    refine ⟨{ toFun := fun c => compress V c
              map_one' := compress_one hV
              map_mul' := fun a b => hmul a a.2 b b.2
              map_zero' := by simp [compress]
              map_add' := fun a b => compress_add V a b
              commutes' := fun r => by
                change compress V (algebraMap ℂ (Matrix h h ℂ) r) = algebraMap ℂ _ r
                rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
                  compress_smul, compress_one hV]
              map_star' := fun a => by
                change compress V (star (a : Matrix h h ℂ)) = star (compress V a)
                rw [star_eq_conjTranspose, star_eq_conjTranspose, compress_conjTranspose] },
      fun c => rfl⟩

end Compression

section Extension

variable {Y X : Type*} [Fintype Y] [Fintype X] [DecidableEq Y] [DecidableEq X]

/-- **Isometry-to-unitary extension**: an isometry `V : ℂ^X → ℂ^{Y ⊕ X}` is the `X`-column
block of a unitary matrix on `ℂ^{Y ⊕ X}`. -/
theorem exists_unitary_extension_of_isometry (V : Matrix (Y ⊕ X) X ℂ) (hV : Vᴴ * V = 1) :
    ∃ U : Matrix (Y ⊕ X) (Y ⊕ X) ℂ, U ∈ unitary (Matrix (Y ⊕ X) (Y ⊕ X) ℂ) ∧
      ∀ z x, U z (Sum.inr x) = V z x := by
  classical
  let v : Y ⊕ X → EuclideanSpace ℂ (Y ⊕ X) := fun w =>
    Sum.elim (fun _ => 0) (fun x => WithLp.toLp 2 fun z => V z x) w
  have hinner : ∀ x x' : X, inner ℂ (v (Sum.inr x)) (v (Sum.inr x')) = (1 : Matrix X X ℂ) x x' := by
    intro x x'
    rw [← hV, EuclideanSpace.inner_eq_star_dotProduct, Matrix.mul_apply]
    simp only [v, Sum.elim_inr, dotProduct, conjTranspose_apply, Pi.star_apply]
    refine Finset.sum_congr rfl fun z _ => ?_
    ring
  have hv : Orthonormal ℂ ((Set.range (Sum.inr : X → Y ⊕ X)).domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨_, x, rfl⟩ ⟨_, x', rfl⟩
    change inner ℂ (v (Sum.inr x)) (v (Sum.inr x')) = _
    rw [hinner, one_apply]
    by_cases hxx : x = x'
    · subst hxx; simp
    · rw [if_neg hxx, if_neg]
      intro h
      exact hxx (Sum.inr_injective (congrArg Subtype.val h))
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨Matrix.of fun z w => (b w).ofLp z, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    ext w w'
    have := (orthonormal_iff_ite.1 b.orthonormal) w w'
    rw [EuclideanSpace.inner_eq_star_dotProduct] at this
    rw [star_eq_conjTranspose, Matrix.mul_apply, one_apply, ← this]
    simp only [conjTranspose_apply, Matrix.of_apply, dotProduct, Pi.star_apply]
    refine Finset.sum_congr rfl fun z _ => ?_
    ring
  · intro z x
    simp only [Matrix.of_apply]
    rw [hb (Sum.inr x) (Set.mem_range_self x)]
    rfl

end Extension

section Completion

open RenewalGeometry.MatrixKraus

/-- A linear map of matrix algebras is **trace-nonincreasing** on positive inputs. -/
def IsTraceNonincreasing {n m : ℕ}
    (T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) : Prop :=
  ∀ X : Matrix (Fin n) (Fin n) ℂ, X.PosSemidef → (T X).trace.re ≤ X.trace.re

/-- A Kraus family whose map is trace-nonincreasing satisfies `∑ Wᴴ W ⪯ 1`. -/
theorem one_sub_sum_conjTranspose_mul_posSemidef {p q κ : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [Fintype κ] (W : κ → Matrix q p ℂ)
    (hT : ∀ X : Matrix p p ℂ, X.PosSemidef → (krausMap W X).trace.re ≤ X.trace.re) :
    (1 - ∑ a, (W a)ᴴ * W a).PosSemidef := by
  set S := ∑ a, (W a)ᴴ * W a with hS
  have hSh : Sᴴ = S := by
    simp [hS, conjTranspose_sum, conjTranspose_mul]
  have hH : (1 - S).IsHermitian := by
    simp [IsHermitian, conjTranspose_sub, hSh]
  refine PosSemidef.of_dotProduct_mulVec_nonneg hH fun x => ?_
  have h1 := hT _ (posSemidef_vecMulVec_self_star x)
  rw [trace_krausMap, ← hS, mul_vecMulVec, trace_vecMulVec, trace_vecMulVec] at h1
  have him := hH.im_star_dotProduct_mulVec_self x
  rw [Complex.nonneg_iff]
  refine ⟨?_, ?_⟩
  · rw [sub_mulVec, one_mulVec, dotProduct_sub, Complex.sub_re]
    rw [dotProduct_comm (S *ᵥ x), dotProduct_comm x] at h1
    linarith
  · exact him.symm

/-- The dilation space `(ℂᵐ ⊗ ℂ^κ) ⊕ ℂⁿ` with Kraus ancilla `κ = Fin n × Fin m`. -/
abbrev DilationSpace (n m : ℕ) : Type := (Fin m × (Fin n × Fin m)) ⊕ Fin n

/-- The isometric input embedding `ℂⁿ → (ℂᵐ ⊗ ℂ^κ) ⊕ ℂⁿ` (ancilla adjoined). -/
def inputEmbed (n m : ℕ) : Matrix (DilationSpace n m) (Fin n) ℂ :=
  Matrix.of fun z i => if z = Sum.inr i then 1 else 0

/-- The read-out of the output register with the ancilla in basis state `k`. -/
def readout {n m : ℕ} (k : Fin n × Fin m) : Matrix (Fin m) (DilationSpace n m) ℂ :=
  Matrix.of fun a z => if z = Sum.inl (a, k) then 1 else 0

theorem inputEmbed_isometry (n m : ℕ) : (inputEmbed n m)ᴴ * inputEmbed n m = 1 := by
  ext i j
  simp only [inputEmbed, Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply, one_apply]
  rw [Finset.sum_eq_single (Sum.inr i)]
  · by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  · intro z _ hz; simp [hz]
  · simp

theorem readout_mul_conjTranspose {n m : ℕ} (k k' : Fin n × Fin m) :
    readout k * (readout k')ᴴ = if k = k' then 1 else 0 := by
  ext a b
  simp only [readout, Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single (Sum.inl (a, k))]
  · by_cases hkk : k = k'
    · subst hkk; by_cases hab : a = b
      · subst hab; simp
      · simp [hab, Ne.symm hab]
    · simp [hkk]
  · intro z _ hz; simp [hz]
  · simp

theorem mul_inputEmbed {n m : ℕ} (U : Matrix (DilationSpace n m) (DilationSpace n m) ℂ) :
    U * inputEmbed n m = Matrix.of fun z i => U z (Sum.inr i) := by
  ext z i
  simp only [inputEmbed, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single (Sum.inr i)]
  · simp
  · intro w _ hw; simp [hw]
  · simp

theorem readout_mul {n m : ℕ} {r : Type*} (k : Fin n × Fin m)
    (M : Matrix (DilationSpace n m) r ℂ) :
    readout k * M = Matrix.of fun a i => M (Sum.inl (a, k)) i := by
  ext a i
  simp only [readout, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single (Sum.inl (a, k))]
  · simp
  · intro w _ hw; simp [hw]
  · simp

/-- **Unitary completion of one CP trace-nonincreasing map** (Stinespring contraction,
completed to a unitary): `T(X) = ∑_k O_k U J X Jᴴ Uᴴ O_kᴴ` with `U` unitary on
`(ℂᵐ ⊗ ℂ^κ) ⊕ ℂⁿ`, `J = inputEmbed` and `O_k = readout k`. -/
theorem exists_unitary_completion {n m : ℕ}
    (T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (hCP : IsMatrixCompletelyPositive T) (hTN : IsTraceNonincreasing T) :
    ∃ U : Matrix (DilationSpace n m) (DilationSpace n m) ℂ,
      U ∈ unitary (Matrix (DilationSpace n m) (DilationSpace n m) ℂ) ∧
      ∀ X, T X = ∑ k : Fin n × Fin m, readout k * U * inputEmbed n m * X *
        (inputEmbed n m)ᴴ * Uᴴ * (readout k)ᴴ := by
  classical
  obtain ⟨W, hW⟩ := exists_kraus_of_completelyPositive hCP
  have hTW : T = krausMap W := LinearMap.ext fun X => (hW X).trans (krausMap_apply W X).symm
  have hle : (1 - ∑ a, (W a)ᴴ * W a).PosSemidef :=
    one_sub_sum_conjTranspose_mul_posSemidef W fun X hX => hTW ▸ hTN X hX
  obtain ⟨D, hD⟩ := exists_eq_conjTranspose_mul_self hle
  -- the Stinespring isometry `x ↦ (∑_k W_k x ⊗ e_k) ⊕ D x`
  set V : Matrix (DilationSpace n m) (Fin n) ℂ :=
    Matrix.of fun z i => Sum.elim (fun p => W p.2 p.1 i) (fun j => D j i) z with hVdef
  have hVV : Vᴴ * V = 1 := by
    have h1 : Vᴴ * V = (∑ a, (W a)ᴴ * W a) + Dᴴ * D := by
      ext i j
      simp only [hVdef, Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply,
        Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Matrix.add_apply, Matrix.sum_apply,
        Fintype.sum_prod_type]
      congr 1
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    rw [h1, ← hD, add_sub_cancel]
  obtain ⟨U, hU, hUV⟩ := exists_unitary_extension_of_isometry V hVV
  refine ⟨U, hU, fun X => ?_⟩
  rw [hW X]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hUJ : U * inputEmbed n m = V := by
    rw [mul_inputEmbed]; ext z i; exact hUV z i
  have hOV : readout k * V = W k := by
    rw [readout_mul]; ext a i; simp [hVdef]
  rw [← hOV, ← hUJ]
  simp only [conjTranspose_mul, Matrix.mul_assoc]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The block embedding `ℂ^{Z_i} → ⊕_j ℂ^{Z_j}` of the `i`-th control sector. -/
def sectorEmbed {Z : ι → Type*} [∀ i, Fintype (Z i)] [∀ i, DecidableEq (Z i)] (i : ι) :
    Matrix (Σ j, Z j) (Z i) ℂ :=
  Matrix.of fun d z => if d = ⟨i, z⟩ then 1 else 0

theorem sectorEmbed_isometry {Z : ι → Type*} [∀ i, Fintype (Z i)] [∀ i, DecidableEq (Z i)]
    (i : ι) : (sectorEmbed (Z := Z) i)ᴴ * sectorEmbed (Z := Z) i = 1 := by
  ext z z'
  simp only [sectorEmbed, Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply, one_apply]
  rw [Finset.sum_eq_single ⟨i, z⟩]
  · by_cases hz : z = z'
    · subst hz; simp
    · simp [hz, Ne.symm hz]
  · intro d _ hd; simp [hd]
  · simp

theorem sectorEmbed_orthogonal {Z : ι → Type*} [∀ i, Fintype (Z i)] [∀ i, DecidableEq (Z i)]
    {i i' : ι} (hii : i ≠ i') : (sectorEmbed (Z := Z) i)ᴴ * sectorEmbed (Z := Z) i' = 0 := by
  ext z z'
  simp only [sectorEmbed, Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply,
    Matrix.zero_apply]
  refine Finset.sum_eq_zero fun d _ => ?_
  by_cases h1 : d = ⟨i, z⟩
  · subst h1; simp [hii]
  · simp [h1]

theorem blockDiagonal'_mul_sectorEmbed {Z : ι → Type*} [∀ i, Fintype (Z i)]
    [∀ i, DecidableEq (Z i)] (U : ∀ i, Matrix (Z i) (Z i) ℂ) (i : ι) :
    blockDiagonal' U * sectorEmbed (Z := Z) i = sectorEmbed (Z := Z) i * U i := by
  ext ⟨i', z'⟩ z
  simp only [sectorEmbed, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single ⟨i, z⟩]
  · by_cases hi : i' = i
    · subst hi
      rw [blockDiagonal'_apply_eq, Finset.sum_eq_single z']
      · simp
      · intro w _ hw; simp [Ne.symm hw]
      · simp
    · rw [blockDiagonal'_apply_ne _ _ _ hi]
      simp [hi]
  · intro d _ hd; simp [hd]
  · simp

theorem blockDiagonal'_mem_unitary {Z : ι → Type*} [∀ i, Fintype (Z i)]
    [∀ i, DecidableEq (Z i)] {U : ∀ i, Matrix (Z i) (Z i) ℂ}
    (hU : ∀ i, U i ∈ unitary (Matrix (Z i) (Z i) ℂ)) :
    blockDiagonal' U ∈ unitary (Matrix (Σ i, Z i) (Σ i, Z i) ℂ) := by
  rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose, blockDiagonal'_conjTranspose,
    ← blockDiagonal'_mul]
  have : (fun k => (U k)ᴴ * U k) = (1 : ∀ i, Matrix (Z i) (Z i) ℂ) := by
    funext k
    have := (Matrix.mem_unitaryGroup_iff'.1 (hU k))
    rwa [star_eq_conjTranspose] at this
  rw [this, blockDiagonal'_one]

/-- The total dilation space of a finite family: the control register `i` selects the
sector `(ℂ^{m_i} ⊗ ℂ^{κ_i}) ⊕ ℂ^{n_i}`. -/
abbrev FamilyDilationSpace (n m : ι → ℕ) : Type _ := Σ i, DilationSpace (n i) (m i)

/-- The input embedding of the `i`-th map: control register set to `i`, ancilla adjoined. -/
def familyInput (n m : ι → ℕ) (i : ι) : Matrix (FamilyDilationSpace n m) (Fin (n i)) ℂ :=
  sectorEmbed (Z := fun j => DilationSpace (n j) (m j)) i * inputEmbed (n i) (m i)

/-- The output read-out of the `i`-th map with the ancilla in basis state `k`. -/
def familyReadout (n m : ι → ℕ) (i : ι) (k : Fin (n i) × Fin (m i)) :
    Matrix (Fin (m i)) (FamilyDilationSpace n m) ℂ :=
  readout k * (sectorEmbed (Z := fun j => DilationSpace (n j) (m j)) i)ᴴ

theorem familyInput_isometry (n m : ι → ℕ) (i : ι) :
    (familyInput n m i)ᴴ * familyInput n m i = 1 := by
  rw [familyInput, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ (sectorEmbed i),
    sectorEmbed_isometry, Matrix.one_mul, inputEmbed_isometry]

theorem familyInput_orthogonal (n m : ι → ℕ) {i i' : ι} (hii : i ≠ i') :
    (familyInput n m i)ᴴ * familyInput n m i' = 0 := by
  rw [familyInput, familyInput, conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc _ (sectorEmbed i'), sectorEmbed_orthogonal hii, Matrix.zero_mul,
    Matrix.mul_zero]

theorem familyReadout_mul_conjTranspose (n m : ι → ℕ) (i : ι) (k k' : Fin (n i) × Fin (m i)) :
    familyReadout n m i k * (familyReadout n m i k')ᴴ = if k = k' then 1 else 0 := by
  rw [familyReadout, familyReadout, conjTranspose_mul, conjTranspose_conjTranspose,
    Matrix.mul_assoc, ← Matrix.mul_assoc _ (sectorEmbed i), sectorEmbed_isometry,
    Matrix.one_mul, readout_mul_conjTranspose]

/-- **Proposition `prop:ncg-compression-defect`, first claim (simultaneous finite unitary
completion)**: for every finite family `T_i : M_{n_i}(ℂ) → M_{m_i}(ℂ)` of completely positive
trace-nonincreasing maps there is ONE unitary `U` on the finite space
`⊕_i ((ℂ^{m_i} ⊗ ℂ^{κ_i}) ⊕ ℂ^{n_i})` (finite ancillas `κ_i`, finite control register `i`)
such that `T_i(X) = ∑_k O_{i,k} U J_i X J_iᴴ Uᴴ O_{i,k}ᴴ` for all `i` and `X`, where the input
embeddings `J_i = familyInput` are isometries with mutually orthogonal ranges
(`familyInput_isometry`, `familyInput_orthogonal`) and the read-outs `O_{i,k} = familyReadout`
are coisometries with orthogonal supports (`familyReadout_mul_conjTranspose`). -/
theorem exists_simultaneous_unitary_completion {n m : ι → ℕ}
    (T : ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℂ →ₗ[ℂ] Matrix (Fin (m i)) (Fin (m i)) ℂ)
    (hCP : ∀ i, IsMatrixCompletelyPositive (T i)) (hTN : ∀ i, IsTraceNonincreasing (T i)) :
    ∃ U : Matrix (FamilyDilationSpace n m) (FamilyDilationSpace n m) ℂ,
      U ∈ unitary (Matrix (FamilyDilationSpace n m) (FamilyDilationSpace n m) ℂ) ∧
      ∀ i X, T i X = ∑ k : Fin (n i) × Fin (m i), familyReadout n m i k * U * familyInput n m i * X *
        (familyInput n m i)ᴴ * Uᴴ * (familyReadout n m i k)ᴴ := by
  choose U hU hT using fun i => exists_unitary_completion (T i) (hCP i) (hTN i)
  refine ⟨blockDiagonal' U, blockDiagonal'_mem_unitary hU, fun i X => ?_⟩
  rw [hT i X]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hE := blockDiagonal'_mul_sectorEmbed (Z := fun j => DilationSpace (n j) (m j)) U i
  have hI := sectorEmbed_isometry (Z := fun j => DilationSpace (n j) (m j)) i
  have hcore : (sectorEmbed (Z := fun j => DilationSpace (n j) (m j)) i)ᴴ * blockDiagonal' U *
      sectorEmbed (Z := fun j => DilationSpace (n j) (m j)) i = U i := by
    rw [Matrix.mul_assoc, hE, ← Matrix.mul_assoc, hI, Matrix.one_mul]
  have hcore' : (sectorEmbed (Z := fun j => DilationSpace (n j) (m j)) i)ᴴ *
      (blockDiagonal' U)ᴴ * sectorEmbed (Z := fun j => DilationSpace (n j) (m j)) i
        = (U i)ᴴ := by
    rw [← hcore]; simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hR : familyReadout n m i k * blockDiagonal' U * familyInput n m i * X *
        (familyInput n m i)ᴴ * (blockDiagonal' U)ᴴ * (familyReadout n m i k)ᴴ
      = readout k * ((sectorEmbed (Z := fun j => DilationSpace (n j) (m j)) i)ᴴ *
          blockDiagonal' U * sectorEmbed (Z := fun j => DilationSpace (n j) (m j)) i) *
          inputEmbed (n i) (m i) * X * (inputEmbed (n i) (m i))ᴴ *
          ((sectorEmbed (Z := fun j => DilationSpace (n j) (m j)) i)ᴴ * (blockDiagonal' U)ᴴ *
          sectorEmbed (Z := fun j => DilationSpace (n j) (m j)) i) * (readout k)ᴴ := by
    simp only [familyReadout, familyInput, conjTranspose_mul, conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  rw [hR, hcore, hcore']

/-- Non-vacuity witness for `exists_simultaneous_unitary_completion`: the identity channel
(Kraus operator `1`) is completely positive and trace-nonincreasing. -/
example (n : ℕ) :
    IsMatrixCompletelyPositive (krausMap (fun _ : Unit => (1 : Matrix (Fin n) (Fin n) ℂ))) ∧
    IsTraceNonincreasing (krausMap (fun _ : Unit => (1 : Matrix (Fin n) (Fin n) ℂ))) :=
  ⟨krausMap_completelyPositive _, fun X _ => by simp [krausMap_apply]⟩

end Completion

end CompressionDefect
end RenewalGeometry
