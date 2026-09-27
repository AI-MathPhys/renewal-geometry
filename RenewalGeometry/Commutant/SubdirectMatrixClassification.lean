/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Commutant.FiniteComplexStarSubalgebraSemisimplicity
import NCG.Algebra.CanonicalReductions

/-!
# Finite subdirect matrix-algebra classification (`thm:subdirect-classification`)

`thm:subdirect-classification` of the spacetime–gauge duality paper: a unital `*`-subalgebra
`ℬ ⊆ ⊕_{i<r} M_{n_i}(ℂ)` whose coordinate projections are all surjective is, up to inner
automorphisms of the coordinates, the diagonal embedding of `⊕_β M_{d_β}(ℂ)` along a class
function `cls : Fin r → Fin k`; in particular coordinates in one class have the same size.

* `piMatrixBlockDiagonalAlgHom`: the block-diagonal embedding `⊕_i M_{n_i}(ℂ) → M_{Σ n_i}(ℂ)`,
  a star-preserving injective algebra homomorphism;
* `exists_wedderburn_pi_matrix`: **intrinsic Wedderburn decomposition** — every star-closed
  unital subalgebra of `⊕_i M_{n_i}(ℂ)` is isomorphic to `⊕_{β<k} M_{d_β}(ℂ)` with all
  `d_β ≥ 1` (semisimplicity from `FiniteComplexStarSubalgebraSemisimplicity`, then Mathlib's
  Wedderburn–Artin theorem over the algebraically closed field `ℂ`);
* `exists_factor_algEquiv_of_surjective`: a surjective unital homomorphism
  `⊕_β M_{d_β}(ℂ) → M_n(ℂ)` (`n ≥ 1`) kills all but one summand and is an isomorphism on it
  (the images of the central units are orthogonal central projections summing to `1`, hence
  scalars `0` or `1`, exactly one being `1`; a nonzero homomorphism out of a simple ring is
  injective);
* `algEquiv_matrix_size_eq`: isomorphic full matrix algebras have equal size;
* `finite_subdirect_classification`: **`thm:subdirect-classification`**.

The inner form of the coordinate identifications is obtained from Skolem–Noether for `M_n(ℂ)`
(`NCG.matrix_algEquiv_inner`): each coordinate `i` carries an invertible `V_i` such that
`ℬ = { x : ∀ i, x_i = V_i (Y_{cls i}) V_i⁻¹ for some Y ∈ ⊕_β M_{d_β}(ℂ) }`, where `Y_{cls i}` is
read in `M_{n_i}(ℂ)` through the size identity `n_i = d_{cls i}`.
-/

open Matrix

namespace RenewalGeometry
namespace SubdirectClassification

/-! ### The block-diagonal embedding -/

section BlockDiagonal

variable {r : ℕ} (n : Fin r → ℕ)

/-- The block-diagonal embedding `⊕_i M_{n_i}(ℂ) → M_{Σ_i n_i}(ℂ)` as a unital algebra
homomorphism. -/
def piMatrixBlockDiagonalAlgHom :
    (Π i, Matrix (Fin (n i)) (Fin (n i)) ℂ) →ₐ[ℂ]
      Matrix (Σ i, Fin (n i)) (Σ i, Fin (n i)) ℂ :=
  { Matrix.blockDiagonal'RingHom (fun i => Fin (n i)) ℂ with
    commutes' := fun c => by
      change Matrix.blockDiagonal' (algebraMap ℂ _ c) = algebraMap ℂ _ c
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        Matrix.blockDiagonal'_smul, Matrix.blockDiagonal'_one] }

@[simp] theorem piMatrixBlockDiagonalAlgHom_apply (x : Π i, Matrix (Fin (n i)) (Fin (n i)) ℂ) :
    piMatrixBlockDiagonalAlgHom n x = Matrix.blockDiagonal' x := rfl

theorem piMatrixBlockDiagonalAlgHom_injective :
    Function.Injective (piMatrixBlockDiagonalAlgHom n) :=
  Matrix.blockDiagonal'_injective

theorem piMatrixBlockDiagonalAlgHom_star (x : Π i, Matrix (Fin (n i)) (Fin (n i)) ℂ) :
    star (piMatrixBlockDiagonalAlgHom n x) = piMatrixBlockDiagonalAlgHom n (star x) := by
  simp only [piMatrixBlockDiagonalAlgHom_apply, Matrix.star_eq_conjTranspose,
    Matrix.blockDiagonal'_conjTranspose]
  rfl

/-- The image of a star-closed subalgebra of `⊕_i M_{n_i}(ℂ)` is a star subalgebra of
`M_{Σ n_i}(ℂ)`. -/
def imageStarSubalgebra (B : Subalgebra ℂ (Π i, Matrix (Fin (n i)) (Fin (n i)) ℂ))
    (hstar : ∀ b ∈ B, star b ∈ B) :
    StarSubalgebra ℂ (Matrix (Σ i, Fin (n i)) (Σ i, Fin (n i)) ℂ) :=
  { B.map (piMatrixBlockDiagonalAlgHom n) with
    star_mem' := by
      rintro _ ⟨b, hb, rfl⟩
      exact ⟨star b, hstar b hb, (piMatrixBlockDiagonalAlgHom_star n b).symm⟩ }

theorem imageStarSubalgebra_toSubalgebra (B : Subalgebra ℂ (Π i, Matrix (Fin (n i)) (Fin (n i)) ℂ))
    (hstar : ∀ b ∈ B, star b ∈ B) :
    (imageStarSubalgebra n B hstar).toSubalgebra = B.map (piMatrixBlockDiagonalAlgHom n) := rfl

/-- **Intrinsic Wedderburn decomposition.**  Every star-closed unital subalgebra of
`⊕_i M_{n_i}(ℂ)` is isomorphic, as a unital `ℂ`-algebra, to `⊕_{β<k} M_{d_β}(ℂ)` with all
`d_β ≥ 1`. -/
theorem exists_wedderburn_pi_matrix (B : Subalgebra ℂ (Π i, Matrix (Fin (n i)) (Fin (n i)) ℂ))
    (hstar : ∀ b ∈ B, star b ∈ B) :
    ∃ (k : ℕ) (d : Fin k → ℕ), (∀ β, NeZero (d β)) ∧
      Nonempty (B ≃ₐ[ℂ] Π β, Matrix (Fin (d β)) (Fin (d β)) ℂ) := by
  haveI hss : IsSemisimpleRing (imageStarSubalgebra n B hstar) :=
    FiniteComplexStarSubalgebraSemisimplicity.starSubalgebra_isSemisimpleRing _
  haveI : IsSemisimpleRing (B.map (piMatrixBlockDiagonalAlgHom n)) := hss
  obtain ⟨k, d, hd, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ
      (B.map (piMatrixBlockDiagonalAlgHom n))
  exact ⟨k, d, hd, ⟨(B.equivMapOfInjective _ (piMatrixBlockDiagonalAlgHom_injective n)).trans e⟩⟩

end BlockDiagonal

/-! ### Surjections out of a product of matrix algebras -/

section Factor

variable {k : ℕ} {d : Fin k → ℕ}

theorem single_one_mul (β : Fin k) (y : Π β, Matrix (Fin (d β)) (Fin (d β)) ℂ) :
    Pi.single β (1 : Matrix (Fin (d β)) (Fin (d β)) ℂ) * y = Pi.single β (y β) := by
  ext γ i j
  by_cases h : γ = β
  · subst h
    simp
  · simp [Pi.single_apply, h]

theorem mul_single_one (β : Fin k) (y : Π β, Matrix (Fin (d β)) (Fin (d β)) ℂ) :
    y * Pi.single β (1 : Matrix (Fin (d β)) (Fin (d β)) ℂ) = Pi.single β (y β) := by
  ext γ i j
  by_cases h : γ = β
  · subst h
    simp
  · simp [Pi.single_apply, h]

theorem sum_single_one :
    ∑ β, Pi.single β (1 : Matrix (Fin (d β)) (Fin (d β)) ℂ) =
      (1 : Π β, Matrix (Fin (d β)) (Fin (d β)) ℂ) :=
  Finset.univ_sum_single (1 : Π β, Matrix (Fin (d β)) (Fin (d β)) ℂ)

/-- **A surjection onto a full matrix algebra factors through one summand.**  A surjective
unital algebra homomorphism `ψ : ⊕_β M_{d_β}(ℂ) → M_n(ℂ)` (`n ≥ 1`, all `d_β ≥ 1`) is of the
form `ψ y = φ (y β)` for one index `β` and an algebra isomorphism `φ : M_{d_β}(ℂ) ≃ M_n(ℂ)`. -/
theorem exists_factor_algEquiv_of_surjective [hd : ∀ β, NeZero (d β)] {n : ℕ} (hn : 0 < n)
    (ψ : (Π β, Matrix (Fin (d β)) (Fin (d β)) ℂ) →ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (hψ : Function.Surjective ψ) :
    ∃ (β : Fin k) (φ : Matrix (Fin (d β)) (Fin (d β)) ℂ ≃ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ),
      ∀ y, ψ y = φ (y β) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  -- the images of the central units are scalars
  have hscalar : ∀ β, ∃ c : ℂ, ψ (Pi.single β 1) = Matrix.scalar (Fin n) c := by
    intro β
    have hmem : ψ (Pi.single β 1) ∈ Set.range (Matrix.scalar (Fin n)) := by
      rw [Matrix.mem_range_scalar_iff_commute_single']
      intro i j
      obtain ⟨y, hy⟩ := hψ (Matrix.single i j 1)
      rw [← hy]
      change ψ y * ψ (Pi.single β 1) = ψ (Pi.single β 1) * ψ y
      rw [← map_mul, ← map_mul, mul_single_one, single_one_mul]
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, hc.symm⟩
  choose c hc using hscalar
  -- idempotent scalars are `0` or `1`
  have hidem : ∀ β, c β = 0 ∨ c β = 1 := by
    intro β
    have h1 : ψ (Pi.single β 1) * ψ (Pi.single β 1) = ψ (Pi.single β 1) := by
      rw [← map_mul, ← Pi.single_mul, mul_one]
    rw [hc, ← map_mul] at h1
    have h2 : c β * c β = c β := Matrix.scalar_inj.mp h1
    have h3 : c β * (c β - 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp h3 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  -- the scalars sum to `1`, so one of them is `1`
  have hsum : ∑ β, c β = 1 := by
    have h1 : ∑ β, ψ (Pi.single β 1) = 1 := by
      rw [← map_sum, sum_single_one, map_one]
    simp_rw [hc] at h1
    rw [← map_sum] at h1
    have h2 : Matrix.scalar (Fin n) (∑ β, c β) = Matrix.scalar (Fin n) 1 := by
      rw [h1, map_one]
    exact Matrix.scalar_inj.mp h2
  have hex : ∃ β, c β = 1 := by
    by_contra hno
    push_neg at hno
    have hzero : ∀ β, c β = 0 := fun β => (hidem β).resolve_right (hno β)
    simp only [hzero, Finset.sum_const_zero] at hsum
    exact zero_ne_one hsum
  obtain ⟨β, hβ⟩ := hex
  have hunit : ψ (Pi.single β 1) = 1 := by rw [hc, hβ, map_one]
  -- `ψ` factors through the `β`-th coordinate
  have hfactor : ∀ y, ψ y = ψ (Pi.single β (y β)) := by
    intro y
    rw [← single_one_mul, map_mul, hunit, one_mul]
  let φ₀ : Matrix (Fin (d β)) (Fin (d β)) ℂ →ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun Y => ψ (Pi.single β Y)
      map_one' := hunit
      map_mul' := fun Y Z => by simp only [Pi.single_mul, map_mul]
      map_zero' := by simp only [Pi.single_zero, map_zero]
      map_add' := fun Y Z => by simp only [Pi.single_add, map_add]
      commutes' := fun a => by
        simp only [Algebra.algebraMap_eq_smul_one, Pi.single_smul, map_smul, hunit] }
  have hφ₀ : ∀ Y, φ₀ Y = ψ (Pi.single β Y) := fun Y => rfl
  haveI : Nonempty (Fin (d β)) := ⟨⟨0, Nat.pos_of_ne_zero (hd β).out⟩⟩
  have hinj : Function.Injective φ₀ := fun a b h => RingHom.injective φ₀.toRingHom h
  have hsurj : Function.Surjective φ₀ := by
    intro X
    obtain ⟨y, hy⟩ := hψ X
    exact ⟨y β, by rw [hφ₀, ← hfactor, hy]⟩
  refine ⟨β, AlgEquiv.ofBijective φ₀ ⟨hinj, hsurj⟩, fun y => ?_⟩
  rw [hfactor y]
  rfl

end Factor

/-! ### Sizes of isomorphic full matrix algebras -/

/-- Isomorphic full complex matrix algebras have the same size. -/
theorem algEquiv_matrix_size_eq {a b : ℕ}
    (φ : Matrix (Fin a) (Fin a) ℂ ≃ₐ[ℂ] Matrix (Fin b) (Fin b) ℂ) : a = b := by
  have h := LinearEquiv.finrank_eq φ.toLinearEquiv
  rw [Module.finrank_matrix, Module.finrank_matrix, Module.finrank_self, Fintype.card_fin,
    Fintype.card_fin, mul_one, mul_one] at h
  exact Nat.mul_self_inj.mp h

/-! ### The classification -/

/-- **`thm:subdirect-classification`** (finite subdirect matrix-algebra classification).
Let `ℬ ⊆ ⊕_{i<r} M_{n_i}(ℂ)` (`n_i ≥ 1`) be a unital star-closed subalgebra whose coordinate
projections are all surjective.  Then there are a number `k` of classes, sizes `d_β ≥ 1`, a
surjective class function `cls : Fin r → Fin k` with `n_i = d_{cls i}` (so coordinates in one
class have equal matrix size, and distinct sizes are never identified), and invertible
conjugators `V_i ∈ M_{n_i}(ℂ)` such that

`x ∈ ℬ ↔ ∃ Y ∈ ⊕_β M_{d_β}(ℂ), ∀ i, x_i = V_i · Y_{cls i} · V_i⁻¹`

(`Y_{cls i}` read in `M_{n_i}(ℂ)` through `n_i = d_{cls i}`): `ℬ` contains one independent
full matrix algebra `M_{d_β}(ℂ)` per class, embedded diagonally across the class up to the
inner automorphisms `Ad(V_i)`. -/
theorem finite_subdirect_classification {r : ℕ} (n : Fin r → ℕ) (hn : ∀ i, 0 < n i)
    (B : Subalgebra ℂ (Π i, Matrix (Fin (n i)) (Fin (n i)) ℂ)) (hstar : ∀ b ∈ B, star b ∈ B)
    (hsurj : ∀ i, ∀ X : Matrix (Fin (n i)) (Fin (n i)) ℂ, ∃ b ∈ B, b i = X) :
    ∃ (k : ℕ) (d : Fin k → ℕ) (cls : Fin r → Fin k) (hd : ∀ i, n i = d (cls i)),
      (∀ β, 0 < d β) ∧ Function.Surjective cls ∧
      ∃ V : ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℂ, (∀ i, IsUnit (V i)) ∧
        ∀ x : Π i, Matrix (Fin (n i)) (Fin (n i)) ℂ,
          x ∈ B ↔ ∃ Y : Π β, Matrix (Fin (d β)) (Fin (d β)) ℂ, ∀ i,
            x i = V i * Matrix.reindex (finCongr (hd i).symm) (finCongr (hd i).symm) (Y (cls i)) *
              (V i)⁻¹ := by
  classical
  obtain ⟨k, d, hd0, ⟨e⟩⟩ := exists_wedderburn_pi_matrix n B hstar
  haveI := hd0
  -- the coordinate projections composed with the Wedderburn isomorphism
  let ψ : ∀ i, (Π β, Matrix (Fin (d β)) (Fin (d β)) ℂ) →ₐ[ℂ] Matrix (Fin (n i)) (Fin (n i)) ℂ :=
    fun i => (Pi.evalAlgHom ℂ (fun i => Matrix (Fin (n i)) (Fin (n i)) ℂ) i).comp
      (B.val.comp e.symm.toAlgHom)
  have hψ : ∀ i (y : Π β, Matrix (Fin (d β)) (Fin (d β)) ℂ),
      ψ i y = (e.symm y : Π i, Matrix (Fin (n i)) (Fin (n i)) ℂ) i :=
    fun i y => rfl
  have hψsurj : ∀ i, Function.Surjective (ψ i) := by
    intro i X
    obtain ⟨b, hb, hbX⟩ := hsurj i X
    refine ⟨e ⟨b, hb⟩, ?_⟩
    rw [hψ, AlgEquiv.symm_apply_apply]
    exact hbX
  have hfac : ∀ i, ∃ (β : Fin k) (φ : Matrix (Fin (d β)) (Fin (d β)) ℂ ≃ₐ[ℂ]
      Matrix (Fin (n i)) (Fin (n i)) ℂ), ∀ y, ψ i y = φ (y β) :=
    fun i => exists_factor_algEquiv_of_surjective (hn i) (ψ i) (hψsurj i)
  choose cls φ hφ using hfac
  have hd : ∀ i, n i = d (cls i) := fun i => (algEquiv_matrix_size_eq (φ i)).symm
  -- Skolem–Noether: the identification of the `cls i`-th summand with the `i`-th coordinate
  -- is inner
  have hinner : ∀ i, ∃ V : Matrix (Fin (n i)) (Fin (n i)) ℂ, IsUnit V ∧
      ∀ Z : Matrix (Fin (d (cls i))) (Fin (d (cls i))) ℂ,
        φ i Z = V * Matrix.reindex (finCongr (hd i).symm) (finCongr (hd i).symm) Z * V⁻¹ := by
    intro i
    let α : Matrix (Fin (n i)) (Fin (n i)) ℂ ≃ₐ[ℂ] Matrix (Fin (n i)) (Fin (n i)) ℂ :=
      (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hd i).symm)).symm.trans (φ i)
    obtain ⟨V, hV, hαV⟩ := NCG.matrix_algEquiv_inner (hn i) α
    refine ⟨V, hV, fun Z => ?_⟩
    have h := hαV (Matrix.reindex (finCongr (hd i).symm) (finCongr (hd i).symm) Z)
    have hα : α (Matrix.reindex (finCongr (hd i).symm) (finCongr (hd i).symm) Z) = φ i Z := by
      simp only [α, AlgEquiv.trans_apply]
      congr 1
    rw [hα] at h
    exact h
  choose V hVunit hV using hinner
  refine ⟨k, d, cls, hd, fun β => Nat.pos_of_ne_zero (hd0 β).out, ?_, V, hVunit, fun x => ?_⟩
  · -- every class is seen by some coordinate
    intro β
    by_contra hno
    push_neg at hno
    have hzero : e.symm (Pi.single β 1) = 0 := by
      apply Subtype.ext
      funext i
      have h := hψ i (Pi.single β 1)
      rw [hφ] at h
      rw [Pi.single_eq_of_ne (hno i), map_zero] at h
      exact h.symm
    have h1 : (Pi.single β (1 : Matrix (Fin (d β)) (Fin (d β)) ℂ) :
        Π β, Matrix (Fin (d β)) (Fin (d β)) ℂ) = 0 := by
      have := congrArg e hzero
      rwa [AlgEquiv.apply_symm_apply, map_zero] at this
    have h2 := congrFun h1 β
    rw [Pi.single_eq_same, Pi.zero_apply] at h2
    haveI : Nonempty (Fin (d β)) := ⟨⟨0, Nat.pos_of_ne_zero (hd0 β).out⟩⟩
    exact one_ne_zero h2
  · constructor
    · intro hx
      refine ⟨e ⟨x, hx⟩, fun i => ?_⟩
      rw [← hV, ← hφ, hψ, AlgEquiv.symm_apply_apply]
    · rintro ⟨Y, hY⟩
      have hb : (e.symm Y : Π i, Matrix (Fin (n i)) (Fin (n i)) ℂ) = x := by
        funext i
        rw [hY i, ← hV, ← hφ, hψ]
      rw [← hb]
      exact (e.symm Y).2

end SubdirectClassification
end RenewalGeometry
