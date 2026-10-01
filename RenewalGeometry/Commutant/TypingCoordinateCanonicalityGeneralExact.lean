/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Commutant.ArbitraryIncidenceDualityExact

/-!
# Canonicality under arbitrary Wedderburn coordinates (`cor:typing-coordinate-canonicality`)

General form of `cor:typing-coordinate-canonicality` of the spacetime–gauge duality paper.
Two decompositions `z_λ ℋ ≅ K_λ ⊗ M_λ` and `z_λ ℋ ≅ K̃_λ ⊗ M̃_λ`, with possibly different
action factors `K̃_λ`, are only required to realize the same represented external–typing algebra:
`U (B(K) ⊗ 1) U^* = Ũ (B(K̃) ⊗ 1) Ũ^*` as sets.

* `spatial_of_starAlgHom`: every unital `*`-isomorphism `B(K) → B(K̃)` of full matrix algebras is
  spatial, `x ↦ V x V^*` with `V` unitary (built from the matrix units and a unit vector in the
  range of the image of a minimal projection, whose corner is one-dimensional);
* `multiplicity_unitary_of_same_algebra`: two such decompositions differ by `V_λ ⊗ W_λ` with
  `V_λ : K_λ → K̃_λ` and `W_λ : M_λ → M̃_λ` unitary (`U = Ũ (V ⊗ W)`);
* `coefficientSpace_genTransport`: the slices are independent of the carrier unitary `V`, so
  `𝔅̃_e = W_μ 𝔅_e W_λ^*`;
* `typing_coordinate_canonicality_general`: for a physical packet (incidences `𝐘_e` between
  central blocks) read in two such coordinate systems, there are multiplicity unitaries `W_λ`
  with `𝔅̃_e = W_μ 𝔅_e W_λ^*`, `𝒪̃_Y = W 𝒪_Y W^*` and `𝓜̃_type = W 𝓜_type W^*`
  (`eq:typing-coordinate-canonicality`).
-/

open Matrix
open scoped Kronecker

namespace RenewalGeometry
namespace ArbitraryIncidenceDuality

open SMSTQuiverCommutantAssembly GraphLoadedEdgeCommutant RepresentedJointPacket

set_option linter.unusedSectionVars false

/-! ### Unital `*`-isomorphisms of full matrix algebras are spatial -/

section Spatial

variable {K K' : Type*} [Fintype K] [DecidableEq K] [Fintype K'] [DecidableEq K']

/-- **Spatial implementation.**  A bijective unital `*`-homomorphism
`α : B(ℂ^K) → B(ℂ^{K'})` (`K` nonempty) is `x ↦ V x V^*` for a unitary `V : ℂ^K → ℂ^{K'}`. -/
theorem spatial_of_starAlgHom [Nonempty K] (α : Matrix K K ℂ →ₐ[ℂ] Matrix K' K' ℂ)
    (hstar : ∀ x, α xᴴ = (α x)ᴴ) (hinj : Function.Injective α)
    (hsurj : Function.Surjective α) :
    ∃ V : Matrix K' K ℂ, Vᴴ * V = 1 ∧ V * Vᴴ = 1 ∧ ∀ x, α x = V * x * Vᴴ := by
  classical
  obtain ⟨k0⟩ := (inferInstance : Nonempty K)
  set e : K → K → Matrix K K ℂ := fun i j => Matrix.single i j 1 with he
  have hemul : ∀ i j k l, e i j * e k l = if j = k then e i l else 0 := by
    intro i j k l
    by_cases hjk : j = k
    · subst hjk
      simp [he]
    · rw [if_neg hjk]
      simp [he, hjk]
  have heH : ∀ i j, (e i j)ᴴ = e j i := by
    intro i j
    simp [he, Matrix.conjTranspose_single]
  have hesum : ∑ i, e i i = 1 := by
    ext a b
    rw [Matrix.sum_apply, Finset.sum_eq_single a]
    · by_cases hab : a = b
      · subst hab
        simp [he]
      · simp [he, hab]
    · intro i _ hi
      simp [he, hi]
    · simp
  set P := α (e k0 k0) with hPdef
  have hPH : Pᴴ = P := by rw [hPdef, ← hstar, heH]
  have hPP : P * P = P := by rw [hPdef, ← map_mul, hemul, if_pos rfl]
  have hP0 : P ≠ 0 := by
    intro h
    have h0 : e k0 k0 = 0 := hinj (by rw [← hPdef, h, map_zero])
    have := congrFun (congrFun h0 k0) k0
    simp [he] at this
  have hcorner : ∀ y, ∃ c : ℂ, P * y * P = c • P := by
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    refine ⟨x k0 k0, ?_⟩
    rw [hPdef, ← map_mul, ← map_mul, ← map_smul]
    congr 1
    simp [he, Matrix.smul_single]
  -- a unit vector in the range of `P`
  obtain ⟨c, hc⟩ : ∃ c, P *ᵥ Pi.single c 1 ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    apply hP0
    ext a b
    have := congrFun (hall b) a
    simpa [Matrix.mulVec_single_one] using this
  set η := P *ᵥ Pi.single c 1 with hη
  have hPη : P *ᵥ η = η := by rw [hη, Matrix.mulVec_mulVec, hPP]
  obtain ⟨k1, hk1⟩ : ∃ k, η k ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hc (funext hall)
  set t : ℝ := ∑ k, Complex.normSq (η k) with ht
  have htpos : 0 < t := by
    apply lt_of_lt_of_le (Complex.normSq_pos.mpr hk1)
    exact Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (η k)) (Finset.mem_univ k1)
  set ξ : K' → ℂ := ((Real.sqrt t : ℂ)⁻¹) • η with hξdef
  have hξ : star ξ ⬝ᵥ ξ = 1 := by
    have hs : (Real.sqrt t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr htpos).ne'
    have hdot : star η ⬝ᵥ η = (t : ℂ) := by
      simp only [dotProduct, Pi.star_apply, ht, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Complex.star_def, mul_comm, Complex.mul_conj]
    rw [hξdef, star_smul, smul_dotProduct, dotProduct_smul, hdot, smul_eq_mul, smul_eq_mul,
      star_inv₀, Complex.star_def, Complex.conj_ofReal, ← mul_assoc, ← mul_inv,
      ← Complex.ofReal_mul, Real.mul_self_sqrt htpos.le, inv_mul_cancel₀]
    exact Complex.ofReal_ne_zero.mpr htpos.ne'
  have hPξ : P *ᵥ ξ = ξ := by rw [hξdef, Matrix.mulVec_smul, hPη]
  have hξ0 : ξ ≠ 0 := by
    intro h
    rw [h] at hξ
    simp at hξ
  -- `P = |ξ⟩⟨ξ|`
  have hQ : vecMulVec ξ (star ξ) = P := by
    obtain ⟨c', hc'⟩ := hcorner (vecMulVec ξ (star ξ))
    have hPQP : P * vecMulVec ξ (star ξ) * P = vecMulVec ξ (star ξ) := by
      rw [Matrix.mul_vecMulVec, hPξ, Matrix.vecMulVec_mul, ← hPH, ← Matrix.star_mulVec, hPξ]
    rw [hPQP] at hc'
    have h1 := congrArg (fun M => M *ᵥ ξ) hc'
    simp only [Matrix.vecMulVec_mulVec, hξ, Matrix.smul_mulVec, hPξ] at h1
    have h2 : c' = 1 := by
      have h3 : (1 - c') • ξ = 0 := by
        rw [sub_smul, one_smul, sub_eq_zero]
        simpa using h1
      rcases smul_eq_zero.mp h3 with h | h
      · exact (sub_eq_zero.mp h).symm
      · exact absurd h hξ0
    rw [hc', h2, one_smul]
  -- the partial isometry `R : e_{k0} ↦ ξ`
  set R : Matrix K' K ℂ := vecMulVec ξ (Pi.single k0 1) with hRdef
  have hsk : star (Pi.single k0 (1 : ℂ) : K → ℂ) = Pi.single k0 1 := by
    funext k
    by_cases h : k = k0
    · subst h
      simp
    · simp [Pi.single_apply, h]
  have hRR : Rᴴ * R = e k0 k0 := by
    rw [hRdef, Matrix.conjTranspose_vecMulVec, hsk, Matrix.vecMulVec_mul_vecMulVec, hξ, one_smul]
    ext a b
    by_cases ha : a = k0 <;> by_cases hb : b = k0
    · subst ha hb
      simp [he, Matrix.vecMulVec_apply]
    · subst ha
      simp [he, Matrix.vecMulVec_apply, Pi.single_apply, Matrix.single_apply, hb, Ne.symm hb]
    · subst hb
      simp [he, Matrix.vecMulVec_apply, Pi.single_apply, Matrix.single_apply, ha, Ne.symm ha]
    · simp [he, Matrix.vecMulVec_apply, Pi.single_apply, Matrix.single_apply, ha, Ne.symm ha]
  have hRRH : R * Rᴴ = P := by
    rw [hRdef, Matrix.conjTranspose_vecMulVec, hsk, Matrix.vecMulVec_mul_vecMulVec]
    have h1 : (Pi.single k0 (1 : ℂ) : K → ℂ) ⬝ᵥ Pi.single k0 1 = 1 := by simp
    rw [h1, one_smul, hQ]
  have hPR : P * R = R := by rw [hRdef, Matrix.mul_vecMulVec, hPξ]
  have hRe : R * e k0 k0 = R := by
    rw [hRdef, Matrix.vecMulVec_mul]
    congr 1
    funext k
    by_cases h : k = k0
    · subst h
      simp [he, Matrix.vecMul, dotProduct, Matrix.single_apply]
    · simp [he, Matrix.vecMul, dotProduct, Matrix.single_apply, Pi.single_apply, h, Ne.symm h]
  -- the implementing unitary
  set V : Matrix K' K ℂ := ∑ i, α (e i k0) * R * e k0 i with hVdef
  have hunit : ∀ a b, α (e a b) * V = V * e a b := by
    intro a b
    have hL : ∀ i, α (e a b) * (α (e i k0) * R * e k0 i) =
        if b = i then α (e a k0) * R * e k0 b else 0 := by
      intro i
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← map_mul, hemul]
      by_cases h : b = i
      · subst h
        rw [if_pos rfl, if_pos rfl]
      · rw [if_neg h, if_neg h, map_zero, Matrix.zero_mul, Matrix.zero_mul]
    have hR : ∀ i, α (e i k0) * R * e k0 i * e a b =
        if i = a then α (e a k0) * R * e k0 b else 0 := by
      intro i
      rw [Matrix.mul_assoc _ (e k0 i), hemul]
      by_cases h : i = a
      · subst h
        rw [if_pos rfl, if_pos rfl]
      · rw [if_neg h, if_neg h, Matrix.mul_zero]
    rw [hVdef, Matrix.mul_sum, Matrix.sum_mul]
    simp only [hL, hR, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hinter : ∀ x, α x * V = V * x := by
    intro x
    conv_lhs => rw [Matrix.matrix_eq_sum_single x]
    conv_rhs => rw [Matrix.matrix_eq_sum_single x]
    simp only [map_sum, Matrix.sum_mul, Matrix.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have hs : Matrix.single a b (x a b) = x a b • e a b := by
      rw [he, Matrix.smul_single, smul_eq_mul, mul_one]
    rw [hs, map_smul, Matrix.smul_mul, Matrix.mul_smul, hunit]
  have hVH : Vᴴ = ∑ i, e i k0 * Rᴴ * α (e k0 i) := by
    rw [hVdef, Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [conjTranspose_mul, conjTranspose_mul, heH, ← hstar, heH, Matrix.mul_assoc]
  have hV1 : Vᴴ * V = 1 := by
    have hterm : ∀ i j, e i k0 * Rᴴ * α (e k0 i) * (α (e j k0) * R * e k0 j) =
        if i = j then e i i else 0 := by
      intro i j
      calc e i k0 * Rᴴ * α (e k0 i) * (α (e j k0) * R * e k0 j)
          = e i k0 * (Rᴴ * (α (e k0 i * e j k0) * R)) * e k0 j := by
            rw [map_mul]; simp only [Matrix.mul_assoc]
        _ = _ := by
            rw [hemul]
            by_cases h : i = j
            · subst h
              rw [if_pos rfl, if_pos rfl, ← hPdef, hPR, hRR, hemul, if_pos rfl, hemul, if_pos rfl]
            · rw [if_neg h, if_neg h, map_zero, Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_zero,
                Matrix.zero_mul]
    rw [hVH, hVdef, Matrix.sum_mul, ← hesum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_sum]
    simp only [hterm, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hV2 : V * Vᴴ = 1 := by
    have hterm : ∀ i j, α (e i k0) * R * e k0 i * (e j k0 * Rᴴ * α (e k0 j)) =
        if i = j then α (e i i) else 0 := by
      intro i j
      calc α (e i k0) * R * e k0 i * (e j k0 * Rᴴ * α (e k0 j))
          = α (e i k0) * (R * (e k0 i * e j k0) * Rᴴ) * α (e k0 j) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by
            rw [hemul]
            by_cases h : i = j
            · subst h
              rw [if_pos rfl, if_pos rfl, hRe, hRRH, hPdef, ← map_mul, ← map_mul, hemul, if_pos rfl,
                hemul, if_pos rfl]
            · rw [if_neg h, if_neg h, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_zero,
                Matrix.zero_mul]
    rw [hVH, hVdef, Matrix.sum_mul, ← map_one α, ← hesum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_sum]
    simp only [hterm, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine ⟨V, hV1, hV2, fun x => ?_⟩
  calc α x = α x * (V * Vᴴ) := by rw [hV2, Matrix.mul_one]
    _ = V * x * Vᴴ := by rw [← Matrix.mul_assoc, hinter]


end Spatial

/-! ### Two decompositions of one central block -/

section Decompositions

variable {Z K K' N N' : Type*} [Fintype Z] [DecidableEq Z] [Fintype K] [DecidableEq K]
  [Fintype K'] [DecidableEq K'] [Fintype N] [DecidableEq N] [Fintype N'] [DecidableEq N']

/-- Cancellation of `· ⊗ I_N` for nonempty `N`. -/
theorem kron_one_cancel [Nonempty N] {x y : Matrix K K ℂ}
    (h : x ⊗ₖ (1 : Matrix N N ℂ) = y ⊗ₖ (1 : Matrix N N ℂ)) : x = y := by
  obtain ⟨n0⟩ := (inferInstance : Nonempty N)
  ext a b
  have := congrFun (congrFun h (a, n0)) (b, n0)
  simpa [kroneckerMap_apply] using this

/-- A unitary `U : ℂ^{K ⊗ N} → ℂ^Z` with `Z` nonempty has nonempty source. -/
theorem nonempty_of_unitary [Nonempty Z] {ι : Type*} [Fintype ι] (U : Matrix Z ι ℂ)
    (hU : U * Uᴴ = 1) : Nonempty ι := by
  by_contra h
  rw [not_nonempty_iff] at h
  obtain ⟨z⟩ := (inferInstance : Nonempty Z)
  have h1 := congrFun (congrFun hU z) z
  rw [Matrix.mul_apply, Finset.univ_eq_empty, Finset.sum_empty, Matrix.one_apply_eq] at h1
  exact zero_ne_one h1

/-- The represented action `x ↦ U (x ⊗ I) U^*` of `B(ℂ^K)` through a unitary
`U : ℂ^{K ⊗ N} → ℂ^Z`, as a unital algebra map. -/
def kronConjHom (U : Matrix Z (K × N) ℂ) (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1) :
    Matrix K K ℂ →ₐ[ℂ] Matrix Z Z ℂ where
  toFun x := U * (x ⊗ₖ (1 : Matrix N N ℂ)) * Uᴴ
  map_one' := by rw [Matrix.one_kronecker_one, Matrix.mul_one, hU2]
  map_mul' x y := by
    calc U * ((x * y) ⊗ₖ (1 : Matrix N N ℂ)) * Uᴴ
        = U * ((x ⊗ₖ (1 : Matrix N N ℂ)) * (Uᴴ * U) * (y ⊗ₖ (1 : Matrix N N ℂ))) * Uᴴ := by
          rw [hU1, Matrix.mul_one, ← Matrix.mul_kronecker_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  map_zero' := by rw [Matrix.zero_kronecker, Matrix.mul_zero, Matrix.zero_mul]
  map_add' x y := by rw [Matrix.add_kronecker, Matrix.mul_add, Matrix.add_mul]
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.smul_kronecker, Matrix.one_kronecker_one,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU2]

theorem kronConjHom_apply (U : Matrix Z (K × N) ℂ) (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1)
    (x : Matrix K K ℂ) : kronConjHom U hU1 hU2 x = U * (x ⊗ₖ (1 : Matrix N N ℂ)) * Uᴴ := rfl

theorem kronConjHom_injective [Nonempty N] (U : Matrix Z (K × N) ℂ) (hU1 : Uᴴ * U = 1)
    (hU2 : U * Uᴴ = 1) : Function.Injective (kronConjHom U hU1 hU2) := by
  intro x y h
  rw [kronConjHom_apply, kronConjHom_apply] at h
  apply kron_one_cancel (N := N)
  have h' := congrArg (fun X => Uᴴ * X * U) h
  calc x ⊗ₖ (1 : Matrix N N ℂ) = (Uᴴ * U) * (x ⊗ₖ (1 : Matrix N N ℂ)) * (Uᴴ * U) := by
        rw [hU1, Matrix.one_mul, Matrix.mul_one]
    _ = Uᴴ * (U * (x ⊗ₖ (1 : Matrix N N ℂ)) * Uᴴ) * U := by simp only [Matrix.mul_assoc]
    _ = Uᴴ * (U * (y ⊗ₖ (1 : Matrix N N ℂ)) * Uᴴ) * U := h'
    _ = (Uᴴ * U) * (y ⊗ₖ (1 : Matrix N N ℂ)) * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
    _ = y ⊗ₖ (1 : Matrix N N ℂ) := by rw [hU1, Matrix.one_mul, Matrix.mul_one]

theorem kronConjHom_conjTranspose (U : Matrix Z (K × N) ℂ) (hU1 : Uᴴ * U = 1)
    (hU2 : U * Uᴴ = 1) (x : Matrix K K ℂ) :
    kronConjHom U hU1 hU2 xᴴ = (kronConjHom U hU1 hU2 x)ᴴ := by
  rw [kronConjHom_apply, kronConjHom_apply, conjTranspose_mul, conjTranspose_mul,
    conjTranspose_conjTranspose, conjTranspose_kronecker, conjTranspose_one, Matrix.mul_assoc]

/-- **Two Wedderburn decompositions of one central block differ by `V ⊗ W`**
(`cor:typing-coordinate-canonicality`, first clause, general form).  If unitaries
`U : ℂ^{K ⊗ N} → ℂ^Z` and `U' : ℂ^{K' ⊗ N'} → ℂ^Z` (`Z ≠ ∅`) realize the same represented algebra,
`U (B(K) ⊗ 1) U^* = U' (B(K') ⊗ 1) U'^*` as sets, there are unitaries `V : ℂ^K → ℂ^{K'}` and
`W : ℂ^N → ℂ^{N'}` with `U = U' (V ⊗ W)`. -/
theorem multiplicity_unitary_of_same_algebra [Nonempty Z]
    (U : Matrix Z (K × N) ℂ) (U' : Matrix Z (K' × N') ℂ)
    (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1) (hU'1 : U'ᴴ * U' = 1) (hU'2 : U' * U'ᴴ = 1)
    (hsame : Set.range (fun x : Matrix K K ℂ => U * (x ⊗ₖ (1 : Matrix N N ℂ)) * Uᴴ) =
      Set.range (fun y : Matrix K' K' ℂ => U' * (y ⊗ₖ (1 : Matrix N' N' ℂ)) * U'ᴴ)) :
    ∃ (V : Matrix K' K ℂ) (W : Matrix N' N ℂ), Vᴴ * V = 1 ∧ V * Vᴴ = 1 ∧
      Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧ U = U' * (V ⊗ₖ W) := by
  classical
  have hKN : Nonempty (K × N) := nonempty_of_unitary U hU2
  have hKN' : Nonempty (K' × N') := nonempty_of_unitary U' hU'2
  have : Nonempty K := ⟨hKN.some.1⟩
  have : Nonempty N := ⟨hKN.some.2⟩
  have : Nonempty N' := ⟨hKN'.some.2⟩
  set Φ := kronConjHom U hU1 hU2 with hΦ
  set Φ' := kronConjHom U' hU'1 hU'2 with hΦ'
  have hΦinj := kronConjHom_injective U hU1 hU2
  have hΦ'inj := kronConjHom_injective U' hU'1 hU'2
  have hmem : ∀ x, ∃ y, Φ' y = Φ x := by
    intro x
    have hx : Φ x ∈ Set.range (fun x : Matrix K K ℂ => U * (x ⊗ₖ (1 : Matrix N N ℂ)) * Uᴴ) :=
      ⟨x, rfl⟩
    rw [hsame] at hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, hy⟩
  choose a ha using hmem
  -- the induced algebra map `B(K) → B(K')`
  let α : Matrix K K ℂ →ₐ[ℂ] Matrix K' K' ℂ :=
    { toFun := a
      map_one' := hΦ'inj (by rw [ha, map_one, map_one])
      map_mul' := fun x y => hΦ'inj (by rw [ha, map_mul, map_mul, ha, ha])
      map_zero' := hΦ'inj (by rw [ha, map_zero, map_zero])
      map_add' := fun x y => hΦ'inj (by rw [ha, map_add, map_add, ha, ha])
      commutes' := fun c => hΦ'inj (by rw [ha, AlgHom.commutes, AlgHom.commutes]) }
  have hαapp : ∀ x, Φ' (α x) = Φ x := ha
  have hαstar : ∀ x, α xᴴ = (α x)ᴴ := by
    intro x
    apply hΦ'inj
    rw [hαapp, kronConjHom_conjTranspose, kronConjHom_conjTranspose, hαapp]
  have hαinj : Function.Injective α := by
    intro x y h
    apply hΦinj
    rw [← hαapp, ← hαapp]
    exact congrArg Φ' h
  have hαsurj : Function.Surjective α := by
    intro y
    have hy : Φ' y ∈ Set.range (fun y : Matrix K' K' ℂ => U' * (y ⊗ₖ (1 : Matrix N' N' ℂ)) * U'ᴴ) :=
      ⟨y, rfl⟩
    rw [← hsame] at hy
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, hΦ'inj (by rw [hαapp]; exact hx)⟩
  obtain ⟨V, hV1, hV2, hαV⟩ := spatial_of_starAlgHom α hαstar hαinj hαsurj
  -- the corrected coordinates `U'' = U' (V ⊗ 1)`
  set U'' : Matrix Z (K × N') ℂ := U' * (V ⊗ₖ (1 : Matrix N' N' ℂ)) with hU''
  have hVk1 : (V ⊗ₖ (1 : Matrix N' N' ℂ))ᴴ * (V ⊗ₖ (1 : Matrix N' N' ℂ)) = 1 := by
    rw [conjTranspose_kronecker, conjTranspose_one, ← Matrix.mul_kronecker_mul, hV1,
      Matrix.one_mul, Matrix.one_kronecker_one]
  have hVk2 : (V ⊗ₖ (1 : Matrix N' N' ℂ)) * (V ⊗ₖ (1 : Matrix N' N' ℂ))ᴴ = 1 := by
    rw [conjTranspose_kronecker, conjTranspose_one, ← Matrix.mul_kronecker_mul, hV2,
      Matrix.one_mul, Matrix.one_kronecker_one]
  have hU''1 : U''ᴴ * U'' = 1 := by
    rw [hU'', conjTranspose_mul]
    calc (V ⊗ₖ (1 : Matrix N' N' ℂ))ᴴ * U'ᴴ * (U' * (V ⊗ₖ (1 : Matrix N' N' ℂ)))
        = (V ⊗ₖ (1 : Matrix N' N' ℂ))ᴴ * (U'ᴴ * U') * (V ⊗ₖ (1 : Matrix N' N' ℂ)) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU'1, Matrix.mul_one, hVk1]
  have hU''2 : U'' * U''ᴴ = 1 := by
    rw [hU'', conjTranspose_mul]
    calc U' * (V ⊗ₖ (1 : Matrix N' N' ℂ)) * ((V ⊗ₖ (1 : Matrix N' N' ℂ))ᴴ * U'ᴴ)
        = U' * ((V ⊗ₖ (1 : Matrix N' N' ℂ)) * (V ⊗ₖ (1 : Matrix N' N' ℂ))ᴴ) * U'ᴴ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hVk2, Matrix.mul_one, hU'2]
  have hsameAction : ∀ x : Matrix K K ℂ,
      U * (x ⊗ₖ (1 : Matrix N N ℂ)) * Uᴴ = U'' * (x ⊗ₖ (1 : Matrix N' N' ℂ)) * U''ᴴ := by
    intro x
    have hk : (V * x * Vᴴ) ⊗ₖ (1 : Matrix N' N' ℂ) = (V ⊗ₖ (1 : Matrix N' N' ℂ)) *
        (x ⊗ₖ (1 : Matrix N' N' ℂ)) * (Vᴴ ⊗ₖ (1 : Matrix N' N' ℂ)) := by
      rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.mul_one]
    rw [← kronConjHom_apply U hU1 hU2, ← hΦ, ← hαapp, hΦ', kronConjHom_apply, hαV, hU'',
      conjTranspose_mul, conjTranspose_kronecker, conjTranspose_one, hk]
    simp only [Matrix.mul_assoc]
  obtain ⟨W, ⟨hW1, hW2, hUW⟩, -⟩ :=
    multiplicity_unitary_of_same_action U U'' hU1 hU2 hU''1 hU''2 hsameAction
  refine ⟨V, W, hV1, hV2, hW1, hW2, ?_⟩
  rw [hUW, hU'', Matrix.mul_assoc, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

/-- In coordinates `U = U' X` with `X X^* = 1`, a physical incidence `𝐘` has new coordinate
expression `U_t'^* 𝐘 U_s' = X_t (U_t^* 𝐘 U_s) X_s^*`. -/
theorem incidence_coordinates_change_general {Zs Zt Is It Is' It' : Type*} [Fintype Zs]
    [Fintype Zt] [Fintype Is] [Fintype It] [Fintype Is'] [Fintype It'] [DecidableEq Is']
    [DecidableEq It']
    (Us : Matrix Zs Is ℂ) (Us' : Matrix Zs Is' ℂ) (Ut : Matrix Zt It ℂ) (Ut' : Matrix Zt It' ℂ)
    (Xs : Matrix Is' Is ℂ) (Xt : Matrix It' It ℂ) (hXs : Xs * Xsᴴ = 1) (hXt : Xt * Xtᴴ = 1)
    (hs : Us = Us' * Xs) (ht : Ut = Ut' * Xt) (Y : Matrix Zt Zs ℂ) :
    Ut'ᴴ * Y * Us' = Xt * (Utᴴ * Y * Us) * Xsᴴ := by
  have hs' : Us' = Us * Xsᴴ := by rw [hs, Matrix.mul_assoc, hXs, Matrix.mul_one]
  have ht' : Ut'ᴴ = Xt * Utᴴ := by
    have : Ut' = Ut * Xtᴴ := by rw [ht, Matrix.mul_assoc, hXt, Matrix.mul_one]
    rw [this, conjTranspose_mul, conjTranspose_conjTranspose]
  rw [hs', ht']
  simp only [Matrix.mul_assoc]

end Decompositions

/-! ### Carrier-unitary invariance of the slice spaces -/

section CarrierInvariance

variable {Kb Ka Kb' Ka' Nb Na : Type*} [Fintype Kb] [Fintype Ka] [Fintype Kb'] [Fintype Ka']
  [DecidableEq Kb] [DecidableEq Ka] [DecidableEq Kb'] [DecidableEq Ka'] [Fintype Nb] [Fintype Na]
  [DecidableEq Nb] [DecidableEq Na]

theorem kron_one_mul_apply' (A : Matrix Kb' Kb ℂ) (S : Matrix (Kb × Nb) (Ka × Na) ℂ)
    (vb : Kb') (n : Nb) (va : Ka) (m : Na) :
    ((A ⊗ₖ (1 : Matrix Nb Nb ℂ)) * S) (vb, n) (va, m) = ∑ vb', A vb vb' * S (vb', n) (va, m) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun vb' _ => ?_
  rw [Finset.sum_eq_single n]
  · simp [kroneckerMap_apply]
  · intro n' _ hn
    simp [kroneckerMap_apply, Matrix.one_apply_ne (Ne.symm hn)]
  · simp

theorem mul_kron_one_apply' (C : Matrix Ka Ka' ℂ) (S : Matrix (Kb × Nb) (Ka × Na) ℂ)
    (vb : Kb) (n : Nb) (va : Ka') (m : Na) :
    (S * (C ⊗ₖ (1 : Matrix Na Na ℂ))) (vb, n) (va, m) = ∑ va', S (vb, n) (va', m) * C va' va := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun va' _ => ?_
  rw [Finset.sum_eq_single m]
  · simp [kroneckerMap_apply]
  · intro m' _ hm
    simp [kroneckerMap_apply, Matrix.one_apply_ne hm]
  · simp

/-- Functional slices of `(A ⊗ I) S (C ⊗ I)` are functional slices of `S`. -/
theorem functionalSlice_kron_sandwich (A : Matrix Kb' Kb ℂ) (S : Matrix (Kb × Nb) (Ka × Na) ℂ)
    (C : Matrix Ka Ka' ℂ) (φ : Matrix Kb' Ka' ℂ →ₗ[ℂ] ℂ) :
    functionalSlice φ ((A ⊗ₖ (1 : Matrix Nb Nb ℂ)) * S * (C ⊗ₖ (1 : Matrix Na Na ℂ))) =
      functionalSlice (φ.comp (sandwichLinearMap A C)) S := by
  funext n m
  simp only [functionalSlice, LinearMap.coe_comp, sandwichLinearMap,
    LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  funext vb va
  rw [mul_kron_one_apply']
  simp only [kron_one_mul_apply']
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rfl

/-- **Carrier-basis independence of the slice space**: for left-invertible `A` and
right-invertible `C`, `{(φ ⊗ id)((A ⊗ I) S (C ⊗ I))} = {(φ ⊗ id)(S)}`. -/
theorem range_slice_kron_sandwich (A : Matrix Kb' Kb ℂ) (A' : Matrix Kb Kb' ℂ) (hA : A' * A = 1)
    (C : Matrix Ka Ka' ℂ) (C' : Matrix Ka' Ka ℂ) (hC : C * C' = 1)
    (S : Matrix (Kb × Nb) (Ka × Na) ℂ) :
    LinearMap.range (sliceLinearMap ((A ⊗ₖ (1 : Matrix Nb Nb ℂ)) * S *
        (C ⊗ₖ (1 : Matrix Na Na ℂ)))) = LinearMap.range (sliceLinearMap S) := by
  apply le_antisymm
  · rintro _ ⟨φ, rfl⟩
    exact ⟨φ.comp (sandwichLinearMap A C), (functionalSlice_kron_sandwich A S C φ).symm⟩
  · rintro _ ⟨φ, rfl⟩
    refine ⟨φ.comp (sandwichLinearMap A' C'), ?_⟩
    rw [sliceLinearMap_apply, sliceLinearMap_apply, functionalSlice_kron_sandwich]
    congr 1
    apply LinearMap.ext
    intro X
    simp only [LinearMap.comp_apply, sandwichLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
    congr 1
    calc A' * (A * X * C) * C' = (A' * A) * X * (C * C') := by simp only [Matrix.mul_assoc]
      _ = X := by rw [hA, hC, Matrix.one_mul, Matrix.mul_one]

end CarrierInvariance

/-! ### General change of Wedderburn coordinates on a packet -/

section GeneralTransport

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
variable {V M V' M' : Λ → Type*} [∀ l, Fintype (V l)] [∀ l, DecidableEq (V l)]
  [∀ l, Fintype (M l)] [∀ l, DecidableEq (M l)] [∀ l, Fintype (V' l)] [∀ l, DecidableEq (V' l)]
  [∀ l, Fintype (M' l)] [∀ l, DecidableEq (M' l)] {E : Type*} [Fintype E]

/-- The packet in new coordinates `U = U' (A ⊗ W)`: incidences
`(A_t ⊗ W_t) Y_e (A_s ⊗ W_s)^*`, with carrier unitaries `A_λ : K_λ → K̃_λ` and multiplicity
unitaries `W_λ`. -/
def genTransportPacket (P : RepresentedJointPacket Λ V M E)
    (A : ∀ l, Matrix (Fin 4 × V' l) (Fin 4 × V l) ℂ) (W : ∀ l, Matrix (M' l) (M l) ℂ) :
    RepresentedJointPacket Λ V' M' E where
  src := P.src
  tgt := P.tgt
  Y e := (A (P.tgt e) ⊗ₖ W (P.tgt e)) * P.Y e * (A (P.src e) ⊗ₖ W (P.src e))ᴴ

/-- The carrier unitaries do not change the coefficient spaces: `𝔅̃_e` of the general transport
equals that of the pure multiplicity transport. -/
theorem coefficientSpace_genTransport_eq (P : RepresentedJointPacket Λ V M E)
    (A : ∀ l, Matrix (Fin 4 × V' l) (Fin 4 × V l) ℂ) (W : ∀ l, Matrix (M' l) (M l) ℂ)
    (hA1 : ∀ l, (A l)ᴴ * A l = 1) (e : E) :
    (genTransportPacket P A W).coefficientSpace e = (transportPacket P W).coefficientSpace e := by
  have hsplit : (A (P.tgt e) ⊗ₖ W (P.tgt e)) * P.Y e * (A (P.src e) ⊗ₖ W (P.src e))ᴴ =
      (A (P.tgt e) ⊗ₖ (1 : Matrix (M' (P.tgt e)) (M' (P.tgt e)) ℂ)) *
        (((1 : Matrix (Fin 4 × V (P.tgt e)) (Fin 4 × V (P.tgt e)) ℂ) ⊗ₖ W (P.tgt e)) * P.Y e *
          ((1 : Matrix (Fin 4 × V (P.src e)) (Fin 4 × V (P.src e)) ℂ) ⊗ₖ (W (P.src e))ᴴ)) *
        ((A (P.src e))ᴴ ⊗ₖ (1 : Matrix (M' (P.src e)) (M' (P.src e)) ℂ)) := by
    rw [conjTranspose_kronecker]
    simp only [← Matrix.mul_assoc]
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  show LinearMap.range (sliceLinearMap
      ((A (P.tgt e) ⊗ₖ W (P.tgt e)) * P.Y e * (A (P.src e) ⊗ₖ W (P.src e))ᴴ)) =
    LinearMap.range (sliceLinearMap
      (((1 : Matrix (Fin 4 × V (P.tgt e)) (Fin 4 × V (P.tgt e)) ℂ) ⊗ₖ W (P.tgt e)) * P.Y e *
          ((1 : Matrix (Fin 4 × V (P.src e)) (Fin 4 × V (P.src e)) ℂ) ⊗ₖ (W (P.src e))ᴴ)))
  rw [hsplit]
  exact range_slice_kron_sandwich _ _ (hA1 _) _ _ (hA1 _) _

/-- `𝓜_type` and `𝒪_Y` depend only on the coefficient spaces. -/
theorem genTransport_algebras_eq (P : RepresentedJointPacket Λ V M E)
    (A : ∀ l, Matrix (Fin 4 × V' l) (Fin 4 × V l) ℂ) (W : ∀ l, Matrix (M' l) (M l) ℂ)
    (hA1 : ∀ l, (A l)ᴴ * A l = 1) :
    (genTransportPacket P A W).typedMultiplicityAlgebra =
        (transportPacket P W).typedMultiplicityAlgebra ∧
      (genTransportPacket P A W).coefficientActionAlgebra =
        (transportPacket P W).coefficientActionAlgebra := by
  have hc := coefficientSpace_genTransport_eq P A W hA1
  constructor
  · ext R
    rw [RepresentedJointPacket.mem_typedMultiplicityAlgebra,
      RepresentedJointPacket.mem_typedMultiplicityAlgebra]
    exact forall_congr' fun e => by rw [hc e]; rfl
  · unfold RepresentedJointPacket.coefficientActionAlgebra
      RepresentedJointPacket.coefficientGenerators
    congr 2
    refine Set.iUnion_congr fun e => ?_
    rw [hc e]
    rfl

/-- **`𝔅̃_e = W_μ 𝔅_e W_λ^*`** for a general change of coordinates `A_λ ⊗ W_λ`. -/
theorem coefficientSpace_genTransport (P : RepresentedJointPacket Λ V M E)
    (A : ∀ l, Matrix (Fin 4 × V' l) (Fin 4 × V l) ℂ) (W : ∀ l, Matrix (M' l) (M l) ℂ)
    (hA1 : ∀ l, (A l)ᴴ * A l = 1) (e : E) :
    (genTransportPacket P A W).coefficientSpace e =
      (P.coefficientSpace e).map (sandwichLinearMap (W (P.tgt e)) (W (P.src e))ᴴ) := by
  rw [coefficientSpace_genTransport_eq P A W hA1 e, coefficientSpace_transport]

end GeneralTransport

/-! ### Physical packets read in two Wedderburn coordinate systems -/

section Physical

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {E : Type*} [Fintype E]
variable {Z : Λ → Type*} [∀ l, Fintype (Z l)] [∀ l, DecidableEq (Z l)]
variable {V M V' M' : Λ → Type*} [∀ l, Fintype (V l)] [∀ l, DecidableEq (V l)]
  [∀ l, Fintype (M l)] [∀ l, DecidableEq (M l)] [∀ l, Fintype (V' l)] [∀ l, DecidableEq (V' l)]
  [∀ l, Fintype (M' l)] [∀ l, DecidableEq (M' l)]

/-- A physical packet (central blocks `z_λ ℋ = ℂ^{Z_λ}`, incidences
`𝐘_e : z_{s(e)} ℋ → z_{t(e)} ℋ`) read in the Wedderburn coordinates
`U_λ : K_λ ⊗ M_λ → z_λ ℋ`: `Y_e = U_{t(e)}^* 𝐘_e U_{s(e)}`. -/
def coordinatePacket (src tgt : E → Λ) (Y : ∀ e, Matrix (Z (tgt e)) (Z (src e)) ℂ)
    (U : ∀ l, Matrix (Z l) ((Fin 4 × V l) × M l) ℂ) : RepresentedJointPacket Λ V M E where
  src := src
  tgt := tgt
  Y e := (U (tgt e))ᴴ * Y e * U (src e)

/-- **Canonicality under Wedderburn coordinates (`cor:typing-coordinate-canonicality`, general
form).**  Let the same physical packet be read in two coordinate systems
`z_λ ℋ ≅ K_λ ⊗ M_λ` (`U_λ`) and `z_λ ℋ ≅ K̃_λ ⊗ M̃_λ` (`U'_λ`), with possibly different action
factors `K̃_λ = ℂ⁴ ⊗ Ṽ_λ`, which realize the same represented external–typing algebra on every
(nonzero) central block: `U_λ (B(K_λ) ⊗ 1) U_λ^* = U'_λ (B(K̃_λ) ⊗ 1) U'_λ^*` as sets.  Then the
coordinates differ by `A_λ ⊗ W_λ` with unitaries `A_λ : K_λ → K̃_λ` and multiplicity unitaries
`W_λ : M_λ → M̃_λ`, and `𝔅̃_e = W_{t(e)} 𝔅_e W_{s(e)}^*`, `𝒪̃_Y = W 𝒪_Y W^*`,
`𝓜̃_type = W 𝓜_type W^*` with `W = ⊕_λ W_λ` (`eq:typing-coordinate-canonicality`). -/
theorem typing_coordinate_canonicality_general [∀ l, Nonempty (Z l)] (src tgt : E → Λ)
    (Y : ∀ e, Matrix (Z (tgt e)) (Z (src e)) ℂ)
    (U : ∀ l, Matrix (Z l) ((Fin 4 × V l) × M l) ℂ)
    (U' : ∀ l, Matrix (Z l) ((Fin 4 × V' l) × M' l) ℂ)
    (hU1 : ∀ l, (U l)ᴴ * U l = 1) (hU2 : ∀ l, U l * (U l)ᴴ = 1)
    (hU'1 : ∀ l, (U' l)ᴴ * U' l = 1) (hU'2 : ∀ l, U' l * (U' l)ᴴ = 1)
    (hsame : ∀ l, Set.range (fun x : Matrix (Fin 4 × V l) (Fin 4 × V l) ℂ =>
        U l * (x ⊗ₖ (1 : Matrix (M l) (M l) ℂ)) * (U l)ᴴ) =
      Set.range (fun y : Matrix (Fin 4 × V' l) (Fin 4 × V' l) ℂ =>
        U' l * (y ⊗ₖ (1 : Matrix (M' l) (M' l) ℂ)) * (U' l)ᴴ)) :
    ∃ (A : ∀ l, Matrix (Fin 4 × V' l) (Fin 4 × V l) ℂ) (W : ∀ l, Matrix (M' l) (M l) ℂ),
      (∀ l, (A l)ᴴ * A l = 1 ∧ A l * (A l)ᴴ = 1) ∧
      (∀ l, (W l)ᴴ * W l = 1 ∧ W l * (W l)ᴴ = 1) ∧
      (∀ l, U l = U' l * (A l ⊗ₖ W l)) ∧
      (∀ e, (coordinatePacket src tgt Y U').coefficientSpace e =
        ((coordinatePacket src tgt Y U).coefficientSpace e).map
          (sandwichLinearMap (W (tgt e)) (W (src e))ᴴ)) ∧
      (((coordinatePacket src tgt Y U').coefficientActionAlgebra : StarSubalgebra ℂ _) :
          Set (Matrix (TotalCarrier M') (TotalCarrier M') ℂ)) =
        (fun X => totalUnitary W * X * (totalUnitary W)ᴴ) ''
          (((coordinatePacket src tgt Y U).coefficientActionAlgebra : StarSubalgebra ℂ _) :
            Set (Matrix (TotalCarrier M) (TotalCarrier M) ℂ)) ∧
      coefficientCarrierAlgebra (coordinatePacket src tgt Y U') =
        (fun X => totalUnitary W * X * (totalUnitary W)ᴴ) ''
          coefficientCarrierAlgebra (coordinatePacket src tgt Y U) ∧
      ((coordinatePacket src tgt Y U').typedMultiplicityAlgebra :
          Set (∀ l, Matrix (M' l) (M' l) ℂ)) =
        conjFamily W '' ((coordinatePacket src tgt Y U).typedMultiplicityAlgebra :
          Set (∀ l, Matrix (M l) (M l) ℂ)) := by
  have hdec : ∀ l, ∃ (A : Matrix (Fin 4 × V' l) (Fin 4 × V l) ℂ) (W : Matrix (M' l) (M l) ℂ),
      Aᴴ * A = 1 ∧ A * Aᴴ = 1 ∧ Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧ U l = U' l * (A ⊗ₖ W) :=
    fun l => multiplicity_unitary_of_same_algebra (U l) (U' l) (hU1 l) (hU2 l) (hU'1 l)
      (hU'2 l) (hsame l)
  choose A W hA1 hA2 hW1 hW2 hUAW using hdec
  set P := coordinatePacket src tgt Y U with hPdef
  have hX : ∀ l, (A l ⊗ₖ W l) * (A l ⊗ₖ W l)ᴴ = 1 := by
    intro l
    rw [conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hA2, hW2, Matrix.one_kronecker_one]
  have hP' : coordinatePacket src tgt Y U' = genTransportPacket P A W := by
    show (⟨src, tgt, fun e => (U' (tgt e))ᴴ * Y e * U' (src e)⟩ :
        RepresentedJointPacket Λ V' M' E) =
      ⟨src, tgt, fun e => (A (tgt e) ⊗ₖ W (tgt e)) * ((U (tgt e))ᴴ * Y e * U (src e)) *
        (A (src e) ⊗ₖ W (src e))ᴴ⟩
    congr 1
    funext e
    exact incidence_coordinates_change_general (U (src e)) (U' (src e)) (U (tgt e))
      (U' (tgt e)) _ _ (hX _) (hX _) (hUAW _) (hUAW _) (Y e)
  obtain ⟨htyped, hO⟩ := genTransport_algebras_eq P A W hA1
  have hcarrier : coefficientCarrierAlgebra (genTransportPacket P A W) =
      coefficientCarrierAlgebra (transportPacket P W) := by
    unfold coefficientCarrierAlgebra
    rw [htyped]
  refine ⟨A, W, fun l => ⟨hA1 l, hA2 l⟩, fun l => ⟨hW1 l, hW2 l⟩, hUAW, ?_, ?_, ?_, ?_⟩
  · intro e
    have hYe : (U' (tgt e))ᴴ * Y e * U' (src e) = (A (tgt e) ⊗ₖ W (tgt e)) *
        ((U (tgt e))ᴴ * Y e * U (src e)) * (A (src e) ⊗ₖ W (src e))ᴴ :=
      incidence_coordinates_change_general (U (src e)) (U' (src e)) (U (tgt e))
        (U' (tgt e)) _ _ (hX _) (hX _) (hUAW _) (hUAW _) (Y e)
    show LinearMap.range (sliceLinearMap ((U' (tgt e))ᴴ * Y e * U' (src e))) = _
    rw [hYe]
    exact coefficientSpace_genTransport P A W hA1 e
  · rw [hP', hO]
    exact coefficientActionAlgebra_transport P W hW1 hW2
  · rw [hP', hcarrier]
    exact coefficientCarrierAlgebra_transport P W hW1 hW2
  · rw [hP', htyped]
    exact typedMultiplicity_transport P W hW1 hW2

end Physical

end ArbitraryIncidenceDuality
end RenewalGeometry
