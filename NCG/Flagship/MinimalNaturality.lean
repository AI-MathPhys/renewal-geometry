/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.HodgeBSD
import NCG.Flagship.CutFactorization

/-!
# Minimal-realization naturality
  (`thm:minimal-realization-naturality-master`, flagship
   manuscript)

For a finite channel `Φ(X) = V*(X⊗I)V` with Stinespring isometry
`V` and a covariant physical automorphism
(`U_g*Φ(X)U_g = Φ(Z_g*XZ_g)`), minimality of the rotated dilation
(surjectivity of its cyclic stack, the matrix rendering of the
Stinespring cyclic span — disclosed) yields:

* the boxed intertwining: a unique unitary `W_g` on the
  environment with `(Z_g ⊗ W_g)V = VU_g`
  (`minimal_realization_naturality`), constructed by the generic
  Gram factorization `Ω = MN*(NN*)⁻¹` on the cyclic stacks
  (`gram_unitary`) and the full-matrix commutant computation
  (`full_commutant_scalar` + `cut_commutant_factorizes`);
* the boxed projective cocycle `W_gW_h = a(g,h)b(g,h)⁻¹W_{gh}`
  from uniqueness (`naturality_cocycle`);
* the boxed refinement covariance
  `g·Θ_V(F) = Θ_V(W_gFW_g*)` (`naturality_refinement`).

Hence the admitted refinement family and its record algebra are
natural; the interpretive uniqueness of invariantly characterized
Reads/resets is prose.
-/

open Matrix Kronecker Finset
open scoped ComplexOrder

namespace NCG

section GramUnitary

variable {n q : Type*} [Fintype n] [Fintype q] [DecidableEq n]
  [DecidableEq q]

omit [DecidableEq q] in
/-- Generic Gram factorization: equal Grams over a surjective
stack give a unitary intertwiner `Ω = MN*(NN*)⁻¹`. -/
theorem gram_unitary (M N : Matrix n q ℂ)
    (hgram : Nᴴ * N = Mᴴ * M)
    (hsurj : Function.Surjective N.mulVec) :
    ∃ Ω : Matrix n n ℂ, Ωᴴ * Ω = 1 ∧ Ω * N = M := by
  classical
  have hPD : (N * Nᴴ).PosDef :=
    ((hodge_cycle_observability N).2.1).mp hsurj
  have hdet : IsUnit (N * Nᴴ).det :=
    isUnit_iff_ne_zero.mpr hPD.det_pos.ne'
  have hHerm : ((N * Nᴴ)⁻¹)ᴴ = (N * Nᴴ)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  set Ω : Matrix n n ℂ := M * Nᴴ * (N * Nᴴ)⁻¹ with hΩ
  set P : Matrix q q ℂ := Nᴴ * (N * Nᴴ)⁻¹ * N with hP
  have hNP : N * P = N := by
    rw [hP, show N * (Nᴴ * (N * Nᴴ)⁻¹ * N)
        = (N * Nᴴ) * (N * Nᴴ)⁻¹ * N from by
      simp only [Matrix.mul_assoc],
      Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
  have hMP : M * P = M := by
    have hzero : (M * (1 - P))ᴴ * (M * (1 - P)) = 0 := by
      rw [Matrix.conjTranspose_mul,
        show (1 - P)ᴴ * Mᴴ * (M * (1 - P))
          = (1 - P)ᴴ * (Mᴴ * M) * (1 - P) from by
        simp only [Matrix.mul_assoc], ← hgram,
        show (1 - P)ᴴ * (Nᴴ * N) * (1 - P)
          = (N * (1 - P))ᴴ * (N * (1 - P)) from by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]]
      rw [Matrix.mul_sub, Matrix.mul_one, hNP, sub_self,
        Matrix.conjTranspose_zero, Matrix.mul_zero]
    have h0 := Matrix.conjTranspose_mul_self_eq_zero.mp hzero
    rw [Matrix.mul_sub, Matrix.mul_one] at h0
    have := sub_eq_zero.mp h0
    exact this.symm
  refine ⟨Ω, ?_, ?_⟩
  · rw [hΩ, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hHerm, Matrix.conjTranspose_conjTranspose,
      show (N * Nᴴ)⁻¹ * (N * Mᴴ) * (M * Nᴴ * (N * Nᴴ)⁻¹)
        = (N * Nᴴ)⁻¹ * (N * (Mᴴ * M) * Nᴴ) * (N * Nᴴ)⁻¹ from by
      simp only [Matrix.mul_assoc], ← hgram,
      show (N * Nᴴ)⁻¹ * (N * (Nᴴ * N) * Nᴴ) * (N * Nᴴ)⁻¹
        = ((N * Nᴴ)⁻¹ * (N * Nᴴ)) * ((N * Nᴴ) * (N * Nᴴ)⁻¹)
        from by simp only [Matrix.mul_assoc],
      Matrix.nonsing_inv_mul _ hdet,
      Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
  · rw [hΩ, show M * Nᴴ * (N * Nᴴ)⁻¹ * N = M * P from by
      rw [hP]
      simp only [Matrix.mul_assoc], hMP]

omit [DecidableEq n] [DecidableEq q] in
/-- Right cancellation across a surjective stack. -/
theorem eq_of_mul_stack_eq {r : Type*}
    (S T : Matrix r n ℂ) (N : Matrix n q ℂ)
    (h : S * N = T * N) (hsurj : Function.Surjective N.mulVec) :
    S = T := by
  have hvec : ∀ v, S *ᵥ v = T *ᵥ v := by
    intro v
    obtain ⟨w, rfl⟩ := hsurj v
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]
  classical
  ext i j
  have h1 := congrFun (hvec (Pi.single j 1)) i
  simp only [Matrix.mulVec, dotProduct] at h1
  rw [Finset.sum_eq_single j (fun k _ hk => by
      simp [Pi.single_eq_of_ne hk]) (fun hj =>
      absurd (Finset.mem_univ j) hj),
    Finset.sum_eq_single j (fun k _ hk => by
      simp [Pi.single_eq_of_ne hk]) (fun hj =>
      absurd (Finset.mem_univ j) hj)] at h1
  simpa using h1

end GramUnitary

section Commutant

variable {Kd : Type*} [Fintype Kd] [DecidableEq Kd]

/-- The commutant of the full matrix algebra is scalar. -/
theorem full_commutant_scalar (M : Matrix Kd Kd ℂ)
    (h : ∀ X : Matrix Kd Kd ℂ, X * M = M * X) :
    ∃ c : ℂ, M = c • 1 := by
  rcases isEmpty_or_nonempty Kd with hK | ⟨⟨k0⟩⟩
  · exact ⟨0, by ext i j; exact (IsEmpty.false i).elim⟩
  · refine ⟨M k0 k0, ?_⟩
    ext b j
    have h1 : (Matrix.single k0 b (1 : ℂ) * M) k0 j
        = (M * Matrix.single k0 b (1 : ℂ)) k0 j :=
      congrFun (congrFun (h (Matrix.single k0 b (1 : ℂ))) k0) j
    have hL : (Matrix.single k0 b (1 : ℂ) * M) k0 j = M b j := by
      rw [Matrix.mul_apply, Finset.sum_eq_single b]
      · simp
      · intro k _ hk
        simp [Ne.symm hk]
      · intro hb
        exact absurd (Finset.mem_univ b) hb
    have hR : (M * Matrix.single k0 b (1 : ℂ)) k0 j
        = if b = j then M k0 k0 else 0 := by
      rw [Matrix.mul_apply, Finset.sum_eq_single k0]
      · by_cases hbj : b = j <;> simp [hbj]
      · intro k _ hk
        simp [Ne.symm hk]
      · intro hb
        exact absurd (Finset.mem_univ k0) hb
    rw [hL, hR] at h1
    rw [h1, Matrix.smul_apply, Matrix.one_apply]
    by_cases hbj : b = j <;> simp [hbj]

end Commutant

section Naturality

variable {Kd Ed Hd : Type*} [Fintype Kd] [Fintype Ed] [Fintype Hd]
  [DecidableEq Kd] [DecidableEq Ed] [DecidableEq Hd]

/-- The Stinespring cyclic stack: columns `(X_{ab} ⊗ I)V'` over
the matrix-unit basis. -/
noncomputable def stineStack (V' : Matrix (Kd × Ed) Hd ℂ) :
    Matrix (Kd × Ed) ((Kd × Kd) × Hd) ℂ :=
  Matrix.of fun p q =>
    ((Matrix.single q.1.1 q.1.2 (1 : ℂ)
        ⊗ₖ (1 : Matrix Ed Ed ℂ)) * V') p q.2

omit [Fintype Hd] [DecidableEq Hd] in
/-- The stack Gram consists of channel moments, so equal moments
give equal stack Grams. -/
lemma stineStack_gram (V₁ V₂ : Matrix (Kd × Ed) Hd ℂ)
    (hmom : ∀ X : Matrix Kd Kd ℂ,
      V₁ᴴ * (X ⊗ₖ (1 : Matrix Ed Ed ℂ)) * V₁
        = V₂ᴴ * (X ⊗ₖ (1 : Matrix Ed Ed ℂ)) * V₂) :
    (stineStack V₁)ᴴ * stineStack V₁
      = (stineStack V₂)ᴴ * stineStack V₂ := by
  have key : ∀ (W : Matrix (Kd × Ed) Hd ℂ)
      (ab cd : Kd × Kd) (h h' : Hd),
      ((stineStack W)ᴴ * stineStack W) (ab, h) (cd, h')
        = (Wᴴ * ((((Matrix.single ab.1 ab.2 (1 : ℂ))ᴴ
            * Matrix.single cd.1 cd.2 (1 : ℂ))
              ⊗ₖ (1 : Matrix Ed Ed ℂ)) * W)) h h' := by
    intro W ab cd h h'
    have hsplit : (((Matrix.single ab.1 ab.2 (1 : ℂ))ᴴ
          * Matrix.single cd.1 cd.2 (1 : ℂ))
            ⊗ₖ (1 : Matrix Ed Ed ℂ))
        = (Matrix.single ab.1 ab.2 (1 : ℂ)
            ⊗ₖ (1 : Matrix Ed Ed ℂ))ᴴ
          * (Matrix.single cd.1 cd.2 (1 : ℂ)
            ⊗ₖ (1 : Matrix Ed Ed ℂ)) := by
      rw [conjTranspose_kronecker, Matrix.conjTranspose_one,
        ← Matrix.mul_kronecker_mul, Matrix.one_mul]
    rw [hsplit,
      show Wᴴ * ((Matrix.single ab.1 ab.2 (1 : ℂ)
            ⊗ₖ (1 : Matrix Ed Ed ℂ))ᴴ
          * (Matrix.single cd.1 cd.2 (1 : ℂ)
            ⊗ₖ (1 : Matrix Ed Ed ℂ)) * W)
        = ((Matrix.single ab.1 ab.2 (1 : ℂ)
            ⊗ₖ (1 : Matrix Ed Ed ℂ)) * W)ᴴ
          * ((Matrix.single cd.1 cd.2 (1 : ℂ)
            ⊗ₖ (1 : Matrix Ed Ed ℂ)) * W) from by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]]
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.conjTranspose_apply, Matrix.conjTranspose_apply]
    rfl
  ext ⟨ab, h⟩ ⟨cd, h'⟩
  rw [key V₁ ab cd h h', key V₂ ab cd h h',
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, hmom]

/-- The label matrix implementing left multiplication by
`Y ⊗ I` on the stack. -/
noncomputable def stackLabel (Y : Matrix Kd Kd ℂ) :
    Matrix ((Kd × Kd) × Hd) ((Kd × Kd) × Hd) ℂ :=
  Matrix.of fun q r =>
    if q.1.2 = r.1.2 ∧ q.2 = r.2 then Y q.1.1 r.1.1 else 0

/-- Matrix-unit expansion of a left product. -/
lemma mul_single_expand (Y : Matrix Kd Kd ℂ) (a b : Kd) :
    Y * Matrix.single a b (1 : ℂ)
      = ∑ c, Y c a • Matrix.single c b (1 : ℂ) := by
  ext i j
  rw [Matrix.mul_apply, Matrix.sum_apply,
    Finset.sum_eq_single a
      (fun k _ hk => by simp [Ne.symm hk])
      (fun ha => absurd (Finset.mem_univ a) ha),
    Finset.sum_eq_single i
      (fun c _ hc => by simp [hc])
      (fun hi => absurd (Finset.mem_univ i) hi)]
  by_cases hj : b = j <;>
    simp [hj]

omit [Fintype Kd] [Fintype Ed] [DecidableEq Kd]
  [DecidableEq Ed] in
/-- Sums pull out of the left Kronecker slot. -/
lemma sum_kronecker_left {ι : Type*} (s : Finset ι)
    (A : ι → Matrix Kd Kd ℂ) (B : Matrix Ed Ed ℂ) :
    (∑ c ∈ s, A c) ⊗ₖ B = ∑ c ∈ s, A c ⊗ₖ B := by
  ext ⟨p1, p2⟩ ⟨q1, q2⟩
  simp [Matrix.kroneckerMap_apply, Matrix.sum_apply,
    Finset.sum_mul]

/-- Left multiplication by `Y ⊗ I` acts on the stack through the
label matrix. -/
lemma stineStack_mul_left (V' : Matrix (Kd × Ed) Hd ℂ)
    (Y : Matrix Kd Kd ℂ) :
    (Y ⊗ₖ (1 : Matrix Ed Ed ℂ)) * stineStack V'
      = stineStack V' * stackLabel (Hd := Hd) Y := by
  ext p ⟨⟨a, b⟩, h⟩
  have hRHS : (stineStack V' * stackLabel (Hd := Hd) Y) p
      ((a, b), h)
      = ∑ c, stineStack V' p ((c, b), h) * Y c a := by
    rw [Matrix.mul_apply, Fintype.sum_prod_type,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_eq_single b
      (fun d _ hd => Finset.sum_eq_zero fun h' _ => by
        simp [stackLabel, hd])
      (fun hb => absurd (Finset.mem_univ b) hb),
      Finset.sum_eq_single h
      (fun h' _ hh => by simp [stackLabel, hh])
      (fun hh => absurd (Finset.mem_univ h) hh)]
    simp [stackLabel]
  have hLHS : ((Y ⊗ₖ (1 : Matrix Ed Ed ℂ)) * stineStack V') p
      ((a, b), h)
      = ∑ c, stineStack V' p ((c, b), h) * Y c a := by
    have h1 : ((Y ⊗ₖ (1 : Matrix Ed Ed ℂ)) * stineStack V') p
        ((a, b), h)
        = ((Y ⊗ₖ (1 : Matrix Ed Ed ℂ))
            * ((Matrix.single a b (1 : ℂ)
              ⊗ₖ (1 : Matrix Ed Ed ℂ)) * V')) p h := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun p' _ => rfl
    rw [h1, ← Matrix.mul_assoc,
      show (Y ⊗ₖ (1 : Matrix Ed Ed ℂ))
          * (Matrix.single a b (1 : ℂ) ⊗ₖ (1 : Matrix Ed Ed ℂ))
        = (Y * Matrix.single a b (1 : ℂ))
            ⊗ₖ (1 : Matrix Ed Ed ℂ) from by
        rw [← Matrix.mul_kronecker_mul, Matrix.one_mul],
      mul_single_expand, sum_kronecker_left, Matrix.sum_mul,
      Matrix.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.smul_kronecker, Matrix.smul_mul,
      Matrix.smul_apply, smul_eq_mul, mul_comm]
    rfl
  rw [hRHS, hLHS]

/-- The diagonal matrix units sum to the identity. -/
lemma sum_single_diag :
    (∑ a : Kd, Matrix.single a a (1 : ℂ)) = 1 := by
  ext i j
  rw [Matrix.sum_apply,
    Finset.sum_eq_single i
      (fun c _ hc => by simp [hc])
      (fun hi => absurd (Finset.mem_univ i) hi)]
  by_cases hij : i = j <;>
    simp [Matrix.one_apply, hij]

/-- The extraction matrix recovering `V'` from its stack. -/
noncomputable def stackExtract :
    Matrix ((Kd × Kd) × Hd) Hd ℂ :=
  Matrix.of fun q h =>
    if q.1.1 = q.1.2 ∧ q.2 = h then 1 else 0

/-- The stack recovers the isometry through the diagonal
labels. -/
lemma stineStack_extract (V' : Matrix (Kd × Ed) Hd ℂ) :
    stineStack V' * stackExtract (Kd := Kd) (Hd := Hd)
      = V' := by
  ext p h
  rw [Matrix.mul_apply, Fintype.sum_prod_type,
    Fintype.sum_prod_type]
  have hcollapse : ∀ c : Kd,
      (∑ d, ∑ h', stineStack V' p ((c, d), h')
        * stackExtract ((c, d), h') h)
      = stineStack V' p ((c, c), h) := by
    intro c
    rw [Finset.sum_eq_single c
      (fun d _ hd => Finset.sum_eq_zero fun h' _ => by
        simp [stackExtract, Ne.symm hd])
      (fun hc => absurd (Finset.mem_univ c) hc),
      Finset.sum_eq_single h
      (fun h' _ hh => by simp [stackExtract, hh])
      (fun hh => absurd (Finset.mem_univ h) hh)]
    simp [stackExtract]
  rw [Finset.sum_congr rfl fun c _ => hcollapse c]
  have hterm : ∀ c : Kd, stineStack V' p ((c, c), h)
      = ∑ p', (Matrix.single c c (1 : ℂ)
          ⊗ₖ (1 : Matrix Ed Ed ℂ)) p p' * V' p' h :=
    fun c => Matrix.mul_apply
  rw [Finset.sum_congr rfl fun c _ => hterm c, Finset.sum_comm]
  have hone : ∀ p' : Kd × Ed,
      (∑ c, (Matrix.single c c (1 : ℂ)
        ⊗ₖ (1 : Matrix Ed Ed ℂ)) p p')
      = (1 : Matrix (Kd × Ed) (Kd × Ed) ℂ) p p' := by
    intro p'
    rw [Finset.sum_eq_single p.1
      (fun c _ hc => by
        simp [Matrix.kroneckerMap_apply, hc])
      (fun hin => absurd (Finset.mem_univ p.1) hin)]
    by_cases h1 : p.1 = p'.1
    · by_cases h2 : p.2 = p'.2
      · simp [Matrix.kroneckerMap_apply, Matrix.one_apply,
          Prod.ext_iff, h1, h2]
      · simp [Matrix.kroneckerMap_apply, Prod.ext_iff, h2]
    · simp [Matrix.kroneckerMap_apply, Matrix.one_apply,
        Prod.ext_iff, h1]
  rw [Finset.sum_congr rfl fun p' _ => by
    rw [← Finset.sum_mul, hone p']]
  rw [Finset.sum_eq_single p
    (fun q _ hq => by simp [Ne.symm hq])
    (fun hin => absurd (Finset.mem_univ p) hin)]
  simp

omit [Fintype Hd] [DecidableEq Hd] in
/-- Environment operators commute with the stack through the
system slot. -/
lemma stack_kron_one_mul (V' : Matrix (Kd × Ed) Hd ℂ)
    (M : Matrix Ed Ed ℂ) :
    ((1 : Matrix Kd Kd ℂ) ⊗ₖ M) * stineStack V'
      = stineStack (((1 : Matrix Kd Kd ℂ) ⊗ₖ M) * V') := by
  ext p ⟨ab, h⟩
  have h1 : (((1 : Matrix Kd Kd ℂ) ⊗ₖ M) * stineStack V') p
      (ab, h)
      = (((1 : Matrix Kd Kd ℂ) ⊗ₖ M)
          * ((Matrix.single ab.1 ab.2 (1 : ℂ)
            ⊗ₖ (1 : Matrix Ed Ed ℂ)) * V')) p h := by
    rw [Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun p' _ => rfl
  rw [h1, ← Matrix.mul_assoc,
    show ((1 : Matrix Kd Kd ℂ) ⊗ₖ M)
        * (Matrix.single ab.1 ab.2 (1 : ℂ)
          ⊗ₖ (1 : Matrix Ed Ed ℂ))
      = (Matrix.single ab.1 ab.2 (1 : ℂ)
          ⊗ₖ (1 : Matrix Ed Ed ℂ))
        * ((1 : Matrix Kd Kd ℂ) ⊗ₖ M) from by
      rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
      simp,
    Matrix.mul_assoc]
  rfl

omit [Fintype Kd] [Fintype Ed] [DecidableEq Ed] in
/-- Injectivity of the environment slot. -/
lemma kron_one_left_inj [Nonempty Kd] (M N : Matrix Ed Ed ℂ)
    (h : (1 : Matrix Kd Kd ℂ) ⊗ₖ M
      = (1 : Matrix Kd Kd ℂ) ⊗ₖ N) : M = N := by
  obtain ⟨k0⟩ := ‹Nonempty Kd›
  ext e e'
  have h1 := congrFun (congrFun h (k0, e)) (k0, e')
  simpa [Matrix.kroneckerMap_apply, Matrix.one_apply] using h1

omit [DecidableEq Hd] in
/-- `thm:minimal-realization-naturality-master`, boxed
intertwining: covariance and minimality of the rotated dilation
produce a unique unitary `W` on the environment with
`(Z_g ⊗ W)V = VU_g`. -/
theorem minimal_realization_naturality [Nonempty Kd]
    (V : Matrix (Kd × Ed) Hd ℂ) (Ug : Matrix Hd Hd ℂ)
    (Zg : Matrix Kd Kd ℂ)
    (hcov : ∀ X : Matrix Kd Kd ℂ,
      Ugᴴ * (Vᴴ * (X ⊗ₖ (1 : Matrix Ed Ed ℂ)) * V) * Ug
        = Vᴴ * ((Zgᴴ * X * Zg) ⊗ₖ (1 : Matrix Ed Ed ℂ)) * V)
    (hmin : Function.Surjective
      (stineStack ((Zg ⊗ₖ (1 : Matrix Ed Ed ℂ)) * V)).mulVec) :
    ∃ W : Matrix Ed Ed ℂ, Wᴴ * W = 1
      ∧ (Zg ⊗ₖ W) * V = V * Ug
      ∧ ∀ W' : Matrix Ed Ed ℂ,
          (Zg ⊗ₖ W') * V = V * Ug → W' = W := by
  classical
  set B : Matrix (Kd × Ed) Hd ℂ
    := (Zg ⊗ₖ (1 : Matrix Ed Ed ℂ)) * V with hB
  set A : Matrix (Kd × Ed) Hd ℂ := V * Ug with hA
  have hconv : ∀ M : Matrix Ed Ed ℂ,
      (Zg ⊗ₖ M) * V = ((1 : Matrix Kd Kd ℂ) ⊗ₖ M) * B := by
    intro M
    rw [hB, ← Matrix.mul_assoc, ← Matrix.mul_kronecker_mul]
    simp
  have hmom : ∀ X : Matrix Kd Kd ℂ,
      Bᴴ * (X ⊗ₖ (1 : Matrix Ed Ed ℂ)) * B
        = Aᴴ * (X ⊗ₖ (1 : Matrix Ed Ed ℂ)) * A := by
    intro X
    have hBside : Bᴴ * (X ⊗ₖ (1 : Matrix Ed Ed ℂ)) * B
        = Vᴴ * ((Zgᴴ * X * Zg)
            ⊗ₖ (1 : Matrix Ed Ed ℂ)) * V := by
      rw [hB, Matrix.conjTranspose_mul, conjTranspose_kronecker,
        Matrix.conjTranspose_one,
        show (Zgᴴ * X * Zg) ⊗ₖ (1 : Matrix Ed Ed ℂ)
          = (Zgᴴ ⊗ₖ (1 : Matrix Ed Ed ℂ))
            * (X ⊗ₖ (1 : Matrix Ed Ed ℂ))
            * (Zg ⊗ₖ (1 : Matrix Ed Ed ℂ)) from by
          rw [← Matrix.mul_kronecker_mul,
            ← Matrix.mul_kronecker_mul, Matrix.one_mul,
            Matrix.one_mul]]
      simp only [Matrix.mul_assoc]
    have hAside : Aᴴ * (X ⊗ₖ (1 : Matrix Ed Ed ℂ)) * A
        = Ugᴴ * (Vᴴ * (X ⊗ₖ (1 : Matrix Ed Ed ℂ)) * V)
          * Ug := by
      rw [hA, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [hBside, hAside, hcov]
  have hgram := stineStack_gram B A hmom
  obtain ⟨Ω, hΩu, hΩN⟩ := gram_unitary (stineStack A)
    (stineStack B) hgram hmin
  have hcomm : ∀ Y : Matrix Kd Kd ℂ,
      (Y ⊗ₖ (1 : Matrix Ed Ed ℂ)) * Ω
        = Ω * (Y ⊗ₖ (1 : Matrix Ed Ed ℂ)) := by
    intro Y
    have h1 : Ω * ((Y ⊗ₖ (1 : Matrix Ed Ed ℂ)) * stineStack B)
        = (Y ⊗ₖ (1 : Matrix Ed Ed ℂ)) * stineStack A := by
      rw [stineStack_mul_left, ← Matrix.mul_assoc, hΩN,
        ← stineStack_mul_left]
    have h2 : ((Y ⊗ₖ (1 : Matrix Ed Ed ℂ)) * Ω) * stineStack B
        = (Ω * (Y ⊗ₖ (1 : Matrix Ed Ed ℂ))) * stineStack B := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, hΩN]
    exact eq_of_mul_stack_eq _ _ _ h2 hmin
  obtain ⟨W, hW⟩ := cut_commutant_factorizes
    (U := fun Y : Matrix Kd Kd ℂ => Y)
    (fun M hM => full_commutant_scalar M fun X => hM X)
    Ω (fun Y => (hcomm Y).symm)
  have hΩB : Ω * B = A := by
    have h3 : (Ω * stineStack B)
          * stackExtract (Kd := Kd) (Hd := Hd)
        = stineStack A * stackExtract (Kd := Kd) (Hd := Hd)
        := by rw [hΩN]
    rw [Matrix.mul_assoc, stineStack_extract,
      stineStack_extract] at h3
    exact h3
  have hbox : (Zg ⊗ₖ W) * V = V * Ug := by
    rw [hconv, ← hW, hΩB, hA]
  have hWu : Wᴴ * W = 1 := by
    have h5 : ((1 : Matrix Kd Kd ℂ) ⊗ₖ W)ᴴ
        * ((1 : Matrix Kd Kd ℂ) ⊗ₖ W) = 1 := by
      rw [← hW]; exact hΩu
    rw [conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul] at h5
    refine kron_one_left_inj (Kd := Kd) _ _ ?_
    rw [Matrix.one_kronecker_one]
    exact h5
  refine ⟨W, hWu, hbox, ?_⟩
  intro W' hW'
  have hD : (((1 : Matrix Kd Kd ℂ) ⊗ₖ W')
      - ((1 : Matrix Kd Kd ℂ) ⊗ₖ W)) * stineStack B
      = (0 : Matrix (Kd × Ed) (Kd × Ed) ℂ) * stineStack B := by
    rw [Matrix.zero_mul, Matrix.sub_mul, stack_kron_one_mul,
      stack_kron_one_mul,
      show ((1 : Matrix Kd Kd ℂ) ⊗ₖ W') * B = V * Ug from by
        rw [← hconv]; exact hW',
      show ((1 : Matrix Kd Kd ℂ) ⊗ₖ W) * B = V * Ug from by
        rw [← hconv]; exact hbox,
      sub_self]
  have h6 := eq_of_mul_stack_eq _ _ _ hD hmin
  exact kron_one_left_inj _ _ (sub_eq_zero.mp h6)

omit [DecidableEq Kd] [DecidableEq Ed] [DecidableEq Hd] in
/-- Boxed projective cocycle: `W_gW_h = a(g,h)b(g,h)⁻¹W_{gh}`
from the uniqueness clause. -/
theorem naturality_cocycle
    (V : Matrix (Kd × Ed) Hd ℂ)
    (Ug Uh Ugh : Matrix Hd Hd ℂ)
    (Zg Zh Zgh : Matrix Kd Kd ℂ)
    (Wg Wh Wgh : Matrix Ed Ed ℂ) (a b : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hboxg : (Zg ⊗ₖ Wg) * V = V * Ug)
    (hboxh : (Zh ⊗ₖ Wh) * V = V * Uh)
    (hU : Ug * Uh = a • Ugh) (hZcomp : Zg * Zh = b • Zgh)
    (huniq : ∀ W' : Matrix Ed Ed ℂ,
      (Zgh ⊗ₖ W') * V = V * Ugh → W' = Wgh) :
    Wg * Wh = (a * b⁻¹) • Wgh := by
  have hcomp : ((Zg * Zh) ⊗ₖ (Wg * Wh)) * V
      = V * (Ug * Uh) := by
    rw [Matrix.mul_kronecker_mul, Matrix.mul_assoc, hboxh,
      ← Matrix.mul_assoc, hboxg, Matrix.mul_assoc]
  rw [hZcomp, hU, Matrix.smul_kronecker, Matrix.smul_mul,
    Matrix.mul_smul] at hcomp
  have h1 : (Zgh ⊗ₖ (Wg * Wh)) * V
      = (b⁻¹ * a) • (V * Ugh) := by
    have h2 := congrArg (fun M => b⁻¹ • M) hcomp
    simp only [smul_smul] at h2
    rw [inv_mul_cancel₀ hb, one_smul] at h2
    exact h2
  have hres : (Zgh ⊗ₖ ((b * a⁻¹) • (Wg * Wh))) * V
      = V * Ugh := by
    rw [Matrix.kronecker_smul, Matrix.smul_mul, h1, smul_smul,
      show b * a⁻¹ * (b⁻¹ * a) = a⁻¹ * a * (b⁻¹ * b) from by
        ring,
      inv_mul_cancel₀ ha, inv_mul_cancel₀ hb, one_mul, one_smul]
  have hgh := huniq _ hres
  rw [← hgh, smul_smul,
    show a * b⁻¹ * (b * a⁻¹) = a⁻¹ * a * (b⁻¹ * b) from by ring,
    inv_mul_cancel₀ ha, inv_mul_cancel₀ hb, one_mul, one_smul]

/-- Boxed refinement covariance: `g·Θ_V(F) = Θ_V(W_gFW_g*)` for
the intertwined dilation. -/
theorem naturality_refinement
    (V : Matrix (Kd × Ed) Hd ℂ) (Ug : Matrix Hd Hd ℂ)
    (Zg : Matrix Kd Kd ℂ) (Wg F : Matrix Ed Ed ℂ)
    (X : Matrix Kd Kd ℂ)
    (hbox : (Zg ⊗ₖ Wg) * V = V * Ug)
    (hZu : Zg * Zgᴴ = 1) (hZu' : Zgᴴ * Zg = 1)
    (hWu : Wgᴴ * Wg = 1) (hUu : Ug * Ugᴴ = 1) :
    Ug * (Vᴴ * ((Zgᴴ * X * Zg) ⊗ₖ F) * V) * Ugᴴ
      = Vᴴ * (X ⊗ₖ (Wg * F * Wgᴴ)) * V := by
  have h1 : V * Ugᴴ = (Zgᴴ ⊗ₖ Wgᴴ) * V := by
    have h2 : (Zgᴴ ⊗ₖ Wgᴴ) * ((Zg ⊗ₖ Wg) * V)
        = (Zgᴴ ⊗ₖ Wgᴴ) * (V * Ug) := by rw [hbox]
    rw [← Matrix.mul_assoc, ← Matrix.mul_kronecker_mul, hZu',
      hWu, Matrix.one_kronecker_one, Matrix.one_mul] at h2
    have h3 : V * Ugᴴ
        = ((Zgᴴ ⊗ₖ Wgᴴ) * (V * Ug)) * Ugᴴ := by
      rw [← h2]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hUu,
      Matrix.mul_one] at h3
    exact h3
  have hL : Ug * (Vᴴ * ((Zgᴴ * X * Zg) ⊗ₖ F) * V) * Ugᴴ
      = (V * Ugᴴ)ᴴ * (((Zgᴴ * X * Zg) ⊗ₖ F) * (V * Ugᴴ)) := by
    rw [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  have hmid : (Zg ⊗ₖ Wg) * (((Zgᴴ * X * Zg) ⊗ₖ F)
      * (Zgᴴ ⊗ₖ Wgᴴ)) = X ⊗ₖ (Wg * F * Wgᴴ) := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      show Zg * (Zgᴴ * X * Zg * Zgᴴ)
          = Zg * Zgᴴ * X * (Zg * Zgᴴ) from by
        simp only [Matrix.mul_assoc],
      hZu, Matrix.one_mul, Matrix.mul_one,
      show Wg * (F * Wgᴴ) = Wg * F * Wgᴴ from by
        rw [Matrix.mul_assoc]]
  rw [hL, h1, Matrix.conjTranspose_mul, conjTranspose_kronecker,
    Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_conjTranspose,
    show Vᴴ * (Zg ⊗ₖ Wg) * (((Zgᴴ * X * Zg) ⊗ₖ F)
        * ((Zgᴴ ⊗ₖ Wgᴴ) * V))
      = Vᴴ * ((Zg ⊗ₖ Wg) * (((Zgᴴ * X * Zg) ⊗ₖ F)
          * (Zgᴴ ⊗ₖ Wgᴴ))) * V from by
      simp only [Matrix.mul_assoc], hmid]

end Naturality

end NCG
