/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.MinimalNaturality

/-!
# Predictive Radon–Nikodym envelope
  (`thm:predictive-RN-master`, flagship manuscript)

For the finite Stinespring model `Φ(X) = V*(X⊗I)V` with
environment coordinate `Θ_V(F)(X) = V*(X⊗F)V`:

* the map `F ↦ Θ_V(F)` is affine (`thetaV_add`, `thetaV_smul`)
  and lands in the CP order interval: positive `F` give positive
  values on positive inputs (`thetaV_posSemidef`), and `F ⪯ I`
  gives domination `Θ_V(F) ≤ Φ` through the exact complement
  identity `Φ - Θ_V(F) = Θ_V(I-F)` (`thetaV_dominated`);
* the coordinate is unique: minimality (surjectivity of the
  Stinespring cyclic stack, as in the naturality record) forces
  `Θ_V(F) = 0 → F = 0` (`thetaV_injective`), by evaluating the
  stack pairing on matrix units and cancelling the stack on both
  sides;
* finite POVMs on the environment correspond to finite CP
  decompositions of `Φ`: `Σ Fᵢ = I → Σ Θ_V(Fᵢ) = Φ`
  (`thetaV_povm`).

Rendering disclosed: complete positivity and the CP order are
rendered at the level of positive matrix inputs of every
Kronecker-ampliated size (the Choi-equivalent form used
throughout the house ledger); the converse surjectivity of the
envelope — every `0 ≤_CP Ψ ≤_CP Φ` arises as some `Θ_V(F)` — is
the finite Radon–Nikodym theorem for CP maps together with the
minimal-commutant identification, the manuscript's standard cited
input, and is not re-proved here.  The automorphism action
`g·Θ_V(F) = Θ_V(W_g F W_g*)` is the already-recorded
`naturality_refinement` of the minimal-realization slice.
-/

open Matrix Kronecker Finset
open scoped ComplexOrder

namespace NCG

variable {Kd Ed Hd : Type*} [Fintype Kd] [Fintype Ed]
  [Fintype Hd] [DecidableEq Kd] [DecidableEq Ed]
  [DecidableEq Hd]

/-- The Radon–Nikodym coordinate map
`Θ_V(F)(X) = V*(X⊗F)V`. -/
noncomputable def thetaV (V' : Matrix (Kd × Ed) Hd ℂ)
    (F : Matrix Ed Ed ℂ) (X : Matrix Kd Kd ℂ) :
    Matrix Hd Hd ℂ :=
  V'ᴴ * (X ⊗ₖ F) * V'

omit [Fintype Kd] [Fintype Ed] [DecidableEq Kd] [DecidableEq Ed] in
theorem kronecker_sub' (X : Matrix Kd Kd ℂ)
    (F G : Matrix Ed Ed ℂ) :
    X ⊗ₖ (F - G) = X ⊗ₖ F - X ⊗ₖ G := by
  ext ⟨a, e⟩ ⟨b, f⟩
  simp [Matrix.kroneckerMap_apply, mul_sub]

omit [Fintype Kd] [Fintype Ed] [DecidableEq Kd] [DecidableEq Ed] in
theorem kronecker_sum' {ι : Type*} (s : Finset ι)
    (X : Matrix Kd Kd ℂ) (F : ι → Matrix Ed Ed ℂ) :
    X ⊗ₖ (∑ i ∈ s, F i) = ∑ i ∈ s, X ⊗ₖ F i := by
  ext ⟨a, e⟩ ⟨b, f⟩
  simp [Matrix.kroneckerMap_apply, Matrix.sum_apply,
    Finset.mul_sum]

omit [Fintype Hd] [DecidableEq Kd] [DecidableEq Ed] [DecidableEq Hd] in
/-- Affinity of the coordinate map: additivity. -/
theorem thetaV_add (V' : Matrix (Kd × Ed) Hd ℂ)
    (F G : Matrix Ed Ed ℂ) (X : Matrix Kd Kd ℂ) :
    thetaV V' (F + G) X = thetaV V' F X + thetaV V' G X := by
  have h1 : X ⊗ₖ (F + G) = X ⊗ₖ F + X ⊗ₖ G := by
    ext ⟨a, e⟩ ⟨b, f⟩
    simp [Matrix.kroneckerMap_apply, mul_add]
  simp [thetaV, h1, Matrix.mul_add, Matrix.add_mul]

omit [Fintype Hd] [DecidableEq Kd] [DecidableEq Ed] [DecidableEq Hd] in
/-- Affinity of the coordinate map: homogeneity. -/
theorem thetaV_smul (V' : Matrix (Kd × Ed) Hd ℂ) (c : ℂ)
    (F : Matrix Ed Ed ℂ) (X : Matrix Kd Kd ℂ) :
    thetaV V' (c • F) X = c • thetaV V' F X := by
  have h1 : X ⊗ₖ (c • F) = c • (X ⊗ₖ F) :=
    Matrix.kronecker_smul c X F
  simp [thetaV, h1, Matrix.mul_smul, Matrix.smul_mul]

omit [Fintype Hd] [DecidableEq Kd] [DecidableEq Ed] [DecidableEq Hd] in
/-- Positivity: a positive environment coordinate gives a
positive map on positive inputs of every ampliated size. -/
theorem thetaV_posSemidef [Finite Hd]
    (V' : Matrix (Kd × Ed) Hd ℂ)
    {F : Matrix Ed Ed ℂ} {X : Matrix Kd Kd ℂ}
    (hF : F.PosSemidef) (hX : X.PosSemidef) :
    (thetaV V' F X).PosSemidef := by
  have h1 : (X ⊗ₖ F).PosSemidef := hX.kronecker hF
  have h2 := h1.conjTranspose_mul_mul_same V'
  simpa [thetaV, Matrix.mul_assoc] using h2

omit [Fintype Hd] [DecidableEq Kd] [DecidableEq Hd] in
/-- Domination: the exact complement identity
`Φ - Θ_V(F) = Θ_V(I - F)`, positive for `F ⪯ I`. -/
theorem thetaV_dominated [Finite Hd]
    (V' : Matrix (Kd × Ed) Hd ℂ)
    {F : Matrix Ed Ed ℂ} {X : Matrix Kd Kd ℂ}
    (hF : ((1 : Matrix Ed Ed ℂ) - F).PosSemidef)
    (hX : X.PosSemidef) :
    (thetaV V' 1 X - thetaV V' F X).PosSemidef := by
  have h1 : thetaV V' 1 X - thetaV V' F X
      = thetaV V' (1 - F) X := by
    simp [thetaV, kronecker_sub', Matrix.mul_sub,
      Matrix.sub_mul]
  rw [h1]
  exact thetaV_posSemidef V' hF hX

omit [Fintype Hd] [DecidableEq Kd] [DecidableEq Hd] in
/-- Finite POVMs on the environment produce finite CP
decompositions of the channel. -/
theorem thetaV_povm (V' : Matrix (Kd × Ed) Hd ℂ)
    {ι : Type*} (s : Finset ι) (F : ι → Matrix Ed Ed ℂ)
    (hsum : ∑ i ∈ s, F i = 1) (X : Matrix Kd Kd ℂ) :
    ∑ i ∈ s, thetaV V' (F i) X = thetaV V' 1 X := by
  rw [← hsum]
  simp only [thetaV, kronecker_sum']
  rw [Matrix.mul_sum, Matrix.sum_mul]

omit [Fintype Hd] [DecidableEq Hd] in
/-- The block pairing of the cyclic stack with the environment
coordinate reduces to the coordinate map on matrix units. -/
theorem block_pairing (V' : Matrix (Kd × Ed) Hd ℂ)
    (F : Matrix Ed Ed ℂ) (a b c d : Kd) :
    ((Matrix.single a b (1 : ℂ)
        ⊗ₖ (1 : Matrix Ed Ed ℂ)) * V')ᴴ
      * ((1 : Matrix Kd Kd ℂ) ⊗ₖ F)
      * ((Matrix.single c d (1 : ℂ)
        ⊗ₖ (1 : Matrix Ed Ed ℂ)) * V')
    = thetaV V' F
        ((Matrix.single a b (1 : ℂ))ᴴ
          * Matrix.single c d (1 : ℂ)) := by
  rw [thetaV, Matrix.conjTranspose_mul, conjTranspose_kronecker,
    Matrix.conjTranspose_one]
  have h1 : ((Matrix.single a b (1 : ℂ))ᴴ
        ⊗ₖ (1 : Matrix Ed Ed ℂ))
      * ((1 : Matrix Kd Kd ℂ) ⊗ₖ F)
      = (Matrix.single a b (1 : ℂ))ᴴ ⊗ₖ F := by
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one,
      Matrix.one_mul]
  have h2 : ((Matrix.single a b (1 : ℂ))ᴴ ⊗ₖ F)
      * (Matrix.single c d (1 : ℂ)
        ⊗ₖ (1 : Matrix Ed Ed ℂ))
      = ((Matrix.single a b (1 : ℂ))ᴴ
          * Matrix.single c d (1 : ℂ)) ⊗ₖ F := by
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
  calc (V'ᴴ * ((Matrix.single a b (1 : ℂ))ᴴ
        ⊗ₖ (1 : Matrix Ed Ed ℂ)))
      * ((1 : Matrix Kd Kd ℂ) ⊗ₖ F)
      * ((Matrix.single c d (1 : ℂ)
        ⊗ₖ (1 : Matrix Ed Ed ℂ)) * V')
      = V'ᴴ * (((Matrix.single a b (1 : ℂ))ᴴ
          ⊗ₖ (1 : Matrix Ed Ed ℂ))
        * ((1 : Matrix Kd Kd ℂ) ⊗ₖ F))
        * ((Matrix.single c d (1 : ℂ)
          ⊗ₖ (1 : Matrix Ed Ed ℂ)) * V') := by
        simp only [Matrix.mul_assoc]
    _ = V'ᴴ * ((Matrix.single a b (1 : ℂ))ᴴ ⊗ₖ F)
        * ((Matrix.single c d (1 : ℂ)
          ⊗ₖ (1 : Matrix Ed Ed ℂ)) * V') := by rw [h1]
    _ = V'ᴴ * (((Matrix.single a b (1 : ℂ))ᴴ ⊗ₖ F)
        * (Matrix.single c d (1 : ℂ)
          ⊗ₖ (1 : Matrix Ed Ed ℂ))) * V' := by
        simp only [Matrix.mul_assoc]
    _ = V'ᴴ * (((Matrix.single a b (1 : ℂ))ᴴ
          * Matrix.single c d (1 : ℂ)) ⊗ₖ F) * V' := by
        rw [h2]

omit [DecidableEq Hd] in
/-- Uniqueness of the Radon–Nikodym coordinate: minimality
(surjectivity of the cyclic stack) forces injectivity. -/
theorem thetaV_injective [Nonempty Kd]
    (V' : Matrix (Kd × Ed) Hd ℂ)
    (hmin : Function.Surjective (stineStack V').mulVec)
    {F : Matrix Ed Ed ℂ} (hFh : F.IsHermitian)
    (hzero : ∀ X : Matrix Kd Kd ℂ, thetaV V' F X = 0) :
    F = 0 := by
  classical
  set S := stineStack V' with hS
  have key : ∀ (ab cd : Kd × Kd) (h h' : Hd),
      (Sᴴ * ((1 : Matrix Kd Kd ℂ) ⊗ₖ F) * S) (ab, h) (cd, h')
      = (((Matrix.single ab.1 ab.2 (1 : ℂ)
            ⊗ₖ (1 : Matrix Ed Ed ℂ)) * V')ᴴ
          * ((1 : Matrix Kd Kd ℂ) ⊗ₖ F)
          * ((Matrix.single cd.1 cd.2 (1 : ℂ)
            ⊗ₖ (1 : Matrix Ed Ed ℂ)) * V')) h h' := by
    intro ab cd h h'
    rfl
  have hSMS : Sᴴ * ((1 : Matrix Kd Kd ℂ) ⊗ₖ F) * S = 0 := by
    ext ⟨ab, h⟩ ⟨cd, h'⟩
    rw [key ab cd h h', block_pairing V' F ab.1 ab.2 cd.1 cd.2,
      hzero]
    simp
  have h1 : Sᴴ * ((1 : Matrix Kd Kd ℂ) ⊗ₖ F) = 0 := by
    refine eq_of_mul_stack_eq _ 0 S ?_ hmin
    rw [Matrix.zero_mul]
    exact hSMS
  have h2 : ((1 : Matrix Kd Kd ℂ) ⊗ₖ F) * S = 0 := by
    have h3 := congrArg Matrix.conjTranspose h1
    rw [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] at h3
    rw [conjTranspose_kronecker, Matrix.conjTranspose_one,
      show Fᴴ = F from hFh] at h3
    exact h3
  have h4 : ((1 : Matrix Kd Kd ℂ) ⊗ₖ F) = 0 := by
    refine eq_of_mul_stack_eq _ 0 S ?_ hmin
    rw [Matrix.zero_mul]
    exact h2
  ext e e'
  obtain ⟨a⟩ := ‹Nonempty Kd›
  have h5 := congrFun (congrFun h4 (a, e)) (a, e')
  simpa [Matrix.kroneckerMap_apply, Matrix.one_apply] using h5

end NCG
