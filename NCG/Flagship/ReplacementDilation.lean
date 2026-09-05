/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.ChronologyLeakage

/-!
# Minimal replacement dilation and past–fresh split
  (`thm:replacement-dilation-master`, flagship manuscript)

With a purification `|Ω_ω⟩ ∈ ℋ₊ ⊗ ℰ_ω` of `ω` and a unitary
`J : ℋ₋ → ℰ_mem`, the boxed map `V_rep|ψ⟩ = |Ω_ω⟩ ⊗ J|ψ⟩`
(`repVec`) satisfies:

* it is an isometry (`replacement_isometry`);
* it dilates the replacement channel: for every system effect `X`
  lifted as `X ⊗ I_{ℰ_ω} ⊗ I_{ℰ_mem}`, the matrix elements are
  `⟨V ψ, (X⊗I⊗I) V φ⟩ = Tr(ωX)·⟨ψ, φ⟩`
  (`replacement_channel`) — the weak form of
  `Tr_env(VρV*) = Tr(ρ)ω`;
* the boxed reference-system identity: for every reference system
  `R`, `(I_R ⊗ V_rep)|Ψ⟩` equals `(I_R ⊗ J)|Ψ⟩ ⊗ |Ω_ω⟩` up to the
  index reshuffle `(x,((a,e),k)) ↦ ((x,k),(a,e))`
  (`replacement_reference_split`, stated pointwise): the past is
  transferred to one memory factor while a fixed fresh factor is
  prepared.

The environment index is `ℰ_ω × ℰ_mem ≅ r × dim ℋ₋` by
construction; minimality (environment dimension equals the Choi
rank `r·dim ℋ₋` of the replacement channel) is the standard
Choi-rank criterion, cited as interface (disclosed).  Vectors are
plain finite tuples with the sesquilinear `star ⬝ᵥ` pairing.
-/

open Matrix Kronecker

namespace NCG

variable {n m r R : Type*} [Fintype n] [Fintype m] [Fintype r]
  [Fintype R] [DecidableEq n] [DecidableEq r]

/-- The boxed replacement isometry `V_rep ψ = Ω_ω ⊗ Jψ` (the
memory unitary `J` given as a matrix `U`). -/
noncomputable def repVec (Ω : m × r → ℂ) (U : Matrix n n ℂ)
    (ψ : n → ℂ) : (m × r) × n → ℂ :=
  kronVec Ω (U *ᵥ ψ)

/-- Unitaries preserve the sesquilinear pairing. -/
lemma unitary_dot (U : Matrix n n ℂ) (hU : Uᴴ * U = 1)
    (ψ φ : n → ℂ) :
    star (U *ᵥ ψ) ⬝ᵥ (U *ᵥ φ) = star ψ ⬝ᵥ φ := by
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, hU, Matrix.vecMul_one]

omit [DecidableEq r] in
/-- `V_rep` is an isometry. -/
theorem replacement_isometry (Ω : m × r → ℂ)
    (hΩ : star Ω ⬝ᵥ Ω = 1) (U : Matrix n n ℂ) (hU : Uᴴ * U = 1)
    (ψ φ : n → ℂ) :
    star (repVec Ω U ψ) ⬝ᵥ repVec Ω U φ = star ψ ⬝ᵥ φ := by
  rw [repVec, repVec, star_kronVec_dotProduct, hΩ, one_mul,
    unitary_dot U hU]

/-- `V_rep` dilates the replacement channel: matrix elements of
lifted system effects are `Tr(ωX)·⟨ψ,φ⟩`. -/
theorem replacement_channel (Ω : m × r → ℂ) (ω : Matrix m m ℂ)
    (hpur : ∀ X : Matrix m m ℂ,
      star Ω ⬝ᵥ ((X ⊗ₖ (1 : Matrix r r ℂ)) *ᵥ Ω)
        = (ω * X).trace)
    (U : Matrix n n ℂ) (hU : Uᴴ * U = 1)
    (X : Matrix m m ℂ) (ψ φ : n → ℂ) :
    star (repVec Ω U ψ) ⬝ᵥ
        (((X ⊗ₖ (1 : Matrix r r ℂ)) ⊗ₖ (1 : Matrix n n ℂ))
          *ᵥ repVec Ω U φ)
      = (ω * X).trace * (star ψ ⬝ᵥ φ) := by
  rw [repVec, repVec, mulVec_kronVec, Matrix.one_mulVec,
    star_kronVec_dotProduct, hpur, unitary_dot U hU]

omit [Fintype m] [Fintype r] [Fintype R] [DecidableEq n]
  [DecidableEq r] in
/-- Boxed reference-system identity, pointwise: under the index
reshuffle `(x,((a,e),k)) ↦ ((x,k),(a,e))`, the extended isometry
`(I_R ⊗ V_rep)|Ψ⟩` is `(I_R ⊗ J)|Ψ⟩ ⊗ |Ω_ω⟩`. -/
theorem replacement_reference_split (Ω : m × r → ℂ)
    (U : Matrix n n ℂ) (Ψ : R × n → ℂ) (x : R) (p : m × r)
    (k : n) :
    repVec Ω U (fun k' => Ψ (x, k')) (p, k)
      = (U *ᵥ fun k' => Ψ (x, k')) k * Ω p := by
  simp [repVec, kronVec, mul_comm]

end NCG
