/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Matter.SMEasyV5

/-!
# Stinespring support intertwining
  (`cor:stinespring-intertwining`, SM manuscript)

If a completely positive channel `𝒯(ρ) = Σ_α K_α ρ K_α†` preserves
every central support of the orthogonal resolution `Σ_s P_s = 1`,
then by the positive Kraus-block no-go (`kraus_block_identity` +
`kraus_block_nogo`) all cross blocks `P_t K_α P_s` (`s ≠ t`)
vanish, so every Kraus operator commutes with every support
(`support_commute`), and the Stinespring isometry
`Vψ = Σ_α K_αψ ⊗ |α⟩` — realized as the block-column matrix
`stineV K : Matrix (d × E) d ℂ` — satisfies the boxed intertwining

  `(P_s ⊗ I_E) V = V P_s`

(`stinespring_intertwining`).  Environment measurements and unitary
rotations of the Kraus frame act by linear combinations of the same
block-diagonal operators, hence remain support preserving: the
final conjunct shows every combination `Σ_α c_α K_α` commutes with
every support (interpretive reading disclosed in the ledger).
-/

open Matrix

namespace NCG

variable {d E S : Type*} [Fintype d] [DecidableEq d]
  [Fintype E] [DecidableEq E] [Fintype S]

/-- The Stinespring isometry of a Kraus family in an orthonormal
environment basis: `Vψ = Σ_α K_αψ ⊗ |α⟩` as a block-column
matrix. -/
noncomputable def stineV (K : E → Matrix d d ℂ) :
    Matrix (d × E) d ℂ :=
  Matrix.of fun p j => K p.2 p.1 j

omit [DecidableEq d] [DecidableEq E] [Fintype S] in
/-- Support preservation kills every cross block of every Kraus
operator. -/
lemma cross_block_vanish (K : E → Matrix d d ℂ)
    (P : S → Matrix d d ℂ)
    (hPH : ∀ s, (P s)ᴴ = P s) (hP2 : ∀ s, P s * P s = P s)
    (hpres : ∀ s t, s ≠ t →
      P t * (∑ α, K α * P s * (K α)ᴴ) * P t = 0) :
    ∀ s t, s ≠ t → ∀ α, P t * K α * P s = 0 := by
  intro s t hst α
  refine kraus_block_nogo (fun α => P t * K α * P s) ?_ α
  rw [← kraus_block_identity K (P s) (P t) (hPH s) (hP2 s) (hPH t)]
  exact hpres s t hst

omit [Fintype E] [DecidableEq E] in
/-- Block-diagonal Kraus operators commute with every support. -/
lemma support_commute (K : E → Matrix d d ℂ)
    (P : S → Matrix d d ℂ)
    (hres : ∑ s, P s = 1)
    (hcross : ∀ s t, s ≠ t → ∀ α, P t * K α * P s = 0) :
    ∀ α s, P s * K α = K α * P s := by
  intro α s
  have h1 : P s * K α = P s * K α * P s := by
    calc P s * K α = P s * K α * 1 := (Matrix.mul_one _).symm
      _ = ∑ t, P s * K α * P t := by
          rw [← hres, Finset.mul_sum]
      _ = P s * K α * P s := by
          refine Finset.sum_eq_single s (fun t _ hts => ?_)
            (fun h => absurd (Finset.mem_univ s) h)
          exact hcross t s hts α
  have h2 : K α * P s = P s * K α * P s := by
    calc K α * P s = 1 * (K α * P s) := (Matrix.one_mul _).symm
      _ = ∑ t, P t * (K α * P s) := by
          rw [← hres, Finset.sum_mul]
      _ = P s * (K α * P s) := by
          refine Finset.sum_eq_single s (fun t _ hts => ?_)
            (fun h => absurd (Finset.mem_univ s) h)
          rw [← Matrix.mul_assoc]
          exact hcross s t (Ne.symm hts) α
      _ = P s * K α * P s := by rw [Matrix.mul_assoc]
  rw [h1, h2]

omit [DecidableEq d] in
/-- Left multiplication by `P ⊗ I_E` acts on the Stinespring
column by compressing every Kraus operator on the left. -/
lemma kron_mul_stineV (Q : Matrix d d ℂ) (K : E → Matrix d d ℂ) :
    Matrix.kroneckerMap (· * ·) Q (1 : Matrix E E ℂ) * stineV K
      = stineV (fun α => Q * K α) := by
  ext p j
  rw [Matrix.mul_apply]
  rw [Fintype.sum_prod_type]
  simp only [stineV, Matrix.kroneckerMap_apply, Matrix.of_apply,
    Matrix.one_apply]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single p.2 (fun γ _ hγ => by
    simp [Ne.symm hγ]) (fun h => absurd (Finset.mem_univ p.2) h)]
  simp [Matrix.mul_apply]

omit [DecidableEq d] [Fintype E] [DecidableEq E] in
/-- Right multiplication acts on the Stinespring column by
compressing every Kraus operator on the right. -/
lemma stineV_mul (K : E → Matrix d d ℂ) (Q : Matrix d d ℂ) :
    stineV K * Q = stineV (fun α => K α * Q) := by
  ext p j
  simp [stineV, Matrix.mul_apply]

/-- `cor:stinespring-intertwining`: for a support-preserving
channel, the Stinespring isometry intertwines every central
support, `(P_s ⊗ I_E)V = VP_s`, and every linear combination of
the Kraus frame (environment measurements, unitary frame
rotations) commutes with every support. -/
theorem stinespring_intertwining (K : E → Matrix d d ℂ)
    (P : S → Matrix d d ℂ)
    (hPH : ∀ s, (P s)ᴴ = P s) (hP2 : ∀ s, P s * P s = P s)
    (_horth : ∀ s t, s ≠ t → P s * P t = 0)
    (hres : ∑ s, P s = 1)
    (hpres : ∀ s t, s ≠ t →
      P t * (∑ α, K α * P s * (K α)ᴴ) * P t = 0) :
    ∀ s, (Matrix.kroneckerMap (· * ·) (P s) (1 : Matrix E E ℂ)
        * stineV K = stineV K * P s)
      ∧ ∀ c : E → ℂ, P s * (∑ α, c α • K α)
          = (∑ α, c α • K α) * P s := by
  have hcross := cross_block_vanish K P hPH hP2 hpres
  have hcomm := support_commute K P hres hcross
  intro s
  constructor
  · rw [kron_mul_stineV, stineV_mul]
    congr 1
    funext α
    exact hcomm α s
  · intro c
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, hcomm α s]

end NCG
