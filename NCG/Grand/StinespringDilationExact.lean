/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.RelEntropyInvarianceExact
import NCG.Grand.PetzSufficiencyExact

/-!
# The Stinespring column dilation and the partial-trace reduction

Step (D5) of the finite Uhlmann-monotonicity programme for
`thm:accepted-Petz-sufficiency`: every Kraus channel is an environment
partial trace of an isometry conjugation, so data processing for arbitrary
finite CPTP maps reduces — through the proved isometry invariance — to
data processing for the environment partial trace alone.

* `stineCol`: the stacked Kraus column `V : (κ × m) × n`, an isometry
  exactly when the family is trace preserving;
* `envTrace`: the partial trace over the environment index;
* `envTrace_stineConj`: `Tr_env(V ρ V^*) = Φ_*(ρ)` — the Stinespring
  factorization of the channel;
* `relEntropy_kraus_le_of_envTrace_le`: **the reduction** — monotonicity
  of the relative entropy under the environment partial trace at the
  dilated pair implies monotonicity under the channel.
-/

open Matrix Finset
open scoped ComplexOrder

namespace NCG
namespace Petz

open NCG.QRE

variable {n m κ : Type*} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m] [Fintype κ] [DecidableEq κ]

/-- The stacked Kraus column. -/
def stineCol (K : κ → Matrix m n ℂ) : Matrix (κ × m) n ℂ :=
  Matrix.of fun p j => K p.1 p.2 j

omit [Fintype n] [DecidableEq m] [DecidableEq κ] in
/-- Trace preservation makes the Kraus column an isometry. -/
theorem stineCol_isometry (K : κ → Matrix m n ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
    (stineCol K)ᴴ * stineCol K = 1 := by
  have hrhs := hK
  ext a b
  have h := congrArg (fun M : Matrix n n ℂ => M a b) hrhs
  simp only [Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply] at h
  rw [Matrix.mul_apply]
  rw [show (1 : Matrix n n ℂ) a b = ∑ i, ∑ c, star (K i c a) * K i c b
    from h.symm]
  rw [Fintype.sum_prod_type]
  rfl

/-- The Stinespring conjugation `ρ ↦ V ρ V^*`. -/
def stineConj (K : κ → Matrix m n ℂ) (ρ : Matrix n n ℂ) :
    Matrix (κ × m) (κ × m) ℂ :=
  stineCol K * ρ * (stineCol K)ᴴ

omit [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype κ] [DecidableEq κ] in
theorem stineConj_isHermitian (K : κ → Matrix m n ℂ) {ρ : Matrix n n ℂ}
    (hρ : ρ.IsHermitian) : (stineConj K ρ).IsHermitian := by
  unfold stineConj Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hρ.eq, Matrix.mul_assoc]

/-- The partial trace over the environment index. -/
def envTrace (X : Matrix (κ × m) (κ × m) ℂ) : Matrix m m ℂ :=
  Matrix.of fun a b => ∑ i, X (i, a) (i, b)

omit [DecidableEq n] [Fintype m] [DecidableEq m] [DecidableEq κ] in
theorem envTrace_isHermitian {X : Matrix (κ × m) (κ × m) ℂ}
    (hX : X.IsHermitian) : (envTrace X).IsHermitian := by
  unfold envTrace Matrix.IsHermitian
  ext a b
  rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply,
    star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Matrix.conjTranspose_apply, hX.eq]

omit [DecidableEq n] [DecidableEq m] [DecidableEq κ] in
/-- The partial trace preserves the full trace. -/
theorem envTrace_trace (X : Matrix (κ × m) (κ × m) ℂ) :
    (envTrace X).trace = X.trace := by
  simp only [envTrace, Matrix.trace, Matrix.diag, Matrix.of_apply]
  rw [Finset.sum_comm]
  exact (Fintype.sum_prod_type (f := fun p : κ × m => X p p)).symm

omit [DecidableEq n] [Fintype m] [DecidableEq m] [DecidableEq κ] in
/-- **Stinespring factorization**: `Tr_env(V ρ V^*) = Φ_*(ρ)`. -/
theorem envTrace_stineConj (K : κ → Matrix m n ℂ) (ρ : Matrix n n ℂ) :
    envTrace (stineConj K ρ) = kraus K ρ := by
  ext a b
  simp only [envTrace, stineConj, stineCol, kraus, Matrix.of_apply,
    Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- **The partial-trace reduction of data processing**: monotonicity of the
relative entropy under the environment partial trace at the dilated pair
implies monotonicity under the channel. -/
theorem relEntropy_kraus_le_of_envTrace_le (K : κ → Matrix m n ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1)
    {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hbρ : (kraus K ρ).IsHermitian) (hbσ : (kraus K σ).IsHermitian)
    (hmono : ∀ (hX : (envTrace (stineConj K ρ)).IsHermitian)
      (hY : (envTrace (stineConj K σ)).IsHermitian),
      relEntropy hX hY ≤
        relEntropy (stineConj_isHermitian K hρ)
          (stineConj_isHermitian K hσ)) :
    relEntropy hbρ hbσ ≤ relEntropy hρ hσ := by
  have hXh : (envTrace (stineConj K ρ)).IsHermitian :=
    envTrace_isHermitian (stineConj_isHermitian K hρ)
  have hYh : (envTrace (stineConj K σ)).IsHermitian :=
    envTrace_isHermitian (stineConj_isHermitian K hσ)
  have h1 := hmono hXh hYh
  have h2 : relEntropy (stineConj_isHermitian K hρ)
      (stineConj_isHermitian K hσ) = relEntropy hρ hσ :=
    relEntropy_isometry hρ hσ (stineCol_isometry K hK) _ _
  have h3 : relEntropy hXh hYh = relEntropy hbρ hbσ :=
    relEntropy_congr (envTrace_stineConj K ρ) (envTrace_stineConj K σ)
      hXh hYh hbρ hbσ
  rw [h2, h3] at h1
  exact h1

end Petz
end NCG
