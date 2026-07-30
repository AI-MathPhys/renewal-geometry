/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Algebra.CliffordConcrete

/-!
# The canonical external Lüders direction instrument

The instrument packaging of `thm:octahedral-record` (flagship): on
the concrete external Clifford factor of
`NCG/Algebra/CliffordConcrete.lean`, the six spectral projections
`P_{i,±} = (1 ± Γᵢ)/2` of the three spatial generators form a
trace-preserving resolved Lüders instrument:

* `dirProj` — the direction projections; `dirProj_idem`,
  `dirProj_herm`, `dirProj_pair` — each is a Hermitian idempotent
  and each axis pair resolves the identity;
* `dirProj_sum_third` — the POVM normalization
  `∑_{i,±} P_{i,±}/3 = 1`;
* `lueders_kraus_sum` — the Kraus normalization
  `∑_{i,±} K_{i,±}ᴴ K_{i,±} = 1` for `K_{i,±} = P_{i,±}/√3`, i.e.
  the instrument `ρ ↦ K ρ Kᴴ` is trace preserving.

The exact state-independent second moment `I₃/3` of the associated
direction labels `±eᵢ` is the proved cross-polytope tight-frame
identity `NCG.crossPolytope_second_moment`
(`NCG/Dimension/TightFrame.lean`); together these are the finite
resolved-record content of `thm:octahedral-record`.
-/

namespace NCG.CommonOrigin

open Matrix

/-- The spatial direction projections `P_{i,±} = (1 ± Γ_{i+1})/2` on
the concrete external Clifford factor (index `0` of `gamma` is the
temporal generator). -/
noncomputable def dirProj (i : Fin 3) :
    Bool → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ
  | true => (2:ℂ)⁻¹ • (1 + gamma i.succ)
  | false => (2:ℂ)⁻¹ • (1 - gamma i.succ)

/-- Half of one-plus-involution is idempotent. -/
theorem half_one_add_involution_idem
    {n : Type*} [Fintype n] [DecidableEq n]
    (g : Matrix n n ℂ) (hg : g * g = 1) :
    ((2:ℂ)⁻¹ • (1 + g)) * ((2:ℂ)⁻¹ • (1 + g))
      = (2:ℂ)⁻¹ • (1 + g) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
    Matrix.mul_one, hg]
  module

/-- Half of one-minus-involution is idempotent. -/
theorem half_one_sub_involution_idem
    {n : Type*} [Fintype n] [DecidableEq n]
    (g : Matrix n n ℂ) (hg : g * g = 1) :
    ((2:ℂ)⁻¹ • (1 - g)) * ((2:ℂ)⁻¹ • (1 - g))
      = (2:ℂ)⁻¹ • (1 - g) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, hg]
  module

/-- Each direction projection is idempotent. -/
theorem dirProj_idem (i : Fin 3) (s : Bool) :
    dirProj i s * dirProj i s = dirProj i s := by
  cases s
  · exact half_one_sub_involution_idem _ (gamma_sq _)
  · exact half_one_add_involution_idem _ (gamma_sq _)

/-- Each direction projection is Hermitian. -/
theorem dirProj_herm (i : Fin 3) (s : Bool) :
    (dirProj i s)ᴴ = dirProj i s := by
  cases s <;>
    simp [dirProj, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, gamma_herm, star_inv₀]

/-- Each axis pair resolves the identity:
`P_{i,+} + P_{i,-} = 1`. -/
theorem dirProj_pair (i : Fin 3) :
    dirProj i true + dirProj i false = 1 := by
  change (2:ℂ)⁻¹ • (1 + gamma i.succ)
      + (2:ℂ)⁻¹ • (1 - gamma i.succ) = 1
  module

/-- **POVM normalization** (`thm:octahedral-record`): the six
direction effects `E_{i,±} = P_{i,±}/3` sum to the identity. -/
theorem dirProj_sum_third :
    (∑ i : Fin 3, ∑ s : Bool, (3:ℂ)⁻¹ • dirProj i s) = 1 := by
  have hpair : ∀ i : Fin 3,
      (∑ s : Bool, (3:ℂ)⁻¹ • dirProj i s) = (3:ℂ)⁻¹ • 1 := by
    intro i
    rw [Fintype.sum_bool, ← smul_add, dirProj_pair]
  simp only [hpair]
  rw [Fin.sum_univ_three]
  module

/-- **Kraus normalization** (`thm:octahedral-record`): the Kraus
operators `K_{i,±} = P_{i,±}/√3` of the resolved Lüders instrument
satisfy `∑ K_{i,±}ᴴ K_{i,±} = 1`, so the instrument is trace
preserving. -/
theorem lueders_kraus_sum :
    (∑ i : Fin 3, ∑ s : Bool,
        (((Real.sqrt 3 : ℝ) : ℂ)⁻¹ • dirProj i s)ᴴ
          * (((Real.sqrt 3 : ℝ) : ℂ)⁻¹ • dirProj i s)) = 1 := by
  have hterm : ∀ (i : Fin 3) (s : Bool),
      (((Real.sqrt 3 : ℝ) : ℂ)⁻¹ • dirProj i s)ᴴ
        * (((Real.sqrt 3 : ℝ) : ℂ)⁻¹ • dirProj i s)
      = (3:ℂ)⁻¹ • dirProj i s := by
    intro i s
    rw [Matrix.conjTranspose_smul, dirProj_herm,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, dirProj_idem]
    congr 1
    have hstar : star ((Real.sqrt 3 : ℝ) : ℂ)
        = ((Real.sqrt 3 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_ofReal]
    rw [star_inv₀, hstar, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    norm_num
  simp only [hterm]
  exact dirProj_sum_third

end NCG.CommonOrigin
