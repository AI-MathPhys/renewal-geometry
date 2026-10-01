/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.PalatiniDeterminantVolumeExact

/-!
# Pointwise Palatini–Holst–volume coframe variations and the Einstein insertion
  (algebraic core of `eq:supp-einstein-insertion` in `thm:supp-renewal-palatini`;
  emergent-spacetime manuscript, supplement)

All objects are the component densities of the paper's four-forms
(`eq:main-phv-densities`) at one point of a four-dimensional chart, in the convention
`R^{KL} = ½ R^{KL}_{ρσ} dx^ρ ∧ dx^σ`, `d⁴x = dx⁰ ∧ dx¹ ∧ dx² ∧ dx³`:

* `eps4` — the permutation (Levi-Civita) symbol in four indices;
* `palatiniDensity e R` — the coefficient of `d⁴x` in `½ ε_{IJKL} e^I ∧ e^J ∧ R^{KL}`,
  i.e. `¼ ε_{IJKL} ε^{μνρσ} e^I_μ e^J_ν R^{KL}_{ρσ}`;
* `holstDensity η e R` — the coefficient of `d⁴x` in `e^I ∧ e^J ∧ R_{IJ}`
  (`R_{IJ} = η_{IK} η_{JL} R^{KL}`), i.e. `½ ε^{μνρσ} e^I_μ e^J_ν R_{IJρσ}`;
* `volumeDensity e` — the coefficient of `d⁴x` in `(1/4!) ε_{IJKL} e^I ∧ e^J ∧ e^K ∧ e^L`,
  which equals `det e` (`volumeDensity_eq_det`).

Main results (pure finite algebra, every statement exact):

* `sum_eps_mul_entries`: `ε_{IJKL} M^I_a M^J_b M^K_c M^L_d = det M · ε_{abcd}`;
* `hasDerivAt_palatiniDensity`, `hasDerivAt_holstDensity`, `hasDerivAt_volumeDensity`: the
  coframe first variations (curvature `R^{KL}_{ρσ}` held fixed, as in the Palatini
  first-order formalism) are the derivatives along `e + t δe`;
* `holstVariation_eq_zero_of_bianchi`: **the first Bianchi identity removes the Holst
  coframe variation**: if `R^{KL}` is antisymmetric and the algebraic first Bianchi identity
  `(R^I{}_J ∧ e^J)_{νρσ} = 0` holds, the Holst variation vanishes for every coframe
  variation `δe = e H` (every variation when `e` is invertible);
* `palatiniVariation_mul_eq`: for `R^{KL}_{ρσ} = e^K_α e^L_β 𝓡^{αβ}_{ρσ}` with `𝓡`
  antisymmetric in both pairs, `δ_{eH} L_P = det e (tr H · S - 2 tr(H · Ric))`,
  `Ric^μ_γ = 𝓡^{μσ}_{γσ}`, `S = Ric^μ_μ`;
* `classifiedVariation_metricTest_eq`: **Einstein insertion.**  For the inverse-metric test
  lift `δe = -½ e (k g)` (`g = eᵀ η e`, `δ g^{μν} = k^{μν}`), the classified coframe variation
  `α δL_H + β δL_P + λ δL_vol` equals `det e · k^{γβ}(β G_{βγ} - (λ/2) g_{βγ})` on the
  torsion-free (Bianchi) branch, with `G_{βγ} = g_{βμ}(Ric^μ_γ - ½ δ^μ_γ S)` the Einstein
  tensor of the coordinate curvature `𝓡`; for `β ≠ 0` this is
  `β · det e · k^{γβ}(G + Λ g)_{βγ}` with `Λ = -λ/(2β)` (`classifiedVariation_einstein`), and
  `det e = √(-det g)` for an oriented coframe and `det η = -1` (`sqrt_neg_det_metric`).
-/

open Finset

noncomputable section

namespace RenewalGeometry.PalatiniEinsteinAlgebra

/-! ### The permutation symbol -/

/-- The four-index permutation symbol `ε_{abcd}` (`0` on repeated indices, the sign of the
permutation otherwise), by the product formula `∏_{i<j} sign(a_j - a_i)`. -/
def eps4 (a b c d : Fin 4) : ℤ :=
  Int.sign ((b : ℤ) - a) * Int.sign ((c : ℤ) - a) * Int.sign ((d : ℤ) - a) *
    Int.sign ((c : ℤ) - b) * Int.sign ((d : ℤ) - b) * Int.sign ((d : ℤ) - c)

/-- Integer Kronecker delta on `Fin 4`. -/
def kdz (a b : Fin 4) : ℤ := if a = b then 1 else 0

set_option maxRecDepth 100000 in
/-- Single contraction of two permutation symbols: the generalized Kronecker delta
`ε_{ν m r s} ε_{ν g a b} = δ^{mrs}_{gab}` (a `3 × 3` determinant of deltas). -/
theorem eps4_contract_one : ∀ m r s g a b : Fin 4,
    (∑ n : Fin 4, eps4 n m r s * eps4 n g a b) =
      kdz m g * (kdz r a * kdz s b - kdz r b * kdz s a)
      - kdz m a * (kdz r g * kdz s b - kdz r b * kdz s g)
      + kdz m b * (kdz r g * kdz s a - kdz r a * kdz s g) := by
  decide

set_option maxRecDepth 100000 in
/-- Triple contraction: `ε_{m n r s} ε_{g n r s} = 6 δ_{mg}`. -/
theorem eps4_contract_three : ∀ m g : Fin 4,
    (∑ n : Fin 4, ∑ r : Fin 4, ∑ s : Fin 4, eps4 m n r s * eps4 g n r s) = 6 * kdz m g := by
  decide

set_option maxRecDepth 100000 in
theorem eps4_swap01 : ∀ a b c d : Fin 4, eps4 b a c d = -eps4 a b c d := by decide

set_option maxRecDepth 100000 in
theorem eps4_cyclic123 : ∀ a b c d : Fin 4, eps4 a c d b = eps4 a b c d := by decide

/-- The permutation symbol as a real number. -/
abbrev epsR (a b c d : Fin 4) : ℝ := (eps4 a b c d : ℝ)

theorem epsR_contract_one (m r s g a b : Fin 4) :
    (∑ n : Fin 4, epsR n m r s * epsR n g a b) =
      ((kdz m g * (kdz r a * kdz s b - kdz r b * kdz s a)
      - kdz m a * (kdz r g * kdz s b - kdz r b * kdz s g)
      + kdz m b * (kdz r g * kdz s a - kdz r a * kdz s g) : ℤ) : ℝ) := by
  rw [← eps4_contract_one]; push_cast; rfl

theorem epsR_swap01 (a b c d : Fin 4) : epsR b a c d = -epsR a b c d := by
  rw [epsR, epsR, eps4_swap01, Int.cast_neg]

theorem epsR_cyclic123 (a b c d : Fin 4) : epsR a c d b = epsR a b c d := by
  rw [epsR, epsR, eps4_cyclic123]

/-! ### Determinants and the permutation symbol -/

/-- Leibniz formula with the permutation symbol: `det X = ε_{IJKL} X_{0I} X_{1J} X_{2K} X_{3L}`. -/
theorem det_eq_sum_eps (X : Matrix (Fin 4) (Fin 4) ℝ) :
    X.det = ∑ I, ∑ J, ∑ K, ∑ L, epsR I J K L * X 0 I * X 1 J * X 2 K * X 3 L := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply]
  have h2 : Int.sign 2 = 1 := rfl
  have h3 : Int.sign 3 = 1 := rfl
  simp [epsR, eps4, Fin.succAbove, Fin.lt_def, h2, h3]
  ring

/-- `ε_{IJKL} M^I_a M^J_b M^K_c M^L_d = det M · ε_{abcd}`. -/
theorem sum_eps_mul_entries (M : Matrix (Fin 4) (Fin 4) ℝ) (a b c d : Fin 4) :
    ∑ I, ∑ J, ∑ K, ∑ L, epsR I J K L * M I a * M J b * M K c * M L d =
      M.det * epsR a b c d := by
  set idx : Fin 4 → Fin 4 := ![a, b, c, d]
  set S : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun r q => if q = idx r then 1 else 0
  have hN : (Matrix.of fun r I => M I (idx r)) = S * M.transpose := by
    ext r I
    simp [S, Matrix.mul_apply]
  have hS : S.det = epsR a b c d := by
    rw [det_eq_sum_eps]
    simp only [S, idx, Matrix.of_apply]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp
  have hdet : (Matrix.of fun r I => M I (idx r)).det = epsR a b c d * M.det := by
    rw [hN, Matrix.det_mul, Matrix.det_transpose, hS]
  rw [det_eq_sum_eps] at hdet
  rw [mul_comm]
  simpa [idx] using hdet

/-! ### Reordering finite sums -/

section Reorder

variable {f3 : Fin 4 → Fin 4 → Fin 4 → ℝ} {f4 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ}

theorem sum_swap_inner (f : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ a, ∑ c, ∑ b, f a b c :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- Move the outermost index of a quadruple sum to the innermost position. -/
theorem sum_move_in3 (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ∑ n, ∑ a, ∑ b, ∑ c, f n a b c = ∑ a, ∑ b, ∑ c, ∑ n, f n a b c := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]

/-- Move the innermost index of a quadruple sum to the outermost position. -/
theorem sum_move_out3 (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ n, f n a b c = ∑ n, ∑ a, ∑ b, ∑ c, f n a b c :=
  (sum_move_in3 f).symm

end Reorder

/-! ### Multilinear forms built from the permutation symbol -/

/-- The internal volume form `ε_{IJKL} u^I v^J w^K z^L`. -/
def vol4 (u v w z : Fin 4 → ℝ) : ℝ :=
  ∑ I, ∑ J, ∑ K, ∑ L, epsR I J K L * u I * v J * w K * z L

/-- The internal Palatini contraction `ε_{IJKL} u^I v^J Q^{KL}` of two internal vectors with an
internal bivector `Q`. -/
def pal4 (u v : Fin 4 → ℝ) (Q : Fin 4 → Fin 4 → ℝ) : ℝ :=
  ∑ I, ∑ J, ∑ K, ∑ L, epsR I J K L * u I * v J * Q K L

theorem vol4_cols (M : Matrix (Fin 4) (Fin 4) ℝ) (a b c d : Fin 4) :
    vol4 (fun I => M I a) (fun I => M I b) (fun I => M I c) (fun I => M I d) =
      M.det * epsR a b c d :=
  sum_eps_mul_entries M a b c d

theorem vol4_eq_sum_left (u v w z : Fin 4 → ℝ) :
    vol4 u v w z = ∑ I, u I * ∑ J, ∑ K, ∑ L, epsR I J K L * v J * w K * z L := by
  unfold vol4
  refine Finset.sum_congr rfl fun I _ => ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun K _ =>
    Finset.sum_congr rfl fun L _ => ?_
  ring

theorem vol4_eq_sum_second (u v w z : Fin 4 → ℝ) :
    vol4 u v w z = ∑ J, v J * ∑ I, ∑ K, ∑ L, epsR I J K L * u I * w K * z L := by
  unfold vol4
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun J _ => ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun K _ =>
    Finset.sum_congr rfl fun L _ => ?_
  ring

/-- Pull a finite linear combination out of a contraction with a fixed covector. -/
theorem sum_lin_aux (c : Fin 4 → ℝ) (x : Fin 4 → Fin 4 → ℝ) (A : Fin 4 → ℝ) :
    ∑ I, (∑ g, c g * x g I) * A I = ∑ g, c g * ∑ I, x g I * A I := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun I _ => ?_
  ring

/-- Linearity of `vol4` in its first slot along a finite combination. -/
theorem vol4_sum_left (c : Fin 4 → ℝ) (x : Fin 4 → Fin 4 → ℝ) (v w z : Fin 4 → ℝ) :
    vol4 (fun I => ∑ g, c g * x g I) v w z = ∑ g, c g * vol4 (x g) v w z := by
  simp only [vol4_eq_sum_left]
  exact sum_lin_aux c x _

/-- Linearity of `vol4` in its second slot along a finite combination. -/
theorem vol4_sum_second (c : Fin 4 → ℝ) (x : Fin 4 → Fin 4 → ℝ) (u w z : Fin 4 → ℝ) :
    vol4 u (fun J => ∑ g, c g * x g J) w z = ∑ g, c g * vol4 u (x g) w z := by
  simp only [vol4_eq_sum_second]
  exact sum_lin_aux c x _

/-- Swap two pairs of summation indices. -/
theorem sum_block_swap (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem pal4_eq (u v : Fin 4 → ℝ) (Q : Fin 4 → Fin 4 → ℝ) :
    pal4 u v Q = ∑ K, ∑ L, Q K L * ∑ I, ∑ J, epsR I J K L * u I * v J := by
  unfold pal4
  rw [sum_block_swap (fun I J K L => epsR I J K L * u I * v J * Q K L)]
  refine Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun L _ => ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ => ?_
  ring

theorem vol4_eq_sum34 (u v w z : Fin 4 → ℝ) :
    vol4 u v w z = ∑ K, ∑ L, w K * z L * ∑ I, ∑ J, epsR I J K L * u I * v J := by
  unfold vol4
  rw [sum_block_swap (fun I J K L => epsR I J K L * u I * v J * w K * z L)]
  refine Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun L _ => ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ => ?_
  ring

theorem sum_coord_aux (M : Matrix (Fin 4) (Fin 4) ℝ) (C D : Fin 4 → Fin 4 → ℝ) :
    ∑ K, ∑ L, (∑ α, ∑ β, M K α * M L β * C α β) * D K L =
      ∑ α, ∑ β, C α β * ∑ K, ∑ L, M K α * M L β * D K L := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [sum_block_swap (fun K L α β => M K α * M L β * C α β * D K L)]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  refine Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun L _ => ?_
  ring

/-- Substituting `Q^{KL} = M^K_α M^L_β C^{αβ}` in the Palatini contraction. -/
theorem pal4_of_coord (u v : Fin 4 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (C : Fin 4 → Fin 4 → ℝ) :
    pal4 u v (fun K L => ∑ α, ∑ β, M K α * M L β * C α β) =
      ∑ α, ∑ β, C α β * vol4 u v (fun K => M K α) (fun L => M L β) := by
  rw [pal4_eq, sum_coord_aux]
  simp only [vol4_eq_sum34]


theorem sum_move_in2 (f : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ∑ n, ∑ a, ∑ b, f n a b = ∑ a, ∑ b, ∑ n, f n a b := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

theorem sum_move_out2 (f : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ∑ a, ∑ b, ∑ n, f n a b = ∑ n, ∑ a, ∑ b, f n a b :=
  (sum_move_in2 f).symm

/-! ### The three densities and their coframe first variations -/

/-- Coefficient of `d⁴x` in the Palatini density `½ ε_{IJKL} e^I ∧ e^J ∧ R^{KL}`
(`eq:main-phv-densities`): `¼ ε^{μνρσ} ε_{IJKL} e^I_μ e^J_ν R^{KL}_{ρσ}`.  The coframe is the
matrix `e I μ = e^I_μ`, the curvature has components `R K L ρ σ = R^{KL}_{ρσ}`. -/
def palatiniDensity (e : Matrix (Fin 4) (Fin 4) ℝ) (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ℝ :=
  (1 / 4) * ∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsR μ ν ρ σ *
    pal4 (fun I => e I μ) (fun J => e J ν) (fun K L => R K L ρ σ)

/-- The coframe first variation of the Palatini density (curvature held fixed). -/
def palatiniVariation (e δ : Matrix (Fin 4) (Fin 4) ℝ)
    (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) : ℝ :=
  (1 / 4) * ∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsR μ ν ρ σ *
    (pal4 (fun I => δ I μ) (fun J => e J ν) (fun K L => R K L ρ σ) +
      pal4 (fun I => e I μ) (fun J => δ J ν) (fun K L => R K L ρ σ))

/-- Lowering of the internal curvature indices, `R_{IJ} = η_{IK} η_{JL} R^{KL}`. -/
def lowerInternal (η : Matrix (Fin 4) (Fin 4) ℝ) (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun I J ρ σ => ∑ K, ∑ L, η I K * η J L * R K L ρ σ

/-- The contraction `u^I v^J Q_{IJ}`. -/
def hol2 (u v : Fin 4 → ℝ) (Q : Fin 4 → Fin 4 → ℝ) : ℝ := ∑ I, ∑ J, u I * v J * Q I J

/-- Coefficient of `d⁴x` in the Holst density `e^I ∧ e^J ∧ R_{IJ}` (`eq:main-phv-densities`):
`½ ε^{μνρσ} e^I_μ e^J_ν R_{IJρσ}`. -/
def holstDensity (η e : Matrix (Fin 4) (Fin 4) ℝ) (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) : ℝ :=
  (1 / 2) * ∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsR μ ν ρ σ *
    hol2 (fun I => e I μ) (fun J => e J ν) (fun I J => lowerInternal η R I J ρ σ)

/-- The coframe first variation of the Holst density (curvature held fixed). -/
def holstVariation (η e δ : Matrix (Fin 4) (Fin 4) ℝ)
    (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) : ℝ :=
  (1 / 2) * ∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsR μ ν ρ σ *
    (hol2 (fun I => δ I μ) (fun J => e J ν) (fun I J => lowerInternal η R I J ρ σ) +
      hol2 (fun I => e I μ) (fun J => δ J ν) (fun I J => lowerInternal η R I J ρ σ))

/-- Coefficient of `d⁴x` in the volume density `(1/4!) ε_{IJKL} e^I ∧ e^J ∧ e^K ∧ e^L`. -/
def volumeDensity (e : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  (1 / 24) * ∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsR μ ν ρ σ *
    vol4 (fun I => e I μ) (fun J => e J ν) (fun K => e K ρ) (fun L => e L σ)

set_option maxRecDepth 100000 in
theorem eps4_sq_sum :
    (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4, eps4 μ ν ρ σ * eps4 μ ν ρ σ) = 24 := by
  decide

/-- The volume density is the coframe determinant. -/
theorem volumeDensity_eq_det (e : Matrix (Fin 4) (Fin 4) ℝ) : volumeDensity e = e.det := by
  unfold volumeDensity
  simp only [vol4_cols]
  have h : (∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4,
      epsR μ ν ρ σ * (e.det * epsR μ ν ρ σ)) =
      e.det * ((∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4,
        eps4 μ ν ρ σ * eps4 μ ν ρ σ : ℤ) : ℝ) := by
    push_cast
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    simp only [epsR]; ring
  rw [h, eps4_sq_sum]
  push_cast
  ring

/-- Jacobi: the coframe first variation of the volume density at an invertible coframe is
`det e · tr(e⁻¹ δe)`. -/
theorem hasDerivAt_volumeDensity (e δ : Matrix (Fin 4) (Fin 4) ℝ) (hdet : e.det ≠ 0) :
    HasDerivAt (fun t : ℝ => volumeDensity (e + t • δ)) (e.det * Matrix.trace (e⁻¹ * δ)) 0 := by
  simp only [volumeDensity_eq_det]
  exact PalatiniDeterminantVolume.determinant_firstVariation_at_invertible e δ hdet

theorem hasDerivAt_quadratic (a b c : ℝ) :
    HasDerivAt (fun t : ℝ => a + t * b + t ^ 2 * c) b 0 := by
  have h1 : HasDerivAt (fun t : ℝ => t * b) (1 * b) 0 := (hasDerivAt_id 0).mul_const b
  have h2 : HasDerivAt (fun t : ℝ => t ^ 2 * c) (((2 : ℕ) * (0 : ℝ) ^ (2 - 1) * 1) * c) 0 :=
    ((hasDerivAt_id 0).pow 2).mul_const c
  exact ((h1.const_add a).add h2).congr_deriv (by simp)

theorem pal4_add_smul (u x v y : Fin 4 → ℝ) (Q : Fin 4 → Fin 4 → ℝ) (t : ℝ) :
    pal4 (fun I => u I + t * x I) (fun J => v J + t * y J) Q =
      pal4 u v Q + t * (pal4 x v Q + pal4 u y Q) + t ^ 2 * pal4 x y Q := by
  unfold pal4
  rw [mul_add]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ =>
    Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun L _ => ?_
  ring

theorem hol2_add_smul (u x v y : Fin 4 → ℝ) (Q : Fin 4 → Fin 4 → ℝ) (t : ℝ) :
    hol2 (fun I => u I + t * x I) (fun J => v J + t * y J) Q =
      hol2 u v Q + t * (hol2 x v Q + hol2 u y Q) + t ^ 2 * hol2 x y Q := by
  unfold hol2
  rw [mul_add]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ => ?_
  ring

/-- The Palatini coframe variation is the derivative along `e + t δe`. -/
theorem hasDerivAt_palatiniDensity (e δ : Matrix (Fin 4) (Fin 4) ℝ)
    (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    HasDerivAt (fun t : ℝ => palatiniDensity (e + t • δ) R) (palatiniVariation e δ R) 0 := by
  unfold palatiniDensity palatiniVariation
  refine HasDerivAt.const_mul _ ?_
  apply HasDerivAt.fun_sum; intro μ _
  apply HasDerivAt.fun_sum; intro ν _
  apply HasDerivAt.fun_sum; intro ρ _
  apply HasDerivAt.fun_sum; intro σ _
  apply HasDerivAt.const_mul
  have hfun : (fun t : ℝ => pal4 (fun I => (e + t • δ) I μ) (fun J => (e + t • δ) J ν)
      (fun K L => R K L ρ σ)) = fun t => pal4 (fun I => e I μ) (fun J => e J ν)
        (fun K L => R K L ρ σ) + t * (pal4 (fun I => δ I μ) (fun J => e J ν)
        (fun K L => R K L ρ σ) + pal4 (fun I => e I μ) (fun J => δ J ν)
        (fun K L => R K L ρ σ)) + t ^ 2 * pal4 (fun I => δ I μ) (fun J => δ J ν)
        (fun K L => R K L ρ σ) := by
    funext t
    rw [← pal4_add_smul]
    simp [Matrix.add_apply, smul_eq_mul]
  rw [hfun]
  exact hasDerivAt_quadratic _ _ _

/-- The Holst coframe variation is the derivative along `e + t δe`. -/
theorem hasDerivAt_holstDensity (η e δ : Matrix (Fin 4) (Fin 4) ℝ)
    (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    HasDerivAt (fun t : ℝ => holstDensity η (e + t • δ) R) (holstVariation η e δ R) 0 := by
  unfold holstDensity holstVariation
  refine HasDerivAt.const_mul _ ?_
  apply HasDerivAt.fun_sum; intro μ _
  apply HasDerivAt.fun_sum; intro ν _
  apply HasDerivAt.fun_sum; intro ρ _
  apply HasDerivAt.fun_sum; intro σ _
  apply HasDerivAt.const_mul
  have hfun : (fun t : ℝ => hol2 (fun I => (e + t • δ) I μ) (fun J => (e + t • δ) J ν)
      (fun I J => lowerInternal η R I J ρ σ)) = fun t => hol2 (fun I => e I μ)
        (fun J => e J ν) (fun I J => lowerInternal η R I J ρ σ) +
        t * (hol2 (fun I => δ I μ) (fun J => e J ν) (fun I J => lowerInternal η R I J ρ σ) +
          hol2 (fun I => e I μ) (fun J => δ J ν) (fun I J => lowerInternal η R I J ρ σ)) +
        t ^ 2 * hol2 (fun I => δ I μ) (fun J => δ J ν)
          (fun I J => lowerInternal η R I J ρ σ) := by
    funext t
    rw [← hol2_add_smul]
    simp [Matrix.add_apply, smul_eq_mul]
  rw [hfun]
  exact hasDerivAt_quadratic _ _ _


/-! ### The first Bianchi identity removes the Holst coframe variation -/

/-- The components `R^K{}_{Jρσ} e^J_ν` (with `R^K{}_J = R^{KL} η_{LJ}`); their cyclic sum over
`(ν, ρ, σ)` is the algebraic first-Bianchi three-form `(R^K{}_J ∧ e^J)_{νρσ}`. -/
def bianchiTerm (η e : Matrix (Fin 4) (Fin 4) ℝ) (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (K ν ρ σ : Fin 4) : ℝ :=
  ∑ L, R K L ρ σ * ∑ J, η L J * e J ν

/-- The algebraic first Bianchi identity `R^K{}_J ∧ e^J = 0` at a point. -/
def SatisfiesFirstBianchi (η e : Matrix (Fin 4) (Fin 4) ℝ)
    (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) : Prop :=
  ∀ K ν ρ σ, bianchiTerm η e R K ν ρ σ + bianchiTerm η e R K ρ σ ν +
    bianchiTerm η e R K σ ν ρ = 0

theorem hol2_eq_left (u v : Fin 4 → ℝ) (Q : Fin 4 → Fin 4 → ℝ) :
    hol2 u v Q = ∑ I, u I * ∑ J, v J * Q I J := by
  unfold hol2
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  ring

theorem hol2_eq_second (u v : Fin 4 → ℝ) (Q : Fin 4 → Fin 4 → ℝ) :
    hol2 u v Q = ∑ J, v J * ∑ I, u I * Q I J := by
  unfold hol2
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  ring

theorem hol2_sum_left (c : Fin 4 → ℝ) (x : Fin 4 → Fin 4 → ℝ) (v : Fin 4 → ℝ)
    (Q : Fin 4 → Fin 4 → ℝ) :
    hol2 (fun I => ∑ g, c g * x g I) v Q = ∑ g, c g * hol2 (x g) v Q := by
  simp only [hol2_eq_left]
  exact sum_lin_aux c x _

theorem hol2_sum_second (c : Fin 4 → ℝ) (x : Fin 4 → Fin 4 → ℝ) (u : Fin 4 → ℝ)
    (Q : Fin 4 → Fin 4 → ℝ) :
    hol2 u (fun J => ∑ g, c g * x g J) Q = ∑ g, c g * hol2 u (x g) Q := by
  simp only [hol2_eq_second]
  exact sum_lin_aux c x _

theorem hol2_antisymm (u v : Fin 4 → ℝ) (Q : Fin 4 → Fin 4 → ℝ)
    (hQ : ∀ I J, Q J I = -Q I J) : hol2 u v Q = -hol2 v u Q := by
  unfold hol2
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [hQ]; ring

theorem lowerInternal_antisymm (η : Matrix (Fin 4) (Fin 4) ℝ)
    (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (hR : ∀ K L ρ σ, R L K ρ σ = -R K L ρ σ)
    (I J ρ σ : Fin 4) : lowerInternal η R J I ρ σ = -lowerInternal η R I J ρ σ := by
  unfold lowerInternal
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun L _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [hR]; ring

/-- `e^I_γ e^J_ν R_{IJρσ} = (e^I_γ η_{IK}) R^K{}_{Jρσ} e^J_ν`. -/
theorem hol2_lower_eq (η e : Matrix (Fin 4) (Fin 4) ℝ) (hη : ∀ I K, η I K = η K I)
    (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (γ ν ρ σ : Fin 4) :
    hol2 (fun I => e I γ) (fun J => e J ν) (fun I J => lowerInternal η R I J ρ σ) =
      ∑ K, (∑ I, e I γ * η I K) * bianchiTerm η e R K ν ρ σ := by
  unfold hol2 lowerInternal bianchiTerm
  simp only [Finset.mul_sum, Finset.sum_mul]
  symm
  rw [sum_move_out3]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [sum_move_out2]
  refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun K _ =>
    Finset.sum_congr rfl fun L _ => ?_
  rw [hη L J]; ring

/-- A permutation-symbol contraction kills any tensor with vanishing cyclic sum. -/
theorem sum_eps_cyclic_eq_zero (μ : Fin 4) (B : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hB : ∀ ν ρ σ, B ν ρ σ + B ρ σ ν + B σ ν ρ = 0) :
    ∑ ν, ∑ ρ, ∑ σ, epsR μ ν ρ σ * B ν ρ σ = 0 := by
  set S := ∑ ν, ∑ ρ, ∑ σ, epsR μ ν ρ σ * B ν ρ σ with hS
  have h1 : ∑ ν, ∑ ρ, ∑ σ, epsR μ ν ρ σ * B ρ σ ν = S := by
    have : ∀ ν ρ σ, epsR μ ν ρ σ * B ρ σ ν = epsR μ ρ σ ν * B ρ σ ν := fun ν ρ σ => by
      rw [← epsR_cyclic123 μ ν ρ σ]
    rw [Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ρ _ =>
      Finset.sum_congr rfl fun σ _ => this ν ρ σ]
    exact sum_move_in2 (fun n a b => epsR μ a b n * B a b n)
  have h2 : ∑ ν, ∑ ρ, ∑ σ, epsR μ ν ρ σ * B σ ν ρ = S := by
    have : ∀ ν ρ σ, epsR μ ν ρ σ * B σ ν ρ = epsR μ σ ν ρ * B σ ν ρ := fun ν ρ σ => by
      rw [epsR_cyclic123 μ σ ν ρ]
    rw [Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ρ _ =>
      Finset.sum_congr rfl fun σ _ => this ν ρ σ]
    exact sum_move_out2 (fun n a b => epsR μ n a b * B n a b)
  have h3 : (∑ ν, ∑ ρ, ∑ σ, epsR μ ν ρ σ * B ν ρ σ) +
      (∑ ν, ∑ ρ, ∑ σ, epsR μ ν ρ σ * B ρ σ ν) + (∑ ν, ∑ ρ, ∑ σ, epsR μ ν ρ σ * B σ ν ρ) = 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun ν _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun ρ _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun σ _ => ?_
    rw [← mul_add, ← mul_add, hB, mul_zero]
  rw [h1, h2] at h3
  linarith

theorem holst_part_eq_zero (H : Matrix (Fin 4) (Fin 4) ℝ)
    (Bl : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hcyc : ∀ γ ν ρ σ, Bl γ ν ρ σ + Bl γ ρ σ ν + Bl γ σ ν ρ = 0) :
    ∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsR μ ν ρ σ * ∑ γ, H γ μ * Bl γ ν ρ σ = 0 := by
  have hμ : ∀ μ, ∑ ν, ∑ ρ, ∑ σ, epsR μ ν ρ σ * ∑ γ, H γ μ * Bl γ ν ρ σ =
      ∑ γ, H γ μ * ∑ ν, ∑ ρ, ∑ σ, epsR μ ν ρ σ * Bl γ ν ρ σ := by
    intro μ
    simp only [Finset.mul_sum]
    rw [sum_move_out3 (fun γ ν ρ σ => epsR μ ν ρ σ * (H γ μ * Bl γ ν ρ σ))]
    refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun ν _ =>
      Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun σ _ => ?_
    ring
  simp only [hμ]
  refine Finset.sum_eq_zero fun μ _ => Finset.sum_eq_zero fun γ _ => ?_
  rw [sum_eps_cyclic_eq_zero μ (fun ν ρ σ => Bl γ ν ρ σ) (hcyc γ), mul_zero]

/-- **The first Bianchi identity removes the Holst coframe variation.**  If `η` is symmetric,
the internal curvature `R^{KL}_{ρσ}` is antisymmetric in `(K, L)` and the algebraic first
Bianchi identity `R^K{}_J ∧ e^J = 0` holds, then the Holst coframe variation vanishes in every
direction `δe = e H` (hence in every direction when `e` is invertible). -/
theorem holstVariation_mul_eq_zero (η e H : Matrix (Fin 4) (Fin 4) ℝ)
    (hη : ∀ I K, η I K = η K I) (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hR : ∀ K L ρ σ, R L K ρ σ = -R K L ρ σ) (hB : SatisfiesFirstBianchi η e R) :
    holstVariation η e (e * H) R = 0 := by
  set Bl : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ := fun γ ν ρ σ =>
    hol2 (fun I => e I γ) (fun J => e J ν) (fun I J => lowerInternal η R I J ρ σ) with hBl
  have hcol : ∀ μ, (fun I => (e * H) I μ) = fun I => ∑ γ, H γ μ * e I γ := by
    intro μ; funext I; simp [Matrix.mul_apply, mul_comm]
  have hcyc : ∀ γ ν ρ σ, Bl γ ν ρ σ + Bl γ ρ σ ν + Bl γ σ ν ρ = 0 := by
    intro γ ν ρ σ
    simp only [hBl, hol2_lower_eq η e hη R]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun K _ => ?_
    rw [← mul_add, ← mul_add, hB K ν ρ σ, mul_zero]
  have hfirst : ∀ μ ν ρ σ, hol2 (fun I => (e * H) I μ) (fun J => e J ν)
      (fun I J => lowerInternal η R I J ρ σ) = ∑ γ, H γ μ * Bl γ ν ρ σ := by
    intro μ ν ρ σ
    rw [hcol, hol2_sum_left]
  have hsecond : ∀ μ ν ρ σ, hol2 (fun I => e I μ) (fun J => (e * H) J ν)
      (fun I J => lowerInternal η R I J ρ σ) = -∑ γ, H γ ν * Bl γ μ ρ σ := by
    intro μ ν ρ σ
    rw [hcol, hol2_sum_second, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [hBl, hol2_antisymm _ _ _ (fun I J => lowerInternal_antisymm η R hR I J ρ σ)]
    ring
  unfold holstVariation
  simp only [hfirst, hsecond, mul_add, Finset.sum_add_distrib]
  rw [holst_part_eq_zero H Bl hcyc, mul_zero, zero_add]
  have hswap : ∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsR μ ν ρ σ * -∑ γ, H γ ν * Bl γ μ ρ σ =
      ∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsR μ ν ρ σ * ∑ γ, H γ μ * Bl γ ν ρ σ := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun σ _ => ?_
    rw [epsR_swap01 b a]; ring
  rw [hswap, holst_part_eq_zero H Bl hcyc, mul_zero]

/-! ### The Palatini coframe variation is the Einstein tensor -/

/-- Ricci contraction `Ric^μ_γ = 𝓡^{μσ}_{γσ}` of a coordinate curvature `𝓡^{αβ}_{ρσ}`. -/
def ricciOf (Rc : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (μ γ : Fin 4) : ℝ := ∑ σ, Rc μ σ γ σ

/-- Scalar curvature `S = Ric^μ_μ`. -/
def scalarOf (Rc : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) : ℝ := ∑ μ, ricciOf Rc μ μ

/-- The Einstein tensor with lowered indices
`G_{βγ} = g_{βμ} (Ric^μ_γ - ½ δ^μ_γ S)` of the coordinate curvature `𝓡` and metric `g`. -/
def einsteinOf (g : Matrix (Fin 4) (Fin 4) ℝ) (Rc : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (β γ : Fin 4) : ℝ :=
  ∑ μ, g β μ * ricciOf Rc μ γ - (1 / 2) * g β γ * scalarOf Rc

theorem kdz_cast (a b : Fin 4) : ((kdz a b : ℤ) : ℝ) = if a = b then 1 else 0 := by
  unfold kdz; split_ifs <;> simp

/-- The double contraction of the generalized Kronecker delta with a curvature antisymmetric in
both pairs: `δ^{μρσ}_{γαβ} 𝓡^{αβ}_{ρσ} = 2 S δ^μ_γ - 4 Ric^μ_γ`. -/
theorem sum_contract_one_curv (Rc : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (h1 : ∀ α β ρ σ, Rc β α ρ σ = -Rc α β ρ σ) (h2 : ∀ α β ρ σ, Rc α β σ ρ = -Rc α β ρ σ)
    (μ γ : Fin 4) :
    ∑ ρ, ∑ σ, ∑ α, ∑ β, Rc α β ρ σ * (∑ n, epsR n μ ρ σ * epsR n γ α β) =
      2 * scalarOf Rc * (if μ = γ then 1 else 0) - 4 * ricciOf Rc μ γ := by
  simp only [epsR_contract_one]
  push_cast
  simp only [kdz_cast]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp [mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
  have e1 : ∑ x, ∑ y, Rc y x x y = -scalarOf Rc := by
    simp only [scalarOf, ricciOf, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => h1 x y x y
  have e0 : ∑ x, ∑ y, Rc x y x y = scalarOf Rc := rfl
  have e2 : ∑ x, Rc μ x x γ = -ricciOf Rc μ γ := by
    simp only [ricciOf, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x _ => h2 μ x γ x
  have e3 : ∑ x, Rc x μ γ x = -ricciOf Rc μ γ := by
    simp only [ricciOf, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x _ => h1 μ x γ x
  have e4 : ∑ x, Rc x μ x γ = ricciOf Rc μ γ := by
    simp only [ricciOf]
    exact Finset.sum_congr rfl fun x _ => by rw [h1 μ x x γ, h2 μ x γ x, neg_neg]
  rw [e1, e0, e2, e3, e4]
  have e5 : ∑ x, Rc μ x γ x = ricciOf Rc μ γ := rfl
  rw [e5]
  split_ifs <;> ring

/-- Substituting the coordinate curvature, first slot. -/
theorem pal4_mul_first (e H : Matrix (Fin 4) (Fin 4) ℝ)
    (R Rc : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hR : ∀ K L ρ σ, R K L ρ σ = ∑ α, ∑ β, e K α * e L β * Rc α β ρ σ) (μ ν ρ σ : Fin 4) :
    pal4 (fun I => (e * H) I μ) (fun J => e J ν) (fun K L => R K L ρ σ) =
      e.det * ∑ α, ∑ β, Rc α β ρ σ * ∑ γ, H γ μ * epsR γ ν α β := by
  have hQ : (fun K L => R K L ρ σ) = fun K L => ∑ α, ∑ β, e K α * e L β * Rc α β ρ σ := by
    funext K L; exact hR K L ρ σ
  have hcol : (fun I => (e * H) I μ) = fun I => ∑ γ, H γ μ * e I γ := by
    funext I; simp [Matrix.mul_apply, mul_comm]
  rw [hQ, pal4_of_coord, hcol, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [vol4_sum_left]
  simp only [vol4_cols, Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  ring

/-- Substituting the coordinate curvature, second slot. -/
theorem pal4_mul_second (e H : Matrix (Fin 4) (Fin 4) ℝ)
    (R Rc : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hR : ∀ K L ρ σ, R K L ρ σ = ∑ α, ∑ β, e K α * e L β * Rc α β ρ σ) (μ ν ρ σ : Fin 4) :
    pal4 (fun I => e I μ) (fun J => (e * H) J ν) (fun K L => R K L ρ σ) =
      e.det * ∑ α, ∑ β, Rc α β ρ σ * ∑ γ, H γ ν * epsR μ γ α β := by
  have hQ : (fun K L => R K L ρ σ) = fun K L => ∑ α, ∑ β, e K α * e L β * Rc α β ρ σ := by
    funext K L; exact hR K L ρ σ
  have hcol : (fun I => (e * H) I ν) = fun I => ∑ γ, H γ ν * e I γ := by
    funext I; simp [Matrix.mul_apply, mul_comm]
  rw [hQ, pal4_of_coord, hcol, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [vol4_sum_second]
  simp only [vol4_cols, Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  ring

theorem sum_four_mul_add (c : ℝ) (f g : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsR μ ν ρ σ * (c * f μ ν ρ σ + c * g μ ν ρ σ) =
      c * ((∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsR μ ν ρ σ * f μ ν ρ σ) +
        ∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsR μ ν ρ σ * g μ ν ρ σ) := by
  rw [mul_add]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem sum_move_in5 (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ∑ n, ∑ a, ∑ b, ∑ c, ∑ d, ∑ g, f n a b c d g =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ g, ∑ n, f n a b c d g := by
  rw [sum_move_in3 (fun n a b c => ∑ d, ∑ g, f n a b c d g)]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  exact sum_move_in2 (fun n d g => f n a b c d g)

theorem sum_move_out4 (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ n, f n a b c d = ∑ n, ∑ a, ∑ b, ∑ c, ∑ d, f n a b c d := by
  rw [show (∑ a, ∑ b, ∑ c, ∑ d, ∑ n, f n a b c d) = ∑ a, ∑ n, ∑ b, ∑ c, ∑ d, f n a b c d from
    Finset.sum_congr rfl fun a _ => sum_move_out3 (fun n b c d => f n a b c d)]
  exact Finset.sum_comm

/-- The first Palatini contraction:
`ε^{μνρσ} 𝓡^{αβ}_{ρσ} H^γ_μ ε_{γναβ} = 2 S tr H - 4 tr(H Ric)`. -/
theorem palatini_first_contraction (H : Matrix (Fin 4) (Fin 4) ℝ)
    (Rc : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (h1 : ∀ α β ρ σ, Rc β α ρ σ = -Rc α β ρ σ) (h2 : ∀ α β ρ σ, Rc α β σ ρ = -Rc α β ρ σ) :
    ∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsR μ ν ρ σ * ∑ α, ∑ β, Rc α β ρ σ * ∑ γ, H γ μ * epsR γ ν α β =
      2 * scalarOf Rc * Matrix.trace H - 4 * ∑ γ, ∑ μ, H γ μ * ricciOf Rc μ γ := by
  have hμ : ∀ μ, ∑ ν, ∑ ρ, ∑ σ, epsR μ ν ρ σ * ∑ α, ∑ β, Rc α β ρ σ *
      ∑ γ, H γ μ * epsR γ ν α β =
      ∑ γ, H γ μ * ∑ ρ, ∑ σ, ∑ α, ∑ β, Rc α β ρ σ * (∑ n, epsR n μ ρ σ * epsR n γ α β) := by
    intro μ
    simp only [Finset.mul_sum]
    rw [sum_move_in5 (fun ν ρ σ α β γ => epsR μ ν ρ σ * (Rc α β ρ σ * (H γ μ * epsR γ ν α β)))]
    rw [sum_move_out4 (fun γ ρ σ α β => ∑ ν, epsR μ ν ρ σ *
      (Rc α β ρ σ * (H γ μ * epsR γ ν α β)))]
    refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun ρ _ =>
      Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun α _ =>
        Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun n _ => ?_
    rw [epsR_swap01 n μ, epsR_swap01 n γ]
    ring
  simp only [hμ, sum_contract_one_curv Rc h1 h2]
  rw [Finset.sum_comm]
  simp only [Matrix.trace, Matrix.diag, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun γ _ => ?_
    rw [Finset.sum_eq_single γ]
    · simp; ring
    · intro b _ hb; simp [hb]
    · simp
  · refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun μ _ => ?_
    ring

/-- **Palatini coframe variation.**  If `R^{KL}_{ρσ} = e^K_α e^L_β 𝓡^{αβ}_{ρσ}` with `𝓡`
antisymmetric in both pairs, then for every `H`,
`δ_{eH} L_P = det e · (tr H · S - 2 tr(H · Ric))`. -/
theorem palatiniVariation_mul_eq (e H : Matrix (Fin 4) (Fin 4) ℝ)
    (R Rc : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hR : ∀ K L ρ σ, R K L ρ σ = ∑ α, ∑ β, e K α * e L β * Rc α β ρ σ)
    (h1 : ∀ α β ρ σ, Rc β α ρ σ = -Rc α β ρ σ) (h2 : ∀ α β ρ σ, Rc α β σ ρ = -Rc α β ρ σ) :
    palatiniVariation e (e * H) R =
      e.det * (Matrix.trace H * scalarOf Rc - 2 * ∑ γ, ∑ μ, H γ μ * ricciOf Rc μ γ) := by
  unfold palatiniVariation
  simp only [pal4_mul_first e H R Rc hR, pal4_mul_second e H R Rc hR]
  rw [sum_four_mul_add]
  have hX : ∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsR μ ν ρ σ * ∑ α, ∑ β, Rc α β ρ σ *
      ∑ γ, H γ ν * epsR μ γ α β =
      ∑ μ, ∑ ν, ∑ ρ, ∑ σ, epsR μ ν ρ σ * ∑ α, ∑ β, Rc α β ρ σ *
      ∑ γ, H γ μ * epsR γ ν α β := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun σ _ => ?_
    rw [epsR_swap01 b a, neg_mul, ← mul_neg]
    congr 1
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [← mul_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [epsR_swap01 b γ]; ring
  rw [hX, palatini_first_contraction H Rc h1 h2]
  ring


/-! ### Coordinate curvature, metric, and the inverse-metric test lift -/

/-- The coordinate curvature `𝓡^{αβ}_{ρσ} = E^α_K E^β_L R^{KL}_{ρσ}`, `E = e⁻¹` (matrix inverse;
the frame-to-coordinate transform of the internal curvature). -/
def coordCurvature (e : Matrix (Fin 4) (Fin 4) ℝ) (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun α β ρ σ => ∑ K, ∑ L, e⁻¹ α K * e⁻¹ β L * R K L ρ σ

/-- The coframe metric `g = eᵀ η e`, `g_{μν} = η_{IJ} e^I_μ e^J_ν`. -/
def coframeMetric (η e : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  e.transpose * η * e

/-- The coframe lift `δe = e H`, `H = -½ k g`, of an inverse-metric test `k^{μν}`
(it induces `δ g^{μν} = k^{μν}` for symmetric `k`). -/
def metricTestGenerator (η e k : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  -(1 / 2 : ℝ) • (k * coframeMetric η e)

theorem coordCurvature_spec (e : Matrix (Fin 4) (Fin 4) ℝ) (hdet : e.det ≠ 0)
    (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (K L ρ σ : Fin 4) :
    R K L ρ σ = ∑ α, ∑ β, e K α * e L β * coordCurvature e R α β ρ σ := by
  have hEE : e * e⁻¹ = 1 := Matrix.mul_nonsing_inv e (isUnit_iff_ne_zero.mpr hdet)
  have hrow : ∀ K K', ∑ α, e K α * e⁻¹ α K' = if K = K' then 1 else 0 := by
    intro K K'
    have := congrFun (congrFun hEE K) K'
    rw [Matrix.mul_apply] at this
    rw [this, Matrix.one_apply]
  unfold coordCurvature
  simp only [Finset.mul_sum]
  rw [sum_block_swap (fun α β K' L' => e K α * e L β * (e⁻¹ α K' * e⁻¹ β L' * R K' L' ρ σ))]
  have : ∀ K' L', ∑ α, ∑ β, e K α * e L β * (e⁻¹ α K' * e⁻¹ β L' * R K' L' ρ σ) =
      (∑ α, e K α * e⁻¹ α K') * (∑ β, e L β * e⁻¹ β L') * R K' L' ρ σ := by
    intro K' L'
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun β _ => ?_
    ring
  simp only [this, hrow]
  simp

theorem coordCurvature_antisymm_left (e : Matrix (Fin 4) (Fin 4) ℝ)
    (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (hR : ∀ K L ρ σ, R L K ρ σ = -R K L ρ σ)
    (α β ρ σ : Fin 4) : coordCurvature e R β α ρ σ = -coordCurvature e R α β ρ σ := by
  unfold coordCurvature
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun L _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [hR]; ring

theorem coordCurvature_antisymm_right (e : Matrix (Fin 4) (Fin 4) ℝ)
    (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (hR : ∀ K L ρ σ, R K L σ ρ = -R K L ρ σ)
    (α β ρ σ : Fin 4) : coordCurvature e R α β σ ρ = -coordCurvature e R α β ρ σ := by
  unfold coordCurvature
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun L _ => ?_
  rw [hR]; ring

theorem trace_metricTestGenerator (η e k : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix.trace (metricTestGenerator η e k) =
      -(1 / 2) * ∑ γ, ∑ b, k γ b * coframeMetric η e b γ := by
  simp [metricTestGenerator, Matrix.trace, Matrix.mul_apply, Finset.mul_sum]

theorem sum_metricTestGenerator_mul (η e k : Matrix (Fin 4) (Fin 4) ℝ)
    (Y : Fin 4 → Fin 4 → ℝ) :
    ∑ γ, ∑ μ, metricTestGenerator η e k γ μ * Y μ γ =
      -(1 / 2) * ∑ γ, ∑ b, k γ b * ∑ μ, coframeMetric η e b μ * Y μ γ := by
  simp only [metricTestGenerator, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun μ _ => ?_
  ring

theorem sum_einstein_split (k g X : Matrix (Fin 4) (Fin 4) ℝ) (S β lam : ℝ) :
    ∑ γ, ∑ b, k γ b * (β * (X b γ - (1 / 2) * g b γ * S) - lam / 2 * g b γ) =
      β * (∑ γ, ∑ b, k γ b * X b γ) - (β * S / 2 + lam / 2) * ∑ γ, ∑ b, k γ b * g b γ := by
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- **Einstein insertion of the classified coframe variation** (pointwise algebraic core of
`eq:supp-einstein-insertion`).  Let `e` be an invertible coframe, `η` symmetric, `R^{KL}_{ρσ}`
antisymmetric in both pairs and satisfying the algebraic first Bianchi identity
`R^K{}_J ∧ e^J = 0`.  For the inverse-metric test lift `δe = e H`, `H = -½ k g`, the first
variation of `α L_H + β L_P + λ L_vol` is
`det e · k^{γb} (β G_{bγ} - (λ/2) g_{bγ})`, where `G` is the Einstein tensor of the coordinate
curvature `𝓡 = E E R` and `g = eᵀ η e`. -/
theorem hasDerivAt_classifiedDensity_metricTest (η e k : Matrix (Fin 4) (Fin 4) ℝ)
    (hdet : e.det ≠ 0) (hη : ∀ I K, η I K = η K I) (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hR1 : ∀ K L ρ σ, R L K ρ σ = -R K L ρ σ) (hR2 : ∀ K L ρ σ, R K L σ ρ = -R K L ρ σ)
    (hB : SatisfiesFirstBianchi η e R) (α β lam : ℝ) :
    HasDerivAt (fun t : ℝ =>
        α * holstDensity η (e + t • (e * metricTestGenerator η e k)) R +
        β * palatiniDensity (e + t • (e * metricTestGenerator η e k)) R +
        lam * volumeDensity (e + t • (e * metricTestGenerator η e k)))
      (e.det * ∑ γ, ∑ b, k γ b * (β * einsteinOf (coframeMetric η e)
        (coordCurvature e R) b γ - lam / 2 * coframeMetric η e b γ)) 0 := by
  set H := metricTestGenerator η e k with hH
  set Rc := coordCurvature e R
  set g := coframeMetric η e
  have h := (((hasDerivAt_holstDensity η e (e * H) R).const_mul α).add
    ((hasDerivAt_palatiniDensity e (e * H) R).const_mul β)).add
    ((hasDerivAt_volumeDensity e (e * H) hdet).const_mul lam)
  refine h.congr_deriv ?_
  rw [holstVariation_mul_eq_zero η e H hη R hR1 hB,
    palatiniVariation_mul_eq e H R Rc (coordCurvature_spec e hdet R)
      (coordCurvature_antisymm_left e R hR1) (coordCurvature_antisymm_right e R hR2),
    Matrix.nonsing_inv_mul_cancel_left e H (isUnit_iff_ne_zero.mpr hdet)]
  have hsplit := sum_einstein_split k g (fun b γ => ∑ μ, g b μ * ricciOf Rc μ γ)
    (scalarOf Rc) β lam
  simp only [einsteinOf]
  rw [hsplit, hH, trace_metricTestGenerator, sum_metricTestGenerator_mul]
  ring

/-! ### Lorentzian volume and the cosmological normalization -/

/-- The Minkowski metric `η = diag(-1, 1, 1, 1)`. -/
def minkowski : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![-1, 1, 1, 1]

theorem minkowski_symm (I K : Fin 4) : minkowski I K = minkowski K I := by
  unfold minkowski
  by_cases h : I = K
  · rw [h]
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]

theorem det_minkowski : minkowski.det = -1 := by
  simp [minkowski, Matrix.det_diagonal, Fin.prod_univ_four]

/-- `√(-det g) = |det e|` for `g = eᵀ η e` and `det η = -1`. -/
theorem sqrt_neg_det_coframeMetric (η e : Matrix (Fin 4) (Fin 4) ℝ) (hη : η.det = -1) :
    Real.sqrt (-(coframeMetric η e).det) = |e.det| := by
  have : -(coframeMetric η e).det = e.det ^ 2 := by
    simp [coframeMetric, Matrix.det_mul, Matrix.det_transpose, hη]; ring
  rw [this, Real.sqrt_sq_eq_abs]

/-- **Einstein insertion `χ √(-g) (G + Λ g) k`.**  For an oriented (`det e > 0`) coframe, the
Minkowski fibre metric, and a curvature with the internal antisymmetries and the algebraic first
Bianchi identity, the first variation of the classified density
`α L_H + β L_P + λ L_vol` along the inverse-metric test lift equals
`β √(-det g) k^{γb} (G_{bγ} + Λ g_{bγ})` with `Λ = -λ/(2β)`; the Holst coefficient `α` drops
out.  This is `eq:supp-einstein-insertion` at a point, with `χ = β ≠ 0`. -/
theorem hasDerivAt_classifiedDensity_einstein (e k : Matrix (Fin 4) (Fin 4) ℝ)
    (hdet : 0 < e.det) (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hR1 : ∀ K L ρ σ, R L K ρ σ = -R K L ρ σ) (hR2 : ∀ K L ρ σ, R K L σ ρ = -R K L ρ σ)
    (hB : SatisfiesFirstBianchi minkowski e R) (α β lam : ℝ) (hβ : β ≠ 0) :
    HasDerivAt (fun t : ℝ =>
        α * holstDensity minkowski (e + t • (e * metricTestGenerator minkowski e k)) R +
        β * palatiniDensity (e + t • (e * metricTestGenerator minkowski e k)) R +
        lam * volumeDensity (e + t • (e * metricTestGenerator minkowski e k)))
      (β * Real.sqrt (-(coframeMetric minkowski e).det) *
        ∑ γ, ∑ b, k γ b * (einsteinOf (coframeMetric minkowski e) (coordCurvature e R) b γ +
          (-lam / (2 * β)) * coframeMetric minkowski e b γ)) 0 := by
  refine (hasDerivAt_classifiedDensity_metricTest minkowski e k hdet.ne' minkowski_symm R hR1
    hR2 hB α β lam).congr_deriv ?_
  rw [sqrt_neg_det_coframeMetric minkowski e det_minkowski, abs_of_pos hdet, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  field_simp
  ring

/-- Non-vacuity: the identity coframe (oriented) with zero curvature satisfies the hypotheses of
`hasDerivAt_classifiedDensity_einstein`. -/
example : (0 : ℝ) < (1 : Matrix (Fin 4) (Fin 4) ℝ).det ∧
    SatisfiesFirstBianchi minkowski 1 (fun _ _ _ _ => 0) :=
  ⟨by simp, fun _ _ _ _ => by simp [bianchiTerm]⟩

end RenewalGeometry.PalatiniEinsteinAlgebra
