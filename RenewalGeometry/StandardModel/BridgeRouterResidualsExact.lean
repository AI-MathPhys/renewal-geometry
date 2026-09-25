/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.WeakResetGenerationExact
import RenewalGeometry.StandardModel.InternalCommutantSeedExact

/-!
# Minimal bridge and weak-router residuals

`prop:bridge-router-residuals` of the spacetime–gauge duality paper.

## Colour residual

On `T ⊕ H_priv = ℂ ⊕ ℂ² = ℂ³` the colour residual is
`δ_col(u) = ‖p_H u p_T‖²_HS + ‖p_T u p_H‖²_HS`; `colourResidual_eq_omegaCol` identifies
it with the corner weight `omegaCol u = |u₁₀|² + |u₂₀|² + |u₀₁|² + |u₀₂|²` of
`InternalCommutantSeedExact.lean`.  Then (with the private matrix units among the
generators, i.e. the hypothesis of `thm:colour-bridge` that the private words
generate `M₂(H_priv)`):

* `adjoin_eq_top_iff_colourResidual_pos`: `δ_col > 0` gives `M₃` (and conversely);
* `adjoin_eq_blockDiag_iff_colourResidual_zero`: `δ_col = 0` **exactly** on the
  reducing branch, where the generated algebra is the block algebra `M₂ ⊕ ℂ`
  (`InternalSeed.blockDiag`).

## Weak residual

For rank-one projections `p = |t⟩⟨t|`, `q = |h⟩⟨h|` onto unit vectors of `ℂ²`,
`δ_wk(p, q) = ‖[p, q]‖²_HS` (`weakResidual`) and

* `weakResidual_eq`: `δ_wk = 2c²(1 − c²)` with `c = |⟨t, h⟩|` (`eq:weak-router-residual`);
  the underlying polynomial identity `weakResidual_eq_general` holds for all vectors;
* `weakResidual_pos_iff`: `δ_wk > 0` iff the projections are distinct and
  non-orthogonal (`p ≠ q ∧ ⟨t, h⟩ ≠ 0`), via `proj_eq_iff` (`p = q ↔ c² = 1`) and the
  two-dimensional Lagrange identity `lagrange_identity`
  `|t₀h₁ − t₁h₀|² + |⟨t,h⟩|² = ‖t‖²‖h‖²`;
* `adjoin_eq_top_of_weakResidual_pos`: in that case `p, q` generate `M₂(ℂ)`
  (`WeakReset.two_lines_generate`, the Burnside condition of `lem:weak-M2`).

`bridge_router_residuals` assembles the proposition.
-/

open Finset Matrix Complex

namespace RenewalGeometry
namespace BridgeRouter

/-- Squared Hilbert–Schmidt (Frobenius) norm `∑_{ij} |A_{ij}|²`. -/
noncomputable def frobSq {m : Type*} [Fintype m] (A : Matrix m m ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (A i j)

theorem frobSq_nonneg {m : Type*} [Fintype m] (A : Matrix m m ℂ) : 0 ≤ frobSq A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-! ### The colour residual on `T ⊕ H_priv` -/

/-- The private-plane projection `p_H = E₁₁ + E₂₂` on `ℂ³ = T ⊕ H_priv`. -/
def pH : Matrix (Fin 3) (Fin 3) ℂ := Matrix.single 1 1 1 + Matrix.single 2 2 1

/-- The colour residual `δ_col(u) = ‖p_H u p_T‖²_HS + ‖p_T u p_H‖²_HS`. -/
noncomputable def colourResidual (u : Matrix (Fin 3) (Fin 3) ℂ) : ℝ :=
  frobSq (pH * u * InternalSeed.pT) + frobSq (InternalSeed.pT * u * pH)

theorem pH_mul_mul_pT (u : Matrix (Fin 3) (Fin 3) ℂ) :
    pH * u * InternalSeed.pT = Matrix.single 1 0 (u 1 0) + Matrix.single 2 0 (u 2 0) := by
  rw [pH, InternalSeed.pT, add_mul, add_mul, Matrix.single_mul_mul_single,
    Matrix.single_mul_mul_single, mul_one, one_mul, mul_one, one_mul]

theorem pT_mul_mul_pH (u : Matrix (Fin 3) (Fin 3) ℂ) :
    InternalSeed.pT * u * pH = Matrix.single 0 1 (u 0 1) + Matrix.single 0 2 (u 0 2) := by
  rw [pH, InternalSeed.pT, mul_add, Matrix.single_mul_mul_single,
    Matrix.single_mul_mul_single, mul_one, one_mul, mul_one, one_mul]

/-- The colour residual is the corner weight `ω_col(u)` of `thm:colour-bridge`. -/
theorem colourResidual_eq_omegaCol (u : Matrix (Fin 3) (Fin 3) ℂ) :
    colourResidual u = InternalSeed.omegaCol u := by
  rw [colourResidual, pH_mul_mul_pT, pT_mul_mul_pH, InternalSeed.omegaCol, frobSq, frobSq]
  simp only [Fin.sum_univ_three, Matrix.add_apply, Matrix.single_apply]
  simp
  ring

/-- **Positive colour residual gives `M₃`** (and conversely): `thm:colour-bridge` in
the residual language. -/
theorem adjoin_eq_top_iff_colourResidual_pos (u : Matrix (Fin 3) (Fin 3) ℂ) :
    Algebra.adjoin ℂ (InternalSeed.gens u) = ⊤ ↔ 0 < colourResidual u := by
  rw [colourResidual_eq_omegaCol]
  exact InternalSeed.internal_seed_dichotomy u

theorem blockDiag_ne_top : InternalSeed.blockDiag ≠ ⊤ := by
  intro h
  have hmem : Matrix.single (0 : Fin 3) 1 (1 : ℂ) ∈ InternalSeed.blockDiag := by
    rw [h]; exact Algebra.mem_top
  have := hmem.1
  rw [Matrix.single_apply_same] at this
  exact one_ne_zero this

/-- The generators lie in the block algebra `M₂ ⊕ ℂ` when the colour residual vanishes. -/
theorem gens_subset_blockDiag {u : Matrix (Fin 3) (Fin 3) ℂ} (h : colourResidual u = 0) :
    InternalSeed.gens u ⊆ (InternalSeed.blockDiag : Set (Matrix (Fin 3) (Fin 3) ℂ)) := by
  rw [colourResidual_eq_omegaCol, InternalSeed.omegaCol] at h
  have hnn := fun z : ℂ => Complex.normSq_nonneg z
  have h1 := hnn (u 1 0); have h2 := hnn (u 2 0)
  have h3 := hnn (u 0 1); have h4 := hnn (u 0 2)
  have h10 : u 1 0 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  have h20 : u 2 0 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  have h01 : u 0 1 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  have h02 : u 0 2 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  intro X hX
  simp only [InternalSeed.gens, Set.union_insert, Set.union_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hX
  rcases hX with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [InternalSeed.pT, Matrix.single_apply, Matrix.conjTranspose_apply, h10, h20, h01, h02]

/-- The block algebra `M₂ ⊕ ℂ` is spanned by the five generators `E₀₀, E₁₁, E₁₂, E₂₁, E₂₂`. -/
theorem blockDiag_le_adjoin (u : Matrix (Fin 3) (Fin 3) ℂ) :
    InternalSeed.blockDiag ≤ Algebra.adjoin ℂ (InternalSeed.gens u) := by
  intro X hX
  set A := Algebra.adjoin ℂ (InternalSeed.gens u) with hA
  have hunit : ∀ i j : Fin 3, Matrix.single i j (1 : ℂ) ∈ A → Matrix.single i j (X i j) ∈ A := by
    intro i j hij
    rw [show Matrix.single i j (X i j) = X i j • Matrix.single i j 1 from by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]]
    exact A.smul_mem hij _
  have h00 : Matrix.single (0 : Fin 3) 0 (1 : ℂ) ∈ A := by
    have : InternalSeed.pT ∈ A := Algebra.subset_adjoin (by simp [InternalSeed.gens])
    rwa [InternalSeed.pT] at this
  have h11 : Matrix.single (1 : Fin 3) 1 (1 : ℂ) ∈ A :=
    Algebra.subset_adjoin (by simp [InternalSeed.gens])
  have h12 : Matrix.single (1 : Fin 3) 2 (1 : ℂ) ∈ A :=
    Algebra.subset_adjoin (by simp [InternalSeed.gens])
  have h21 : Matrix.single (2 : Fin 3) 1 (1 : ℂ) ∈ A :=
    Algebra.subset_adjoin (by simp [InternalSeed.gens])
  have h22 : Matrix.single (2 : Fin 3) 2 (1 : ℂ) ∈ A :=
    Algebra.subset_adjoin (by simp [InternalSeed.gens])
  rw [Matrix.matrix_eq_sum_single X, Fin.sum_univ_three, Fin.sum_univ_three,
    Fin.sum_univ_three, Fin.sum_univ_three, hX.1, hX.2.1, hX.2.2.1, hX.2.2.2,
    Matrix.single_zero, Matrix.single_zero, Matrix.single_zero, Matrix.single_zero]
  simp only [add_zero, zero_add]
  repeat' first
    | exact hunit 0 0 h00 | exact hunit 1 1 h11 | exact hunit 1 2 h12
    | exact hunit 2 1 h21 | exact hunit 2 2 h22 | apply add_mem

/-- **Vanishing colour residual is exactly the reducing branch `M₂ ⊕ ℂ`**: the
generated algebra equals the block algebra iff `δ_col = 0`. -/
theorem adjoin_eq_blockDiag_iff_colourResidual_zero (u : Matrix (Fin 3) (Fin 3) ℂ) :
    Algebra.adjoin ℂ (InternalSeed.gens u) = InternalSeed.blockDiag ↔ colourResidual u = 0 := by
  constructor
  · intro h
    by_contra hne
    have hpos : 0 < colourResidual u := lt_of_le_of_ne
      (by rw [colourResidual]; exact add_nonneg (frobSq_nonneg _) (frobSq_nonneg _))
      (Ne.symm hne)
    have htop := (adjoin_eq_top_iff_colourResidual_pos u).mpr hpos
    rw [h] at htop
    exact blockDiag_ne_top htop
  · intro h
    exact le_antisymm (Algebra.adjoin_le (gens_subset_blockDiag h)) (blockDiag_le_adjoin u)

/-! ### The weak residual on `ℂ²` -/

/-- The rank-one carrier `|v⟩⟨v|`. -/
def proj (v : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ := Matrix.vecMulVec v (star v)

/-- The overlap `⟨t, h⟩ = ∑ conj(t_m) h_m`. -/
def overlap (t h : Fin 2 → ℂ) : ℂ := ∑ m, star (t m) * h m

/-- The weak residual `δ_wk(p, q) = ‖[p, q]‖²_HS` of the two rank-one carriers. -/
noncomputable def weakResidual (t h : Fin 2 → ℂ) : ℝ :=
  frobSq (proj t * proj h - proj h * proj t)

/-- Squared norm `‖v‖² = ∑ |v_m|²`. -/
noncomputable def normSqVec (v : Fin 2 → ℂ) : ℝ := ∑ m, Complex.normSq (v m)

theorem ofReal_normSq_eq (z : ℂ) : ((Complex.normSq z : ℝ) : ℂ) = z * star z := by
  rw [Complex.star_def, Complex.mul_conj]

/-- The general polynomial identity
`‖[p,q]‖²_HS = 2|⟨t,h⟩|² ‖t‖²‖h‖² − 2|⟨t,h⟩|⁴` for arbitrary vectors. -/
theorem weakResidual_eq_general (t h : Fin 2 → ℂ) :
    weakResidual t h =
      2 * Complex.normSq (overlap t h) * (normSqVec t * normSqVec h)
        - 2 * Complex.normSq (overlap t h) ^ 2 := by
  apply Complex.ofReal_injective
  simp only [weakResidual, frobSq, normSqVec, overlap, proj, Fin.sum_univ_two, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_add, Complex.ofReal_ofNat,
    ofReal_normSq_eq, Matrix.sub_apply, Matrix.mul_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, star_sub, star_add, star_mul, star_star]
  ring

/-- The two-dimensional Lagrange identity `|t₀h₁ − t₁h₀|² + |⟨t,h⟩|² = ‖t‖²‖h‖²`. -/
theorem lagrange_identity (t h : Fin 2 → ℂ) :
    Complex.normSq (t 0 * h 1 - t 1 * h 0) + Complex.normSq (overlap t h)
      = normSqVec t * normSqVec h := by
  apply Complex.ofReal_injective
  simp only [normSqVec, overlap, Fin.sum_univ_two, Complex.ofReal_add, Complex.ofReal_mul,
    ofReal_normSq_eq, star_sub, star_add, star_mul, star_star]
  ring

/-- **`eq:weak-router-residual`**: for unit vectors, `δ_wk = 2c²(1 − c²)` with
`c² = |⟨t, h⟩|²`. -/
theorem weakResidual_eq (t h : Fin 2 → ℂ) (ht : normSqVec t = 1) (hh : normSqVec h = 1) :
    weakResidual t h =
      2 * Complex.normSq (overlap t h) * (1 - Complex.normSq (overlap t h)) := by
  rw [weakResidual_eq_general, ht, hh]
  ring

/-- The same with `c = |⟨t, h⟩|`. -/
theorem weakResidual_eq_norm (t h : Fin 2 → ℂ) (ht : normSqVec t = 1) (hh : normSqVec h = 1) :
    weakResidual t h = 2 * ‖overlap t h‖ ^ 2 * (1 - ‖overlap t h‖ ^ 2) := by
  rw [weakResidual_eq t h ht hh, Complex.normSq_eq_norm_sq]

/-- For unit vectors `c² ≤ 1` (Cauchy–Schwarz via the Lagrange identity). -/
theorem normSq_overlap_le_one (t h : Fin 2 → ℂ) (ht : normSqVec t = 1) (hh : normSqVec h = 1) :
    Complex.normSq (overlap t h) ≤ 1 := by
  have := lagrange_identity t h
  rw [ht, hh, mul_one] at this
  have := Complex.normSq_nonneg (t 0 * h 1 - t 1 * h 0)
  linarith

/-- The unit-vector condition in the complex form `∑ t_m conj(t_m) = 1`. -/
theorem sum_mul_star_eq_one {t : Fin 2 → ℂ} (ht : normSqVec t = 1) :
    ∑ m, t m * star (t m) = 1 := by
  have := congrArg (fun r : ℝ => (r : ℂ)) ht
  simpa only [normSqVec, Complex.ofReal_sum, ofReal_normSq_eq, Complex.ofReal_one] using this

/-- **Distinctness criterion**: for unit vectors the carriers coincide iff `c² = 1`. -/
theorem proj_eq_iff (t h : Fin 2 → ℂ) (ht : normSqVec t = 1) (hh : normSqVec h = 1) :
    proj t = proj h ↔ Complex.normSq (overlap t h) = 1 := by
  have ht' := sum_mul_star_eq_one ht
  have hh' := sum_mul_star_eq_one hh
  rw [Fin.sum_univ_two] at ht' hh'
  constructor
  · intro hpq
    -- apply both carriers to `t`: `t = conj(a) h`
    have hcol : ∀ i, t i = h i * star (overlap t h) := by
      intro i
      have h1 : ∑ j, proj t i j * t j = ∑ j, proj h i j * t j := by rw [hpq]
      simp only [proj, Matrix.vecMulVec_apply, Pi.star_apply, Fin.sum_univ_two] at h1
      calc t i = t i * (t 0 * star (t 0) + t 1 * star (t 1)) := by rw [ht', mul_one]
        _ = t i * star (t 0) * t 0 + t i * star (t 1) * t 1 := by ring
        _ = h i * star (h 0) * t 0 + h i * star (h 1) * t 1 := h1
        _ = h i * star (overlap t h) := by
          simp only [overlap, Fin.sum_univ_two, star_add, star_mul, star_star]
          ring
    apply Complex.ofReal_injective
    rw [Complex.ofReal_one, ofReal_normSq_eq]
    calc overlap t h * star (overlap t h)
        = (h 0 * star (h 0) + h 1 * star (h 1)) * (overlap t h * star (overlap t h)) := by
          rw [hh', one_mul]
      _ = t 0 * star (t 0) + t 1 * star (t 1) := by
          rw [hcol 0, hcol 1]
          simp only [star_mul, star_star]
          ring
      _ = 1 := ht'
  · intro hc
    -- `‖t − conj(a) h‖² = ‖t‖² − 2|a|² + |a|²‖h‖² = 0`
    have hc' : overlap t h * star (overlap t h) = 1 := by
      have := congrArg (fun r : ℝ => (r : ℂ)) hc
      simpa only [ofReal_normSq_eq, Complex.ofReal_one] using this
    have hzero : ∑ m, Complex.normSq (t m - h m * star (overlap t h)) = 0 := by
      apply Complex.ofReal_injective
      simp only [Fin.sum_univ_two, Complex.ofReal_add, ofReal_normSq_eq, Complex.ofReal_zero]
      have hexp : ∀ m : Fin 2,
          (t m - h m * star (overlap t h)) * star (t m - h m * star (overlap t h))
            = t m * star (t m) - overlap t h * (t m * star (h m))
              - star (overlap t h) * (h m * star (t m))
              + (overlap t h * star (overlap t h)) * (h m * star (h m)) := by
        intro m
        simp only [star_sub, star_mul, star_star]
        ring
      rw [hexp 0, hexp 1]
      have hsum1 : t 0 * star (h 0) + t 1 * star (h 1) = star (overlap t h) := by
        simp only [overlap, Fin.sum_univ_two, star_add, star_mul, star_star]
        ring
      have hsum2 : h 0 * star (t 0) + h 1 * star (t 1) = overlap t h := by
        simp only [overlap, Fin.sum_univ_two]
        ring
      calc _ = (t 0 * star (t 0) + t 1 * star (t 1))
            - overlap t h * (t 0 * star (h 0) + t 1 * star (h 1))
            - star (overlap t h) * (h 0 * star (t 0) + h 1 * star (t 1))
            + (overlap t h * star (overlap t h)) * (h 0 * star (h 0) + h 1 * star (h 1)) := by
              ring
        _ = 0 := by
          rw [ht', hh', hsum1, hsum2, hc', mul_comm (star (overlap t h)) (overlap t h), hc']
          ring
    have hall : ∀ m, t m = h m * star (overlap t h) := by
      intro m
      have := (Finset.sum_eq_zero_iff_of_nonneg fun m _ => Complex.normSq_nonneg _).mp hzero m
        (Finset.mem_univ m)
      exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp this)
    ext i j
    simp only [proj, Matrix.vecMulVec_apply, Pi.star_apply]
    rw [hall i, hall j]
    calc h i * star (overlap t h) * star (h j * star (overlap t h))
        = (overlap t h * star (overlap t h)) * (h i * star (h j)) := by
          simp only [star_mul, star_star]; ring
      _ = h i * star (h j) := by rw [hc', one_mul]

/-- **Positivity of the weak residual**: for unit vectors `δ_wk > 0` iff the carriers
are distinct and non-orthogonal, i.e. `0 < c² < 1`. -/
theorem weakResidual_pos_iff (t h : Fin 2 → ℂ) (ht : normSqVec t = 1) (hh : normSqVec h = 1) :
    0 < weakResidual t h ↔ proj t ≠ proj h ∧ overlap t h ≠ 0 := by
  rw [weakResidual_eq t h ht hh, ne_eq, proj_eq_iff t h ht hh, ne_eq, ← Complex.normSq_eq_zero]
  have hle := normSq_overlap_le_one t h ht hh
  have hnn := Complex.normSq_nonneg (overlap t h)
  constructor
  · intro hpos
    constructor
    · intro h1; rw [h1] at hpos; simp at hpos
    · intro h0; rw [h0] at hpos; simp at hpos
  · rintro ⟨h1, h0⟩
    have hlt : Complex.normSq (overlap t h) < 1 := lt_of_le_of_ne hle h1
    have hgt : 0 < Complex.normSq (overlap t h) := lt_of_le_of_ne hnn (Ne.symm h0)
    have : 0 < 1 - Complex.normSq (overlap t h) := by linarith
    positivity

/-- **Generation**: a positive weak residual makes the two carriers generate `M₂(ℂ)`
(`lem:weak-M2`). -/
theorem adjoin_eq_top_of_weakResidual_pos (t h : Fin 2 → ℂ) (ht : normSqVec t = 1)
    (hh : normSqVec h = 1) (hpos : 0 < weakResidual t h) :
    Algebra.adjoin ℂ {proj t, proj h} = ⊤ := by
  obtain ⟨hne, hover⟩ := (weakResidual_pos_iff t h ht hh).mp hpos
  have hc1 : Complex.normSq (overlap t h) ≠ 1 := fun hc =>
    hne ((proj_eq_iff t h ht hh).mpr hc)
  have hd : t 0 * h 1 - t 1 * h 0 ≠ 0 := by
    intro hd
    have := lagrange_identity t h
    rw [hd, ht, hh, Complex.normSq_zero, zero_add, mul_one] at this
    exact hc1 this
  exact WeakReset.two_lines_generate t h hd hover

/-- **`prop:bridge-router-residuals`** (spacetime–gauge duality paper), assembled.
Colour: `δ_col = 0` exactly on the reducing branch `M₂ ⊕ ℂ`, and `δ_col > 0` exactly
when the generated algebra is `M₃`.  Weak: for unit vectors,
`δ_wk = 2c²(1 − c²)`, `δ_wk > 0` iff the carriers are distinct and non-orthogonal, and
then they generate `M₂`. -/
theorem bridge_router_residuals :
    (∀ u : Matrix (Fin 3) (Fin 3) ℂ,
      (Algebra.adjoin ℂ (InternalSeed.gens u) = InternalSeed.blockDiag ↔ colourResidual u = 0) ∧
      (Algebra.adjoin ℂ (InternalSeed.gens u) = ⊤ ↔ 0 < colourResidual u)) ∧
    (∀ t h : Fin 2 → ℂ, normSqVec t = 1 → normSqVec h = 1 →
      weakResidual t h = 2 * ‖overlap t h‖ ^ 2 * (1 - ‖overlap t h‖ ^ 2) ∧
      (0 < weakResidual t h ↔ proj t ≠ proj h ∧ overlap t h ≠ 0) ∧
      (0 < weakResidual t h → Algebra.adjoin ℂ {proj t, proj h} = ⊤)) :=
  ⟨fun u => ⟨adjoin_eq_blockDiag_iff_colourResidual_zero u, adjoin_eq_top_iff_colourResidual_pos u⟩,
    fun t h ht hh => ⟨weakResidual_eq_norm t h ht hh, weakResidual_pos_iff t h ht hh,
      adjoin_eq_top_of_weakResidual_pos t h ht hh⟩⟩

end BridgeRouter
end RenewalGeometry
