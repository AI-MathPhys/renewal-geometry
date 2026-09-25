/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact all-cutoff transverse rank and natural-order bounds
  (`thm:supp-exact-transverse`, `eq:supp-exact-transverse-space`,
  `eq:supp-exact-transverse-source`, `eq:supp-exact-transverse-rank`,
  `eq:supp-exact-transverse-bounds`, `eq:supp-exact-transverse-positive`;
  emergent-spacetime manuscript)

The paper defines the odd-grid phase derivatives `δ_i`, the operator
`Ω_h`, and the transverse-shift space `𝒯_h` by their Fourier symbols
(`eq:supp-exact-phase-derivative`, `eq:supp-exact-transverse-space`), and
its proof of the theorem is entirely mode-wise.  We therefore work in the
mode representation: `K` is the finite set of nonzero modes (`|K| = V - 1`
on the grid), `κ k : Fin 3 → ℝ` the real symbol `κ(k) ≠ 0`,
`σ k : Fin 3 → ℂ` the unimodular symbols of the shifts `S_i`, and a shift
is a family of mode amplitudes `b : K → Fin 3 → ℂ` (the zero mode is
absent, which is the condition `β̂(0) = 0`).  Grid `ℓ²` norms are mode sums
(Parseval); this identification of the grid operators with their symbols is
the only step not formalised here.

* `IsTransverse`, `transverseSpace`: `κ(k)ᵀ β̂(k) = 0` for all `k`;
  `finrank_transverseSpace`: `dim 𝒯_h = 2 |K|` (`= 2(V-1)`).
* `curlMode`: the mode `i κ(k) × β̂(k)` of `curl_δ β`;
  `vecNormSq_curlMode_of_transverse`: `‖curl_δ β‖ = ‖Ω_h β‖` on transverse
  modes (Lagrange identity).
* `offDiag`: the zero-diagonal symmetric matrix `(ℒ_h w)_{ij} = S_i w_j + S_j w_i`
  at one mode; `frobSq_offDiag_eq`, `frobSq_offDiag_bounds`: its Gram form is
  unitarily `w ↦ (w₁+w₂, w₁+w₃, w₂+w₃)` with squared singular values
  `4, 1, 1`, giving `2‖w‖² ≤ ‖ℒ_h w‖_F² ≤ 8‖w‖²`.
* `sourceMode`, `sourceMap`: the transverse source
  `A_h β = -(h ϰ_h/2) ℒ_h(-½ curl_δ β)` (`eq:supp-exact-transverse-source`).
* `sourceMode_frobSq_bounds`, `source_bounds`, `source_bounds_weighted`:
  the boxed two-sided estimate `c h² ‖Ω_h β‖² ≤ ‖A_h β‖² ≤ C h² ‖Ω_h β‖²`
  with `c = ϰlo²/8`, `C = ϰhi²/2` for `ϰlo ≤ ϰ_h ≤ ϰhi`, also after any scalar
  Fourier Sobolev weight.
* `trace_sourceMode`: `𝖯_tr A_h = 0`; `finrank_range_source`:
  `rank A_h = dim 𝒯_h = 2|K|` (injectivity from the lower bound).
* `dewittInvK0`, `dewittInvK0_of_trace_zero`, `gram_signed_eq_half`,
  `gram_pos`: `K₀⁻¹ = ½ I - ¾ 𝖯_tr` acts by `½` on the trace-free range, so
  `A_h^* K₀⁻¹ A_h = ½ A_h^* A_h ≻ 0` on `𝒯_h`.
-/

namespace RenewalGeometry
namespace ExactTransverse

open Complex Matrix Finset ComplexConjugate

noncomputable section

/-! ### One mode -/

/-- Complex cast of a real 3-vector. -/
def toC (κ : Fin 3 → ℝ) : Fin 3 → ℂ := fun i => (κ i : ℂ)

/-- Squared `ℓ²` norm of a complex 3-vector. -/
def vecNormSq (w : Fin 3 → ℂ) : ℝ := ∑ i, normSq (w i)

/-- Squared Euclidean norm of a real 3-vector. -/
def realNormSq (κ : Fin 3 → ℝ) : ℝ := ∑ i, κ i ^ 2

theorem vecNormSq_nonneg (w : Fin 3 → ℂ) : 0 ≤ vecNormSq w :=
  Finset.sum_nonneg fun _ _ => normSq_nonneg _

theorem realNormSq_nonneg (κ : Fin 3 → ℝ) : 0 ≤ realNormSq κ :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem realNormSq_pos {κ : Fin 3 → ℝ} (hκ : κ ≠ 0) : 0 < realNormSq κ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hκ
  have hi : κ i ≠ 0 := by simpa using hi
  unfold realNormSq
  exact lt_of_lt_of_le (by positivity)
    (Finset.single_le_sum (fun j _ => sq_nonneg (κ j)) (Finset.mem_univ i))

theorem vecNormSq_eq_zero {w : Fin 3 → ℂ} (h : vecNormSq w = 0) : w = 0 := by
  unfold vecNormSq at h
  funext i
  exact normSq_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg fun j _ => normSq_nonneg (w j)).mp h i (Finset.mem_univ i))

theorem vecNormSq_smul (c : ℂ) (w : Fin 3 → ℂ) : vecNormSq (c • w) = normSq c * vecNormSq w := by
  unfold vecNormSq
  simp [normSq_mul, Finset.mul_sum]

/-- The mode of `curl_δ β`: `i κ(k) × β̂(k)`. -/
def curlMode (κ : Fin 3 → ℝ) (w : Fin 3 → ℂ) : Fin 3 → ℂ :=
  I • (toC κ ⨯₃ w)

/-- Lagrange identity on a transverse mode: `|κ × w|² = |κ|² |w|²` when
`κ · w = 0` (`κ` real). -/
theorem vecNormSq_cross_of_transverse (κ : Fin 3 → ℝ) (w : Fin 3 → ℂ)
    (hw : ∑ i, (κ i : ℂ) * w i = 0) :
    vecNormSq (toC κ ⨯₃ w) = realNormSq κ * vecNormSq w := by
  have hre := congrArg Complex.re hw
  have him := congrArg Complex.im hw
  simp only [Fin.sum_univ_three, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.zero_re,
    Complex.zero_im] at hre him
  simp only [vecNormSq, realNormSq, cross_apply, toC, Fin.sum_univ_three, normSq_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead,
    Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  linear_combination (-(κ 0 * (w 0).re + κ 1 * (w 1).re + κ 2 * (w 2).re)) * hre
    + (-(κ 0 * (w 0).im + κ 1 * (w 1).im + κ 2 * (w 2).im)) * him

/-- `‖curl_δ β‖ = ‖Ω_h β‖` on a transverse mode. -/
theorem vecNormSq_curlMode_of_transverse (κ : Fin 3 → ℝ) (w : Fin 3 → ℂ)
    (hw : ∑ i, (κ i : ℂ) * w i = 0) :
    vecNormSq (curlMode κ w) = realNormSq κ * vecNormSq w := by
  unfold curlMode
  rw [vecNormSq_smul, normSq_I, one_mul, vecNormSq_cross_of_transverse κ w hw]

/-- The zero-diagonal symmetric matrix `(ℒ_h w)_{ij} = S_i w_j + S_j w_i` at one
mode, with `S_i` acting by the unimodular symbol `σ i`. -/
def offDiag (σ w : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of fun i j => if i = j then 0 else σ i * w j + σ j * w i

/-- Squared Frobenius norm. -/
def frobSq (M : Matrix (Fin 3) (Fin 3) ℂ) : ℝ := ∑ i, ∑ j, normSq (M i j)

theorem frobSq_nonneg (M : Matrix (Fin 3) (Fin 3) ℂ) : 0 ≤ frobSq M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => normSq_nonneg _

theorem frobSq_smul (c : ℂ) (M : Matrix (Fin 3) (Fin 3) ℂ) :
    frobSq (c • M) = normSq c * frobSq M := by
  unfold frobSq
  simp [normSq_mul, Finset.mul_sum]

theorem offDiag_add (σ v w : Fin 3 → ℂ) : offDiag σ (v + w) = offDiag σ v + offDiag σ w := by
  ext i j
  by_cases hij : i = j
  · simp [offDiag, hij]
  · simp only [offDiag, Matrix.of_apply, Matrix.add_apply, Pi.add_apply, if_neg hij]; ring

theorem offDiag_smul (σ : Fin 3 → ℂ) (c : ℂ) (w : Fin 3 → ℂ) :
    offDiag σ (c • w) = c • offDiag σ w := by
  ext i j
  by_cases hij : i = j
  · simp [offDiag, hij]
  · simp only [offDiag, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
      if_neg hij]
    ring

theorem trace_offDiag (σ w : Fin 3 → ℂ) : (offDiag σ w).trace = 0 := by
  simp [Matrix.trace, Matrix.diag, offDiag]

theorem offDiag_apply_self (σ w : Fin 3 → ℂ) (i : Fin 3) : offDiag σ w i i = 0 := by
  simp [offDiag]

theorem offDiag_apply_ne (σ w : Fin 3 → ℂ) {i j : Fin 3} (hij : i ≠ j) :
    offDiag σ w i j = σ i * w j + σ j * w i := by
  simp [offDiag, hij]

/-- The Gram identity of the off-diagonal map: with `u_i = conj(σ_i) w_i`,
`‖ℒ_h w‖_F² = 2 (‖u‖² + |u₁ + u₂ + u₃|²)`, i.e. the map is unitarily
`w ↦ (w₁+w₂, w₁+w₃, w₂+w₃)` whose Gram matrix has eigenvalues `4, 1, 1`. -/
theorem frobSq_offDiag_eq (σ w : Fin 3 → ℂ) (hσ : ∀ i, normSq (σ i) = 1) :
    frobSq (offDiag σ w)
      = 2 * (vecNormSq w + normSq (∑ i, conj (σ i) * w i)) := by
  have hunit : ∀ i, σ i * conj (σ i) = 1 := fun i => by
    rw [Complex.mul_conj, hσ i, Complex.ofReal_one]
  have key : ∀ i j, σ i * w j + σ j * w i
      = σ i * σ j * (conj (σ i) * w i + conj (σ j) * w j) := by
    intro i j
    linear_combination (-(σ j * w i)) * hunit i + (-(σ i * w j)) * hunit j
  have hnorm : ∀ i j, i ≠ j → normSq (σ i * w j + σ j * w i)
      = normSq (conj (σ i) * w i + conj (σ j) * w j) := by
    intro i j _
    rw [key, normSq_mul, normSq_mul, hσ i, hσ j]; ring
  have hu : ∀ i, normSq (conj (σ i) * w i) = normSq (w i) := fun i => by
    rw [normSq_mul, normSq_conj, hσ i, one_mul]
  -- expand the Frobenius sum over the six off-diagonal entries
  have hexp : frobSq (offDiag σ w)
      = normSq (conj (σ 0) * w 0 + conj (σ 1) * w 1)
        + normSq (conj (σ 0) * w 0 + conj (σ 2) * w 2)
        + normSq (conj (σ 1) * w 1 + conj (σ 0) * w 0)
        + normSq (conj (σ 1) * w 1 + conj (σ 2) * w 2)
        + normSq (conj (σ 2) * w 2 + conj (σ 0) * w 0)
        + normSq (conj (σ 2) * w 2 + conj (σ 1) * w 1) := by
    simp only [frobSq, Fin.sum_univ_three, offDiag_apply_self, normSq_zero,
      offDiag_apply_ne σ w (show (0 : Fin 3) ≠ 1 by decide),
      offDiag_apply_ne σ w (show (0 : Fin 3) ≠ 2 by decide),
      offDiag_apply_ne σ w (show (1 : Fin 3) ≠ 0 by decide),
      offDiag_apply_ne σ w (show (1 : Fin 3) ≠ 2 by decide),
      offDiag_apply_ne σ w (show (2 : Fin 3) ≠ 0 by decide),
      offDiag_apply_ne σ w (show (2 : Fin 3) ≠ 1 by decide)]
    rw [hnorm 0 1 (by decide), hnorm 0 2 (by decide), hnorm 1 0 (by decide),
      hnorm 1 2 (by decide), hnorm 2 0 (by decide), hnorm 2 1 (by decide)]
    ring
  rw [hexp]
  unfold vecNormSq
  simp only [Fin.sum_univ_three, ← hu]
  set u0 := conj (σ 0) * w 0
  set u1 := conj (σ 1) * w 1
  set u2 := conj (σ 2) * w 2
  simp only [normSq_apply, Complex.add_re, Complex.add_im]
  ring

/-- `|u₁ + u₂ + u₃|² ≤ 3 (|u₁|² + |u₂|² + |u₃|²)`. -/
theorem normSq_sum_three_le (u : Fin 3 → ℂ) :
    normSq (∑ i, u i) ≤ 3 * ∑ i, normSq (u i) := by
  simp only [Fin.sum_univ_three, normSq_apply, Complex.add_re, Complex.add_im]
  nlinarith [sq_nonneg ((u 0).re - (u 1).re), sq_nonneg ((u 0).re - (u 2).re),
    sq_nonneg ((u 1).re - (u 2).re), sq_nonneg ((u 0).im - (u 1).im),
    sq_nonneg ((u 0).im - (u 2).im), sq_nonneg ((u 1).im - (u 2).im)]

/-- Singular value bounds of the off-diagonal map: `2‖w‖² ≤ ‖ℒ_h w‖_F² ≤ 8‖w‖²`. -/
theorem frobSq_offDiag_bounds (σ w : Fin 3 → ℂ) (hσ : ∀ i, normSq (σ i) = 1) :
    2 * vecNormSq w ≤ frobSq (offDiag σ w) ∧ frobSq (offDiag σ w) ≤ 8 * vecNormSq w := by
  rw [frobSq_offDiag_eq σ w hσ]
  have h1 := normSq_nonneg (∑ i, conj (σ i) * w i)
  have h2 := normSq_sum_three_le fun i => conj (σ i) * w i
  have hu : ∑ i, normSq (conj (σ i) * w i) = vecNormSq w := by
    unfold vecNormSq
    exact Finset.sum_congr rfl fun i _ => by rw [normSq_mul, normSq_conj, hσ i, one_mul]
  rw [hu] at h2
  constructor <;> linarith

/-- The transverse source at one mode,
`A_h β = -(h ϰ_h/2) ℒ_h(-½ curl_δ β)` (`eq:supp-exact-transverse-source`). -/
def sourceMode (h ϰ : ℝ) (κ : Fin 3 → ℝ) (σ w : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  ((-(h * ϰ / 2) : ℝ) : ℂ) • offDiag σ ((-1 / 2 : ℂ) • curlMode κ w)

/-- The output diagonal vanishes: `𝖯_tr A_h = 0`. -/
theorem trace_sourceMode (h ϰ : ℝ) (κ : Fin 3 → ℝ) (σ w : Fin 3 → ℂ) :
    (sourceMode h ϰ κ σ w).trace = 0 := by
  unfold sourceMode
  rw [Matrix.trace_smul, trace_offDiag, smul_zero]

/-- The boxed two-sided estimate at one mode:
`(h² ϰ²/8) |κ|² |w|² ≤ ‖A_h w‖_F² ≤ (h² ϰ²/2) |κ|² |w|²` for a transverse mode. -/
theorem sourceMode_frobSq_bounds (h ϰ : ℝ) (κ : Fin 3 → ℝ) (σ w : Fin 3 → ℂ)
    (hσ : ∀ i, normSq (σ i) = 1) (hw : ∑ i, (κ i : ℂ) * w i = 0) :
    h ^ 2 * ϰ ^ 2 / 8 * (realNormSq κ * vecNormSq w) ≤ frobSq (sourceMode h ϰ κ σ w) ∧
    frobSq (sourceMode h ϰ κ σ w) ≤ h ^ 2 * ϰ ^ 2 / 2 * (realNormSq κ * vecNormSq w) := by
  unfold sourceMode
  rw [frobSq_smul, offDiag_smul, frobSq_smul, normSq_ofReal]
  have hhalf : normSq (-1 / 2 : ℂ) = 1 / 4 := by
    rw [show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by push_cast; ring, normSq_ofReal]; norm_num
  rw [hhalf]
  obtain ⟨hlo, hhi⟩ := frobSq_offDiag_bounds σ (curlMode κ w) hσ
  rw [vecNormSq_curlMode_of_transverse κ w hw] at hlo hhi
  have hf := frobSq_nonneg (offDiag σ (curlMode κ w))
  have hhk : 0 ≤ (-(h * ϰ / 2)) * (-(h * ϰ / 2)) := mul_self_nonneg _
  constructor
  · nlinarith
  · nlinarith

/-! ### All modes -/

variable {K : Type*} [Fintype K]

/-- Mode-wise transversality `κ(k)ᵀ β̂(k) = 0` (`eq:supp-exact-transverse-space`). -/
def IsTransverse (κ : K → Fin 3 → ℝ) (b : K → Fin 3 → ℂ) : Prop :=
  ∀ k, ∑ i, (κ k i : ℂ) * b k i = 0

/-- The functional `b ↦ (κ(k)ᵀ b(k))_k`. -/
def dotMap (κ : K → Fin 3 → ℝ) : (K → Fin 3 → ℂ) →ₗ[ℂ] (K → ℂ) where
  toFun b := fun k => ∑ i, (κ k i : ℂ) * b k i
  map_add' b c := by
    funext k
    simp [Finset.sum_add_distrib, mul_add]
  map_smul' c b := by
    funext k
    simp [Finset.mul_sum, mul_left_comm]

/-- The transverse-shift space `𝒯_h` in mode representation. -/
def transverseSpace (κ : K → Fin 3 → ℝ) : Submodule ℂ (K → Fin 3 → ℂ) :=
  LinearMap.ker (dotMap κ)

omit [Fintype K] in
theorem mem_transverseSpace {κ : K → Fin 3 → ℝ} {b : K → Fin 3 → ℂ} :
    b ∈ transverseSpace κ ↔ IsTransverse κ b := by
  simp only [transverseSpace, LinearMap.mem_ker, IsTransverse, dotMap, LinearMap.coe_mk,
    AddHom.coe_mk]
  exact funext_iff

omit [Fintype K] in
theorem dotMap_surjective (κ : K → Fin 3 → ℝ) (hκ : ∀ k, κ k ≠ 0) :
    Function.Surjective (dotMap κ) := by
  intro t
  refine ⟨fun k => (t k / (realNormSq (κ k) : ℂ)) • toC (κ k), ?_⟩
  funext k
  simp only [dotMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul, toC]
  have hpos : (realNormSq (κ k) : ℂ) ≠ 0 := by
    exact_mod_cast (realNormSq_pos (hκ k)).ne'
  have : ∑ i, (κ k i : ℂ) * (t k / (realNormSq (κ k) : ℂ) * (κ k i : ℂ))
      = t k / (realNormSq (κ k) : ℂ) * (realNormSq (κ k) : ℂ) := by
    unfold realNormSq
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this, div_mul_cancel₀ _ hpos]

/-- `dim 𝒯_h = 2 |K|`, i.e. `2(V-1)` for the `V - 1` nonzero modes
(`eq:supp-exact-transverse-space`). -/
theorem finrank_transverseSpace (κ : K → Fin 3 → ℝ) (hκ : ∀ k, κ k ≠ 0) :
    Module.finrank ℂ (transverseSpace κ) = 2 * Fintype.card K := by
  have h := LinearMap.finrank_range_add_finrank_ker (dotMap κ)
  rw [LinearMap.range_eq_top.mpr (dotMap_surjective κ hκ), finrank_top] at h
  have h1 : Module.finrank ℂ (K → ℂ) = Fintype.card K := Module.finrank_pi ℂ
  have h2 : Module.finrank ℂ (K → Fin 3 → ℂ) = 3 * Fintype.card K := by
    rw [Module.finrank_pi_fintype]
    simp [mul_comm]
  unfold transverseSpace
  omega

/-- `‖Ω_h β‖² = ∑_k |κ(k)|² |β̂(k)|²` (with an optional scalar Fourier weight `wt`). -/
def omegaNormSq (wt : K → ℝ) (κ : K → Fin 3 → ℝ) (b : K → Fin 3 → ℂ) : ℝ :=
  ∑ k, wt k * (realNormSq (κ k) * vecNormSq (b k))

/-- The transverse source `A_h` as a linear map on mode families. -/
def sourceMap (h ϰ : ℝ) (κ : K → Fin 3 → ℝ) (σ : K → Fin 3 → ℂ) :
    (K → Fin 3 → ℂ) →ₗ[ℂ] (K → Matrix (Fin 3) (Fin 3) ℂ) where
  toFun b := fun k => sourceMode h ϰ (κ k) (σ k) (b k)
  map_add' b c := by
    funext k
    simp only [sourceMode, curlMode, Pi.add_apply, map_add, smul_add, offDiag_add]
  map_smul' c b := by
    funext k
    simp only [sourceMode, curlMode, Pi.smul_apply, map_smul, RingHom.id_apply, smul_comm c,
      offDiag_smul]

/-- `‖A_h β‖² = ∑_k ‖(A_h β)(k)‖_F²` with an optional scalar weight. -/
def sourceNormSq (wt : K → ℝ) (h ϰ : ℝ) (κ : K → Fin 3 → ℝ) (σ : K → Fin 3 → ℂ)
    (b : K → Fin 3 → ℂ) : ℝ :=
  ∑ k, wt k * frobSq (sourceMap h ϰ κ σ b k)

/-- **`eq:supp-exact-transverse-bounds`, weighted.** For `β ∈ 𝒯_h`,
unimodular shift symbols and `0 < ϰlo ≤ ϰ_h ≤ ϰhi`, after multiplication by
any nonnegative scalar Fourier Sobolev weight `wt`,
`(ϰlo²/8) h² ‖Ω_h β‖² ≤ ‖A_h β‖² ≤ (ϰhi²/2) h² ‖Ω_h β‖²`. -/
theorem source_bounds_weighted (wt : K → ℝ) (hwt : ∀ k, 0 ≤ wt k) (h ϰ ϰlo ϰhi : ℝ)
    (hϰlo : 0 ≤ ϰlo) (hlo : ϰlo ≤ ϰ) (hhi : ϰ ≤ ϰhi)
    (κ : K → Fin 3 → ℝ) (σ : K → Fin 3 → ℂ) (hσ : ∀ k i, normSq (σ k i) = 1)
    (b : K → Fin 3 → ℂ) (hb : IsTransverse κ b) :
    ϰlo ^ 2 / 8 * h ^ 2 * omegaNormSq wt κ b ≤ sourceNormSq wt h ϰ κ σ b ∧
    sourceNormSq wt h ϰ κ σ b ≤ ϰhi ^ 2 / 2 * h ^ 2 * omegaNormSq wt κ b := by
  have hϰsq_lo : ϰlo ^ 2 ≤ ϰ ^ 2 := by nlinarith
  have hϰsq_hi : ϰ ^ 2 ≤ ϰhi ^ 2 := by nlinarith
  unfold omegaNormSq sourceNormSq
  rw [Finset.mul_sum, Finset.mul_sum]
  constructor
  · refine Finset.sum_le_sum fun k _ => ?_
    obtain ⟨h1, -⟩ := sourceMode_frobSq_bounds h ϰ (κ k) (σ k) (b k) (hσ k) (hb k)
    have hm : 0 ≤ realNormSq (κ k) * vecNormSq (b k) :=
      mul_nonneg (realNormSq_nonneg _) (vecNormSq_nonneg _)
    have : ϰlo ^ 2 / 8 * h ^ 2 * (realNormSq (κ k) * vecNormSq (b k))
        ≤ h ^ 2 * ϰ ^ 2 / 8 * (realNormSq (κ k) * vecNormSq (b k)) := by
      apply mul_le_mul_of_nonneg_right _ hm
      nlinarith [sq_nonneg h]
    calc ϰlo ^ 2 / 8 * h ^ 2 * (wt k * (realNormSq (κ k) * vecNormSq (b k)))
        = wt k * (ϰlo ^ 2 / 8 * h ^ 2 * (realNormSq (κ k) * vecNormSq (b k))) := by ring
      _ ≤ wt k * frobSq (sourceMap h ϰ κ σ b k) :=
          mul_le_mul_of_nonneg_left (this.trans h1) (hwt k)
  · refine Finset.sum_le_sum fun k _ => ?_
    obtain ⟨-, h2⟩ := sourceMode_frobSq_bounds h ϰ (κ k) (σ k) (b k) (hσ k) (hb k)
    have hm : 0 ≤ realNormSq (κ k) * vecNormSq (b k) :=
      mul_nonneg (realNormSq_nonneg _) (vecNormSq_nonneg _)
    have : h ^ 2 * ϰ ^ 2 / 2 * (realNormSq (κ k) * vecNormSq (b k))
        ≤ ϰhi ^ 2 / 2 * h ^ 2 * (realNormSq (κ k) * vecNormSq (b k)) := by
      apply mul_le_mul_of_nonneg_right _ hm
      nlinarith [sq_nonneg h]
    calc wt k * frobSq (sourceMap h ϰ κ σ b k)
        ≤ wt k * (ϰhi ^ 2 / 2 * h ^ 2 * (realNormSq (κ k) * vecNormSq (b k))) :=
          mul_le_mul_of_nonneg_left (h2.trans this) (hwt k)
      _ = ϰhi ^ 2 / 2 * h ^ 2 * (wt k * (realNormSq (κ k) * vecNormSq (b k))) := by ring

/-- **`eq:supp-exact-transverse-bounds`.** The unweighted boxed estimate
`c h² ‖Ω_h β‖² ≤ ‖A_h β‖² ≤ C h² ‖Ω_h β‖²`, `β ∈ 𝒯_h`, with
`c = ϰlo²/8`, `C = ϰhi²/2`. -/
theorem source_bounds (h ϰ ϰlo ϰhi : ℝ) (hϰlo : 0 ≤ ϰlo) (hlo : ϰlo ≤ ϰ) (hhi : ϰ ≤ ϰhi)
    (κ : K → Fin 3 → ℝ) (σ : K → Fin 3 → ℂ) (hσ : ∀ k i, normSq (σ k i) = 1)
    (b : K → Fin 3 → ℂ) (hb : IsTransverse κ b) :
    ϰlo ^ 2 / 8 * h ^ 2 * omegaNormSq (fun _ => 1) κ b ≤ sourceNormSq (fun _ => 1) h ϰ κ σ b ∧
    sourceNormSq (fun _ => 1) h ϰ κ σ b ≤ ϰhi ^ 2 / 2 * h ^ 2 * omegaNormSq (fun _ => 1) κ b :=
  source_bounds_weighted (fun _ => 1) (fun _ => zero_le_one) h ϰ ϰlo ϰhi hϰlo hlo hhi κ σ hσ b hb

theorem omegaNormSq_eq_zero (κ : K → Fin 3 → ℝ) (hκ : ∀ k, κ k ≠ 0) (b : K → Fin 3 → ℂ)
    (h : omegaNormSq (fun _ => 1) κ b = 0) : b = 0 := by
  unfold omegaNormSq at h
  simp only [one_mul] at h
  funext k
  have hk := (Finset.sum_eq_zero_iff_of_nonneg fun k _ =>
    mul_nonneg (realNormSq_nonneg (κ k)) (vecNormSq_nonneg (b k))).mp h k (Finset.mem_univ k)
  rcases mul_eq_zero.mp hk with h0 | h0
  · exact absurd h0 (realNormSq_pos (hκ k)).ne'
  · exact vecNormSq_eq_zero h0

/-- Injectivity of `A_h` on `𝒯_h` (from the lower bound, `h ≠ 0`, `ϰ ≠ 0`). -/
theorem source_injective_on_transverse (h ϰ : ℝ) (hh : h ≠ 0) (hϰ : 0 < ϰ)
    (κ : K → Fin 3 → ℝ) (hκ : ∀ k, κ k ≠ 0) (σ : K → Fin 3 → ℂ)
    (hσ : ∀ k i, normSq (σ k i) = 1) :
    Function.Injective ((sourceMap h ϰ κ σ).domRestrict (transverseSpace κ)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨b, hb⟩ hzero
  have hb' : IsTransverse κ b := mem_transverseSpace.mp hb
  have hAb : sourceMap h ϰ κ σ b = 0 := hzero
  have hnorm : sourceNormSq (fun _ => 1) h ϰ κ σ b = 0 := by
    unfold sourceNormSq
    rw [hAb]
    simp [frobSq]
  obtain ⟨hlo, -⟩ := source_bounds h ϰ ϰ ϰ hϰ.le le_rfl le_rfl κ σ hσ b hb'
  rw [hnorm] at hlo
  have hpos : 0 < ϰ ^ 2 / 8 * h ^ 2 := by positivity
  have hΩ0 : 0 ≤ omegaNormSq (fun _ => 1) κ b := by
    unfold omegaNormSq
    exact Finset.sum_nonneg fun k _ => by
      have := mul_nonneg (realNormSq_nonneg (κ k)) (vecNormSq_nonneg (b k)); positivity
  have hΩ : omegaNormSq (fun _ => 1) κ b = 0 := by
    by_contra hne
    have : 0 < omegaNormSq (fun _ => 1) κ b := lt_of_le_of_ne hΩ0 (Ne.symm hne)
    nlinarith
  have := omegaNormSq_eq_zero κ hκ b hΩ
  exact Subtype.ext this

/-- **`eq:supp-exact-transverse-rank`.** `rank A_h = dim 𝒯_h = 2 |K|`
(`= 2(V-1)`). -/
theorem finrank_range_source (h ϰ : ℝ) (hh : h ≠ 0) (hϰ : 0 < ϰ)
    (κ : K → Fin 3 → ℝ) (hκ : ∀ k, κ k ≠ 0) (σ : K → Fin 3 → ℂ)
    (hσ : ∀ k i, normSq (σ k i) = 1) :
    Module.finrank ℂ (LinearMap.range ((sourceMap h ϰ κ σ).domRestrict (transverseSpace κ)))
      = 2 * Fintype.card K := by
  rw [LinearMap.finrank_range_of_inj (source_injective_on_transverse h ϰ hh hϰ κ hκ σ hσ),
    finrank_transverseSpace κ hκ]

/-! ### The signed Gram form -/

/-- The trace projection `𝖯_tr S = (tr S / 3) I`. -/
def traceProj (S : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  (S.trace / 3) • (1 : Matrix (Fin 3) (Fin 3) ℂ)

/-- `K₀⁻¹ = ½ I - ¾ 𝖯_tr` (the inverse DeWitt kinetic block of the paper). -/
def dewittInvK0 (S : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  (1 / 2 : ℂ) • S - (3 / 4 : ℂ) • traceProj S

/-- `K₀⁻¹` acts by `½` on trace-free matrices. -/
theorem dewittInvK0_of_trace_zero (S : Matrix (Fin 3) (Fin 3) ℂ) (hS : S.trace = 0) :
    dewittInvK0 S = (1 / 2 : ℂ) • S := by
  unfold dewittInvK0 traceProj
  rw [hS]; simp

/-- Frobenius pairing `⟨M, N⟩ = ∑ conj(M_ij) N_ij`. -/
def frobInner (M N : Matrix (Fin 3) (Fin 3) ℂ) : ℂ :=
  ∑ i, ∑ j, conj (M i j) * N i j

theorem frobInner_self (M : Matrix (Fin 3) (Fin 3) ℂ) : frobInner M M = (frobSq M : ℂ) := by
  unfold frobInner frobSq
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, Complex.mul_conj]

/-- **`eq:supp-exact-transverse-positive`, identity.** The signed Gram form
`⟨A_h β, K₀⁻¹ A_h β⟩ = ½ ‖A_h β‖²`, i.e. `A_h^* K₀⁻¹ A_h = ½ A_h^* A_h`,
because the range of `A_h` is trace-free. -/
theorem gram_signed_eq_half (h ϰ : ℝ) (κ : K → Fin 3 → ℝ) (σ : K → Fin 3 → ℂ)
    (b : K → Fin 3 → ℂ) :
    ∑ k, frobInner (sourceMap h ϰ κ σ b k) (dewittInvK0 (sourceMap h ϰ κ σ b k))
      = (1 / 2 : ℂ) * (sourceNormSq (fun _ => 1) h ϰ κ σ b : ℂ) := by
  unfold sourceNormSq
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have htr : ((sourceMap h ϰ κ σ) b k).trace = 0 := trace_sourceMode h ϰ (κ k) (σ k) (b k)
  rw [dewittInvK0_of_trace_zero _ htr, one_mul, ← frobInner_self]
  unfold frobInner
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **`eq:supp-exact-transverse-positive`, positivity.** `A_h^* A_h ≻ 0` on
`𝒯_h`: `‖A_h β‖² > 0` for every nonzero transverse `β`. -/
theorem gram_pos (h ϰ : ℝ) (hh : h ≠ 0) (hϰ : 0 < ϰ)
    (κ : K → Fin 3 → ℝ) (hκ : ∀ k, κ k ≠ 0) (σ : K → Fin 3 → ℂ)
    (hσ : ∀ k i, normSq (σ k i) = 1) (b : K → Fin 3 → ℂ) (hb : IsTransverse κ b)
    (hb0 : b ≠ 0) :
    0 < sourceNormSq (fun _ => 1) h ϰ κ σ b := by
  obtain ⟨hlo, -⟩ := source_bounds h ϰ ϰ ϰ hϰ.le le_rfl le_rfl κ σ hσ b hb
  have hΩ0 : 0 ≤ omegaNormSq (fun _ => 1) κ b := by
    unfold omegaNormSq
    exact Finset.sum_nonneg fun k _ => by
      have := mul_nonneg (realNormSq_nonneg (κ k)) (vecNormSq_nonneg (b k)); positivity
  have hΩ : omegaNormSq (fun _ => 1) κ b ≠ 0 := fun h0 => hb0 (omegaNormSq_eq_zero κ hκ b h0)
  have hΩpos : 0 < omegaNormSq (fun _ => 1) κ b := lt_of_le_of_ne hΩ0 (Ne.symm hΩ)
  have hpos : 0 < ϰ ^ 2 / 8 * h ^ 2 := by positivity
  calc (0 : ℝ) < ϰ ^ 2 / 8 * h ^ 2 * omegaNormSq (fun _ => 1) κ b := by positivity
    _ ≤ _ := hlo

end

end ExactTransverse
end RenewalGeometry
