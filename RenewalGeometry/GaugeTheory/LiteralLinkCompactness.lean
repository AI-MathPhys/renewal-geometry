/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.GaugeTheory.LiteralLinkEvolution
import RenewalGeometry.Continuum.PeriodicGridAubinLions

/-!
# Strong compactness of literal-link coordinates
  (infrastructure for `thm:main-literal-link-compactness`; emergent-spacetime manuscript)

Complex `n × n` matrix arrays on the periodic grid `(ℤ/N)³` (`h = 1/N`, Frobenius coefficient
norm), as in `LiteralLink`.

* `dft_synth`, `gridInner_synth`: Fourier synthesis on the grid.
* `sum_inv_gridWeight_le_negSobNorm2_sq`: the dual `H_h^{-2}` norm `negSobNorm2` of
  `lem:supp-literal-link-evolution` dominates the Fourier form `Σ_{a,b,k} w₂(k)⁻¹ |û_{ab}(k)|²`
  (optimal test array by synthesis).
* `gridWeight_two_le`, `trigNegSq_two_interp_le`: uniformly in `N`, the trigonometric
  `H^{-2}(𝕋³)` norm of the interpolant is at most `#{|α| ≤ 2}` times that Fourier form.
* `matArr_aubinLions`: matrix arrays with `W^{1,2}` entries, bounded in `L²_t H¹_h`, with time
  derivative bounded in `L²_t H_h^{-2}` have entrywise interpolants converging strongly in
  `L²((0,T] × 𝕋³)` along a subsequence (the `Z_h` compactness step of the paper's proof).
* `sum_norm_pow_four_le` (uniform discrete `L⁴` bound from the product estimate) and
  `matNormSq_sub_le_of_chart`: the logarithmic chart error
  `‖Z - A‖_h² ≤ C² δ h · n√K · ‖A‖_h · ‖A‖²_{1,h}` (`eq:supp-literal-log-error`, with an `L³`
  interpolation replacing the paper's `L^{10/3}` one).
-/

open MeasureTheory Filter Topology Set

noncomputable section

set_option linter.unusedSectionVars false

namespace RenewalGeometry.LiteralLinkCompactness

open PeriodicGridSobolev LatticeTorusPlancherel LiteralLink GridAubinLions
open scoped ComplexConjugate Matrix.Norms.Frobenius

variable {N : ℕ} [NeZero N] {n : ℕ}

/-! ### Fourier synthesis and the dual `H_h^{-2}` norm -/

/-- Fourier synthesis on the grid: the array `x ↦ Σ_k e(k·x) c(k)` has DFT `c`. -/
theorem dft_synth (c : Grid N → ℂ) (ℓ : Grid N) :
    dft (fun x => ∑ k, latticeChar k x * c k) ℓ = c ℓ := by
  have hn : ((N : ℂ) ^ 3) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne N))
  unfold dft
  simp only [smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hrow : ∀ k : Grid N, ∑ x : Grid N, (conj (latticeChar ℓ x) * (latticeChar k x * c k)) =
      (∑ x : Grid N, latticeChar x (k - ℓ)) * c k := by
    intro k
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [latticeChar_sub_right, latticeChar_comm k x, latticeChar_comm ℓ x]
    ring
  simp only [← Finset.mul_sum, hrow, sum_latticeChar, sub_eq_zero]
  rw [Finset.sum_eq_single ℓ]
  · simp [hn]
  · intro k _ hk
    simp [hk]
  · simp

/-- The grid inner product against a synthesized array: `⟨Σ_k e_k c_k, g⟩_h = Σ_k conj(c_k) ĝ(k)`. -/
theorem gridInner_synth (c g : Grid N → ℂ) :
    gridInner (fun x => ∑ k, latticeChar k x * c k) g = ∑ k, conj (c k) * dft g k := by
  unfold gridInner dft
  simp only [map_sum, map_mul, Finset.sum_mul, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun x _ => ?_
  ring

theorem norm_matPair_le_matNorm (φ u : MatArr N n) : ‖matPair φ u‖ ≤ matNorm φ * matNorm u := by
  refine (norm_matPair_le φ u).trans ?_
  rw [matNorm_eq, matNorm_eq]
  have := grid_cs (N := N) (fun x => ‖φ x‖) (fun x => ‖u x‖)
  simpa using this

/-- **Fourier lower bound for the dual norm**: the dual grid norm `‖u‖_{H_h^{-2}}` dominates the
Fourier-weighted norm `Σ_{a,b} Σ_k w₂(k)⁻¹ |û_{ab}(k)|²` (`w₂` the `H_h²` symbol weight). -/
theorem sum_inv_gridWeight_le_negSobNorm2_sq (u : MatArr N n) :
    ∑ a, ∑ b, ∑ k, (gridWeight 2 k)⁻¹ * ‖dft (entry u a b) k‖ ^ 2 ≤ negSobNorm2 u ^ 2 := by
  set S2 := ∑ a, ∑ b, ∑ k, (gridWeight 2 k)⁻¹ * ‖dft (entry u a b) k‖ ^ 2 with hS2def
  have hw : ∀ k : Grid N, 0 < gridWeight 2 k := gridWeight_two_pos
  have hS2 : 0 ≤ S2 := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
    Finset.sum_nonneg fun k _ => mul_nonneg (inv_nonneg.2 (hw k).le) (sq_nonneg _)
  rcases hS2.eq_or_lt with h0 | hpos
  · rw [← h0]; exact sq_nonneg _
  obtain ⟨S, hSdef⟩ : ∃ S, S = Real.sqrt S2 := ⟨_, rfl⟩
  have hS : 0 < S := hSdef ▸ Real.sqrt_pos.2 hpos
  have hSS : S ^ 2 = S2 := hSdef ▸ Real.sq_sqrt hS2
  -- the optimal test array
  obtain ⟨c, hc⟩ : ∃ c : Fin n → Fin n → Grid N → ℂ, c = fun a b k =>
      (((gridWeight 2 k)⁻¹ / S : ℝ) : ℂ) * dft (entry u a b) k := ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : MatArr N n,
      φ = fun x => Matrix.of fun a b => ∑ k, latticeChar k x * c a b k := ⟨_, rfl⟩
  have hent : ∀ a b, entry φ a b = fun x => ∑ k, latticeChar k x * c a b k := fun a b => by
    rw [hφ]; rfl
  have hsob : matSobSq 2 φ = 1 := by
    unfold matSobSq
    simp only [hent, sobSq_eq_weight, dft_synth]
    have e : ∀ a b k, gridWeight 2 k * ‖c a b k‖ ^ 2 =
        (S ^ 2)⁻¹ * ((gridWeight 2 k)⁻¹ * ‖dft (entry u a b) k‖ ^ 2) := by
      intro a b k
      simp only [hc, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (by have := (hw k).le; positivity)]
      have := (hw k).ne'
      field_simp
    simp only [e, ← Finset.mul_sum]
    rw [← hS2def, hSS, inv_mul_cancel₀ hpos.ne']
  have hφ1 : matSobNorm 2 φ ≤ 1 := by rw [matSobNorm, hsob, Real.sqrt_one]
  have hpair : matPair φ u = (S : ℂ) := by
    rw [matPair_eq_sum_gridInner]
    simp only [hent, gridInner_synth]
    have e : ∀ a b k, conj (c a b k) * dft (entry u a b) k =
        ((S⁻¹ * ((gridWeight 2 k)⁻¹ * ‖dft (entry u a b) k‖ ^ 2) : ℝ) : ℂ) := by
      intro a b k
      simp only [hc, map_mul, Complex.conj_ofReal]
      rw [mul_assoc, Complex.conj_mul']
      push_cast
      ring
    simp only [e]
    have hsum : (∑ a, ∑ b, ∑ k, S⁻¹ * ((gridWeight 2 k)⁻¹ * ‖dft (entry u a b) k‖ ^ 2)) = S := by
      simp only [← Finset.mul_sum]
      rw [← hS2def, ← hSS]
      field_simp
    conv_rhs => rw [← hsum]
    push_cast
    rfl
  have hbdd : BddAbove ((fun φ => ‖matPair φ u‖) '' {φ | matSobNorm 2 φ ≤ 1}) := by
    refine ⟨matNorm u, ?_⟩
    rintro _ ⟨ψ, hψ, rfl⟩
    refine (norm_matPair_le_matNorm ψ u).trans ?_
    have h1 := (matNorm_le_matSobNorm_two ψ).trans hψ
    have h2 := matNorm_nonneg u
    nlinarith [matNorm_nonneg ψ]
  have hle : S ≤ negSobNorm2 u := by
    have := le_csSup hbdd ⟨φ, hφ1, rfl⟩
    simp only [hpair, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS] at this
    exact this
  rw [← hSS]
  exact pow_le_pow_left₀ hS.le hle 2

/-! ### Comparison of the grid `H²` weight with the trigonometric weight -/

theorem tsymSq_le_tW_pow (α : Fin 3 → ℕ) (n : Fin 3 → ℤ) : tsymSq α n ≤ tW n ^ deg α := by
  have hle : ∀ i, (2 * Real.pi * n i) ^ 2 ≤ tW n := fun i => by
    have : (2 * Real.pi * n i) ^ 2 ≤ ∑ j, (2 * Real.pi * n j) ^ 2 :=
      Finset.single_le_sum (f := fun j => (2 * Real.pi * n j) ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ i)
    unfold tW; linarith
  rw [tsymSq, deg, pow_add, pow_add]
  have ht : 0 ≤ tW n := (tW_pos n).le
  exact mul_le_mul (mul_le_mul (pow_le_pow_left₀ (sq_nonneg _) (hle 0) _)
    (pow_le_pow_left₀ (sq_nonneg _) (hle 1) _) (pow_nonneg (sq_nonneg _) _)
    (pow_nonneg ht _))
    (pow_le_pow_left₀ (sq_nonneg _) (hle 2) _) (pow_nonneg (sq_nonneg _) _)
    (mul_nonneg (pow_nonneg ht _) (pow_nonneg ht _))

/-- `w₂(k) ≤ #{|α| ≤ 2} (1 + 4π²|k̃|²)²`, uniformly in `N`. -/
theorem gridWeight_two_le (k : Grid N) :
    gridWeight 2 k ≤ ((multiIndices 2).card : ℝ) * tW (freqVec k) ^ 2 := by
  unfold gridWeight
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun α hα => ?_
  refine (norm_dsym_sq_le_tsymSq α k).trans ((tsymSq_le_tW_pow α _).trans ?_)
  exact pow_le_pow_right₀ (one_le_tW _) (mem_multiIndices.1 hα)

theorem card_multiIndices_two_pos : 0 < ((multiIndices 2).card : ℝ) := by
  have : (0 : Fin 3 → ℕ) ∈ multiIndices 2 := mem_multiIndices.2 (by simp [deg])
  exact_mod_cast Finset.card_pos.2 ⟨_, this⟩

/-- The trigonometric `H⁻²(𝕋³)` norm of an interpolant is controlled by the Fourier form of the
dual grid norm. -/
theorem trigNegSq_two_interp_le (w : Grid N → ℂ) :
    trigNegSq 2 (interp w) ≤
      ((multiIndices 2).card : ℝ) * ∑ k, (gridWeight 2 k)⁻¹ * ‖dft w k‖ ^ 2 := by
  rw [trigNegSq_interp, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  have hc := card_multiIndices_two_pos
  have hw := gridWeight_two_pos k
  have ht : 0 < tW (freqVec k) ^ 2 := pow_pos (tW_pos _) 2
  have hle := gridWeight_two_le k
  rw [← div_eq_mul_inv, le_div_iff₀ hw, inv_mul_le_iff₀ ht]
  linarith

/-! ### Strong compactness of matrix arrays bounded in `L²_t H¹_h` with `∂ₜ ∈ L²_t H_h^{-2}` -/

theorem sum_entry_gridNormSq (u : MatArr N n) :
    ∑ ab : Fin n × Fin n, gridNormSq (entry u ab.1 ab.2) = matNormSq u := by
  rw [Fintype.sum_prod_type]; rfl

theorem sum_entry_coordForm (u : MatArr N n) :
    ∑ ab : Fin n × Fin n, coordForm (entry u ab.1 ab.2) = ∑ i, matNormSq (matDp i u) := by
  rw [Fintype.sum_prod_type]
  simp only [coordForm, matNormSq, entry_matDp]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_comm

/-- **Aubin–Lions–Simon for matrix link arrays** (the compactness step of
`thm:main-literal-link-compactness`).  Let `Z m t` be complex `n × n` matrix arrays on the
periodic grids `(ℤ/N_m)³` whose entries are `W^{1,2}(0,T)` in time with derivative `W m t`,
bounded in `L²_t H¹_h` (`∫₀ᵀ ‖Z‖_h² + Σ_i ‖D_i⁺Z‖_h² ≤ B`, Frobenius coefficient norm), with
`∂ₜ Z = W` bounded in `L²_t H_h^{-2}` (dual grid norm `negSobNorm2`).  Then a subsequence of the
entrywise trigonometric interpolants converges strongly in `L²((0,T] × 𝕋³)`. -/
theorem matArr_aubinLions {N : ℕ → ℕ} [∀ m, NeZero (N m)] {T : ℝ} (hT : 0 < T)
    (Z W : ∀ m, ℝ → MatArr (N m) n)
    (hW : ∀ m a b, IsGridW12Rep T (fun t => entry (Z m t) a b) (fun t => entry (W m t) a b))
    {B B1 : ℝ}
    (hB : ∀ m, ∫ t in Ioc 0 T, (matNormSq (Z m t) + ∑ i, matNormSq (matDp i (Z m t))) ≤ B)
    (hWint : ∀ m, IntegrableOn (fun t => negSobNorm2 (W m t) ^ 2) (Ioc 0 T))
    (hB1 : ∀ m, ∫ t in Ioc 0 T, negSobNorm2 (W m t) ^ 2 ≤ B1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Ω : Fin n × Fin n → ℝ × UnitAddTorus (Fin 3) → ℂ, ∀ ab,
      MemLp (Ω ab) 2 (cylMeasure T) ∧
      Tendsto (fun m => ∫ p, ‖field (fun t => entry (Z (φ m) t) ab.1 ab.2) p - Ω ab p‖ ^ 2
        ∂cylMeasure T) atTop (𝓝 0) := by
  have hB' : ∀ m, ∫ t in Ioc 0 T, ∑ ab : Fin n × Fin n,
      (gridNormSq (entry (Z m t) ab.1 ab.2) + coordForm (entry (Z m t) ab.1 ab.2)) ≤ B := by
    intro m
    have e : ∀ t, ∑ ab : Fin n × Fin n,
        (gridNormSq (entry (Z m t) ab.1 ab.2) + coordForm (entry (Z m t) ab.1 ab.2)) =
        matNormSq (Z m t) + ∑ i, matNormSq (matDp i (Z m t)) := fun t => by
      rw [Finset.sum_add_distrib, sum_entry_gridNormSq, sum_entry_coordForm]
    simp only [e]
    exact hB m
  have hB1' : ∀ m, ∫ t in Ioc 0 T, ∑ ab : Fin n × Fin n,
      trigNegSq 2 (interp (entry (W m t) ab.1 ab.2)) ≤ ((multiIndices 2).card : ℝ) * B1 := by
    intro m
    have hpt : ∀ t, ∑ ab : Fin n × Fin n, trigNegSq 2 (interp (entry (W m t) ab.1 ab.2)) ≤
        ((multiIndices 2).card : ℝ) * negSobNorm2 (W m t) ^ 2 := by
      intro t
      refine le_trans (Finset.sum_le_sum fun ab _ => trigNegSq_two_interp_le _) ?_
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ card_multiIndices_two_pos.le
      rw [Fintype.sum_prod_type]
      exact sum_inv_gridWeight_le_negSobNorm2_sq (W m t)
    calc ∫ t in Ioc 0 T, ∑ ab : Fin n × Fin n, trigNegSq 2 (interp (entry (W m t) ab.1 ab.2))
        ≤ ∫ t in Ioc 0 T, ((multiIndices 2).card : ℝ) * negSobNorm2 (W m t) ^ 2 :=
          integral_mono_of_nonneg (ae_of_all _ fun t =>
            Finset.sum_nonneg fun ab _ => trigNegSq_nonneg _ _) ((hWint m).const_mul _)
            (ae_of_all _ hpt)
      _ = ((multiIndices 2).card : ℝ) * ∫ t in Ioc 0 T, negSobNorm2 (W m t) ^ 2 :=
          integral_const_mul _ _
      _ ≤ ((multiIndices 2).card : ℝ) * B1 :=
          mul_le_mul_of_nonneg_left (hB1 m) card_multiIndices_two_pos.le
  exact gridAubinLions_limit (C := Fin n × Fin n) hT
    (fun m t ab => entry (Z m t) ab.1 ab.2) (fun m t ab => entry (W m t) ab.1 ab.2)
    (fun m ab => hW m ab.1 ab.2) 2 hB' hB1'

/-! ### The logarithmic chart error `‖Z_h - A_h‖_h → 0` (`eq:supp-literal-log-error`) -/

/-- Discrete `L⁴` bound for a matrix array from the uniform product estimate:
`h³ Σ_x ‖A(x)‖⁴ ≤ n² K (Σ_{a,b} ‖A_{ab}‖²_{1,h})²` with `K = Kprod` independent of `N`. -/
theorem sum_norm_pow_four_le (A : MatArr N n) :
    ((N : ℝ) ^ 3)⁻¹ * ∑ x, ‖A x‖ ^ 4 ≤
      (n : ℝ) ^ 2 * Kprod * (∑ a, ∑ b, sobSq 1 (entry A a b)) ^ 2 := by
  have hN : (0 : ℝ) ≤ ((N : ℝ) ^ 3)⁻¹ := by positivity
  -- pointwise Cauchy–Schwarz over the `n²` entries
  have hpt : ∀ x, ‖A x‖ ^ 4 ≤ (n : ℝ) ^ 2 * ∑ ab : Fin n × Fin n, ‖A x ab.1 ab.2‖ ^ 4 := by
    intro x
    have h1 : ‖A x‖ ^ 2 = ∑ ab : Fin n × Fin n, ‖A x ab.1 ab.2‖ ^ 2 := by
      rw [frob_sq, Fintype.sum_prod_type]
    have h2 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n × Fin n)))
      (f := fun ab => ‖A x ab.1 ab.2‖ ^ 2)
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h2
    calc ‖A x‖ ^ 4 = (‖A x‖ ^ 2) ^ 2 := by ring
      _ = (∑ ab : Fin n × Fin n, ‖A x ab.1 ab.2‖ ^ 2) ^ 2 := by rw [h1]
      _ ≤ ((n * n : ℕ) : ℝ) * ∑ ab : Fin n × Fin n, (‖A x ab.1 ab.2‖ ^ 2) ^ 2 := h2
      _ = (n : ℝ) ^ 2 * ∑ ab : Fin n × Fin n, ‖A x ab.1 ab.2‖ ^ 4 := by
          push_cast; ring_nf
  -- each entry: `h³ Σ_x |f|⁴ = ‖f·f‖_h² ≤ K ‖f‖⁴_{1,h}`
  have hent : ∀ ab : Fin n × Fin n, ((N : ℝ) ^ 3)⁻¹ * ∑ x, ‖A x ab.1 ab.2‖ ^ 4 ≤
      Kprod * sobSq 1 (entry A ab.1 ab.2) ^ 2 := by
    intro ab
    have h := gridNormSq_mul_le_one_one (entry A ab.1 ab.2) (entry A ab.1 ab.2)
    have e : gridNormSq (entry A ab.1 ab.2 * entry A ab.1 ab.2) =
        ((N : ℝ) ^ 3)⁻¹ * ∑ x, ‖A x ab.1 ab.2‖ ^ 4 := by
      simp only [gridNormSq, Pi.mul_apply, entry, norm_mul]
      congr 1
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [← e]
    nlinarith [h]
  have hsob : ∀ ab : Fin n × Fin n, 0 ≤ sobSq 1 (entry A ab.1 ab.2) := fun ab => sobSq_nonneg _ _
  calc ((N : ℝ) ^ 3)⁻¹ * ∑ x, ‖A x‖ ^ 4
      ≤ ((N : ℝ) ^ 3)⁻¹ * ∑ x, (n : ℝ) ^ 2 * ∑ ab : Fin n × Fin n, ‖A x ab.1 ab.2‖ ^ 4 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => hpt x) hN
    _ = (n : ℝ) ^ 2 * ∑ ab : Fin n × Fin n, ((N : ℝ) ^ 3)⁻¹ * ∑ x, ‖A x ab.1 ab.2‖ ^ 4 := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun ab _ => Finset.sum_congr rfl fun x _ => by ring
    _ ≤ (n : ℝ) ^ 2 * ∑ ab : Fin n × Fin n, Kprod * sobSq 1 (entry A ab.1 ab.2) ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ab _ => hent ab) (by positivity)
    _ ≤ (n : ℝ) ^ 2 * (Kprod * (∑ ab : Fin n × Fin n, sobSq 1 (entry A ab.1 ab.2)) ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ Kprod_nonneg
        exact Finset.sum_sq_le_sq_sum_of_nonneg fun ab _ => hsob ab
    _ = (n : ℝ) ^ 2 * Kprod * (∑ a, ∑ b, sobSq 1 (entry A a b)) ^ 2 := by
        rw [Fintype.sum_prod_type]; ring

/-- **Logarithmic chart error** (`eq:supp-literal-log-error`, pointwise in time).  If
`‖Z(x) - A(x)‖ ≤ C h ‖A(x)‖²` and `h ‖A(x)‖ ≤ δ` (the identity chart, `h = 1/N`), then
`‖Z - A‖_h² ≤ C² δ h · n √K · ‖A‖_h · Σ_{a,b} ‖A_{ab}‖²_{1,h}`.  Integrated in time against an
`L^∞_t L²_h ∩ L²_t H¹_h` bound this is `O(h)`, so `Z_h - A_h → 0` in `L²`. -/
theorem matNormSq_sub_le_of_chart (A Z : MatArr N n) {C δ : ℝ} (hC : 0 ≤ C)
    (hZA : ∀ x, ‖Z x - A x‖ ≤ C * ((N : ℝ)⁻¹ * ‖A x‖ ^ 2))
    (hchart : ∀ x, (N : ℝ)⁻¹ * ‖A x‖ ≤ δ) :
    matNormSq (fun x => Z x - A x) ≤
      C ^ 2 * δ * (N : ℝ)⁻¹ * ((n : ℝ) * Real.sqrt Kprod) * matNorm A *
        ∑ a, ∑ b, sobSq 1 (entry A a b) := by
  have hN : (0 : ℝ) ≤ ((N : ℝ) ^ 3)⁻¹ := by positivity
  have hh : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  have hδ : 0 ≤ δ := le_trans (mul_nonneg hh (norm_nonneg _)) (hchart 0)
  -- pointwise: `‖Z - A‖² ≤ C² δ h ‖A‖³`
  have hpt : ∀ x, ‖Z x - A x‖ ^ 2 ≤ C ^ 2 * δ * (N : ℝ)⁻¹ * (‖A x‖ * ‖A x‖ ^ 2) := by
    intro x
    have h1 := hZA x
    have h2 := hchart x
    have h0 := norm_nonneg (Z x - A x)
    have ha := norm_nonneg (A x)
    have hsq : ‖Z x - A x‖ ^ 2 ≤ (C * ((N : ℝ)⁻¹ * ‖A x‖ ^ 2)) ^ 2 :=
      pow_le_pow_left₀ h0 h1 2
    calc ‖Z x - A x‖ ^ 2 ≤ (C * ((N : ℝ)⁻¹ * ‖A x‖ ^ 2)) ^ 2 := hsq
      _ = C ^ 2 * ((N : ℝ)⁻¹ * ‖A x‖) * (N : ℝ)⁻¹ * (‖A x‖ * ‖A x‖ ^ 2) := by ring
      _ ≤ C ^ 2 * δ * (N : ℝ)⁻¹ * (‖A x‖ * ‖A x‖ ^ 2) := by
          gcongr
  -- Cauchy–Schwarz in `x` and the `L⁴` bound
  have hcs := grid_cs (N := N) (fun x => ‖A x‖) (fun x => ‖A x‖ ^ 2)
  have h4 := sum_norm_pow_four_le A
  have hS : 0 ≤ ∑ a, ∑ b, sobSq 1 (entry A a b) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sobSq_nonneg _ _
  have hsqrt4 : Real.sqrt (((N : ℝ) ^ 3)⁻¹ * ∑ x, (‖A x‖ ^ 2) ^ 2) ≤
      (n : ℝ) * Real.sqrt Kprod * ∑ a, ∑ b, sobSq 1 (entry A a b) := by
    have e : ∀ x, (‖A x‖ ^ 2) ^ 2 = ‖A x‖ ^ 4 := fun x => by ring
    simp only [e]
    refine Real.sqrt_le_iff.2 ⟨by have := Real.sqrt_nonneg Kprod; positivity, ?_⟩
    rw [mul_pow, mul_pow, Real.sq_sqrt Kprod_nonneg]
    exact h4
  have hmat : matNorm A = Real.sqrt (((N : ℝ) ^ 3)⁻¹ * ∑ x, ‖A x‖ ^ 2) := matNorm_eq A
  rw [matNormSq_eq]
  calc ((N : ℝ) ^ 3)⁻¹ * ∑ x, ‖Z x - A x‖ ^ 2
      ≤ ((N : ℝ) ^ 3)⁻¹ * ∑ x, C ^ 2 * δ * (N : ℝ)⁻¹ * (‖A x‖ * ‖A x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => hpt x) hN
    _ = C ^ 2 * δ * (N : ℝ)⁻¹ * (((N : ℝ) ^ 3)⁻¹ * ∑ x, ‖A x‖ * ‖A x‖ ^ 2) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ C ^ 2 * δ * (N : ℝ)⁻¹ * (matNorm A *
          ((n : ℝ) * Real.sqrt Kprod * ∑ a, ∑ b, sobSq 1 (entry A a b))) := by
        refine mul_le_mul_of_nonneg_left (hcs.trans ?_) (by positivity)
        rw [← hmat]
        exact mul_le_mul_of_nonneg_left hsqrt4 (matNorm_nonneg A)
    _ = _ := by ring

end RenewalGeometry.LiteralLinkCompactness
