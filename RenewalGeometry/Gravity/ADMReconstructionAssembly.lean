/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.ADMFrameUniqueness
import RenewalGeometry.Gravity.ADMPacketPersistenceExact
import RenewalGeometry.Lorentz.LorentzianPrincipalSquare
import RenewalGeometry.Dimension.DimensionK4Classification
import RenewalGeometry.Dimension.DimensionRegularGraphExact
import RenewalGeometry.Dimension.DimensionCofinal3Plus1
import RenewalGeometry.Krein.SignatureMinimalityOrientationFloor

/-!
# Minimal faithful `3+1` ADM reconstruction: assembly (`mt:adm`, emergent-spacetime manuscript)

The seven clauses of `mt:adm` are stated as propositions `ADMReconstruction.clauseI`, …,
`clauseVII` and proved together in `ADMReconstruction.adm_reconstruction`.

New general infrastructure (cofinal persistence, the finite-dimensional core of clause (vii)):

* `posDef_map_ofReal` — a real positive definite matrix stays positive definite over `ℂ`.
* `tendsto_of_summable_entry_defects` — matrices with summable entrywise successive defects
  converge entrywise.
* `posSemidef_of_tendsto` — entrywise limits of positive semidefinite complex matrices are
  positive semidefinite.
* `posDef_of_tendsto_coercive` — a uniform coercivity margin `c |v|² ≤ v·B_n v` persists to
  the limit, which is positive definite (pair gap persistence).
* `admMetric_posDef`, `admLapse_pos` — the boxed ADM inversion of a positive definite bracket
  is a positive definite metric with positive lapse.
* `adm_cofinal_persistence` — clause (vii): under summable correction defects the corrected
  source forms, brackets and speed densities converge; exact threshold ranks persist (and
  persisted endpoint/edge ranks `3, 6` of an even cell select `K₄` and `1 + 3`); the pair gap
  persists; the ADM packet converges to that of the limit; and the limit metric with its lapse
  has Lorentzian signed inertia `(1, 3)` (and `(3, 1)` up to overall sign).
-/

open Matrix Filter Topology Module
open scoped ComplexOrder

namespace RenewalGeometry

namespace ADMReconstruction

/-! ## Infrastructure -/

/-- A real positive definite matrix is positive definite as a complex matrix. -/
theorem posDef_map_ofReal {n : Type*} [Fintype n] {g : Matrix n n ℝ} (hg : g.PosDef) :
    (g.map (fun r : ℝ => (r : ℂ))).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec] at hg ⊢
  obtain ⟨hH, hpos⟩ := hg
  have hsym : ∀ i j, g j i = g i j := fun i j => by
    simpa using congrFun (congrFun hH i) j
  refine ⟨?_, fun x hx => ?_⟩
  · ext i j
    simp [Matrix.conjTranspose_apply, hsym]
  set u : n → ℝ := fun i => (x i).re
  set v : n → ℝ := fun i => (x i).im
  have hq : ∀ w : n → ℝ, 0 ≤ w ⬝ᵥ (g *ᵥ w) := fun w => by
    by_cases hw : w = 0
    · simp [hw]
    · simpa using (hpos hw).le
  have key : star x ⬝ᵥ (g.map (fun r : ℝ => (r : ℂ)) *ᵥ x)
      = ((u ⬝ᵥ (g *ᵥ u) + v ⬝ᵥ (g *ᵥ v) : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [dotProduct, mulVec, Matrix.map_apply, Pi.star_apply, Complex.re_sum,
        Finset.mul_sum, Complex.ofReal_re, Complex.ofReal_add, Complex.add_re, u, v]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re,
        Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    · simp only [dotProduct, mulVec, Matrix.map_apply, Pi.star_apply, Complex.im_sum,
        Finset.mul_sum, Complex.ofReal_im]
      have h1 : ∀ i j, (star (x i) * ((g i j : ℂ) * x j)).im
          = g i j * u i * v j - g i j * v i * u j := fun i j => by
        simp only [Complex.mul_im, Complex.mul_re, Complex.star_def, Complex.conj_re,
          Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, u, v]
        ring
      simp only [h1, Finset.sum_sub_distrib]
      rw [Finset.sum_comm (f := fun i j => g i j * v i * u j)]
      rw [sub_eq_zero]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hsym]
      ring
  rw [key, Complex.zero_lt_real]
  have huv : u ≠ 0 ∨ v ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    funext i
    apply Complex.ext
    · exact congrFun h.1 i
    · exact congrFun h.2 i
  rcases huv with hu | hv
  · have := hpos hu
    simp only [star_trivial] at this
    linarith [hq v]
  · have := hpos hv
    simp only [star_trivial] at this
    linarith [hq u]

/-- Matrices with summable entrywise successive defects converge entrywise. -/
theorem tendsto_of_summable_entry_defects {n m : Type*} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    [CompleteSpace 𝕜] (A : ℕ → Matrix n m 𝕜)
    (hA : ∀ i j, Summable fun k => ‖A (k + 1) i j - A k i j‖) :
    ∃ A' : Matrix n m 𝕜, ∀ i j, Tendsto (fun k => A k i j) atTop (𝓝 (A' i j)) := by
  have h : ∀ i j, ∃ l : 𝕜, Tendsto (fun k => A k i j) atTop (𝓝 l) := fun i j => by
    refine cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist ?_)
    refine (hA i j).congr fun k => ?_
    rw [dist_eq_norm, ← norm_neg, neg_sub]
  choose L hL using h
  exact ⟨Matrix.of L, hL⟩

/-- Entrywise convergence of matrices gives convergence of `star x ⬝ᵥ A x`. -/
theorem dotProduct_mulVec_tendsto {n : Type*} [Fintype n] (A : ℕ → Matrix n n ℂ)
    (A' : Matrix n n ℂ) (hconv : ∀ i j, Tendsto (fun k => A k i j) atTop (𝓝 (A' i j)))
    (x : n → ℂ) :
    Tendsto (fun k => star x ⬝ᵥ (A k *ᵥ x)) atTop (𝓝 (star x ⬝ᵥ (A' *ᵥ x))) := by
  simp only [dotProduct, Matrix.mulVec]
  refine tendsto_finsetSum _ fun i _ => ?_
  exact tendsto_const_nhds.mul
    (tendsto_finsetSum _ fun j _ => (hconv i j).mul tendsto_const_nhds)

/-- Entrywise limits of positive semidefinite complex matrices are positive semidefinite. -/
theorem posSemidef_of_tendsto {n : Type*} [Fintype n] (A : ℕ → Matrix n n ℂ)
    (A' : Matrix n n ℂ) (hconv : ∀ i j, Tendsto (fun k => A k i j) atTop (𝓝 (A' i j)))
    (hA : ∀ k, (A k).PosSemidef) : A'.PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext i j
    have h1 : Tendsto (fun k => star (A k j i)) atTop (𝓝 (star (A' j i))) :=
      (continuous_star.tendsto _).comp (hconv j i)
    have h2 : ∀ k, star (A k j i) = A k i j := fun k => by
      have := congrFun (congrFun (hA k).1 i) j
      simpa [Matrix.conjTranspose_apply] using this
    simp only [h2] at h1
    simpa [Matrix.conjTranspose_apply] using tendsto_nhds_unique h1 (hconv i j)
  · exact ge_of_tendsto' (dotProduct_mulVec_tendsto A A' hconv x)
      fun k => ((Matrix.posSemidef_iff_dotProduct_mulVec.1 (hA k)).2 x)

/-- A uniform coercivity margin persists to the limit of convergent symmetric brackets, which is
positive definite with the same margin (the pair-gap clause). -/
theorem posDef_of_tendsto_coercive {n : Type*} [Fintype n] (B : ℕ → Matrix n n ℝ)
    (Blim : Matrix n n ℝ) (hBt : Tendsto B atTop (𝓝 Blim)) (hsym : ∀ k, (B k)ᵀ = B k)
    (c : ℝ) (hc : 0 < c) (hcoer : ∀ k v, c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (B k *ᵥ v)) :
    Blimᵀ = Blim ∧ (∀ v, c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Blim *ᵥ v)) ∧ Blim.PosDef := by
  have hT : Blimᵀ = Blim := by
    have h1 : Tendsto (fun k => (B k)ᵀ) atTop (𝓝 Blimᵀ) :=
      (Continuous.matrix_transpose continuous_id).continuousAt.tendsto.comp hBt
    simp only [hsym] at h1
    exact tendsto_nhds_unique h1 hBt
  have hform : ∀ v, Tendsto (fun k => v ⬝ᵥ (B k *ᵥ v)) atTop (𝓝 (v ⬝ᵥ (Blim *ᵥ v))) := by
    intro v
    have hc : Continuous fun M : Matrix n n ℝ => v ⬝ᵥ (M *ᵥ v) := by
      simp only [dotProduct, Matrix.mulVec]
      fun_prop
    exact hc.continuousAt.tendsto.comp hBt
  have hm : ∀ v, c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Blim *ᵥ v) := fun v =>
    ge_of_tendsto' (hform v) fun k => hcoer k v
  refine ⟨hT, hm, ?_⟩
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hT]
  · simp only [star_trivial]
    have hxx : 0 < x ⬝ᵥ x := by
      have := Matrix.dotProduct_star_self_pos_iff.2 hx
      simpa using this
    exact lt_of_lt_of_le (mul_pos hc hxx) (hm x)

/-- The boxed ADM metric of a positive definite bracket with positive speed density is
positive definite. -/
theorem admMetric_posDef (B : Matrix (Fin 3) (Fin 3) ℝ) (ϱ : ℝ) (hB : B.PosDef) (hϱ : 0 < ϱ) :
    (admMetric B ϱ).PosDef := by
  have hdet : 0 < B.det := hB.det_pos
  have hs : 0 < ϱ ^ ((2 : ℝ) / 3) * B.det ^ ((1 : ℝ) / 3) := by positivity
  exact hB.inv.smul hs

/-- The boxed ADM lapse of a positive definite bracket with positive speed density is
positive. -/
theorem admLapse_pos (B : Matrix (Fin 3) (Fin 3) ℝ) (ϱ : ℝ) (hB : B.PosDef) (hϱ : 0 < ϱ) :
    0 < admLapse B ϱ := by
  have hdet : 0 < B.det := hB.det_pos
  unfold admLapse
  positivity

/-! ## Clause (vii): cofinal persistence -/

/-- **`mt:adm` (vii), finite-dimensional core of the cofinal limit.**  Along a cofinal tower
of cutoffs, let the corrected (harmonically transported) packets on a protected finite screen
have summable successive defects: positive semidefinite source forms `A k` (with uniform
margins on an `r`-dimensional witness subspace `V` and vanishing tails on a complementary
null witness `W`), symmetric spatial brackets `B k` with a uniform coercivity margin `c > 0`
(nondegenerate continuum bracket), and speed densities `ϱ k ≥ ϱ₀ > 0`.  Then:

* the corrected packets converge, and the limit source form has exactly the threshold rank
  `r` (source rank persistence);
* the pair gap persists: the limit bracket keeps the margin `c` and is positive definite;
* the ADM metric and lapse converge to the ADM packet of the limit, which is a positive
  definite metric with positive lapse;
* the limit metric with its lapse has Lorentzian signed inertia `(1, 3, 0)` (one-line signed
  extension `-N⁻²τ² + g(w,w)`), and `(3, 1, 0)` up to overall sign. -/
theorem adm_cofinal_persistence {n : Type} [Fintype n]
    (A : ℕ → Matrix n n ℂ) (hAdef : ∀ i j, Summable fun k => ‖A (k + 1) i j - A k i j‖)
    (hApsd : ∀ k, (A k).PosSemidef) (r : ℕ) (V W : Submodule ℂ (n → ℂ))
    (hVr : finrank ℂ V = r) (hWr : finrank ℂ W = Fintype.card n - r)
    (hr : r ≤ Fintype.card n)
    (hlowV : ∀ x ∈ V, x ≠ 0 → ∃ δ > (0 : ℝ), ∀ k, δ ≤ DimensionCofinal.qf (A k) x)
    (htailW : ∀ x ∈ W, Tendsto (fun k => DimensionCofinal.qf (A k) x) atTop (𝓝 0))
    (B : ℕ → Matrix (Fin 3) (Fin 3) ℝ) (hBdef : ∀ i j, Summable fun k => |B (k + 1) i j - B k i j|)
    (hBsym : ∀ k, (B k)ᵀ = B k) (c : ℝ) (hc : 0 < c)
    (hcoer : ∀ k v, c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (B k *ᵥ v))
    (ϱ : ℕ → ℝ) (hϱdef : Summable fun k => |ϱ (k + 1) - ϱ k|) (ϱ₀ : ℝ) (hϱ₀ : 0 < ϱ₀)
    (hϱlow : ∀ k, ϱ₀ ≤ ϱ k) :
    ∃ (A' : Matrix n n ℂ) (Blim : Matrix (Fin 3) (Fin 3) ℝ) (ϱlim : ℝ),
      (∀ i j, Tendsto (fun k => A k i j) atTop (𝓝 (A' i j))) ∧ A'.rank = r ∧
      Tendsto B atTop (𝓝 Blim) ∧ Tendsto ϱ atTop (𝓝 ϱlim) ∧ ϱ₀ ≤ ϱlim ∧
      (∀ v, c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Blim *ᵥ v)) ∧ Blim.PosDef ∧
      Tendsto (fun k => admMetric (B k) (ϱ k)) atTop (𝓝 (admMetric Blim ϱlim)) ∧
      Tendsto (fun k => admLapse (B k) (ϱ k)) atTop (𝓝 (admLapse Blim ϱlim)) ∧
      (admMetric Blim ϱlim).PosDef ∧ 0 < admLapse Blim ϱlim ∧
      (negInertia (oneLineSignedExtension (-((admLapse Blim ϱlim)⁻¹) ^ 2)
          ((admMetric Blim ϱlim).map (fun x : ℝ => (x : ℂ)))) = 1 ∧
        posInertia (oneLineSignedExtension (-((admLapse Blim ϱlim)⁻¹) ^ 2)
          ((admMetric Blim ϱlim).map (fun x : ℝ => (x : ℂ)))) = 3 ∧
        nullInertia (oneLineSignedExtension (-((admLapse Blim ϱlim)⁻¹) ^ 2)
          ((admMetric Blim ϱlim).map (fun x : ℝ => (x : ℂ)))) = 0) ∧
      (negInertia (-(oneLineSignedExtension (-((admLapse Blim ϱlim)⁻¹) ^ 2)
          ((admMetric Blim ϱlim).map (fun x : ℝ => (x : ℂ))))) = 3 ∧
        posInertia (-(oneLineSignedExtension (-((admLapse Blim ϱlim)⁻¹) ^ 2)
          ((admMetric Blim ϱlim).map (fun x : ℝ => (x : ℂ))))) = 1 ∧
        nullInertia (-(oneLineSignedExtension (-((admLapse Blim ϱlim)⁻¹) ^ 2)
          ((admMetric Blim ϱlim).map (fun x : ℝ => (x : ℂ))))) = 0) := by
  obtain ⟨A', hA'⟩ := tendsto_of_summable_entry_defects A hAdef
  have hA'psd := posSemidef_of_tendsto A A' hA' hApsd
  have hrank := DimensionCofinal.exact_rank_persistence A A' r hA' hA'psd V W hVr hWr hr
    hlowV htailW
  obtain ⟨Blim, ϱlim, hBt, hϱt, hpack⟩ := adm_packet_persists_of_summable_defects B ϱ hBdef hϱdef
  have hϱlim : ϱ₀ ≤ ϱlim := ge_of_tendsto' hϱt hϱlow
  have hϱpos : 0 < ϱlim := lt_of_lt_of_le hϱ₀ hϱlim
  obtain ⟨-, hm, hBpd⟩ := posDef_of_tendsto_coercive B Blim hBt hBsym c hc hcoer
  obtain ⟨hgt, hNt⟩ := hpack hBpd.det_pos
  have hg := admMetric_posDef Blim ϱlim hBpd hϱpos
  have hN := admLapse_pos Blim ϱlim hBpd hϱpos
  obtain ⟨hi1, hi2⟩ := oneLineSignedExtension_inertia_lorentz (admLapse Blim ϱlim) hN
    ((admMetric Blim ϱlim).map (fun x : ℝ => (x : ℂ))) (posDef_map_ofReal hg)
  exact ⟨A', Blim, ϱlim, hA', hrank, hBt, hϱt, hϱlim, hm, hBpd, hgt, hNt, hg, hN, hi1, hi2⟩

/-! ## The seven clauses -/

/-- The summation functional on `ℝ⁴`; its kernel is the `A₃` root space `W₄`. -/
def sumFunctional : (Fin 4 → ℝ) →ₗ[ℝ] ℝ := ∑ i, LinearMap.proj i

/-- The `A₃` spatial module `W₄ = {x ∈ ℝ⁴ : Σ xᵢ = 0}` is three-dimensional. -/
theorem finrank_a3SpatialModule : finrank ℝ (LinearMap.ker sumFunctional) = 3 := by
  have hsurj : LinearMap.range sumFunctional = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro t
    refine ⟨Pi.single 0 t, ?_⟩
    simp [sumFunctional, Fin.sum_univ_four]
  have h := sumFunctional.finrank_range_add_finrank_ker
  rw [hsurj, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h
  omega

/-- `mt:adm` (i): either selector picks `K₄` and the spatial module is `W₄ ≅ ℝ³`.  Regular-graph
route (`prop:main-regular-graph-k4`): a simple `k`-regular graph on `v ≥ 2` vertices with equal
endpoint and cycle source ranks is `K₄`.  Alternating/minimal-source route
(`prop:main-alternating-k4`): a nondegenerate alternating form forces even dimension, and an
even cell `N ≥ 3` has endpoint/edge ranks `≥ 3, 6` with equality exactly for `N = 4`. -/
def clauseI : Prop :=
  (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ),
      2 ≤ Fintype.card V → (∀ v, G.degree v = k) →
      ((Fintype.card V : ℤ) - 1 = (G.edgeFinset.card : ℤ) - Fintype.card V + 1) →
      Fintype.card V = 4 ∧ k = 3 ∧ G = ⊤) ∧
  (∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℝ), Jᵀ = -J → IsUnit J.det → Even n) ∧
  (∀ N : ℕ, Even N → 3 ≤ N →
      4 ≤ N ∧ 3 ≤ N - 1 ∧ 6 ≤ N.choose 2 ∧ ((N - 1 = 3 ∧ N.choose 2 = 6) ↔ N = 4)) ∧
  finrank ℝ (LinearMap.ker sumFunctional) = 3

/-- `mt:adm` (ii): the winner–waiting statistics of the scheduler-separated root race form a
faithful coordinate system (score covariance `δ_{bc} k_b / K`, `lem:supp-race-score`), whereas
winner probabilities alone lose the common scale. -/
def clauseII : Prop :=
  (∀ k : Fin 6 → ℝ, (∀ a, 0 < k a) → ∀ b c : Fin 6,
      (∑ a, ∫ t in Set.Ioi (0 : ℝ),
        ((if a = b then (1 : ℝ) else 0) - k b * t)
        * ((if a = c then (1 : ℝ) else 0) - k c * t)
        * (k a * Real.exp (-((∑ j, k j) * t))))
      = if b = c then k b / (∑ j, k j) else 0) ∧
  (∀ (k : Fin 6 → ℝ) (lam : ℝ), 0 < lam → (∀ a, 0 < k a) → ∀ b,
      (lam * k b) / (∑ j, lam * k j) = k b / (∑ j, k j))

/-- `mt:adm` (iii): the root moments and speed density invert uniquely to the ADM spatial
metric, lapse and shift (`thm:supp-adm-frame`): the six root dyadics are a basis of `Sym₃`,
the rate-difference (shift) map has rank three with the tetrahedral circulation kernel, and
the boxed `eq:adm-inversion-main` is the unique positive solution. -/
def clauseIII : Prop :=
  (∀ S : Matrix (Fin 3) (Fin 3) ℝ, S.IsSymm →
      ∃! c : Fin 6 → ℝ, (∑ a, c a • vecMulVec (a3SchedulerRoot a) (a3SchedulerRoot a)) = S) ∧
  (LinearMap.range a3ShiftMap = ⊤ ∧
      LinearMap.ker a3ShiftMap = Submodule.span ℝ (Set.range a3Cycle) ∧
      finrank ℝ (LinearMap.ker a3ShiftMap) = 3) ∧
  (∀ (B : Matrix (Fin 3) (Fin 3) ℝ) (ϱ : ℝ), 0 < ϱ → 0 < B.det →
      Real.sqrt (((ϱ ^ ((2 : ℝ) / 3) * B.det ^ ((1 : ℝ) / 3)) • B⁻¹).det) = ϱ ∧
      ((ϱ ^ ((1 : ℝ) / 3) * B.det ^ ((1 : ℝ) / 6)) ^ 2) •
        ((ϱ ^ ((2 : ℝ) / 3) * B.det ^ ((1 : ℝ) / 3)) • B⁻¹)⁻¹ = B) ∧
  (∀ (B g : Matrix (Fin 3) (Fin 3) ℝ) (ϱ N : ℝ),
      0 < ϱ → 0 < B.det → 0 < N → 0 < g.det → B = (N ^ 2) • g⁻¹ → ϱ = Real.sqrt g.det →
      N = ϱ ^ ((1 : ℝ) / 3) * B.det ^ ((1 : ℝ) / 6) ∧
        g = (ϱ ^ ((2 : ℝ) / 3) * B.det ^ ((1 : ℝ) / 3)) • B⁻¹)

/-- `mt:adm` (iv): a nondegenerate bracket `c |v|² ≤ v·B_h v` requires total rate
`Σ k_a ≥ 3c / (2h²)`, i.e. an `O(h⁻²)` fast scheduler (`lem:supp-fast-clock`). -/
def clauseIV : Prop :=
  ∀ (h c : ℝ) (k : Fin 6 → ℝ), 0 < h → (∀ a, 0 ≤ k a) →
    (∀ v : Fin 3 → ℝ, c * (∑ i, v i ^ 2)
      ≤ v ⬝ᵥ (((h ^ 2) • ∑ a, k a • vecMulVec (a3SchedulerRoot a) (a3SchedulerRoot a)) *ᵥ v)) →
    3 * c ≤ 2 * h ^ 2 * ∑ a, k a

/-- `mt:adm` (v): the protected orientation is independent of the positive packet (it has an
anchored separating pair that survives conservative refinement,
`thm:supp-relative-primitive-floor`), and a positive spatial form `D` with exactly one
independent signed line (`def:main-signed-extension`, coefficient `c < 0`) has Lorentzian
inertia `(1, 3, 0)`, `(3, 1, 0)` up to overall sign, invariantly under change of basis, before
any Clifford representation. -/
def clauseV : Prop :=
  (∀ {𝔊 : OperationalEntrance.AnchoredGrammar} (M : OperationalEntrance.Model 𝔊),
      OperationalEntrance.IsSeparatingPair .orientation M (M.withOrientation (-M.orientation))) ∧
  ∀ (c : ℝ), c < 0 → ∀ D : Matrix (Fin 3) (Fin 3) ℂ, D.PosDef →
    (negInertia (oneLineSignedExtension c D) = 1 ∧
      posInertia (oneLineSignedExtension c D) = 3 ∧
      nullInertia (oneLineSignedExtension c D) = 0) ∧
    (negInertia (-(oneLineSignedExtension c D)) = 3 ∧
      posInertia (-(oneLineSignedExtension c D)) = 1 ∧
      nullInertia (-(oneLineSignedExtension c D)) = 0) ∧
    (∀ X : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ, IsUnit X.det →
      negInertia (Xᴴ * oneLineSignedExtension c D * X) = 1 ∧
        posInertia (Xᴴ * oneLineSignedExtension c D * X) = 3 ∧
        nullInertia (Xᴴ * oneLineSignedExtension c D * X) = 0)

/-- `mt:adm` (vi): the Clifford cell `eq:clifford-main` satisfies the Clifford relations of
signature `(-,+,+,+)` and generates `M₄(ℂ)` (faithful), the principal symbol squares to
`eq:dirac-square-main`, and its characteristic form realizes the inertia `(1, 3)`. -/
def clauseVI : Prop :=
  ((gamma0 * gamma0 = -1 ∧ gamma1 * gamma1 = 1 ∧ gamma2 * gamma2 = 1 ∧ gamma3 * gamma3 = 1) ∧
    (gamma0 * gamma1 + gamma1 * gamma0 = 0 ∧ gamma0 * gamma2 + gamma2 * gamma0 = 0 ∧
      gamma0 * gamma3 + gamma3 * gamma0 = 0 ∧ gamma1 * gamma2 + gamma2 * gamma1 = 0 ∧
      gamma1 * gamma3 + gamma3 * gamma1 = 0 ∧ gamma2 * gamma3 + gamma3 * gamma2 = 0) ∧
    Algebra.adjoin ℂ ({gamma0, gamma1, gamma2, gamma3} :
      Set (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) = ⊤) ∧
  (∀ (N : ℝ) (β ξ : Fin 3 → ℝ) (ξ0 : ℝ) (E ginv : Matrix (Fin 3) (Fin 3) ℝ), E * Eᵀ = ginv →
    ((N⁻¹ * (ξ0 - β ⬝ᵥ ξ)) • gamma0 + ∑ a, (∑ i, E i a * ξ i) • gammaDir a)
      * ((N⁻¹ * (ξ0 - β ⬝ᵥ ξ)) • gamma0 + ∑ a, (∑ i, E i a * ξ i) • gammaDir a)
      = (-(N⁻¹ * (ξ0 - β ⬝ᵥ ξ)) ^ 2 + ξ ⬝ᵥ (ginv *ᵥ ξ))
        • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) ∧
  (∀ (N : ℝ), 0 < N → ∀ (β : Fin 3 → ℝ) (ginv : Matrix (Fin 3) (Fin 3) ℝ),
    (∀ ξ : Fin 3 → ℝ, ξ ≠ 0 → 0 < ξ ⬝ᵥ (ginv *ᵥ ξ)) →
    (∀ (η0 : ℝ) (η : Fin 3 → ℝ),
        lorentzCharForm N β ginv (N * η0 + β ⬝ᵥ η) η = -η0 ^ 2 + η ⬝ᵥ (ginv *ᵥ η)) ∧
    (∀ (ξ0 : ℝ) (ξ : Fin 3 → ℝ), N * (N⁻¹ * (ξ0 - β ⬝ᵥ ξ)) + β ⬝ᵥ ξ = ξ0) ∧
    lorentzCharForm N β ginv 1 0 < 0 ∧
    (∀ ξ : Fin 3 → ℝ, ξ ≠ 0 → 0 < lorentzCharForm N β ginv (β ⬝ᵥ ξ) ξ))

/-- `mt:adm` (vii): under summably correctable defects of the corrected packets on a protected
finite screen, the source ranks persist (and persisted endpoint/edge ranks `3, 6` of an even
cell select `K₄` and the dimension `1 + 3`), the pair gap persists, the ADM packet converges to
the ADM packet of the limit, and the limit carries Lorentzian signed inertia. -/
def clauseVII : Prop :=
  (∀ {n : Type} [Fintype n] (A : ℕ → Matrix n n ℂ),
    (∀ i j, Summable fun k => ‖A (k + 1) i j - A k i j‖) → (∀ k, (A k).PosSemidef) →
    ∀ (r : ℕ) (V W : Submodule ℂ (n → ℂ)), finrank ℂ V = r → finrank ℂ W = Fintype.card n - r →
    r ≤ Fintype.card n →
    (∀ x ∈ V, x ≠ 0 → ∃ δ > (0 : ℝ), ∀ k, δ ≤ DimensionCofinal.qf (A k) x) →
    (∀ x ∈ W, Tendsto (fun k => DimensionCofinal.qf (A k) x) atTop (𝓝 0)) →
    ∀ (B : ℕ → Matrix (Fin 3) (Fin 3) ℝ), (∀ i j, Summable fun k => |B (k + 1) i j - B k i j|) →
    (∀ k, (B k)ᵀ = B k) → ∀ (c : ℝ), 0 < c → (∀ k v, c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (B k *ᵥ v)) →
    ∀ (ϱ : ℕ → ℝ), (Summable fun k => |ϱ (k + 1) - ϱ k|) → ∀ (ϱ₀ : ℝ), 0 < ϱ₀ →
    (∀ k, ϱ₀ ≤ ϱ k) →
    ∃ (A' : Matrix n n ℂ) (Blim : Matrix (Fin 3) (Fin 3) ℝ) (ϱlim : ℝ),
      (∀ i j, Tendsto (fun k => A k i j) atTop (𝓝 (A' i j))) ∧ A'.rank = r ∧
      Tendsto B atTop (𝓝 Blim) ∧ Tendsto ϱ atTop (𝓝 ϱlim) ∧ ϱ₀ ≤ ϱlim ∧
      (∀ v, c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Blim *ᵥ v)) ∧ Blim.PosDef ∧
      Tendsto (fun k => admMetric (B k) (ϱ k)) atTop (𝓝 (admMetric Blim ϱlim)) ∧
      Tendsto (fun k => admLapse (B k) (ϱ k)) atTop (𝓝 (admLapse Blim ϱlim)) ∧
      (admMetric Blim ϱlim).PosDef ∧ 0 < admLapse Blim ϱlim ∧
      (negInertia (oneLineSignedExtension (-((admLapse Blim ϱlim)⁻¹) ^ 2)
          ((admMetric Blim ϱlim).map (fun x : ℝ => (x : ℂ)))) = 1 ∧
        posInertia (oneLineSignedExtension (-((admLapse Blim ϱlim)⁻¹) ^ 2)
          ((admMetric Blim ϱlim).map (fun x : ℝ => (x : ℂ)))) = 3 ∧
        nullInertia (oneLineSignedExtension (-((admLapse Blim ϱlim)⁻¹) ^ 2)
          ((admMetric Blim ϱlim).map (fun x : ℝ => (x : ℂ)))) = 0) ∧
      (negInertia (-(oneLineSignedExtension (-((admLapse Blim ϱlim)⁻¹) ^ 2)
          ((admMetric Blim ϱlim).map (fun x : ℝ => (x : ℂ))))) = 3 ∧
        posInertia (-(oneLineSignedExtension (-((admLapse Blim ϱlim)⁻¹) ^ 2)
          ((admMetric Blim ϱlim).map (fun x : ℝ => (x : ℂ))))) = 1 ∧
        nullInertia (-(oneLineSignedExtension (-((admLapse Blim ϱlim)⁻¹) ^ 2)
          ((admMetric Blim ϱlim).map (fun x : ℝ => (x : ℂ))))) = 0)) ∧
  (∀ {nE nF : Type} [Fintype nE] [Fintype nF] (Aend' : Matrix nE nE ℂ) (Aedge' : Matrix nF nF ℂ)
    (N : ℕ), Even N → 3 ≤ N → Aend'.rank = N - 1 → Aedge'.rank = N.choose 2 →
    Aend'.rank = 3 → Aedge'.rank = 6 → N = 4 ∧ 1 + (N - 1) = 4)

/-- **`mt:adm`, minimal faithful `3+1` ADM reconstruction from either finite selector.**
All seven clauses hold. -/
theorem adm_reconstruction :
    clauseI ∧ clauseII ∧ clauseIII ∧ clauseIV ∧ clauseV ∧ clauseVI ∧ clauseVII := by
  obtain ⟨-, -, hA3, hA3', -, hA5⟩ := relational_scheduler_ADM
  obtain ⟨hsel, hsel2, -⟩ := dimension_K4_selector_complete
  refine ⟨⟨fun G _ k hv hreg hbal => dimension_regular_graph_exact G k hv hreg hbal,
      hsel.1, hsel.2.1, finrank_a3SpatialModule⟩,
    ⟨hA3, hA3'⟩, adm_frame_complete, hA5, ⟨fun M => OperationalEntrance.separating_reverseOrientation M,
      fun c hc D hD => ?_⟩,
    ⟨anchor_external_clifford, fun N β ξ ξ0 E ginv hE =>
      anchor_lorentzian_symbol_square N β ξ ξ0 E ginv hE,
      fun N hN β ginv hg => lorentzCharForm_inertia N hN β ginv hg⟩,
    ⟨fun A hAdef hApsd r V W hVr hWr hr hlowV htailW B hBdef hBsym c hc hcoer ϱ hϱdef ϱ₀ hϱ₀
        hϱlow => adm_cofinal_persistence A hAdef hApsd r V W hVr hWr hr hlowV htailW B hBdef
        hBsym c hc hcoer ϱ hϱdef ϱ₀ hϱ₀ hϱlow,
      fun Aend' Aedge' N hN h3 h1 h2 h3' h6 =>
        DimensionCofinal.cofinal_dimension_selection Aend' Aedge' N hN h3 h1 h2 h3' h6⟩⟩
  obtain ⟨a, ⟨ha, hca⟩, -⟩ := exists_sq_of_neg c hc
  subst hca
  exact oneLineSignedExtension_inertia_full (W := Fin 3) a ha D hD |>.imp
    (fun h => by simpa using h) (fun h => h.imp (fun h => by simpa using h)
      (fun h X hX => by simpa using h X hX))

/-- Non-vacuity of the clause (vii) hypotheses: the constant packet `A k = 1` (rank `1` on
`Fin 1`), `B k = 1`, `ϱ k = 1` satisfies them. -/
example : True := by
  have h := adm_reconstruction.2.2.2.2.2.2.1 (n := Fin 1) (fun _ => 1) (fun i j => by simp)
    (fun _ => Matrix.PosSemidef.one) 1 ⊤ ⊥ (by simp) (by simp) (by simp)
    (fun x _ hx => ⟨DimensionCofinal.qf 1 x, by
      simp only [DimensionCofinal.qf, Matrix.one_mulVec]
      have := Matrix.dotProduct_star_self_pos_iff.2 hx
      exact (Complex.pos_iff.1 this).1, fun _ => le_rfl⟩)
    (fun x hx => by simp [(Submodule.mem_bot ℂ).1 hx, DimensionCofinal.qf])
    (fun _ => 1) (fun i j => by simp) (fun _ => by simp) 1 one_pos
    (fun _ v => by simp) (fun _ => 1) (by simp) 1 one_pos (fun _ => le_rfl)
  trivial

end ADMReconstruction

end RenewalGeometry
