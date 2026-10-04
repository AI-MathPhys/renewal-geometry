/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.TorusCurvatureConvergence

/-!
# A-priori Sobolev bounds imply bosonic strong compactness on `𝕋^d`

Assembly, on the periodic box `𝕋^d`, of the analytic content of `prop:sobolev-bosonic` of the
Einstein–Standard-Model action-closure manuscript (generic; no renewal notions).

* `rellich_L2_family`: Rellich–Kondrachov for finitely many sequences with **one common
  subsequence** (per-component exponents `t_j < s_j`), via `FourierRellich.rellich_coefficients`
  on the index set `J × ℤ^d`.
* `sobolev_bosonic_torus`: frame components bounded in `H^{s_e}` (`s_e > max(1, d/2)`, e.g.
  `2 + σ` on `𝕋⁴`), gauge potentials and Higgs components bounded in `H^{s_A}`, `H^{s_H}`
  (`> max(1, d/4)`, e.g. `1 + σ` on `𝕋⁴`) and coefficient banks in a compact set: along one
  subsequence `e_h → e` strongly in `H¹` and uniformly (continuous representatives),
  `A_h → A` and `H_h → H` strongly in `H¹ ∩ L⁴`, `F_{A_h} → F_A` and `D_{A_h} H_h → D_A H`
  strongly in `L²`, and the coefficients converge.
-/

open Finset Filter Topology MeasureTheory UnitAddTorus
open scoped BigOperators Real ENNReal

namespace RenewalGeometry.TorusSobolev

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

noncomputable section

local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)

variable {d : Type*} [Fintype d]

theorem finite_sobWeight_rpow_lt {t s : ℝ} (hts : t < s) (R : ℝ) :
    {n : d → ℤ | sobWeight n ^ s < R * sobWeight n ^ t}.Finite := by
  refine (finite_sobWeight_lt (R ^ (s - t)⁻¹)).subset ?_
  intro n hn
  simp only [Set.mem_setOf_eq] at hn ⊢
  have hwt := sobWeight_rpow_pos n t
  have h1 : sobWeight n ^ (s - t) < R := by
    rw [Real.rpow_sub (sobWeight_pos n), div_lt_iff₀ hwt]; exact hn
  have hst : 0 < (s - t)⁻¹ := inv_pos.mpr (by linarith)
  have := Real.rpow_lt_rpow (sobWeight_rpow_nonneg n _) h1 hst
  rwa [← Real.rpow_mul (sobWeight_pos n).le, mul_inv_cancel₀ (by linarith),
    Real.rpow_one] at this

/-- **Rellich–Kondrachov for a finite family, common subsequence** (`prop:sobolev-bosonic`):
finitely many sequences `f_k j ∈ L²(𝕋^d)` bounded in `H^{s_j}` (`s_j ≥ 0`) have one common
subsequence along which every component converges in `H^{t_j}`, `t_j < s_j`, to a limit in
`H^{s_j}`. -/
theorem rellich_L2_family {J : Type*} [Fintype J] (t s : J → ℝ) (hts : ∀ j, t j < s j)
    (hs0 : ∀ j, 0 ≤ s j) {B : ℝ} (f : ℕ → J → L²(UnitAddTorus d))
    (hf : ∀ k j, MemH (s j) (f k j)) (hB : ∀ k j, sobSq (s j) (f k j) ≤ B) :
    ∃ (φ : ℕ → ℕ) (g : J → L²(UnitAddTorus d)), StrictMono φ ∧ (∀ j, MemH (s j) (g j)) ∧
      (∀ k j, MemH (t j) ⇑(f (φ k) j - g j)) ∧
      ∀ j, Tendsto (fun k => sobSq (t j) ⇑(f (φ k) j - g j)) atTop (𝓝 0) := by
  classical
  set W : J × (d → ℤ) → ℝ := fun p => sobWeight p.2 ^ s p.1
  set V : J × (d → ℤ) → ℝ := fun p => sobWeight p.2 ^ t p.1
  set c : ℕ → J × (d → ℤ) → ℂ := fun k p => mFourierCoeff (f k p.1) p.2
  have hfin : ∀ R : ℝ, {p | W p < R * V p}.Finite := by
    intro R
    have e : {p | W p < R * V p} =
        ⋃ j, (fun n => (j, n)) '' {n : d → ℤ | sobWeight n ^ s j < R * sobWeight n ^ t j} := by
      ext ⟨j, n⟩
      simp [W, V]
    rw [e]
    exact Set.finite_iUnion fun j => (finite_sobWeight_rpow_lt (hts j) R).image _
  have hWnn : ∀ k, 0 ≤ fun p => W p * ‖c k p‖ ^ 2 := fun k p =>
    coeffSobSq_term_nonneg _ _ _
  have hsum : ∀ k, Summable fun p => W p * ‖c k p‖ ^ 2 := fun k =>
    (summable_prod_of_nonneg (hWnn k)).mpr ⟨fun j => hf k j, Summable.of_finite⟩
  have hB' : ∀ k, ∑' p, W p * ‖c k p‖ ^ 2 ≤ Fintype.card J * B := by
    intro k
    rw [(hsum k).tsum_prod' (fun j => hf k j), tsum_fintype]
    calc ∑ j, ∑' n, W (j, n) * ‖c k (j, n)‖ ^ 2 ≤ ∑ _j : J, B :=
          Finset.sum_le_sum fun j _ => hB k j
      _ = Fintype.card J * B := by simp
  obtain ⟨φ, cl, hφ, -, hcl, -, hV, hlim⟩ := FourierRellich.rellich_coefficients W V
    (fun p => sobWeight_rpow_pos _ _) (fun p => sobWeight_rpow_nonneg _ _) hfin c hsum hB'
  have hclnn : 0 ≤ fun p => W p * ‖cl p‖ ^ 2 := fun p =>
    mul_nonneg (sobWeight_rpow_nonneg _ _) (sq_nonneg _)
  have hclj : ∀ j, CoeffMemH (s j) (fun n => cl (j, n)) := fun j =>
    ((summable_prod_of_nonneg hclnn).mp hcl).1 j
  have hmem : ∀ j, Memℓp (fun n => cl (j, n)) 2 := by
    intro j
    refine memℓp_gen ?_
    have : Summable fun n => ‖cl (j, n)‖ ^ 2 :=
      Summable.of_nonneg_of_le (fun n => sq_nonneg _)
        (fun n => le_mul_of_one_le_left (sq_nonneg _) (one_le_sobWeight_rpow n (hs0 j)))
        (hclj j)
    simpa using this
  set g : J → L²(UnitAddTorus d) := fun j => mFourierBasis.repr.symm ⟨fun n => cl (j, n), hmem j⟩
  have hg : ∀ j n, mFourierCoeff (g j) n = cl (j, n) := by
    intro j n
    rw [← mFourierBasis_repr]
    simp [g]
  have hsub : ∀ k j, mFourierCoeff ⇑(f (φ k) j - g j) = fun n => c (φ k) (j, n) - cl (j, n) := by
    intro k j; funext n; rw [mFourierCoeff_Lp_sub, hg]
  have hVnn : ∀ k, 0 ≤ fun p => V p * ‖c (φ k) p - cl p‖ ^ 2 := fun k p =>
    mul_nonneg (sobWeight_rpow_nonneg _ _) (sq_nonneg _)
  have hVj : ∀ k j, Summable fun n => V (j, n) * ‖c (φ k) (j, n) - cl (j, n)‖ ^ 2 := fun k j =>
    ((summable_prod_of_nonneg (hVnn k)).mp (hV k)).1 j
  refine ⟨φ, g, hφ, fun j => ?_, fun k j => ?_, fun j => ?_⟩
  · show CoeffMemH (s j) (mFourierCoeff (g j))
    rw [funext (hg j)]
    exact hclj j
  · show CoeffMemH (t j) _
    rw [hsub]
    exact hVj k j
  · refine squeeze_zero (fun k => sobSq_nonneg _ _) (fun k => ?_) hlim
    unfold sobSq coeffSobSq
    rw [hsub, (hV k).tsum_prod' (hVj k)]
    conv_rhs => rw [tsum_fintype]
    exact Finset.single_le_sum
      (f := fun j => ∑' n, V (j, n) * ‖c (φ k) (j, n) - cl (j, n)‖ ^ 2)
      (fun j _ => tsum_nonneg fun n => (hVnn k) (j, n)) (mem_univ j)

/-- **`prop:sobolev-bosonic` on the periodic box `𝕋^d`** (torus rendering).  Frame components
`e_h` bounded in `H^{s_e}`, `s_e > max(1, d/2)` (`2 + σ` on `𝕋⁴`); gauge-potential components
`A_h` (matrix-valued, `r × r`) and Higgs components `H_h` bounded in `H^{s_A}`, `H^{s_H}`,
`s_A, s_H > max(1, d/4)` (`1 + σ` on `𝕋⁴`); coefficient banks `θ_h` in a compact set.  Then
along one subsequence:
* `e_h → e` strongly in `H¹`, and uniformly for the continuous representatives
  (so in `H¹ ∩ L^∞`);
* `A_h → A` and `H_h → H` strongly in `H¹` and in `L⁴`;
* `F_{A_h} → F_A` strongly in `L²` (`F = dA + A ∧ A`, weak derivatives);
* `D_{A_h} H_h → D_A H` strongly in `L²` (`D_A H = dH + ρ(A) H`, `ρ` given by `R`);
* `θ_h → θ ∈ K_θ`.
Not included: the manuscript's extra clause "`H_h` bounded in `L^{4+δ}`" (only `L⁴` is proved
here; strong `L⁴` convergence is what the quartic term needs). -/
theorem sobolev_bosonic_torus [DecidableEq d] {Je r r' : Type*} [Fintype Je] [Fintype r] [Fintype r'] {m : ℕ}
    {se sA sH : ℝ} (hse1 : 1 < se) (hse : (Fintype.card d : ℝ) / 2 < se) (hsA1 : 1 < sA)
    (hsA : (Fintype.card d : ℝ) / 4 < sA) (hsH1 : 1 < sH) (hsH : (Fintype.card d : ℝ) / 4 < sH)
    (R : r' → r' → r → r → ℂ) {B : ℝ}
    (e : ℕ → Je → L²(UnitAddTorus d)) (A : ℕ → d → r → r → L²(UnitAddTorus d))
    (H : ℕ → r' → L²(UnitAddTorus d))
    (he : ∀ k j, MemH se (e k j)) (heB : ∀ k j, sobSq se (e k j) ≤ B)
    (hA : ∀ k μ a b, MemH sA (A k μ a b)) (hAB : ∀ k μ a b, sobSq sA (A k μ a b) ≤ B)
    (hH : ∀ k a, MemH sH (H k a)) (hHB : ∀ k a, sobSq sH (H k a) ≤ B)
    (θ : ℕ → Fin m → ℝ) {Kθ : Set (Fin m → ℝ)} (hKθ : IsCompact Kθ) (hθ : ∀ k, θ k ∈ Kθ) :
    ∃ (φ : ℕ → ℕ) (e₀ : Je → L²(UnitAddTorus d)) (A₀ : d → r → r → L²(UnitAddTorus d))
      (H₀ : r' → L²(UnitAddTorus d)) (θ₀ : Fin m → ℝ) (E : ℕ → Je → C(UnitAddTorus d, ℂ))
      (E₀ : Je → C(UnitAddTorus d, ℂ)), StrictMono φ ∧
      (∀ j, Tendsto (fun k => sobSq 1 ⇑(e (φ k) j - e₀ j)) atTop (𝓝 0)) ∧
      (∀ k j, ⇑(e k j) =ᵐ[volume] ⇑(E k j)) ∧ (∀ j, ⇑(e₀ j) =ᵐ[volume] ⇑(E₀ j)) ∧
      (∀ j, Tendsto (fun k => ‖E (φ k) j - E₀ j‖) atTop (𝓝 0)) ∧
      (∀ μ a b, Tendsto (fun k => sobSq 1 ⇑(A (φ k) μ a b - A₀ μ a b)) atTop (𝓝 0)) ∧
      (∀ μ a b, Tendsto (fun k => eLpNorm (⇑(A (φ k) μ a b) - ⇑(A₀ μ a b)) 4 volume) atTop
        (𝓝 0)) ∧
      (∀ a, Tendsto (fun k => sobSq 1 ⇑(H (φ k) a - H₀ a)) atTop (𝓝 0)) ∧
      (∀ a, Tendsto (fun k => eLpNorm (⇑(H (φ k) a) - ⇑(H₀ a)) 4 volume) atTop (𝓝 0)) ∧
      (∀ μ ν a b, Tendsto (fun k => eLpNorm (curvature (A (φ k)) μ ν a b -
        curvature A₀ μ ν a b) 2 volume) atTop (𝓝 0)) ∧
      (∀ μ a, Tendsto (fun k => eLpNorm (covDeriv R (A (φ k)) (H (φ k)) μ a -
        covDeriv R A₀ H₀ μ a) 2 volume) atTop (𝓝 0)) ∧
      θ₀ ∈ Kθ ∧ Tendsto (fun k => θ (φ k)) atTop (𝓝 θ₀) := by
  classical
  obtain ⟨θ₀, hθ₀, ψ, hψ, hθlim⟩ := hKθ.tendsto_subseq hθ
  have hD : (0 : ℝ) ≤ (Fintype.card d : ℝ) := Nat.cast_nonneg _
  -- intermediate exponents
  set te : ℝ := (max 1 ((Fintype.card d : ℝ) / 2) + se) / 2 with hte
  set tA : ℝ := (max 1 ((Fintype.card d : ℝ) / 4) + sA) / 2 with htA
  set tH : ℝ := (max 1 ((Fintype.card d : ℝ) / 4) + sH) / 2 with htH
  have hm1 := le_max_left (1 : ℝ) ((Fintype.card d : ℝ) / 2)
  have hm2 := le_max_right (1 : ℝ) ((Fintype.card d : ℝ) / 2)
  have hm3 := le_max_left (1 : ℝ) ((Fintype.card d : ℝ) / 4)
  have hm4 := le_max_right (1 : ℝ) ((Fintype.card d : ℝ) / 4)
  have hmax2 : max 1 ((Fintype.card d : ℝ) / 2) < se := max_lt hse1 hse
  have hmaxA : max 1 ((Fintype.card d : ℝ) / 4) < sA := max_lt hsA1 hsA
  have hmaxH : max 1 ((Fintype.card d : ℝ) / 4) < sH := max_lt hsH1 hsH
  have hte1 : 1 < te := by rw [hte]; linarith
  have hte2 : (Fintype.card d : ℝ) / 2 < te := by rw [hte]; linarith
  have htes : te < se := by rw [hte]; linarith
  have htA1 : 1 < tA := by rw [htA]; linarith
  have htA4 : (Fintype.card d : ℝ) / 4 < tA := by rw [htA]; linarith
  have htAs : tA < sA := by rw [htA]; linarith
  have htH1 : 1 < tH := by rw [htH]; linarith
  have htH4 : (Fintype.card d : ℝ) / 4 < tH := by rw [htH]; linarith
  have htHs : tH < sH := by rw [htH]; linarith
  -- the combined family
  let J := Je ⊕ ((d × r × r) ⊕ r')
  let F : ℕ → J → L²(UnitAddTorus d) := fun k =>
    Sum.elim (e (ψ k)) (Sum.elim (fun q => A (ψ k) q.1 q.2.1 q.2.2) (H (ψ k)))
  let s : J → ℝ := Sum.elim (fun _ => se) (Sum.elim (fun _ => sA) (fun _ => sH))
  let t : J → ℝ := Sum.elim (fun _ => te) (Sum.elim (fun _ => tA) (fun _ => tH))
  have hts : ∀ j, t j < s j := by
    intro j; rcases j with j | j | j
    · exact htes
    · exact htAs
    · exact htHs
  have hs0 : ∀ j, 0 ≤ s j := by
    intro j; rcases j with j | j | j
    · show 0 ≤ se; linarith
    · show 0 ≤ sA; linarith
    · show 0 ≤ sH; linarith
  have hF : ∀ k j, MemH (s j) (F k j) := by
    intro k j; rcases j with j | ⟨μ, a, b⟩ | a
    · exact he _ j
    · exact hA _ μ a b
    · exact hH _ a
  have hFB : ∀ k j, sobSq (s j) (F k j) ≤ B := by
    intro k j; rcases j with j | ⟨μ, a, b⟩ | a
    · exact heB _ j
    · exact hAB _ μ a b
    · exact hHB _ a
  obtain ⟨φ', g, hφ', hgs, hdm, hdlim⟩ := rellich_L2_family t s hts hs0 F hF hFB
  set φ := ψ ∘ φ'
  set e₀ : Je → L²(UnitAddTorus d) := fun j => g (Sum.inl j)
  set A₀ : d → r → r → L²(UnitAddTorus d) := fun μ a b => g (Sum.inr (Sum.inl (μ, a, b)))
  set H₀ : r' → L²(UnitAddTorus d) := fun a => g (Sum.inr (Sum.inr a))
  -- component statements
  have hee : ∀ j, Tendsto (fun k => sobSq te ⇑(e (φ k) j - e₀ j)) atTop (𝓝 0) :=
    fun j => hdlim (Sum.inl j)
  have heem : ∀ k j, MemH te ⇑(e (φ k) j - e₀ j) := fun k j => hdm k (Sum.inl j)
  have he₀ : ∀ j, MemH se (e₀ j) := fun j => hgs (Sum.inl j)
  have hAA : ∀ μ a b, Tendsto (fun k => sobSq tA ⇑(A (φ k) μ a b - A₀ μ a b)) atTop (𝓝 0) :=
    fun μ a b => hdlim (Sum.inr (Sum.inl (μ, a, b)))
  have hAAm : ∀ k μ a b, MemH tA ⇑(A (φ k) μ a b - A₀ μ a b) := fun k μ a b =>
    hdm k (Sum.inr (Sum.inl (μ, a, b)))
  have hA₀ : ∀ μ a b, MemH sA (A₀ μ a b) := fun μ a b => hgs (Sum.inr (Sum.inl (μ, a, b)))
  have hHH : ∀ a, Tendsto (fun k => sobSq tH ⇑(H (φ k) a - H₀ a)) atTop (𝓝 0) :=
    fun a => hdlim (Sum.inr (Sum.inr a))
  have hHHm : ∀ k a, MemH tH ⇑(H (φ k) a - H₀ a) := fun k a => hdm k (Sum.inr (Sum.inr a))
  have hH₀ : ∀ a, MemH sH (H₀ a) := fun a => hgs (Sum.inr (Sum.inr a))
  -- lowering the exponent
  have lower : ∀ {t' t : ℝ} {u : ℕ → UnitAddTorus d → ℂ}, t' ≤ t → (∀ k, MemH t (u k)) →
      Tendsto (fun k => sobSq t (u k)) atTop (𝓝 0) →
      Tendsto (fun k => sobSq t' (u k)) atTop (𝓝 0) := fun h hm hl =>
    squeeze_zero (fun k => sobSq_nonneg _ _) (fun k => coeffSobSq_mono h (hm k)) hl
  -- continuous representatives of the frame
  choose E hE using fun k j => exists_continuous_of_memH hse (e k j) (he k j)
  choose E₀ hE₀ using fun j => exists_continuous_of_memH hse (e₀ j) (he₀ j)
  have hEunif : ∀ j, Tendsto (fun k => ‖E (φ k) j - E₀ j‖) atTop (𝓝 0) := by
    intro j
    have hdiff : ∀ k, mFourierCoeff ⇑(E (φ k) j - E₀ j) = mFourierCoeff ⇑(e (φ k) j - e₀ j) := by
      intro k; funext n
      rw [mFourierCoeff_continuous_sub, mFourierCoeff_Lp_sub, (hE (φ k) j).2.2.1 n,
        (hE₀ j).2.2.1 n]
    have hbound : ∀ k, ‖E (φ k) j - E₀ j‖ ≤
        embConst d te * Real.sqrt (sobSq te ⇑(e (φ k) j - e₀ j)) := by
      intro k
      have hmk : MemH te ⇑(E (φ k) j - E₀ j) := by
        show CoeffMemH te _; rw [hdiff]; exact heem k j
      have := norm_le_of_memH hte2 _ hmk
      unfold sobNorm sobSq at this
      rw [hdiff] at this
      exact this
    have hl : Tendsto (fun k => embConst d te * Real.sqrt (sobSq te ⇑(e (φ k) j - e₀ j))) atTop
        (𝓝 0) := by
      have := ((Real.continuous_sqrt.tendsto 0).comp (hee j)).const_mul (embConst d te)
      simpa [Function.comp_def] using this
    exact squeeze_zero (fun k => norm_nonneg _) hbound hl
  -- the common exponent for the covariant derivative
  set tm : ℝ := min tA tH
  have htm1 : 1 ≤ tm := le_min htA1.le htH1.le
  have htm4 : (Fintype.card d : ℝ) / 4 < tm := lt_min htA4 htH4
  refine ⟨φ, e₀, A₀, H₀, θ₀, E, E₀, hψ.comp hφ', fun j => lower hte1.le (heem · j) (hee j),
    fun k j => (hE k j).2.1, fun j => (hE₀ j).2.1, hEunif,
    fun μ a b => lower htA1.le (hAAm · μ a b) (hAA μ a b),
    fun μ a b => tendsto_eLpNorm_four_of_H htA4 (fun k => (hA (φ k) μ a b).mono htAs.le)
      ((hA₀ μ a b).mono htAs.le) (hAA μ a b),
    fun a => lower htH1.le (hHHm · a) (hHH a),
    fun a => tendsto_eLpNorm_four_of_H htH4 (fun k => (hH (φ k) a).mono htHs.le)
      ((hH₀ a).mono htHs.le) (hHH a),
    fun μ ν a b => tendsto_curvature_of_H htA1.le htA4
      (fun k μ a b => (hA (φ k) μ a b).mono htAs.le) (fun μ a b => (hA₀ μ a b).mono htAs.le)
      hAA μ ν a b,
    fun μ a => tendsto_covDeriv_of_H htm1 htm4 R
      (fun k μ a b => (hA (φ k) μ a b).mono (min_le_left _ _ |>.trans htAs.le))
      (fun μ a b => (hA₀ μ a b).mono (min_le_left _ _ |>.trans htAs.le))
      (fun k a => (hH (φ k) a).mono (min_le_right _ _ |>.trans htHs.le))
      (fun a => (hH₀ a).mono (min_le_right _ _ |>.trans htHs.le))
      (fun μ a b => lower (min_le_left _ _) (hAAm · μ a b) (hAA μ a b))
      (fun a => lower (min_le_right _ _) (hHHm · a) (hHH a)) μ a,
    hθ₀, hθlim.comp hφ'.tendsto_atTop⟩

/-- Non-vacuity of `sobolev_bosonic_torus`: its hypotheses are met on `𝕋⁴` (`s_e = 3`,
`s_A = s_H = 3/2`) by constant fields equal to the constant monomial, with an empty coefficient
bank. -/
example : ∃ φ : ℕ → ℕ, StrictMono φ := by
  set u : L²(UnitAddTorus (Fin 4)) := (mFourier (0 : Fin 4 → ℤ)).toLp 2 volume ℂ
  have hmem : ∀ s : ℝ, MemH s u := by
    intro s
    have := memH_mFourier (d := Fin 4) s 0
    unfold MemH CoeffMemH at this ⊢
    simp_rw [u, mFourierCoeff_toLp]
    exact this
  have hsq : ∀ s : ℝ, sobSq s u ≤ 1 := by
    intro s
    have h := sobSq_mFourier (d := Fin 4) s 0
    have e : sobSq s u = sobSq s ⇑(mFourier (0 : Fin 4 → ℤ)) := by
      unfold sobSq coeffSobSq
      simp_rw [u, mFourierCoeff_toLp]
    rw [e, h, show sobWeight (0 : Fin 4 → ℤ) = 1 by simp [sobWeight], Real.one_rpow]
  obtain ⟨φ, _, _, _, _, _, _, hφ, -⟩ := sobolev_bosonic_torus (d := Fin 4) (Je := Fin 1)
    (r := Fin 1) (r' := Fin 1) (m := 0) (se := 3) (sA := 3 / 2) (sH := 3 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun _ _ _ _ => 0) (B := 1) (fun _ _ => u) (fun _ _ _ _ => u) (fun _ _ => u)
    (fun _ _ => hmem 3) (fun _ _ => hsq 3) (fun _ _ _ _ => hmem _) (fun _ _ _ _ => hsq _)
    (fun _ _ => hmem _) (fun _ _ => hsq _) (fun _ => 0) isCompact_singleton (fun _ => rfl)
  exact ⟨φ, hφ⟩

end

end RenewalGeometry.TorusSobolev
