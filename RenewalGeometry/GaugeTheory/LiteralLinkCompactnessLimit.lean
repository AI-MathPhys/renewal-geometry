/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.GaugeTheory.LiteralLinkLimitGrid

/-!
# Gauge-free anisotropic literal-link compactness (`thm:main-literal-link-compactness`)

Emergent-spacetime manuscript, `thm:main-literal-link-compactness` (proof in
`subsubsec:supp-literal-link-compactness`).  On odd periodic grids `(ℤ/N_m)³`, `h_m = 1/N_m → 0`,
complex `n × n` matrix link histories `U_{i}(t,x) = exp(h A_i(t,x))` on the identity chart
`h‖A_i‖ ≤ δ_* ≤ 1/16`, a temporal coefficient `A₀`, the literal electric records
`E_i U_i = (∂ₜU_i + A₀U_i − U_i S_iA₀)/h` (`elecRec`) and the literal magnetic records
`F_{ij}` (`h⁻²`-logarithmic plaquette coefficients, `magRec`), bounded as in `eq:main-link-energy`:

  `sup_m (‖A‖_{L^∞_t L²_h} + ‖A‖_{L²_t H¹_h} + ‖A₀‖_{L²} + ‖E‖_{L²} + ‖F‖_{L²}) < ∞`.

`literal_link_compactness` proves: after extraction,
* `𝓘_h A_i → A_i` strongly in `L²((0,T] × 𝕋³)` (entrywise), `𝓘_h A₀ ⇀ A₀`, `𝓘_h E_i ⇀ E_i`,
  `𝓘_h F_{ij} ⇀ F_{ij}` weakly in `L²` (`eq:main-link-convergence`);
* the weak limits are the components of `R(ω) = dω + ω ∧ ω`, `ω = A₀ dt + Σ A_i dx^i`
  (`eq:main-link-curvature-limit`):
  `E_i = ∂ₜA_i − ∂_iA₀ − [A_i, A₀]` (`eq:supp-literal-electric-limit`) and
  `F_{ij} = ∂_iA_j − ∂_jA_i + [A_i, A_j]` (`eq:supp-literal-magnetic-limit`), in distributions on
  `(0,T) × 𝕋³`, tested against the total family `ψ(t,x) = χ(t) e_k(x)` (`χ ∈ C¹_c(0,T)`,
  `k ∈ ℤ³`; for the magnetic identity any continuous `χ`).

No Coulomb condition, gauge smallness, temporal-mean, `D⁺A₀` or `∂ₜA₀` bound is used; `A₀` is only
weakly convergent.
-/

open MeasureTheory Filter Topology UnitAddTorus
open scoped ComplexConjugate Matrix.Norms.Frobenius

noncomputable section

set_option linter.unusedSectionVars false

namespace RenewalGeometry.LiteralLinkLimit

open PeriodicGridSobolev LatticeTorusPlancherel GridAubinLions LiteralLink LiteralLinkCompactness

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : MeasureTheory.IsProbabilityMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ### Time regularity helpers -/

section Helpers

variable {N : ℕ} [NeZero N] {n : ℕ} {T : ℝ}

theorem integrableOn_Ioc_of_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    IntegrableOn f (Set.Ioc 0 T) :=
  (hf.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self

theorem memLp_Ioc_of_continuous {f : ℝ → ℂ} (hf : Continuous f) :
    MemLp f 2 (volume.restrict (Set.Ioc 0 T)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := 0) (b := T)).exists_bound_of_continuousOn
    hf.continuousOn
  refine MemLp.of_bound hf.aestronglyMeasurable C ?_
  exact (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun t ht =>
    hC t (Set.Ioc_subset_Icc_self ht))

theorem isL2Grid_of_continuous {u : ℝ → Grid N → ℂ} (hu : ∀ x, Continuous fun t => u t x) :
    IsL2Grid T u :=
  ⟨fun x => (hu x).aestronglyMeasurable,
    integrableOn_Ioc_of_continuous (continuous_gridNormSq.comp (continuous_pi hu))⟩

theorem integrableOn_coordForm_of_continuous {u : ℝ → Grid N → ℂ}
    (hu : ∀ x, Continuous fun t => u t x) :
    IntegrableOn (fun t => coordForm (u t)) (Set.Ioc 0 T) :=
  integrableOn_Ioc_of_continuous (continuous_coordForm.comp (continuous_pi hu))

theorem isGridW12Rep_of_hasDerivAt {u u' : ℝ → Grid N → ℂ}
    (hd : ∀ x t, HasDerivAt (fun s => u s x) (u' t x) t) (hc : ∀ x, Continuous fun t => u' t x) :
    IsGridW12Rep T u u' := by
  intro x
  refine ⟨memLp_Ioc_of_continuous (hc x), fun t _ => ?_⟩
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
    (fun s _ => hd x s) ((hc x).intervalIntegrable _ _)
  rw [this]; ring

theorem gridNormSq_entry_le (u : MatArr N n) (a b : Fin n) :
    gridNormSq (entry u a b) ≤ matNormSq u := by
  unfold matNormSq
  refine (Finset.single_le_sum (f := fun b => gridNormSq (entry u a b))
    (fun _ _ => gridNormSq_nonneg _) (Finset.mem_univ b)).trans ?_
  exact Finset.single_le_sum (f := fun a => ∑ b, gridNormSq (entry u a b))
    (fun _ _ => Finset.sum_nonneg fun _ _ => gridNormSq_nonneg _) (Finset.mem_univ a)

theorem coordForm_entry_le (u : MatArr N n) (a b : Fin n) :
    coordForm (entry u a b) ≤ ∑ j, matNormSq (matDp j u) := by
  have h2 : ∑ a, ∑ b, coordForm (entry u a b) = ∑ j, matNormSq (matDp j u) := by
    rw [← sum_entry_coordForm u, Fintype.sum_prod_type]
  rw [← h2]
  refine (Finset.single_le_sum (f := fun b => coordForm (entry u a b))
    (fun _ _ => coordForm_nonneg _) (Finset.mem_univ b)).trans ?_
  exact Finset.single_le_sum (f := fun a => ∑ b, coordForm (entry u a b))
    (fun _ _ => Finset.sum_nonneg fun _ _ => coordForm_nonneg _) (Finset.mem_univ a)

theorem isL2Grid_entry {u : ℝ → MatArr N n}
    (hm : ∀ x a b, AEStronglyMeasurable (fun t => u t x a b) (volume.restrict (Set.Ioc 0 T)))
    (hi : IntegrableOn (fun t => matNormSq (u t)) (Set.Ioc 0 T)) (a b : Fin n) :
    IsL2Grid T (fun t => entry (u t) a b) := by
  refine ⟨fun x => hm x a b, Integrable.mono' hi ?_ (ae_of_all _ fun t => ?_)⟩
  · have : (fun t => gridNormSq (entry (u t) a b)) = fun t =>
        ((N : ℝ) ^ 3)⁻¹ * ∑ x, ‖u t x a b‖ ^ 2 := rfl
    rw [this]
    exact (Finset.aestronglyMeasurable_fun_sum _ fun x _ => (hm x a b).norm.pow 2).const_mul _
  · rw [Real.norm_of_nonneg (gridNormSq_nonneg _)]
    exact gridNormSq_entry_le _ a b

theorem integral_gridNormSq_entry_le {u : ℝ → MatArr N n}
    (hi : IntegrableOn (fun t => matNormSq (u t)) (Set.Ioc 0 T)) (a b : Fin n) :
    ∫ t in Set.Ioc 0 T, gridNormSq (entry (u t) a b) ≤ ∫ t in Set.Ioc 0 T, matNormSq (u t) :=
  integral_mono_of_nonneg (ae_of_all _ fun _ => gridNormSq_nonneg _) hi
    (ae_of_all _ fun t => gridNormSq_entry_le _ a b)

theorem entry_linkZ (A : MatArr N n) (x : Grid N) (a b : Fin n) :
    linkZ A x a b = (N : ℂ) * (linkU A x a b - (1 : Matrix (Fin n) (Fin n) ℂ) a b) := by
  simp only [linkZ, Matrix.smul_apply, Matrix.sub_apply, Complex.real_smul]
  push_cast; simp

theorem entry_smul_U' (U' : MatArr N n) (x : Grid N) (a b : Fin n) :
    (((N : ℝ)⁻¹)⁻¹ • U' x) a b = (N : ℂ) * U' x a b := by
  simp only [Matrix.smul_apply, Complex.real_smul]
  push_cast; simp

/-- Integration by parts in time for a tested grid array against `χ ∈ C¹_c(0,T)`. -/
theorem integral_deriv_mul_gp (hT : 0 < T) {u u' : ℝ → Grid N → ℂ}
    (hd : ∀ x t, HasDerivAt (fun s => u s x) (u' t x) t) (hc : ∀ x, Continuous fun t => u' t x)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) (hsupp : tsupport χ ⊆ Set.Ioo 0 T) (k : Fin 3 → ℤ) :
    ∫ t in Set.Ioc 0 T, ((deriv χ t : ℝ) : ℂ) * gp k oneArr (u t) =
      -∫ t in Set.Ioc 0 T, ((χ t : ℝ) : ℂ) * gp k oneArr (u' t) := by
  have hdv : ∀ t, HasDerivAt (fun s => gp k oneArr (u s)) (gp k oneArr (u' t)) t := by
    intro t
    unfold gp
    refine HasDerivAt.const_mul _ ?_
    exact HasDerivAt.fun_sum fun x _ => (hd x t).const_mul _
  have hdχ : ∀ t, HasDerivAt (fun s => ((χ s : ℝ) : ℂ)) ((deriv χ t : ℝ) : ℂ) t := fun t =>
    ((hχ.differentiable one_ne_zero t).hasDerivAt).ofReal_comp
  have hcv' : Continuous fun t => gp k oneArr (u' t) := by
    unfold gp
    exact continuous_const.mul (continuous_finset_sum _ fun x _ => continuous_const.mul (hc x))
  have hcχ' : Continuous fun t => ((deriv χ t : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (hχ.continuous_deriv le_rfl)
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := T)
    (fun t _ => hdχ t) (fun t _ => hdv t) (hcχ'.intervalIntegrable _ _)
    (hcv'.intervalIntegrable _ _)
  have h0 : χ 0 = 0 := image_eq_zero_of_notMem_tsupport fun h => (hsupp h).1.false
  have hT0 : χ T = 0 := image_eq_zero_of_notMem_tsupport fun h => (lt_irrefl _ (hsupp h).2)
  rw [h0, hT0] at h
  simp only [Complex.ofReal_zero, zero_mul, sub_zero, zero_sub] at h
  rw [intervalIntegral.integral_of_le hT.le, intervalIntegral.integral_of_le hT.le] at h
  rw [h, neg_neg]

end Helpers

/-! ### Weak extraction of bounded matrix records -/

section Extraction

variable {n : ℕ} {T : ℝ} {Nm : ℕ → ℕ} [∀ m, NeZero (Nm m)]

/-- **Weak extraction** for finitely many `L²((0,T]; L²_h)`-bounded families of matrix records:
along a subsequence every entry interpolant converges weakly in `L²((0,T] × 𝕋³)`. -/
theorem exists_weakSeq_entries {ι : Type*} [Fintype ι] (f : ι → ∀ m, ℝ → MatArr (Nm m) n)
    (hm : ∀ l m x a b, AEStronglyMeasurable (fun t => f l m t x a b) (volume.restrict (Set.Ioc 0 T)))
    (hi : ∀ l m, IntegrableOn (fun t => matNormSq (f l m t)) (Set.Ioc 0 T)) {B : ℝ}
    (hB : ∀ l m, ∫ t in Set.Ioc 0 T, matNormSq (f l m t) ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : ι → Fin n → Fin n → ℝ × UnitAddTorus (Fin 3) → ℂ,
      ∀ l a b, MemLp (G l a b) 2 (cylMeasure T) ∧
        WeakSeq (fun m => Nm (φ m)) T (fun m t => entry (f l (φ m) t) a b) (G l a b) := by
  have hL2 : ∀ l m a b, IsL2Grid T (fun t => entry (f l m t) a b) := fun l m a b =>
    isL2Grid_entry (hm l m) (hi l m) a b
  obtain ⟨φ, hφ, G, hG⟩ := exists_subseq_weakL2 (μ := cylMeasure T)
    (fun (c : ι × Fin n × Fin n) m => field (fun t => entry (f c.1 m t) c.2.1 c.2.2))
    (fun c m => memLp_field_of_isL2Grid (hL2 c.1 m c.2.1 c.2.2)) (B := B) (fun c m => by
      rw [integral_norm_field_sq (hL2 c.1 m c.2.1 c.2.2)]
      exact (integral_gridNormSq_entry_le (hi c.1 m) _ _).trans (hB c.1 m))
  refine ⟨φ, hφ, fun l a b => G (l, a, b), fun l a b => ⟨(hG (l, a, b)).1, ?_, (hG (l, a, b)).2,
    ⟨B, fun m => (integral_gridNormSq_entry_le (hi l (φ m)) _ _).trans (hB l (φ m))⟩⟩⟩
  exact fun m => hL2 l (φ m) a b

end Extraction

/-! ### The distributional curvature identities -/

section Identities

variable {n : ℕ} {T : ℝ} {Nm : ℕ → ℕ} [∀ m, NeZero (Nm m)]

/-- The cylinder pairing `∫_{(0,T] × 𝕋³} χ(t) e_k(x) f(t,x)` with the test `ψ = χ ⊗ e_k`. -/
def cylPair (T : ℝ) (χ : ℝ → ℝ) (k : Fin 3 → ℤ) (f : ℝ × UnitAddTorus (Fin 3) → ℂ) : ℂ :=
  ∫ p, ((χ p.1 : ℝ) : ℂ) * mFourier k p.2 * f p ∂cylMeasure T

theorem limit_form_eq (χ : ℝ → ℝ) (k : Fin 3 → ℤ) (U G : ℝ × UnitAddTorus (Fin 3) → ℂ) :
    ∫ p, ((χ p.1 : ℝ) : ℂ) * (mFourier k p.2 * U p) * G p ∂cylMeasure T =
      ∫ p, ((χ p.1 : ℝ) : ℂ) * mFourier k p.2 * (U p * G p) ∂cylMeasure T := by
  congr 1; funext p; ring

theorem bound_of_compact_support {χ : ℝ → ℝ} (hχ : Continuous χ) (hsupp : tsupport χ ⊆ Set.Ioo 0 T) :
    ∃ C, 0 ≤ C ∧ ∀ t, ‖((χ t : ℝ) : ℂ)‖ ≤ C := by
  have hcs : HasCompactSupport χ :=
    (isCompact_Icc (a := 0) (b := T)).of_isClosed_subset (isClosed_tsupport _)
      (hsupp.trans Set.Ioo_subset_Icc_self)
  obtain ⟨C, hC⟩ := hχ.bounded_above_of_compact_support hcs
  exact ⟨C ⊔ 0, le_sup_right, fun t => by rw [Complex.norm_real]; exact (hC t).trans le_sup_left⟩

theorem bound_on_Icc {χ : ℝ → ℝ} (hχ : Continuous χ) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Set.Ioc 0 T, ‖((χ t : ℝ) : ℂ)‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := 0) (b := T)).exists_bound_of_continuousOn
    hχ.continuousOn
  exact ⟨C ⊔ 0, le_sup_right, fun t ht => by
    rw [Complex.norm_real]; exact (hC t (Set.Ioc_subset_Icc_self ht)).trans le_sup_left⟩

/-- Linearity of the time integral over a five-term combination. -/
theorem integral_combo {μ : Measure ℝ} {f1 f3 : ℝ → ℂ} {f2 f4 f5 : Fin n → ℝ → ℂ}
    (h1 : Integrable f1 μ) (h2 : ∀ c, Integrable (f2 c) μ) (h3 : Integrable f3 μ)
    (h4 : ∀ c, Integrable (f4 c) μ) (h5 : ∀ c, Integrable (f5 c) μ) (α β : ℂ) :
    ∫ t, (f1 t + ∑ c, f2 c t + α * f3 t + β * ∑ c, f4 c t - ∑ c, f5 c t) ∂μ =
      ∫ t, f1 t ∂μ + ∑ c, ∫ t, f2 c t ∂μ + α * ∫ t, f3 t ∂μ + β * ∑ c, ∫ t, f4 c t ∂μ -
        ∑ c, ∫ t, f5 c t ∂μ := by
  have i2 : Integrable (fun t => ∑ c, f2 c t) μ := integrable_finset_sum _ fun c _ => h2 c
  have i4 : Integrable (fun t => ∑ c, f4 c t) μ := integrable_finset_sum _ fun c _ => h4 c
  have i5 : Integrable (fun t => ∑ c, f5 c t) μ := integrable_finset_sum _ fun c _ => h5 c
  have j3 : Integrable (fun t => α * f3 t) μ := h3.const_mul α
  have j4 : Integrable (fun t => β * ∑ c, f4 c t) μ := i4.const_mul β
  have g1 : Integrable (fun t => f1 t + ∑ c, f2 c t) μ := h1.add i2
  have g2 : Integrable (fun t => f1 t + ∑ c, f2 c t + α * f3 t) μ := g1.add j3
  have g3 : Integrable (fun t => f1 t + ∑ c, f2 c t + α * f3 t + β * ∑ c, f4 c t) μ := g2.add j4
  rw [integral_sub g3 i5, integral_add g2 j4, integral_add g1 j3, integral_add h1 i2,
    integral_const_mul, integral_const_mul, integral_finset_sum _ fun c _ => h2 c,
    integral_finset_sum _ fun c _ => h4 c, integral_finset_sum _ fun c _ => h5 c]

theorem IsL2Grid.smul_left {N : ℕ} [NeZero N] {u : ℝ → Grid N → ℂ} (hu : IsL2Grid T u) (c : ℂ) :
    IsL2Grid T (fun t x => c * u t x) := by
  refine ⟨fun x => (hu.1 x).const_mul _, ?_⟩
  simp only [gridNormSq_smul]
  exact hu.2.const_mul _

theorem IsL2Grid.shiftBack' {N : ℕ} [NeZero N] {u : ℝ → Grid N → ℂ} (hu : IsL2Grid T u)
    (i : Fin 3) : IsL2Grid T (fun t => shiftBack i (u t)) := by
  refine ⟨fun x => hu.1 _, ?_⟩
  simp only [gridNormSq_shiftBack]; exact hu.2

/-- The tested exact electric identity on one odd grid, integrated against `χ ∈ C¹_c(0,T)`. -/
theorem electric_grid_identity {N : ℕ} [NeZero N] (hN : Odd N) (hT : 0 < T)
    (A : ℝ → Fin 3 → MatArr N n) (A₀ : ℝ → MatArr N n) (U' : ℝ → Fin 3 → MatArr N n)
    (i : Fin 3)
    (hU' : ∀ x a b t, HasDerivAt (fun s => linkU (A s i) x a b) (U' t i x a b) t)
    (hU'c : ∀ x a b, Continuous fun t => U' t i x a b)
    (a b : Fin n) (k : Fin 3 → ℤ) {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hsupp : tsupport χ ⊆ Set.Ioo 0 T) {C : ℝ} (hC : ∀ t, ‖((χ t : ℝ) : ℂ)‖ ≤ C)
    (hEl : ∀ c, IsL2Grid T (fun t => entry (elecRec i (A t i) (U' t i) (A₀ t)) a c))
    (hA₀l : ∀ c d, IsL2Grid T (fun t => entry (A₀ t) c d))
    (hZl : ∀ c d, IsL2Grid T (fun t => entry (linkZ (A t i)) c d)) :
    -(∫ t in Set.Ioc 0 T, ((deriv χ t : ℝ) : ℂ) * gp k oneArr (entry (linkZ (A t i)) a b)) =
      (∫ t in Set.Ioc 0 T, ((χ t : ℝ) : ℂ) *
          gp k oneArr (entry (elecRec i (A t i) (U' t i) (A₀ t)) a b))
      + ∑ c, (∫ t in Set.Ioc 0 T, ((χ t : ℝ) : ℂ) *
          gp k (fun x => ((N : ℂ))⁻¹ * entry (linkZ (A t i)) c b x)
            (entry (elecRec i (A t i) (U' t i) (A₀ t)) a c))
      + ((N : ℂ) * (conj (modChar (N := N) k (unit i)) - 1)) *
          (∫ t in Set.Ioc 0 T, ((χ t : ℝ) : ℂ) * gp k oneArr (entry (A₀ t) a b))
      + conj (modChar (N := N) k (unit i)) * ∑ c, (∫ t in Set.Ioc 0 T, ((χ t : ℝ) : ℂ) *
          gp k (shiftBack i (entry (linkZ (A t i)) a c)) (entry (A₀ t) c b))
      - ∑ c, (∫ t in Set.Ioc 0 T, ((χ t : ℝ) : ℂ) *
          gp k (entry (linkZ (A t i)) c b) (entry (A₀ t) a c)) := by
  have hψm : AEStronglyMeasurable (fun t => ((χ t : ℝ) : ℂ)) (volume.restrict (Set.Ioc 0 T)) :=
    (Complex.continuous_ofReal.comp hχ.continuous).aestronglyMeasurable
  have hd : ∀ x t, HasDerivAt (fun s => entry (linkZ (A s i)) a b x)
      (entry (fun x => ((N : ℝ)⁻¹)⁻¹ • U' t i x) a b x) t := by
    intro x t
    have h := ((hU' x a b t).sub_const ((1 : Matrix (Fin n) (Fin n) ℂ) a b)).const_mul (N : ℂ)
    simp only [entry]
    rw [entry_smul_U']
    exact h.congr_of_eventuallyEq (Eventually.of_forall fun s => entry_linkZ _ _ _ _)
  have hWc : ∀ x, Continuous fun t => entry (fun x => ((N : ℝ)⁻¹)⁻¹ • U' t i x) a b x := by
    intro x
    simp only [entry, entry_smul_U']
    exact continuous_const.mul (hU'c x a b)
  rw [integral_deriv_mul_gp hT hd hWc hχ hsupp k, neg_neg]
  set ζ : ℂ := conj (modChar (N := N) k (unit i))
  set F1 : ℝ → ℂ := fun t => ((χ t : ℝ) : ℂ) *
    gp k oneArr (entry (elecRec i (A t i) (U' t i) (A₀ t)) a b) with hF1
  set F2 : Fin n → ℝ → ℂ := fun c t => ((χ t : ℝ) : ℂ) *
    gp k (fun x => ((N : ℂ))⁻¹ * entry (linkZ (A t i)) c b x)
      (entry (elecRec i (A t i) (U' t i) (A₀ t)) a c) with hF2
  set F3 : ℝ → ℂ := fun t => ((χ t : ℝ) : ℂ) * gp k oneArr (entry (A₀ t) a b) with hF3
  set F4 : Fin n → ℝ → ℂ := fun c t => ((χ t : ℝ) : ℂ) *
    gp k (shiftBack i (entry (linkZ (A t i)) a c)) (entry (A₀ t) c b) with hF4
  set F5 : Fin n → ℝ → ℂ := fun c t => ((χ t : ℝ) : ℂ) *
    gp k (entry (linkZ (A t i)) c b) (entry (A₀ t) a c) with hF5
  have e : ∀ t, ((χ t : ℝ) : ℂ) * gp k oneArr (entry (fun x => ((N : ℝ)⁻¹)⁻¹ • U' t i x) a b) =
      F1 t + ∑ c, F2 c t + ((N : ℂ) * (ζ - 1)) * F3 t + ζ * ∑ c, F4 c t - ∑ c, F5 c t := by
    intro t
    rw [gp_linkTime k i (A t i) (U' t i) (A₀ t) a b]
    simp only [hF1, hF2, hF3, hF4, hF5, ← Finset.mul_sum]
    ring
  have i1 : Integrable F1 (volume.restrict (Set.Ioc 0 T)) :=
    integrableOn_gp hN (IsL2Grid.const _) (hEl b) hψm hC k
  have i2 : ∀ c, Integrable (F2 c) (volume.restrict (Set.Ioc 0 T)) :=
    fun c => integrableOn_gp hN ((hZl c b).smul_left _) (hEl c) hψm hC k
  have i3 : Integrable F3 (volume.restrict (Set.Ioc 0 T)) :=
    integrableOn_gp hN (IsL2Grid.const _) (hA₀l a b) hψm hC k
  have i4 : ∀ c, Integrable (F4 c) (volume.restrict (Set.Ioc 0 T)) :=
    fun c => integrableOn_gp hN ((hZl a c).shiftBack' i) (hA₀l c b) hψm hC k
  have i5 : ∀ c, Integrable (F5 c) (volume.restrict (Set.Ioc 0 T)) :=
    fun c => integrableOn_gp hN (hZl c b) (hA₀l a c) hψm hC k
  rw [integral_congr_ae (ae_of_all _ e)]
  exact integral_combo i1 i2 i3 i4 i5 _ _

theorem tendsto_inv_natCast_cpx {Nm : ℕ → ℕ} (hN : Tendsto Nm atTop atTop) :
    Tendsto (fun m => ((Nm m : ℂ))⁻¹) atTop (𝓝 0) := by
  have h1 : Tendsto (fun m => ((Nm m : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hN)
  have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
  simpa [Function.comp_def] using h2

theorem norm_inv_natCast_cpx_le (N : ℕ) [NeZero N] : ‖((N : ℂ))⁻¹‖ ≤ 1 := by
  rw [norm_inv, Complex.norm_natCast]
  exact inv_le_one_of_one_le₀ (Nat.one_le_cast.2 (Nat.pos_of_ne_zero (NeZero.ne _)))

theorem tendsto_conj_modChar_unit {Nm : ℕ → ℕ} [∀ m, NeZero (Nm m)]
    (hN : Tendsto Nm atTop atTop) (k : Fin 3 → ℤ) (i : Fin 3) :
    Tendsto (fun m => conj (modChar (N := Nm m) k (unit i))) atTop (𝓝 1) := by
  have h := (tendsto_natCast_mul_modChar_unit hN k i).mul (tendsto_inv_natCast_cpx hN)
  rw [mul_zero] at h
  have e : ∀ m, (Nm m : ℂ) * (conj (modChar (N := Nm m) k (unit i)) - 1) * ((Nm m : ℂ))⁻¹ =
      conj (modChar (N := Nm m) k (unit i)) - 1 := fun m => by
    field_simp [Nat.cast_ne_zero.2 (NeZero.ne (Nm m))]
  simp only [e] at h
  simpa using h.add_const 1

/-- **Electric curvature identity** (`eq:supp-literal-electric-limit`).  Along odd grids
`N_m → ∞`, let the link coordinates `Z = (e^{hA} − I)/h` converge strongly (entrywise) to `Ω`,
and let `A₀` and the literal electric records `E_i` converge weakly to `A₀^∞`, `E_i^∞`.  Then for
`χ ∈ C¹_c(0,T)` and `k ∈ ℤ³`, with `ψ = χ e_k`,
`−⟨Ω_i, ∂ₜψ⟩ = ⟨E_i^∞, ψ⟩ + ⟨Ω_i A₀^∞ − A₀^∞ Ω_i, ψ⟩ − 2πi k_i ⟨A₀^∞, ψ⟩`,
i.e. `∂ₜΩ_i = E_i^∞ + ∂_iA₀^∞ + Ω_iA₀^∞ − A₀^∞Ω_i` in distributions. -/
theorem electric_identity (hT : 0 < T) (hodd : ∀ m, Odd (Nm m)) (hN : Tendsto Nm atTop atTop)
    (A : ∀ m, ℝ → Fin 3 → MatArr (Nm m) n) (A₀ : ∀ m, ℝ → MatArr (Nm m) n)
    (U' : ∀ m, ℝ → Fin 3 → MatArr (Nm m) n)
    (hU' : ∀ m i x a b t, HasDerivAt (fun s => linkU (A m s i) x a b) (U' m t i x a b) t)
    (hU'c : ∀ m i x a b, Continuous fun t => U' m t i x a b)
    {Ω : Fin 3 → Fin n → Fin n → ℝ × UnitAddTorus (Fin 3) → ℂ}
    {A₀lim : Fin n → Fin n → ℝ × UnitAddTorus (Fin 3) → ℂ}
    {Elim : Fin 3 → Fin n → Fin n → ℝ × UnitAddTorus (Fin 3) → ℂ}
    (hZ : ∀ i a b, StrongSeq Nm T (fun m t => entry (linkZ (A m t i)) a b) (Ω i a b))
    (hA₀ : ∀ a b, WeakSeq Nm T (fun m t => entry (A₀ m t) a b) (A₀lim a b))
    (hE : ∀ i a b, WeakSeq Nm T (fun m t => entry (elecRec i (A m t i) (U' m t i) (A₀ m t)) a b)
      (Elim i a b))
    (i : Fin 3) (a b : Fin n) (k : Fin 3 → ℤ) {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hsupp : tsupport χ ⊆ Set.Ioo 0 T) :
    -cylPair T (deriv χ) k (Ω i a b) =
      cylPair T χ k (Elim i a b)
      + ∑ c, cylPair T χ k (fun p => Ω i a c p * A₀lim c b p)
      - ∑ c, cylPair T χ k (fun p => A₀lim a c p * Ω i c b p)
      - 2 * Real.pi * Complex.I * k i * cylPair T χ k (A₀lim a b) := by
  have hχc : Continuous χ := hχ.continuous
  have hχ'c : Continuous (deriv χ) := hχ.continuous_deriv le_rfl
  obtain ⟨C, hC0, hC⟩ := bound_of_compact_support hχc hsupp
  obtain ⟨C', hC0', hC'⟩ := bound_of_compact_support hχ'c (tsupport_deriv_subset.trans hsupp)
  have hψm : AEStronglyMeasurable (fun t => ((χ t : ℝ) : ℂ)) (volume.restrict (Set.Ioc 0 T)) :=
    (Complex.continuous_ofReal.comp hχc).aestronglyMeasurable
  have hψ'm : AEStronglyMeasurable (fun t => ((deriv χ t : ℝ) : ℂ))
      (volume.restrict (Set.Ioc 0 T)) :=
    (Complex.continuous_ofReal.comp hχ'c).aestronglyMeasurable
  have hZh : ∀ c, StrongSeq Nm T (fun m t x => ((Nm m : ℂ))⁻¹ * entry (linkZ (A m t i)) c b x)
      (fun _ => 0) := fun c =>
    (hZ i c b).smul_zero _ (tendsto_inv_natCast_cpx hN) fun m => norm_inv_natCast_cpx_le _
  have hZs : ∀ c, StrongSeq Nm T
      (fun m t => shiftBack i (entry (linkZ (A m t i)) a c)) (Ω i a c) :=
    fun c => (hZ i a c).shiftBack hN i
  have L0 := tendsto_gp hodd hN (StrongSeq.one (Nm := Nm) (T := T)) (hZ i a b).toWeak hψ'm hC0'
    hC' k
  have L1 := tendsto_gp hodd hN (StrongSeq.one (Nm := Nm) (T := T)) (hE i a b) hψm hC0 hC k
  have L2 := fun c => tendsto_gp hodd hN (hZh c) (hE i a c) hψm hC0 hC k
  have L3 := tendsto_gp hodd hN (StrongSeq.one (Nm := Nm) (T := T)) (hA₀ a b) hψm hC0 hC k
  have L4 := fun c => tendsto_gp hodd hN (hZs c) (hA₀ c b) hψm hC0 hC k
  have L5 := fun c => tendsto_gp hodd hN (hZ i c b) (hA₀ a c) hψm hC0 hC k
  have hα := tendsto_natCast_mul_modChar_unit hN k i
  have hζ := tendsto_conj_modChar_unit hN k i
  have Lrhs := ((((L1.add (tendsto_finset_sum Finset.univ fun c _ => L2 c)).add
    (hα.mul L3)).add (hζ.mul (tendsto_finset_sum Finset.univ fun c _ => L4 c))).sub
    (tendsto_finset_sum Finset.univ fun c _ => L5 c))
  have heq : ∀ m, -(∫ t in Set.Ioc 0 T, ((deriv χ t : ℝ) : ℂ) *
      gp k oneArr (entry (linkZ (A m t i)) a b)) = _ := fun m =>
    electric_grid_identity (hodd m) hT (A m) (A₀ m) (U' m) i (hU' m i) (hU'c m i) a b k hχ hsupp
      hC (fun c => (hE i a c).isL2 m) (fun c d => (hA₀ c d).isL2 m) (fun c d => (hZ i c d).isL2 m)
  have huniq := tendsto_nhds_unique (L0.neg.congr heq) Lrhs
  simp only [mul_one, mul_zero, zero_mul, integral_zero, Finset.sum_const_zero, add_zero,
    one_mul, limit_form_eq] at huniq
  unfold cylPair
  have e5 : ∀ c, ∫ p, ((χ p.1 : ℝ) : ℂ) * mFourier k p.2 * (A₀lim a c p * Ω i c b p)
      ∂cylMeasure T = ∫ p, ((χ p.1 : ℝ) : ℂ) * mFourier k p.2 * (Ω i c b p * A₀lim a c p)
      ∂cylMeasure T := fun c => by congr 1; funext p; ring
  simp only [e5]
  linear_combination huniq


/-- Linearity of the time integral over the magnetic five-term combination. -/
theorem integral_combo' {μ : Measure ℝ} {f1 f2 f5 : ℝ → ℂ} {f3 f4 : Fin n → ℝ → ℂ}
    (h1 : Integrable f1 μ) (h2 : Integrable f2 μ) (h3 : ∀ c, Integrable (f3 c) μ)
    (h4 : ∀ c, Integrable (f4 c) μ) (h5 : Integrable f5 μ) (α β : ℂ) :
    ∫ t, (α * f1 t - β * f2 t + ∑ c, f3 c t - ∑ c, f4 c t + f5 t) ∂μ =
      α * ∫ t, f1 t ∂μ - β * ∫ t, f2 t ∂μ + ∑ c, ∫ t, f3 c t ∂μ - ∑ c, ∫ t, f4 c t ∂μ +
        ∫ t, f5 t ∂μ := by
  have i3 : Integrable (fun t => ∑ c, f3 c t) μ := integrable_finset_sum _ fun c _ => h3 c
  have i4 : Integrable (fun t => ∑ c, f4 c t) μ := integrable_finset_sum _ fun c _ => h4 c
  have j1 : Integrable (fun t => α * f1 t) μ := h1.const_mul α
  have j2 : Integrable (fun t => β * f2 t) μ := h2.const_mul β
  have g1 : Integrable (fun t => α * f1 t - β * f2 t) μ := j1.sub j2
  have g2 : Integrable (fun t => α * f1 t - β * f2 t + ∑ c, f3 c t) μ := g1.add i3
  have g3 : Integrable (fun t => α * f1 t - β * f2 t + ∑ c, f3 c t - ∑ c, f4 c t) μ := g2.sub i4
  rw [integral_add g3 h5, integral_sub g2 i4, integral_add g1 i3, integral_sub j1 j2,
    integral_const_mul, integral_const_mul, integral_finset_sum _ fun c _ => h3 c,
    integral_finset_sum _ fun c _ => h4 c]

theorem norm_entry_le_norm (M : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) : ‖M a b‖ ≤ ‖M‖ := by
  have h := frob_sq M
  have h1 : ‖M a b‖ ^ 2 ≤ ∑ a, ∑ b, ‖M a b‖ ^ 2 := by
    refine (Finset.single_le_sum (f := fun b => ‖M a b‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ b)).trans ?_
    exact Finset.single_le_sum (f := fun a => ∑ b, ‖M a b‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ a)
  rw [← h] at h1
  nlinarith [norm_nonneg (M a b), norm_nonneg M]

theorem norm_gp_one_le {N : ℕ} [NeZero N] (k : Fin 3 → ℤ) (R : MatArr N n) (a b : Fin n) :
    ‖gp k oneArr (entry R a b)‖ ≤ ((N : ℝ) ^ 3)⁻¹ * ∑ x, ‖R x‖ := by
  unfold gp
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_))
    (by positivity)
  rw [norm_mul, norm_mul, norm_modChar]
  simp only [oneArr, norm_one, one_mul, entry]
  exact norm_entry_le_norm _ a b

theorem continuous_matNormSq {N : ℕ} [NeZero N] {u : ℝ → MatArr N n}
    (hu : ∀ x a b, Continuous fun t => u t x a b) : Continuous fun t => matNormSq (u t) := by
  unfold matNormSq
  exact continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ =>
    continuous_gridNormSq.comp (continuous_pi fun x => hu x a b)

theorem continuous_matDp_entry {N : ℕ} [NeZero N] {u : ℝ → MatArr N n}
    (hu : ∀ x a b, Continuous fun t => u t x a b) (j : Fin 3) :
    ∀ x a b, Continuous fun t => matDp j (u t) x a b := by
  intro x a b
  simp only [matDp, LiteralLink.fwdDiff, Matrix.smul_apply, Matrix.sub_apply, Complex.real_smul]
  exact continuous_const.mul ((hu _ a b).sub (hu x a b))

/-- The tested plaquette decomposition on one odd grid, integrated against a bounded weight. -/
theorem magnetic_grid_identity {N : ℕ} [NeZero N] (hN : Odd N) (Ai Aj : ℝ → MatArr N n)
    (i j : Fin 3) (a b : Fin n) (k : Fin 3 → ℤ) {χ : ℝ → ℝ}
    (hψm : AEStronglyMeasurable (fun t => ((χ t : ℝ) : ℂ)) (volume.restrict (Set.Ioc 0 T)))
    {C : ℝ} (hC : ∀ t, ‖((χ t : ℝ) : ℂ)‖ ≤ C)
    (hAil : ∀ c d, IsL2Grid T (fun t => entry (Ai t) c d))
    (hAjl : ∀ c d, IsL2Grid T (fun t => entry (Aj t) c d))
    (hFl : IsL2Grid T (fun t => entry (magRec i j (Ai t) (Aj t)) a b)) :
    (∫ t in Set.Ioc 0 T, ((χ t : ℝ) : ℂ) * gp k oneArr (entry (magRec i j (Ai t) (Aj t)) a b)) =
      ((N : ℂ) * (conj (modChar (N := N) k (unit i)) - 1)) *
          (∫ t in Set.Ioc 0 T, ((χ t : ℝ) : ℂ) * gp k oneArr (entry (Aj t) a b))
      - ((N : ℂ) * (conj (modChar (N := N) k (unit j)) - 1)) *
          (∫ t in Set.Ioc 0 T, ((χ t : ℝ) : ℂ) * gp k oneArr (entry (Ai t) a b))
      + ∑ c, (∫ t in Set.Ioc 0 T, ((χ t : ℝ) : ℂ) * gp k (entry (Ai t) a c) (entry (Aj t) c b))
      - ∑ c, (∫ t in Set.Ioc 0 T, ((χ t : ℝ) : ℂ) * gp k (entry (Aj t) a c) (entry (Ai t) c b))
      + (∫ t in Set.Ioc 0 T, ((χ t : ℝ) : ℂ) *
          gp k oneArr (entry (magRem i j (Ai t) (Aj t)) a b)) := by
  set α : ℂ := (N : ℂ) * (conj (modChar (N := N) k (unit i)) - 1)
  set β : ℂ := (N : ℂ) * (conj (modChar (N := N) k (unit j)) - 1)
  set F1 : ℝ → ℂ := fun t => ((χ t : ℝ) : ℂ) * gp k oneArr (entry (Aj t) a b) with hF1
  set F2 : ℝ → ℂ := fun t => ((χ t : ℝ) : ℂ) * gp k oneArr (entry (Ai t) a b) with hF2
  set F3 : Fin n → ℝ → ℂ := fun c t => ((χ t : ℝ) : ℂ) *
    gp k (entry (Ai t) a c) (entry (Aj t) c b) with hF3
  set F4 : Fin n → ℝ → ℂ := fun c t => ((χ t : ℝ) : ℂ) *
    gp k (entry (Aj t) a c) (entry (Ai t) c b) with hF4
  set F5 : ℝ → ℂ := fun t => ((χ t : ℝ) : ℂ) *
    gp k oneArr (entry (magRem i j (Ai t) (Aj t)) a b) with hF5
  set F : ℝ → ℂ := fun t => ((χ t : ℝ) : ℂ) *
    gp k oneArr (entry (magRec i j (Ai t) (Aj t)) a b) with hF
  have e : ∀ t, F t = α * F1 t - β * F2 t + ∑ c, F3 c t - ∑ c, F4 c t + F5 t := by
    intro t
    simp only [hF, hF1, hF2, hF3, hF4, hF5]
    rw [gp_magRec k i j (Ai t) (Aj t) a b]
    simp only [← Finset.mul_sum]
    ring
  have i1 : Integrable F1 (volume.restrict (Set.Ioc 0 T)) :=
    integrableOn_gp hN (IsL2Grid.const _) (hAjl a b) hψm hC k
  have i2 : Integrable F2 (volume.restrict (Set.Ioc 0 T)) :=
    integrableOn_gp hN (IsL2Grid.const _) (hAil a b) hψm hC k
  have i3 : ∀ c, Integrable (F3 c) (volume.restrict (Set.Ioc 0 T)) :=
    fun c => integrableOn_gp hN (hAil a c) (hAjl c b) hψm hC k
  have i4 : ∀ c, Integrable (F4 c) (volume.restrict (Set.Ioc 0 T)) :=
    fun c => integrableOn_gp hN (hAjl a c) (hAil c b) hψm hC k
  have iF : Integrable F (volume.restrict (Set.Ioc 0 T)) :=
    integrableOn_gp hN (IsL2Grid.const _) hFl hψm hC k
  have i5 : Integrable F5 (volume.restrict (Set.Ioc 0 T)) := by
    have h := iF.sub ((((i1.const_mul α).sub (i2.const_mul β)).add
      (integrable_finset_sum Finset.univ fun c _ => i3 c)).sub
        (integrable_finset_sum Finset.univ fun c _ => i4 c))
    refine h.congr (ae_of_all _ fun t => ?_)
    simp only [Pi.sub_apply, Pi.add_apply, Finset.sum_apply]
    rw [e t]; ring
  rw [integral_congr_ae (ae_of_all _ e)]
  exact integral_combo' i1 i2 i3 i4 i5 α β

/-- **Magnetic curvature identity** (`eq:supp-literal-magnetic-limit`).  Along odd grids
`N_m → ∞`, let the spatial coefficients `A_i` converge strongly (entrywise) to `Ω_i`, on the
identity chart `h‖A‖ ≤ 1/16` with `‖A(t)‖²_h ≤ B` and `∫₀ᵀ Σ_i ‖A_i‖²_{1,h} ≤ B`, and let the literal
magnetic records `F_{ij}` converge weakly to `F_{ij}^∞`.  Then, tested against `ψ = χ e_k`,
`⟨F_{ij}^∞, ψ⟩ = −2πi k_i ⟨Ω_j, ψ⟩ + 2πi k_j ⟨Ω_i, ψ⟩ + ⟨Ω_iΩ_j − Ω_jΩ_i, ψ⟩`, i.e.
`F_{ij}^∞ = ∂_iΩ_j − ∂_jΩ_i + [Ω_i, Ω_j]` in distributions. -/
theorem magnetic_identity (hodd : ∀ m, Odd (Nm m)) (hN : Tendsto Nm atTop atTop)
    (A : ∀ m, ℝ → Fin 3 → MatArr (Nm m) n)
    (hAc : ∀ m i x a b, Continuous fun t => A m t i x a b)
    (hchart : ∀ m t i x, (Nm m : ℝ)⁻¹ * ‖A m t i x‖ ≤ 1 / 16) {B : ℝ}
    (hAinf : ∀ m, ∀ t ∈ Set.Ioc 0 T, ∀ i, matNormSq (A m t i) ≤ B)
    (hAH1 : ∀ m, ∫ t in Set.Ioc 0 T,
      ∑ i, (matNormSq (A m t i) + ∑ j, matNormSq (matDp j (A m t i))) ≤ B)
    {Ω : Fin 3 → Fin n → Fin n → ℝ × UnitAddTorus (Fin 3) → ℂ}
    {Flim : Fin 3 → Fin 3 → Fin n → Fin n → ℝ × UnitAddTorus (Fin 3) → ℂ}
    (hA : ∀ i a b, StrongSeq Nm T (fun m t => entry (A m t i) a b) (Ω i a b))
    (hF : ∀ i j a b, WeakSeq Nm T (fun m t => entry (magRec i j (A m t i) (A m t j)) a b)
      (Flim i j a b))
    (i j : Fin 3) (a b : Fin n) (k : Fin 3 → ℤ) {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hsupp : tsupport χ ⊆ Set.Ioo 0 T) :
    cylPair T χ k (Flim i j a b) =
      -(2 * Real.pi * Complex.I * k i) * cylPair T χ k (Ω j a b)
      + 2 * Real.pi * Complex.I * k j * cylPair T χ k (Ω i a b)
      + ∑ c, cylPair T χ k (fun p => Ω i a c p * Ω j c b p)
      - ∑ c, cylPair T χ k (fun p => Ω j a c p * Ω i c b p) := by
  have hχc : Continuous χ := hχ.continuous
  obtain ⟨C, hC0, hC⟩ := bound_of_compact_support hχc hsupp
  have hψm : AEStronglyMeasurable (fun t => ((χ t : ℝ) : ℂ)) (volume.restrict (Set.Ioc 0 T)) :=
    (Complex.continuous_ofReal.comp hχc).aestronglyMeasurable
  -- limits of the main pieces
  have L0 := tendsto_gp hodd hN (StrongSeq.one (Nm := Nm) (T := T)) (hF i j a b) hψm hC0 hC k
  have L1 := tendsto_gp hodd hN (StrongSeq.one (Nm := Nm) (T := T)) (hA j a b).toWeak hψm hC0 hC k
  have L2 := tendsto_gp hodd hN (StrongSeq.one (Nm := Nm) (T := T)) (hA i a b).toWeak hψm hC0 hC k
  have L3 := fun c => tendsto_gp hodd hN (hA i a c) (hA j c b).toWeak hψm hC0 hC k
  have L4 := fun c => tendsto_gp hodd hN (hA j a c) (hA i c b).toWeak hψm hC0 hC k
  have hαi := tendsto_natCast_mul_modChar_unit hN k i
  have hαj := tendsto_natCast_mul_modChar_unit hN k j
  -- the plaquette remainder vanishes
  set κ := kappa (Matrix (Fin n) (Fin n) ℂ)
  have hκ : 0 ≤ κ := (kappa_pos (𝔸 := Matrix (Fin n) (Fin n) ℂ)).le
  set K2 : ℝ := 16 + 384 * κ * (Real.sqrt (B ⊔ 0) * ((n : ℝ) * Real.sqrt Kprod))
  have hK2 : 0 ≤ K2 := by positivity
  set H : ∀ m, ℝ → ℝ := fun m t =>
    ∑ l, (matNormSq (A m t l) + ∑ j', matNormSq (matDp j' (A m t l)))
  have hHc : ∀ m, Continuous (H m) := fun m =>
    continuous_finset_sum _ fun l _ => (continuous_matNormSq (hAc m l)).add
      (continuous_finset_sum _ fun j' _ => continuous_matNormSq (continuous_matDp_entry (hAc m l) j'))
  have hH1 : ∀ m t l, matNormSq (A m t l) + ∑ j', matNormSq (matDp j' (A m t l)) ≤ H m t :=
    fun m t l => Finset.single_le_sum (f := fun l => matNormSq (A m t l) +
      ∑ j', matNormSq (matDp j' (A m t l)))
      (fun _ _ => add_nonneg (matNormSq_nonneg _)
        (Finset.sum_nonneg fun _ _ => matNormSq_nonneg _)) (Finset.mem_univ l)
  have hcube : ∀ m, ∀ t ∈ Set.Ioc 0 T, ∀ l, ((Nm m : ℝ) ^ 3)⁻¹ * ∑ x, ‖A m t l x‖ ^ 3 ≤
      Real.sqrt (B ⊔ 0) * ((n : ℝ) * Real.sqrt Kprod) * H m t := by
    intro m t ht l
    refine (sum_norm_cube_le (A m t l)).trans ?_
    rw [sum_sobSq_one_eq]
    have hm : matNorm (A m t l) ≤ Real.sqrt (B ⊔ 0) :=
      Real.sqrt_le_sqrt ((hAinf m t ht l).trans le_sup_left)
    have hn : 0 ≤ (n : ℝ) * Real.sqrt Kprod := by positivity
    calc matNorm (A m t l) * ((n : ℝ) * Real.sqrt Kprod *
          (matNormSq (A m t l) + ∑ j', matNormSq (matDp j' (A m t l))))
        ≤ Real.sqrt (B ⊔ 0) * ((n : ℝ) * Real.sqrt Kprod * H m t) := by
          refine mul_le_mul hm (mul_le_mul_of_nonneg_left (hH1 m t l) hn)
            (mul_nonneg hn (add_nonneg (matNormSq_nonneg _)
              (Finset.sum_nonneg fun _ _ => matNormSq_nonneg _))) (Real.sqrt_nonneg _)
      _ = _ := by ring
  have hRpt : ∀ m, ∀ t ∈ Set.Ioc 0 T, ‖((χ t : ℝ) : ℂ) *
      gp k oneArr (entry (magRem i j (A m t i) (A m t j)) a b)‖ ≤
      C * ((Nm m : ℝ)⁻¹ * (K2 * H m t)) := by
    intro m t ht
    rw [norm_mul]
    refine mul_le_mul (hC t) ((norm_gp_one_le k _ a b).trans ?_) (norm_nonneg _) hC0
    refine (sum_norm_magRem_le i j (A m t i) (A m t j) (hchart m t i) (hchart m t j)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (Nat.cast_nonneg _))
    have hi := hH1 m t i
    have hj := hH1 m t j
    have hdi : matNormSq (matDp j (A m t i)) ≤ ∑ j', matNormSq (matDp j' (A m t i)) :=
      Finset.single_le_sum (f := fun j' => matNormSq (matDp j' (A m t i)))
        (fun _ _ => matNormSq_nonneg _) (Finset.mem_univ j)
    have hdj : matNormSq (matDp i (A m t j)) ≤ ∑ j', matNormSq (matDp j' (A m t j)) :=
      Finset.single_le_sum (f := fun j' => matNormSq (matDp j' (A m t j)))
        (fun _ _ => matNormSq_nonneg _) (Finset.mem_univ i)
    have h0i := matNormSq_nonneg (A m t i)
    have h0j := matNormSq_nonneg (A m t j)
    have hci := hcube m t ht i
    have hcj := hcube m t ht j
    have hs : 0 ≤ Real.sqrt (B ⊔ 0) * ((n : ℝ) * Real.sqrt Kprod) := by positivity
    have hH0 : 0 ≤ H m t := le_trans (add_nonneg h0i (Finset.sum_nonneg fun _ _ =>
      matNormSq_nonneg _)) hi
    have hk1 : 192 * κ * (((Nm m : ℝ) ^ 3)⁻¹ * ∑ x, ‖A m t i x‖ ^ 3 +
        ((Nm m : ℝ) ^ 3)⁻¹ * ∑ x, ‖A m t j x‖ ^ 3) ≤
        192 * κ * (2 * (Real.sqrt (B ⊔ 0) * ((n : ℝ) * Real.sqrt Kprod) * H m t)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      linarith
    simp only [K2]
    nlinarith
  have hRint : ∀ m, Integrable (fun t => C * ((Nm m : ℝ)⁻¹ * (K2 * H m t)))
      (volume.restrict (Set.Ioc 0 T)) := fun m =>
    integrableOn_Ioc_of_continuous (continuous_const.mul (continuous_const.mul
      (continuous_const.mul (hHc m))))
  have hRbd : ∀ m, ‖∫ t in Set.Ioc 0 T, ((χ t : ℝ) : ℂ) *
      gp k oneArr (entry (magRem i j (A m t i) (A m t j)) a b)‖ ≤
      C * ((Nm m : ℝ)⁻¹ * (K2 * B)) := by
    intro m
    have hI : ∫ t in Set.Ioc 0 T, C * ((Nm m : ℝ)⁻¹ * (K2 * H m t)) =
        C * ((Nm m : ℝ)⁻¹ * (K2 * ∫ t in Set.Ioc 0 T, H m t)) := by
      rw [integral_const_mul, integral_const_mul, integral_const_mul]
    calc _ ≤ ∫ t in Set.Ioc 0 T, C * ((Nm m : ℝ)⁻¹ * (K2 * H m t)) :=
          norm_integral_le_of_norm_le (hRint m) ((ae_restrict_iff' measurableSet_Ioc).2
            (ae_of_all _ (hRpt m)))
      _ = _ := hI
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hAH1 m) hK2) (inv_nonneg.2 (Nat.cast_nonneg _))) hC0
  have L5 : Tendsto (fun m => ∫ t in Set.Ioc 0 T, ((χ t : ℝ) : ℂ) *
      gp k oneArr (entry (magRem i j (A m t i) (A m t j)) a b)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h1 : Tendsto (fun m => ((Nm m : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hN)
    have h2 : Tendsto (fun m => C * ((Nm m : ℝ)⁻¹ * (K2 * B))) atTop (𝓝 0) := by
      simpa using (h1.mul_const (K2 * B)).const_mul C
    exact squeeze_zero (fun _ => norm_nonneg _) hRbd h2
  have Lrhs := (((((hαi.mul L1).sub (hαj.mul L2)).add
    (tendsto_finset_sum Finset.univ fun c _ => L3 c)).sub
    (tendsto_finset_sum Finset.univ fun c _ => L4 c)).add L5)
  have heq : ∀ m, (∫ t in Set.Ioc 0 T, ((χ t : ℝ) : ℂ) *
      gp k oneArr (entry (magRec i j (A m t i) (A m t j)) a b)) = _ := fun m =>
    magnetic_grid_identity (hodd m) (fun t => A m t i) (fun t => A m t j) i j a b k hψm hC
      (fun c d => (hA i c d).isL2 m) (fun c d => (hA j c d).isL2 m) ((hF i j a b).isL2 m)
  have huniq := tendsto_nhds_unique (L0.congr heq) Lrhs
  simp only [mul_one, add_zero, limit_form_eq] at huniq
  unfold cylPair
  linear_combination huniq

end Identities

end RenewalGeometry.LiteralLinkLimit
