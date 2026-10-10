/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.UhlenbeckHodgeEstimate
import RenewalGeometry.Analysis.CoulombHodgeAbsorption
import RenewalGeometry.Analysis.CovariantGradientCompactness

/-!
# The critical Coulomb a-priori estimate and uniqueness of the Coulomb gauge on `𝕋⁴`
  (the analytic core of Uhlenbeck's small-energy gauge theorem, periodic rendering)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript (K. Uhlenbeck, Comm. Math. Phys. 83 (1982),
Thm 1.3 and its uniqueness statement, case `p = n/2 = 2`), on the flat unit torus
`𝕋⁴ = UnitAddTorus (Fin 4)`.

A matrix-valued one-form (connection of the trivial `ℂ^m` bundle) is given by its entries
`a ν c e : 𝕋⁴ → ℂ` (form index `ν`, matrix indices `c, e`) and their torus partial derivatives
`da ν c e μ = ∂_μ a_{ν,ce}` (`IsTPartial`, Fourier rule).  Its curvature is
`F_{μν} = ∂_μ a_ν - ∂_ν a_μ + [a_μ, a_ν]` (`tCurv`).  No skew-Hermitian or structure-group
condition is needed for the estimates: they hold for every `𝔤 ⊂ 𝔲(m) ⊂ M_m(ℂ)`, in particular
for `𝔤_SM = 𝔰(𝔲(3) ⊕ 𝔲(2))`.

* `coulomb_apriori_torus` (**critical Coulomb a-priori estimate with absorption**, the
  "closedness" estimate of Uhlenbeck's continuity method): there is `δ > 0` depending only on `m`
  such that every Coulomb (`d^*a = 0`), mean-zero one-form with `L²` gradient and
  `‖∇a‖_{L²} ≤ δ` satisfies `‖∇a‖_{L²} ≤ 32 m² ‖F_a‖_{L²}`; consequently
  `‖a‖_{L²} ≤ 32 m² ‖F_a‖_{L²}` and `‖a‖_{L⁴} ≤ 224 m² ‖F_a‖_{L²}` (`coulomb_apriori_torus_L4`).
  Ingredients: Hodge estimate for co-closed forms (`eLpNorm_partial_le_curl_of_coclosed`),
  critical Sobolev–Poincaré `‖a‖_4 ≤ 7‖∇a‖_2`, Hölder `‖[a ∧ a]‖_2 ≤ 2m ‖a‖_4²`, absorption.
* `coulomb_apriori_gap`: the first-exit gap `‖∇a‖ ≤ δ ∧ 64 m² ‖F_a‖ ≤ δ ⇒ ‖∇a‖ ≤ δ/2` used along
  continuity paths.
* `coulomb_gauge_unique_torus` (**uniqueness of the Coulomb gauge up to constants**): if `a, b`
  are Coulomb one-forms with `H¹` entries and small total `L⁴` norm (`28 m² δ < 1`), and a matrix
  function `g` with `H¹` entries intertwines them, `∂_μ g = g a_μ - b_μ g` (this is
  `b = g a g⁻¹ - dg g⁻¹`, i.e. `b = g · a`, for invertible `g`), then `g` is a.e. constant.
  Proof: `‖∇g‖² = Σ_μ ⟨∂_μ g, (g - ḡ)a_μ - b_μ(g - ḡ)⟩` (the mean `ḡ` drops out after integration
  by parts because `d^*a = d^*b = 0`), Hölder, critical Sobolev–Poincaré and Cauchy–Schwarz give
  `‖∇g‖² ≤ 28 m² δ ‖∇g‖²`.  Both this and the next item are corollaries of
  `coulomb_intertwiner_const` (`∂_μ g = g a_μ - b_μ g + η_μ` with `η ⊥ ∇g` forces `∇g = 0`).
* `linearized_coulomb_kernel_const` (**injectivity of the linearised Coulomb operator modulo
  constants**, the injectivity input of the implicit-function step): for a small Coulomb `a`,
  every `H¹` matrix function `ξ` with `d^*(d_a ξ) = 0` weakly (`d_a ξ = dξ + [a, ξ]`, `covLin`)
  is constant.
-/

open MeasureTheory Filter Topology Set UnitAddTorus
open scoped ENNReal NNReal Real ComplexConjugate InnerProductSpace

noncomputable section

namespace RenewalGeometry.UhlenbeckTorus

open SobolevOpen TorusSobolev

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local notation "𝕋⁴" => UnitAddTorus (Fin 4)

/-! ### Matrix-valued one-forms on `𝕋⁴` -/

/-- The curvature entries `F_{μν,ce} = ∂_μ a_{ν,ce} - ∂_ν a_{μ,ce} + Σ_k (a_{μ,ck} a_{ν,ke} -
a_{ν,ck} a_{μ,ke})` of a matrix-valued one-form on `𝕋⁴`. -/
def tCurv {m : ℕ} (a : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ)
    (da : Fin 4 → Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ) (μ ν : Fin 4) (c e : Fin m) (x : 𝕋⁴) : ℂ :=
  da ν c e μ x - da μ c e ν x + ∑ k, (a μ c k x * a ν k e x - a ν c k x * a μ k e x)

/-- The commutator term `[a_μ, a_ν]_{ce}`. -/
def tComm {m : ℕ} (a : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ) (μ ν : Fin 4) (c e : Fin m) (x : 𝕋⁴) :
    ℂ :=
  ∑ k, (a μ c k x * a ν k e x - a ν c k x * a μ k e x)

/-- A matrix-valued one-form on `𝕋⁴` with `H¹` entries: `L²` entries, `L²` torus partial
derivatives `da ν c e μ = ∂_μ a_{ν,ce}`. -/
structure IsH1Form {m : ℕ} (a : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ)
    (da : Fin 4 → Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ) : Prop where
  memLp : ∀ ν c e, MemLp (a ν c e) 2 volume
  memLp_grad : ∀ ν c e μ, MemLp (da ν c e μ) 2 volume
  hasPartial : ∀ ν c e μ, IsTPartial μ (a ν c e) (da ν c e μ)

/-- Coulomb gauge `d^*a = 0`: `Σ_μ ∂_μ a_{μ,ce} = 0` a.e., for every matrix entry. -/
def IsCoulomb {m : ℕ} (da : Fin 4 → Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ) : Prop :=
  ∀ c e, ∀ᵐ x ∂volume, ∑ μ, da μ c e μ x = 0

/-- The total `L²` norm of the gradient, `Σ_{νceμ} ‖∂_μ a_{ν,ce}‖_{L²}`. -/
def gradNorm {m : ℕ} (da : Fin 4 → Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ) : ℝ≥0∞ :=
  ∑ ν, ∑ c, ∑ e, ∑ μ, eLpNorm (da ν c e μ) 2 volume

/-- The total `L²` norm of the curvature, `Σ_{μνce} ‖F_{μν,ce}‖_{L²}`. -/
def curvNorm {m : ℕ} (a : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ)
    (da : Fin 4 → Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ) : ℝ≥0∞ :=
  ∑ μ, ∑ ν, ∑ c, ∑ e, eLpNorm (tCurv a da μ ν c e) 2 volume

theorem le_sum_four {α β γ δ' : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ']
    (f : α → β → γ → δ' → ℝ≥0∞) (i : α) (j : β) (k : γ) (l : δ') :
    f i j k l ≤ ∑ i, ∑ j, ∑ k, ∑ l, f i j k l :=
  (le_sum_three (f i) j k l).trans
    (Finset.single_le_sum (f := fun i => ∑ j, ∑ k, ∑ l, f i j k l) (fun _ _ => zero_le)
      (Finset.mem_univ i))

theorem sum_four_le_const {m : ℕ} {f : Fin 4 → Fin m → Fin m → Fin 4 → ℝ≥0∞} {K : ℝ≥0∞}
    (h : ∀ ν c e μ, f ν c e μ ≤ K) :
    ∑ ν, ∑ c, ∑ e, ∑ μ, f ν c e μ ≤ 16 * (m : ℝ≥0∞) ^ 2 * K := by
  calc ∑ ν, ∑ c, ∑ e, ∑ μ, f ν c e μ ≤ ∑ _ν : Fin 4, ∑ _c : Fin m, ∑ _e : Fin m, ∑ _μ : Fin 4, K :=
        Finset.sum_le_sum fun ν _ => Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun e _ =>
          Finset.sum_le_sum fun μ _ => h ν c e μ
    _ = 16 * (m : ℝ≥0∞) ^ 2 * K := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

/-- `L⁴` bound of the entries of a mean-zero `H¹` one-form by the total gradient norm. -/
theorem eLpNorm_four_entry_le {m : ℕ} {a : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ}
    {da : Fin 4 → Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ} (ha : IsH1Form a da)
    (h0 : ∀ ν c e, mFourierCoeff (a ν c e) 0 = 0) (ν : Fin 4) (c e : Fin m) :
    eLpNorm (a ν c e) 4 volume ≤ 7 * gradNorm da := by
  refine (eLpNorm_four_le_of_mean_zero (ha.memLp ν c e) (ha.memLp_grad ν c e)
    (ha.hasPartial ν c e) (h0 ν c e)).trans ?_
  gcongr
  calc ∑ μ, eLpNorm (da ν c e μ) 2 volume ≤ ∑ c, ∑ e, ∑ μ, eLpNorm (da ν c e μ) 2 volume :=
        (Finset.single_le_sum (f := fun e => ∑ μ, eLpNorm (da ν c e μ) 2 volume)
          (fun _ _ => zero_le) (Finset.mem_univ e)).trans
          (Finset.single_le_sum (f := fun c => ∑ e, ∑ μ, eLpNorm (da ν c e μ) 2 volume)
            (fun _ _ => zero_le) (Finset.mem_univ c))
    _ ≤ gradNorm da :=
        Finset.single_le_sum (f := fun ν => ∑ c, ∑ e, ∑ μ, eLpNorm (da ν c e μ) 2 volume)
          (fun _ _ => zero_le) (Finset.mem_univ ν)

/-- Hölder for the commutator: `‖[a_μ, a_ν]_{ce}‖_{L²} ≤ Σ_k (‖a_{μ,ck}‖_4 ‖a_{ν,ke}‖_4 +
‖a_{ν,ck}‖_4 ‖a_{μ,ke}‖_4)`. -/
theorem eLpNorm_tComm_le {m : ℕ} {a : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ}
    (ham : ∀ ν c e, AEStronglyMeasurable (a ν c e) volume) (μ ν : Fin 4) (c e : Fin m) :
    eLpNorm (tComm a μ ν c e) 2 volume ≤
      ∑ k, (eLpNorm (a μ c k) 4 volume * eLpNorm (a ν k e) 4 volume +
        eLpNorm (a ν c k) 4 volume * eLpNorm (a μ k e) 4 volume) := by
  have e' : tComm a μ ν c e =
      ∑ k, (fun x => a μ c k x * a ν k e x - a ν c k x * a μ k e x) := by
    funext x; simp only [tComm, Finset.sum_apply]
  rw [e']
  refine (eLpNorm_sum_le (f := fun k x => a μ c k x * a ν k e x - a ν c k x * a μ k e x)
    (fun k _ => ((ham μ c k).mul (ham ν k e)).sub
    ((ham ν c k).mul (ham μ k e))) (by norm_num)).trans (Finset.sum_le_sum fun k _ => ?_)
  refine (eLpNorm_sub_le ((ham μ c k).mul (ham ν k e)) ((ham ν c k).mul (ham μ k e))
    (by norm_num)).trans (add_le_add ?_ ?_)
  · exact eLpNorm_mul_le_L4 (ham μ c k) (ham ν k e)
  · exact eLpNorm_mul_le_L4 (ham ν c k) (ham μ k e)

/-! ### The a-priori estimate -/

/-- The quadratic bound behind the a-priori estimate:
`‖∇a‖ ≤ 16 m² ‖F_a‖ + 25088 m³ ‖∇a‖²` for every Coulomb mean-zero `H¹` one-form. -/
theorem gradNorm_le_quadratic {m : ℕ} {a : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ}
    {da : Fin 4 → Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ} (ha : IsH1Form a da)
    (h0 : ∀ ν c e, mFourierCoeff (a ν c e) 0 = 0) (hC : IsCoulomb da) :
    gradNorm da ≤ 16 * (m : ℝ≥0∞) ^ 2 * curvNorm a da +
      25088 * (m : ℝ≥0∞) ^ 3 * (gradNorm da * gradNorm da) := by
  set X := gradNorm da
  have ham : ∀ ν c e, AEStronglyMeasurable (a ν c e) volume := fun ν c e => (ha.memLp ν c e).1
  have h4 := eLpNorm_four_entry_le ha h0
  -- commutator bound
  have hcomm : ∀ μ ν c e, eLpNorm (tComm a μ ν c e) 2 volume ≤ 98 * (m : ℝ≥0∞) * (X * X) := by
    intro μ ν c e
    refine (eLpNorm_tComm_le ham μ ν c e).trans ?_
    calc ∑ k, (eLpNorm (a μ c k) 4 volume * eLpNorm (a ν k e) 4 volume +
          eLpNorm (a ν c k) 4 volume * eLpNorm (a μ k e) 4 volume)
        ≤ ∑ _k : Fin m, ((7 * X) * (7 * X) + (7 * X) * (7 * X)) :=
          Finset.sum_le_sum fun k _ => by gcongr <;> exact h4 _ _ _
      _ = 98 * (m : ℝ≥0∞) * (X * X) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  -- curl = F - commutator
  have hcurl : ∀ μ' ν' c e, eLpNorm (fun x => da ν' c e μ' x - da μ' c e ν' x) 2 volume ≤
      eLpNorm (tCurv a da μ' ν' c e) 2 volume + 98 * (m : ℝ≥0∞) * (X * X) := by
    intro μ' ν' c e
    have e1 : (fun x => da ν' c e μ' x - da μ' c e ν' x) =
        fun x => tCurv a da μ' ν' c e x - tComm a μ' ν' c e x := by
      funext x; simp only [tCurv, tComm]; ring
    have hFm : AEStronglyMeasurable (tCurv a da μ' ν' c e) volume := by
      unfold tCurv
      exact (((ha.memLp_grad ν' c e μ').1.sub (ha.memLp_grad μ' c e ν').1).add
        (Finset.aestronglyMeasurable_fun_sum _ fun k _ => ((ham μ' c k).mul (ham ν' k e)).sub
          ((ham ν' c k).mul (ham μ' k e))))
    have hKm : AEStronglyMeasurable (tComm a μ' ν' c e) volume := by
      unfold tComm
      exact Finset.aestronglyMeasurable_fun_sum _ fun k _ => ((ham μ' c k).mul (ham ν' k e)).sub
        ((ham ν' c k).mul (ham μ' k e))
    rw [e1]
    exact (eLpNorm_sub_le hFm hKm (by norm_num)).trans (add_le_add le_rfl (hcomm μ' ν' c e))
  -- Hodge for each matrix entry
  have hentry : ∀ ν c e μ, eLpNorm (da ν c e μ) 2 volume ≤
      curvNorm a da + 1568 * (m : ℝ≥0∞) * (X * X) := by
    intro ν c e μ
    have hH := eLpNorm_partial_le_curl_of_coclosed (w := fun ν x => a ν c e x)
      (g := fun ν μ x => da ν c e μ x) (fun ν μ => ha.memLp_grad ν c e μ)
      (fun ν μ => ha.hasPartial ν c e μ) (hC c e) ν μ
    refine hH.trans ?_
    calc ∑ μ', ∑ ν', eLpNorm (fun x => da ν' c e μ' x - da μ' c e ν' x) 2 volume
        ≤ ∑ μ', ∑ ν', (eLpNorm (tCurv a da μ' ν' c e) 2 volume +
            98 * (m : ℝ≥0∞) * (X * X)) :=
          Finset.sum_le_sum fun μ' _ => Finset.sum_le_sum fun ν' _ => hcurl μ' ν' c e
      _ = ∑ μ', ∑ ν', eLpNorm (tCurv a da μ' ν' c e) 2 volume +
            16 * (98 * (m : ℝ≥0∞) * (X * X)) := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          ring
      _ ≤ curvNorm a da + 1568 * (m : ℝ≥0∞) * (X * X) := by
          refine add_le_add ?_ (le_of_eq (by ring))
          unfold curvNorm
          refine Finset.sum_le_sum fun μ' _ => Finset.sum_le_sum fun ν' _ => ?_
          exact (Finset.single_le_sum (f := fun e => eLpNorm (tCurv a da μ' ν' c e) 2 volume)
            (fun _ _ => zero_le) (Finset.mem_univ e)).trans
            (Finset.single_le_sum (f := fun c => ∑ e, eLpNorm (tCurv a da μ' ν' c e) 2 volume)
              (fun _ _ => zero_le) (Finset.mem_univ c))
  calc X ≤ 16 * (m : ℝ≥0∞) ^ 2 * (curvNorm a da + 1568 * (m : ℝ≥0∞) * (X * X)) :=
        sum_four_le_const hentry
    _ = 16 * (m : ℝ≥0∞) ^ 2 * curvNorm a da + 25088 * (m : ℝ≥0∞) ^ 3 * (X * X) := by ring

/-- **Critical Coulomb a-priori estimate on `𝕋⁴`** (Uhlenbeck's closedness estimate, periodic
rendering).  There is `δ > 0`, depending only on the matrix size `m`, such that every
matrix-valued one-form `a` on `𝕋⁴` with `H¹` entries, mean zero, in Coulomb gauge `d^*a = 0`,
with `‖∇a‖_{L²} ≤ δ`, satisfies `‖∇a‖_{L²} ≤ 32 m² ‖F_a‖_{L²}` (entrywise sums of norms). -/
theorem coulomb_apriori_torus (m : ℕ) : ∃ δ : ℝ≥0, 0 < δ ∧
    ∀ (a : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ) (da : Fin 4 → Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ),
      IsH1Form a da → (∀ ν c e, mFourierCoeff (a ν c e) 0 = 0) → IsCoulomb da →
      gradNorm da ≤ δ → gradNorm da ≤ 32 * (m : ℝ≥0∞) ^ 2 * curvNorm a da := by
  set κ : ℝ≥0 := 25088 * (m : ℝ≥0) ^ 3
  refine ⟨(2 * κ + 1)⁻¹, by positivity, fun a da ha h0 hC hX => ?_⟩
  have hq : (κ : ℝ≥0∞) * ((2 * κ + 1)⁻¹ : ℝ≥0) ≤ 2⁻¹ := coulombKappa_mul_le le_rfl
  have hQ := gradNorm_le_quadratic ha h0 hC
  have hXt : gradNorm da ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hX
  have h1 : gradNorm da ≤ 16 * (m : ℝ≥0∞) ^ 2 * curvNorm a da +
      ((κ : ℝ≥0∞) * ((2 * κ + 1)⁻¹ : ℝ≥0)) * gradNorm da := by
    calc gradNorm da ≤ 16 * (m : ℝ≥0∞) ^ 2 * curvNorm a da +
          25088 * (m : ℝ≥0∞) ^ 3 * (gradNorm da * gradNorm da) := hQ
      _ ≤ 16 * (m : ℝ≥0∞) ^ 2 * curvNorm a da +
          25088 * (m : ℝ≥0∞) ^ 3 * ((((2 * κ + 1)⁻¹ : ℝ≥0) : ℝ≥0∞) * gradNorm da) := by
          gcongr
      _ = 16 * (m : ℝ≥0∞) ^ 2 * curvNorm a da +
          ((κ : ℝ≥0∞) * ((2 * κ + 1)⁻¹ : ℝ≥0)) * gradNorm da := by
          simp only [κ]; push_cast; ring
  calc gradNorm da ≤ 2 * (16 * (m : ℝ≥0∞) ^ 2 * curvNorm a da) :=
        le_two_mul_of_le_add_mul hXt hq h1
    _ = 32 * (m : ℝ≥0∞) ^ 2 * curvNorm a da := by ring

/-- The `L²` and `L⁴` clauses of the a-priori estimate: under the hypotheses of
`coulomb_apriori_torus`, every entry satisfies `‖a_{ν,ce}‖_{L²} ≤ 32 m² ‖F_a‖_{L²}` and
`‖a_{ν,ce}‖_{L⁴} ≤ 224 m² ‖F_a‖_{L²}`. -/
theorem coulomb_apriori_torus_L4 (m : ℕ) : ∃ δ : ℝ≥0, 0 < δ ∧
    ∀ (a : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ) (da : Fin 4 → Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ),
      IsH1Form a da → (∀ ν c e, mFourierCoeff (a ν c e) 0 = 0) → IsCoulomb da →
      gradNorm da ≤ δ →
      gradNorm da ≤ 32 * (m : ℝ≥0∞) ^ 2 * curvNorm a da ∧
      (∀ ν c e, eLpNorm (a ν c e) 2 volume ≤ 32 * (m : ℝ≥0∞) ^ 2 * curvNorm a da) ∧
      (∀ ν c e, eLpNorm (a ν c e) 4 volume ≤ 224 * (m : ℝ≥0∞) ^ 2 * curvNorm a da) := by
  obtain ⟨δ, hδ, h⟩ := coulomb_apriori_torus m
  refine ⟨δ, hδ, fun a da ha h0 hC hX => ⟨h a da ha h0 hC hX, fun ν c e => ?_, fun ν c e => ?_⟩⟩
  · have hP := eLpNorm_le_of_mean_zero (ha.memLp ν c e) (ha.memLp_grad ν c e) (ha.hasPartial ν c e)
      (h0 ν c e)
    refine hP.trans (le_trans ?_ (h a da ha h0 hC hX))
    exact (Finset.single_le_sum (f := fun e => ∑ μ, eLpNorm (da ν c e μ) 2 volume)
      (fun _ _ => zero_le) (Finset.mem_univ e)).trans
      ((Finset.single_le_sum (f := fun c => ∑ e, ∑ μ, eLpNorm (da ν c e μ) 2 volume)
        (fun _ _ => zero_le) (Finset.mem_univ c)).trans
        (Finset.single_le_sum (f := fun ν => ∑ c, ∑ e, ∑ μ, eLpNorm (da ν c e μ) 2 volume)
          (fun _ _ => zero_le) (Finset.mem_univ ν)))
  · refine (eLpNorm_four_entry_le ha h0 ν c e).trans ?_
    calc 7 * gradNorm da ≤ 7 * (32 * (m : ℝ≥0∞) ^ 2 * curvNorm a da) := by
          gcongr; exact h a da ha h0 hC hX
      _ = 224 * (m : ℝ≥0∞) ^ 2 * curvNorm a da := by ring

/-- **The first-exit gap** used along continuity paths: if `‖∇a‖ ≤ δ` and the curvature is
small, `64 m² ‖F_a‖ ≤ δ`, then in fact `‖∇a‖ ≤ δ/2`; so along a path on which `‖∇a_t‖` varies
continuously from `0`, the value `δ` is never reached. -/
theorem coulomb_apriori_gap (m : ℕ) : ∃ δ : ℝ≥0, 0 < δ ∧
    ∀ (a : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ) (da : Fin 4 → Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ),
      IsH1Form a da → (∀ ν c e, mFourierCoeff (a ν c e) 0 = 0) → IsCoulomb da →
      gradNorm da ≤ δ → 64 * (m : ℝ≥0∞) ^ 2 * curvNorm a da ≤ δ →
      gradNorm da ≤ (δ : ℝ≥0∞) / 2 := by
  obtain ⟨δ, hδ, h⟩ := coulomb_apriori_torus m
  refine ⟨δ, hδ, fun a da ha h0 hC hX hF => ?_⟩
  refine (h a da ha h0 hC hX).trans ?_
  rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]
  calc (32 * (m : ℝ≥0∞) ^ 2 * curvNorm a da * 2 : ℝ≥0∞) =
        64 * (m : ℝ≥0∞) ^ 2 * curvNorm a da := by ring
    _ ≤ (δ : ℝ≥0∞) := hF

/-! ### Uniqueness of the Coulomb gauge up to constants -/

theorem integrable_conj_mul {u v : 𝕋⁴ → ℂ} (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
    Integrable (fun x => conj (u x) * v x) volume := by
  refine (L2.integrable_inner (𝕜 := ℂ) (hu.toLp u) (hv.toLp v)).congr ?_
  filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with x h1 h2
  rw [h1, h2, RCLike.inner_apply]; ring

/-- Cauchy–Schwarz: `Re ∫ conj(u) v ≤ ‖u‖_{L²} ‖v‖_{L²}`. -/
theorem re_integral_conj_mul_le {u v : 𝕋⁴ → ℂ} (hu : MemLp u 2 volume)
    (hv : MemLp v 2 volume) :
    (∫ x, conj (u x) * v x).re ≤ (eLpNorm u 2 volume).toReal * (eLpNorm v 2 volume).toReal := by
  have e : ∫ x, conj (u x) * v x = ⟪hu.toLp u, hv.toLp v⟫_ℂ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with x h1 h2
    rw [h1, h2, RCLike.inner_apply]; ring
  rw [e]
  refine (Complex.re_le_norm _).trans ((norm_inner_le_norm _ _).trans (le_of_eq ?_))
  rw [Lp.norm_toLp, Lp.norm_toLp]

theorem re_integral_conj_mul_self {u : 𝕋⁴ → ℂ} (hu : MemLp u 2 volume) :
    (∫ x, conj (u x) * u x).re = (eLpNorm u 2 volume).toReal ^ 2 := by
  have e : (fun x => conj (u x) * u x) = fun x => ((‖u x‖ ^ 2 : ℝ) : ℂ) := by
    funext x; rw [Complex.conj_mul']; push_cast; ring
  rw [e, integral_complex_ofReal, Complex.ofReal_re, eLpNorm_two_eq_sqrt hu,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    Real.sq_sqrt (integral_nonneg fun _ => by positivity)]

/-- **The mean drops out**: if `u ∈ H¹` (partials `gu μ`) and `v` is a co-closed one-form with
`H¹` components, then `Σ_μ ∫ conj(∂_μ u) v_μ = -∫ conj(u) Σ_μ ∂_μ v_μ = 0`. -/
theorem sum_integral_conj_partial_coclosed {u : 𝕋⁴ → ℂ} {gu : Fin 4 → 𝕋⁴ → ℂ}
    {v : Fin 4 → 𝕋⁴ → ℂ} {dv : Fin 4 → 𝕋⁴ → ℂ} (hu : MemLp u 2 volume)
    (hgu : ∀ μ, MemLp (gu μ) 2 volume) (hdu : ∀ μ, IsTPartial μ u (gu μ))
    (hv : ∀ μ, MemLp (v μ) 2 volume) (hdv2 : ∀ μ, MemLp (dv μ) 2 volume)
    (hdv : ∀ μ, IsTPartial μ (v μ) (dv μ)) (hdiv : ∀ᵐ x ∂volume, ∑ μ, dv μ x = 0) :
    ∑ μ, ∫ x, conj (gu μ x) * v μ x = 0 := by
  have h1 : ∀ μ, ∫ x, conj (gu μ x) * v μ x = -∫ x, conj (u x) * dv μ x := fun μ =>
    integral_conj_partial_mul hu (hv μ) (hgu μ) (hdv2 μ) (hdu μ) (hdv μ)
  simp only [h1, Finset.sum_neg_distrib, neg_eq_zero]
  rw [← integral_finsetSum _ fun μ _ => integrable_conj_mul hu (hdv2 μ)]
  have e : (fun x => ∑ μ, conj (u x) * dv μ x) =ᵐ[volume] fun _ => (0 : ℂ) := by
    filter_upwards [hdiv] with x hx
    rw [← Finset.mul_sum, hx, mul_zero]
  rw [integral_congr_ae e, integral_zero]

/-- `(Σ_{i} x_i)² ≤ N Σ x_i²` over a finite type with `N` elements. -/
theorem sq_sum_le_card_mul {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    (∑ i, x i) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, x i ^ 2 := by
  have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := x)
  simpa using this

theorem sum_mul_add_mul_eq {ι : Type*} (s : Finset ι) (K : ℝ≥0∞) (x y : ι → ℝ≥0∞) :
    ∑ k ∈ s, (K * x k + y k * K) = K * (∑ k ∈ s, x k + ∑ k ∈ s, y k) := by
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **Rigidity of intertwiners between small Coulomb connections** (the common core of the
uniqueness of the Coulomb gauge and of the injectivity of the linearised Coulomb operator).
There is `δ > 0` depending only on `m` such that: if `a, b` are matrix-valued one-forms on `𝕋⁴`
with `H¹` entries, both in Coulomb gauge, with `Σ‖a_{μ,ce}‖_4 + Σ‖b_{μ,ce}‖_4 ≤ δ`, and a matrix
function `g` with `H¹` entries satisfies `∂_μ g = g a_μ - b_μ g + η_μ` a.e. with an `L²` remainder
`η` orthogonal to `∇g` (`Σ_μ ⟨∂_μ g_{ce}, η_{μ,ce}⟩ = 0`), then `∇g = 0` and `g` is a.e. equal to
the constant matrix of its means. -/
theorem coulomb_intertwiner_const (m : ℕ) : ∃ δ : ℝ≥0, 0 < δ ∧
    ∀ (a b : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ) (da db : Fin 4 → Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ)
      (g : Fin m → Fin m → 𝕋⁴ → ℂ) (dg η : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ),
      IsH1Form a da → IsH1Form b db → IsCoulomb da → IsCoulomb db →
      (∀ c e, MemLp (g c e) 2 volume) → (∀ c e μ, MemLp (dg c e μ) 2 volume) →
      (∀ c e μ, IsTPartial μ (g c e) (dg c e μ)) → (∀ c e μ, MemLp (η c e μ) 2 volume) →
      (∀ c e, ∑ μ, ∫ x, conj (dg c e μ x) * η c e μ x = 0) →
      (∀ c e μ, ∀ᵐ x ∂volume,
        dg c e μ x = ∑ k, (g c k x * a μ k e x - b μ c k x * g k e x) + η c e μ x) →
      (∑ μ, ∑ c, ∑ e, eLpNorm (a μ c e) 4 volume +
        ∑ μ, ∑ c, ∑ e, eLpNorm (b μ c e) 4 volume ≤ δ) →
      (∀ c e μ, dg c e μ =ᵐ[volume] 0) ∧
        (∀ c e, ∀ᵐ x ∂volume, g c e x = mFourierCoeff (g c e) 0) := by
  refine ⟨(28 * (m : ℝ≥0) ^ 2 + 1)⁻¹, by positivity, ?_⟩
  intro a b da db g dg η ha hb hCa hCb hg hdg hgd hη2 hηo hrel hsmall
  set δ : ℝ≥0 := (28 * (m : ℝ≥0) ^ 2 + 1)⁻¹ with hδdef
  -- notation
  set gb : Fin m → Fin m → ℂ := fun c e => mFourierCoeff (g c e) 0
  set h : Fin m → Fin m → 𝕋⁴ → ℂ := fun c e x => g c e x - gb c e
  have hint : ∀ c e, Integrable (g c e) volume := fun c e => integrable_of_memLp_two (hg c e)
  have hh2 : ∀ c e, MemLp (h c e) 2 volume := fun c e => (hg c e).sub (memLp_const _)
  have hhd : ∀ c e μ, IsTPartial μ (h c e) (dg c e μ) := fun c e μ =>
    (hgd c e μ).sub_const (hint c e) _
  have hh0 : ∀ c e, mFourierCoeff (h c e) 0 = 0 := fun c e => mFourierCoeff_sub_mean (hint c e)
  have hh4 : ∀ c e, eLpNorm (h c e) 4 volume ≤ 7 * ∑ μ, eLpNorm (dg c e μ) 2 volume :=
    fun c e => eLpNorm_four_le_of_mean_zero (hh2 c e) (hdg c e) (hhd c e) (hh0 c e)
  have hdgt : ∀ c e μ, eLpNorm (dg c e μ) 2 volume ≠ ⊤ := fun c e μ => (hdg c e μ).2.ne
  have hh4t : ∀ c e, eLpNorm (h c e) 4 volume ≠ ⊤ := fun c e =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num)
      (ENNReal.sum_ne_top.2 fun μ _ => hdgt c e μ)) (hh4 c e)
  have hδt : ((δ : ℝ≥0) : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have ha4le : ∀ μ c e, eLpNorm (a μ c e) 4 volume ≤ δ := fun μ c e =>
    (le_sum_three (fun μ c e => eLpNorm (a μ c e) 4 volume) μ c e).trans (le_self_add.trans hsmall)
  have hb4le : ∀ μ c e, eLpNorm (b μ c e) 4 volume ≤ δ := fun μ c e =>
    (le_sum_three (fun μ c e => eLpNorm (b μ c e) 4 volume) μ c e).trans (le_add_self.trans hsmall)
  have ha4 : ∀ μ c e, MemLp (a μ c e) 4 volume := fun μ c e =>
    ⟨(ha.memLp μ c e).1, lt_of_le_of_lt (ha4le μ c e) ENNReal.coe_lt_top⟩
  have hb4 : ∀ μ c e, MemLp (b μ c e) 4 volume := fun μ c e =>
    ⟨(hb.memLp μ c e).1, lt_of_le_of_lt (hb4le μ c e) ENNReal.coe_lt_top⟩
  have hh4m : ∀ c e, MemLp (h c e) 4 volume := fun c e =>
    ⟨(hh2 c e).1, lt_top_iff_ne_top.2 (hh4t c e)⟩
  -- the remainder `R = Σ_k (h a - b h)`
  set R : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ := fun c e μ x =>
    ∑ k, (h c k x * a μ k e x - b μ c k x * h k e x)
  have hR2 : ∀ c e μ, MemLp (R c e μ) 2 volume := fun c e μ =>
    memLp_finsetSum _ fun k _ => ((ha4 μ k e).mul' (hh4m c k) (r := 2)).sub
      ((hh4m k e).mul' (hb4 μ c k) (r := 2))
  -- Step A: pointwise decomposition and integration
  have hdec : ∀ c e μ, ∫ x, conj (dg c e μ x) * dg c e μ x =
      (∫ x, conj (dg c e μ x) * R c e μ x) + ∑ k, (gb c k * (∫ x, conj (dg c e μ x) * a μ k e x) -
        gb k e * (∫ x, conj (dg c e μ x) * b μ c k x)) +
        ∫ x, conj (dg c e μ x) * η c e μ x := by
    intro c e μ
    have hpt : (fun x => conj (dg c e μ x) * dg c e μ x) =ᵐ[volume] fun x =>
        conj (dg c e μ x) * R c e μ x + ∑ k, (gb c k * (conj (dg c e μ x) * a μ k e x) -
          gb k e * (conj (dg c e μ x) * b μ c k x)) + conj (dg c e μ x) * η c e μ x := by
      filter_upwards [hrel c e μ] with x hx
      refine (congrArg (fun z => conj (dg c e μ x) * z) hx).trans ?_
      rw [mul_add]
      congr 1
      simp only [R, h, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    have hI1 : ∀ k, Integrable (fun x => gb c k * (conj (dg c e μ x) * a μ k e x) -
        gb k e * (conj (dg c e μ x) * b μ c k x)) volume := fun k =>
      ((integrable_conj_mul (hdg c e μ) (ha.memLp μ k e)).const_mul _).sub
        ((integrable_conj_mul (hdg c e μ) (hb.memLp μ c k)).const_mul _)
    have hI2 : Integrable (fun x => ∑ k, (gb c k * (conj (dg c e μ x) * a μ k e x) -
        gb k e * (conj (dg c e μ x) * b μ c k x))) volume :=
      integrable_finsetSum Finset.univ fun k _ => hI1 k
    have hI3 : Integrable (fun x => conj (dg c e μ x) * R c e μ x + ∑ k,
        (gb c k * (conj (dg c e μ x) * a μ k e x) -
          gb k e * (conj (dg c e μ x) * b μ c k x))) volume :=
      (integrable_conj_mul (hdg c e μ) (hR2 c e μ)).add hI2
    rw [integral_congr_ae hpt,
      integral_add hI3 (integrable_conj_mul (hdg c e μ) (hη2 c e μ)),
      integral_add (integrable_conj_mul (hdg c e μ) (hR2 c e μ)) hI2,
      integral_finsetSum _ fun k _ => hI1 k]
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_sub ((integrable_conj_mul (hdg c e μ) (ha.memLp μ k e)).const_mul _)
      ((integrable_conj_mul (hdg c e μ) (hb.memLp μ c k)).const_mul _), integral_const_mul,
      integral_const_mul]
  -- Step B: the constant part drops out after summing over `μ`
  have hsumμ : ∀ c e, ∑ μ, ∫ x, conj (dg c e μ x) * dg c e μ x =
      ∑ μ, ∫ x, conj (dg c e μ x) * R c e μ x := by
    intro c e
    have hA : ∀ k, ∑ μ, ∫ x, conj (dg c e μ x) * a μ k e x = 0 := fun k =>
      sum_integral_conj_partial_coclosed (hg c e) (hdg c e) (hgd c e) (fun μ => ha.memLp μ k e)
        (fun μ => ha.memLp_grad μ k e μ) (fun μ => ha.hasPartial μ k e μ) (hCa k e)
    have hB : ∀ k, ∑ μ, ∫ x, conj (dg c e μ x) * b μ c k x = 0 := fun k =>
      sum_integral_conj_partial_coclosed (hg c e) (hdg c e) (hgd c e) (fun μ => hb.memLp μ c k)
        (fun μ => hb.memLp_grad μ c k μ) (fun μ => hb.hasPartial μ c k μ) (hCb c k)
    rw [Finset.sum_congr rfl fun μ _ => hdec c e μ, Finset.sum_add_distrib,
      Finset.sum_add_distrib, hηo c e, add_zero]
    have hz : ∑ μ, ∑ k, (gb c k * (∫ x, conj (dg c e μ x) * a μ k e x) -
        gb k e * (∫ x, conj (dg c e μ x) * b μ c k x)) = 0 := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hA, hB, mul_zero, sub_zero,
        Finset.sum_const_zero]
    rw [hz, add_zero]
  -- Step C: real parts
  set G : Fin m → Fin m → Fin 4 → ℝ := fun c e μ => (eLpNorm (dg c e μ) 2 volume).toReal
  set Rn : Fin m → Fin m → Fin 4 → ℝ := fun c e μ => (eLpNorm (R c e μ) 2 volume).toReal
  have hC : ∀ c e, ∑ μ, G c e μ ^ 2 ≤ ∑ μ, G c e μ * Rn c e μ := by
    intro c e
    have h1 : ∑ μ, G c e μ ^ 2 = (∑ μ, ∫ x, conj (dg c e μ x) * dg c e μ x).re := by
      rw [Complex.re_sum]
      exact Finset.sum_congr rfl fun μ _ => (re_integral_conj_mul_self (hdg c e μ)).symm
    rw [h1, hsumμ c e, Complex.re_sum]
    exact Finset.sum_le_sum fun μ _ => re_integral_conj_mul_le (hdg c e μ) (hR2 c e μ)
  -- Step D: the remainder bound
  set Zt : ℝ≥0∞ := ∑ c, ∑ e, ∑ μ, eLpNorm (dg c e μ) 2 volume
  have hZt : Zt ≠ ⊤ := ENNReal.sum_ne_top.2 fun c _ => ENNReal.sum_ne_top.2 fun e _ =>
    ENNReal.sum_ne_top.2 fun μ _ => hdgt c e μ
  have hh4Z : ∀ c e, eLpNorm (h c e) 4 volume ≤ 7 * Zt := fun c e =>
    (hh4 c e).trans (by
      gcongr
      exact (Finset.single_le_sum (f := fun e => ∑ μ, eLpNorm (dg c e μ) 2 volume)
        (fun _ _ => zero_le) (Finset.mem_univ e)).trans
        (Finset.single_le_sum (f := fun c => ∑ e, ∑ μ, eLpNorm (dg c e μ) 2 volume)
          (fun _ _ => zero_le) (Finset.mem_univ c)))
  have hRle : ∀ c e μ, eLpNorm (R c e μ) 2 volume ≤ 7 * Zt * δ := by
    intro c e μ
    have e' : R c e μ = ∑ k, (fun x => h c k x * a μ k e x - b μ c k x * h k e x) := by
      funext x; simp only [R, Finset.sum_apply]
    rw [e']
    refine (eLpNorm_sum_le (f := fun k x => h c k x * a μ k e x - b μ c k x * h k e x)
      (fun k _ => ((hh2 c k).1.mul (ha.memLp μ k e).1).sub ((hb.memLp μ c k).1.mul (hh2 k e).1))
      (by norm_num)).trans ?_
    calc ∑ k, eLpNorm (fun x => h c k x * a μ k e x - b μ c k x * h k e x) 2 volume
        ≤ ∑ k, (eLpNorm (h c k) 4 volume * eLpNorm (a μ k e) 4 volume +
            eLpNorm (b μ c k) 4 volume * eLpNorm (h k e) 4 volume) := by
          refine Finset.sum_le_sum fun k _ => (eLpNorm_sub_le ((hh2 c k).1.mul (ha.memLp μ k e).1)
            ((hb.memLp μ c k).1.mul (hh2 k e).1) (by norm_num)).trans (add_le_add ?_ ?_)
          · exact eLpNorm_mul_le_L4 (hh2 c k).1 (ha.memLp μ k e).1
          · exact eLpNorm_mul_le_L4 (hb.memLp μ c k).1 (hh2 k e).1
      _ ≤ ∑ k, (7 * Zt * eLpNorm (a μ k e) 4 volume + eLpNorm (b μ c k) 4 volume * (7 * Zt)) := by
          gcongr with k
          · exact hh4Z c k
          · exact hh4Z k e
      _ = 7 * Zt * (∑ k, eLpNorm (a μ k e) 4 volume + ∑ k, eLpNorm (b μ c k) 4 volume) := by
          exact sum_mul_add_mul_eq _ _ _ _
      _ ≤ 7 * Zt * δ := by
          gcongr
          refine le_trans (add_le_add ?_ ?_) hsmall
          · calc ∑ k, eLpNorm (a μ k e) 4 volume ≤ ∑ k, ∑ e', eLpNorm (a μ k e') 4 volume :=
                  Finset.sum_le_sum fun k _ => Finset.single_le_sum
                    (f := fun e' => eLpNorm (a μ k e') 4 volume) (fun _ _ => zero_le)
                    (Finset.mem_univ e)
              _ ≤ ∑ μ', ∑ c', ∑ e', eLpNorm (a μ' c' e') 4 volume :=
                  Finset.single_le_sum (f := fun μ' => ∑ c', ∑ e', eLpNorm (a μ' c' e') 4 volume)
                    (fun _ _ => zero_le) (Finset.mem_univ μ)
          · calc ∑ k, eLpNorm (b μ c k) 4 volume ≤ ∑ c', ∑ k, eLpNorm (b μ c' k) 4 volume :=
                  Finset.single_le_sum (f := fun c' => ∑ k, eLpNorm (b μ c' k) 4 volume)
                    (fun _ _ => zero_le) (Finset.mem_univ c)
              _ ≤ ∑ μ', ∑ c', ∑ e', eLpNorm (b μ' c' e') 4 volume :=
                  Finset.single_le_sum (f := fun μ' => ∑ c', ∑ e', eLpNorm (b μ' c' e') 4 volume)
                    (fun _ _ => zero_le) (Finset.mem_univ μ)
  -- Step E: the quadratic inequality `Y ≤ 28 m² δ Y`
  set Zr : ℝ := ∑ c, ∑ e, ∑ μ, G c e μ
  have hZr : Zt.toReal = Zr := by
    simp only [Zt, Zr, G]
    rw [ENNReal.toReal_sum fun c _ => ENNReal.sum_ne_top.2 fun e _ =>
      ENNReal.sum_ne_top.2 fun μ _ => hdgt c e μ]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [ENNReal.toReal_sum fun e _ => ENNReal.sum_ne_top.2 fun μ _ => hdgt c e μ]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [ENNReal.toReal_sum fun μ _ => hdgt c e μ]
  have hRn : ∀ c e μ, Rn c e μ ≤ 7 * Zr * δ := by
    intro c e μ
    have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) hZt)
      ENNReal.coe_ne_top) (hRle c e μ)
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, hZr, ENNReal.coe_toReal] at h1
    simpa using h1
  have hG0 : ∀ c e μ, 0 ≤ G c e μ := fun _ _ _ => ENNReal.toReal_nonneg
  have hZr0 : 0 ≤ Zr := Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun e _ =>
    Finset.sum_nonneg fun μ _ => hG0 c e μ
  set Y : ℝ := ∑ c, ∑ e, ∑ μ, G c e μ ^ 2
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun e _ =>
    Finset.sum_nonneg fun μ _ => sq_nonneg _
  have hY1 : Y ≤ 7 * (δ : ℝ) * Zr ^ 2 := by
    calc Y ≤ ∑ c, ∑ e, ∑ μ, G c e μ * (7 * Zr * δ) :=
          Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun e _ => (hC c e).trans
            (Finset.sum_le_sum fun μ _ => mul_le_mul_of_nonneg_left (hRn c e μ) (hG0 c e μ))
      _ = 7 * (δ : ℝ) * Zr ^ 2 := by
          simp only [← Finset.sum_mul, Zr]; ring
  have hY2 : Zr ^ 2 ≤ 4 * (m : ℝ) ^ 2 * Y := by
    have := sq_sum_le_card_mul (fun p : Fin m × Fin m × Fin 4 => G p.1 p.2.1 p.2.2)
    simp only [Fintype.sum_prod_type, Fintype.card_prod, Fintype.card_fin] at this
    calc Zr ^ 2 ≤ ((m * (m * 4) : ℕ) : ℝ) * Y := this
      _ = 4 * (m : ℝ) ^ 2 * Y := by push_cast; ring
  have hδr : (δ : ℝ) = (28 * (m : ℝ) ^ 2 + 1)⁻¹ := by simp [δ]
  have hq : 28 * (m : ℝ) ^ 2 * (δ : ℝ) < 1 := by
    rw [hδr, ← div_eq_mul_inv, div_lt_one (by positivity)]; linarith
  have hY : Y = 0 := by
    have h3 : Y ≤ 28 * (m : ℝ) ^ 2 * (δ : ℝ) * Y := by
      calc Y ≤ 7 * (δ : ℝ) * Zr ^ 2 := hY1
        _ ≤ 7 * (δ : ℝ) * (4 * (m : ℝ) ^ 2 * Y) := by gcongr
        _ = 28 * (m : ℝ) ^ 2 * (δ : ℝ) * Y := by ring
    nlinarith
  -- Step F: conclusions
  have hGz : ∀ c e μ, G c e μ = 0 := by
    intro c e μ
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => Finset.sum_nonneg fun e _ =>
      Finset.sum_nonneg fun μ _ => sq_nonneg (G c e μ))).1 hY c (Finset.mem_univ c)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun e _ =>
      Finset.sum_nonneg fun μ _ => sq_nonneg (G c e μ))).1 h1 e (Finset.mem_univ e)
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun μ _ => sq_nonneg (G c e μ))).1 h2 μ
      (Finset.mem_univ μ)
    exact pow_eq_zero_iff (two_ne_zero) |>.1 h3
  have hdg0 : ∀ c e μ, eLpNorm (dg c e μ) 2 volume = 0 := by
    intro c e μ
    rcases (ENNReal.toReal_eq_zero_iff _).1 (hGz c e μ) with h1 | h1
    · exact h1
    · exact absurd h1 (hdgt c e μ)
  refine ⟨fun c e μ => (eLpNorm_eq_zero_iff (hdg c e μ).1 (by norm_num)).1 (hdg0 c e μ),
    fun c e => ?_⟩
  have hP := eLpNorm_le_of_mean_zero (hh2 c e) (hdg c e) (hhd c e) (hh0 c e)
  simp only [hdg0, Finset.sum_const_zero, nonpos_iff_eq_zero] at hP
  filter_upwards [(eLpNorm_eq_zero_iff (hh2 c e).1 (by norm_num)).1 hP] with x hx
  have : g c e x - gb c e = 0 := hx
  exact sub_eq_zero.1 this

/-- **Uniqueness of the Coulomb gauge up to constants** (Uhlenbeck, periodic rendering).  There is
`δ > 0` depending only on `m` such that: if `a, b` are matrix-valued one-forms on `𝕋⁴` with `H¹`
entries, both in Coulomb gauge, with total `L⁴` norm `Σ‖a_{μ,ce}‖_4 + Σ‖b_{μ,ce}‖_4 ≤ δ`, and a
matrix function `g` with `H¹` entries intertwines them, `∂_μ g = g a_μ - b_μ g` a.e. (for an
invertible `g` this is exactly `b = g a g⁻¹ - dg g⁻¹`, the gauge action), then `∇g = 0` and `g`
is a.e. equal to the constant matrix of its means. -/
theorem coulomb_gauge_unique_torus (m : ℕ) : ∃ δ : ℝ≥0, 0 < δ ∧
    ∀ (a b : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ) (da db : Fin 4 → Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ)
      (g : Fin m → Fin m → 𝕋⁴ → ℂ) (dg : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ),
      IsH1Form a da → IsH1Form b db → IsCoulomb da → IsCoulomb db →
      (∀ c e, MemLp (g c e) 2 volume) → (∀ c e μ, MemLp (dg c e μ) 2 volume) →
      (∀ c e μ, IsTPartial μ (g c e) (dg c e μ)) →
      (∀ c e μ, ∀ᵐ x ∂volume,
        dg c e μ x = ∑ k, (g c k x * a μ k e x - b μ c k x * g k e x)) →
      (∑ μ, ∑ c, ∑ e, eLpNorm (a μ c e) 4 volume +
        ∑ μ, ∑ c, ∑ e, eLpNorm (b μ c e) 4 volume ≤ δ) →
      (∀ c e μ, dg c e μ =ᵐ[volume] 0) ∧
        (∀ c e, ∀ᵐ x ∂volume, g c e x = mFourierCoeff (g c e) 0) := by
  obtain ⟨δ, hδ, H⟩ := coulomb_intertwiner_const m
  refine ⟨δ, hδ, fun a b da db g dg ha hb hCa hCb hg hdg hgd hrel hsmall => ?_⟩
  exact H a b da db g dg (fun _ _ _ _ => 0) ha hb hCa hCb hg hdg hgd
    (fun _ _ _ => memLp_const 0) (fun c e => by simp)
    (fun c e μ => (hrel c e μ).mono fun x hx => by rw [hx, add_zero]) hsmall

/-- The linearised covariant derivative `(d_a ξ)_μ = ∂_μ ξ + [a_μ, ξ]` (matrix entries). -/
def covLin {m : ℕ} (a : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ) (ξ : Fin m → Fin m → 𝕋⁴ → ℂ)
    (dξ : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ) (c e : Fin m) (μ : Fin 4) (x : 𝕋⁴) : ℂ :=
  dξ c e μ x + ∑ k, (a μ c k x * ξ k e x - ξ c k x * a μ k e x)

/-- **Injectivity of the linearised Coulomb operator modulo constants** (the infinitesimal form of
the uniqueness; the injectivity input of the implicit-function step).  There is `δ > 0` depending
only on `m` such that, for a Coulomb one-form `a` with `H¹` entries and `2 Σ‖a_{μ,ce}‖_4 ≤ δ`,
every matrix function `ξ` with `H¹` entries in the kernel of `L_a = d^* d_a` in the weak sense
(`d_a ξ ⊥ ∇u` in `L²` for every `H¹` function `u`, entrywise) is constant: `∇ξ = 0`. -/
theorem linearized_coulomb_kernel_const (m : ℕ) : ∃ δ : ℝ≥0, 0 < δ ∧
    ∀ (a : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ) (da : Fin 4 → Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ)
      (ξ : Fin m → Fin m → 𝕋⁴ → ℂ) (dξ : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ),
      IsH1Form a da → IsCoulomb da →
      (∀ c e, MemLp (ξ c e) 2 volume) → (∀ c e μ, MemLp (dξ c e μ) 2 volume) →
      (∀ c e μ, IsTPartial μ (ξ c e) (dξ c e μ)) →
      (∀ (u : 𝕋⁴ → ℂ) (gu : Fin 4 → 𝕋⁴ → ℂ), MemLp u 2 volume →
        (∀ μ, MemLp (gu μ) 2 volume) → (∀ μ, IsTPartial μ u (gu μ)) →
        ∀ c e, ∑ μ, ∫ x, conj (gu μ x) * covLin a ξ dξ c e μ x = 0) →
      2 * ∑ μ, ∑ c, ∑ e, eLpNorm (a μ c e) 4 volume ≤ δ →
      (∀ c e μ, dξ c e μ =ᵐ[volume] 0) ∧
        (∀ c e, ∀ᵐ x ∂volume, ξ c e x = mFourierCoeff (ξ c e) 0) := by
  obtain ⟨δ, hδ, H⟩ := coulomb_intertwiner_const m
  refine ⟨δ, hδ, fun a da ξ dξ ha hC hξ hdξ hξd hweak hsmall => ?_⟩
  have ha4 : ∀ μ c e, MemLp (a μ c e) 4 volume := by
    intro μ c e
    refine ⟨(ha.memLp μ c e).1, lt_of_le_of_lt ?_ (lt_of_le_of_lt hsmall ENNReal.coe_lt_top)⟩
    calc eLpNorm (a μ c e) 4 volume ≤ ∑ μ, ∑ c, ∑ e, eLpNorm (a μ c e) 4 volume :=
          le_sum_three (fun μ c e => eLpNorm (a μ c e) 4 volume) μ c e
      _ ≤ 2 * ∑ μ, ∑ c, ∑ e, eLpNorm (a μ c e) 4 volume :=
          le_mul_of_one_le_left zero_le (by norm_num)
  have hξ4 : ∀ c e, MemLp (ξ c e) 4 volume := by
    intro c e
    refine ⟨(hξ c e).1, lt_of_le_of_lt (eLpNorm_four_le_torus (hξ c e) (hdξ c e) (hξd c e)) ?_⟩
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by norm_num)
      (ENNReal.sum_lt_top.2 fun μ _ => (hdξ c e μ).2), ENNReal.mul_lt_top (by norm_num) (hξ c e).2⟩
  have hη2 : ∀ c e μ, MemLp (covLin a ξ dξ c e μ) 2 volume := fun c e μ =>
    (hdξ c e μ).add (memLp_finsetSum _ fun k _ => ((hξ4 k e).mul' (ha4 μ c k) (r := 2)).sub
      ((ha4 μ k e).mul' (hξ4 c k) (r := 2)))
  refine H a a da da ξ dξ (covLin a ξ dξ) ha ha hC hC hξ hdξ hξd hη2
    (fun c e => hweak (ξ c e) (dξ c e) (hξ c e) (hdξ c e) (hξd c e) c e)
    (fun c e μ => Eventually.of_forall fun x => ?_) (by rw [← two_mul]; exact hsmall)
  simp only [covLin]
  have h0 : ∑ k, (ξ c k x * a μ k e x - a μ c k x * ξ k e x) +
      ∑ k, (a μ c k x * ξ k e x - ξ c k x * a μ k e x) = 0 := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_eq_zero fun k _ => by ring
  linear_combination (-1 : ℂ) * h0

end RenewalGeometry.UhlenbeckTorus
