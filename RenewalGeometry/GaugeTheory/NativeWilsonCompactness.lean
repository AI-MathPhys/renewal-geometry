/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.TorusPiecewiseConstantTranslation
import RenewalGeometry.Continuum.CompactMagnitudeUniformIntegrabilityExact

/-!
# Direct native Wilson compactness

This file proves `thm:native-Wilson-compactness` of the Einstein–SM action-closure manuscript
(`papers/einstein_sm_action_closure`, Appendix "Wilson compactness and same-record Coulomb
normalization") on the periodic grid `(ℤ/N)^d` (`d = 4` in the manuscript).

## Setting and rendering

* Fibre: a finite-dimensional complex normed space `F` (the representation space).  The
  represented links `ρ(U_μ(x))` are unitary, rendered as linear isometry equivalences
  `V μ x : F ≃ₗᵢ[ℂ] F`.
* `openLink V μ m x = ρ(U_μ(x)) ρ(U_μ(x+e_μ)) ⋯ ρ(U_μ(x+(m-1)e_μ))` (`eq:open-finite-link`)
  and the Wilson shift `wilsonShift V μ m Y x = openLink V μ m x (Y(x + m e_μ))`
  (`eq:finite-Wilson-shift`).
* The Wilson screen `lim_{ρ↓0} limsup_{h↓0} Ω_h(Y_h;ρ) = 0` (`eq:native-Wilson-compactness`,
  `eq:finite-Wilson-modulus` on the entire periodic box) is used for positive displacements
  `0 < m h ≤ ρ` only, in the form "for every `ε` there is `ρ` such that eventually all these
  Wilson differences are at most `ε` in `L²_h`" (implied by the manuscript's hypothesis).
* Grid conventions (unit torus, mesh `h = 1/N`, `R^0`, `‖·‖_{2,h}`) are those of
  `Continuum/TorusPiecewiseConstantTranslation.lean` (the `2π`-box differs by a dilation).
* Link coordinates `U_h = e^{hA_h}` with `sup_h ‖A_h‖_{2,h} = M_A`: rendered by the pointwise
  consequence `‖ρ(U_μ(x)) v - v‖ ≤ h a_μ(x) ‖v‖` with `a_μ ≥ 0`, `‖a_μ‖_{2,h} ≤ M_A`
  (`a = C|A|`, `C` the representation constant; `norm_exp_sub_one_le` below shows that every
  unitary `exp(hX)` satisfies it with `a = e‖X‖`).

## Main results

* `abs_norm_shift_sub_le_wilson`: unitarity gives `| |Y|(x + m e_μ) - |Y|(x) | ≤ |W Y - Y|(x)`.
* `native_wilson_magnitude_totallyBounded` and `native_wilson_magnitude_unifIntegrable`: the
  scalar assertion: `|R^0 Y_h|` is precompact in `L²` and `|R^0 Y_h|²` is uniformly integrable,
  with no connection bound, in any site gauge.
* `gridNorm_shift_sub_le_wilson`: the estimate `eq:native-Wilson-ordinary-modulus`
  `‖T_{μ,m} Y - Y‖_{2,h} ≤ ‖W_{μ,m} Y - Y‖_{2,h} + R m h M_A + 2 q_h(R)`.
* `native_wilson_vector_totallyBounded`: the vector assertion: with the connection bound,
  `R^0 Y_h` itself is precompact in `L²`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace RenewalGeometry.NativeWilsonCompactness

open TorusPiecewiseConstantTranslation KolmogorovRieszTorus

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

variable {d : Type*} [Fintype d] [DecidableEq d] {N : ℕ} [NeZero N]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-! ### Open links and Wilson shifts -/

/-- The open finite link `𝒰_{μ,m}(x) = ρ(U_μ(x)) ⋯ ρ(U_μ(x + (m-1)e_μ))`. -/
def openLink (V : d → (d → ZMod N) → (F ≃ₗᵢ[ℂ] F)) (μ : d) : ℕ → (d → ZMod N) → (F ≃ₗᵢ[ℂ] F)
  | 0, _ => LinearIsometryEquiv.refl ℂ F
  | m + 1, x => (openLink V μ m (x + Pi.single μ 1)).trans (V μ x)

/-- The Wilson shift `W_{μ,m} Y (x) = 𝒰_{μ,m}(x) Y(x + m e_μ)`. -/
def wilsonShift (V : d → (d → ZMod N) → (F ≃ₗᵢ[ℂ] F)) (μ : d) (m : ℕ)
    (Y : (d → ZMod N) → F) : (d → ZMod N) → F :=
  fun x => openLink V μ m x (Y (x + Pi.single μ (m : ZMod N)))

theorem shift_natCast_apply {E : Type*} (μ : d) (m : ℕ) (u : (d → ZMod N) → E) (x : d → ZMod N) :
    shift μ (m : ℤ) u x = u (x + Pi.single μ (m : ZMod N)) := by
  simp [shift]

/-- **Translation Kato inequality on the grid.**  Unitarity of the links gives
`| |Y(x + m e_μ)| - |Y(x)| | ≤ |W_{μ,m} Y(x) - Y(x)|`. -/
theorem abs_norm_shift_sub_le_wilson (V : d → (d → ZMod N) → (F ≃ₗᵢ[ℂ] F)) (μ : d) (m : ℕ)
    (Y : (d → ZMod N) → F) (x : d → ZMod N) :
    |‖Y (x + Pi.single μ (m : ZMod N))‖ - ‖Y x‖| ≤ ‖wilsonShift V μ m Y x - Y x‖ := by
  have h := abs_norm_sub_norm_le (wilsonShift V μ m Y x) (Y x)
  simpa [wilsonShift, LinearIsometryEquiv.norm_map] using h

/-- The complex-valued magnitude `|Y|` of a grid field. -/
def mag (Y : (d → ZMod N) → F) : (d → ZMod N) → ℂ := fun x => ((‖Y x‖ : ℝ) : ℂ)

/-- The discrete magnitude modulus is controlled by the Wilson modulus. -/
theorem gridNorm_shift_mag_sub_le (V : d → (d → ZMod N) → (F ≃ₗᵢ[ℂ] F)) (μ : d) (m : ℕ)
    (Y : (d → ZMod N) → F) :
    gridNorm (shift μ (m : ℤ) (mag Y) - mag Y) ≤ gridNorm (wilsonShift V μ m Y - Y) := by
  refine gridNorm_mono fun x => ?_
  simp only [Pi.sub_apply, shift_natCast_apply, mag]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact abs_norm_shift_sub_le_wilson V μ m Y x

theorem gridNorm_mag (Y : (d → ZMod N) → F) : gridNorm (mag Y) = gridNorm Y := by
  unfold gridNorm mag
  simp

/-! ### The scalar assertion -/

variable [FiniteDimensional ℂ F]

/-- **`thm:native-Wilson-compactness`, scalar assertion (compactness).**  If `Y_k` is bounded
in `L²_h` on the periodic box, the links are unitary and the Wilson screen vanishes, then the
magnitudes `|R^0 Y_k|` are precompact in `L²(𝕋^d)`.  No connection bound is used, and the
hypotheses are invariant under site gauges. -/
theorem native_wilson_magnitude_totallyBounded (n : ℕ → ℕ) [∀ k, NeZero (n k)]
    (hn : Tendsto n atTop atTop) (V : ∀ k, d → (d → ZMod (n k)) → (F ≃ₗᵢ[ℂ] F))
    (Y : ∀ k, (d → ZMod (n k)) → F) (hbdd : ∃ M, ∀ k, gridNorm (Y k) ≤ M)
    (hΩ : ∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : d) (m : ℕ), 0 < m →
      (m : ℝ) / n k ≤ ρ → gridNorm (wilsonShift (V k) μ m (Y k) - Y k) ≤ ε) :
    TotallyBounded (range fun k => pcLp (mag (Y k))) := by
  obtain ⟨M, hM⟩ := hbdd
  refine native_discrete_KR n hn (fun k => mag (Y k))
    ⟨M, fun k => (gridNorm_mag (Y k)).trans_le (hM k)⟩ fun ε hε => ?_
  obtain ⟨ρ, hρ, hev⟩ := hΩ ε hε
  exact ⟨ρ, hρ, hev.mono fun k hk μ m hm hmρ =>
    (gridNorm_shift_mag_sub_le (V k) μ m (Y k)).trans (hk μ m hm hmρ)⟩

/-- The real-valued magnitude `|R^0 Y|` as an element of `L²(𝕋^d; ℝ)`. -/
theorem pc_mag_eq (Y : (d → ZMod N) → F) (y : UnitAddTorus d) :
    pc (mag Y) y = ((‖pc Y y‖ : ℝ) : ℂ) := rfl

/-- **`thm:native-Wilson-compactness`, scalar assertion (real-valued form).**  The real
magnitudes `|R^0 Y_k| ∈ L²(𝕋^d; ℝ)` form a totally bounded family. -/
theorem native_wilson_magnitude_totallyBounded_real (n : ℕ → ℕ) [∀ k, NeZero (n k)]
    (hn : Tendsto n atTop atTop) (V : ∀ k, d → (d → ZMod (n k)) → (F ≃ₗᵢ[ℂ] F))
    (Y : ∀ k, (d → ZMod (n k)) → F) (hbdd : ∃ M, ∀ k, gridNorm (Y k) ≤ M)
    (hΩ : ∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : d) (m : ℕ), 0 < m →
      (m : ℝ) / n k ≤ ρ → gridNorm (wilsonShift (V k) μ m (Y k) - Y k) ≤ ε) :
    TotallyBounded (range fun k => pcLp (fun x => ‖Y k x‖)) := by
  set ι : Lp ℝ 2 (volume : Measure (UnitAddTorus d)) → Lp ℂ 2 (volume : Measure (UnitAddTorus d)) :=
    fun f => (Complex.ofRealCLM).compLp f with hι
  have hnorm : ∀ f, ‖ι f‖ = ‖f‖ := by
    intro f
    rw [Lp.norm_def, Lp.norm_def]
    congr 1
    refine eLpNorm_congr_norm_ae ?_
    filter_upwards [(Complex.ofRealCLM).coeFn_compLp' f] with y hy
    rw [hy, Complex.ofRealCLM_apply, Complex.norm_real]
  have hiso : Isometry ι := by
    refine AddMonoidHomClass.isometry_of_norm
      ((ContinuousLinearMap.compLpL 2 volume Complex.ofRealCLM).toLinearMap.toAddMonoidHom) ?_
    intro f
    exact hnorm f
  refine (totallyBounded_preimage hiso.isUniformInducing
    (native_wilson_magnitude_totallyBounded n hn V Y hbdd hΩ)).subset ?_
  rintro _ ⟨k, rfl⟩
  refine ⟨k, Lp.ext ?_⟩
  filter_upwards [(Complex.ofRealCLM).coeFn_compLp' (pcLp fun x => ‖Y k x‖),
    (memLp_pc (mag (Y k))).coeFn_toLp, (memLp_pc fun x => ‖Y k x‖).coeFn_toLp] with y h1 h2 h3
  change (pcLp (mag (Y k))) y = (Complex.ofRealCLM.compLp (pcLp fun x => ‖Y k x‖)) y
  rw [h1]
  change ((memLp_pc (mag (Y k))).toLp _) y = Complex.ofRealCLM (((memLp_pc _).toLp _) y)
  rw [h2, h3]
  rfl

/-- **`thm:native-Wilson-compactness`, scalar assertion (uniform integrability).**  The squares
`|R^0 Y_k|²` are uniformly integrable (`UnifIntegrable` with exponent `2`). -/
theorem native_wilson_magnitude_unifIntegrable (n : ℕ → ℕ) [∀ k, NeZero (n k)]
    (hn : Tendsto n atTop atTop) (V : ∀ k, d → (d → ZMod (n k)) → (F ≃ₗᵢ[ℂ] F))
    (Y : ∀ k, (d → ZMod (n k)) → F) (hbdd : ∃ M, ∀ k, gridNorm (Y k) ≤ M)
    (hΩ : ∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : d) (m : ℕ), 0 < m →
      (m : ℝ) / n k ≤ ρ → gridNorm (wilsonShift (V k) μ m (Y k) - Y k) ≤ ε) :
    UnifIntegrable (fun k => pc (Y k)) 2 (volume : Measure (UnitAddTorus d)) := by
  have hUI := RenewalGeometry.compactMagnitude_unifIntegrable _
    (native_wilson_magnitude_totallyBounded n hn V Y hbdd hΩ)
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hUI hε
  refine ⟨δ, hδ, fun k s hs hμs => ?_⟩
  refine le_of_eq_of_le ?_ (h k s hs hμs)
  refine eLpNorm_congr_norm_ae ?_
  filter_upwards [(memLp_pc (mag (Y k))).coeFn_toLp] with y hy
  by_cases hys : y ∈ s
  · simp only [indicator_of_mem hys]
    change ‖pc (Y k) y‖ = ‖((memLp_pc (mag (Y k))).toLp _) y‖
    rw [hy, pc_mag_eq, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  · simp [indicator_of_notMem hys]


/-! ### Link estimates and the ordinary translation modulus -/

/-- Telescoping and unitarity: `‖𝒰_{μ,m}(x) v - v‖ ≤ (Σ_{j<m} h a(x + j e_μ)) ‖v‖`. -/
theorem norm_openLink_sub_le (V : d → (d → ZMod N) → (F ≃ₗᵢ[ℂ] F)) (μ : d)
    (a : (d → ZMod N) → ℝ) (hlink : ∀ x (v : F), ‖V μ x v - v‖ ≤ a x / N * ‖v‖) (m : ℕ)
    (x : d → ZMod N) (v : F) :
    ‖openLink V μ m x v - v‖ ≤
      (∑ j ∈ Finset.range m, a (x + Pi.single μ (j : ZMod N)) / N) * ‖v‖ := by
  induction m generalizing x with
  | zero => simp [openLink]
  | succ m ih =>
      have hstep : openLink V μ (m + 1) x v = V μ x (openLink V μ m (x + Pi.single μ 1) v) := rfl
      rw [hstep, Finset.sum_range_succ']
      have h1 : ‖V μ x (openLink V μ m (x + Pi.single μ 1) v) - v‖ ≤
          ‖openLink V μ m (x + Pi.single μ 1) v - v‖ + ‖V μ x v - v‖ := by
        calc ‖V μ x (openLink V μ m (x + Pi.single μ 1) v) - v‖
            = ‖(V μ x (openLink V μ m (x + Pi.single μ 1) v) - V μ x v) + (V μ x v - v)‖ := by
              abel_nf
          _ ≤ ‖V μ x (openLink V μ m (x + Pi.single μ 1) v) - V μ x v‖ + ‖V μ x v - v‖ :=
              norm_add_le _ _
          _ = _ := by rw [← map_sub, LinearIsometryEquiv.norm_map]
      refine h1.trans ?_
      have h2 := ih (x + Pi.single μ 1)
      have hre : ∀ j : ℕ, x + Pi.single μ 1 + Pi.single μ (j : ZMod N) =
          x + Pi.single μ ((j + 1 : ℕ) : ZMod N) := by
        intro j
        rw [add_assoc, ← Pi.single_add]
        push_cast
        rw [add_comm (1 : ZMod N)]
      simp only [hre] at h2
      have h3 := hlink x v
      simp only [Nat.cast_zero, Pi.single_zero, add_zero] at *
      nlinarith [h2, h3]

/-- The amplitude tail `1_{|Y| > R} Y`. -/
def tailPart (R : ℝ) (Y : (d → ZMod N) → F) : (d → ZMod N) → F :=
  fun x => if R < ‖Y x‖ then Y x else 0

theorem gridNorm_neg {E : Type*} [NormedAddCommGroup E] (u : (d → ZMod N) → E) :
    gridNorm (-u) = gridNorm u := by
  unfold gridNorm; simp

theorem gridNorm_sub_le {E : Type*} [NormedAddCommGroup E] (u v : (d → ZMod N) → E) :
    gridNorm (u - v) ≤ gridNorm u + gridNorm v := by
  rw [sub_eq_add_neg, ← gridNorm_neg v]
  exact gridNorm_add_le _ _

theorem gridNorm_norm {E : Type*} [NormedAddCommGroup E] (u : (d → ZMod N) → E) :
    gridNorm (fun x => ‖u x‖) = gridNorm u := by
  unfold gridNorm; simp

/-- **`eq:native-Wilson-ordinary-modulus`.**  With links `‖ρ(U_μ(x))v - v‖ ≤ h a_μ(x)‖v‖`,
`‖a_μ‖_{2,h} ≤ M_A` and any amplitude `R ≥ 0`,
`‖T_{μ,m} Y - Y‖_{2,h} ≤ ‖W_{μ,m} Y - Y‖_{2,h} + R (m h) M_A + 2 q_h(R)`,
`q_h(R) = ‖Y 1_{|Y| > R}‖_{2,h}`. -/
theorem gridNorm_shift_sub_le_wilson (V : d → (d → ZMod N) → (F ≃ₗᵢ[ℂ] F)) (μ : d)
    (a : (d → ZMod N) → ℝ) (ha0 : ∀ x, 0 ≤ a x)
    (hlink : ∀ x (v : F), ‖V μ x v - v‖ ≤ a x / N * ‖v‖) {MA : ℝ} (hA : gridNorm a ≤ MA)
    (m : ℕ) (Y : (d → ZMod N) → F) {R : ℝ} (hR : 0 ≤ R) :
    gridNorm (shift μ (m : ℤ) Y - Y) ≤
      gridNorm (wilsonShift V μ m Y - Y) + R * ((m : ℝ) / N * MA) +
        2 * gridNorm (tailPart R Y) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨S, hS⟩ : ∃ S : (d → ZMod N) → ℝ,
      S = fun x => ∑ j ∈ Finset.range m, a (x + Pi.single μ (j : ZMod N)) / N := ⟨_, rfl⟩
  have hS0 : ∀ x, 0 ≤ S x := fun x => by
    rw [hS]; exact Finset.sum_nonneg fun j _ => div_nonneg (ha0 _) hN.le
  -- pointwise transport error
  have hpt : ∀ x, ‖(wilsonShift V μ m Y - shift μ (m : ℤ) Y) x‖ ≤
      ‖R * S x + 2 * ‖tailPart R Y (x + Pi.single μ (m : ZMod N))‖‖ := by
    intro x
    set w := Y (x + Pi.single μ (m : ZMod N))
    have hW : (wilsonShift V μ m Y - shift μ (m : ℤ) Y) x = openLink V μ m x w - w := by
      simp [wilsonShift, shift_natCast_apply, w]
    rw [hW, Real.norm_of_nonneg (by have := hS0 x; positivity)]
    have hlk := norm_openLink_sub_le V μ a hlink m x w
    rw [show (∑ j ∈ Finset.range m, a (x + Pi.single μ (j : ZMod N)) / N) = S x by rw [hS]] at hlk
    by_cases hw : R < ‖w‖
    · have ht : tailPart R Y (x + Pi.single μ (m : ZMod N)) = w := by simp [tailPart, w, hw]
      rw [ht]
      have : ‖openLink V μ m x w - w‖ ≤ 2 * ‖w‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [LinearIsometryEquiv.norm_map]; linarith
      nlinarith [hS0 x]
    · have ht : tailPart R Y (x + Pi.single μ (m : ZMod N)) = 0 := by simp [tailPart, w, hw]
      rw [ht, norm_zero, mul_zero, add_zero]
      replace hw := not_lt.1 hw
      exact hlk.trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hw (hS0 x))
  have hWT : gridNorm (wilsonShift V μ m Y - shift μ (m : ℤ) Y) ≤
      R * ((m : ℝ) / N * MA) + 2 * gridNorm (tailPart R Y) := by
    set T : (d → ZMod N) → ℝ := fun x => ‖tailPart R Y (x + Pi.single μ (m : ZMod N))‖ with hT
    have hmono : gridNorm (wilsonShift V μ m Y - shift μ (m : ℤ) Y) ≤
        gridNorm ((fun x => R * S x) + fun x => 2 * T x) := gridNorm_mono hpt
    have hadd : gridNorm ((fun x => R * S x) + fun x => 2 * T x) ≤
        gridNorm (fun x => R * S x) + gridNorm (fun x => 2 * T x) := gridNorm_add_le _ _
    have hT' : gridNorm T = gridNorm (tailPart R Y) := by
      rw [hT, gridNorm_comp_add (fun x => ‖tailPart R Y x‖), gridNorm_norm]
    refine hmono.trans (hadd.trans ?_)
    rw [gridNorm_const_mul S hR, gridNorm_const_mul T (by norm_num : (0 : ℝ) ≤ 2), hT']
    refine add_le_add (mul_le_mul_of_nonneg_left ?_ hR) le_rfl
    have hSsum : S = ∑ j ∈ Finset.range m,
        fun x => (1 / (N : ℝ)) * a (x + Pi.single μ (j : ZMod N)) := by
      rw [hS]; funext x; simp only [Finset.sum_apply]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hSsum]
    refine (gridNorm_sum_le _ _).trans ?_
    calc ∑ j ∈ Finset.range m,
          gridNorm (fun x => (1 / (N : ℝ)) * a (x + Pi.single μ (j : ZMod N)))
        = ∑ j ∈ Finset.range m, (1 / (N : ℝ)) * gridNorm a := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [gridNorm_const_mul _ (by positivity), gridNorm_comp_add]
      _ ≤ ∑ j ∈ Finset.range m, (1 / (N : ℝ)) * MA :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left hA (by positivity)
      _ = (m : ℝ) / N * MA := by simp [Finset.sum_const]; ring
  have hsplit : shift μ (m : ℤ) Y - Y =
      (wilsonShift V μ m Y - Y) - (wilsonShift V μ m Y - shift μ (m : ℤ) Y) := by abel
  rw [hsplit]
  refine (gridNorm_sub_le _ _).trans ?_
  linarith

/-- The amplitude tails `q_h(R)` of a family whose reconstructions are uniformly integrable and
bounded tend to zero uniformly: `lim_{R→∞} sup_k q_k(R) = 0`. -/
theorem exists_tail_le (n : ℕ → ℕ) [∀ k, NeZero (n k)] (Y : ∀ k, (d → ZMod (n k)) → F)
    {M : ℝ} (hM : ∀ k, gridNorm (Y k) ≤ M)
    (hUI : UnifIntegrable (fun k => pc (Y k)) 2 (volume : Measure (UnitAddTorus d)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R, C ≤ R → ∀ k, gridNorm (tailPart R (Y k)) ≤ ε := by
  have hU : UniformIntegrable (fun k => pc (Y k)) 2 (volume : Measure (UnitAddTorus d)) := by
    refine ⟨fun k => (stronglyMeasurable_pc _).aestronglyMeasurable, hUI, M.toNNReal,
      fun k => ?_⟩
    rw [eLpNorm_pc]
    exact ENNReal.ofReal_le_ofReal (hM k)
  obtain ⟨C, hC⟩ := hU.spec' (by norm_num) (by norm_num) (fun k => stronglyMeasurable_pc _) hε
  refine ⟨C, C.2, fun R hR k => ?_⟩
  have h1 : eLpNorm (pc (tailPart R (Y k))) 2 (volume : Measure (UnitAddTorus d)) ≤
      ENNReal.ofReal ε := by
    refine le_trans (eLpNorm_mono fun y => ?_) (hC k)
    change ‖tailPart R (Y k) (index (n k) y)‖ ≤ ‖{x | C ≤ ‖pc (Y k) x‖₊}.indicator (pc (Y k)) y‖
    by_cases h : R < ‖Y k (index (n k) y)‖
    · have hmem : y ∈ {x | C ≤ ‖pc (Y k) x‖₊} := by
        change (C : ℝ) ≤ ‖pc (Y k) y‖
        exact hR.trans h.le
      rw [indicator_of_mem hmem]
      simp only [tailPart, h, ↓reduceIte]
      rfl
    · simp only [tailPart, h, ↓reduceIte, norm_zero]
      exact norm_nonneg _
  rw [eLpNorm_pc] at h1
  exact (ENNReal.ofReal_le_ofReal_iff hε.le).1 h1

/-- **`thm:native-Wilson-compactness`, vector assertion.**  If, in addition, the links have
coordinates with `sup_h ‖A_h‖_{2,h} = M_A < ∞` (rendered as `‖ρ(U_μ(x))v - v‖ ≤ h a_μ(x)‖v‖`,
`a ≥ 0`, `‖a_μ‖_{2,h} ≤ M_A`), then `R^0 Y_k` itself is precompact in `L²(𝕋^d)`. -/
theorem native_wilson_vector_totallyBounded (n : ℕ → ℕ) [∀ k, NeZero (n k)]
    (hn : Tendsto n atTop atTop) (V : ∀ k, d → (d → ZMod (n k)) → (F ≃ₗᵢ[ℂ] F))
    (Y : ∀ k, (d → ZMod (n k)) → F) (hbdd : ∃ M, ∀ k, gridNorm (Y k) ≤ M)
    (hΩ : ∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : d) (m : ℕ), 0 < m →
      (m : ℝ) / n k ≤ ρ → gridNorm (wilsonShift (V k) μ m (Y k) - Y k) ≤ ε)
    (a : ∀ k, d → (d → ZMod (n k)) → ℝ) (ha0 : ∀ k μ x, 0 ≤ a k μ x) {MA : ℝ}
    (hA : ∀ k μ, gridNorm (a k μ) ≤ MA)
    (hlink : ∀ k μ x (v : F), ‖V k μ x v - v‖ ≤ a k μ x / n k * ‖v‖) :
    TotallyBounded (range fun k => pcLp (Y k)) := by
  obtain ⟨M, hM⟩ := hbdd
  have hUI := native_wilson_magnitude_unifIntegrable n hn V Y ⟨M, hM⟩ hΩ
  refine native_discrete_KR n hn Y ⟨M, hM⟩ fun ε hε => ?_
  obtain ⟨C, hC0, hC⟩ := exists_tail_le n Y hM hUI (by positivity : (0 : ℝ) < ε / 6)
  obtain ⟨ρ₀, hρ₀, hev⟩ := hΩ (ε / 3) (by positivity)
  set ρ : ℝ := min ρ₀ (ε / (3 * (C * |MA| + 1))) with hρ
  have hρpos : 0 < ρ := lt_min hρ₀ (by positivity)
  refine ⟨ρ, hρpos, hev.mono fun k hk μ m hm hmρ => ?_⟩
  have hMA : 0 ≤ MA := (gridNorm_nonneg _).trans (hA k μ)
  have h1 := gridNorm_shift_sub_le_wilson (V k) μ (a k μ) (ha0 k μ) (hlink k μ) (hA k μ) m
    (Y k) hC0
  have h2 := hk μ m hm (hmρ.trans (min_le_left _ _))
  have h3 := hC C le_rfl k
  have h4 : C * ((m : ℝ) / n k * MA) ≤ ε / 3 := by
    have hle : (m : ℝ) / n k ≤ ε / (3 * (C * |MA| + 1)) := hmρ.trans (min_le_right _ _)
    rw [abs_of_nonneg hMA] at hle
    calc C * ((m : ℝ) / n k * MA) = (m : ℝ) / n k * (C * MA) := by ring
      _ ≤ ε / (3 * (C * MA + 1)) * (C * MA) :=
          mul_le_mul_of_nonneg_right hle (mul_nonneg hC0 hMA)
      _ ≤ ε / 3 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [mul_nonneg hC0 hMA]
  linarith


/-! ### Exponential link coordinates -/

/-- If `‖exp(tX)‖ ≤ 1` for `t ∈ [0,1]` (e.g. `exp(tX)` unitary), then `‖exp X - 1‖ ≤ ‖X‖`. -/
theorem norm_exp_sub_one_le_of_norm_exp_smul_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] (X : 𝔸) (h : ∀ t ∈ Icc (0 : ℝ) 1, ‖NormedSpace.exp (t • X)‖ ≤ 1) :
    ‖NormedSpace.exp X - 1‖ ≤ ‖X‖ := by
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun u : ℝ => NormedSpace.exp (u • X))
      (X * NormedSpace.exp (t • X)) (Icc 0 1) t :=
    fun t _ => (hasDerivAt_exp_smul_const' X t).hasDerivWithinAt
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ‖X * NormedSpace.exp (t • X)‖ ≤ ‖X‖ := by
    intro t ht
    refine (norm_mul_le _ _).trans ?_
    calc ‖X‖ * ‖NormedSpace.exp (t • X)‖ ≤ ‖X‖ * 1 :=
          mul_le_mul_of_nonneg_left (h t (Ico_subset_Icc_self ht)) (norm_nonneg _)
      _ = ‖X‖ := mul_one _
  have := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound 1 ⟨zero_le_one, le_rfl⟩
  simpa using this

/-- For a skew-adjoint operator `X` on a complex Hilbert space, `exp(tX)` is unitary, so
`‖exp X - 1‖ ≤ ‖X‖`. -/
theorem norm_exp_sub_one_le_of_skewAdjoint {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (X : H →L[ℂ] H) (hX : X ∈ skewAdjoint (H →L[ℂ] H)) :
    ‖NormedSpace.exp X - 1‖ ≤ ‖X‖ := by
  refine norm_exp_sub_one_le_of_norm_exp_smul_le X fun t _ => ?_
  have hmem : t • X ∈ skewAdjoint (H →L[ℂ] H) := skewAdjoint.smul_mem t hX
  let _ : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ (H →L[ℂ] H)
  have hu := NormedSpace.exp_mem_unitary_of_mem_skewAdjoint hmem
  rcases subsingleton_or_nontrivial (H →L[ℂ] H) with hs | hs
  · rw [Subsingleton.elim (NormedSpace.exp (t • X)) 0, norm_zero]; exact zero_le_one
  · exact (CStarRing.norm_of_mem_unitary hu).le

/-- **`thm:native-Wilson-compactness`, vector assertion in exponential link coordinates.**
Fibre: a finite-dimensional complex Hilbert space `H` carrying a unitary representation whose
derivative `dρ : 𝔤 →L[ℝ] End(H)` takes skew-adjoint values.  If the represented links are
`ρ(U_μ(x)) = exp(h dρ(A_μ(x)))` (`U_h = e^{hA_h}`, `h = 1/N`) with
`sup_k ‖A_{k,μ}‖_{2,h} ≤ M_A`, the family is bounded in `L²_h` and the Wilson screen vanishes, then
`R^0 Y_k` is precompact in `L²(𝕋^d)`. -/
theorem native_wilson_vector_totallyBounded_exp {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] {𝔤 : Type*} [NormedAddCommGroup 𝔤]
    [NormedSpace ℝ 𝔤] (dρ : 𝔤 →L[ℝ] (H →L[ℂ] H)) (hdρ : ∀ A, dρ A ∈ skewAdjoint (H →L[ℂ] H))
    (n : ℕ → ℕ) [∀ k, NeZero (n k)] (hn : Tendsto n atTop atTop)
    (V : ∀ k, d → (d → ZMod (n k)) → (H ≃ₗᵢ[ℂ] H)) (A : ∀ k, d → (d → ZMod (n k)) → 𝔤)
    (hV : ∀ k μ x (v : H), V k μ x v = NormedSpace.exp ((1 / (n k : ℝ)) • dρ (A k μ x)) v)
    {MA : ℝ} (hA : ∀ k μ, gridNorm (A k μ) ≤ MA)
    (Y : ∀ k, (d → ZMod (n k)) → H) (hbdd : ∃ M, ∀ k, gridNorm (Y k) ≤ M)
    (hΩ : ∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : d) (m : ℕ), 0 < m →
      (m : ℝ) / n k ≤ ρ → gridNorm (wilsonShift (V k) μ m (Y k) - Y k) ≤ ε) :
    TotallyBounded (range fun k => pcLp (Y k)) := by
  have : CompleteSpace H := FiniteDimensional.complete ℂ H
  refine native_wilson_vector_totallyBounded n hn V Y hbdd hΩ
    (fun k μ x => ‖dρ‖ * ‖A k μ x‖) (fun k μ x => by positivity) (MA := ‖dρ‖ * |MA|)
    (fun k μ => ?_) (fun k μ x v => ?_)
  · rw [gridNorm_const_mul (fun x => ‖A k μ x‖) (norm_nonneg _), gridNorm_norm]
    exact mul_le_mul_of_nonneg_left ((hA k μ).trans (le_abs_self _)) (norm_nonneg _)
  · have hN : (0 : ℝ) < n k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (n k))
    set X := (1 / (n k : ℝ)) • dρ (A k μ x) with hX
    have hXs : X ∈ skewAdjoint (H →L[ℂ] H) := skewAdjoint.smul_mem _ (hdρ _)
    have h1 : V k μ x v - v = (NormedSpace.exp X - 1) v := by
      rw [hV]; rfl
    rw [h1]
    refine ((NormedSpace.exp X - 1).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    refine (norm_exp_sub_one_le_of_skewAdjoint X hXs).trans ?_
    rw [hX, norm_smul, Real.norm_of_nonneg (by positivity)]
    calc 1 / (n k : ℝ) * ‖dρ (A k μ x)‖ ≤ 1 / (n k : ℝ) * (‖dρ‖ * ‖A k μ x‖) :=
          mul_le_mul_of_nonneg_left (dρ.le_opNorm _) (by positivity)
      _ = ‖dρ‖ * ‖A k μ x‖ / n k := by ring

end

end RenewalGeometry.NativeWilsonCompactness
