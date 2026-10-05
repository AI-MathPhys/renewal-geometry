/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeReconstructedConsistency
import RenewalGeometry.GaugeTheory.NativeWilsonCompactness
import RenewalGeometry.GaugeTheory.NativeActionGaugeInvariance
import RenewalGeometry.Analysis.FirstVariationCalculus

/-!
# The finite Wilson-screen zero-defect criterion: the Wilson/Coulomb extraction chain
  (`thm:finite-Wilson-zero-defect`, Einstein–SM action closure)

Einstein–SM action-closure manuscript, `thm:finite-Wilson-zero-defect` (Section "The finite
Wilson-screen criterion").  Its proof has a fixed direction: (i) same-record site-gauge
normalization from the rooted certificate `(F2)`; (ii) compactness of the literal packets from the
Wilson screens `(F3)` (`thm:native-Wilson-compactness`); (iii) critical discrete Coulomb absorption
(`thm:native-discrete-Coulomb`); (iv) the all-sector native theorem
(`thm:native-firstvariation-no-band`); (v) `(F5)` ⟹ stationarity; (vi) stress densities.

This file assembles **(ii)–(iv)** on the proved Lean theorems, after the normalization (i):

* `native_wilson_vector_totallyBounded_real`: `thm:native-Wilson-compactness` (vector assertion)
  for **real** finite-dimensional packet spaces with real linear isometric links (the library
  version is stated for complex fibres; the Higgs fibre of the native closure is `ℝ^{r_H}`); the
  proof is the library's, with `ℝ` for `ℂ`.
* `exists_subseq_lpTendsto`: precompactness of the raw reconstructions gives a strongly
  convergent subsequence.
* `exists_bankConv`: banks in a compact physical parameter set have a convergent subsequence
  (`(F4)`, second half).
* `wilson_coulomb_chain` (**`thm:finite-Wilson-zero-defect`, the extraction chain**): for records
  in exact discrete Coulomb gauge with `‖A_h‖_{4,h} ≤ ε_*` (the output of the normalization clause,
  `RootedCoulomb.rooted_coulomb_normalization`), under `(F1)`, `(F3)`, `(F4)`, after extraction:
  strong `H¹` coframes, strong `L⁴` connections with strongly convergent first differences,
  `F_{A_h} → F_A`, the Higgs and spinor conclusions, `eq:native-all-sector-limit` with cutoff banks,
  the reconstructed-field consistency, and the Euler equations under native stationarity.

Rendering: unit torus, mesh `h = 1/N`, as in the sector files; the Wilson screens are taken in
the form of `NativeWilsonCompactness` (positive displacements `0 < mh ≤ ρ`) on the literal packets
`𝔽_h = (F^h_{μν})_{μ,ν}` (all ordered pairs; on the plaquette chart the pairs `ν < μ` are the
negatives of `μ < ν`) and `𝕂_h = (K^h_μ)_μ`, with sup norms on the packet components.
-/

open MeasureTheory Set Finset Filter Topology Metric NormedSpace
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace RenewalGeometry.FiniteWilsonZeroDefect

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- The unit torus `𝕋⁴`. -/
local notation "𝕋" => UnitAddTorus (Fin 4)

open TorusPiecewiseConstantTranslation KolmogorovRieszTorus
open NativeGravityFirstJet (M4 asM4 coframeM liftL)

/-! ### Real Wilson compactness -/

section RealWilson

variable {d : Type*} [Fintype d] [DecidableEq d] {N : ℕ} [NeZero N]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The open finite link `𝒰_{μ,m}(x)` for real isometric links. -/
def openLinkR (V : d → (d → ZMod N) → (F ≃ₗᵢ[ℝ] F)) (μ : d) : ℕ → (d → ZMod N) → (F ≃ₗᵢ[ℝ] F)
  | 0, _ => LinearIsometryEquiv.refl ℝ F
  | m + 1, x => (openLinkR V μ m (x + Pi.single μ 1)).trans (V μ x)

/-- The Wilson shift `W_{μ,m} Y (x) = 𝒰_{μ,m}(x) Y(x + m e_μ)` (`eq:finite-Wilson-shift`). -/
def wilsonShiftR (V : d → (d → ZMod N) → (F ≃ₗᵢ[ℝ] F)) (μ : d) (m : ℕ)
    (Y : (d → ZMod N) → F) : (d → ZMod N) → F :=
  fun x => openLinkR V μ m x (Y (x + Pi.single μ (m : ZMod N)))

/-- The real magnitude `|Y|`. -/
def magR (Y : (d → ZMod N) → F) : (d → ZMod N) → ℝ := fun x => ‖Y x‖

theorem gridNorm_shift_magR_sub_le (V : d → (d → ZMod N) → (F ≃ₗᵢ[ℝ] F)) (μ : d) (m : ℕ)
    (Y : (d → ZMod N) → F) :
    gridNorm (shift μ (m : ℤ) (magR Y) - magR Y) ≤ gridNorm (wilsonShiftR V μ m Y - Y) := by
  refine gridNorm_mono fun x => ?_
  simp only [Pi.sub_apply, NativeWilsonCompactness.shift_natCast_apply, magR, Real.norm_eq_abs]
  have h := abs_norm_sub_norm_le (wilsonShiftR V μ m Y x) (Y x)
  simpa [wilsonShiftR, LinearIsometryEquiv.norm_map] using h

theorem gridNorm_magR (Y : (d → ZMod N) → F) : gridNorm (magR Y) = gridNorm Y := by
  unfold gridNorm magR
  simp

/-- The scalar assertion (uniform integrability of `|R^0 Y_k|²`). -/
theorem native_wilson_unifIntegrable_real (n : ℕ → ℕ) [∀ k, NeZero (n k)]
    (hn : Tendsto n atTop atTop) (V : ∀ k, d → (d → ZMod (n k)) → (F ≃ₗᵢ[ℝ] F))
    (Y : ∀ k, (d → ZMod (n k)) → F) (hbdd : ∃ M, ∀ k, gridNorm (Y k) ≤ M)
    (hΩ : ∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : d) (m : ℕ), 0 < m →
      (m : ℝ) / n k ≤ ρ → gridNorm (wilsonShiftR (V k) μ m (Y k) - Y k) ≤ ε) :
    UnifIntegrable (fun k => pc (Y k)) 2 (volume : Measure (UnitAddTorus d)) := by
  obtain ⟨M, hM⟩ := hbdd
  have hTB : TotallyBounded (range fun k => pcLp (magR (Y k))) := by
    refine native_discrete_KR n hn (fun k => magR (Y k))
      ⟨M, fun k => (gridNorm_magR (Y k)).trans_le (hM k)⟩ fun ε hε => ?_
    obtain ⟨ρ, hρ, hev⟩ := hΩ ε hε
    exact ⟨ρ, hρ, hev.mono fun k hk μ m hm hmρ =>
      (gridNorm_shift_magR_sub_le (V k) μ m (Y k)).trans (hk μ m hm hmρ)⟩
  have hUI := RenewalGeometry.compactMagnitude_unifIntegrable _ hTB
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hUI hε
  refine ⟨δ, hδ, fun k s hs hμs => ?_⟩
  refine le_of_eq_of_le ?_ (h k s hs hμs)
  refine eLpNorm_congr_norm_ae ?_
  filter_upwards [(memLp_pc (magR (Y k))).coeFn_toLp] with y hy
  by_cases hys : y ∈ s
  · simp only [indicator_of_mem hys]
    change ‖pc (Y k) y‖ = ‖((memLp_pc (magR (Y k))).toLp _) y‖
    rw [hy]
    simp [pc, magR]
  · simp [indicator_of_notMem hys]

theorem norm_openLinkR_sub_le (V : d → (d → ZMod N) → (F ≃ₗᵢ[ℝ] F)) (μ : d)
    (a : (d → ZMod N) → ℝ) (hlink : ∀ x (v : F), ‖V μ x v - v‖ ≤ a x / N * ‖v‖) (m : ℕ)
    (x : d → ZMod N) (v : F) :
    ‖openLinkR V μ m x v - v‖ ≤
      (∑ j ∈ Finset.range m, a (x + Pi.single μ (j : ZMod N)) / N) * ‖v‖ := by
  induction m generalizing x with
  | zero => simp [openLinkR]
  | succ m ih =>
      have hstep : openLinkR V μ (m + 1) x v = V μ x (openLinkR V μ m (x + Pi.single μ 1) v) :=
        rfl
      rw [hstep, Finset.sum_range_succ']
      have h1 : ‖V μ x (openLinkR V μ m (x + Pi.single μ 1) v) - v‖ ≤
          ‖openLinkR V μ m (x + Pi.single μ 1) v - v‖ + ‖V μ x v - v‖ := by
        calc ‖V μ x (openLinkR V μ m (x + Pi.single μ 1) v) - v‖
            = ‖(V μ x (openLinkR V μ m (x + Pi.single μ 1) v) - V μ x v) + (V μ x v - v)‖ := by
              abel_nf
          _ ≤ ‖V μ x (openLinkR V μ m (x + Pi.single μ 1) v) - V μ x v‖ + ‖V μ x v - v‖ :=
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

/-- `eq:native-Wilson-ordinary-modulus` for real isometric links. -/
theorem gridNorm_shift_sub_le_wilsonR (V : d → (d → ZMod N) → (F ≃ₗᵢ[ℝ] F)) (μ : d)
    (a : (d → ZMod N) → ℝ) (ha0 : ∀ x, 0 ≤ a x)
    (hlink : ∀ x (v : F), ‖V μ x v - v‖ ≤ a x / N * ‖v‖) {MA : ℝ} (hA : gridNorm a ≤ MA)
    (m : ℕ) (Y : (d → ZMod N) → F) {R : ℝ} (hR : 0 ≤ R) :
    gridNorm (shift μ (m : ℤ) Y - Y) ≤
      gridNorm (wilsonShiftR V μ m Y - Y) + R * ((m : ℝ) / N * MA) +
        2 * gridNorm (fun x => if R < ‖Y x‖ then Y x else 0) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set tp : (d → ZMod N) → F := fun x => if R < ‖Y x‖ then Y x else 0 with htp
  obtain ⟨S, hS⟩ : ∃ S : (d → ZMod N) → ℝ,
      S = fun x => ∑ j ∈ Finset.range m, a (x + Pi.single μ (j : ZMod N)) / N := ⟨_, rfl⟩
  have hS0 : ∀ x, 0 ≤ S x := fun x => by
    rw [hS]; exact Finset.sum_nonneg fun j _ => div_nonneg (ha0 _) hN.le
  have hpt : ∀ x, ‖(wilsonShiftR V μ m Y - shift μ (m : ℤ) Y) x‖ ≤
      ‖R * S x + 2 * ‖tp (x + Pi.single μ (m : ZMod N))‖‖ := by
    intro x
    set w := Y (x + Pi.single μ (m : ZMod N))
    have hW : (wilsonShiftR V μ m Y - shift μ (m : ℤ) Y) x = openLinkR V μ m x w - w := by
      simp [wilsonShiftR, NativeWilsonCompactness.shift_natCast_apply, w]
    rw [hW, Real.norm_of_nonneg (by have := hS0 x; positivity)]
    have hlk := norm_openLinkR_sub_le V μ a hlink m x w
    rw [show (∑ j ∈ Finset.range m, a (x + Pi.single μ (j : ZMod N)) / N) = S x by rw [hS]]
      at hlk
    by_cases hw : R < ‖w‖
    · have ht : tp (x + Pi.single μ (m : ZMod N)) = w := by simp [htp, w, hw]
      rw [ht]
      have : ‖openLinkR V μ m x w - w‖ ≤ 2 * ‖w‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [LinearIsometryEquiv.norm_map]; linarith
      nlinarith [hS0 x]
    · have ht : tp (x + Pi.single μ (m : ZMod N)) = 0 := by simp [htp, w, hw]
      rw [ht, norm_zero, mul_zero, add_zero]
      replace hw := not_lt.1 hw
      exact hlk.trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hw (hS0 x))
  have hWT : gridNorm (wilsonShiftR V μ m Y - shift μ (m : ℤ) Y) ≤
      R * ((m : ℝ) / N * MA) + 2 * gridNorm tp := by
    set T : (d → ZMod N) → ℝ := fun x => ‖tp (x + Pi.single μ (m : ZMod N))‖ with hT
    have hmono : gridNorm (wilsonShiftR V μ m Y - shift μ (m : ℤ) Y) ≤
        gridNorm ((fun x => R * S x) + fun x => 2 * T x) := gridNorm_mono hpt
    have hadd : gridNorm ((fun x => R * S x) + fun x => 2 * T x) ≤
        gridNorm (fun x => R * S x) + gridNorm (fun x => 2 * T x) := gridNorm_add_le _ _
    have hT' : gridNorm T = gridNorm tp := by
      rw [hT, gridNorm_comp_add (fun x => ‖tp x‖)]
      unfold gridNorm; simp
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
      (wilsonShiftR V μ m Y - Y) - (wilsonShiftR V μ m Y - shift μ (m : ℤ) Y) := by abel
  rw [hsplit]
  refine (NativeWilsonCompactness.gridNorm_sub_le _ _).trans ?_
  linarith

variable [FiniteDimensional ℝ F]

/-- Uniform smallness of the amplitude tails. -/
theorem exists_tail_leR (n : ℕ → ℕ) [∀ k, NeZero (n k)] (Y : ∀ k, (d → ZMod (n k)) → F)
    {M : ℝ} (hM : ∀ k, gridNorm (Y k) ≤ M)
    (hUI : UnifIntegrable (fun k => pc (Y k)) 2 (volume : Measure (UnitAddTorus d)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R, C ≤ R → ∀ k,
      gridNorm (fun x => if R < ‖Y k x‖ then Y k x else 0) ≤ ε := by
  have hU : UniformIntegrable (fun k => pc (Y k)) 2 (volume : Measure (UnitAddTorus d)) := by
    refine ⟨fun k => (stronglyMeasurable_pc _).aestronglyMeasurable, hUI, M.toNNReal,
      fun k => ?_⟩
    rw [eLpNorm_pc]
    exact ENNReal.ofReal_le_ofReal (hM k)
  obtain ⟨C, hC⟩ := hU.spec' (by norm_num) (by norm_num) (fun k => stronglyMeasurable_pc _) hε
  refine ⟨C, C.2, fun R hR k => ?_⟩
  have h1 : eLpNorm (pc (fun x => if R < ‖Y k x‖ then Y k x else 0)) 2
      (volume : Measure (UnitAddTorus d)) ≤ ENNReal.ofReal ε := by
    refine le_trans (eLpNorm_mono fun y => ?_) (hC k)
    change ‖(if R < ‖Y k (index (n k) y)‖ then Y k (index (n k) y) else 0)‖ ≤
      ‖{x | C ≤ ‖pc (Y k) x‖₊}.indicator (pc (Y k)) y‖
    by_cases h : R < ‖Y k (index (n k) y)‖
    · have hmem : y ∈ {x | C ≤ ‖pc (Y k) x‖₊} := by
        change (C : ℝ) ≤ ‖pc (Y k) y‖
        exact hR.trans h.le
      rw [indicator_of_mem hmem]
      simp only [h, ↓reduceIte]
      rfl
    · simp only [h, ↓reduceIte, norm_zero]
      exact norm_nonneg _
  rw [eLpNorm_pc] at h1
  exact (ENNReal.ofReal_le_ofReal_iff hε.le).1 h1

/-- **`thm:native-Wilson-compactness`, vector assertion, real fibres.**  If `Y_k` is bounded in
`L²_h`, the represented links are real linear isometries with `‖ρ(U_μ(x))v - v‖ ≤ h a_μ(x)‖v‖`,
`‖a_μ‖_{2,h} ≤ M_A`, and the Wilson screen vanishes, then `R^0 Y_k` is precompact in `L²`. -/
theorem native_wilson_vector_totallyBounded_real (n : ℕ → ℕ) [∀ k, NeZero (n k)]
    (hn : Tendsto n atTop atTop) (V : ∀ k, d → (d → ZMod (n k)) → (F ≃ₗᵢ[ℝ] F))
    (Y : ∀ k, (d → ZMod (n k)) → F) (hbdd : ∃ M, ∀ k, gridNorm (Y k) ≤ M)
    (hΩ : ∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : d) (m : ℕ), 0 < m →
      (m : ℝ) / n k ≤ ρ → gridNorm (wilsonShiftR (V k) μ m (Y k) - Y k) ≤ ε)
    (a : ∀ k, d → (d → ZMod (n k)) → ℝ) (ha0 : ∀ k μ x, 0 ≤ a k μ x) {MA : ℝ}
    (hA : ∀ k μ, gridNorm (a k μ) ≤ MA)
    (hlink : ∀ k μ x (v : F), ‖V k μ x v - v‖ ≤ a k μ x / n k * ‖v‖) :
    TotallyBounded (range fun k => pcLp (Y k)) := by
  obtain ⟨M, hM⟩ := hbdd
  have hUI := native_wilson_unifIntegrable_real n hn V Y ⟨M, hM⟩ hΩ
  refine native_discrete_KR n hn Y ⟨M, hM⟩ fun ε hε => ?_
  obtain ⟨C, hC0, hC⟩ := exists_tail_leR n Y hM hUI (by positivity : (0 : ℝ) < ε / 6)
  obtain ⟨ρ₀, hρ₀, hev⟩ := hΩ (ε / 3) (by positivity)
  set ρ : ℝ := min ρ₀ (ε / (3 * (C * |MA| + 1))) with hρ
  have hρpos : 0 < ρ := lt_min hρ₀ (by positivity)
  refine ⟨ρ, hρpos, hev.mono fun k hk μ m hm hmρ => ?_⟩
  have hMA : 0 ≤ MA := (gridNorm_nonneg _).trans (hA k μ)
  have h1 := gridNorm_shift_sub_le_wilsonR (V k) μ (a k μ) (ha0 k μ) (hlink k μ) (hA k μ) m
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

end RealWilson

/-! ### Extraction from precompactness -/

section Extraction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Precompact raw reconstructions have a strongly convergent subsequence.** -/
theorem exists_subseq_lpTendsto {n : ℕ → ℕ} [∀ k, NeZero (n k)]
    (u : ∀ k, (Fin 4 → ZMod (n k)) → E) (hTB : TotallyBounded (range fun k => pcLp (u k))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : 𝕋 → E, LpTendsto volume 2 (fun k => pc (u (φ k))) f := by
  obtain ⟨a, -, φ, hφ, ht⟩ := (hTB.closure.isCompact_of_isClosed isClosed_closure).tendsto_subseq
    (x := fun k => pcLp (u k)) fun k => subset_closure ⟨k, rfl⟩
  refine ⟨φ, hφ, a, fun k => memLp_pc _, Lp.memLp a, ?_⟩
  have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun k => pc (u (φ k)))
    (fun k => memLp_pc _) (a : 𝕋 → E) (Lp.memLp a)).1 (by
      rw [Lp.toLp_coeFn]
      exact ht)
  exact h

/-- Subsequences of totally bounded families are totally bounded. -/
theorem totallyBounded_comp {X : Type*} [UniformSpace X] {u : ℕ → X}
    (h : TotallyBounded (range u)) (φ : ℕ → ℕ) : TotallyBounded (range fun k => u (φ k)) :=
  h.subset (by rintro _ ⟨k, rfl⟩; exact ⟨φ k, rfl⟩)

end Extraction

/-! ### Isometric links of the two literal packets -/

section Links

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A linear isometry acting componentwise on a sup-normed tuple. -/
def piIso {ι : Type*} [Fintype ι] (L : G ≃ₗᵢ[ℝ] G) : (ι → G) ≃ₗᵢ[ℝ] (ι → G) where
  toLinearEquiv := LinearEquiv.piCongrRight fun _ => L.toLinearEquiv
  norm_map' v := by
    change ‖fun i => L (v i)‖ = ‖v‖
    simp only [Pi.norm_def, LinearIsometryEquiv.nnnorm_map]

@[simp] theorem piIso_apply {ι : Type*} [Fintype ι] (L : G ≃ₗᵢ[ℝ] G) (v : ι → G) (i : ι) :
    piIso L v i = L (v i) := rfl

theorem norm_piIso_sub_le {ι : Type*} [Fintype ι] (L : G ≃ₗᵢ[ℝ] G) {c : ℝ} (hc : 0 ≤ c)
    (hL : ∀ v, ‖L v - v‖ ≤ c * ‖v‖) (v : ι → G) : ‖piIso L v - v‖ ≤ c * ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  simp only [Pi.sub_apply, piIso_apply]
  exact (hL (v i)).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm v i) hc)

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]

theorem exp_mul_exp_neg' (Z : 𝔄) : exp Z * exp (-Z) = 1 := NativeDensity.exp_mul_exp_neg Z

theorem exp_neg_mul_exp' (Z : 𝔄) : exp (-Z) * exp Z = 1 := NativeDensity.exp_neg_mul_exp Z

/-- **The adjoint link** `Ad(e^Z) X = e^Z X e^{-Z}` as a real linear isometry, given that it
preserves the norm (unitary links of a compact gauge group). -/
def adIso (Z : 𝔄) (hZ : ∀ X : 𝔄, ‖exp Z * X * exp (-Z)‖ = ‖X‖) : 𝔄 ≃ₗᵢ[ℝ] 𝔄 where
  toFun X := exp Z * X * exp (-Z)
  invFun X := exp (-Z) * X * exp Z
  left_inv X := by
    simp only [← mul_assoc, exp_neg_mul_exp', one_mul]
    rw [mul_assoc, exp_neg_mul_exp', mul_one]
  right_inv X := by
    simp only [← mul_assoc, exp_mul_exp_neg', one_mul]
    rw [mul_assoc, exp_mul_exp_neg', mul_one]
  map_add' X Y := by simp only [mul_add, add_mul]
  map_smul' c X := by simp only [mul_smul_comm, smul_mul_assoc, RingHom.id_apply]
  norm_map' := hZ

@[simp] theorem adIso_apply (Z : 𝔄) (hZ : ∀ X : 𝔄, ‖exp Z * X * exp (-Z)‖ = ‖X‖) (X : 𝔄) :
    adIso Z hZ X = exp Z * X * exp (-Z) := rfl

/-- `‖e^Z X e^{-Z} - X‖ ≤ 6 ‖Z‖ ‖X‖` for `‖Z‖ ≤ 1/2`. -/
theorem norm_ad_sub_le {Z : 𝔄} (hZ : ‖Z‖ ≤ 1 / 2) (X : 𝔄) :
    ‖exp Z * X * exp (-Z) - X‖ ≤ 6 * ‖Z‖ * ‖X‖ := by
  have hZ1 : ‖Z‖ ≤ 1 := by linarith
  have hZ1' : ‖-Z‖ ≤ 1 := by rw [norm_neg]; exact hZ1
  have h1 := SeriesLogChart.norm_exp_sub_one_le hZ1
  have h2 := SeriesLogChart.norm_exp_sub_one_le hZ1'
  have h3 := SeriesLogChart.norm_exp_le_one_add hZ1'
  rw [norm_neg] at h2 h3
  have e : exp Z * X * exp (-Z) - X = (exp Z - 1) * X * exp (-Z) + X * (exp (-Z) - 1) := by
    noncomm_ring
  rw [e]
  have n1 : ‖(exp Z - 1) * X * exp (-Z)‖ ≤ ‖exp Z - 1‖ * ‖X‖ * ‖exp (-Z)‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
  have n2 : ‖X * (exp (-Z) - 1)‖ ≤ ‖X‖ * ‖exp (-Z) - 1‖ := norm_mul_le _ _
  have hX := norm_nonneg X
  have hz := norm_nonneg Z
  have hE := norm_nonneg (exp (-Z))
  have hE1 := norm_nonneg (exp Z - 1)
  calc _ ≤ ‖exp Z - 1‖ * ‖X‖ * ‖exp (-Z)‖ + ‖X‖ * ‖exp (-Z) - 1‖ :=
        (norm_add_le _ _).trans (add_le_add n1 n2)
    _ ≤ (2 * ‖Z‖) * ‖X‖ * 2 + ‖X‖ * (2 * ‖Z‖) := by
        gcongr
        linarith
    _ = 6 * ‖Z‖ * ‖X‖ := by ring

end Links

/-! ### Convergent subsequences of banks -/

section BankExtraction

open NativeBank NativeDensity

variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [FiniteDimensional ℝ 𝓢]
variable {J : ℕ}

/-- The coordinates of a bank `(κ, Λ, λ_H, v_H, w, Y)`. -/
def bankVec (θ : Bank J 𝓗 𝓢) : ℝ × ℝ × ℝ × ℝ × (Fin J → ℝ) × (𝓗 →L[ℝ] Spin 𝓢) :=
  (θ.κ, θ.Λ, θ.lamH, θ.vH, θ.w, θ.Y)

/-- **`(F4)`, banks**: cutoff banks in a compact physical parameter set (`κ ≠ 0`, nonnegative
gauge weights) have a convergent subsequence with a physical limit. -/
theorem exists_bankConv {θs : ℕ → Bank J 𝓗 𝓢}
    {Kθ : Set (ℝ × ℝ × ℝ × ℝ × (Fin J → ℝ) × (𝓗 →L[ℝ] Spin 𝓢))} (hK : IsCompact Kθ)
    (hθK : ∀ k, bankVec (θs k) ∈ Kθ) (hphys : ∀ v ∈ Kθ, v.1 ≠ 0 ∧ ∀ j, 0 ≤ v.2.2.2.2.1 j) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ θ : Bank J 𝓗 𝓢, BankConv (fun k => θs (φ k)) θ ∧
      θ.κ ≠ 0 ∧ ∀ j, 0 ≤ θ.w j := by
  obtain ⟨v, hv, φ, hφ, ht⟩ := hK.tendsto_subseq hθK
  refine ⟨φ, hφ, ⟨v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2⟩,
    ⟨(continuous_fst.tendsto v).comp ht, ((continuous_fst.comp continuous_snd).tendsto v).comp ht,
      ((continuous_fst.comp (continuous_snd.comp continuous_snd)).tendsto v).comp ht,
      ((continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).tendsto
        v).comp ht,
      fun j => (((continuous_apply j).comp (continuous_fst.comp (continuous_snd.comp
        (continuous_snd.comp (continuous_snd.comp continuous_snd))))).tendsto v).comp ht,
      ((continuous_snd.comp (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp
        continuous_snd)))).tendsto v).comp ht⟩, (hphys v hv).1, (hphys v hv).2⟩

end BankExtraction

/-! ### The literal packets and their isometric links -/

section Packets

open NativeDensity
open ShiftedJetAction (Grid)

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [Nontrivial G] [CompleteSpace G]

/-- The link `e^Z` of a represented connection as a real linear isometry (given that it preserves
the norm: unitary internal representation). -/
def expIso (Z : G →L[ℝ] G) (hZ : ∀ v, ‖exp Z v‖ = ‖v‖) : G ≃ₗᵢ[ℝ] G where
  toFun v := exp Z v
  invFun v := exp (-Z) v
  left_inv v := by
    change (exp (-Z) * exp Z) v = v
    rw [NativeDensity.exp_neg_mul_exp]; rfl
  right_inv v := by
    change (exp Z * exp (-Z)) v = v
    rw [NativeDensity.exp_mul_exp_neg]; rfl
  map_add' v w := map_add _ v w
  map_smul' c v := map_smul _ c v
  norm_map' := hZ

theorem norm_expIso_sub_le {Z : G →L[ℝ] G} (hZ : ∀ v, ‖exp Z v‖ = ‖v‖) (hZ1 : ‖Z‖ ≤ 1)
    (v : G) : ‖expIso Z hZ v - v‖ ≤ 2 * ‖Z‖ * ‖v‖ := by
  change ‖exp Z v - v‖ ≤ _
  have h := SeriesLogChart.norm_exp_sub_one_le hZ1
  have e : exp Z v - v = (exp Z - 1) v := by simp
  rw [e]
  exact ((exp Z - 1).le_opNorm v).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]

/-- **The literal curvature packet** `𝔽_h = (F^h_{μν})_{μ,ν}` (`eq:literal-finite-bosonic-packets`,
all ordered pairs). -/
def curvPacket (N : ℕ) [NeZero N] (y : Grid N → Field 𝔄 𝓗 𝓢) : Grid N → Fin 4 → Fin 4 → 𝔄 :=
  fun x μ ν => NativeScaling.fieldStrength (N : ℝ)⁻¹ (gauge y) x μ ν

/-- **The literal Higgs-gradient packet** `𝕂_h = (K^h_μ)_μ`. -/
def higgsPacket (D : Data 𝔄 𝓗 𝓢) (N : ℕ) [NeZero N] (y : Grid N → Field 𝔄 𝓗 𝓢) :
    Grid N → Fin 4 → 𝓗 :=
  fun x μ => higgsLink D (N : ℝ)⁻¹ y x μ

/-- The adjoint links `Ad(e^{hA_μ(x)})` acting componentwise on the curvature packet. -/
def adLinks (N : ℕ) [NeZero N] (y : Grid N → Field 𝔄 𝓗 𝓢)
    (hAd : ∀ x μ (X : 𝔄), ‖exp ((N : ℝ)⁻¹ • gauge y μ x) * X *
      exp (-((N : ℝ)⁻¹ • gauge y μ x))‖ = ‖X‖) :
    Fin 4 → Grid N → ((Fin 4 → Fin 4 → 𝔄) ≃ₗᵢ[ℝ] (Fin 4 → Fin 4 → 𝔄)) :=
  fun μ x => piIso (piIso (adIso ((N : ℝ)⁻¹ • gauge y μ x) (hAd x μ)))

/-- The Higgs links `ρ_H(e^{hA_μ(x)}) = e^{h ρ_H(A_μ(x))}` acting componentwise on the Higgs
packet. -/
def higgsLinks (D : Data 𝔄 𝓗 𝓢) (N : ℕ) [NeZero N] (y : Grid N → Field 𝔄 𝓗 𝓢)
    (hUH : ∀ x μ (v : 𝓗), ‖exp ((N : ℝ)⁻¹ • D.ρHL (gauge y μ x)) v‖ = ‖v‖) :
    Fin 4 → Grid N → ((Fin 4 → 𝓗) ≃ₗᵢ[ℝ] (Fin 4 → 𝓗)) :=
  fun μ x => piIso (expIso ((N : ℝ)⁻¹ • D.ρHL (gauge y μ x)) (hUH x μ))

end Packets

/-! ### The Wilson/Coulomb extraction chain -/

section Chain

open NativeDensity NativeBank
open ShiftedJetAction (Grid)
open NativeDiracConv (CoHyp qM ωM)
open NativeScaling (Mat)

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {rH : ℕ} [NeZero rH]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {E₀ : Type*} [NormedAddCommGroup E₀] [InnerProductSpace ℝ E₀]
variable {J : ℕ}

/-- The gauge field is pointwise small at mesh scale in the normalized gauge:
`h ‖A_μ(x)‖ ≤ c ‖A‖_{4,h}`. -/
theorem mesh_small (T₀ : 𝔄 →L[ℝ] E₀) {c₀ : ℝ} (hc0 : 0 ≤ c₀) (hc : ∀ X, ‖X‖ ≤ c₀ * ‖T₀ X‖)
    {N : ℕ} [NeZero N] (A : Fin 4 → Grid N → 𝔄) {ε : ℝ}
    (hs : ∀ μ, NativeCoulomb.g4 (fun x => T₀ (A μ x)) ≤ ε) (x : Grid N) (μ : Fin 4) :
    (N : ℝ)⁻¹ * ‖A μ x‖ ≤ c₀ * ε := by
  calc (N : ℝ)⁻¹ * ‖A μ x‖ ≤ (N : ℝ)⁻¹ * (c₀ * ‖T₀ (A μ x)‖) :=
        mul_le_mul_of_nonneg_left (hc _) (by positivity)
    _ = c₀ * ((N : ℝ)⁻¹ * ‖(fun x => T₀ (A μ x)) x‖) := by ring
    _ ≤ c₀ * ε := mul_le_mul_of_nonneg_left ((NativeCoulomb.le_g4 _ x).trans (hs μ)) hc0

theorem gridNorm_norm_le (T₀ : 𝔄 →L[ℝ] E₀) {c₀ : ℝ} (hc0 : 0 ≤ c₀) (hc : ∀ X, ‖X‖ ≤ c₀ * ‖T₀ X‖)
    {N : ℕ} [NeZero N] (A : Fin 4 → Grid N → 𝔄) {ε : ℝ}
    (hs : ∀ μ, NativeCoulomb.g4 (fun x => T₀ (A μ x)) ≤ ε) (μ : Fin 4) {K : ℝ} (hK : 0 ≤ K) :
    gridNorm (fun x => K * ‖A μ x‖) ≤ K * (c₀ * ε) := by
  rw [gridNorm_const_mul (fun x => ‖A μ x‖) hK, NativeWilsonCompactness.gridNorm_norm]
  refine mul_le_mul_of_nonneg_left ?_ hK
  refine (NativeCoulomb.gridNorm_le_g4 _).trans ?_
  refine (NativeCoulomb.g4_le_mul hc0 (u := A μ) (v := fun x => T₀ (A μ x))
    fun x => hc _).trans ?_
  exact mul_le_mul_of_nonneg_left (hs μ) hc0

set_option maxHeartbeats 3200000 in
-- six successive extractions
/-- **`thm:finite-Wilson-zero-defect`, the Wilson/Coulomb extraction chain** (unit-torus
rendering).  There is a cutoff-independent `ε_* > 0` such that for native records in **exact
discrete Coulomb gauge** `δ_h A_h = 0` with `‖T₀A_h‖_{4,h} ≤ ε_*` (the output of the normalization
clause `RootedCoulomb.rooted_coulomb_normalization` applied to the same records), under
* `(F1)`: coframes in one compact oriented chart with the logarithm margin `c_* ≤ 1/64`, and
  `R^0E_h`, `R^0D⁺E_h` precompact in `L²`;
* `(F3)`: unitary links (`Ad` on the curvature packet, `ρ_H` on the Higgs packet), bounded
  literal packets `𝔽_h`, `𝕂_h` and vanishing Wilson screens `eq:two-finite-Wilson-screens` (in the
  form of `thm:native-Wilson-compactness`);
* `(F4)` (banks): the cutoff banks stay in a compact physical parameter set,
after extraction the native hypotheses `(N1)–(N5)` hold: a `CoHyp` (strong `L²` coframes and first
differences, strong `L⁴` connections) on the same chart, convergent banks with a physical limit,
`R^0 𝔽_h → F` strongly in `L²` (`thm:native-Wilson-compactness`), **the ordinary connection first
differences converge strongly**, `R^0 D⁺_μ A_ν → G_{μν}`, with `F = G - Gᵀ + [A, A]`
(`thm:native-discrete-Coulomb`), and `R^0 𝕂_h → K` strongly in `L²`. -/
theorem wilson_coulomb_extraction (D : Data 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢)
    (T₀ : 𝔄 →L[ℝ] E₀) {c₀ : ℝ} (hc0 : 0 ≤ c₀) (hc : ∀ X, ‖X‖ ≤ c₀ * ‖T₀ X‖) :
    ∃ εstar > 0, ∀ (n : ℕ → ℕ) [∀ k, NeZero (n k)]
      (y : ∀ k, Grid (n k) → Field 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢)
      (θs : ℕ → Bank J (EuclideanSpace ℝ (Fin rH)) 𝓢), Tendsto n atTop atTop →
      -- the normalized gauge
      (∀ k, NativeCoulomb.codiffT T₀ (NativeYMBridge.gaugeArr (y k)) = 0) →
      (∀ k μ, NativeCoulomb.g4 (fun x => T₀ (gauge (y k) μ x)) ≤ εstar) →
      -- `(F1)`
      ∀ (Ke : Set M4), IsCompact Ke → (∀ M ∈ Ke, 0 < Matrix.det (show Mat from M)) →
      (∀ k x, coframeM (y k) x ∈ Ke) → ∀ cm : ℝ, cm ≤ 1 / 64 →
      (∀ k x μ, (n k : ℝ)⁻¹ * ‖ωM (y k) μ x‖ ≤ cm) →
      TotallyBounded (range fun k => pcLp (coframeM (y k))) →
      TotallyBounded (range fun k => pcLp (fun x lam => qM (y k) lam x)) →
      -- `(F3)`
      ∀ (hAd : ∀ k x μ (X : 𝔄), ‖exp ((n k : ℝ)⁻¹ • gauge (y k) μ x) * X *
          exp (-((n k : ℝ)⁻¹ • gauge (y k) μ x))‖ = ‖X‖)
        (hUH : ∀ k x μ (v : EuclideanSpace ℝ (Fin rH)),
          ‖exp ((n k : ℝ)⁻¹ • D.ρHL (gauge (y k) μ x)) v‖ = ‖v‖),
      (∃ M, ∀ k, gridNorm (curvPacket (n k) (y k)) ≤ M) →
      (∃ M, ∀ k, gridNorm (higgsPacket D (n k) (y k)) ≤ M) →
      (∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : Fin 4) (m : ℕ), 0 < m → (m : ℝ) / n k ≤ ρ →
        gridNorm (wilsonShiftR (adLinks (n k) (y k) (hAd k)) μ m (curvPacket (n k) (y k)) -
          curvPacket (n k) (y k)) ≤ ε) →
      (∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : Fin 4) (m : ℕ), 0 < m → (m : ℝ) / n k ≤ ρ →
        gridNorm (wilsonShiftR (higgsLinks D (n k) (y k) (hUH k)) μ m
          (higgsPacket D (n k) (y k)) - higgsPacket D (n k) (y k)) ≤ ε) →
      -- `(F4)`, banks
      ∀ (Kθ : Set (ℝ × ℝ × ℝ × ℝ × (Fin J → ℝ) ×
          (EuclideanSpace ℝ (Fin rH) →L[ℝ] Spin 𝓢))), IsCompact Kθ →
      (∀ k, bankVec (θs k) ∈ Kθ) → (∀ v ∈ Kθ, v.1 ≠ 0 ∧ ∀ j, 0 ≤ v.2.2.2.2.1 j) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ H : CoHyp (fun k => n (φ k)) (fun k => y (φ k)),
        H.Ke = Ke ∧ H.c = cm ∧
        ∃ θ : Bank J (EuclideanSpace ℝ (Fin rH)) 𝓢, BankConv (fun k => θs (φ k)) θ ∧
          θ.κ ≠ 0 ∧ (∀ j, 0 ≤ θ.w j) ∧
        ∃ F : Fin 4 → Fin 4 → 𝕋 → 𝔄, (∀ μ ν, LpTendsto volume 2 (fun k => pc (fun x =>
            NativeScaling.fieldStrength (n (φ k) : ℝ)⁻¹ (gauge (y (φ k))) x μ ν)) (F μ ν)) ∧
        ∃ G : Fin 4 → Fin 4 → 𝕋 → 𝔄, (∀ μ ν, LpTendsto volume 2
            (fun k => pc (NativeHiggs.DpV μ (gauge (y (φ k)) ν))) (G μ ν)) ∧
          (∀ μ ν, F μ ν =ᵐ[MeasureTheory.volume] NativeReconstructed.recCurv H.A₀ G μ ν) ∧
        ∃ K₀ : Fin 4 → 𝕋 → EuclideanSpace ℝ (Fin rH), ∀ μ, LpTendsto volume 2
          (fun k => pc (fun x => higgsLink D (n (φ k) : ℝ)⁻¹ (y (φ k)) x μ)) (K₀ μ) := by
  have : FiniteDimensional ℂ 𝔄 := Module.Finite.of_restrictScalars_finite ℝ ℂ 𝔄
  obtain ⟨ε₀, hε₀, hC⟩ := NativeCoulomb.native_discrete_Coulomb T₀ hc0 hc
  set εstar : ℝ := min ε₀ (1 / (128 * (c₀ + 1) * (‖D.ρHL‖ + 1))) with hεs
  have hεs0 : 0 < εstar := lt_min hε₀ (by positivity)
  have hεsε : εstar ≤ ε₀ := min_le_left _ _
  have hsmall : c₀ * εstar ≤ 1 / 128 / (‖D.ρHL‖ + 1) := by
    have h1 : εstar ≤ 1 / (128 * (c₀ + 1) * (‖D.ρHL‖ + 1)) := min_le_right _ _
    have h2 : c₀ * εstar ≤ c₀ * (1 / (128 * (c₀ + 1) * (‖D.ρHL‖ + 1))) :=
      mul_le_mul_of_nonneg_left h1 hc0
    refine h2.trans ?_
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [norm_nonneg D.ρHL]
  have hsm1 : c₀ * εstar ≤ 1 / 128 := by
    refine hsmall.trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg D.ρHL]
  have hsmρ : ‖D.ρHL‖ * (c₀ * εstar) ≤ 1 / 128 := by
    have := mul_le_mul_of_nonneg_left hsmall (norm_nonneg D.ρHL)
    refine this.trans ?_
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg D.ρHL]
  refine ⟨εstar, hεs0, fun n _ y θs hn hδ hs Ke hKe hpos hval cm hcm hmar hTBe hTBq hAd hUH
    hFb hKb hΩF hΩK Kθ hKθ hθK hphys => ?_⟩
  have hpt := fun k => mesh_small T₀ hc0 hc (N := n k) (fun μ x => gauge (y k) μ x) (hs k)
  -- the curvature packet is precompact
  have hTBF : TotallyBounded (range fun k => pcLp (curvPacket (n k) (y k))) := by
    refine native_wilson_vector_totallyBounded_real n hn (fun k => adLinks (n k) (y k) (hAd k))
      (fun k => curvPacket (n k) (y k)) hFb hΩF (fun k μ x => 6 * ‖gauge (y k) μ x‖)
      (fun k μ x => by positivity) (MA := 6 * (c₀ * εstar))
      (fun k μ => gridNorm_norm_le T₀ hc0 hc (N := n k) (fun μ x => gauge (y k) μ x) (hs k) μ
        (by norm_num)) (fun k μ x v => ?_)
    have hZ : ‖(n k : ℝ)⁻¹ • gauge (y k) μ x‖ ≤ 1 / 2 := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      linarith [hpt k x μ]
    have hZ' : ‖(n k : ℝ)⁻¹ • gauge (y k) μ x‖ = 6 * ‖gauge (y k) μ x‖ / n k / 6 := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]; ring
    have h1 : ∀ X : 𝔄, ‖adIso ((n k : ℝ)⁻¹ • gauge (y k) μ x) (hAd k x μ) X - X‖ ≤
        6 * ‖gauge (y k) μ x‖ / n k * ‖X‖ := fun X => by
      refine (norm_ad_sub_le hZ X).trans (le_of_eq ?_)
      rw [hZ']; ring
    exact norm_piIso_sub_le _ (by positivity) (fun w => norm_piIso_sub_le _ (by positivity) h1 w) v
  -- the Higgs packet is precompact
  have hTBK : TotallyBounded (range fun k => pcLp (higgsPacket D (n k) (y k))) := by
    refine native_wilson_vector_totallyBounded_real n hn (fun k => higgsLinks D (n k) (y k) (hUH k))
      (fun k => higgsPacket D (n k) (y k)) hKb hΩK
      (fun k μ x => (2 * ‖D.ρHL‖) * ‖gauge (y k) μ x‖) (fun k μ x => by positivity)
      (MA := (2 * ‖D.ρHL‖) * (c₀ * εstar))
      (fun k μ => gridNorm_norm_le T₀ hc0 hc (N := n k) (fun μ x => gauge (y k) μ x) (hs k) μ
        (by positivity)) (fun k μ x v => ?_)
    have hZ : ‖(n k : ℝ)⁻¹ • D.ρHL (gauge (y k) μ x)‖ ≤ ‖D.ρHL‖ * ((n k : ℝ)⁻¹ *
        ‖gauge (y k) μ x‖) := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      calc (n k : ℝ)⁻¹ * ‖D.ρHL (gauge (y k) μ x)‖ ≤ (n k : ℝ)⁻¹ * (‖D.ρHL‖ *
            ‖gauge (y k) μ x‖) := mul_le_mul_of_nonneg_left (D.ρHL.le_opNorm _) (by positivity)
        _ = _ := by ring
    have hZ1 : ‖(n k : ℝ)⁻¹ • D.ρHL (gauge (y k) μ x)‖ ≤ 1 := by
      refine hZ.trans ?_
      have := mul_le_mul_of_nonneg_left (hpt k x μ) (norm_nonneg D.ρHL)
      linarith
    have h1 : ∀ w : EuclideanSpace ℝ (Fin rH),
        ‖expIso ((n k : ℝ)⁻¹ • D.ρHL (gauge (y k) μ x)) (hUH k x μ) w - w‖ ≤
          (2 * ‖D.ρHL‖) * ‖gauge (y k) μ x‖ / n k * ‖w‖ := fun w => by
      refine (norm_expIso_sub_le _ hZ1 w).trans ?_
      have := mul_le_mul_of_nonneg_left hZ (by norm_num : (0 : ℝ) ≤ 2)
      calc 2 * ‖(n k : ℝ)⁻¹ • D.ρHL (gauge (y k) μ x)‖ * ‖w‖ ≤
            2 * (‖D.ρHL‖ * ((n k : ℝ)⁻¹ * ‖gauge (y k) μ x‖)) * ‖w‖ :=
            mul_le_mul_of_nonneg_right this (norm_nonneg _)
        _ = _ := by ring
    exact norm_piIso_sub_le _ (by positivity) h1 v
  -- successive extractions
  obtain ⟨φ₁, hφ₁, e₀, he⟩ := exists_subseq_lpTendsto (fun k => coframeM (y k)) hTBe
  obtain ⟨φ₂, hφ₂, q₀, hq⟩ := exists_subseq_lpTendsto
    (n := fun k => n (φ₁ k)) (fun k x lam => qM (y (φ₁ k)) lam x) (totallyBounded_comp hTBq φ₁)
  set ψ₂ : ℕ → ℕ := fun k => φ₁ (φ₂ k) with hψ₂
  obtain ⟨φ₃, hφ₃, Fp, hFp⟩ := exists_subseq_lpTendsto (n := fun k => n (ψ₂ k))
    (fun k => curvPacket (n (ψ₂ k)) (y (ψ₂ k))) (totallyBounded_comp hTBF ψ₂)
  set ψ₃ : ℕ → ℕ := fun k => ψ₂ (φ₃ k) with hψ₃
  obtain ⟨φ₄, hφ₄, Kp, hKp⟩ := exists_subseq_lpTendsto (n := fun k => n (ψ₃ k))
    (fun k => higgsPacket D (n (ψ₃ k)) (y (ψ₃ k))) (totallyBounded_comp hTBK ψ₃)
  set ψ₄ : ℕ → ℕ := fun k => ψ₃ (φ₄ k) with hψ₄
  have hψ₄m : StrictMono ψ₄ := ((hφ₁.comp hφ₂).comp hφ₃).comp hφ₄
  -- the literal curvature along `ψ₄`, in `curvLog` form
  have hF4 : ∀ μ ν, LpTendsto volume 2 (fun k => pc (fun x =>
      NativeScaling.fieldStrength (n (ψ₄ k) : ℝ)⁻¹ (gauge (y (ψ₄ k))) x μ ν))
      (fun z => Fp z μ ν) := fun μ ν =>
    ((hFp.comp_strictMono hφ₄).clm ((ContinuousLinearMap.proj ν).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => Fin 4 → 𝔄) μ))).congr
      (fun k => Eventually.of_forall fun z => rfl) (Eventually.of_forall fun z => rfl)
  have hch : ∀ k x μ ν, ((n k : ℝ))⁻¹ * LogBCH.normSum
      (NativeYMIdentification.slots (NativeYMBridge.gaugeArr (y k)) x μ ν) ≤ 1 / 32 :=
    fun k x μ ν => NativeCoulomb.chart_of_small T₀ hc0 hc (by linarith)
      (NativeYMBridge.gaugeArr (y k)) (hs k) x μ ν
  have hFcl : ∀ μ ν, LpTendsto volume 2 (fun k => pc (fun x =>
      NativeYMIdentification.curvLog (n (ψ₄ k)) (NativeYMBridge.gaugeArr (y (ψ₄ k))) x μ ν))
      (fun z => Fp z μ ν) := fun μ ν =>
    (hF4 μ ν).congr (fun k => Eventually.of_forall fun z => by
      simp only [pc]
      exact NativeYMBridge.fieldStrength_eq_curvLog (gauge (y (ψ₄ k))) _ μ ν
        (NativeYMBridge.gaugePlaquette_lt_of_chart (gauge (y (ψ₄ k))) _ μ ν (hch _ _ μ ν)))
      (Eventually.of_forall fun z => rfl)
  -- critical discrete Coulomb absorption
  obtain ⟨φ₅, hφ₅, A₀, G, hA, hG, -, -, hFG, -⟩ := hC (fun k => n (ψ₄ k))
    (hn.comp hψ₄m.tendsto_atTop) (fun k => NativeYMBridge.gaugeArr (y (ψ₄ k)))
    (fun μ ν z => Fp z μ ν) (fun k => hδ (ψ₄ k)) (fun k μ => (hs (ψ₄ k) μ).trans hεsε) hFcl
  set ψ₅ : ℕ → ℕ := fun k => ψ₄ (φ₅ k) with hψ₅
  -- the banks
  obtain ⟨φ₆, hφ₆, θ, hθ, hκ, hw⟩ := exists_bankConv (θs := fun k => θs (ψ₅ k)) hKθ
    (fun k => hθK (ψ₅ k)) hphys
  set φ : ℕ → ℕ := fun k => ψ₅ (φ₆ k) with hφ
  have hφm : StrictMono φ := (hψ₄m.comp hφ₅).comp hφ₆
  -- the remaining compositions
  have r1 : StrictMono (fun k => φ₂ (φ₃ (φ₄ (φ₅ (φ₆ k))))) :=
    (((hφ₂.comp hφ₃).comp hφ₄).comp hφ₅).comp hφ₆
  have r2 : StrictMono (fun k => φ₃ (φ₄ (φ₅ (φ₆ k)))) := ((hφ₃.comp hφ₄).comp hφ₅).comp hφ₆
  have r4 : StrictMono (fun k => φ₅ (φ₆ k)) := hφ₅.comp hφ₆
  let H : CoHyp (fun k => n (φ k)) (fun k => y (φ k)) :=
    { hn := hn.comp hφm.tendsto_atTop
      Ke := Ke
      hKe := hKe
      hKdet := fun M hM => (hpos M hM).ne'
      hval := fun k x => hval (φ k) x
      c := cm
      hmar := fun k x μ => hmar (φ k) x μ
      e₀ := e₀
      he := he.comp_strictMono r1
      p := fun lam z => q₀ z lam
      hp := fun lam => ((hq.comp_strictMono r2).clm (ContinuousLinearMap.proj lam)).congr
        (fun k => Eventually.of_forall fun z => rfl) (Eventually.of_forall fun z => rfl)
      A₀ := A₀
      hA := fun μ => ((hA μ).comp_strictMono hφ₆).congr
        (fun k => Eventually.of_forall fun z => rfl) (Eventually.of_forall fun z => rfl) }
  refine ⟨φ, hφm, H, rfl, rfl, θ, hθ, hκ, hw, fun μ ν z => Fp z μ ν,
    fun μ ν => (hF4 μ ν).comp_strictMono r4, G,
    fun μ ν => ((hG μ ν).comp_strictMono hφ₆).congr (fun k => Eventually.of_forall fun z => rfl)
      (Eventually.of_forall fun z => rfl), fun μ ν => ?_, fun μ z => Kp z μ, fun μ => ?_⟩
  · filter_upwards [hFG μ ν] with z hz
    simp only [NativeReconstructed.recCurv]
    exact hz
  · exact ((hKp.comp_strictMono r4).clm (ContinuousLinearMap.proj μ)).congr
      (fun k => Eventually.of_forall fun z => rfl) (Eventually.of_forall fun z => rfl)

end Chain

/-! ### Bosonic stress densities and the Euler argument -/

section Stress

open NativeDensity

variable {PF PK 𝓗 : Type*} [NormedAddCommGroup PF] [NormedSpace ℝ PF] [NormedAddCommGroup PK]
  [NormedSpace ℝ PK] [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗]

local instance fact_one_le_two_fw : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance fact_one_le_four_fw : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance holder221_fw : ENNReal.HolderTriple 2 2 1 :=
  ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩
local instance holder442_fw : ENNReal.HolderTriple 4 4 2 := TorusSobolev.holderTriple_four_four_two

/-- A quadratic density with chart coefficients: `Θ(e_k)[Y_k, Y_k] → Θ(e)[Y, Y]` in `L¹` when
`e_k → e` in `L²` in a compact chart, `Θ` is continuous on the chart and `Y_k → Y` in `L²`. -/
theorem lpTendsto_chart_quadratic {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {K : Set M4} (hK : IsCompact K) {f : ℕ → 𝕋 → M4} {e₀ : 𝕋 → M4}
    (hf : LpTendsto volume 2 f e₀) (hfK : ∀ k z, f k z ∈ K) {Θ : M4 → P →L[ℝ] P →L[ℝ] ℝ}
    (hΘ : ContinuousOn Θ K) {Y : ℕ → 𝕋 → P} {Y₀ : 𝕋 → P} (hY : LpTendsto volume 2 Y Y₀) :
    LpTendsto volume 1 (fun k z => Θ (f k z) (Y k z) (Y k z)) (fun z => Θ (e₀ z) (Y₀ z) (Y₀ z)) :=
  LpTendsto.bilin (p := 2) (q := 2) (r := 1) (ContinuousLinearMap.id ℝ (P →L[ℝ] ℝ))
    (NativeReconstructed.chart (p := 2) (by norm_num) hK hf hfK hΘ
      (ContinuousLinearMap.id ℝ (P →L[ℝ] P →L[ℝ] ℝ)) hY) hY

/-- The quartic potential `λ_k(|H_k|² - v_k²)²` with convergent coefficients converges in `L¹`. -/
theorem lpTendsto_potential_seq (h : 𝓗 →L[ℝ] 𝓗 →L[ℝ] ℝ) {lam v : ℕ → ℝ} {lam₀ v₀ : ℝ}
    (hlam : Tendsto lam atTop (𝓝 lam₀)) (hv : Tendsto v atTop (𝓝 v₀)) {H : ℕ → 𝕋 → 𝓗}
    {H₀ : 𝕋 → 𝓗} (hH : LpTendsto volume 4 H H₀) :
    LpTendsto volume 1 (fun k z => lam k * (h (H k z) (H k z) - v k ^ 2) ^ 2)
      (fun z => lam₀ * (h (H₀ z) (H₀ z) - v₀ ^ 2) ^ 2) := by
  have hq := LpTendsto.bilin (p := 4) (q := 4) (r := 2) h hH hH
  have hc := FirstVariationCalculus.LpTendsto.const_seq (μ := (volume : Measure 𝕋)) (p := 2)
    (X := 𝕋) ((hv.pow 2))
  have hr := hq.sub hc
  have hs := LpTendsto.bilin (p := 2) (q := 2) (r := 1) (ContinuousLinearMap.mul ℝ ℝ) hr hr
  have ht := FirstVariationCalculus.LpTendsto.smul_seq hlam hs
  refine ht.congr (fun k => Eventually.of_forall fun z => ?_) (Eventually.of_forall fun z => ?_)
  · simp only [Pi.sub_apply, smul_eq_mul, ContinuousLinearMap.mul_apply', sq]
  · simp only [Pi.sub_apply, smul_eq_mul, ContinuousLinearMap.mul_apply', sq]

end Stress

section Euler

open NativeDensity NativeAllSector
open ShiftedJetAction (Grid)
open NativeDiracLimit (DTest testRec)

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']

/-- **The Euler argument** (`thm:abstract-closure` form): if the finite first variations along
`𝓘_h v` converge to `L(v)` uniformly on every `C²` ball and tend to zero on the unit test family,
then `L ≡ 0` (homogeneity of the finite variation in the test). -/
theorem euler_of_limit {n : ℕ → ℕ} [∀ k, NeZero (n k)] {y : ∀ k, Grid (n k) → Field 𝔄 𝓗 𝓢}
    (Ds : ℕ → Data 𝔄 𝓗 𝓢) (κ : W' →L[ℝ] CoSpinor 𝓢) (L : DTest 𝔄 𝓗 𝓢 W' → ℝ)
    (hlim : ∀ M : NNReal, ∀ ε > 0, ∀ᶠ k in atTop, ∀ τ : DTest 𝔄 𝓗 𝓢 W', τ.norm ≤ M →
      |nativeVar (Ds k) (n k) (y k) (testRec κ (n k) (y k) τ) - L τ| ≤ ε)
    (hstat : ∀ ε > 0, ∀ᶠ k in atTop, ∀ τ : DTest 𝔄 𝓗 𝓢 W', τ.norm ≤ 1 →
      |nativeVar (Ds k) (n k) (y k) (testRec κ (n k) (y k) τ)| ≤ ε) (τ : DTest 𝔄 𝓗 𝓢 W') :
    L τ = 0 := by
  have hτ0 := τ.norm_nonneg
  set c : ℝ := τ.norm + 1 with hc'
  have hc0 : 0 < c := by positivity
  refine abs_eq_zero.1 (le_antisymm ?_ (abs_nonneg _))
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have h1' := hlim ⟨τ.norm, hτ0⟩ (ε / 2) (by positivity)
  have hst := hstat (ε / (2 * c)) (by positivity)
  obtain ⟨k, hk1, hk2⟩ := (h1'.and hst).exists
  have h1 := hk1 τ le_rfl
  have hτ1 : (dsmul c⁻¹ τ).norm ≤ 1 := by
    rw [dsmul_norm, abs_of_pos (inv_pos.2 hc0), inv_mul_le_iff₀ hc0]
    linarith
  have h2 := hk2 (dsmul c⁻¹ τ) hτ1
  have hrec : testRec κ (n k) (y k) τ = c • testRec κ (n k) (y k) (dsmul c⁻¹ τ) := by
    rw [testRec_dsmul, smul_smul, mul_inv_cancel₀ hc0.ne', one_smul]
  rw [hrec, nativeVar_smul] at h1
  have h3 : |c * nativeVar (Ds k) (n k) (y k) (testRec κ (n k) (y k) (dsmul c⁻¹ τ))| ≤ ε / 2 := by
    rw [abs_mul, abs_of_pos hc0]
    calc c * |nativeVar (Ds k) (n k) (y k) (testRec κ (n k) (y k) (dsmul c⁻¹ τ))|
        ≤ c * (ε / (2 * c)) := mul_le_mul_of_nonneg_left h2 hc0.le
      _ = ε / 2 := by field_simp
  have h4 := abs_sub_abs_le_abs_sub (L τ)
    (c * nativeVar (Ds k) (n k) (y k) (testRec κ (n k) (y k) (dsmul c⁻¹ τ)))
  rw [abs_sub_comm] at h4
  linarith

end Euler

/-! ### The criterion after normalization -/

section Criterion

open NativeDensity NativeBank NativeHiggsVar NativeDiracLimit NativeDiracConvergence
open ShiftedJetAction (Grid)
open NativeDiracConv (CoHyp qM ωM)
open NativeScaling (Mat)
open NativeSpinorGraph (κid spinGraph dualGraph coHypSubseq)

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {rH : ℕ} [NeZero rH]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {E E₀ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup E₀]
  [InnerProductSpace ℝ E₀]
variable {r r' : ℕ} [NeZero r] [NeZero r']
variable {J : ℕ}

local instance fact_one_le_two_fc : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

set_option maxHeartbeats 6400000 in
-- the composition of the extraction chain with the all-sector closure
/-- **`thm:finite-Wilson-zero-defect` after the same-record normalization** (unit-torus
rendering; Higgs fibre `ℝ^{r_H}`, co-spinors read with `κ = id`, fixed representation packet `D₀`,
gauge metrics `⟪T_j ·, T_j ·⟫` weighted by the banks).  There is a cutoff-independent `ε_* > 0`
such that, for native records in exact discrete Coulomb gauge with `‖T₀A_h‖_{4,h} ≤ ε_*` (the output
of `RootedCoulomb.rooted_coulomb_normalization` on the same records), under `(F1)`, `(F3)` (bounded
packets `𝔽_h, 𝕂_h, H_h`, unitary links, vanishing Wilson screens), `(F4)` (unitary spin links,
bounded positive internal-link spinor graphs, banks in a compact physical set) and the
reconstruction comparison estimates, after extraction:
* `eq:Wilson-strong-convergence`: `R^0 e_h → e`, `R^0 D⁺e_h → ∂e` (strong `H¹`), `R^0A_h → A`
  in `L⁴` with `R^0D⁺A_h → G = ∂A` in `L²`, `R^0𝔽_h → F = F_A`, `R^0H_h → H` in `L⁴` with
  `R^0D⁺H_h → K - ρ_H(A)H` and `R^0𝕂_h → K = D_AH` in `L²`, spinors weakly in `H¹`
  (`u₀ = (∂Ψ, ∂Ψ̄)`);
* `eq:native-all-sector-limit` with the cutoff banks, and the complete consistency error relative
  to the reconstructed fields tends to zero;
* **if the complete finite variation tends to zero on the unit test family, every limit satisfies
  the distributional Einstein–Standard-Model equations** (`D𝒮_θ(z)[v] = 0` for all tests);
* **the bosonic stress densities converge strongly in `L¹`**: for every quadratic stress
  density `Θ_F(e)[𝔽, 𝔽] + Θ_K(e)[𝕂, 𝕂] + Θ_V(e) V_{θ_h}(H)` with coefficients continuous on the
  chart (in particular the Yang–Mills and Higgs stress tensors), at the cutoff banks. -/
theorem finite_wilson_criterion (D₀ : Data 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢)
    (Tj : Fin J → 𝔄 →L[ℝ] E) (T₀ : 𝔄 →L[ℝ] E₀) {c₀ : ℝ} (hc0 : 0 ≤ c₀)
    (hc : ∀ X, ‖X‖ ≤ c₀ * ‖T₀ X‖)
    (Θ : 𝓢 ≃L[ℝ] EuclideanSpace ℝ (Fin r)) (Θ' : CoSpinor 𝓢 ≃L[ℝ] EuclideanSpace ℝ (Fin r')) :
    ∃ εstar > 0, ∀ (n : ℕ → ℕ) [∀ k, NeZero (n k)]
      (y : ∀ k, Grid (n k) → Field 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢)
      (θs : ℕ → Bank J (EuclideanSpace ℝ (Fin rH)) 𝓢), Tendsto n atTop atTop →
      -- the normalized gauge
      (∀ k, NativeCoulomb.codiffT T₀ (NativeYMBridge.gaugeArr (y k)) = 0) →
      (∀ k μ, NativeCoulomb.g4 (fun x => T₀ (gauge (y k) μ x)) ≤ εstar) →
      -- `(F1)`
      ∀ (Ke : Set M4), IsCompact Ke → (∀ M ∈ Ke, 0 < Matrix.det (show Mat from M)) →
      (∀ k x, coframeM (y k) x ∈ Ke) → ∀ cm : ℝ, cm ≤ 1 / 64 →
      (∀ k x μ, (n k : ℝ)⁻¹ * ‖ωM (y k) μ x‖ ≤ cm) →
      TotallyBounded (range fun k => pcLp (coframeM (y k))) →
      TotallyBounded (range fun k => pcLp (fun x lam => qM (y k) lam x)) →
      -- `(F3)`
      ∀ (hAd : ∀ k x μ (X : 𝔄), ‖exp ((n k : ℝ)⁻¹ • gauge (y k) μ x) * X *
          exp (-((n k : ℝ)⁻¹ • gauge (y k) μ x))‖ = ‖X‖)
        (hUH : ∀ k x μ (v : EuclideanSpace ℝ (Fin rH)),
          ‖exp ((n k : ℝ)⁻¹ • D₀.ρHL (gauge (y k) μ x)) v‖ = ‖v‖),
      (∃ M, ∀ k, gridNorm (curvPacket (n k) (y k)) ≤ M) →
      (∃ M, ∀ k, gridNorm (higgsPacket D₀ (n k) (y k)) ≤ M) →
      ∀ BH : ℝ, (∀ k, gridNorm (higgs (y k)) ≤ BH) →
      (∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : Fin 4) (m : ℕ), 0 < m → (m : ℝ) / n k ≤ ρ →
        gridNorm (wilsonShiftR (adLinks (n k) (y k) (hAd k)) μ m (curvPacket (n k) (y k)) -
          curvPacket (n k) (y k)) ≤ ε) →
      (∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : Fin 4) (m : ℕ), 0 < m → (m : ℝ) / n k ≤ ρ →
        gridNorm (wilsonShiftR (higgsLinks D₀ (n k) (y k) (hUH k)) μ m
          (higgsPacket D₀ (n k) (y k)) - higgsPacket D₀ (n k) (y k)) ≤ ε) →
      -- `(F4)`
      (∀ k x μ (v : 𝓢), ‖D₀.ρS (exp ((n k : ℝ)⁻¹ • gauge (y k) μ x)) v‖ = ‖v‖) →
      ∀ B : ℝ, (∀ k, gridNorm (psi (y k)) ≤ B) →
      (∀ k μ, gridNorm (fun x => spinGraph D₀ (n k : ℝ)⁻¹ (y k) x μ) ≤ B) →
      (∀ k, gridNorm (psiBar (y k)) ≤ B) →
      (∀ k μ, gridNorm (fun x => dualGraph D₀ (n k : ℝ)⁻¹ (y k) x μ) ≤ B) →
      ∀ (Kθ : Set (ℝ × ℝ × ℝ × ℝ × (Fin J → ℝ) ×
          (EuclideanSpace ℝ (Fin rH) →L[ℝ] Spin 𝓢))), IsCompact Kθ →
      (∀ k, bankVec (θs k) ∈ Kθ) → (∀ v ∈ Kθ, v.1 ≠ 0 ∧ ∀ j, 0 ≤ v.2.2.2.2.1 j) →
      -- the reconstructed fields
      ∀ (f : ℕ → 𝕋 → M4), (∀ k z, f k z ∈ Ke) →
      LpTendsto volume 2 (fun k => f k - pc (coframeM (y k))) 0 →
      ∀ (g : ℕ → Fin 4 → 𝕋 → M4),
      (∀ lam, LpTendsto volume 2 (fun k => g k lam - pc (qM (y k) lam)) 0) →
      ∀ (Ar : ℕ → Fin 4 → 𝕋 → 𝔄),
      (∀ μ, LpTendsto volume 4 (fun k => Ar k μ - pc (gauge (y k) μ)) 0) →
      ∀ (dAr : ℕ → Fin 4 → Fin 4 → 𝕋 → 𝔄),
      (∀ μ ν, LpTendsto volume 2
        (fun k => dAr k μ ν - pc (NativeHiggs.DpV μ (gauge (y k) ν))) 0) →
      ∀ (Hr : ℕ → 𝕋 → EuclideanSpace ℝ (Fin rH)),
      LpTendsto volume 4 (fun k => Hr k - pc (higgs (y k))) 0 →
      ∀ (dH : ℕ → Fin 4 → 𝕋 → EuclideanSpace ℝ (Fin rH)),
      (∀ μ, LpTendsto volume 2 (fun k => dH k μ - pc (NativeHiggs.DpV μ (higgs (y k)))) 0) →
      ∀ (Ψr : ℕ → 𝕋 → 𝓢), LpTendsto volume 2 (fun k => Ψr k - pc (psi (y k))) 0 →
      ∀ (χr : ℕ → 𝕋 → CoSpinor 𝓢), LpTendsto volume 2 (fun k => χr k - pc (psiBar (y k))) 0 →
      ∀ B4 : ℝ≥0∞, B4 ≠ ∞ → (∀ k, eLpNorm (Ψr k) 4 volume ≤ B4) →
      (∀ k, eLpNorm (χr k) 4 volume ≤ B4) →
      ∀ (ur : ℕ → 𝕋 → Dif 𝓢 (CoSpinor 𝓢)), (∀ k, MemLp (ur k) 2 volume) →
      ∀ Cr : ℝ, (∀ k, (eLpNorm (ur k) 2 volume).toReal ≤ Cr) →
      (∀ Gt : 𝕋 → Dif 𝓢 (CoSpinor 𝓢) →L[ℝ] ℝ, MemLp Gt 2 volume →
        Tendsto (fun k => ∫ z, Gt z (ur k z - pc (difs (y k) (psiBar (y k))) z)) atTop (𝓝 0)) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ H : CoHyp (fun k => n (φ k)) (fun k => y (φ k)),
      H.Ke = Ke ∧
      ∃ θ : Bank J (EuclideanSpace ℝ (Fin rH)) 𝓢, BankConv (fun k => θs (φ k)) θ ∧
      ∃ F : Fin 4 → Fin 4 → 𝕋 → 𝔄, ∃ G : Fin 4 → Fin 4 → 𝕋 → 𝔄,
      ∃ P : HiggsHyp (bankData D₀ Tj θ) (fun k => y (φ k)),
      ∃ S : SpinHyp (κid 𝓢) (fun k => y (φ k)), ∃ u₀ : 𝕋 → Dif 𝓢 (CoSpinor 𝓢),
      -- `eq:Wilson-strong-convergence`
      (∀ μ ν, LpTendsto volume 2 (fun k => pc (fun x =>
        NativeScaling.fieldStrength (n (φ k) : ℝ)⁻¹ (gauge (y (φ k))) x μ ν)) (F μ ν)) ∧
      (∀ μ ν, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (gauge (y (φ k)) ν)))
        (G μ ν)) ∧
      (∀ μ ν, F μ ν =ᵐ[MeasureTheory.volume] NativeReconstructed.recCurv H.A₀ G μ ν) ∧
      (∀ μ, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (higgs (y (φ k)))))
        (fun z => P.K₀ μ z - D₀.ρHL (H.A₀ μ z) (P.H₀ z))) ∧
      (∀ j, ∃ fj : Lp ℂ 2 (MeasureTheory.volume : Measure 𝕋),
        ((fj : 𝕋 → ℂ) =ᵐ[MeasureTheory.volume] fun z => ((Θ (S.Ψ₀ z) j : ℝ) : ℂ)) ∧
        TorusSobolev.MemH 1 fj ∧ ∀ μ, (TorusSobolev.weakDeriv μ fj : 𝕋 → ℂ)
          =ᵐ[MeasureTheory.volume] fun z => ((Θ ((u₀ z).1 μ) j : ℝ) : ℂ)) ∧
      -- `eq:native-all-sector-limit` with the cutoff banks
      (∀ M : NNReal, ∀ ε > 0, ∀ᶠ k in atTop,
        ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ M →
        |NativeAllSector.nativeVar (bankData D₀ Tj (θs (φ k))) (n (φ k)) (y (φ k))
            (testRec (κid 𝓢) (n (φ k)) (y (φ k)) τ) -
          NativeAllSector.contAllVar (bankData D₀ Tj θ) (κid 𝓢) (bankT Tj θ.w) H F P S u₀ τ|
            ≤ ε) ∧
      -- consistency relative to the reconstructed fields
      (∀ M : NNReal, ∀ ε > 0, ∀ᶠ k in atTop,
        ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ M →
        |NativeAllSector.nativeVar (bankData D₀ Tj (θs (φ k))) (n (φ k)) (y (φ k))
            (testRec (κid 𝓢) (n (φ k)) (y (φ k)) τ) -
          NativeReconstructed.recAllVar (bankData D₀ Tj θ) (κid 𝓢) (bankT Tj θ.w) (f (φ k))
            (g (φ k)) (Ar (φ k)) (dAr (φ k)) (Hr (φ k)) (dH (φ k)) (Ψr (φ k)) (χr (φ k))
            (ur (φ k)) τ| ≤ ε) ∧
      -- the Euler equations under native stationarity
      ((∀ ε > 0, ∀ᶠ k in atTop,
          ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ 1 →
          |NativeAllSector.nativeVar (bankData D₀ Tj (θs k)) (n k) (y k)
            (testRec (κid 𝓢) (n k) (y k) τ)| ≤ ε) →
        ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢),
          NativeAllSector.contAllVar (bankData D₀ Tj θ) (κid 𝓢) (bankT Tj θ.w) H F P S u₀ τ
            = 0) ∧
      -- the bosonic stress densities
      (∀ (ΘF : M4 → (Fin 4 → Fin 4 → 𝔄) →L[ℝ] (Fin 4 → Fin 4 → 𝔄) →L[ℝ] ℝ)
        (ΘK : M4 → (Fin 4 → EuclideanSpace ℝ (Fin rH)) →L[ℝ]
          (Fin 4 → EuclideanSpace ℝ (Fin rH)) →L[ℝ] ℝ) (ΘV : M4 → ℝ),
        ContinuousOn ΘF Ke → ContinuousOn ΘK Ke → ContinuousOn ΘV Ke →
        LpTendsto volume 1
          (fun k z => ΘF (pc (coframeM (y (φ k))) z) (pc (curvPacket (n (φ k)) (y (φ k))) z)
              (pc (curvPacket (n (φ k)) (y (φ k))) z) +
            ΘK (pc (coframeM (y (φ k))) z) (pc (higgsPacket D₀ (n (φ k)) (y (φ k))) z)
              (pc (higgsPacket D₀ (n (φ k)) (y (φ k))) z) +
            ΘV (pc (coframeM (y (φ k))) z) *
              potential (bankData D₀ Tj (θs (φ k))) (pc (higgs (y (φ k))) z))
          (fun z => ΘF (H.e₀ z) (fun μ ν => F μ ν z) (fun μ ν => F μ ν z) +
            ΘK (H.e₀ z) (fun μ => P.K₀ μ z) (fun μ => P.K₀ μ z) +
            ΘV (H.e₀ z) * potential (bankData D₀ Tj θ) (P.H₀ z))) := by
  obtain ⟨εstar, hεs, hA⟩ := wilson_coulomb_extraction (J := J) D₀ T₀ hc0 hc
  refine ⟨εstar, hεs, fun n _ y θs hn hδ hs Ke hKe hpos hval cm hcm hmar hTBe hTBq hAd hUH hFb
    hKb BH hHb hΩF hΩK hU B hΨ hKs hΨb hKbd Kθ hKθ hθK hphys f hfK hfc g hgc Ar hAc dAr hdAc Hr
    hHc dH hdHc Ψr hΨc χr hχc B4 hB4 hΨ4 hχ4 ur hur Cr hurb hurw => ?_⟩
  obtain ⟨φ, hφ, H, hHK, hHc', θ, hθ, hκ, hw, F, hF, G, hG, hFG, K₀, hK⟩ :=
    hA n y θs hn hδ hs Ke hKe hpos hval cm hcm hmar hTBe hTBq hAd hUH hFb hKb hΩF hΩK Kθ hKθ
      hθK hphys
  have hposH : ∀ M ∈ H.Ke, 0 < Matrix.det (show Mat from M) := by rw [hHK]; exact hpos
  have hcH : H.c ≤ 1 / 64 := by rw [hHc']; exact hcm
  have hfKH : ∀ k z, f (φ k) z ∈ H.Ke := by rw [hHK]; exact fun k => hfK (φ k)
  obtain ⟨ψ, hψ, P, S, u₀, hlim, -, hPK, hDH, hid1, -, htot, -, -, -, -⟩ :=
    NativeReconstructed.native_reconstructed_closure_bank D₀ Tj hθ hκ hw Θ Θ' H hposH hcH hF
      (fun k => hUH (φ k)) (BH := BH) (fun k => hHb (φ k)) hK (fun k => hU (φ k)) (B := B)
      (fun k => hΨ (φ k)) (fun k => hKs (φ k)) (fun k => hΨb (φ k)) (fun k => hKbd (φ k)) hG
      (fun k => f (φ k)) hfKH (hfc.comp_strictMono hφ) (fun k => g (φ k))
      (fun lam => (hgc lam).comp_strictMono hφ) (fun k => Ar (φ k))
      (fun μ => (hAc μ).comp_strictMono hφ) (fun k => dAr (φ k))
      (fun μ ν => (hdAc μ ν).comp_strictMono hφ) (fun k => Hr (φ k))
      (hHc.comp_strictMono hφ) (fun k => dH (φ k)) (fun μ => (hdHc μ).comp_strictMono hφ)
      (fun k => Ψr (φ k)) (hΨc.comp_strictMono hφ) (fun k => χr (φ k))
      (hχc.comp_strictMono hφ) hB4 (fun k => hΨ4 (φ k)) (fun k => hχ4 (φ k))
      (fun k => ur (φ k)) (fun k => hur (φ k)) (Cr := Cr) (fun k => hurb (φ k))
      (fun Gt hGt => (hurw Gt hGt).comp hφ.tendsto_atTop)
  have hφψ : StrictMono (fun k => φ (ψ k)) := hφ.comp hψ
  set H' := coHypSubseq H hψ with hH'
  have hθ' : BankConv (fun k => θs (φ (ψ k))) θ :=
    ⟨hθ.κ.comp hψ.tendsto_atTop, hθ.Λ.comp hψ.tendsto_atTop, hθ.lamH.comp hψ.tendsto_atTop,
      hθ.vH.comp hψ.tendsto_atTop, fun j => (hθ.w j).comp hψ.tendsto_atTop,
      hθ.Y.comp hψ.tendsto_atTop⟩
  refine ⟨fun k => φ (ψ k), hφψ, H', hHK, θ, hθ', F, G, P, S, u₀,
    fun μ ν => (hF μ ν).comp_strictMono hψ, fun μ ν => (hG μ ν).comp_strictMono hψ, hFG,
    by rw [hPK]; exact hDH, hid1, hlim, htot, fun hstat τ => ?_, ?_⟩
  · refine euler_of_limit (fun k => bankData D₀ Tj (θs (φ (ψ k)))) (κid 𝓢) _ (hlim) ?_ τ
    intro ε hε
    exact (hstat ε hε).filter_mono hφψ.tendsto_atTop |>.mono fun k hk => hk
  · intro ΘF ΘK ΘV hΘF hΘK hΘV
    have he : LpTendsto volume 2 (fun k => pc (coframeM (y (φ (ψ k))))) H.e₀ := H'.he
    have hfK' : ∀ k z, pc (coframeM (y (φ (ψ k)))) z ∈ Ke := fun k z => hval _ _
    have hFp : LpTendsto volume 2 (fun k => pc (curvPacket (n (φ (ψ k))) (y (φ (ψ k)))))
        (fun z μ ν => F μ ν z) :=
      LpTendsto.pi fun μ => LpTendsto.pi fun ν => (hF μ ν).comp_strictMono hψ
    have hKp : LpTendsto volume 2 (fun k => pc (higgsPacket D₀ (n (φ (ψ k))) (y (φ (ψ k)))))
        (fun z μ => P.K₀ μ z) :=
      LpTendsto.pi fun μ => by rw [hPK]; exact (hK μ).comp_strictMono hψ
    have T1 := lpTendsto_chart_quadratic hKe he hfK' hΘF hFp
    have T2 := lpTendsto_chart_quadratic hKe he hfK' hΘK hKp
    have hpot := lpTendsto_potential_seq (D₀.hermH) (hθ'.lamH) (hθ'.vH) P.hH
    have T3 := NativeReconstructed.chart (p := 1) ENNReal.one_ne_top hKe he hfK' hΘV
      (ContinuousLinearMap.mul ℝ ℝ) hpot
    refine ((T1.add T2).add T3).congr (fun k => Eventually.of_forall fun z => ?_)
      (Eventually.of_forall fun z => ?_)
    · simp only [Pi.add_apply, ContinuousLinearMap.mul_apply', potential, bankData]
    · simp only [Pi.add_apply, ContinuousLinearMap.mul_apply', potential, bankData]

end Criterion

end

end RenewalGeometry.FiniteWilsonZeroDefect
