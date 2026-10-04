/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.KolmogorovRieszTorus
import RenewalGeometry.Continuum.TorusPiecewiseConstantEmbedding

/-!
# Piecewise-constant reconstruction on `𝕋^d`: translations and discrete Kolmogorov–Riesz

This file proves `lem:native-discrete-KR` ("discrete translation compactness") of the
Einstein–SM action-closure manuscript (`papers/einstein_sm_action_closure`), in any dimension
`d` (the manuscript uses `d = 4`) and for values in any finite-dimensional real (or complex)
normed space.

## Setting and rendering

The manuscript works on a periodic comparison box of period `2π` with `h = 2π/n`, nodal norms
`‖u‖²_{2,h} = h⁴ Σ_x |u(x)|²` and the piecewise-constant reconstruction `R_h^0`.  We work on the
unit torus `𝕋^d = UnitAddTorus d` with grid `(ℤ/N)^d`, mesh `1/N`, cells
`Q_g = Π_i (g_i/N, (g_i+1)/N]` (`TorusPiecewiseConstant.cell1`), nodal norm
`gridNorm u = (N^{-d} Σ_g |u(g)|²)^{1/2}` and reconstruction `pc u (y) = u(index y)`.  The
dilation by `2π` maps one setting onto the other, multiplying all `L²` norms by the same
constant `(2π)^{d/2}`; precompactness and the vanishing of moduli are unaffected.

* `index1_add_int`, `index1_add_frac`: a translation by `m/N` shifts the cell index by `m`; a
  sub-cell translation by `θ/N`, `0 ≤ θ ≤ 1`, moves it by `0` or `1`.
* `lintegral_comp_index`: `∫ G(index y) dy = N^{-d} Σ_g G(g)`; hence `eLpNorm_pc`:
  `‖R^0 u‖_{L²} = ‖u‖_{2,h}` (the reconstruction is an isometry).
* `pc_add_coordPt_int`: `R^0 u(· + m e_μ / N) = R^0(T_{μ,m} u)`.
* `norm_transl_pcLp_sub_le`: **discrete-to-continuum translation modulus**: for `s ≥ 0`,
  `‖τ_{s e_μ} R^0 u - R^0 u‖_{L²} ≤ ‖T_{μ,⌊Ns⌋} u - u‖_{2,h} + ‖T_{μ,1} u - u‖_{2,h}`
  (integer displacement plus a sub-cell remainder, as in the manuscript's proof).
* `native_discrete_KR`: **`lem:native-discrete-KR`.**  If `u_k` is bounded in `L²_h` and
  `lim_{ρ↓0} limsup_{h↓0} max_μ max_{0 < m h ≤ ρ} ‖T_{μ,m}u_h - u_h‖_{2,h} = 0`, then
  `{R_h^0 u_h}` is totally bounded (precompact) in `L²(𝕋^d)`.
-/

open MeasureTheory Set Filter Topology UnitAddTorus
open scoped ENNReal

namespace RenewalGeometry.TorusPiecewiseConstantTranslation

open TorusPiecewiseConstant KolmogorovRieszTorus

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

variable {N : ℕ} [NeZero N]

/-! ### One-dimensional index arithmetic -/

theorem natCast_toNat_eq_intCast {z : ℤ} (hz : 0 ≤ z) : ((z.toNat : ℕ) : ZMod N) = (z : ZMod N) := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hz]

/-- If `r` represents `t` and `k < N r ≤ k + 1`, then the cell index of `t` is `k mod N`. -/
theorem index1_coe_eq {r : ℝ} {k : ℤ} (hk1 : (k : ℝ) < N * r) (hk2 : (N : ℝ) * r ≤ k + 1) :
    index1 N (r : UnitAddCircle) = (k : ZMod N) := by
  have hrep := coe_rep (r : UnitAddCircle)
  obtain ⟨z, hz⟩ : ∃ z : ℤ, (z : ℝ) = r - rep (r : UnitAddCircle) := by
    have h := (QuotientAddGroup.eq (s := AddSubgroup.zmultiples (1 : ℝ))).mp hrep
    obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp h
    exact ⟨z, by rw [zsmul_eq_mul, mul_one] at hz; linarith⟩
  have hceil : ⌈(N : ℝ) * rep (r : UnitAddCircle)⌉ = k + 1 - N * z := by
    rw [Int.ceil_eq_iff]
    have : (N : ℝ) * rep (r : UnitAddCircle) = N * r - N * z := by rw [hz]; ring
    rw [this]; push_cast; constructor <;> linarith
  have hpos : 1 ≤ ⌈(N : ℝ) * rep (r : UnitAddCircle)⌉ := by
    rw [Int.one_le_ceil_iff]
    have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    exact mul_pos hN (rep_mem _).1
  unfold index1
  rw [natCast_toNat_eq_intCast (by omega), hceil]
  push_cast
  rw [ZMod.natCast_self]
  ring

theorem index1_eq_ceil (t : UnitAddCircle) :
    index1 N t = ((⌈(N : ℝ) * rep t⌉ - 1 : ℤ) : ZMod N) := by
  conv_lhs => rw [← coe_rep t]
  apply index1_coe_eq
  · push_cast; have := Int.ceil_lt_add_one ((N : ℝ) * rep t); linarith
  · push_cast; have := Int.le_ceil ((N : ℝ) * rep t); linarith

/-- A translation by `m/N` shifts the cell index by `m`. -/
theorem index1_add_int (t : UnitAddCircle) (m : ℤ) :
    index1 N (t + (((m : ℝ) / N : ℝ) : UnitAddCircle)) = index1 N t + (m : ZMod N) := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [index1_eq_ceil t]
  conv_lhs => rw [← coe_rep t, ← AddCircle.coe_add]
  set r := rep t
  have h1 := Int.ceil_lt_add_one ((N : ℝ) * r)
  have h2 := Int.le_ceil ((N : ℝ) * r)
  rw [index1_coe_eq (k := ⌈(N : ℝ) * r⌉ - 1 + m)]
  · push_cast; ring
  · rw [mul_add, mul_div_cancel₀ _ hN]; push_cast; linarith
  · rw [mul_add, mul_div_cancel₀ _ hN]; push_cast; linarith

/-- A sub-cell translation by `θ/N`, `0 ≤ θ ≤ 1`, moves the cell index by `0` or `1`. -/
theorem index1_add_frac (t : UnitAddCircle) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    index1 N (t + ((θ / N : ℝ) : UnitAddCircle)) = index1 N t ∨
      index1 N (t + ((θ / N : ℝ) : UnitAddCircle)) = index1 N t + 1 := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have key : t + ((θ / N : ℝ) : UnitAddCircle) = ((rep t + θ / N : ℝ) : UnitAddCircle) := by
    rw [AddCircle.coe_add, coe_rep]
  rw [key, index1_eq_ceil t]
  set r := rep t
  have hc1 := Int.ceil_lt_add_one ((N : ℝ) * r)
  have hc2 := Int.le_ceil ((N : ℝ) * r)
  have hsum : (N : ℝ) * (r + θ / N) = N * r + θ := by rw [mul_add, mul_div_cancel₀ _ hN]
  rcases le_or_gt ((N : ℝ) * r + θ) (⌈(N : ℝ) * r⌉ : ℝ) with h | h
  · left
    rw [index1_coe_eq (k := ⌈(N : ℝ) * r⌉ - 1)]
    · rw [hsum]; push_cast; linarith
    · rw [hsum]; push_cast; linarith
  · right
    rw [index1_coe_eq (k := ⌈(N : ℝ) * r⌉)]
    · push_cast; ring
    · rw [hsum]; exact h
    · rw [hsum]; linarith


/-! ### Cells and the piecewise-constant reconstruction in dimension `d` -/

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The grid index of a point of `𝕋^d`. -/
def index (N : ℕ) (y : UnitAddTorus d) : d → ZMod N := fun i => index1 N (y i)

/-- The cell `Q_g = Π_i (g_i/N, (g_i+1)/N]`. -/
def cellD (g : d → ZMod N) : Set (UnitAddTorus d) := Set.pi univ fun i => cell1 N (g i)

theorem measurableSet_cellD (g : d → ZMod N) : MeasurableSet (cellD g) :=
  MeasurableSet.univ_pi fun i => measurableSet_cell1 (g i)

theorem mem_cellD_iff (g : d → ZMod N) (y : UnitAddTorus d) : y ∈ cellD g ↔ index N y = g := by
  constructor
  · intro hy
    funext i
    by_contra hne
    exact Set.disjoint_left.mp (cell1_disjoint hne) (mem_cell1_index1 (y i)) (hy i (mem_univ i))
  · rintro rfl
    exact fun i _ => mem_cell1_index1 (y i)

theorem volume_cellD (g : d → ZMod N) :
    volume (cellD g) = ENNReal.ofReal (1 / N) ^ Fintype.card d := by
  rw [cellD]
  change (Measure.pi fun _ => (volume : Measure UnitAddCircle)) _ = _
  rw [Measure.pi_pi]
  simp [volume_cell1, Finset.prod_const]

/-- The piecewise-constant reconstruction `R^0 u (y) = u(index y)`. -/
def pc {E : Type*} (u : (d → ZMod N) → E) : UnitAddTorus d → E := fun y => u (index N y)

theorem pc_eq_sum_indicator {E : Type*} [AddCommMonoid E] (u : (d → ZMod N) → E) :
    pc u = ∑ g, (cellD g).indicator (fun _ => u g) := by
  funext y
  rw [Finset.sum_apply, Finset.sum_eq_single (index N y)]
  · rw [indicator_of_mem ((mem_cellD_iff _ y).2 rfl)]; rfl
  · intro g _ hg
    exact indicator_of_notMem (fun h => hg ((mem_cellD_iff g y).1 h).symm) _
  · simp

/-- `∫ G(index y) dy = N^{-d} Σ_g G(g)`. -/
theorem lintegral_comp_index (G : (d → ZMod N) → ℝ≥0∞) :
    ∫⁻ y, G (index N y) = ENNReal.ofReal (1 / N) ^ Fintype.card d * ∑ g, G g := by
  calc ∫⁻ y, G (index N y) = ∫⁻ y, ∑ g, (cellD g).indicator (fun _ => G g) y := by
        refine lintegral_congr fun y => ?_
        rw [← Finset.sum_apply, ← pc_eq_sum_indicator]; rfl
    _ = ∑ g, ∫⁻ y, (cellD g).indicator (fun _ => G g) y :=
        lintegral_finsetSum _ fun g _ => measurable_const.indicator (measurableSet_cellD g)
    _ = ∑ g, G g * volume (cellD g) := by
        simp_rw [lintegral_indicator_const (measurableSet_cellD _)]
    _ = _ := by
        simp_rw [volume_cellD]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun g _ => mul_comm _ _

variable {E : Type*} [NormedAddCommGroup E]

theorem stronglyMeasurable_pc (u : (d → ZMod N) → E) : StronglyMeasurable (pc u) := by
  rw [pc_eq_sum_indicator]
  exact Finset.stronglyMeasurable_sum _ fun g _ =>
    stronglyMeasurable_const.indicator (measurableSet_cellD g)

/-- The nodal `L²` norm `‖u‖_{2,h} = (N^{-d} Σ_g |u(g)|²)^{1/2}` (mesh `h = 1/N`). -/
def gridNorm (u : (d → ZMod N) → E) : ℝ :=
  Real.sqrt ((1 / (N : ℝ)) ^ Fintype.card d * ∑ g, ‖u g‖ ^ 2)

theorem gridNorm_nonneg (u : (d → ZMod N) → E) : 0 ≤ gridNorm u := Real.sqrt_nonneg _

/-- The reconstruction is an isometry: `‖R^0 u‖_{L²} = ‖u‖_{2,h}`. -/
theorem eLpNorm_pc (u : (d → ZMod N) → E) :
    eLpNorm (pc u) 2 (volume : Measure (UnitAddTorus d)) = ENNReal.ofReal (gridNorm u) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  have h := lintegral_comp_index (d := d) (N := N) fun g => ‖u g‖ₑ ^ (2 : ℝ)
  simp only [ENNReal.toReal_ofNat]
  change (∫⁻ y, ‖u (index N y)‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) = _
  rw [h, gridNorm, Real.sqrt_eq_rpow]
  have hN : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  have hS : ∀ g, ‖u g‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖u g‖ ^ 2) := by
    intro g
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
    norm_num
  simp_rw [hS]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun g _ => by positivity), ← ENNReal.ofReal_pow hN,
    ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]

theorem memLp_pc (u : (d → ZMod N) → E) : MemLp (pc u) 2 (volume : Measure (UnitAddTorus d)) :=
  ⟨(stronglyMeasurable_pc u).aestronglyMeasurable, by rw [eLpNorm_pc]; exact ENNReal.ofReal_lt_top⟩

/-- The reconstruction `R^0 u` as an element of `L²(𝕋^d; E)`. -/
def pcLp (u : (d → ZMod N) → E) : Lp E 2 (volume : Measure (UnitAddTorus d)) :=
  (memLp_pc u).toLp _

theorem norm_pcLp (u : (d → ZMod N) → E) : ‖pcLp u‖ = gridNorm u := by
  rw [pcLp, Lp.norm_toLp, eLpNorm_pc, ENNReal.toReal_ofReal (gridNorm_nonneg u)]

theorem pc_sub (u v : (d → ZMod N) → E) : pc (u - v) = pc u - pc v := rfl

/-! ### Grid shifts and translations -/

/-- The grid shift `T_{μ,m} u (g) = u(g + m e_μ)`. -/
def shift (μ : d) (m : ℤ) (u : (d → ZMod N) → E) : (d → ZMod N) → E :=
  fun g => u (g + Pi.single μ (m : ZMod N))

theorem shift_zero (μ : d) (u : (d → ZMod N) → E) : shift μ 0 u = u := by
  funext g; simp [shift]

theorem coordPt_apply_self (μ : d) (s : ℝ) : coordPt μ s μ = (s : UnitAddCircle) := by
  simp [coordPt]

theorem coordPt_apply_ne {μ i : d} (h : i ≠ μ) (s : ℝ) : coordPt μ s i = 0 := by
  simp [coordPt, Pi.single_eq_of_ne h]

theorem index_add_coordPt_int (y : UnitAddTorus d) (μ : d) (m : ℤ) :
    index N (y + coordPt μ ((m : ℝ) / N)) = index N y + Pi.single μ (m : ZMod N) := by
  funext i
  by_cases h : i = μ
  · subst h
    simp only [index, Pi.add_apply, coordPt_apply_self, Pi.single_eq_same]
    exact index1_add_int (y i) m
  · simp [index, coordPt_apply_ne h, Pi.single_eq_of_ne h]

/-- `R^0 u(· + m e_μ/N) = R^0(T_{μ,m} u)`. -/
theorem pc_add_coordPt_int (u : (d → ZMod N) → E) (y : UnitAddTorus d) (μ : d) (m : ℤ) :
    pc u (y + coordPt μ ((m : ℝ) / N)) = pc (shift μ m u) y := by
  simp only [pc, shift, index_add_coordPt_int]

/-- A sub-cell translation changes `R^0 u` at most by `R^0 |T_{μ,1}u - u|`. -/
theorem norm_pc_add_coordPt_frac_sub_le (u : (d → ZMod N) → E) (y : UnitAddTorus d) (μ : d)
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    ‖pc u (y + coordPt μ (θ / N)) - pc u y‖ ≤ ‖pc (shift μ 1 u - u) y‖ := by
  rcases index1_add_frac (N := N) (y μ) h0 h1 with h | h
  · have : index N (y + coordPt μ (θ / N)) = index N y := by
      funext i
      by_cases hi : i = μ
      · subst hi; simpa [index, coordPt_apply_self] using h
      · simp [index, coordPt_apply_ne hi]
    simp only [pc, this, sub_self, norm_zero]
    exact norm_nonneg _
  · have : index N (y + coordPt μ (θ / N)) = index N y + Pi.single μ ((1 : ℤ) : ZMod N) := by
      funext i
      by_cases hi : i = μ
      · subst hi; simpa [index, coordPt_apply_self] using h
      · simp [index, coordPt_apply_ne hi, Pi.single_eq_of_ne hi]
    simp only [pc, this, shift, Pi.sub_apply]
    exact le_rfl


theorem coordPt_add (μ : d) (a b : ℝ) : coordPt μ a + coordPt μ b = coordPt μ (a + b) := by
  simp only [coordPt, AddCircle.coe_add, Pi.single_add]

theorem norm_transl_pcLp_sub_eq (u : (d → ZMod N) → E) (z : UnitAddTorus d) :
    ‖transl z (pcLp u) - pcLp u‖ =
      (eLpNorm (fun y => pc u (y + z) - pc u y) 2 (volume : Measure (UnitAddTorus d))).toReal := by
  rw [Lp.norm_def]
  congr 1
  apply eLpNorm_congr_ae
  have hqmp := (measurePreserving_add_right (volume : Measure (UnitAddTorus d)) z).quasiMeasurePreserving
  have h1 : (fun y => pcLp u (y + z)) =ᵐ[volume] fun y => pc u (y + z) :=
    hqmp.ae_eq_comp (memLp_pc u).coeFn_toLp
  filter_upwards [Lp.coeFn_sub (transl z (pcLp u)) (pcLp u), coeFn_transl z (pcLp u), h1,
    (memLp_pc u).coeFn_toLp] with y hs ht h1 h2
  rw [hs, Pi.sub_apply, ht, h1]
  exact congrArg _ h2

/-- **Discrete-to-continuum translation modulus.**  For `s ≥ 0`,
`‖τ_{s e_μ} R^0 u - R^0 u‖ ≤ ‖T_{μ,⌊Ns⌋} u - u‖_{2,h} + ‖T_{μ,1} u - u‖_{2,h}`. -/
theorem norm_transl_pcLp_sub_le (u : (d → ZMod N) → E) (μ : d) {s : ℝ} (hs : 0 ≤ s) :
    ‖transl (coordPt μ s) (pcLp u) - pcLp u‖ ≤
      gridNorm (shift μ (⌊(N : ℝ) * s⌋₊ : ℤ) u - u) + gridNorm (shift μ 1 u - u) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set m : ℕ := ⌊(N : ℝ) * s⌋₊ with hm
  set θ : ℝ := (N : ℝ) * s - m with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; linarith [Nat.floor_le (mul_nonneg hN.le hs)]
  have hθ1 : θ ≤ 1 := by rw [hθ]; linarith [Nat.lt_floor_add_one ((N : ℝ) * s)]
  have hsplit : coordPt μ s = coordPt μ (θ / N) + coordPt μ (((m : ℤ) : ℝ) / N) := by
    rw [coordPt_add]; congr 1; rw [hθ]; push_cast; field_simp; ring
  rw [norm_transl_pcLp_sub_eq, hsplit]
  have hmeas : ∀ (w : (d → ZMod N) → E) (c : UnitAddTorus d),
      AEStronglyMeasurable (fun y => pc w (y + c)) (volume : Measure (UnitAddTorus d)) :=
    fun w c => ((stronglyMeasurable_pc w).comp_measurable (measurable_add_const c)).aestronglyMeasurable
  have hpt : (fun y => pc u (y + (coordPt μ (θ / N) + coordPt μ (((m : ℤ) : ℝ) / N))) - pc u y) =
      (fun y => pc (shift μ (m : ℤ) u - u) (y + coordPt μ (θ / N))) +
        fun y => pc u (y + coordPt μ (θ / N)) - pc u y := by
    funext y
    simp only [Pi.add_apply, pc_sub, Pi.sub_apply, ← add_assoc, pc_add_coordPt_int]
    abel
  rw [hpt]
  have h1 : eLpNorm (fun y => pc (shift μ (m : ℤ) u - u) (y + coordPt μ (θ / N))) 2
      (volume : Measure (UnitAddTorus d)) = ENNReal.ofReal (gridNorm (shift μ (m : ℤ) u - u)) := by
    rw [← eLpNorm_pc]
    exact eLpNorm_comp_measurePreserving (stronglyMeasurable_pc _).aestronglyMeasurable
      (measurePreserving_add_right _ _)
  have h2 : eLpNorm (fun y => pc u (y + coordPt μ (θ / N)) - pc u y) 2
      (volume : Measure (UnitAddTorus d)) ≤ ENNReal.ofReal (gridNorm (shift μ 1 u - u)) := by
    rw [← eLpNorm_pc]
    exact eLpNorm_mono fun y => norm_pc_add_coordPt_frac_sub_le u y μ hθ0 hθ1
  have h3 : eLpNorm ((fun y => pc (shift μ (m : ℤ) u - u) (y + coordPt μ (θ / N))) +
        fun y => pc u (y + coordPt μ (θ / N)) - pc u y) 2 (volume : Measure (UnitAddTorus d)) ≤
      eLpNorm (fun y => pc (shift μ (m : ℤ) u - u) (y + coordPt μ (θ / N))) 2
          (volume : Measure (UnitAddTorus d)) +
        eLpNorm (fun y => pc u (y + coordPt μ (θ / N)) - pc u y) 2
          (volume : Measure (UnitAddTorus d)) :=
    eLpNorm_add_le (hmeas _ _)
      ((hmeas u (coordPt μ (θ / N))).sub (stronglyMeasurable_pc u).aestronglyMeasurable)
      (by norm_num)
  rw [h1] at h3
  have h4 := h3.trans (add_le_add_right h2 _)
  rw [← ENNReal.ofReal_add (gridNorm_nonneg _) (gridNorm_nonneg _)] at h4
  exact ENNReal.toReal_le_of_le_ofReal (add_nonneg (gridNorm_nonneg _) (gridNorm_nonneg _)) h4

theorem gridNorm_zero : gridNorm (0 : (d → ZMod N) → E) = 0 := by
  simp [gridNorm]

/-! ### `lem:native-discrete-KR` -/

/-- **`lem:native-discrete-KR` (discrete translation compactness).**  Let `N_k → ∞` (mesh
`h_k = 1/N_k → 0`) and let `u_k` be grid functions on `(ℤ/N_k)^d` with values in a
finite-dimensional real (or complex) normed space, uniformly bounded in `L²_h`, such that
`lim_{ρ↓0} limsup_{k} max_μ max_{0 < m h_k ≤ ρ} ‖T_{μ,m}u_k - u_k‖_{2,h} = 0` (in the form: for
every `ε > 0` there is `ρ > 0` such that eventually all these shifts are at most `ε`).  Then the
piecewise-constant reconstructions `R^0 u_k` form a totally bounded (precompact) family in
`L²(𝕋^d)`. -/
theorem native_discrete_KR [NormedSpace ℝ E] [FiniteDimensional ℝ E] (n : ℕ → ℕ)
    [∀ k, NeZero (n k)] (hn : Tendsto n atTop atTop) (u : ∀ k, (d → ZMod (n k)) → E)
    (hbdd : ∃ M, ∀ k, gridNorm (u k) ≤ M)
    (hmod : ∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : d) (m : ℕ), 0 < m →
      (m : ℝ) / n k ≤ ρ → gridNorm (shift μ (m : ℤ) (u k) - u k) ≤ ε) :
    TotallyBounded (range fun k => pcLp (u k)) := by
  obtain ⟨M, hM⟩ := hbdd
  refine kolmogorovRiesz_torus_vector_cofinite _ ⟨M, fun k => (norm_pcLp _).trans_le (hM k)⟩ ?_
  intro ε hε
  obtain ⟨ρ, hρ, hev⟩ := hmod (ε / 2) (by positivity)
  have hev2 : ∀ᶠ k in atTop, ⌈1 / ρ⌉₊ ≤ n k := hn.eventually_ge_atTop _
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hev.and hev2)
  refine ⟨ρ, hρ, Set.Iio K, Set.finite_Iio K, fun k hk μ s hs => ?_⟩
  obtain ⟨h1, h2⟩ := hK k (not_lt.1 hk)
  have hN : (0 : ℝ) < n k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (n k))
  refine (norm_transl_pcLp_sub_le (u k) μ hs.1).trans ?_
  have hb1 : gridNorm (shift μ ((1 : ℕ) : ℤ) (u k) - u k) ≤ ε / 2 := by
    refine h1 μ 1 one_pos ?_
    have : 1 / ρ ≤ (n k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast h2)
    rw [Nat.cast_one, div_le_iff₀ hN]
    rw [div_le_iff₀ hρ] at this
    linarith
  have hb2 : gridNorm (shift μ (⌊(n k : ℝ) * s⌋₊ : ℤ) (u k) - u k) ≤ ε / 2 := by
    rcases Nat.eq_zero_or_pos ⌊(n k : ℝ) * s⌋₊ with h0 | hpos
    · rw [h0, Nat.cast_zero, shift_zero, sub_self, gridNorm_zero]; positivity
    · refine h1 μ _ hpos ?_
      rw [div_le_iff₀ hN]
      have := Nat.floor_le (mul_nonneg hN.le hs.1)
      nlinarith [hs.2]
  simp only [Nat.cast_one] at hb1
  linarith


/-! ### Calculus of the nodal norm -/

theorem pcLp_add (u v : (d → ZMod N) → E) : pcLp (u + v) = pcLp u + pcLp v :=
  (memLp_pc u).toLp_add (memLp_pc v)

theorem gridNorm_add_le (u v : (d → ZMod N) → E) : gridNorm (u + v) ≤ gridNorm u + gridNorm v := by
  rw [← norm_pcLp, ← norm_pcLp, ← norm_pcLp, pcLp_add]
  exact norm_add_le _ _

theorem gridNorm_sum_le {J : Type*} (s : Finset J) (u : J → (d → ZMod N) → E) :
    gridNorm (∑ j ∈ s, u j) ≤ ∑ j ∈ s, gridNorm (u j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [gridNorm_zero]
  | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      exact (gridNorm_add_le _ _).trans (add_le_add le_rfl ih)

theorem gridNorm_mono {F : Type*} [NormedAddCommGroup F] {u : (d → ZMod N) → E}
    {v : (d → ZMod N) → F} (h : ∀ x, ‖u x‖ ≤ ‖v x‖) : gridNorm u ≤ gridNorm v := by
  unfold gridNorm
  refine Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => ?_)
    (by positivity))
  exact pow_le_pow_left₀ (norm_nonneg _) (h x) 2

theorem gridNorm_comp_add (u : (d → ZMod N) → E) (c : d → ZMod N) :
    gridNorm (fun x => u (x + c)) = gridNorm u := by
  unfold gridNorm
  congr 2
  exact Equiv.sum_comp (Equiv.addRight c) (fun x => ‖u x‖ ^ 2)

theorem gridNorm_shift_sub_comm (μ : d) (m : ℤ) (u : (d → ZMod N) → E) :
    gridNorm (shift μ m u) = gridNorm u :=
  gridNorm_comp_add u _

theorem gridNorm_const_mul (a : (d → ZMod N) → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    gridNorm (fun x => c * a x) = c * gridNorm a := by
  unfold gridNorm
  have : ∑ x, ‖c * a x‖ ^ 2 = c ^ 2 * ∑ x, ‖a x‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [norm_mul, mul_pow, Real.norm_of_nonneg hc]
  rw [this, mul_left_comm, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-! ### Non-vacuity -/

/-- Non-vacuity of `native_discrete_KR`: the constant grid functions `u_k ≡ 1` on
`(ℤ/(k+1))^d` satisfy its hypotheses. -/
example : TotallyBounded (range fun k : ℕ =>
    pcLp (d := d) (N := k + 1) (fun _ => (1 : ℂ))) := by
  refine native_discrete_KR (fun k => k + 1) (tendsto_add_atTop_nat 1)
    (fun k => fun _ => (1 : ℂ)) ⟨1, fun k => ?_⟩ fun ε hε => ⟨1, one_pos, ?_⟩
  · unfold gridNorm
    simp only [norm_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [Fintype.card_fun, ZMod.card]
    push_cast
    rw [← mul_pow, one_div, inv_mul_cancel₀ (by positivity), one_pow, Real.sqrt_one]
  · refine Eventually.of_forall fun k μ m _ _ => ?_
    have : shift μ (m : ℤ) (fun _ : d → ZMod (k + 1) => (1 : ℂ)) - (fun _ => 1) = 0 := by
      funext x; simp [shift]
    rw [this, gridNorm_zero]
    exact hε.le

end

end RenewalGeometry.TorusPiecewiseConstantTranslation
