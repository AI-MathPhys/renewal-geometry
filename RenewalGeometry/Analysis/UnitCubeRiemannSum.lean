/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Riemann sums of continuous functions on the unit cube

For a continuous `g : (Fin d → ℝ) → ℝ`, the left-endpoint Riemann sums on the uniform grid
of mesh `1/M` converge to the integral over the unit cube:

`(1/M)^d Σ_{k ∈ {0,…,M-1}^d} g(k/M) → ∫_{[0,1]^d} g` as `M → ∞` (`tendsto_riemannSum`).

The proof decomposes `[0,1)^d` into the half-open cells `Π_i [k_i/M, (k_i+1)/M)`
(`cell`, `iUnion_cell`, `pairwise_disjoint_cell`) and uses uniform continuity of `g` on the
closed cube.  Used for the Dirichlet-form limit of the coframe renewal packet
(paper `predictive_spectral_geometry`, `eq:supp-general-form-limit`).
-/

open MeasureTheory Set Filter Topology Finset

namespace RenewalGeometry.UnitCubeRiemannSum

variable {d : ℕ}

/-- The grid point `k / M`. -/
noncomputable def gridPoint (M : ℕ) (k : Fin d → Fin M) : Fin d → ℝ := fun i => (k i : ℝ) / M

/-- The half-open cell `Π_i [k_i/M, (k_i+1)/M)`. -/
def cell (M : ℕ) (k : Fin d → Fin M) : Set (Fin d → ℝ) :=
  pi univ fun i => Ico ((k i : ℝ) / M) (((k i : ℝ) + 1) / M)

theorem measurableSet_cell (M : ℕ) (k : Fin d → Fin M) : MeasurableSet (cell M k) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

theorem gridPoint_mem_Icc {M : ℕ} (hM : 0 < M) (k : Fin d → Fin M) :
    gridPoint M k ∈ Icc (0 : Fin d → ℝ) 1 := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  refine ⟨fun i => ?_, fun i => ?_⟩
  · exact div_nonneg (Nat.cast_nonneg _) hM'.le
  · show (k i : ℝ) / M ≤ 1
    rw [div_le_one hM']
    exact_mod_cast (k i).isLt.le

theorem cell_subset_Icc {M : ℕ} (hM : 0 < M) (k : Fin d → Fin M) :
    cell M k ⊆ Icc (0 : Fin d → ℝ) 1 := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  intro x hx
  refine ⟨fun i => ?_, fun i => ?_⟩
  · exact (div_nonneg (Nat.cast_nonneg _) hM'.le).trans (hx i (mem_univ i)).1
  · show x i ≤ 1
    refine (hx i (mem_univ i)).2.le.trans ?_
    rw [div_le_one hM']
    have : (k i : ℝ) + 1 ≤ M := by exact_mod_cast (k i).isLt
    exact this

theorem cell_subset_pi_Ico {M : ℕ} (hM : 0 < M) (k : Fin d → Fin M) :
    cell M k ⊆ pi univ fun _ => Ico (0 : ℝ) 1 := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  intro x hx i _
  refine ⟨(div_nonneg (Nat.cast_nonneg _) hM'.le).trans (hx i (mem_univ i)).1, ?_⟩
  refine (hx i (mem_univ i)).2.trans_le ?_
  rw [div_le_one hM']
  exact_mod_cast (k i).isLt

/-- The cells cover the half-open cube. -/
theorem iUnion_cell {M : ℕ} (hM : 0 < M) :
    (⋃ k : Fin d → Fin M, cell M k) = pi univ fun _ => Ico (0 : ℝ) 1 := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  ext x
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, hx⟩
    exact cell_subset_pi_Ico hM k hx
  · intro hx
    have hfl : ∀ i, ⌊(M : ℝ) * x i⌋₊ < M := by
      intro i
      rw [Nat.floor_lt (mul_nonneg hM'.le (hx i (mem_univ i)).1)]
      have := (hx i (mem_univ i)).2
      calc (M : ℝ) * x i < M * 1 := by gcongr
        _ = M := mul_one _
    refine mem_iUnion.mpr ⟨fun i => ⟨⌊(M : ℝ) * x i⌋₊, hfl i⟩, fun i _ => ?_⟩
    simp only
    constructor
    · rw [div_le_iff₀ hM', mul_comm (x i) (M : ℝ)]
      exact Nat.floor_le (mul_nonneg hM'.le (hx i (mem_univ i)).1)
    · rw [lt_div_iff₀ hM', mul_comm (x i) (M : ℝ)]
      exact Nat.lt_floor_add_one _

/-- Distinct cells are disjoint. -/
theorem pairwise_disjoint_cell {M : ℕ} (hM : 0 < M) :
    Pairwise (Function.onFun Disjoint (cell (d := d) M)) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  intro k k' hkk'
  show Disjoint (cell M k) (cell M k')
  rw [Set.disjoint_left]
  intro x hx hx'
  apply hkk'
  funext i
  have h1 := hx i (mem_univ i)
  have h2 := hx' i (mem_univ i)
  have a1 : (k i : ℝ) < (k' i : ℝ) + 1 := by
    have := h1.1.trans_lt h2.2
    rwa [div_lt_div_iff_of_pos_right hM'] at this
  have a2 : (k' i : ℝ) < (k i : ℝ) + 1 := by
    have := h2.1.trans_lt h1.2
    rwa [div_lt_div_iff_of_pos_right hM'] at this
  have b1 : (k i : ℕ) < k' i + 1 := by exact_mod_cast a1
  have b2 : (k' i : ℕ) < k i + 1 := by exact_mod_cast a2
  exact Fin.ext (by omega)

theorem volume_real_cell {M : ℕ} (hM : 0 < M) (k : Fin d → Fin M) :
    (volume : Measure (Fin d → ℝ)).real (cell M k) = (1 / (M : ℝ)) ^ d := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  unfold cell
  rw [measureReal_def, Real.volume_pi_Ico_toReal]
  · simp only [add_div, add_sub_cancel_left, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  · intro i
    show (k i : ℝ) / M ≤ ((k i : ℝ) + 1) / M
    gcongr
    linarith

theorem volume_cell_lt_top {M : ℕ} (hM : 0 < M) (k : Fin d → Fin M) :
    (volume : Measure (Fin d → ℝ)) (cell M k) < ⊤ :=
  (measure_mono (cell_subset_Icc hM k)).trans_lt isCompact_Icc.measure_lt_top

/-- Points of a cell are within `1/M` of its grid point (sup distance). -/
theorem dist_lt_of_mem_cell {M : ℕ} (hM : 0 < M) (k : Fin d → Fin M) {x : Fin d → ℝ}
    (hx : x ∈ cell M k) : dist x (gridPoint M k) < 1 / M := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  rw [dist_pi_lt_iff (by positivity)]
  intro i
  have h := hx i (mem_univ i)
  rw [Real.dist_eq, abs_lt]
  constructor
  · have : (0 : ℝ) ≤ x i - gridPoint M k i := by
      simp only [gridPoint]; linarith [h.1]
    linarith [show (0 : ℝ) < 1 / M by positivity]
  · simp only [gridPoint]
    have := h.2
    rw [add_div] at this
    linarith

/-- The integral over the closed cube is the sum of the cell integrals. -/
theorem setIntegral_Icc_eq_sum_cell {M : ℕ} (hM : 0 < M) (g : (Fin d → ℝ) → ℝ)
    (hg : Continuous g) :
    ∫ x in Icc (0 : Fin d → ℝ) 1, g x = ∑ k : Fin d → Fin M, ∫ x in cell M k, g x := by
  have hae : (Icc (0 : Fin d → ℝ) 1 : Set (Fin d → ℝ)) =ᵐ[volume]
      (pi univ fun _ => Ico (0 : ℝ) 1) := by
    have := (Measure.univ_pi_Ico_ae_eq_Icc (μ := fun _ : Fin d => (volume : Measure ℝ))
      (f := (0 : Fin d → ℝ)) (g := 1)).symm
    exact this
  rw [setIntegral_congr_set hae, ← iUnion_cell hM,
    integral_iUnion (fun k => measurableSet_cell M k) (pairwise_disjoint_cell hM)
      ((hg.continuousOn.integrableOn_compact isCompact_Icc).mono_set
        (by rw [iUnion_cell hM]; exact fun x hx => ⟨fun i => (hx i (mem_univ i)).1,
          fun i => (hx i (mem_univ i)).2.le⟩)),
    tsum_fintype]

/-- One-cell error: `|∫_{cell} g - (1/M)^d g(x_k)| ≤ ε (1/M)^d` when `g` varies by at most
`ε` on the cell. -/
theorem abs_setIntegral_cell_sub_le {M : ℕ} (hM : 0 < M) (g : (Fin d → ℝ) → ℝ)
    (hg : Continuous g) (k : Fin d → Fin M) {ε : ℝ}
    (hε : ∀ x ∈ cell M k, |g x - g (gridPoint M k)| ≤ ε) :
    |(∫ x in cell M k, g x) - (1 / (M : ℝ)) ^ d * g (gridPoint M k)| ≤ ε * (1 / (M : ℝ)) ^ d := by
  have hint : IntegrableOn g (cell M k) volume :=
    (hg.continuousOn.integrableOn_compact isCompact_Icc).mono_set (cell_subset_Icc hM k)
  have hsub : (∫ x in cell M k, g x) - (1 / (M : ℝ)) ^ d * g (gridPoint M k) =
      ∫ x in cell M k, (g x - g (gridPoint M k)) := by
    rw [integral_sub hint (integrableOn_const (volume_cell_lt_top hM k).ne),
      setIntegral_const, volume_real_cell hM k, smul_eq_mul]
  rw [hsub, ← Real.norm_eq_abs, ← volume_real_cell hM k]
  exact norm_setIntegral_le_of_norm_le_const (volume_cell_lt_top hM k) fun x hx => by
    rw [Real.norm_eq_abs]; exact hε x hx

/-- **Riemann sums on the unit cube.** For continuous `g`, the left-endpoint Riemann sums on
the grid of mesh `1/(n+1)` converge to `∫_{[0,1]^d} g`. -/
theorem tendsto_riemannSum (g : (Fin d → ℝ) → ℝ) (hg : Continuous g) :
    Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) ^ d *
        ∑ k : Fin d → Fin (n + 1), g (gridPoint (n + 1) k)) atTop
      (𝓝 (∫ x in Icc (0 : Fin d → ℝ) 1, g x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hunif := isCompact_Icc.uniformContinuousOn_of_continuous
    (s := Icc (0 : Fin d → ℝ) 1) hg.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hunif
  obtain ⟨δ, hδ, hδε⟩ := hunif (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  refine ⟨N, fun n hn => ?_⟩
  have hM : 0 < n + 1 := Nat.succ_pos n
  have hM' : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hmesh : 1 / ((n : ℝ) + 1) < δ := by
    refine lt_of_le_of_lt ?_ hN
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    gcongr
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [Real.dist_eq, setIntegral_Icc_eq_sum_cell hM g hg, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hcell : ∀ k : Fin d → Fin (n + 1),
      |(1 / ((n : ℝ) + 1)) ^ d * g (gridPoint (n + 1) k) - ∫ x in cell (n + 1) k, g x| ≤
        ε / 2 * (1 / ((n : ℝ) + 1)) ^ d := by
    intro k
    rw [abs_sub_comm, ← hcast]
    refine abs_setIntegral_cell_sub_le hM g hg k fun x hx => ?_
    have hd := dist_lt_of_mem_cell hM k hx
    rw [hcast] at hd
    have := hδε x (cell_subset_Icc hM k hx) (gridPoint (n + 1) k) (gridPoint_mem_Icc hM k)
      (hd.trans hmesh)
    rw [Real.dist_eq] at this
    exact this.le
  calc |∑ k : Fin d → Fin (n + 1), ((1 / ((n : ℝ) + 1)) ^ d * g (gridPoint (n + 1) k) -
        ∫ x in cell (n + 1) k, g x)|
      ≤ ∑ k : Fin d → Fin (n + 1), (ε / 2 * (1 / ((n : ℝ) + 1)) ^ d) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => hcell k)
    _ = ε / 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, hcast, mul_comm (ε / 2), ← mul_assoc,
          ← mul_pow, mul_one_div_cancel hM'.ne', one_pow, one_mul]
    _ < ε := by linarith

end RenewalGeometry.UnitCubeRiemannSum
