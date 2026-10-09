/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Division of analytic maps by a scalar coordinate; jointly analytic scaled cubic remainders
  (infrastructure for `lem:supp-initial-calculus`: "the full link remainder starts at cubic
  order", uniformly in the lattice spacing; emergent-spacetime manuscript)

Let `E, F` be real Banach spaces and consider maps on `ℝ × E` (a scalar coordinate `s` and a
vector coordinate `w`).

* `divSeries p`: from a formal power series `p` at `(0, w₀)` the series of the quotient by `s`,
  built from the exact multilinear telescoping
  `p(z, …, z) - p(πz, …, πz) = s Σ_i p(z, …, z, e, πz, …, πz)` (`e = (1, 0)`, `π z = (0, w)`);
  `norm_divSeries_le` (`‖q_m‖ ≤ (m + 1)‖p_{m+1}‖`) and `radius_divSeries_pos`.
* **`exists_eq_fst_smul`** (division by a coordinate): if `f` is analytic at `(0, w₀)` and
  `f(0, w) = 0` for `w` near `w₀`, then `f(s, w) = s • g(s, w)` near `(0, w₀)` with `g` analytic at
  `(0, w₀)`.
* **`exists_scaled_cubic`** (jointly analytic rescaled remainders): if `ρ` is analytic at `0` and
  `‖ρ v‖ ≤ C‖v‖³` near `0`, there is `G` analytic at `(0, 0)` with `s² • G(s, w) = ρ(s • w)`
  near `(0, 0)`; hence `G(s, w) = s⁻² ρ(s w)` for `s ≠ 0` (`scaled_cubic_eq`), i.e. the rescaled
  lattice remainders `h⁻² ρ(h ·)` are the restrictions to `s = h` of ONE analytic function of
  `(s, w)`, analytic through `s = 0`.

These statements replace "the integral Taylor formula extends this map analytically through
`t = 0`" by an exact power-series argument.
-/

open Filter Topology

noncomputable section

namespace RenewalGeometry.AnalyticDivision

set_option linter.unusedSectionVars false

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The scalar unit direction `e = (1, 0)`. -/
def eS : ℝ × E := (1, 0)

/-- The projection `π(s, w) = (0, w)` onto the vector coordinate. -/
def piS : (ℝ × E) →L[ℝ] (ℝ × E) :=
  (ContinuousLinearMap.inr ℝ ℝ E).comp (ContinuousLinearMap.snd ℝ ℝ E)

@[simp] theorem piS_apply (z : ℝ × E) : piS z = (0, z.2) := rfl

theorem norm_eS : ‖(eS : ℝ × E)‖ = 1 := by simp [eS, Prod.norm_def]

theorem norm_piS_le : ‖(piS : (ℝ × E) →L[ℝ] (ℝ × E))‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by
    rw [piS_apply, one_mul, Prod.norm_def, Prod.norm_def, norm_zero]
    exact max_le (le_max_of_le_left (norm_nonneg _)) (le_max_right _ _)

theorem sub_piS (z : ℝ × E) : z - piS z = z.1 • (eS : ℝ × E) := by
  ext <;> simp [eS]

/-- The slot maps of the telescoping: identity on slots `j ≤ i`, `π` on slots `j > i`. -/
def slotL {m : ℕ} (i j : Fin (m + 1)) : (ℝ × E) →L[ℝ] (ℝ × E) :=
  if j ≤ i then ContinuousLinearMap.id ℝ (ℝ × E) else piS

theorem norm_slotL_le {m : ℕ} (i j : Fin (m + 1)) : ‖(slotL i j : (ℝ × E) →L[ℝ] (ℝ × E))‖ ≤ 1 := by
  unfold slotL
  split_ifs
  · exact ContinuousLinearMap.norm_id_le
  · exact norm_piS_le

/-- The `i`-th telescoping term: slot `i` of `p_{m+1}` frozen to `e`, slots before `i` free,
slots after `i` projected. -/
def telTerm (P : ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) => ℝ × E) F) (i : Fin (m + 1)) :
    ContinuousMultilinearMap ℝ (fun _ : Fin m => ℝ × E) F :=
  ((P.compContinuousLinearMap (slotL i)).domDomCongr (Equiv.swap i 0)).curryLeft eS

/-- **The divided series** `q_m = Σ_{i ≤ m} telTerm p_{m+1} i`. -/
def divSeries (p : FormalMultilinearSeries ℝ (ℝ × E) F) : FormalMultilinearSeries ℝ (ℝ × E) F :=
  fun m => ∑ i : Fin (m + 1), telTerm (p (m + 1)) i

theorem norm_telTerm_le {m : ℕ} (P : ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) => ℝ × E) F)
    (i : Fin (m + 1)) : ‖telTerm P i‖ ≤ ‖P‖ := by
  unfold telTerm
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  rw [ContinuousMultilinearMap.curryLeft_norm, ContinuousMultilinearMap.norm_domDomCongr, norm_eS,
    mul_one]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h : ∏ j, ‖(slotL i j : (ℝ × E) →L[ℝ] (ℝ × E))‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) fun j _ => norm_slotL_le i j
  calc ‖P‖ * ∏ j, ‖(slotL i j : (ℝ × E) →L[ℝ] (ℝ × E))‖ ≤ ‖P‖ * 1 :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = ‖P‖ := mul_one _

theorem norm_divSeries_le (p : FormalMultilinearSeries ℝ (ℝ × E) F) (m : ℕ) :
    ‖divSeries p m‖ ≤ (m + 1) * ‖p (m + 1)‖ := by
  unfold divSeries
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => norm_telTerm_le (p (m + 1)) i).trans ?_
  simp

/-- Diagonal value of a telescoping term. -/
theorem telTerm_diag {m : ℕ} (P : ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) => ℝ × E) F)
    (i : Fin (m + 1)) (z : ℝ × E) :
    telTerm P i (fun _ => z) =
      P (Function.update (fun j => slotL i j z) i (eS : ℝ × E)) := by
  unfold telTerm
  rw [ContinuousMultilinearMap.curryLeft_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj
    simp [slotL]
  · rw [Function.update_of_ne hj]
    have hs : Equiv.swap i 0 j ≠ 0 := by
      intro h
      rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at h
      exact hj h
    obtain ⟨k, hk⟩ := Fin.exists_succ_eq.mpr hs
    rw [← hk, Fin.cons_succ]

/-- **The multilinear telescoping identity**: `p(z, …, z) - p(πz, …, πz) = s • q_m(z, …, z)`. -/
theorem map_sub_map_piS {m : ℕ} (P : ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) => ℝ × E) F)
    (z : ℝ × E) :
    P (fun _ => z) - P (fun _ => piS z) = z.1 • ∑ i : Fin (m + 1), telTerm P i (fun _ => z) := by
  have h := P.toMultilinearMap.map_sub_map_piecewise (fun _ => z) (fun _ => piS z) Finset.univ
  rw [Finset.piecewise_univ] at h
  change P (fun _ => z) - P (fun _ => piS z) = _ at h
  rw [h, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [telTerm_diag]
  have e : (fun j => if j ∈ Finset.univ → j < i then z else if i = j then z - piS z else piS z) =
      Function.update (fun j => slotL i j z) i (z.1 • (eS : ℝ × E)) := by
    funext j
    by_cases hji : j = i
    · subst hji
      rw [Function.update_self, ite_eq_right_of_eq_false _ _ (by simp), ite_eq_left_of_eq_true _ _ (by simp), sub_piS]
    · rw [Function.update_of_ne hji]
      have hij : i ≠ j := Ne.symm hji
      by_cases hlt : j < i
      · simp [hlt, slotL, le_of_lt hlt]
      · have hgt : ¬ j ≤ i := fun h => hlt (lt_of_le_of_ne h hji)
        simp [hlt, hij, slotL, hgt]
  change P.toMultilinearMap _ = _
  rw [e]
  exact P.map_update_smul _ i z.1 eS

theorem radius_divSeries_pos (p : FormalMultilinearSeries ℝ (ℝ × E) F) (hp : 0 < p.radius) :
    0 < (divSeries p).radius := by
  obtain ⟨r, hr0, hrR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp
  obtain ⟨K, hK, hKp⟩ := p.norm_mul_pow_le_of_lt_radius hrR
  have hr : (0 : ℝ) < r := NNReal.coe_pos.mpr (ENNReal.coe_pos.mp hr0)
  have hbound : ∀ m : ℕ, ‖divSeries p m‖ * ((r / 2 : NNReal) : ℝ) ^ m ≤ K / r := by
    intro m
    have h1 := norm_divSeries_le p m
    have h2 := hKp (m + 1)
    have hm : ((m : ℝ) + 1) ≤ 2 ^ m := by
      have := Nat.lt_two_pow_self (n := m)
      exact_mod_cast this
    have hpos : 0 ≤ ‖p (m + 1)‖ := norm_nonneg _
    rw [NNReal.coe_div, NNReal.coe_two, div_pow]
    calc ‖divSeries p m‖ * ((r : ℝ) ^ m / 2 ^ m)
        ≤ ((m + 1) * ‖p (m + 1)‖) * ((r : ℝ) ^ m / 2 ^ m) := by gcongr
      _ = ((m + 1) / 2 ^ m) * (‖p (m + 1)‖ * (r : ℝ) ^ (m + 1)) / r := by
          field_simp; ring
      _ ≤ 1 * K / r := by
          gcongr
          · rw [div_le_one (by positivity)]; exact hm
      _ = K / r := by ring
  have := (divSeries p).le_radius_of_bound (K / r) hbound
  refine lt_of_lt_of_le ?_ this
  have hr' : (0 : NNReal) < r := ENNReal.coe_pos.mp hr0
  exact ENNReal.coe_pos.mpr (div_pos hr' two_pos)

/-- **Division by a scalar coordinate.**  If `f : ℝ × E → F` is analytic at `(0, w₀)` and
vanishes on the hyperplane `s = 0` near `w₀`, then `f(s, w) = s • g(s, w)` near `(0, w₀)` for a
map `g` analytic at `(0, w₀)`. -/
theorem exists_eq_fst_smul [CompleteSpace F] {f : ℝ × E → F} {w₀ : E}
    (hf : AnalyticAt ℝ f (0, w₀)) (h0 : ∀ᶠ w in 𝓝 w₀, f (0, w) = 0) :
    ∃ g : ℝ × E → F, AnalyticAt ℝ g (0, w₀) ∧ ∀ᶠ z in 𝓝 ((0 : ℝ), w₀), f z = z.1 • g z := by
  obtain ⟨p, R, hp⟩ := hf
  set q := divSeries p
  have hq : 0 < q.radius := radius_divSeries_pos p (lt_of_lt_of_le hp.r_pos hp.r_le)
  set z₀ : ℝ × E := (0, w₀)
  refine ⟨fun z => q.sum (z - z₀), ?_, ?_⟩
  · have h := (q.hasFPowerSeriesOnBall hq).comp_sub z₀
    rw [zero_add] at h
    exact h.analyticAt
  · obtain ⟨ε, hε, hεw⟩ := Metric.eventually_nhds_iff.mp h0
    obtain ⟨r, hr0, hrR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (lt_min hp.r_pos hq)
    have hr : (0 : ℝ) < r := NNReal.coe_pos.mpr (ENNReal.coe_pos.mp hr0)
    refine Metric.eventually_nhds_iff.mpr ⟨min ε r, lt_min hε hr, fun z hz => ?_⟩
    set y := z - z₀ with hy
    have hyn : ‖y‖ < min ε r := by rw [hy, ← dist_eq_norm]; exact hz
    have hyR : ∀ v : ℝ × E, ‖v‖ ≤ ‖y‖ → v ∈ Metric.eball (0 : ℝ × E) (min R q.radius) := by
      intro v hv
      rw [Metric.mem_eball, edist_zero_right]
      refine lt_of_le_of_lt ?_ hrR
      rw [enorm_eq_nnnorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm]
      exact hv.trans (hyn.le.trans (min_le_right _ _))
    have hmemR : ∀ v : ℝ × E, ‖v‖ ≤ ‖y‖ → v ∈ Metric.eball (0 : ℝ × E) R := fun v hv =>
      Metric.eball_subset_eball (min_le_left _ _) (hyR v hv)
    have hπy : ‖piS y‖ ≤ ‖y‖ := (piS.le_opNorm y).trans (by
      have := norm_piS_le (E := E); nlinarith [norm_nonneg y])
    -- the two expansions
    have hs1 := hp.hasSum (hmemR y le_rfl)
    have hs2 := hp.hasSum (hmemR (piS y) hπy)
    have hf0 : f (z₀ + piS y) = 0 := by
      have : z₀ + piS y = (0, w₀ + y.2) := by ext <;> simp [z₀]
      rw [this]
      refine hεw ?_
      rw [dist_eq_norm, add_sub_cancel_left]
      calc ‖y.2‖ ≤ ‖y‖ := norm_snd_le y
        _ < ε := hyn.trans_le (min_le_left _ _)
    rw [hf0] at hs2
    have hdiff := hs1.sub hs2
    rw [sub_zero] at hdiff
    have hz : z₀ + y = z := by rw [hy]; abel
    rw [hz] at hdiff
    -- shift by one
    have hshift := (hasSum_nat_add_iff' 1).mpr hdiff
    have h00 : p 0 (fun _ => y) - p 0 (fun _ => piS y) = 0 := by
      rw [sub_eq_zero]; congr 1; funext i; exact Fin.elim0 i
    simp only [Finset.range_one, Finset.sum_singleton, h00, sub_zero] at hshift
    have hterm : (fun n => p (n + 1) (fun _ => y) - p (n + 1) (fun _ => piS y)) =
        fun n => y.1 • q n (fun _ => y) := by
      funext n
      rw [map_sub_map_piS]
      simp [q, divSeries]
    rw [hterm] at hshift
    have hq' := (q.hasSum (Metric.eball_subset_eball (min_le_right _ _) (hyR y le_rfl))).const_smul y.1
    have := hshift.unique hq'
    rw [this]
    have hy1 : y.1 = z.1 := by simp [hy, z₀]
    rw [hy1]

/-- **Jointly analytic rescaled cubic remainders.**  If `ρ` is analytic at `0` and cubic
(`‖ρ v‖ ≤ C‖v‖³` near `0`), there is `G` analytic at `(0, 0)` with `s² • G(s, w) = ρ(s • w)` near
`(0, 0)`. -/
theorem exists_scaled_cubic [CompleteSpace E] [CompleteSpace F] {ρ : E → F}
    (hρ : AnalyticAt ℝ ρ 0) {C : ℝ} (hC : ∀ᶠ v in 𝓝 (0 : E), ‖ρ v‖ ≤ C * ‖v‖ ^ 3) :
    ∃ G : ℝ × E → F, AnalyticAt ℝ G (0, 0) ∧
      ∀ᶠ z in 𝓝 ((0 : ℝ), (0 : E)), z.1 ^ 2 • G z = ρ (z.1 • z.2) := by
  have hρ0 : ρ 0 = 0 := by
    have := hC.self_of_nhds
    simpa using this
  set f : ℝ × E → F := fun z => ρ (z.1 • z.2) with hfdef
  have hsm : AnalyticAt ℝ (fun z : ℝ × E => z.1 • z.2) ((0 : ℝ), (0 : E)) :=
    analyticAt_fst.smul analyticAt_snd
  have hf : AnalyticAt ℝ f ((0 : ℝ), (0 : E)) := by
    refine hρ.comp_of_eq hsm ?_
    simp
  have hf0 : ∀ᶠ w in 𝓝 (0 : E), f (0, w) = 0 := Eventually.of_forall fun w => by
    simp [hfdef, hρ0]
  obtain ⟨g₁, hg₁, hfg₁⟩ := exists_eq_fst_smul hf hf0
  -- `g₁` vanishes on `s = 0` near `0`
  have hg₁0 : ∀ᶠ w in 𝓝 (0 : E), g₁ (0, w) = 0 := by
    have hcont := hg₁.eventually_analyticAt
    have ht : Tendsto (fun z : ℝ × E => z.1 • z.2) (𝓝 ((0 : ℝ), (0 : E))) (𝓝 0) := by
      have hcs : Continuous (fun z : ℝ × E => z.1 • z.2) := continuous_fst.smul continuous_snd
      simpa using hcs.tendsto ((0 : ℝ), (0 : E))
    have hC' : ∀ᶠ z in 𝓝 ((0 : ℝ), (0 : E)), ‖ρ (z.1 • z.2)‖ ≤ C * ‖z.1 • z.2‖ ^ 3 :=
      ht.eventually hC
    obtain ⟨ε, hε, hall⟩ := Metric.eventually_nhds_iff.mp ((hcont.and hfg₁).and hC')
    refine Metric.eventually_nhds_iff.mpr ⟨ε / 2, by positivity, fun w hw => ?_⟩
    have hw' : ‖w‖ < ε / 2 := by simpa using hw
    -- continuity of `s ↦ g₁(s, w)` at `0`
    have hmem : ∀ s : ℝ, |s| < ε / 2 → dist ((s, w) : ℝ × E) ((0 : ℝ), (0 : E)) < ε := by
      intro s hs
      show max (dist s 0) (dist w 0) < ε
      rw [dist_zero_right, dist_zero_right, Real.norm_eq_abs]
      exact max_lt (by linarith) (by linarith)
    have hca : ContinuousAt (fun s : ℝ => g₁ (s, w)) 0 := by
      have h1 : ContinuousAt g₁ ((0 : ℝ), w) := (hall (hmem 0 (by simpa using hε))).1.1.continuousAt
      have h2 : ContinuousAt (fun s : ℝ => ((s, w) : ℝ × E)) 0 :=
        (continuous_id.prodMk continuous_const).continuousAt
      exact ContinuousAt.comp (g := g₁) (f := fun s : ℝ => ((s, w) : ℝ × E)) h1 h2
    -- the limit along `s ≠ 0` is `0`
    have hlim : Tendsto (fun s : ℝ => g₁ (s, w)) (𝓝[≠] 0) (𝓝 0) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      simp only [sub_zero]
      refine squeeze_zero_norm' ?_ (?_ : Tendsto (fun s : ℝ => |C| * s ^ 2 * ‖w‖ ^ 3) (𝓝[≠] 0) (𝓝 0))
      · have hev : ∀ᶠ s in 𝓝[≠] (0 : ℝ), s ≠ 0 ∧ |s| < ε / 2 := by
          refine (eventually_mem_nhdsWithin).and (nhdsWithin_le_nhds ?_)
          have hb : Metric.ball (0 : ℝ) (ε / 2) ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ (by positivity)
          filter_upwards [hb] with s hs
          simpa [Real.dist_eq] using hs
        filter_upwards [hev] with s ⟨hs0, hs⟩
        have hP := hall (hmem s hs)
        have h1 : f (s, w) = s • g₁ (s, w) := hP.1.2
        have h2 : ‖ρ (s • w)‖ ≤ C * ‖s • w‖ ^ 3 := hP.2
        rw [norm_norm]
        have hfs : ‖f (s, w)‖ = |s| * ‖g₁ (s, w)‖ := by rw [h1, norm_smul, Real.norm_eq_abs]
        have hρs : ‖f (s, w)‖ ≤ |C| * |s| ^ 3 * ‖w‖ ^ 3 := by
          have : f (s, w) = ρ (s • w) := rfl
          rw [this]
          refine h2.trans ?_
          rw [norm_smul, Real.norm_eq_abs, mul_pow]
          have : C ≤ |C| := le_abs_self C
          have h0 : 0 ≤ |s| ^ 3 * ‖w‖ ^ 3 := by positivity
          nlinarith
        have hspos : 0 < |s| := abs_pos.mpr hs0
        rw [hfs] at hρs
        have : ‖g₁ (s, w)‖ ≤ |C| * |s| ^ 2 * ‖w‖ ^ 3 := by
          have e : |C| * |s| ^ 3 * ‖w‖ ^ 3 = |s| * (|C| * |s| ^ 2 * ‖w‖ ^ 3) := by ring
          rw [e] at hρs
          exact le_of_mul_le_mul_left hρs hspos
        calc ‖g₁ (s, w)‖ ≤ |C| * |s| ^ 2 * ‖w‖ ^ 3 := this
          _ = |C| * s ^ 2 * ‖w‖ ^ 3 := by rw [sq_abs]
      · have : Tendsto (fun s : ℝ => |C| * s ^ 2 * ‖w‖ ^ 3) (𝓝 0) (𝓝 (|C| * 0 ^ 2 * ‖w‖ ^ 3)) :=
          (tendsto_const_nhds.mul ((continuous_pow 2).tendsto 0)).mul tendsto_const_nhds
        simpa using this.mono_left nhdsWithin_le_nhds
    have h1 : Tendsto (fun s : ℝ => g₁ (s, w)) (𝓝[≠] 0) (𝓝 (g₁ (0, w))) :=
      hca.tendsto.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique h1 hlim
  obtain ⟨g₂, hg₂, hg₁g₂⟩ := exists_eq_fst_smul hg₁ hg₁0
  refine ⟨g₂, hg₂, ?_⟩
  filter_upwards [hfg₁, hg₁g₂] with z h1 h2
  rw [sq, mul_smul, ← h2]
  exact h1.symm

/-- The rescaled form: for `s ≠ 0`, `G(s, w) = (s²)⁻¹ • ρ(s • w)` near `(0, 0)`. -/
theorem scaled_cubic_eq {ρ : E → F} {G : ℝ × E → F}
    (hG : ∀ᶠ z in 𝓝 ((0 : ℝ), (0 : E)), z.1 ^ 2 • G z = ρ (z.1 • z.2)) :
    ∀ᶠ z in 𝓝 ((0 : ℝ), (0 : E)), z.1 ≠ 0 → G z = (z.1 ^ 2)⁻¹ • ρ (z.1 • z.2) := by
  filter_upwards [hG] with z hz hs
  rw [← hz, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hs), one_smul]

end RenewalGeometry.AnalyticDivision
