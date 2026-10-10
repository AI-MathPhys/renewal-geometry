/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallSobolevAlgebra

/-!
# Products `H^p(B) × H^t(B) → H^t(B)` for `p ≥ 3`, `t ≤ p` on balls of `ℝ⁴`
  (stage D1c of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.  The algebra property of `BallSobolevAlgebra`
(`p = t ≥ 3`) is extended to **mixed regularity**: multiplication by an `H^p(B)` function,
`p ≥ 3`, maps `H^t(B)` into itself for every `t ≤ p` (`memHk_mul_gen`), which is what the elliptic
bootstrap of the linearised Coulomb problem with rough coefficients needs.

* `exists_term_bound_gen` — one Leibniz term `∂^a u ∂^b v`, `|a| + |b| ≤ t`, is bounded by
  `K ‖u‖_{H^p} ‖v‖_{H^t}` (sup bound `H³ ⊂ L^∞` on the factor with few derivatives, otherwise
  `H¹ ⊂ L⁴` on both factors);
* `nW_mul_le_gen` — `‖u v‖_{H^t} ≤ C ‖u‖_{H^p} ‖v‖_{H^t}` for smooth `u, v`;
* `memHk_mul_gen` — the weak version by density.
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallReg

open SobolevOpen

set_option linter.unusedSectionVars false

section Gen

variable (c : Fin 4 → ℝ) (r : ℝ)

/-- **One Leibniz term with mixed regularity** (`p ≥ 3`, `t ≤ p`, `|a| + |b| ≤ t`). -/
theorem exists_term_bound_gen (hr : 0 < r) : ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
    ∀ {p t : ℕ}, 3 ≤ p → t ≤ p → ∀ {u v : (Fin 4 → ℝ) → ℝ} {a b : List (Fin 4)},
      ContDiff ℝ ∞ u → ContDiff ℝ ∞ v → a.length + b.length ≤ t →
      eLpNorm (fun x => pdw u a x * pdw v b x) 2 (volume.restrict (euclBall c r)) ≤
        K * nW c r p u * nW c r t v := by
  obtain ⟨C3, hC3, hsup⟩ := exists_sup_pdw_bound c r hr
  obtain ⟨C4, hC4, hL4⟩ := exists_L4_pdw_bound c r hr
  refine ⟨C3 + C3 + C4 * C4, by finiteness, fun {p t} hp htp {u v a b} hu hv hab => ?_⟩
  have hBm := measurableSet_euclBall c r
  have hfin : ∀ {w : (Fin 4 → ℝ) → ℝ} {q : ℕ}, ContDiff ℝ ∞ w → C3 * nW c r q w ≠ ⊤ :=
    fun {w q} hw => ENNReal.mul_ne_top hC3 (nW_lt_top c r hr hw q).ne
  by_cases ha : a.length + 3 ≤ p
  · have hpt : ∀ᵐ x ∂(volume.restrict (euclBall c r)),
        ‖pdw u a x * pdw v b x‖ ≤ (C3 * nW c r p u).toReal * ‖pdw v b x‖ := by
      filter_upwards [ae_restrict_mem hBm] with x hx
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      exact (ENNReal.ofReal_le_iff_le_toReal (hfin hu)).mp (hsup hu ha x hx)
    refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hpt 2).trans ?_
    rw [ENNReal.ofReal_toReal (hfin hu)]
    calc C3 * nW c r p u * eLpNorm (pdw v b) 2 (volume.restrict (euclBall c r))
        ≤ C3 * nW c r p u * nW c r t v := by
          gcongr; exact eLpNorm_pdw_le_nW c r v (by omega)
      _ ≤ (C3 + C3 + C4 * C4) * nW c r p u * nW c r t v := by
          gcongr; exact le_add_right le_self_add
  by_cases hb : b.length + 3 ≤ t
  · have hpt : ∀ᵐ x ∂(volume.restrict (euclBall c r)),
        ‖pdw u a x * pdw v b x‖ ≤ (C3 * nW c r t v).toReal * ‖pdw u a x‖ := by
      filter_upwards [ae_restrict_mem hBm] with x hx
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      exact (ENNReal.ofReal_le_iff_le_toReal (hfin hv)).mp (hsup hv hb x hx)
    refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hpt 2).trans ?_
    rw [ENNReal.ofReal_toReal (hfin hv)]
    calc C3 * nW c r t v * eLpNorm (pdw u a) 2 (volume.restrict (euclBall c r))
        ≤ C3 * nW c r t v * nW c r p u := by
          gcongr; exact eLpNorm_pdw_le_nW c r u (by omega)
      _ = C3 * nW c r p u * nW c r t v := by ring
      _ ≤ (C3 + C3 + C4 * C4) * nW c r p u * nW c r t v := by
          gcongr; exact le_add_right le_add_self
  · have ha1 : a.length + 1 ≤ p := by omega
    have hb1 : b.length + 1 ≤ t := by omega
    have hH : eLpNorm (fun x => pdw u a x * pdw v b x) 2 (volume.restrict (euclBall c r)) ≤
        eLpNorm (pdw u a) 4 (volume.restrict (euclBall c r)) *
          eLpNorm (pdw v b) 4 (volume.restrict (euclBall c r)) := by
      have := eLpNorm_smul_le_mul_eLpNorm (p := 4) (q := 4) (r := 2)
        (μ := volume.restrict (euclBall c r)) (contDiff_pdw hv b).continuous.aestronglyMeasurable
        (contDiff_pdw hu a).continuous.aestronglyMeasurable
      exact this
    refine hH.trans ?_
    calc eLpNorm (pdw u a) 4 (volume.restrict (euclBall c r)) *
          eLpNorm (pdw v b) 4 (volume.restrict (euclBall c r))
        ≤ (C4 * nW c r p u) * (C4 * nW c r t v) := by
          gcongr
          · exact hL4 hu ha1
          · exact hL4 hv hb1
      _ = C4 * C4 * nW c r p u * nW c r t v := by ring
      _ ≤ (C3 + C3 + C4 * C4) * nW c r p u * nW c r t v := by
          gcongr; exact le_add_self

/-- **The mixed product estimate, smooth functions** (`p ≥ 3`, `t ≤ p`):
`‖u v‖_{H^t(B)} ≤ C ‖u‖_{H^p(B)} ‖v‖_{H^t(B)}`. -/
theorem nW_mul_le_gen (hr : 0 < r) : ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ {p t : ℕ}, 3 ≤ p → t ≤ p →
    ∀ {u v : (Fin 4 → ℝ) → ℝ}, ContDiff ℝ ∞ u → ContDiff ℝ ∞ v →
      nW c r t (fun x => u x * v x) ≤
        ((wordsUpTo 4 t).card * 2 ^ t : ℝ≥0∞) * K * nW c r p u * nW c r t v := by
  obtain ⟨K, hK, hterm⟩ := exists_term_bound_gen c r hr
  refine ⟨K, hK, fun {p t} hp htp {u v} hu hv => ?_⟩
  have hw : ∀ w ∈ wordsUpTo 4 t,
      eLpNorm (pdw (fun x => u x * v x) w) 2 (volume.restrict (euclBall c r)) ≤
        2 ^ t * (K * nW c r p u * nW c r t v) := by
    intro w hwmem
    have hlen := mem_wordsUpTo.mp hwmem
    have e : pdw (fun x => u x * v x) w =
        fun x => ((splits w).map fun q => pdw u q.1 x * pdw v q.2 x).sum :=
      funext (pdw_mul hu hv w)
    rw [e]
    refine (eLpNorm_list_sum_le c r (splits w) (fun q x => pdw u q.1 x * pdw v q.2 x)
      fun q => ((contDiff_pdw hu q.1).mul (contDiff_pdw hv q.2)).continuous).trans ?_
    have hbd : ∀ q ∈ splits w, eLpNorm (fun x => pdw u q.1 x * pdw v q.2 x) 2
        (volume.restrict (euclBall c r)) ≤ K * nW c r p u * nW c r t v := fun q hq =>
      hterm hp htp hu hv (by rw [length_add_of_mem_splits hq]; exact hlen)
    calc ((splits w).map fun q => eLpNorm (fun x => pdw u q.1 x * pdw v q.2 x) 2
          (volume.restrict (euclBall c r))).sum
        ≤ ((splits w).map fun _ => K * nW c r p u * nW c r t v).sum :=
          List.sum_le_sum fun q hq => hbd q hq
      _ = (splits w).length * (K * nW c r p u * nW c r t v) := by
          rw [List.map_const', List.sum_replicate, nsmul_eq_mul]
      _ ≤ 2 ^ t * (K * nW c r p u * nW c r t v) := by
          rw [length_splits]
          gcongr
          · push_cast; exact pow_le_pow_right₀ (by norm_num) hlen
  unfold nW
  calc ∑ w ∈ wordsUpTo 4 t, eLpNorm (pdw (fun x => u x * v x) w) 2 (volume.restrict (euclBall c r))
      ≤ ∑ w ∈ wordsUpTo 4 t, 2 ^ t * (K * nW c r p u * nW c r t v) :=
        Finset.sum_le_sum hw
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; unfold nW; ring

/-- `nW` is monotone in the order. -/
theorem nW_mono {p q : ℕ} (h : q ≤ p) (u : (Fin 4 → ℝ) → ℝ) : nW c r q u ≤ nW c r p u := by
  unfold nW
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun w hw => mem_wordsUpTo.mpr
    ((mem_wordsUpTo.mp hw).trans h)) fun _ _ _ => bot_le

/-- **Multiplication by an `H^p(B)` function, `p ≥ 3`, preserves `H^t(B)`, `t ≤ p`** (weak
Sobolev spaces on balls of `ℝ⁴`). -/
theorem memHk_mul_gen (hr : 0 < r) {p t : ℕ} (hp : 3 ≤ p) (htp : t ≤ p)
    {u v : (Fin 4 → ℝ) → ℝ} (hu : MemHk (euclBall c r) p u) (hv : MemHk (euclBall c r) t v) :
    MemHk (euclBall c r) t (fun x => u x * v x) := by
  have : Fact (0 < r) := ⟨hr⟩
  obtain ⟨K, hK, hmul0⟩ := nW_mul_le_gen c r hr
  obtain ⟨C, hC⟩ : ∃ C : ℝ≥0∞, C = ((wordsUpTo 4 t).card * 2 ^ t : ℝ≥0∞) * K := ⟨_, rfl⟩
  have hCt : C ≠ ⊤ := by rw [hC]; finiteness
  have hmul : ∀ {u v : (Fin 4 → ℝ) → ℝ}, ContDiff ℝ ∞ u → ContDiff ℝ ∞ v →
      nW c r t (fun x => u x * v x) ≤ C * nW c r p u * nW c r t v := fun hu hv => by
    rw [hC]; exact hmul0 hp htp hu hv
  obtain ⟨φ, hφ, hcu⟩ := (memHk_iff_exists_convHk c r p).mp hu
  obtain ⟨ψ, hψ, hcv⟩ := (memHk_iff_exists_convHk c r t).mp hv
  obtain ⟨Du, Gu, hGu, hDu, hdu, hbu⟩ := exists_word_data c r hr hφ hcu
  obtain ⟨Dv, Gv, hGv, hDv, hdv, hbv⟩ := exists_word_data c r hr hψ hcv
  have hΦ : ∀ m, ContDiff ℝ ∞ (fun x => φ m x * ψ m x) := fun m => (hφ m).mul (hψ m)
  have hRHS : Tendsto (fun q : ℕ × ℕ => C * ((Du q.1 + Du q.2) * (Gv + Dv q.1)) +
      C * ((Gu + Du q.2) * (Dv q.1 + Dv q.2))) atTop (𝓝 0) := by
    have hA : Tendsto (fun q : ℕ × ℕ => Du q.1 + Du q.2) atTop (𝓝 0) := by
      simpa using (hDu.comp tendsto_fst_nat).add (hDu.comp tendsto_snd_nat)
    have hB : Tendsto (fun q : ℕ × ℕ => Gv + Dv q.1) atTop (𝓝 Gv) := by
      simpa using (tendsto_const_nhds (x := Gv)).add (hDv.comp tendsto_fst_nat)
    have hA' : Tendsto (fun q : ℕ × ℕ => Gu + Du q.2) atTop (𝓝 Gu) := by
      simpa using (tendsto_const_nhds (x := Gu)).add (hDu.comp tendsto_snd_nat)
    have hB' : Tendsto (fun q : ℕ × ℕ => Dv q.1 + Dv q.2) atTop (𝓝 0) := by
      simpa using (hDv.comp tendsto_fst_nat).add (hDv.comp tendsto_snd_nat)
    have h1 := ENNReal.Tendsto.const_mul
      (ENNReal.Tendsto.mul hA (Or.inr hGv) hB (Or.inr ENNReal.zero_ne_top)) (Or.inr hCt)
    have h2 := ENNReal.Tendsto.const_mul
      (ENNReal.Tendsto.mul hA' (Or.inr ENNReal.zero_ne_top) hB' (Or.inr hGu)) (Or.inr hCt)
    simpa using h1.add h2
  have hmul_sub : ∀ m q, nW c r t (fun x => φ m x * ψ m x - φ q x * ψ q x) ≤
      C * nW c r p (fun x => φ m x - φ q x) * nW c r t (ψ m) +
        C * nW c r p (φ q) * nW c r t (fun x => ψ m x - ψ q x) := by
    intro m q
    have e : (fun x => φ m x * ψ m x - φ q x * ψ q x) =
        fun x => (fun y => (φ m y - φ q y) * ψ m y) x + (fun y => φ q y * (ψ m y - ψ q y)) x := by
      funext x; ring
    rw [e]
    refine (nW_add_le c r (((hφ m).sub (hφ q)).mul (hψ m)) ((hφ q).mul ((hψ m).sub (hψ q))) t).trans ?_
    exact add_le_add (hmul ((hφ m).sub (hφ q)) (hψ m)) (hmul (hφ q) ((hψ m).sub (hψ q)))
  have hcauchy : ∀ w : List (Fin 4), w.length ≤ t → Tendsto (fun q : ℕ × ℕ =>
      eLpNorm (pdw (fun x => φ q.1 x * ψ q.1 x) w - pdw (fun x => φ q.2 x * ψ q.2 x) w) 2
        (volume.restrict (euclBall c r))) atTop (𝓝 0) := by
    intro w hw
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hRHS
      (fun _ => bot_le) fun q => ?_
    have e : pdw (fun x => φ q.1 x * ψ q.1 x) w - pdw (fun x => φ q.2 x * ψ q.2 x) w =
        pdw (fun x => φ q.1 x * ψ q.1 x - φ q.2 x * ψ q.2 x) w := by
      rw [pdw_sub (hΦ q.1) (hΦ q.2) w]; rfl
    rw [e]
    refine (eLpNorm_pdw_le_nW c r _ hw).trans ?_
    refine (hmul_sub q.1 q.2).trans ?_
    rw [mul_assoc, mul_assoc]
    gcongr
    · exact hdu q.1 q.2
    · exact hbv q.1
    · exact hbu q.2
    · exact hdv q.1 q.2
  obtain ⟨U, hU⟩ := exists_convHk_of_cauchy c hr.le t hΦ hcauchy
  have hUm : MemHk (euclBall c r) t U := (memHk_iff_exists_convHk c r t).mpr ⟨_, hΦ, hU⟩
  refine hUm.congr_ae ?_
  have hfin := isFiniteMeasure_restrict_euclBall c hr.le
  obtain ⟨V, hV⟩ : ∃ V : ℝ≥0∞, V = (volume.restrict (euclBall c r)) Set.univ ^
      (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) := ⟨_, rfl⟩
  have hVt : V ≠ ⊤ := by
    rw [hV]; exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _)
  have hUb := hU.base
  have hub := hcu.base
  have hvb := hcv.base
  have huv : AEStronglyMeasurable (fun x => u x * v x) (volume.restrict (euclBall c r)) :=
    hub.1.aestronglyMeasurable.mul hvb.1.aestronglyMeasurable
  have hbound : ∀ m, eLpNorm (U - fun x => u x * v x) 1 (volume.restrict (euclBall c r)) ≤
      eLpNorm ((fun x => φ m x * ψ m x) - U) 2 (volume.restrict (euclBall c r)) * V +
        (eLpNorm (φ m - u) 2 (volume.restrict (euclBall c r)) *
            (eLpNorm (ψ m - v) 2 (volume.restrict (euclBall c r)) +
              eLpNorm v 2 (volume.restrict (euclBall c r))) +
          eLpNorm u 2 (volume.restrict (euclBall c r)) *
            eLpNorm (ψ m - v) 2 (volume.restrict (euclBall c r))) := by
    intro m
    have hφm := (hφ m).continuous.aestronglyMeasurable (μ := volume.restrict (euclBall c r))
    have hψm := (hψ m).continuous.aestronglyMeasurable (μ := volume.restrict (euclBall c r))
    have hΦm := (hΦ m).continuous.aestronglyMeasurable (μ := volume.restrict (euclBall c r))
    have e1 : (U - fun x => u x * v x) =
        (U - fun x => φ m x * ψ m x) + ((fun x => φ m x * ψ m x) - fun x => u x * v x) := by
      funext x; simp
    have e2 : ((fun x => φ m x * ψ m x) - fun x => u x * v x) =
        (φ m - u) • ψ m + u • (ψ m - v) := by
      funext x; simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, smul_eq_mul]; ring
    rw [e1]
    refine (eLpNorm_add_le (hUb.1.aestronglyMeasurable.sub hΦm) (hΦm.sub huv) le_rfl).trans ?_
    gcongr
    · rw [eLpNorm_sub_comm]
      rw [hV]
      exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num)
        (hΦm.sub hUb.1.aestronglyMeasurable)
    · rw [e2]
      refine (eLpNorm_add_le ((hφm.sub hub.1.aestronglyMeasurable).smul hψm)
        (hub.1.aestronglyMeasurable.smul (hψm.sub hvb.1.aestronglyMeasurable)) le_rfl).trans ?_
      gcongr
      · refine (eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) hψm
          (hφm.sub hub.1.aestronglyMeasurable)).trans ?_
        gcongr
        exact eLpNorm_le_via hψm hvb.1.aestronglyMeasurable
      · exact eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
          (hψm.sub hvb.1.aestronglyMeasurable) hub.1.aestronglyMeasurable
  have hlim : Tendsto (fun m => eLpNorm ((fun x => φ m x * ψ m x) - U) 2
        (volume.restrict (euclBall c r)) * V +
      (eLpNorm (φ m - u) 2 (volume.restrict (euclBall c r)) *
          (eLpNorm (ψ m - v) 2 (volume.restrict (euclBall c r)) +
            eLpNorm v 2 (volume.restrict (euclBall c r))) +
        eLpNorm u 2 (volume.restrict (euclBall c r)) *
          eLpNorm (ψ m - v) 2 (volume.restrict (euclBall c r)))) atTop (𝓝 0) := by
    have t1 := ENNReal.Tendsto.mul_const hUb.2 (Or.inr hVt)
    have t2 : Tendsto (fun m => eLpNorm (ψ m - v) 2 (volume.restrict (euclBall c r)) +
        eLpNorm v 2 (volume.restrict (euclBall c r))) atTop
          (𝓝 (eLpNorm v 2 (volume.restrict (euclBall c r)))) := by
      simpa using hvb.2.add (tendsto_const_nhds (x := eLpNorm v 2 (volume.restrict (euclBall c r))))
    have t3 := ENNReal.Tendsto.mul hub.2 (Or.inr hvb.1.eLpNorm_lt_top.ne) t2
      (Or.inr ENNReal.zero_ne_top)
    have t4 := ENNReal.Tendsto.const_mul hvb.2 (Or.inr hub.1.eLpNorm_lt_top.ne)
    simpa using t1.add (t3.add t4)
  have h0 : eLpNorm (U - fun x => u x * v x) 1 (volume.restrict (euclBall c r)) = 0 :=
    le_antisymm (ge_of_tendsto' hlim hbound) bot_le
  have := (eLpNorm_eq_zero_iff (hUb.1.aestronglyMeasurable.sub huv) one_ne_zero).mp h0
  exact this.mono fun x hx => sub_eq_zero.mp hx

end Gen

end RenewalGeometry.BallAnalysis.BallReg
