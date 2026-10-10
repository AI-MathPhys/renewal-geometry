/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallSobolevInfty

/-!
# The Banach algebra `H^s(B)`, `s ≥ 3`, on balls of `ℝ⁴`
  (stage C5b of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `pdw u w` — iterated classical partial derivatives along a word `w` (`pdw u (i :: w) =
  ∂_i (pdw u w)`), `pdw_append`;
* `wordsUpTo s` (the words of length `≤ s`) and the classical `H^s(B)` norm
  `nW c r s u = Σ_{|w| ≤ s} ‖∂^w u‖_{L²(B)}`;
* `splits`, `pdw_mul` — **the Leibniz rule along words**:
  `∂^w (u v) = Σ_{(a, b) ∈ splits w} ∂^a u · ∂^b v`, with `|a| + |b| = |w|`;
* `nW_mul_le` (**the algebra estimate**, `n = 4`, `s ≥ 3`): `‖u v‖_{H^s(B)} ≤ C ‖u‖_{H^s(B)}
  ‖v‖_{H^s(B)}` for smooth `u, v` — each Leibniz term is estimated by `H³ ⊂ L^∞`
  (`abs_le_n3`) on the factor with at most `s - 3` derivatives, or by `H¹ ⊂ L⁴` on both factors;
* `memHk_mul` (**`H^s(B)` is an algebra**): `u, v ∈ H^s(B)` (weak) implies `u v ∈ H^s(B)`,
  by the density of smooth functions (`convHk_smoothApprox`) and the algebra estimate.
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallReg

open SobolevOpen

set_option linter.unusedSectionVars false

variable {n : ℕ}

/-! ### Words and iterated derivatives -/

section Words

/-- Iterated classical partial derivatives along a word: `pdw u [] = u`,
`pdw u (i :: w) = ∂_i (pdw u w)`. -/
def pdw (u : (Fin n → ℝ) → ℝ) : List (Fin n) → (Fin n → ℝ) → ℝ
  | [] => u
  | i :: w => pd (pdw u w) i

@[simp] theorem pdw_nil (u : (Fin n → ℝ) → ℝ) : pdw u [] = u := rfl

@[simp] theorem pdw_cons (u : (Fin n → ℝ) → ℝ) (i : Fin n) (w : List (Fin n)) :
    pdw u (i :: w) = pd (pdw u w) i := rfl

theorem pdw_append (u : (Fin n → ℝ) → ℝ) (a b : List (Fin n)) :
    pdw (pdw u a) b = pdw u (b ++ a) := by
  induction b with
  | nil => rfl
  | cons i b ih => simp [ih]

theorem contDiff_pdw {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u) (w : List (Fin n)) :
    ContDiff ℝ ∞ (pdw u w) := by
  induction w with
  | nil => exact hu
  | cons i w ih => exact contDiff_pd ih i

/-- The words of length at most `s`. -/
def wordsUpTo (n s : ℕ) : Finset (List (Fin n)) :=
  (Finset.range (s + 1)).biUnion fun m => (Finset.univ : Finset (Fin m → Fin n)).image List.ofFn

theorem mem_wordsUpTo {s : ℕ} {w : List (Fin n)} : w ∈ wordsUpTo n s ↔ w.length ≤ s := by
  simp only [wordsUpTo, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨m, hm, f, rfl⟩
    simp only [List.length_ofFn]; omega
  · intro h
    exact ⟨w.length, by omega, fun i => w.get i, List.ofFn_get w⟩

/-- The decompositions of a word into two complementary subwords. -/
def splits : List (Fin n) → List (List (Fin n) × List (Fin n))
  | [] => [([], [])]
  | i :: w => (splits w).map (fun p => (i :: p.1, p.2)) ++ (splits w).map (fun p => (p.1, i :: p.2))

theorem length_splits (w : List (Fin n)) : (splits w).length = 2 ^ w.length := by
  induction w with
  | nil => rfl
  | cons i w ih => simp [splits, ih, pow_succ]; ring

theorem length_add_of_mem_splits {w : List (Fin n)} {p : List (Fin n) × List (Fin n)}
    (h : p ∈ splits w) : p.1.length + p.2.length = w.length := by
  induction w generalizing p with
  | nil => simp [splits] at h; subst h; rfl
  | cons i w ih =>
    simp only [splits, List.mem_append, List.mem_map] at h
    rcases h with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · have := ih hq; simp; omega
    · have := ih hq; simp; omega

/-- **The Leibniz rule along words** for smooth functions. -/
theorem pdw_mul {u v : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (w : List (Fin n)) (x : Fin n → ℝ) :
    pdw (fun y => u y * v y) w x = ((splits w).map fun p => pdw u p.1 x * pdw v p.2 x).sum := by
  induction w generalizing x with
  | nil => simp [splits]
  | cons i w ih =>
    have hfun : pdw (fun y => u y * v y) w =
        fun y => ((splits w).map fun p => pdw u p.1 y * pdw v p.2 y).sum := funext ih
    simp only [pdw_cons, hfun]
    have hd : ∀ p ∈ splits w, DifferentiableAt ℝ (fun y => pdw u p.1 y * pdw v p.2 y) x :=
      fun p _ => (((contDiff_pdw hu p.1).mul (contDiff_pdw hv p.2)).differentiable (by simp)) x
    -- derivative of a finite list sum
    have hsum : ∀ (L : List (List (Fin n) × List (Fin n))), (∀ p ∈ L, DifferentiableAt ℝ
        (fun y => pdw u p.1 y * pdw v p.2 y) x) →
        pd (fun y => (L.map fun p => pdw u p.1 y * pdw v p.2 y).sum) i x =
          (L.map fun p => pd (fun y => pdw u p.1 y * pdw v p.2 y) i x).sum := by
      intro L hL
      induction L with
      | nil => simp [pd]
      | cons p L ihL =>
        simp only [List.map_cons, List.sum_cons]
        have hp := hL p (List.mem_cons_self ..)
        have hL' : ∀ q ∈ L, DifferentiableAt ℝ (fun y => pdw u q.1 y * pdw v q.2 y) x :=
          fun q hq => hL q (List.mem_cons_of_mem _ hq)
        have hdl : DifferentiableAt ℝ (fun y => (L.map fun p => pdw u p.1 y * pdw v p.2 y).sum) x := by
          clear ihL
          induction L with
          | nil => simp
          | cons q L ihq =>
            simp only [List.map_cons, List.sum_cons]
            exact (hL' q (List.mem_cons_self ..)).add
              (ihq (fun r hr => hL r (by simp at hr ⊢; tauto)) fun r hr => hL' r (List.mem_cons_of_mem _ hr))
        rw [show (fun y => pdw u p.1 y * pdw v p.2 y +
            (L.map fun p => pdw u p.1 y * pdw v p.2 y).sum) =
            fun y => (fun y => pdw u p.1 y * pdw v p.2 y) y +
              (fun y => (L.map fun p => pdw u p.1 y * pdw v p.2 y).sum) y from rfl]
        rw [pd_add_real hp hdl, ihL (fun q hq => hL q (List.mem_cons_of_mem _ hq))]
    rw [hsum _ hd]
    have hpm : ∀ p ∈ splits w, pd (fun y => pdw u p.1 y * pdw v p.2 y) i x =
        pdw u (i :: p.1) x * pdw v p.2 x + pdw u p.1 x * pdw v (i :: p.2) x := by
      intro p _
      rw [pd_mul ((contDiff_pdw hu p.1).of_le (by simp)) ((contDiff_pdw hv p.2).of_le (by simp))]
      rfl
    rw [List.map_congr_left hpm, List.sum_map_add]
    simp only [splits, List.map_append, List.map_map, List.sum_append, Function.comp_def]

end Words

/-! ### The algebra estimate for smooth functions -/

section Estimate

variable (c : Fin 4 → ℝ) (r : ℝ)

/-- The classical `H^s(B)` norm `Σ_{|w| ≤ s} ‖∂^w u‖_{L²(B)}`. -/
def nW (s : ℕ) (u : (Fin 4 → ℝ) → ℝ) : ℝ≥0∞ :=
  ∑ w ∈ wordsUpTo 4 s, eLpNorm (pdw u w) 2 (volume.restrict (euclBall c r))

theorem eLpNorm_pdw_le_nW {s : ℕ} (u : (Fin 4 → ℝ) → ℝ) {w : List (Fin 4)} (hw : w.length ≤ s) :
    eLpNorm (pdw u w) 2 (volume.restrict (euclBall c r)) ≤ nW c r s u :=
  Finset.single_le_sum (f := fun w => eLpNorm (pdw u w) 2 (volume.restrict (euclBall c r)))
    (fun _ _ => zero_le) (mem_wordsUpTo.mpr hw)

/-- Sums over injective families of words of bounded length are bounded by `nW`. -/
theorem sum_image_le_nW {ι : Type*} [Fintype ι] {s : ℕ} (u : (Fin 4 → ℝ) → ℝ)
    {f : ι → List (Fin 4)} (hf : Function.Injective f) (hlen : ∀ i, (f i).length ≤ s) :
    ∑ i, eLpNorm (pdw u (f i)) 2 (volume.restrict (euclBall c r)) ≤ nW c r s u := by
  classical
  rw [← Finset.sum_image (f := fun w => eLpNorm (pdw u w) 2 (volume.restrict (euclBall c r)))
    (fun i _ j _ h => hf h)]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun w hw => ?_) (fun _ _ _ => zero_le)
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hw
  exact mem_wordsUpTo.mpr (hlen i)

/-- `n3` of a derivative is controlled by `nW` (at most `4 nW`). -/
theorem n3_pdw_le {s : ℕ} (u : (Fin 4 → ℝ) → ℝ) {a : List (Fin 4)} (ha : a.length + 3 ≤ s) :
    n3 c r (pdw u a) ≤ 4 * nW c r s u := by
  have h0 : eLpNorm (pdw u a) 2 (volume.restrict (euclBall c r)) ≤ nW c r s u :=
    eLpNorm_pdw_le_nW c r u (by omega)
  have h1 : ∑ i, eLpNorm (pd (pdw u a) i) 2 (volume.restrict (euclBall c r)) ≤ nW c r s u :=
    sum_image_le_nW c r u (f := fun i => i :: a) (fun i j h => (List.cons.inj h).1)
      (fun i => by simp; omega)
  have h2 : ∑ i, ∑ j, eLpNorm (pd (pd (pdw u a) i) j) 2 (volume.restrict (euclBall c r)) ≤
      nW c r s u := by
    rw [← Finset.sum_product']
    exact sum_image_le_nW c r u (f := fun p : Fin 4 × Fin 4 => p.2 :: p.1 :: a)
      (fun p q h => by
        have h' := List.cons.inj h
        have h'' := List.cons.inj h'.2
        exact Prod.ext h''.1 h'.1)
      (fun p => by simp; omega)
  have h3 : ∑ i, ∑ j, ∑ k, eLpNorm (pd (pd (pd (pdw u a) i) j) k) 2
      (volume.restrict (euclBall c r)) ≤ nW c r s u := by
    have e : ∑ i, ∑ j, ∑ k, eLpNorm (pd (pd (pd (pdw u a) i) j) k) 2
        (volume.restrict (euclBall c r)) =
        ∑ p : Fin 4 × Fin 4 × Fin 4, eLpNorm (pdw u (p.2.2 :: p.2.1 :: p.1 :: a)) 2
          (volume.restrict (euclBall c r)) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fintype.sum_prod_type]
      rfl
    rw [e]
    exact sum_image_le_nW c r u (f := fun p : Fin 4 × Fin 4 × Fin 4 => p.2.2 :: p.2.1 :: p.1 :: a)
      (fun p q h => by
        have h' := List.cons.inj h
        have h'' := List.cons.inj h'.2
        have h''' := List.cons.inj h''.2
        exact Prod.ext h'''.1 (Prod.ext h''.1 h'.1))
      (fun p => by simp; omega)
  unfold n3
  calc _ ≤ nW c r s u + nW c r s u + nW c r s u + nW c r s u := by gcongr
    _ = 4 * nW c r s u := by ring

end Estimate

section Estimate2

variable (c : Fin 4 → ℝ) (r : ℝ)

theorem memLp_ball_of_contDiff (hr : 0 < r) {f : (Fin 4 → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (p : ℝ≥0∞) : MemLp f p (volume.restrict (euclBall c r)) :=
  memLp_euclBall_of_continuous c hr.le hf.continuous p

theorem nW_lt_top (hr : 0 < r) {u : (Fin 4 → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u) (s : ℕ) :
    nW c r s u < ⊤ :=
  ENNReal.sum_lt_top.mpr fun w _ =>
    (memLp_ball_of_contDiff c r hr (contDiff_pdw hu w) 2).eLpNorm_lt_top

/-- `H³ ⊂ L^∞` for derivatives of order `≤ s - 3`. -/
theorem exists_sup_pdw_bound (hr : 0 < r) : ∃ C3 : ℝ≥0∞, C3 ≠ ⊤ ∧
    ∀ {s : ℕ} {u : (Fin 4 → ℝ) → ℝ} {a : List (Fin 4)}, ContDiff ℝ ∞ u → a.length + 3 ≤ s →
      ∀ x ∈ euclBall c r, ENNReal.ofReal |pdw u a x| ≤ C3 * nW c r s u := by
  obtain ⟨C, hC, hb⟩ := abs_le_n3 c r hr
  refine ⟨C * 4, ENNReal.mul_ne_top hC (by norm_num), fun hu ha x hx => ?_⟩
  refine (hb _ (contDiff_pdw hu _) x hx).trans ?_
  rw [mul_assoc]
  exact mul_le_mul' le_rfl (n3_pdw_le c r _ ha)

/-- `H¹ ⊂ L⁴` for derivatives of order `≤ s - 1`. -/
theorem exists_L4_pdw_bound (hr : 0 < r) : ∃ C4 : ℝ≥0∞, C4 ≠ ⊤ ∧
    ∀ {s : ℕ} {u : (Fin 4 → ℝ) → ℝ} {a : List (Fin 4)}, ContDiff ℝ ∞ u → a.length + 1 ≤ s →
      eLpNorm (pdw u a) 4 (volume.restrict (euclBall c r)) ≤ C4 * nW c r s u := by
  obtain ⟨CS, hCS⟩ := sobolev_ball_real (n := 4) (by norm_num) (p' := 4) (by norm_num)
  refine ⟨CS * (1 + ENNReal.ofReal r⁻¹), ENNReal.mul_ne_top ENNReal.coe_ne_top
    (ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, ENNReal.ofReal_ne_top⟩), fun {s u a} hu ha => ?_⟩
  have h := hCS c r hr (pdw u a) ((contDiff_pdw hu a).of_le (by simp))
  have h1 : ∑ i, eLpNorm (pd (pdw u a) i) 2 (volume.restrict (euclBall c r)) ≤ nW c r s u :=
    sum_image_le_nW c r u (f := fun i => i :: a) (fun i j h => (List.cons.inj h).1)
      (fun i => by simp; omega)
  have h2 : eLpNorm (pdw u a) 2 (volume.restrict (euclBall c r)) ≤ nW c r s u :=
    eLpNorm_pdw_le_nW c r u (by omega)
  refine h.trans ?_
  calc (CS : ℝ≥0∞) * (∑ i, eLpNorm (pd (pdw u a) i) 2 (volume.restrict (euclBall c r)) +
        ENNReal.ofReal r⁻¹ * eLpNorm (pdw u a) 2 (volume.restrict (euclBall c r)))
      ≤ CS * (nW c r s u + ENNReal.ofReal r⁻¹ * nW c r s u) := by gcongr
    _ = CS * (1 + ENNReal.ofReal r⁻¹) * nW c r s u := by ring

/-- The `L²` norm of a finite list sum of continuous functions is at most the sum of the norms. -/
theorem eLpNorm_list_sum_le {ι : Type*} (L : List ι) (F : ι → (Fin 4 → ℝ) → ℝ)
    (hF : ∀ i, Continuous (F i)) :
    eLpNorm (fun x => (L.map fun i => F i x).sum) 2 (volume.restrict (euclBall c r)) ≤
      (L.map fun i => eLpNorm (F i) 2 (volume.restrict (euclBall c r))).sum := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.map_cons, List.sum_cons]
    have hc : Continuous fun x => (L.map fun i => F i x).sum := by
      clear ih
      induction L with
      | nil => simp [continuous_const]
      | cons j L ihj => simp only [List.map_cons, List.sum_cons]; exact (hF j).add ihj
    refine (eLpNorm_add_le (f := F i) (g := fun x => (L.map fun i => F i x).sum)
      (hF i).aestronglyMeasurable hc.aestronglyMeasurable (by norm_num)).trans ?_
    gcongr

/-- **The bound on one Leibniz term** (`s ≥ 3`, `|a| + |b| ≤ s`). -/
theorem exists_term_bound (hr : 0 < r) : ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
    ∀ {s : ℕ}, 3 ≤ s → ∀ {u v : (Fin 4 → ℝ) → ℝ} {a b : List (Fin 4)}, ContDiff ℝ ∞ u →
      ContDiff ℝ ∞ v → a.length + b.length ≤ s →
      eLpNorm (fun x => pdw u a x * pdw v b x) 2 (volume.restrict (euclBall c r)) ≤
        K * nW c r s u * nW c r s v := by
  obtain ⟨C3, hC3, hsup⟩ := exists_sup_pdw_bound c r hr
  obtain ⟨C4, hC4, hL4⟩ := exists_L4_pdw_bound c r hr
  refine ⟨C3 + C3 + C4 * C4, by finiteness, fun {s} hs {u v a b} hu hv hab => ?_⟩
  have hBm := measurableSet_euclBall c r
  have hfin : ∀ {w : (Fin 4 → ℝ) → ℝ}, ContDiff ℝ ∞ w → C3 * nW c r s w ≠ ⊤ := fun hw =>
    ENNReal.mul_ne_top hC3 (nW_lt_top c r hr hw s).ne
  by_cases ha : a.length + 3 ≤ s
  · have hpt : ∀ᵐ x ∂(volume.restrict (euclBall c r)),
        ‖pdw u a x * pdw v b x‖ ≤ (C3 * nW c r s u).toReal * ‖pdw v b x‖ := by
      filter_upwards [ae_restrict_mem hBm] with x hx
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      exact (ENNReal.ofReal_le_iff_le_toReal (hfin hu)).mp (hsup hu ha x hx)
    refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hpt 2).trans ?_
    rw [ENNReal.ofReal_toReal (hfin hu)]
    calc C3 * nW c r s u * eLpNorm (pdw v b) 2 (volume.restrict (euclBall c r))
        ≤ C3 * nW c r s u * nW c r s v := by
          gcongr; exact eLpNorm_pdw_le_nW c r v (by omega)
      _ ≤ (C3 + C3 + C4 * C4) * nW c r s u * nW c r s v := by
          gcongr; exact le_add_right le_self_add
  by_cases hb : b.length + 3 ≤ s
  · have hpt : ∀ᵐ x ∂(volume.restrict (euclBall c r)),
        ‖pdw u a x * pdw v b x‖ ≤ (C3 * nW c r s v).toReal * ‖pdw u a x‖ := by
      filter_upwards [ae_restrict_mem hBm] with x hx
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      exact (ENNReal.ofReal_le_iff_le_toReal (hfin hv)).mp (hsup hv hb x hx)
    refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hpt 2).trans ?_
    rw [ENNReal.ofReal_toReal (hfin hv)]
    calc C3 * nW c r s v * eLpNorm (pdw u a) 2 (volume.restrict (euclBall c r))
        ≤ C3 * nW c r s v * nW c r s u := by
          gcongr; exact eLpNorm_pdw_le_nW c r u (by omega)
      _ = C3 * nW c r s u * nW c r s v := by ring
      _ ≤ (C3 + C3 + C4 * C4) * nW c r s u * nW c r s v := by
          gcongr; exact le_add_right le_add_self
  · have ha1 : a.length + 1 ≤ s := by omega
    have hb1 : b.length + 1 ≤ s := by omega
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
        ≤ (C4 * nW c r s u) * (C4 * nW c r s v) := by
          gcongr
          · exact hL4 hu ha1
          · exact hL4 hv hb1
      _ = C4 * C4 * nW c r s u * nW c r s v := by ring
      _ ≤ (C3 + C3 + C4 * C4) * nW c r s u * nW c r s v := by
          gcongr; exact le_add_self

/-- **The algebra estimate on `H^s(B)`, `s ≥ 3`, smooth functions** (balls of `ℝ⁴`):
`‖u v‖_{H^s(B)} ≤ C_s ‖u‖_{H^s(B)} ‖v‖_{H^s(B)}`. -/
theorem nW_mul_le (hr : 0 < r) : ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ {s : ℕ}, 3 ≤ s →
    ∀ {u v : (Fin 4 → ℝ) → ℝ}, ContDiff ℝ ∞ u → ContDiff ℝ ∞ v →
      nW c r s (fun x => u x * v x) ≤
        ((wordsUpTo 4 s).card * 2 ^ s : ℝ≥0∞) * K * nW c r s u * nW c r s v := by
  obtain ⟨K, hK, hterm⟩ := exists_term_bound c r hr
  refine ⟨K, hK, fun {s} hs {u v} hu hv => ?_⟩
  unfold nW
  have hw : ∀ w ∈ wordsUpTo 4 s,
      eLpNorm (pdw (fun x => u x * v x) w) 2 (volume.restrict (euclBall c r)) ≤
        2 ^ s * (K * (∑ w ∈ wordsUpTo 4 s, eLpNorm (pdw u w) 2 (volume.restrict (euclBall c r))) *
          ∑ w ∈ wordsUpTo 4 s, eLpNorm (pdw v w) 2 (volume.restrict (euclBall c r))) := by
    intro w hwmem
    have hlen := mem_wordsUpTo.mp hwmem
    have e : pdw (fun x => u x * v x) w =
        fun x => ((splits w).map fun p => pdw u p.1 x * pdw v p.2 x).sum :=
      funext (pdw_mul hu hv w)
    rw [e]
    refine (eLpNorm_list_sum_le c r (splits w) (fun p x => pdw u p.1 x * pdw v p.2 x)
      fun p => ((contDiff_pdw hu p.1).mul (contDiff_pdw hv p.2)).continuous).trans ?_
    have hbd : ∀ p ∈ splits w, eLpNorm (fun x => pdw u p.1 x * pdw v p.2 x) 2
        (volume.restrict (euclBall c r)) ≤ K * nW c r s u * nW c r s v := fun p hp =>
      hterm hs hu hv (by rw [length_add_of_mem_splits hp]; exact hlen)
    calc ((splits w).map fun p => eLpNorm (fun x => pdw u p.1 x * pdw v p.2 x) 2
          (volume.restrict (euclBall c r))).sum
        ≤ ((splits w).map fun _ => K * nW c r s u * nW c r s v).sum :=
          List.sum_le_sum fun p hp => hbd p hp
      _ = (splits w).length * (K * nW c r s u * nW c r s v) := by
          rw [List.map_const', List.sum_replicate, nsmul_eq_mul]
      _ ≤ 2 ^ s * (K * nW c r s u * nW c r s v) := by
          rw [length_splits]
          gcongr
          · push_cast; exact pow_le_pow_right₀ (by norm_num) hlen
  calc ∑ w ∈ wordsUpTo 4 s, eLpNorm (pdw (fun x => u x * v x) w) 2 (volume.restrict (euclBall c r))
      ≤ ∑ w ∈ wordsUpTo 4 s, 2 ^ s * (K * (∑ w ∈ wordsUpTo 4 s,
          eLpNorm (pdw u w) 2 (volume.restrict (euclBall c r))) *
            ∑ w ∈ wordsUpTo 4 s, eLpNorm (pdw v w) 2 (volume.restrict (euclBall c r))) :=
        Finset.sum_le_sum hw
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end Estimate2

/-! ### Closure: `H^s(B)` (weak) is an algebra -/

section Closure

theorem pdw_add {u v : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (w : List (Fin n)) : pdw (fun x => u x + v x) w = fun x => pdw u w x + pdw v w x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext x
    simp only [pdw_cons, ih]
    exact pd_add_real (((contDiff_pdw hu w).differentiable (by simp)) x)
      (((contDiff_pdw hv w).differentiable (by simp)) x) i

theorem pdw_sub {u v : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (w : List (Fin n)) : pdw (fun x => u x - v x) w = fun x => pdw u w x - pdw v w x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext x
    simp only [pdw_cons, ih]
    exact pd_sub_real (((contDiff_pdw hu w).differentiable (by simp)) x)
      (((contDiff_pdw hv w).differentiable (by simp)) x) i

/-- Limits of the derivatives along words, for a `ConvHk` sequence. -/
theorem ConvHk.exists_word_limit {Ω : Set (Fin n → ℝ)} : ∀ {k : ℕ} {φ : ℕ → (Fin n → ℝ) → ℝ}
    {u : (Fin n → ℝ) → ℝ}, ConvHk Ω k φ u → ∀ w : List (Fin n), w.length ≤ k →
      ∃ g, MemLp g 2 (volume.restrict Ω) ∧
        Tendsto (fun m => eLpNorm (pdw (φ m) w - g) 2 (volume.restrict Ω)) atTop (𝓝 0) := by
  intro k
  induction k with
  | zero =>
    intro φ u h w hw
    obtain rfl : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact ⟨u, h.1, h.2⟩
  | succ k ih =>
    intro φ u h w hw
    rcases List.eq_nil_or_concat w with rfl | ⟨w', i, rfl⟩
    · exact ⟨u, h.1.1, h.1.2⟩
    · obtain ⟨g, hg⟩ := h.2 i
      have hlen : w'.length ≤ k := by rw [List.length_concat] at hw; omega
      obtain ⟨g', hg'⟩ := ih hg w' hlen
      refine ⟨g', hg'.1, ?_⟩
      have e : ∀ m, pdw (φ m) (w'.concat i) = pdw (pd (φ m) i) w' := fun m => by
        rw [List.concat_eq_append, ← pdw_append]; rfl
      simpa only [e] using hg'.2

/-- Completeness of `L²` in the form used below. -/
theorem exists_limit_of_cauchy {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} (hf : ∀ m, MemLp (f m) 2 μ)
    (h : Tendsto (fun q : ℕ × ℕ => eLpNorm (f q.1 - f q.2) 2 μ) atTop (𝓝 0)) :
    ∃ g, MemLp g 2 μ ∧ Tendsto (fun m => eLpNorm (f m - g) 2 μ) atTop (𝓝 0) := by
  have hc : CauchySeq fun m => (hf m).toLp (f m) := by
    rw [cauchySeq_iff_tendsto_dist_atTop_0]
    have e : (fun q : ℕ × ℕ => dist ((hf q.1).toLp (f q.1)) ((hf q.2).toLp (f q.2))) =
        fun q => (eLpNorm (f q.1 - f q.2) 2 μ).toReal := by
      funext q
      rw [dist_eq_norm, ← MemLp.toLp_sub, Lp.norm_toLp]
    rw [e, ← ENNReal.toReal_zero]
    exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨G, Lp.memLp G, ?_⟩
  have := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ G).mp hG
  refine this.congr fun m => eLpNorm_congr_ae ?_
  filter_upwards [(hf m).coeFn_toLp] with x hx
  simp [hx]

/-- Smooth sequences whose derivatives along words of length `≤ k` are Cauchy in `L²(B)` converge
in the sense of `ConvHk`. -/
theorem exists_convHk_of_cauchy [NeZero n] (c : Fin n → ℝ) {r : ℝ} (hr : 0 ≤ r) : ∀ (k : ℕ)
    {Φ : ℕ → (Fin n → ℝ) → ℝ}, (∀ m, ContDiff ℝ ∞ (Φ m)) →
    (∀ w : List (Fin n), w.length ≤ k → Tendsto (fun q : ℕ × ℕ =>
      eLpNorm (pdw (Φ q.1) w - pdw (Φ q.2) w) 2 (volume.restrict (euclBall c r))) atTop (𝓝 0)) →
    ∃ U, ConvHk (euclBall c r) k Φ U := by
  intro k
  induction k with
  | zero =>
    intro Φ hΦ h
    obtain ⟨U, hU⟩ := exists_limit_of_cauchy
      (fun m => memLp_euclBall_of_continuous c hr (hΦ m).continuous 2) (h [] (by simp))
    exact ⟨U, hU⟩
  | succ k ih =>
    intro Φ hΦ h
    obtain ⟨U, hU⟩ := exists_limit_of_cauchy
      (fun m => memLp_euclBall_of_continuous c hr (hΦ m).continuous 2) (h [] (by simp))
    refine ⟨U, hU, fun i => ?_⟩
    obtain ⟨g, hg⟩ := ih (Φ := fun m => pd (Φ m) i) (fun m => contDiff_pd (hΦ m) i) fun w hw => by
      have e : ∀ m, pdw (pd (Φ m) i) w = pdw (Φ m) (w ++ [i]) := fun m => pdw_append (Φ m) [i] w
      simp only [e]
      exact h (w ++ [i]) (by simp; omega)
    exact ⟨g, hg⟩

variable (c : Fin 4 → ℝ) (r : ℝ)

theorem nW_add_le {u v : (Fin 4 → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (s : ℕ) :
    nW c r s (fun x => u x + v x) ≤ nW c r s u + nW c r s v := by
  unfold nW
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun w _ => ?_
  rw [pdw_add hu hv w]
  exact eLpNorm_add_le (contDiff_pdw hu w).continuous.aestronglyMeasurable
    (contDiff_pdw hv w).continuous.aestronglyMeasurable (by norm_num)

/-- Bilinear difference estimate. -/
theorem nW_mul_sub_le {s : ℕ} {C : ℝ≥0∞}
    (hmul : ∀ {u v : (Fin 4 → ℝ) → ℝ}, ContDiff ℝ ∞ u → ContDiff ℝ ∞ v →
      nW c r s (fun x => u x * v x) ≤ C * nW c r s u * nW c r s v)
    {a b a' b' : (Fin 4 → ℝ) → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (ha' : ContDiff ℝ ∞ a') (hb' : ContDiff ℝ ∞ b') :
    nW c r s (fun x => a x * b x - a' x * b' x) ≤
      C * nW c r s (fun x => a x - a' x) * nW c r s b +
        C * nW c r s a' * nW c r s (fun x => b x - b' x) := by
  have e : (fun x => a x * b x - a' x * b' x) =
      fun x => (fun y => (a y - a' y) * b y) x + (fun y => a' y * (b y - b' y)) x := by
    funext x; ring
  rw [e]
  refine (nW_add_le c r ((ha.sub ha').mul hb) (ha'.mul (hb.sub hb')) s).trans ?_
  exact add_le_add (hmul (ha.sub ha') hb) (hmul ha' (hb.sub hb'))

theorem eLpNorm_sub_le_via {μ : Measure (Fin 4 → ℝ)} {a b g : (Fin 4 → ℝ) → ℝ}
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (hg : AEStronglyMeasurable g μ) :
    eLpNorm (fun x => a x - b x) 2 μ ≤ eLpNorm (a - g) 2 μ + eLpNorm (b - g) 2 μ := by
  have e : (fun x => a x - b x) = (a - g) - (b - g) := by funext x; simp
  rw [e]
  exact eLpNorm_sub_le (ha.sub hg) (hb.sub hg) (by norm_num)

theorem eLpNorm_le_via {μ : Measure (Fin 4 → ℝ)} {a g : (Fin 4 → ℝ) → ℝ}
    (ha : AEStronglyMeasurable a μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm a 2 μ ≤ eLpNorm (a - g) 2 μ + eLpNorm g 2 μ := by
  have e : a = (a - g) + g := by funext x; simp
  conv_lhs => rw [e]
  exact eLpNorm_add_le (ha.sub hg) hg (by norm_num)

end Closure

section Algebra

variable (c : Fin 4 → ℝ) (r : ℝ)

theorem tendsto_fst_nat : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop :=
  tendsto_atTop_atTop_of_monotone (fun _ _ h => h.1) fun b => ⟨(b, 0), le_rfl⟩

theorem tendsto_snd_nat : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop :=
  tendsto_atTop_atTop_of_monotone (fun _ _ h => h.2) fun b => ⟨(0, b), le_rfl⟩

/-- Word-wise limits of a weak `H^s` function's smooth approximants, packaged with the
two estimates used in the closure argument. -/
theorem exists_word_data (_hr : 0 < r) {s : ℕ} {φ : ℕ → (Fin 4 → ℝ) → ℝ}
    (hφ : ∀ m, ContDiff ℝ ∞ (φ m)) {u : (Fin 4 → ℝ) → ℝ}
    (hc : ConvHk (euclBall c r) s φ u) :
    ∃ D : ℕ → ℝ≥0∞, ∃ G : ℝ≥0∞, G ≠ ⊤ ∧ Tendsto D atTop (𝓝 0) ∧
      (∀ m p, nW c r s (fun x => φ m x - φ p x) ≤ D m + D p) ∧
      (∀ m, nW c r s (φ m) ≤ G + D m) := by
  have hex : ∀ w : List (Fin 4), ∃ g : (Fin 4 → ℝ) → ℝ, w.length ≤ s →
      MemLp g 2 (volume.restrict (euclBall c r)) ∧
      Tendsto (fun m => eLpNorm (pdw (φ m) w - g) 2 (volume.restrict (euclBall c r)))
        atTop (𝓝 0) := by
    intro w
    by_cases hw : w.length ≤ s
    · obtain ⟨g, hg⟩ := hc.exists_word_limit w hw
      exact ⟨g, fun _ => hg⟩
    · exact ⟨0, fun h => absurd h hw⟩
  choose g hg using hex
  refine ⟨fun m => ∑ w ∈ wordsUpTo 4 s,
      eLpNorm (pdw (φ m) w - g w) 2 (volume.restrict (euclBall c r)),
    ∑ w ∈ wordsUpTo 4 s, eLpNorm (g w) 2 (volume.restrict (euclBall c r)), ?_, ?_, ?_, ?_⟩
  · exact (ENNReal.sum_lt_top.mpr fun w hw =>
      (hg w (mem_wordsUpTo.mp hw)).1.eLpNorm_lt_top).ne
  · have := tendsto_finsetSum (wordsUpTo 4 s) fun w hw => (hg w (mem_wordsUpTo.mp hw)).2
    simpa using this
  · intro m p
    unfold nW
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun w hw => ?_
    rw [pdw_sub (hφ m) (hφ p) w]
    exact eLpNorm_sub_le_via (contDiff_pdw (hφ m) w).continuous.aestronglyMeasurable
      (contDiff_pdw (hφ p) w).continuous.aestronglyMeasurable
      (hg w (mem_wordsUpTo.mp hw)).1.aestronglyMeasurable
  · intro m
    unfold nW
    rw [add_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun w hw => ?_
    exact eLpNorm_le_via (contDiff_pdw (hφ m) w).continuous.aestronglyMeasurable
      (hg w (mem_wordsUpTo.mp hw)).1.aestronglyMeasurable

/-- **`H^s(B)` is an algebra** (`B` a ball of `ℝ⁴`, `s ≥ 3`, weak Sobolev spaces):
`u, v ∈ H^s(B) ⟹ u v ∈ H^s(B)`. -/
theorem memHk_mul (hr : 0 < r) {s : ℕ} (hs : 3 ≤ s) {u v : (Fin 4 → ℝ) → ℝ}
    (hu : MemHk (euclBall c r) s u) (hv : MemHk (euclBall c r) s v) :
    MemHk (euclBall c r) s (fun x => u x * v x) := by
  have : Fact (0 < r) := ⟨hr⟩
  obtain ⟨K, hK, hmul0⟩ := nW_mul_le c r hr
  obtain ⟨C, hC⟩ : ∃ C : ℝ≥0∞, C = ((wordsUpTo 4 s).card * 2 ^ s : ℝ≥0∞) * K := ⟨_, rfl⟩
  have hCt : C ≠ ⊤ := by rw [hC]; finiteness
  have hmul : ∀ {u v : (Fin 4 → ℝ) → ℝ}, ContDiff ℝ ∞ u → ContDiff ℝ ∞ v →
      nW c r s (fun x => u x * v x) ≤ C * nW c r s u * nW c r s v := fun hu hv => by
    rw [hC]; exact hmul0 hs hu hv
  obtain ⟨φ, hφ, hcu⟩ := (memHk_iff_exists_convHk c r s).mp hu
  obtain ⟨ψ, hψ, hcv⟩ := (memHk_iff_exists_convHk c r s).mp hv
  obtain ⟨Du, Gu, hGu, hDu, hdu, hbu⟩ := exists_word_data c r hr hφ hcu
  obtain ⟨Dv, Gv, hGv, hDv, hdv, hbv⟩ := exists_word_data c r hr hψ hcv
  have hΦ : ∀ m, ContDiff ℝ ∞ (fun x => φ m x * ψ m x) := fun m => (hφ m).mul (hψ m)
  -- the products are Cauchy in every derivative of order `≤ s`
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
  have hcauchy : ∀ w : List (Fin 4), w.length ≤ s → Tendsto (fun q : ℕ × ℕ =>
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
    refine (nW_mul_sub_le c r hmul (hφ q.1) (hψ q.1) (hφ q.2) (hψ q.2)).trans ?_
    rw [mul_assoc, mul_assoc]
    gcongr
    · exact hdu q.1 q.2
    · exact hbv q.1
    · exact hbu q.2
    · exact hdv q.1 q.2
  obtain ⟨U, hU⟩ := exists_convHk_of_cauchy c hr.le s hΦ hcauchy
  have hUm : MemHk (euclBall c r) s U := (memHk_iff_exists_convHk c r s).mpr ⟨_, hΦ, hU⟩
  -- identification of the limit: `U = u v` a.e.
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
      exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) (hΦm.sub hUb.1.aestronglyMeasurable)
    · rw [e2]
      refine (eLpNorm_add_le ((hφm.sub hub.1.aestronglyMeasurable).smul hψm)
        (hub.1.aestronglyMeasurable.smul (hψm.sub hvb.1.aestronglyMeasurable)) le_rfl).trans ?_
      gcongr
      · refine (eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) hψm
          (hφm.sub hub.1.aestronglyMeasurable)).trans ?_
        gcongr
        have := eLpNorm_le_via hψm hvb.1.aestronglyMeasurable
        exact this
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

end Algebra

/-! ### Complex and matrix-valued `H^s(B)` -/

section Matrix

variable (c : Fin 4 → ℝ) (r : ℝ)

/-- A complex function is in `H^s(B)` iff its real and imaginary parts are. -/
def MemHkC (s : ℕ) (f : (Fin 4 → ℝ) → ℂ) : Prop :=
  MemHk (euclBall c r) s (fun x => (f x).re) ∧ MemHk (euclBall c r) s (fun x => (f x).im)

theorem MemHkC.add {s : ℕ} {f g : (Fin 4 → ℝ) → ℂ} (hf : MemHkC c r s f) (hg : MemHkC c r s g) :
    MemHkC c r s (fun x => f x + g x) := by
  refine ⟨?_, ?_⟩
  · simpa using hf.1.add hg.1
  · simpa using hf.2.add hg.2

theorem MemHkC.mul (hr : 0 < r) {s : ℕ} (hs : 3 ≤ s) {f g : (Fin 4 → ℝ) → ℂ}
    (hf : MemHkC c r s f) (hg : MemHkC c r s g) : MemHkC c r s (fun x => f x * g x) := by
  refine ⟨?_, ?_⟩
  · simpa using (memHk_mul c r hr hs hf.1 hg.1).sub (memHk_mul c r hr hs hf.2 hg.2)
  · simpa using (memHk_mul c r hr hs hf.1 hg.2).add (memHk_mul c r hr hs hf.2 hg.1)

theorem MemHkC.sum {s : ℕ} {ι : Type*} (t : Finset ι) {f : ι → (Fin 4 → ℝ) → ℂ}
    (hf : ∀ k ∈ t, MemHkC c r s (f k)) : MemHkC c r s (fun x => ∑ k ∈ t, f k x) := by
  refine ⟨?_, ?_⟩
  · simpa [Complex.re_sum] using MemHk.sum' t fun k hk => (hf k hk).1
  · simpa [Complex.im_sum] using MemHk.sum' t fun k hk => (hf k hk).2

/-- **`H^s(B, M_m(ℂ))` is an algebra** (`B` a ball of `ℝ⁴`, `s ≥ 3`): entrywise `H^s` matrix
fields are closed under pointwise matrix multiplication. -/
theorem memHkC_matrix_mul (hr : 0 < r) {s : ℕ} (hs : 3 ≤ s) {m : ℕ}
    {A B : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ}
    (hA : ∀ i j, MemHkC c r s (fun x => A x i j)) (hB : ∀ i j, MemHkC c r s (fun x => B x i j)) :
    ∀ i j, MemHkC c r s (fun x => (A x * B x) i j) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact MemHkC.sum c r _ fun k _ => (hA i k).mul c r hr hs (hB k j)

end Matrix

/-- Smooth functions belong to every `H^k(B)`. -/
theorem memHk_of_contDiff (c : Fin 4 → ℝ) {r : ℝ} (hr : 0 ≤ r) (k : ℕ) :
    ∀ {u : (Fin 4 → ℝ) → ℝ}, ContDiff ℝ ∞ u → MemHk (euclBall c r) k u := by
  induction k with
  | zero => intro u hu; exact memLp_euclBall_of_continuous c hr hu.continuous 2
  | succ k ih =>
    intro u hu
    exact ⟨memLp_euclBall_of_continuous c hr hu.continuous 2, fun i =>
      ⟨pd u i, hasWeakPartialR_of_contDiff _ (hu.of_le (by simp)) i, ih (contDiff_pd hu i)⟩⟩

/-! ### Non-vacuity -/

/-- The algebra property applied to two non-trivial `H³` functions on the unit ball of `ℝ⁴`. -/
example : MemHk (euclBall (0 : Fin 4 → ℝ) 1) 3 (fun x => (x 0 + 1) * x 1 ^ 2) :=
  memHk_mul (0 : Fin 4 → ℝ) 1 one_pos le_rfl
    (memHk_of_contDiff 0 zero_le_one 3 (by fun_prop))
    (memHk_of_contDiff 0 zero_le_one 3 (by fun_prop))

/-- The algebra estimate is non-vacuous: its constant is finite. -/
example : ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ {s : ℕ}, 3 ≤ s →
    ∀ {u v : (Fin 4 → ℝ) → ℝ}, ContDiff ℝ ∞ u → ContDiff ℝ ∞ v →
      nW 0 1 s (fun x => u x * v x) ≤
        ((wordsUpTo 4 s).card * 2 ^ s : ℝ≥0∞) * K * nW 0 1 s u * nW 0 1 s v :=
  nW_mul_le 0 1 one_pos

end RenewalGeometry.BallAnalysis.BallReg
