/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Graph.RecordOrientation

/-!
# Determinant crossings, jets, and orientation stability

Covers `prop:det-crossing`, `prop:det-jet`, and
`prop:noisy-record-sign-stability` from `manuscripts/renewal_emergence/renewal_emergence.tex`.

* `jet_sign` / `jet_flip_parity`: if the first `m − 1` derivatives of
  a `C^m` real function vanish at `t₀` and the `m`-th does not, the
  function is nonvanishing in a punctured neighbourhood and its sign
  flips across `t₀` **iff `m` is odd** (proved by induction on `m`
  through the mean value theorem — no Taylor machinery needed).
* `det_transverse_crossing`: the `m = 1` case for determinant paths —
  a transverse zero of `det L(t)` flips the orientation sign.
* `det_crossing_parity`: for a determinant path with finitely many
  transverse crossings, the endpoint orientations differ by exactly
  the crossing parity, `orSign(det L b) = orSign(det L a) + N mod 2`;
  since the endpoints determine the parity, it is unchanged by any
  perturbation fixing the endpoint signs.
* `det_sign_locally_constant`: along a continuous determinant-regular
  family, the orientation sign is locally constant — it can change
  only through a rank-loss locus `det = 0`.
-/

namespace NCG

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Filter Set

/-! ## `ℤ/2` sign arithmetic -/

theorem orSign_neg {x : ℝ} (hx : x ≠ 0) :
    orSign (-x) = orSign x + 1 := by
  rcases lt_or_gt_of_ne hx with h | h
  · rw [orSign, orSign, if_pos (neg_pos.mpr h),
      if_neg (not_lt.mpr h.le)]
    decide
  · rw [orSign, orSign, if_neg (not_lt.mpr (neg_nonpos.mpr h.le)),
      if_pos h]
    decide

theorem orSign_eq_of_mul_pos {x y : ℝ} (h : 0 < x * y) :
    orSign x = orSign y := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hy : y < 0 := by nlinarith
    rw [orSign, orSign, if_neg (not_lt.mpr hx.le),
      if_neg (not_lt.mpr hy.le)]
  · exfalso
    rw [hx, zero_mul] at h
    exact lt_irrefl 0 h
  · have hy : 0 < y := by nlinarith
    rw [orSign, orSign, if_pos hx, if_pos hy]

theorem orSign_eq_add_one_of_mul_neg {x y : ℝ} (h : x * y < 0) :
    orSign x = orSign y + 1 := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hy : 0 < y := by nlinarith
    rw [orSign, orSign, if_neg (not_lt.mpr hx.le), if_pos hy]
    decide
  · exfalso
    rw [hx, zero_mul] at h
    exact lt_irrefl 0 h
  · have hy : y < 0 := by nlinarith
    rw [orSign, orSign, if_pos hx, if_neg (not_lt.mpr hy.le)]
    decide

theorem mul_neg_iff_orSign_ne {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    x * y < 0 ↔ orSign x ≠ orSign y := by
  constructor
  · intro h heq
    have h1 := orSign_eq_add_one_of_mul_neg h
    rw [heq] at h1
    have h2 : orSign y + 1 = orSign y + 0 := by
      rw [add_zero]
      exact h1.symm
    have h3 := add_left_cancel h2
    exact absurd h3 (by decide)
  · intro h
    rcases lt_trichotomy (x * y) 0 with hlt | heq | hgt
    · exact hlt
    · exfalso
      rcases mul_eq_zero.mp heq with h0 | h0
      exacts [hx h0, hy h0]
    · exact absurd (orSign_eq_of_mul_pos hgt) h

theorem natCast_zmodTwo_even {m : ℕ} (h : Even m) :
    (m : ZMod 2) = 0 := by
  obtain ⟨k, rfl⟩ := h
  push_cast
  rw [← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul]

theorem natCast_zmodTwo_odd {m : ℕ} (h : Odd m) :
    (m : ZMod 2) = 1 := by
  obtain ⟨k, rfl⟩ := h
  push_cast
  rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]

/-- Same-sign control within a relative-error ball. -/
theorem orSign_of_dist_lt {u c : ℝ} (h : |u - c| < |c|) :
    u ≠ 0 ∧ orSign u = orSign c := by
  rcases lt_trichotomy c 0 with hc | hc | hc
  · have h1 := abs_lt.mp h
    rw [abs_of_neg hc] at h1
    have hu : u < 0 := by linarith [h1.2]
    exact ⟨hu.ne, by
      rw [orSign, orSign, if_neg (not_lt.mpr hu.le),
        if_neg (not_lt.mpr hc.le)]⟩
  · exfalso
    rw [hc, abs_zero] at h
    linarith [abs_nonneg (u - 0)]
  · have h1 := abs_lt.mp h
    rw [abs_of_pos hc] at h1
    have hu : 0 < u := by linarith [h1.1]
    exact ⟨hu.ne', by rw [orSign, orSign, if_pos hu, if_pos hc]⟩

/-! ## Sign constancy on zero-free intervals -/

theorem sign_mul_pos_of_forall_ne {f : ℝ → ℝ} (hf : Continuous f)
    {a b : ℝ} (hab : a ≤ b) (h : ∀ x ∈ Set.Icc a b, f x ≠ 0) :
    0 < f a * f b := by
  have hfa := h a (Set.left_mem_Icc.mpr hab)
  have hfb := h b (Set.right_mem_Icc.mpr hab)
  rcases lt_or_gt_of_ne hfa with ha | ha <;>
    rcases lt_or_gt_of_ne hfb with hb | hb
  · exact mul_pos_of_neg_of_neg ha hb
  · exfalso
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hab
      hf.continuousOn (Set.mem_Icc.mpr ⟨ha.le, hb.le⟩)
    exact h c hc hc0
  · exfalso
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hab
      hf.continuousOn (Set.mem_Icc.mpr ⟨hb.le, ha.le⟩)
    exact h c hc hc0
  · exact mul_pos ha hb

theorem orSign_eq_of_forall_ne {f : ℝ → ℝ} (hf : Continuous f)
    {a b : ℝ} (hab : a ≤ b) (h : ∀ x ∈ Set.Icc a b, f x ≠ 0) :
    orSign (f a) = orSign (f b) :=
  orSign_eq_of_mul_pos (sign_mul_pos_of_forall_ne hf hab h)

/-! ## The jet sign law (`prop:det-jet` core) -/

/-- **Jet sign law**: if the first `m − 1` derivatives vanish at `t₀`
and the `m`-th does not, then near `t₀` the function is nonvanishing
off `t₀`, carries the sign of the `m`-th derivative on the right, and
that sign shifted by `m` (mod 2) on the left.  Proved by induction on
`m` through the mean value theorem. -/
theorem jet_sign : ∀ m : ℕ, 1 ≤ m → ∀ {f : ℝ → ℝ} {t₀ : ℝ},
    ContDiff ℝ m f → (∀ k, k < m → iteratedDeriv k f t₀ = 0) →
    iteratedDeriv m f t₀ ≠ 0 →
    ∃ δ > 0,
      (∀ t, t₀ < t → t < t₀ + δ →
        f t ≠ 0 ∧ orSign (f t) = orSign (iteratedDeriv m f t₀))
      ∧ (∀ t, t₀ - δ < t → t < t₀ →
        f t ≠ 0 ∧ orSign (f t)
          = orSign (iteratedDeriv m f t₀) + (m : ZMod 2)) := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ n ih =>
    intro _ f t₀ hf hvan hc
    have hf0 : f t₀ = 0 := by
      have h0 := hvan 0 (by omega)
      rwa [iteratedDeriv_zero] at h0
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · -- base case m = 1: the slope argument
      have hdiff : DifferentiableAt ℝ f t₀ :=
        (hf.differentiable (by simp)).differentiableAt
      have hder : HasDerivAt f (iteratedDeriv (0 + 1) f t₀) t₀ := by
        have h2 := hdiff.hasDerivAt
        rwa [show iteratedDeriv (0 + 1) f = deriv f from
          iteratedDeriv_one]
      have hslope := hasDerivAt_iff_tendsto_slope.mp hder
      have hball := hslope (Metric.ball_mem_nhds _ (abs_pos.mpr hc))
      rw [Filter.mem_map, Metric.mem_nhdsWithin_iff] at hball
      obtain ⟨δ, hδ, hδprop⟩ := hball
      refine ⟨δ, hδ, ?_, ?_⟩
      · intro t ht1 ht2
        have hmem : t ∈ Metric.ball t₀ δ ∩ {t₀}ᶜ := by
          constructor
          · rw [Metric.mem_ball, Real.dist_eq,
              abs_of_pos (by linarith : (0:ℝ) < t - t₀)]
            linarith
          · exact fun h => by simp at h; linarith [h]
        have hs := hδprop hmem
        rw [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hs
        obtain ⟨hsne, hseq⟩ := orSign_of_dist_lt hs
        have hne : t - t₀ ≠ 0 := by
          intro h
          linarith [sub_eq_zero.mp h]
        have hft : f t = slope f t₀ t * (t - t₀) := by
          rw [slope_def_field, hf0, sub_zero, div_mul_cancel₀ _ hne]
        constructor
        · rw [hft]
          exact mul_ne_zero hsne hne
        · rw [hft, orSign_mul hsne hne, hseq,
            show orSign (t - t₀) = 0 from
              if_pos (by linarith : (0:ℝ) < t - t₀), add_zero]
      · intro t ht1 ht2
        have hmem : t ∈ Metric.ball t₀ δ ∩ {t₀}ᶜ := by
          constructor
          · rw [Metric.mem_ball, Real.dist_eq,
              abs_of_neg (by linarith : t - t₀ < 0)]
            linarith
          · exact fun h => by simp at h; linarith [h]
        have hs := hδprop hmem
        rw [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hs
        obtain ⟨hsne, hseq⟩ := orSign_of_dist_lt hs
        have hne : t - t₀ ≠ 0 := by
          intro h
          linarith [sub_eq_zero.mp h]
        have hft : f t = slope f t₀ t * (t - t₀) := by
          rw [slope_def_field, hf0, sub_zero, div_mul_cancel₀ _ hne]
        constructor
        · rw [hft]
          exact mul_ne_zero hsne hne
        · rw [hft, orSign_mul hsne hne, hseq,
            show orSign (t - t₀) = 1 from
              if_neg (not_lt.mpr (by linarith : t - t₀ ≤ 0))]
          norm_num
    · -- inductive step through the mean value theorem
      have hcast : ((n + 1 : ℕ) : WithTop ℕ∞)
          = (n : WithTop ℕ∞) + 1 := by
        push_cast
        rfl
      have hf1 : ContDiff ℝ ((n : WithTop ℕ∞) + 1) f := by
        rwa [hcast] at hf
      have hf' : ContDiff ℝ n (deriv f) :=
        (contDiff_succ_iff_deriv.mp hf1).2.2
      have hvan' : ∀ k, k < n → iteratedDeriv k (deriv f) t₀ = 0 := by
        intro k hk
        have h1 := hvan (k + 1) (by omega)
        rwa [iteratedDeriv_succ'] at h1
      have hc' : iteratedDeriv n (deriv f) t₀ ≠ 0 := by
        have h1 := hc
        rwa [iteratedDeriv_succ'] at h1
      obtain ⟨δ, hδ, hR, hL⟩ := ih hn hf' hvan' hc'
      have hdiff : Differentiable ℝ f := by
        refine hf.differentiable ?_
        exact_mod_cast Nat.succ_ne_zero n
      refine ⟨δ, hδ, ?_, ?_⟩
      · intro t ht1 ht2
        obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope f (deriv f)
          ht1 hdiff.continuous.continuousOn
          (fun x _ => (hdiff x).hasDerivAt)
        have hξmem := hR ξ hξ.1 (by linarith [hξ.2])
        have hne : t - t₀ ≠ 0 := by
          intro h
          linarith [sub_eq_zero.mp h]
        have hft : f t = deriv f ξ * (t - t₀) := by
          rw [hξeq, hf0, sub_zero, div_mul_cancel₀ _ hne]
        constructor
        · rw [hft]
          exact mul_ne_zero hξmem.1 hne
        · rw [hft, orSign_mul hξmem.1 hne, hξmem.2,
            show orSign (t - t₀) = 0 from
              if_pos (by linarith : (0:ℝ) < t - t₀), add_zero,
            ← iteratedDeriv_succ']
      · intro t ht1 ht2
        obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope f (deriv f)
          ht2 hdiff.continuous.continuousOn
          (fun x _ => (hdiff x).hasDerivAt)
        have hξmem := hL ξ (by linarith [hξ.1]) hξ.2
        have htt : (0:ℝ) < t₀ - t := by linarith
        have hft : f t = -(deriv f ξ * (t₀ - t)) := by
          rw [hξeq, hf0, zero_sub, neg_div,
            neg_mul, div_mul_cancel₀ _ htt.ne', neg_neg]
        constructor
        · rw [hft]
          exact neg_ne_zero.mpr (mul_ne_zero hξmem.1 htt.ne')
        · rw [hft, orSign_neg (mul_ne_zero hξmem.1 htt.ne'),
            orSign_mul hξmem.1 htt.ne', hξmem.2,
            show orSign (t₀ - t) = 0 from if_pos htt, add_zero,
            ← iteratedDeriv_succ']
          push_cast
          ring

/-- **Proposition `prop:det-jet` (sign-change criterion)**: with the
first nonzero jet of order `m`, the function is nonvanishing off `t₀`
nearby, and the sign changes across `t₀` **iff `m` is odd**. -/
theorem jet_flip_parity {f : ℝ → ℝ} {t₀ : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hf : ContDiff ℝ m f)
    (hvan : ∀ k, k < m → iteratedDeriv k f t₀ = 0)
    (hc : iteratedDeriv m f t₀ ≠ 0) :
    ∃ δ > 0, (∀ t, t ≠ t₀ → |t - t₀| < δ → f t ≠ 0)
      ∧ ∀ s t, t₀ - δ < s → s < t₀ → t₀ < t → t < t₀ + δ →
        (f s * f t < 0 ↔ Odd m) := by
  obtain ⟨δ, hδ, hR, hL⟩ := jet_sign m hm hf hvan hc
  refine ⟨δ, hδ, ?_, ?_⟩
  · intro t ht hdist
    have h1 := abs_lt.mp hdist
    rcases lt_or_gt_of_ne ht with h | h
    · exact (hL t (by linarith [h1.1]) h).1
    · exact (hR t h (by linarith [h1.2])).1
  · intro s t hs1 hs2 ht1 ht2
    obtain ⟨hsne, hseq⟩ := hL s hs1 hs2
    obtain ⟨htne, hteq⟩ := hR t ht1 ht2
    rw [mul_neg_iff_orSign_ne hsne htne, hseq, hteq]
    constructor
    · intro h
      by_contra heven
      rw [Nat.not_odd_iff_even] at heven
      rw [natCast_zmodTwo_even heven, add_zero] at h
      exact h rfl
    · intro hodd heq
      rw [natCast_zmodTwo_odd hodd] at heq
      have h2 : orSign (iteratedDeriv m f t₀) + 1
          = orSign (iteratedDeriv m f t₀) + 0 := by
        rw [add_zero]
        exact heq
      have h3 := add_left_cancel h2
      exact absurd h3 (by decide)

/-! ## Crossing parity along an interval -/

/-- Auxiliary induction: the endpoint orientation difference counts
the transversal crossings mod 2. -/
theorem crossing_parity_aux {f : ℝ → ℝ} (hcont : Continuous f)
    {a : ℝ} :
    ∀ (N : ℕ) (Z : Finset ℝ) (b : ℝ), Z.card = N → a ≤ b →
      f a ≠ 0 → f b ≠ 0 →
      (∀ z ∈ Z, z ∈ Set.Ioo a b) →
      (∀ x ∈ Set.Icc a b, x ∉ Z → f x ≠ 0) →
      (∀ z ∈ Z, ∃ δ > 0, ∀ s t, z - δ < s → s < z → z < t →
        t < z + δ → f s * f t < 0) →
      orSign (f b) = orSign (f a) + (N : ZMod 2) := by
  intro N
  induction N with
  | zero =>
    intro Z b hcard hab hfa hfb hZ hoff _
    have hempty : Z = ∅ := Finset.card_eq_zero.mp hcard
    subst hempty
    have h1 : ∀ x ∈ Set.Icc a b, f x ≠ 0 := by
      intro x hx
      exact hoff x hx (Finset.notMem_empty x)
    rw [Nat.cast_zero, add_zero]
    exact (orSign_eq_of_forall_ne hcont hab h1).symm
  | succ n ihn =>
    intro Z b hcard hab hfa hfb hZ hoff hflip
    have hZne : Z.Nonempty := by
      rw [← Finset.card_pos, hcard]
      omega
    set z := Z.max' hZne with hz
    have hzZ : z ∈ Z := Z.max'_mem hZne
    have hzmem := hZ z hzZ
    have hzlt : ∀ w ∈ Z, w ≤ z := fun w hw => Z.le_max' w hw
    -- a cut point u ∈ (a, z) above all remaining crossings
    obtain ⟨u, hau, huz, hupper⟩ :
        ∃ u, a < u ∧ u < z ∧ ∀ w ∈ Z.erase z, w < u := by
      rcases (Z.erase z).eq_empty_or_nonempty with he | he
      · exact ⟨(a + z) / 2, by linarith [hzmem.1],
          by linarith [hzmem.1],
          fun w hw => absurd hw
            (by rw [he]; exact Finset.notMem_empty w)⟩
      · have hMZ : (Z.erase z).max' he ∈ Z.erase z :=
          (Z.erase z).max'_mem he
        have hMz : (Z.erase z).max' he < z := by
          have h1 := Finset.mem_erase.mp hMZ
          exact lt_of_le_of_ne (hzlt _ h1.2) h1.1
        have hMa : a < (Z.erase z).max' he :=
          (hZ _ (Finset.mem_erase.mp hMZ).2).1
        refine ⟨((Z.erase z).max' he + z) / 2, by linarith,
          by linarith, ?_⟩
        intro w hw
        have h2 := (Z.erase z).le_max' w hw
        linarith
    have huZ : u ∉ Z := by
      intro hu
      rcases eq_or_ne u z with heq | hne
      · rw [heq] at huz
        exact lt_irrefl z huz
      · exact lt_irrefl u
          (hupper u (Finset.mem_erase.mpr ⟨hne, hu⟩))
    have hub : u < b := lt_trans huz hzmem.2
    have hfu : f u ≠ 0 :=
      hoff u (Set.mem_Icc.mpr ⟨hau.le, hub.le⟩) huZ
    -- inductive hypothesis on [a, u]
    have hIH : orSign (f u) = orSign (f a) + (n : ZMod 2) := by
      refine ihn (Z.erase z) u ?_ hau.le hfa hfu ?_ ?_ ?_
      · rw [Finset.card_erase_of_mem hzZ, hcard]
        omega
      · intro w hw
        exact Set.mem_Ioo.mpr
          ⟨(hZ w (Finset.mem_erase.mp hw).2).1, hupper w hw⟩
      · intro x hx hxZ'
        refine hoff x (Set.mem_Icc.mpr
          ⟨(Set.mem_Icc.mp hx).1,
            le_trans (Set.mem_Icc.mp hx).2 hub.le⟩) ?_
        intro hxZ
        rcases eq_or_ne x z with rfl | hne
        · exact absurd (Set.mem_Icc.mp hx).2 (not_le.mpr huz)
        · exact hxZ' (Finset.mem_erase.mpr ⟨hne, hxZ⟩)
      · intro w hw
        exact hflip w (Finset.mem_erase.mp hw).2
    -- the single crossing at z between u and b
    obtain ⟨δz, hδz, hflipz⟩ := hflip z hzZ
    set s : ℝ := (max u (z - δz) + z) / 2 with hsdef
    set t : ℝ := (z + min b (z + δz)) / 2 with htdef
    have hmaxlt : max u (z - δz) < z := max_lt huz (by linarith)
    have hminlt : z < min b (z + δz) :=
      lt_min hzmem.2 (by linarith)
    have hs1 : max u (z - δz) < s := by
      rw [hsdef]
      linarith
    have hs2 : s < z := by
      rw [hsdef]
      linarith
    have ht1 : z < t := by
      rw [htdef]
      linarith
    have ht2 : t < min b (z + δz) := by
      rw [htdef]
      linarith
    have hus : u ≤ s := le_trans (le_max_left _ _) hs1.le
    have htb : t ≤ b := le_trans ht2.le (min_le_left _ _)
    -- no zeros on [u, s]
    have hseg1 : ∀ x ∈ Set.Icc u s, f x ≠ 0 := by
      intro x hx
      refine hoff x (Set.mem_Icc.mpr
        ⟨le_trans hau.le (Set.mem_Icc.mp hx).1,
          le_trans (Set.mem_Icc.mp hx).2
            (le_trans hs2.le hzmem.2.le)⟩) ?_
      intro hxZ
      rcases eq_or_ne x z with rfl | hne
      · exact absurd (Set.mem_Icc.mp hx).2 (not_le.mpr hs2)
      · exact absurd (Set.mem_Icc.mp hx).1
          (not_le.mpr (hupper x (Finset.mem_erase.mpr ⟨hne, hxZ⟩)))
    -- no zeros on [t, b]
    have hseg2 : ∀ x ∈ Set.Icc t b, f x ≠ 0 := by
      intro x hx
      refine hoff x (Set.mem_Icc.mpr
        ⟨le_trans hau.le (le_trans huz.le
          (le_trans ht1.le (Set.mem_Icc.mp hx).1)),
          (Set.mem_Icc.mp hx).2⟩) ?_
      intro hxZ
      have h5 := hzlt x hxZ
      have h6 : z < x := lt_of_lt_of_le ht1 (Set.mem_Icc.mp hx).1
      linarith
    have h7 : orSign (f u) = orSign (f s) :=
      orSign_eq_of_forall_ne hcont hus hseg1
    have h8 : orSign (f t) = orSign (f b) :=
      orSign_eq_of_forall_ne hcont htb hseg2
    have h9 : f s * f t < 0 := hflipz s t
      (lt_of_le_of_lt (le_max_right _ _) hs1) hs2 ht1
      (lt_of_lt_of_le ht2 (min_le_right _ _))
    have h10 : orSign (f s) = orSign (f t) + 1 :=
      orSign_eq_add_one_of_mul_neg h9
    have h11 : orSign (f t) = orSign (f s) + 1 := by
      rw [h10, add_assoc, show (1 + 1 : ZMod 2) = 0 from by decide,
        add_zero]
    rw [← h8, h11, ← h7, hIH]
    push_cast
    ring

/-- **Crossing parity**: for a continuous function with nonvanishing
endpoints and finitely many local sign flips, the endpoint
orientations differ by the flip count mod 2.  Since the endpoints
determine the parity, `(−1)^{N_cross}` is unchanged by any
perturbation fixing the endpoint signs. -/
theorem crossing_parity {f : ℝ → ℝ} (hcont : Continuous f)
    {a b : ℝ} (hab : a ≤ b) (hfa : f a ≠ 0) (hfb : f b ≠ 0)
    (Z : Finset ℝ) (hZ : ∀ z ∈ Z, z ∈ Set.Ioo a b)
    (hoff : ∀ x ∈ Set.Icc a b, x ∉ Z → f x ≠ 0)
    (hflip : ∀ z ∈ Z, ∃ δ > 0, ∀ s t, z - δ < s → s < z → z < t →
      t < z + δ → f s * f t < 0) :
    orSign (f b) = orSign (f a) + (Z.card : ZMod 2) :=
  crossing_parity_aux hcont Z.card Z b rfl hab hfa hfb hZ hoff hflip

/-! ## Determinant paths (`prop:det-crossing`, `prop:det-jet`) -/

/-- Smoothness of the determinant along a smooth matrix path, via the
Leibniz expansion. -/
theorem contDiff_det {r : ℕ} {N : WithTop ℕ∞}
    {L : ℝ → Matrix (Fin r) (Fin r) ℝ} (hL : ContDiff ℝ N L) :
    ContDiff ℝ N fun t => (L t).det := by
  have hentry : ∀ i j, ContDiff ℝ N fun t => L t i j := by
    intro i j
    exact (contDiff_pi.mp ((contDiff_pi.mp hL) i)) j
  have hprod : ∀ (s : Finset (Fin r)) (σ : Equiv.Perm (Fin r)),
      ContDiff ℝ N fun t => ∏ i ∈ s, L t (σ i) i := by
    intro s σ
    induction s using Finset.induction_on with
    | empty => simpa using contDiff_const
    | insert a s ha ih =>
      have h1 : (fun t => ∏ i ∈ insert a s, L t (σ i) i)
          = fun t => L t (σ a) a * ∏ i ∈ s, L t (σ i) i :=
        funext fun t => Finset.prod_insert ha
      rw [h1]
      exact (hentry _ _).mul ih
  have hdet : (fun t => (L t).det)
      = fun t => ∑ σ : Equiv.Perm (Fin r),
          Equiv.Perm.sign σ • ∏ i, L t (σ i) i :=
    funext fun t => Matrix.det_apply (L t)
  rw [hdet]
  refine ContDiff.sum fun σ _ => ?_
  have h2 : (fun t => Equiv.Perm.sign σ • ∏ i, L t (σ i) i)
      = fun t => ((Equiv.Perm.sign σ : ℤ) : ℝ)
          * ∏ i, L t (σ i) i := by
    funext t
    rw [Units.smul_def, zsmul_eq_mul]
  rw [h2]
  exact contDiff_const.mul (hprod Finset.univ σ)

/-- **Proposition `prop:det-crossing` (transverse flip)**: a
transverse zero of the determinant along a `C¹` matrix path flips the
orientation sign, and the determinant is nonvanishing on a punctured
neighbourhood. -/
theorem det_transverse_crossing {r : ℕ}
    {L : ℝ → Matrix (Fin r) (Fin r) ℝ} {t₀ : ℝ}
    (hL : ContDiff ℝ 1 L) (h0 : (L t₀).det = 0)
    (h1 : deriv (fun t => (L t).det) t₀ ≠ 0) :
    ∃ δ > 0, (∀ t, t ≠ t₀ → |t - t₀| < δ → (L t).det ≠ 0)
      ∧ ∀ s t, t₀ - δ < s → s < t₀ → t₀ < t → t < t₀ + δ →
        (L s).det * (L t).det < 0 := by
  have hvan : ∀ k, k < 1 → iteratedDeriv k
      (fun t => (L t).det) t₀ = 0 := by
    intro k hk
    interval_cases k
    rwa [iteratedDeriv_zero]
  have hc : iteratedDeriv 1 (fun t => (L t).det) t₀ ≠ 0 := by
    rwa [iteratedDeriv_one]
  obtain ⟨δ, hδ, hne, hflip⟩ := jet_flip_parity le_rfl
    (contDiff_det hL) hvan hc
  exact ⟨δ, hδ, hne, fun s t hs1 hs2 ht1 ht2 =>
    (hflip s t hs1 hs2 ht1 ht2).mpr odd_one⟩

/-- **Proposition `prop:det-jet`**: with vanishing determinant jets
up to order `m − 1` and a nonzero `m`-th jet, the determinant sign
changes across the parameter **iff `m` is odd**. -/
theorem det_jet_parity {r : ℕ}
    {L : ℝ → Matrix (Fin r) (Fin r) ℝ} {t₀ : ℝ} {m : ℕ}
    (hm : 1 ≤ m) (hL : ContDiff ℝ m L)
    (hvan : ∀ k, k < m →
      iteratedDeriv k (fun t => (L t).det) t₀ = 0)
    (hc : iteratedDeriv m (fun t => (L t).det) t₀ ≠ 0) :
    ∃ δ > 0, (∀ t, t ≠ t₀ → |t - t₀| < δ → (L t).det ≠ 0)
      ∧ ∀ s t, t₀ - δ < s → s < t₀ → t₀ < t → t < t₀ + δ →
        ((L s).det * (L t).det < 0 ↔ Odd m) :=
  jet_flip_parity hm (contDiff_det hL) hvan hc

/-- **Proposition `prop:det-crossing` (parity formula)**: along a
`C¹` determinant path whose zeros in `(a,b)` are finitely many
transverse crossings, the endpoint orientation signs differ exactly
by the crossing count mod 2 — the parity `(−1)^{N_cross}` is fixed by
the endpoint data and hence unchanged by endpoint-fixing
perturbations. -/
theorem det_crossing_parity {r : ℕ}
    {L : ℝ → Matrix (Fin r) (Fin r) ℝ} (hL : ContDiff ℝ 1 L)
    {a b : ℝ} (hab : a ≤ b)
    (hfa : (L a).det ≠ 0) (hfb : (L b).det ≠ 0)
    (Z : Finset ℝ) (hZ : ∀ z ∈ Z, z ∈ Set.Ioo a b)
    (hoff : ∀ x ∈ Set.Icc a b, x ∉ Z → (L x).det ≠ 0)
    (hzero : ∀ z ∈ Z, (L z).det = 0)
    (htrans : ∀ z ∈ Z, deriv (fun t => (L t).det) z ≠ 0) :
    orSign ((L b).det) = orSign ((L a).det) + (Z.card : ZMod 2) := by
  refine crossing_parity (contDiff_det hL).continuous hab hfa hfb Z
    hZ hoff ?_
  intro z hzZ
  obtain ⟨δ, hδ, _, hflip⟩ := det_transverse_crossing hL
    (hzero z hzZ) (htrans z hzZ)
  exact ⟨δ, hδ, hflip⟩

/-! ## Orientation stability (`prop:noisy-record-sign-stability`) -/

/-- **Proposition `prop:noisy-record-sign-stability`**: along a
continuous determinant-regular family of record transports, the
orientation sign is locally constant; it can change only across a
rank-loss locus `det = 0`. -/
theorem det_sign_locally_constant {X : Type*} [TopologicalSpace X]
    {r : ℕ} {L : X → Matrix (Fin r) (Fin r) ℝ} (hL : Continuous L)
    {p₀ : X} (h0 : (L p₀).det ≠ 0) :
    ∀ᶠ p in nhds p₀, orSign (L p).det = orSign (L p₀).det := by
  have hdet : Continuous fun p => (L p).det := hL.matrix_det
  rcases lt_or_gt_of_ne h0 with h | h
  · have hev : ∀ᶠ p in nhds p₀, (L p).det < 0 :=
      (hdet.tendsto p₀).eventually_lt_const h
    filter_upwards [hev] with p hp
    rw [orSign, orSign, if_neg (not_lt.mpr hp.le),
      if_neg (not_lt.mpr h.le)]
  · have hev : ∀ᶠ p in nhds p₀, 0 < (L p).det :=
      (hdet.tendsto p₀).eventually_const_lt h
    filter_upwards [hev] with p hp
    rw [orSign, orSign, if_pos hp, if_pos h]

end NCG
