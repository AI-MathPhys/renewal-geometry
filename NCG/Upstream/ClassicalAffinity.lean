/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.ClassicalReverse
import NCG.Upstream.AffinityCohomology

/-!
# The classical cycle-affinity theorem and the Kolmogorov criterion

Covers, from `manuscripts/renewal_emergence/renewal_emergence.tex`:

* `thm:classical-affinity` — the edge affinity
  `A_{ij} = log(π_i p_{ij}/(π_j p_{ji}))` is antisymmetric; cycle
  affinity is (i) additive under concatenation, (ii) equal to
  `log(∏ p_forward/∏ p_backward)` (the stationary potential
  telescopes on cycles), (iii) zero under detailed balance, and
  (iv) — Kolmogorov's criterion, proved in full — for an
  irreducible chain (positive-path reachability) with bidirected
  support, vanishing of all cycle affinities implies detailed
  balance.  The proof builds the affinity potential along chosen
  positive paths, produces the reversible stationary weight
  `m = π e^F`, and uses a self-contained ratio-minimum uniqueness
  argument for stationary laws (`stationary_unique`).
* `cor:kolmogorov-cohomology` — `[A] = 0` in `H¹` of the support
  graph, vanishing of all cycle affinities, and detailed balance
  are equivalent.
-/

namespace NCG.Upstream

open NCG

variable {V : Type*} [Fintype V] [DecidableEq V]
  (p : V → V → ℝ) (π : V → ℝ)

/-! ## Edge and path affinity -/

/-- **Theorem `thm:classical-affinity` (edge affinity)**:
`A_{ij} = log(π_i p_{ij}/(π_j p_{ji}))`. -/
noncomputable def edgeAff (i j : V) : ℝ :=
  Real.log (π i * p i j / (π j * p j i))

omit [DecidableEq V] [Fintype V] in
/-- Edge affinity is antisymmetric, `A_{ji} = −A_{ij}`. -/
theorem edgeAff_antisymm (i j : V) :
    edgeAff p π j i = -edgeAff p π i j := by
  unfold edgeAff
  rw [show π j * p j i / (π i * p i j)
      = (π i * p i j / (π j * p j i))⁻¹ from by rw [inv_div]]
  exact Real.log_inv _

/-- The affinity of a finite path. -/
noncomputable def pathAff (γ : ℕ → V) (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range M, edgeAff p π (γ k) (γ (k + 1))

/-- Concatenation of two paths (`γ₁` for the first `m₁` steps). -/
def pathConcat (γ₁ γ₂ : ℕ → V) (m₁ : ℕ) : ℕ → V :=
  fun k => if k < m₁ then γ₁ k else γ₂ (k - m₁)

omit [DecidableEq V] [Fintype V] in
theorem pathConcat_left {γ₁ γ₂ : ℕ → V} {m₁ : ℕ}
    (hseam : γ₂ 0 = γ₁ m₁) {k : ℕ} (hk : k ≤ m₁) :
    pathConcat γ₁ γ₂ m₁ k = γ₁ k := by
  unfold pathConcat
  rcases lt_or_eq_of_le hk with h | h
  · rw [if_pos h]
  · subst h
    rw [if_neg (lt_irrefl k), Nat.sub_self, hseam]

omit [DecidableEq V] [Fintype V] in
theorem pathConcat_right {γ₁ γ₂ : ℕ → V} {m₁ : ℕ} {k : ℕ}
    (hk : m₁ ≤ k) :
    pathConcat γ₁ γ₂ m₁ k = γ₂ (k - m₁) := by
  unfold pathConcat
  rw [if_neg (not_lt.mpr hk)]

omit [DecidableEq V] [Fintype V] in
/-- **Theorem `thm:classical-affinity` (i)**: affinity is additive
under concatenation (of paths, in particular of based cycles). -/
theorem pathAff_concat (γ₁ γ₂ : ℕ → V) (m₁ m₂ : ℕ)
    (hseam : γ₂ 0 = γ₁ m₁) :
    pathAff p π (pathConcat γ₁ γ₂ m₁) (m₁ + m₂)
      = pathAff p π γ₁ m₁ + pathAff p π γ₂ m₂ := by
  induction m₂ with
  | zero =>
    unfold pathAff
    rw [Nat.add_zero, Finset.sum_range_zero, add_zero]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkm := Finset.mem_range.mp hk
    rw [pathConcat_left hseam (le_of_lt hkm),
      pathConcat_left hseam (by omega)]
  | succ m₂ ih =>
    have hstep : pathAff p π (pathConcat γ₁ γ₂ m₁) (m₁ + (m₂ + 1))
        = pathAff p π (pathConcat γ₁ γ₂ m₁) (m₁ + m₂)
          + edgeAff p π (γ₂ m₂) (γ₂ (m₂ + 1)) := by
      unfold pathAff
      rw [show m₁ + (m₂ + 1) = (m₁ + m₂) + 1 from by omega,
        Finset.sum_range_succ]
      congr 1
      rw [pathConcat_right (by omega : m₁ ≤ m₁ + m₂),
        pathConcat_right (by omega : m₁ ≤ m₁ + m₂ + 1),
        show m₁ + m₂ - m₁ = m₂ from by omega,
        show m₁ + m₂ + 1 - m₁ = m₂ + 1 from by omega]
    rw [hstep, ih]
    unfold pathAff
    rw [Finset.sum_range_succ]
    ring

omit [DecidableEq V] [Fintype V] in
/-- Positivity of edges along a concatenation. -/
theorem pathConcat_pos {γ₁ γ₂ : ℕ → V} {m₁ m₂ : ℕ}
    (hseam : γ₂ 0 = γ₁ m₁)
    (h1 : ∀ k < m₁, 0 < p (γ₁ k) (γ₁ (k + 1)))
    (h2 : ∀ k < m₂, 0 < p (γ₂ k) (γ₂ (k + 1))) :
    ∀ k < m₁ + m₂,
      0 < p (pathConcat γ₁ γ₂ m₁ k) (pathConcat γ₁ γ₂ m₁ (k + 1)) := by
  intro k hk
  by_cases hkm : k < m₁
  · rw [pathConcat_left hseam (le_of_lt hkm),
      pathConcat_left hseam (by omega)]
    exact h1 k hkm
  · rw [pathConcat_right (by omega : m₁ ≤ k),
      pathConcat_right (by omega : m₁ ≤ k + 1),
      show k + 1 - m₁ = (k - m₁) + 1 from by omega]
    exact h2 (k - m₁) (by omega)

omit [DecidableEq V] [Fintype V] in
/-- Path reversal negates affinity (antisymmetry is
unconditional). -/
theorem pathAff_reverse (γ : ℕ → V) (M : ℕ) :
    pathAff p π (fun k => γ (M - k)) M = -pathAff p π γ M := by
  unfold pathAff
  rw [show -(∑ k ∈ Finset.range M, edgeAff p π (γ k) (γ (k + 1)))
      = ∑ k ∈ Finset.range M, -edgeAff p π (γ k) (γ (k + 1)) from by
    simp]
  rw [← Finset.sum_range_reflect
    (fun k => -edgeAff p π (γ k) (γ (k + 1))) M]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkM := Finset.mem_range.mp hk
  dsimp only
  rw [show M - 1 - k + 1 = M - k from by omega,
    show M - (k + 1) = M - 1 - k from by omega]
  exact edgeAff_antisymm p π (γ (M - 1 - k)) (γ (M - k))

omit [DecidableEq V] [Fintype V] in
/-- Positivity of edges along a reversal, from bidirected
support. -/
theorem pathReverse_pos {γ : ℕ → V} {M : ℕ}
    (hbid : ∀ i j, 0 < p i j ↔ 0 < p j i)
    (hpos : ∀ k < M, 0 < p (γ k) (γ (k + 1))) :
    ∀ k < M, 0 < p (γ (M - k)) (γ (M - (k + 1))) := by
  intro k hk
  have h1 := hpos (M - (k + 1)) (by omega)
  rw [show M - (k + 1) + 1 = M - k from by omega] at h1
  exact (hbid _ _).mp h1

/-- One-step path. -/
def singleStep (a b : V) : ℕ → V :=
  fun k => if k = 0 then a else b

omit [DecidableEq V] [Fintype V] in
@[simp] theorem singleStep_zero (a b : V) :
    singleStep a b 0 = a := rfl

omit [DecidableEq V] [Fintype V] in
@[simp] theorem singleStep_succ (a b : V) (k : ℕ) :
    singleStep a b (k + 1) = b := rfl

omit [DecidableEq V] [Fintype V] in
theorem pathAff_singleStep (a b : V) :
    pathAff p π (singleStep a b) 1 = edgeAff p π a b := by
  unfold pathAff
  rw [Finset.sum_range_one]
  rfl

/-! ## `thm:classical-affinity` (ii) and (iii) -/

omit [DecidableEq V] [Fintype V] in
/-- **Theorem `thm:classical-affinity` (ii)**: on a cycle the
stationary potential telescopes, so the cycle affinity is
`log(∏ p_forward / ∏ p_backward)`. -/
theorem cycleAff_eq_log_ratio (hπ : ∀ i, 0 < π i)
    (hbid : ∀ i j, 0 < p i j ↔ 0 < p j i)
    (γ : ℕ → V) (M : ℕ) (hcycle : γ M = γ 0)
    (hpos : ∀ k < M, 0 < p (γ k) (γ (k + 1))) :
    pathAff p π γ M
      = Real.log ((∏ k ∈ Finset.range M, p (γ k) (γ (k + 1)))
          / ∏ k ∈ Finset.range M, p (γ (k + 1)) (γ k)) := by
  have hterm : ∀ k ∈ Finset.range M,
      edgeAff p π (γ k) (γ (k + 1))
        = (Real.log (π (γ k)) - Real.log (π (γ (k + 1))))
          + (Real.log (p (γ k) (γ (k + 1)))
            - Real.log (p (γ (k + 1)) (γ k))) := by
    intro k hk
    have hkM := Finset.mem_range.mp hk
    have h1 := hpos k hkM
    have h2 := (hbid _ _).mp h1
    unfold edgeAff
    rw [Real.log_div (mul_pos (hπ _) h1).ne' (mul_pos (hπ _) h2).ne',
      Real.log_mul (hπ _).ne' h1.ne',
      Real.log_mul (hπ _).ne' h2.ne']
    ring
  unfold pathAff
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  have htel : ∑ k ∈ Finset.range M,
      (Real.log (π (γ k)) - Real.log (π (γ (k + 1)))) = 0 := by
    rw [Finset.sum_range_sub' (fun k => Real.log (π (γ k)))]
    rw [hcycle, sub_self]
  rw [htel, zero_add, Finset.sum_sub_distrib]
  rw [← Real.log_prod
      (fun k hk => (hpos k (Finset.mem_range.mp hk)).ne'),
    ← Real.log_prod
      (fun k hk =>
        ((hbid _ _).mp (hpos k (Finset.mem_range.mp hk))).ne'),
    ← Real.log_div
      (Finset.prod_pos
        (fun k hk => hpos k (Finset.mem_range.mp hk))).ne'
      (Finset.prod_pos
        (fun k hk => (hbid _ _).mp
          (hpos k (Finset.mem_range.mp hk)))).ne']

omit [DecidableEq V] [Fintype V] in
/-- **Theorem `thm:classical-affinity` (iii)**: detailed balance
makes every edge affinity zero (hence every cycle affinity). -/
theorem edgeAff_eq_zero_of_balanced
    (hbal : ∀ i j, π i * p i j = π j * p j i) (i j : V) :
    edgeAff p π i j = 0 := by
  unfold edgeAff
  rw [hbal i j]
  by_cases h : π j * p j i = 0
  · rw [h, div_zero, Real.log_zero]
  · rw [div_self h, Real.log_one]

omit [DecidableEq V] [Fintype V] in
theorem pathAff_eq_zero_of_balanced
    (hbal : ∀ i j, π i * p i j = π j * p j i) (γ : ℕ → V)
    (M : ℕ) : pathAff p π γ M = 0 := by
  unfold pathAff
  exact Finset.sum_eq_zero fun k _ =>
    edgeAff_eq_zero_of_balanced p π hbal _ _

/-! ## Uniqueness of the stationary law (ratio-minimum argument) -/

omit [DecidableEq V] in
/-- **Theorem `thm:classical-affinity` (iv), uniqueness input**:
positive stationary laws of an irreducible chain are proportional —
the ratio-minimum/zero-propagation argument, self-contained. -/
theorem stationary_unique
    (hp : ∀ i j, 0 ≤ p i j) (_hrow : ∀ i, ∑ j, p i j = 1)
    (hπ : ∀ i, 0 < π i) (hπs : ∀ j, ∑ i, π i * p i j = π j)
    (m : V → ℝ) (hm : ∀ i, 0 < m i)
    (hms : ∀ j, ∑ i, m i * p i j = m j)
    (hreach : ∀ i j : V, ∃ (M : ℕ) (γ : ℕ → V),
      γ 0 = i ∧ γ M = j ∧ ∀ k < M, 0 < p (γ k) (γ (k + 1))) :
    ∃ c : ℝ, 0 < c ∧ ∀ i, m i = c * π i := by
  rcases isEmpty_or_nonempty (V) with hemp | hne
  · exact ⟨1, one_pos, fun i => (hemp.false i).elim⟩
  · obtain ⟨i₀, -, hmin⟩ := Finset.exists_min_image Finset.univ
      (fun i => m i / π i) ⟨hne.some, Finset.mem_univ _⟩
    refine ⟨m i₀ / π i₀, div_pos (hm i₀) (hπ i₀), ?_⟩
    set c := m i₀ / π i₀ with hc
    set m' : V → ℝ := fun i => m i - c * π i with hm'
    have hm'nonneg : ∀ i, 0 ≤ m' i := by
      intro i
      have h1 : c ≤ m i / π i := hmin i (Finset.mem_univ i)
      have h2 : c * π i ≤ m i := by
        rw [← le_div_iff₀ (hπ i)]
        exact h1
      change 0 ≤ m i - c * π i
      linarith
    have hm'stat : ∀ j, ∑ i, m' i * p i j = m' j := by
      intro j
      change ∑ i, (m i - c * π i) * p i j = m j - c * π j
      have hsplit : ∀ i, (m i - c * π i) * p i j
          = m i * p i j - c * (π i * p i j) := fun i => by ring
      rw [Finset.sum_congr rfl fun i _ => hsplit i,
        Finset.sum_sub_distrib, hms j, ← Finset.mul_sum, hπs j]
    have hm'zero : m' i₀ = 0 := by
      change m i₀ - c * π i₀ = 0
      rw [hc, div_mul_cancel₀ _ (hπ i₀).ne', sub_self]
    have hprop : ∀ (L : ℕ) (γ : ℕ → V),
        (∀ k < L, 0 < p (γ k) (γ (k + 1))) → m' (γ L) = 0 →
        m' (γ 0) = 0 := by
      intro L
      induction L with
      | zero => intro γ _ h; exact h
      | succ L ih =>
        intro γ hpos hend
        have hstatj := hm'stat (γ (L + 1))
        rw [hend] at hstatj
        have hterms : ∀ i ∈ Finset.univ,
            0 ≤ m' i * p i (γ (L + 1)) :=
          fun i _ => mul_nonneg (hm'nonneg i) (hp i _)
        have hzero := (Finset.sum_eq_zero_iff_of_nonneg hterms).mp
          hstatj
        have hL := hzero (γ L) (Finset.mem_univ _)
        have hpL := hpos L (Nat.lt_succ_self L)
        have hm'L : m' (γ L) = 0 := by
          rcases mul_eq_zero.mp hL with h | h
          · exact h
          · exact absurd h hpL.ne'
        exact ih γ (fun k hk => hpos k (Nat.lt_succ_of_lt hk)) hm'L
    intro i
    obtain ⟨M, γ, hγ0, hγM, hγpos⟩ := hreach i i₀
    have h0 : m' (γ M) = 0 := by rw [hγM]; exact hm'zero
    have h1 : m' (γ 0) = 0 := hprop M γ hγpos h0
    rw [hγ0] at h1
    have h2 : m i - c * π i = 0 := h1
    linarith

/-! ## `thm:classical-affinity` (iv): the Kolmogorov criterion -/

omit [DecidableEq V] [Fintype V] in
/-- The affinity of a positive edge is a potential difference of
path affinities from a common base (via one closed cycle). -/
theorem edgeAff_eq_potential_sub
    (hbid : ∀ i j, 0 < p i j ↔ 0 < p j i)
    (hcyc : ∀ (γ : ℕ → V) (M : ℕ), γ M = γ 0 →
      (∀ k < M, 0 < p (γ k) (γ (k + 1))) → pathAff p π γ M = 0)
    {o a b : V} (hab : 0 < p a b)
    {Ma : ℕ} {γa : ℕ → V} (ha0 : γa 0 = o) (haM : γa Ma = a)
    (hapos : ∀ k < Ma, 0 < p (γa k) (γa (k + 1)))
    {Mb : ℕ} {γb : ℕ → V} (hb0 : γb 0 = o) (hbM : γb Mb = b)
    (hbpos : ∀ k < Mb, 0 < p (γb k) (γb (k + 1))) :
    edgeAff p π a b = pathAff p π γb Mb - pathAff p π γa Ma := by
  have hseam1 : singleStep a b 0 = γa Ma := by
    rw [singleStep_zero, haM]
  have hseam2 : (fun k => γb (Mb - k)) 0
      = pathConcat γa (singleStep a b) Ma (Ma + 1) := by
    change γb (Mb - 0) = _
    rw [Nat.sub_zero, hbM,
      pathConcat_right (by omega : Ma ≤ Ma + 1),
      show Ma + 1 - Ma = 1 from by omega]
    rfl
  have hepos : ∀ k < 1,
      0 < p (singleStep a b k) (singleStep a b (k + 1)) := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    rw [singleStep_zero, singleStep_succ]
    exact hab
  have hc1pos := pathConcat_pos p hseam1 hapos hepos
  have hrpos : ∀ k < Mb,
      0 < p ((fun k => γb (Mb - k)) k)
        ((fun k => γb (Mb - k)) (k + 1)) := by
    intro k hk
    exact pathReverse_pos p hbid hbpos k hk
  have hc2pos := pathConcat_pos p hseam2 hc1pos hrpos
  have hclosed : pathConcat (pathConcat γa (singleStep a b) Ma)
      (fun k => γb (Mb - k)) (Ma + 1) ((Ma + 1) + Mb)
      = pathConcat (pathConcat γa (singleStep a b) Ma)
        (fun k => γb (Mb - k)) (Ma + 1) 0 := by
    rw [pathConcat_right (by omega : Ma + 1 ≤ Ma + 1 + Mb),
      show Ma + 1 + Mb - (Ma + 1) = Mb from by omega]
    show γb (Mb - Mb) = _
    rw [Nat.sub_self, hb0]
    rw [pathConcat_left hseam2 (by omega : 0 ≤ Ma + 1),
      pathConcat_left hseam1 (by omega : 0 ≤ Ma), ha0]
  have hzero := hcyc _ ((Ma + 1) + Mb) hclosed hc2pos
  rw [pathAff_concat p π _ _ (Ma + 1) Mb hseam2,
    pathAff_concat p π _ _ Ma 1 hseam1,
    pathAff_singleStep, pathAff_reverse] at hzero
  linarith

omit [DecidableEq V] in
/-- **Theorem `thm:classical-affinity` (iv), Kolmogorov's
criterion**: for an irreducible chain (positive-path reachability)
with bidirected support and stationary positive law `π`, vanishing
of all cycle affinities implies detailed balance. -/
theorem classical_affinity_kolmogorov
    (hπ : ∀ i, 0 < π i) (hp : ∀ i j, 0 ≤ p i j)
    (hrow : ∀ i, ∑ j, p i j = 1)
    (hπs : ∀ j, ∑ i, π i * p i j = π j)
    (hbid : ∀ i j, 0 < p i j ↔ 0 < p j i)
    (hreach : ∀ i j : V, ∃ (M : ℕ) (γ : ℕ → V),
      γ 0 = i ∧ γ M = j ∧ ∀ k < M, 0 < p (γ k) (γ (k + 1)))
    (hcyc : ∀ (γ : ℕ → V) (M : ℕ), γ M = γ 0 →
      (∀ k < M, 0 < p (γ k) (γ (k + 1))) → pathAff p π γ M = 0)
    (i j : V) : π i * p i j = π j * p j i := by
  by_cases hpos : 0 < p i j
  case neg =>
    have h1 : p i j = 0 := le_antisymm (not_lt.mp hpos) (hp i j)
    have h2 : p j i = 0 := by
      by_contra h
      exact hpos ((hbid j i).mp
        (lt_of_le_of_ne (hp j i) (Ne.symm h)))
    rw [h1, h2, mul_zero, mul_zero]
  case pos =>
    classical
    choose Mf γf hγ0 hγM hγpos using hreach
    have hreach' : ∀ a b : V, ∃ (M : ℕ) (γ : ℕ → V),
        γ 0 = a ∧ γ M = b ∧ ∀ k < M, 0 < p (γ k) (γ (k + 1)) :=
      fun a b => ⟨Mf a b, γf a b, hγ0 a b, hγM a b, hγpos a b⟩
    have hkey : ∀ a b : V, 0 < p a b →
        edgeAff p π a b
          = pathAff p π (γf i b) (Mf i b)
            - pathAff p π (γf i a) (Mf i a) := by
      intro a b hab
      exact edgeAff_eq_potential_sub p π hbid hcyc hab
        (hγ0 i a) (hγM i a) (hγpos i a)
        (hγ0 i b) (hγM i b) (hγpos i b)
    set F : V → ℝ :=
      fun v => pathAff p π (γf i v) (Mf i v) with hF
    set mw : V → ℝ := fun v => π v * Real.exp (F v) with hmw
    have hmwpos : ∀ v, 0 < mw v := fun v =>
      mul_pos (hπ v) (Real.exp_pos _)
    have hmwrev : ∀ a b, mw a * p a b = mw b * p b a := by
      intro a b
      by_cases hab : 0 < p a b
      · have hba := (hbid a b).mp hab
        have hAab := hkey a b hab
        have hratio : π a * p a b / (π b * p b a)
            = Real.exp (F b - F a) := by
          rw [← hAab]
          exact (Real.exp_log (div_pos (mul_pos (hπ a) hab)
            (mul_pos (hπ b) hba))).symm
        rw [Real.exp_sub] at hratio
        rw [div_eq_div_iff (mul_pos (hπ b) hba).ne'
          (Real.exp_pos (F a)).ne'] at hratio
        change π a * Real.exp (F a) * p a b
          = π b * Real.exp (F b) * p b a
        linear_combination hratio
      · have h1 : p a b = 0 := le_antisymm (not_lt.mp hab) (hp a b)
        have h2 : p b a = 0 := by
          by_contra h
          exact hab ((hbid b a).mp
            (lt_of_le_of_ne (hp b a) (Ne.symm h)))
        rw [h1, h2, mul_zero, mul_zero]
    have hmwstat : ∀ b, ∑ a, mw a * p a b = mw b := by
      intro b
      rw [Finset.sum_congr rfl fun a _ => hmwrev a b,
        ← Finset.mul_sum, hrow b, mul_one]
    obtain ⟨c, hcpos, hc⟩ := stationary_unique p π hp hrow hπ hπs
      mw hmwpos hmwstat hreach'
    have hrev := hmwrev i j
    rw [hc i, hc j] at hrev
    have h3 : c * (π i * p i j) = c * (π j * p j i) := by
      calc c * (π i * p i j) = (c * π i) * p i j := by ring
        _ = (c * π j) * p j i := hrev
        _ = c * (π j * p j i) := by ring
    exact mul_left_cancel₀ hcpos.ne' h3

/-! ## `cor:kolmogorov-cohomology` -/

/-- The support multigraph of the chain: one oriented edge per
positive transition. -/
def supportGraph (p : V → V → ℝ) : Multigraph where
  V := V
  E := {ij : V × V // 0 < p ij.1 ij.2}
  src := fun e => e.1.1
  tgt := fun e => e.1.2

/-- The edge-affinity cochain on the support graph. -/
noncomputable def edgeAffCochain : (supportGraph p).E → ℝ :=
  fun e => edgeAff p π e.1.1 e.1.2

omit [DecidableEq V] [Fintype V] in
/-- Shift lemma for path affinity. -/
theorem pathAff_shift (γ : ℕ → V) (M : ℕ) :
    pathAff p π γ (M + 1)
      = edgeAff p π (γ 0) (γ 1)
        + pathAff p π (fun k => γ (k + 1)) M := by
  unfold pathAff
  rw [Finset.sum_range_succ']
  rw [add_comm]

omit [DecidableEq V] [Fintype V] in
/-- Every positive path realizes a walk in the support graph with
the same affinity. -/
theorem path_to_walk (_hbid : ∀ i j, 0 < p i j ↔ 0 < p j i) :
    ∀ (M : ℕ) (γ : ℕ → V),
      (∀ k < M, 0 < p (γ k) (γ (k + 1))) →
      ∃ w : (supportGraph p).Walk (γ 0) (γ M),
        w.affinity (edgeAffCochain p π) = pathAff p π γ M := by
  intro M
  induction M with
  | zero =>
    intro γ _
    refine ⟨Multigraph.Walk.nil (G := supportGraph p) (γ 0), ?_⟩
    change (0 : ℝ) = pathAff p π γ 0
    unfold pathAff
    simp
  | succ M ih =>
    intro γ hpos
    have h0 := hpos 0 (by omega)
    obtain ⟨w', hw'⟩ := ih (fun k => γ (k + 1))
      (fun k hk => hpos (k + 1) (by omega))
    refine ⟨Multigraph.Walk.fwd (G := supportGraph p)
      (⟨(γ 0, γ 1), h0⟩ : (supportGraph p).E) w', ?_⟩
    change edgeAffCochain p π (⟨(γ 0, γ 1), h0⟩ : (supportGraph p).E)
        + w'.affinity (edgeAffCochain p π) = pathAff p π γ (M + 1)
    rw [hw', pathAff_shift]
    rfl

/-- Prepend a vertex to a path. -/
def pathPrepend (x : V) (γ : ℕ → V) : ℕ → V
  | 0 => x
  | k + 1 => γ k

omit [DecidableEq V] [Fintype V] in
@[simp] theorem pathPrepend_zero (x : V) (γ : ℕ → V) :
    pathPrepend x γ 0 = x := rfl

omit [DecidableEq V] [Fintype V] in
@[simp] theorem pathPrepend_succ (x : V) (γ : ℕ → V)
    (k : ℕ) : pathPrepend x γ (k + 1) = γ k := rfl

omit [DecidableEq V] [Fintype V] in
theorem pathAff_prepend (x : V) (γ : ℕ → V) (M : ℕ) :
    pathAff p π (pathPrepend x γ) (M + 1)
      = edgeAff p π x (γ 0) + pathAff p π γ M := by
  unfold pathAff
  rw [Finset.sum_range_succ', add_comm]
  congr 1

omit [DecidableEq V] [Fintype V] in
/-- Every walk in the support graph is realized by a positive path
with the same affinity. -/
theorem walk_to_path (hbid : ∀ i j, 0 < p i j ↔ 0 < p j i) :
    ∀ {x y : V} (w : (supportGraph p).Walk x y),
      ∃ (M : ℕ) (γ : ℕ → V), γ 0 = x ∧ γ M = y
        ∧ (∀ k < M, 0 < p (γ k) (γ (k + 1)))
        ∧ pathAff p π γ M
            = w.affinity (edgeAffCochain p π)
  | _, _, .nil v =>
    ⟨0, fun _ => v, rfl, rfl, by omega, by unfold pathAff; simp⟩
  | _, _, .fwd e q => by
    obtain ⟨M, γ, hγ0, hγM, hγpos, hγaff⟩ := walk_to_path hbid q
    refine ⟨M + 1, pathPrepend e.1.1 γ, rfl, hγM, ?_, ?_⟩
    · intro k hk
      match k with
      | 0 =>
        change 0 < p e.1.1 (γ 0)
        rw [hγ0]
        exact e.2
      | k + 1 =>
        change 0 < p (γ k) (γ (k + 1))
        exact hγpos k (by omega)
    · change pathAff p π (pathPrepend e.1.1 γ) (M + 1)
        = edgeAffCochain p π e + q.affinity (edgeAffCochain p π)
      rw [pathAff_prepend, hγ0, hγaff]
      rfl
  | _, _, .bwd e q => by
    obtain ⟨M, γ, hγ0, hγM, hγpos, hγaff⟩ := walk_to_path hbid q
    refine ⟨M + 1, pathPrepend e.1.2 γ, rfl, hγM, ?_, ?_⟩
    · intro k hk
      match k with
      | 0 =>
        change 0 < p e.1.2 (γ 0)
        rw [hγ0]
        exact (hbid _ _).mp e.2
      | k + 1 =>
        change 0 < p (γ k) (γ (k + 1))
        exact hγpos k (by omega)
    · change pathAff p π (pathPrepend e.1.2 γ) (M + 1)
        = -edgeAffCochain p π e + q.affinity (edgeAffCochain p π)
      rw [pathAff_prepend, hγ0, hγaff]
      have h2 : edgeAff p π e.1.2 ((supportGraph p).src e)
          = -edgeAffCochain p π e :=
        edgeAff_antisymm p π e.1.1 e.1.2
      rw [h2]

omit [DecidableEq V] in
/-- **Corollary `cor:kolmogorov-cohomology`**: for an irreducible
chain with bidirected support and stationary positive law, the
following are equivalent: `[A] = 0` in `H¹` of the support graph,
all cycle affinities vanish, and detailed balance. -/
theorem kolmogorov_cohomology
    (hπ : ∀ i, 0 < π i) (hp : ∀ i j, 0 ≤ p i j)
    (hrow : ∀ i, ∑ j, p i j = 1)
    (hπs : ∀ j, ∑ i, π i * p i j = π j)
    (hbid : ∀ i j, 0 < p i j ↔ 0 < p j i)
    (hreach : ∀ i j : V, ∃ (M : ℕ) (γ : ℕ → V),
      γ 0 = i ∧ γ M = j ∧ ∀ k < M, 0 < p (γ k) (γ (k + 1))) :
    ((Multigraph.H1R.mk (supportGraph p) (edgeAffCochain p π) = 0)
        ↔ ∀ (γ : ℕ → V) (M : ℕ), γ M = γ 0 →
            (∀ k < M, 0 < p (γ k) (γ (k + 1))) →
            pathAff p π γ M = 0)
    ∧ ((∀ (γ : ℕ → V) (M : ℕ), γ M = γ 0 →
            (∀ k < M, 0 < p (γ k) (γ (k + 1))) →
            pathAff p π γ M = 0)
        ↔ ∀ i j, π i * p i j = π j * p j i) := by
  constructor
  · constructor
    · -- [A] = 0 ⇒ cycle affinities vanish (potential telescoping)
      intro hzero γ M hcycle hpos
      obtain ⟨u, hu⟩ := Multigraph.H1R.mk_eq_zero_iff.mp hzero
      have hterm : ∀ k ∈ Finset.range M,
          edgeAff p π (γ k) (γ (k + 1))
            = u (γ (k + 1)) - u (γ k) := by
        intro k hk
        have hkM := Finset.mem_range.mp hk
        exact congrFun hu
          (⟨(γ k, γ (k + 1)), hpos k hkM⟩ : (supportGraph p).E)
      unfold pathAff
      rw [Finset.sum_congr rfl hterm,
        Finset.sum_range_sub (fun k => u (γ k)), hcycle, sub_self]
    · -- cycle affinities vanish ⇒ [A] = 0
      intro hcyc
      rcases isEmpty_or_nonempty (V) with hemp | hne
      · rw [Multigraph.H1R.mk_eq_zero_iff]
        refine ⟨fun _ => 0, ?_⟩
        funext e
        exact (hemp.false e.1.1).elim
      · have hconn : (supportGraph p).ConnectedTo hne.some := by
          intro v
          obtain ⟨M, γ, hγ0, hγM, hγpos⟩ := hreach hne.some v
          obtain ⟨w, -⟩ := path_to_walk p π hbid M γ hγpos
          rw [hγ0, hγM] at w
          exact ⟨w⟩
        rw [Multigraph.H1R.mk_eq_zero_iff_cycles hconn]
        intro v w
        obtain ⟨M, γ, hγ0, hγM, hγpos, hγaff⟩ :=
          walk_to_path p π hbid w
        rw [← hγaff]
        exact hcyc γ M (hγM.trans hγ0.symm) hγpos
  · constructor
    · intro hcyc i j
      exact classical_affinity_kolmogorov p π hπ hp hrow hπs hbid
        hreach hcyc i j
    · intro hbal γ M _ _
      exact pathAff_eq_zero_of_balanced p π hbal γ M

end NCG.Upstream
