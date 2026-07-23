/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.GibbsDLR

/-!
# Dobrushin uniqueness: clause (i) of the phase-coexistence theorem

At high temperature (`4·tanh θ < 1`) the infinite-volume Gibbs state
is **unique**: any two DLR states agree on every bounded local
observable.  The proof is the oscillation-contraction form of the
Dobrushin argument: single-site heat-bath resampling kills the
oscillation at the resampled site and leaks at most `tanh θ` of it
to each of the four neighbours, so greedy resampling drives the
total oscillation to zero (the harmonic series diverges), while DLR
states are blind to resampling.

* `OscLe`/`IsLocal` — the oscillation calculus of local observables;
* `oneSite` — the single-site heat-bath kernel, equal to `dlrK` on
  singletons;
* `condP_diff_le` — the sharp `tanh θ` influence bound;
* `oscLe_oneSite_self`/`oscLe_oneSite_other` — the Dobrushin
  oscillation estimates;
* `DLRState` and `dlrState_unique` — **uniqueness**;
* `gibbsPlus_eq_gibbsMinus_highTemp`, `gibbsPlus_spin_zero` — the
  unique state is deck-flip invariant with zero magnetization: the
  torsion defect vanishes, exactly clause (i).
-/

namespace NCG.Upstream.Ising

open Filter Topology

/-! ## The oscillation calculus -/

/-- Overwrite a single site. -/
def setSite (v : V2) (b : Bool) (τ : V2 → Bool) : V2 → Bool :=
  fun w => if w = v then b else τ w

theorem setSite_self (v : V2) (b : Bool) (τ : V2 → Bool) :
    setSite v b τ v = b := if_pos rfl

theorem setSite_other {v w : V2} (h : w ≠ v) (b : Bool)
    (τ : V2 → Bool) : setSite v b τ w = τ w := if_neg h

theorem setSite_eta (v : V2) (τ : V2 → Bool) :
    setSite v (τ v) τ = τ := by
  funext w
  unfold setSite
  by_cases h : w = v
  · rw [if_pos h, h]
  · rw [if_neg h]

theorem setSite_absorb (v : V2) (b c : Bool) (τ : V2 → Bool) :
    setSite v b (setSite v c τ) = setSite v b τ := by
  funext w
  unfold setSite
  by_cases h : w = v
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, if_neg h]

theorem setSite_comm {v u : V2} (h : v ≠ u) (b c : Bool)
    (τ : V2 → Bool) :
    setSite v b (setSite u c τ) = setSite u c (setSite v b τ) := by
  funext w
  unfold setSite
  by_cases hv : w = v
  · rw [if_pos hv, if_neg (by rw [hv]; exact h), if_pos hv]
  · rw [if_neg hv]
    by_cases hu : w = u
    · rw [if_pos hu, if_pos hu]
    · rw [if_neg hu, if_neg hu, if_neg hv]

/-- The oscillation of `f` at site `v` is at most `δ`. -/
def OscLe (f : (V2 → Bool) → ℝ) (v : V2) (δ : ℝ) : Prop :=
  ∀ τ, |f (setSite v true τ) - f (setSite v false τ)| ≤ δ

/-- Oscillation bounds cover arbitrary value pairs. -/
theorem OscLe.pair {f : (V2 → Bool) → ℝ} {v : V2} {δ : ℝ}
    (h : OscLe f v δ) (hδ : 0 ≤ δ) (b b' : Bool) (τ : V2 → Bool) :
    |f (setSite v b τ) - f (setSite v b' τ)| ≤ δ := by
  cases b <;> cases b'
  · simpa using hδ
  · rw [abs_sub_comm]
    exact h τ
  · exact h τ
  · simpa using hδ

/-- Locality: `f` depends only on the sites of `S`. -/
def IsLocal (S : Finset V2) (f : (V2 → Bool) → ℝ) : Prop :=
  ∀ τ τ' : V2 → Bool, (∀ v ∈ S, τ v = τ' v) → f τ = f τ'

open Classical in
/-- The hybrid configuration: `τ'` on `T`, `τ` elsewhere. -/
noncomputable def mixCfg (T : Finset V2) (τ' τ : V2 → Bool) :
    V2 → Bool :=
  fun w => if w ∈ T then τ' w else τ w

open Classical in
theorem mixCfg_insert {a : V2} {T : Finset V2} (ha : a ∉ T)
    (τ' τ : V2 → Bool) :
    mixCfg (insert a T) τ' τ = setSite a (τ' a) (mixCfg T τ' τ) := by
  funext w
  show (if w ∈ insert a T then τ' w else τ w)
    = if w = a then τ' a else (if w ∈ T then τ' w else τ w)
  by_cases h : w = a
  · rw [if_pos (by rw [h]; exact Finset.mem_insert_self a T),
      if_pos h, h]
  · rw [if_neg h]
    by_cases hT : w ∈ T
    · rw [if_pos hT, if_pos (Finset.mem_insert_of_mem hT)]
    · rw [if_neg hT, if_neg (by
        rw [Finset.mem_insert]
        rintro (h1 | h1)
        · exact h h1
        · exact hT h1)]

open Classical in
/-- Telescoping: hybridization is controlled by the site
oscillations. -/
theorem abs_sub_mixCfg_le {f : (V2 → Bool) → ℝ} {m : V2 → ℝ}
    (hm : ∀ v, 0 ≤ m v) (hosc : ∀ v, OscLe f v (m v))
    (τ' τ : V2 → Bool) :
    ∀ T : Finset V2, |f (mixCfg T τ' τ) - f τ| ≤ ∑ v ∈ T, m v := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
      have h0 : mixCfg ∅ τ' τ = τ := by
        funext w
        unfold mixCfg
        rw [if_neg (Finset.notMem_empty w)]
      rw [h0]
      simp
  | insert a T ha ih =>
      have h1 := abs_sub_le (f (mixCfg (insert a T) τ' τ))
        (f (mixCfg T τ' τ)) (f τ)
      have h2 : |f (mixCfg (insert a T) τ' τ) - f (mixCfg T τ' τ)|
          ≤ m a := by
        rw [mixCfg_insert ha]
        have h3 : mixCfg T τ' τ
            = setSite a (mixCfg T τ' τ a) (mixCfg T τ' τ) :=
          (setSite_eta a _).symm
        nth_rewrite 2 [h3]
        exact (hosc a).pair (hm a) _ _ _
      rw [Finset.sum_insert ha]
      linarith [ih]

open Classical in
/-- **The global oscillation bound**: a local observable with
summable site oscillations varies by at most their total. -/
theorem global_osc_bound {S : Finset V2} {f : (V2 → Bool) → ℝ}
    {m : V2 → ℝ} (hloc : IsLocal S f) (hm : ∀ v, 0 ≤ m v)
    (hosc : ∀ v, OscLe f v (m v)) (τ τ' : V2 → Bool) :
    |f τ - f τ'| ≤ ∑ v ∈ S, m v := by
  have h1 : f (mixCfg S τ' τ) = f τ' := by
    refine hloc _ _ fun v hv => ?_
    unfold mixCfg
    rw [if_pos hv]
  calc |f τ - f τ'| = |f (mixCfg S τ' τ) - f τ| := by
        rw [h1, abs_sub_comm]
    _ ≤ ∑ v ∈ S, m v := abs_sub_mixCfg_le hm hosc τ' τ S

/-! ## The single-site heat-bath kernel -/

/-- The four lattice neighbours. -/
def nbrs (v : V2) : Finset V2 :=
  {v + ((1 : ℤ), (0 : ℤ)), v - ((1 : ℤ), (0 : ℤ)),
    v + ((0 : ℤ), (1 : ℤ)), v - ((0 : ℤ), (1 : ℤ))}

theorem notMem_nbrs (v : V2) : v ∉ nbrs v := by
  obtain ⟨x, y⟩ := v
  simp [nbrs, Prod.ext_iff]
  omega

theorem card_nbrs (v : V2) : (nbrs v).card = 4 := by
  obtain ⟨x, y⟩ := v
  rw [nbrs]
  rw [Finset.card_insert_of_notMem (by
    simp [Prod.ext_iff] <;> omega)]
  rw [Finset.card_insert_of_notMem (by
    simp [Prod.ext_iff] <;> omega)]
  rw [Finset.card_insert_of_notMem (by
    simp [Prod.ext_iff] <;> omega)]
  rw [Finset.card_singleton]

/-- The neighbour field: the sum of the four adjacent spins. -/
noncomputable def nbrField (v : V2) (τ : V2 → Bool) : ℝ :=
  spin (τ (v + ((1 : ℤ), (0 : ℤ))))
    + spin (τ (v - ((1 : ℤ), (0 : ℤ))))
    + spin (τ (v + ((0 : ℤ), (1 : ℤ))))
    + spin (τ (v - ((0 : ℤ), (1 : ℤ))))

/-- The conditional plus-weight and the heat-bath probability. -/
noncomputable def condP (v : V2) (θ : ℝ) (τ : V2 → Bool) : ℝ :=
  Real.exp (θ * nbrField v τ)
    / (Real.exp (θ * nbrField v τ) + Real.exp (-(θ * nbrField v τ)))

theorem condP_pos (v : V2) (θ : ℝ) (τ : V2 → Bool) :
    0 < condP v θ τ :=
  div_pos (Real.exp_pos _)
    (by positivity)

theorem condP_lt_one (v : V2) (θ : ℝ) (τ : V2 → Bool) :
    condP v θ τ < 1 := by
  unfold condP
  rw [div_lt_one (by positivity)]
  nlinarith [Real.exp_pos (-(θ * nbrField v τ))]

/-- The single-site heat-bath update. -/
noncomputable def oneSite (v : V2) (θ : ℝ) (f : (V2 → Bool) → ℝ)
    (τ : V2 → Bool) : ℝ :=
  condP v θ τ * f (setSite v true τ)
    + (1 - condP v θ τ) * f (setSite v false τ)

/-! ## `oneSite` is `dlrK` on singletons -/

theorem patchV_singleton (v : V2)
    (η : ↥({v} : Finset V2) → Bool) (τ : V2 → Bool) :
    patchV {v} η τ
      = setSite v (η ⟨v, Finset.mem_singleton_self v⟩) τ := by
  funext w
  show (if h : w ∈ ({v} : Finset V2) then η ⟨w, h⟩ else τ w)
    = if w = v then η ⟨v, Finset.mem_singleton_self v⟩ else τ w
  by_cases h : w = v
  · subst h
    rw [dif_pos (Finset.mem_singleton_self w), if_pos rfl]
  · rw [dif_neg (by rw [Finset.mem_singleton]; exact h), if_neg h]

instance uniqueSingleton (v : V2) :
    Unique (↥({v} : Finset V2)) where
  default := ⟨v, Finset.mem_singleton_self v⟩
  uniq x := Subtype.ext (Finset.mem_singleton.mp x.2)

/-- The local energy at a single site in field form. -/
theorem eLoc_singleton (v : V2) (θ : ℝ) (b : Bool)
    (τ : V2 → Bool) :
    eLoc {v} θ (setSite v b τ)
      = Real.exp (θ * (spin b * nbrField v τ)) := by
  obtain ⟨x, y⟩ := v
  unfold eLoc
  congr 1
  have hbi : eVol ({((x, y) : V2)} : Finset V2)
      = {(((x, y) : V2), true), (((x, y) : V2), false),
          (((x, y) : V2) - ((1 : ℤ), (0 : ℤ)), true),
          (((x, y) : V2) - ((0 : ℤ), (1 : ℤ)), false)} := by
    unfold eVol
    rw [Finset.singleton_biUnion]
  rw [hbi]
  rw [Finset.sum_insert (by simp [Prod.ext_iff] <;> omega),
    Finset.sum_insert (by simp [Prod.ext_iff] <;> omega),
    Finset.sum_insert (by simp [Prod.ext_iff] <;> omega),
    Finset.sum_singleton]
  have hep1t : ep1 ((((x, y) : V2), true) : IEdge)
      = ((x, y) : V2) + ((1 : ℤ), (0 : ℤ)) := by
    show ((x, y) : V2) + edir true = _
    rw [show edir true = ((1 : ℤ), (0 : ℤ)) from rfl]
  have hep1f : ep1 ((((x, y) : V2), false) : IEdge)
      = ((x, y) : V2) + ((0 : ℤ), (1 : ℤ)) := by
    show ((x, y) : V2) + edir false = _
    rw [show edir false = ((0 : ℤ), (1 : ℤ)) from rfl]
  have hep3 : ep1 ((((x, y) : V2) - ((1 : ℤ), (0 : ℤ)), true)
      : IEdge) = ((x, y) : V2) := by
    show ((x, y) : V2) - ((1 : ℤ), (0 : ℤ)) + edir true = _
    rw [show edir true = ((1 : ℤ), (0 : ℤ)) from rfl]
    exact sub_add_cancel _ _
  have hep4 : ep1 ((((x, y) : V2) - ((0 : ℤ), (1 : ℤ)), false)
      : IEdge) = ((x, y) : V2) := by
    show ((x, y) : V2) - ((0 : ℤ), (1 : ℤ)) + edir false = _
    rw [show edir false = ((0 : ℤ), (1 : ℤ)) from rfl]
    exact sub_add_cancel _ _
  have hne1 : ((x, y) : V2) + ((1 : ℤ), (0 : ℤ)) ≠ ((x, y) : V2) := by
    simp [Prod.ext_iff]
  have hne2 : ((x, y) : V2) + ((0 : ℤ), (1 : ℤ)) ≠ ((x, y) : V2) := by
    simp [Prod.ext_iff]
  have hne3 : ((x, y) : V2) - ((1 : ℤ), (0 : ℤ)) ≠ ((x, y) : V2) := by
    simp [Prod.ext_iff]
  have hne4 : ((x, y) : V2) - ((0 : ℤ), (1 : ℤ)) ≠ ((x, y) : V2) := by
    simp [Prod.ext_iff]
  rw [show ep0 ((((x, y) : V2), true) : IEdge) = ((x, y) : V2)
      from rfl,
    show ep0 ((((x, y) : V2), false) : IEdge) = ((x, y) : V2)
      from rfl,
    show ep0 ((((x, y) : V2) - ((1 : ℤ), (0 : ℤ)), true) : IEdge)
      = ((x, y) : V2) - ((1 : ℤ), (0 : ℤ)) from rfl,
    show ep0 ((((x, y) : V2) - ((0 : ℤ), (1 : ℤ)), false) : IEdge)
      = ((x, y) : V2) - ((0 : ℤ), (1 : ℤ)) from rfl,
    hep1t, hep1f, hep3, hep4]
  rw [setSite_self, setSite_other hne1, setSite_other hne2,
    setSite_other hne3, setSite_other hne4]
  unfold nbrField
  ring

/-- The two conditional weights in field form. -/
theorem weights_form (v : V2) (θ : ℝ) (τ : V2 → Bool) :
    eLoc {v} θ (setSite v true τ) = Real.exp (θ * nbrField v τ)
      ∧ eLoc {v} θ (setSite v false τ)
        = Real.exp (-(θ * nbrField v τ)) := by
  constructor
  · rw [eLoc_singleton]
    congr 1
    show θ * (spin true * nbrField v τ) = θ * nbrField v τ
    rw [show spin true = (1 : ℝ) from rfl]
    ring
  · rw [eLoc_singleton]
    congr 1
    show θ * (spin false * nbrField v τ) = -(θ * nbrField v τ)
    rw [show spin false = (-1 : ℝ) from rfl]
    ring

/-- **The kernel identification**: `oneSite` is `dlrK` on a
singleton. -/
theorem dlrK_singleton (v : V2) (θ : ℝ) (f : (V2 → Bool) → ℝ)
    (τ : V2 → Bool) :
    dlrK ({v} : Finset V2) θ f τ = oneSite v θ f τ := by
  have hsum : ∀ g : (V2 → Bool) → ℝ,
      (∑ η : ↥({v} : Finset V2) → Bool, g (patchV {v} η τ))
        = g (setSite v true τ) + g (setSite v false τ) := by
    intro g
    rw [Fintype.sum_equiv (Equiv.funUnique (↥({v} : Finset V2)) Bool)
      _ (fun b => g (setSite v b τ)) (fun η => by
        rw [patchV_singleton]
        rfl)]
    exact Fintype.sum_bool _
  unfold dlrK zLoc
  rw [hsum (fun τ' => eLoc {v} θ τ' * f τ'), hsum (eLoc {v} θ)]
  obtain ⟨hw1, hw2⟩ := weights_form v θ τ
  rw [hw1, hw2]
  unfold oneSite condP
  set A := Real.exp (θ * nbrField v τ) with hA
  set B := Real.exp (-(θ * nbrField v τ)) with hB
  have hApos : 0 < A := Real.exp_pos _
  have hBpos : 0 < B := Real.exp_pos _
  have hAB : 0 < A + B := by linarith
  field_simp
  ring

/-! ## The sharp influence bound -/

/-- `tanh` in doubled exponential form. -/
theorem tanh_form (θ : ℝ) :
    Real.tanh θ = (Real.exp (2 * θ) - 1) / (Real.exp (2 * θ) + 1) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have h1 : Real.exp θ * Real.exp (-θ) = 1 := by
    rw [← Real.exp_add]
    simp
  have h2 : Real.exp (2 * θ) = Real.exp θ * Real.exp θ := by
    rw [← Real.exp_add]
    ring_nf
  have hp : (0 : ℝ) < Real.exp θ + Real.exp (-θ) := by positivity
  have hp2 : (0 : ℝ) < Real.exp (2 * θ) + 1 := by positivity
  have h3 : (Real.exp θ - Real.exp (-θ)) / 2
      / ((Real.exp θ + Real.exp (-θ)) / 2)
      = (Real.exp θ - Real.exp (-θ))
        / (Real.exp θ + Real.exp (-θ)) := by
    field_simp
  rw [h3, div_eq_div_iff hp.ne' hp2.ne', h2]
  linear_combination (-2 * Real.exp θ) * h1

theorem tanh_nonneg' {θ : ℝ} (hθ : 0 ≤ θ) : 0 ≤ Real.tanh θ := by
  rw [tanh_form]
  have h1 : (1 : ℝ) ≤ Real.exp (2 * θ) := by
    calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (2 * θ) := Real.exp_le_exp.mpr (by linarith)
  exact div_nonneg (by linarith) (by positivity)

/-- The heat-bath probability in doubled form. -/
theorem P_form (a : ℝ) :
    Real.exp a / (Real.exp a + Real.exp (-a))
      = Real.exp (2 * a) / (Real.exp (2 * a) + 1) := by
  have h1 : Real.exp a * Real.exp (-a) = 1 := by
    rw [← Real.exp_add]
    simp
  have h2 : Real.exp (2 * a) = Real.exp a * Real.exp a := by
    rw [← Real.exp_add]
    ring_nf
  have hp : (0 : ℝ) < Real.exp a + Real.exp (-a) := by positivity
  have hp2 : (0 : ℝ) < Real.exp (2 * a) + 1 := by positivity
  rw [div_eq_div_iff hp.ne' hp2.ne', h2]
  linear_combination (-Real.exp a) * h1

/-- Monotonicity of the doubled form. -/
theorem P_mono {a b : ℝ} (hab : a ≤ b) :
    Real.exp (2 * a) / (Real.exp (2 * a) + 1)
      ≤ Real.exp (2 * b) / (Real.exp (2 * b) + 1) := by
  have h1 : Real.exp (2 * a) ≤ Real.exp (2 * b) :=
    Real.exp_le_exp.mpr (by linarith)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [h1]

/-- **The key fraction inequality**: linear interpolation between
the endpoint values `(u-1)(Y+1)²` and `(u-1)(Yu-1)²`. -/
theorem key_frac {X Y u : ℝ} (hY : 0 < Y) (hu : 1 ≤ u)
    (hXY : Y ≤ X) (hX2 : X ≤ Y * u ^ 2) :
    X / (X + 1) - Y / (Y + 1) ≤ (u - 1) / (u + 1) := by
  have hX : 0 < X := lt_of_lt_of_le hY hXY
  have hX1 : (0 : ℝ) < X + 1 := by linarith
  have hY1 : (0 : ℝ) < Y + 1 := by linarith
  have hu1 : (0 : ℝ) < u + 1 := by linarith
  rw [div_sub_div _ _ hX1.ne' hY1.ne',
    div_le_div_iff₀ (by positivity) hu1]
  rcases eq_or_lt_of_le hu with heq | hlt
  · have hXeq : X = Y := le_antisymm (by
      rw [← heq] at hX2
      simpa using hX2) hXY
    rw [hXeq, ← heq]
    ring_nf
    try linarith
  · have hu2 : (0 : ℝ) < Y * (u ^ 2 - 1) := by
      have hm1 : (0 : ℝ) < u - 1 := by linarith
      have hm2 : (0 : ℝ) < u + 1 := by linarith
      have hm3 : (0 : ℝ) < u ^ 2 - 1 := by
        nlinarith [mul_pos hm1 hm2]
      exact mul_pos hY hm3
    have hint1 : (0 : ℝ) ≤ (Y * u ^ 2 - X) * (u - 1) * (Y + 1) ^ 2 :=
      mul_nonneg (mul_nonneg (sub_nonneg.mpr hX2)
        (sub_nonneg.mpr hu)) (sq_nonneg (Y + 1))
    have hint2 : (0 : ℝ) ≤ (X - Y) * (u - 1) * (Y * u - 1) ^ 2 :=
      mul_nonneg (mul_nonneg (sub_nonneg.mpr hXY)
        (sub_nonneg.mpr hu)) (sq_nonneg (Y * u - 1))
    have hid : (u - 1) * ((X + 1) * (Y + 1)) * (Y * (u ^ 2 - 1))
        - (X * (Y + 1) - (X + 1) * Y) * (u + 1) * (Y * (u ^ 2 - 1))
        = (Y * u ^ 2 - X) * (u - 1) * (Y + 1) ^ 2
          + (X - Y) * (u - 1) * (Y * u - 1) ^ 2 := by
      ring
    have hkey : (X * (Y + 1) - (X + 1) * Y) * (u + 1)
        * (Y * (u ^ 2 - 1))
        ≤ (u - 1) * ((X + 1) * (Y + 1)) * (Y * (u ^ 2 - 1)) := by
      linarith [hint1, hint2, hid]
    exact le_of_mul_le_mul_right hkey hu2

/-- **The sharp influence bound**: a field change of at most `2`
moves the heat-bath probability by at most `tanh θ`. -/
theorem condP_diff_le {θ : ℝ} (hθ : 0 ≤ θ) {h₁ h₂ : ℝ}
    (hgap : |h₁ - h₂| ≤ 2) :
    |Real.exp (θ * h₁)
        / (Real.exp (θ * h₁) + Real.exp (-(θ * h₁)))
      - Real.exp (θ * h₂)
        / (Real.exp (θ * h₂) + Real.exp (-(θ * h₂)))|
      ≤ Real.tanh θ := by
  have hcore : ∀ p q : ℝ, q ≤ p → p - q ≤ 2 →
      Real.exp (θ * p)
          / (Real.exp (θ * p) + Real.exp (-(θ * p)))
        - Real.exp (θ * q)
          / (Real.exp (θ * q) + Real.exp (-(θ * q)))
        ≤ Real.tanh θ := by
    intro p q hqp hp2
    rw [P_form (θ * p), P_form (θ * q), tanh_form]
    have hsq : Real.exp (2 * θ) ^ 2 = Real.exp (4 * θ) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    refine key_frac (Real.exp_pos _) ?_ ?_ ?_
    · calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
        _ ≤ Real.exp (2 * θ) := Real.exp_le_exp.mpr (by linarith)
    · refine Real.exp_le_exp.mpr ?_
      have := mul_le_mul_of_nonneg_left hqp hθ
      nlinarith
    · rw [hsq, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have := mul_le_mul_of_nonneg_left hp2 hθ
      nlinarith
  have hmono : ∀ p q : ℝ, q ≤ p →
      Real.exp (θ * q)
          / (Real.exp (θ * q) + Real.exp (-(θ * q)))
        ≤ Real.exp (θ * p)
          / (Real.exp (θ * p) + Real.exp (-(θ * p))) := by
    intro p q hqp
    rw [P_form (θ * p), P_form (θ * q)]
    exact P_mono (mul_le_mul_of_nonneg_left hqp hθ)
  rcases le_total h₂ h₁ with hle | hle
  · rw [abs_of_nonneg (by linarith [hmono h₁ h₂ hle])]
    refine hcore h₁ h₂ hle ?_
    have := abs_le.mp hgap
    linarith [this.2]
  · rw [abs_sub_comm,
      abs_of_nonneg (by linarith [hmono h₂ h₁ hle])]
    refine hcore h₂ h₁ hle ?_
    have := abs_le.mp hgap
    linarith [this.1]

/-! ## The Dobrushin oscillation estimates -/

theorem nbrField_setSite_self (v : V2) (b : Bool)
    (τ : V2 → Bool) :
    nbrField v (setSite v b τ) = nbrField v τ := by
  obtain ⟨x, y⟩ := v
  unfold nbrField
  rw [setSite_other (by simp [Prod.ext_iff]) b τ,
    setSite_other (by simp [Prod.ext_iff]) b τ,
    setSite_other (by simp [Prod.ext_iff]) b τ,
    setSite_other (by simp [Prod.ext_iff]) b τ]

/-- **T1**: the update kills the oscillation at its own site. -/
theorem oscLe_oneSite_self (v : V2) (θ : ℝ)
    (f : (V2 → Bool) → ℝ) : OscLe (oneSite v θ f) v 0 := by
  intro τ
  have hkey : ∀ b : Bool,
      oneSite v θ f (setSite v b τ) = oneSite v θ f τ := by
    intro b
    unfold oneSite condP
    rw [nbrField_setSite_self, setSite_absorb, setSite_absorb]
  rw [hkey true, hkey false, sub_self, abs_zero]

theorem nbrField_setSite_notMem {u v : V2} (hu : u ∉ nbrs v)
    (b : Bool) (τ : V2 → Bool) :
    nbrField v (setSite u b τ) = nbrField v τ := by
  simp only [nbrs, Finset.mem_insert, Finset.mem_singleton,
    not_or] at hu
  obtain ⟨h1, h2, h3, h4⟩ := hu
  unfold nbrField
  rw [setSite_other (fun h => h1 h.symm) b τ,
    setSite_other (fun h => h2 h.symm) b τ,
    setSite_other (fun h => h3 h.symm) b τ,
    setSite_other (fun h => h4 h.symm) b τ]

theorem nbrField_gap {u v : V2} (hu : u ∈ nbrs v)
    (τ : V2 → Bool) :
    |nbrField v (setSite u true τ)
      - nbrField v (setSite u false τ)| ≤ 2 := by
  have hs1 : spin true = (1 : ℝ) := by simp [spin]
  have hs2 : spin false = (-1 : ℝ) := by simp [spin]
  obtain ⟨x, y⟩ := v
  simp only [nbrs, Finset.mem_insert, Finset.mem_singleton] at hu
  unfold nbrField
  rcases hu with h | h | h | h
  all_goals subst h
  all_goals rw [setSite_self, setSite_self,
    setSite_other (by simp [Prod.ext_iff] <;> omega) true τ,
    setSite_other (by simp [Prod.ext_iff] <;> omega) false τ,
    setSite_other (by simp [Prod.ext_iff] <;> omega) true τ,
    setSite_other (by simp [Prod.ext_iff] <;> omega) false τ,
    setSite_other (by simp [Prod.ext_iff] <;> omega) true τ,
    setSite_other (by simp [Prod.ext_iff] <;> omega) false τ]
  all_goals rw [hs1, hs2, abs_le]
  all_goals exact ⟨by linarith, by linarith⟩

open Classical in
/-- **T2**: the update leaks at most `tanh θ` of the site-`v`
oscillation to each neighbour and preserves the rest. -/
theorem oscLe_oneSite_other {u v : V2} (huv : u ≠ v) {θ : ℝ}
    (hθ : 0 ≤ θ) {f : (V2 → Bool) → ℝ} {δu δv : ℝ}
    (hu : OscLe f u δu) (hv : OscLe f v δv)
    (hδu : 0 ≤ δu) (hδv : 0 ≤ δv) :
    OscLe (oneSite v θ f) u
      (δu + (if u ∈ nbrs v then Real.tanh θ else 0) * δv) := by
  have hcoeff : 0 ≤ (if u ∈ nbrs v then Real.tanh θ else 0) := by
    by_cases h : u ∈ nbrs v
    · rw [if_pos h]
      exact tanh_nonneg' hθ
    · rw [if_neg h]
  intro τ
  have hp1 := condP_pos v θ (setSite u true τ)
  have hp1' := condP_lt_one v θ (setSite u true τ)
  have hdecomp : oneSite v θ f (setSite u true τ)
      - oneSite v θ f (setSite u false τ)
      = condP v θ (setSite u true τ)
          * (f (setSite v true (setSite u true τ))
            - f (setSite v true (setSite u false τ)))
        + (1 - condP v θ (setSite u true τ))
          * (f (setSite v false (setSite u true τ))
            - f (setSite v false (setSite u false τ)))
        + (condP v θ (setSite u true τ)
            - condP v θ (setSite u false τ))
          * (f (setSite v true (setSite u false τ))
            - f (setSite v false (setSite u false τ))) := by
    unfold oneSite
    ring
  have hA : |f (setSite v true (setSite u true τ))
      - f (setSite v true (setSite u false τ))| ≤ δu := by
    rw [setSite_comm (Ne.symm huv), setSite_comm (Ne.symm huv)]
    exact hu (setSite v true τ)
  have hB : |f (setSite v false (setSite u true τ))
      - f (setSite v false (setSite u false τ))| ≤ δu := by
    rw [setSite_comm (Ne.symm huv), setSite_comm (Ne.symm huv)]
    exact hu (setSite v false τ)
  have hC : |f (setSite v true (setSite u false τ))
      - f (setSite v false (setSite u false τ))| ≤ δv :=
    hv (setSite u false τ)
  have hp : |condP v θ (setSite u true τ)
      - condP v θ (setSite u false τ)|
      ≤ (if u ∈ nbrs v then Real.tanh θ else 0) := by
    by_cases hmem : u ∈ nbrs v
    · rw [if_pos hmem]
      exact condP_diff_le hθ (nbrField_gap hmem τ)
    · rw [if_neg hmem]
      have he : nbrField v (setSite u true τ)
          = nbrField v (setSite u false τ) := by
        rw [nbrField_setSite_notMem hmem,
          nbrField_setSite_notMem hmem]
      unfold condP
      rw [he, sub_self, abs_zero]
  set p := condP v θ (setSite u true τ) with hpdef
  set q := condP v θ (setSite u false τ) with hqdef
  set A := f (setSite v true (setSite u true τ))
    - f (setSite v true (setSite u false τ)) with hAdef
  set B := f (setSite v false (setSite u true τ))
    - f (setSite v false (setSite u false τ)) with hBdef
  set Cc := f (setSite v true (setSite u false τ))
    - f (setSite v false (setSite u false τ)) with hCdef
  rw [hdecomp]
  have h1 : |p * A + (1 - p) * B + (p - q) * Cc|
      ≤ |p * A| + |(1 - p) * B| + |(p - q) * Cc| :=
    (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  have e1 : |p * A| ≤ p * δu := by
    rw [abs_mul, abs_of_pos hp1]
    exact mul_le_mul_of_nonneg_left hA hp1.le
  have e2 : |(1 - p) * B| ≤ δu - p * δu := by
    rw [abs_mul, abs_of_pos (by linarith)]
    have h3 := mul_le_mul_of_nonneg_left hB
      (by linarith : (0 : ℝ) ≤ 1 - p)
    nlinarith
  have e3 : |(p - q) * Cc|
      ≤ (if u ∈ nbrs v then Real.tanh θ else 0) * δv := by
    rw [abs_mul]
    exact mul_le_mul hp hC (abs_nonneg _) hcoeff
  linarith

/-! ## Oscillation data and the greedy descent -/

/-- The update preserves sup bounds. -/
theorem abs_oneSite_le (v : V2) (θ : ℝ) {f : (V2 → Bool) → ℝ}
    {C : ℝ} (hb : ∀ τ, |f τ| ≤ C) (τ : V2 → Bool) :
    |oneSite v θ f τ| ≤ C := by
  have hp := condP_pos v θ τ
  have hp' := condP_lt_one v θ τ
  unfold oneSite
  have h1 : |condP v θ τ * f (setSite v true τ)|
      ≤ condP v θ τ * C := by
    rw [abs_mul, abs_of_pos hp]
    exact mul_le_mul_of_nonneg_left (hb _) hp.le
  have h2 : |(1 - condP v θ τ) * f (setSite v false τ)|
      ≤ C - condP v θ τ * C := by
    rw [abs_mul, abs_of_pos (by linarith)]
    have h3 := mul_le_mul_of_nonneg_left (hb (setSite v false τ))
      (by linarith : (0 : ℝ) ≤ 1 - condP v θ τ)
    nlinarith
  calc |condP v θ τ * f (setSite v true τ)
      + (1 - condP v θ τ) * f (setSite v false τ)|
      ≤ |condP v θ τ * f (setSite v true τ)|
        + |(1 - condP v θ τ) * f (setSite v false τ)| :=
        abs_add_le _ _
    _ ≤ C := by linarith

theorem mem_nbrs_all (v : V2) :
    v + ((1 : ℤ), (0 : ℤ)) ∈ nbrs v
    ∧ v - ((1 : ℤ), (0 : ℤ)) ∈ nbrs v
    ∧ v + ((0 : ℤ), (1 : ℤ)) ∈ nbrs v
    ∧ v - ((0 : ℤ), (1 : ℤ)) ∈ nbrs v :=
  ⟨Finset.mem_insert_self _ _,
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_self _ _)),
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))⟩

/-- The update spreads locality only to the neighbours. -/
theorem isLocal_oneSite {S : Finset V2} {f : (V2 → Bool) → ℝ}
    (hloc : IsLocal S f) (v : V2) (θ : ℝ) :
    IsLocal (S ∪ nbrs v) (oneSite v θ f) := by
  intro τ τ' hagree
  obtain ⟨hm1, hm2, hm3, hm4⟩ := mem_nbrs_all v
  have hfield : nbrField v τ = nbrField v τ' := by
    unfold nbrField
    rw [hagree _ (Finset.mem_union_right _ hm1),
      hagree _ (Finset.mem_union_right _ hm2),
      hagree _ (Finset.mem_union_right _ hm3),
      hagree _ (Finset.mem_union_right _ hm4)]
  have hf : ∀ b : Bool, f (setSite v b τ) = f (setSite v b τ') := by
    intro b
    refine hloc _ _ fun w hw => ?_
    by_cases hwv : w = v
    · rw [hwv, setSite_self, setSite_self]
    · rw [setSite_other hwv, setSite_other hwv]
      exact hagree w (Finset.mem_union_left _ hw)
  unfold oneSite condP
  rw [hfield, hf true, hf false]

open Classical in
/-- The oscillation-mass update. -/
noncomputable def updM (v : V2) (θ : ℝ) (m : V2 → ℝ) : V2 → ℝ :=
  fun u => if u = v then 0
    else if u ∈ nbrs v then m u + Real.tanh θ * m v
    else m u

/-- **The oscillation data** of an observable: a finite support with
certified site-oscillation bounds. -/
structure OscData (θ C : ℝ) (f : (V2 → Bool) → ℝ) where
  S : Finset V2
  m : V2 → ℝ
  hb : ∀ τ, |f τ| ≤ C
  hloc : IsLocal S f
  hm : ∀ v, 0 ≤ m v
  hosc : ∀ v, OscLe f v (m v)
  hoff : ∀ v ∉ S, m v = 0

/-- **A DLR state**: normalized, monotone on bounded observables,
and blind to single-site heat-bath resampling. -/
structure DLRState (θ : ℝ) where
  val : ((V2 → Bool) → ℝ) → ℝ
  const : ∀ c : ℝ, val (fun _ => c) = c
  mono : ∀ {f g : (V2 → Bool) → ℝ} {Cf Cg : ℝ},
    (∀ τ, |f τ| ≤ Cf) → (∀ τ, |g τ| ≤ Cg) →
    (∀ τ, f τ ≤ g τ) → val f ≤ val g
  dlr : ∀ (v : V2) {f : (V2 → Bool) → ℝ} {C : ℝ},
    (∀ τ, |f τ| ≤ C) → val (dlrK {v} θ f) = val f

open Classical in
theorem oscLe_update {θ C : ℝ} (hθ : 0 ≤ θ)
    {f : (V2 → Bool) → ℝ} (D : OscData θ C f) (v : V2) :
    ∀ u, OscLe (oneSite v θ f) u (updM v θ D.m u) := by
  intro u
  unfold updM
  by_cases h1 : u = v
  · rw [if_pos h1, h1]
    exact oscLe_oneSite_self v θ f
  · rw [if_neg h1]
    by_cases h2 : u ∈ nbrs v
    · rw [if_pos h2]
      have h3 := oscLe_oneSite_other h1 hθ (D.hosc u) (D.hosc v)
        (D.hm u) (D.hm v)
      rwa [if_pos h2] at h3
    · rw [if_neg h2]
      have h3 := oscLe_oneSite_other h1 hθ (D.hosc u) (D.hosc v)
        (D.hm u) (D.hm v)
      rwa [if_neg h2, zero_mul, add_zero] at h3

open Classical in
/-- **The mass identity** of one greedy update. -/
theorem sum_updM {θ C : ℝ} {f : (V2 → Bool) → ℝ}
    (D : OscData θ C f) (v : V2) (hv : v ∈ D.S) :
    ∑ u ∈ D.S ∪ nbrs v, updM v θ D.m u
      = (∑ u ∈ D.S, D.m u)
        - (1 - 4 * Real.tanh θ) * D.m v := by
  have hpt : ∀ u, updM v θ D.m u
      = D.m u + ((if u = v then -D.m v else 0)
        + (if u ∈ nbrs v then Real.tanh θ * D.m v else 0)) := by
    intro u
    unfold updM
    by_cases h1 : u = v
    · rw [if_pos h1, if_pos h1, h1, if_neg (notMem_nbrs v)]
      ring
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : u ∈ nbrs v
      · rw [if_pos h2, if_pos h2]
        ring
      · rw [if_neg h2, if_neg h2]
        ring
  rw [Finset.sum_congr rfl fun u _ => hpt u]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hsub : D.S ⊆ D.S ∪ nbrs v := Finset.subset_union_left
  have h1 : ∑ u ∈ D.S ∪ nbrs v, D.m u = ∑ u ∈ D.S, D.m u :=
    (Finset.sum_subset hsub fun x _ hx => D.hoff x hx).symm
  have h2 : (∑ u ∈ D.S ∪ nbrs v,
      (if u = v then -D.m v else 0)) = -D.m v := by
    rw [Finset.sum_ite_eq' (D.S ∪ nbrs v) v (fun _ => -D.m v)]
    rw [if_pos (Finset.mem_union_left _ hv)]
  have h3 : (∑ u ∈ D.S ∪ nbrs v,
      (if u ∈ nbrs v then Real.tanh θ * D.m v else 0))
      = 4 * (Real.tanh θ * D.m v) := by
    rw [← Finset.sum_filter]
    have hfe : (D.S ∪ nbrs v).filter (fun u => u ∈ nbrs v)
        = nbrs v := by
      ext u
      rw [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨-, h⟩
        exact h
      · intro h
        exact ⟨Or.inr h, h⟩
    rw [hfe, Finset.sum_const, card_nbrs, nsmul_eq_mul]
    norm_num
  rw [h1, h2, h3]
  ring

open Classical in
/-- **One greedy step**: resample the heaviest site. -/
theorem greedy_step {θ C : ℝ} (hθ : 0 ≤ θ)
    (hα : 4 * Real.tanh θ < 1) {f : (V2 → Bool) → ℝ}
    (D : OscData θ C f) (hne : D.S.Nonempty) :
    ∃ (g : (V2 → Bool) → ℝ) (E : OscData θ C g),
      (∀ ω : DLRState θ, ω.val g = ω.val f) ∧
      E.S.card ≤ D.S.card + 4 ∧
      (∑ u ∈ E.S, E.m u) ≤ (∑ u ∈ D.S, D.m u)
        - (1 - 4 * Real.tanh θ)
          * ((∑ u ∈ D.S, D.m u) / D.S.card) := by
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image D.S D.m hne
  have hcardpos : (0 : ℝ) < D.S.card := by
    rw [Nat.cast_pos, Finset.card_pos]
    exact hne
  have hMle : (∑ u ∈ D.S, D.m u) ≤ D.S.card * D.m v := by
    calc (∑ u ∈ D.S, D.m u) ≤ ∑ _u ∈ D.S, D.m v :=
        Finset.sum_le_sum fun u hu => hmax u hu
      _ = D.S.card * D.m v := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hdivle : (∑ u ∈ D.S, D.m u) / D.S.card ≤ D.m v := by
    rw [div_le_iff₀ hcardpos, mul_comm]
    exact hMle
  refine ⟨oneSite v θ f,
    ⟨D.S ∪ nbrs v, updM v θ D.m,
      abs_oneSite_le v θ D.hb,
      isLocal_oneSite D.hloc v θ,
      ?_, oscLe_update hθ D v, ?_⟩, ?_, ?_, ?_⟩
  · intro u
    unfold updM
    by_cases h1 : u = v
    · rw [if_pos h1]
    · rw [if_neg h1]
      by_cases h2 : u ∈ nbrs v
      · rw [if_pos h2]
        have h3 := mul_nonneg (tanh_nonneg' hθ) (D.hm v)
        have h4 := D.hm u
        linarith
      · rw [if_neg h2]
        exact D.hm u
  · intro u hu
    rw [Finset.mem_union, not_or] at hu
    unfold updM
    rw [if_neg (fun h => hu.1 (by rw [h]; exact hv)),
      if_neg hu.2]
    exact D.hoff u hu.1
  · intro ω
    have hfn : dlrK ({v} : Finset V2) θ f = oneSite v θ f :=
      funext (dlrK_singleton v θ f)
    rw [← hfn]
    exact ω.dlr v D.hb
  · calc (D.S ∪ nbrs v).card ≤ D.S.card + (nbrs v).card :=
        Finset.card_union_le _ _
      _ = D.S.card + 4 := by rw [card_nbrs]
  · rw [sum_updM D v hv]
    have h1 : (1 - 4 * Real.tanh θ)
        * ((∑ u ∈ D.S, D.m u) / D.S.card)
        ≤ (1 - 4 * Real.tanh θ) * D.m v :=
      mul_le_mul_of_nonneg_left hdivle (by linarith)
    linarith

open Classical in
/-- **The oscillation collapses**: greedy resampling drives the
total oscillation below any positive threshold, without changing
any DLR state's value.  The engine is the divergence of the
harmonic series against the linearly growing support. -/
theorem osc_to_eps {θ C : ℝ} (hθ : 0 ≤ θ)
    (hα : 4 * Real.tanh θ < 1) {f : (V2 → Bool) → ℝ}
    (D : OscData θ C f) (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : (V2 → Bool) → ℝ) (E : OscData θ C g),
      (∀ ω : DLRState θ, ω.val g = ω.val f) ∧
      (∑ u ∈ E.S, E.m u) ≤ ε := by
  set M₀ := ∑ u ∈ D.S, D.m u with hM₀
  set s₀ := D.S.card with hs₀
  set κ := (1 - 4 * Real.tanh θ) * ε with hκ
  have hκpos : 0 < κ := by
    have h0 : (0 : ℝ) < 1 - 4 * Real.tanh θ := by linarith
    exact mul_pos h0 hε
  by_cases hM₀ε : M₀ ≤ ε
  · exact ⟨f, D, fun ω => rfl, hM₀ε⟩
  have hM₀gt : ε < M₀ := lt_of_not_ge hM₀ε
  have hs₀pos : 0 < s₀ := by
    rw [hs₀, Finset.card_pos]
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    have h6 : M₀ = 0 := by
      rw [hM₀, hc, Finset.sum_empty]
    linarith
  have main : ∀ k : ℕ, ∃ (g : (V2 → Bool) → ℝ)
      (E : OscData θ C g),
      (∀ ω : DLRState θ, ω.val g = ω.val f) ∧
      E.S.card ≤ s₀ + 4 * k ∧
      ((∑ u ∈ E.S, E.m u) ≤ ε ∨
        (∑ u ∈ E.S, E.m u) ≤ M₀
          - κ * ∑ j ∈ Finset.range k,
              1 / ((s₀ : ℝ) + 4 * (j : ℝ))) := by
    intro k
    induction k with
    | zero =>
        refine ⟨f, D, fun ω => rfl, by omega, Or.inr ?_⟩
        simp [hM₀]
    | succ k ih =>
        obtain ⟨g, E, hinv, hcard, hM⟩ := ih
        rcases hM with hdone | hM
        · exact ⟨g, E, hinv, by omega, Or.inl hdone⟩
        by_cases hMε : (∑ u ∈ E.S, E.m u) ≤ ε
        · exact ⟨g, E, hinv, by omega, Or.inl hMε⟩
        have hMgt : ε < ∑ u ∈ E.S, E.m u := lt_of_not_ge hMε
        have hne : E.S.Nonempty := by
          rw [← Finset.card_pos]
          by_contra hc
          have h5 : E.S.card = 0 := by omega
          have h6 : E.S = ∅ := Finset.card_eq_zero.mp h5
          rw [h6, Finset.sum_empty] at hMgt
          linarith
        obtain ⟨g', E', hinv', hcard', hM'⟩ :=
          greedy_step hθ hα E hne
        refine ⟨g', E', fun ω => (hinv' ω).trans (hinv ω),
          by omega, Or.inr ?_⟩
        rw [Finset.sum_range_succ, mul_add]
        have hcards : (0 : ℝ) < E.S.card := by
          rw [Nat.cast_pos, Finset.card_pos]
          exact hne
        have hcardle : (E.S.card : ℝ) ≤ (s₀ : ℝ) + 4 * (k : ℝ) := by
          have h4 : ((E.S.card : ℕ) : ℝ)
              ≤ ((s₀ + 4 * k : ℕ) : ℝ) := Nat.cast_le.mpr hcard
          push_cast at h4
          linarith
        have hden : (0 : ℝ) < (s₀ : ℝ) + 4 * (k : ℝ) :=
          lt_of_lt_of_le hcards hcardle
        have hfrac : ε / ((s₀ : ℝ) + 4 * (k : ℝ))
            ≤ (∑ u ∈ E.S, E.m u) / E.S.card := by
          have h7 : ε / ((s₀ : ℝ) + 4 * (k : ℝ))
              ≤ ε / (E.S.card : ℝ) := by
            rw [div_le_div_iff₀ hden hcards]
            nlinarith [hε.le, hcardle]
          have h8 : ε / (E.S.card : ℝ)
              ≤ (∑ u ∈ E.S, E.m u) / E.S.card := by
            rw [div_le_div_iff₀ hcards hcards]
            nlinarith [hMgt.le, hcards]
          exact h7.trans h8
        have hstep : κ * (1 / ((s₀ : ℝ) + 4 * (k : ℝ)))
            ≤ (1 - 4 * Real.tanh θ)
              * ((∑ u ∈ E.S, E.m u) / E.S.card) := by
          rw [hκ]
          have h3 : (0 : ℝ) ≤ 1 - 4 * Real.tanh θ := by linarith
          calc (1 - 4 * Real.tanh θ) * ε
              * (1 / ((s₀ : ℝ) + 4 * (k : ℝ)))
              = (1 - 4 * Real.tanh θ)
                * (ε / ((s₀ : ℝ) + 4 * (k : ℝ))) := by ring
            _ ≤ (1 - 4 * Real.tanh θ)
                * ((∑ u ∈ E.S, E.m u) / E.S.card) :=
              mul_le_mul_of_nonneg_left hfrac h3
        linarith
  have hdiv := Real.tendsto_sum_range_one_div_nat_succ_atTop
  have hs0R : (1 : ℝ) ≤ (s₀ : ℝ) := by exact_mod_cast hs₀pos
  have hcomp : ∀ K : ℕ, (1 / ((s₀ : ℝ) + 4))
      * (∑ j ∈ Finset.range K, 1 / ((j : ℝ) + 1))
      ≤ ∑ j ∈ Finset.range K, 1 / ((s₀ : ℝ) + 4 * (j : ℝ)) := by
    intro K
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [div_mul_div_comm, one_mul]
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    refine one_div_le_one_div_of_le (by nlinarith) (by nlinarith)
  obtain ⟨K, hK⟩ := (Filter.tendsto_atTop.mp hdiv
    ((M₀ + 1) * ((s₀ : ℝ) + 4) / κ)).exists
  obtain ⟨g, E, hinv, -, hM⟩ := main K
  rcases hM with h | h
  · exact ⟨g, E, hinv, h⟩
  · have hM0 : 0 ≤ ∑ u ∈ E.S, E.m u :=
      Finset.sum_nonneg fun u _ => E.hm u
    have hs4 : (0 : ℝ) < (s₀ : ℝ) + 4 := by linarith
    have h7 : (1 / ((s₀ : ℝ) + 4))
        * ((M₀ + 1) * ((s₀ : ℝ) + 4) / κ) = (M₀ + 1) / κ := by
      field_simp
    have h8 : (M₀ + 1) / κ
        ≤ ∑ j ∈ Finset.range K, 1 / ((s₀ : ℝ) + 4 * (j : ℝ)) := by
      rw [← h7]
      calc (1 / ((s₀ : ℝ) + 4))
          * ((M₀ + 1) * ((s₀ : ℝ) + 4) / κ)
          ≤ (1 / ((s₀ : ℝ) + 4))
            * (∑ j ∈ Finset.range K, 1 / ((j : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hK (by positivity)
        _ ≤ ∑ j ∈ Finset.range K, 1 / ((s₀ : ℝ) + 4 * (j : ℝ)) :=
            hcomp K
    have h9 : M₀ + 1
        ≤ κ * ∑ j ∈ Finset.range K, 1 / ((s₀ : ℝ) + 4 * (j : ℝ)) := by
      have h10 := (div_le_iff₀ hκpos).mp h8
      nlinarith [h10]
    exact ⟨g, E, hinv, by linarith⟩

/-! ## Uniqueness and clause (i) -/

open Classical in
/-- The initial oscillation data of a bounded local observable. -/
noncomputable def initData {θ C : ℝ} {S : Finset V2}
    {f : (V2 → Bool) → ℝ} (hb : ∀ τ, |f τ| ≤ C)
    (hloc : IsLocal S f) : OscData θ C f where
  S := S
  m := fun v => if v ∈ S then 2 * C else 0
  hb := hb
  hloc := hloc
  hm := by
    intro v
    have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hb fun _ => true)
    by_cases h : v ∈ S
    · rw [if_pos h]
      linarith
    · rw [if_neg h]
  hosc := by
    intro v
    by_cases h : v ∈ S
    · rw [if_pos h]
      intro τ
      have h1 := hb (setSite v true τ)
      have h2 := hb (setSite v false τ)
      have h3 := abs_sub_le (f (setSite v true τ)) 0
        (f (setSite v false τ))
      simp only [sub_zero, zero_sub, abs_neg] at h3
      linarith
    · rw [if_neg h]
      intro τ
      have h4 : f (setSite v true τ) = f (setSite v false τ) := by
        refine hloc _ _ fun w hw => ?_
        have hwv : w ≠ v := fun he => h (he ▸ hw)
        rw [setSite_other hwv, setSite_other hwv]
      rw [h4, sub_self, abs_zero]
  hoff := fun v hv => if_neg hv

open Classical in
/-- **Dobrushin uniqueness**: at `4·tanh θ < 1` any two DLR states
agree on every bounded local observable — the infinite-volume Gibbs
state is unique. -/
theorem dlrState_unique {θ : ℝ} (hθ : 0 ≤ θ)
    (hα : 4 * Real.tanh θ < 1) (ω₁ ω₂ : DLRState θ)
    {S : Finset V2} {f : (V2 → Bool) → ℝ} {C : ℝ}
    (hb : ∀ τ, |f τ| ≤ C) (hloc : IsLocal S f) :
    ω₁.val f = ω₂.val f := by
  have key : ∀ ε : ℝ, 0 < ε → |ω₁.val f - ω₂.val f| ≤ 2 * ε := by
    intro ε hε
    obtain ⟨g, E, hinv, hM⟩ :=
      osc_to_eps hθ hα (initData hb hloc) ε hε
    set c := g (fun _ => true) with hc
    have hgc : ∀ τ, |g τ - c| ≤ ε := fun τ =>
      (global_osc_bound E.hloc E.hm E.hosc τ (fun _ => true)).trans
        hM
    have habs : ∀ ω : DLRState θ, |ω.val g - c| ≤ ε := by
      intro ω
      have hub : ω.val g ≤ c + ε := by
        have h5 := ω.mono E.hb
          (g := fun _ => c + ε) (Cg := |c| + ε)
          (fun _ => abs_le.mpr
            ⟨by linarith [neg_abs_le c], by linarith [le_abs_self c]⟩)
          (fun τ => by
            have h6 := abs_le.mp (hgc τ)
            linarith [h6.2])
        rwa [ω.const] at h5
      have hlb : c - ε ≤ ω.val g := by
        have h5 := ω.mono (f := fun _ => c - ε) (Cf := |c| + ε)
          (fun _ => abs_le.mpr
            ⟨by linarith [neg_abs_le c], by linarith [le_abs_self c]⟩)
          E.hb
          (fun τ => by
            have h6 := abs_le.mp (hgc τ)
            linarith [h6.1])
        rwa [ω.const] at h5
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    have h1 := habs ω₁
    have h2 := habs ω₂
    rw [hinv ω₁] at h1
    rw [hinv ω₂] at h2
    have h3 := abs_le.mp h1
    have h4 := abs_le.mp h2
    rw [abs_le]
    exact ⟨by linarith [h3.1, h4.2], by linarith [h3.2, h4.1]⟩
  by_contra hne
  have hd : 0 < |ω₁.val f - ω₂.val f| :=
    abs_pos.mpr (sub_ne_zero.mpr hne)
  have h5 := key (|ω₁.val f - ω₂.val f| / 4) (by linarith)
  linarith

/-- The plus phase is monotone. -/
theorem gibbsPlus_mono (θ : ℝ) {f g : (V2 → Bool) → ℝ}
    {Cf Cg : ℝ} (hf : ∀ τ, |f τ| ≤ Cf) (hg : ∀ τ, |g τ| ≤ Cg)
    (h : ∀ τ, f τ ≤ g τ) : gibbsPlus θ f ≤ gibbsPlus θ g :=
  le_of_tendsto_of_tendsto' (gibbsPlus_spec (θ := θ) hf)
    (gibbsPlus_spec (θ := θ) hg) (fun n => expec_mono θ h)

/-- **The plus phase is a DLR state.** -/
noncomputable def gibbsPlusState (θ : ℝ) : DLRState θ where
  val := gibbsPlus θ
  const := gibbsPlus_const θ
  mono := fun {f g Cf Cg} hf hg h => gibbsPlus_mono θ hf hg h
  dlr := fun v {f C} hf => gibbsPlus_dlr θ {v} hf

/-- **The minus phase is a DLR state.** -/
noncomputable def gibbsMinusState (θ : ℝ) : DLRState θ where
  val := gibbsMinus θ
  const := gibbsMinus_const θ
  mono := fun {f g Cf Cg} hf hg h =>
    gibbsPlus_mono θ (fun τ => hf (flipAll τ))
      (fun τ => hg (flipAll τ)) (fun τ => h (flipAll τ))
  dlr := fun v {f C} hf => gibbsMinus_dlr θ {v} hf

/-- **Clause (i), uniqueness**: at high temperature the plus and
minus phases coincide on every bounded local observable — the
infinite-volume Gibbs state is unique and deck-flip (exchange)
invariant. -/
theorem gibbsPlus_eq_gibbsMinus_highTemp {θ : ℝ} (hθ : 0 ≤ θ)
    (hα : 4 * Real.tanh θ < 1) {S : Finset V2}
    {f : (V2 → Bool) → ℝ} {C : ℝ} (hb : ∀ τ, |f τ| ≤ C)
    (hloc : IsLocal S f) :
    gibbsPlus θ f = gibbsMinus θ f :=
  dlrState_unique hθ hα (gibbsPlusState θ) (gibbsMinusState θ)
    hb hloc

/-- **Clause (i), zero defect**: the unique high-temperature state
has zero magnetization, so the translational torsion defect
vanishes. -/
theorem gibbsPlus_spin_zero {θ : ℝ} (hθ : 0 ≤ θ)
    (hα : 4 * Real.tanh θ < 1) :
    gibbsPlus θ (fun τ => spin (τ 0)) = 0 := by
  have hloc : IsLocal {(0 : V2)} (fun τ => spin (τ 0)) := by
    intro τ τ' h
    show spin (τ 0) = spin (τ' 0)
    rw [h 0 (Finset.mem_singleton_self 0)]
  have h1 := gibbsPlus_eq_gibbsMinus_highTemp hθ hα
    (fun τ => spin_abs_le _) hloc
  have h2 : gibbsMinus θ (fun τ => spin (τ 0))
      = -gibbsPlus θ (fun τ => spin (τ 0)) := by
    unfold gibbsMinus
    have h3 : (fun τ : V2 → Bool => spin (flipAll τ 0))
        = fun τ : V2 → Bool => (-1 : ℝ) * spin (τ 0) :=
      funext fun τ => by
        rw [show flipAll τ 0 = !(τ 0) from rfl, spin_not]
        ring
    rw [h3, gibbsPlus_smul θ (-1) (fun τ => spin_abs_le _)]
    ring
  rw [h2] at h1
  linarith

end NCG.Upstream.Ising
