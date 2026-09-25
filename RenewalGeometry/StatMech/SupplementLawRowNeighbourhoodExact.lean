/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Chronological row neighbourhoods and profile transport
  (`thm:supp-law-row-neighbourhood`, `prop:supp-law-transport`;
  emergent-spacetime manuscript)

## Row neighbourhoods (`thm:supp-law-row-neighbourhood`)

A chronological word is generated stage by stage: at stage `j`, after the
prefix `π` (the list of letters executed so far), an arbitrary finite
transition row `K j π : E → ℝ` — possibly depending on the entire past —
selects the next letter.  The stage cost `c j π e ≥ 0` is a function of the
prefix and the letter only (`eq:main-law-cost`), and the word cost is the sum
of the stage costs.  Stopped prefixes carry zero future cost, so the
conditional mean bound `∑ₑ K(e | π) c(π, e) ≤ M τ_j h⁴` is only a
constraint at live prefixes.

* `WordProcess`: the stage kernels with nonnegative rows summing to one.
* `WordProcess.expectAux`, `WordProcess.expect`, `WordProcess.prob`: the
  finite-path expectation (tower recursion) and the induced probability.
* `WordProcess.expect_totalCost_le`: the boxed expectation bound
  `𝔼 C_h ≤ M T h⁴` from the per-prefix conditional moment bound
  (`eq:supp-law-row-moment`), by conditioning on live prefixes.
* `WordProcess.prob_lt_le_expect_div`: Markov's inequality for the finite
  path law; `WordProcess.prob_cost_gt_le`: the boxed
  `ℙ{C_h > h²} ≤ M T h²` (`eq:supp-law-row-probability`).
* `odd_cutoff_eventually_not_exceptional`: along `h_m = (2m+1)⁻¹` the
  exceptional probabilities `≤ M T h_m²` are summable, so under any common
  coupling the exceptional events happen only finitely often almost surely
  (first Borel–Cantelli lemma, no independence used).
* `rowConstraintSet`, `isOpen_rowConstraintSet`, `convex_rowConstraintSet`,
  `isOpen_rowConstraintSet_restrict`, `rowConstraintSet_nonempty`,
  `rowConstraintSet_exists_pos_row`: at fixed cutoff and finite grammar the
  strict conditional-mean inequalities cut a relatively open convex subset of
  the product of row simplexes, nonempty when a letter of cost below the
  threshold is available at every live source, and containing strictly
  positive rows.

The clause "on `{C_h ≤ h²}` the history obeys `lem:supp-law-cost-control`
with `d_h = h` and therefore has the same Einstein limit as
`thm:supp-law-einstein`" is a citation of those two results and is not
restated here.

## Profile transport (`prop:supp-law-transport`)

Attach to each letter a profile `Φ e` in a normed space (the paper's
`L²(I_j;H_h^s) ⊕ L²(I_j;H_h^{s-3}) ⊕ ℝ`), so that the cost is
`c e = ‖Φ e‖²` and `d e e' = ‖Φ e - Φ e'‖`.  `W2 d K P` is the finite
optimal-transport distance (infimum over couplings of `(∑ π d²)^{1/2}`).

* `weighted_sqrt_sum_add_le`: Minkowski's inequality in a weighted `ℓ²`.
* `sqrt_row_cost_le_sqrt_add_W2`: the transport bound
  `(∑ K c)^{1/2} ≤ (∑ P c)^{1/2} + W_{2,d}(K, P)`
  (`eq:supp-law-transport-bound`), by Minkowski under each coupling and
  taking the infimum (no minimiser is needed).
* `row_moment_of_W2_lt`: if `∑ P c ≤ M₀ τ h⁴` and `W_{2,d}(K,P) < γ √τ h²`
  then `∑ K c < M τ h⁴` for every `M > (√M₀ + γ)²`
  (`eq:supp-law-transport-ball`).
* `W2_le_sqrt_add_of_totalVariation`, `isOpen_W2_ball_restrict`: an explicit
  coupling perturbation gives the upper semicontinuity
  `W2(K', P)² ≤ W2(K, P)² + D² · TV(K', K)`, hence the strict transport balls
  are relatively open in the finite probability simplex.
-/

namespace RenewalGeometry

open Finset Filter Topology

namespace ChronologicalRow

variable {E : Type*} [Fintype E]

/-- A chronological word process on the finite letter alphabet `E`: at stage
`j` and prefix `π` (the letters executed so far) the transition row
`row j π` is a probability vector on `E`.  The rows may depend on the entire
past (`thm:supp-law-row-neighbourhood`). -/
structure WordProcess (E : Type*) [Fintype E] where
  /-- number of stages (cells of the partition of `[0, T]`) -/
  stages : ℕ
  /-- the transition row at stage `j` after the prefix `π` -/
  row : ℕ → List E → E → ℝ
  row_nonneg : ∀ j π e, 0 ≤ row j π e
  row_sum : ∀ j π, ∑ e, row j π e = 1

namespace WordProcess

variable (P : WordProcess E)

/-- Expectation of `f` over the completions of the prefix `π` at stage `j`
when `m` stages remain (tower recursion of the finite path law). -/
def expectAux : ℕ → ℕ → List E → (List E → ℝ) → ℝ
  | 0, _, π, f => f π
  | m + 1, j, π, f => ∑ e, P.row j π e * expectAux m (j + 1) (π ++ [e]) f

/-- Expectation of a functional of the whole chronological word. -/
def expect (f : List E → ℝ) : ℝ := P.expectAux P.stages 0 [] f

/-- Probability of an event of the whole chronological word. -/
def prob (A : List E → Prop) [DecidablePred A] : ℝ :=
  P.expect fun w => if A w then 1 else 0

theorem expectAux_const (m j : ℕ) (π : List E) (a : ℝ) :
    P.expectAux m j π (fun _ => a) = a := by
  induction m generalizing j π with
  | zero => rfl
  | succ m ih => simp [expectAux, ih, ← Finset.sum_mul, P.row_sum]

theorem expectAux_add (m j : ℕ) (π : List E) (f g : List E → ℝ) :
    P.expectAux m j π (fun w => f w + g w)
      = P.expectAux m j π f + P.expectAux m j π g := by
  induction m generalizing j π with
  | zero => rfl
  | succ m ih => simp [expectAux, ih, mul_add, Finset.sum_add_distrib]

theorem expectAux_const_mul (m j : ℕ) (π : List E) (a : ℝ) (f : List E → ℝ) :
    P.expectAux m j π (fun w => a * f w) = a * P.expectAux m j π f := by
  induction m generalizing j π with
  | zero => rfl
  | succ m ih => simp [expectAux, ih, Finset.mul_sum, mul_left_comm]

theorem expectAux_mono (m j : ℕ) (π : List E) {f g : List E → ℝ}
    (hfg : ∀ w, f w ≤ g w) :
    P.expectAux m j π f ≤ P.expectAux m j π g := by
  induction m generalizing j π with
  | zero => exact hfg π
  | succ m ih =>
    simp only [expectAux]
    exact Finset.sum_le_sum fun e _ =>
      mul_le_mul_of_nonneg_left (ih _ _) (P.row_nonneg _ _ _)

theorem expectAux_nonneg (m j : ℕ) (π : List E) {f : List E → ℝ}
    (hf : ∀ w, 0 ≤ f w) : 0 ≤ P.expectAux m j π f := by
  have := P.expectAux_mono m j π (f := fun _ => 0) (g := f) hf
  rwa [expectAux_const] at this

/-- The expectation from the prefix `π` only sees words extending `π`. -/
theorem expectAux_congr (m j : ℕ) (π : List E) {f g : List E → ℝ}
    (hfg : ∀ w, π <+: w → f w = g w) :
    P.expectAux m j π f = P.expectAux m j π g := by
  induction m generalizing j π with
  | zero => exact hfg π List.prefix_rfl
  | succ m ih =>
    simp only [expectAux]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [ih (j + 1) (π ++ [e]) fun w hw => hfg w ((List.prefix_append π [e]).trans hw)]

/-- The cost paid at stage `j` of the word `w`: the stage cost of the
`j`-th letter given the prefix of length `j` (zero if the word is shorter). -/
def stageCost (c : ℕ → List E → E → ℝ) (j : ℕ) (w : List E) : ℝ :=
  match w.drop j with
  | [] => 0
  | e :: _ => c j (w.take j) e

/-- The total word cost `C_h = ∑_j c_{h,j}` (`eq:main-law-cost`). -/
def totalCost (c : ℕ → List E → E → ℝ) (n : ℕ) (w : List E) : ℝ :=
  ∑ j ∈ range n, stageCost c j w

omit [Fintype E] in
theorem stageCost_of_prefix (c : ℕ → List E → E → ℝ) {j : ℕ} {π : List E}
    (hj : π.length = j) (e : E) {w : List E} (hw : π ++ [e] <+: w) :
    stageCost c j w = c j π e := by
  obtain ⟨t, rfl⟩ := hw
  simp only [stageCost, List.append_assoc, List.singleton_append,
    List.drop_left' hj, List.take_left' hj]

omit [Fintype E] in
theorem stageCost_nonneg (c : ℕ → List E → E → ℝ) (hc : ∀ j π e, 0 ≤ c j π e)
    (j : ℕ) (w : List E) : 0 ≤ stageCost c j w := by
  unfold stageCost
  split <;> simp [hc]

omit [Fintype E] in
theorem totalCost_nonneg (c : ℕ → List E → E → ℝ) (hc : ∀ j π e, 0 ≤ c j π e)
    (n : ℕ) (w : List E) : 0 ≤ totalCost c n w :=
  Finset.sum_nonneg fun j _ => stageCost_nonneg c hc j w

/-- Conditioning on live prefixes: the expected cost of the stages
`j, …, j+m-1` from a live prefix of length `j` is bounded by the sum of the
per-stage conditional mean bounds, independently of the probability of
reaching the prefix. -/
theorem expectAux_window_cost_le (c : ℕ → List E → E → ℝ) (b : ℕ → ℝ)
    (hb : ∀ j π, j < P.stages → π.length = j →
      ∑ e, P.row j π e * c j π e ≤ b j) :
    ∀ (m j : ℕ) (π : List E), j + m ≤ P.stages → π.length = j →
      P.expectAux m j π (fun w => ∑ i ∈ range m, stageCost c (j + i) w)
        ≤ ∑ i ∈ range m, b (j + i) := by
  intro m
  induction m with
  | zero => intro j π _ _; simp [expectAux]
  | succ m ih =>
    intro j π hjm hπ
    have hsplit : ∀ w, (∑ i ∈ range (m + 1), stageCost c (j + i) w)
        = stageCost c j w + ∑ i ∈ range m, stageCost c (j + 1 + i) w := by
      intro w
      rw [Finset.sum_range_succ', add_zero, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show j + (i + 1) = j + 1 + i by omega]
    have hsplitb : (∑ i ∈ range (m + 1), b (j + i))
        = b j + ∑ i ∈ range m, b (j + 1 + i) := by
      rw [Finset.sum_range_succ', add_zero, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show j + (i + 1) = j + 1 + i by omega]
    simp only [expectAux]
    rw [hsplitb]
    have hstep : ∀ e, P.expectAux m (j + 1) (π ++ [e])
        (fun w => ∑ i ∈ range (m + 1), stageCost c (j + i) w)
        ≤ c j π e + ∑ i ∈ range m, b (j + 1 + i) := by
      intro e
      have hcongr := P.expectAux_congr m (j + 1) (π ++ [e])
        (f := fun w => ∑ i ∈ range (m + 1), stageCost c (j + i) w)
        (g := fun w => c j π e + ∑ i ∈ range m, stageCost c (j + 1 + i) w)
        (fun w hw => by rw [hsplit w, stageCost_of_prefix c hπ e hw])
      rw [hcongr, P.expectAux_add, P.expectAux_const]
      have hlen : (π ++ [e]).length = j + 1 := by simp [hπ]
      have := ih (j + 1) (π ++ [e]) (by omega) hlen
      linarith
    calc ∑ e, P.row j π e * P.expectAux m (j + 1) (π ++ [e])
          (fun w => ∑ i ∈ range (m + 1), stageCost c (j + i) w)
        ≤ ∑ e, P.row j π e * (c j π e + ∑ i ∈ range m, b (j + 1 + i)) :=
          Finset.sum_le_sum fun e _ =>
            mul_le_mul_of_nonneg_left (hstep e) (P.row_nonneg _ _ _)
      _ = ∑ e, P.row j π e * c j π e
          + (∑ e, P.row j π e) * ∑ i ∈ range m, b (j + 1 + i) := by
          rw [Finset.sum_mul, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun e _ => ?_
          ring
      _ ≤ b j + ∑ i ∈ range m, b (j + 1 + i) := by
          rw [P.row_sum, one_mul]
          have := hb j π (by omega) hπ
          linarith

/-- The boxed expectation bound `𝔼 C_h ≤ M T h⁴` of
`eq:supp-law-row-probability`: if every live prefix at stage `j` has
conditional stage-cost mean at most `M τ_j h⁴` (`eq:supp-law-row-moment`)
and `∑_j τ_j ≤ T`, then the expected word cost is at most `M T h⁴`. -/
theorem expect_totalCost_le (c : ℕ → List E → E → ℝ) (τ : ℕ → ℝ)
    (M h T : ℝ) (hM : 0 ≤ M) (hτ : ∑ j ∈ range P.stages, τ j ≤ T)
    (hrow : ∀ j π, j < P.stages → π.length = j →
      ∑ e, P.row j π e * c j π e ≤ M * τ j * h ^ 4) :
    P.expect (totalCost c P.stages) ≤ M * T * h ^ 4 := by
  have hwin := P.expectAux_window_cost_le c (fun j => M * τ j * h ^ 4) hrow
    P.stages 0 [] (by omega) rfl
  simp only [zero_add] at hwin
  refine hwin.trans ?_
  have : (∑ i ∈ range P.stages, M * τ i * h ^ 4)
      = (M * h ^ 4) * ∑ i ∈ range P.stages, τ i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  have hMh : 0 ≤ M * h ^ 4 := by positivity
  nlinarith

/-- Markov's inequality for the finite path law:
`ℙ{f > t} ≤ 𝔼 f / t` for nonnegative `f` and `t > 0`. -/
theorem prob_lt_le_expect_div (f : List E → ℝ) (hf : ∀ w, 0 ≤ f w) {t : ℝ}
    (ht : 0 < t) :
    P.prob (fun w => t < f w) ≤ P.expect f / t := by
  rw [le_div_iff₀ ht]
  unfold prob expect
  rw [mul_comm, ← P.expectAux_const_mul]
  refine P.expectAux_mono _ _ _ fun w => ?_
  by_cases hw : t < f w
  · simp [hw, hw.le]
  · simp [hw, hf w]

/-- The boxed probability bound `ℙ{C_h > h²} ≤ M T h²` of
`eq:supp-law-row-probability`. -/
theorem prob_cost_gt_le (c : ℕ → List E → E → ℝ) (hc : ∀ j π e, 0 ≤ c j π e)
    (τ : ℕ → ℝ) (M h T : ℝ) (hM : 0 ≤ M) (hh : 0 < h)
    (hτ : ∑ j ∈ range P.stages, τ j ≤ T)
    (hrow : ∀ j π, j < P.stages → π.length = j →
      ∑ e, P.row j π e * c j π e ≤ M * τ j * h ^ 4) :
    P.prob (fun w => h ^ 2 < totalCost c P.stages w) ≤ M * T * h ^ 2 := by
  refine (P.prob_lt_le_expect_div _ (totalCost_nonneg c hc _) (by positivity)).trans ?_
  rw [div_le_iff₀ (by positivity)]
  calc P.expect (totalCost c P.stages) ≤ M * T * h ^ 4 :=
        P.expect_totalCost_le c τ M h T hM hτ hrow
    _ = M * T * h ^ 2 * h ^ 2 := by ring

end WordProcess

/-- Along the odd cutoffs `h_m = (2m+1)⁻¹` the exceptional probabilities
`M T h_m² = M T/(2m+1)²` are summable, so under any common coupling of the
cutoffs (any measure `μ` with `μ(A_m) ≤ M T/(2m+1)²`) the exceptional events
occur only finitely often almost surely — the first Borel–Cantelli lemma,
without independence between cutoffs
(`thm:supp-law-row-neighbourhood`, last sentence). -/
theorem odd_cutoff_eventually_not_exceptional {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (A : ℕ → Set Ω) (K : ℝ) (hK : 0 ≤ K)
    (hA : ∀ m : ℕ, μ (A m) ≤ ENNReal.ofReal (K / (2 * (m : ℝ) + 1) ^ 2)) :
    ∀ᵐ ω ∂μ, ∀ᶠ m in atTop, ω ∉ A m := by
  have hsum : Summable fun m : ℕ => K / (2 * (m : ℝ) + 1) ^ 2 := by
    have h1 : Summable fun m : ℕ => (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 2 :=
      (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) (h1.mul_left K)
    rw [div_eq_mul_one_div]
    refine mul_le_mul_of_nonneg_left ?_ hK
    push_cast
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  refine MeasureTheory.ae_eventually_notMem ?_
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hA)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsum]
  exact ENNReal.ofReal_ne_top

/-! ### Relatively open row neighbourhoods at fixed cutoff -/

section RowSimplex

variable {S : Type*}

/-- The strict conditional-mean constraint set on a product of rows indexed
by the live sources `S`: `∑ₑ K p e · c p e < b p` at every source
(`eq:supp-law-row-moment` with `b p = M τ_j h⁴`). -/
def rowConstraintSet (S : Type*) (c : S → E → ℝ) (b : S → ℝ) : Set (S → E → ℝ) :=
  {K | ∀ p, ∑ e, K p e * c p e < b p}

theorem rowConstraintSet_eq_iInter (c : S → E → ℝ) (b : S → ℝ) :
    rowConstraintSet S c b = ⋂ p, {K : S → E → ℝ | ∑ e, K p e * c p e < b p} := by
  ext K; simp [rowConstraintSet]

theorem continuous_rowMean (c : S → E → ℝ) (p : S) :
    Continuous fun K : S → E → ℝ => ∑ e, K p e * c p e := by
  fun_prop

/-- Each strict conditional-mean bound is an open condition; finitely many
live sources give an open set. -/
theorem isOpen_rowConstraintSet [Finite S] (c : S → E → ℝ) (b : S → ℝ) :
    IsOpen (rowConstraintSet S c b) := by
  rw [rowConstraintSet_eq_iInter]
  exact isOpen_iInter_of_finite fun p =>
    isOpen_lt (continuous_rowMean c p) continuous_const

/-- Each strict conditional-mean bound is an open affine half-space; the
constraint set is convex. -/
theorem convex_rowConstraintSet (c : S → E → ℝ) (b : S → ℝ) :
    Convex ℝ (rowConstraintSet S c b) := by
  rw [rowConstraintSet_eq_iInter]
  refine convex_iInter fun p => convex_halfSpace_lt ?_ (b p)
  exact ⟨fun x y => by simp [Finset.sum_add_distrib, add_mul],
    fun a x => by simp [Finset.mul_sum, mul_assoc]⟩

/-- The product of row simplexes indexed by the live sources. -/
def RowProduct (S : Type*) (E : Type*) [Fintype E] : Type _ :=
  {K : S → E → ℝ // ∀ p, K p ∈ stdSimplex ℝ E}

instance : TopologicalSpace (RowProduct S E) :=
  inferInstanceAs (TopologicalSpace {K : S → E → ℝ // ∀ p, K p ∈ stdSimplex ℝ E})

/-- Relative openness: the constraint set is open in the product of row
simplexes (subspace topology). -/
theorem isOpen_rowConstraintSet_restrict [Finite S] (c : S → E → ℝ) (b : S → ℝ) :
    IsOpen ((fun K : RowProduct S E => K.1) ⁻¹' rowConstraintSet S c b) :=
  (isOpen_rowConstraintSet c b).preimage continuous_subtype_val

/-- Convexity of the relative constraint set inside the product of row
simplexes. -/
theorem convex_rowConstraintSet_inter (c : S → E → ℝ) (b : S → ℝ) :
    Convex ℝ (rowConstraintSet S c b ∩ {K | ∀ p, K p ∈ stdSimplex ℝ E}) := by
  refine (convex_rowConstraintSet c b).inter ?_
  have : {K : S → E → ℝ | ∀ p, K p ∈ stdSimplex ℝ E}
      = Set.pi Set.univ fun _ => stdSimplex ℝ E := by
    ext K; simp [Set.mem_pi]
  rw [this]
  exact convex_pi fun _ _ => convex_stdSimplex ℝ E

/-- Nonemptiness: when a letter of cost below the threshold is available at
every live source (a uniformly accurate completion), the Dirac rows lie in
the constraint set. -/
theorem rowConstraintSet_nonempty [DecidableEq E] (c : S → E → ℝ) (b : S → ℝ)
    (hex : ∀ p, ∃ e, c p e < b p) :
    ∃ K ∈ rowConstraintSet S c b, ∀ p, K p ∈ stdSimplex ℝ E := by
  choose e₀ he₀ using hex
  refine ⟨fun p e => if e = e₀ p then 1 else 0, fun p => ?_, fun p => ?_⟩
  · simpa using he₀ p
  · refine ⟨fun e => by dsimp only; split <;> norm_num, by simp⟩

/-- Strictly positive rows: small positive mixing of the Dirac rows with the
uniform row keeps the strict margin (all letters having finite cost). -/
theorem rowConstraintSet_exists_pos_row [Finite S] [DecidableEq E] [Nonempty E]
    (c : S → E → ℝ) (b : S → ℝ) (hex : ∀ p, ∃ e, c p e < b p) :
    ∃ K ∈ rowConstraintSet S c b,
      (∀ p, K p ∈ stdSimplex ℝ E) ∧ ∀ p e, 0 < K p e := by
  choose e₀ he₀ using hex
  set n : ℝ := (Fintype.card E : ℝ)
  have hn : 0 < n := by
    simp only [n]; exact_mod_cast Fintype.card_pos
  -- the mixed row and its conditional mean as functions of the mixing weight
  let g : S → ℝ → ℝ := fun p ε => (1 - ε) * c p (e₀ p) + ε / n * ∑ e, c p e
  have hg : ∀ p, Continuous (g p) := fun p => by
    simp only [g]; fun_prop
  have hopen : IsOpen {ε : ℝ | ∀ p, g p ε < b p} := by
    have : {ε : ℝ | ∀ p, g p ε < b p} = ⋂ p, {ε | g p ε < b p} := by
      ext; simp
    rw [this]
    exact isOpen_iInter_of_finite fun p => isOpen_lt (hg p) continuous_const
  have hmem : (0 : ℝ) ∈ {ε : ℝ | ∀ p, g p ε < b p} := by
    intro p; simpa [g] using he₀ p
  have h1 : {ε : ℝ | ∀ p, g p ε < b p} ∈ 𝓝[>] (0 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hmem)
  have h2 : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT one_pos
  obtain ⟨ε, hε1, hε2⟩ := Filter.nonempty_of_mem (Filter.inter_mem h1 h2)
  have hε0 : 0 < ε := hε2.1
  have hε1' : ε < 1 := hε2.2
  refine ⟨fun p e => (1 - ε) * (if e = e₀ p then 1 else 0) + ε / n,
    fun p => ?_, fun p => ⟨fun e => ?_, ?_⟩, fun p e => ?_⟩
  · have := hε1 p
    simp only [g] at this
    convert this using 1
    simp [add_mul, Finset.sum_add_distrib, Finset.mul_sum, ite_mul, Finset.sum_ite_eq']
  · have : 0 ≤ (1 - ε) * (if e = e₀ p then 1 else 0) := by
      apply mul_nonneg (by linarith); split <;> norm_num
    have : 0 < ε / n := by positivity
    linarith
  · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp only [n]
    field_simp
    ring
  · have : 0 ≤ (1 - ε) * (if e = e₀ p then 1 else 0) := by
      apply mul_nonneg (by linarith); split <;> norm_num
    have : 0 < ε / n := by positivity
    linarith

end RowSimplex

end ChronologicalRow

/-! ## Physical profile transport (`prop:supp-law-transport`) -/

namespace ProfileTransport

variable {E : Type*} [Fintype E]

/-- `π` is a coupling of the finite rows `K` and `P`. -/
def IsCoupling (K P : E → ℝ) (π : E → E → ℝ) : Prop :=
  (∀ e e', 0 ≤ π e e') ∧ (∀ e, ∑ e', π e e' = K e) ∧ (∀ e', ∑ e, π e e' = P e')

/-- The quadratic transport cost of a coupling for the ground distance `d`. -/
def transportCost (d : E → E → ℝ) (π : E → E → ℝ) : ℝ :=
  ∑ e, ∑ e', π e e' * d e e' ^ 2

/-- The finite quadratic optimal-transport distance `W_{2,d}(K, P)`:
the infimum over couplings of `(∑ π d²)^{1/2}`. -/
noncomputable def W2 (d : E → E → ℝ) (K P : E → ℝ) : ℝ :=
  sInf {r | ∃ π, IsCoupling K P π ∧ r = Real.sqrt (transportCost d π)}

theorem isCoupling_prod {K P : E → ℝ} (hK : K ∈ stdSimplex ℝ E)
    (hP : P ∈ stdSimplex ℝ E) : IsCoupling K P fun e e' => K e * P e' :=
  ⟨fun e e' => mul_nonneg (hK.1 e) (hP.1 e'),
    fun e => by rw [← Finset.mul_sum, hP.2, mul_one],
    fun e' => by rw [← Finset.sum_mul, hK.2, one_mul]⟩

theorem W2_set_nonempty {d : E → E → ℝ} {K P : E → ℝ} (hK : K ∈ stdSimplex ℝ E)
    (hP : P ∈ stdSimplex ℝ E) :
    {r | ∃ π, IsCoupling K P π ∧ r = Real.sqrt (transportCost d π)}.Nonempty :=
  ⟨_, _, isCoupling_prod hK hP, rfl⟩

theorem W2_set_bddBelow (d : E → E → ℝ) (K P : E → ℝ) :
    BddBelow {r | ∃ π, IsCoupling K P π ∧ r = Real.sqrt (transportCost d π)} :=
  ⟨0, fun _ ⟨_, _, hr⟩ => hr ▸ Real.sqrt_nonneg _⟩

theorem W2_nonneg (d : E → E → ℝ) {K P : E → ℝ} (hK : K ∈ stdSimplex ℝ E)
    (hP : P ∈ stdSimplex ℝ E) : 0 ≤ W2 d K P :=
  le_csInf (W2_set_nonempty hK hP) fun _ ⟨_, _, hr⟩ => hr ▸ Real.sqrt_nonneg _

/-- Minkowski's inequality in a weighted finite `ℓ²`. -/
theorem weighted_sqrt_sum_add_le {ι : Type*} (s : Finset ι) (w a b : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) :
    Real.sqrt (∑ i ∈ s, w i * (a i + b i) ^ 2)
      ≤ Real.sqrt (∑ i ∈ s, w i * a i ^ 2) + Real.sqrt (∑ i ∈ s, w i * b i ^ 2) := by
  set A := ∑ i ∈ s, w i * a i ^ 2 with hA
  set B := ∑ i ∈ s, w i * b i ^ 2 with hB
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => by have := hw i; positivity
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => by have := hw i; positivity
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt s (fun i => Real.sqrt (w i) * a i)
    (fun i => Real.sqrt (w i) * b i)
  have h1 : ∀ i, (Real.sqrt (w i) * a i) ^ 2 = w i * a i ^ 2 := fun i => by
    rw [mul_pow, Real.sq_sqrt (hw i)]
  have h2 : ∀ i, (Real.sqrt (w i) * b i) ^ 2 = w i * b i ^ 2 := fun i => by
    rw [mul_pow, Real.sq_sqrt (hw i)]
  have h3 : ∀ i, (Real.sqrt (w i) * a i) * (Real.sqrt (w i) * b i) = w i * (a i * b i) :=
    fun i => by rw [mul_mul_mul_comm, ← sq, Real.sq_sqrt (hw i)]
  simp only [h1, h2, h3] at hcs
  have hexp : ∑ i ∈ s, w i * (a i + b i) ^ 2 = A + B + 2 * ∑ i ∈ s, w i * (a i * b i) := by
    have : ∀ i, w i * (a i + b i) ^ 2
        = w i * a i ^ 2 + w i * b i ^ 2 + 2 * (w i * (a i * b i)) := fun i => by ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hA, hB]
  have key : ∑ i ∈ s, w i * (a i + b i) ^ 2 ≤ (Real.sqrt A + Real.sqrt B) ^ 2 := by
    rw [hexp]
    nlinarith [Real.sq_sqrt hA0, Real.sq_sqrt hB0]
  calc Real.sqrt (∑ i ∈ s, w i * (a i + b i) ^ 2)
      ≤ Real.sqrt ((Real.sqrt A + Real.sqrt B) ^ 2) := Real.sqrt_le_sqrt key
    _ = Real.sqrt A + Real.sqrt B := Real.sqrt_sq (by positivity)

variable {H : Type*} [NormedAddCommGroup H]

/-- The transport bound `eq:supp-law-transport-bound`: for profiles `Φ e`
with cost `c e = ‖Φ e‖²` and ground distance `d e e' = ‖Φ e - Φ e'‖`,
`(∑ K c)^{1/2} ≤ (∑ P c)^{1/2} + W_{2,d}(K, P)` for all finite rows
`K, P` (Minkowski under every coupling, then the infimum). -/
theorem sqrt_row_cost_le_sqrt_add_W2 (Φ : E → H) {K P : E → ℝ}
    (hK : K ∈ stdSimplex ℝ E) (hP : P ∈ stdSimplex ℝ E) :
    Real.sqrt (∑ e, K e * ‖Φ e‖ ^ 2)
      ≤ Real.sqrt (∑ e, P e * ‖Φ e‖ ^ 2)
        + W2 (fun e e' => ‖Φ e - Φ e'‖) K P := by
  rw [← sub_le_iff_le_add']
  refine le_csInf (W2_set_nonempty hK hP) ?_
  rintro r ⟨π, ⟨hπ0, hπK, hπP⟩, rfl⟩
  rw [sub_le_iff_le_add']
  -- rewrite both row costs as coupling averages
  have hKc : ∑ e, K e * ‖Φ e‖ ^ 2 = ∑ x : E × E, π x.1 x.2 * ‖Φ x.1‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun e _ => by rw [← hπK e, Finset.sum_mul]
  have hPc : ∑ e, P e * ‖Φ e‖ ^ 2 = ∑ x : E × E, π x.1 x.2 * ‖Φ x.2‖ ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    exact Finset.sum_congr rfl fun e' _ => by rw [← hπP e', Finset.sum_mul]
  have hcost : transportCost (fun e e' => ‖Φ e - Φ e'‖) π
      = ∑ x : E × E, π x.1 x.2 * ‖Φ x.1 - Φ x.2‖ ^ 2 := by
    rw [transportCost, Fintype.sum_prod_type]
  rw [hKc, hPc, hcost]
  refine le_trans (Real.sqrt_le_sqrt ?_)
    (weighted_sqrt_sum_add_le Finset.univ (fun x : E × E => π x.1 x.2)
      (fun x => ‖Φ x.2‖) (fun x => ‖Φ x.1 - Φ x.2‖) fun x => hπ0 x.1 x.2)
  refine Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ (hπ0 x.1 x.2)
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_insert' _ _) 2

/-- `eq:supp-law-transport-ball`: if the reference row has conditional mean
`∑ P c ≤ M₀ τ h⁴` and `W_{2,d}(K, P) < γ √τ h²`, then the row `K` obeys
the moment bound `∑ K c < M τ h⁴` for every `M > (√M₀ + γ)²`. -/
theorem row_moment_of_W2_lt (Φ : E → H) {K P : E → ℝ}
    (hK : K ∈ stdSimplex ℝ E) (hP : P ∈ stdSimplex ℝ E)
    {M₀ γ τ h M : ℝ} (hM₀ : 0 ≤ M₀) (hτ : 0 < τ) (hh : 0 < h)
    (hPc : ∑ e, P e * ‖Φ e‖ ^ 2 ≤ M₀ * τ * h ^ 4)
    (hW : W2 (fun e e' => ‖Φ e - Φ e'‖) K P < γ * Real.sqrt τ * h ^ 2)
    (hM : (Real.sqrt M₀ + γ) ^ 2 < M) :
    ∑ e, K e * ‖Φ e‖ ^ 2 < M * τ * h ^ 4 := by
  have hsqrt : Real.sqrt (∑ e, K e * ‖Φ e‖ ^ 2)
      < (Real.sqrt M₀ + γ) * (Real.sqrt τ * h ^ 2) := by
    have h1 := sqrt_row_cost_le_sqrt_add_W2 Φ hK hP
    have h2 : Real.sqrt (∑ e, P e * ‖Φ e‖ ^ 2) ≤ Real.sqrt M₀ * (Real.sqrt τ * h ^ 2) := by
      calc Real.sqrt (∑ e, P e * ‖Φ e‖ ^ 2) ≤ Real.sqrt (M₀ * τ * h ^ 4) :=
            Real.sqrt_le_sqrt hPc
        _ = Real.sqrt M₀ * (Real.sqrt τ * h ^ 2) := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hM₀,
              show h ^ 4 = (h ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
            ring
    nlinarith
  have hlt := Real.lt_sq_of_sqrt_lt hsqrt
  have hτh : 0 < τ * h ^ 4 := by positivity
  calc ∑ e, K e * ‖Φ e‖ ^ 2
      < ((Real.sqrt M₀ + γ) * (Real.sqrt τ * h ^ 2)) ^ 2 := hlt
    _ = (Real.sqrt M₀ + γ) ^ 2 * (τ * h ^ 4) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hτ.le]; ring
    _ ≤ M * (τ * h ^ 4) := mul_le_mul_of_nonneg_right hM.le hτh.le
    _ = M * τ * h ^ 4 := by ring

/-! ### Relative openness of the strict transport balls -/

section Openness

/-- Row-shrinking ratio `min(K', K₀)/K₀` (zero on empty rows of `K₀`). -/
noncomputable def ratio (K₀ K' : E → ℝ) (e : E) : ℝ :=
  if K₀ e = 0 then 0 else min (K' e) (K₀ e) / K₀ e

/-- Excess mass `K' - min(K', K₀)` of the perturbed row. -/
def excess (K₀ K' : E → ℝ) (e : E) : ℝ := K' e - min (K' e) (K₀ e)

/-- Column mass of `π₀` left unfilled after shrinking its rows. -/
noncomputable def deficit (K₀ K' : E → ℝ) (π₀ : E → E → ℝ) (e' : E) : ℝ :=
  ∑ e, (1 - ratio K₀ K' e) * π₀ e e'

/-- Total excess mass `∑ₑ (K' - min(K', K₀))`. -/
def totalExcess (K₀ K' : E → ℝ) : ℝ := ∑ e, excess K₀ K' e

/-- The perturbed coupling: shrink the rows of `π₀` to `min(K', K₀)` and
distribute the excess mass of `K'` over the unfilled column mass. -/
noncomputable def perturbCoupling (K₀ K' : E → ℝ) (π₀ : E → E → ℝ) (e e' : E) : ℝ :=
  ratio K₀ K' e * π₀ e e' + excess K₀ K' e * deficit K₀ K' π₀ e' / totalExcess K₀ K'

variable {K₀ K' P : E → ℝ} {π₀ : E → E → ℝ}

omit [Fintype E] in
theorem ratio_nonneg (hK₀ : ∀ e, 0 ≤ K₀ e) (hK' : ∀ e, 0 ≤ K' e) (e : E) :
    0 ≤ ratio K₀ K' e := by
  unfold ratio
  split
  · exact le_rfl
  · exact div_nonneg (le_min (hK' e) (hK₀ e)) (hK₀ e)

omit [Fintype E] in
theorem ratio_le_one (hK₀ : ∀ e, 0 ≤ K₀ e) (e : E) : ratio K₀ K' e ≤ 1 := by
  unfold ratio
  split
  · exact zero_le_one
  · exact div_le_one_of_le₀ (min_le_right _ _) (hK₀ e)

omit [Fintype E] in
theorem ratio_mul (hK' : ∀ e, 0 ≤ K' e) (e : E) :
    ratio K₀ K' e * K₀ e = min (K' e) (K₀ e) := by
  unfold ratio
  split
  · rename_i h0
    rw [h0, zero_mul, min_eq_right (hK' e)]
  · rename_i h0
    exact div_mul_cancel₀ _ h0

omit [Fintype E] in
theorem excess_nonneg (K₀ : E → ℝ) (K' : E → ℝ) (e : E) : 0 ≤ excess K₀ K' e := by
  unfold excess; linarith [min_le_left (K' e) (K₀ e)]

omit [Fintype E] in
theorem excess_le_abs (K₀ K' : E → ℝ) (e : E) : excess K₀ K' e ≤ |K' e - K₀ e| := by
  unfold excess
  rcases le_total (K' e) (K₀ e) with h | h
  · rw [min_eq_left h]; simp
  · rw [min_eq_right h]; exact le_abs_self _

theorem deficit_nonneg (hK₀ : ∀ e, 0 ≤ K₀ e) (hπ : ∀ e e', 0 ≤ π₀ e e') (e' : E) :
    0 ≤ deficit K₀ K' π₀ e' :=
  Finset.sum_nonneg fun e _ =>
    mul_nonneg (by linarith [ratio_le_one (K' := K') hK₀ e]) (hπ e e')

theorem totalExcess_nonneg (K₀ K' : E → ℝ) : 0 ≤ totalExcess K₀ K' :=
  Finset.sum_nonneg fun e _ => excess_nonneg K₀ K' e

theorem totalExcess_le_abs (K₀ K' : E → ℝ) :
    totalExcess K₀ K' ≤ ∑ e, |K' e - K₀ e| :=
  Finset.sum_le_sum fun e _ => excess_le_abs K₀ K' e

/-- The unfilled column mass equals the total excess (both rows are
probability vectors). -/
theorem sum_deficit (hK₀ : K₀ ∈ stdSimplex ℝ E) (hK' : K' ∈ stdSimplex ℝ E)
    (hπ : IsCoupling K₀ P π₀) :
    ∑ e', deficit K₀ K' π₀ e' = totalExcess K₀ K' := by
  unfold deficit totalExcess excess
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hπ.2.1, sub_mul, one_mul, ratio_mul hK'.1,
    Finset.sum_sub_distrib, hK₀.2, hK'.2]

theorem perturbCoupling_nonneg (hK₀ : K₀ ∈ stdSimplex ℝ E) (hK' : K' ∈ stdSimplex ℝ E)
    (hπ : IsCoupling K₀ P π₀) (e e' : E) : 0 ≤ perturbCoupling K₀ K' π₀ e e' := by
  unfold perturbCoupling
  have := ratio_nonneg (K₀ := K₀) (K' := K') hK₀.1 hK'.1 e
  have := hπ.1 e e'
  have := excess_nonneg K₀ K' e
  have := deficit_nonneg (K' := K') hK₀.1 hπ.1 e'
  have := totalExcess_nonneg K₀ K'
  positivity

theorem perturbCoupling_isCoupling (hK₀ : K₀ ∈ stdSimplex ℝ E)
    (hK' : K' ∈ stdSimplex ℝ E) (hπ : IsCoupling K₀ P π₀) :
    IsCoupling K' P (perturbCoupling K₀ K' π₀) := by
  refine ⟨perturbCoupling_nonneg hK₀ hK' hπ, fun e => ?_, fun e' => ?_⟩
  · -- row sums
    unfold perturbCoupling
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hπ.2.1, ratio_mul hK'.1,
      ← Finset.sum_div, ← Finset.mul_sum, sum_deficit hK₀ hK' hπ]
    by_cases h0 : totalExcess K₀ K' = 0
    · have hex : excess K₀ K' e = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun e _ => excess_nonneg K₀ K' e)).mp h0 e (Finset.mem_univ _)
      have : K' e - min (K' e) (K₀ e) = 0 := hex
      rw [h0, div_zero, add_zero]; linarith
    · rw [mul_div_assoc, div_self h0, mul_one]
      unfold excess; ring
  · -- column sums
    unfold perturbCoupling
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul]
    have hdef : deficit K₀ K' π₀ e' = P e' - ∑ e, ratio K₀ K' e * π₀ e e' := by
      unfold deficit
      simp only [sub_mul, one_mul, Finset.sum_sub_distrib, hπ.2.2]
    by_cases h0 : totalExcess K₀ K' = 0
    · have hd : deficit K₀ K' π₀ e' = 0 := by
        have hsum := sum_deficit hK₀ hK' hπ (P := P)
        rw [h0] at hsum
        exact (Finset.sum_eq_zero_iff_of_nonneg
          (fun e' _ => deficit_nonneg (K' := K') hK₀.1 hπ.1 e')).mp hsum e' (Finset.mem_univ _)
      rw [h0, div_zero, add_zero]
      linarith
    · change _ + totalExcess K₀ K' * deficit K₀ K' π₀ e' / totalExcess K₀ K' = _
      rw [mul_div_cancel_left₀ _ h0]
      linarith

/-- Cost of the perturbed coupling: at most the cost of `π₀` plus the
diameter bound times the total excess mass. -/
theorem transportCost_perturbCoupling_le (d : E → E → ℝ) (hK₀ : K₀ ∈ stdSimplex ℝ E)
    (hK' : K' ∈ stdSimplex ℝ E) (hπ : IsCoupling K₀ P π₀) {D : ℝ}
    (hD : ∀ e e', d e e' ^ 2 ≤ D) :
    transportCost d (perturbCoupling K₀ K' π₀)
      ≤ transportCost d π₀ + D * totalExcess K₀ K' := by
  unfold transportCost perturbCoupling
  have hsplit : ∀ e e', (ratio K₀ K' e * π₀ e e'
      + excess K₀ K' e * deficit K₀ K' π₀ e' / totalExcess K₀ K') * d e e' ^ 2
      = ratio K₀ K' e * (π₀ e e' * d e e' ^ 2)
        + excess K₀ K' e * deficit K₀ K' π₀ e' / totalExcess K₀ K' * d e e' ^ 2 := by
    intro e e'; ring
  simp only [hsplit, Finset.sum_add_distrib]
  refine add_le_add ?_ ?_
  · refine Finset.sum_le_sum fun e _ => ?_
    rw [← Finset.mul_sum]
    refine mul_le_of_le_one_left ?_ (ratio_le_one (K' := K') hK₀.1 e)
    exact Finset.sum_nonneg fun e' _ => mul_nonneg (hπ.1 e e') (sq_nonneg _)
  · have hterm : ∀ e e', excess K₀ K' e * deficit K₀ K' π₀ e' / totalExcess K₀ K' * d e e' ^ 2
        ≤ D * (excess K₀ K' e * deficit K₀ K' π₀ e' / totalExcess K₀ K') := by
      intro e e'
      have h1 : 0 ≤ excess K₀ K' e * deficit K₀ K' π₀ e' / totalExcess K₀ K' := by
        have := excess_nonneg K₀ K' e
        have := deficit_nonneg (K' := K') hK₀.1 hπ.1 e'
        have := totalExcess_nonneg K₀ K'
        positivity
      rw [mul_comm D]
      exact mul_le_mul_of_nonneg_left (hD e e') h1
    refine (Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun e' _ => hterm e e').trans ?_
    simp only [← Finset.mul_sum, ← Finset.sum_div, ← Finset.sum_mul, sum_deficit hK₀ hK' hπ]
    change D * (totalExcess K₀ K' * totalExcess K₀ K' / totalExcess K₀ K') ≤ _
    by_cases h0 : totalExcess K₀ K' = 0
    · rw [h0]; simp
    · rw [mul_div_cancel_left₀ _ h0]

/-- Upper semicontinuity of the transport distance in the row: for every
coupling `π₀` of `(K₀, P)` and every row `K'`,
`W_{2,d}(K', P) ≤ (cost(π₀) + D · ∑ₑ |K' e - K₀ e|)^{1/2}`. -/
theorem W2_le_sqrt_cost_add_totalVariation (d : E → E → ℝ) (hK₀ : K₀ ∈ stdSimplex ℝ E)
    (hK' : K' ∈ stdSimplex ℝ E) (hπ : IsCoupling K₀ P π₀)
    {D : ℝ} (hD0 : 0 ≤ D) (hD : ∀ e e', d e e' ^ 2 ≤ D) :
    W2 d K' P ≤ Real.sqrt (transportCost d π₀ + D * ∑ e, |K' e - K₀ e|) := by
  refine (csInf_le (W2_set_bddBelow d K' P)
    ⟨_, perturbCoupling_isCoupling hK₀ hK' hπ, rfl⟩).trans (Real.sqrt_le_sqrt ?_)
  refine (transportCost_perturbCoupling_le d hK₀ hK' hπ hD).trans ?_
  have := mul_le_mul_of_nonneg_left (totalExcess_le_abs K₀ K') hD0
  linarith

/-- The strict transport balls `{K : W_{2,d}(K, P) < ρ}` are relatively open
in the finite probability simplex (`prop:supp-law-transport`, last
sentence). -/
theorem isOpen_W2_ball_restrict (d : E → E → ℝ) (hP : P ∈ stdSimplex ℝ E) (ρ : ℝ) :
    IsOpen {K : {K : E → ℝ // K ∈ stdSimplex ℝ E} | W2 d K.1 P < ρ} := by
  rw [isOpen_iff_forall_mem_open]
  rintro ⟨K₀, hK₀⟩ hlt
  change W2 d K₀ P < ρ at hlt
  obtain ⟨r, ⟨π₀, hπ₀, rfl⟩, hr⟩ := exists_lt_of_csInf_lt (W2_set_nonempty hK₀ hP) hlt
  have hcost0 : 0 ≤ transportCost d π₀ :=
    Finset.sum_nonneg fun e _ => Finset.sum_nonneg fun e' _ =>
      mul_nonneg (hπ₀.1 e e') (sq_nonneg _)
  have hρ : 0 < ρ := (Real.sqrt_nonneg _).trans_lt hr
  have hcost : transportCost d π₀ < ρ ^ 2 := Real.lt_sq_of_sqrt_lt hr
  set D : ℝ := ∑ e, ∑ e', d e e' ^ 2 with hDdef
  have hD0 : 0 ≤ D :=
    Finset.sum_nonneg fun e _ => Finset.sum_nonneg fun e' _ => sq_nonneg _
  have hD : ∀ e e', d e e' ^ 2 ≤ D := fun e e' =>
    (Finset.single_le_sum (fun e' _ => sq_nonneg (d e e')) (Finset.mem_univ e')).trans
      (Finset.single_le_sum (f := fun e => ∑ e', d e e' ^ 2)
        (fun e _ => Finset.sum_nonneg fun e' _ => sq_nonneg _) (Finset.mem_univ e))
  set η : ℝ := ρ ^ 2 - transportCost d π₀ with hη
  have hη0 : 0 < η := by simp only [hη]; linarith
  refine ⟨{K : {K : E → ℝ // K ∈ stdSimplex ℝ E} | D * ∑ e, |K.1 e - K₀ e| < η}, ?_, ?_, ?_⟩
  · rintro ⟨K', hK'⟩ hK'mem
    change D * ∑ e, |K' e - K₀ e| < η at hK'mem
    show W2 d K' P < ρ
    calc W2 d K' P ≤ Real.sqrt (transportCost d π₀ + D * ∑ e, |K' e - K₀ e|) :=
          W2_le_sqrt_cost_add_totalVariation d hK₀ hK' hπ₀ hD0 hD
      _ < Real.sqrt (ρ ^ 2) := by
          apply Real.sqrt_lt_sqrt
          · have : 0 ≤ D * ∑ e, |K' e - K₀ e| :=
              mul_nonneg hD0 (Finset.sum_nonneg fun e _ => abs_nonneg _)
            linarith
          · linarith
      _ = ρ := Real.sqrt_sq hρ.le
  · have : Continuous fun K : {K : E → ℝ // K ∈ stdSimplex ℝ E} =>
        D * ∑ e, |K.1 e - K₀ e| :=
      continuous_const.mul (continuous_finsetSum _ fun e _ =>
        (((continuous_apply e).comp continuous_subtype_val).sub continuous_const).abs)
    exact isOpen_lt this continuous_const
  · simp [hη0]

end Openness

end ProfileTransport

end RenewalGeometry
