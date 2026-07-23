/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Operator.Diagonal

/-!
# The finite-fibre dichotomy on `ℓ²`

**Theorem `thm:fibre-dichotomy`** on the dense finitely supported core:

* **(bounded half)** if every fibre of the shift map has at most `B`
  points, then `‖Ŝf‖² ≤ B·‖f‖²` — Cauchy–Schwarz over each fibre and
  the fibre partition of the support
  (`NCG.l2normSq_shiftOp_le`);
* **(sharpness)** a fibre with exactly `k` points carries the witness
  `f = Σ e_x` with `‖Ŝf‖² = k·‖f‖²`
  (`NCG.l2normSq_shiftOp_indicator`) — the operator norm squared is the
  supremal fibre cardinality;
* **(unbounded half)** unbounded fibres defeat every bound `C`
  (`NCG.shiftOp_unbounded_of_unbounded_fibres`) — the shift extends to
  no bounded operator on `ℓ²`.

Together with the proved commutator formula
(`NCG.diagOp_comm_shiftOp_single`), the bounded-increment classes
(`NCG/Renewal/FibreClasses.lean`), and the finite length shells
(`NCG.RenewalMemory.shell_finite` — the compact-resolvent input), this
supplies the analytic pillars of **Theorem `thm:triple`** and its
corollaries `cor:automatic-triples`, `cor:sharp-existence`, and
`cor:checkable-signed-triple` on the finitely supported core; the
`lp 2`-completion packaging is the noted remaining step. -/

namespace NCG

open Finsupp

variable {ι : Type*} [DecidableEq ι]

/-- The squared `ℓ²`-norm of a finitely supported vector. -/
noncomputable def l2normSq (f : ι →₀ ℂ) : ℝ :=
  ∑ i ∈ f.support, ‖f i‖ ^ 2

theorem l2normSq_nonneg (f : ι →₀ ℂ) : 0 ≤ l2normSq f :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

/-- The `ℓ²`-norm may be computed over any finite superset of the
support. -/
theorem l2normSq_eq_sum_subset (f : ι →₀ ℂ) {T : Finset ι}
    (hT : f.support ⊆ T) :
    l2normSq f = ∑ i ∈ T, ‖f i‖ ^ 2 :=
  Finset.sum_subset hT fun x _ hx => by
    rw [Finsupp.notMem_support_iff.mp hx]
    simp

/-- The shifted vector sums each fibre:
`(Ŝf)(y) = Σ_{s(x)=y} f(x)`. -/
theorem shiftOp_apply_sum (s : ι → ι) (f : ι →₀ ℂ) (y : ι) :
    (shiftOp s f) y
      = ∑ x ∈ f.support.filter (fun x => s x = y), f x := by
  show (Finsupp.mapDomain s f) y = _
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finsupp.single_apply]

/-- Cauchy–Schwarz for complex sums:
`‖Σ_A f‖² ≤ |A|·Σ_A ‖f‖²`. -/
theorem normSq_sum_le (A : Finset ι) (f : ι → ℂ) :
    ‖∑ x ∈ A, f x‖ ^ 2 ≤ (A.card : ℝ) * ∑ x ∈ A, ‖f x‖ ^ 2 := by
  have h1 : ‖∑ x ∈ A, f x‖ ≤ ∑ x ∈ A, ‖f x‖ := norm_sum_le A f
  have h2 : (∑ x ∈ A, ‖f x‖) ^ 2
      ≤ (A.card : ℝ) * ∑ x ∈ A, ‖f x‖ ^ 2 := by
    exact_mod_cast sq_sum_le_card_mul_sum_sq (s := A)
      (f := fun x => ‖f x‖)
  calc ‖∑ x ∈ A, f x‖ ^ 2 ≤ (∑ x ∈ A, ‖f x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (A.card : ℝ) * ∑ x ∈ A, ‖f x‖ ^ 2 := h2

/-- **Theorem `thm:fibre-dichotomy` (2a), bounded half**: with every
fibre of size at most `B`, the shift satisfies `‖Ŝf‖² ≤ B·‖f‖²` on the
finitely supported core — finite fibres make the descended shifts
bounded with norm² at most the fibre bound. -/
theorem l2normSq_shiftOp_le (s : ι → ι) {B : ℕ}
    (hB : ∀ (T : Finset ι) (y : ι),
      (T.filter fun x => s x = y).card ≤ B)
    (f : ι →₀ ℂ) :
    l2normSq (shiftOp s f) ≤ (B : ℝ) * l2normSq f := by
  have hsupp : (shiftOp s f).support ⊆ f.support.image s := by
    show (Finsupp.mapDomain s f).support ⊆ _
    exact Finsupp.mapDomain_support
  rw [l2normSq_eq_sum_subset _ hsupp]
  calc ∑ y ∈ f.support.image s, ‖(shiftOp s f) y‖ ^ 2
      = ∑ y ∈ f.support.image s,
          ‖∑ x ∈ f.support.filter (fun x => s x = y), f x‖ ^ 2 := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [shiftOp_apply_sum]
    _ ≤ ∑ y ∈ f.support.image s, (B : ℝ)
          * ∑ x ∈ f.support.filter (fun x => s x = y), ‖f x‖ ^ 2 := by
        refine Finset.sum_le_sum fun y _ => ?_
        calc ‖∑ x ∈ f.support.filter (fun x => s x = y), f x‖ ^ 2
            ≤ ((f.support.filter (fun x => s x = y)).card : ℝ)
              * ∑ x ∈ f.support.filter (fun x => s x = y),
                  ‖f x‖ ^ 2 := normSq_sum_le _ _
          _ ≤ (B : ℝ) * ∑ x ∈ f.support.filter (fun x => s x = y),
                  ‖f x‖ ^ 2 := by
              have hcard := hB f.support y
              have hnn : (0:ℝ) ≤ ∑ x ∈ f.support.filter
                  (fun x => s x = y), ‖f x‖ ^ 2 :=
                Finset.sum_nonneg fun x _ => sq_nonneg _
              exact mul_le_mul_of_nonneg_right
                (by exact_mod_cast hcard) hnn
    _ = (B : ℝ) * ∑ y ∈ f.support.image s,
          ∑ x ∈ f.support.filter (fun x => s x = y), ‖f x‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ = (B : ℝ) * l2normSq f := by
        congr 1
        exact Finset.sum_fiberwise_of_maps_to
          (fun x hx => Finset.mem_image_of_mem s hx) _

/-- The fibre indicator: `Σ_{x ∈ A} e_x` for a set inside one fibre. -/
noncomputable def fibreIndicator (A : Finset ι) : ι →₀ ℂ :=
  ∑ x ∈ A, Finsupp.single x (1:ℂ)

theorem fibreIndicator_apply (A : Finset ι) (i : ι) :
    fibreIndicator A i = if i ∈ A then (1:ℂ) else 0 := by
  unfold fibreIndicator
  rw [Finset.sum_apply']
  simp [Finsupp.single_apply, Finset.sum_ite_eq]

theorem l2normSq_fibreIndicator (A : Finset ι) :
    l2normSq (fibreIndicator A) = A.card := by
  have hsupp : (fibreIndicator A).support ⊆ A := by
    intro i hi
    by_contra hiA
    have := Finsupp.mem_support_iff.mp hi
    rw [fibreIndicator_apply, if_neg hiA] at this
    exact this rfl
  rw [l2normSq_eq_sum_subset _ hsupp]
  rw [Finset.sum_congr rfl fun i hi => by
    rw [fibreIndicator_apply, if_pos hi, norm_one, one_pow]]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **Theorem `thm:fibre-dichotomy`, sharpness**: a fibre with `k`
points carries the indicator witness with `‖Ŝf‖² = k·‖f‖²` — the shift
norm² equals the supremal fibre cardinality. -/
theorem l2normSq_shiftOp_indicator (s : ι → ι) (y : ι) (A : Finset ι)
    (hA : ∀ x ∈ A, s x = y) :
    l2normSq (shiftOp s (fibreIndicator A))
      = (A.card : ℝ) * l2normSq (fibreIndicator A) := by
  have himg : shiftOp s (fibreIndicator A)
      = Finsupp.single y (A.card : ℂ) := by
    unfold fibreIndicator
    rw [map_sum]
    calc ∑ x ∈ A, shiftOp s (Finsupp.single x (1:ℂ))
        = ∑ x ∈ A, Finsupp.single y (1:ℂ) := by
          refine Finset.sum_congr rfl fun x hx => ?_
          rw [shiftOp_single, hA x hx]
      _ = Finsupp.single y (A.card : ℂ) := by
          rw [Finset.sum_const, Finsupp.smul_single, nsmul_eq_mul,
            mul_one]
  rw [himg, l2normSq_fibreIndicator]
  have hsingle : l2normSq (Finsupp.single y (A.card : ℂ))
      = (A.card : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos A.card with h0 | hpos
    · rw [h0]
      simp [l2normSq]
    · rw [l2normSq_eq_sum_subset _ Finsupp.support_single_subset,
        Finset.sum_singleton, Finsupp.single_eq_same]
      rw [Complex.norm_natCast]
  rw [hsingle]
  ring

/-- **Theorem `thm:fibre-dichotomy`, unbounded half** (with
`cor:sharp-existence`): unbounded fibres defeat every candidate bound —
the descended shift extends to no bounded operator on `ℓ²`.  Combined
with the bounded half, the predictive-length triple exists **iff** the
fibres are uniformly finite. -/
theorem shiftOp_unbounded_of_unbounded_fibres (s : ι → ι)
    (hunb : ∀ B : ℕ, ∃ (y : ι) (A : Finset ι),
      (∀ x ∈ A, s x = y) ∧ B < A.card) (C : ℝ) :
    ∃ f : ι →₀ ℂ, C * l2normSq f < l2normSq (shiftOp s f) := by
  obtain ⟨y, A, hA, hcard⟩ := hunb ⌈max C 0⌉₊
  refine ⟨fibreIndicator A, ?_⟩
  rw [l2normSq_shiftOp_indicator s y A hA, l2normSq_fibreIndicator]
  have hpos : (0:ℝ) < (A.card : ℝ) := by
    have h : (0:ℕ) < A.card := by omega
    exact_mod_cast h
  have hC : C < (A.card : ℝ) := by
    have h1 : C ≤ max C 0 := le_max_left _ _
    have h2 : max C 0 ≤ (⌈max C 0⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : ((⌈max C 0⌉₊ : ℕ) : ℝ) < (A.card : ℝ) := by
      exact_mod_cast hcard
    linarith
  nlinarith

/-! ## Length increments and the Dirac commutator
(`thm:fibre-dichotomy` (2b) and `cor:sharp-existence`, increment
half): the commutator `[D, Ŝ]` is the shift applied after the diagonal
increment multiplier, so bounded increments bound it and unbounded
increments defeat every bound — for **every** bi-Lipschitz
reparametrisation of the length diagonal. -/

/-- Pointwise action of the diagonal operator. -/
theorem diagOp_apply (w : ι → ℂ) (f : ι →₀ ℂ) (i : ι) :
    diagOp w f i = w i * f i := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      rw [map_add, Finsupp.add_apply, hf, hg, Finsupp.add_apply,
        mul_add]
  | single j c =>
      rw [diagOp_single]
      rcases eq_or_ne j i with h | h
      · subst h
        rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
      · simp [Finsupp.single_apply, h]

/-- **Commutator factorization**: `[diagOp d, shiftOp s]` is the shift
composed with the diagonal increment multiplier `d∘s − d`. -/
theorem diagOp_comm_shiftOp_eq (d : ι → ℂ) (s : ι → ι) :
    diagOp d ∘ₗ shiftOp s - shiftOp s ∘ₗ diagOp d
      = shiftOp s ∘ₗ diagOp (fun x => d (s x) - d x) := by
  apply Finsupp.lhom_ext
  intro i c
  rw [diagOp_comm_shiftOp_single, LinearMap.comp_apply, diagOp_single,
    shiftOp_single, Finsupp.smul_single, smul_eq_mul]

/-- A diagonal with uniformly bounded symbol is `ℓ²`-bounded with
norm² at most the symbol bound squared. -/
theorem l2normSq_diagOp_le (w : ι → ℂ) (C : ℝ)
    (hC : ∀ x, ‖w x‖ ≤ C) (f : ι →₀ ℂ) :
    l2normSq (diagOp w f) ≤ C ^ 2 * l2normSq f := by
  have hsupp : (diagOp w f).support ⊆ f.support := by
    intro i hi
    have h1 := Finsupp.mem_support_iff.mp hi
    rw [diagOp_apply] at h1
    exact Finsupp.mem_support_iff.mpr fun h => h1 (by rw [h, mul_zero])
  rw [l2normSq_eq_sum_subset _ hsupp,
    l2normSq_eq_sum_subset f (Finset.Subset.refl _)]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [diagOp_apply, norm_mul, mul_pow]
  have h0 : 0 ≤ ‖w i‖ := norm_nonneg _
  have h1 : ‖w i‖ ^ 2 ≤ C ^ 2 := by nlinarith [hC i]
  exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)

/-- **`cor:sharp-existence` (increment half, bounded direction)**:
uniformly finite fibres and uniformly bounded length increments make
the Dirac commutator `ℓ²`-bounded on the core:
`‖[D, Ŝ]f‖² ≤ B·C²·‖f‖²`. -/
theorem l2normSq_comm_le (d : ι → ℂ) (s : ι → ι) {B : ℕ} (C : ℝ)
    (hB : ∀ (T : Finset ι) (y : ι),
      (T.filter fun x => s x = y).card ≤ B)
    (hC : ∀ x, ‖d (s x) - d x‖ ≤ C) (f : ι →₀ ℂ) :
    l2normSq ((diagOp d ∘ₗ shiftOp s - shiftOp s ∘ₗ diagOp d) f)
      ≤ (B : ℝ) * C ^ 2 * l2normSq f := by
  rw [diagOp_comm_shiftOp_eq, LinearMap.comp_apply]
  calc l2normSq (shiftOp s (diagOp (fun x => d (s x) - d x) f))
      ≤ (B : ℝ) * l2normSq (diagOp (fun x => d (s x) - d x) f) :=
        l2normSq_shiftOp_le s hB _
    _ ≤ (B : ℝ) * (C ^ 2 * l2normSq f) :=
        mul_le_mul_of_nonneg_left
          (l2normSq_diagOp_le _ C hC f) (Nat.cast_nonneg B)
    _ = (B : ℝ) * C ^ 2 * l2normSq f := by ring

theorem l2normSq_single_one (x : ι) :
    l2normSq (Finsupp.single x (1 : ℂ)) = 1 := by
  rw [l2normSq_eq_sum_subset _ Finsupp.support_single_subset,
    Finset.sum_singleton, Finsupp.single_eq_same, norm_one, one_pow]

/-- The commutator on a basis vector has `ℓ²`-norm² exactly the
squared increment. -/
theorem l2normSq_comm_single (d : ι → ℂ) (s : ι → ι) (x : ι) :
    l2normSq ((diagOp d ∘ₗ shiftOp s - shiftOp s ∘ₗ diagOp d)
        (Finsupp.single x 1))
      = ‖d (s x) - d x‖ ^ 2 := by
  rw [diagOp_comm_shiftOp_single, Finsupp.smul_single, smul_eq_mul,
    mul_one]
  rcases eq_or_ne (d (s x) - d x) 0 with h0 | hne
  · rw [h0]
    simp [l2normSq]
  · rw [l2normSq_eq_sum_subset _ Finsupp.support_single_subset,
      Finset.sum_singleton, Finsupp.single_eq_same]

/-- **`thm:fibre-dichotomy` (2b) / `cor:sharp-existence` (increment
half, unbounded direction)**: unbounded `Λ_min`-increments defeat
every candidate commutator bound for **every** bi-Lipschitz-below
reparametrisation `f` of the length diagonal — no reparametrised
length Dirac `f(D_CP)` has a bounded commutator with the shift.
(With `f = id`, `c = 1` this is also the converse of the first box:
bounded commutators force bounded increments.) -/
theorem comm_unbounded_of_unbounded_increments (Λ : ι → ℝ) (s : ι → ι)
    (hunb : ∀ M : ℝ, ∃ x, M ≤ |Λ (s x) - Λ x|)
    (f : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hf : ∀ a b : ℝ, c * |a - b| ≤ |f a - f b|) (C : ℝ) :
    ∃ g : ι →₀ ℂ, l2normSq g = 1 ∧
      C * l2normSq g <
        l2normSq ((diagOp (fun i => (f (Λ i) : ℂ)) ∘ₗ shiftOp s
          - shiftOp s ∘ₗ diagOp (fun i => (f (Λ i) : ℂ))) g) := by
  obtain ⟨x, hx⟩ := hunb ((Real.sqrt (max C 0) + 1) / c)
  refine ⟨Finsupp.single x 1, l2normSq_single_one x, ?_⟩
  rw [l2normSq_single_one, mul_one, l2normSq_comm_single]
  have hcast : (f (Λ (s x)) : ℂ) - (f (Λ x) : ℂ)
      = ((f (Λ (s x)) - f (Λ x) : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  have h2 := hf (Λ (s x)) (Λ x)
  have h4 := mul_le_mul_of_nonneg_left hx hc.le
  rw [mul_div_cancel₀ _ hc.ne'] at h4
  have h1 : Real.sqrt (max C 0) + 1 ≤ |f (Λ (s x)) - f (Λ x)| := by
    linarith
  have hs := Real.sq_sqrt (le_max_right C 0)
  have hs0 := Real.sqrt_nonneg (max C 0)
  have h5 : C < (Real.sqrt (max C 0) + 1) ^ 2 := by
    nlinarith [le_max_left C 0]
  have h6 : (Real.sqrt (max C 0) + 1) ^ 2
      ≤ |f (Λ (s x)) - f (Λ x)| ^ 2 := by
    have hb : (0:ℝ) ≤ Real.sqrt (max C 0) + 1 := by linarith
    nlinarith
  linarith

end NCG
