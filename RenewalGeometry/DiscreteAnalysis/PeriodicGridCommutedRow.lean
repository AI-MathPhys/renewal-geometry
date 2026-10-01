/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.PeriodicGridMoserComposition

/-!
# The commuted divergence–transport row on the periodic grid
  (`eq:supp-open-commuted-row`, `eq:supp-open-remainder`; emergent-spacetime manuscript)

For complex arrays on `(ℤ/N)³` (mesh `h = 1/N`):

* `IsMult.comm`, `Dα_Dp`, `Dα_Dm`, `Dα_D0`: Fourier multipliers commute; `D^α` commutes with
  `D_i^±`, `D_i⁰`.
* `sobSq_Dp_le`, `sobSq_Dm_le`, `sobSq_D0_le`: one difference costs one order,
  `‖D u‖_{r,h} ≤ ‖u‖_{r+1,h}`.
* `sobSq_succ_le_shifted` (counting): `‖u‖²_{r+1,h} ≤ Σ_{|α| ≤ r} (‖D^α u‖_h² +
  Σ_i ‖D_i⁺ D^α u‖_h²)`.
* `commuted_row` (**`eq:supp-open-commuted-row`**, exact): if
  `a v_t = Σ_{ij} D_i⁻(c^{ij} D_j⁺ q) - Σ_i (b^i D_i⁰ v + D_i⁰(b^i v)) + G`, then for every
  multi-index `α`, with `a_α = S^α a`, `c_α = S^α c`, `b_α = S^α b`,
  `a_α D^α v_t = Σ_{ij} D_i⁻(c_α^{ij} D_j⁺ D^α q) - 𝖪_{b_α} D^α v + 𝖱_α` with the explicit
  remainder `rowRem` built from shifted commutators and `D^α G`.
* `rowRem_norm_le` (**commutator part of `eq:supp-open-remainder`**): for `s ≥ 3`, `|α| ≤ s` and
  constant coefficient values `a₀, c₀, b₀`, with one `N`-independent constant,
  `‖𝖱_α‖_h ≤ C (‖a - a₀‖_{s,h} ‖v_t‖_{s-1,h} + Σ_{ij} ‖c^{ij} - c₀^{ij}‖_{s+1,h} ‖q‖_{s+1,h}
  + Σ_i ‖b^i - b₀^i‖_{s+1,h} ‖v‖_{s,h}) + ‖G‖_{s,h}`.
-/

open Finset ComplexConjugate
open scoped BigOperators

namespace RenewalGeometry.PeriodicGridSobolev

namespace CommutedRow

open LatticeTorusPlancherel Moser

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N]

/-! ### Commuting multipliers -/

theorem IsMult.comm {T T' : Module.End ℂ (Grid N → ℂ)} {m m' : Grid N → ℂ}
    (h : IsMult T m) (h' : IsMult T' m') (u : Grid N → ℂ) : T (T' u) = T' (T u) :=
  (h.mul h').apply_eq' (h'.mul h) (fun k => mul_comm _ _) u

theorem isMult_D0 (i : Fin 3) :
    IsMult (D0 (N := N) i) (fun k => (2 : ℂ)⁻¹ * (sym i k + (N : ℂ) * (1 - conj (chi i k)))) :=
  ((isMult_Dp i).add (isMult_Dm i)).smul _

theorem Dα_Dp (α : Fin 3 → ℕ) (i : Fin 3) (u : Grid N → ℂ) :
    Dα α (Dp i u) = Dp i (Dα α u) := IsMult.comm (isMult_Dα α) (isMult_Dp i) u

theorem Dα_Dm (α : Fin 3 → ℕ) (i : Fin 3) (u : Grid N → ℂ) :
    Dα α (Dm i u) = Dm i (Dα α u) := IsMult.comm (isMult_Dα α) (isMult_Dm i) u

theorem Dα_D0 (α : Fin 3 → ℕ) (i : Fin 3) (u : Grid N → ℂ) :
    Dα α (D0 i u) = D0 i (Dα α u) := IsMult.comm (isMult_Dα α) (isMult_D0 i) u

/-! ### One difference costs one order -/

theorem Dp_eq_Dα (i : Fin 3) (u : Grid N → ℂ) : Dp i u = Dα (Pi.single i 1) u := by
  have := Dp_Dα (N := N) i 0 u
  rw [Dα_zero, Module.End.one_apply, zero_add] at this
  exact this

theorem deg_single_one (i : Fin 3) : deg (Pi.single i 1 : Fin 3 → ℕ) = 1 := by
  fin_cases i <;> simp [deg]

theorem sobSq_Dp_le (r : ℕ) (i : Fin 3) (u : Grid N → ℂ) : sobSq r (Dp i u) ≤ sobSq (r + 1) u := by
  rw [Dp_eq_Dα]
  exact sobSq_Dα_le (by rw [deg_single_one]; omega) u

theorem sobSq_Dm_eq (r : ℕ) (i : Fin 3) (u : Grid N → ℂ) : sobSq r (Dm i u) = sobSq r (Dp i u) := by
  unfold sobSq
  refine sum_congr rfl fun α _ => ?_
  rw [Dα_Dm, Dα_Dp, ← gridNorm_sq, ← gridNorm_sq, gridNorm_Dm_eq]

theorem sobSq_Dm_le (r : ℕ) (i : Fin 3) (u : Grid N → ℂ) : sobSq r (Dm i u) ≤ sobSq (r + 1) u := by
  rw [sobSq_Dm_eq]; exact sobSq_Dp_le r i u

theorem sobSq_D0_le (r : ℕ) (i : Fin 3) (u : Grid N → ℂ) : sobSq r (D0 i u) ≤ sobSq (r + 1) u := by
  refine le_trans ?_ (sobSq_Dp_le r i u)
  unfold sobSq
  refine sum_le_sum fun α _ => ?_
  rw [Dα_D0, Dα_Dp, ← gridNorm_sq, ← gridNorm_sq]
  exact pow_le_pow_left₀ (gridNorm_nonneg _) (gridNorm_D0_le _ _) 2

theorem sobNorm_Dp_le (r : ℕ) (i : Fin 3) (u : Grid N → ℂ) :
    sobNorm r (Dp i u) ≤ sobNorm (r + 1) u := Real.sqrt_le_sqrt (sobSq_Dp_le r i u)

theorem sobNorm_Dm_le (r : ℕ) (i : Fin 3) (u : Grid N → ℂ) :
    sobNorm r (Dm i u) ≤ sobNorm (r + 1) u := Real.sqrt_le_sqrt (sobSq_Dm_le r i u)

theorem sobNorm_D0_le (r : ℕ) (i : Fin 3) (u : Grid N → ℂ) :
    sobNorm r (D0 i u) ≤ sobNorm (r + 1) u := Real.sqrt_le_sqrt (sobSq_D0_le r i u)

theorem gridNorm_Dα_le_sobNorm {r : ℕ} {α : Fin 3 → ℕ} (h : deg α ≤ r) (u : Grid N → ℂ) :
    gridNorm (Dα α u) ≤ sobNorm r u := Real.sqrt_le_sqrt (gridNormSq_Dα_le_sobSq h u)

/-! ### Counting: the top order is reached by one forward difference -/

/-- The first coordinate in which a nonzero multi-index is positive. -/
def firstPos (β : Fin 3 → ℕ) : Fin 3 := if β 0 ≠ 0 then 0 else if β 1 ≠ 0 then 1 else 2

theorem firstPos_pos {β : Fin 3 → ℕ} (h : 1 ≤ deg β) : 1 ≤ β (firstPos β) := by
  unfold firstPos deg at *
  split_ifs with h0 h1 <;> omega

theorem sub_add_single {β : Fin 3 → ℕ} {i : Fin 3} (h : 1 ≤ β i) :
    β - Pi.single i 1 + Pi.single i 1 = β := by
  funext j
  by_cases hj : j = i
  · subst hj; simp; omega
  · simp [hj]

/-- **Counting lemma**: `‖u‖²_{r+1,h} ≤ Σ_{|α| ≤ r} (‖D^α u‖_h² + Σ_i ‖D_i⁺ D^α u‖_h²)`. -/
theorem sobSq_succ_le_shifted (r : ℕ) (u : Grid N → ℂ) :
    sobSq (r + 1) u ≤ ∑ α ∈ multiIndices r,
      (gridNormSq (Dα α u) + ∑ i, gridNormSq (Dp i (Dα α u))) := by
  set f : (Fin 3 → ℕ) → ℝ := fun β => gridNormSq (Dα β u)
  have hf : ∀ β, 0 ≤ f β := fun _ => gridNormSq_nonneg _
  unfold sobSq
  rw [← sum_filter_add_sum_filter_not (multiIndices (r + 1)) (fun β => deg β ≤ r)]
  have h1 : (multiIndices (r + 1)).filter (fun β => deg β ≤ r) = multiIndices r := by
    ext β; simp only [mem_filter, mem_multiIndices]; omega
  rw [h1, sum_add_distrib]
  refine add_le_add le_rfl ?_
  set T := (multiIndices (r + 1)).filter (fun β => ¬ deg β ≤ r)
  set g : (Fin 3 → ℕ) → (Fin 3 → ℕ) × Fin 3 := fun β => (β - Pi.single (firstPos β) 1, firstPos β)
  have hT : ∀ β ∈ T, 1 ≤ deg β := fun β hβ => by
    simp only [T, mem_filter, mem_multiIndices] at hβ; omega
  have hinj : Set.InjOn g T := by
    intro β hβ β' hβ' he
    have h2 : (g β).2 = (g β').2 := by rw [he]
    have h1' : (g β).1 = (g β').1 := by rw [he]
    simp only [g] at h1' h2
    rw [← sub_add_single (firstPos_pos (hT β hβ)), ← sub_add_single (firstPos_pos (hT β' hβ')),
      h1', h2]
  have hval : ∀ β ∈ T, f β = gridNormSq (Dp (g β).2 (Dα (g β).1 u)) := by
    intro β hβ
    simp only [f, g]
    rw [Dp_Dα, sub_add_single (firstPos_pos (hT β hβ))]
  rw [sum_congr rfl hval, ← sum_image (f := fun p => gridNormSq (Dp p.2 (Dα p.1 u))) hinj]
  have hsub : T.image g ⊆ multiIndices r ×ˢ univ := by
    intro p hp
    obtain ⟨β, hβ, rfl⟩ := mem_image.mp hp
    simp only [mem_product, mem_univ, and_true, mem_multiIndices]
    have hβ' := hβ
    simp only [T, mem_filter, mem_multiIndices] at hβ'
    have hpos := firstPos_pos (hT β hβ)
    have := deg_add (β - Pi.single (firstPos β) 1) (Pi.single (firstPos β) 1)
    rw [sub_add_single hpos, deg_single_one] at this
    simp only [g]; omega
  refine (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => gridNormSq_nonneg _).trans ?_
  rw [sum_product]

/-! ### The commuted row -/

/-- The remainder `𝖱_α` of the commuted row (`eq:supp-open-commuted-row`): every term is a
shifted commutator or `D^α G`. -/
noncomputable def rowRem (α : Fin 3 → ℕ) (a vt v q G : Grid N → ℂ) (c : Fin 3 → Fin 3 → Grid N → ℂ)
    (b : Fin 3 → Grid N → ℂ) : Grid N → ℂ :=
  -commutator α a vt + ∑ i, ∑ j, Dm i (commutator α (c i j) (Dp j q))
    - ∑ i, (commutator α (b i) (D0 i v) + D0 i (commutator α (b i) v)) + Dα α G

theorem Dα_mul_eq (α : Fin 3 → ℕ) (f w : Grid N → ℂ) :
    Dα α (f * w) = Sα α f * Dα α w + commutator α f w := by
  rw [commutator]; abel

/-- **The commuted row** (`eq:supp-open-commuted-row`), an exact identity. -/
theorem commuted_row (α : Fin 3 → ℕ) (a vt v q G : Grid N → ℂ)
    (c : Fin 3 → Fin 3 → Grid N → ℂ) (b : Fin 3 → Grid N → ℂ)
    (hrow : a * vt = ∑ i, ∑ j, Dm i (c i j * Dp j q) -
      ∑ i, (b i * D0 i v + D0 i (b i * v)) + G) :
    Sα α a * Dα α vt = ∑ i, ∑ j, Dm i (Sα α (c i j) * Dp j (Dα α q)) -
      ∑ i, (Sα α (b i) * D0 i (Dα α v) + D0 i (Sα α (b i) * Dα α v)) +
      rowRem α a vt v q G c b := by
  have h := congrArg (Dα α) hrow
  simp only [map_add, map_sub, map_sum, Dα_Dm, Dα_D0, Dα_mul_eq, Dα_Dp] at h
  simp only [map_add, sum_add_distrib] at h
  rw [rowRem]
  simp only [sum_add_distrib]
  linear_combination h

/-- **Commutator part of the remainder bound** (`eq:supp-open-remainder`): one
`N`-independent constant `C_s` (`s ≥ 3`) bounds `‖𝖱_α‖_h` for every `|α| ≤ s`. -/
theorem rowRem_norm_le (s : ℕ) (hs : 3 ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (α : Fin 3 → ℕ), deg α ≤ s →
      ∀ (a vt v q G : Grid N → ℂ) (c : Fin 3 → Fin 3 → Grid N → ℂ) (b : Fin 3 → Grid N → ℂ)
        (a₀ : ℂ) (c₀ : Fin 3 → Fin 3 → ℂ) (b₀ : Fin 3 → ℂ),
        gridNorm (rowRem α a vt v q G c b) ≤
          C * (sobNorm s (a - fun _ => a₀) * sobNorm (s - 1) vt +
            ∑ i, ∑ j, sobNorm (s + 1) (c i j - fun _ => c₀ i j) * sobNorm (s + 1) q +
            ∑ i, sobNorm (s + 1) (b i - fun _ => b₀ i) * sobNorm s v) + sobNorm s G := by
  obtain ⟨C, hC, hcalc⟩ := uniform_sobolev_calculus s hs
  refine ⟨2 * C, by positivity, fun N _ α hα a vt v q G c b a₀ c₀ b₀ => ?_⟩
  obtain ⟨-, hcomm⟩ := hcalc N
  have hv1 : ∀ i, sobNorm (s - 1) (D0 i v) ≤ sobNorm s v := fun i => by
    have := sobNorm_D0_le (s - 1) i v
    rwa [show s - 1 + 1 = s by omega] at this
  have hbs : ∀ i, sobNorm s (b i - fun _ => b₀ i) ≤ sobNorm (s + 1) (b i - fun _ => b₀ i) :=
    fun i => sobNorm_mono (by omega) _
  -- the four groups
  have t1 : gridNorm (commutator α a vt) ≤ C * sobNorm s (a - fun _ => a₀) * sobNorm (s - 1) vt :=
    (hcomm α hα a vt a₀ 0).1
  have t2 : ∀ i j, gridNorm (Dm i (commutator α (c i j) (Dp j q))) ≤
      C * sobNorm (s + 1) (c i j - fun _ => c₀ i j) * sobNorm (s + 1) q := by
    intro i j
    have h := (hcomm α hα (c i j) (Dp j q) (c₀ i j) i).2
    have hq := sobNorm_Dp_le s j q
    have := gridNorm_nonneg (D0 i (commutator α (c i j) (Dp j q)))
    have := sobNorm_nonneg (s + 1) (c i j - fun _ => c₀ i j)
    calc gridNorm (Dm i (commutator α (c i j) (Dp j q)))
        ≤ C * sobNorm (s + 1) (c i j - fun _ => c₀ i j) * sobNorm s (Dp j q) := by linarith
      _ ≤ C * sobNorm (s + 1) (c i j - fun _ => c₀ i j) * sobNorm (s + 1) q := by gcongr
  have t3 : ∀ i, gridNorm (commutator α (b i) (D0 i v) + D0 i (commutator α (b i) v)) ≤
      2 * C * sobNorm (s + 1) (b i - fun _ => b₀ i) * sobNorm s v := by
    intro i
    have h1 := (hcomm α hα (b i) (D0 i v) (b₀ i) i).1
    have h2 := (hcomm α hα (b i) v (b₀ i) i).2
    have := gridNorm_nonneg (Dm i (commutator α (b i) v))
    have := sobNorm_nonneg s (b i - fun _ => b₀ i)
    have := sobNorm_nonneg (s - 1) (D0 i v)
    refine (gridNorm_add_le _ _).trans ?_
    have h1' : gridNorm (commutator α (b i) (D0 i v)) ≤
        C * sobNorm (s + 1) (b i - fun _ => b₀ i) * sobNorm s v :=
      h1.trans (mul_le_mul (mul_le_mul_of_nonneg_left (hbs i) hC) (hv1 i)
        (sobNorm_nonneg _ _) (mul_nonneg hC (sobNorm_nonneg _ _)))
    linarith
  have t4 : gridNorm (Dα α G) ≤ sobNorm s G := gridNorm_Dα_le_sobNorm hα G
  have hA : 0 ≤ sobNorm s (a - fun _ => a₀) * sobNorm (s - 1) vt :=
    mul_nonneg (sobNorm_nonneg _ _) (sobNorm_nonneg _ _)
  have hB : 0 ≤ ∑ i, ∑ j, sobNorm (s + 1) (c i j - fun _ => c₀ i j) * sobNorm (s + 1) q :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => mul_nonneg (sobNorm_nonneg _ _) (sobNorm_nonneg _ _)
  have hB' : 0 ≤ ∑ i, sobNorm (s + 1) (b i - fun _ => b₀ i) * sobNorm s v :=
    sum_nonneg fun _ _ => mul_nonneg (sobNorm_nonneg _ _) (sobNorm_nonneg _ _)
  unfold rowRem
  calc gridNorm (-commutator α a vt + ∑ i, ∑ j, Dm i (commutator α (c i j) (Dp j q))
        - ∑ i, (commutator α (b i) (D0 i v) + D0 i (commutator α (b i) v)) + Dα α G)
      ≤ gridNorm (commutator α a vt) + ∑ i, ∑ j, gridNorm (Dm i (commutator α (c i j) (Dp j q)))
        + ∑ i, gridNorm (commutator α (b i) (D0 i v) + D0 i (commutator α (b i) v))
        + gridNorm (Dα α G) := by
        refine (gridNorm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (gridNorm_sub_le _ _).trans (add_le_add ?_ (gridNorm_sum_le _ _))
        refine (gridNorm_add_le _ _).trans (add_le_add (le_of_eq (gridNorm_neg _)) ?_)
        exact (gridNorm_sum_le _ _).trans (sum_le_sum fun i _ => gridNorm_sum_le _ _)
    _ ≤ C * sobNorm s (a - fun _ => a₀) * sobNorm (s - 1) vt +
        ∑ i, ∑ j, C * sobNorm (s + 1) (c i j - fun _ => c₀ i j) * sobNorm (s + 1) q +
        ∑ i, 2 * C * sobNorm (s + 1) (b i - fun _ => b₀ i) * sobNorm s v + sobNorm s G := by
        gcongr with i _ j _ i _
        · exact t2 i j
        · exact t3 i
    _ ≤ 2 * C * (sobNorm s (a - fun _ => a₀) * sobNorm (s - 1) vt +
          ∑ i, ∑ j, sobNorm (s + 1) (c i j - fun _ => c₀ i j) * sobNorm (s + 1) q +
          ∑ i, sobNorm (s + 1) (b i - fun _ => b₀ i) * sobNorm s v) + sobNorm s G := by
        have e1 : ∑ i, ∑ j, C * sobNorm (s + 1) (c i j - fun _ => c₀ i j) * sobNorm (s + 1) q =
            C * ∑ i, ∑ j, sobNorm (s + 1) (c i j - fun _ => c₀ i j) * sobNorm (s + 1) q := by
          rw [mul_sum]
          refine sum_congr rfl fun i _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun j _ => ?_
          ring
        have e2 : ∑ i, 2 * C * sobNorm (s + 1) (b i - fun _ => b₀ i) * sobNorm s v =
            2 * C * ∑ i, sobNorm (s + 1) (b i - fun _ => b₀ i) * sobNorm s v := by
          rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
        rw [e1, e2]
        nlinarith

end CommutedRow

end RenewalGeometry.PeriodicGridSobolev
