/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# From nodal Euler bounds to a physical source norm
  (`lem:nodal-source-transfer`, Einstein–SM action closure)

Setting: the mesh-`h` lattice `h ℤ^d` in `ℝ^d` (`Fin d → ℝ`, sup norm, product
Lebesgue measure; the paper has `d = 4`), with half-open cells
`C_k = Π_i [h k_i, h k_i + h)` based at the nodes `x_k = h k`.  For a vector
valued `f` (values in any real normed space) its nodal sample is
`𝖲_h f (x_k) = f(x_k)` and the squared nodal mass norm on the buffered slab is
`‖𝖲_h f‖²_{0,h;Q'} = h^d Σ_{x_k ∈ Q'} |f(x_k)|²` (`nodalMassSq`).

* `lintegral_sq_le_nodalMassSq` — squared form of `eq:nodal-source-transfer`:
  if every cell meeting `Q` lies in `Q'` (the buffer condition, which is what
  "`Q ⋐ Q'` and `h` sufficiently small" provides), and `f` has derivative
  bounded by `L` on `Q'`, then
  `∫_Q |f|² ≤ 2 ‖𝖲_h f‖²_{0,h;Q'} + 2 |Q'| (h L)²`.
  Proof as in the paper: on each cell meeting `Q` the mean-value inequality
  gives `|f(y) - f(x_k)| ≤ h L`; square, integrate over the union of these
  cells (disjoint, total volume `≤ |Q'|`) and use the exact mass `h^d` of each
  cell.
* `eLpNorm_le_nodalNorm` — the norm form
  `‖f‖_{L²(Q)} ≤ √2 ‖𝖲_h f‖_{0,h;Q'} + √2 |Q'|^{1/2} h L`, i.e.
  `eq:nodal-source-transfer` with `C = √2 · max(1, |Q'|^{1/2})`.
* `eLpNorm_le_nodalNorm_growing` — the `O(h K³)` clause: when the derivative of
  the density is bounded by `C_E K³` (the bound the paper derives from
  `eq:growing-derivatives` for an Euler density of differential degree at
  most two), the last term is `√2 |Q'|^{1/2} C_E h K³`.

`∂f` is the Fréchet derivative and `‖∂f‖_∞` its operator norm for the sup norm
on `ℝ^d` (equivalent to the Euclidean one up to a dimensional constant absorbed
in `C`).  No band-limitation or measurability assumption on `f` is needed.
-/

namespace RenewalGeometry

namespace NodalSourceTransfer

open MeasureTheory Set
open scoped ENNReal

variable {d : ℕ}

/-- The lattice node `x_k = h k` of `h ℤ^d`. -/
def node (h : ℝ) (k : Fin d → ℤ) : Fin d → ℝ := fun i => h * k i

/-- The half-open lattice cell `C_k = Π_i [h k_i, h k_i + h)`. -/
def cell (h : ℝ) (k : Fin d → ℤ) : Set (Fin d → ℝ) :=
  pi univ fun i => Ico (h * k i) (h * k i + h)

/-- Squared nodal mass norm `‖𝖲_h v‖²_{0,h;Q'} = h^d Σ_{x_k ∈ Q'} |v(x_k)|²`
(`lem:nodal-source-transfer`), valued in `[0, ∞]`. -/
noncomputable def nodalMassSq {E : Type*} [NormedAddCommGroup E] (h : ℝ)
    (Q' : Set (Fin d → ℝ)) (v : (Fin d → ℝ) → E) : ℝ≥0∞ :=
  ∑' k : {k : Fin d → ℤ // node h k ∈ Q'}, ENNReal.ofReal (h ^ d) * ‖v (node h k)‖ₑ ^ 2

theorem measurableSet_cell (h : ℝ) (k : Fin d → ℤ) : MeasurableSet (cell h k) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

theorem node_mem_cell {h : ℝ} (hh : 0 < h) (k : Fin d → ℤ) : node h k ∈ cell h k :=
  fun i _ => ⟨le_rfl, by simp only [node]; linarith⟩

theorem convex_cell (h : ℝ) (k : Fin d → ℤ) : Convex ℝ (cell h k) :=
  convex_pi fun _ _ => convex_Ico _ _

theorem volume_cell {h : ℝ} (hh : 0 < h) (k : Fin d → ℤ) :
    volume (cell h k) = ENNReal.ofReal (h ^ d) := by
  unfold cell
  rw [Real.volume_pi_Ico]
  simp only [add_sub_cancel_left, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow hh.le]

theorem norm_sub_node_le {h : ℝ} (hh : 0 < h) {k : Fin d → ℤ} {y : Fin d → ℝ}
    (hy : y ∈ cell h k) : ‖y - node h k‖ ≤ h := by
  refine (pi_norm_le_iff_of_nonneg hh.le).2 fun i => ?_
  have := hy i (mem_univ i)
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_le]
  simp only [node]
  constructor <;> linarith [this.1, this.2]

theorem pairwise_disjoint_cell {h : ℝ} (hh : 0 < h) :
    Pairwise (Function.onFun Disjoint (cell (d := d) h)) := by
  intro k k' hkk'
  show Disjoint (cell h k) (cell h k')
  rw [Set.disjoint_left]
  intro x hx hx'
  apply hkk'
  funext i
  have h1 := hx i (mem_univ i)
  have h2 := hx' i (mem_univ i)
  have a1 : h * (k i : ℝ) < h * ((k' i : ℝ) + 1) := by linarith [h1.1, h2.2]
  have a2 : h * (k' i : ℝ) < h * ((k i : ℝ) + 1) := by linarith [h2.1, h1.2]
  have b1 : (k i : ℝ) < (k' i : ℝ) + 1 := lt_of_mul_lt_mul_left a1 hh.le
  have b2 : (k' i : ℝ) < (k i : ℝ) + 1 := lt_of_mul_lt_mul_left a2 hh.le
  have c1 : k i < k' i + 1 := by exact_mod_cast b1
  have c2 : k' i < k i + 1 := by exact_mod_cast b2
  omega

theorem exists_mem_cell {h : ℝ} (hh : 0 < h) (y : Fin d → ℝ) : ∃ k, y ∈ cell h k := by
  refine ⟨fun i => ⌊y i / h⌋, fun i _ => ⟨?_, ?_⟩⟩
  · have := Int.floor_le (y i / h)
    rw [le_div_iff₀ hh] at this
    linarith
  · have := Int.lt_floor_add_one (y i / h)
    rw [div_lt_iff₀ hh] at this
    linarith

/-- Pointwise cell estimate: `|f(y)|² ≤ 2|f(x_k)|² + 2(hL)²` on a cell where
`f` has derivative bounded by `L`. -/
theorem enorm_sq_le_on_cell {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 < h) {k : Fin d → ℤ} {f : (Fin d → ℝ) → E}
    {f' : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] E}
    (hf : ∀ y ∈ cell h k, HasFDerivWithinAt f (f' y) (cell h k) y)
    (hL : ∀ y ∈ cell h k, ‖f' y‖ ≤ L) {y : Fin d → ℝ} (hy : y ∈ cell h k) :
    ‖f y‖ₑ ^ 2 ≤ 2 * ‖f (node h k)‖ₑ ^ 2 + 2 * ENNReal.ofReal (h * L) ^ 2 := by
  have hn := node_mem_cell hh k
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL _ hn)
  have hmv := (convex_cell h k).norm_image_sub_le_of_norm_hasFDerivWithin_le hf hL hn hy
  have h1 : ‖f y‖ ≤ ‖f (node h k)‖ + h * L := by
    calc ‖f y‖ = ‖f (node h k) + (f y - f (node h k))‖ := by congr 1; abel
      _ ≤ ‖f (node h k)‖ + ‖f y - f (node h k)‖ := norm_add_le _ _
      _ ≤ ‖f (node h k)‖ + L * ‖y - node h k‖ := by linarith
      _ ≤ ‖f (node h k)‖ + h * L := by
          have := mul_le_mul_of_nonneg_left (norm_sub_node_le hh hy) hL0
          linarith
  have h2 : ‖f y‖ ^ 2 ≤ 2 * ‖f (node h k)‖ ^ 2 + 2 * (h * L) ^ 2 := by
    have hhL : 0 ≤ h * L := mul_nonneg hh.le hL0
    nlinarith [norm_nonneg (f y), norm_nonneg (f (node h k)),
      sq_nonneg (‖f (node h k)‖ - h * L)]
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (mul_nonneg hh.le hL0)]
  calc ENNReal.ofReal (‖f y‖ ^ 2)
      ≤ ENNReal.ofReal (2 * ‖f (node h k)‖ ^ 2 + 2 * (h * L) ^ 2) := ENNReal.ofReal_le_ofReal h2
    _ = 2 * ENNReal.ofReal (‖f (node h k)‖ ^ 2) + 2 * ENNReal.ofReal ((h * L) ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

/-- `lem:nodal-source-transfer`, squared form of `eq:nodal-source-transfer`:
if every cell of `h ℤ^d` meeting `Q` lies in the buffered slab `Q'` and `f` has
a derivative bounded by `L` on `Q'`, then
`∫_Q |f|² ≤ 2 ‖𝖲_h f‖²_{0,h;Q'} + 2 |Q'| (h L)²`. -/
theorem lintegral_sq_le_nodalMassSq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 < h) {Q Q' : Set (Fin d → ℝ)}
    (hbuf : ∀ k, (cell h k ∩ Q).Nonempty → cell h k ⊆ Q')
    {f : (Fin d → ℝ) → E} {f' : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] E}
    (hf : ∀ y ∈ Q', HasFDerivWithinAt f (f' y) Q' y) (hL : ∀ y ∈ Q', ‖f' y‖ ≤ L) :
    ∫⁻ y in Q, ‖f y‖ₑ ^ 2 ≤
      2 * nodalMassSq h Q' f + 2 * volume Q' * ENNReal.ofReal (h * L) ^ 2 := by
  set N := {k : Fin d → ℤ // (cell h k ∩ Q).Nonempty}
  set c : ℝ≥0∞ := ENNReal.ofReal (h * L) ^ 2
  have hcover : Q ⊆ ⋃ k : N, cell h k.1 := by
    intro y hy
    obtain ⟨k, hk⟩ := exists_mem_cell hh y
    exact mem_iUnion.2 ⟨⟨k, y, hk, hy⟩, hk⟩
  have hcell : ∀ k : N, ∫⁻ y in cell h k.1, ‖f y‖ₑ ^ 2 ≤
      (2 * ‖f (node h k.1)‖ₑ ^ 2 + 2 * c) * ENNReal.ofReal (h ^ d) := by
    intro k
    have hsub := hbuf k.1 k.2
    calc ∫⁻ y in cell h k.1, ‖f y‖ₑ ^ 2
        ≤ ∫⁻ _ in cell h k.1, (2 * ‖f (node h k.1)‖ₑ ^ 2 + 2 * c) :=
          setLIntegral_mono measurable_const fun y hy =>
            enorm_sq_le_on_cell hh (fun z hz => (hf z (hsub hz)).mono hsub)
              (fun z hz => hL z (hsub hz)) hy
      _ = (2 * ‖f (node h k.1)‖ₑ ^ 2 + 2 * c) * ENNReal.ofReal (h ^ d) := by
          rw [setLIntegral_const, volume_cell hh]
  have hvol : ∑' _ : N, ENNReal.ofReal (h ^ d) ≤ volume Q' := by
    calc ∑' _ : N, ENNReal.ofReal (h ^ d) = ∑' k : N, volume (cell h k.1) := by
          simp_rw [volume_cell hh]
      _ = volume (⋃ k : N, cell h k.1) := by
          rw [measure_iUnion]
          · intro a b hab
            exact pairwise_disjoint_cell hh (fun e => hab (Subtype.ext e))
          · exact fun k => measurableSet_cell h k.1
      _ ≤ volume Q' := measure_mono (iUnion_subset fun k => hbuf k.1 k.2)
  have hnodal : ∑' k : N, ENNReal.ofReal (h ^ d) * ‖f (node h k.1)‖ₑ ^ 2 ≤
      nodalMassSq h Q' f := by
    let ι : N → {k : Fin d → ℤ // node h k ∈ Q'} :=
      fun k => ⟨k.1, hbuf k.1 k.2 (node_mem_cell hh k.1)⟩
    have hι : Function.Injective ι := fun a b hab =>
      Subtype.ext (congrArg Subtype.val hab :)
    exact ENNReal.tsum_comp_le_tsum_of_injective hι
      (fun k => ENNReal.ofReal (h ^ d) * ‖f (node h k.1)‖ₑ ^ 2)
  calc ∫⁻ y in Q, ‖f y‖ₑ ^ 2 ≤ ∫⁻ y in ⋃ k : N, cell h k.1, ‖f y‖ₑ ^ 2 :=
        lintegral_mono_set hcover
    _ ≤ ∑' k : N, ∫⁻ y in cell h k.1, ‖f y‖ₑ ^ 2 := lintegral_iUnion_le _ _
    _ ≤ ∑' k : N, (2 * ‖f (node h k.1)‖ₑ ^ 2 + 2 * c) * ENNReal.ofReal (h ^ d) :=
        ENNReal.tsum_le_tsum hcell
    _ = 2 * ∑' k : N, ENNReal.ofReal (h ^ d) * ‖f (node h k.1)‖ₑ ^ 2 +
          2 * c * ∑' _ : N, ENNReal.ofReal (h ^ d) := by
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
        congr 1; funext k; ring
    _ ≤ 2 * nodalMassSq h Q' f + 2 * c * volume Q' := by gcongr
    _ = 2 * nodalMassSq h Q' f + 2 * volume Q' * c := by ring

/-- `lem:nodal-source-transfer`, norm form of `eq:nodal-source-transfer`:
`‖f‖_{L²(Q)} ≤ √2 ‖𝖲_h f‖_{0,h;Q'} + √2 |Q'|^{1/2} h ‖∂f‖_{L^∞(Q')}`,
i.e. `C = √2 · max(1, |Q'|^{1/2})`. -/
theorem eLpNorm_le_nodalNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 < h) {Q Q' : Set (Fin d → ℝ)}
    (hbuf : ∀ k, (cell h k ∩ Q).Nonempty → cell h k ⊆ Q')
    {f : (Fin d → ℝ) → E} {f' : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] E}
    (hf : ∀ y ∈ Q', HasFDerivWithinAt f (f' y) Q' y) (hL : ∀ y ∈ Q', ‖f' y‖ ≤ L) :
    eLpNorm f 2 (volume.restrict Q) ≤
      (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) * nodalMassSq h Q' f ^ (1 / 2 : ℝ) +
        (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) * volume Q' ^ (1 / 2 : ℝ) * ENNReal.ofReal (h * L) := by
  have key := lintegral_sq_le_nodalMassSq hh hbuf hf hL
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  simp only [h2, ENNReal.rpow_two]
  have hp : (0 : ℝ) ≤ 1 / 2 := by norm_num
  calc (∫⁻ y in Q, ‖f y‖ₑ ^ 2) ^ (1 / 2 : ℝ)
      ≤ (2 * nodalMassSq h Q' f + 2 * volume Q' * ENNReal.ofReal (h * L) ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow key hp
    _ ≤ (2 * nodalMassSq h Q' f) ^ (1 / 2 : ℝ) +
          (2 * volume Q' * ENNReal.ofReal (h * L) ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_add_le_add_rpow _ _ hp (by norm_num)
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp, ENNReal.mul_rpow_of_nonneg _ _ hp,
          ENNReal.mul_rpow_of_nonneg _ _ hp, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num

/-- `lem:nodal-source-transfer`, the `O(hK³)` clause: if the density's first
derivative is bounded by `C_E K³` on `Q'` (the bound obtained from
`eq:growing-derivatives` for an Euler density of differential degree at most
two), the sampling term of `eq:nodal-source-transfer` is
`√2 |Q'|^{1/2} C_E h K³`. -/
theorem eLpNorm_le_nodalNorm_growing {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h CE K : ℝ} (hh : 0 < h) {Q Q' : Set (Fin d → ℝ)}
    (hbuf : ∀ k, (cell h k ∩ Q).Nonempty → cell h k ⊆ Q')
    {f : (Fin d → ℝ) → E} {f' : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] E}
    (hf : ∀ y ∈ Q', HasFDerivWithinAt f (f' y) Q' y) (hL : ∀ y ∈ Q', ‖f' y‖ ≤ CE * K ^ 3) :
    eLpNorm f 2 (volume.restrict Q) ≤
      (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) * nodalMassSq h Q' f ^ (1 / 2 : ℝ) +
        (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) * volume Q' ^ (1 / 2 : ℝ) *
          ENNReal.ofReal (CE * h * K ^ 3) := by
  have := eLpNorm_le_nodalNorm hh hbuf hf hL
  rwa [show h * (CE * K ^ 3) = CE * h * K ^ 3 by ring] at this

end NodalSourceTransfer

end RenewalGeometry
