/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeSlabFourierBridge
import RenewalGeometry.Continuum.NativeEulerTail
import RenewalGeometry.DiscreteAnalysis.NodalSourceTransferExact
import RenewalGeometry.Analysis.DyadicRateAsymptotics

/-!
# The zero-order physical source of the complete reconstruction (`eq:native-zero-source`)

Einstein–Standard-Model action-closure manuscript, `thm:native-source`, first display: for the
complete, unfiltered reconstruction `z_h = 𝓘_h^trig u_h` of a record on the odd grid `(ℤ/n)⁴`
(mesh `h = 2π/n`, period-`2π` box),
`‖𝓡_B(z_h)‖_{L²(Q)} + ‖𝓡_D(z_h)‖_{L²(Q)} ≤ C ε_{0,h}`, `ε_{0,h} = σ_h + hK³`,
where `σ_h` bounds the finite-action covector norm `‖E_h^raw(u_h)‖_{0,h;Q'}` on the buffered slab.

Proof as in the manuscript: the full field satisfies the growing derivative reserve by the tail
bounds (Bernstein for the low head plus the measured tail), so `prop:native-consistency`
(`NativeEulerConsistency.native_consistency`) gives `|E_h^raw(𝖲_h z_h)(x) - 𝓔₀(z_h)(x)| ≤ C h K³` at
every node; `𝖲_h z_h = u_h` (`TrigInterp.recon_gpos`, odd `n`); `lem:nodal-source-transfer`
(`NodalSourceTransfer.lintegral_sq_le_nodalMassSq`) converts the nodal bound into the continuum
`L²(Q)` bound, with the derivative of the Euler density bounded by `C K³`.

## Main results

* `slabIco`, `bufSlab`, `slab_ae_eq_slabIco`: the half-open slab used for the cell decomposition
  is a.e. equal to `NativeSlab.slab`.
* `cell_subset_bufSlab`: the buffer condition `cells meeting Q ⊆ Q'` for `h ≤ δ`.
* `nodalMassSq_le_grid`: the lattice mass on `Q'` is the grid mass of the record's nodes in `Q'`.
* **`native_zero_source`** (`eq:native-zero-source`).
-/

open MeasureTheory Filter Topology Set Finset
open scoped Real ENNReal Nat ContDiff

namespace RenewalGeometry.NativeZeroSource

open ShiftedJetAction (Grid unitVec stencil action)
open NativeScaling (Mat eta metric readerOmega omegaLink)
open ShiftedPlaquette NativeDensity DiscreteEulerConsistency NativeEulerConsistency NativeTail
open TrigInterp (recon reconLow tau)
open ContEulerBounds (jetP eulerOp)
open Metric (mem_closedBall closedBall cthickening)

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-! ### Slabs and cells -/

/-- The half-open slab `[t₀,t₁] × [0,2π)³`. -/
def slabIco (t₀ t₁ : ℝ) : Set R4 := {z | z 0 ∈ Icc t₀ t₁ ∧ ∀ i : Fin 3, z i.succ ∈ Ico 0 (2 * π)}

/-- The buffered slab `Q' = [a,b) × [0,2π)³`. -/
def bufSlab (a b : ℝ) : Set R4 := {z | z 0 ∈ Ico a b ∧ ∀ i : Fin 3, z i.succ ∈ Ico 0 (2 * π)}

theorem slab_eq_pi (t₀ t₁ : ℝ) : NativeSlab.slab t₀ t₁ =
    Set.pi univ (Fin.cons (Icc t₀ t₁) (fun _ => Ioc 0 (2 * π)) : Fin 4 → Set ℝ) := by
  ext z
  simp only [NativeSlab.slab, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
  constructor
  · rintro ⟨h0, hi⟩ μ
    induction μ using Fin.cases with
    | zero => simpa using h0
    | succ i => simpa using hi i
  · intro h
    exact ⟨by simpa using h 0, fun i => by simpa using h i.succ⟩

theorem slabIco_eq_pi (t₀ t₁ : ℝ) : slabIco t₀ t₁ =
    Set.pi univ (Fin.cons (Icc t₀ t₁) (fun _ => Ico 0 (2 * π)) : Fin 4 → Set ℝ) := by
  ext z
  simp only [slabIco, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
  constructor
  · rintro ⟨h0, hi⟩ μ
    induction μ using Fin.cases with
    | zero => simpa using h0
    | succ i => simpa using hi i
  · intro h
    exact ⟨by simpa using h 0, fun i => by simpa using h i.succ⟩

/-- The two slabs differ by a null set. -/
theorem slab_ae_eq_slabIco (t₀ t₁ : ℝ) :
    NativeSlab.slab t₀ t₁ =ᵐ[MeasureTheory.volume] slabIco t₀ t₁ := by
  rw [slab_eq_pi, slabIco_eq_pi, volume_pi]
  refine (Measure.ae_eq_set_pi fun μ _ => ?_)
  induction μ using Fin.cases with
  | zero => exact EventuallyEq.rfl
  | succ i =>
    simp only [Fin.cons_succ]
    exact Ioc_ae_eq_Icc.trans Ico_ae_eq_Icc.symm

theorem measurableSet_slabIco (t₀ t₁ : ℝ) : MeasurableSet (slabIco t₀ t₁) := by
  rw [slabIco_eq_pi]
  exact MeasurableSet.univ_pi fun μ => by
    induction μ using Fin.cases with
    | zero => exact measurableSet_Icc
    | succ i => exact measurableSet_Ico

theorem bufSlab_eq_pi (a b : ℝ) : bufSlab a b =
    Set.pi univ (Fin.cons (Ico a b) (fun _ => Ico 0 (2 * π)) : Fin 4 → Set ℝ) := by
  ext z
  simp only [bufSlab, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
  constructor
  · rintro ⟨h0, hi⟩ μ
    induction μ using Fin.cases with
    | zero => simpa using h0
    | succ i => simpa using hi i
  · intro h
    exact ⟨by simpa using h 0, fun i => by simpa using h i.succ⟩

theorem volume_bufSlab_ne_top (a b : ℝ) : MeasureTheory.volume (bufSlab a b) ≠ ⊤ := by
  rw [bufSlab_eq_pi, volume_pi_pi]
  refine ENNReal.prod_ne_top fun μ _ => ?_
  induction μ using Fin.cases with
  | zero => simp
  | succ i => simpa using ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top

/-- **Buffer condition**: for `h = 2π/n ≤ δ`, every cell meeting `[t₀,t₁] × [0,2π)³` lies in
`[t₀-δ, t₁+δ) × [0,2π)³`. -/
theorem cell_subset_bufSlab {n : ℕ} [NeZero n] {h δ t₀ t₁ : ℝ} (hh : h = 2 * π / n)
    (hδ : h ≤ δ) (k : Fin 4 → ℤ)
    (hk : (NodalSourceTransfer.cell h k ∩ slabIco t₀ t₁).Nonempty) :
    NodalSourceTransfer.cell h k ⊆ bufSlab (t₀ - δ) (t₁ + δ) := by
  obtain ⟨y, hyc, hyQ⟩ := hk
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hh0 : 0 < h := by rw [hh]; positivity
  have hnh : (n : ℝ) * h = 2 * π := by rw [hh]; field_simp
  intro z hz
  have hcz := fun μ => hz μ (mem_univ μ)
  have hcy := fun μ => hyc μ (mem_univ μ)
  have hy0 : h * (k 0 : ℝ) ≤ y 0 ∧ y 0 < h * (k 0 : ℝ) + h := hcy 0
  have hz0 : h * (k 0 : ℝ) ≤ z 0 ∧ z 0 < h * (k 0 : ℝ) + h := hcz 0
  have hQ0 : t₀ ≤ y 0 ∧ y 0 ≤ t₁ := hyQ.1
  refine ⟨⟨?_, ?_⟩, fun i => ⟨?_, ?_⟩⟩
  · linarith
  · linarith
  · -- spatial lower bound: `k ≥ 0`
    have h1 := hcy i.succ; have h2 := hcz i.succ; have h3 := hyQ.2 i
    have hk0 : (-1 : ℝ) < k i.succ := by
      have : h * (k i.succ : ℝ) + h > 0 := by linarith [h3.1, h1.2]
      nlinarith
    have hk0' : (0 : ℤ) ≤ k i.succ := by
      have : (-1 : ℤ) < k i.succ := by exact_mod_cast hk0
      omega
    have : (0 : ℝ) ≤ k i.succ := by exact_mod_cast hk0'
    nlinarith [h2.1]
  · -- spatial upper bound: `k ≤ n - 1`
    have h1 := hcy i.succ; have h2 := hcz i.succ; have h3 := hyQ.2 i
    have hkn : (k i.succ : ℝ) < n := by
      have : h * (k i.succ : ℝ) < h * n := by rw [mul_comm h (n : ℝ), hnh]; linarith [h1.1, h3.2]
      exact lt_of_mul_lt_mul_left this hh0.le
    have hkn' : k i.succ + 1 ≤ (n : ℤ) := by
      have : k i.succ < (n : ℤ) := by exact_mod_cast hkn
      omega
    have : (k i.succ : ℝ) + 1 ≤ n := by exact_mod_cast hkn'
    have : h * (k i.succ : ℝ) + h ≤ 2 * π := by rw [← hnh]; nlinarith
    linarith [h2.2]

open Classical in
/-- **The lattice mass on the buffered slab is a grid mass**: for `0 < a`, `b ≤ 2π` and
`h = 2π/n`, the nodes `h k ∈ Q'` are exactly the grid nodes `pos h x ∈ Q'`. -/
theorem nodalMassSq_le_grid {E : Type*} [NormedAddCommGroup E] {n : ℕ} [NeZero n] {h a b : ℝ}
    (hh : h = 2 * π / n) (ha : 0 < a) (hb : b ≤ 2 * π) (f : R4 → E) :
    NodalSourceTransfer.nodalMassSq h (bufSlab a b) f ≤
      ENNReal.ofReal (h ^ 4 * ∑ x ∈ Finset.univ.filter (fun x : Grid n => pos h x ∈ bufSlab a b),
        ‖f (pos h x)‖ ^ 2) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hh0 : 0 < h := by rw [hh]; positivity
  have hnh : (n : ℝ) * h = 2 * π := by rw [hh]; field_simp
  -- nodes in `Q'` have coordinates in `[0, n)`
  have hrange : ∀ k : Fin 4 → ℤ, NodalSourceTransfer.node h k ∈ bufSlab a b →
      ∀ μ, 0 ≤ k μ ∧ k μ < n := by
    intro k hk μ
    have hbnd : 0 ≤ h * (k μ : ℝ) ∧ h * (k μ : ℝ) < 2 * π := by
      induction μ using Fin.cases with
      | zero =>
        have := hk.1
        simp only [NodalSourceTransfer.node] at this
        exact ⟨by linarith [this.1], by linarith [this.2]⟩
      | succ i =>
        have := hk.2 i
        simp only [NodalSourceTransfer.node] at this
        exact ⟨this.1, this.2⟩
    have h1 : (0 : ℝ) ≤ k μ := by
      by_contra hc
      have hc' : (k μ : ℝ) < 0 := not_le.mp hc
      nlinarith [hbnd.1]
    have h2 : (k μ : ℝ) < n := by
      have : h * (k μ : ℝ) < h * n := by rw [mul_comm h (n : ℝ), hnh]; exact hbnd.2
      exact lt_of_mul_lt_mul_left this hh0.le
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  set S := Finset.univ.filter (fun x : Grid n => pos h x ∈ bufSlab a b)
  -- the reduction map
  let red : {k : Fin 4 → ℤ // NodalSourceTransfer.node h k ∈ bufSlab a b} → S := fun k =>
    ⟨fun μ => ((k.1 μ : ℤ) : ZMod n), by
      have hpos : pos h (fun μ => ((k.1 μ : ℤ) : ZMod n)) = NodalSourceTransfer.node h k.1 := by
        funext μ
        obtain ⟨h1, h2⟩ := hrange k.1 k.2 μ
        simp only [pos, NodalSourceTransfer.node]
        congr 1
        have : (((k.1 μ : ℤ) : ZMod n).val : ℤ) = k.1 μ := by
          rw [ZMod.val_intCast]; exact Int.emod_eq_of_lt h1 h2
        exact_mod_cast this
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hpos]; exact k.2⟩
  have hredpos : ∀ k, pos h (red k).1 = NodalSourceTransfer.node h k.1 := by
    intro k
    funext μ
    obtain ⟨h1, h2⟩ := hrange k.1 k.2 μ
    simp only [red, pos, NodalSourceTransfer.node]
    congr 1
    have : (((k.1 μ : ℤ) : ZMod n).val : ℤ) = k.1 μ := by
      rw [ZMod.val_intCast]; exact Int.emod_eq_of_lt h1 h2
    exact_mod_cast this
  have hredinj : Function.Injective red := by
    intro k k' hkk
    apply Subtype.ext
    funext μ
    have hpos := congrArg (fun x : S => pos h x.1 μ) hkk
    simp only [hredpos] at hpos
    simp only [NodalSourceTransfer.node] at hpos
    have : (k.1 μ : ℝ) = k'.1 μ := mul_left_cancel₀ hh0.ne' hpos
    exact_mod_cast this
  unfold NodalSourceTransfer.nodalMassSq
  have hcomp := ENNReal.tsum_comp_le_tsum_of_injective hredinj
    (fun x : S => ENNReal.ofReal (h ^ 4) * ‖f (pos h x.1)‖ₑ ^ 2)
  simp only [hredpos] at hcomp
  refine hcomp.trans (le_of_eq ?_)
  rw [tsum_fintype, Finset.sum_coe_sort S (fun x => ENNReal.ofReal (h ^ 4) * ‖f (pos h x)‖ₑ ^ 2),
    ← Finset.mul_sum, ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]

/-! ### The complete reconstruction: derivative reserve, samples, Euler density -/

section Native

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)

local notation "FJ" => ContEulerBounds.JS (Field 𝔄 𝓗 𝓢)
local notation "FF" => Field 𝔄 𝓗 𝓢

/-- **The growing derivative reserve of the complete field** (`eq:growing-derivatives` for
`z_h`, orders `j ≤ 3`): `‖D^j z_h‖ ≤ ((240K)^j A + K^j τ_{h,3})`. -/
theorem norm_iteratedFDeriv_recon_le {n : ℕ} [NeZero n] (u : Grid n → FF) {K A : ℝ}
    (hK : 1 ≤ K) (hA : ∀ y, ‖reconLow n K u y‖ ≤ A) {j : ℕ} (hj : j ≤ 3) (x : R4) :
    ‖iteratedFDeriv ℝ j (recon n u) x‖ ≤ (240 ^ 3 * A + tau n K 3 u) * K ^ j := by
  have hK0 : 0 < K := by linarith
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hτ := TrigInterp.tau_nonneg n hK0 3 u
  have e : recon n u = reconLow n K u + fun x => recon n u x - reconLow n K u x := by
    funext x; simp
  have hlo : ContDiff ℝ ∞ (reconLow n K u) := contDiff_reconLow u K
  have hfu : ContDiff ℝ ∞ (recon n u) := contDiff_recon u
  have hj' := ContEulerBounds.natCast_le_infty j
  rw [e, iteratedFDeriv_add_apply (hlo.of_le hj').contDiffAt ((hfu.sub hlo).of_le hj').contDiffAt]
  have h1 := TrigInterp.norm_iteratedFDeriv_reconLow_le n hK0.le u hA j x
  have h2 := TrigInterp.norm_iteratedFDeriv_tail_le n hK0 u hj x
  have h3 : (60 * ((4 : ℕ) : ℝ) * K) ^ j * A ≤ 240 ^ 3 * A * K ^ j := by
    have : (60 * ((4 : ℕ) : ℝ) * K) ^ j = 240 ^ j * K ^ j := by rw [← mul_pow]; norm_num
    rw [this]
    have h240 : (240 : ℝ) ^ j ≤ 240 ^ 3 := pow_le_pow_right₀ (by norm_num) hj
    have hKj : 0 ≤ K ^ j := by positivity
    have := mul_le_mul_of_nonneg_right h240 (mul_nonneg hKj hA0)
    nlinarith
  calc ‖iteratedFDeriv ℝ j (reconLow n K u) x +
        iteratedFDeriv ℝ j (fun x => recon n u x - reconLow n K u x) x‖
      ≤ ‖iteratedFDeriv ℝ j (reconLow n K u) x‖ +
          ‖iteratedFDeriv ℝ j (fun x => recon n u x - reconLow n K u x) x‖ := norm_add_le _ _
    _ ≤ 240 ^ 3 * A * K ^ j + K ^ j * tau n K 3 u := add_le_add (h1.trans h3) h2
    _ = (240 ^ 3 * A + tau n K 3 u) * K ^ j := by ring

/-- The samples of the reconstruction are the record (`n` odd, `h = 2π/n`). -/
theorem samp_recon {n : ℕ} [NeZero n] (hn : Odd n) (u : Grid n → FF) :
    samp (2 * π / n) (recon n u) = u := by
  funext x
  have : pos (2 * π / n) x = TrigInterp.gpos n x := rfl
  rw [samp, this, TrigInterp.recon_gpos n hn u x]

theorem isPeriodic_recon {n : ℕ} [NeZero n] (u : Grid n → FF) :
    IsPeriodic ((n : ℝ) * (2 * π / n)) (recon n u) := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  rw [show (n : ℝ) * (2 * π / n) = 2 * π by field_simp]
  exact NativeTail.isPeriodic_tp _

variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]

/-- **The Euler density of the complete field has derivative `O(K³)`** (`lem:nodal-source-transfer`:
"differentiating once and applying `eq:growing-derivatives` bounds its first derivative by `CK³`"). -/
theorem exists_fderiv_Rfull_bound {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det)
    (A τs : ℝ) :
    ∃ CE : ℝ, 0 ≤ CE ∧ ∀ (n : ℕ) [NeZero n] (u : Grid n → FF) (K : ℝ), 1 ≤ K →
      tau n K 3 u ≤ τs → (∀ x, ‖reconLow n K u x‖ ≤ A) →
      (∀ x, (recon n u x).1 ∈ Ke) → (∀ x, ‖recon n u x‖ ≤ A) →
      ContDiff ℝ ∞ (Rfull D (recon n u)) ∧
        ∀ x, ‖fderiv ℝ (Rfull D (recon n u)) x‖ ≤ CE * K ^ 3 := by
  obtain ⟨A', hA'0, hAA'⟩ : ∃ A' : ℝ, 0 ≤ A' ∧ A ≤ A' := ⟨max A 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨τ', hτ'0, hττ'⟩ : ∃ τ' : ℝ, 0 ≤ τ' ∧ τs ≤ τ' := ⟨max τs 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨δ, hδ, M, hM0, hsU, -, hbU, -⟩ :=
    exists_native_constants D hKe hdet A' (240 * A' + τ') 2
  set B : ℝ := 5 * 240 ^ 3 * (A' + 1) + 5 * τ' with hBdef
  have hB1 : 1 ≤ B := by
    have : (1 : ℝ) ≤ 5 * 240 ^ 3 * (A' + 1) := by nlinarith
    rw [hBdef]; linarith
  refine ⟨ContEulerBounds.cE 1 * M * B ^ 2, by have := ContEulerBounds.cE_nonneg 1; positivity, ?_⟩
  intro n _ u K hK hτ hAl hKe' hAf
  have hK0 : 0 < K := by linarith
  have hτ0 := TrigInterp.tau_nonneg n hK0 3 u
  have hAl' : ∀ y, ‖reconLow n K u y‖ ≤ A' := fun y => (hAl y).trans hAA'
  set Y := recon n u
  have hY : ContDiff ℝ ∞ Y := contDiff_recon u
  set Yt := resc K Y
  have hYt : ContDiff ℝ ∞ Yt := hY.comp (contDiff_const_smul K⁻¹)
  -- the full jets lie in the compact jet set
  have hmem : ∀ ξ, jetP K⁻¹ Yt ξ ∈ jetSet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) Ke A' (240 * A' + τ') := by
    intro ξ
    refine ⟨⟨inv_nonneg.mpr hK0.le, inv_le_one_of_one_le₀ hK⟩, ⟨hKe' _, ?_⟩, ?_⟩
    · rw [mem_closedBall, dist_zero_right]; exact (hAf _).trans hAA'
    · rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by positivity)]
      intro μ
      have h1 := resc_recon_bound u hK hAl' (p := 1) (m := 3) (by norm_num) ξ
      have h2 := (iteratedFDeriv ℝ 1 Yt ξ).le_opNorm (fun _ => evec μ)
      rw [iteratedFDeriv_one_apply] at h2
      simp only [norm_evec, Finset.prod_const_one, mul_one] at h2
      refine le_trans h2 (h1.trans ?_)
      rw [pow_one]; linarith
  have hch : ∀ ξ, ((K⁻¹, jet1 Yt ξ) : ℝ × FJ) ∈ chartU := fun ξ =>
    jetSet_subset hdet _ _ (hmem ξ)
  have hE : ContDiff ℝ ∞ (eulerOp (Gd D) K⁻¹ Yt) :=
    ContEulerBounds.contDiff_eulerOp (contDiffOn_Gd D) hYt hch
  have hfun : Rfull D Y = fun x => (K ^ 2 : ℝ) • eulerOp (Gd D) K⁻¹ Yt (K • x) := by
    funext x; exact Rfull_scale D hK0.ne' Y hch x
  refine ⟨?_, fun x => ?_⟩
  · rw [hfun]; exact (contDiff_const (c := (K ^ 2 : ℝ))).smul (hE.comp (contDiff_const_smul K))
  -- `‖D(K² E(K·))‖ ≤ K³ ‖DE‖`
  have hsc : ContDiff ℝ ∞ (fun ξ => (K ^ 2 : ℝ) • eulerOp (Gd D) K⁻¹ Yt ξ) := (contDiff_const (c := (K ^ 2 : ℝ))).smul hE
  have h1 := norm_iteratedFDeriv_comp_smul_le hsc K 1 x
  have h2 : ‖iteratedFDeriv ℝ 1 (fun ξ => (K ^ 2 : ℝ) • eulerOp (Gd D) K⁻¹ Yt ξ) (K • x)‖ ≤
      K ^ 2 * ‖iteratedFDeriv ℝ 1 (eulerOp (Gd D) K⁻¹ Yt) (K • x)‖ := by
    rw [iteratedFDeriv_const_smul_apply' ((hE.of_le (ContEulerBounds.natCast_le_infty 1)).contDiffAt),
      norm_smul, Real.norm_of_nonneg (by positivity)]
  have h3 := ContEulerBounds.norm_iteratedFDeriv_eulerOp_le (n := 1) isOpen_chartU
    ((contDiffOn_Gd D).of_le (ContEulerBounds.natCast_le_infty _))
    (hYt.of_le (ContEulerBounds.natCast_le_infty _)) hch (z := K • x)
    (fun k hk => hbU _ (Metric.self_subset_cthickening _ (hmem _)) k (by omega) |>.1) hB1
    (fun p hp1 hp2 => by
      have := jet1_resc_full_bound u hK hAl' (p := p) (m := 3) (by omega) (K • x)
      refine this.trans ?_
      have h240 : (240 : ℝ) ^ (p + 1) ≤ 240 ^ 3 := pow_le_pow_right₀ (by norm_num) (by omega)
      have : 5 * 240 ^ (p + 1) * A' ≤ 5 * 240 ^ 3 * (A' + 1) := by nlinarith
      have : 5 * tau n K 3 u ≤ 5 * τ' := by linarith
      rw [hBdef]; linarith)
  rw [← norm_iteratedFDeriv_one, hfun]
  calc ‖iteratedFDeriv ℝ 1 (fun x => (K ^ 2 : ℝ) • eulerOp (Gd D) K⁻¹ Yt (K • x)) x‖
      ≤ |K| ^ 1 * ‖iteratedFDeriv ℝ 1 (fun ξ => (K ^ 2 : ℝ) • eulerOp (Gd D) K⁻¹ Yt ξ) (K • x)‖ := h1
    _ ≤ K * (K ^ 2 * (ContEulerBounds.cE 1 * M * B ^ (1 + 1))) := by
        rw [abs_of_pos hK0, pow_one]
        gcongr
        exact h2.trans (by gcongr)
    _ = ContEulerBounds.cE 1 * M * B ^ 2 * K ^ 3 := by ring

end Native

/-! ### `eq:native-zero-source` -/

section ZeroSource

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)
variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]

local notation "FF" => Field 𝔄 𝓗 𝓢

/-- The `L²(Q)` norm of a row map bounded pointwise by a continuum covector field, through the
lintegral over the half-open slab. -/
theorem sobX_zero_le_of_lintegral {W W' : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup W'] {G : R4 → W} (hG : Continuous G) {f : R4 → W'}
    (hGf : ∀ z, ‖G z‖ ≤ ‖f z‖) (t₀ t₁ : ℝ) {X c e : ℝ} (hc : 0 ≤ c) (he : 0 ≤ e)
    (hX : ∫⁻ y in slabIco t₀ t₁, ‖f y‖ₑ ^ 2 ≤ ENNReal.ofReal X) (hX0 : 0 ≤ X)
    (hXc : X ≤ c ^ 2 * e ^ 2) :
    sobX 0 (NativeSlab.slab t₀ t₁) G ≤ c * e := by
  have hcG : Continuous fun z => ‖G z‖ ^ 2 := hG.norm.pow 2
  have e1 : sobXSq 0 (NativeSlab.slab t₀ t₁) G = ∫ z in NativeSlab.slab t₀ t₁, ‖G z‖ ^ 2 := by
    unfold sobXSq
    simp [NativeSlab.norm_dX_zero]
  have h1 : ENNReal.ofReal (sobXSq 0 (NativeSlab.slab t₀ t₁) G) ≤ ENNReal.ofReal X := by
    rw [e1, ofReal_integral_eq_lintegral_ofReal (NativeSlab.integrableOn_slab hcG t₀ t₁)
      (Eventually.of_forall fun _ => sq_nonneg _), setLIntegral_congr (slab_ae_eq_slabIco t₀ t₁)]
    refine le_trans (lintegral_mono fun z => ?_) hX
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hGf z) 2)
  have h2 := (ENNReal.ofReal_le_ofReal_iff hX0).mp h1
  unfold sobX
  calc Real.sqrt (sobXSq 0 (NativeSlab.slab t₀ t₁) G) ≤ Real.sqrt (c ^ 2 * e ^ 2) :=
        Real.sqrt_le_sqrt (h2.trans hXc)
    _ = c * e := by rw [← mul_pow, Real.sqrt_sq (by positivity)]

open Classical in
-- the assembly carries many inequalities between real and extended-real quantities
set_option maxHeartbeats 1000000 in
/-- **`eq:native-zero-source`** (`thm:native-source`, first display).  For a compact coframe chart
`K_e ⊂ {det e > 0}`, an amplitude bound `A` and buffered slabs `Q = [t₀,t₁] × 𝕋³ ⋐
Q' = [t₀-δ, t₁+δ) × 𝕋³` inside one period (`δ < t₀`, `t₁ + δ ≤ 2π`), there are `C`, `c_res > 0` and
`τ_* > 0` such that for every odd `n`, `h = 2π/n`, every record `u_h` whose complete reconstruction
`z_h` and low-frequency head `z_h^lo` lie in the chart with `|·| ≤ A`, every `K ≥ 1` with
`hK ≤ c_res` and `τ_{h,3}(K) ≤ τ_*`, and every `σ ≥ ‖E_h^raw(u_h)‖_{0,h;Q'}`,
`‖𝓡_B(z_h)‖_{L²(Q)} + ‖𝓡_D(z_h)‖_{L²(Q)} ≤ C (σ + hK³) = C ε_{0,h}`. -/
theorem native_zero_source {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det)
    (A : ℝ) {t₀ t₁ δ : ℝ} (hδ : 0 < δ) (h0 : δ < t₀) (h1 : t₁ + δ ≤ 2 * π) :
    ∃ C c_res τs : ℝ, 0 ≤ C ∧ 0 < c_res ∧ 0 < τs ∧ ∀ (n : ℕ) [NeZero n], Odd n →
      ∀ (u : Grid n → FF) (K σ : ℝ), 1 ≤ K → (2 * π / n) * K ≤ c_res → tau n K 3 u ≤ τs →
      (∀ x, (reconLow n K u x).1 ∈ Ke) → (∀ x, ‖reconLow n K u x‖ ≤ A) →
      (∀ x, (recon n u x).1 ∈ Ke) → (∀ x, ‖recon n u x‖ ≤ A) → 0 ≤ σ →
      (2 * π / n) ^ 4 * ∑ x ∈ Finset.univ.filter
          (fun x : Grid n => pos (2 * π / n) x ∈ bufSlab (t₀ - δ) (t₁ + δ)),
          ‖eulerRow (localAction D (2 * π / n)) (2 * π / n) u x‖ ^ 2 ≤ σ ^ 2 →
      sobX 0 (NativeSlab.slab t₀ t₁) (RB D (recon n u)) +
          sobX 0 (NativeSlab.slab t₀ t₁) (RD D (recon n u)) ≤
        C * NativeRate.eps0 σ (2 * π / n) K := by
  set Bc : ℝ := 240 ^ 3 * (A + 1) + 1 with hBc
  obtain ⟨C₀, c₀, hc₀, hcons⟩ := native_consistency D hKe hdet A Bc
  obtain ⟨CE, hCE, hderiv⟩ := exists_fderiv_Rfull_bound D hKe hdet A 1
  set V : ℝ := (MeasureTheory.volume (bufSlab (t₀ - δ) (t₁ + δ))).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  set C₁ : ℝ := Real.sqrt (4 + 4 * (2 * π) ^ 4 * C₀ ^ 2 + 2 * V * CE ^ 2) with hC₁
  refine ⟨2 * C₁, min c₀ δ, 1, by positivity, lt_min hc₀ hδ, one_pos, ?_⟩
  intro n _ hn u K σ hK hhK hτ hKel hAl hKef hAf hσ hσb
  set h : ℝ := 2 * π / n with hhdef
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hh0 : 0 < h := by rw [hhdef]; positivity
  have hnh : (n : ℝ) * h = 2 * π := by rw [hhdef]; field_simp
  have hK0 : 0 < K := by linarith
  have hhδ : h ≤ δ := by
    have : h ≤ h * K := le_mul_of_one_le_right hh0.le hK
    linarith [min_le_right c₀ δ]
  have hhc : h * K ≤ c₀ := hhK.trans (min_le_left _ _)
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hAl 0)
  set Y := recon n u with hYdef
  -- the derivative reserve of the complete field
  have hD : ∀ j, j ≤ 3 → 1 ≤ j → ∀ z, ‖iteratedFDeriv ℝ j Y z‖ ≤ Bc * K ^ j := by
    intro j hj _ z
    refine (norm_iteratedFDeriv_recon_le u hK hAl hj z).trans ?_
    have : 240 ^ 3 * A + tau n K 3 u ≤ Bc := by rw [hBc]; nlinarith
    exact mul_le_mul_of_nonneg_right this (by positivity)
  obtain ⟨-, -, hnode⟩ := hcons K hK h hh0 hhc n Y ((contDiff_recon u).of_le (ContEulerBounds.natCast_le_infty 3))
    (isPeriodic_recon u) hKef hAf (fun z => by rw [← pow_one K]; exact hD 1 (by norm_num) le_rfl z)
    (hD 2 (by norm_num) (by norm_num)) (hD 3 le_rfl (by norm_num))
  rw [hYdef, samp_recon hn u] at hnode
  obtain ⟨hRsm, hRd⟩ := hderiv n u K hK hτ hAl hKef hAf
  -- nodal transfer
  set Q' := bufSlab (t₀ - δ) (t₁ + δ)
  have hbuf := fun k hk => cell_subset_bufSlab (t₀ := t₀) (t₁ := t₁) hhdef hhδ k hk
  have hRdiff : ∀ y ∈ Q', HasFDerivWithinAt (Rfull D Y) (fderiv ℝ (Rfull D Y) y) Q' y :=
    fun y _ => ((hRsm.differentiable (by simp)) y).hasFDerivAt.hasFDerivWithinAt
  have hnod := NodalSourceTransfer.lintegral_sq_le_nodalMassSq (d := 4) hh0 hbuf hRdiff
    (L := CE * K ^ 3) (fun y _ => hRd y)
  have hmass := nodalMassSq_le_grid hhdef (a := t₀ - δ) (b := t₁ + δ) (by linarith) h1 (Rfull D Y)
  -- the grid sum
  set S := Finset.univ.filter (fun x : Grid n => pos h x ∈ Q')
  have hpt : ∀ x : Grid n, ‖Rfull D Y (pos h x)‖ ^ 2 ≤
      2 * ‖eulerRow (localAction D h) h u x‖ ^ 2 + 2 * (C₀ * h * K ^ 3) ^ 2 := by
    intro x
    have h1x := hnode x
    have : ‖Rfull D Y (pos h x)‖ ≤ ‖eulerRow (localAction D h) h u x‖ + C₀ * h * K ^ 3 := by
      have e : Rfull D Y (pos h x) = eulerRow (localAction D h) h u x -
          (eulerRow (localAction D h) h u x - Rfull D Y (pos h x)) := by abel
      rw [e]
      refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
      exact h1x
    have h0' : 0 ≤ ‖Rfull D Y (pos h x)‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖eulerRow (localAction D h) h u x‖ - C₀ * h * K ^ 3)]
  have hcard : h ^ 4 * (S.card : ℝ) ≤ (2 * π) ^ 4 := by
    have : (S.card : ℝ) ≤ (n : ℝ) ^ 4 := by
      have h1c : S.card ≤ Fintype.card (Grid n) := Finset.card_le_univ S
      have h2c : Fintype.card (Grid n) = n ^ 4 := by simp [ShiftedJetAction.Grid]
      exact_mod_cast h2c ▸ h1c
    calc h ^ 4 * (S.card : ℝ) ≤ h ^ 4 * (n : ℝ) ^ 4 := by gcongr
      _ = (2 * π) ^ 4 := by rw [← mul_pow, mul_comm, hnh]
  have hgrid : h ^ 4 * ∑ x ∈ S, ‖Rfull D Y (pos h x)‖ ^ 2 ≤
      2 * σ ^ 2 + 2 * (2 * π) ^ 4 * (C₀ * h * K ^ 3) ^ 2 := by
    calc h ^ 4 * ∑ x ∈ S, ‖Rfull D Y (pos h x)‖ ^ 2
        ≤ h ^ 4 * ∑ x ∈ S, (2 * ‖eulerRow (localAction D h) h u x‖ ^ 2 +
            2 * (C₀ * h * K ^ 3) ^ 2) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => hpt x) (by positivity)
      _ = 2 * (h ^ 4 * ∑ x ∈ S, ‖eulerRow (localAction D h) h u x‖ ^ 2) +
            2 * (h ^ 4 * (S.card : ℝ)) * (C₀ * h * K ^ 3) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]; ring
      _ ≤ 2 * σ ^ 2 + 2 * (2 * π) ^ 4 * (C₀ * h * K ^ 3) ^ 2 := by
          have : 0 ≤ (C₀ * h * K ^ 3) ^ 2 := sq_nonneg _
          gcongr
  -- the `L²(Q)` bound for the complete covector
  have hX : ∫⁻ y in slabIco t₀ t₁, ‖Rfull D Y y‖ₑ ^ 2 ≤
      ENNReal.ofReal (4 * σ ^ 2 + 4 * (2 * π) ^ 4 * (C₀ * h * K ^ 3) ^ 2 +
        2 * V * (h * (CE * K ^ 3)) ^ 2) := by
    refine hnod.trans ?_
    have hVe : MeasureTheory.volume Q' = ENNReal.ofReal V := by
      rw [hV, ENNReal.ofReal_toReal (volume_bufSlab_ne_top _ _)]
    rw [hVe]
    calc 2 * NodalSourceTransfer.nodalMassSq h Q' (Rfull D Y) +
          2 * ENNReal.ofReal V * ENNReal.ofReal (h * (CE * K ^ 3)) ^ 2
        ≤ 2 * ENNReal.ofReal (h ^ 4 * ∑ x ∈ S, ‖Rfull D Y (pos h x)‖ ^ 2) +
          2 * ENNReal.ofReal V * ENNReal.ofReal (h * (CE * K ^ 3)) ^ 2 := by gcongr
      _ ≤ 2 * ENNReal.ofReal (2 * σ ^ 2 + 2 * (2 * π) ^ 4 * (C₀ * h * K ^ 3) ^ 2) +
          2 * ENNReal.ofReal V * ENNReal.ofReal (h * (CE * K ^ 3)) ^ 2 := by
          gcongr
      _ = ENNReal.ofReal (4 * σ ^ 2 + 4 * (2 * π) ^ 4 * (C₀ * h * K ^ 3) ^ 2 +
            2 * V * (h * (CE * K ^ 3)) ^ 2) := by
          rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_ofNat 2,
            ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
              (by positivity)]
          congr 1; ring
  -- each row
  have hbound : 4 * σ ^ 2 + 4 * (2 * π) ^ 4 * (C₀ * h * K ^ 3) ^ 2 +
      2 * V * (h * (CE * K ^ 3)) ^ 2 ≤ C₁ ^ 2 * NativeRate.eps0 σ h K ^ 2 := by
    rw [hC₁, Real.sq_sqrt (by positivity)]
    have hs : σ ^ 2 ≤ NativeRate.eps0 σ h K ^ 2 := by
      unfold NativeRate.eps0
      have : 0 ≤ h * K ^ 3 := by positivity
      nlinarith
    have hk : (h * K ^ 3) ^ 2 ≤ NativeRate.eps0 σ h K ^ 2 := by
      unfold NativeRate.eps0
      have : 0 ≤ h * K ^ 3 := by positivity
      nlinarith
    have e1 : (C₀ * h * K ^ 3) ^ 2 = C₀ ^ 2 * (h * K ^ 3) ^ 2 := by ring
    have e2 : (h * (CE * K ^ 3)) ^ 2 = CE ^ 2 * (h * K ^ 3) ^ 2 := by ring
    rw [e1, e2]
    have : 0 ≤ (2 * π) ^ 4 * C₀ ^ 2 := by positivity
    have : 0 ≤ V * CE ^ 2 := by positivity
    nlinarith
  have he0 : 0 ≤ NativeRate.eps0 σ h K := by unfold NativeRate.eps0; positivity
  have hC₁0 : 0 ≤ C₁ := Real.sqrt_nonneg _
  have hRBc : Continuous (RB D Y) :=
    ((ContEulerBounds.preL (ιB (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢))).continuous.comp hRsm.continuous)
  have hRDc : Continuous (RD D Y) :=
    ((ContEulerBounds.preL (ιS (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢))).continuous.comp hRsm.continuous)
  have hB := sobX_zero_le_of_lintegral hRBc (f := Rfull D Y)
    (fun z => norm_comp_ιB_le (Rfull D Y z)) t₀ t₁ hC₁0 he0 hX (by positivity) hbound
  have hDr := sobX_zero_le_of_lintegral hRDc (f := Rfull D Y)
    (fun z => norm_comp_ιS_le (Rfull D Y z)) t₀ t₁ hC₁0 he0 hX (by positivity) hbound
  linarith

end ZeroSource

end

end RenewalGeometry.NativeZeroSource
