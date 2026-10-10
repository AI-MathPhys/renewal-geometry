/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeSourceComparison
import RenewalGeometry.Continuum.NativeSourceCompareBudget
import RenewalGeometry.Continuum.NativeSourceTheorem
import RenewalGeometry.Continuum.NativeSourcePhys

/-!
# The source-budget comparison for the actual tuple of a native record

Einstein–Standard-Model action-closure manuscript, `thm:native-closure` (the source estimate
`𝒴_k(z_h) ≤ C F_{h,k}` for the actual field tuple of the native record, feeding
`prop:coupled-bootstrap`).

For a native grid record `u` (odd `n`, nodal gauges) the trigonometric reconstruction
`z_h = recon n u` dilated to unit spatial period (`dilField t₀`, `ξ = 2πx + t₀e₀`) is an actual
field tuple (`RecordTuple.toTuple`), whose slab residuals are `bosF = MB(2πe(ξ))((2π)⁴𝓡_B∘Φ⁻¹)`,
`dirF = (2π)⁴MD(2πe(ξ))𝓡_D(ξ)` (`bosF_dil`, `dirF_dil`).  The comparison combines

* Leibniz and Faà di Bruno (`sobXSq_clm_apply_le`, `exists_comp_bound`) with the record derivative
  bounds `‖D^i e‖ ≤ (BK)^i` (`norm_iteratedFDeriv_clm_recon_le`);
* `thm:native-source` for the physical rows (`NativeSourceThm.native_source_phys` with the
  projection `πg` onto the gauge Lie algebra: gauge rows in `𝔤` only, both in the budget `σ` and in
  the residual `𝓡_B^𝔤`) at every order `1 ≤ k' ≤ k`, its zero-order clause, and the budget
  monotonicity `K^lF_{h,k-l} ≤ F_{h,k}`, `K^lε_{0,h} ≤ F_{h,k}`;
* the interpolation `‖·‖²_{H¹} ≤ ‖·‖² + c‖·‖‖·‖_{H²}` for the Dirac term of order `k`;
* the dilation identity between `L²_tH^k_x` on the unit-period slab and on `[t₀, t₁] × 𝕋³_{2π}`.

## Main results

* `sqrt_l2Sq_dil_le` — generic: `‖a·b‖_{L²H^N}` of a dilated product with `‖D^l_x a‖ ≤ ΛK^l` and
  `K^l‖b‖_{H^{N-l}} ≤ E` is `≤ C Λ E`.
* **`native_source_tuple`** — the source estimate for the actual tuple:
  `resB(z_h) + resD(z_h) ≤ C₁ F_{h,k}` (`F_{h,k} = forcingBudget`) under exactly the hypotheses of
  `thm:native-source` (finite-action budget of the physical rows, `σ ≥ ‖E_h^raw ∘ physF πg‖`).
-/

open MeasureTheory Set Filter Topology Finset
open scoped Real ContDiff Nat

namespace RenewalGeometry.SourceCompare

open DiscreteEulerConsistency (R4)
open NativeTail (dX sobXSq sobX spatialL)

noncomputable section

set_option linter.unusedSectionVars false

/-! ### Generic: dilated products -/

theorem sum_coef_sq_le {N : ℕ} {Λ K E : ℝ} (hK : 0 ≤ K) {s : ℕ → ℝ} (hs : ∀ l, 0 ≤ s l)
    (hE : ∀ l ≤ N, K ^ l * Real.sqrt (s l) ≤ E) :
    ∑ l ∈ range (N + 1), (Λ * K ^ l) ^ 2 * s l ≤ (N + 1) * (Λ ^ 2 * E ^ 2) := by
  have hterm : ∀ l ∈ range (N + 1), (Λ * K ^ l) ^ 2 * s l ≤ Λ ^ 2 * E ^ 2 := by
    intro l hl
    have hl' : l ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
    have h0 : 0 ≤ K ^ l * Real.sqrt (s l) := by positivity
    have h1 : (K ^ l * Real.sqrt (s l)) ^ 2 ≤ E ^ 2 := pow_le_pow_left₀ h0 (hE l hl') 2
    have e : (Λ * K ^ l) ^ 2 * s l = Λ ^ 2 * (K ^ l * Real.sqrt (s l)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (hs l)]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  calc ∑ l ∈ range (N + 1), (Λ * K ^ l) ^ 2 * s l ≤ ∑ l ∈ range (N + 1), Λ ^ 2 * E ^ 2 :=
        Finset.sum_le_sum hterm
    _ = (N + 1) * (Λ ^ 2 * E ^ 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

/-- The constant of `sqrt_l2Sq_dil_le`. -/
def dilConst (N : ℕ) (card : ℕ) : ℝ :=
  Real.sqrt (nWords N * (2 * π) ^ (2 * N) / (2 * π) ^ 4 * card * ((N + 1) ^ 2 * 4 ^ N) * (N + 1))

theorem dilConst_nonneg (N card : ℕ) : 0 ≤ dilConst N card := Real.sqrt_nonneg _

/-- **The `L²_tH^N_x` norm of a dilated product with record-type coefficient bounds.** -/
theorem sqrt_l2Sq_dil_le {ι W : Type*} [Fintype ι] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {a : ι → R4 → W →L[ℝ] ℝ} (ha : ∀ i, ContDiff ℝ ∞ (a i)) {b : R4 → W}
    (hb : ContDiff ℝ ∞ b) (N : ℕ) {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁) {Λ K E : ℝ} (hΛ : 0 ≤ Λ)
    (hK : 0 ≤ K)
    (hA : ∀ i, ∀ z ∈ NativeSlab.slab t₀ t₁, ∀ l ≤ N, ‖dX l (a i) z‖ ≤ Λ * K ^ l)
    (hE : ∀ l ≤ N, K ^ l * sobX (N - l) (NativeSlab.slab t₀ t₁) b ≤ E) :
    Real.sqrt (CoupledBootstrap.l2Sq N ((t₁ - t₀) / (2 * π))
        (fun i x => a i ((2 * π) • x + Pi.single 0 t₀) (b ((2 * π) • x + Pi.single 0 t₀)))) ≤
      dilConst N (Fintype.card ι) * (Λ * E) := by
  have hE0 : 0 ≤ E := le_trans (by
    have := Real.sqrt_nonneg (sobXSq (N - 0) (NativeSlab.slab t₀ t₁) b)
    rw [pow_zero, one_mul]
    simp [sobX]) (hE 0 (Nat.zero_le _))
  set c : ℝ := nWords N * (2 * π) ^ (2 * N) / (2 * π) ^ 4 with hc
  have hc0 : 0 ≤ c := by
    have : (0 : ℝ) ≤ nWords N := Nat.cast_nonneg _
    positivity
  have h1 := l2Sq_dil_le (G := fun i ξ => a i ξ (b ξ)) (fun i => (ha i).clm_apply hb) N h01
  have h2 : ∀ i, sobXSq N (NativeSlab.slab t₀ t₁) (fun ξ => a i ξ (b ξ)) ≤
      ((N + 1) ^ 2 * 4 ^ N : ℝ) * ((N + 1) * (Λ ^ 2 * E ^ 2)) := by
    intro i
    refine (sobXSq_clm_apply_le (ha i) hb N t₀ t₁ (A := fun l => Λ * K ^ l)
      (fun l => by positivity) (hA i)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact sum_coef_sq_le hK (fun l => NativeSlab.sobXSq_nonneg _ _ _) hE
  have h3 : CoupledBootstrap.l2Sq N ((t₁ - t₀) / (2 * π))
      (fun i x => a i ((2 * π) • x + Pi.single 0 t₀) (b ((2 * π) • x + Pi.single 0 t₀))) ≤
      (c * Fintype.card ι * ((N + 1) ^ 2 * 4 ^ N) * (N + 1)) * (Λ * E) ^ 2 := by
    refine h1.trans ?_
    calc c * ∑ i, sobXSq N (NativeSlab.slab t₀ t₁) (fun ξ => a i ξ (b ξ))
        ≤ c * ∑ _i : ι, ((N + 1) ^ 2 * 4 ^ N : ℝ) * ((N + 1) * (Λ ^ 2 * E ^ 2)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => h2 i) hc0
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  refine (Real.sqrt_le_sqrt h3).trans (le_of_eq ?_)
  rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (mul_nonneg hΛ hE0)]
  rfl

/-! ### The order bookkeeping (real-number lemmas) -/

/-- Bosonic orders: from `s_0 ≤ Cε₀`, `s_{j+1} ≤ C F_{j+1}` (`j < k`), `K^lF_{j+1} ≤ F` for
`j + 1 + l = k` and `K^lε₀ ≤ F`, every `K^l s_{k-l} ≤ C F` (`l ≤ k`). -/
theorem bos_orders {k : ℕ} {K Cs F e0 : ℝ} {sB : ℕ → ℝ} {Fj : ℕ → ℝ} (hK : 1 ≤ K)
    (hCs : 0 ≤ Cs) (h0 : sB 0 ≤ Cs * e0) (hj : ∀ j < k, sB (j + 1) ≤ Cs * Fj j)
    (hFj : ∀ j < k, ∀ l, j + 1 + l = k → K ^ l * Fj j ≤ F)
    (he0 : ∀ l ≤ k + 1, K ^ l * e0 ≤ F) :
    ∀ l ≤ k, K ^ l * sB (k - l) ≤ Cs * F := by
  intro l hl
  have hKl : 0 ≤ K ^ l := pow_nonneg (by linarith) l
  rcases Nat.lt_or_ge l k with hlk | hlk
  · obtain ⟨j, hj'⟩ : ∃ j, k - l = j + 1 := ⟨k - l - 1, by omega⟩
    have hjk : j < k := by omega
    rw [hj']
    calc K ^ l * sB (j + 1) ≤ K ^ l * (Cs * Fj j) := mul_le_mul_of_nonneg_left (hj j hjk) hKl
      _ = Cs * (K ^ l * Fj j) := by ring
      _ ≤ Cs * F := mul_le_mul_of_nonneg_left (hFj j hjk l (by omega)) hCs
  · have hl' : l = k := le_antisymm hl hlk
    subst hl'
    rw [Nat.sub_self]
    calc K ^ l * sB 0 ≤ K ^ l * (Cs * e0) := mul_le_mul_of_nonneg_left h0 hKl
      _ = Cs * (K ^ l * e0) := by ring
      _ ≤ Cs * F := mul_le_mul_of_nonneg_left (he0 l (by omega)) hCs

/-- Dirac orders: as `bos_orders` one order higher, with the interpolation
`s_1² ≤ s_0² + c s_0 s_2` for the order `k` term. -/
theorem dir_orders {k : ℕ} (hk : 1 ≤ k) {K Cs F e0 c9 : ℝ} {sD : ℕ → ℝ} {Fj : ℕ → ℝ}
    (hK : 1 ≤ K) (hCs : 0 ≤ Cs) (hF : 0 ≤ F) (hc9 : 0 ≤ c9) (hs : ∀ l, 0 ≤ sD l)
    (h0 : sD 0 ≤ Cs * e0) (hj : ∀ j < k, sD (j + 2) ≤ Cs * Fj j)
    (hFj : ∀ j < k, ∀ l, j + 1 + l = k → K ^ l * Fj j ≤ F)
    (he0 : ∀ l ≤ k + 1, K ^ l * e0 ≤ F)
    (hint : sD 1 ^ 2 ≤ sD 0 ^ 2 + c9 * sD 0 * sD 2) :
    ∀ l ≤ k + 1, K ^ l * sD (k + 1 - l) ≤ Real.sqrt (1 + c9) * Cs * F := by
  have hK0 : 0 ≤ K := by linarith
  have hsq : 1 ≤ Real.sqrt (1 + c9) := by
    have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + c9 by linarith)
    rwa [Real.sqrt_one] at this
  have hCF : 0 ≤ Cs * F := mul_nonneg hCs hF
  have hup : Cs * F ≤ Real.sqrt (1 + c9) * Cs * F := by
    rw [mul_assoc]; exact le_mul_of_one_le_left hCF hsq
  -- the zero-order term at every power `≤ k + 1`
  have hz : ∀ l ≤ k + 1, K ^ l * sD 0 ≤ Cs * F := fun l hl =>
    calc K ^ l * sD 0 ≤ K ^ l * (Cs * e0) := mul_le_mul_of_nonneg_left h0 (pow_nonneg hK0 l)
      _ = Cs * (K ^ l * e0) := by ring
      _ ≤ Cs * F := mul_le_mul_of_nonneg_left (he0 l hl) hCs
  intro l hl
  have hKl : 0 ≤ K ^ l := pow_nonneg hK0 l
  rcases Nat.lt_or_ge l k with hlk | hlk
  · obtain ⟨j, hj'⟩ : ∃ j, k + 1 - l = j + 2 := ⟨k - 1 - l, by omega⟩
    have hjk : j < k := by omega
    rw [hj']
    calc K ^ l * sD (j + 2) ≤ K ^ l * (Cs * Fj j) := mul_le_mul_of_nonneg_left (hj j hjk) hKl
      _ = Cs * (K ^ l * Fj j) := by ring
      _ ≤ Cs * F := mul_le_mul_of_nonneg_left (hFj j hjk l (by omega)) hCs
      _ ≤ _ := hup
  · rcases Nat.lt_or_ge l (k + 1) with hlk' | hlk'
    · -- `l = k`: interpolation
      have hlk2 : l = k := by omega
      subst hlk2
      rw [show l + 1 - l = 1 by omega]
      have hA : K ^ (l + 1) * sD 0 ≤ Cs * F := hz (l + 1) le_rfl
      have hB : K ^ (l - 1) * sD 2 ≤ Cs * F := by
        calc K ^ (l - 1) * sD 2 = K ^ (l - 1) * sD (0 + 2) := rfl
          _ ≤ K ^ (l - 1) * (Cs * Fj 0) :=
              mul_le_mul_of_nonneg_left (hj 0 (by omega)) (pow_nonneg hK0 _)
          _ = Cs * (K ^ (l - 1) * Fj 0) := by ring
          _ ≤ Cs * F := mul_le_mul_of_nonneg_left (hFj 0 (by omega) (l - 1) (by omega)) hCs
      have hC : K ^ l * sD 0 ≤ Cs * F := hz l (by omega)
      have hpow : K ^ l * K ^ l = K ^ (l + 1) * K ^ (l - 1) := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      have h2 : (K ^ l * sD 1) ^ 2 ≤ (Real.sqrt (1 + c9) * Cs * F) ^ 2 := by
        have e1 : (Real.sqrt (1 + c9) * Cs * F) ^ 2 = (1 + c9) * (Cs * F) ^ 2 := by
          rw [mul_assoc, mul_pow, Real.sq_sqrt (by linarith)]
        rw [e1]
        calc (K ^ l * sD 1) ^ 2 = (K ^ l) ^ 2 * sD 1 ^ 2 := by ring
          _ ≤ (K ^ l) ^ 2 * (sD 0 ^ 2 + c9 * sD 0 * sD 2) :=
              mul_le_mul_of_nonneg_left hint (sq_nonneg _)
          _ = (K ^ l * sD 0) ^ 2 + c9 * ((K ^ (l + 1) * sD 0) * (K ^ (l - 1) * sD 2)) := by
              have : (K ^ l) ^ 2 * (c9 * sD 0 * sD 2) =
                  c9 * ((K ^ l * K ^ l) * (sD 0 * sD 2)) := by ring
              rw [mul_add, this, hpow]; ring
          _ ≤ (Cs * F) ^ 2 + c9 * ((Cs * F) * (Cs * F)) := by
              gcongr
              all_goals first
                | assumption
                | exact mul_nonneg hKl (hs 0)
                | exact mul_nonneg (pow_nonneg hK0 _) (hs 0)
                | exact mul_nonneg (pow_nonneg hK0 _) (hs 2)
          _ = (1 + c9) * (Cs * F) ^ 2 := by ring
      exact (pow_le_pow_iff_left₀ (mul_nonneg hKl (hs 1))
        (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hCs) hF) two_ne_zero).1 h2
    · have hl' : l = k + 1 := le_antisymm hl hlk'
      subst hl'
      rw [Nat.sub_self]
      exact (hz (k + 1) le_rfl).trans hup

end

end RenewalGeometry.SourceCompare

namespace RenewalGeometry.RecordTuple

open DiscreteEulerConsistency (R4 jet1 contEuler)
open NativeScaling (Mat eta metric)
open ShiftedJetAction (Grid)
open NativeDensity DiscreteEulerConsistency NativeModel SlabData ActualJetState
  ActualJetCompleteForcing FieldScaling SourceCompare
open ContEulerBounds (NCLM)
open TrigInterp (recon reconLow tau)
open NativeRate (eps0 forcingBudget)
open NativeTail (dX sobX sobXSq RB RD)

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]
variable {m : ℕ} (M : SlabModel 𝔄 𝓗 𝓢 m)

/-- The coframe slot of a native field value. -/
def fstL : NCLM (Field 𝔄 𝓗 𝓢) Mat := ContinuousLinearMap.fst ℝ Mat _

theorem norm_fstL_le : ‖(fstL : NCLM (Field 𝔄 𝓗 𝓢) Mat)‖ ≤ 1 :=
  ContinuousLinearMap.norm_fst_le _ _ _

/-- The bosonic coordinate projections `v ↦ (eY⁻¹v)_i`. -/
def PB {na : ℕ} (eY : (Fin na → ℝ) ≃L[ℝ] BosP m (HSp M)) (i : Fin na) :
    BosP m (HSp M) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (eY.symm : BosP m (HSp M) →L[ℝ] (Fin na → ℝ))

/-- The Dirac coordinate projections `v ↦ (eYD⁻¹v)_i`. -/
def PD {nb : ℕ} (eYD : (Fin nb → ℝ) ≃L[ℝ] 𝓢 × CoSpinor 𝓢) (i : Fin nb) :
    𝓢 × CoSpinor 𝓢 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (eYD.symm : 𝓢 × CoSpinor 𝓢 →L[ℝ] (Fin nb → ℝ))

/-- The interpolation constant of the Dirac rows. -/
def c9D : ℝ :=
  9 * Real.sqrt (PeriodicSobInterp.interpConst (NCLM (Dir 𝓢) ℝ) (Fin 3) 1 2)

theorem c9D_nonneg : 0 ≤ c9D (𝓢 := 𝓢) := by unfold c9D; positivity

/-- **Coefficient bounds along a record**: a smooth function of the coframe (Faà di Bruno
constant `C`) composed with the reconstruction has `‖D^l_x(g∘e)‖ ≤ N! C' max(B,1)^N K^l`,
`B = 240(A + τ + 1)`, for `l ≤ N`. -/
theorem dX_comp_recon_le {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {g : Mat → G}
    {C : ℝ} {N : ℕ} {Ke : Set Mat}
    (hC : ∀ (f : R4 → Mat), ContDiff ℝ ∞ f → (∀ x, f x ∈ Ke) → ∀ (D : ℝ) (x : R4),
      (∀ i, 1 ≤ i → i ≤ N → ‖iteratedFDeriv ℝ i f x‖ ≤ D ^ i) →
      ∀ j ≤ N, ‖iteratedFDeriv ℝ j (g ∘ f) x‖ ≤ j ! * C * D ^ j)
    (hC0 : 0 ≤ C) {n : ℕ} [NeZero n] (u : Grid n → Field 𝔄 𝓗 𝓢) {K A τ : ℝ} (hK : 1 ≤ K)
    (hA : ∀ y, ‖reconLow n K u y‖ ≤ A) (hτ : tau n K (N + 1) u ≤ τ)
    (hKe : ∀ x, (recon n u x).1 ∈ Ke) {Cg : ℝ} (hCg : C ≤ Cg) (z : R4) {l : ℕ} (hl : l ≤ N) :
    ‖dX l (fun ξ => g (recon n u ξ).1) z‖ ≤
      (N ! * Cg * max (240 * (A + τ + 1)) 1 ^ N) * K ^ l := by
  have hK0 : 0 < K := by linarith
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hτ0 : 0 ≤ τ := (TrigInterp.tau_nonneg n hK0 _ u).trans hτ
  set B : ℝ := 240 * (A + τ + 1) with hB
  have hB0 : 0 ≤ B := by positivity
  set f : R4 → Mat := fun ξ => fstL (recon n u ξ) with hf
  have hfs : ContDiff ℝ ∞ f := fstL.contDiff.comp (NativeTail.contDiff_recon u)
  have hD : ∀ i, 1 ≤ i → i ≤ N → ‖iteratedFDeriv ℝ i f z‖ ≤ (B * K) ^ i := fun i hi1 hiN =>
    norm_iteratedFDeriv_clm_recon_le fstL norm_fstL_le u hK hA (j := N + 1) (by omega) hτ hi1 z
  have h1 := hC f hfs hKe (B * K) z hD l hl
  have h2 : ‖dX l (fun ξ => g (recon n u ξ).1) z‖ ≤ l ! * C * (B * K) ^ l :=
    (NativeTail.norm_dX_le l _ z).trans h1
  refine h2.trans ?_
  have hf1 : (l ! : ℝ) ≤ N ! := by exact_mod_cast Nat.factorial_le hl
  have hBl : B ^ l ≤ max B 1 ^ N :=
    (pow_le_pow_left₀ hB0 (le_max_left _ _) l).trans
      (pow_le_pow_right₀ (le_max_right _ _) hl)
  have hCg0 : 0 ≤ Cg := hC0.trans hCg
  rw [mul_pow]
  calc (l ! : ℝ) * C * (B ^ l * K ^ l) = (l ! * C * B ^ l) * K ^ l := by ring
    _ ≤ (N ! * Cg * max B 1 ^ N) * K ^ l := by
        gcongr

open Classical in
set_option maxHeartbeats 4000000 in
/-- **The source estimate for the actual tuple of a native record** (`thm:native-closure`, the
bound `𝒴_k(z_h) ≤ C F_{h,k}` fed to `prop:coupled-bootstrap`).  Under exactly the hypotheses of
`thm:native-source` for the physical rows (gauge rows in the gauge Lie algebra: finite-action budget
`σ ≥ ‖E_h^raw ∘ physF πg‖`; compact chart `K_e ⊂ {det > 0}`, amplitude `A`, order `k ≥ 1`, buffered slab
`[t₀, t₁] ⊂ (b, 2π - b]`), for every record whose dilated reconstruction satisfies the tuple
hypotheses (`TupleHyp`: adapted Lorentz gauge, temporal gauge, physical co-spinors, chart
margin), the slab residual norms of the actual tuple `z = toTuple` on `[0, (t₁-t₀)/2π] × 𝕋³` obey
`‖bosF(z)‖_{L²H^k} + ‖dirF(z)‖_{L²H^{k+1}} ≤ C₁ F_{h,k}` in the coordinates `eY`, `eYD`. -/
theorem native_source_tuple {δ : ℝ} (hδ : 0 < δ) {na nb : ℕ}
    (eY : (Fin na → ℝ) ≃L[ℝ] BosP m (HSp M)) (eYD : (Fin nb → ℝ) ≃L[ℝ] 𝓢 × CoSpinor 𝓢)
    {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det) (A : ℝ) (k : ℕ)
    (hk : 1 ≤ k) {Ck : ℝ} (hCk : 0 < Ck) {t₀ t₁ b : ℝ} (hb : 0 < b) (h0 : b < t₀)
    (h1 : t₁ + b ≤ 2 * π) (h01 : t₀ ≤ t₁) :
    ∃ C₁ c_res τs : ℝ, 0 ≤ C₁ ∧ 0 < c_res ∧ 0 < τs ∧ ∀ (n : ℕ) [NeZero n], Odd n →
      ∀ (u : Grid n → Field 𝔄 𝓗 𝓢) (K σ : ℝ), 1 ≤ K → (2 * π / n) * K ≤ c_res →
      tau n K (k + 2) u ≤ τs →
      (∀ x, (reconLow n K u x).1 ∈ Ke) → (∀ x, ‖reconLow n K u x‖ ≤ A) →
      (∀ x, (recon n u x).1 ∈ Ke) → (∀ x, ‖recon n u x‖ ≤ A) → 0 ≤ σ →
      (2 * π / n) ^ 4 * ∑ x ∈ Finset.univ.filter
          (fun x : Grid n => pos (2 * π / n) x ∈ NativeZeroSource.bufSlab (t₀ - b) (t₁ + b)),
          ‖(eulerRow (localAction M.toData (2 * π / n)) (2 * π / n) u x).comp
            (NativeTail.physF M.πg)‖ ^ 2 ≤ σ ^ 2 →
      ∀ h : TupleHyp M δ (dilField t₀ (recon n u)),
      Real.sqrt (CoupledBootstrap.l2Sq k ((t₁ - t₀) / (2 * π))
          (CoupledBootstrap.RBc (toSMData M δ) eY (toTuple hδ h))) +
        Real.sqrt (CoupledBootstrap.l2Sq (k + 1) ((t₁ - t₀) / (2 * π))
          (CoupledBootstrap.RDc (toSMData M δ) eYD (toTuple hδ h))) ≤
        C₁ * forcingBudget k Ck σ (2 * π / n) K (tau n K 2 u) (tau n K (k + 2) u) := by
  -- `thm:native-source` at every order `1 ≤ j + 1 ≤ k`
  have hns := fun j : ℕ => NativeSourceThm.native_source_phys M.toData M.πg hKe hdet A (j + 1)
    (by omega) hCk hb h0 h1
  choose Cf cf τf hCf hcf hτf hsrc using hns
  have hne : (range k).Nonempty := ⟨0, Finset.mem_range.2 (by omega)⟩
  set cs := (range k).inf' hne cf with hcs_def
  set τs := (range k).inf' hne τf with hτs_def
  set Cs := ∑ j ∈ range k, Cf j with hCs_def
  have hcs : 0 < cs := (Finset.lt_inf'_iff hne).2 fun j _ => hcf j
  have hτs : 0 < τs := (Finset.lt_inf'_iff hne).2 fun j _ => hτf j
  have hCs0 : 0 ≤ Cs := Finset.sum_nonneg fun j _ => hCf j
  have hCfle : ∀ j < k, Cf j ≤ Cs := fun j hj =>
    Finset.single_le_sum (f := Cf) (fun i _ => hCf i) (Finset.mem_range.2 hj)
  have hcsle : ∀ j < k, cs ≤ cf j := fun j hj => Finset.inf'_le _ (Finset.mem_range.2 hj)
  have hτsle : ∀ j < k, τs ≤ τf j := fun j hj => Finset.inf'_le _ (Finset.mem_range.2 hj)
  -- Faà di Bruno constants of the coordinate coefficients
  have hKU : Ke ⊆ detU := fun e he => (hdet e he).ne'
  have hgB := fun i => exists_comp_bound (E := R4) isOpen_detU (contDiffOn_gB M (PB M eY i)) hKe
    hKU (k + 1)
  have hgD := fun i => exists_comp_bound (E := R4) isOpen_detU (contDiffOn_gD M (PD eYD i)) hKe
    hKU (k + 1)
  choose CB hCB0 hCB using hgB
  choose CD hCD0 hCD using hgD
  set Cg : ℝ := ∑ i, CB i + ∑ i, CD i with hCg_def
  have hCB1 : ∀ i, CB i ≤ Cg := fun i =>
    (Finset.single_le_sum (f := CB) (fun j _ => hCB0 j) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => hCD0 j))
  have hCD1 : ∀ i, CD i ≤ Cg := fun i =>
    (Finset.single_le_sum (f := CD) (fun j _ => hCD0 j) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left (Finset.sum_nonneg fun j _ => hCB0 j))
  have hCg0 : 0 ≤ Cg :=
    add_nonneg (Finset.sum_nonneg fun j _ => hCB0 j) (Finset.sum_nonneg fun j _ => hCD0 j)
  set B : ℝ := 240 * (A + τs + 1) with hB_def
  set Λ0 : ℝ := (k + 1)! * Cg * max B 1 ^ (k + 1) with hΛ0_def
  have hΛ0 : 0 ≤ Λ0 := by
    have : 0 ≤ max B 1 := le_trans zero_le_one (le_max_right _ _)
    positivity
  set c9 : ℝ := c9D (𝓢 := 𝓢) with hc9_def
  have hc9 : 0 ≤ c9 := c9D_nonneg
  set CE : ℝ := Real.sqrt (1 + c9) * Cs with hCE_def
  have hCE : Cs ≤ CE := by
    have h1' := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + c9 by linarith)
    rw [Real.sqrt_one] at h1'
    exact le_mul_of_one_le_left hCs0 h1'
  have hCE0 : 0 ≤ CE := hCs0.trans hCE
  refine ⟨dilConst k na * (Λ0 * CE) + dilConst (k + 1) nb * (Λ0 * CE), cs, τs,
    add_nonneg (mul_nonneg (dilConst_nonneg _ _) (mul_nonneg hΛ0 hCE0))
      (mul_nonneg (dilConst_nonneg _ _) (mul_nonneg hΛ0 hCE0)), hcs, hτs, ?_⟩
  intro n _ hn u K σ hK hhK hτ hKel hAl hKef hAf hσ hσb h
  have hK0 : 0 < K := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hh0 : 0 ≤ 2 * π / n := by positivity
  have hτ2 : 0 ≤ tau n K 2 u := TrigInterp.tau_nonneg n hK0 _ u
  have hτk : 0 ≤ tau n K (k + 2) u := TrigInterp.tau_nonneg n hK0 _ u
  set F := forcingBudget k Ck σ (2 * π / n) K (tau n K 2 u) (tau n K (k + 2) u) with hF_def
  have hF0 : 0 ≤ F := forcingBudget_nonneg k hCk.le hσ hh0 hK hτ2 hτk
  have he0 : 0 ≤ eps0 σ (2 * π / n) K := by unfold NativeRate.eps0; positivity
  -- the per-order sources
  have hsrcj := fun j (hj : j < k) => hsrc j n hn u K σ hK (hhK.trans (hcsle j hj))
    ((TrigInterp.tau_mono n hK0 (show j + 1 + 2 ≤ k + 2 by omega) u).trans
      (hτ.trans (hτsle j hj))) hKel hAl hKef hAf hσ hσb
  set Q := NativeSlab.slab t₀ t₁ with hQ
  set sB : ℕ → ℝ := fun l => sobX l Q (NativeTail.RBP M.toData M.πg (recon n u)) with hsB
  set sD : ℕ → ℝ := fun l => sobX l Q (RD M.toData (recon n u)) with hsD
  have hsB0 : ∀ l, 0 ≤ sB l := fun l => Real.sqrt_nonneg _
  have hsD0 : ∀ l, 0 ≤ sD l := fun l => Real.sqrt_nonneg _
  have hz := (hsrcj 0 (by omega)).1
  have hB0 : sB 0 ≤ Cs * eps0 σ (2 * π / n) K :=
    (le_add_of_nonneg_right (hsD0 0)).trans (hz.trans
      (mul_le_mul_of_nonneg_right (hCfle 0 (by omega)) he0))
  have hD0 : sD 0 ≤ Cs * eps0 σ (2 * π / n) K :=
    (le_add_of_nonneg_left (hsB0 0)).trans (hz.trans
      (mul_le_mul_of_nonneg_right (hCfle 0 (by omega)) he0))
  set Fj : ℕ → ℝ := fun j => forcingBudget (j + 1) Ck σ (2 * π / n) K (tau n K 2 u)
    (tau n K (j + 1 + 2) u) with hFj_def
  have hFjn : ∀ j, 0 ≤ Fj j := fun j => forcingBudget_nonneg _ hCk.le hσ hh0 hK hτ2
    (TrigInterp.tau_nonneg n hK0 _ u)
  have hBj : ∀ j < k, sB (j + 1) ≤ Cs * Fj j := fun j hj =>
    (le_add_of_nonneg_right (hsD0 _)).trans ((hsrcj j hj).2.1.trans
      (mul_le_mul_of_nonneg_right (hCfle j hj) (hFjn j)))
  have hDj : ∀ j < k, sD (j + 2) ≤ Cs * Fj j := fun j hj =>
    (le_add_of_nonneg_left (hsB0 _)).trans ((hsrcj j hj).2.1.trans
      (mul_le_mul_of_nonneg_right (hCfle j hj) (hFjn j)))
  have hFj : ∀ j < k, ∀ l, j + 1 + l = k → K ^ l * Fj j ≤ F := fun j _ l hjl =>
    pow_mul_forcingBudget_le hjl hCk.le hσ hh0 hK hτ2
      (TrigInterp.tau_mono n hK0 (show j + 1 + 2 ≤ k + 2 by omega) u)
  have hE0 : ∀ l ≤ k + 1, K ^ l * eps0 σ (2 * π / n) K ≤ F := fun l hl =>
    pow_mul_eps0_le hl hCk.le hσ hh0 hK hτ2 hτk
  -- smoothness and periodicity of the rows
  have hYf := NativeTail.contDiff_recon u
  have hch := NativeSourceThm.chartU_of_mem (K := K) hdet hKef
  have hRB := NativeTail.contDiff_RBP M.toData M.πg hK0 hYf hch
  have hRD := NativeTail.contDiff_RD M.toData hK0 hYf hch
  have hperD := NativeSourceThm.isPeriodic_RD M.toData (NativeSourceThm.isPeriodic_recon' u)
  have hint : sD 1 ^ 2 ≤ sD 0 ^ 2 + c9 * sD 0 * sD 2 := by
    have hi := sobXSq_one_le hRD (fun z μ => hperD z μ) h01
    simp only [hsD, sobX, Real.sq_sqrt (NativeSlab.sobXSq_nonneg _ _ _)]
    refine hi.trans (le_of_eq ?_)
    simp only [hc9_def, c9D]
    ring
  have hEB := bos_orders hK hCs0 hB0 hBj hFj hE0
  have hED := dir_orders hk hK hCs0 hF0 hc9 hsD0 hD0 hDj hFj hE0 hint
  -- the coefficients
  have hdetY : ∀ z, 0 < (recon n u z).1.det := fun z => hdet _ (hKef z)
  have hfs : ContDiff ℝ ∞ (fun ξ => (recon n u ξ).1) := fstL.contDiff.comp hYf
  have hτ' : tau n K (k + 1 + 1) u ≤ τs := hτ
  -- bosonic part
  have hBos : Real.sqrt (CoupledBootstrap.l2Sq k ((t₁ - t₀) / (2 * π))
      (CoupledBootstrap.RBc (toSMData M δ) eY (toTuple hδ h))) ≤
      dilConst k na * (Λ0 * (CE * F)) := by
    have e : CoupledBootstrap.RBc (toSMData M δ) eY (toTuple hδ h) = fun i x =>
        gB M (PB M eY i) (recon n u ((2 * π) • x + Pi.single 0 t₀)).1
          (NativeTail.RBP M.toData M.πg (recon n u) ((2 * π) • x + Pi.single 0 t₀)) := by
      funext i x
      exact bosF_dil hδ hdetY h (PB M eY i) x
    rw [e]
    have := sqrt_l2Sq_dil_le (ι := Fin na)
      (a := fun i ξ => gB M (PB M eY i) (recon n u ξ).1)
      (fun i => (contDiffOn_gB M (PB M eY i)).comp_contDiff hfs fun ξ => hKU (hKef ξ)) hRB k
      h01 hΛ0 hK0.le (E := CE * F)
      (fun i z _ l hl => dX_comp_recon_le (hCB i) (hCB0 i) u hK hAl hτ' hKef (hCB1 i) z
        (by omega))
      (fun l hl => (hEB l hl).trans (mul_le_mul_of_nonneg_right hCE hF0))
    rwa [Fintype.card_fin] at this
  -- Dirac part
  have hDir : Real.sqrt (CoupledBootstrap.l2Sq (k + 1) ((t₁ - t₀) / (2 * π))
      (CoupledBootstrap.RDc (toSMData M δ) eYD (toTuple hδ h))) ≤
      dilConst (k + 1) nb * (Λ0 * (CE * F)) := by
    have e : CoupledBootstrap.RDc (toSMData M δ) eYD (toTuple hδ h) = fun i x =>
        gD M (PD eYD i) (recon n u ((2 * π) • x + Pi.single 0 t₀)).1
          (RD M.toData (recon n u) ((2 * π) • x + Pi.single 0 t₀)) := by
      funext i x
      exact dirF_dil hδ hdetY h (PD eYD i) x
    rw [e]
    have := sqrt_l2Sq_dil_le (ι := Fin nb)
      (a := fun i ξ => gD M (PD eYD i) (recon n u ξ).1)
      (fun i => (contDiffOn_gD M (PD eYD i)).comp_contDiff hfs fun ξ => hKU (hKef ξ)) hRD
      (k + 1) h01 hΛ0 hK0.le (E := CE * F)
      (fun i z _ l hl => dX_comp_recon_le (hCD i) (hCD0 i) u hK hAl hτ' hKef (hCD1 i) z hl)
      (fun l hl => by
        have := hED l hl
        rw [hCE_def, mul_assoc] at *
        exact this)
    rwa [Fintype.card_fin] at this
  calc _ ≤ dilConst k na * (Λ0 * (CE * F)) + dilConst (k + 1) nb * (Λ0 * (CE * F)) :=
        add_le_add hBos hDir
    _ = _ := by ring
end

end RenewalGeometry.RecordTuple
