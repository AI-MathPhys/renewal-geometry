/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.GaugeTheory.TransportPlaquetteConsistency
import RenewalGeometry.DiscreteAnalysis.PositiveHiggsEnvelopeExact

/-!
# Consistency of the native Higgs edge packet on smooth bounded families
  (continuum identification of `prop:positive-Higgs-envelope`)

Einstein–Standard-Model action-closure manuscript, `prop:positive-Higgs-envelope`: "On smooth
bounded reconstructed families, the consistency estimate of `prop:mesh-consistency` for `K_h^H`
identifies this criterion with the corresponding local continuum bound for `D_{A_h}H_h`, up to the
already controlled reconstruction error"; proof: "The smooth-family continuum statement follows
from `K_h^H = D_AH + o(1)` in the corresponding local norm and the uniform equivalence of the
positive cell masses."

The Higgs edge packet of the local action is `K^h_μ(x) = h⁻¹(ρ_H(U_μ(x))H(x + he_μ) - H(x))`
with `U_μ(x) = exp(hA_μ(x))` (`eq:native-matter-links`); on the trivialised bundle the represented
link is `exp(h ρ_H(A_μ(x)))`, with `ρ_H(A_μ) : E → End F` (`F` the real Higgs fibre).

* `norm_exp_smul_sub_one_sub_le`: `‖exp(hX) - (1 + hX)‖ ≤ ‖X‖² e^{‖X‖h} h²`.
* `norm_nativeHiggsPacket_sub_le` (**pointwise consistency**): for represented connection
  components bounded by `K` and a Higgs field with `L`-Lipschitz derivative, `‖H‖ ≤ B`,
  `‖dH‖ ≤ D_H`, every component of the native packet satisfies
  `‖K^h_μ(x) - (D_AH)_μ(x)‖ ≤ (K²e^K B + L + K(D_H + L)) h`, `(D_AH)_μ = dH(e_μ) + A_μ H`;
  for transport links the same estimate is
  `TransportPlaquetteConsistency.norm_higgsLink_sub_covDeriv_le`.
* `lpNorm83_nativeHiggsPacket_sub_le`: on any finite family of cells with positions `pos x` and
  masses `m x ≥ 0`, the `L_h^{8/3}` norm of `K_h^H - (D_AH)_h` is at most
  `√|D| C h (Σ_x m_x)^{3/8}`;
* `nativeHiggs_continuum_identification`: for a family of cutoffs `0 < h ≤ 1` with uniformly
  bounded total cell mass (`Σ_x m_h(x) ≤ M`, e.g. `m_h ≤ C_m h⁴` on `O(h⁻⁴)` cells), the
  `L_h^{8/3}` criterion for `K_h^H` and for the sampled `D_AH` differ by `O(h)`, and one is
  uniformly bounded iff the other is (the third clause of
  `PositiveHiggsEnvelope.positive_higgs_envelope` with its consistency hypothesis discharged).
-/

open NormedSpace Set

noncomputable section

namespace RenewalGeometry.HiggsPacketConsistency

open PathOrderedExp TransportPlaquetteConsistency PositiveHiggsEnvelope

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-- First-order expansion of the exponential link: `‖exp(hX) - (1 + hX)‖ ≤ ‖X‖² e^{‖X‖h} h²`. -/
theorem norm_exp_smul_sub_one_sub_le (X : 𝔸) {h : ℝ} (hh : 0 ≤ h) :
    ‖exp (h • X) - (1 + h • X)‖ ≤ ‖X‖ ^ 2 * Real.exp (‖X‖ * h) * h ^ 2 := by
  have hT := isTransport_const_exp (-X) 0 h
  have := norm_transport_sub_linear_le (ω := fun _ => -X) (K := ‖X‖) (m := 0) (Z := -X) hh
    continuousOn_const (fun _ _ => by rw [norm_neg]) (fun _ _ => by simp) hT (by simp)
  simp only [sub_zero, neg_neg, smul_neg, sub_neg_eq_add, zero_mul, add_zero] at this
  exact this

variable {D : Type*} [Fintype D] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [Nontrivial F]

/-- **The native Higgs edge packet** `K^h_μ(x) = h⁻¹(exp(hA_μ(x))H(x + he_μ) - H(x))`
(`eq:native-matter-links`, represented connection components `A_μ : E → End F`). -/
def nativeHiggsPacket (A : D → E → F →L[ℝ] F) (H : E → F) (e : D → E) (h : ℝ) (x : E) :
    D → F :=
  fun μ => h⁻¹ • (exp (h • A μ x) (H (x + h • e μ)) - H x)

/-- The sampled continuum covariant derivative `(D_AH)_μ(x) = dH(x)e_μ + A_μ(x)H(x)`
(`eq:curvature-higgs`). -/
def covHiggsPacket (A : D → E → F →L[ℝ] F) (H : E → F) (H' : E → E →L[ℝ] F) (e : D → E)
    (x : E) : D → F :=
  fun μ => H' x (e μ) + A μ x (H x)

/-- The consistency constant `K²e^K B + L + K(D_H + L)`. -/
def higgsConst (K B L DH : ℝ) : ℝ := K ^ 2 * Real.exp K * B + L + K * (DH + L)

omit [Fintype D] in
/-- **Pointwise consistency of the native Higgs packet** on a smooth bounded family:
`‖K^h_μ(x) - (D_AH)_μ(x)‖ ≤ (K²e^K B + L + K(D_H + L)) h` for `0 < h ≤ 1`. -/
theorem norm_nativeHiggsPacket_sub_le {A : D → E → F →L[ℝ] F} {H : E → F}
    {H' : E → E →L[ℝ] F} {e : D → E} {K B L DH : ℝ} (hK : ∀ μ y, ‖A μ y‖ ≤ K)
    (hH : ∀ y, HasFDerivAt H (H' y) y) (hHL : ∀ y z, ‖H' y - H' z‖ ≤ L * ‖y - z‖) (hL : 0 ≤ L)
    (hB : ∀ y, ‖H y‖ ≤ B) (hDH : ∀ y, ‖H' y‖ ≤ DH) (he : ∀ μ, ‖e μ‖ ≤ 1) (x : E) {h : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (μ : D) :
    ‖nativeHiggsPacket A H e h x μ - covHiggsPacket A H H' e x μ‖ ≤ higgsConst K B L DH * h := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK μ x)
  have hU : ‖exp (h • A μ x) - (1 + h • A μ x)‖ ≤ (K ^ 2 * Real.exp K) * h ^ 2 := by
    refine (norm_exp_smul_sub_one_sub_le (A μ x) hh.le).trans ?_
    have h1 : ‖A μ x‖ ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hK μ x) 2
    have h2 : Real.exp (‖A μ x‖ * h) ≤ Real.exp K :=
      Real.exp_le_exp.2 ((mul_le_mul (hK μ x) hh1 hh.le hK0).trans (by rw [mul_one]))
    have := mul_le_mul h1 h2 (Real.exp_pos _).le (sq_nonneg _)
    nlinarith [sq_nonneg h]
  have hT : ‖H (x + h • e μ) - H x - h • H' x (e μ)‖ ≤ L * h ^ 2 := by
    have := norm_sub_sub_fderiv_le hH hHL x (h • e μ)
    rw [map_smul] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hL)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh, mul_pow]
    nlinarith [norm_nonneg (e μ), pow_le_one₀ (norm_nonneg (e μ)) (he μ) (n := 2)]
  have := norm_covariantForwardDifference_sub_le hh hh1 hU hT (hB _)
  refine this.trans (mul_le_mul_of_nonneg_right ?_ hh.le)
  unfold higgsConst
  have : ‖A μ x‖ * (‖H' x (e μ)‖ + L) ≤ K * (DH + L) := by
    refine mul_le_mul (hK μ x) (add_le_add_left ?_ _) (by positivity) hK0
    exact ((H' x).le_opNorm _).trans ((mul_le_mul (hDH x) (he μ) (norm_nonneg _)
      ((norm_nonneg _).trans (hDH x))).trans (by rw [mul_one]))
  linarith

omit [InnerProductSpace ℝ F] [CompleteSpace F] [Nontrivial F] in
/-- If every component of a packet has norm `≤ ε`, its amplitude is `≤ √|D| ε`. -/
theorem amp_le_of_forall_norm_le {K : D → F} {ε : ℝ} (hε : ∀ μ, ‖K μ‖ ≤ ε) :
    amp K ≤ Real.sqrt (Fintype.card D) * ε := by
  rcases isEmpty_or_nonempty D with hD | ⟨⟨μ₀⟩⟩
  · simp [amp, positiveHiggsAmpSq]
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hε μ₀)
  rw [amp, ← Real.sqrt_sq hε0, ← Real.sqrt_mul (Nat.cast_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  unfold positiveHiggsAmpSq
  calc ∑ μ, ‖K μ‖ ^ 2 ≤ ∑ _μ : D, ε ^ 2 :=
        Finset.sum_le_sum fun μ _ => pow_le_pow_left₀ (norm_nonneg _) (hε μ) 2
    _ = (Fintype.card D : ℝ) * ε ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- `L_h^p` bound from a pointwise bound: `0 ≤ f ≤ ε` gives `‖f‖_{L_h^p} ≤ ε (Σ m)^{1/p}`. -/
theorem lpNorm_le_of_le {C : Type*} [Fintype C] (m : C → ℝ) (hm : ∀ x, 0 ≤ m x) {p : ℝ}
    (hp : 0 < p) (f : C → ℝ) {ε : ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf : ∀ x, f x ≤ ε) (hε : 0 ≤ ε) :
    positiveHiggsLpNorm m p f ≤ ε * (∑ x, m x) ^ (1 / p) := by
  unfold positiveHiggsLpNorm
  have hsum : ∑ x, m x * |f x| ^ p ≤ ε ^ p * ∑ x, m x := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [abs_of_nonneg (hf0 x), mul_comm (ε ^ p)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hf0 x) (hf x) hp.le) (hm x)
  have hS : 0 ≤ ∑ x, m x := Finset.sum_nonneg fun x _ => hm x
  calc (∑ x, m x * |f x| ^ p) ^ (1 / p) ≤ (ε ^ p * ∑ x, m x) ^ (1 / p) :=
        Real.rpow_le_rpow (Finset.sum_nonneg fun x _ =>
          mul_nonneg (hm x) (Real.rpow_nonneg (abs_nonneg _) _)) hsum (by positivity)
    _ = ε * (∑ x, m x) ^ (1 / p) := by
        rw [Real.mul_rpow (Real.rpow_nonneg hε _) hS, ← Real.rpow_mul hε, mul_one_div_cancel hp.ne',
          Real.rpow_one]

omit [CompleteSpace F] [Nontrivial F] in
/-- Nonnegativity of the consistency constant (weighted by `√|D|`). -/
theorem sqrt_card_mul_higgsConst_nonneg {A : D → E → F →L[ℝ] F} {H : E → F}
    {H' : E → E →L[ℝ] F} {K B L DH : ℝ} (hK : ∀ μ y, ‖A μ y‖ ≤ K) (hL : 0 ≤ L)
    (hB : ∀ y, ‖H y‖ ≤ B) (hDH : ∀ y, ‖H' y‖ ≤ DH) :
    0 ≤ Real.sqrt (Fintype.card D) * higgsConst K B L DH := by
  rcases isEmpty_or_nonempty D with hD | ⟨⟨μ⟩⟩
  · simp
  · have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK μ 0)
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
    have hD0 : 0 ≤ DH := (norm_nonneg _).trans (hDH 0)
    unfold higgsConst; positivity

/-- **The `L_h^{8/3}` consistency error of the native Higgs packet**: on finitely many cells with
positions `pos x` and masses `m x ≥ 0`,
`‖K_h^H - (D_AH)_h‖_{L_h^{8/3}} ≤ √|D| (K²e^K B + L + K(D_H + L)) h (Σ_x m_x)^{3/8}`. -/
theorem lpNorm83_nativeHiggsPacket_sub_le {C : Type*} [Fintype C] {A : D → E → F →L[ℝ] F}
    {H : E → F} {H' : E → E →L[ℝ] F} {e : D → E} {K B L DH : ℝ} (hK : ∀ μ y, ‖A μ y‖ ≤ K)
    (hH : ∀ y, HasFDerivAt H (H' y) y) (hHL : ∀ y z, ‖H' y - H' z‖ ≤ L * ‖y - z‖) (hL : 0 ≤ L)
    (hB : ∀ y, ‖H y‖ ≤ B) (hDH : ∀ y, ‖H' y‖ ≤ DH) (he : ∀ μ, ‖e μ‖ ≤ 1) (pos : C → E)
    (m : C → ℝ) (hm : ∀ x, 0 ≤ m x) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    positiveHiggsLpNorm m (8 / 3) (fun x => amp (nativeHiggsPacket A H e h (pos x) -
        covHiggsPacket A H H' e (pos x))) ≤
      Real.sqrt (Fintype.card D) * (higgsConst K B L DH * h) * (∑ x, m x) ^ (3 / 8 : ℝ) := by
  have hpt : ∀ x, amp (nativeHiggsPacket A H e h (pos x) - covHiggsPacket A H H' e (pos x)) ≤
      Real.sqrt (Fintype.card D) * (higgsConst K B L DH * h) := fun x =>
    amp_le_of_forall_norm_le fun μ =>
      norm_nativeHiggsPacket_sub_le hK hH hHL hL hB hDH he (pos x) hh hh1 μ
  have hc0 : 0 ≤ Real.sqrt (Fintype.card D) * (higgsConst K B L DH * h) := by
    rw [← mul_assoc]
    exact mul_nonneg (sqrt_card_mul_higgsConst_nonneg (H := H) hK hL hB hDH) hh.le
  have := lpNorm_le_of_le m hm (p := 8 / 3) (by norm_num) _ (fun x => amp_nonneg _) hpt hc0
  rwa [show (1 : ℝ) / (8 / 3) = 3 / 8 by norm_num] at this

/-- **Continuum identification** (`prop:positive-Higgs-envelope`, smooth-family sentence): for a
family of cutoffs `h_i ∈ (0,1]` with cells `Cell i`, positions `pos i`, masses `m_i ≥ 0` of
uniformly bounded total mass `Σ_x m_i(x) ≤ M`, and a smooth bounded family of reconstructed
fields `(A_i, H_i)` (uniform constants `K, B, L, D_H`), the `L_h^{8/3}` criterion of the native
Higgs packet `K_{h_i}^H` and of the sampled continuum covariant derivative `D_{A_i}H_i` differ by
at most `√|D| C h_i M^{3/8}`, and one is uniformly bounded iff the other is. -/
theorem nativeHiggs_continuum_identification {ι : Type*} {Cell : ι → Type*}
    [∀ i, Fintype (Cell i)] {A : ι → D → E → F →L[ℝ] F} {H : ι → E → F}
    {H' : ι → E → E →L[ℝ] F} {e : D → E} {K B L DH M : ℝ} (hK : ∀ i μ y, ‖A i μ y‖ ≤ K)
    (hH : ∀ i y, HasFDerivAt (H i) (H' i y) y)
    (hHL : ∀ i y z, ‖H' i y - H' i z‖ ≤ L * ‖y - z‖) (hL : 0 ≤ L) (hB : ∀ i y, ‖H i y‖ ≤ B)
    (hDH : ∀ i y, ‖H' i y‖ ≤ DH) (he : ∀ μ, ‖e μ‖ ≤ 1) (cut : ι → ℝ) (hcut : ∀ i, 0 < cut i)
    (hcut1 : ∀ i, cut i ≤ 1) (pos : ∀ i, Cell i → E) (m : ∀ i, Cell i → ℝ)
    (hm : ∀ i x, 0 ≤ m i x) (hM0 : 0 ≤ M) (hM : ∀ i, ∑ x, m i x ≤ M) :
    (∀ i, |positiveHiggsLpNorm (m i) (8 / 3)
          (fun x => amp (nativeHiggsPacket (A i) (H i) e (cut i) (pos i x))) -
        positiveHiggsLpNorm (m i) (8 / 3)
          (fun x => amp (covHiggsPacket (A i) (H i) (H' i) e (pos i x)))| ≤
      Real.sqrt (Fintype.card D) * (higgsConst K B L DH * cut i) * M ^ (3 / 8 : ℝ)) ∧
    ((∃ Bd, ∀ i, positiveHiggsLpNorm (m i) (8 / 3)
          (fun x => amp (nativeHiggsPacket (A i) (H i) e (cut i) (pos i x))) ≤ Bd) ↔
      (∃ Bd, ∀ i, positiveHiggsLpNorm (m i) (8 / 3)
          (fun x => amp (covHiggsPacket (A i) (H i) (H' i) e (pos i x))) ≤ Bd)) := by
  have hc : ∀ i, 0 ≤ Real.sqrt (Fintype.card D) * higgsConst K B L DH := fun i =>
    sqrt_card_mul_higgsConst_nonneg (H := H i) (hK i) hL (hB i) (hDH i)
  have hbound : ∀ i, |positiveHiggsLpNorm (m i) (8 / 3)
          (fun x => amp (nativeHiggsPacket (A i) (H i) e (cut i) (pos i x))) -
        positiveHiggsLpNorm (m i) (8 / 3)
          (fun x => amp (covHiggsPacket (A i) (H i) (H' i) e (pos i x)))| ≤
      Real.sqrt (Fintype.card D) * (higgsConst K B L DH * cut i) * M ^ (3 / 8 : ℝ) := by
    intro i
    refine (lpNorm83_sub_le (m i) (hm i)
      (fun x => nativeHiggsPacket (A i) (H i) e (cut i) (pos i x))
      (fun x => covHiggsPacket (A i) (H i) (H' i) e (pos i x))).trans ?_
    refine (lpNorm83_nativeHiggsPacket_sub_le (hK i) (hH i) (hHL i) hL (hB i) (hDH i) he (pos i)
      (m i) (hm i) (hcut i) (hcut1 i)).trans ?_
    have hS : 0 ≤ ∑ x, m i x := Finset.sum_nonneg fun x _ => hm i x
    have hc' : 0 ≤ Real.sqrt (Fintype.card D) * (higgsConst K B L DH * cut i) := by
      rw [← mul_assoc]; exact mul_nonneg (hc i) (hcut i).le
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hS (hM i) (by norm_num)) hc'
  refine ⟨hbound, ?_⟩
  set E₀ := Real.sqrt (Fintype.card D) * higgsConst K B L DH * M ^ (3 / 8 : ℝ)
  have hE : ∀ i, |positiveHiggsLpNorm (m i) (8 / 3)
          (fun x => amp (nativeHiggsPacket (A i) (H i) e (cut i) (pos i x))) -
        positiveHiggsLpNorm (m i) (8 / 3)
          (fun x => amp (covHiggsPacket (A i) (H i) (H' i) e (pos i x)))| ≤ E₀ := fun i =>
    (hbound i).trans (by
      have hMp : 0 ≤ M ^ (3 / 8 : ℝ) := Real.rpow_nonneg hM0 _
      calc Real.sqrt (Fintype.card D) * (higgsConst K B L DH * cut i) * M ^ (3 / 8 : ℝ)
          = Real.sqrt (Fintype.card D) * higgsConst K B L DH * M ^ (3 / 8 : ℝ) * cut i := by
            ring
        _ ≤ Real.sqrt (Fintype.card D) * higgsConst K B L DH * M ^ (3 / 8 : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left (hcut1 i) (mul_nonneg (hc i) hMp)
        _ = E₀ := mul_one _)
  constructor
  · rintro ⟨Bd, hBd⟩
    refine ⟨Bd + E₀, fun i => ?_⟩
    have := hE i
    rw [abs_sub_le_iff] at this
    linarith [hBd i]
  · rintro ⟨Bd, hBd⟩
    refine ⟨Bd + E₀, fun i => ?_⟩
    have := hE i
    rw [abs_sub_le_iff] at this
    linarith [hBd i]

/-- Non-vacuity: the constant data (`A = 0`, `H ≡ v`, `dH = 0`) satisfy all hypotheses, and the
native packet then vanishes identically, as does `D_AH`. -/
example (v : ℝ) : nativeHiggsPacket (D := Fin 4) (E := Fin 4 → ℝ) (F := ℝ)
    (fun _ _ => 0) (fun _ => v) (fun μ => Pi.single μ 1) (1 / 2) 0 = 0 := by
  funext μ
  simp [nativeHiggsPacket]

end RenewalGeometry.HiggsPacketConsistency
