/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMMeshConsistency

/-!
# Sector estimates of `prop:mesh-consistency` (Standard-Model sector)

Einstein–Standard-Model action-closure manuscript, `prop:mesh-consistency`, proof: "The pointwise
densities and their first variations are finite sums of smooth coefficient functions and products
of these quantities. Their difference is `O(h)‖v‖_{C^{r₀}}`. A Riemann sum over cells of volume
`O(h⁴)` has `O(h⁻⁴)` terms on a fixed region, so the integrated error is `O(h)`."

`exists_sm_estimate`: for the comparison Standard-Model action `smAction` (node sum of
`smPt ∘ stencilJet` with weight `h⁴`), uniformly over `C^{1,1}` reconstructed fields `z = 𝒥_h q`,
reconstructed directions `W = 𝒥_h w` and comparison directions `v̂` with `W - v̂ = O(h)` in `C¹`,
`|D S_{SM,h}(q)[w] - ∫_{box} D smPt(contJet z)[contJetDeriv z v̂]| ≤ C h`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ContDiff ENNReal NNReal

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM
namespace Comparison

open SobolevOpen (pd)
open CardinalQI C11Calculus UnitCubeRiemannSum LipschitzRiemannSum

variable {Ysec : Type} [Fintype Ysec] (FC : FermionCarrier Ysec)

theorem nodePt_eq (N k : ℕ) (j : Fin 4 → Fin N) :
    nodePt N k j = (k : ℝ) • e0 + gridPoint N j := by
  funext i
  by_cases hi : i = 0
  · subst hi; simp [nodePt, gridPoint, e0_apply]
  · simp [nodePt, gridPoint, e0_apply, hi]

theorem BL.continuous {X : Type*} [NormedAddCommGroup X] {f : E4 → X} {M : ℝ} (hf : BL f M) :
    Continuous f :=
  (LipschitzWith.of_dist_le_mul (K := M.toNNReal) fun y y' => by
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hf.nonneg]
    exact hf.lip y y').continuous

/-- **The finite first variation of the comparison SM action** is the weighted node sum of the
derivative of `smPt` along the stencil-jet variations. -/
theorem finiteVar_smAction_eq (θ : CoefficientBank Ysec) (P N : ℕ) (hN : 0 < N)
    (q w : (Fin 4 → ℤ) → FieldVal FC.C) (D : E4 → RJet FC.C)
    (hD : ∀ x, HasDerivAt (fun t : ℝ => stencilJet FC (1 / N)
      (reconFields FC (1 / N) q + t • reconFields FC (1 / N) w) x) (D x) 0)
    (hmem : ∀ x, stencilJet FC (1 / N) (reconFields FC (1 / N) q) x ∈ jetGL FC.C) :
    finiteVar (smAction FC θ P N) q w = (1 / (N : ℝ)) ^ 4 * ∑ k : Fin P, ∑ j : Fin 4 → Fin N,
      fderiv ℝ (smPt FC θ) (stencilJet FC (1 / N) (reconFields FC (1 / N) q) (nodePt N k j))
        (D (nodePt N k j)) := by
  have hh : (0 : ℝ) < 1 / N := by positivity
  have e : (fun t : ℝ => smAction FC θ P N (q + t • w)) = fun t => (1 / (N : ℝ)) ^ 4 *
      ∑ k : Fin P, ∑ j : Fin 4 → Fin N, smPt FC θ (stencilJet FC (1 / N)
        (reconFields FC (1 / N) q + t • reconFields FC (1 / N) w) (nodePt N k j)) := by
    funext t
    simp only [smAction, reconFields_add_smul FC hh]
  have hd : ∀ x, HasDerivAt (fun t : ℝ => smPt FC θ (stencilJet FC (1 / N)
      (reconFields FC (1 / N) q + t • reconFields FC (1 / N) w) x))
      (fderiv ℝ (smPt FC θ) (stencilJet FC (1 / N) (reconFields FC (1 / N) q) x) (D x)) 0 :=
    fun x => (differentiableAt_smPt FC θ (hmem x)).hasFDerivAt.comp_hasDerivAt_of_eq 0 (hD x)
      (by simp)
  have H : HasDerivAt (fun t : ℝ => smAction FC θ P N (q + t • w)) ((1 / (N : ℝ)) ^ 4 *
      ∑ k : Fin P, ∑ j : Fin 4 → Fin N, fderiv ℝ (smPt FC θ)
        (stencilJet FC (1 / N) (reconFields FC (1 / N) q) (nodePt N k j))
        (D (nodePt N k j))) 0 := by
    rw [e]
    refine HasDerivAt.const_mul _ ?_
    exact HasDerivAt.fun_sum fun k _ => HasDerivAt.fun_sum fun j _ => hd _
  exact H.deriv

/-- Bookkeeping of the node sum against the cell integrals. -/
theorem abs_nodeSum_sub_le {P N : ℕ} (hN : 0 < N) (f g : Fin P → (Fin 4 → Fin N) → ℝ)
    (I : Fin P → ℝ) {a b : ℝ} (hfg : ∀ k j, |f k j - g k j| ≤ a)
    (hgI : ∀ k, |(1 / (N : ℝ)) ^ 4 * ∑ j, g k j - I k| ≤ b) :
    |(1 / (N : ℝ)) ^ 4 * ∑ k, ∑ j, f k j - ∑ k, I k| ≤ P * (a + b) := by
  have hcard := card_mul_cellVolume (d := 4) hN
  simp only [Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ] at hcard
  have e : (1 / (N : ℝ)) ^ 4 * ∑ k, ∑ j, f k j - ∑ k, I k = ∑ k : Fin P,
      ((1 / (N : ℝ)) ^ 4 * ∑ j, (f k j - g k j) + ((1 / (N : ℝ)) ^ 4 * ∑ j, g k j - I k)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_sub_distrib]; ring
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hk : ∀ k : Fin P, |(1 / (N : ℝ)) ^ 4 * ∑ j, (f k j - g k j) +
      ((1 / (N : ℝ)) ^ 4 * ∑ j, g k j - I k)| ≤ a + b := by
    intro k
    refine (abs_add_le _ _).trans (add_le_add ?_ (hgI k))
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc (1 / (N : ℝ)) ^ 4 * |∑ j, (f k j - g k j)|
        ≤ (1 / (N : ℝ)) ^ 4 * ∑ _j : Fin 4 → Fin N, a :=
          mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun j _ => hfg k j)) (by positivity)
      _ = a := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, mul_comm _ (_ : ℝ)]
          simp only [Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ]
          rw [mul_comm ((1 / (N : ℝ)) ^ 4), hcard, mul_one]
  calc ∑ k : Fin P, |(1 / (N : ℝ)) ^ 4 * ∑ j, (f k j - g k j) +
        ((1 / (N : ℝ)) ^ 4 * ∑ j, g k j - I k)| ≤ ∑ _k : Fin P, (a + b) :=
        Finset.sum_le_sum fun k _ => hk k
    _ = P * (a + b) := by simp; ring

theorem stencilJet_e (h : ℝ) (z : FieldTuple FC.C) (x : E4) :
    (stencilJet FC h z x).e = z.e x := rfl

theorem contJet_e (z : FieldTuple FC.C) (x : E4) : (contJet FC z x).e = z.e x := rfl

/-- **The Standard-Model sector estimate of `eq:mesh-C1`**: uniformly over `C^{1,1}`
reconstructed fields with coframe in a compact chart set, reconstructed directions `W = 𝒥_h w`
and comparison directions `v̂` with `W - v̂ = O(h)` in `C¹`, the finite first variation of the
comparison Standard-Model action is the box integral of the continuum density variation up to
`O(h)`. -/
theorem exists_sm_estimate [Nonempty FC.C] (θ : CoefficientBank Ysec) {Ke : Set CoframeFibre}
    (hKe : IsCompact Ke) (hKeGL : Ke ⊆ coframeGL) {B : ℝ} (hB : 0 ≤ B) {κ : ℝ} (hκ : 0 ≤ κ)
    (P : ℕ) : ∃ C h₀ : ℝ, 0 < h₀ ∧ ∀ (N : ℕ) (q w : (Fin 4 → ℤ) → FieldVal FC.C)
      (v : FieldTuple FC.C), 0 < N → 1 / (N : ℝ) ≤ h₀ →
      FieldC11 FC (reconFields FC (1 / N) q) B → FieldC11 FC (reconFields FC (1 / N) w) B →
      FieldC11 FC v B → (∀ y, (reconFields FC (1 / N) q).e y ∈ Ke) →
      (∀ y, PtSmall FC (reconFields FC (1 / N) w - v) y (κ * (1 / N))) →
      |finiteVar (smAction FC θ P N) q w - ∫ x in compBox P, fderiv ℝ (smPt FC θ)
        (contJet FC (reconFields FC (1 / N) q) x)
        (contJetDeriv FC (reconFields FC (1 / N) q) v x)| ≤ C * (1 / N) := by
  obtain ⟨C₁, h₀, hh₀, hh₀1, hST⟩ := exists_stencilJet_estimates FC B hB hKe hKeGL
  obtain ⟨M, hS⟩ := exists_spinChart FC hKe hKeGL B
  obtain ⟨Cz, hCz⟩ := exists_bl_contJet FC hKeGL hS hB
  obtain ⟨Cv, hCv⟩ := exists_bl_contJetDeriv FC hKeGL hS hB hB
  set R₀ := |Cz| + |C₁|
  set Kj : Set (RJet FC.C) := {R | R.e ∈ Ke} ∩ closedBall 0 R₀
  have hKj : IsCompact Kj :=
    (isCompact_closedBall (0 : RJet FC.C) R₀).inter_left
      (hKe.isClosed.preimage (πe (C := FC.C)).continuous)
  have hKjGL : Kj ⊆ jetGL FC.C := fun R hR => hKeGL hR.1
  have hD1 : ContDiffOn ℝ 1 (fderiv ℝ (smPt FC θ)) (jetGL FC.C) :=
    ((contDiffOn_bosonPt θ (n := 2)).add (contDiffOn_diracPt FC θ (n := 2))).fderiv_of_isOpen
      isOpen_jetGL (by norm_num)
  obtain ⟨LD, MD, hLD, hMD, hMDb, hLDl⟩ := exists_C1_on_compact isOpen_jetGL hD1 hKj hKjGL
  set CJ := 2 + 24 * B + M * B + M
  set c₂ := LD * |C₁| * (|Cv| + |C₁|) + MD * |C₁| + MD * (CJ * κ)
  set CG := 2 * 1 * max MD (LD * Cz) * Cv
  refine ⟨P * (c₂ + CG), h₀, hh₀, fun N q w v hN hNh₀ hz hW hv hzK hsm => ?_⟩
  set h : ℝ := 1 / N with hhdef
  have hh : 0 < h := by positivity
  have hh1 : h ≤ 1 := hNh₀.trans hh₀1
  set z := reconFields FC h q
  set W := reconFields FC h w
  have hST' := fun x => hST z W hz hW hzK x h hh hNh₀
  choose D hD hDb using fun x => (hST' x).2
  have hC1h : C₁ * h ≤ |C₁| * h := mul_le_mul_of_nonneg_right (le_abs_self C₁) hh.le
  have hC1h' : |C₁| * h ≤ |C₁| := mul_le_of_le_one_right (abs_nonneg _) hh1
  have hzJ : ∀ x, contJet FC z x ∈ Kj := fun x =>
    ⟨hzK x, mem_closedBall_zero_iff.mpr (((hCz z hz hzK).bound x).trans
      ((le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))))⟩
  have hSJ : ∀ x, stencilJet FC h z x ∈ Kj := fun x => by
    refine ⟨hzK x, mem_closedBall_zero_iff.mpr ?_⟩
    have h1 := (hST' x).1
    have h2 := (hCz z hz hzK).bound x
    have h3 := norm_le_insert' (stencilJet FC h z x) (contJet FC z x)
    have h4 := le_abs_self Cz
    simp only [R₀]
    linarith
  have hFV := finiteVar_smAction_eq FC θ P N hN q w D hD (fun x => hKjGL (hSJ x))
  set G : E4 → ℝ := fun x => fderiv ℝ (smPt FC θ) (contJet FC z x) (contJetDeriv FC z v x)
  have hGbl : BL G CG := BL.apply (BL.comp hLD hMDb hLDl (hCz z hz hzK) hzJ) (hCv z v hz hv hzK)
  -- the node estimate
  have hnode : ∀ x, |fderiv ℝ (smPt FC θ) (stencilJet FC h z x) (D x) - G x| ≤ c₂ * h := by
    intro x
    have hdW : DiffAt FC (W - v) x :=
      ⟨(hW.e.differentiable x).sub (hv.e.differentiable x),
        (hW.A.differentiable x).sub (hv.A.differentiable x),
        (hW.H.differentiable x).sub (hv.H.differentiable x),
        (hW.Ψ.differentiable x).sub (hv.Ψ.differentiable x),
        (hW.Ψb.differentiable x).sub (hv.Ψb.differentiable x)⟩
    have hsub := contJetDeriv_sub FC z (hW.diffAt FC x) (hv.diffAt FC x)
    set Sx := stencilJet FC h z x
    set Cx := contJet FC z x
    set fS := fderiv ℝ (smPt FC θ) Sx
    set fC := fderiv ℝ (smPt FC θ) Cx
    have e : fS (D x) - G x = (fS - fC) (D x) + fC (D x - contJetDeriv FC z W x) +
        fC (contJetDeriv FC z (W - v) x) := by
      rw [← hsub]
      simp only [G, ContinuousLinearMap.sub_apply, map_sub]
      abel
    rw [e, ← Real.norm_eq_abs]
    have hDn : ‖D x‖ ≤ |Cv| + |C₁| := by
      have h1 := norm_le_insert' (D x) (contJetDeriv FC z W x)
      have h2 := (hCv z W hz hW hzK).bound x
      have h3 := hDb x
      have h4 := le_abs_self Cv
      linarith
    have t1 : ‖(fS - fC) (D x)‖ ≤ LD * (|C₁| * h) * (|Cv| + |C₁|) :=
      ((fS - fC).le_opNorm _).trans (mul_le_mul ((hLDl _ (hSJ x) _ (hzJ x)).trans
        (mul_le_mul_of_nonneg_left ((hST' x).1.trans hC1h) hLD)) hDn (norm_nonneg _)
        (by positivity))
    have t2 : ‖fC (D x - contJetDeriv FC z W x)‖ ≤ MD * (|C₁| * h) :=
      (fC.le_opNorm _).trans (mul_le_mul (hMDb _ (hzJ x)) ((hDb x).trans hC1h) (norm_nonneg _)
        hMD)
    have t3 : ‖fC (contJetDeriv FC z (W - v) x)‖ ≤ MD * (CJ * (κ * h)) :=
      (fC.le_opNorm _).trans (mul_le_mul (hMDb _ (hzJ x))
        (norm_contJetDeriv_le FC hKeGL hS hz hzK hdW (hsm x)) (norm_nonneg _) hMD)
    calc ‖(fS - fC) (D x) + fC (D x - contJetDeriv FC z W x) + fC (contJetDeriv FC z (W - v) x)‖
        ≤ ‖(fS - fC) (D x)‖ + ‖fC (D x - contJetDeriv FC z W x)‖ +
          ‖fC (contJetDeriv FC z (W - v) x)‖ := norm_add₃_le
      _ ≤ LD * (|C₁| * h) * (|Cv| + |C₁|) + MD * (|C₁| * h) + MD * (CJ * (κ * h)) :=
          add_le_add_three t1 t2 t3
      _ = c₂ * h := by simp only [c₂]; ring
  -- the cell quadratures
  have hcell : ∀ k : Fin P, |(1 / (N : ℝ)) ^ 4 * ∑ j : Fin 4 → Fin N, G (nodePt N k j) -
      ∫ x in Icc (0 : E4) 1, G ((k : ℝ) • e0 + x)| ≤ CG * h := by
    intro k
    have hL : LipschitzOnWith CG.toNNReal (fun x => G ((k : ℝ) • e0 + x)) (Icc 0 1) :=
      LipschitzOnWith.of_dist_le_mul fun x _ y _ => by
        rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hGbl.nonneg]
        have := hGbl.lip ((k : ℝ) • e0 + x) ((k : ℝ) • e0 + y)
        rwa [add_sub_add_left_eq_sub] at this
    have := norm_riemannSum_sub_integral_le hN hL
    rw [Real.norm_eq_abs, smul_eq_mul, Real.coe_toNNReal _ hGbl.nonneg] at this
    simp only [nodePt_eq]
    exact this
  rw [hFV, integral_compBox hGbl.continuous P]
  refine (abs_nodeSum_sub_le hN _ (fun k j => G (nodePt N k j)) _
    (fun k j => hnode (nodePt N k j)) hcell).trans (le_of_eq ?_)
  ring

end Comparison
end EinsteinSM
end RenewalGeometry
