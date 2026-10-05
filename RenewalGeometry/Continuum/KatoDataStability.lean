/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.KatoPhysicalIdentification

/-!
# Continuous dependence of Kato's solutions on the data and physical identification through the
  analytic core

Generic infrastructure (no renewal notions) for `lem:generated-physical-identification` of the
Einstein–Standard-Model action-closure manuscript (`app:generated-dynamics`).  Setting of
`KatoLocalExistence`: `∂_tU + Σ_i A^i(U)∂_iU = F(U)` on `𝕋^d` with smooth real symmetric `A^i`,
smooth `F`, `m > d/2`, `q ≥ 2m`, `q ≥ m + 2`.

* `galerkin_data_L2`, **`galerkin_data_sup`** — `L²` and `C⁰`/`C¹_x` stability of the spectral
  Galerkin evolution in the data, uniformly in the cutoff.
* **`kato_forward_stable`**, **`kato_two_sided_stable`** — Kato's local existence with a solution
  map `U₀ ↦ (U, ∂_xU)` that is continuous from `L²` data (in the `H^q` ball) to `C⁰` with first
  spatial derivatives on `[0, T] × 𝕋^d`.
* `twoSided_unique`, `twoSided_P_eq` — two classical two-sided solutions with the same data
  coincide (with their spatial derivatives) on every common slab `[0, t₁]`.
* `PhysicalOn` — pointwise first-jet identities `Φ_j(U, ∂U) = 0` on `[0, t₁] × ℝ^d`.
* **`AnalyticCoreContinuation`** — the named analytic-core / physical-Cauchy input of
  `ass:constrained-initial-solver` **with its continuation clause** (germs exist on an interval
  controlled by the `H^q` bound) and the availability (density) of the core.
* **`kato_physical_identification`** — the Sobolev-data case of the lemma: for every constrained
  datum (not assumed in the core) the Kato solution satisfies the physical identities on a
  common interval `[0, t₁]`, by approximation from the core, uniqueness and stability.
  Non-vacuity example on `𝕋³`.

Disclosed rendering: `Σ = 𝕋^d`; data are smooth periodic with an `H^q` bound (finite-regularity
data enter through such approximations); the physical identities are an abstract continuous
family of first-jet identities; the symmetric system is generic (its instantiation on the
actual-jet system of `prop:actual-jet-writer` is not made here).
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff Real NNReal

noncomputable section

namespace RenewalGeometry.KatoStab

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy KatoGalerkin

set_option linter.unusedSectionVars false

variable {d n : ℕ}

/-! ### `L²` stability of the Galerkin evolution in the data -/

section Galerkin

variable {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}

/-- **`L²` stability of the spectral Galerkin evolution in the data** (same cutoff): two Galerkin
solutions bounded by `R` in `H^q` on `[0, T]` satisfy
`‖U_N(t) - V_N(t)‖²_{L²} ≤ e^{2K₁t} ‖U_N(0) - V_N(0)‖²_{L²}` (the projection disappears from the
`L²` pairing on `Ran P_N`; symmetric `L²` difference estimate `sym_L2_diff`; Grönwall). -/
theorem galerkin_data_L2 {m q : ℕ} (hm : (d : ℝ) / 2 < m) (hmq : m + 1 ≤ q)
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hsym : ∀ i a b v, A i a b v = A i b a v)
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R T : ℝ} (hR : 0 ≤ R) :
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ (N : ℕ) (γ γ' : ℝ → GS d n N),
      (∀ t ∈ Set.Icc 0 T, HasDerivWithinAt γ (GN A F q (γ t)) (Set.Icc 0 T) t) →
      (∀ t ∈ Set.Icc 0 T, HasDerivWithinAt γ' (GN A F q (γ' t)) (Set.Icc 0 T) t) →
      (∀ t ∈ Set.Icc 0 T, ‖γ t‖ ≤ R) → (∀ t ∈ Set.Icc 0 T, ‖γ' t‖ ≤ R) →
      ∀ t ∈ Set.Icc 0 T, ∑ b, ∑ k ∈ box N, (cf q (γ t) b k - cf q (γ' t) b k) ^ 2 ≤
        Real.exp (2 * K₁ * t) * ∑ b, ∑ k ∈ box N, (cf q (γ 0) b k - cf q (γ' 0) b k) ^ 2 := by
  obtain ⟨CS, hCS, hsup⟩ := exists_sup_sq_le (d := d) hm
  set B := Real.sqrt CS * R with hB
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨K₁, hK₁0, hK₁⟩ := sym_L2_diff hA hsym hF hB0
  refine ⟨K₁, hK₁0, fun N γ γ' hγ hγ' hγR hγR' t ht => ?_⟩
  have hbd : ∀ (g : ℝ → GS d n N), (∀ s ∈ Set.Icc 0 T, ‖g s‖ ≤ R) → ∀ s ∈ Set.Icc 0 T,
      (∀ b x, |fld q (g s) b x| ≤ B) ∧ (∀ b (i : Fin d) x, |pd (fld q (g s) b) i.succ x| ≤ B) := by
    intro g hg s hs
    have hn := hg s hs
    refine ⟨fun b x => ?_, fun b i x => ?_⟩
    · exact (abs_fld_le hmq hCS hsup (g s) b x).1.trans
        (mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg _))
    · exact ((abs_fld_le hmq hCS hsup (g s) b x).2 i).trans
        (mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg _))
  set ĝ : ℝ → Fin n → (Fin d → ℤ) → ℝ := fun s b k =>
    coef (genG A F (fld q (γ s)) b) 0 k with hĝ
  set ĝ' : ℝ → Fin n → (Fin d → ℤ) → ℝ := fun s b k =>
    coef (genG A F (fld q (γ' s)) b) 0 k with hĝ'
  set D : ℝ → ℝ := fun t => ∑ b, ∑ k ∈ box N, (cf q (γ t) b k - cf q (γ' t) b k) ^ 2 with hD
  set D' : ℝ → ℝ := fun t => ∑ b, ∑ k ∈ box N, 2 * (cf q (γ t) b k - cf q (γ' t) b k) *
    (ĝ t b k - ĝ' t b k) with hD'
  have hderiv : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt D (D' t) (Set.Icc 0 T) t := by
    intro t ht
    refine HasDerivWithinAt.fun_sum fun b _ => HasDerivWithinAt.fun_sum fun k hk => ?_
    exact hasDerivWithinAt_sq' ((hasDerivWithinAt_cf (hγ t ht) b hk).sub
      (hasDerivWithinAt_cf (hγ' t ht) b hk))
  have hD'b : ∀ t ∈ Set.Icc 0 T, D' t ≤ 2 * K₁ * D t + 0 := by
    intro t ht
    have h1 : ∀ b, sint (fun x => (fld q (γ t) b x - fld q (γ' t) b x) *
        (genG A F (fld q (γ t)) b x - genG A F (fld q (γ' t)) b x)) 0 =
        ∑ k ∈ box N, (cf q (γ t) b k - cf q (γ' t) b k) * (ĝ t b k - ĝ' t b k) := by
      intro b
      have e : (fun x => (fld q (γ t) b x - fld q (γ' t) b x) *
          (genG A F (fld q (γ t)) b x - genG A F (fld q (γ' t)) b x)) =
          fun x => tfs (box N) (fun k => cf q (γ t) b k - cf q (γ' t) b k) x *
            (fun x => genG A F (fld q (γ t)) b x - genG A F (fld q (γ' t)) b x) x := by
        funext x; rw [fld, fld, tfs_sub]
      rw [e, sint_tfs_mul (g := fun x => genG A F (fld q (γ t)) b x -
          genG A F (fld q (γ' t)) b x) _ _
        ((contDiff_genG hA hF (fun b => contDiff_fld q _ b) b).continuous.sub
        (contDiff_genG hA hF (fun b => contDiff_fld q _ b) b).continuous)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [coef_sub (contDiff_genG hA hF (fun b => contDiff_fld q _ b) b).continuous
        (contDiff_genG hA hF (fun b => contDiff_fld q _ b) b).continuous]
    have hP : ∑ b, sint (fun x => (fld q (γ t) b x - fld q (γ' t) b x) *
        (genG A F (fld q (γ t)) b x - genG A F (fld q (γ' t)) b x)) 0 ≤ K₁ * D t := by
      have := hK₁ (fld q (γ t)) (fld q (γ' t)) (fun b => contDiff_fld q _ b)
        (fun b => contDiff_fld q _ b) (fun b => isSPeriodic_fld q _ b)
        (fun b => isSPeriodic_fld q _ b) (hbd γ hγR t ht).1 (hbd γ' hγR' t ht).1
        (hbd γ hγR t ht).2 (hbd γ' hγR' t ht).2 0
      refine this.trans (le_of_eq ?_)
      congr 1
      exact Finset.sum_congr rfl fun b _ => sint_fld_sub_sq le_rfl _ _ b 0
    have hsum : D' t = 2 * ∑ b, sint (fun x => (fld q (γ t) b x - fld q (γ' t) b x) *
        (genG A F (fld q (γ t)) b x - genG A F (fld q (γ' t)) b x)) 0 := by
      simp only [hD', h1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring
    rw [hsum]; linarith
  have hcont : ContinuousOn D (Set.Icc 0 T) := fun t ht => (hderiv t ht).continuousWithinAt
  have hgr := SpectralGalerkin.le_gronwall_scalar (f := D) (f' := D') (K := 2 * K₁)
    (ε := 0) hcont
    (fun t ht => (hderiv t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)) (fun t ht => hD'b t (Ico_subset_Icc_self ht)) t ht
  rw [gronwallBound_ε0] at hgr
  calc D t ≤ D 0 * Real.exp (2 * K₁ * t) := hgr
    _ = _ := mul_comm _ _

/-- The truncated data differ in `L²` by at most the data: `‖P_N U₀ - P_N V₀‖²_{L²} ≤
‖U₀ - V₀‖²_{L²}` (Bessel). -/
theorem sum_cf_P0_sub_sq_le (q N : ℕ) {U₀ V₀ : Fin n → ST d → ℝ}
    (hU : ∀ b, Continuous (U₀ b)) (hV : ∀ b, Continuous (V₀ b)) :
    ∑ b, ∑ k ∈ box (d := d) N, (cf q (P0 q N U₀) b k - cf q (P0 q N V₀) b k) ^ 2 ≤
      ∑ b, sint (fun x => (U₀ b x - V₀ b x) ^ 2) 0 := by
  refine Finset.sum_le_sum fun b _ => ?_
  have h := bessel_L2 (box (d := d) N) ((hU b).sub (hV b)) 0
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun k hk => ?_)) h
  rw [cf_P0, cf_P0, if_pos hk, if_pos hk]
  congr 1; exact (coef_sub (hU b) (hV b) 0 k).symm

/-- **`C¹` stability of the spectral Galerkin evolution in the data, uniformly in the cutoff**
(`m > d/2`, `q ≥ m + 2`): for every `ε > 0` there is `δ > 0` such that two Galerkin solutions
bounded by `R` in `H^q` on `[0, T]` whose initial states are `δ`-close in `L²` stay `ε`-close on
`[0, T]` together with their first spatial derivatives, for every cutoff `N` (the `L²` stability
`galerkin_data_L2`, frequency splitting `Q_tfs_split` against the uniform `H^q` bound, slice
Sobolev embedding). -/
theorem galerkin_data_sup {m q : ℕ} (hm : (d : ℝ) / 2 < m) (hq2 : m + 2 ≤ q)
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hsym : ∀ i a b v, A i a b v = A i b a v)
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T) :
    ∀ ε > 0, ∃ δ > 0, ∀ (N : ℕ) (γ γ' : ℝ → GS d n N),
      (∀ t ∈ Set.Icc 0 T, HasDerivWithinAt γ (GN A F q (γ t)) (Set.Icc 0 T) t) →
      (∀ t ∈ Set.Icc 0 T, HasDerivWithinAt γ' (GN A F q (γ' t)) (Set.Icc 0 T) t) →
      (∀ t ∈ Set.Icc 0 T, ‖γ t‖ ≤ R) → (∀ t ∈ Set.Icc 0 T, ‖γ' t‖ ≤ R) →
      ∑ b, ∑ k ∈ box N, (cf q (γ 0) b k - cf q (γ' 0) b k) ^ 2 ≤ δ →
      ∀ t ∈ Set.Icc 0 T, ∀ b x, |fld q (γ t) b x - fld q (γ' t) b x| ≤ ε ∧
        ∀ i : Fin d, |pd (fld q (γ t) b) i.succ x - pd (fld q (γ' t) b) i.succ x| ≤ ε := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := galerkin_data_L2 (T := T) hm (by omega : m + 1 ≤ q) hA hsym hF hR
  obtain ⟨CS, hCS, hsup⟩ := exists_sup_sq_le (d := d) hm
  intro ε hε
  set j := q - (m + 1) with hj
  have hj1 : 1 ≤ j := by omega
  have hqj : m + 1 + j = q := by omega
  obtain ⟨K, hK⟩ := exists_nat_gt (8 * CS * R ^ 2 / ε ^ 2)
  set W := ∑ k ∈ box (d := d) K, wq (m + 1) k with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun k _ => wq_nonneg _ k
  set Ex := Real.exp (2 * K₁ * T) with hEx
  have hEx0 : 0 < Ex := Real.exp_pos _
  have hε2 : 0 < ε ^ 2 := by positivity
  set δ := ε ^ 2 / (2 * (CS * W * Ex + 1)) with hδdef
  have hδ0 : 0 < δ := div_pos hε2 (by positivity)
  refine ⟨δ, hδ0, fun N γ γ' hγ hγ' hγR hγR' h0 t ht b x => ?_⟩
  set c : (Fin d → ℤ) → ℝ := fun k => cf q (γ t) b k - cf q (γ' t) b k with hc
  set e : ST d → ℝ := tfs (box N) c with he
  have he_eq : ∀ x, e x = fld q (γ t) b x - fld q (γ' t) b x := fun x => by
    rw [he, fld, fld, tfs_sub]
  have hes : ContDiff ℝ ∞ e := contDiff_tfs _ _
  have hep : IsSPeriodic e := isSPeriodic_tfs _ _
  have hQq : ∀ t', Q q e t' ≤ 4 * R ^ 2 := by
    intro t'
    have h1 : Q q e t' = Q q (fun x => fld q (γ t) b x - fld q (γ' t) b x) t' := by
      congr 1; funext x; exact he_eq x
    rw [h1]
    refine (Q_sub_le q (contDiff_fld q _ b) (contDiff_fld q _ b) t').trans ?_
    have h2 : ∀ (g : GS d n N), ‖g‖ ≤ R → Q q (fld q g b) t' ≤ R ^ 2 := fun g hg =>
      (Q_le_energyQ q (fld q g) t' b).trans ((energyQ_fld q _ t').le.trans
        (pow_le_pow_left₀ (norm_nonneg _) hg 2))
    linarith [h2 _ (hγR t ht), h2 _ (hγR' t ht)]
  have hL2 : ∑ k ∈ box N, c k ^ 2 ≤ Ex * δ := by
    refine le_trans ?_ ((hK₁ N γ γ' hγ hγ' hγR hγR' t ht).trans ?_)
    · exact Finset.single_le_sum (f := fun b => ∑ k ∈ box N,
        (cf q (γ t) b k - cf q (γ' t) b k) ^ 2)
        (fun b _ => Finset.sum_nonneg fun k _ => sq_nonneg _) (Finset.mem_univ b)
    · refine mul_le_mul (Real.exp_le_exp.2 ?_) h0
        (Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun k _ => sq_nonneg _) hEx0.le
      exact mul_le_mul_of_nonneg_left ht.2 (by positivity)
  have hQm : ∀ t', CS * Q (m + 1) e t' < ε ^ 2 := by
    intro t'
    have hsplit := Q_tfs_split (m + 1) j K (box N) c t'
    rw [← he, hqj] at hsplit
    have hsK : (K : ℝ) + 1 ≤ ((2 * π * ((K : ℝ) + 1)) ^ 2) ^ j := by
      have h1 := le_two_pi_succ_pow (q := 2 * j) (by omega) K
      rwa [pow_mul] at h1
    have hsK0 : 0 < (K : ℝ) + 1 := by positivity
    have t1 : CS * (W * ∑ k ∈ box N, c k ^ 2) < ε ^ 2 / 2 := by
      calc CS * (W * ∑ k ∈ box N, c k ^ 2) ≤ CS * (W * (Ex * δ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL2 hW0) hCS
        _ = CS * W * Ex * δ := by ring
        _ < ε ^ 2 / 2 := by
            rw [hδdef, mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
            nlinarith [mul_nonneg (mul_nonneg hCS hW0) hEx0.le]
    have t2 : CS * (Q q e t' / ((2 * π * ((K : ℝ) + 1)) ^ 2) ^ j) ≤
        CS * (4 * R ^ 2) / ((K : ℝ) + 1) := by
      rw [← mul_div_assoc]
      calc CS * Q q e t' / ((2 * π * ((K : ℝ) + 1)) ^ 2) ^ j
          ≤ CS * (4 * R ^ 2) / ((2 * π * ((K : ℝ) + 1)) ^ 2) ^ j :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hQq t') hCS) (by positivity)
        _ ≤ CS * (4 * R ^ 2) / ((K : ℝ) + 1) :=
            div_le_div_of_nonneg_left (by positivity) hsK0 hsK
    have t4 : CS * (4 * R ^ 2) / ((K : ℝ) + 1) < ε ^ 2 / 2 := by
      rw [div_lt_iff₀ hsK0]
      have h1 : 8 * CS * R ^ 2 / ε ^ 2 < K := hK
      rw [div_lt_iff₀ hε2] at h1
      nlinarith
    calc CS * Q (m + 1) e t' ≤ CS * (W * ∑ k ∈ box N, c k ^ 2 +
          Q q e t' / ((2 * π * ((K : ℝ) + 1)) ^ 2) ^ j) :=
          mul_le_mul_of_nonneg_left hsplit hCS
      _ = CS * (W * ∑ k ∈ box N, c k ^ 2) +
          CS * (Q q e t' / ((2 * π * ((K : ℝ) + 1)) ^ 2) ^ j) := by ring
      _ < ε ^ 2 := by linarith
  rw [← Fin.cons_self_tail x]
  refine ⟨?_, fun i => ?_⟩
  · rw [← he_eq]
    refine abs_le_of_sq_le_sq ?_ hε.le
    refine (hsup e hes hep _ _).trans ?_
    exact ((mul_le_mul_of_nonneg_left (Q_mono (Nat.le_succ m) e _) hCS)).trans (hQm _).le
  · have hpd : pd (fld q (γ t) b) i.succ (Fin.cons (x 0) (Fin.tail x)) -
        pd (fld q (γ' t) b) i.succ (Fin.cons (x 0) (Fin.tail x)) =
        pd e i.succ (Fin.cons (x 0) (Fin.tail x)) := by
      have : e = fun x => fld q (γ t) b x - fld q (γ' t) b x := funext he_eq
      rw [this, pd_sub_real (contDiff_fld q _ b) (contDiff_fld q _ b)]
    rw [hpd]
    refine abs_le_of_sq_le_sq ?_ hε.le
    refine (hsup _ (contDiff_pd_top hes _) (isSPeriodic_pd hep _) _ _).trans ?_
    exact (mul_le_mul_of_nonneg_left (Q_pd_le i e _) hCS).trans (hQm _).le

end Galerkin

/-! ### Stability of Kato's solutions in the data -/

/-- Admissible data of radius `R₀`: smooth, periodic, `‖U₀‖_{H^q} ≤ R₀`. -/
def Good (q : ℕ) (R₀ : ℝ) (U₀ : Fin n → ST d → ℝ) : Prop :=
  (∀ b, ContDiff ℝ ∞ (U₀ b)) ∧ (∀ b, IsSPeriodic (U₀ b)) ∧ energyQ q U₀ 0 ≤ R₀ ^ 2

/-- The squared `L²` distance of the data at `t = 0`. -/
def dataDist (U₀ V₀ : Fin n → ST d → ℝ) : ℝ := ∑ b, sint (fun x => (U₀ b x - V₀ b x) ^ 2) 0

section Kato

variable {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}

/-- **Kato's local existence with continuous dependence on the data** (forward form): for
`m > d/2`, `q ≥ 2m`, `q ≥ m + 2` and every data radius `R₀` there are `T > 0` and a solution map
`U₀ ↦ (U, P)` (`P = ∂_xU`) on the admissible data of radius `R₀` producing classical solutions on
`[0, T] × 𝕋^d`, such that for every `ε > 0` there is `δ > 0` with: data `δ`-close in `L²` give
solutions `ε`-close in `C⁰` together with their first spatial derivatives on `[0, T] × 𝕋^d`
(Galerkin-level stability `galerkin_data_sup`, uniform in the cutoff, passed to the limit). -/
theorem kato_forward_stable {m q : ℕ} (hm : (d : ℝ) / 2 < m) (hq : 2 * m ≤ q) (hq2 : m + 2 ≤ q)
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hsym : ∀ i a b v, A i a b v = A i b a v)
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ T > 0, ∃ Sol : (Fin n → ST d → ℝ) → (Fin n → ST d → ℝ) × (Fin n → Fin d → ST d → ℝ),
      (∀ U₀, Good q R₀ U₀ → ForwardSol A F U₀ T (Sol U₀).1 (Sol U₀).2) ∧
      ∀ ε > 0, ∃ δ > 0, ∀ U₀ V₀, Good q R₀ U₀ → Good q R₀ V₀ → dataDist U₀ V₀ ≤ δ →
        ∀ t ∈ Set.Icc 0 T, ∀ y b, |(Sol U₀).1 b (Fin.cons t y) - (Sol V₀).1 b (Fin.cons t y)| ≤ ε ∧
          ∀ i, |(Sol U₀).2 b i (Fin.cons t y) - (Sol V₀).2 b i (Fin.cons t y)| ≤ ε := by
  classical
  obtain ⟨T, hT, R, hR, C, -, hex⟩ := kato_local_existence (A := A) (F := F) hm hq hq2 hA hsym
    hF hR₀
  have hex' : ∀ U₀, Good q R₀ U₀ → ∃ (U : Fin n → ST d → ℝ) (P : Fin n → Fin d → ST d → ℝ),
      ForwardSol A F U₀ T U P ∧ ∃ γ : (N : ℕ) → ℝ → GS d n N, GalerkinHyp A F q U₀ T R γ ∧
        ∀ b, ∀ ε > 0, ∀ᶠ N in atTop, ∀ t ∈ Set.Icc 0 T, ∀ y,
          |fld q (γ N t) b (Fin.cons t y) - U b (Fin.cons t y)| ≤ ε ∧
          ∀ i : Fin d, |pd (fld q (γ N t) b) i.succ (Fin.cons t y) - P b i (Fin.cons t y)| ≤ ε := by
    intro U₀ ⟨hU, hUp, hE⟩
    obtain ⟨U, P, c1, c2, c3, c4, c5, c6, c7, -, -, γ, hG, hconv, -⟩ := hex U₀ hU hUp hE
    exact ⟨U, P, ⟨c1, c2, c3, c4, c5, c6, c7⟩, γ, hG, hconv⟩
  set Sol : (Fin n → ST d → ℝ) → (Fin n → ST d → ℝ) × (Fin n → Fin d → ST d → ℝ) :=
    fun U₀ => if h : Good q R₀ U₀ then ((hex' U₀ h).choose, (hex' U₀ h).choose_spec.choose)
      else (fun _ _ => 0, fun _ _ _ => 0) with hSol
  have hSpec : ∀ U₀ (h : Good q R₀ U₀), ForwardSol A F U₀ T (Sol U₀).1 (Sol U₀).2 ∧
      ∃ γ : (N : ℕ) → ℝ → GS d n N, GalerkinHyp A F q U₀ T R γ ∧
        ∀ b, ∀ ε > 0, ∀ᶠ N in atTop, ∀ t ∈ Set.Icc 0 T, ∀ y,
          |fld q (γ N t) b (Fin.cons t y) - (Sol U₀).1 b (Fin.cons t y)| ≤ ε ∧
          ∀ i : Fin d, |pd (fld q (γ N t) b) i.succ (Fin.cons t y) -
            (Sol U₀).2 b i (Fin.cons t y)| ≤ ε := by
    intro U₀ h
    have e : Sol U₀ = ((hex' U₀ h).choose, (hex' U₀ h).choose_spec.choose) := by
      simp only [hSol, dif_pos h]
    rw [e]
    exact (hex' U₀ h).choose_spec.choose_spec
  refine ⟨T, hT, Sol, fun U₀ h => (hSpec U₀ h).1, fun ε hε => ?_⟩
  obtain ⟨δ, hδ, hstab⟩ := galerkin_data_sup (A := A) (F := F) hm hq2 hA hsym hF hR hT.le
    (ε / 3) (by positivity)
  refine ⟨δ, hδ, fun U₀ V₀ hU hV hdist t ht y b => ?_⟩
  obtain ⟨-, γ, hG, hconv⟩ := hSpec U₀ hU
  obtain ⟨-, γ', hG', hconv'⟩ := hSpec V₀ hV
  have hev := (hconv b (ε / 3) (by positivity)).and (hconv' b (ε / 3) (by positivity))
  obtain ⟨N, hN1, hN2⟩ := hev.exists
  have h0 : ∑ b, ∑ k ∈ box N, (cf q (γ N 0) b k - cf q (γ' N 0) b k) ^ 2 ≤ δ := by
    rw [hG.init N, hG'.init N]
    exact (sum_cf_P0_sub_sq_le q N (fun b => (hU.1 b).continuous)
      (fun b => (hV.1 b).continuous)).trans hdist
  have hs := hstab N (γ N) (γ' N) (hG.deriv N) (hG'.deriv N) (hG.bound N) (hG'.bound N) h0 t ht
    b (Fin.cons t y)
  obtain ⟨a1, a2⟩ := hN1 t ht y
  obtain ⟨b1, b2⟩ := hN2 t ht y
  refine ⟨?_, fun i => ?_⟩
  · have := abs_sub_le ((Sol U₀).1 b (Fin.cons t y)) (fld q (γ N t) b (Fin.cons t y))
      ((Sol V₀).1 b (Fin.cons t y))
    have h2 := abs_sub_le (fld q (γ N t) b (Fin.cons t y)) (fld q (γ' N t) b (Fin.cons t y))
      ((Sol V₀).1 b (Fin.cons t y))
    rw [abs_sub_comm] at a1
    linarith [hs.1]
  · have := abs_sub_le ((Sol U₀).2 b i (Fin.cons t y))
      (pd (fld q (γ N t) b) i.succ (Fin.cons t y)) ((Sol V₀).2 b i (Fin.cons t y))
    have h2 := abs_sub_le (pd (fld q (γ N t) b) i.succ (Fin.cons t y))
      (pd (fld q (γ' N t) b) i.succ (Fin.cons t y)) ((Sol V₀).2 b i (Fin.cons t y))
    have a2' := a2 i
    rw [abs_sub_comm] at a2'
    linarith [hs.2 i, b2 i]

/-- **Kato's local existence on `(-T, T)` with continuous dependence on the data**: a two-sided
solution map (time reversal and gluing, `twoSided_of_forward`) whose forward part has the
`C⁰`/`C¹_x` stability of `kato_forward_stable` on `[0, T]`. -/
theorem kato_two_sided_stable {m q : ℕ} (hm : (d : ℝ) / 2 < m) (hq : 2 * m ≤ q)
    (hq2 : m + 2 ≤ q) (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b))
    (hsym : ∀ i a b v, A i a b v = A i b a v) (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R₀ : ℝ}
    (hR₀ : 0 ≤ R₀) :
    ∃ T > 0, ∃ Sol : (Fin n → ST d → ℝ) → (Fin n → ST d → ℝ) × (Fin n → Fin d → ST d → ℝ),
      (∀ U₀, Good q R₀ U₀ → TwoSidedSol A F U₀ T (Sol U₀).1 (Sol U₀).2) ∧
      ∀ ε > 0, ∃ δ > 0, ∀ U₀ V₀, Good q R₀ U₀ → Good q R₀ V₀ → dataDist U₀ V₀ ≤ δ →
        ∀ t ∈ Set.Icc 0 T, ∀ y b, |(Sol U₀).1 b (Fin.cons t y) - (Sol V₀).1 b (Fin.cons t y)| ≤ ε ∧
          ∀ i, |(Sol U₀).2 b i (Fin.cons t y) - (Sol V₀).2 b i (Fin.cons t y)| ≤ ε := by
  classical
  obtain ⟨T₁, hT₁, S₁, hS₁, hstab⟩ := kato_forward_stable (A := A) (F := F) hm hq hq2 hA hsym hF
    hR₀
  obtain ⟨T₂, hT₂, S₂, hS₂, -⟩ := kato_forward_stable (A := fun i a b v => -A i a b v)
    (F := fun a v => -F a v) hm hq hq2 (fun i a b => (hA i a b).neg)
    (fun i a b v => by rw [hsym]) (fun a => (hF a).neg) hR₀
  set T := min T₁ T₂ with hT
  have hTpos : 0 < T := lt_min hT₁ hT₂
  refine ⟨T, hTpos, fun U₀ => (glue (S₁ U₀).1 (S₂ U₀).1, glueP (S₁ U₀).2 (S₂ U₀).2),
    fun U₀ h => twoSided_of_forward hTpos ((hS₁ U₀ h).mono (min_le_left _ _))
      ((hS₂ U₀ h).mono (min_le_right _ _)), fun ε hε => ?_⟩
  obtain ⟨δ, hδ, h⟩ := hstab ε hε
  refine ⟨δ, hδ, fun U₀ V₀ hU hV hd t ht y b => ?_⟩
  have ht' : t ∈ Set.Icc 0 T₁ := ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
  have hc : (0 : ℝ) ≤ (Fin.cons t y : ST d) 0 := ht.1
  simp only [glue, glueP, if_pos hc]
  exact h U₀ V₀ hU hV hd t ht' y b

end Kato

/-! ### Uniqueness of two-sided solutions -/

section Unique

variable {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}

/-- **Uniqueness of classical two-sided solutions**: two two-sided solutions with the same data
coincide on `[0, t₁] × ℝ^d` for every `t₁` below both existence times (`QLSymSys.unique`, with
the Lipschitz and boundedness inputs derived from `C¹` regularity, periodicity and compactness). -/
theorem twoSided_unique (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b))
    (hsym : ∀ i a b v, A i a b v = A i b a v) (hF : ∀ a, ContDiff ℝ ∞ (F a))
    {U₀ : Fin n → ST d → ℝ} {T T' : ℝ} {U V : Fin n → ST d → ℝ} {P P' : Fin n → Fin d → ST d → ℝ}
    (hU : TwoSidedSol A F U₀ T U P) (hV : TwoSidedSol A F U₀ T' V P') {t₁ : ℝ} (ht₁ : 0 < t₁)
    (hT : t₁ < T) (hT' : t₁ < T') : ∀ x ∈ slab 0 t₁, ∀ b, U b x = V b x := by
  set δ := min T T' with hδ
  have hU' : (complexSys A F).Solves (cplx U) (-δ) δ :=
    Solves.mono (hU.solves hA hF) (by linarith [min_le_left T T']) (min_le_left _ _)
  have hV' : (complexSys A F).Solves (cplx V) (-δ) δ :=
    Solves.mono (hV.solves hA hF) (by linarith [min_le_right T T']) (min_le_right _ _)
  have ha : -δ < 0 := by have := lt_min (ht₁.trans hT) (ht₁.trans hT'); linarith
  have hb : t₁ < δ := lt_min hT hT'
  obtain ⟨B1, hB1⟩ := exists_bound_slab hU'.smooth.continuousOn hU'.per ha hb
  obtain ⟨B2, hB2⟩ := exists_bound_slab hV'.smooth.continuousOn hV'.per ha hb
  set ρ := max (max B1 B2) 0 with hρ
  set Ω : Set (Fin n → ℂ) := Metric.closedBall 0 ρ with hΩ
  have hUΩ : ∀ x ∈ slab 0 t₁, cplx U x ∈ Ω := fun x hx => by
    rw [hΩ, mem_closedBall_zero_iff]
    exact (hB1 x hx).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hVΩ : ∀ x ∈ slab 0 t₁, cplx V x ∈ Ω := fun x hx => by
    rw [hΩ, mem_closedBall_zero_iff]
    exact (hB2 x hx).trans ((le_max_right _ _).trans (le_max_left _ _))
  set Φ : (Fin n ⊕ (Fin d × Fin n × Fin n)) → (Fin n → ℝ) → ℝ :=
    fun k => Sum.elim (fun a => F a) (fun p => A p.1 p.2.1 p.2.2) k with hΦ
  have hΦs : ∀ k, ContDiff ℝ ∞ (Φ k) := by
    intro k; cases k with
    | inl a => exact hF a
    | inr p => exact hA p.1 p.2.1 p.2.2
  obtain ⟨M, hM0, hM⟩ := exists_coeff_bounds hΦs ρ
  have hre : ∀ v ∈ Ω, ‖(fun c => (v c).re)‖ ≤ ρ := fun v hv =>
    (norm_re_le v).trans (by rwa [hΩ, mem_closedBall_zero_iff] at hv)
  have hAlip : ∀ j, LipschitzOnWith M.toNNReal ((complexSys A F).A j) Ω := by
    intro j
    refine LipschitzOnWith.of_dist_le_mul fun v hv w hw => ?_
    rw [Real.coe_toNNReal _ hM0]
    refine (dist_pi_le_iff (by positivity)).2 fun i => (dist_pi_le_iff (by positivity)).2
      fun k => ?_
    simp only [complexSys]
    rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    refine ((hM (Sum.inr (j, i, k)) _ _ (hre v hv) (hre w hw)).2.2).trans ?_
    rw [dist_eq_norm]
    exact mul_le_mul_of_nonneg_left (norm_re_sub_le v w) hM0
  have hAbd : ∀ j, ∀ v ∈ Ω, ‖(complexSys A F).A j v‖ ≤ M := by
    intro j v hv
    refine (pi_norm_le_iff_of_nonneg hM0).2 fun i => (pi_norm_le_iff_of_nonneg hM0).2
      fun k => ?_
    simp only [complexSys, Complex.norm_real, Real.norm_eq_abs]
    exact (hM (Sum.inr (j, i, k)) _ _ (hre v hv) (hre v hv)).1
  have hFlip : LipschitzOnWith M.toNNReal (complexSys A F).F Ω := by
    refine LipschitzOnWith.of_dist_le_mul fun v hv w hw => ?_
    rw [Real.coe_toNNReal _ hM0]
    refine (dist_pi_le_iff (by positivity)).2 fun b => ?_
    simp only [complexSys]
    rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    refine ((hM (Sum.inl b) _ _ (hre v hv) (hre w hw)).2.2).trans ?_
    rw [dist_eq_norm]
    exact mul_le_mul_of_nonneg_left (norm_re_sub_le v w) hM0
  obtain ⟨LU, hLU⟩ := exists_lipschitzOnWith_slab hU'.smooth hU'.per ha hb
  have hpdc : ∀ j : Fin d, ∃ C, ∀ x ∈ slab 0 t₁, ‖pd (cplx V) j.succ x‖ ≤ C := by
    intro j
    have hc : ContinuousOn (fun x => pd (cplx V) j.succ x) (openSlab (-δ) δ) :=
      (hV'.smooth.continuousOn_fderiv_of_isOpen (isOpen_openSlab _ _) le_rfl).clm_apply
        continuousOn_const
    have hp : IsSPeriodic (fun x => pd (cplx V) j.succ x) := fun k x => by
      simp only [SobolevOpen.pd, isSPeriodic_fderiv hV'.per k x]
    exact exists_bound_slab hc hp ha hb
  choose Cj hCj using hpdc
  set MV := ∑ j, max (Cj j) 0 with hMV
  have hMV0 : 0 ≤ MV := Finset.sum_nonneg fun j _ => le_max_right _ _
  have hVd : ∀ j : Fin d, ∀ x ∈ slab 0 t₁, ‖pd (cplx V) j.succ x‖ ≤ MV := fun j x hx =>
    (hCj j x hx).trans ((le_max_left _ _).trans (Finset.single_le_sum
      (f := fun j => max (Cj j) 0) (fun j _ => le_max_right _ _) (Finset.mem_univ j)))
  have h0 : ∀ y : Fin d → ℝ, cplx U (Fin.cons 0 y) = cplx V (Fin.cons 0 y) := fun y => by
    funext b
    simp [cplx, hU.init b y, hV.init b y]
  have huniq := SymHypUniqueness.QLSymSys.unique (complexSys A F) ha ht₁ hb hU' hV' hUΩ hVΩ
    (complexSys_herm hsym) hAlip hAbd hFlip hLU hMV0 hVd h0
  intro x hx b
  have := congrFun (huniq x hx) b
  simpa [cplx] using this

/-- On the common slab the spatial derivatives of two coinciding two-sided solutions agree. -/
theorem twoSided_P_eq {U₀ U₀' : Fin n → ST d → ℝ} {T T' : ℝ} {U V : Fin n → ST d → ℝ}
    {P P' : Fin n → Fin d → ST d → ℝ} (hU : TwoSidedSol A F U₀ T U P)
    (hV : TwoSidedSol A F U₀' T' V P') {t₁ : ℝ} (heq : ∀ x ∈ slab 0 t₁, ∀ b, U b x = V b x) :
    ∀ x ∈ slab 0 t₁, ∀ b i, P b i x = P' b i x := by
  intro x hx b i
  have e : (fun s : ℝ => U b (x + s • ev i.succ)) = fun s => V b (x + s • ev i.succ) := by
    funext s
    refine heq _ ?_ b
    show (x + s • ev i.succ) 0 ∈ Set.Icc 0 t₁
    rw [line_zero_succ]; exact hx
  have h1 := hU.space b i x
  rw [e] at h1
  exact h1.unique (hV.space b i x)

end Unique

/-! ### Physical identification through the analytic core -/

section Physical

variable {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}
  {ι : Type*}

/-- The first jet `(∂_tU, ∂_xU)` of a solution in terms of the state `u = U(x)` and the spatial
derivatives `p = ∂_xU(x)`: `∂_tU = F(u) - Σ_i A^i(u) p_i` (the symmetric system). -/
def jetOf (A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ) (F : Fin n → (Fin n → ℝ) → ℝ)
    (u : Fin n → ℝ) (p : Fin n → Fin d → ℝ) : Fin (d + 1) → Fin n → ℝ :=
  fun μ b => Fin.cases (F b u - ∑ i, ∑ b', A i b b' u * p b' i) (fun i => p b i) μ

theorem continuous_jetOf (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a)) :
    Continuous fun z : (Fin n → ℝ) × (Fin n → Fin d → ℝ) => jetOf A F z.1 z.2 := by
  refine continuous_pi fun μ => continuous_pi fun b => ?_
  induction μ using Fin.cases with
  | zero =>
    simp only [jetOf, Fin.cases_zero]
    exact ((hF b).continuous.comp continuous_fst).sub (continuous_finsetSum _ fun i _ =>
      continuous_finsetSum _ fun b' _ => ((hA i b b').continuous.comp continuous_fst).mul
        ((continuous_apply i).comp ((continuous_apply b').comp continuous_snd)))
  | succ i =>
    simp only [jetOf, Fin.cases_succ]
    exact (continuous_apply i).comp ((continuous_apply b).comp continuous_snd)

theorem solPartial_eq_jetOf (U : Fin n → ST d → ℝ) (P : Fin n → Fin d → ST d → ℝ) (b : Fin n)
    (μ : Fin (d + 1)) (x : ST d) :
    solPartial A F U P b μ x = jetOf A F (fun c => U c x) (fun c i => P c i x) μ b := by
  induction μ using Fin.cases with
  | zero => simp [solPartial, jetOf, genP]
  | succ i => simp [solPartial, jetOf]

/-- **Physical identities on a slab**: pointwise first-jet identities
`Φ_j(U(x), ∂U(x)) = 0` for `x ∈ [0, t₁] × ℝ^d` (`∂U = (∂_tU, ∂_1U, …, ∂_dU)`).  The defining-jet
identities, the Einstein and matter residuals and the Gauss and harmonic constraints of
`lem:generated-physical-identification` are of this form on the actual-jet state. -/
def PhysicalOn (Φ : ι → (Fin n → ℝ) × (Fin (d + 1) → Fin n → ℝ) → ℝ) (U : Fin n → ST d → ℝ)
    (t₁ : ℝ) : Prop :=
  ∀ x ∈ slab 0 t₁, ∀ j, Φ j (fun b => U b x, fun μ b => pd (U b) μ x) = 0

/-- **The analytic-core / physical-Cauchy input of `lem:generated-physical-identification` with
its continuation clause** (`ass:constrained-initial-solver`, last two sentences: "A
constraint-compatible analytic core with the same gauge completion is available for the
physical-identification argument.  On this core the constrained physical Cauchy problem admits
locally unique analytic solutions with continuation controlled by the declared Sobolev bounds and
field-chart margins").  `Constrained` is the constrained Sobolev class, `Core` the analytic core,
`Φ` the physical first-jet identities.  Fields:
* `core_smooth` — core data are smooth periodic;
* `approx` — the core is available for the argument: every constrained datum is an `L²` limit of
  core data with a uniform `H^q` bound (the manuscript obtains these approximants from
  Fourier-polynomial seeds and the exact contraction of `prop:generated-initial`);
* `germ` — **continuation controlled by the Sobolev bound**: for every radius `R₀` there is a
  common `ε > 0` such that every core datum with `‖W‖_{H^q} ≤ R₀` has a physical solution on
  `(-ε, ε)` (`PhysicalOn` on `[0, ε/2]`) whose state solves the symmetric system (the latter by
  `prop:actual-jet-writer`).
This strengthens `SymHypUniqueness.AnalyticGermExistence` (which only gives some `ε` per datum);
it is the named Cauchy–Kovalevskaya gap, not proved here. -/
structure AnalyticCoreContinuation (A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ)
    (F : Fin n → (Fin n → ℝ) → ℝ) (q : ℕ) (Constrained Core : (Fin n → ST d → ℝ) → Prop)
    (Φ : ι → (Fin n → ℝ) × (Fin (d + 1) → Fin n → ℝ) → ℝ) : Prop where
  core_smooth : ∀ W, Core W → (∀ b, ContDiff ℝ ∞ (W b)) ∧ ∀ b, IsSPeriodic (W b)
  approx : ∀ U₀, Constrained U₀ → ∃ W : ℕ → Fin n → ST d → ℝ, (∀ k, Core (W k)) ∧
    (∀ k, energyQ q (W k) 0 ≤ energyQ q U₀ 0 + 1) ∧
    Tendsto (fun k => dataDist (W k) U₀) atTop (𝓝 0)
  germ : ∀ R₀ : ℝ, 0 ≤ R₀ → ∃ ε > 0, ∀ W, Core W → energyQ q W 0 ≤ R₀ ^ 2 →
    ∃ (V : Fin n → ST d → ℝ) (P : Fin n → Fin d → ST d → ℝ), TwoSidedSol A F W ε V P ∧
      PhysicalOn Φ V (ε / 2)

/-- **Physical identification of the symmetric extension** (`lem:generated-physical-
identification`, Sobolev-data case, by approximation from the analytic core).  Let `m > d/2`,
`q ≥ 2m`, `q ≥ m + 2`, `A^i` smooth real symmetric, `F` smooth, `Φ_j` continuous physical
first-jet identities, `R₀ ≥ 0`.  There is `T > 0` (depending only on `R₀`) such that: under the
named input `AnalyticCoreContinuation` there is `t₁ > 0` such that for every constrained datum
`U₀` (smooth periodic, `‖U₀‖_{H^q} ≤ R₀`, **not** assumed in the core) the independent symmetric
system has a two-sided Kato solution on `(-T, T)`, and on `[0, t₁]` its state satisfies all the
physical identities.  Proof: core approximants `W_k → U₀`; their Kato solutions coincide on the
common interval `[0, t₁]` with their physical germs (uniqueness `twoSided_unique`, the interval
being uniform by the continuation clause); the solutions converge in `C⁰` with their first
spatial derivatives (`kato_two_sided_stable`), hence their first jets converge, and the
continuous identities pass to the limit. -/
theorem kato_physical_identification {m q : ℕ} (hm : (d : ℝ) / 2 < m) (hq : 2 * m ≤ q)
    (hq2 : m + 2 ≤ q) (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b))
    (hsym : ∀ i a b v, A i a b v = A i b a v) (hF : ∀ a, ContDiff ℝ ∞ (F a))
    {Φ : ι → (Fin n → ℝ) × (Fin (d + 1) → Fin n → ℝ) → ℝ} (hΦ : ∀ j, Continuous (Φ j))
    {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ T > 0, ∀ Constrained Core : (Fin n → ST d → ℝ) → Prop,
      AnalyticCoreContinuation A F q Constrained Core Φ →
      ∃ t₁ > 0, ∀ U₀ : Fin n → ST d → ℝ, Constrained U₀ → (∀ b, ContDiff ℝ ∞ (U₀ b)) →
        (∀ b, IsSPeriodic (U₀ b)) → energyQ q U₀ 0 ≤ R₀ ^ 2 →
        ∃ (U : Fin n → ST d → ℝ) (P : Fin n → Fin d → ST d → ℝ),
          TwoSidedSol A F U₀ T U P ∧ PhysicalOn Φ U t₁ := by
  set R' := R₀ + 1 with hR'
  have hR'0 : 0 ≤ R' := by linarith
  obtain ⟨T, hT, Sol, hSol, hstab⟩ := kato_two_sided_stable (A := A) (F := F) hm hq hq2 hA hsym
    hF hR'0
  refine ⟨T, hT, fun Constrained Core hass => ?_⟩
  obtain ⟨εg, hεg, hgerm⟩ := hass.germ R' hR'0
  set t₁ := min T εg / 2 with ht₁
  have hmin := lt_min hT hεg
  have ht₁0 : 0 < t₁ := by positivity
  have ht₁T : t₁ < T := by have := min_le_left T εg; linarith
  have ht₁g : t₁ < εg := by have := min_le_right T εg; linarith
  have ht₁g2 : t₁ ≤ εg / 2 := by have := min_le_right T εg; linarith
  refine ⟨t₁, ht₁0, fun U₀ hC hU hUp hE => ?_⟩
  have hgood : Good q R' U₀ := ⟨hU, hUp, hE.trans (by nlinarith)⟩
  refine ⟨(Sol U₀).1, (Sol U₀).2, hSol U₀ hgood, ?_⟩
  obtain ⟨W, hWcore, hWE, hWlim⟩ := hass.approx U₀ hC
  have hWgood : ∀ k, Good q R' (W k) := fun k =>
    ⟨(hass.core_smooth _ (hWcore k)).1, (hass.core_smooth _ (hWcore k)).2,
      (hWE k).trans (by nlinarith)⟩
  -- the approximants are physical on `[0, t₁]` (as jets)
  have happrox : ∀ k, ∀ x ∈ slab 0 t₁, ∀ j, Φ j (fun b => (Sol (W k)).1 b x,
      jetOf A F (fun c => (Sol (W k)).1 c x) (fun c i => (Sol (W k)).2 c i x)) = 0 := by
    intro k x hx j
    obtain ⟨V, P', hV, hphys⟩ := hgerm (W k) (hWcore k) (hWgood k).2.2
    have hS := hSol (W k) (hWgood k)
    have heq := twoSided_unique hA hsym hF hS hV ht₁0 ht₁T ht₁g
    have hPeq := twoSided_P_eq hS hV heq
    have hxo : x ∈ openSlab (-εg) εg := slab_subset_openSlab (by linarith) ht₁g hx
    have h1 := hphys x ⟨hx.1, hx.2.trans ht₁g2⟩ j
    have hpdV : (fun μ b => pd (V b) μ x) =
        jetOf A F (fun c => V c x) (fun c i => P' c i x) := by
      funext μ b
      rw [hV.pd_eq hA hF b hxo μ, solPartial_eq_jetOf]
    rw [hpdV] at h1
    have e1 : (fun c => (Sol (W k)).1 c x) = fun c => V c x := funext fun c => heq x hx c
    have e2 : (fun c i => (Sol (W k)).2 c i x) = fun c i => P' c i x :=
      funext fun c => funext fun i => hPeq x hx c i
    rw [e1, e2]
    exact h1
  -- convergence of the states and spatial derivatives at each point of the slab
  have hconv : ∀ x ∈ slab 0 t₁, Tendsto (fun k => ((fun c => (Sol (W k)).1 c x),
      (fun c i => (Sol (W k)).2 c i x))) atTop
      (𝓝 ((fun c => (Sol U₀).1 c x), (fun c i => (Sol U₀).2 c i x))) := by
    intro x hx
    have hxT : x 0 ∈ Set.Icc 0 T := ⟨hx.1, hx.2.trans ht₁T.le⟩
    have key : ∀ ε > 0, ∀ᶠ k in atTop, ∀ c, |(Sol (W k)).1 c x - (Sol U₀).1 c x| ≤ ε ∧
        ∀ i, |(Sol (W k)).2 c i x - (Sol U₀).2 c i x| ≤ ε := by
      intro ε hε
      obtain ⟨δ, hδ, h⟩ := hstab ε hε
      filter_upwards [(hWlim.eventually (Iic_mem_nhds hδ))] with k hk c
      have := h (W k) U₀ (hWgood k) hgood hk (x 0) hxT (Fin.tail x) c
      rwa [Fin.cons_self_tail] at this
    refine Tendsto.prodMk_nhds (tendsto_pi_nhds.2 fun c => ?_)
      (tendsto_pi_nhds.2 fun c => tendsto_pi_nhds.2 fun i => ?_)
    · rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨K, hK⟩ := (key (ε / 2) (by positivity)).exists_forall_of_atTop
      refine ⟨K, fun k hk => ?_⟩
      rw [Real.dist_eq]; exact (hK k hk c).1.trans_lt (by linarith)
    · rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨K, hK⟩ := (key (ε / 2) (by positivity)).exists_forall_of_atTop
      refine ⟨K, fun k hk => ?_⟩
      rw [Real.dist_eq]; exact ((hK k hk c).2 i).trans_lt (by linarith)
  -- pass the identities to the limit
  intro x hx j
  have hxo : x ∈ openSlab (-T) T := slab_subset_openSlab (by linarith) ht₁T hx
  have hpd : (fun μ b => pd ((Sol U₀).1 b) μ x) =
      jetOf A F (fun c => (Sol U₀).1 c x) (fun c i => (Sol U₀).2 c i x) := by
    funext μ b
    rw [(hSol U₀ hgood).pd_eq hA hF b hxo μ, solPartial_eq_jetOf]
  rw [hpd]
  have hcontΨ : Continuous fun z : (Fin n → ℝ) × (Fin n → Fin d → ℝ) =>
      Φ j (z.1, jetOf A F z.1 z.2) :=
    (hΦ j).comp (continuous_fst.prodMk (continuous_jetOf hA hF))
  have hlim := (hcontΨ.tendsto _).comp (hconv x hx)
  have hzero : (fun k => Φ j ((fun c => (Sol (W k)).1 c x),
      jetOf A F (fun c => (Sol (W k)).1 c x) (fun c i => (Sol (W k)).2 c i x))) = fun _ => 0 :=
    funext fun k => happrox k x hx j
  have h2 : Tendsto (fun k => Φ j ((fun c => (Sol (W k)).1 c x),
      jetOf A F (fun c => (Sol (W k)).1 c x) (fun c i => (Sol (W k)).2 c i x))) atTop
      (𝓝 (Φ j ((fun c => (Sol U₀).1 c x),
        jetOf A F (fun c => (Sol U₀).1 c x) (fun c i => (Sol U₀).2 c i x)))) := hlim
  rw [hzero] at h2
  exact tendsto_nhds_unique h2 tendsto_const_nhds

end Physical

/-! ### Non-vacuity -/

/-- The zero field is a two-sided solution with zero data when `F(0) = 0`. -/
theorem zero_twoSided {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ}
    {F : Fin n → (Fin n → ℝ) → ℝ} (hF0 : ∀ b, F b 0 = 0) (T : ℝ) :
    TwoSidedSol A F (fun _ _ => 0) T (fun _ _ => 0) (fun _ _ _ => 0) := by
  refine ⟨fun _ => continuous_const, fun _ _ => continuous_const, fun _ _ _ => rfl,
    fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ _ => hasDerivAt_const _ _, fun b t _ y => ?_⟩
  have h0 : genP A F (fun _ _ => 0) (fun _ _ _ => 0) b (Fin.cons t y) = 0 := by
    simp only [genP, mul_zero, Finset.sum_const_zero, sub_zero]
    exact hF0 b
  rw [h0]
  exact hasDerivAt_const _ _

theorem dataDist_self (U₀ : Fin n → ST d → ℝ) : dataDist U₀ U₀ = 0 := by
  simp [dataDist, sint_const]

/-- **Non-vacuity of `kato_physical_identification`**: for the symmetric hyperbolic system
`∂_tU + σ₁∂_1U = -U` on `𝕋³` (`m = 2`, `q = 4`), the constrained class and the analytic core
`{0}`, and the physical identity `∂_tu₀ + u₀ = 0`, the named input `AnalyticCoreContinuation`
holds (zero germ) and the theorem applies to the zero datum. -/
example : ∃ T > 0, ∃ t₁ > 0, ∃ (U : Fin 2 → ST 3 → ℝ) (P : Fin 2 → Fin 3 → ST 3 → ℝ),
    TwoSidedSol exampleA (fun a v => -v a) (fun _ _ => 0) T U P ∧
    PhysicalOn (ι := Unit) (fun _ z => z.2 0 0 + z.1 0) U t₁ := by
  have hF0 : ∀ b : Fin 2, (fun (a : Fin 2) (v : Fin 2 → ℝ) => -v a) b 0 = 0 := fun b => by simp
  obtain ⟨T, hT, h⟩ := kato_physical_identification (d := 3) (n := 2) (m := 2) (q := 4)
    (by norm_num) le_rfl le_rfl (A := exampleA) (F := fun a v => -v a)
    (fun _ _ _ => by unfold exampleA; exact contDiff_const)
    (fun i a b v => by
      unfold exampleA
      by_cases h : a = b
      · subst h; rfl
      · simp [h, Ne.symm h])
    (fun a => (contDiff_apply ℝ ℝ a).neg) (ι := Unit) (Φ := fun _ z => z.2 0 0 + z.1 0)
    (fun _ => ((continuous_apply 0).comp ((continuous_apply 0).comp continuous_snd)).add
      ((continuous_apply 0).comp continuous_fst)) zero_le_one
  have hass : AnalyticCoreContinuation exampleA (fun a v => -v a) 4 (fun U₀ => U₀ = fun _ _ => 0)
      (fun U₀ => U₀ = fun _ _ => 0) (ι := Unit) (fun _ z => z.2 0 0 + z.1 0) := by
    refine ⟨fun W hW => ?_, fun U₀ hU₀ => ?_, fun R₀ _ => ⟨1, one_pos, fun W hW _ => ?_⟩⟩
    · subst hW; exact ⟨fun _ => contDiff_const, fun _ _ _ => rfl⟩
    · subst hU₀
      refine ⟨fun _ => fun _ _ => 0, fun _ => rfl, fun _ => le_add_of_nonneg_right zero_le_one, ?_⟩
      simp only [dataDist_self]; exact tendsto_const_nhds
    · subst hW
      refine ⟨fun _ _ => 0, fun _ _ _ => 0, zero_twoSided hF0 1, fun x _ _ => ?_⟩
      simp [SobolevOpen.pd]
  obtain ⟨t₁, ht₁, h'⟩ := h _ _ hass
  obtain ⟨U, P, hsol, hphys⟩ := h' (fun _ _ => 0) rfl (fun _ => contDiff_const) (fun _ _ _ => rfl)
    (by rw [energyQ_zero]; norm_num)
  exact ⟨T, hT, t₁, ht₁, U, P, hsol, hphys⟩

end RenewalGeometry.KatoStab
