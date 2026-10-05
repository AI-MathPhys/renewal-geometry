/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.SlabCoefficientCalculus

/-!
# Derivative-counted forcing bound (`lem:actual-jet-complete-forcing`)

Einstein–Standard-Model action-closure manuscript, `lem:actual-jet-complete-forcing`
(`eq:actual-jet-complete-forcing`), on the slices of `[0, T] × 𝕋^d` (classical squared `H^k`
norms `Q_k` of `Continuum/SlabSobolevAlgebra.lean`; `k ≥ 2m - 1`, `m > d/2`, i.e. `k ≥ 3` on
`𝕋³`, which covers the paper's `k ≥ 4`).

The residual and gauge-forcing part of `eq:actual-jet-writer` has the form
`𝓕_err = Σ_i b_i R_{B,i} + Σ_κ Σ_j q_{κ,j} ∂_jR_{D,κ} + Σ_l (c_l C^l + c⁰_l ∂_tC^l + Σ_j c^j_l ∂_jC^l)`
with zeroth-order coefficients `b, q, c, c⁰, cʲ` (smooth functions of the actual-jet state, bounded
in `H^k` on the actual-jet ball).

* `Q_sum_mul_le` — `Q_k(Σ_τ b_τ f_τ) ≤ |s| C_alg M Σ_τ Q_k(f_τ)` when every `Q_k(b_τ) ≤ M`
  (the `H^k` algebra, `SlabSobAlg.Q_mul_le`).
* **`forcing_bound`** (`eq:actual-jet-complete-forcing`, squared form) —
  `Q_k(𝓕_err) ≤ C_M (Σ Q_k(R_B) + Σ Q_{k+1}(R_D) + Σ Q_{k+1}(C) + Σ Q_k(∂_tC))`: the spatially
  differentiated Dirac residual and harmonic defect cost one extra derivative, the
  undifferentiated residuals and `∂_tC` none (`SlabSobAlg.Q_pd_le`, `Q_mono`).
* `forcing_bound_norm` — the same in the norm form of the paper,
  `‖𝓕_err‖_{H^k} ≤ C (‖R_B‖_{H^k} + ‖R_D‖_{H^{k+1}} + ‖C‖_{H^{k+1}} + ‖∂_tC‖_{H^k})`, with
  `‖F‖_{H^k} = √(Σ_i Q_k(F_i))` for families.
* `coeff_bound_poly` — the coefficient hypothesis holds for coefficient fields that are polynomial
  in the state fields (`SlabSobAlg.evalF_lip`, Moser for polynomials), e.g. the gauge-forcing
  coefficients `𝒥_C^μ = -N(δ g + δ g)` of `Gravity/ActualJetWriterRows.lean`.
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.ActualJetForcing

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg

set_option linter.unusedSectionVars false

variable {d : ℕ}

/-- **Products with `H^k`-bounded coefficients:** if `Q_k(b_τ) ≤ M` for all `τ ∈ s`, then
`Q_k(Σ_{τ∈s} b_τf_τ) ≤ |s| · C_alg · M · Σ_τ Q_k(f_τ)`. -/
theorem Q_sum_mul_le {k m : ℕ} (hk : 2 * m ≤ k + 1) {CS : ℝ} (hCS : 0 ≤ CS)
    (hsup : ∀ f : ST d → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin d → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q m f t)
    {κ : Type*} (s : Finset κ) {b f : κ → ST d → ℝ} (hb : ∀ i, ContDiff ℝ ∞ (b i))
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hpb : ∀ i, IsSPeriodic (b i)) (hpf : ∀ i, IsSPeriodic (f i))
    {M t : ℝ} (hM : ∀ i ∈ s, Q k (b i) t ≤ M) :
    Q k (fun x => ∑ i ∈ s, b i x * f i x) t ≤
      s.card * (algC d k CS * M) * ∑ i ∈ s, Q k (f i) t := by
  have hprod : ∀ i, ContDiff ℝ ∞ (fun x => b i x * f i x) := fun i => (hb i).mul (hf i)
  refine (Q_sum_le k s hprod t).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  refine (Q_mul_le hk hCS hsup (hb i) (hf i) (hpb i) (hpf i) t).trans ?_
  have hC := algC_nonneg (d := d) k hCS
  have hQ := Q_nonneg k (f i) t
  calc algC d k CS * Q k (b i) t * Q k (f i) t ≤ algC d k CS * M * Q k (f i) t := by
        gcongr; exact hM i hi
    _ = _ := rfl

/-- The residual and gauge-forcing part of `eq:actual-jet-writer`:
`Σ_i b_iR_{B,i} + Σ_κ Σ_j q_{κj}∂_jR_{D,κ} + Σ_l (c_lC^l + c⁰_l∂_tC^l + Σ_j cʲ_l∂_jC^l)`. -/
def forcingErr {ι κ θ : Type*} [Fintype ι] [Fintype κ] [Fintype θ] (b RB : ι → ST d → ℝ)
    (q : κ → Fin d → ST d → ℝ) (RD : κ → ST d → ℝ) (c c0 : θ → ST d → ℝ)
    (cj : θ → Fin d → ST d → ℝ) (C dtC : θ → ST d → ℝ) (x : ST d) : ℝ :=
  (∑ i, b i x * RB i x + ∑ p : κ × Fin d, q p.1 p.2 x * pd (RD p.1) p.2.succ x) +
    (∑ l, c l x * C l x + ∑ l, c0 l x * dtC l x +
      ∑ p : θ × Fin d, cj p.1 p.2 x * pd (C p.1) p.2.succ x)

theorem Q_add3_le (k : ℕ) {f g h : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hh : ContDiff ℝ ∞ h) (t : ℝ) :
    Q k (fun x => f x + g x + h x) t ≤ 4 * Q k f t + 4 * Q k g t + 2 * Q k h t := by
  have h1 := Q_add_le k (hf.add hg) hh t
  have h2 := Q_add_le k hf hg t
  have : Q k (fun x => f x + g x) t ≤ 2 * Q k f t + 2 * Q k g t := h2
  linarith

/-- **`eq:actual-jet-complete-forcing`** (squared form).  For smooth periodic coefficients
bounded in `H^k` by `M` and smooth periodic residuals / harmonic defect, with
`k ≥ 2m - 1` (`m > d/2`):
`Q_k(𝓕_err) ≤ C_M (Σ_i Q_k(R_{B,i}) + Σ_κ Q_{k+1}(R_{D,κ}) + Σ_l Q_{k+1}(C^l) + Σ_l Q_k(∂_tC^l))`
with `C_M = 8 C_alg M (|ι| + |κ|d² + |λ|(2 + d²))`. -/
theorem forcing_bound {k m : ℕ} (hk : 2 * m ≤ k + 1) {CS : ℝ} (hCS : 0 ≤ CS)
    (hsup : ∀ f : ST d → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin d → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q m f t)
    {ι κ θ : Type*} [Fintype ι] [Fintype κ] [Fintype θ] {b RB : ι → ST d → ℝ}
    {q : κ → Fin d → ST d → ℝ} {RD : κ → ST d → ℝ} {c c0 : θ → ST d → ℝ}
    {cj : θ → Fin d → ST d → ℝ} {C dtC : θ → ST d → ℝ}
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (hRB : ∀ i, ContDiff ℝ ∞ (RB i))
    (hq : ∀ p j, ContDiff ℝ ∞ (q p j)) (hRD : ∀ p, ContDiff ℝ ∞ (RD p))
    (hc : ∀ l, ContDiff ℝ ∞ (c l)) (hc0 : ∀ l, ContDiff ℝ ∞ (c0 l))
    (hcj : ∀ l j, ContDiff ℝ ∞ (cj l j)) (hC : ∀ l, ContDiff ℝ ∞ (C l))
    (hdtC : ∀ l, ContDiff ℝ ∞ (dtC l))
    (pb : ∀ i, IsSPeriodic (b i)) (pRB : ∀ i, IsSPeriodic (RB i))
    (pq : ∀ p j, IsSPeriodic (q p j)) (pRD : ∀ p, IsSPeriodic (RD p))
    (pc : ∀ l, IsSPeriodic (c l)) (pc0 : ∀ l, IsSPeriodic (c0 l))
    (pcj : ∀ l j, IsSPeriodic (cj l j)) (pC : ∀ l, IsSPeriodic (C l))
    (pdtC : ∀ l, IsSPeriodic (dtC l))
    {M t : ℝ} (hM0 : 0 ≤ M) (hMb : ∀ i, Q k (b i) t ≤ M) (hMq : ∀ p j, Q k (q p j) t ≤ M)
    (hMc : ∀ l, Q k (c l) t ≤ M) (hMc0 : ∀ l, Q k (c0 l) t ≤ M)
    (hMcj : ∀ l j, Q k (cj l j) t ≤ M) :
    Q k (forcingErr b RB q RD c c0 cj C dtC) t ≤
      8 * algC d k CS * M * ((Fintype.card ι + Fintype.card κ * d ^ 2 +
          Fintype.card θ * (2 + d ^ 2)) : ℝ) *
        (∑ i, Q k (RB i) t + ∑ p, Q (k + 1) (RD p) t + ∑ l, Q (k + 1) (C l) t +
          ∑ l, Q k (dtC l) t) := by
  set Ca := algC d k CS with hCa
  have hCa0 : 0 ≤ Ca := algC_nonneg k hCS
  -- smoothness of the pieces
  have sB : ContDiff ℝ ∞ (fun x => ∑ i, b i x * RB i x) :=
    ContDiff.sum fun i _ => (hb i).mul (hRB i)
  have sD : ContDiff ℝ ∞ (fun x => ∑ p : κ × Fin d, q p.1 p.2 x * pd (RD p.1) p.2.succ x) :=
    ContDiff.sum fun p _ => (hq p.1 p.2).mul (contDiff_pd_top (hRD p.1) _)
  have sC1 : ContDiff ℝ ∞ (fun x => ∑ l, c l x * C l x) :=
    ContDiff.sum fun l _ => (hc l).mul (hC l)
  have sC2 : ContDiff ℝ ∞ (fun x => ∑ l, c0 l x * dtC l x) :=
    ContDiff.sum fun l _ => (hc0 l).mul (hdtC l)
  have sC3 : ContDiff ℝ ∞ (fun x => ∑ p : θ × Fin d, cj p.1 p.2 x * pd (C p.1) p.2.succ x) :=
    ContDiff.sum fun p _ => (hcj p.1 p.2).mul (contDiff_pd_top (hC p.1) _)
  -- the five product sums
  have eB := Q_sum_mul_le hk hCS hsup Finset.univ hb hRB pb pRB (M := M) (t := t)
    (fun i _ => hMb i)
  have eD := Q_sum_mul_le hk hCS hsup (Finset.univ : Finset (κ × Fin d))
    (b := fun p => q p.1 p.2) (f := fun p => pd (RD p.1) p.2.succ)
    (fun p => hq p.1 p.2) (fun p => contDiff_pd_top (hRD p.1) _) (fun p => pq p.1 p.2)
    (fun p => isSPeriodic_pd (pRD p.1) _) (M := M) (t := t) (fun p _ => hMq p.1 p.2)
  have eC1 := Q_sum_mul_le hk hCS hsup Finset.univ hc hC pc pC (M := M) (t := t)
    (fun l _ => hMc l)
  have eC2 := Q_sum_mul_le hk hCS hsup Finset.univ hc0 hdtC pc0 pdtC (M := M) (t := t)
    (fun l _ => hMc0 l)
  have eC3 := Q_sum_mul_le hk hCS hsup (Finset.univ : Finset (θ × Fin d))
    (b := fun p => cj p.1 p.2) (f := fun p => pd (C p.1) p.2.succ)
    (fun p => hcj p.1 p.2) (fun p => contDiff_pd_top (hC p.1) _) (fun p => pcj p.1 p.2)
    (fun p => isSPeriodic_pd (pC p.1) _) (M := M) (t := t) (fun p _ => hMcj p.1 p.2)
  -- derivative counting
  have dD : ∑ p : κ × Fin d, Q k (pd (RD p.1) p.2.succ) t ≤ d * ∑ p, Q (k + 1) (RD p) t := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_le_sum fun p _ => ?_
    calc ∑ j : Fin d, Q k (pd (RD p) j.succ) t ≤ ∑ _j : Fin d, Q (k + 1) (RD p) t :=
          Finset.sum_le_sum fun j _ => Q_pd_le j (RD p) t
      _ = d * Q (k + 1) (RD p) t := by simp
  have dC3 : ∑ p : θ × Fin d, Q k (pd (C p.1) p.2.succ) t ≤ d * ∑ l, Q (k + 1) (C l) t := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_le_sum fun l _ => ?_
    calc ∑ j : Fin d, Q k (pd (C l) j.succ) t ≤ ∑ _j : Fin d, Q (k + 1) (C l) t :=
          Finset.sum_le_sum fun j _ => Q_pd_le j (C l) t
      _ = d * Q (k + 1) (C l) t := by simp
  have dC1 : ∑ l, Q k (C l) t ≤ ∑ l, Q (k + 1) (C l) t :=
    Finset.sum_le_sum fun l _ => Q_mono (Nat.le_succ k) _ t
  -- nonnegativity
  set SB := ∑ i, Q k (RB i) t
  set SD := ∑ p, Q (k + 1) (RD p) t
  set SC := ∑ l, Q (k + 1) (C l) t
  set ST' := ∑ l, Q k (dtC l) t
  have nB : 0 ≤ SB := Finset.sum_nonneg fun _ _ => Q_nonneg _ _ _
  have nD : 0 ≤ SD := Finset.sum_nonneg fun _ _ => Q_nonneg _ _ _
  have nC : 0 ≤ SC := Finset.sum_nonneg fun _ _ => Q_nonneg _ _ _
  have nT : 0 ≤ ST' := Finset.sum_nonneg fun _ _ => Q_nonneg _ _ _
  have nCaM : 0 ≤ Ca * M := mul_nonneg hCa0 hM0
  have nι : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have nκ : (0 : ℝ) ≤ Fintype.card κ := Nat.cast_nonneg _
  have nθ : (0 : ℝ) ≤ Fintype.card θ := Nat.cast_nonneg _
  have nd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  -- split the forcing
  have hsplit := Q_add_le k (sB.add sD) ((sC1.add sC2).add sC3) t
  have hBD := Q_add_le k sB sD t
  have hCC := Q_add3_le k sC1 sC2 sC3 t
  have cardκd : ((Finset.univ : Finset (κ × Fin d)).card : ℝ) = Fintype.card κ * d := by
    simp [Finset.card_univ, Fintype.card_prod]
  have cardθd : ((Finset.univ : Finset (θ × Fin d)).card : ℝ) = Fintype.card θ * d := by
    simp [Finset.card_univ, Fintype.card_prod]
  rw [cardκd] at eD
  rw [cardθd] at eC3
  simp only [Finset.card_univ] at eB eC1 eC2
  have b1 : Q k (fun x => ∑ i, b i x * RB i x) t ≤ Fintype.card ι * (Ca * M) * SB := eB
  have b2 : Q k (fun x => ∑ p : κ × Fin d, q p.1 p.2 x * pd (RD p.1) p.2.succ x) t ≤
      Fintype.card κ * d * (Ca * M) * (d * SD) :=
    eD.trans (mul_le_mul_of_nonneg_left dD (by positivity))
  have b3 : Q k (fun x => ∑ l, c l x * C l x) t ≤ Fintype.card θ * (Ca * M) * SC :=
    eC1.trans (mul_le_mul_of_nonneg_left dC1 (by positivity))
  have b4 : Q k (fun x => ∑ l, c0 l x * dtC l x) t ≤ Fintype.card θ * (Ca * M) * ST' := eC2
  have b5 : Q k (fun x => ∑ p : θ × Fin d, cj p.1 p.2 x * pd (C p.1) p.2.succ x) t ≤
      Fintype.card θ * d * (Ca * M) * (d * SC) :=
    eC3.trans (mul_le_mul_of_nonneg_left dC3 (by positivity))
  unfold forcingErr
  have hX : Q k (fun x => (∑ i, b i x * RB i x +
      ∑ p : κ × Fin d, q p.1 p.2 x * pd (RD p.1) p.2.succ x) +
      (∑ l, c l x * C l x + ∑ l, c0 l x * dtC l x +
        ∑ p : θ × Fin d, cj p.1 p.2 x * pd (C p.1) p.2.succ x)) t ≤
      2 * (2 * (Fintype.card ι * (Ca * M) * SB) +
        2 * (Fintype.card κ * d * (Ca * M) * (d * SD))) +
      2 * (4 * (Fintype.card θ * (Ca * M) * SC) + 4 * (Fintype.card θ * (Ca * M) * ST') +
        2 * (Fintype.card θ * d * (Ca * M) * (d * SC))) := by
    refine hsplit.trans ?_
    linarith
  refine hX.trans (le_of_sub_nonneg ?_)
  have e : 8 * Ca * M * ((Fintype.card ι + Fintype.card κ * d ^ 2 +
          Fintype.card θ * (2 + d ^ 2)) : ℝ) * (SB + SD + SC + ST') -
      (2 * (2 * (Fintype.card ι * (Ca * M) * SB) +
        2 * (Fintype.card κ * d * (Ca * M) * (d * SD))) +
      2 * (4 * (Fintype.card θ * (Ca * M) * SC) + 4 * (Fintype.card θ * (Ca * M) * ST') +
        2 * (Fintype.card θ * d * (Ca * M) * (d * SC)))) =
      Ca * M * ((4 * Fintype.card ι + 8 * Fintype.card κ * d ^ 2 + 16 * Fintype.card θ +
          8 * Fintype.card θ * d ^ 2) * SB +
        (8 * Fintype.card ι + 4 * Fintype.card κ * d ^ 2 + 16 * Fintype.card θ +
          8 * Fintype.card θ * d ^ 2) * SD +
        (8 * Fintype.card ι + 8 * Fintype.card κ * d ^ 2 + 8 * Fintype.card θ +
          4 * Fintype.card θ * d ^ 2) * SC +
        (8 * Fintype.card ι + 8 * Fintype.card κ * d ^ 2 + 8 * Fintype.card θ +
          8 * Fintype.card θ * d ^ 2) * ST') := by ring
  rw [e]
  positivity

theorem sqrt_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_left (by positivity)]
  · nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b,
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- **`eq:actual-jet-complete-forcing`** in the norm form of the paper:
`‖𝓕_err‖_{H^k} ≤ C (‖R_B‖_{H^k} + ‖R_D‖_{H^{k+1}} + ‖C‖_{H^{k+1}} + ‖∂_tC‖_{H^k})`, where for a
family `‖F‖_{H^j} = √(Σ_i Q_j(F_i))` and `C = √(8 C_alg M (|ι| + |κ|d² + |θ|(2 + d²)))`. -/
theorem forcing_bound_norm {k m : ℕ} (hk : 2 * m ≤ k + 1) {CS : ℝ} (hCS : 0 ≤ CS)
    (hsup : ∀ f : ST d → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin d → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q m f t)
    {ι κ θ : Type*} [Fintype ι] [Fintype κ] [Fintype θ] {b RB : ι → ST d → ℝ}
    {q : κ → Fin d → ST d → ℝ} {RD : κ → ST d → ℝ} {c c0 : θ → ST d → ℝ}
    {cj : θ → Fin d → ST d → ℝ} {C dtC : θ → ST d → ℝ}
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (hRB : ∀ i, ContDiff ℝ ∞ (RB i))
    (hq : ∀ p j, ContDiff ℝ ∞ (q p j)) (hRD : ∀ p, ContDiff ℝ ∞ (RD p))
    (hc : ∀ l, ContDiff ℝ ∞ (c l)) (hc0 : ∀ l, ContDiff ℝ ∞ (c0 l))
    (hcj : ∀ l j, ContDiff ℝ ∞ (cj l j)) (hC : ∀ l, ContDiff ℝ ∞ (C l))
    (hdtC : ∀ l, ContDiff ℝ ∞ (dtC l))
    (pb : ∀ i, IsSPeriodic (b i)) (pRB : ∀ i, IsSPeriodic (RB i))
    (pq : ∀ p j, IsSPeriodic (q p j)) (pRD : ∀ p, IsSPeriodic (RD p))
    (pc : ∀ l, IsSPeriodic (c l)) (pc0 : ∀ l, IsSPeriodic (c0 l))
    (pcj : ∀ l j, IsSPeriodic (cj l j)) (pC : ∀ l, IsSPeriodic (C l))
    (pdtC : ∀ l, IsSPeriodic (dtC l))
    {M t : ℝ} (hM0 : 0 ≤ M) (hMb : ∀ i, Q k (b i) t ≤ M) (hMq : ∀ p j, Q k (q p j) t ≤ M)
    (hMc : ∀ l, Q k (c l) t ≤ M) (hMc0 : ∀ l, Q k (c0 l) t ≤ M)
    (hMcj : ∀ l j, Q k (cj l j) t ≤ M) :
    Real.sqrt (Q k (forcingErr b RB q RD c c0 cj C dtC) t) ≤
      Real.sqrt (8 * algC d k CS * M * ((Fintype.card ι + Fintype.card κ * d ^ 2 +
          Fintype.card θ * (2 + d ^ 2)) : ℝ)) *
        (Real.sqrt (∑ i, Q k (RB i) t) + Real.sqrt (∑ p, Q (k + 1) (RD p) t) +
          Real.sqrt (∑ l, Q (k + 1) (C l) t) + Real.sqrt (∑ l, Q k (dtC l) t)) := by
  have h := forcing_bound hk hCS hsup hb hRB hq hRD hc hc0 hcj hC hdtC pb pRB pq pRD pc pc0 pcj
    pC pdtC hM0 hMb hMq hMc hMc0 hMcj
  have n1 : 0 ≤ ∑ i, Q k (RB i) t := Finset.sum_nonneg fun _ _ => Q_nonneg _ _ _
  have n2 : 0 ≤ ∑ p, Q (k + 1) (RD p) t := Finset.sum_nonneg fun _ _ => Q_nonneg _ _ _
  have n3 : 0 ≤ ∑ l, Q (k + 1) (C l) t := Finset.sum_nonneg fun _ _ => Q_nonneg _ _ _
  have n4 : 0 ≤ ∑ l, Q k (dtC l) t := Finset.sum_nonneg fun _ _ => Q_nonneg _ _ _
  refine (Real.sqrt_le_sqrt h).trans ?_
  rw [Real.sqrt_mul' _ (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  refine (sqrt_add_le _ _ (by positivity) n4).trans ?_
  have := sqrt_add_le _ _ (by positivity : (0 : ℝ) ≤ ∑ i, Q k (RB i) t + ∑ p, Q (k + 1) (RD p) t)
    n3
  have := sqrt_add_le _ _ n1 n2
  linarith

/-- **The coefficient hypothesis for polynomial coefficient fields** (Moser for polynomials,
`SlabSobAlg.evalF_lip`): for a finite family of polynomials `P_τ` in the state fields and a bound
`B` on `Q_k` of the state fields, there is `M` with `Q_k(P_τ(v)) ≤ M` for every admissible `v`
and every `τ` — the "bounded `H^k` norm of the zeroth-order coefficients on the actual-jet
ball". -/
theorem coeff_bound_poly {σ τ : Type*} [Fintype τ] {k m : ℕ} (hk : 2 * m ≤ k + 1) {CS : ℝ}
    (hCS : 0 ≤ CS)
    (hsup : ∀ f : ST d → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin d → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q m f t)
    (P : τ → MvPolynomial σ ℝ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (v : σ → ST d → ℝ) (t : ℝ), (∀ i, ContDiff ℝ ∞ (v i)) →
      (∀ i, IsSPeriodic (v i)) → (∀ i, Q k (v i) t ≤ B) → ∀ p, Q k (evalF v (P p)) t ≤ M := by
  choose B' L hB' hL hP using fun p => evalF_lip hk hCS hsup (P p) hB
  refine ⟨∑ p, B' p, Finset.sum_nonneg fun p _ => hB' p, fun v t sv pv bv p => ?_⟩
  have := (hP p v v t 0 sv sv pv pv bv bv le_rfl (fun i => by simp [Q_const])).1
  exact this.trans (Finset.single_le_sum (fun p _ => hB' p) (Finset.mem_univ p))

end RenewalGeometry.ActualJetForcing
