/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedHarmonicPropagation
import RenewalGeometry.Continuum.KatoDataStability

/-!
# Backward uniqueness for linear symmetric hyperbolic systems by time reflection

Generic infrastructure (no renewal notions) for `lem:generated-physical-identification`
(Einstein–Standard-Model action-closure manuscript, `app:generated-dynamics`): the forward
uniqueness theorems `GenGauss.transport_unique` (scalar principal part) and
`GenHarmonic.sym_unique` (symmetric principal part with `c⁰ = a₀·1`) hold backward in time.

* `reflL` — the time reflection `(t, y) ↦ (-t, y)` as a continuous linear map; `pd_comp_refl`;
* **`transport_unique_backward`**, **`sym_unique_backward`** — if the defect vanishes on the
  slice `t₀` it vanishes on `[t₁, t₀] × 𝕋^d` (`t₁ < t₀`);
* **`sym_unique_two_sided`**, **`transport_unique_two_sided`** — vanishing on every compact
  sub-slab of `(a, b)` from vanishing on one slice.
-/

open Filter Topology Set
open scoped BigOperators ContDiff NNReal

noncomputable section

namespace RenewalGeometry.GenBackward

open SobolevOpen (pd)
open SymHypEnergy PeriodicCube SlabWaveHk KatoGalerkin

set_option linter.unusedSectionVars false

variable {d : ℕ}

/-- The time reflection `(t, y) ↦ (-t, y)` as a continuous linear map. -/
def reflL : ST d →L[ℝ] ST d :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => refl x
      map_add' := fun x y => by
        funext μ
        induction μ using Fin.cases with
        | zero => simp [KatoGalerkin.refl]; ring
        | succ j => simp [KatoGalerkin.refl, Fin.tail]
      map_smul' := fun c x => by
        funext μ
        induction μ using Fin.cases with
        | zero => simp [KatoGalerkin.refl]
        | succ j => simp [KatoGalerkin.refl, Fin.tail] }

theorem reflL_apply (x : ST d) : reflL x = refl x := rfl

theorem refl_refl (x : ST d) : refl (refl x) = x := by
  funext μ
  induction μ using Fin.cases with
  | zero => simp [KatoGalerkin.refl]
  | succ j => simp [KatoGalerkin.refl, Fin.tail]

theorem refl_zero (x : ST d) : (refl x) 0 = -(x 0) := by simp [KatoGalerkin.refl]

theorem reflL_ev_zero : reflL (ev (0 : Fin (d + 1))) = -ev 0 := by
  funext μ
  induction μ using Fin.cases with
  | zero => simp [reflL_apply, KatoGalerkin.refl]
  | succ j => simp [reflL_apply, KatoGalerkin.refl, Fin.tail, Fin.succ_ne_zero]

theorem reflL_ev_succ (i : Fin d) : reflL (ev (i.succ : Fin (d + 1))) = ev i.succ := by
  funext μ
  induction μ using Fin.cases with
  | zero => simp [reflL_apply, KatoGalerkin.refl, Fin.succ_ne_zero]
  | succ j => simp [reflL_apply, KatoGalerkin.refl, Fin.tail]

/-- The sign of the reflection in direction `μ`. -/
def sgn (μ : Fin (d + 1)) : ℝ := if μ = 0 then -1 else 1

theorem reflL_ev (μ : Fin (d + 1)) : reflL (ev μ) = sgn μ • ev μ := by
  induction μ using Fin.cases with
  | zero => rw [reflL_ev_zero]; simp [sgn]
  | succ i => rw [reflL_ev_succ]; simp [sgn, Fin.succ_ne_zero]

/-- **The partial derivatives of a reflected field.** -/
theorem pd_comp_refl {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ST d → E}
    {x : ST d} (hf : DifferentiableAt ℝ f (refl x)) (μ : Fin (d + 1)) :
    pd (fun y => f (refl y)) μ x = sgn μ • pd f μ (refl x) := by
  unfold SobolevOpen.pd
  have h : HasFDerivAt (fun y => f (reflL y)) ((fderiv ℝ f (refl x)).comp reflL) x :=
    hf.hasFDerivAt.comp x reflL.hasFDerivAt
  rw [show (fun y => f (refl y)) = fun y => f (reflL y) from rfl, h.fderiv,
    ContinuousLinearMap.comp_apply, reflL_ev, map_smul]

theorem refl_mem_openSlab {a b : ℝ} {x : ST d} (hx : x ∈ openSlab a b) :
    refl x ∈ openSlab (-b) (-a) := by
  show (refl x) 0 ∈ Ioo (-b) (-a)
  rw [refl_zero]; exact ⟨by linarith [hx.2], by linarith [hx.1]⟩

theorem refl_mem_slab {t₀ t₁ : ℝ} {x : ST d} (hx : x ∈ slab t₀ t₁) :
    refl x ∈ slab (-t₁) (-t₀) := by
  show (refl x) 0 ∈ Icc (-t₁) (-t₀)
  rw [refl_zero]; exact ⟨by linarith [hx.2], by linarith [hx.1]⟩

theorem contDiffOn_comp_refl {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ST d → E}
    {a b : ℝ} {n : WithTop ℕ∞} (hf : ContDiffOn ℝ n f (openSlab a b)) :
    ContDiffOn ℝ n (fun y => f (refl y)) (openSlab (-b) (-a)) := by
  refine hf.comp reflL.contDiff.contDiffOn fun y hy => ?_
  have := refl_mem_openSlab hy
  simpa [reflL_apply, neg_neg] using this

theorem isSPeriodic_comp_refl' {E : Type*} {f : ST d → E} (hf : IsSPeriodic f) :
    IsSPeriodic (fun y => f (refl y)) := fun k x => by
  have : refl (x + sshift k) = refl x + sshift k := by
    funext μ
    induction μ using Fin.cases with
    | zero => simp [KatoGalerkin.refl, sshift]
    | succ j => simp [KatoGalerkin.refl, Fin.tail, sshift]
  simp only [this, hf k]

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- **Backward uniqueness for transport systems with scalar principal part.** -/
theorem transport_unique_backward {w : ST d → N → ℂ} {c : Fin (d + 1) → ST d → ℝ}
    {a t₁ t₀ b : ℝ} (ha : a < t₁) (h10 : t₁ < t₀) (hb : t₀ < b)
    (hw : ContDiffOn ℝ 1 w (openSlab a b)) (hwp : IsSPeriodic w)
    (hc : ∀ μ, ContDiffOn ℝ 1 (c μ) (openSlab a b)) (hcp : ∀ μ, IsSPeriodic (c μ)) {κ : ℝ}
    (hκ : 0 < κ) (hc0 : ∀ x ∈ slab t₁ t₀, κ ≤ c 0 x) {K : ℝ} (hK : 0 ≤ K)
    (heq : ∀ x ∈ slab t₁ t₀, ‖∑ μ, c μ x • pd w μ x‖ ≤ K * ‖w x‖)
    (h0 : ∀ y : Fin d → ℝ, w (Fin.cons t₀ y) = 0) : ∀ x ∈ slab t₁ t₀, w x = 0 := by
  set w' : ST d → N → ℂ := fun x => w (refl x) with hw'
  set c' : Fin (d + 1) → ST d → ℝ := fun μ x => -sgn μ * c μ (refl x) with hc'
  have hw's : ContDiffOn ℝ 1 w' (openSlab (-b) (-a)) := contDiffOn_comp_refl hw
  have hdiff : ∀ x ∈ slab (-t₀) (-t₁), DifferentiableAt ℝ w (refl x) := by
    intro x hx
    have hx' : refl x ∈ openSlab a b := by
      have := refl_mem_slab hx
      rw [neg_neg, neg_neg] at this
      exact slab_subset_openSlab ha hb this
    exact (hw.differentiableOn one_ne_zero _ hx').differentiableAt
      ((isOpen_openSlab a b).mem_nhds hx')
  have hsq : ∀ μ : Fin (d + 1), sgn μ * sgn μ = (1 : ℝ) := fun μ => by
    unfold sgn; split_ifs <;> norm_num
  have hz := GenGauss.transport_unique (w := w') (c := c') (a := -b) (t₀ := -t₀) (t₁ := -t₁)
    (b := -a) (by linarith) (by linarith) (by linarith) hw's (isSPeriodic_comp_refl' hwp)
    (fun μ => contDiffOn_const.mul (contDiffOn_comp_refl (hc μ)))
    (fun μ k x => by simp only [hc', isSPeriodic_comp_refl' (hcp μ) k x]) hκ
    (fun x hx => by
      have := hc0 (refl x) (by simpa using refl_mem_slab hx)
      simpa [hc', sgn] using this) hK
    (fun x hx => by
      have hr : refl x ∈ slab t₁ t₀ := by simpa using refl_mem_slab hx
      have e : ∑ μ, c' μ x • pd w' μ x = -∑ μ, c μ (refl x) • pd w μ (refl x) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [hw', pd_comp_refl (hdiff x hx) μ, smul_smul]
        have h1 : c' μ x * sgn μ = -c μ (refl x) := by
          simp only [hc']
          linear_combination (-c μ (refl x)) * hsq μ
        rw [h1, neg_smul]
      rw [e, norm_neg]
      exact heq _ hr)
    (fun y => by
      simp only [hw', KatoGalerkin.refl_cons, neg_neg]
      exact h0 y)
  intro x hx
  have hr : refl x ∈ slab (-t₀) (-t₁) := refl_mem_slab hx
  have := hz _ hr
  simpa [hw', refl_refl] using this

/-- **Backward uniqueness for linear symmetric hyperbolic systems with real coefficients.** -/
theorem sym_unique_backward {W : ST d → N → ℝ} {c : Fin (d + 1) → ST d → N → N → ℝ}
    {a0 : ST d → ℝ} {a t₁ t₀ b : ℝ} (ha : a < t₁) (h10 : t₁ < t₀) (hb : t₀ < b)
    (hW : ContDiffOn ℝ 1 W (openSlab a b)) (hWp : IsSPeriodic W)
    (hc : ∀ μ, ContDiffOn ℝ 1 (c μ) (openSlab a b)) (hcp : ∀ μ, IsSPeriodic (c μ))
    (hsym : ∀ μ x i k, c μ x i k = c μ x k i)
    (h0c : ∀ x i k, c 0 x i k = if i = k then a0 x else 0)
    {κ : ℝ} (hκ : 0 < κ) (ha0 : ∀ x ∈ slab t₁ t₀, κ ≤ a0 x) {K : ℝ} (hK : 0 ≤ K)
    (heq : ∀ x ∈ slab t₁ t₀, ‖(fun i => ∑ μ, ∑ k, c μ x i k * pd W μ x k)‖ ≤ K * ‖W x‖)
    (hinit : ∀ y : Fin d → ℝ, W (Fin.cons t₀ y) = 0) : ∀ x ∈ slab t₁ t₀, W x = 0 := by
  set W' : ST d → N → ℝ := fun x => W (refl x) with hW'
  set c' : Fin (d + 1) → ST d → N → N → ℝ := fun μ x i k => -sgn μ * c μ (refl x) i k with hc'
  have hsq : ∀ μ : Fin (d + 1), sgn μ * sgn μ = (1 : ℝ) := fun μ => by
    unfold sgn; split_ifs <;> norm_num
  have hdiff : ∀ x ∈ slab (-t₀) (-t₁), DifferentiableAt ℝ W (refl x) := by
    intro x hx
    have hx' : refl x ∈ openSlab a b := by
      have := refl_mem_slab hx
      rw [neg_neg, neg_neg] at this
      exact slab_subset_openSlab ha hb this
    exact (hW.differentiableOn one_ne_zero _ hx').differentiableAt
      ((isOpen_openSlab a b).mem_nhds hx')
  have hc's : ∀ μ, ContDiffOn ℝ 1 (c' μ) (openSlab (-b) (-a)) := by
    intro μ
    have h := contDiffOn_comp_refl (hc μ)
    have e : c' μ = fun x => (-sgn μ) • c μ (refl x) := by
      funext x i k; simp [hc']
    rw [e]
    exact (contDiffOn_const (c := -sgn μ)).smul h
  have hz := GenHarmonic.sym_unique (W := W') (c := c') (a0 := fun x => a0 (refl x))
    (a := -b) (t₀ := -t₀) (t₁ := -t₁) (b := -a) (by linarith) (by linarith) (by linarith)
    (contDiffOn_comp_refl hW) (isSPeriodic_comp_refl' hWp) hc's
    (fun μ k x => by simp only [hc', isSPeriodic_comp_refl' (hcp μ) k x])
    (fun μ x i k => by simp only [hc', hsym μ (refl x) i k])
    (fun x i k => by
      simp only [hc', h0c (refl x) i k, sgn, ite_true]
      split_ifs <;> ring)
    hκ (fun x hx => ha0 (refl x) (by simpa using refl_mem_slab hx)) hK
    (fun x hx => by
      have hr : refl x ∈ slab t₁ t₀ := by simpa using refl_mem_slab hx
      have e : (fun i => ∑ μ, ∑ k, c' μ x i k * pd W' μ x k) =
          fun i => -(∑ μ, ∑ k, c μ (refl x) i k * pd W μ (refl x) k) := by
        funext i
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hW', pd_comp_refl (hdiff x hx) μ]
        simp only [hc', Pi.smul_apply, smul_eq_mul]
        linear_combination (-(c μ (refl x) i k * pd W μ (refl x) k)) * hsq μ
      have e2 : (fun i => -∑ μ, ∑ k, c μ (refl x) i k * pd W μ (refl x) k) =
          -(fun i => ∑ μ, ∑ k, c μ (refl x) i k * pd W μ (refl x) k) := rfl
      rw [e, e2, norm_neg]
      exact heq _ hr)
    (fun y => by
      simp only [hW', KatoGalerkin.refl_cons, neg_neg]
      exact hinit y)
  intro x hx
  have hr : refl x ∈ slab (-t₀) (-t₁) := refl_mem_slab hx
  have := hz _ hr
  simpa [hW', refl_refl] using this

/-! ### Time reflection of classical solutions and equivariant uniqueness -/

section Equivariant

variable {n : ℕ} {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}
  {U₀ : Fin n → ST d → ℝ} {T : ℝ} {W : Fin n → ST d → ℝ} {P : Fin n → Fin d → ST d → ℝ}

/-- **Time reflection of a two-sided classical solution**: `W(-t, y)` solves the reversed system
`(-A, -F)` with the same data. -/
theorem TwoSidedSol.reflect (h : TwoSidedSol A F U₀ T W P) :
    TwoSidedSol (fun i a b v => -A i a b v) (fun a v => -F a v) U₀ T
      (fun b x => W b (refl x)) (fun b i x => P b i (refl x)) where
  contU b := (h.contU b).comp continuous_refl
  contP b i := (h.contP b i).comp continuous_refl
  perU b := isSPeriodic_comp_refl' (h.perU b)
  perP b i := isSPeriodic_comp_refl' (h.perP b i)
  init b y := by
    simp only [KatoGalerkin.refl_cons, neg_zero]
    exact h.init b y
  space b i x := by
    simp only [refl_line]
    exact h.space b i (refl x)
  time b t ht y := by
    have hm : -t ∈ Ioo (-T) T := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have h1 := (h.time b (-t) hm y).comp t (hasDerivAt_neg t)
    have e1 : (fun s => W b (refl (Fin.cons s y : ST d))) = (fun s => W b (Fin.cons s y)) ∘ Neg.neg := by
      funext s; simp [KatoGalerkin.refl_cons]
    rw [e1]
    have e2 : genP (fun i a b v => -A i a b v) (fun a v => -F a v) (fun b x => W b (refl x))
        (fun b i x => P b i (refl x)) b (Fin.cons t y) =
        genP A F W P b (Fin.cons (-t) y) * (-1) := by
      rw [genP_neg]
      simp only [genP, KatoGalerkin.refl_cons]
      ring
    rw [e2]
    exact h1

/-- **Equivariant uniqueness**: if the coefficients are equivariant under a linear map `L` of the
state space and the data are `L`-invariant, then a two-sided classical solution is `L`-invariant
on `(-T, T)`. -/
theorem twoSided_invariant (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b))
    (hsym : ∀ i a b v, A i a b v = A i b a v) (hF : ∀ a, ContDiff ℝ ∞ (F a))
    (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (hLA : ∀ j a v w, ∑ b, A j a b (L v) * L w b = L (fun a' => ∑ b, A j a' b v * w b) a)
    (hLF : ∀ a v, F a (L v) = L (fun a' => F a' v) a)
    (h : TwoSidedSol A F U₀ T W P)
    (h0 : ∀ y, L (fun c => U₀ c (Fin.cons 0 y)) = fun c => U₀ c (Fin.cons 0 y)) :
    ∀ x : ST d, x 0 ∈ Ioo (-T) T → L (fun c => W c x) = fun c => W c x := by
  -- the transformed solution
  have key : ∀ {A' : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F' : Fin n → (Fin n → ℝ) → ℝ}
      {W' : Fin n → ST d → ℝ} {P' : Fin n → Fin d → ST d → ℝ},
      (∀ i a b, ContDiff ℝ ∞ (A' i a b)) → (∀ i a b v, A' i a b v = A' i b a v) →
      (∀ a, ContDiff ℝ ∞ (F' a)) →
      (∀ j a v w, ∑ b, A' j a b (L v) * L w b = L (fun a' => ∑ b, A' j a' b v * w b) a) →
      (∀ a v, F' a (L v) = L (fun a' => F' a' v) a) → TwoSidedSol A' F' U₀ T W' P' →
      ∀ x : ST d, x 0 ∈ Ico 0 T → L (fun c => W' c x) = fun c => W' c x := by
    intro A' F' W' P' hA' hsym' hF' hLA' hLF' h' x hx
    set V : Fin n → ST d → ℝ := fun b x => L (fun c => W' c x) b with hV
    set Q : Fin n → Fin d → ST d → ℝ := fun b i x => L (fun c => P' c i x) b with hQ
    have hLc : Continuous L := L.continuous
    have hsolV : TwoSidedSol A' F' U₀ T V Q := by
      refine ⟨fun b => ?_, fun b i => ?_, fun b k x => ?_, fun b i k x => ?_, fun b y => ?_,
        fun b i x => ?_, fun b t ht y => ?_⟩
      · exact (continuous_apply b).comp (hLc.comp (continuous_pi fun c => h'.contU c))
      · exact (continuous_apply b).comp (hLc.comp (continuous_pi fun c => h'.contP c i))
      · simp only [hV, h'.perU _ k x]
      · simp only [hQ, h'.perP _ i k x]
      · simp only [hV, h'.init]; exact congrFun (h0 y) b
      · have hd : HasDerivAt (fun s : ℝ => fun c => W' c (x + s • ev i.succ))
            (fun c => P' c i x) 0 := hasDerivAt_pi.2 fun c => h'.space c i x
        have := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
        exact (hasDerivAt_pi.1 this) b
      · have hd : HasDerivAt (fun s : ℝ => fun c => W' c (Fin.cons s y))
            (fun c => genP A' F' W' P' c (Fin.cons t y)) t :=
          hasDerivAt_pi.2 fun c => h'.time c t ht y
        have h2 := (hasDerivAt_pi.1 (L.hasFDerivAt.comp_hasDerivAt t hd)) b
        have hval : genP A' F' V Q b (Fin.cons t y) =
            L (fun c => genP A' F' W' P' c (Fin.cons t y)) b := by
          have hw : (fun c => V c (Fin.cons t y)) = L (fun c => W' c (Fin.cons t y)) := rfl
          have hq : ∀ i b', Q b' i (Fin.cons t y) = L (fun c => P' c i (Fin.cons t y)) b' :=
            fun _ _ => rfl
          unfold genP
          rw [hw]
          simp only [hq]
          rw [hLF']
          have e : (fun a' => F' a' (fun c => W' c (Fin.cons t y)) -
              ∑ i, ∑ b', A' i a' b' (fun c => W' c (Fin.cons t y)) * P' b' i (Fin.cons t y)) =
              (fun a' => F' a' (fun c => W' c (Fin.cons t y))) -
                ∑ i, fun a' => ∑ b', A' i a' b' (fun c => W' c (Fin.cons t y)) *
                  (fun c => P' c i (Fin.cons t y)) b' := by
            funext a'; simp [Finset.sum_apply]
          rw [e, map_sub, map_sum, Pi.sub_apply, Finset.sum_apply]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          exact hLA' i b _ _
        rw [hval]
        exact h2
    obtain ⟨hx0, hxT⟩ := hx
    set t₁ := (x 0 + T) / 2 with ht₁
    have ht₁0 : 0 < t₁ := by rw [ht₁]; linarith
    have ht₁T : t₁ < T := by rw [ht₁]; linarith
    have hu := KatoStab.twoSided_unique hA' hsym' hF' h' hsolV ht₁0 ht₁T ht₁T x
      ⟨hx0, by rw [ht₁]; linarith⟩
    funext b
    exact (hu b).symm
  intro x hx
  rcases le_or_gt 0 (x 0) with h0x | h0x
  · exact key hA hsym hF hLA hLF h x ⟨h0x, hx.2⟩
  · have hr := key (A' := fun i a b v => -A i a b v) (F' := fun a v => -F a v)
      (fun i a b => (hA i a b).neg) (fun i a b v => by rw [hsym]) (fun a => (hF a).neg)
      (fun j a v w => by
        have := hLA j a v w
        simp only [neg_mul, Finset.sum_neg_distrib, this]
        have e : (fun a' => -∑ b, A j a' b v * w b) = -(fun a' => ∑ b, A j a' b v * w b) := rfl
        rw [e, map_neg]; rfl)
      (fun a v => by
        rw [hLF]
        have e : (fun a' => -F a' v) = -(fun a' => F a' v) := rfl
        rw [e, map_neg]; rfl)
      (TwoSidedSol.reflect h) (refl x) ⟨by rw [refl_zero]; linarith, by rw [refl_zero]; linarith [hx.1]⟩
    have e : (fun c => W c (refl (refl x))) = fun c => W c x := by rw [refl_refl]
    simpa only [refl_refl] using hr

end Equivariant

end RenewalGeometry.GenBackward
