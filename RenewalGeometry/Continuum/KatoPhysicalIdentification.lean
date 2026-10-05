/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.KatoLocalExistence
import RenewalGeometry.Continuum.SymmetricHyperbolicUniqueness
import RenewalGeometry.Analysis.PartialDerivativesC1

/-!
# The two-sided Kato solution and the identification of analytic germs

Generic infrastructure (no renewal notions) for `lem:generated-physical-identification`
(Einstein–Standard-Model action-closure manuscript, `app:generated-dynamics`).

* `ForwardSol`, `TwoSidedSol`: the classical solution properties on `[0, T]`, resp. `(-T, T)`;
  `genP A F U P` is the generator `F(U) - Σ_i A^i(U) P_i` with the spatial derivatives `P`.
* `twoSided_of_forward` (**time reversal and gluing**): a forward solution of the system
  `(A, F)` and a forward solution of the reversed system `(-A, -F)` with the same data glue to a
  solution on `(-T, T)` (left and right time derivatives match at `t = 0`).
* **`kato_two_sided`**: Kato's local existence on a symmetric interval `(-T, T)`
  (`kato_local_existence` applied to `(A, F)` and `(-A, -F)`).
* `TwoSidedSol.contDiffOn`: the solution is jointly `C¹` on the open slab
  (`PartialC1.contDiffOn_one_of_partials`); **`TwoSidedSol.solves`**: its complexification solves
  the quasilinear symmetric system `complexSys A F` in the sense of `SymHypUniqueness.QLSymSys`.
* **`kato_germ_identification`** (the uniqueness step of `lem:generated-physical-identification`):
  under the named Cauchy–Kovalevskaya input `SymHypUniqueness.AnalyticGermExistence` (local
  analytic *physical* solutions of the constrained Cauchy problem for data of the analytic core,
  solving the symmetric system), the Kato solution with the same data coincides with a physical
  germ on a common slab `[0, t₁] × 𝕋^d` — by `QLSymSys.unique`.
-/

open MeasureTheory Filter Topology Set Finset
open scoped BigOperators ContDiff Real NNReal

noncomputable section

namespace RenewalGeometry.KatoGalerkin

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy

set_option linter.unusedSectionVars false

variable {d n : ℕ}

/-! ### Classical solutions -/

/-- The generator `F(U) - Σ_i A^i(U) P_i` of a field `U` with spatial derivatives `P`. -/
def genP (A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ) (F : Fin n → (Fin n → ℝ) → ℝ)
    (U : Fin n → ST d → ℝ) (P : Fin n → Fin d → ST d → ℝ) (b : Fin n) (x : ST d) : ℝ :=
  F b (fun c => U c x) - ∑ i, ∑ b', A i b b' (fun c => U c x) * P b' i x

/-- A classical solution on `[0, T] × 𝕋^d` with data `U₀` (the output of
`kato_local_existence`). -/
structure ForwardSol (A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ)
    (F : Fin n → (Fin n → ℝ) → ℝ) (U₀ : Fin n → ST d → ℝ) (T : ℝ) (U : Fin n → ST d → ℝ)
    (P : Fin n → Fin d → ST d → ℝ) : Prop where
  contU : ∀ b, Continuous (U b)
  contP : ∀ b i, Continuous (P b i)
  perU : ∀ b, IsSPeriodic (U b)
  perP : ∀ b i, IsSPeriodic (P b i)
  init : ∀ b y, U b (Fin.cons 0 y) = U₀ b (Fin.cons 0 y)
  space : ∀ b (i : Fin d) x, HasDerivAt (fun s : ℝ => U b (x + s • ev i.succ)) (P b i x) 0
  time : ∀ b, ∀ t ∈ Set.Icc 0 T, ∀ y, HasDerivWithinAt (fun s => U b (Fin.cons s y))
    (genP A F U P b (Fin.cons t y)) (Set.Icc 0 T) t

/-- A classical solution on `(-T, T) × 𝕋^d` with data `U₀` at `t = 0`. -/
structure TwoSidedSol (A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ)
    (F : Fin n → (Fin n → ℝ) → ℝ) (U₀ : Fin n → ST d → ℝ) (T : ℝ) (U : Fin n → ST d → ℝ)
    (P : Fin n → Fin d → ST d → ℝ) : Prop where
  contU : ∀ b, Continuous (U b)
  contP : ∀ b i, Continuous (P b i)
  perU : ∀ b, IsSPeriodic (U b)
  perP : ∀ b i, IsSPeriodic (P b i)
  init : ∀ b y, U b (Fin.cons 0 y) = U₀ b (Fin.cons 0 y)
  space : ∀ b (i : Fin d) x, HasDerivAt (fun s : ℝ => U b (x + s • ev i.succ)) (P b i x) 0
  time : ∀ b, ∀ t ∈ Set.Ioo (-T) T, ∀ y, HasDerivAt (fun s => U b (Fin.cons s y))
    (genP A F U P b (Fin.cons t y)) t

/-! ### Time reversal and gluing -/

/-- The time reflection `(t, y) ↦ (-t, y)`. -/
def refl (x : ST d) : ST d := Fin.cons (-(x 0)) (Fin.tail x)

theorem continuous_refl : Continuous (refl (d := d)) := by
  refine continuous_pi fun μ => ?_
  induction μ using Fin.cases with
  | zero =>
    exact (continuous_neg.comp (continuous_apply (0 : Fin (d + 1)))).congr fun x => by
      simp [refl]
  | succ j => simpa [refl, Fin.tail] using continuous_apply j.succ

theorem refl_cons (t : ℝ) (y : Fin d → ℝ) : refl (Fin.cons t y : ST d) = Fin.cons (-t) y := by
  simp [refl]

theorem refl_of_zero {x : ST d} (h : x 0 = 0) : refl x = x := by
  conv_rhs => rw [← Fin.cons_self_tail x]
  simp [refl, h]

theorem line_zero_succ (x : ST d) (i : Fin d) (s : ℝ) : (x + s • ev i.succ) 0 = x 0 := by
  simp [Pi.single_apply, Fin.succ_ne_zero]

theorem refl_line (x : ST d) (i : Fin d) (s : ℝ) :
    refl (x + s • ev i.succ) = refl x + s • ev i.succ := by
  funext μ
  induction μ using Fin.cases with
  | zero => simp [refl, Pi.single_apply, Fin.succ_ne_zero]
  | succ j => simp [refl, Fin.tail, Pi.single_apply]

theorem isSPeriodic_comp_refl {f : ST d → ℝ} (hf : IsSPeriodic f) :
    IsSPeriodic fun x => f (refl x) := fun k x => by
  have : refl (x + sshift k) = refl x + sshift k := by
    funext μ
    induction μ using Fin.cases with
    | zero => simp [refl, sshift]
    | succ j => simp [refl, Fin.tail, sshift]
  simp only [this, hf k]

theorem genP_neg (A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ) (F : Fin n → (Fin n → ℝ) → ℝ)
    (U : Fin n → ST d → ℝ) (P : Fin n → Fin d → ST d → ℝ) (b : Fin n) (x : ST d) :
    genP (fun i a b v => -A i a b v) (fun a v => -F a v) U P b x = -genP A F U P b x := by
  simp only [genP, neg_mul, Finset.sum_neg_distrib, sub_neg_eq_add]; ring

/-- Two forward solutions with the same data have the same spatial derivatives at `t = 0`. -/
theorem P_zero_eq {A A' : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ}
    {F F' : Fin n → (Fin n → ℝ) → ℝ} {U₀ : Fin n → ST d → ℝ} {T T' : ℝ}
    {U U' : Fin n → ST d → ℝ} {P P' : Fin n → Fin d → ST d → ℝ}
    (h : ForwardSol A F U₀ T U P) (h' : ForwardSol A' F' U₀ T' U' P') (b : Fin n) (i : Fin d)
    (y : Fin d → ℝ) : P b i (Fin.cons 0 y) = P' b i (Fin.cons 0 y) := by
  have e : (fun s : ℝ => U b ((Fin.cons 0 y : ST d) + s • ev i.succ)) =
      fun s : ℝ => U' b ((Fin.cons 0 y : ST d) + s • ev i.succ) := by
    funext s
    rw [← cons_space_eq, h.init, h'.init]
  have h1 := h.space b i (Fin.cons 0 y)
  rw [e] at h1
  exact h1.unique (h'.space b i (Fin.cons 0 y))

/-- The glued field: `U⁺` for `t ≥ 0`, `U⁻(-t, ·)` for `t < 0`. -/
def glue (Up Um : Fin n → ST d → ℝ) (b : Fin n) (x : ST d) : ℝ :=
  if 0 ≤ x 0 then Up b x else Um b (refl x)

/-- The glued spatial derivatives. -/
def glueP (Pp Pm : Fin n → Fin d → ST d → ℝ) (b : Fin n) (i : Fin d) (x : ST d) : ℝ :=
  if 0 ≤ x 0 then Pp b i x else Pm b i (refl x)

/-- **Time reversal and gluing**: a forward solution of `(A, F)` and a forward solution of the
reversed system `(-A, -F)` with the same data glue to a classical solution on `(-T, T)`. -/
theorem twoSided_of_forward {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ}
    {F : Fin n → (Fin n → ℝ) → ℝ} {U₀ : Fin n → ST d → ℝ} {T : ℝ} (hT : 0 < T)
    {Up Um : Fin n → ST d → ℝ} {Pp Pm : Fin n → Fin d → ST d → ℝ}
    (hp : ForwardSol A F U₀ T Up Pp)
    (hm : ForwardSol (fun i a b v => -A i a b v) (fun a v => -F a v) U₀ T Um Pm) :
    TwoSidedSol A F U₀ T (glue Up Um) (glueP Pp Pm) := by
  have hU0 : ∀ b x, x 0 = 0 → Up b x = Um b (refl x) := fun b x hx => by
    rw [refl_of_zero hx, ← Fin.cons_self_tail x, hx, hp.init, hm.init]
  have hP0 : ∀ b i x, x 0 = 0 → Pp b i x = Pm b i (refl x) := fun b i x hx => by
    rw [refl_of_zero hx, ← Fin.cons_self_tail x, hx]
    exact P_zero_eq hp hm b i _
  refine ⟨fun b => ?_, fun b i => ?_, fun b => ?_, fun b i => ?_, fun b y => ?_,
    fun b i x => ?_, fun b t ht y => ?_⟩
  · exact Continuous.if_le (hp.contU b) ((hm.contU b).comp continuous_refl) continuous_const
      (continuous_apply 0) fun x hx => hU0 b x hx.symm
  · exact Continuous.if_le (hp.contP b i) ((hm.contP b i).comp continuous_refl)
      continuous_const (continuous_apply 0) fun x hx => hP0 b i x hx.symm
  · intro k x
    simp only [glue, sshift_zero]
    split_ifs
    · exact hp.perU b k x
    · exact isSPeriodic_comp_refl (hm.perU b) k x
  · intro k x
    simp only [glueP, sshift_zero]
    split_ifs
    · exact hp.perP b i k x
    · exact isSPeriodic_comp_refl (hm.perP b i) k x
  · simp [glue, hp.init]
  · simp only [glue, glueP, line_zero_succ]
    split_ifs with h
    · exact hp.space b i x
    · simp only [refl_line]
      exact hm.space b i (refl x)
  · -- the time derivative
    have hgp : ∀ s ≥ 0, genP A F (glue Up Um) (glueP Pp Pm) b (Fin.cons s y) =
        genP A F Up Pp b (Fin.cons s y) := fun s hs => by
      simp [genP, glue, glueP, hs]
    have hgm : ∀ s ≤ 0, genP A F (glue Up Um) (glueP Pp Pm) b (Fin.cons s y) =
        -genP (fun i a b v => -A i a b v) (fun a v => -F a v) Um Pm b (Fin.cons (-s) y) := by
      intro s hs
      rw [genP_neg, neg_neg]
      rcases eq_or_lt_of_le hs with h | h
      · subst h
        simp only [genP, glue, glueP, le_refl, if_true, Fin.cons_zero, neg_zero]
        simp only [hU0 _ _ (show (Fin.cons 0 y : ST d) 0 = 0 from rfl),
          hP0 _ _ _ (show (Fin.cons 0 y : ST d) 0 = 0 from rfl), refl_cons, neg_zero]
      · have hn : ¬ (0 ≤ (Fin.cons s y : ST d) 0) := by simp [not_le.2 h]
        simp only [genP, glue, glueP, hn, if_false, refl_cons]
    -- the functions on the two sides
    have hfp : ∀ s ≥ 0, glue Up Um b (Fin.cons s y) = Up b (Fin.cons s y) := fun s hs => by
      simp [glue, hs]
    have hfm : ∀ s ≤ 0, glue Up Um b (Fin.cons s y) = Um b (Fin.cons (-s) y) := fun s hs => by
      rcases eq_or_lt_of_le hs with h | h
      · subst h; simp only [neg_zero]
        rw [hfp 0 le_rfl, hU0 b _ rfl, refl_cons, neg_zero]
      · simp [glue, not_le.2 h, refl_cons]
    -- right and left derivatives
    have hright : ∀ t, 0 ≤ t → t < T → HasDerivWithinAt (fun s => glue Up Um b (Fin.cons s y))
        (genP A F Up Pp b (Fin.cons t y)) (Set.Ici t) t := by
      intro t h0 h1
      have := (hp.time b t ⟨h0, h1.le⟩ y).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨h0, h1⟩)
      exact this.congr (fun s hs => hfp s (h0.trans hs)) (hfp t h0)
    have hleft : ∀ t, -T < t → t ≤ 0 → HasDerivWithinAt (fun s => glue Up Um b (Fin.cons s y))
        (-genP (fun i a b v => -A i a b v) (fun a v => -F a v) Um Pm b (Fin.cons (-t) y))
        (Set.Iic t) t := by
      intro t h0 h1
      have hm' := (hm.time b (-t) ⟨by linarith, by linarith⟩ y).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨by linarith, by linarith⟩)
      have hc := hm'.comp t ((hasDerivAt_neg t).hasDerivWithinAt (s := Set.Iic t))
        (fun s (hs : s ≤ t) => show -t ≤ -s by linarith)
      have hc' : HasDerivWithinAt (fun s => Um b (Fin.cons (-s) y))
          (-genP (fun i a b v => -A i a b v) (fun a v => -F a v) Um Pm b (Fin.cons (-t) y))
          (Set.Iic t) t := by
        exact hc.congr_deriv (by ring)
      exact hc'.congr (fun s hs => hfm s (le_trans hs h1)) (hfm t h1)
    rcases lt_trichotomy t 0 with h | h | h
    · have hl := hleft t ht.1 h.le
      have hr : HasDerivWithinAt (fun s => glue Up Um b (Fin.cons s y))
          (-genP (fun i a b v => -A i a b v) (fun a v => -F a v) Um Pm b (Fin.cons (-t) y))
          (Set.Ici t) t := by
        have hm' := (hm.time b (-t) ⟨by linarith, by linarith [ht.1]⟩ y).hasDerivAt
          (Icc_mem_nhds (by linarith) (by linarith [ht.1]))
        have hc := hm'.comp t (hasDerivAt_neg t)
        have hc' : HasDerivAt (fun s => Um b (Fin.cons (-s) y))
            (-genP (fun i a b v => -A i a b v) (fun a v => -F a v) Um Pm b (Fin.cons (-t) y)) t :=
          hc.congr_deriv (by ring)
        refine hc'.hasDerivWithinAt.congr_of_eventuallyEq ?_ (hfm t h.le)
        filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds h)] with s hs
        exact hfm s (le_of_lt hs)
      have := (hl.union hr)
      rw [Set.Iic_union_Ici, hasDerivWithinAt_univ] at this
      rw [hgm t h.le]; exact this
    · subst h
      have hl := hleft 0 (by linarith) le_rfl
      have hr := hright 0 le_rfl hT
      rw [neg_zero] at hl
      have e : genP A F Up Pp b (Fin.cons 0 y) =
          -genP (fun i a b v => -A i a b v) (fun a v => -F a v) Um Pm b (Fin.cons 0 y) := by
        have := hgm 0 le_rfl
        rw [hgp 0 le_rfl, neg_zero] at this
        exact this
      rw [← e] at hl
      have := hl.union hr
      rw [Set.Iic_union_Ici, hasDerivWithinAt_univ] at this
      rw [hgp 0 le_rfl]; exact this
    · have hr := hright t h.le ht.2
      have hl : HasDerivWithinAt (fun s => glue Up Um b (Fin.cons s y))
          (genP A F Up Pp b (Fin.cons t y)) (Set.Iic t) t := by
        have hp' := (hp.time b t ⟨h.le, ht.2.le⟩ y).hasDerivAt (Icc_mem_nhds h ht.2)
        refine hp'.hasDerivWithinAt.congr_of_eventuallyEq ?_ (hfp t h.le)
        filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds h)] with s hs
        exact hfp s (le_of_lt hs)
      have := hl.union hr
      rw [Set.Iic_union_Ici, hasDerivWithinAt_univ] at this
      rw [hgp t h.le]; exact this

theorem ForwardSol.mono {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ}
    {F : Fin n → (Fin n → ℝ) → ℝ} {U₀ : Fin n → ST d → ℝ} {T T' : ℝ}
    {U : Fin n → ST d → ℝ} {P : Fin n → Fin d → ST d → ℝ} (h : ForwardSol A F U₀ T U P)
    (hTT : T' ≤ T) : ForwardSol A F U₀ T' U P :=
  ⟨h.contU, h.contP, h.perU, h.perP, h.init, h.space, fun b t ht y =>
    (h.time b t ⟨ht.1, ht.2.trans hTT⟩ y).mono (Icc_subset_Icc le_rfl hTT)⟩

/-- **Kato's local existence theorem on a symmetric time interval**: the forward theorem
`kato_local_existence` for `(A, F)` and for the time-reversed system `(-A, -F)` (again symmetric),
glued at `t = 0` (`twoSided_of_forward`). -/
theorem kato_two_sided {m q : ℕ} (hm : (d : ℝ) / 2 < m) (hq : 2 * m ≤ q) (hq2 : m + 2 ≤ q)
    {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hsym : ∀ i a b v, A i a b v = A i b a v)
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ T > 0, ∀ U₀ : Fin n → ST d → ℝ, (∀ b, ContDiff ℝ ∞ (U₀ b)) →
      (∀ b, IsSPeriodic (U₀ b)) → energyQ q U₀ 0 ≤ R₀ ^ 2 →
      ∃ (U : Fin n → ST d → ℝ) (P : Fin n → Fin d → ST d → ℝ), TwoSidedSol A F U₀ T U P := by
  obtain ⟨T₁, hT₁, _, _, _, _, h₁⟩ := kato_local_existence (A := A) (F := F) hm hq hq2 hA hsym
    hF hR₀
  obtain ⟨T₂, hT₂, _, _, _, _, h₂⟩ := kato_local_existence (A := fun i a b v => -A i a b v)
    (F := fun a v => -F a v) hm hq hq2 (fun i a b => (hA i a b).neg)
    (fun i a b v => by rw [hsym]) (fun a => (hF a).neg) hR₀
  refine ⟨min T₁ T₂, lt_min hT₁ hT₂, fun U₀ hU hUp hE => ?_⟩
  obtain ⟨Up, Pp, c1, c2, c3, c4, c5, c6, c7, -⟩ := h₁ U₀ hU hUp hE
  obtain ⟨Um, Pm, d1, d2, d3, d4, d5, d6, d7, -⟩ := h₂ U₀ hU hUp hE
  have hp : ForwardSol A F U₀ T₁ Up Pp := ⟨c1, c2, c3, c4, c5, c6, c7⟩
  have hm' : ForwardSol (fun i a b v => -A i a b v) (fun a v => -F a v) U₀ T₂ Um Pm :=
    ⟨d1, d2, d3, d4, d5, d6, d7⟩
  exact ⟨_, _, twoSided_of_forward (lt_min hT₁ hT₂) (hp.mono (min_le_left _ _))
    (hm'.mono (min_le_right _ _))⟩

/-! ### Joint regularity and the complexified system -/

/-- The partial derivatives of a two-sided solution: `∂_t U = G(U)`, `∂_iU = P_i`. -/
def solPartial (A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ) (F : Fin n → (Fin n → ℝ) → ℝ)
    (U : Fin n → ST d → ℝ) (P : Fin n → Fin d → ST d → ℝ) (b : Fin n) :
    Fin (d + 1) → ST d → ℝ :=
  Fin.cases (genP A F U P b) fun i => P b i

theorem cons_line_zero (x : ST d) (s : ℝ) :
    x + s • ev (0 : Fin (d + 1)) = Fin.cons (x 0 + s) (Fin.tail x) := by
  funext μ
  induction μ using Fin.cases with
  | zero => simp
  | succ j => simp [Fin.tail, Pi.single_apply, Fin.succ_ne_zero]

section TwoSided

variable {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}
  {U₀ : Fin n → ST d → ℝ} {T : ℝ} {U : Fin n → ST d → ℝ} {P : Fin n → Fin d → ST d → ℝ}

theorem TwoSidedSol.continuous_genP (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b))
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) (h : TwoSidedSol A F U₀ T U P) (b : Fin n) :
    Continuous (genP A F U P b) := by
  unfold genP
  exact ((hF b).continuous.comp (continuous_pi h.contU)).sub (continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun b' _ => ((hA i b b').continuous.comp
      (continuous_pi h.contU)).mul (h.contP b' i))

theorem TwoSidedSol.hasDerivAt_line (h : TwoSidedSol A F U₀ T U P) (b : Fin n)
    {x : ST d} (hx : x ∈ openSlab (-T) T) (μ : Fin (d + 1)) :
    HasDerivAt (fun s : ℝ => U b (x + s • Pi.single μ 1)) (solPartial A F U P b μ x) 0 := by
  induction μ using Fin.cases with
  | zero =>
    have ht := h.time b (x 0) hx (Fin.tail x)
    have ht' : HasDerivAt (fun s => U b (Fin.cons s (Fin.tail x)))
        (genP A F U P b (Fin.cons (x 0) (Fin.tail x))) (x 0 + 0) := by rwa [add_zero]
    have hc := ht'.comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_add (x 0))
    simp only [Function.comp_def, id] at hc
    have e : (fun s : ℝ => U b (x + s • Pi.single (0 : Fin (d + 1)) 1)) =
        fun s => U b (Fin.cons (x 0 + s) (Fin.tail x)) := by
      funext s; rw [← cons_line_zero]
    rw [e]
    simpa [solPartial, Fin.cons_self_tail, mul_one] using hc
  | succ i => exact h.space b i x

/-- **The two-sided solution is jointly `C¹` on the open slab.** -/
theorem TwoSidedSol.contDiffOn (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b))
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) (h : TwoSidedSol A F U₀ T U P) (b : Fin n) :
    ContDiffOn ℝ 1 (U b) (openSlab (-T) T) := by
  refine PartialC1.contDiffOn_one_of_partials (isOpen_openSlab _ _)
    (g := solPartial A F U P b) (fun μ => ?_) (fun μ x hx => h.hasDerivAt_line b hx μ)
  induction μ using Fin.cases with
  | zero => exact (h.continuous_genP hA hF b).continuousOn
  | succ i => exact (h.contP b i).continuousOn

theorem TwoSidedSol.pd_eq (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b))
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) (h : TwoSidedSol A F U₀ T U P) (b : Fin n)
    {x : ST d} (hx : x ∈ openSlab (-T) T) (μ : Fin (d + 1)) :
    pd (U b) μ x = solPartial A F U P b μ x := by
  have hd := PartialC1.hasFDerivAt_of_partials (isOpen_openSlab _ _)
    (g := solPartial A F U P b) (fun μ => by
      induction μ using Fin.cases with
      | zero => exact (h.continuous_genP hA hF b).continuousOn
      | succ i => exact (h.contP b i).continuousOn)
    (fun μ x hx => h.hasDerivAt_line b hx μ) hx
  unfold SobolevOpen.pd
  rw [hd.fderiv, PartialC1.partialCLM_apply]
  rw [Finset.sum_eq_single μ]
  · simp
  · intro ν _ hν; simp [Pi.single_apply, hν]
  · simp

/-- The complexified quasilinear system `(A, F)` (real symmetric coefficients evaluated on the real
part). -/
def complexSys (A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ) (F : Fin n → (Fin n → ℝ) → ℝ) :
    SymHypUniqueness.QLSymSys d (Fin n) :=
  ⟨fun j v i k => (A j i k (fun c => (v c).re) : ℂ), fun v b => (F b (fun c => (v c).re) : ℂ)⟩

/-- The complexification of a real field. -/
def cplx (U : Fin n → ST d → ℝ) (x : ST d) : Fin n → ℂ := fun b => (U b x : ℂ)

theorem complexSys_herm (hsym : ∀ i a b v, A i a b v = A i b a v) (j : Fin d)
    (v : Fin n → ℂ) (i k : Fin n) :
    (complexSys A F).A j v k i = star ((complexSys A F).A j v i k) := by
  simp [complexSys, hsym j k i]

/-- **The complexified two-sided solution solves the symmetric system** in the sense of
`SymHypUniqueness.QLSymSys.Solves` on `(-T, T)`. -/
theorem TwoSidedSol.solves (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b))
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) (h : TwoSidedSol A F U₀ T U P) :
    (complexSys A F).Solves (cplx U) (-T) T := by
  have hsm : ∀ b, ContDiffOn ℝ 1 (U b) (openSlab (-T) T) := h.contDiffOn hA hF
  refine ⟨?_, fun k x => ?_, fun x hx => ?_⟩
  · exact contDiffOn_pi.2 fun b => Complex.ofRealCLM.contDiff.comp_contDiffOn (hsm b)
  · funext b; simp [cplx, h.perU b k x]
  · have hdiff : ∀ b, DifferentiableAt ℝ (U b) x := fun b =>
      ((hsm b).differentiableOn one_ne_zero x hx).differentiableAt
        ((isOpen_openSlab _ _).mem_nhds hx)
    have hpd : ∀ μ, pd (cplx U) μ x = fun b => ((pd (U b) μ x : ℝ) : ℂ) := by
      intro μ
      have hf : HasFDerivAt (cplx U)
          (ContinuousLinearMap.pi fun b => Complex.ofRealCLM.comp (fderiv ℝ (U b) x)) x :=
        hasFDerivAt_pi.2 fun b => Complex.ofRealCLM.hasFDerivAt.comp x (hdiff b).hasFDerivAt
      unfold SobolevOpen.pd
      rw [hf.fderiv]
      funext b
      simp [SobolevOpen.pd]
    funext b
    simp only [hpd, h.pd_eq hA hF _ hx, solPartial, Fin.cases_zero, Fin.cases_succ, complexSys,
      PeriodicCube.mv, cplx, Complex.ofReal_re, Pi.add_apply, Finset.sum_apply]
    simp only [genP]
    push_cast
    ring

end TwoSided

/-! ### Bounds on slabs from periodicity -/

/-- A periodic field continuous on an open slab is bounded on every closed sub-slab. -/
theorem exists_bound_slab {E : Type*} [NormedAddCommGroup E] {f : ST d → E} {a b t₀ t₁ : ℝ}
    (hf : ContinuousOn f (openSlab a b)) (hp : IsSPeriodic f) (ha : a < t₀) (hb : t₁ < b) :
    ∃ C, ∀ x ∈ slab t₀ t₁, ‖f x‖ ≤ C := by
  set K : Set (ST d) := (fun p : ℝ × (Fin d → ℝ) => (Fin.cons p.1 p.2 : ST d)) ''
    (Set.Icc t₀ t₁ ×ˢ Set.Icc 0 1) with hK
  have hKc : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image continuous_cons2
  have hKs : K ⊆ openSlab a b := by
    rintro _ ⟨p, hp', rfl⟩
    exact ⟨ha.trans_le hp'.1.1, hp'.1.2.trans_lt hb⟩
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hf.mono hKs)
  refine ⟨C, fun x hx => ?_⟩
  have hfr : (fun i => Int.fract (Fin.tail x i)) ∈ Set.Icc (0 : Fin d → ℝ) 1 :=
    ⟨fun i => Int.fract_nonneg _, fun i => (Int.fract_lt_one _).le⟩
  have h1 := (hp.slice (x 0)).apply_fract (Fin.tail x)
  rw [Fin.cons_self_tail] at h1
  rw [← h1]
  exact hC _ ⟨(x 0, _), ⟨hx, hfr⟩, rfl⟩

theorem isSPeriodic_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ST d → E} (hp : IsSPeriodic f) : IsSPeriodic (fderiv ℝ f) := fun k x => by
  have : (fun z => f (z + sshift k)) = f := funext fun z => hp k z
  rw [← fderiv_comp_add_right, this]

theorem convex_slab (t₀ t₁ : ℝ) : Convex ℝ (slab (d := d) t₀ t₁) :=
  (convex_Icc t₀ t₁).linear_preimage (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℝ) 0)

/-- A periodic field `C¹` on an open slab is Lipschitz on every closed sub-slab. -/
theorem exists_lipschitzOnWith_slab {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ST d → E} {a b t₀ t₁ : ℝ} (hf : ContDiffOn ℝ 1 f (openSlab a b)) (hp : IsSPeriodic f)
    (ha : a < t₀) (hb : t₁ < b) : ∃ L : ℝ≥0, LipschitzOnWith L f (slab t₀ t₁) := by
  have hsub : slab (d := d) t₀ t₁ ⊆ openSlab a b := slab_subset_openSlab ha hb
  have hcd := hf.continuousOn_fderiv_of_isOpen (isOpen_openSlab a b) le_rfl
  obtain ⟨C, hC⟩ := exists_bound_slab hcd (isSPeriodic_fderiv hp) ha hb
  refine ⟨C.toNNReal, (convex_slab t₀ t₁).lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x hx => (hf.differentiableOn one_ne_zero x (hsub hx)).differentiableAt
      ((isOpen_openSlab a b).mem_nhds (hsub hx))) (fun x hx => ?_)⟩
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
  exact (hC x hx).trans (le_max_left _ _)

/-! ### Identification of analytic germs -/

theorem Solves.mono {N : Type*} [Fintype N] [DecidableEq N]
    {S : SymHypUniqueness.QLSymSys d N} {U : ST d → N → ℂ} {a b a' b' : ℝ}
    (h : S.Solves U a b) (ha : a ≤ a') (hb : b' ≤ b) : S.Solves U a' b' :=
  ⟨h.smooth.mono fun x hx => ⟨ha.trans_lt hx.1, hx.2.trans_le hb⟩, h.per,
    fun x hx => h.eqn x ⟨ha.trans_lt hx.1, hx.2.trans_le hb⟩⟩

theorem norm_re_le (v : Fin n → ℂ) : ‖(fun c => (v c).re)‖ ≤ ‖v‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun c => by
    rw [Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (norm_le_pi_norm v c)

theorem norm_re_sub_le (v w : Fin n → ℂ) :
    ‖(fun c => (v c).re) - (fun c => (w c).re)‖ ≤ ‖v - w‖ := by
  have : (fun c => (v c).re) - (fun c => (w c).re) = fun c => ((v - w) c).re := by
    funext c; simp
  rw [this]; exact norm_re_le _

/-- **Identification of the analytic germ with the Kato solution**
(`lem:generated-physical-identification`, uniqueness step).  Let `m > d/2`, `q ≥ 2m`,
`q ≥ m + 2`, `A^i` smooth real symmetric, `F` smooth, `R₀ ≥ 0`.  There is `T > 0` (depending only
on `R₀`) such that: if the constrained physical Cauchy problem has local analytic physical
solutions solving the symmetric system for data of the analytic core
(`SymHypUniqueness.AnalyticGermExistence` — the named Cauchy–Kovalevskaya gap of
`ass:constrained-initial-solver`), then for every smooth periodic datum `U₀` of the core with
`‖U₀‖_{H^q} ≤ R₀`, the two-sided Kato solution `U` on `(-T, T)` coincides on a common slab
`[0, t₁] × 𝕋^d` with a physical germ (`Physical Uphys`). -/
theorem kato_germ_identification {m q : ℕ} (hm : (d : ℝ) / 2 < m) (hq : 2 * m ≤ q)
    (hq2 : m + 2 ≤ q) {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ}
    {F : Fin n → (Fin n → ℝ) → ℝ} (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b))
    (hsym : ∀ i a b v, A i a b v = A i b a v) (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R₀ : ℝ}
    (hR₀ : 0 ≤ R₀) :
    ∃ T > 0, ∀ (Core : ((Fin d → ℝ) → Fin n → ℂ) → Prop) (Physical : (ST d → Fin n → ℂ) → Prop),
      SymHypUniqueness.AnalyticGermExistence (complexSys A F) 0 Core Physical →
      ∀ U₀ : Fin n → ST d → ℝ, (∀ b, ContDiff ℝ ∞ (U₀ b)) → (∀ b, IsSPeriodic (U₀ b)) →
        energyQ q U₀ 0 ≤ R₀ ^ 2 → Core (fun y b => (U₀ b (Fin.cons 0 y) : ℂ)) →
        ∃ (U : Fin n → ST d → ℝ) (P : Fin n → Fin d → ST d → ℝ), TwoSidedSol A F U₀ T U P ∧
          ∃ t₁ > 0, ∃ Uphys : ST d → Fin n → ℂ, Physical Uphys ∧
            ∀ x ∈ slab 0 t₁, cplx U x = Uphys x := by
  obtain ⟨T, hT, hex⟩ := kato_two_sided hm hq hq2 hA hsym hF hR₀
  refine ⟨T, hT, fun Core Physical hgerm U₀ hU hUp hE hcore => ?_⟩
  obtain ⟨U, P, hsol⟩ := hex U₀ hU hUp hE
  refine ⟨U, P, hsol, ?_⟩
  obtain ⟨ε, hε, Uphys, hphys, hsolves, hdata⟩ := hgerm _ hcore
  set δ := min ε T with hδ
  have hδ0 : 0 < δ := lt_min hε hT
  have hU' : (complexSys A F).Solves (cplx U) (-δ) δ :=
    Solves.mono (hsol.solves hA hF) (by linarith [min_le_right ε T]) (min_le_right _ _)
  have hV' : (complexSys A F).Solves Uphys (-δ) δ :=
    Solves.mono hsolves (by linarith [min_le_left ε T]) (by linarith [min_le_left ε T])
  have ha : -δ < 0 := by linarith
  have h01 : (0 : ℝ) < δ / 2 := by linarith
  have hb : δ / 2 < δ := by linarith
  -- bounds on the slab
  obtain ⟨B1, hB1⟩ := exists_bound_slab hU'.smooth.continuousOn hU'.per ha hb
  obtain ⟨B2, hB2⟩ := exists_bound_slab hV'.smooth.continuousOn hV'.per ha hb
  set ρ := max (max B1 B2) 0 with hρ
  have hρ0 : 0 ≤ ρ := le_max_right _ _
  set Ω : Set (Fin n → ℂ) := Metric.closedBall 0 ρ with hΩ
  have hUΩ : ∀ x ∈ slab 0 (δ / 2), cplx U x ∈ Ω := fun x hx => by
    rw [hΩ, mem_closedBall_zero_iff]
    exact (hB1 x hx).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hVΩ : ∀ x ∈ slab 0 (δ / 2), Uphys x ∈ Ω := fun x hx => by
    rw [hΩ, mem_closedBall_zero_iff]
    exact (hB2 x hx).trans ((le_max_right _ _).trans (le_max_left _ _))
  -- coefficient bounds on `Ω`
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
  -- Lipschitz bound for the Kato solution and derivative bound for the germ
  obtain ⟨LU, hLU⟩ := exists_lipschitzOnWith_slab hU'.smooth hU'.per ha hb
  have hpdc : ∀ j : Fin d, ∃ C, ∀ x ∈ slab 0 (δ / 2), ‖pd Uphys j.succ x‖ ≤ C := by
    intro j
    have hc : ContinuousOn (fun x => pd Uphys j.succ x) (openSlab (-δ) δ) :=
      (hV'.smooth.continuousOn_fderiv_of_isOpen (isOpen_openSlab _ _) le_rfl).clm_apply
        continuousOn_const
    have hp : IsSPeriodic (fun x => pd Uphys j.succ x) := fun k x => by
      simp only [SobolevOpen.pd, isSPeriodic_fderiv hV'.per k x]
    exact exists_bound_slab hc hp ha hb
  choose Cj hCj using hpdc
  set MV := ∑ j, max (Cj j) 0 with hMV
  have hMV0 : 0 ≤ MV := Finset.sum_nonneg fun j _ => le_max_right _ _
  have hVd : ∀ j : Fin d, ∀ x ∈ slab 0 (δ / 2), ‖pd Uphys j.succ x‖ ≤ MV := fun j x hx =>
    (hCj j x hx).trans ((le_max_left _ _).trans (Finset.single_le_sum
      (f := fun j => max (Cj j) 0) (fun j _ => le_max_right _ _) (Finset.mem_univ j)))
  have h0 : ∀ y : Fin d → ℝ, cplx U (Fin.cons 0 y) = Uphys (Fin.cons 0 y) := fun y => by
    rw [hdata y]
    funext b
    simp [cplx, hsol.init b y]
  exact ⟨δ / 2, h01, Uphys, hphys, SymHypUniqueness.QLSymSys.unique (complexSys A F) ha h01 hb
    hU' hV' hUΩ hVΩ (complexSys_herm hsym) hAlip hAbd hFlip hLU hMV0 hVd h0⟩

/-! ### Non-vacuity -/

/-- The zero field solves the complexified system when `F(0) = 0`. -/
theorem zero_solves_complexSys {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ}
    {F : Fin n → (Fin n → ℝ) → ℝ} (hF0 : ∀ b, F b 0 = 0) (a b : ℝ) :
    (complexSys A F).Solves (fun _ _ => 0) a b := by
  refine ⟨contDiffOn_const, fun _ _ => rfl, fun x _ => ?_⟩
  funext c
  have h0 : (fun c' : Fin n => ((0 : Fin n → ℂ) c').re) = 0 := by funext; simp
  simp only [complexSys, SobolevOpen.pd, PeriodicCube.mv, h0]
  have := hF0 c
  simp only [Pi.zero_def] at this
  simp [this, PeriodicCube.mv_zero]

/-- **Non-vacuity of `kato_germ_identification`**: for the system `∂_tU + σ₁∂_1U = -U` on `𝕋³`
with the analytic core `{0}` and the trivial physical predicate, `AnalyticGermExistence` holds
(the zero germ) and the theorem applies to the zero datum. -/
example : ∃ T > 0, ∃ (U : Fin 2 → ST 3 → ℝ) (P : Fin 2 → Fin 3 → ST 3 → ℝ),
    TwoSidedSol exampleA (fun a v => -v a) (fun _ _ => 0) T U P ∧ ∃ t₁ > 0,
      ∀ x ∈ slab 0 t₁, cplx U x = 0 := by
  obtain ⟨T, hT, h⟩ := kato_germ_identification (d := 3) (n := 2) (m := 2) (q := 4)
    (by norm_num) le_rfl le_rfl (A := exampleA) (F := fun a v => -v a)
    (fun _ _ _ => by unfold exampleA; exact contDiff_const)
    (fun i a b v => by
      unfold exampleA
      by_cases h : a = b
      · subst h; rfl
      · simp [h, Ne.symm h])
    (fun a => (contDiff_apply ℝ ℝ a).neg) zero_le_one
  have hgerm : SymHypUniqueness.AnalyticGermExistence (complexSys exampleA (fun a v => -v a)) 0
      (fun U₀ => U₀ = fun _ _ => 0) (fun Uphys => Uphys = fun _ _ => 0) := by
    intro U₀ hU₀
    refine ⟨1, one_pos, fun _ _ => 0, rfl, zero_solves_complexSys (fun b => by simp) _ _,
      fun y => ?_⟩
    rw [hU₀]
  obtain ⟨U, P, hsol, t₁, ht₁, Uphys, hphys, hid⟩ := h _ _ hgerm (fun _ _ => 0)
    (fun _ => contDiff_const) (fun _ _ _ => rfl) (by rw [energyQ_zero]; norm_num)
    (by funext y b; simp)
  refine ⟨T, hT, U, P, hsol, t₁, ht₁, fun x hx => ?_⟩
  rw [hid x hx, hphys]; rfl

end RenewalGeometry.KatoGalerkin
