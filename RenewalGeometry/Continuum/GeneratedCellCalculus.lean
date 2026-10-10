/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedCellIntegrals
import RenewalGeometry.Gravity.ActualJetFieldBridge

/-!
# Calculus of jet functionals on slab cells

Generic infrastructure for the first variation of the comparison action of
`thm:generated-dynamics` (Einstein–Standard-Model action-closure manuscript,
`eq:generated-stationarity`):

* `Tuple.det_neg` — the metric of a smooth actual field tuple is Lorentzian, `det g < 0`;
* `cellInt_congr`, **`cellInt_pd_succ_loc`**, **`cellInt_pd_zero_loc`** — cell integrals only see
  the cell; divergence identities for fields smooth near the cell;
* **`cell_deriv_of_jet`** — `d/dε ∫_{cell} L(j(x) + εv(x)) = ∫_{cell} DL(j(x))[v(x)]` for a jet
  functional `L` smooth on an open chart containing the line segments;
* **`sint_deriv_of_jet`** — the same for slice integrals.
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff Real

noncomputable section

namespace RenewalGeometry.GenCell

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg KatoGalerkin

set_option linter.unusedSectionVars false

variable {d : ℕ}

/-! ### Cell integrals only see the cell -/

theorem cellInt_congr {f g : ST d → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ t ∈ Icc a b, ∀ y ∈ Icc (0 : Fin d → ℝ) 1, f (Fin.cons t y) = g (Fin.cons t y)) :
    cellInt a b f = cellInt a b g := by
  unfold cellInt
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hab] at ht
  unfold sint
  exact setIntegral_congr_fun measurableSet_Icc fun y hy => h t ht y hy

theorem cons_mem_openSlab {a' b' t : ℝ} (ht : t ∈ Ioo a' b') (y : Fin d → ℝ) :
    (Fin.cons t y : ST d) ∈ openSlab a' b' := by
  show a' < (Fin.cons t y : ST d) 0 ∧ (Fin.cons t y : ST d) 0 < b'
  simpa using ht

theorem slice_contDiff_of_on {f : ST d → ℝ} {a' b' : ℝ} (hf : ContDiffOn ℝ ∞ f (openSlab a' b'))
    {t : ℝ} (ht : t ∈ Ioo a' b') : ContDiff ℝ ∞ (fun y : Fin d → ℝ => f (Fin.cons t y)) :=
  hf.comp_contDiff (contDiff_cons t) fun y => cons_mem_openSlab ht y

theorem differentiableAt_of_on {f : ST d → ℝ} {a' b' : ℝ}
    (hf : ContDiffOn ℝ ∞ f (openSlab a' b')) {x : ST d} (hx : x ∈ openSlab a' b') :
    DifferentiableAt ℝ f x :=
  (hf.contDiffAt ((isOpen_openSlab a' b').mem_nhds hx)).differentiableAt (by simp)

/-- **Spatial divergences integrate to zero** for fields smooth near the cell. -/
theorem cellInt_pd_succ_loc {f : ST d → ℝ} {a' a b b' : ℝ} (hf : ContDiffOn ℝ ∞ f (openSlab a' b'))
    (hp : IsSPeriodic f) (ha : a' < a) (hab : a ≤ b) (hb : b < b') (i : Fin d) :
    cellInt a b (pd f i.succ) = 0 := by
  unfold cellInt
  have hz : ∀ t ∈ uIcc a b, sint (pd f i.succ) t = 0 := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht' : t ∈ Ioo a' b' := ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
    have hs := slice_contDiff_of_on hf ht'
    unfold sint
    have e : ∀ y : Fin d → ℝ, pd f i.succ (Fin.cons t y) = pd (fun y => f (Fin.cons t y)) i y :=
      fun y => (pd_slice i (differentiableAt_of_on hf (cons_mem_openSlab ht' y))).symm
    simp only [e]
    exact integral_pd_eq_zero (hs.of_le (by exact_mod_cast le_top)) (hp.slice t) i
  rw [intervalIntegral.integral_congr hz]
  simp

/-- The time derivative of a slice integral for fields smooth near the slice. -/
theorem hasDerivAt_sint_time {f : ST d → ℝ} {a' b' : ℝ} (hf : ContDiffOn ℝ ∞ f (openSlab a' b'))
    {t : ℝ} (ht : t ∈ Ioo a' b') : HasDerivAt (sint f) (sint (pd f 0) t) t := by
  -- the frozen family `F_s(x) = f(s, x_spatial)`
  set F : ℝ → ST d → ℝ := fun s x => f (Fin.cons s (Fin.tail x)) with hFdef
  set F' : ℝ → ST d → ℝ := fun s x => pd f 0 (Fin.cons s (Fin.tail x)) with hF'def
  set O : Set (ℝ × ST d) := {p | p.1 ∈ Ioo a' b'} with hOdef
  have hO : IsOpen O := isOpen_Ioo.preimage continuous_fst
  have hmap : Continuous (fun p : ℝ × ST d => (Fin.cons p.1 (Fin.tail p.2) : ST d)) := by
    have h1 : Continuous (fun p : ℝ × ST d => (p.1, Fin.tail p.2)) :=
      continuous_fst.prodMk ((continuous_pi fun i : Fin d => continuous_apply (i.succ : Fin (d + 1))).comp
        continuous_snd)
    exact continuous_cons2.comp h1
  have hmapO : ∀ p ∈ O, (Fin.cons p.1 (Fin.tail p.2) : ST d) ∈ openSlab a' b' := fun p hp =>
    cons_mem_openSlab hp _
  have hFc : ContinuousOn (fun p : ℝ × ST d => F p.1 p.2) O :=
    hf.continuousOn.comp hmap.continuousOn hmapO
  have hpd : ContDiffOn ℝ ∞ (pd f 0) (openSlab a' b') := by
    intro x hx
    have h := (hf.contDiffAt ((isOpen_openSlab a' b').mem_nhds hx))
    unfold SobolevOpen.pd
    exact ((h.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).contDiffWithinAt
  have hF'c : ContinuousOn (fun p : ℝ × ST d => F' p.1 p.2) O :=
    hpd.continuousOn.comp hmap.continuousOn hmapO
  have hd : ∀ p ∈ O, HasDerivAt (fun s => F s p.2) (F' p.1 p.2) p.1 := by
    intro p hp
    have hdx := differentiableAt_of_on hf (hmapO p hp)
    have h := ActualJetBridge.hasDerivAt_line0 hdx 0
    have e : ∀ s : ℝ, (Fin.cons p.1 (Fin.tail p.2) : ST d) + s • ev (0 : Fin (d + 1)) =
        Fin.cons (s + p.1) (Fin.tail p.2) := by
      intro s; funext μ
      induction μ using Fin.cases with
      | zero => simp [add_comm]
      | succ i => simp [Fin.succ_ne_zero]
    simp only [e] at h
    have h' : HasDerivAt (fun s => f (Fin.cons (s + p.1) (Fin.tail p.2)))
        (pd f 0 (Fin.cons p.1 (Fin.tail p.2))) (p.1 - p.1) := by rwa [sub_self]
    have h2 := h'.comp_sub_const p.1 p.1
    simp only [sub_add_cancel] at h2
    exact h2
  set r := min (t - a') (b' - t) / 2 with hr
  have hr0 : 0 < r := by have := ht.1; have := ht.2; rw [hr]; positivity
  have hr1 : 2 * r ≤ t - a' := by rw [hr]; linarith [min_le_left (t - a') (b' - t), ht.1]
  have hr2 : 2 * r ≤ b' - t := by rw [hr]; linarith [min_le_right (t - a') (b' - t), ht.2]
  have key := hasDerivAt_sint_param hFc hF'c hd (ε₀ := t) (r := r) (t := t) hr0
    (fun ε hε y _ => show ε ∈ Ioo a' b' from
      ⟨by linarith [hε.1, hr0], by linarith [hε.2, hr0]⟩)
  have h1 : (fun ε => sint (F ε) t) = sint f := by
    funext ε; unfold sint; simp [hFdef]
  have h2 : sint (F' t) t = sint (pd f 0) t := by
    unfold sint; simp [hF'def]
  rw [h1, h2] at key
  exact key

/-- **The time divergence integrates to the boundary slices** for fields smooth near the cell. -/
theorem cellInt_pd_zero_loc {f : ST d → ℝ} {a' a b b' : ℝ} (hf : ContDiffOn ℝ ∞ f (openSlab a' b'))
    (ha : a' < a) (hab : a ≤ b) (hb : b < b') :
    cellInt a b (pd f 0) = sint f b - sint f a := by
  unfold cellInt
  have hsub : ∀ t ∈ uIcc a b, t ∈ Ioo a' b' := fun t ht => by
    rw [uIcc_of_le hab] at ht
    exact ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
  have hderiv : ∀ t ∈ uIcc a b, HasDerivAt (sint f) (sint (pd f 0) t) t := fun t ht =>
    hasDerivAt_sint_time hf (hsub t ht)
  have hpd : ContDiffOn ℝ ∞ (pd f 0) (openSlab a' b') := by
    intro x hx
    have h := (hf.contDiffAt ((isOpen_openSlab a' b').mem_nhds hx))
    unfold SobolevOpen.pd
    exact ((h.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).contDiffWithinAt
  have hcont : ContinuousOn (sint (pd f 0)) (uIcc a b) := by
    intro t ht
    exact (hasDerivAt_sint_time hpd (hsub t ht)).continuousAt.continuousWithinAt
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)

/-! ### Jet functionals along lines -/

section JetLine

variable {J : Type*} [NormedAddCommGroup J] [NormedSpace ℝ J]

theorem jetLine_data {L : J → ℝ} {U : Set J} (hU : IsOpen U) (hL : ContDiffOn ℝ ∞ L U)
    {j v : ST d → J} (hj : Continuous j) (hv : Continuous v) :
    IsOpen {p : ℝ × ST d | j p.2 + p.1 • v p.2 ∈ U} ∧
    ContinuousOn (fun p : ℝ × ST d => L (j p.2 + p.1 • v p.2))
      {p : ℝ × ST d | j p.2 + p.1 • v p.2 ∈ U} ∧
    ContinuousOn (fun p : ℝ × ST d => fderiv ℝ L (j p.2 + p.1 • v p.2) (v p.2))
      {p : ℝ × ST d | j p.2 + p.1 • v p.2 ∈ U} ∧
    ∀ p ∈ {p : ℝ × ST d | j p.2 + p.1 • v p.2 ∈ U},
      HasDerivAt (fun ε => L (j p.2 + ε • v p.2)) (fderiv ℝ L (j p.2 + p.1 • v p.2) (v p.2)) p.1 := by
  have hc : Continuous (fun p : ℝ × ST d => j p.2 + p.1 • v p.2) :=
    (hj.comp continuous_snd).add (continuous_fst.smul (hv.comp continuous_snd))
  refine ⟨hU.preimage hc, hL.continuousOn.comp hc.continuousOn fun p hp => hp, ?_, ?_⟩
  · have hfd : ContinuousOn (fderiv ℝ L) U := hL.continuousOn_fderiv_of_isOpen hU (by simp)
    exact (hfd.comp hc.continuousOn fun p hp => hp).clm_apply (hv.comp continuous_snd).continuousOn
  · intro p hp
    have hdiff : DifferentiableAt ℝ L (j p.2 + p.1 • v p.2) :=
      (hL.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
    have hline : HasDerivAt (fun ε : ℝ => j p.2 + ε • v p.2) (v p.2) p.1 := by
      simpa using ((hasDerivAt_id p.1).smul_const (v p.2)).const_add (j p.2)
    exact hdiff.hasFDerivAt.comp_hasDerivAt p.1 hline

/-- **First variation of a cell integral of a jet functional.** -/
theorem cell_deriv_of_jet {L : J → ℝ} {U : Set J} (hU : IsOpen U) (hL : ContDiffOn ℝ ∞ L U)
    {j v : ST d → J} (hj : Continuous j) (hv : Continuous v) {r a b : ℝ} (hr : 0 < r)
    (hab : a ≤ b)
    (hK : ∀ ε ∈ Icc (-r) r, ∀ t ∈ Icc a b, ∀ y ∈ Icc (0 : Fin d → ℝ) 1,
      j (Fin.cons t y) + ε • v (Fin.cons t y) ∈ U) :
    HasDerivAt (fun ε : ℝ => cellInt a b (fun x => L (j x + ε • v x)))
      (cellInt a b (fun x => fderiv ℝ L (j x) (v x))) 0 := by
  obtain ⟨hO, hFc, hF'c, hd⟩ := jetLine_data hU hL hj hv
  have h := hasDerivAt_cellInt_param (F := fun ε x => L (j x + ε • v x))
    (F' := fun ε x => fderiv ℝ L (j x + ε • v x) (v x)) hO hFc hF'c hd hr hab
    (fun ε hε t ht y hy => hK ε hε t ht y hy)
  simpa using h

/-- **First variation of a slice integral of a jet functional.** -/
theorem sint_deriv_of_jet {L : J → ℝ} {U : Set J} (hU : IsOpen U) (hL : ContDiffOn ℝ ∞ L U)
    {j v : ST d → J} (hj : Continuous j) (hv : Continuous v) {r t : ℝ} (hr : 0 < r)
    (hK : ∀ ε ∈ Icc (-r) r, ∀ y ∈ Icc (0 : Fin d → ℝ) 1,
      j (Fin.cons t y) + ε • v (Fin.cons t y) ∈ U) :
    HasDerivAt (fun ε : ℝ => sint (fun x => L (j x + ε • v x)) t)
      (sint (fun x => fderiv ℝ L (j x) (v x)) t) 0 := by
  obtain ⟨hO, hFc, hF'c, hd⟩ := jetLine_data hU hL hj hv
  have h := hasDerivAt_sint_param (F := fun ε x => L (j x + ε • v x))
    (F' := fun ε x => fderiv ℝ L (j x + ε • v x) (v x)) hFc hF'c hd (ε₀ := 0) (r := r) (t := t)
    hr (fun ε hε y hy => hK ε (by simpa using hε) y hy)
  simpa using h

end JetLine

/-! ### Lorentzian tuples -/

open ActualJetBridge ActualJetSystem in
/-- **The metric of a smooth actual field tuple has negative determinant.** -/
theorem Tuple_det_neg {m : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [LieRingModule (ActualJetSmooth.MatLie m) V]
    [LieModule ℝ (ActualJetSmooth.MatLie m) V] {S : Type*} [NormedAddCommGroup S]
    [NormedSpace ℝ S] [FiniteDimensional ℝ S] {S' : Type*} [NormedAddCommGroup S']
    [NormedSpace ℝ S'] [FiniteDimensional ℝ S'] (z : Tuple m V S S') (x : ST 3) :
    (Matrix.of (z.g x)).det < 0 := by
  set E : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of (z.e x) with hE
  have hgi : Matrix.of (z.gi x) = E.transpose * Matrix.diagonal lorentzSign * E := by
    ext μ ν
    rw [Matrix.of_apply, z.compl x μ ν, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [Matrix.mul_apply, Finset.sum_eq_single A]
    · simp only [hE, Matrix.transpose_apply, Matrix.of_apply, Matrix.diagonal_apply_eq]
      ring
    · intro B _ hB; simp [Matrix.diagonal_apply_ne _ hB]
    · simp
  have hdiag : (Matrix.diagonal lorentzSign).det = -1 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_four]
    simp [lorentzSign]
  have hdetgi : (Matrix.of (z.gi x)).det = -(E.det ^ 2) := by
    rw [hgi, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdiag]
    ring
  have hprod : (Matrix.of (z.g x)).det * (Matrix.of (z.gi x)).det = 1 := by
    rw [← Matrix.det_mul]
    have : Matrix.of (z.g x) * Matrix.of (z.gi x) = 1 := by
      ext a c
      rw [Matrix.mul_apply, Matrix.one_apply]
      exact z.hinv x a c
    rw [this, Matrix.det_one]
  rw [hdetgi] at hprod
  have hE0 : E.det ≠ 0 := by
    intro h0; rw [h0] at hprod; simp at hprod
  have hpos : 0 < E.det ^ 2 := by positivity
  nlinarith

end RenewalGeometry.GenCell
