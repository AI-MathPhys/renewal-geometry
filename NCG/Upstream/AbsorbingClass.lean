/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Algebra.CanonicalReductions

/-!
# Almost-sure absorption into one closed recurrent class

Clause (iv) of `prop:terminal-component` (`manuscripts/renewal_emergence/renewal_emergence.tex`):
under a **stationary Markov law**, almost every trajectory lies in one
closed recurrent class — with a stationary initial law, from time zero
on.  The trajectory measure of the chain is the genuine
Ionescu–Tulcea measure `ProbabilityTheory.Kernel.trajMeasure` on
`ℕ → S`.

* `chainMeasure` — the law of the trajectory of the finite-state
  Markov chain with one-step matrix `P` started from `π`;
* `chainMeasure_map_eval` — **stationary marginals**: at every time
  the marginal law is `π`;
* `chainMeasure_pair_null` — any pairwise property implied by
  `π`-positivity of the current state and positivity of the
  transition holds almost surely at every step;
* `stationary_trajectory_in_closed_class` — almost surely the whole
  trajectory has positive stationary mass and stays in the
  communicating class of its starting point;
* `stationary_ae_in_one_closed_recurrent_class` — the packaged
  statement: almost every trajectory lies, from time `0`, inside one
  **closed** communicating class in which all states communicate;
* `deterministic_path_no_absorption` — sharpness: an explicit
  row-stochastic matrix and an infinite positive-probability path
  that never enters a closed class, so no pathwise statement holds
  without probabilistic qualification.
-/

namespace NCG

open MeasureTheory ProbabilityTheory Finset Preorder

variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
variable [MeasurableSpace S] [MeasurableSingletonClass S]

omit [DecidableEq S] [Fintype S] [Nonempty S] in
/-- Every subset of a finite measurable-singleton space is
measurable. -/
theorem measurableSet_of_finite [Finite S] (s : Set S) : MeasurableSet s :=
  s.toFinite.measurableSet

section Chain

variable (P : S → S → ℝ) (π : S → ℝ)
variable (hP0 : ∀ a b, 0 ≤ P a b) (hrow : ∀ a, ∑ b, P a b = 1)
variable (hπ0 : ∀ a, 0 ≤ π a) (hπ1 : ∑ a, π a = 1)

/-- The transition row of a row-stochastic matrix as a probability
mass function. -/
noncomputable def rowPMF (s : S) : PMF S :=
  PMF.ofFintype (fun t => ENNReal.ofReal (P s t)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun t _ => hP0 s t), hrow s,
      ENNReal.ofReal_one])

/-- The one-step transition kernel of the chain. -/
noncomputable def stepKernel : Kernel S S where
  toFun s := (rowPMF P hP0 hrow s).toMeasure
  measurable' := measurable_of_countable _

instance : IsMarkovKernel (stepKernel P hP0 hrow) :=
  ⟨fun _ => PMF.toMeasure.isProbabilityMeasure _⟩

omit [DecidableEq S] [Nonempty S] in
theorem stepKernel_apply (s : S) :
    stepKernel P hP0 hrow s = (rowPMF P hP0 hrow s).toMeasure := rfl

omit [DecidableEq S] [Nonempty S] in
theorem stepKernel_singleton (s t : S) :
    stepKernel P hP0 hrow s {t} = ENNReal.ofReal (P s t) := by
  rw [stepKernel_apply,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton t)]
  rfl

/-- The history-dependent form of the one-step kernel consumed by the
Ionescu–Tulcea construction: it reads the last coordinate. -/
noncomputable def chainKernel (n : ℕ) :
    Kernel (Π _i : Iic n, S) S :=
  (stepKernel P hP0 hrow).comap
    (fun x => x ⟨n, mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)

instance (n : ℕ) : IsMarkovKernel (chainKernel P hP0 hrow n) := by
  unfold chainKernel
  infer_instance

omit [DecidableEq S] [Nonempty S] in
theorem chainKernel_apply (n : ℕ) (x : Π _i : Iic n, S) :
    chainKernel P hP0 hrow n x
      = (rowPMF P hP0 hrow (x ⟨n, mem_Iic.mpr le_rfl⟩)).toMeasure :=
  rfl

/-- The initial law as a measure. -/
noncomputable def initMeasure : Measure S :=
  (PMF.ofFintype (fun a => ENNReal.ofReal (π a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hπ0 a), hπ1,
      ENNReal.ofReal_one])).toMeasure

instance : IsProbabilityMeasure (initMeasure π hπ0 hπ1) :=
  PMF.toMeasure.isProbabilityMeasure _

omit [DecidableEq S] [Nonempty S] in
theorem initMeasure_singleton (a : S) :
    initMeasure π hπ0 hπ1 {a} = ENNReal.ofReal (π a) := by
  rw [initMeasure,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a)]
  rfl

/-- **The trajectory law of the stationary chain** — the genuine
Ionescu–Tulcea measure on the space of infinite trajectories. -/
noncomputable def chainMeasure : Measure (ℕ → S) :=
  Kernel.trajMeasure (X := fun _ => S) (initMeasure π hπ0 hπ1)
    (chainKernel P hP0 hrow)

instance : IsProbabilityMeasure (chainMeasure P π hP0 hrow hπ0 hπ1) := by
  unfold chainMeasure
  infer_instance

omit [DecidableEq S] in
omit [DecidableEq S] [Nonempty S] in
/-- The law of the position at time `0` is the initial law. -/
theorem chainMeasure_map_eval_zero :
    (chainMeasure P π hP0 hrow hπ0 hπ1).map (fun ω => ω 0)
      = initMeasure π hπ0 hπ1 := by
  have hfr : (chainMeasure P π hP0 hrow hπ0 hπ1).map (frestrictLe 0)
      = (initMeasure π hπ0 hπ1).map
          (MeasurableEquiv.piUnique
            (fun _i : Iic (0 : ℕ) => S)).symm := by
    rw [chainMeasure, Kernel.trajMeasure,
      Measure.map_comp _ _ (measurable_frestrictLe 0),
      Kernel.traj_map_frestrictLe, Kernel.partialTraj_self,
      Measure.id_comp]
  have hcomp : (chainMeasure P π hP0 hrow hπ0 hπ1).map (fun ω => ω 0)
      = ((chainMeasure P π hP0 hrow hπ0 hπ1).map (frestrictLe 0)).map
          (fun x : Π _i : Iic (0 : ℕ), S => x ⟨0, mem_Iic.mpr le_rfl⟩) :=
    (Measure.map_map
      (measurable_pi_apply (⟨0, mem_Iic.mpr le_rfl⟩ : Iic (0 : ℕ)))
      (measurable_frestrictLe 0)).symm
  have hcomp2 : (((initMeasure π hπ0 hπ1).map
        (MeasurableEquiv.piUnique
          (fun _i : Iic (0 : ℕ) => S)).symm).map
          (fun x : Π _i : Iic (0 : ℕ), S => x ⟨0, mem_Iic.mpr le_rfl⟩))
      = (initMeasure π hπ0 hπ1).map
          ((fun x : Π _i : Iic (0 : ℕ), S => x ⟨0, mem_Iic.mpr le_rfl⟩)
            ∘ ⇑(MeasurableEquiv.piUnique
              (fun _i : Iic (0 : ℕ) => S)).symm) :=
    Measure.map_map (measurable_pi_apply _) (by fun_prop)
  have hid : (fun x : Π _i : Iic (0 : ℕ), S => x ⟨0, mem_Iic.mpr le_rfl⟩)
      ∘ ⇑(MeasurableEquiv.piUnique (fun _i : Iic (0 : ℕ) => S)).symm
      = id := by
    funext a
    have hdef : (⟨0, mem_Iic.mpr le_rfl⟩ : Iic (0 : ℕ)) = default :=
      Unique.eq_default _
    simp [hdef]
  rw [hcomp, hfr, hcomp2, hid, Measure.map_id]

omit [DecidableEq S] in
omit [DecidableEq S] [Nonempty S] in
/-- The two-time marginal: the pair `(history to n, position n+1)`
has law `map (frestrictLe n) ⊗ₘ κ n`. -/
theorem chainMeasure_pair (n : ℕ) :
    (chainMeasure P π hP0 hrow hπ0 hπ1).map (frestrictLe n)
      ⊗ₘ chainKernel P hP0 hrow n
    = (chainMeasure P π hP0 hrow hπ0 hπ1).map
        (fun x => (frestrictLe n x, x (n + 1))) :=
  Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure

omit [DecidableEq S] [Nonempty S] in
/-- **Stationary marginals**: at every time the marginal law of the
chain is the stationary law. -/
theorem chainMeasure_map_eval
    (hstat : ∀ b, ∑ a, π a * P a b = π b) (n : ℕ) :
    (chainMeasure P π hP0 hrow hπ0 hπ1).map (fun ω => ω n)
      = initMeasure π hπ0 hπ1 := by
  induction n with
  | zero => exact chainMeasure_map_eval_zero P π hP0 hrow hπ0 hπ1
  | succ n ih =>
    -- the marginal of the pair law
    have hpair := chainMeasure_pair P π hP0 hrow hπ0 hπ1 n
    refine Measure.ext_of_singleton fun t => ?_
    have hmeas1 : Measurable fun ω : ℕ → S => ω (n + 1) :=
      measurable_pi_apply _
    have hmeas2 : Measurable fun x : ℕ → S =>
        (frestrictLe n x, x (n + 1)) := by fun_prop
    -- evaluate both sides of the pair identity on `univ ×ˢ {t}`
    have hset : MeasurableSet
        ((Set.univ : Set (Π _i : Iic n, S)) ×ˢ ({t} : Set S)) :=
      MeasurableSet.prod MeasurableSet.univ (measurableSet_singleton t)
    have hRHS : ((chainMeasure P π hP0 hrow hπ0 hπ1).map
        (fun x => (frestrictLe n x, x (n + 1))))
        (Set.univ ×ˢ {t})
        = ((chainMeasure P π hP0 hrow hπ0 hπ1).map
            (fun ω => ω (n + 1))) {t} := by
      rw [Measure.map_apply hmeas2 hset,
        Measure.map_apply hmeas1 (measurableSet_singleton t)]
      congr 1
      ext ω
      simp
    have hLHS : ((chainMeasure P π hP0 hrow hπ0 hπ1).map
          (frestrictLe n) ⊗ₘ chainKernel P hP0 hrow n)
        (Set.univ ×ˢ {t})
        = ENNReal.ofReal (π t) := by
      rw [Measure.compProd_apply hset]
      have h1 : ∀ x : Π _i : Iic n, S,
          chainKernel P hP0 hrow n x
            (Prod.mk x ⁻¹' (Set.univ ×ˢ ({t} : Set S)))
          = ENNReal.ofReal (P (x ⟨n, mem_Iic.mpr le_rfl⟩) t) := by
        intro x
        have h2 : Prod.mk x ⁻¹' (Set.univ ×ˢ ({t} : Set S))
            = ({t} : Set S) := by
          ext u
          simp
        rw [h2, chainKernel_apply,
          PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton t)]
        rfl
      rw [lintegral_congr h1]
      -- push forward to the time-`n` marginal
      have h3 : ∫⁻ x, ENNReal.ofReal
          (P (x ⟨n, mem_Iic.mpr le_rfl⟩) t)
          ∂((chainMeasure P π hP0 hrow hπ0 hπ1).map (frestrictLe n))
          = ∫⁻ s, ENNReal.ofReal (P s t)
              ∂((chainMeasure P π hP0 hrow hπ0 hπ1).map
                (fun ω => ω n)) := by
        have h4 : (chainMeasure P π hP0 hrow hπ0 hπ1).map
            (fun ω => ω n)
            = ((chainMeasure P π hP0 hrow hπ0 hπ1).map
                (frestrictLe n)).map
                (fun x => x ⟨n, mem_Iic.mpr le_rfl⟩) :=
          (Measure.map_map
            (measurable_pi_apply (⟨n, mem_Iic.mpr le_rfl⟩ : Iic n))
            (measurable_frestrictLe n)).symm
        rw [h4, lintegral_map (by fun_prop) (measurable_pi_apply _)]
      rw [h3, ih, lintegral_fintype]
      have h5 : ∀ s : S, ENNReal.ofReal (P s t)
          * initMeasure π hπ0 hπ1 {s}
          = ENNReal.ofReal (π s * P s t) := by
        intro s
        rw [initMeasure_singleton,
          ← ENNReal.ofReal_mul (hP0 s t), mul_comm]
      rw [Finset.sum_congr rfl fun s _ => h5 s,
        ← ENNReal.ofReal_sum_of_nonneg
          (fun s _ => mul_nonneg (hπ0 s) (hP0 s t)), hstat t]
    rw [← hRHS, ← hpair, hLHS, initMeasure_singleton]

omit [DecidableEq S] [Nonempty S] in
/-- **Almost-sure step property**: any pairwise property implied by
stationary positivity of the current state together with positivity
of the transition fails on a null set, at every time. -/
theorem chainMeasure_pair_null
    (hstat : ∀ b, ∑ a, π a * P a b = π b) (n : ℕ)
    {Q : S → S → Prop}
    (hQ : ∀ s t, 0 < π s → 0 < P s t → Q s t) :
    chainMeasure P π hP0 hrow hπ0 hπ1
      {ω | ¬ Q (ω n) (ω (n + 1))} = 0 := by
  classical
  have hpair := chainMeasure_pair P π hP0 hrow hπ0 hπ1 n
  have hmeas2 : Measurable fun x : ℕ → S =>
      (frestrictLe n x, x (n + 1)) := by fun_prop
  set Bad : Set (S × S) := {p | ¬ Q p.1 p.2} with hBad
  have hBadm : MeasurableSet Bad := (Bad.toFinite).measurableSet
  set T : Set ((Π _i : Iic n, S) × S) :=
    {p | (p.1 ⟨n, mem_Iic.mpr le_rfl⟩, p.2) ∈ Bad} with hT
  have hmT : Measurable fun p : (Π _i : Iic n, S) × S =>
      (p.1 ⟨n, mem_Iic.mpr le_rfl⟩, p.2) := by fun_prop
  have hTm : MeasurableSet T := hmT hBadm
  have hev : {ω : ℕ → S | ¬ Q (ω n) (ω (n + 1))}
      = (fun x : ℕ → S => (frestrictLe n x, x (n + 1))) ⁻¹' T := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hT, hBad]
    rfl
  rw [hev, ← Measure.map_apply hmeas2 hTm, ← hpair,
    Measure.compProd_apply hTm]
  -- each fibre integrand vanishes against the stationary marginal
  have h1 : ∀ x : Π _i : Iic n, S,
      chainKernel P hP0 hrow n x (Prod.mk x ⁻¹' T)
      = ∑ t ∈ Finset.univ.filter
          (fun t => ¬ Q (x ⟨n, mem_Iic.mpr le_rfl⟩) t),
          ENNReal.ofReal (P (x ⟨n, mem_Iic.mpr le_rfl⟩) t) := by
    intro x
    have h2 : Prod.mk x ⁻¹' T
        = {t | ¬ Q (x ⟨n, mem_Iic.mpr le_rfl⟩) t} := rfl
    rw [h2, chainKernel_apply, PMF.toMeasure_apply_fintype]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun t => ¬ Q (x ⟨n, mem_Iic.mpr le_rfl⟩) t)]
    have h3 : ∑ t ∈ Finset.univ.filter
        (fun t => ¬¬ Q (x ⟨n, mem_Iic.mpr le_rfl⟩) t),
        Set.indicator {t | ¬ Q (x ⟨n, mem_Iic.mpr le_rfl⟩) t}
          (⇑(rowPMF P hP0 hrow (x ⟨n, mem_Iic.mpr le_rfl⟩))) t
        = 0 := by
      refine Finset.sum_eq_zero fun t ht => ?_
      rw [Finset.mem_filter] at ht
      rw [Set.indicator_of_notMem]
      exact ht.2
    rw [h3, add_zero]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_filter] at ht
    rw [Set.indicator_of_mem ht.2]
    rfl
  rw [lintegral_congr h1]
  have h4 : ∫⁻ x, (∑ t ∈ Finset.univ.filter
        (fun t => ¬ Q (x ⟨n, mem_Iic.mpr le_rfl⟩) t),
        ENNReal.ofReal (P (x ⟨n, mem_Iic.mpr le_rfl⟩) t))
      ∂((chainMeasure P π hP0 hrow hπ0 hπ1).map (frestrictLe n))
      = ∫⁻ s, (∑ t ∈ Finset.univ.filter (fun t => ¬ Q s t),
          ENNReal.ofReal (P s t))
        ∂((chainMeasure P π hP0 hrow hπ0 hπ1).map (fun ω => ω n)) := by
    have h5 : (chainMeasure P π hP0 hrow hπ0 hπ1).map (fun ω => ω n)
        = ((chainMeasure P π hP0 hrow hπ0 hπ1).map
            (frestrictLe n)).map
            (fun x => x ⟨n, mem_Iic.mpr le_rfl⟩) :=
      (Measure.map_map
        (measurable_pi_apply (⟨n, mem_Iic.mpr le_rfl⟩ : Iic n))
        (measurable_frestrictLe n)).symm
    rw [h5, lintegral_map (measurable_of_countable _)
      (measurable_pi_apply _)]
  rw [h4, chainMeasure_map_eval P π hP0 hrow hπ0 hπ1 hstat,
    lintegral_fintype]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [initMeasure_singleton]
  rcases le_or_gt (π s) 0 with hs | hs
  · have h6 : ENNReal.ofReal (π s) = 0 := by
      rw [ENNReal.ofReal_eq_zero]
      exact hs
    rw [h6, mul_zero]
  · have h7 : ∀ t ∈ Finset.univ.filter (fun t => ¬ Q s t),
        ENNReal.ofReal (P s t) = 0 := by
      intro t ht
      rw [Finset.mem_filter] at ht
      rw [ENNReal.ofReal_eq_zero]
      rcases le_or_gt (P s t) 0 with h | h
      · exact h
      · exact absurd (hQ s t hs h) ht.2
    rw [Finset.sum_congr rfl h7, Finset.sum_const, smul_zero,
      zero_mul]

omit [DecidableEq S] [Nonempty S] in
/-- **Clause (iv), core event**: almost surely every state of the
trajectory carries positive stationary mass and communicates with the
starting state — the trajectory stays inside one communicating class
of the support graph. -/
theorem stationary_trajectory_in_closed_class
    (hstat : ∀ b, ∑ a, π a * P a b = π b) :
    chainMeasure P π hP0 hrow hπ0 hπ1
      {ω | ¬ ∀ n : ℕ, 0 < π (ω n)
        ∧ Reaches P (ω 0) (ω n) ∧ Reaches P (ω n) (ω 0)} = 0 := by
  set Q : S → S → Prop := fun s t => 0 < π s ∧ 0 < P s t with hQdef
  have hQ : ∀ s t, 0 < π s → 0 < P s t → Q s t :=
    fun s t hs ht => ⟨hs, ht⟩
  have hsub : {ω : ℕ → S | ¬ ∀ n : ℕ, 0 < π (ω n)
        ∧ Reaches P (ω 0) (ω n) ∧ Reaches P (ω n) (ω 0)}
      ⊆ ⋃ n : ℕ, {ω : ℕ → S | ¬ Q (ω n) (ω (n + 1))} := by
    intro ω hω
    by_contra hnot
    rw [Set.mem_iUnion] at hnot
    push Not at hnot
    have hall : ∀ n, Q (ω n) (ω (n + 1)) := by
      intro n
      have h1 := hnot n
      rw [Set.mem_setOf_eq] at h1
      exact not_not.mp h1
    have hstep : ∀ n, 0 < π (ω n) ∧ 0 < P (ω n) (ω (n + 1)) :=
      fun n => hall n
    have hreach : ∀ n, Reaches P (ω 0) (ω n) := by
      intro n
      induction n with
      | zero => exact Relation.ReflTransGen.refl
      | succ n ih => exact ih.tail (hstep n).2
    refine hω fun n => ⟨(hstep n).1, hreach n, ?_⟩
    exact (stationary_supported_on_terminal hP0 hrow hπ0 hstat
      (hstep 0).1 (hreach n)).2
  refine measure_mono_null hsub ?_
  exact measure_iUnion_null fun n =>
    chainMeasure_pair_null P π hP0 hrow hπ0 hπ1 hstat n hQ

omit [DecidableEq S] [Nonempty S] in
/-- **Proposition `prop:terminal-component` (iv)**: under a
stationary Markov law, almost every trajectory lies — from time `0`
on — inside one closed communicating class in which all states
communicate and carry positive stationary mass. -/
theorem stationary_ae_in_one_closed_recurrent_class
    (hstat : ∀ b, ∑ a, π a * P a b = π b) :
    ∀ᵐ ω ∂(chainMeasure P π hP0 hrow hπ0 hπ1),
      ∃ C : Set S, (∀ n, ω n ∈ C)
        ∧ (∀ x ∈ C, ∀ y, 0 < P x y → y ∈ C)
        ∧ (∀ x ∈ C, ∀ y ∈ C, Reaches P x y ∧ Reaches P y x)
        ∧ (∀ x ∈ C, 0 < π x) := by
  rw [ae_iff]
  refine measure_mono_null ?_
    (stationary_trajectory_in_closed_class P π hP0 hrow hπ0 hπ1 hstat)
  intro ω hω
  rw [Set.mem_setOf_eq] at hω ⊢
  intro hall
  refine hω ?_
  -- the class of the starting state
  set C : Set S :=
    {y | Reaches P (ω 0) y ∧ Reaches P y (ω 0)} with hC
  have h0 : 0 < π (ω 0) := (hall 0).1
  refine ⟨C, ?_, ?_, ?_, ?_⟩
  · exact fun n => ⟨(hall n).2.1, (hall n).2.2⟩
  · rintro x ⟨hx1, hx2⟩ y hxy
    have hreach : Reaches P (ω 0) y := hx1.tail hxy
    exact ⟨hreach,
      (stationary_supported_on_terminal hP0 hrow hπ0 hstat
        h0 hreach).2⟩
  · rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩
    exact ⟨hx2.trans hy1, hy2.trans hx1⟩
  · rintro x ⟨hx1, _⟩
    exact support_reaches hP0 hπ0 hstat h0 hx1

end Chain

/-- **Clause (iv), sharpness**: a deterministic infinite path may
ignore an available exit forever — an explicit row-stochastic matrix
and a positive-probability path none of whose states lies in a closed
class. -/
theorem deterministic_path_no_absorption :
    ∃ (P : Bool → Bool → ℝ) (ω : ℕ → Bool),
      (∀ a b, 0 ≤ P a b) ∧ (∀ a, ∑ b, P a b = 1)
      ∧ (∀ n, 0 < P (ω n) (ω (n + 1)))
      ∧ ∀ n, ∃ y, 0 < P (ω n) y ∧ ¬ Reaches P y (ω n) := by
  refine ⟨fun a b => if a then (if b then 1 else 0) else 1 / 2,
    fun _ => false, ?_, ?_, ?_, ?_⟩
  · intro a b
    rcases a <;> rcases b <;> norm_num
  · intro a
    rw [Fintype.sum_bool]
    rcases a <;> norm_num
  · intro n
    norm_num
  · intro n
    refine ⟨true, by norm_num, ?_⟩
    intro hreach
    -- everything reachable from `true` is `true`
    have hkey : ∀ z : Bool, Reaches
        (fun a b => if a then (if b then (1 : ℝ) else 0) else 1 / 2)
        true z → z = true := by
      intro z hz
      induction hz with
      | refl => rfl
      | tail _ hstep ih =>
        rename_i b c _
        rw [ih] at hstep
        unfold stepRel at hstep
        rcases c with _ | _
        · norm_num at hstep
        · rfl
    exact Bool.noConfusion (hkey false hreach)

end NCG
