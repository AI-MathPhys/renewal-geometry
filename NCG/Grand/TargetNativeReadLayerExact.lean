/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteTargetProjectionAndQuotients

/-!
# Target-native read layer: remaining exact clauses

Completes the finite target-native probability records on top of
`FiniteTargetProjectionAndQuotients`:

* `thm:GT-projected-likelihood-tower` — the conditional-expectation
  form of the projected likelihood (`projectedLikelihood_eq_condExp`),
  the exact equivalence "every `T`-measurable value is reconstructed
  from a projected density ⟺ `ϱ_T ≪ ν_T`"
  (`dominated_iff_reconstruction`), and the explicit finite
  witnesses that neither domination converse holds
  (`current_domination_not_full`, `separator_domination_not_current`);
* `thm:GT-complex-quotient-tower` — the conditional-Jensen `L¹`
  chain (`complex_jensen_chain`), the positive-shadow criterion
  `w_T/Z ≥ 0` (`positive_shadow_iff`), the `Z = 0` obstruction
  (`no_normalized_law_of_zero_amplitude`), and the complex Lebesgue
  decomposition on a record (`complex_lebesgue_decomposition`);
* `cor:GT-phase-quenched-quotient` — visibility, the coarse-grained
  total variation `|ζ_S| = Z_abs·|a_S|·π_S`
  (`coarse_variation_eq`), the coarse canonical law
  (`coarse_phase_quenched_density`), and the exact cancellation debit
  (`cancellation_debit`).

Everything is finite and fully derived: measures are weight rows on
finite records, conditional expectations are fibre averages, and
all zero-safe divisions are handled explicitly.
-/

open Finset

namespace NCG
namespace FiniteTargetProjectionAndQuotients

open AcceptedActionInformationPythagoras

/-! ### Projected likelihood as a conditional expectation -/

/-- Fibre average (conditional expectation given `T = x`) of `L` under
the reference row `ν`. -/
noncomputable def fibreCondExp {Omega X : Type*} [Fintype Omega]
    [DecidableEq X] (T : Omega → X) (ν L : Omega → ℝ) (x : X) : ℝ :=
  (Finset.univ.filter (fun ω => T ω = x)).sum (fun ω => ν ω * L ω)
    / pushforwardRow T ν x

/-- **Boxed**: `ℓ_T ∘ T = 𝔼_ν[L | T]` — the projected likelihood of
`ϱ = L·ν` is the fibre conditional expectation of `L`. -/
theorem projectedLikelihood_eq_condExp {Omega X : Type*} [Fintype Omega]
    [DecidableEq X] (T : Omega → X) (ν L : Omega → ℝ) (x : X) :
    projectedLikelihood T (fun ω => L ω * ν ω) ν x
      = fibreCondExp T ν L x := by
  unfold projectedLikelihood fibreCondExp pushforwardRow
  congr 1
  exact Finset.sum_congr rfl fun ω _ => by ring

/-! ### Domination ⟺ reconstruction -/

/-- Integrating the fibre indicator of `x` gives the pushforward mass. -/
theorem realIntegral_fibre_indicator {Omega X : Type*} [Fintype Omega]
    [DecidableEq X] (T : Omega → X) (ρ : Omega → ℝ) (x : X) :
    realIntegral ρ (fun ω => if T ω = x then (1 : ℝ) else 0)
      = pushforwardRow T ρ x := by
  unfold realIntegral pushforwardRow
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : T ω = x <;> simp [h]

theorem realIntegral_fibre_indicator_mul {Omega X : Type*} [Fintype Omega]
    [DecidableEq X] (T : Omega → X) (ν : Omega → ℝ) (ℓ : X → ℝ) (x : X) :
    realIntegral ν (fun ω => ℓ (T ω) * if T ω = x then (1 : ℝ) else 0)
      = ℓ x * pushforwardRow T ν x := by
  unfold realIntegral pushforwardRow
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : T ω = x
  · simp [h]
    ring
  · simp [h]

/-- `ϱ_T ≪ ν_T` on a finite record. -/
def RecordDominated {Omega X : Type*} [Fintype Omega] [DecidableEq X]
    (T : Omega → X) (ρ ν : Omega → ℝ) : Prop :=
  ∀ x, pushforwardRow T ν x = 0 → pushforwardRow T ρ x = 0

set_option linter.unusedFintypeInType false in
/-- **Boxed equivalence**: reconstruction of every `T`-measurable active
value from a projected density is equivalent to `ϱ_T ≪ ν_T`, whether
or not a full-history density exists. -/
theorem dominated_iff_reconstruction {Omega X : Type*} [Fintype Omega]
    [Fintype X] [DecidableEq X] (T : Omega → X) (ρ ν : Omega → ℝ) :
    RecordDominated T ρ ν ↔
      ∃ ℓ : X → ℝ, ∀ f : X → ℝ,
        realIntegral ρ (fun ω => f (T ω))
          = realIntegral ν (fun ω => ℓ (T ω) * f (T ω)) := by
  constructor
  · intro hdom
    let ℓ : X → ℝ := fun x => if pushforwardRow T ν x = 0 then 0
      else pushforwardRow T ρ x / pushforwardRow T ν x
    refine ⟨ℓ, fun f => ?_⟩
    rw [real_pushforward_change_variables T ρ f,
      real_pushforward_change_variables T ν (fun x => ℓ x * f x)]
    unfold realIntegral
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h : pushforwardRow T ν x = 0
    · simp [ℓ, h, hdom x h]
    · simp only [ℓ, if_neg h]
      field_simp
  · rintro ⟨ℓ, hℓ⟩ x hx
    have h := hℓ (fun y => if y = x then 1 else 0)
    rw [realIntegral_fibre_indicator, realIntegral_fibre_indicator_mul,
      hx, mul_zero] at h
    exact h

/-- Full-history domination implies record domination. -/
theorem record_dominated_of_full {Omega X : Type*} [Fintype Omega]
    [DecidableEq X] (T : Omega → X) (ρ ν : Omega → ℝ)
    (hν : ∀ ω, 0 ≤ ν ω) (_hρ : ∀ ω, 0 ≤ ρ ω)
    (hfull : ∀ ω, ν ω = 0 → ρ ω = 0) :
    RecordDominated T ρ ν := by
  intro x hx
  unfold pushforwardRow at hx ⊢
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun ω _ => hν ω)).mp hx
  exact Finset.sum_eq_zero fun ω hω => hfull ω (hzero ω hω)

set_option linter.unusedFintypeInType false in
/-- Record domination descends to coarser records. -/
theorem record_dominated_comp {Omega X Y : Type*} [Fintype Omega]
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (T : Omega → X) (s : X → Y) (ρ ν : Omega → ℝ)
    (hν : ∀ ω, 0 ≤ ν ω) (_hρ : ∀ ω, 0 ≤ ρ ω)
    (hdom : RecordDominated T ρ ν) :
    RecordDominated (fun ω => s (T ω)) ρ ν := by
  intro y hy
  rw [real_pushforward_comp T s ν] at hy
  rw [real_pushforward_comp T s ρ]
  unfold pushforwardRow at hy ⊢
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun x _ => Finset.sum_nonneg fun ω _ => hν ω)).mp hy
  refine Finset.sum_eq_zero fun x hx => ?_
  have := hdom x (by unfold pushforwardRow; exact hzero x hx)
  unfold pushforwardRow at this
  exact this

/-- **Converse failure (current)**: a reference-null history can share a
current value with a reference-supported history, so current domination
does not imply full-history domination. -/
theorem current_domination_not_full :
    ∃ (ρ ν : Fin 2 → ℝ) (T : Fin 2 → Unit),
      (∀ ω, 0 ≤ ν ω) ∧ (∀ ω, 0 ≤ ρ ω) ∧
      RecordDominated T ρ ν ∧ ¬ (∀ ω, ν ω = 0 → ρ ω = 0) := by
  refine ⟨![0, 1], ![1, 0], fun _ => (), ?_, ?_, ?_, ?_⟩
  · intro ω; fin_cases ω <;> simp
  · intro ω; fin_cases ω <;> simp
  · intro x hx
    exfalso
    revert hx
    simp [pushforwardRow, Fin.sum_univ_two]
  · intro h
    have := h 1 (by simp)
    simp at this

/-- **Converse failure (separator)**: separator domination does not imply
current domination. -/
theorem separator_domination_not_current :
    ∃ (ρ ν : Fin 2 → ℝ) (T : Fin 2 → Fin 2) (s : Fin 2 → Unit),
      (∀ ω, 0 ≤ ν ω) ∧ (∀ ω, 0 ≤ ρ ω) ∧
      RecordDominated (fun ω => s (T ω)) ρ ν ∧
      ¬ RecordDominated T ρ ν := by
  refine ⟨![0, 1], ![1, 0], id, fun _ => (), ?_, ?_, ?_, ?_⟩
  · intro ω; fin_cases ω <;> simp
  · intro ω; fin_cases ω <;> simp
  · intro x hx
    exfalso
    revert hx
    simp [pushforwardRow, Fin.sum_univ_two]
  · intro h
    have := h 1 (by simp [pushforwardRow, Finset.sum_filter])
    simp [pushforwardRow, Finset.sum_filter] at this

/-! ### Complex quotient tower: Jensen, positive shadow, `Z = 0` -/

/-- **Conditional Jensen**: the `L¹(ν_T)` norms of projected complex
densities decrease along the tower
`‖w_S‖ ≤ ‖w_C‖ ≤ ‖w‖` (here as total variations of the projected
complex measures). -/
theorem complex_jensen_chain {Omega X Y : Type*} [Fintype Omega]
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (T : Omega → X) (s : X → Y) (ζ : Omega → ℂ) :
    complexVariation (complexPushforward (fun ω => s (T ω)) ζ)
        ≤ complexVariation (complexPushforward T ζ) ∧
    complexVariation (complexPushforward T ζ) ≤ complexVariation ζ := by
  constructor
  · unfold complexVariation
    simp_rw [complex_pushforward_comp T s ζ]
    calc (∑ y, ‖(Finset.univ.filter (fun x => s x = y)).sum
            (complexPushforward T ζ)‖)
        ≤ ∑ y, (Finset.univ.filter (fun x => s x = y)).sum
            (fun x => ‖complexPushforward T ζ x‖) :=
          Finset.sum_le_sum fun y _ => norm_sum_le _ _
      _ = ∑ x, ‖complexPushforward T ζ x‖ := by
          rw [← Finset.sum_fiberwise Finset.univ s
            (fun x => ‖complexPushforward T ζ x‖)]
  · unfold complexVariation
    calc (∑ x, ‖complexPushforward T ζ x‖)
        ≤ ∑ x, (Finset.univ.filter (fun ω => T ω = x)).sum
            (fun ω => ‖ζ ω‖) :=
          Finset.sum_le_sum fun x _ => norm_sum_le _ _
      _ = ∑ ω, ‖ζ ω‖ := by
          rw [← Finset.sum_fiberwise Finset.univ T (fun ω => ‖ζ ω‖)]

/-- **Positive shadow criterion**: with `Z = ζ_T(X) ≠ 0`, a positive
probability law `μ_T` and the single scalar `Z` reproduce every
`T`-measurable complex amplitude exactly iff `ζ_T/Z ≥ 0` pointwise. -/
theorem positive_shadow_iff {X : Type*} [Fintype X]
    (ζT : X → ℂ) (hZ : (∑ x, ζT x) ≠ 0) :
    (∃ μ : X → ℝ, (∀ x, 0 ≤ μ x) ∧ (∑ x, μ x) = 1 ∧
        ∀ f : X → ℂ, (∑ x, ζT x * f x)
          = (∑ x, ζT x) * ∑ x, (μ x : ℂ) * f x)
      ↔ ∀ x, ∃ r : ℝ, 0 ≤ r ∧ ζT x = (∑ x, ζT x) * r := by
  classical
  constructor
  · rintro ⟨μ, hμ0, _, hμ⟩ x
    refine ⟨μ x, hμ0 x, ?_⟩
    have h := hμ (fun y => if y = x then 1 else 0)
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h
    exact h
  · intro h
    choose r hr0 hr using h
    refine ⟨r, hr0, ?_, fun f => ?_⟩
    · have hsum : (∑ x, ζT x) = (∑ x, ζT x) * ∑ x, (r x : ℂ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => hr x
      have hsumr : ((∑ x, r x : ℝ) : ℂ) = 1 := by
        push_cast
        have := mul_left_cancel₀ hZ
          (hsum.symm.trans (mul_one _).symm)
        exact this
      exact_mod_cast hsumr
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by rw [hr x]; ring

/-- **`Z = 0` obstruction**: a nonzero projected complex measure with
zero total amplitude admits no normalized target law. -/
theorem no_normalized_law_of_zero_amplitude {X : Type*} [Fintype X]
    (ζT : X → ℂ) (hZ : (∑ x, ζT x) = 0) (hne : ζT ≠ 0) :
    ¬ ∃ (c : ℂ) (μ : X → ℝ), (∑ x, μ x) = 1 ∧
        ∀ x, ζT x = c * (μ x : ℂ) := by
  rintro ⟨c, μ, hμ, hζ⟩
  have hc : c = 0 := by
    have : (∑ x, ζT x) = c * ∑ x, (μ x : ℂ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => hζ x
    rw [hZ] at this
    have hμC : (∑ x, (μ x : ℂ)) = 1 := by
      exact_mod_cast hμ
    rw [hμC, mul_one] at this
    exact this.symm
  apply hne
  funext x
  rw [hζ x, hc, zero_mul]
  rfl

/-- Zero-safe projected complex density. -/
noncomputable def complexRegularDensity {X : Type*}
    (ζT : X → ℂ) (νT : X → ℝ) (x : X) : ℂ :=
  if νT x = 0 then 0 else ζT x / (νT x : ℂ)

/-- Projected singular complex part. -/
noncomputable def complexSingularPart {X : Type*}
    (ζT : X → ℂ) (νT : X → ℝ) (x : X) : ℂ :=
  if νT x = 0 then ζT x else 0

/-- **Complex Lebesgue decomposition on the record**:
`ζ_T = w_T·ν_T + ζ_T^⊥` with the singular part retained explicitly. -/
theorem complex_lebesgue_decomposition {X : Type*}
    (ζT : X → ℂ) (νT : X → ℝ) (x : X) :
    ζT x = complexRegularDensity ζT νT x * (νT x : ℂ)
      + complexSingularPart ζT νT x := by
  by_cases h : νT x = 0
  · simp [complexRegularDensity, complexSingularPart, h]
  · have hC : (νT x : ℂ) ≠ 0 := by exact_mod_cast h
    simp [complexRegularDensity, complexSingularPart, h, hC]

/-! ### Phase-quenched quotient: coarse graining -/

/-- Average-phase visibility `𝔳_T = |Z|/Z_abs`. -/
noncomputable def phaseVisibility {X : Type*} [Fintype X]
    (ζ : X → ℂ) : ℝ :=
  ‖∑ x, ζ x‖ / complexVariation ζ

/-- The visibility is at most one (and the condition number `𝔳⁻¹` is at
least one). -/
theorem phaseVisibility_le_one {X : Type*} [Fintype X] (ζ : X → ℂ)
    (hvar : complexVariation ζ ≠ 0) :
    phaseVisibility ζ ≤ 1 := by
  unfold phaseVisibility complexVariation at *
  have hpos : 0 < ∑ x, ‖ζ x‖ :=
    lt_of_le_of_ne (Finset.sum_nonneg fun x _ => norm_nonneg _)
      (Ne.symm hvar)
  rw [div_le_one hpos]
  exact norm_sum_le _ _

/-- Coarse-grained phase-quenched law `π_S = s_*π_T`. -/
noncomputable def coarsePhaseLaw {X Y : Type*} [Fintype X]
    [DecidableEq Y] (s : X → Y) (ζ : X → ℂ) (y : Y) : ℝ :=
  pushforwardRow s (phaseQuenchedLaw ζ) y

/-- Fibre-averaged phase `a_S = 𝔼_{π_T}[u_T | S]` (zero-safe). -/
noncomputable def fibrePhase {X Y : Type*} [Fintype X]
    [DecidableEq Y] (s : X → Y) (ζ : X → ℂ) (y : Y) : ℂ :=
  if coarsePhaseLaw s ζ y = 0 then 0 else
    ((Finset.univ.filter (fun x => s x = y)).sum
      (fun x => (phaseQuenchedLaw ζ x : ℂ) * polarPhase ζ x))
      / (coarsePhaseLaw s ζ y : ℂ)

/-- The coarse complex measure is `Z_abs·a_S·π_S`. -/
theorem coarse_complex_eq {X Y : Type*} [Fintype X] [DecidableEq Y]
    (s : X → Y) (ζ : X → ℂ) (hvar : complexVariation ζ ≠ 0) (y : Y) :
    complexPushforward s ζ y
      = (complexVariation ζ : ℂ) * fibrePhase s ζ y
          * (coarsePhaseLaw s ζ y : ℂ) := by
  obtain ⟨_, _, _, hpolar, _⟩ := phase_quenched_quotient ζ hvar
  unfold complexPushforward fibrePhase
  by_cases hy : coarsePhaseLaw s ζ y = 0
  · rw [if_pos hy]
    simp only [mul_zero, zero_mul]
    -- all fibre masses vanish, so every `ζ x` in the fibre is zero
    have hnn : ∀ x, 0 ≤ phaseQuenchedLaw ζ x := fun x =>
      div_nonneg (norm_nonneg _)
        (Finset.sum_nonneg fun x _ => norm_nonneg _)
    unfold coarsePhaseLaw pushforwardRow at hy
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun x _ => hnn x)).mp hy
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [hpolar x, hzero x hx]
    simp
  · rw [if_neg hy]
    have hyC : (coarsePhaseLaw s ζ y : ℂ) ≠ 0 := by exact_mod_cast hy
    rw [mul_assoc, div_mul_cancel₀ _ hyC, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [hpolar x]; ring

/-- **Boxed**: `|ζ_S| = Z_abs·|a_S|·π_S`. -/
theorem coarse_variation_eq {X Y : Type*} [Fintype X] [DecidableEq Y]
    (s : X → Y) (ζ : X → ℂ) (hvar : complexVariation ζ ≠ 0) (y : Y) :
    ‖complexPushforward s ζ y‖
      = complexVariation ζ * ‖fibrePhase s ζ y‖ * coarsePhaseLaw s ζ y := by
  rw [coarse_complex_eq s ζ hvar y, norm_mul, norm_mul]
  have hv : 0 ≤ complexVariation ζ :=
    Finset.sum_nonneg fun x _ => norm_nonneg _
  have hc : 0 ≤ coarsePhaseLaw s ζ y :=
    Finset.sum_nonneg fun x _ =>
      div_nonneg (norm_nonneg _)
        (Finset.sum_nonneg fun x _ => norm_nonneg _)
  rw [Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hv,
    Real.norm_of_nonneg hc]

/-- **Boxed**: the coarse canonical phase-quenched law has density
`|a_S| / 𝔼_{π_S}|a_S|` with respect to `π_S`. -/
theorem coarse_phase_quenched_density {X Y : Type*} [Fintype X]
    [Fintype Y] [DecidableEq Y]
    (s : X → Y) (ζ : X → ℂ) (hvar : complexVariation ζ ≠ 0)
    (hcoarse : complexVariation (complexPushforward s ζ) ≠ 0) (y : Y) :
    phaseQuenchedLaw (complexPushforward s ζ) y
      = ‖fibrePhase s ζ y‖
          / (∑ y', coarsePhaseLaw s ζ y' * ‖fibrePhase s ζ y'‖)
          * coarsePhaseLaw s ζ y := by
  have hvpos : 0 < complexVariation ζ :=
    lt_of_le_of_ne (Finset.sum_nonneg fun x _ => norm_nonneg _)
      (Ne.symm hvar)
  have hTV : complexVariation (complexPushforward s ζ)
      = complexVariation ζ
        * ∑ y', coarsePhaseLaw s ζ y' * ‖fibrePhase s ζ y'‖ := by
    rw [complexVariation, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y' _ => by
      rw [coarse_variation_eq s ζ hvar y']; ring
  have hsum_ne : (∑ y', coarsePhaseLaw s ζ y' * ‖fibrePhase s ζ y'‖) ≠ 0 := by
    intro h
    apply hcoarse
    rw [hTV, h, mul_zero]
  unfold phaseQuenchedLaw
  rw [coarse_variation_eq s ζ hvar y, hTV]
  field_simp

/-- **Boxed cancellation debit**:
`Z_abs - ‖ζ_S‖_TV = Z_abs·𝔼_{π_S}(1 - |a_S|)`, vanishing exactly when the
fibre phases are aligned. -/
theorem cancellation_debit {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] (s : X → Y) (ζ : X → ℂ)
    (hvar : complexVariation ζ ≠ 0) :
    complexVariation ζ - complexVariation (complexPushforward s ζ)
      = complexVariation ζ
        * ∑ y, coarsePhaseLaw s ζ y * (1 - ‖fibrePhase s ζ y‖) := by
  obtain ⟨_, hmass, _, _, _⟩ := phase_quenched_quotient ζ hvar
  have hcoarse_mass : (∑ y, coarsePhaseLaw s ζ y) = 1 := by
    unfold coarsePhaseLaw pushforwardRow
    rw [Finset.sum_fiberwise Finset.univ s (phaseQuenchedLaw ζ)]
    exact hmass
  have hTV : complexVariation (complexPushforward s ζ)
      = complexVariation ζ
        * ∑ y', coarsePhaseLaw s ζ y' * ‖fibrePhase s ζ y'‖ := by
    rw [complexVariation, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y' _ => by
      rw [coarse_variation_eq s ζ hvar y']; ring
  rw [hTV]
  have : (∑ y, coarsePhaseLaw s ζ y * (1 - ‖fibrePhase s ζ y‖))
      = (∑ y, coarsePhaseLaw s ζ y)
        - ∑ y, coarsePhaseLaw s ζ y * ‖fibrePhase s ζ y‖ := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [this, hcoarse_mass]
  ring

end FiniteTargetProjectionAndQuotients
end NCG
