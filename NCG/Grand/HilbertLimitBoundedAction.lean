/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Compatible future forms and the exact uniform-gap
  theorem (`thm:compatible-future-forms` and
  `thm:uniform-gap-limit`, Gran-Tensor manuscript)

Both theorems live on a Hilbert limit presented as a
complete space `H` with an increasing stage filtration
`S : ℕ → Submodule ℂ H` whose union is dense (the
finite-stage vectors of the direct limit, isometrically
embedded — the manuscript's compatible-form
identification).

* `compatible_future_forms`: the boxed criterion — a
  stage-compatible action `T₀` (a linear map on the
  union submodule) extends to a bounded operator on the
  limit **iff** the uniform stage bound
  `β = sup_m ‖L_a‖_{𝔤_m→𝔤_m} < ∞` holds (rendered as
  `∃ C, ∀ n, ∀ x ∈ S n, ‖T₀ x‖ ≤ C·‖x‖`); the bounded
  extension is unique.

* `uniform_gap_limit`: for a bounded operator `T` on the
  limit,
  (i) the boxed norm equality
      `‖T‖ = sup_X ρ_X` — the operator norm is the least
      upper bound of the stage restriction norms;
  (ii) the boxed power estimate: if `E` is an idempotent
      with `TE = ET = E` then `QTQ = T - E`
      (`Q = 1 - E`), and `‖QTQ‖ ≤ 1 - γ₀` gives
      `‖T^k - E‖ ≤ (1-γ₀)^k`;
  (iii) collapse: the stage-norm profile
      `ρ_X = 1 - 1/(X+1)` has every stage norm `< 1`
      while its least upper bound is `1` — positive
      finite-stage gaps do not give a uniform gap.

The GNS provenance of the uniform bound (a state form
gives `β ≤ ‖a‖`) is `thm:AF-limit-state`'s layer; the
direct-limit construction itself enters through the
dense-filtration presentation.
-/

open Filter

namespace NCG

section HilbertLimit

variable {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `thm:compatible-future-forms` (bounded action on the
Hilbert limit iff the boxed uniform stage bound; the
extension is unique). -/
theorem compatible_future_forms
    (S : ℕ → Submodule ℂ H) (hmono : Monotone S)
    (hdense : Dense ((⨆ n, S n : Submodule ℂ H) : Set H))
    (T₀ : (⨆ n, S n : Submodule ℂ H) →ₗ[ℂ] H) :
    -- the boxed iff
    ((∃ T : H →L[ℂ] H, ∀ (x : H)
        (hx : x ∈ (⨆ n, S n : Submodule ℂ H)),
        T x = T₀ ⟨x, hx⟩) ↔
      (∃ C : ℝ, ∀ n, ∀ (x : H) (hx : x ∈ S n),
        ‖T₀ ⟨x, Submodule.mem_iSup_of_mem n hx⟩‖
          ≤ C * ‖x‖))
    -- uniqueness of the bounded extension
    ∧ (∀ T T' : H →L[ℂ] H,
        (∀ (x : H) (hx : x ∈ (⨆ n, S n : Submodule ℂ H)),
          T x = T₀ ⟨x, hx⟩) →
        (∀ (x : H) (hx : x ∈ (⨆ n, S n : Submodule ℂ H)),
          T' x = T₀ ⟨x, hx⟩) →
        T = T') := by
  have hmem : ∀ x : H,
      x ∈ (⨆ n, S n : Submodule ℂ H) ↔ ∃ n, x ∈ S n :=
    fun x => Submodule.mem_iSup_of_directed S
      hmono.directed_le
  constructor
  · constructor
    · -- necessity: the extension's norm is a uniform bound
      rintro ⟨T, hT⟩
      refine ⟨‖T‖, fun n x hx => ?_⟩
      rw [← hT x (Submodule.mem_iSup_of_mem n hx)]
      exact T.le_opNorm x
    · -- sufficiency: extend along the dense inclusion
      rintro ⟨C, hC⟩
      have hbound : ∀ x : (⨆ n, S n : Submodule ℂ H),
          ‖T₀ x‖ ≤ C * ‖x‖ := by
        rintro ⟨x, hx⟩
        obtain ⟨n, hn⟩ := (hmem x).mp hx
        exact hC n x hn
      have hdr : DenseRange
          ((⨆ n, S n : Submodule ℂ H).subtypeL :
            (⨆ n, S n : Submodule ℂ H) →L[ℂ] H) := by
        have hrange : Set.range
            ((⨆ n, S n : Submodule ℂ H).subtypeL :
              (⨆ n, S n : Submodule ℂ H) →L[ℂ] H)
            = ((⨆ n, S n : Submodule ℂ H) : Set H) :=
          Subtype.range_coe
        rw [DenseRange, hrange]
        exact hdense
      have hui : IsUniformInducing
          ((⨆ n, S n : Submodule ℂ H).subtypeL :
            (⨆ n, S n : Submodule ℂ H) →L[ℂ] H) :=
        isometry_subtype_coe.isUniformInducing
      refine ⟨(T₀.mkContinuous C hbound).extend
        (⨆ n, S n : Submodule ℂ H).subtypeL, ?_⟩
      intro x hx
      exact (T₀.mkContinuous C hbound).extend_eq
        hdr hui ⟨x, hx⟩
  · -- uniqueness by density
    intro T T' hT hT'
    ext x
    have hagree : ((⨆ n, S n : Submodule ℂ H) : Set H)
        ⊆ {y : H | T y = T' y} := by
      intro y hy
      simp only [Set.mem_setOf_eq]
      rw [hT y hy, hT' y hy]
    have hclosed : IsClosed {y : H | T y = T' y} :=
      isClosed_eq T.continuous T'.continuous
    exact hclosed.closure_subset_iff.mpr hagree
      (hdense x)

omit [CompleteSpace H] in
/-- `thm:uniform-gap-limit` (the boxed norm equality,
the boxed power estimate, and stage-gap collapse). -/
theorem uniform_gap_limit
    (S : ℕ → Submodule ℂ H) (hmono : Monotone S)
    (hdense : Dense ((⨆ n, S n : Submodule ℂ H) : Set H))
    (T : H →L[ℂ] H) :
    -- (i) `‖T‖ = sup_X ρ_X` as a least upper bound
    IsLUB (Set.range fun n =>
      ‖T.comp (S n).subtypeL‖) ‖T‖
    -- (ii) `QTQ = T - E` and the boxed power estimate
    ∧ (∀ (E : H →L[ℂ] H) (γ₀ : ℝ),
        E * E = E → T * E = E → E * T = E →
        ((1 - E) * (T * (1 - E)) = T - E)
        ∧ (‖T - E‖ ≤ 1 - γ₀ → ∀ k : ℕ, 1 ≤ k →
            ‖(T ^ k : H →L[ℂ] H) - E‖ ≤ (1 - γ₀) ^ k))
    -- (iii) finite-stage gaps may collapse in the limit
    ∧ ((∀ n : ℕ, (1 : ℝ) - 1 / (n + 1) < 1)
        ∧ IsLUB (Set.range fun n : ℕ =>
            (1 : ℝ) - 1 / (n + 1)) 1) := by
  have hmem : ∀ x : H,
      x ∈ (⨆ n, S n : Submodule ℂ H) ↔ ∃ n, x ∈ S n :=
    fun x => Submodule.mem_iSup_of_directed S
      hmono.directed_le
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · -- upper bound: every stage norm is at most `‖T‖`
    rintro ρ ⟨n, rfl⟩
    apply ContinuousLinearMap.opNorm_le_bound _
      (norm_nonneg T)
    intro x
    calc ‖(T.comp (S n).subtypeL) x‖ = ‖T (x : H)‖ := rfl
      _ ≤ ‖T‖ * ‖(x : H)‖ := T.le_opNorm _
      _ = ‖T‖ * ‖x‖ := rfl
  · -- least: any stage-uniform bound dominates `‖T‖`
    intro C hC
    have h0 : ‖T.comp (S 0).subtypeL‖ ≤ C := hC ⟨0, rfl⟩
    have hC0 : 0 ≤ C :=
      le_trans (ContinuousLinearMap.opNorm_nonneg _) h0
    apply ContinuousLinearMap.opNorm_le_bound _ hC0
    intro x
    -- the bound holds on the dense union, then closes up
    have hUbound : ((⨆ n, S n : Submodule ℂ H) : Set H)
        ⊆ {y : H | ‖T y‖ ≤ C * ‖y‖} := by
      intro y hy
      obtain ⟨n, hn⟩ := (hmem y).mp hy
      have hstage : ‖T.comp (S n).subtypeL‖ ≤ C :=
        hC ⟨n, rfl⟩
      simp only [Set.mem_setOf_eq]
      calc ‖T y‖
          = ‖(T.comp (S n).subtypeL) ⟨y, hn⟩‖ := rfl
        _ ≤ ‖T.comp (S n).subtypeL‖
            * ‖(⟨y, hn⟩ : S n)‖ :=
            (T.comp (S n).subtypeL).le_opNorm _
        _ ≤ C * ‖y‖ := by
            apply mul_le_mul_of_nonneg_right hstage
            exact norm_nonneg _
    have hclosed : IsClosed {y : H | ‖T y‖ ≤ C * ‖y‖} := by
      apply isClosed_le
      · exact T.continuous.norm
      · exact continuous_const.mul continuous_norm
    exact hclosed.closure_subset_iff.mpr hUbound
      (hdense x)
  · -- (ii): `QTQ = T - E` and the power estimate
    intro E γ₀ hEE hTE hET
    have hTmE : (1 - E) * (T * (1 - E)) = T - E := by
      calc (1 - E) * (T * (1 - E))
          = T - T * E - (E * T - E * T * E) := by
            noncomm_ring
        _ = T - E - (E - E * E) := by
            rw [hTE, hET]
        _ = T - E := by
            rw [hEE]
            abel
    refine ⟨hTmE, ?_⟩
    intro hnorm k hk
    -- `T^k · E = E` for every `k`
    have hTkE : ∀ k : ℕ,
        (T ^ k : H →L[ℂ] H) * E = E := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, mul_assoc, hTE, ih]
    -- `(T - E)^k = T^k - E` for `k ≥ 1`
    have hpow : ∀ k : ℕ, 1 ≤ k →
        ((T - E) ^ k : H →L[ℂ] H)
          = (T ^ k : H →L[ℂ] H) - E := by
      intro k hk
      induction k with
      | zero => omega
      | succ k ih =>
        rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · simp
        · calc ((T - E) ^ (k + 1) : H →L[ℂ] H)
              = ((T - E) ^ k) * (T - E) := pow_succ _ _
            _ = ((T ^ k : H →L[ℂ] H) - E) * (T - E) := by
                rw [ih hkpos]
            _ = (T ^ k) * T - (T ^ k) * E
                - (E * T - E * E) := by noncomm_ring
            _ = (T ^ (k + 1) : H →L[ℂ] H) - E := by
                rw [hTkE k, hET, hEE, ← pow_succ]
                abel
    calc ‖(T ^ k : H →L[ℂ] H) - E‖
        = ‖((T - E) ^ k : H →L[ℂ] H)‖ := by
          rw [hpow k hk]
      _ ≤ ‖T - E‖ ^ k := norm_pow_le' _ (by omega)
      _ ≤ (1 - γ₀) ^ k := by gcongr
  · -- (iii) each stage value is below one …
    intro n
    have : (0 : ℝ) < 1 / (n + 1) := by positivity
    linarith
  · -- … but the least upper bound is one
    constructor
    · rintro ρ ⟨n, rfl⟩
      have : (0 : ℝ) < 1 / (n + 1) := by positivity
      linarith
    · intro b hb
      by_contra hlt
      push Not at hlt
      -- pick `n` with `1 - 1/(n+1) > b`
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / (1 - b))
      have hb1 : 0 < 1 - b := by linarith
      have hn0 : (0 : ℝ) < n + 1 := by positivity
      have hkey : 1 - 1 / (n + 1) > b := by
        have h1 : 1 / (1 - b) < n + 1 := by linarith
        have h2 : 1 / ((n : ℝ) + 1) < 1 - b := by
          rw [div_lt_iff₀ hn0]
          rw [div_lt_iff₀ hb1] at h1
          nlinarith
        linarith
      have := hb ⟨n, rfl⟩
      linarith

end HilbertLimit

end NCG
