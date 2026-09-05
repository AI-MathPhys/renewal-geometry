/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExactSourceSchurResidual
import NCG.Grand.JointSourceUniversality
import NCG.Grand.SchurRedheffer
import Mathlib

/-!
# Brand-new easy records, batch 02

This file formalizes the following brand-new Gran-Tensor manuscript records:

* `thm:GT-error-not-verdict` — input rejection is not a theorem verdict
  (`gt_error_not_verdict` and its component theorems);
* `thm:GT-upstream-compiler-transfer` — transfer of future-operational
  compilers through the minimal predictive quotient
  (`upstream_compiler_transfer`);
* `thm:GTLOC-collar-contact-quotient` — exact collar-relative contact
  quotient (`collar_contact_quotient_convergence_iff` and the
  minimum-norm counterterm theorems);
* `thm:GTLOC-leakage-Gram-transport` — transport of locality leakage Grams
  (`leakage_gram_transport_bound`, `leakage_gram_transport_cauchy`,
  `leakage_gram_transport_limit`);
* `thm:GTLOC-locality-leakage` — exact collar criterion and exponential
  bound (`locality_leakage_zero_iff`, `locality_leakage_exponential_bound`);
* `thm:GTLOC-quasilocal-commutator` — quasilocal commutator from local
  collars (`quasilocal_commutator_from_collars`,
  `quasilocal_commutator_exponential`);
* `thm:SMFS-operator-birth` — source-minimal field-shell operator birth
  (`field_shell_operator_birth`);
* `thm:SMOS-Ward-short` — simultaneous Ward-short Pythagoras
  (`simultaneous_ward_short`).
-/

open Matrix Filter
open scoped ComplexOrder MatrixOrder Norms.L2Operator

namespace NCG

universe u v w

/-! ## Shared helper lemmas -/

/-- The Gram difference of two syntheses splits into two mixed products. -/
theorem gram_diff_split {p q : ℕ} (X Y : Matrix (Fin p) (Fin q) ℂ) :
    Xᴴ * X - Yᴴ * Y = Xᴴ * (X - Y) + (X - Y)ᴴ * Y := by
  rw [Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]
  abel

/-- Operator-norm perturbation bound for a Gram difference. -/
theorem gram_diff_norm_le {p q : ℕ} (X Y : Matrix (Fin p) (Fin q) ℂ) :
    ‖Xᴴ * X - Yᴴ * Y‖ ≤ (‖X‖ + ‖Y‖) * ‖X - Y‖ := by
  rw [gram_diff_split]
  calc
    ‖Xᴴ * (X - Y) + (X - Y)ᴴ * Y‖
        ≤ ‖Xᴴ * (X - Y)‖ + ‖(X - Y)ᴴ * Y‖ := norm_add_le _ _
    _ ≤ ‖Xᴴ‖ * ‖X - Y‖ + ‖(X - Y)ᴴ‖ * ‖Y‖ :=
      add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _)
    _ = (‖X‖ + ‖Y‖) * ‖X - Y‖ := by
      rw [Matrix.l2_opNorm_conjTranspose, Matrix.l2_opNorm_conjTranspose]
      ring

/-- The congruence of an orthogonal complement is the plain sandwiched
quadratic form. -/
theorem orthComplement_gram_synthesis {k e : ℕ}
    (P : Matrix (Fin k) (Fin k) ℂ) (hPH : Pᴴ = P) (hP2 : P * P = P)
    (B : Matrix (Fin k) (Fin e) ℂ) :
    ((1 - P) * B)ᴴ * ((1 - P) * B) = Bᴴ * (1 - P) * B := by
  have hQH : (1 - P)ᴴ = 1 - P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH]
  have hQ2 : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hP2]
    abel
  rw [Matrix.conjTranspose_mul, hQH]
  calc
    Bᴴ * (1 - P) * ((1 - P) * B)
        = Bᴴ * ((1 - P) * (1 - P)) * B := by
          simp only [Matrix.mul_assoc]
    _ = Bᴴ * ((1 - P) * B) := by rw [hQ2, Matrix.mul_assoc]
    _ = Bᴴ * (1 - P) * B := by rw [Matrix.mul_assoc]

/-- Two syntheses of one Gram have equal source count. -/
theorem gram_synthesis_rank_eq {p k e : ℕ}
    (B : Matrix (Fin p) (Fin e) ℂ) (C : Matrix (Fin k) (Fin e) ℂ)
    (h : Bᴴ * B = Cᴴ * C) : B.rank = C.rank := by
  rw [← Matrix.rank_conjTranspose_mul_self B,
    ← Matrix.rank_conjTranspose_mul_self C, h]

/-- The sesquilinear self-pairing as a Euclidean norm square. -/
theorem star_dot_self_eq_euclidean {p : Type*} [Fintype p] (v : p → ℂ) :
    star v ⬝ᵥ v =
      ((‖(WithLp.toLp 2 v : EuclideanSpace ℂ p)‖ : ℝ) : ℂ) ^ 2 := by
  rw [dotProduct_comm, ← EuclideanSpace.inner_toLp_toLp,
    inner_self_eq_norm_sq_to_K]
  rfl

/-- The sesquilinear self-pairing is nonnegative. -/
theorem star_dot_self_nonneg {p : Type*} [Fintype p] (v : p → ℂ) :
    0 ≤ star v ⬝ᵥ v := by
  rw [star_dot_self_eq_euclidean, ← Complex.ofReal_pow]
  exact Complex.zero_le_real.mpr (sq_nonneg _)

/-- An operator-norm bound gives the scalar Loewner sandwich on the Gram. -/
theorem posSemidef_smul_one_sub_gram {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (c : ℝ) (hM : ‖M‖ ≤ c) :
    (((c ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - Mᴴ * M).PosSemidef := by
  have hherm : (((c ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
      Mᴴ * M).IsHermitian := by
    change _ᴴ = _
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Complex.star_def,
      Complex.conj_ofReal]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm fun x => ?_
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, ← gram_realization_inner,
    star_dot_self_eq_euclidean, star_dot_self_eq_euclidean, smul_eq_mul,
    ← Complex.ofReal_pow, ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, ← Complex.ofReal_sub]
  apply Complex.zero_le_real.mpr
  have hb : ‖(WithLp.toLp 2 (M *ᵥ x) : EuclideanSpace ℂ (Fin m))‖ ≤
      ‖M‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n))‖ :=
    Matrix.l2_opNorm_mulVec M (WithLp.toLp 2 x)
  have h1 : ‖(WithLp.toLp 2 (M *ᵥ x) : EuclideanSpace ℂ (Fin m))‖ ≤
      c * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n))‖ :=
    hb.trans (mul_le_mul_of_nonneg_right hM (norm_nonneg _))
  nlinarith [norm_nonneg (WithLp.toLp 2 (M *ᵥ x) : EuclideanSpace ℂ (Fin m)),
    norm_nonneg (WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n))]

/-- Orthogonal-projection Pythagoras for the sesquilinear pairing. -/
theorem projection_dotProduct_split {k : ℕ}
    (P : Matrix (Fin k) (Fin k) ℂ) (hPH : Pᴴ = P) (hP2 : P * P = P)
    (r : Fin k → ℂ) :
    star r ⬝ᵥ r =
      star (P *ᵥ r) ⬝ᵥ (P *ᵥ r) +
        star ((1 - P) *ᵥ r) ⬝ᵥ ((1 - P) *ᵥ r) := by
  have hQH : (1 - P)ᴴ = 1 - P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH]
  have hQ2 : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hP2]
    abel
  have h1 : star (P *ᵥ r) ⬝ᵥ (P *ᵥ r) = star r ⬝ᵥ (P *ᵥ r) := by
    rw [gram_realization_inner, hPH, hP2]
  have h2 : star ((1 - P) *ᵥ r) ⬝ᵥ ((1 - P) *ᵥ r) =
      star r ⬝ᵥ ((1 - P) *ᵥ r) := by
    rw [gram_realization_inner, hQH, hQ2]
  rw [h1, h2, ← dotProduct_add, ← Matrix.add_mulVec]
  congr 2
  rw [add_sub_cancel]
  exact (Matrix.one_mulVec r).symm

/-! ## `thm:GT-error-not-verdict`: input rejection is not a theorem verdict -/

/-- The finite status alphabet of the certificate verifier: three theorem
verdicts and the malformed-input status `ERROR`. -/
inductive GTVerifierStatus : Type
  | PASS
  | OBSTRUCTION
  | UNRESOLVED
  | ERROR
  deriving DecidableEq

/-- The verifier accepts a command exactly when its computed status agrees
with the user-declared expected status. -/
def gtExpectedBranchAccepts (expected computed : GTVerifierStatus) : Prop :=
  computed = expected

/-- A status is a theorem verdict when it establishes a mathematical
proposition, i.e. when it is not the malformed-input status `ERROR`. -/
def GTVerifierStatus.IsTheoremVerdict (s : GTVerifierStatus) : Prop :=
  s ≠ GTVerifierStatus.ERROR

/-- An expectation alphabet is sound when every accepted computed status is a
theorem verdict. -/
def GTSoundExpectationAlphabet (S : Set GTVerifierStatus) : Prop :=
  ∀ expected ∈ S, ∀ computed,
    gtExpectedBranchAccepts expected computed → computed.IsTheoremVerdict

/-- Sound expected-branch verification holds exactly when `ERROR` is excluded
from the expectation alphabet. -/
theorem gt_soundExpectationAlphabet_iff (S : Set GTVerifierStatus) :
    GTSoundExpectationAlphabet S ↔ GTVerifierStatus.ERROR ∉ S := by
  constructor
  · intro hs hmem
    exact hs GTVerifierStatus.ERROR hmem GTVerifierStatus.ERROR rfl rfl
  · intro hnot e he c hacc hc
    cases hacc
    exact hnot (hc ▸ he)

/-- `CERT.2`: an expectation alphabet is sound exactly when it is contained
in `{PASS, OBSTRUCTION, UNRESOLVED}`. -/
theorem gt_certTwo_expectation_alphabet (S : Set GTVerifierStatus) :
    GTSoundExpectationAlphabet S ↔
      S ⊆ ({GTVerifierStatus.PASS, GTVerifierStatus.OBSTRUCTION,
        GTVerifierStatus.UNRESOLVED} : Set GTVerifierStatus) := by
  rw [gt_soundExpectationAlphabet_iff]
  constructor
  · intro h s hs
    cases s with
    | PASS => simp
    | OBSTRUCTION => simp
    | UNRESOLVED => simp
    | ERROR => exact absurd hs h
  · intro h hmem
    have hin := h hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hin
    rcases hin with h' | h' | h' <;> exact GTVerifierStatus.noConfusion h'

/-- If `ERROR` is admitted into the expectation alphabet, every malformed
input which reaches that status passes by declaring the error in advance,
although no theorem verdict is established. -/
theorem gt_error_admitted_exploit {Input : Type*}
    (computed : Input → GTVerifierStatus) (S : Set GTVerifierStatus)
    (hS : GTVerifierStatus.ERROR ∈ S) :
    ∀ x, computed x = GTVerifierStatus.ERROR →
      ∃ expected ∈ S, gtExpectedBranchAccepts expected (computed x) ∧
        ¬ (computed x).IsTheoremVerdict := by
  intro x hx
  exact ⟨GTVerifierStatus.ERROR, hS, hx, fun h => h hx⟩

/-- `thm:GT-error-not-verdict`: the sound-alphabet characterization `CERT.2`
together with the explicit exploit produced by admitting `ERROR`. -/
theorem gt_error_not_verdict {Input : Type*}
    (computed : Input → GTVerifierStatus) (S : Set GTVerifierStatus) :
    (GTSoundExpectationAlphabet S ↔
      S ⊆ ({GTVerifierStatus.PASS, GTVerifierStatus.OBSTRUCTION,
        GTVerifierStatus.UNRESOLVED} : Set GTVerifierStatus)) ∧
      (GTVerifierStatus.ERROR ∈ S →
        ∀ x, computed x = GTVerifierStatus.ERROR →
          ∃ expected ∈ S, gtExpectedBranchAccepts expected (computed x) ∧
            ¬ (computed x).IsTheoremVerdict) :=
  ⟨gt_certTwo_expectation_alphabet S,
    fun hS => gt_error_admitted_exploit computed S hS⟩

/-! ## `thm:GT-upstream-compiler-transfer`: transfer of compilers -/

/-- Two candidate states are equivalent when they carry the same complete
declared future signature. -/
def futureSignatureSetoid {State : Type u} {Sig : Type v}
    (σ : State → Sig) : Setoid State where
  r s t := σ s = σ t
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-- The minimal predictive state space `Z^min`: the quotient of the supplied
predictive primitive by equality of complete declared future signatures. -/
abbrev minimalPredictiveQuotient {State : Type u} {Sig : Type v}
    (σ : State → Sig) : Type u :=
  Quotient (futureSignatureSetoid σ)

/-- The canonical projection `π` from the supplied predictive primitive onto
`Z^min`. -/
abbrev minimalPredictiveProjection {State : Type u} {Sig : Type v}
    (σ : State → Sig) : State → minimalPredictiveQuotient σ :=
  Quotient.mk (futureSignatureSetoid σ)

/-- `thm:GT-upstream-compiler-transfer` (`UP.8`): every downstream compiler
whose value is unchanged on states with equal complete declared future
signatures factors uniquely through the minimal predictive quotient, so
passage to `Z^min` preserves every quotient-invariant downstream output. -/
theorem upstream_compiler_transfer {State : Type u} {Sig : Type v}
    {V : Type w} (σ : State → Sig) (D : State → V)
    (hD : ∀ s t, σ s = σ t → D s = D t) :
    ∃! Dbar : minimalPredictiveQuotient σ → V,
      D = Dbar ∘ minimalPredictiveProjection σ := by
  refine ⟨Quotient.lift D (fun a b hab => hD a b hab), ?_, ?_⟩
  · funext s
    rfl
  · intro F hF
    funext q
    obtain ⟨s⟩ := q
    exact (congrFun hF s).symm

/-! ## `thm:GTLOC-collar-contact-quotient`: exact collar-relative quotient -/

/-- The canonical minimum-norm local subtraction
`u^min = L† P Π` (`eq:GTLOC-local-minimum-counterterm`), with the
Moore–Penrose inverse rendered through the Gram pseudoinverse. -/
noncomputable def contactMinimalCounterterm {h e : ℕ}
    (L : Matrix (Fin h) (Fin e) ℂ) (v : Fin h → ℂ) : Fin e → ℂ :=
  sourceGramPseudoinverse L *ᵥ (Lᴴ *ᵥ (sourceRangeProjection L *ᵥ v))

/-- The minimum-norm subtraction synthesizes the range component, so its
residual is exactly the orthogonal complement of the local model. -/
theorem contactMinimalCounterterm_residual {h e : ℕ}
    (L : Matrix (Fin h) (Fin e) ℂ) (v : Fin h → ℂ) :
    L *ᵥ contactMinimalCounterterm L v = sourceRangeProjection L *ᵥ v ∧
      v - L *ᵥ contactMinimalCounterterm L v =
        (1 - sourceRangeProjection L) *ᵥ v := by
  obtain ⟨-, hP2, -⟩ := (sourceGramPseudoinverse_projection L).2.2.2
  change sourceRangeProjection L * sourceRangeProjection L =
    sourceRangeProjection L at hP2
  have hmain : L *ᵥ contactMinimalCounterterm L v =
      sourceRangeProjection L *ᵥ v := by
    unfold contactMinimalCounterterm
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    have hgroup : L * sourceGramPseudoinverse L * Lᴴ *
        sourceRangeProjection L = sourceRangeProjection L := by
      rw [show L * sourceGramPseudoinverse L * Lᴴ =
        sourceRangeProjection L from rfl, hP2]
    rw [hgroup]
  refine ⟨hmain, ?_⟩
  rw [hmain, Matrix.sub_mulVec, Matrix.one_mulVec]

/-- `thm:GTLOC-collar-contact-quotient`, main equivalence: some local
subtraction renders the contact data convergent if and only if the
collar-orthogonal component is Cauchy. -/
theorem collar_contact_quotient_convergence_iff {h e : ℕ}
    (L : Matrix (Fin h) (Fin e) ℂ) (v : ℕ → Fin h → ℂ) :
    (∃ u : ℕ → Fin e → ℂ, ∃ w : Fin h → ℂ,
        Tendsto (fun n => v n - L *ᵥ u n) atTop (nhds w)) ↔
      CauchySeq fun n => (1 - sourceRangeProjection L) *ᵥ v n := by
  obtain ⟨-, -, hPS⟩ := (sourceGramPseudoinverse_projection L).2.2.2
  change sourceRangeProjection L * L = L at hPS
  have hQL : (1 - sourceRangeProjection L) * L = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hPS, sub_self]
  constructor
  · rintro ⟨u, w, htend⟩
    have hcont : Continuous fun x : Fin h → ℂ =>
        (1 - sourceRangeProjection L) *ᵥ x :=
      LinearMap.continuous_of_finiteDimensional
        ((1 - sourceRangeProjection L).mulVecLin)
    have h1 : Tendsto
        (fun n => (1 - sourceRangeProjection L) *ᵥ (v n - L *ᵥ u n))
        atTop (nhds ((1 - sourceRangeProjection L) *ᵥ w)) :=
      (hcont.tendsto w).comp htend
    have h2 : ∀ n,
        (1 - sourceRangeProjection L) *ᵥ (v n - L *ᵥ u n) =
          (1 - sourceRangeProjection L) *ᵥ v n := by
      intro n
      have hmap := ((1 - sourceRangeProjection L).mulVecLin).map_sub
        (v n) (L *ᵥ u n)
      simp only [Matrix.mulVecLin_apply] at hmap
      rw [hmap, Matrix.mulVec_mulVec, hQL, Matrix.zero_mulVec, sub_zero]
    exact (h1.congr h2).cauchySeq
  · intro hC
    obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hC
    refine ⟨fun n => contactMinimalCounterterm L (v n), w, ?_⟩
    exact hw.congr fun n =>
      ((contactMinimalCounterterm_residual L (v n)).2).symm

/-- Least-squares optimality of the minimum-norm subtraction: no local
coefficients beat the collar-orthogonal residual energy. -/
theorem contactMinimalCounterterm_leastSquares {h e : ℕ}
    (L : Matrix (Fin h) (Fin e) ℂ) (v : Fin h → ℂ) (u : Fin e → ℂ) :
    star ((1 - sourceRangeProjection L) *ᵥ v) ⬝ᵥ
        ((1 - sourceRangeProjection L) *ᵥ v) ≤
      star (v - L *ᵥ u) ⬝ᵥ (v - L *ᵥ u) := by
  obtain ⟨-, hP2, hPS⟩ := (sourceGramPseudoinverse_projection L).2.2.2
  obtain ⟨hPH, -, -⟩ := (sourceGramPseudoinverse_projection L).2.2.2
  change (sourceRangeProjection L)ᴴ = sourceRangeProjection L at hPH
  change sourceRangeProjection L * sourceRangeProjection L =
    sourceRangeProjection L at hP2
  change sourceRangeProjection L * L = L at hPS
  have hQL : (1 - sourceRangeProjection L) * L = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hPS, sub_self]
  have hres : (1 - sourceRangeProjection L) *ᵥ v =
      (1 - sourceRangeProjection L) *ᵥ (v - L *ᵥ u) := by
    have hmap := ((1 - sourceRangeProjection L).mulVecLin).map_sub
      v (L *ᵥ u)
    simp only [Matrix.mulVecLin_apply] at hmap
    rw [hmap, Matrix.mulVec_mulVec, hQL, Matrix.zero_mulVec, sub_zero]
  rw [hres,
    projection_dotProduct_split (sourceRangeProjection L) hPH hP2
      (v - L *ᵥ u)]
  exact le_add_of_nonneg_left (star_dot_self_nonneg _)

/-- Minimum-norm property: among all coefficients realizing the range
component, the canonical subtraction has the least energy. -/
theorem contactMinimalCounterterm_minimumNorm {h e : ℕ}
    (L : Matrix (Fin h) (Fin e) ℂ) (v : Fin h → ℂ) (u : Fin e → ℂ)
    (hu : L *ᵥ u = sourceRangeProjection L *ᵥ v) :
    star (contactMinimalCounterterm L v) ⬝ᵥ contactMinimalCounterterm L v ≤
      star u ⬝ᵥ u := by
  obtain ⟨hQH, hQ2, -⟩ := sourceCoefficientSupport_properties L
  change (sourceGramPseudoinverse L * (Lᴴ * L))ᴴ =
    sourceGramPseudoinverse L * (Lᴴ * L) at hQH
  change (sourceGramPseudoinverse L * (Lᴴ * L)) *
      (sourceGramPseudoinverse L * (Lᴴ * L)) =
    sourceGramPseudoinverse L * (Lᴴ * L) at hQ2
  have hQu : (sourceGramPseudoinverse L * (Lᴴ * L)) *ᵥ u =
      contactMinimalCounterterm L v := by
    unfold contactMinimalCounterterm
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hu]
  rw [← hQu,
    projection_dotProduct_split (sourceGramPseudoinverse L * (Lᴴ * L))
      hQH hQ2 u]
  exact le_add_of_nonneg_right (star_dot_self_nonneg _)

/-! ## `thm:GTLOC-leakage-Gram-transport`: transport of leakage Grams -/

/-- `eq:GTLOC-leakage-Gram-transport`: the one-line Gram perturbation bound
for uniformly bounded transported leakage representatives. -/
theorem leakage_gram_transport_bound {p q : ℕ}
    (A : ℕ → Matrix (Fin p) (Fin q) ℂ) (MR : ℝ)
    (hbound : ∀ n, ‖A n‖ ≤ MR) (n : ℕ) :
    ‖(A (n + 1))ᴴ * A (n + 1) - (A n)ᴴ * A n‖ ≤
      2 * MR * ‖A (n + 1) - A n‖ := by
  have h := gram_diff_norm_le (A (n + 1)) (A n)
  have hsum : ‖A (n + 1)‖ + ‖A n‖ ≤ 2 * MR := by
    linarith [hbound n, hbound (n + 1)]
  exact h.trans (mul_le_mul_of_nonneg_right hsum (norm_nonneg _))

/-- Summable transported defects make both the representatives and their
leakage Grams Cauchy. -/
theorem leakage_gram_transport_cauchy {p q : ℕ}
    (A : ℕ → Matrix (Fin p) (Fin q) ℂ) (MR : ℝ)
    (hbound : ∀ n, ‖A n‖ ≤ MR)
    (hsum : Summable fun n => ‖A (n + 1) - A n‖) :
    CauchySeq A ∧ CauchySeq fun n => (A n)ᴴ * A n := by
  constructor
  · apply cauchySeq_of_summable_dist
    refine Summable.of_nonneg_of_le (fun n => dist_nonneg)
      (fun n => ?_) hsum
    rw [dist_eq_norm, norm_sub_rev]
  · apply cauchySeq_of_summable_dist
    refine Summable.of_nonneg_of_le (fun n => dist_nonneg)
      (fun n => ?_) (hsum.mul_left (2 * MR))
    rw [dist_eq_norm, norm_sub_rev]
    exact leakage_gram_transport_bound A MR hbound n

/-- Cofinal limit of the selected locality packet: convergent transported
representatives carry every fixed-radius leakage Gram to the limit Gram. -/
theorem leakage_gram_transport_limit {p q : ℕ}
    (A : ℕ → Matrix (Fin p) (Fin q) ℂ) (Alim : Matrix (Fin p) (Fin q) ℂ)
    (hlim : Tendsto A atTop (nhds Alim)) :
    Tendsto (fun n => (A n)ᴴ * A n) atTop (nhds (Alimᴴ * Alim)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at hlim ⊢
  have hb : ∀ n, ‖(A n)ᴴ * A n - Alimᴴ * Alim‖ ≤
      (‖A n - Alim‖ + 2 * ‖Alim‖) * ‖A n - Alim‖ := by
    intro n
    have h := gram_diff_norm_le (A n) Alim
    have hXn : ‖A n‖ ≤ ‖Alim‖ + ‖A n - Alim‖ := by
      calc
        ‖A n‖ = ‖Alim + (A n - Alim)‖ := by
          rw [show Alim + (A n - Alim) = A n from by abel]
        _ ≤ ‖Alim‖ + ‖A n - Alim‖ := norm_add_le _ _
    have hfac : ‖A n‖ + ‖Alim‖ ≤ ‖A n - Alim‖ + 2 * ‖Alim‖ := by
      linarith
    exact h.trans (mul_le_mul_of_nonneg_right hfac (norm_nonneg _))
  have hgoal : Tendsto
      (fun n => (‖A n - Alim‖ + 2 * ‖Alim‖) * ‖A n - Alim‖) atTop
      (nhds 0) := by
    have hmul := (hlim.add
      (tendsto_const_nhds (x := 2 * ‖Alim‖))).mul hlim
    simpa using hmul
  exact squeeze_zero (fun n => norm_nonneg _) hb hgoal

/-! ## `thm:GTLOC-locality-leakage`: exact collar criterion and bound -/

/-- The locality leakage Gram
`L_R^loc(T | J_X) = J_X^* T^* (I − P_{X^[R]}) T J_X`
(`eq:GTLOC-locality-leakage-Gram`). -/
def localityLeakageGram {k e : ℕ} (Q T : Matrix (Fin k) (Fin k) ℂ)
    (J : Matrix (Fin k) (Fin e) ℂ) : Matrix (Fin e) (Fin e) ℂ :=
  Jᴴ * Tᴴ * (1 - Q) * T * J

/-- The leakage Gram is synthesized by the missing collar bank
`(I − P_{X^[R]}) T J_X`, hence positive semidefinite. -/
theorem localityLeakageGram_synthesis {k e : ℕ}
    (Q T : Matrix (Fin k) (Fin k) ℂ) (J : Matrix (Fin k) (Fin e) ℂ)
    (hQH : Qᴴ = Q) (hQ2 : Q * Q = Q) :
    localityLeakageGram Q T J =
        ((1 - Q) * (T * J))ᴴ * ((1 - Q) * (T * J)) ∧
      (localityLeakageGram Q T J).PosSemidef := by
  have hsyn : ((1 - Q) * (T * J))ᴴ * ((1 - Q) * (T * J)) =
      localityLeakageGram Q T J := by
    rw [orthComplement_gram_synthesis Q hQH hQ2 (T * J)]
    unfold localityLeakageGram
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  refine ⟨hsyn.symm, ?_⟩
  rw [← hsyn]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- `eq:GTLOC-exact-collar-zero`: the leakage Gram vanishes exactly when the
response never leaves the physical collar. -/
theorem locality_leakage_zero_iff {k e : ℕ}
    (Q T : Matrix (Fin k) (Fin k) ℂ) (J : Matrix (Fin k) (Fin e) ℂ)
    (hQH : Qᴴ = Q) (hQ2 : Q * Q = Q) :
    localityLeakageGram Q T J = 0 ↔ (1 - Q) * (T * J) = 0 := by
  rw [(localityLeakageGram_synthesis Q T J hQH hQ2).1]
  exact Matrix.conjTranspose_mul_self_eq_zero

/-- `eq:GTLOC-locality-leakage-bound`: for a quasilocal operator with the
manuscript's off-diagonal collar decay, the leakage Gram is sandwiched
between `0` and `e^{-2αR} ‖T‖²_{α,Sch} · J_X^* J_X`. -/
theorem locality_leakage_exponential_bound {k e : ℕ}
    (Q P T : Matrix (Fin k) (Fin k) ℂ) (J : Matrix (Fin k) (Fin e) ℂ)
    (alpha R c : ℝ)
    (hQH : Qᴴ = Q) (hQ2 : Q * Q = Q) (_hPH : Pᴴ = P) (hPJ : P * J = J)
    (hdecay : ‖(1 - Q) * T * P‖ ≤ Real.exp (-(alpha * R)) * c) :
    (localityLeakageGram Q T J).PosSemidef ∧
      (((Real.exp (-(2 * alpha * R)) * c ^ 2 : ℝ) : ℂ) • (Jᴴ * J) -
        localityLeakageGram Q T J).PosSemidef := by
  refine ⟨(localityLeakageGram_synthesis Q T J hQH hQ2).2, ?_⟩
  have hsand := posSemidef_smul_one_sub_gram ((1 - Q) * T * P)
    (Real.exp (-(alpha * R)) * c) hdecay
  have hcongr := hsand.conjTranspose_mul_mul_same J
  have hMJ : (1 - Q) * T * P * J = (1 - Q) * (T * J) := by
    rw [Matrix.mul_assoc ((1 - Q) * T) P J, hPJ, Matrix.mul_assoc]
  have hgram : Jᴴ * (((1 - Q) * T * P)ᴴ * ((1 - Q) * T * P)) * J =
      localityLeakageGram Q T J := by
    calc
      Jᴴ * (((1 - Q) * T * P)ᴴ * ((1 - Q) * T * P)) * J
          = ((1 - Q) * T * P * J)ᴴ * ((1 - Q) * T * P * J) := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = ((1 - Q) * (T * J))ᴴ * ((1 - Q) * (T * J)) := by rw [hMJ]
      _ = localityLeakageGram Q T J :=
        ((localityLeakageGram_synthesis Q T J hQH hQ2).1).symm
  have hexpand : Jᴴ *
      ((((Real.exp (-(alpha * R)) * c) ^ 2 : ℝ) : ℂ) •
          (1 : Matrix (Fin k) (Fin k) ℂ) -
        ((1 - Q) * T * P)ᴴ * ((1 - Q) * T * P)) * J =
      (((Real.exp (-(alpha * R)) * c) ^ 2 : ℝ) : ℂ) • (Jᴴ * J) -
        Jᴴ * (((1 - Q) * T * P)ᴴ * ((1 - Q) * T * P)) * J := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one]
  rw [hexpand, hgram] at hcongr
  have hexp : (Real.exp (-(alpha * R)) * c) ^ 2 =
      Real.exp (-(2 * alpha * R)) * c ^ 2 := by
    rw [mul_pow, sq (Real.exp (-(alpha * R))), ← Real.exp_add]
    ring_nf
  rwa [hexp] at hcongr

/-- Source-minimality of the missing collar bank: every synthesis of the
leakage Gram spends exactly as many source directions as
`(I − P_{X^[R]}) T J_X`. -/
theorem locality_leakage_bank_minimality {k e p : ℕ}
    (Q T : Matrix (Fin k) (Fin k) ℂ) (J : Matrix (Fin k) (Fin e) ℂ)
    (hQH : Qᴴ = Q) (hQ2 : Q * Q = Q)
    (B : Matrix (Fin p) (Fin e) ℂ)
    (hB : Bᴴ * B = localityLeakageGram Q T J) :
    B.rank = ((1 - Q) * (T * J)).rank := by
  apply gram_synthesis_rank_eq
  rw [hB, (localityLeakageGram_synthesis Q T J hQH hQ2).1]

/-! ## `thm:GTLOC-quasilocal-commutator`: commutator from local collars -/

/-- Triangle splitting of a commutator through commuting local
representatives (`eq:GTLOC-quasilocal-commutator-bound`). -/
theorem quasilocal_commutator_split {E : Type*} [NormedRing E]
    (A B AR BR : E) (etaA etaB : ℝ)
    (hA : ‖A - AR‖ ≤ etaA) (hB : ‖B - BR‖ ≤ etaB)
    (hcomm : AR * BR = BR * AR) :
    ‖A * B - B * A‖ ≤ 2 * etaA * ‖B‖ + 2 * (‖A‖ + etaA) * etaB := by
  have hsplit : A * B - B * A =
      ((A - AR) * B - B * (A - AR)) +
        (AR * (B - BR) - (B - BR) * AR) + (AR * BR - BR * AR) := by
    noncomm_ring
  rw [hcomm, sub_self, add_zero] at hsplit
  have h1 : ‖(A - AR) * B - B * (A - AR)‖ ≤ 2 * etaA * ‖B‖ := by
    have hk1 : ‖A - AR‖ * ‖B‖ ≤ etaA * ‖B‖ :=
      mul_le_mul_of_nonneg_right hA (norm_nonneg B)
    have hk2 : ‖B‖ * ‖A - AR‖ = ‖A - AR‖ * ‖B‖ := mul_comm _ _
    calc
      ‖(A - AR) * B - B * (A - AR)‖
          ≤ ‖(A - AR) * B‖ + ‖B * (A - AR)‖ := norm_sub_le _ _
      _ ≤ ‖A - AR‖ * ‖B‖ + ‖B‖ * ‖A - AR‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ 2 * etaA * ‖B‖ := by linarith
  have hetaA0 : 0 ≤ etaA := (norm_nonneg _).trans hA
  have hAR : ‖AR‖ ≤ ‖A‖ + etaA := by
    calc
      ‖AR‖ = ‖A - (A - AR)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖A‖ + ‖A - AR‖ := norm_sub_le _ _
      _ ≤ ‖A‖ + etaA := by linarith
  have h2 : ‖AR * (B - BR) - (B - BR) * AR‖ ≤
      2 * (‖A‖ + etaA) * etaB := by
    have hkey : ‖AR‖ * ‖B - BR‖ ≤ (‖A‖ + etaA) * etaB :=
      mul_le_mul hAR hB (norm_nonneg _)
        (add_nonneg (norm_nonneg A) hetaA0)
    have hswap : ‖B - BR‖ * ‖AR‖ = ‖AR‖ * ‖B - BR‖ := mul_comm _ _
    calc
      ‖AR * (B - BR) - (B - BR) * AR‖
          ≤ ‖AR * (B - BR)‖ + ‖(B - BR) * AR‖ := norm_sub_le _ _
      _ ≤ ‖AR‖ * ‖B - BR‖ + ‖B - BR‖ * ‖AR‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ 2 * (‖A‖ + etaA) * etaB := by linarith
  calc
    ‖A * B - B * A‖ = ‖((A - AR) * B - B * (A - AR)) +
        (AR * (B - BR) - (B - BR) * AR)‖ := by rw [hsplit]
    _ ≤ ‖(A - AR) * B - B * (A - AR)‖ +
        ‖AR * (B - BR) - (B - BR) * AR‖ := norm_add_le _ _
    _ ≤ 2 * etaA * ‖B‖ + 2 * (‖A‖ + etaA) * etaB := add_le_add h1 h2

/-- `thm:GTLOC-quasilocal-commutator`, packet form: if both observables have
local approximation packets and local representatives with disjoint supports
commute, then inside the collar gate `2R < d(X,Y)` the commutator obeys the
boxed bound. -/
theorem quasilocal_commutator_from_collars {E : Type*} [NormedRing E]
    (A B : E) (AR BR : ℝ → E) (etaA etaB : ℝ → ℝ) (dXY : ℝ)
    (hApk : ∀ R, ‖A - AR R‖ ≤ etaA R)
    (hBpk : ∀ R, ‖B - BR R‖ ≤ etaB R)
    (hdisj : ∀ R, 2 * R < dXY → AR R * BR R = BR R * AR R) :
    ∀ R, 2 * R < dXY →
      ‖A * B - B * A‖ ≤
        2 * etaA R * ‖B‖ + 2 * (‖A‖ + etaA R) * etaB R :=
  fun R hR => quasilocal_commutator_split A B (AR R) (BR R)
    (etaA R) (etaB R) (hApk R) (hBpk R) (hdisj R hR)

/-- `eq:GTLOC-exponential-approximants`: exponentially good approximants at
the choice `R = d(X,Y)/3` give the explicit commutator bound with rate
`α/3`. -/
theorem quasilocal_commutator_exponential {E : Type*} [NormedRing E]
    (A B : E) (AR BR : ℝ → E) (etaA etaB : ℝ → ℝ)
    (dXY alpha CA CB : ℝ)
    (hApk : ∀ R, ‖A - AR R‖ ≤ etaA R)
    (hBpk : ∀ R, ‖B - BR R‖ ≤ etaB R)
    (hdisj : ∀ R, 2 * R < dXY → AR R * BR R = BR R * AR R)
    (hAexp : ∀ R, etaA R ≤ CA * Real.exp (-(alpha * R)))
    (hBexp : ∀ R, etaB R ≤ CB * Real.exp (-(alpha * R)))
    (hd : 0 < dXY) :
    ‖A * B - B * A‖ ≤
      2 * (CA * Real.exp (-(alpha * (dXY / 3)))) * ‖B‖ +
        2 * (‖A‖ + CA * Real.exp (-(alpha * (dXY / 3)))) *
          (CB * Real.exp (-(alpha * (dXY / 3)))) := by
  have hR : 2 * (dXY / 3) < dXY := by linarith
  have hmain := quasilocal_commutator_from_collars A B AR BR etaA etaB
    dXY hApk hBpk hdisj (dXY / 3) hR
  have ha0 : 0 ≤ etaA (dXY / 3) := (norm_nonneg _).trans (hApk _)
  have hb0 : 0 ≤ etaB (dXY / 3) := (norm_nonneg _).trans (hBpk _)
  have hA3 := hAexp (dXY / 3)
  have hB3 := hBexp (dXY / 3)
  have hk1 : etaA (dXY / 3) * ‖B‖ ≤
      CA * Real.exp (-(alpha * (dXY / 3))) * ‖B‖ :=
    mul_le_mul_of_nonneg_right hA3 (norm_nonneg B)
  have hk2 : (‖A‖ + etaA (dXY / 3)) * etaB (dXY / 3) ≤
      (‖A‖ + CA * Real.exp (-(alpha * (dXY / 3)))) *
        (CB * Real.exp (-(alpha * (dXY / 3)))) :=
    mul_le_mul (add_le_add le_rfl hA3) hB3 hb0
      (add_nonneg (norm_nonneg A) (ha0.trans hA3))
  nlinarith [hmain, hk1, hk2]

/-! ## `thm:SMFS-operator-birth`: source-minimal field-shell birth -/

/-- The field-shell coefficient update `δx = G† C^* ΔD` (`FS.36`). -/
noncomputable def fieldShellCoefficient {h e m : ℕ}
    (C : Matrix (Fin h) (Fin e) ℂ) (D : Matrix (Fin h) (Fin m) ℂ) :
    Matrix (Fin e) (Fin m) ℂ :=
  sourceGramPseudoinverse C * (Cᴴ * D)

/-- The orthogonal operator residual `R^op = (I − P_C) ΔD` (`FS.36`). -/
noncomputable def fieldShellResidual {h e m : ℕ}
    (C : Matrix (Fin h) (Fin e) ℂ) (D : Matrix (Fin h) (Fin m) ℂ) :
    Matrix (Fin h) (Fin m) ℂ :=
  (1 - sourceRangeProjection C) * D

/-- `FS.37`: the exact operator decomposition `ΔD = C δx + R^op` with the
residual annihilated by the source frame. -/
theorem field_shell_operator_decomposition {h e m : ℕ}
    (C : Matrix (Fin h) (Fin e) ℂ) (D : Matrix (Fin h) (Fin m) ℂ) :
    D = C * fieldShellCoefficient C D + fieldShellResidual C D ∧
      Cᴴ * fieldShellResidual C D = 0 := by
  obtain ⟨hPH, -, hPC⟩ := (sourceGramPseudoinverse_projection C).2.2.2
  change (sourceRangeProjection C)ᴴ = sourceRangeProjection C at hPH
  change sourceRangeProjection C * C = C at hPC
  have hQH : (1 - sourceRangeProjection C)ᴴ = 1 - sourceRangeProjection C := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH]
  have hCdx : C * fieldShellCoefficient C D =
      sourceRangeProjection C * D := by
    unfold fieldShellCoefficient sourceRangeProjection
    simp only [Matrix.mul_assoc]
  constructor
  · rw [hCdx]
    unfold fieldShellResidual
    rw [Matrix.sub_mul, Matrix.one_mul]
    abel
  · have hQC : (1 - sourceRangeProjection C) * C = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, hPC, sub_self]
    have hCQ : Cᴴ * (1 - sourceRangeProjection C) = 0 := by
      have ht := congrArg Matrix.conjTranspose hQC
      rw [Matrix.conjTranspose_mul, hQH, Matrix.conjTranspose_zero] at ht
      exact ht
    unfold fieldShellResidual
    rw [← Matrix.mul_assoc, hCQ, Matrix.zero_mul]

/-- `FS.38`, Gram form: the exact operator Pythagoras
`ΔD^* ΔD = δx^* G δx + (R^op)^* R^op`. -/
theorem field_shell_operator_pythagoras {h e m : ℕ}
    (C : Matrix (Fin h) (Fin e) ℂ) (D : Matrix (Fin h) (Fin m) ℂ) :
    Dᴴ * D =
      (fieldShellCoefficient C D)ᴴ *
          ((Cᴴ * C) * fieldShellCoefficient C D) +
        (fieldShellResidual C D)ᴴ * fieldShellResidual C D := by
  obtain ⟨hJH, -, hJXJ, hPH, hP2, -⟩ := sourceGramPseudoinverse_projection C
  change (sourceGramPseudoinverse C)ᴴ = sourceGramPseudoinverse C at hJH
  change sourceGramPseudoinverse C * (Cᴴ * C) * sourceGramPseudoinverse C =
    sourceGramPseudoinverse C at hJXJ
  change (sourceRangeProjection C)ᴴ = sourceRangeProjection C at hPH
  change sourceRangeProjection C * sourceRangeProjection C =
    sourceRangeProjection C at hP2
  have hterm : (fieldShellCoefficient C D)ᴴ *
      ((Cᴴ * C) * fieldShellCoefficient C D) =
      Dᴴ * (sourceRangeProjection C * D) := by
    unfold fieldShellCoefficient
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hJH]
    calc
      Dᴴ * C * sourceGramPseudoinverse C *
          ((Cᴴ * C) * (sourceGramPseudoinverse C * (Cᴴ * D)))
          = Dᴴ * (C * (sourceGramPseudoinverse C * (Cᴴ * C) *
              sourceGramPseudoinverse C) * (Cᴴ * D)) := by
            simp only [Matrix.mul_assoc]
      _ = Dᴴ * (C * sourceGramPseudoinverse C * (Cᴴ * D)) := by
        rw [hJXJ]
      _ = Dᴴ * (C * sourceGramPseudoinverse C * Cᴴ * D) := by
        simp only [Matrix.mul_assoc]
      _ = Dᴴ * (sourceRangeProjection C * D) := rfl
  have hres : (fieldShellResidual C D)ᴴ * fieldShellResidual C D =
      Dᴴ * ((1 - sourceRangeProjection C) * D) := by
    unfold fieldShellResidual
    rw [orthComplement_gram_synthesis (sourceRangeProjection C) hPH hP2 D,
      Matrix.mul_assoc]
  rw [hterm, hres, ← Matrix.mul_add]
  congr 1
  rw [Matrix.sub_mul, Matrix.one_mul]
  abel

/-- `FS.38`, Hilbert–Schmidt form: the trace Pythagoras
`‖ΔD‖²_HS = ⟨δx, G δx⟩ + ‖R^op‖²_HS`. -/
theorem field_shell_operator_pythagoras_trace {h e m : ℕ}
    (C : Matrix (Fin h) (Fin e) ℂ) (D : Matrix (Fin h) (Fin m) ℂ) :
    (Dᴴ * D).trace =
      ((fieldShellCoefficient C D)ᴴ *
          ((Cᴴ * C) * fieldShellCoefficient C D)).trace +
        ((fieldShellResidual C D)ᴴ * fieldShellResidual C D).trace := by
  rw [field_shell_operator_pythagoras C D, Matrix.trace_add]

/-- Source-minimality of the new operator bank: every synthesis of the
residual Gram spends exactly as many operator directions as `R^op`. -/
theorem field_shell_bank_minimality {h e m p : ℕ}
    (C : Matrix (Fin h) (Fin e) ℂ) (D : Matrix (Fin h) (Fin m) ℂ)
    (B : Matrix (Fin p) (Fin m) ℂ)
    (hB : Bᴴ * B = (fieldShellResidual C D)ᴴ * fieldShellResidual C D) :
    B.rank = (fieldShellResidual C D).rank :=
  gram_synthesis_rank_eq B (fieldShellResidual C D) hB

/-- `thm:SMFS-operator-birth`: the bundled decomposition, orthogonality and
Hilbert–Schmidt Pythagoras of the field-shell operator birth. -/
theorem field_shell_operator_birth {h e m : ℕ}
    (C : Matrix (Fin h) (Fin e) ℂ) (D : Matrix (Fin h) (Fin m) ℂ) :
    D = C * fieldShellCoefficient C D + fieldShellResidual C D ∧
      Cᴴ * fieldShellResidual C D = 0 ∧
      (Dᴴ * D).trace =
        ((fieldShellCoefficient C D)ᴴ *
            ((Cᴴ * C) * fieldShellCoefficient C D)).trace +
          ((fieldShellResidual C D)ᴴ * fieldShellResidual C D).trace :=
  ⟨(field_shell_operator_decomposition C D).1,
    (field_shell_operator_decomposition C D).2,
    field_shell_operator_pythagoras_trace C D⟩

/-! ## `thm:SMOS-Ward-short`: simultaneous Ward-short Pythagoras -/

/-- The physical Ward residual `Y_phys = (I − P_N) Y`
(`eq:SMOS-Ward-short-Gram`). -/
noncomputable def wardPhysicalResidual {h f e : ℕ}
    (N : Matrix (Fin h) (Fin f) ℂ) (Y : Matrix (Fin h) (Fin e) ℂ) :
    Matrix (Fin h) (Fin e) ℂ :=
  (1 - sourceRangeProjection N) * Y

/-- The physical Ward Gram `C_W^phys = Y^* (I − P_N) Y`
(`eq:SMOS-Ward-short-Gram`). -/
noncomputable def wardPhysicalGram {h f e : ℕ}
    (N : Matrix (Fin h) (Fin f) ℂ) (Y : Matrix (Fin h) (Fin e) ℂ) :
    Matrix (Fin e) (Fin e) ℂ :=
  Yᴴ * (1 - sourceRangeProjection N) * Y

/-- The optimal trivial coefficient map `L₀ = G_N† N^* Y`. -/
noncomputable def wardOptimalCoefficient {h f e : ℕ}
    (N : Matrix (Fin h) (Fin f) ℂ) (Y : Matrix (Fin h) (Fin e) ℂ) :
    Matrix (Fin f) (Fin e) ℂ :=
  sourceGramPseudoinverse N * (Nᴴ * Y)

/-- The physical Ward Gram is the exact source Schur residual of the packet,
hence positive semidefinite. -/
theorem wardPhysicalGram_eq_schur {h f e : ℕ}
    (N : Matrix (Fin h) (Fin f) ℂ) (Y : Matrix (Fin h) (Fin e) ℂ) :
    wardPhysicalGram N Y = sourceSchurResidual N Y ∧
      (wardPhysicalGram N Y).PosSemidef := by
  have heq : wardPhysicalGram N Y = sourceSchurResidual N Y :=
    (sourceSchurResidual_eq_orthogonalResidual N Y).symm
  exact ⟨heq, heq ▸ sourceSchurResidual_posSemidef N Y⟩

/-- `eq:SMOS-Ward-short-Pythagoras`: for every proposed trivial coefficient
map the residual Gram splits as the physical Gram plus the nuisance
curvature at the optimal coefficients. -/
theorem ward_short_pythagoras {h f e : ℕ}
    (N : Matrix (Fin h) (Fin f) ℂ) (Y : Matrix (Fin h) (Fin e) ℂ)
    (L : Matrix (Fin f) (Fin e) ℂ) :
    (Y - N * L)ᴴ * (Y - N * L) =
      wardPhysicalGram N Y +
        (L - wardOptimalCoefficient N Y)ᴴ *
          ((Nᴴ * N) * (L - wardOptimalCoefficient N Y)) := by
  obtain ⟨hPH, hP2, hPN⟩ := (sourceGramPseudoinverse_projection N).2.2.2
  change (sourceRangeProjection N)ᴴ = sourceRangeProjection N at hPH
  change sourceRangeProjection N * sourceRangeProjection N =
    sourceRangeProjection N at hP2
  change sourceRangeProjection N * N = N at hPN
  have hQH : (1 - sourceRangeProjection N)ᴴ =
      1 - sourceRangeProjection N := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH]
  have hQN : (1 - sourceRangeProjection N) * N = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hPN, sub_self]
  have hNL0 : N * wardOptimalCoefficient N Y =
      sourceRangeProjection N * Y := by
    unfold wardOptimalCoefficient sourceRangeProjection
    simp only [Matrix.mul_assoc]
  have hdec : Y - N * L =
      (1 - sourceRangeProjection N) * Y +
        N * (wardOptimalCoefficient N Y - L) := by
    rw [Matrix.mul_sub, hNL0, Matrix.sub_mul, Matrix.one_mul]
    abel
  have hcross1 : ((1 - sourceRangeProjection N) * Y)ᴴ *
      (N * (wardOptimalCoefficient N Y - L)) = 0 := by
    rw [Matrix.conjTranspose_mul, hQH]
    calc
      Yᴴ * (1 - sourceRangeProjection N) *
          (N * (wardOptimalCoefficient N Y - L))
          = Yᴴ * (((1 - sourceRangeProjection N) * N) *
              (wardOptimalCoefficient N Y - L)) := by
            simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hQN, Matrix.zero_mul, Matrix.mul_zero]
  have hcross2 : (N * (wardOptimalCoefficient N Y - L))ᴴ *
      ((1 - sourceRangeProjection N) * Y) = 0 := by
    have ht := congrArg Matrix.conjTranspose hcross1
    simpa only [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] using ht
  have hgram1 : ((1 - sourceRangeProjection N) * Y)ᴴ *
      ((1 - sourceRangeProjection N) * Y) = wardPhysicalGram N Y :=
    orthComplement_gram_synthesis (sourceRangeProjection N) hPH hP2 Y
  have hgram2 : (N * (wardOptimalCoefficient N Y - L))ᴴ *
      (N * (wardOptimalCoefficient N Y - L)) =
      (L - wardOptimalCoefficient N Y)ᴴ *
        ((Nᴴ * N) * (L - wardOptimalCoefficient N Y)) := by
    have hneg : wardOptimalCoefficient N Y - L =
        -(L - wardOptimalCoefficient N Y) :=
      (neg_sub L (wardOptimalCoefficient N Y)).symm
    rw [hneg, Matrix.mul_neg, Matrix.conjTranspose_neg,
      Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  conv_lhs => rw [hdec]
  rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_add, hcross1, hcross2, hgram1, hgram2]
  simp only [add_zero, zero_add]

/-- Range inclusion is exactly factorization through the nuisance source. -/
theorem range_mulVecLin_le_iff_factor {h f e : ℕ}
    (N : Matrix (Fin h) (Fin f) ℂ) (Y : Matrix (Fin h) (Fin e) ℂ) :
    LinearMap.range Y.mulVecLin ≤ LinearMap.range N.mulVecLin ↔
      ∃ L : Matrix (Fin f) (Fin e) ℂ, Y = N * L := by
  constructor
  · intro hr
    obtain ⟨-, -, hPN⟩ := (sourceGramPseudoinverse_projection N).2.2.2
    change sourceRangeProjection N * N = N at hPN
    have hPY : sourceRangeProjection N * Y = Y := by
      apply Matrix.ext
      intro i j
      obtain ⟨x, hx⟩ := hr (LinearMap.mem_range_self
        Y.mulVecLin (Pi.single j 1))
      simp only [Matrix.mulVecLin_apply] at hx
      have hcol : sourceRangeProjection N *ᵥ (Y *ᵥ Pi.single j 1) =
          Y *ᵥ Pi.single j 1 := by
        rw [← hx, Matrix.mulVec_mulVec, hPN]
      rw [Matrix.mulVec_mulVec] at hcol
      have hentry := congrFun hcol i
      rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at hentry
      exact hentry
    refine ⟨sourceGramPseudoinverse N * (Nᴴ * Y), ?_⟩
    conv_lhs => rw [← hPY]
    unfold sourceRangeProjection
    simp only [Matrix.mul_assoc]
  · rintro ⟨L, rfl⟩
    rintro y ⟨x, hx⟩
    refine ⟨L *ᵥ x, ?_⟩
    rw [Matrix.mulVecLin_apply] at hx ⊢
    rw [Matrix.mulVec_mulVec]
    exact hx

/-- `eq:SMOS-Ward-short-zero`: the physical Ward Gram vanishes exactly when
the direct defect lies in the range of the nuisance source, i.e. when it is
a trivial modification `Y = N L`. -/
theorem ward_short_zero_iff {h f e : ℕ}
    (N : Matrix (Fin h) (Fin f) ℂ) (Y : Matrix (Fin h) (Fin e) ℂ) :
    (wardPhysicalGram N Y = 0 ↔
        LinearMap.range Y.mulVecLin ≤ LinearMap.range N.mulVecLin) ∧
      (wardPhysicalGram N Y = 0 ↔
        ∃ L : Matrix (Fin f) (Fin e) ℂ, Y = N * L) := by
  have hfac : wardPhysicalGram N Y = 0 ↔
      ∃ L : Matrix (Fin f) (Fin e) ℂ, Y = N * L := by
    rw [(wardPhysicalGram_eq_schur N Y).1,
      sourceSchurResidual_eq_zero_iff_rangeIncluded N Y]
    exact Iff.rfl
  exact ⟨hfac.trans (range_mulVecLin_le_iff_factor N Y).symm, hfac⟩

/-- `eq:SMOS-Ward-short-rank`: appending the direct defect to the nuisance
source raises the rank by exactly the rank of the physical Ward Gram. -/
theorem ward_short_rank_increment {h f e : ℕ}
    (N : Matrix (Fin h) (Fin f) ℂ) (Y : Matrix (Fin h) (Fin e) ℂ) :
    (Matrix.fromCols N Y).rank - N.rank = (wardPhysicalGram N Y).rank := by
  have hblock : (Matrix.fromCols N Y)ᴴ * Matrix.fromCols N Y =
      Matrix.fromBlocks (Nᴴ * N) (Nᴴ * Y) ((Nᴴ * Y)ᴴ) (Yᴴ * Y) := by
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Matrix.fromRows_mul_fromCols]
    simp only [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  calc
    (Matrix.fromCols N Y).rank - N.rank
        = ((Matrix.fromCols N Y)ᴴ * Matrix.fromCols N Y).rank -
            (Nᴴ * N).rank := by
          rw [Matrix.rank_conjTranspose_mul_self,
            Matrix.rank_conjTranspose_mul_self]
    _ = (Matrix.fromBlocks (Nᴴ * N) (Nᴴ * Y) ((Nᴴ * Y)ᴴ)
          (Yᴴ * Y)).rank - (Nᴴ * N).rank := by rw [hblock]
    _ = (sourceSchurResidual N Y).rank :=
      sourceSchurResidual_rank_increment N Y
    _ = (wardPhysicalGram N Y).rank := by
      rw [(wardPhysicalGram_eq_schur N Y).1]

/-- Source-minimality of the Ward obstruction: every synthesis of the
physical Ward Gram spends exactly as many source directions as `Y_phys`. -/
theorem ward_short_obstruction_minimality {h f e p : ℕ}
    (N : Matrix (Fin h) (Fin f) ℂ) (Y : Matrix (Fin h) (Fin e) ℂ)
    (B : Matrix (Fin p) (Fin e) ℂ)
    (hB : Bᴴ * B = wardPhysicalGram N Y) :
    B.rank = (wardPhysicalResidual N Y).rank := by
  obtain ⟨hPH, hP2, -⟩ := (sourceGramPseudoinverse_projection N).2.2.2
  change (sourceRangeProjection N)ᴴ = sourceRangeProjection N at hPH
  change sourceRangeProjection N * sourceRangeProjection N =
    sourceRangeProjection N at hP2
  apply gram_synthesis_rank_eq
  rw [hB]
  exact (orthComplement_gram_synthesis (sourceRangeProjection N)
    hPH hP2 Y).symm

/-- `thm:SMOS-Ward-short`: the bundled simultaneous Ward-short theorem —
positivity of the physical Gram, the Pythagoras identity for every trivial
coefficient map, the zero alternative, and the rank identity. -/
theorem simultaneous_ward_short {h f e : ℕ}
    (N : Matrix (Fin h) (Fin f) ℂ) (Y : Matrix (Fin h) (Fin e) ℂ) :
    (wardPhysicalGram N Y).PosSemidef ∧
      (∀ L : Matrix (Fin f) (Fin e) ℂ,
        (Y - N * L)ᴴ * (Y - N * L) =
          wardPhysicalGram N Y +
            (L - wardOptimalCoefficient N Y)ᴴ *
              ((Nᴴ * N) * (L - wardOptimalCoefficient N Y))) ∧
      (wardPhysicalGram N Y = 0 ↔
        ∃ L : Matrix (Fin f) (Fin e) ℂ, Y = N * L) ∧
      (Matrix.fromCols N Y).rank - N.rank = (wardPhysicalGram N Y).rank :=
  ⟨(wardPhysicalGram_eq_schur N Y).2,
    fun L => ward_short_pythagoras N Y L,
    (ward_short_zero_iff N Y).2,
    ward_short_rank_increment N Y⟩

end NCG
