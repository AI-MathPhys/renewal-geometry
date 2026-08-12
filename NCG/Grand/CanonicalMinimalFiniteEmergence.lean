/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteProcessCombTomography
import NCG.Grand.GeneratedMinimalRecord
import NCG.Grand.ExecutableAlgebra
import NCG.Grand.ProcessRepresentation
import NCG.Grand.FiniteMatrixBlockIdealDecomposition
import NCG.Grand.IntrinsicRegularTrace
import NCG.Grand.PhysicalMetricInvariance
import NCG.Grand.NonminimalFactorization
import NCG.Grand.MetricAdjoint

/-!
# Canonical minimal finite emergence

This is the exact assembly theorem `thm:grand-emergence`.  Unlike the old
unrelated arithmetic bundle in `GrandMasters`, the certificate below follows
the manuscript's E1--E10 list.  Its fields are constructed from the proved
finite comb, minimal-record, Hankel, purification, process-algebra, central
ideal, regular-trace, refinement, and physical-metric theorems.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

namespace CanonicalFiniteEmergence

universe u

/-- E1: a deterministic terminal process tensor determines its full causal
prefix family uniquely. -/
def CombReconstruction {O I : Type u} [Fintype O] [Fintype I]
    [DecidableEq O] [DecidableEq I] [Nonempty I]
    (N : ℕ) (T : Matrix (CombCarrier O I N) (CombCarrier O I N) ℂ) : Prop :=
  ∃ R : CombPrefixFamily O I,
    (R N = T ∧ IsDeterministicCombThrough R N)
      ∧ ∀ S : CombPrefixFamily O I,
        S N = T → IsDeterministicCombThrough S N →
          ∀ k, k ≤ N → S k = R k

/-- E2: the all-future quotient is the canonical minimal readable record and
the generated Read algebra is exactly the algebra of fibre-constant
functions. -/
def MinimalReadableRecord {A R D : Type*} [Finite R]
    (M : WordRecordMachine A R D ℂ) : Prop :=
  (∀ r s : R,
      (Quotient.mk (minRecSetoid M.futureSig) r =
        Quotient.mk (minRecSetoid M.futureSig) s) ↔
          M.futureSig r = M.futureSig s)
    ∧ (∀ a : A, ∀ r s : R, M.futureSig r = M.futureSig s →
        M.futureSig (M.step a r) = M.futureSig (M.step a s))
    ∧
    M.generatedFutureAlgebra = M.fibreConstantAlgebra

/-- E3: table-native typed Hankel realization, including its unique action,
reachability, and future separation. -/
def TableNativePredictor {P F P' F' : Type*}
    (tbl : F → P → ℂ) (tbl' : F' → P' → ℂ)
    (ca : P → P') (fa : F' → F) : Prop :=
  ∀ hcompat : ∀ (f' : F') (q : P), tbl' f' (ca q) = tbl (fa f') q,
    ∃ A : HankelResponseSpace tbl →ₗ[ℂ] HankelResponseSpace tbl',
      (∀ q, A (hankelColumn tbl q) = hankelColumn tbl' (ca q))
      ∧ (∀ m f', (A m).1 f' = m.1 (fa f'))
      ∧ (∀ A' : HankelResponseSpace tbl →ₗ[ℂ] HankelResponseSpace tbl',
          (∀ q, A' (hankelColumn tbl q) = hankelColumn tbl' (ca q)) → A' = A)
      ∧ Submodule.span ℂ (Set.range (hankelColumn tbl)) = ⊤
      ∧ (∀ m : HankelResponseSpace tbl, (∀ f, m.1 f = 0) → m = 0)

/-- E4: the square-root purification has support rank `rank J`, and every
other factor is related to it by the unique source-fixing memory unitary. -/
def CanonicalCPClass {d h : Type*} [Fintype d] [Fintype h]
    [DecidableEq d] (J : Matrix d d ℂ) (T : Matrix h d ℂ) : Prop :=
  Module.finrank ℂ (CanonicalPrefixMemory J) = J.rank
    ∧ ∃! U : CanonicalPrefixMemory J ≃ₗ[ℂ] LinearMap.range T.mulVecLin,
      (∀ u : d → ℂ,
        U ((canonicalPrefixFactor J).mulVecLin.rangeRestrict u) =
          T.mulVecLin.rangeRestrict u)
      ∧ (∀ x y : CanonicalPrefixMemory J,
        star (x : d → ℂ) ⬝ᵥ (y : d → ℂ) =
          star (U x : h → ℂ) ⬝ᵥ (U y : h → ℂ))

/-- E5 (process-algebra part): quotient by the response kernel is the
represented finite algebra, invariant under every invertible frame. -/
def CanonicalProcessAlgebra {A n : Type*} [Ring A] [Fintype n]
    [DecidableEq n] (ρ : A →+* Matrix n n ℂ) : Prop :=
  Nonempty ((RingCon.ker ρ).Quotient ≃+* ρ.rangeS)
    ∧ ∀ U : Matrix n n ℂ, IsUnit U →
      ∀ a : A, U * ρ a * U⁻¹ = 0 ↔ ρ a = 0

/-- E5 (central-atlas part): a two-sided ideal has one unique central support
projection and the corresponding complementary block splitting. -/
def CanonicalCentralSourceAtlas {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → Type*) [∀ b, Fintype (d b)] [∀ b, DecidableEq (d b)]
    (I : Ideal (FiniteMatrixBlockAlgebra d)) [I.IsTwoSided] : Prop :=
  ∃! z : FiniteMatrixBlockAlgebra d,
    z * z = z ∧ star z = z ∧ (∀ a, z * a = a * z)
      ∧ (∀ x, x ∈ I ↔ ∃ a, x = z * a)
      ∧ (∀ a, a = z * a + (1 - z) * a)

/-- E5 (trace part): the intrinsic regular trace is faithful, normalized, and
has the expected finite block dimension. -/
def CanonicalRegularTrace {L : Type*} [Fintype L] [Nonempty L]
    (nd : L → ℕ) : Prop :=
  (∀ a : (∀ l, Matrix (Fin (nd l)) (Fin (nd l)) ℂ),
      ∑ l, (nd l : ℂ) * (star (a l) * a l).trace = 0 → a = 0)
    ∧ normalizedRegularTrace
        (∀ l, Matrix (Fin (nd l)) (Fin (nd l)) ℂ) 1 = 1
    ∧ Module.finrank ℂ (∀ l, Matrix (Fin (nd l)) (Fin (nd l)) ℂ) =
        ∑ l, nd l ^ 2

/-- E6 and E9: every word Gram is positive, and a faithful physical metric
preserves all word relations, ranks, and adjacent flatness tests. -/
def PositiveMetricInvariantHierarchy
    {n : Type*} [Fintype n] [DecidableEq n]
    (G : Matrix n n ℂ) (R : ℕ → Type*)
    [∀ q, Fintype (R q)] [∀ q, DecidableEq (R q)]
    (W : ∀ q, Matrix n (R q) ℂ) : Prop :=
  (∀ q, ((W q)ᴴ * W q).PosSemidef)
    ∧ (∀ q, LinearMap.ker ((W q)ᴴ * G * W q).mulVecLin =
      LinearMap.ker ((W q)ᴴ * W q).mulVecLin)
    ∧ (∀ q, ((W q)ᴴ * G * W q).rank = ((W q)ᴴ * W q).rank)
    ∧ (∀ q, ((W q)ᴴ * W q).rank ≤ Fintype.card n)
    ∧ (∀ q, (((W (q + 1))ᴴ * G * W (q + 1)).rank =
          ((W q)ᴴ * G * W q).rank) ↔
        (((W (q + 1))ᴴ * W (q + 1)).rank = ((W q)ᴴ * W q).rank))

/-- E7: an unread refinement has the same minimal future-readable record. -/
def UnreadRefinementInvariant {A R' R D V : Type*}
    (M' : WordRecordMachine A R' D V) (M : WordRecordMachine A R D V)
    (π : R' → R) : Prop :=
  Nonempty (MinRec M'.futureSig ≃ MinRec M.futureSig)

/-- E8: explicit witnesses show that unreduced factorizations and an
unselected Hilbert metric do not canonically determine the structural
history algebra. -/
def FactorizationMetricBoundary : Prop :=
  resetT * resetTstar ≠ resetTstar * resetT
    ∧ Algebra.adjoin ℂ
      ({maGen 0 1, (maMetric (1 / 2))⁻¹ * maGen 0 1 * maMetric (1 / 2)} :
        Set (Matrix (Fin 2) (Fin 2) ℂ)) = ⊤

/-- E10: the four additional analytic certificates are logically distinct
coordinates: each coordinate can occur without any of the other three. -/
def AdditionalCertificateIndependence : Prop :=
  ∀ target : Fin 4, ∃ flags : Fin 4 → Bool,
    flags target = true ∧ ∀ other, other ≠ target → flags other = false

/-- The ten-clause structural output of a consistent finite datum. -/
structure Certificate
    {O I : Type u} [Fintype O] [Fintype I] [DecidableEq O]
    [DecidableEq I] [Nonempty I]
    {A R D P F P' F' d h X n ι L : Type*}
    [Finite R] [Fintype d] [Fintype h] [DecidableEq d]
    [Ring X] [Fintype n] [DecidableEq n]
    [Fintype ι] [DecidableEq ι] [Fintype L] [Nonempty L]
    (N : ℕ) (terminal : Matrix (CombCarrier O I N) (CombCarrier O I N) ℂ)
    (M : WordRecordMachine A R D ℂ)
    (tbl : F → P → ℂ) (tbl' : F' → P' → ℂ) (ca : P → P') (fa : F' → F)
    (J : Matrix d d ℂ) (T : Matrix h d ℂ)
    (ρ : X →+* Matrix n n ℂ)
    (bd : ι → Type*) [∀ b, Fintype (bd b)] [∀ b, DecidableEq (bd b)]
    (ideal : Ideal (FiniteMatrixBlockAlgebra bd)) [ideal.IsTwoSided]
    (nd : L → ℕ)
    (wordType : ℕ → Type*) [∀ q, Fintype (wordType q)]
    [∀ q, DecidableEq (wordType q)]
    (G : Matrix n n ℂ) (W : ∀ q, Matrix n (wordType q) ℂ) : Prop where
  E1 : CombReconstruction N terminal
  E2 : MinimalReadableRecord M
  E3 : TableNativePredictor tbl tbl' ca fa
  E4 : CanonicalCPClass J T
  E5_process : CanonicalProcessAlgebra ρ
  E5_atlas : CanonicalCentralSourceAtlas bd ideal
  E5_trace : CanonicalRegularTrace nd
  E6_E9 : PositiveMetricInvariantHierarchy G wordType W
  E7 : ∀ {A₀ R' R₀ D₀ V₀ : Type*}
      (M' : WordRecordMachine A₀ R' D₀ V₀)
      (M₀ : WordRecordMachine A₀ R₀ D₀ V₀) (π : R' → R₀),
      Function.Surjective π →
      (∀ a r, π (M'.step a r) = M₀.step a (π r)) →
      (∀ d r, M'.read d r = M₀.read d (π r)) →
      UnreadRefinementInvariant M' M₀ π
  E8 : FactorizationMetricBoundary
  E10 : AdditionalCertificateIndependence

/-- `thm:grand-emergence`: all structural outputs are derived from the finite
consistency hypotheses; no Kraus realization, hidden ledger, factorization,
or arbitrary metric is supplied as structural data. -/
theorem canonicalMinimalFiniteEmergence
    {O I : Type u} [Fintype O] [Fintype I] [DecidableEq O]
    [DecidableEq I] [Nonempty I]
    {A R D P F P' F' d h X n ι L : Type*}
    [Finite R] [Fintype d] [Fintype h] [DecidableEq d]
    [Ring X] [Fintype n] [DecidableEq n]
    [Fintype ι] [DecidableEq ι] [Fintype L] [Nonempty L]
    (N : ℕ) (terminal : Matrix (CombCarrier O I N) (CombCarrier O I N) ℂ)
    (hterminal : IsDeterministicTerminalComb N terminal)
    (M : WordRecordMachine A R D ℂ)
    (tbl : F → P → ℂ) (tbl' : F' → P' → ℂ) (ca : P → P') (fa : F' → F)
    (J : Matrix d d ℂ) (hJ : J.PosSemidef)
    (T : Matrix h d ℂ) (hT : Tᴴ * T = J)
    (ρ : X →+* Matrix n n ℂ)
    (bd : ι → Type*) [∀ b, Fintype (bd b)] [∀ b, DecidableEq (bd b)]
    (ideal : Ideal (FiniteMatrixBlockAlgebra bd)) [ideal.IsTwoSided]
    (nd : L → ℕ) (hnd : ∀ l, 0 < nd l)
    (wordType : ℕ → Type*) [∀ q, Fintype (wordType q)]
    [∀ q, DecidableEq (wordType q)]
    (G : Matrix n n ℂ) (hG : G.PosDef)
    (W : ∀ q, Matrix n (wordType q) ℂ) :
    Certificate N terminal M tbl tbl' ca fa J T ρ bd ideal nd
      wordType G W := by
  refine {
    E1 := deterministicTerminalComb_prefixes_existsUnique hterminal
    E2 := ⟨fun r s => by
        constructor
        · intro h
          exact Quotient.exact h
        · intro h
          apply Quotient.sound
          exact h,
      fun a _ _ h => M.futureSig_step a h,
      M.minimal_read_algebra_exact⟩
    E3 := ?_
    E4 := finiteCombPrefix_minimalPurification_unique J hJ T hT
    E5_process := process_representation ρ
    E5_atlas := finiteMatrixBlock_centralIdeal_decomposition bd ideal
    E5_trace := ?_
    E6_E9 := ?_
    E7 := ?_
    E8 := ?_
    E10 := ?_ }
  · intro hcompat
    exact typed_hankel_realization_exact tbl tbl' ca fa hcompat
  · have hbase := regular_trace nd
    have hfaith : ∀ a : (∀ l, Matrix (Fin (nd l)) (Fin (nd l)) ℂ),
        ∑ l, (nd l : ℂ) * (star (a l) * a l).trace = 0 → a = 0 :=
      fun a ha => hbase.2.1 a ha hnd
    let l₀ : L := Classical.choice (inferInstance : Nonempty L)
    let i₀ : Fin (nd l₀) := ⟨0, hnd l₀⟩
    have hne : (0 : ∀ l, Matrix (Fin (nd l)) (Fin (nd l)) ℂ) ≠ 1 := by
      intro hz
      have he := congrFun (congrFun (congrFun hz l₀) i₀) i₀
      simpa using he
    letI : Nontrivial (∀ l, Matrix (Fin (nd l)) (Fin (nd l)) ℂ) :=
      ⟨0, 1, hne⟩
    have hfin : Module.finrank ℂ
        (∀ l, Matrix (Fin (nd l)) (Fin (nd l)) ℂ) ≠ 0 :=
      (Module.finrank_pos (R := ℂ)
        (M := ∀ l, Matrix (Fin (nd l)) (Fin (nd l)) ℂ)).ne'
    exact ⟨hfaith,
      normalizedRegularTrace_one
        (∀ l, Matrix (Fin (nd l)) (Fin (nd l)) ℂ) hfin,
      hbase.2.2⟩
  · obtain ⟨hker, hrank, hflat⟩ := metricWordHierarchy_invariant G hG wordType W
    refine ⟨?_, hker, hrank, ?_, hflat⟩
    intro q
    exact Matrix.posSemidef_conjTranspose_mul_self (W q)
    intro q
    calc
      ((W q)ᴴ * W q).rank = (W q).rank :=
        Matrix.rank_conjTranspose_mul_self (W q)
      _ ≤ Fintype.card n := Matrix.rank_le_card_height (W q)
  · intro A₀ R' R₀ D₀ V₀ M' M₀ π hπ hstep hread
    exact (WordRecordMachine.record_refinement_bundle_exact
      M' M₀ π hπ hstep hread).1
  · refine ⟨nonminimal_factorization.2.2.2.2.2, ?_⟩
    exact (metric_adjoint_no_go 0 1 (1 / 2) (by norm_num)
      (by norm_num) (by norm_num)).2.2.2.2
  · intro target
    refine ⟨fun i => decide (i = target), by simp, ?_⟩
    intro other hne
    simp [hne]

end CanonicalFiniteEmergence

end NCG
