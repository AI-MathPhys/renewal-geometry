/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CPFrameSpan
import NCG.Grand.CombTomography
import NCG.Grand.CanonicalPrefixPurificationUniqueness

/-!
# Exact finite process-comb tomography

This module supplies the multi-slot layer of `thm:comb-tomography`.  Prefix
carriers are recursively typed, the latest output leg is traced explicitly,
and deterministic causality is the full nested recursion.  Positive causal
families produce canonical square-root purifications at every prefix, with
minimal memory rank and the causal Gram links.  Conversely, the certificate
retains exactly positivity, normalization, and those links.  Backward
uniqueness proves that the prefix combs are derived from the terminal tensor.
-/

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

universe u

/-! ## Physical finite tomography -/

/-- Hermitian real part of a finite matrix. -/
def matrixHermitianRealPart {d : Type*} [Fintype d]
    (M : Matrix d d ℂ) : Matrix d d ℂ :=
  (1 / 2 : ℂ) • (M + Mᴴ)

/-- Hermitian imaginary part of a finite matrix. -/
def matrixHermitianImaginaryPart {d : Type*} [Fintype d]
    (M : Matrix d d ℂ) : Matrix d d ℂ :=
  (-Complex.I / 2 : ℂ) • (M - Mᴴ)

theorem matrixHermitianRealPart_isHermitian {d : Type*} [Fintype d]
    (M : Matrix d d ℂ) : (matrixHermitianRealPart M).IsHermitian := by
  apply Matrix.IsHermitian.smul (Matrix.isHermitian_add_transpose_self M)
  simp [IsSelfAdjoint]

theorem matrixHermitianImaginaryPart_isHermitian
    {d : Type*} [Fintype d]
    (M : Matrix d d ℂ) : (matrixHermitianImaginaryPart M).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp [matrixHermitianImaginaryPart, Matrix.conjTranspose_apply]
  ring

theorem matrix_eq_hermitian_parts {d : Type*} [Fintype d]
    (M : Matrix d d ℂ) :
    M = matrixHermitianRealPart M +
      Complex.I • matrixHermitianImaginaryPart M := by
  ext i j
  simp [matrixHermitianRealPart, matrixHermitianImaginaryPart,
    Matrix.conjTranspose_apply]
  rw [← mul_assoc,
    show Complex.I * (-Complex.I / 2) = (1 / 2 : ℂ) by
      calc
        Complex.I * (-Complex.I / 2) =
            (-1 / 2 : ℂ) * (Complex.I * Complex.I) := by ring
        _ = 1 / 2 := by rw [Complex.I_mul_I]; ring]
  ring

/-- Pairing against physical trace-normalized positive Choi branches already
separates Hermitian tensors.  Thus restricting the probability table to
physical interventions loses no tomographic information. -/
theorem physicalChoiBranches_separate_hermitian
    {d : Type*} [Fintype d]
    (R R' : Matrix d d ℂ)
    (hpair : ∀ M : Matrix d d ℂ, M.PosSemidef → (M.trace).re ≤ 1 →
      (R * M).trace = (R' * M).trace) :
    R = R' := by
  have hHermitianPair : ∀ M : Matrix d d ℂ, M.IsHermitian →
      (R * M).trace = (R' * M).trace := by
    intro M hM
    obtain ⟨A, B, s, t, hA, hB, hAtr, hBtr, hs, ht, hsplit⟩ :=
      cp_frame_span M hM
    rw [hsplit, Matrix.mul_sub, Matrix.mul_sub]
    simp only [Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul]
    rw [hpair A hA hAtr, hpair B hB hBtr]
  apply (comb_tomography (m := d)).1 R R'
  intro M
  rw [matrix_eq_hermitian_parts M, Matrix.mul_add, Matrix.mul_add]
  simp only [Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul]
  rw [hHermitianPair _ (matrixHermitianRealPart_isHermitian M),
    hHermitianPair _ (matrixHermitianImaginaryPart_isHermitian M)]

/-- A finite physical Choi frame together with its Hilbert--Schmidt dual. -/
structure PhysicalChoiTomographyFrame (d : Type*) [Fintype d] where
  Probe : Type
  probeFintype : Fintype Probe
  probeDecidableEq : DecidableEq Probe
  probe : Probe → Matrix d d ℂ
  dual : Probe → Matrix d d ℂ
  probePositive : ∀ a, (probe a).PosSemidef
  probeNormalized : ∀ a, ((probe a).trace).re ≤ 1
  dualHermitian : ∀ a, (dual a).IsHermitian
  duality : ∀ a b, ((dual a) * probe b).trace = if a = b then 1 else 0

attribute [instance] PhysicalChoiTomographyFrame.probeFintype
  PhysicalChoiTomographyFrame.probeDecidableEq

/-- Tensor reconstructed by the dual-frame formula from a finite real
probability table. -/
def reconstructChoiTensor {d : Type*} [Fintype d]
    (F : PhysicalChoiTomographyFrame d) (p : F.Probe → ℝ) :
    Matrix d d ℂ :=
  ∑ a, (p a : ℂ) • F.dual a

theorem reconstructChoiTensor_isHermitian {d : Type*} [Fintype d]
    (F : PhysicalChoiTomographyFrame d) (p : F.Probe → ℝ) :
    (reconstructChoiTensor F p).IsHermitian := by
  classical
  unfold reconstructChoiTensor
  exact Finset.sum_induction _ _
    (fun A B hA hB => hA.add hB) Matrix.isHermitian_zero
    (fun a _ => (F.dualHermitian a).smul (by simp [IsSelfAdjoint]))

/-- The reconstructed tensor represents every entry of its physical frame. -/
theorem reconstructChoiTensor_pairing {d : Type*} [Fintype d]
    (F : PhysicalChoiTomographyFrame d) (p : F.Probe → ℝ) (b : F.Probe) :
    ((reconstructChoiTensor F p) * F.probe b).trace = p b := by
  classical
  rw [reconstructChoiTensor, Finset.sum_mul]
  simp only [Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul, F.duality]
  rw [Finset.sum_eq_single b]
  · simp
  · intro a _ hab
    simp [hab]
  · simp

/-- Frame independence: two physical dual frames representing the same
multilinear intervention functional reconstruct the same Hermitian tensor. -/
theorem reconstructChoiTensor_frame_independent
    {d : Type*} [Fintype d]
    (F G : PhysicalChoiTomographyFrame d)
    (p : F.Probe → ℝ) (q : G.Probe → ℝ)
    (hsame : ∀ M : Matrix d d ℂ, M.PosSemidef → (M.trace).re ≤ 1 →
      ((reconstructChoiTensor F p) * M).trace =
        ((reconstructChoiTensor G q) * M).trace) :
    reconstructChoiTensor F p = reconstructChoiTensor G q :=
  physicalChoiBranches_separate_hermitian _ _
    hsame

/-- Chronologically nested carrier for `n` input-output intervention slots. -/
def CombCarrier (O I : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => O × (I × CombCarrier O I n)

instance combCarrierFintype (O I : Type u) [Fintype O] [Fintype I] :
    ∀ n, Fintype (CombCarrier O I n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => by
      letI := combCarrierFintype O I n
      exact inferInstanceAs (Fintype (O × (I × CombCarrier O I n)))

instance combCarrierDecidableEq (O I : Type u) [DecidableEq O] [DecidableEq I] :
    ∀ n, DecidableEq (CombCarrier O I n)
  | 0 => inferInstanceAs (DecidableEq PUnit)
  | n + 1 => by
      letI := combCarrierDecidableEq O I n
      exact inferInstanceAs (DecidableEq (O × (I × CombCarrier O I n)))

/-- Trace the newest output leg of an `(n+1)`-slot Choi tensor. -/
def combOutputTrace {O I : Type u} [Fintype O] {n : ℕ}
    (R : Matrix (CombCarrier O I (n + 1))
      (CombCarrier O I (n + 1)) ℂ) :
    Matrix (I × CombCarrier O I n) (I × CombCarrier O I n) ℂ :=
  fun ix jy => ∑ o : O, R (o, (ix.1, ix.2)) (o, (jy.1, jy.2))

/-- Tensoring a prefix with the identity on the newest input leg. -/
def combIdentityExtension {O I : Type u} [DecidableEq I] {n : ℕ}
    (R : Matrix (CombCarrier O I n) (CombCarrier O I n) ℂ) :
    Matrix (I × CombCarrier O I n) (I × CombCarrier O I n) ℂ :=
  fun ix jy => if ix.1 = jy.1 then R ix.2 jy.2 else 0

@[simp] theorem combIdentityExtension_same {O I : Type u} [DecidableEq I]
    {n : ℕ} (R : Matrix (CombCarrier O I n) (CombCarrier O I n) ℂ)
    (i : I) (x y : CombCarrier O I n) :
    combIdentityExtension R (i, x) (i, y) = R x y := by
  simp [combIdentityExtension]

/-- Identity extension is injective as soon as the input leg is inhabited. -/
theorem combIdentityExtension_injective {O I : Type u} [DecidableEq I]
    [Nonempty I] {n : ℕ} : Function.Injective
      (combIdentityExtension (O := O) (I := I) (n := n)) := by
  intro R S h
  classical
  let i : I := Classical.choice ‹Nonempty I›
  ext x y
  have hxy := congrFun (congrFun h (i, x)) (i, y)
  simpa using hxy

/-- A family of Choi tensors, one at every finite prefix depth. -/
abbrev CombPrefixFamily (O I : Type u) :=
  ∀ n : ℕ, Matrix (CombCarrier O I n) (CombCarrier O I n) ℂ

/-- The exact positive nested-trace criterion through horizon `N`. -/
def IsDeterministicCombThrough {O I : Type u} [Fintype O] [Fintype I]
    [DecidableEq O] [DecidableEq I]
    (R : CombPrefixFamily O I) (N : ℕ) : Prop :=
  R 0 = 1
    ∧ (∀ k, k ≤ N → (R k).PosSemidef)
    ∧ (∀ k, k < N → combOutputTrace (R (k + 1)) =
        combIdentityExtension (R k))

/-- Canonical minimal purifications of all positive prefixes, linked by the
same nested causal Gram recursion. -/
structure LinkedCombPurificationCertificate
    {O I : Type u} [Fintype O] [Fintype I]
    [DecidableEq O] [DecidableEq I]
    (R : CombPrefixFamily O I) (N : ℕ) where
  factor : ∀ k : Fin (N + 1),
    Matrix (CombCarrier O I k.1) (CombCarrier O I k.1) ℂ
  gram : ∀ k : Fin (N + 1), (factor k)ᴴ * factor k = R k.1
  minimalRank : ∀ k : Fin (N + 1),
    Module.finrank ℂ (LinearMap.range (factor k).mulVecLin) = (R k.1).rank
  causalGram : ∀ k : Fin N,
    combOutputTrace ((factor k.succ)ᴴ * factor k.succ) =
      combIdentityExtension ((factor k.castSucc)ᴴ * factor k.castSucc)

/-- A deterministic process comb is a normalized positive causal prefix
family together with its derived linked minimal-purification certificate. -/
structure FiniteDeterministicComb
    {O I : Type u} [Fintype O] [Fintype I]
    [DecidableEq O] [DecidableEq I]
    (R : CombPrefixFamily O I) (N : ℕ) where
  causal : IsDeterministicCombThrough R N
  purification : LinkedCombPurificationCertificate R N

/-- Positivity and the nested trace recursion construct the canonical linked
minimal purifications.  This is the finite sufficiency direction. -/
theorem linkedCombPurificationCertificate_exists
    {O I : Type u} [Fintype O] [Fintype I]
    [DecidableEq O] [DecidableEq I]
    {R : CombPrefixFamily O I} {N : ℕ}
    (hR : IsDeterministicCombThrough R N) :
    Nonempty (LinkedCombPurificationCertificate R N) := by
  let S : ∀ k : Fin (N + 1),
      Matrix (CombCarrier O I k.1) (CombCarrier O I k.1) ℂ :=
    fun k => canonicalPrefixFactor (R k.1)
  refine ⟨{
    factor := S
    gram := ?_
    minimalRank := ?_
    causalGram := ?_ }⟩
  · intro k
    exact canonicalPrefixFactor_gram (R k.1) (hR.2.1 k.1 (Nat.le_of_lt_succ k.2))
  · intro k
    exact canonicalPrefixMemory_finrank (R k.1)
      (hR.2.1 k.1 (Nat.le_of_lt_succ k.2))
  · intro k
    rw [canonicalPrefixFactor_gram (R k.succ.1)
        (hR.2.1 k.succ.1 (Nat.le_of_lt_succ k.succ.2)),
      canonicalPrefixFactor_gram (R k.castSucc.1)
        (hR.2.1 k.castSucc.1 (Nat.le_of_lt_succ k.castSucc.2))]
    exact hR.2.2 k.1 k.2

/-- Exact Choi characterization: a finite deterministic process exists if and
only if the terminal family is positive, normalized at depth zero, and obeys
every nested output-trace recursion. -/
theorem finiteDeterministicComb_iff
    {O I : Type u} [Fintype O] [Fintype I]
    [DecidableEq O] [DecidableEq I]
    {R : CombPrefixFamily O I} {N : ℕ} :
    Nonempty (FiniteDeterministicComb R N) ↔
      IsDeterministicCombThrough R N := by
  constructor
  · rintro ⟨P⟩
    exact P.causal
  · intro hR
    obtain ⟨C⟩ := linkedCombPurificationCertificate_exists hR
    exact ⟨⟨hR, C⟩⟩

/-- The positive causal prefix tensors are derived outputs: two causal prefix
families with the same terminal Choi tensor agree at every earlier depth. -/
theorem causalCombPrefixes_unique_from_terminal
    {O I : Type u} [Fintype O] [Fintype I]
    [DecidableEq O] [DecidableEq I] [Nonempty I]
    {R S : CombPrefixFamily O I} {N : ℕ}
    (hR : IsDeterministicCombThrough R N)
    (hS : IsDeterministicCombThrough S N) (hTop : R N = S N) :
    ∀ k, k ≤ N → R k = S k := by
  intro k hk
  exact Nat.decreasingInduction (motive := fun j _ => R j = S j)
    (fun j hj hnext => by
      apply combIdentityExtension_injective
      calc
        combIdentityExtension (R j) = combOutputTrace (R (j + 1)) :=
          (hR.2.2 j hj).symm
        _ = combOutputTrace (S (j + 1)) :=
          congrArg (combOutputTrace (O := O) (I := I)) hnext
        _ = combIdentityExtension (S j) := hS.2.2 j hj)
    hTop hk

/-- A terminal `N`-slot tensor is deterministic when it admits a normalized,
positive causal prefix family ending at that tensor. -/
def IsDeterministicTerminalComb
    {O I : Type u} [Fintype O] [Fintype I]
    [DecidableEq O] [DecidableEq I]
    (N : ℕ) (T : Matrix (CombCarrier O I N) (CombCarrier O I N) ℂ) : Prop :=
  ∃ R : CombPrefixFamily O I,
    R N = T ∧ IsDeterministicCombThrough R N

/-- Prefix combs are consistency outputs of the terminal tensor: whenever a
deterministic terminal comb exists, its entire causal prefix family is unique. -/
theorem deterministicTerminalComb_prefixes_existsUnique
    {O I : Type u} [Fintype O] [Fintype I]
    [DecidableEq O] [DecidableEq I] [Nonempty I]
    {N : ℕ} {T : Matrix (CombCarrier O I N) (CombCarrier O I N) ℂ}
    (hT : IsDeterministicTerminalComb N T) :
    ∃ R : CombPrefixFamily O I,
      (R N = T ∧ IsDeterministicCombThrough R N)
      ∧ ∀ S : CombPrefixFamily O I,
        S N = T → IsDeterministicCombThrough S N →
          ∀ k, k ≤ N → S k = R k := by
  obtain ⟨R, hRT, hR⟩ := hT
  refine ⟨R, ⟨hRT, hR⟩, ?_⟩
  intro S hST hS k hk
  exact causalCombPrefixes_unique_from_terminal hS hR
    (hST.trans hRT.symm) k hk

/-- Every canonical prefix factor has the manuscript's support-minimal memory
dimension, and any other factor of the same prefix is linked to it by the
unique source-fixing inner-product-preserving gauge. -/
theorem finiteCombPrefix_minimalPurification_unique
    {d h : Type*} [Fintype d] [Fintype h] [DecidableEq d]
    (J : Matrix d d ℂ) (hJ : J.PosSemidef) (T : Matrix h d ℂ)
    (hT : Tᴴ * T = J) :
    Module.finrank ℂ (CanonicalPrefixMemory J) = J.rank
    ∧ ∃! U : CanonicalPrefixMemory J ≃ₗ[ℂ] LinearMap.range T.mulVecLin,
      (∀ u : d → ℂ,
        U ((canonicalPrefixFactor J).mulVecLin.rangeRestrict u) =
          T.mulVecLin.rangeRestrict u)
      ∧ (∀ x y : CanonicalPrefixMemory J,
        star (x : d → ℂ) ⬝ᵥ (y : d → ℂ) =
          star (U x : h → ℂ) ⬝ᵥ (U y : h → ℂ)) :=
  ⟨canonicalPrefixMemory_finrank J hJ,
    canonicalPrefixPurification_unique J hJ T hT⟩

end NCG
