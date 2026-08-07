/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SqrtPolar

/-!
# Canonical cutoff support, absorbing histories, and quotient
  transport
  (`thm:cutoff-compatibility`, Gran-Tensor manuscript)

* `cutoff_support_transport` (C1)–(C2): on full supports, the
  boxed support isometry `W·(R_X)^{1/2} = (R_Y)^{1/2}·J`
  exists (`W = √R_Y·J·(√R_X)⁻¹`), is an exact isometry
  (`WᴴW = 1`, from the prefix-exact congruence
  `JᴴR_YJ = R_X`), is unique, and composes strictly along
  chained cutoffs.

* `cutoff_absorbing_corner` (C3)–(C4): for an isometry `C`,
  the absorbing compression `Γ(x) = CxCᴴ` is a unital-corner
  `*`-embedding: multiplicative onto the corner, adjoint-
  preserving, injective, with idempotent hermitian corner
  unit `Γ(1) = CCᴴ`.

* `cutoff_quotient_transport` (C6)–(C7): the contextual
  innovation Gram `F(1-P)Fᴴ` vanishes exactly when the new
  rows lie in the old contextual span, and the central
  transport density is unique under a faithful trace.

Clause (C5) (full-letter inflow defects) and the exact
sequential-isometry intertwinings are the manuscript's
bookkeeping over these identities; the congruence core
`K_X = IᴴK_YI` is the previously proved
`NCG.cutoff_compatibility` (GrandOrder.lean).
-/

open Matrix
open scoped ComplexOrder MatrixOrder

set_option linter.unusedDecidableInType false

namespace NCG

/-- `thm:cutoff-compatibility` (C1)–(C2): the boxed polar
support isometry, its uniqueness, and strict transitivity. -/
theorem cutoff_support_transport {a b c : Type*} [Fintype a]
    [Fintype b] [Fintype c] [DecidableEq a] [DecidableEq b]
    [DecidableEq c]
    (RX : Matrix a a ℂ) (RY : Matrix b b ℂ)
    (J : Matrix b a ℂ) (hRX : RX.PosDef)
    (hprefix : Jᴴ * RY * J = RX) :
    -- the boxed intertwining `W·√R_X = √R_Y·J`
    (CFC.sqrt RY * J * (CFC.sqrt RX)⁻¹) * CFC.sqrt RX
      = CFC.sqrt RY * J
    -- `W` is an exact isometry
    ∧ (RY.PosSemidef →
        (CFC.sqrt RY * J * (CFC.sqrt RX)⁻¹)ᴴ
          * (CFC.sqrt RY * J * (CFC.sqrt RX)⁻¹) = 1)
    -- uniqueness on the full support
    ∧ (∀ W : Matrix b a ℂ,
        W * CFC.sqrt RX = CFC.sqrt RY * J →
        W = CFC.sqrt RY * J * (CFC.sqrt RX)⁻¹)
    -- strict transitivity along chained cutoffs
    ∧ (∀ (RZ : Matrix c c ℂ) (JYZ : Matrix c b ℂ)
        (_hRY : RY.PosDef),
        (CFC.sqrt RZ * JYZ * (CFC.sqrt RY)⁻¹)
          * (CFC.sqrt RY * J * (CFC.sqrt RX)⁻¹)
        = CFC.sqrt RZ * (JYZ * J) * (CFC.sqrt RX)⁻¹) := by
  have hXu := sqrt_isUnit hRX
  haveI := hXu.invertible
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, Matrix.inv_mul_of_invertible,
      Matrix.mul_one]
  · intro hRYpsd
    set S := CFC.sqrt RX with hSdef
    have hS2 : S * S = RX := sqrt_mul_self_eq RX hRX.posSemidef
    have hSinvH : (S⁻¹)ᴴ = S⁻¹ := sqrt_inv_isHermitian RX
    have hT2 : CFC.sqrt RY * CFC.sqrt RY = RY :=
      sqrt_mul_self_eq RY hRYpsd
    have hTH : (CFC.sqrt RY)ᴴ = CFC.sqrt RY :=
      sqrt_isHermitian RY
    calc (CFC.sqrt RY * J * S⁻¹)ᴴ
          * (CFC.sqrt RY * J * S⁻¹)
        = (S⁻¹)ᴴ * (Jᴴ * ((CFC.sqrt RY)ᴴ
            * (CFC.sqrt RY * (J * S⁻¹)))) := by
          simp only [Matrix.conjTranspose_mul,
            Matrix.mul_assoc]
      _ = S⁻¹ * ((Jᴴ * RY * J) * S⁻¹) := by
          rw [hSinvH, hTH,
            ← Matrix.mul_assoc (CFC.sqrt RY) (CFC.sqrt RY),
            hT2]
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hprefix, ← hS2]
          calc S⁻¹ * (S * S * S⁻¹)
              = S⁻¹ * (S * (S * S⁻¹)) := by
                simp only [Matrix.mul_assoc]
            _ = 1 := by
                rw [Matrix.mul_inv_of_invertible,
                  Matrix.mul_one,
                  Matrix.inv_mul_of_invertible]
  · intro W hW
    have h := congrArg (fun X => X * (CFC.sqrt RX)⁻¹) hW
    simpa [Matrix.mul_assoc,
      Matrix.mul_inv_of_invertible] using h
  · intro RZ JYZ hRY
    have hYu := sqrt_isUnit hRY
    haveI := hYu.invertible
    calc (CFC.sqrt RZ * JYZ * (CFC.sqrt RY)⁻¹)
          * (CFC.sqrt RY * J * (CFC.sqrt RX)⁻¹)
        = CFC.sqrt RZ * JYZ * (((CFC.sqrt RY)⁻¹
            * CFC.sqrt RY) * (J * (CFC.sqrt RX)⁻¹)) := by
          simp only [Matrix.mul_assoc]
      _ = CFC.sqrt RZ * (JYZ * J) * (CFC.sqrt RX)⁻¹ := by
          rw [Matrix.inv_mul_of_invertible, Matrix.one_mul]
          simp only [Matrix.mul_assoc]

/-- `thm:cutoff-compatibility` (C3)–(C4): the absorbing
corner is a unital-corner `*`-embedding. -/
theorem cutoff_absorbing_corner {a b : Type} [Fintype a]
    [Fintype b] [DecidableEq a]
    (C : Matrix b a ℂ) (hC : Cᴴ * C = 1) :
    -- multiplicative onto the corner
    (∀ x y : Matrix a a ℂ,
      (C * x * Cᴴ) * (C * y * Cᴴ) = C * (x * y) * Cᴴ)
    -- adjoint-preserving
    ∧ (∀ x : Matrix a a ℂ,
        (C * x * Cᴴ)ᴴ = C * xᴴ * Cᴴ)
    -- injective
    ∧ (∀ x : Matrix a a ℂ, C * x * Cᴴ = 0 → x = 0)
    -- idempotent hermitian corner unit
    ∧ (C * Cᴴ) * (C * Cᴴ) = C * Cᴴ
    ∧ (C * Cᴴ)ᴴ = C * Cᴴ := by
  have hcan : ∀ {m : Type} [Fintype m]
      (X : Matrix a m ℂ), Cᴴ * (C * X) = X := by
    intro m _ X
    rw [← Matrix.mul_assoc, hC, Matrix.one_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    calc (C * x * Cᴴ) * (C * y * Cᴴ)
        = C * (x * (Cᴴ * (C * (y * Cᴴ)))) := by
          simp only [Matrix.mul_assoc]
      _ = C * (x * y) * Cᴴ := by
          rw [hcan]
          simp only [Matrix.mul_assoc]
  · intro x
    simp only [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  · intro x hx
    have h := congrArg (fun Y => Cᴴ * Y * C) hx
    simp only [Matrix.mul_zero, Matrix.zero_mul] at h
    rw [show Cᴴ * (C * x * Cᴴ) * C = x from by
      calc Cᴴ * (C * x * Cᴴ) * C
          = Cᴴ * (C * (x * (Cᴴ * C))) := by
            simp only [Matrix.mul_assoc]
        _ = x := by
            rw [hC, Matrix.mul_one, hcan]] at h
    exact h
  · calc (C * Cᴴ) * (C * Cᴴ)
        = C * (Cᴴ * C) * Cᴴ := by
          simp only [Matrix.mul_assoc]
      _ = C * Cᴴ := by
          rw [hC, Matrix.mul_one]
  · rw [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]

/-- `thm:cutoff-compatibility` (C6)–(C7): contextual
innovation vanishing and uniqueness of the central transport
density. -/
theorem cutoff_quotient_transport {n r : Type*} [Fintype n]
    [DecidableEq n] :
    -- (C6) the innovation Gram vanishes iff containment
    (∀ (F : Matrix r n ℂ) (P : Matrix n n ℂ),
      Pᴴ = P → P * P = P →
      (F * (1 - P) * Fᴴ = 0 ↔ (1 - P) * Fᴴ = 0))
    -- (C7) uniqueness of the central density
    ∧ (∀ h h' : Matrix n n ℂ,
        (∀ x : Matrix n n ℂ,
          (h * x).trace = (h' * x).trace) →
        h = h') := by
  constructor
  · intro F P hPH hP2
    have hQH : ((1 : Matrix n n ℂ) - P)ᴴ = 1 - P := by
      rw [Matrix.conjTranspose_sub,
        Matrix.conjTranspose_one, hPH]
    have hQ2 : ((1 : Matrix n n ℂ) - P) * (1 - P)
        = 1 - P := by
      simp only [Matrix.sub_mul, Matrix.mul_sub,
        Matrix.one_mul, Matrix.mul_one, hP2]
      abel
    have hfac : F * (1 - P) * Fᴴ
        = ((1 - P) * Fᴴ)ᴴ * ((1 - P) * Fᴴ) := by
      rw [Matrix.conjTranspose_mul, hQH,
        Matrix.conjTranspose_conjTranspose]
      calc F * (1 - P) * Fᴴ
          = F * ((1 - P) * ((1 - P) * Fᴴ)) := by
            rw [← Matrix.mul_assoc (1 - P), hQ2,
              Matrix.mul_assoc]
        _ = F * (1 - P) * ((1 - P) * Fᴴ) := by
            simp only [Matrix.mul_assoc]
    rw [hfac]
    exact Matrix.conjTranspose_mul_self_eq_zero
  · intro h h' htr
    have hkey := htr (h - h')ᴴ
    have hz : ((h - h') * (h - h')ᴴ).trace = 0 := by
      rw [Matrix.sub_mul, Matrix.trace_sub, hkey]
      exact sub_self _
    have h0 :=
      Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp hz
    exact sub_eq_zero.mp h0

end NCG
