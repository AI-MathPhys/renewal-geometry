/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GrandInterface2

/-!
# Reset/record audit and the common Hodge–Dirac transport
  (`thm:reset-record-audit`, `thm:SM-common-Hodge-Dirac`,
   Gran-Tensor manuscript)

* `reset_record_audit`: exact record future-nullity is the boxed
  Gram identity — `J*(C*C)J = 0 ↔ CJ = 0`; and for the
  reset-form branch `R(X) = Tr(EX)·ω` the Hilbert–Schmidt
  pairing factors, `⟨Y, R(X)⟩ = Tr(EX)·⟨Y, ω⟩` — the rank-one
  form of the transfer;
* `sm_common_hodge_dirac`: the record-naturality residual
  vanishes exactly when the induced unitary intertwines the
  generating family, and exact intertwining transports each
  generator by conjugation, `B_j = J A_j J*` — the boxed
  `K_res = J K_occ J*` and `Θ_res = J Θ_occ J*` on the
  generated algebra.

Rendering disclosed: the converse rank-one⇒factorization
direction of the reset audit is the singular-value bookkeeping;
the transport of `K` and `Θ` beyond the generating family
follows on the generated algebra and is disclosed.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- `thm:reset-record-audit`: the boxed nullity identity and
the rank-one factored pairing of the reset branch. -/
theorem reset_record_audit {t h e : Type*} [Fintype t]
    [Fintype h]
    (C : Matrix h t ℂ) (J : Matrix t e ℂ)
    (E ω : Matrix t t ℂ) :
    (Jᴴ * (Cᴴ * C) * J = 0 ↔ C * J = 0)
    ∧ (∀ X Y : Matrix t t ℂ,
        (Yᴴ * (((E * X).trace) • ω)).trace
          = ((E * X).trace) * ((Yᴴ * ω).trace)) := by
  constructor
  · have hgram : Jᴴ * (Cᴴ * C) * J = (C * J)ᴴ * (C * J) := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [hgram]
    exact Matrix.conjTranspose_mul_self_eq_zero
  · intro X Y
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

/-- `thm:SM-common-Hodge-Dirac`: vanishing record-naturality
residual is exact intertwining, and exact intertwining is
conjugation transport of each generator. -/
theorem sm_common_hodge_dirac {occ res : Type*} [Fintype occ]
    [DecidableEq occ] [Fintype res] [DecidableEq res] {s : ℕ}
    (J : Matrix res occ ℂ) (_hJl : Jᴴ * J = 1)
    (hJr : J * Jᴴ = 1)
    (Ao : Fin s → Matrix occ occ ℂ)
    (Ar : Fin s → Matrix res res ℂ) :
    ((∑ j, (((J * Ao j - Ar j * J)ᴴ
        * (J * Ao j - Ar j * J)).trace).re) = 0
      ↔ ∀ j, J * Ao j = Ar j * J)
    ∧ (∀ j, J * Ao j = Ar j * J →
        Ar j = J * Ao j * Jᴴ) := by
  constructor
  · constructor
    · intro h0 j
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => by
          rw [trace_conj_self_re]
          exact Finset.sum_nonneg fun a _ =>
            Finset.sum_nonneg fun b _ =>
              Complex.normSq_nonneg _)).mp h0 j
        (Finset.mem_univ j)
      have hz := (trace_conj_self_re_eq_zero _).mp hterm
      exact sub_eq_zero.mp hz
    · intro hcomm
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [show J * Ao j - Ar j * J = 0 from
        sub_eq_zero.mpr (hcomm j)]
      simp
  · intro j hj
    rw [hj, Matrix.mul_assoc, hJr, Matrix.mul_one]

end NCG
