/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact character-sector leakage and primitive sector saturation
  (`thm:character-leakage-master`, `thm:primitive-sector-saturation`,
   flagship manuscript)

In the whitened picture (the pseudoinverse square root
`(ℍ⁰)†/²` turning the controllability map into an isometry `V`,
the displayed classical whitening step):

* `saturation_rank`: `thm:primitive-sector-saturation`, boxed
  identity — the rank of the Gram `ℍ⁰ = C*C` equals the rank of
  the controllability map `C`, i.e. the dimension of the Krylov
  head `𝒦_{π,n}`;
* `krylov_stabilization`: if consecutive Krylov heads have equal
  dimension they coincide, and a `T`-invariant head freezes all
  later layers — the finite-transition reconstruction clause;
* `leakage_gram_identity`: `thm:character-leakage-master`, boxed
  operator — for an isometry `V` (`V*V = 1`) and Hermitian `T`,
  `𝕍 = V*T²V - (V*TV)² = (QTV)*(QTV)` with `Q = 1 - VV*`,
  so `𝕍 ⪰ 0`;
* `leakage_rank_and_vanishing`: `rank 𝕍 = rank(QTV)` — the
  number of explicit next missing source directions — and
  `𝕍 = 0` exactly when the head is `T`-invariant (`QTV = 0`),
  the saturation criterion.

Rendering disclosed: the pseudoinverse square-root whitening
`(ℍ⁰)†/²` and the identification of `rank(QTV)` with
`dim(𝒦_{n+1} ⊖ 𝒦_n)` in the ambient realization are the
manuscript's spectral-calculus bookkeeping; the isotypic
divisibility `d_π ∣ rank` is the `K`-invariance clause on top of
Schur's lemma.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

variable {N q : Type*} [Fintype N] [Fintype q]

/-- `thm:primitive-sector-saturation`, boxed identity: the Gram
rank equals the controllability rank (the Krylov-head
dimension). -/
theorem saturation_rank (C : Matrix N q ℂ) :
    (Cᴴ * C).rank = C.rank :=
  Matrix.rank_conjTranspose_mul_self C

/-- Krylov stabilization: nested heads of equal finite dimension
coincide, and a `T`-invariant head freezes all later layers. -/
theorem krylov_stabilization {E : Type*} [AddCommGroup E]
    [Module ℂ E] [FiniteDimensional ℂ E]
    (K : ℕ → Submodule ℂ E) (T : E →ₗ[ℂ] E) (n : ℕ)
    (hmono : ∀ k, K k ≤ K (k + 1))
    (hstep : ∀ k, K (k + 1) ≤ K k ⊔ Submodule.map T (K k))
    (heq : Module.finrank ℂ (K (n + 1))
      ≤ Module.finrank ℂ (K n)) :
    K (n + 1) = K n
    ∧ (Submodule.map T (K n) ≤ K n →
        ∀ j, n ≤ j → K j = K n) := by
  have hKn : K (n + 1) = K n :=
    (Submodule.eq_of_le_of_finrank_le (hmono n) heq).symm
  refine ⟨hKn, fun hT j hj => ?_⟩
  induction j with
  | zero =>
    have h0 : n = 0 := Nat.le_zero.mp hj
    rw [h0]
  | succ j ih =>
    rcases Nat.lt_or_ge n (j + 1) with hlt | hge
    · have hnj : n ≤ j := Nat.lt_succ_iff.mp hlt
      have hj' := ih hnj
      refine le_antisymm ?_ (hj' ▸ hmono j)
      calc K (j + 1) ≤ K j ⊔ Submodule.map T (K j) := hstep j
        _ = K n ⊔ Submodule.map T (K n) := by rw [hj']
        _ ≤ K n := sup_le le_rfl hT
    · have hjn : j + 1 = n := le_antisymm hge hj
      rw [hjn]

/-- `thm:character-leakage-master`, boxed operator: in the
whitened picture the leakage Gram is
`𝕍 = V*T²V - (V*TV)² = (QTV)*(QTV) ⪰ 0`. -/
theorem leakage_gram_identity [DecidableEq N] [DecidableEq q]
    (V : Matrix N q ℂ) (T : Matrix N N ℂ)
    (hV : Vᴴ * V = 1) (hT : Tᴴ = T) :
    Vᴴ * (T * T) * V - (Vᴴ * T * V) * (Vᴴ * T * V)
      = ((1 - V * Vᴴ) * T * V)ᴴ * ((1 - V * Vᴴ) * T * V)
    ∧ (Vᴴ * (T * T) * V
        - (Vᴴ * T * V) * (Vᴴ * T * V)).PosSemidef := by
  have hM : (1 - V * Vᴴ) * T * V
      = T * V - V * (Vᴴ * T * V) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul]
    simp only [Matrix.mul_assoc]
  have hVX : Vᴴ * (T * V) = Vᴴ * T * V := by
    rw [Matrix.mul_assoc]
  have hAH : (Vᴴ * T * V)ᴴ = Vᴴ * T * V := by
    rw [conjTranspose_mul, conjTranspose_mul,
      conjTranspose_conjTranspose, hT, Matrix.mul_assoc]
  have hXV : (T * V)ᴴ * V = Vᴴ * T * V := by
    rw [conjTranspose_mul, hT, Matrix.mul_assoc]
  have hkey : ((1 - V * Vᴴ) * T * V)ᴴ * ((1 - V * Vᴴ) * T * V)
      = Vᴴ * (T * T) * V
        - (Vᴴ * T * V) * (Vᴴ * T * V) := by
    rw [hM]
    have hexp : (T * V - V * (Vᴴ * T * V))ᴴ
          * (T * V - V * (Vᴴ * T * V))
        = (T * V)ᴴ * (T * V)
          - (T * V)ᴴ * (V * (Vᴴ * T * V))
          - (V * (Vᴴ * T * V))ᴴ * (T * V)
          + (V * (Vᴴ * T * V))ᴴ * (V * (Vᴴ * T * V)) := by
      rw [conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub,
        Matrix.mul_sub]
      abel
    have ht1 : (T * V)ᴴ * (T * V) = Vᴴ * (T * T) * V := by
      rw [conjTranspose_mul, hT]
      simp only [Matrix.mul_assoc]
    have ht2 : (T * V)ᴴ * (V * (Vᴴ * T * V))
        = (Vᴴ * T * V) * (Vᴴ * T * V) := by
      rw [← Matrix.mul_assoc, hXV]
    have ht3 : (V * (Vᴴ * T * V))ᴴ * (T * V)
        = (Vᴴ * T * V) * (Vᴴ * T * V) := by
      rw [conjTranspose_mul, hAH, Matrix.mul_assoc, hVX]
    have ht4 : (V * (Vᴴ * T * V))ᴴ * (V * (Vᴴ * T * V))
        = (Vᴴ * T * V) * (Vᴴ * T * V) := by
      rw [conjTranspose_mul, hAH, ← Matrix.mul_assoc,
        Matrix.mul_assoc (Vᴴ * T * V), hV, Matrix.mul_one]
    rw [hexp, ht1, ht2, ht3, ht4]
    abel
  refine ⟨hkey.symm, ?_⟩
  rw [← hkey]
  exact posSemidef_conjTranspose_mul_self _

/-- Leakage rank and vanishing: `rank 𝕍 = rank(QTV)` and
`𝕍 = 0 ↔ QTV = 0` (the head is `T`-invariant — saturation). -/
theorem leakage_rank_and_vanishing [DecidableEq N]
    [DecidableEq q]
    (V : Matrix N q ℂ) (T : Matrix N N ℂ)
    (hV : Vᴴ * V = 1) (hT : Tᴴ = T) :
    (Vᴴ * (T * T) * V - (Vᴴ * T * V) * (Vᴴ * T * V)).rank
      = ((1 - V * Vᴴ) * T * V).rank
    ∧ (Vᴴ * (T * T) * V - (Vᴴ * T * V) * (Vᴴ * T * V) = 0
        ↔ (1 - V * Vᴴ) * T * V = 0) := by
  obtain ⟨hid, -⟩ := leakage_gram_identity V T hV hT
  constructor
  · rw [hid]
    exact Matrix.rank_conjTranspose_mul_self _
  · rw [hid]
    exact conjTranspose_mul_self_eq_zero

end NCG
