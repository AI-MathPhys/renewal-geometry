/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.KMSDual

/-!
# Branchwise Petz reversal on the predictive orbit

Covers `prop:branchwise-petz-reference-renewal` from
`manuscripts/renewal_emergence/renewal_emergence.tex`, for a **general** CP trace-nonincreasing
branch `ℰ_e : 𝒜_x → 𝒜_y` satisfying the reference-renewal identity
`ℰ_e(ρ_x) = w_e ρ_y` with faithful support states: the Petz reversal

`ℰ_e^← := Γ_{ρ_x} ∘ ℰ_e^* ∘ Γ_{ρ_y}^{-1}`, `Γ_ρ(a) = ρ^{1/2} a ρ^{1/2}`,

is a CP branch (`petzReverse_cp`) with exact trace scaling
`Tr ℰ_e^←(τ) = w_e Tr τ` (`petzReverse_trace`, hence
trace-nonincreasing for `w_e ≤ 1`, and `Tr ℰ_e^←(ρ_y) = w_e`), its
Heisenberg adjoint is `Γ_{ρ_y}^{-1} ∘ ℰ_e ∘ Γ_{ρ_x}`
(`petzReverse_pairing`) with unit value `w_e 1_y`
(`petzReverseHeis_unit`), it renews the reverse reference state iff
`ℰ_e^*(1_y) = w_e 1_x` (`petzReverse_renewal_iff`), reversal is
involutive (`petzReverse_involutive`), and composition reverses
contravariantly (`petzReverse_comp`).

Conventions follow `NCG.Upstream.KMSDual`: algebras are star-ordered
`ℂ`-algebras with cyclic trace functionals; maps travel with their
trace-adjoint preduals (the pairing is a hypothesis); square roots
`σ = ρ^{1/2}` and inverses are data.  CP of the trace adjoint of a CP
branch is supplied as a hypothesis (as in `prop:reverse-comparison`,
it is data in the abstract setting; it is automatic in the intended
matrix realization).
-/

namespace NCG.Upstream

open NCG

variable {Ax Ay Az : Type*}
variable [Ring Ax] [PartialOrder Ax] [StarRing Ax] [StarOrderedRing Ax]
  [Algebra ℂ Ax] [StarModule ℂ Ax]
variable [Ring Ay] [PartialOrder Ay] [StarRing Ay] [StarOrderedRing Ay]
  [Algebra ℂ Ay] [StarModule ℂ Ay]
variable [Ring Az] [PartialOrder Az] [StarRing Az] [StarOrderedRing Az]
  [Algebra ℂ Az] [StarModule ℂ Az]

/-- Complete positivity for a linear map between two (possibly
different) star-ordered algebras: every matrix amplification
preserves quadratic-form positivity.  For `Ax = Ay` this is
definitionally `NCG.IsCompletelyPositive`. -/
def IsCPBranchMap (φ : Ax →ₗ[ℂ] Ay) : Prop :=
  ∀ (k : ℕ) (M : Matrix (Fin k) (Fin k) Ax),
    MatrixQF M → MatrixQF (M.map φ)

omit [StarModule ℂ Ax] [StarModule ℂ Ay] [StarModule ℂ Az] [StarOrderedRing Ax] [StarOrderedRing
  Ay] [StarOrderedRing Az] in
/-- CP branch maps compose. -/
theorem IsCPBranchMap.comp {φ : Ax →ₗ[ℂ] Ay} {ψ : Ay →ₗ[ℂ] Az}
    (hφ : IsCPBranchMap φ) (hψ : IsCPBranchMap ψ) :
    IsCPBranchMap (ψ ∘ₗ φ) := by
  intro k M hM
  have h : M.map ⇑(ψ ∘ₗ φ) = (M.map ⇑φ).map ⇑ψ := by
    ext i j
    simp [Matrix.map_apply]
  rw [h]
  exact hψ k _ (hφ k M hM)

omit [StarModule ℂ Ax] [StarOrderedRing Ax] in
/-- On a single algebra the branch notion coincides with
`NCG.IsCompletelyPositive`. -/
theorem isCPBranchMap_iff_cp (φ : Ax →ₗ[ℂ] Ax) :
    IsCPBranchMap φ ↔ IsCompletelyPositive φ := Iff.rfl

section Branch

variable (τx : Ax →ₗ[ℂ] ℂ) (τy : Ay →ₗ[ℂ] ℂ)
variable (σx σxi : Ax) (σy σyi : Ay)
variable (E : Ax →ₗ[ℂ] Ay) (Estar : Ay →ₗ[ℂ] Ax) (w : ℝ)

/-- **Proposition `prop:branchwise-petz-reference-renewal`
(the reversal)**: `ℰ^← = Γ_{ρ_x} ∘ ℰ^* ∘ Γ_{ρ_y}^{-1}` on densities,
with `Γ_ρ = sandwich ρ^{1/2}`. -/
def petzReverse : Ay →ₗ[ℂ] Ax :=
  (sandwich σx) ∘ₗ Estar ∘ₗ (sandwich σyi)

omit [PartialOrder Ax] [PartialOrder Ay] [StarModule ℂ Ax] [StarModule ℂ Ay] [StarOrderedRing Ax]
  [StarOrderedRing Ay] [StarRing Ax] [StarRing Ay] in
theorem petzReverse_apply (t : Ay) :
    petzReverse σx σyi Estar t = σx * Estar (σyi * t * σyi) * σx := rfl

/-- The Heisenberg adjoint of the reversal,
`(ℰ^←)^* = Γ_{ρ_y}^{-1} ∘ ℰ ∘ Γ_{ρ_x}`. -/
def petzReverseHeis : Ax →ₗ[ℂ] Ay :=
  (sandwich σyi) ∘ₗ E ∘ₗ (sandwich σx)

omit [PartialOrder Ax] [PartialOrder Ay] [StarModule ℂ Ax] [StarModule ℂ Ay] [StarOrderedRing Ax]
  [StarOrderedRing Ay] [StarRing Ax] [StarRing Ay] in
theorem petzReverseHeis_apply (a : Ax) :
    petzReverseHeis σx σyi E a = σyi * E (σx * a * σx) * σyi := rfl

omit [StarModule ℂ Ax] [StarModule ℂ Ay] [StarOrderedRing Ax] [StarOrderedRing Ay] in
/-- **`prop:branchwise-petz-reference-renewal` (CP)**: the reversal
of a CP branch is a CP branch — a composition of the two sandwich
congruences with the CP trace adjoint. -/
theorem petzReverse_cp (hσx : star σx = σx) (hσyi : star σyi = σyi)
    (hE : IsCPBranchMap Estar) :
    IsCPBranchMap (petzReverse σx σyi Estar) := by
  have h1 : IsCPBranchMap (sandwich σyi : Ay →ₗ[ℂ] Ay) :=
    sandwich_cp_self σyi hσyi
  have h2 : IsCPBranchMap (sandwich σx : Ax →ₗ[ℂ] Ax) :=
    sandwich_cp_self σx hσx
  exact IsCPBranchMap.comp (IsCPBranchMap.comp h1 hE) h2

omit [PartialOrder Ax] [PartialOrder Ay] [StarModule ℂ Ax] [StarModule ℂ Ay] [StarOrderedRing Ax]
  [StarOrderedRing Ay] [StarRing Ax] [StarRing Ay] in
/-- **`prop:branchwise-petz-reference-renewal` (exact trace
scaling)**: `Tr ℰ^←(τ) = w Tr τ` for every `τ` — reference renewal
`ℰ(ρ_x) = w ρ_y` plus the trace pairing.  Trace-nonincrease for
`w ≤ 1` and the value `Tr ℰ^←(ρ_y) = w` (normalisation
`Tr ρ_y = 1`) are immediate specializations. -/
theorem petzReverse_trace
    (hτxc : ∀ a b : Ax, τx (a * b) = τx (b * a))
    (hτyc : ∀ a b : Ay, τy (a * b) = τy (b * a))
    (hpair : ∀ (s : Ax) (a : Ay), τy (E s * a) = τx (s * Estar a))
    (hren : E (σx * σx) = ((w : ℝ) : ℂ) • (σy * σy))
    (hσy1 : σy * σyi = 1) (hσy2 : σyi * σy = 1) (t : Ay) :
    τx (petzReverse σx σyi Estar t) = ((w : ℝ) : ℂ) * τy t := by
  rw [petzReverse_apply]
  have h1 : τx (σx * Estar (σyi * t * σyi) * σx)
      = τx ((σx * σx) * Estar (σyi * t * σyi)) := by
    rw [hτxc (σx * Estar (σyi * t * σyi)) σx]
    congr 1
    noncomm_ring
  rw [h1, ← hpair, hren, smul_mul_assoc, map_smul, smul_eq_mul]
  congr 1
  calc τy ((σy * σy) * (σyi * t * σyi))
      = τy ((σy * (σy * σyi)) * (t * σyi)) := by
        congr 1
        noncomm_ring
    _ = τy (σy * (t * σyi)) := by rw [hσy1, mul_one]
    _ = τy ((t * σyi) * σy) := hτyc _ _
    _ = τy (t * (σyi * σy)) := by
        congr 1
        noncomm_ring
    _ = τy t := by rw [hσy2, mul_one]

omit [PartialOrder Ax] [PartialOrder Ay] [StarModule ℂ Ax] [StarModule ℂ Ay] [StarOrderedRing Ax]
  [StarOrderedRing Ay] [StarRing Ax] [StarRing Ay] in
/-- **`prop:branchwise-petz-reference-renewal`
(trace-nonincreasing)**: for `0 < w ≤ 1` the reversed branch does
not increase the trace of any density with real nonnegative
trace. -/
theorem petzReverse_trace_le
    (hτxc : ∀ a b : Ax, τx (a * b) = τx (b * a))
    (hτyc : ∀ a b : Ay, τy (a * b) = τy (b * a))
    (hpair : ∀ (s : Ax) (a : Ay), τy (E s * a) = τx (s * Estar a))
    (hren : E (σx * σx) = ((w : ℝ) : ℂ) • (σy * σy))
    (hσy1 : σy * σyi = 1) (hσy2 : σyi * σy = 1)
    (hw0 : 0 < w) (hw1 : w ≤ 1) (t : Ay) (r : ℝ) (hr : 0 ≤ r)
    (ht : τy t = (r : ℂ)) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ r ∧
      τx (petzReverse σx σyi Estar t) = (s : ℂ) := by
  refine ⟨w * r, mul_nonneg hw0.le hr, ?_, ?_⟩
  · nlinarith
  · rw [petzReverse_trace τx τy σx σy σyi E Estar w hτxc hτyc hpair
      hren hσy1 hσy2 t, ht]
    push_cast
    ring

omit [PartialOrder Ax] [PartialOrder Ay] [StarModule ℂ Ax] [StarModule ℂ Ay] [StarOrderedRing Ax]
  [StarOrderedRing Ay] [StarRing Ax] [StarRing Ay] in
/-- **`prop:branchwise-petz-reference-renewal` (adjoint pairing)**:
`Γ_{ρ_y}^{-1} ∘ ℰ ∘ Γ_{ρ_x}` is the trace adjoint of the reversal,
`Tr_x(ℰ^←(τ) a) = Tr_y(τ (ℰ^←)^*(a))`. -/
theorem petzReverse_pairing
    (hτxc : ∀ a b : Ax, τx (a * b) = τx (b * a))
    (hτyc : ∀ a b : Ay, τy (a * b) = τy (b * a))
    (hpair : ∀ (s : Ax) (a : Ay), τy (E s * a) = τx (s * Estar a))
    (t : Ay) (a : Ax) :
    τx (petzReverse σx σyi Estar t * a)
      = τy (t * petzReverseHeis σx σyi E a) := by
  rw [petzReverse_apply, petzReverseHeis_apply]
  have h1 : τx ((σx * Estar (σyi * t * σyi) * σx) * a)
      = τx ((σx * a * σx) * Estar (σyi * t * σyi)) := by
    rw [show (σx * Estar (σyi * t * σyi) * σx) * a
        = (σx * Estar (σyi * t * σyi)) * (σx * a) from by noncomm_ring]
    rw [hτxc (σx * Estar (σyi * t * σyi)) (σx * a)]
    congr 1
    noncomm_ring
  rw [h1, ← hpair]
  rw [hτyc (E (σx * a * σx)) (σyi * t * σyi)]
  rw [show (σyi * t * σyi) * E (σx * a * σx)
      = σyi * (t * σyi * E (σx * a * σx)) from by noncomm_ring]
  rw [hτyc σyi (t * σyi * E (σx * a * σx))]
  congr 1
  noncomm_ring

omit [PartialOrder Ax] [PartialOrder Ay] [StarModule ℂ Ax] [StarModule ℂ Ay] [StarOrderedRing Ax]
  [StarOrderedRing Ay] [StarRing Ax] [StarRing Ay] in
/-- **`prop:branchwise-petz-reference-renewal` (adjoint unit
value)**: `(ℰ^←)^*(1_x) = w 1_y`. -/
theorem petzReverseHeis_unit
    (hren : E (σx * σx) = ((w : ℝ) : ℂ) • (σy * σy))
    (hσy1 : σy * σyi = 1) (hσy2 : σyi * σy = 1) :
    petzReverseHeis σx σyi E 1 = ((w : ℝ) : ℂ) • 1 := by
  rw [petzReverseHeis_apply]
  rw [show σx * (1 : Ax) * σx = σx * σx from by rw [mul_one], hren]
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  calc σyi * (σy * σy) * σyi = (σyi * σy) * (σy * σyi) := by
        noncomm_ring
    _ = 1 := by rw [hσy1, hσy2, one_mul]

omit [PartialOrder Ax] [PartialOrder Ay] [StarModule ℂ Ax] [StarModule ℂ Ay] [StarOrderedRing Ax]
  [StarOrderedRing Ay] [StarRing Ax] [StarRing Ay] in
/-- **`prop:branchwise-petz-reference-renewal` (reverse renewal
iff)**: `ℰ^←(ρ_y) = w ρ_x` if and only if `ℰ^*(1_y) = w 1_x`. -/
theorem petzReverse_renewal_iff
    (hσx1 : σx * σxi = 1) (hσx2 : σxi * σx = 1)
    (hσy1 : σy * σyi = 1) (hσy2 : σyi * σy = 1) :
    petzReverse σx σyi Estar (σy * σy) = ((w : ℝ) : ℂ) • (σx * σx)
      ↔ Estar 1 = ((w : ℝ) : ℂ) • 1 := by
  have hu : σyi * (σy * σy) * σyi = 1 := by
    calc σyi * (σy * σy) * σyi = (σyi * σy) * (σy * σyi) := by
          noncomm_ring
      _ = 1 := by rw [hσy1, hσy2, one_mul]
  constructor
  · intro h
    rw [petzReverse_apply, hu] at h
    calc Estar 1 = (σxi * σx) * Estar 1 * (σx * σxi) := by
          rw [hσx2, hσx1, one_mul, mul_one]
      _ = σxi * (σx * Estar 1 * σx) * σxi := by noncomm_ring
      _ = σxi * (((w : ℝ) : ℂ) • (σx * σx)) * σxi := by rw [h]
      _ = ((w : ℝ) : ℂ) • (σxi * (σx * σx) * σxi) := by
          rw [mul_smul_comm, smul_mul_assoc]
      _ = ((w : ℝ) : ℂ) • (1 : Ax) := by
          congr 1
          calc σxi * (σx * σx) * σxi = (σxi * σx) * (σx * σxi) := by
                noncomm_ring
            _ = 1 := by rw [hσx2, hσx1, one_mul]
  · intro h
    rw [petzReverse_apply, hu, h, mul_smul_comm, smul_mul_assoc,
      mul_one]

omit [PartialOrder Ax] [PartialOrder Ay] [StarModule ℂ Ax] [StarModule ℂ Ay] [StarOrderedRing Ax]
  [StarOrderedRing Ay] [StarRing Ax] [StarRing Ay] in
/-- **`prop:branchwise-petz-reference-renewal` (involutivity)**:
reversing the reversed branch (with its established adjoint
`petzReverseHeis`, the roles of `x` and `y` exchanged) recovers the
original branch: `(ℰ^←)^← = ℰ`. -/
theorem petzReverse_involutive
    (hσx1 : σx * σxi = 1) (hσx2 : σxi * σx = 1)
    (hσy1 : σy * σyi = 1) (hσy2 : σyi * σy = 1) :
    petzReverse σy σxi (petzReverseHeis σx σyi E) = E := by
  apply LinearMap.ext
  intro a
  change σy * (σyi * E (σx * (σxi * a * σxi) * σx) * σyi) * σy = E a
  have h1 : σx * (σxi * a * σxi) * σx = a := by
    calc σx * (σxi * a * σxi) * σx = (σx * σxi) * a * (σxi * σx) := by
          noncomm_ring
      _ = a := by rw [hσx1, hσx2, one_mul, mul_one]
  rw [h1]
  calc σy * (σyi * E a * σyi) * σy = (σy * σyi) * E a * (σyi * σy) := by
        noncomm_ring
    _ = E a := by rw [hσy1, hσy2, one_mul, mul_one]

omit [PartialOrder Ax] [PartialOrder Ay] [PartialOrder Az] [StarModule ℂ Ax] [StarModule ℂ Ay]
  [StarModule ℂ Az] [StarOrderedRing Ax] [StarOrderedRing Ay] [StarOrderedRing Az] [StarRing Ax]
  [StarRing Ay] [StarRing Az] in
/-- **`prop:branchwise-petz-reference-renewal` (contravariant
composition)**: for composable branches `ℰ : x → y` and `𝓕 : y → z`
(composite adjoint `ℰ^* ∘ 𝓕^*`), the reversal composes
contravariantly: `(𝓕 ∘ ℰ)^← = ℰ^← ∘ 𝓕^←`. -/
theorem petzReverse_comp (Fstar : Az →ₗ[ℂ] Ay) (σzi : Az)
    (hσy1 : σy * σyi = 1) (hσy2 : σyi * σy = 1) :
    petzReverse σx σzi (Estar ∘ₗ Fstar)
      = (petzReverse σx σyi Estar) ∘ₗ
          (petzReverse σy σzi Fstar) := by
  apply LinearMap.ext
  intro t
  change σx * Estar (Fstar (σzi * t * σzi)) * σx
    = σx * Estar (σyi * (σy * Fstar (σzi * t * σzi) * σy) * σyi) * σx
  have h : σyi * (σy * Fstar (σzi * t * σzi) * σy) * σyi
      = Fstar (σzi * t * σzi) := by
    calc σyi * (σy * Fstar (σzi * t * σzi) * σy) * σyi
        = (σyi * σy) * Fstar (σzi * t * σzi) * (σy * σyi) := by
          noncomm_ring
      _ = Fstar (σzi * t * σzi) := by
          rw [hσy2, hσy1, one_mul, mul_one]
  rw [h]

end Branch

end NCG.Upstream
