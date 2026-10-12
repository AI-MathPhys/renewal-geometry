/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The abstract slab model of `prop:coupled-bootstrap` and its stability conclusion

Einstein–Standard-Model action-closure manuscript, `prop:coupled-bootstrap`
(`eq:bootstrap-state`, `eq:bootstrap-curvature`): the abstract analytic data on a slab
`Q = [0,T] × 𝕋³` used to state the coupled stability estimate for the Einstein–Yang–Mills–Higgs–Dirac
system.

* `SlabModel Z X O` — field tuples `Z`, their initial state in a normed space `X` (`init`), a
  comparison observable in a pseudometric space `O` (`obs`), the residual norms `resB`, `resD`, the
  harmonic-defect norm `harm`, admissibility and exactness predicates (exact solutions have
  vanishing residuals and harmonic defect).
* `SlabModel.mismatch` — the mismatch `d` (initial distance plus residual and defect norms).
* `CoupledBootstrapConclusion` — the stability conclusion `d ≤ d_* ⟹ dist(obs) ≤ C_* d` on a
  reference class.

Split out of `MathPhys.Continuum.AposterioriPhysicalShadow` (which re-exports it); names are
unchanged.
-/

open Metric Filter Topology

namespace MathPhys.AposterioriShadow

noncomputable section

/-- **The analytic slab model** (`subsec:aposteriori-shadow`, `prop:coupled-bootstrap`): actual
field tuples `Z` on the slab, their initial actual-jet state in `𝒳_k` (`H^k` norm), the comparison
observable `(𝒰, Riem, T^SM)` in the pseudometric space `O`, the residual and harmonic-defect norms,
admissible approximate records and exact solutions. -/
structure SlabModel (Z X O : Type*) [NormedAddCommGroup X] [PseudoMetricSpace O] where
  /-- The initial actual-jet state `𝒰(z)(0) ∈ 𝒳_k`. -/
  init : Z → X
  /-- The comparison observable `(𝒰(z), Riem(g), T^SM(z))`; its distance is the left side of
  `eq:aposteriori-physical-shadow`. -/
  obs : Z → O
  /-- `‖𝓡_B(z)‖_{L²_tH^k_x}` (Einstein, Yang–Mills and Higgs rows). -/
  resB : Z → ℝ
  /-- `‖𝓡_D(z)‖_{L²_tH^{k+1}_x}` (Dirac and dual-Dirac rows). -/
  resD : Z → ℝ
  /-- `‖C(g)‖_{L²_tH^{k+1}_x} + ‖∂_tC(g)‖_{L²_tH^k_x}`, `C^μ = g^{αβ}Γ^μ_{αβ}`. -/
  harm : Z → ℝ
  /-- Smooth actual field tuple on the slab and foliated chart, exact temporal internal gauge. -/
  Admissible : Z → Prop
  /-- Exact physical Einstein–Standard-Model solution in the declared gauge class. -/
  IsExact : Z → Prop
  resB_nonneg : ∀ z, 0 ≤ resB z
  resD_nonneg : ∀ z, 0 ≤ resD z
  harm_nonneg : ∀ z, 0 ≤ harm z
  /-- An exact solution has vanishing physical rows. -/
  exact_resB : ∀ z, IsExact z → resB z = 0
  /-- An exact solution has vanishing Dirac rows. -/
  exact_resD : ∀ z, IsExact z → resD z = 0
  /-- An exact solution is in harmonic coordinates. -/
  exact_harm : ∀ z, IsExact z → harm z = 0

variable {Z X O : Type*} [NormedAddCommGroup X] [PseudoMetricSpace O]

/-- The mismatch `d` of `prop:coupled-bootstrap`:
`‖𝒰̂(0) - 𝒰_*(0)‖_{H^k} + ‖𝓡_B(ẑ)‖_{L²H^k} + ‖𝓡_D(ẑ)‖_{L²H^{k+1}} + (harmonic defect of ĝ)`;
the reference has vanishing residuals. -/
def SlabModel.mismatch (M : SlabModel Z X O) (zh zs : Z) : ℝ :=
  ‖M.init zh - M.init zs‖ + M.resB zh + M.resD zh + M.harm zh

/-- **The conclusion of `prop:coupled-bootstrap`** for the references in `Ref` with constants
`(d_*, C_*)`: for every reference `z_* ∈ Ref` and every admissible approximate record `ẑ`,
`d ≤ d_*` implies `‖𝒰̂ - 𝒰_*‖_{C_tH^k} + ‖Riem(ĝ) - Riem(g_*)‖_{L²H^{k-1}} +
‖T^SM(ẑ) - T^SM(z_*)‖_{L²H^k} ≤ C_* d` (`eq:bootstrap-state`, `eq:bootstrap-curvature`).
`prop:coupled-bootstrap` is open in the ledger; this predicate is used only as a hypothesis. -/
def CoupledBootstrapConclusion (M : SlabModel Z X O) (Ref : Set Z) (dstar Cstar : ℝ) : Prop :=
  ∀ zs ∈ Ref, ∀ zh, M.Admissible zh → M.mismatch zh zs ≤ dstar →
    dist (M.obs zh) (M.obs zs) ≤ Cstar * M.mismatch zh zs

end

end MathPhys.AposterioriShadow
