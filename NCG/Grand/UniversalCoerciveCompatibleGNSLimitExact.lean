/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.UniversalCoerciveContinuumExact
import NCG.Grand.CompatibleHilbertDirectLimitGap
import NCG.Grand.HeadTailContractionExact

/-!
# Universal coercivity on a compatible GNS direct limit

This file closes the direct-limit identification in
`thm:universal-coercive-continuum`.  Compatible stage transitions and fixed
projections are represented on an increasing dense GNS filtration.  The
transient norm of the limit is exactly the least upper bound of the stage
transient norms, so either finite-stage coercivity branch passes to the limit
with no loss and yields the advertised physical-time gap.
-/

open Filter

noncomputable section

namespace NCG.UniversalCoerciveGNS

open CompatibleHilbertDirectLimitGap

variable {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Exact compatible-GNS handoff of a uniform transient contraction. -/
theorem compatible_gns_coercive_handoff
    (S : ℕ → Submodule ℂ H) (hmono : Monotone S)
    (hdense : Dense ((⨆ n, S n : Submodule ℂ H) : Set H))
    (T E : (n : ℕ) → ContinuousLinearMap (RingHom.id ℂ) (S n) (S n))
    (Tlimit Elimit : H →L[ℂ] H)
    (hT : ∀ n (x : S n), ((T n x : S n) : H) = Tlimit x)
    (hE : ∀ n (x : S n), ((E n x : S n) : H) = Elimit x)
    (hEid : Elimit * Elimit = Elimit)
    (hTE : Tlimit * Elimit = Elimit) (hET : Elimit * Tlimit = Elimit)
    (q tau : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (htau : 0 < tau)
    (hstage : ∀ n, ‖transient (T n) (E n)‖ ≤ q) :
    IsLUB (Set.range fun n => ‖transient (T n) (E n)‖)
        ‖transient Tlimit Elimit‖ ∧
    ‖transient Tlimit Elimit‖ ≤ q ∧
    0 < tau⁻¹ * Real.log q⁻¹ ∧
    (∀ k : ℕ, ‖(transient Tlimit Elimit) ^ k‖ ≤
      Real.exp (-(tau⁻¹ * Real.log q⁻¹) * (k * tau))) ∧
    (∀ {n m : ℕ} (hnm : n ≤ m),
      (stageInclusion S hmono hnm).comp (T n) =
        (T m).comp (stageInclusion S hmono hnm) ∧
      (stageInclusion S hmono hnm).comp (E n) =
        (E m).comp (stageInclusion S hmono hnm)) := by
  have hfamily := uniform_gap_compatible_family S hmono hdense
    T E Tlimit Elimit hT hE hEid hTE hET
  have hlimit : ‖transient Tlimit Elimit‖ ≤ q :=
    hfamily.1.2 (fun rho hrho => by
      obtain ⟨n, rfl⟩ := hrho
      exact hstage n)
  have hgap : 0 < tau⁻¹ * Real.log q⁻¹ := by
    have hinv : 1 < q⁻¹ := one_lt_inv_iff₀.mpr ⟨hq0, hq1⟩
    exact mul_pos (inv_pos.mpr htau) (Real.log_pos hinv)
  refine ⟨hfamily.1, hlimit, hgap, ?_, hfamily.2.2.2⟩
  intro k
  exact UniversalCoercive.contraction_gap
    (transient Tlimit Elimit) q tau hq0 htau hlimit k

/-- The sharp positive head--tail branch uses exactly the manuscript's
`q* = (a+d+sqrt((a-d)^2+4b^2))/2`; its determinant condition proves `q*<1`,
after which the compatible GNS handoff is immediate. -/
theorem sharp_head_tail_compatible_gns_handoff
    (S : ℕ → Submodule ℂ H) (hmono : Monotone S)
    (hdense : Dense ((⨆ n, S n : Submodule ℂ H) : Set H))
    (T E : (n : ℕ) → ContinuousLinearMap (RingHom.id ℂ) (S n) (S n))
    (Tlimit Elimit : H →L[ℂ] H)
    (hT : ∀ n (x : S n), ((T n x : S n) : H) = Tlimit x)
    (hE : ∀ n (x : S n), ((E n x : S n) : H) = Elimit x)
    (hEid : Elimit * Elimit = Elimit)
    (hTE : Tlimit * Elimit = Elimit) (hET : Elimit * Tlimit = Elimit)
    (a b d tau : ℝ) (ha0 : 0 ≤ a) (hd0 : 0 ≤ d)
    (ha1 : a < 1) (hd1 : d < 1)
    (hdet : b ^ 2 < (1 - a) * (1 - d))
    (hq0 : 0 < HeadTail.qstar a b d) (htau : 0 < tau)
    (hstage : ∀ n, ‖transient (T n) (E n)‖ ≤
      HeadTail.qstar a b d) :
    ‖transient Tlimit Elimit‖ ≤ HeadTail.qstar a b d ∧
      0 < tau⁻¹ * Real.log (HeadTail.qstar a b d)⁻¹ := by
  have hq1 := HeadTail.headTail_lt_one ha1 hd1 hdet
  have h := compatible_gns_coercive_handoff S hmono hdense T E
    Tlimit Elimit hT hE hEid hTE hET (HeadTail.qstar a b d) tau
    hq0 hq1 htau hstage
  exact ⟨h.2.1, h.2.2.1⟩

end NCG.UniversalCoerciveGNS
