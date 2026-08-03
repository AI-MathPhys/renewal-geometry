/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Arithmetic.QutritCompletion
import NCG.Arithmetic.SMDescent

/-!
# Conditional gauge-descent theorem
  (`thm:sm-chain`, arithmetic manuscript)

`sm_gauge_descent`: the assembly — the entry data of the
constituent proved records return, in one conjunction:

* (S1) the colour carrier: the nondegenerate qutrit revision
  datum generates the full `M₃(ℂ)` (`thm:qutrit`);
* (S2)–(S3) the hypercharge descent of one generation with the
  `ℤ₆` kernel congruence `6 ∣ 2t + 3d + q`
  (`thm:hypercharge`);
* anomaly freedom: the five anomaly sums vanish and the doublet
  count is even (`thm:anomaly`);
* (S5) the coupling matching: one primitive common current trace
  forces `g_Y² = (3/5)g²` and `sin²θ_W = 3/8` (`thm:coupling`).

Rendering disclosed: the weak doublet factor, Pati–Salam typing,
right-breaking source with stabilizer `Y = T_R³ + (B-L)/2`, and
the branch-blind BRST/Goldstone quotient (S2)–(S4) are the
manuscript's structural entry assumptions — the quotient leaves
the unbroken Lie algebra unchanged (prose); their numeric
descendants (hypercharges, kernel, anomalies, matching) are what
is proved.
-/

namespace NCG

/-- `thm:sm-chain`: the gauge-descent assembly. -/
theorem sm_gauge_descent (ω : ℂ) (hω3 : ω ^ 3 = 1)
    (hsum : 1 + ω + ω ^ 2 = 0) (g gY : ℝ) (hg : 0 < g)
    (hgY : 0 < gY)
    (hrel : 1 / gY ^ 2 = 1 / g ^ 2 + 2 / (3 * g ^ 2)) :
    -- (S1) colour carrier generates M₃(ℂ)
    Algebra.adjoin ℂ ({qutritU ω, qutritV} :
        Set (Matrix (Fin 3) (Fin 3) ℂ)) = ⊤
    -- (S2)-(S3) Z₆ kernel congruence of the one-generation table
    ∧ (∀ r ∈ [((1 : ℤ), (1 : ℤ), (1 : ℤ)),
        (0, 1, -3), (-1, 0, -4), (-1, 0, 2),
        (0, 0, 6), (0, 0, 0)],
        (6 : ℤ) ∣ 2 * r.1 + 3 * r.2.1 + r.2.2)
    -- anomaly freedom (five sums + Witten parity)
    ∧ (((2 : ℚ) * 1 + 1 * (-1) + 1 * (-1) = 0)
        ∧ ((2 : ℚ) * (1/2) * (1/6) + (1/2) * (-2/3)
            + (1/2) * (1/3) = 0)
        ∧ ((3 : ℚ) * (1/2) * (1/6) + (1/2) * (-1/2) = 0)
        ∧ ((6 : ℚ) * (1/6)^3 + 3 * (-2/3)^3 + 3 * (1/3)^3
            + 2 * (-1/2)^3 + 1^3 = 0)
        ∧ ((6 : ℚ) * (1/6) + 3 * (-2/3) + 3 * (1/3)
            + 2 * (-1/2) + 1 = 0)
        ∧ (3 + 1) % 2 = 0)
    -- (S5) coupling matching and weak angle
    ∧ (gY ^ 2 = 3 / 5 * g ^ 2
        ∧ gY ^ 2 / (g ^ 2 + gY ^ 2) = 3 / 8) :=
  ⟨qutrit_algebra_top ω hω3 hsum,
    hypercharge_z6_kernel,
    ps_anomaly_cancellation,
    coupling_matching g gY hg hgY hrel⟩

end NCG
