/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The spectral Pati–Salam one-loop no-go
  (`thm:spectral-ps-nogo-consolidated`, SM_emergence)

At the fixed absolute boundary, neither the composite nor the
general minimal spectral Pati–Salam scalar sector can reproduce the
low-energy comparison couplings at one loop:

* `composite_ps_no_go` — the composite branch has
  `d₃ = b₄ - b₃^SM ≤ -2`, while the integrated target is
  `T₃ = 71.3331971483… > 0`; a physical interval requires
  `T₃ = t·d₃` with `t > 0` — contradiction;
* `general_ps_Q_nonneg` — the exposure-fraction linear program: the
  invariant `Q = 32d₂ - 31d₃` of the gauge–fermion background plus
  light bidoublet is `119`, the optional thresholds contribute
  `Q(2,2,15) = -16/3`, `Q(3,1,10) = -93`, `Q(1,3,10) = +361/3`, and
  each of the two sextets `-31/3`; over all exposure fractions in
  `[0,1]` the minimum is exactly `0`, so `Q(d) ≥ 0`;
* `general_ps_no_go` — the fixed-boundary integrated target has
  `Q(T) = 32T₂ - 31T₃ = -152.9628019448… < 0`, incompatible with
  `Q(T) = t·Q(d) ≥ 0`.
-/

namespace NCG

/-- Composite branch: `d₃ ≤ -2` cannot integrate to the positive
target `T₃` over a physical interval `t > 0`. -/
theorem composite_ps_no_go {t d3 T3 : ℝ} (ht : 0 < t)
    (hd : d3 ≤ -2) (hT : T3 = t * d3)
    (htarget : (71.3331971483 : ℝ) ≤ T3) : False := by
  nlinarith

/-- General branch (exposure LP): the invariant `Q` is nonnegative
for every choice of exposure fractions in `[0,1]` — the minimum
`119 - 16/3 - 93 - 2·31/3 = 0` is attained at full exposure of the
`(2,2,15)`, the `(3,1,10)`, and both sextets. -/
theorem general_ps_Q_nonneg {f1 f2 f3 g1 g2 : ℝ}
    (h1 : f1 ∈ Set.Icc (0 : ℝ) 1) (h2 : f2 ∈ Set.Icc (0 : ℝ) 1)
    (h3 : f3 ∈ Set.Icc (0 : ℝ) 1) (h4 : g1 ∈ Set.Icc (0 : ℝ) 1)
    (h5 : g2 ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ 119 - 16 / 3 * f1 - 93 * f2 + 361 / 3 * f3
      - 31 / 3 * (g1 + g2) := by
  obtain ⟨h1l, h1r⟩ := h1
  obtain ⟨h2l, h2r⟩ := h2
  obtain ⟨h3l, h3r⟩ := h3
  obtain ⟨h4l, h4r⟩ := h4
  obtain ⟨h5l, h5r⟩ := h5
  linarith

/-- General branch conclusion: the negative integrated target
`Q(T) < 0` cannot equal `t·Q(d)` with `t > 0` and `Q(d) ≥ 0`. -/
theorem general_ps_no_go {t Qd QT : ℝ} (ht : 0 < t) (hQd : 0 ≤ Qd)
    (hQT : QT = t * Qd)
    (hval : QT = (-152.9628019448 : ℝ)) : False := by
  nlinarith

end NCG
