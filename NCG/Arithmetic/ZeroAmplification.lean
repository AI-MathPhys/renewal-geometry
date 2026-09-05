/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Arithmetic.LaplacePole

/-!
# Off-critical zero amplification and packetwise GRH
  (`thm:v002-zero-amplification`, `thm:v002-packet-grh`,
   arithmetic manuscript)

In the logarithmic variable `r = log X`, the packet
`𝓔(X) = f(r)` carries an off-critical zero as an exponential term
`c_k e^{λ_k r}` with `α = Re λ_k > 0` and `c_k ≠ 0`.

* `zero_amplification`: if the packet were `O(e^{(α-ε)r})`, its
  weighted energy at `σ = α - ε/2` would be finite (dominated by
  `C² e^{-εr}`), and the Laplace-pole obstruction
  (`laplace_pole_obstruction`) would force `α ≤ α - ε/2` —
  contradiction.  Hence no bound `|𝓔(X)| ≤ C·X^{α-ε}` can hold,
  the boxed `limsup |𝓔|/X^{α-ε} = ∞` in its boundedness
  rendering;
* `packet_subpower_grh`: the subpower property `SP(χ)` (every
  positive exponent `η` bounds the packet) is therefore
  incompatible with any off-critical exponent `α > 0` — the
  packetwise conditional GRH, at the tested exponent.

Rendering disclosed: the meromorphic-continuation route of the
manuscript is replaced by the equivalent elementary Laplace-pole
test of the `lem:laplace-pole` record, whose displayed hypotheses
(isolated, rightmost tested exponent; locally bounded remainder
transform) carry the manuscript's grouped-zero expansion; the
`limsup = ∞` box is rendered as the failure of every global bound
`C·X^{α-ε}`; the reflection to the left half-strip and the
imprimitive/completed-packet extensions are the manuscript's
prose steps.
-/

open MeasureTheory Set Filter Topology

namespace NCG

/-- `thm:v002-zero-amplification`, boxed unboundedness: an
off-critical exponent `α = Re λ_k > 0` with nonzero grouped
coefficient forbids every packet bound `O(e^{(α-ε)r})`. -/
theorem zero_amplification
    (f R : ℝ → ℂ) (c lam : ℕ → ℂ) (δ CR Cb ε : ℝ) (k : ℕ)
    (hδ : 0 < δ) (hck : c k ≠ 0)
    (hcs : Summable fun j => ‖c j‖)
    (hmax : ∀ j, (lam j).re ≤ (lam k).re)
    (hsep : ∀ j, j ≠ k → δ ≤ ‖lam k - lam j‖)
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hf : ∀ r : ℝ, 0 < r →
      f r = R r + ∑' j, c j * Complex.exp (lam j * r))
    (hR : ∀ ε' : ℝ, 0 < ε' → ε' ≤ 1 →
      IntegrableOn (fun r => R r
        * Complex.exp (-(lam k + (ε' : ℂ)) * r)) (Ioi 0)
      ∧ ‖∫ r in Ioi (0 : ℝ), R r
          * Complex.exp (-(lam k + (ε' : ℂ)) * r)‖ ≤ CR)
    (hε : 0 < ε)
    (hbound : ∀ r : ℝ, 0 < r →
      ‖f r‖ ≤ Cb * Real.exp (((lam k).re - ε) * r)) :
    False := by
  set σ : ℝ := (lam k).re - ε / 2 with hσ_def
  have hCb0 : 0 ≤ Cb := by
    have h1 := hbound 1 one_pos
    have h2 := norm_nonneg (f 1)
    nlinarith [Real.exp_pos (((lam k).re - ε) * 1)]
  have hE : IntegrableOn
      (fun r => Real.exp (-(2 * σ) * r) * ‖f r‖ ^ 2)
      (Ioi 0) := by
    refine Integrable.mono'
      (g := fun r => Cb ^ 2 * Real.exp (-ε * r)) ?_ ?_ ?_
    · exact (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _
    · refine (Continuous.aestronglyMeasurable
        (by fun_prop)).mul ?_
      exact (hfm.norm.mul hfm.norm).congr
        (Eventually.of_forall fun r => (pow_two ‖f r‖).symm)
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr
        (ae_of_all _ ?_)
      intro r hr
      have h1 := hbound r hr
      have h5 : ‖Real.exp (-(2 * σ) * r) * ‖f r‖ ^ 2‖
          = Real.exp (-(2 * σ) * r) * ‖f r‖ ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [h5]
      have h2 : Real.exp (-(2 * σ) * r) * ‖f r‖ ^ 2
          ≤ Real.exp (-(2 * σ) * r)
            * (Cb * Real.exp (((lam k).re - ε) * r)) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        have h3 : (0 : ℝ) ≤ ‖f r‖ := norm_nonneg _
        nlinarith
      have h4 : Real.exp (-(2 * σ) * r)
          * (Cb * Real.exp (((lam k).re - ε) * r)) ^ 2
          = Cb ^ 2 * Real.exp (-ε * r) := by
        rw [show (Cb * Real.exp (((lam k).re - ε) * r)) ^ 2
            = Cb ^ 2 * (Real.exp (((lam k).re - ε) * r)
              * Real.exp (((lam k).re - ε) * r)) by ring,
          ← Real.exp_add, mul_left_comm, ← Real.exp_add,
          hσ_def]
        congr 2
        ring
      rw [h4] at h2
      exact h2
  have h1 := laplace_pole_obstruction f R c lam σ δ CR k hδ
    hck hcs hmax hsep hfm hE hf hR
  rw [hσ_def] at h1
  linarith

/-- `thm:v002-packet-grh`, tested exponent: the subpower property
is incompatible with any off-critical displacement `α > 0`. -/
theorem packet_subpower_grh
    (f R : ℝ → ℂ) (c lam : ℕ → ℂ) (δ CR : ℝ) (k : ℕ)
    (hδ : 0 < δ) (hck : c k ≠ 0)
    (hcs : Summable fun j => ‖c j‖)
    (hmax : ∀ j, (lam j).re ≤ (lam k).re)
    (hsep : ∀ j, j ≠ k → δ ≤ ‖lam k - lam j‖)
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hf : ∀ r : ℝ, 0 < r →
      f r = R r + ∑' j, c j * Complex.exp (lam j * r))
    (hR : ∀ ε' : ℝ, 0 < ε' → ε' ≤ 1 →
      IntegrableOn (fun r => R r
        * Complex.exp (-(lam k + (ε' : ℂ)) * r)) (Ioi 0)
      ∧ ‖∫ r in Ioi (0 : ℝ), R r
          * Complex.exp (-(lam k + (ε' : ℂ)) * r)‖ ≤ CR)
    (hα : 0 < (lam k).re)
    (hSP : ∀ η : ℝ, 0 < η → ∃ Cb : ℝ, ∀ r : ℝ, 0 < r →
      ‖f r‖ ≤ Cb * Real.exp (η * r)) :
    False := by
  obtain ⟨Cb, hb⟩ := hSP ((lam k).re / 2) (by linarith)
  refine zero_amplification f R c lam δ CR Cb ((lam k).re / 2)
    k hδ hck hcs hmax hsep hfm hf hR (by linarith) ?_
  intro r hr
  have h1 := hb r hr
  rw [show (lam k).re - (lam k).re / 2 = (lam k).re / 2 by ring]
  exact h1

end NCG
