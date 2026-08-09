/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.CrossHankel
import NCG.Arithmetic.SMDescent

/-!
# cross-Hankel assembly and anomaly packet
-/

open Matrix
open scoped ComplexOrder

namespace NCG

variable {u p q : Type*} [Fintype u] [Fintype p] [Fintype q]
  [DecidableEq u] [DecidableEq p] [DecidableEq q]

/-- `thm:SMST-cross-Hankel`, assembled at the manuscript objects:
history Gram, projected Schur identity and positivity, residual rank,
and the Moore--Penrose/minimum-norm chronology reconstruction. -/
theorem cross_hankel_chronology_alternative_exact
    (T : Matrix u u ℂ) (Sc : Matrix u p ℂ) (Sg : Matrix u q ℂ)
    (d : ℕ) (hT : Tᴴ = T)
    (hPD : ((krylovMat T Sc d)ᴴ * krylovMat T Sc d).PosDef)
    (hd : 0 < d) :
    (∀ (mq : Fin d × p) (nr : Fin d × q),
      ((krylovMat T Sc d)ᴴ * krylovMat T Sg d) mq nr
        = (Scᴴ * T ^ ((mq.1 : ℕ) + (nr.1 : ℕ)) * Sg) mq.2 nr.2)
    ∧ ((krylovMat T Sg d)ᴴ * krylovMat T Sg d
        - ((krylovMat T Sc d)ᴴ * krylovMat T Sg d)ᴴ
          * ((krylovMat T Sc d)ᴴ * krylovMat T Sc d)⁻¹
          * ((krylovMat T Sc d)ᴴ * krylovMat T Sg d)
      = ((1 - clockPacketProj T Sc d) * krylovMat T Sg d)ᴴ
          * ((1 - clockPacketProj T Sc d) * krylovMat T Sg d))
    ∧ ((krylovMat T Sg d)ᴴ * krylovMat T Sg d
        - ((krylovMat T Sc d)ᴴ * krylovMat T Sg d)ᴴ
          * ((krylovMat T Sc d)ᴴ * krylovMat T Sc d)⁻¹
          * ((krylovMat T Sc d)ᴴ * krylovMat T Sg d)).PosSemidef
    ∧ ((krylovMat T Sg d)ᴴ * krylovMat T Sg d
        - ((krylovMat T Sc d)ᴴ * krylovMat T Sg d)ᴴ
          * ((krylovMat T Sc d)ᴴ * krylovMat T Sc d)⁻¹
          * ((krylovMat T Sc d)ᴴ * krylovMat T Sg d)).rank
      = ((1 - clockPacketProj T Sc d) * krylovMat T Sg d).rank
    ∧ (((krylovMat T Sg d)ᴴ * krylovMat T Sg d
        - ((krylovMat T Sc d)ᴴ * krylovMat T Sg d)ᴴ
          * ((krylovMat T Sc d)ᴴ * krylovMat T Sc d)⁻¹
          * ((krylovMat T Sc d)ᴴ * krylovMat T Sg d) = 0) →
      Sg = ∑ n : Fin d, T ^ (n : ℕ) * Sc
        * Matrix.of fun (a : p) (y : q) =>
          (((krylovMat T Sc d)ᴴ * krylovMat T Sc d)⁻¹
            * ((krylovMat T Sc d)ᴴ * krylovMat T Sg d))
          (n, a) (⟨0, hd⟩, y)) := by
  refine ⟨?_, cross_hankel_schur T Sc Sg d hPD,
    cross_hankel_psd T Sc Sg d hPD,
    cross_hankel_rank T Sc Sg d hPD, ?_⟩
  · intro mq nr
    exact cross_hankel_gram T hT Sc Sg mq nr
  · intro hvan
    exact cross_hankel_reconstruction T Sc Sg d hPD hd hvan

/-- `thm:SM-anomaly` in the manuscript's one-generation charge
normalization, including the mod-two global anomaly check. -/
theorem sm_anomaly_generated_packet_exact :
    ((2 : ℚ) * 1 + 1 * (-1) + 1 * (-1) = 0)
    ∧ ((2 : ℚ) * (1/2) * (1/6) + (1/2) * (-2/3)
        + (1/2) * (1/3) = 0)
    ∧ ((3 : ℚ) * (1/2) * (1/6) + (1/2) * (-1/2) = 0)
    ∧ ((6 : ℚ) * (1/6)^3 + 3 * (-2/3)^3 + 3 * (1/3)^3
        + 2 * (-1/2)^3 + 1^3 = 0)
    ∧ ((6 : ℚ) * (1/6) + 3 * (-2/3) + 3 * (1/3)
        + 2 * (-1/2) + 1 = 0)
    ∧ (3 + 1) % 2 = 0 :=
  ps_anomaly_cancellation

end NCG
