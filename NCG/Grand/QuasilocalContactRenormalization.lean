import Mathlib
import NCG.Grand.OrdinaryNormDoesNotTransportLocality

/-!
# Quasilocal contact renormalization

A finite local counterterm bank defines a bounded finite-rank subtraction on
the weighted Banach carrier.  A Cauchy family after that subtraction therefore
has a unique weighted limit, and every physical collar estimate enjoyed by the
carrier passes immediately to the renormalized contact.
-/

open Filter

noncomputable section

namespace NCG
namespace QuasilocalContactRenormalization

universe u w

variable {B : Type u} [NormedAddCommGroup B] [NormedSpace ℂ B]
  [CompleteSpace B]
variable {Region : Type w}

/-- The finite local counterterm synthesis projector. -/
def countertermProjection {m : ℕ}
    (L : Fin m → B) (phi : Fin m → B →L[ℂ] ℂ) (T : B) : B :=
  ∑ j, (phi j T) • L j

/-- The weighted conditioning constant of the calibrated counterterm bank. -/
def countertermConditioning {m : ℕ}
    (L : Fin m → B) (phi : Fin m → B →L[ℂ] ℂ) : ℝ :=
  ∑ j, ‖L j‖ * ‖phi j‖

/-- The local counterterm projector has exactly the finite-bank norm bound
stated in the manuscript. -/
theorem norm_countertermProjection_le {m : ℕ}
    (L : Fin m → B) (phi : Fin m → B →L[ℂ] ℂ) (T : B) :
    ‖countertermProjection L phi T‖
      ≤ countertermConditioning L phi * ‖T‖ := by
  calc
    ‖countertermProjection L phi T‖
        ≤ ∑ j, ‖(phi j T) • L j‖ := norm_sum_le _ _
    _ ≤ ∑ j, (‖L j‖ * ‖phi j‖) * ‖T‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_smul]
      calc
        ‖phi j T‖ * ‖L j‖
            ≤ (‖phi j‖ * ‖T‖) * ‖L j‖ := by
              gcongr
              exact (phi j).le_opNorm T
        _ = (‖L j‖ * ‖phi j‖) * ‖T‖ := by ring
    _ = countertermConditioning L phi * ‖T‖ := by
      simp [countertermConditioning, Finset.sum_mul]

/-- The complementary subtraction is bounded by one plus the bank
conditioning constant. -/
theorem norm_countertermComplement_le {m : ℕ}
    (L : Fin m → B) (phi : Fin m → B →L[ℂ] ℂ) (T : B) :
    ‖T - countertermProjection L phi T‖
      ≤ (1 + countertermConditioning L phi) * ‖T‖ := by
  calc
    ‖T - countertermProjection L phi T‖
        ≤ ‖T‖ + ‖countertermProjection L phi T‖ := norm_sub_le _ _
    _ ≤ ‖T‖ + countertermConditioning L phi * ‖T‖ := by
      gcongr
      exact norm_countertermProjection_le L phi T
    _ = (1 + countertermConditioning L phi) * ‖T‖ := by ring

/-- Weighted Cauchy convergence after local subtraction produces one unique
renormalized contact in the complete weighted carrier. -/
theorem renormalizedContact_exists_unique {m : ℕ}
    (L : Fin m → B) (phi : Fin m → B →L[ℂ] ℂ)
    (contact : ℕ → B)
    (hCauchy : CauchySeq
      (fun n => contact n - countertermProjection L phi (contact n))) :
    ∃! renormalized : B,
      Tendsto
        (fun n => contact n - countertermProjection L phi (contact n))
        atTop (nhds renormalized) := by
  obtain ⟨renormalized, hren⟩ := cauchySeq_tendsto_of_complete hCauchy
  refine ⟨renormalized, hren, ?_⟩
  intro other hother
  exact tendsto_nhds_unique hother hren

/-- The limiting renormalized contact obeys every weighted physical collar
estimate of the Banach carrier. -/
theorem renormalizedContact_collar_le
    (compress : Region → Region → B →L[ℂ] B)
    (distance : Region → Region → ℝ)
    (alpha : ℝ)
    (hcompress : ∀ X Y T,
      ‖compress X Y T‖
        ≤ Real.exp (-alpha * distance X Y) * ‖T‖)
    (renormalized : B) (X Y : Region) :
    ‖compress X Y renormalized‖
      ≤ Real.exp (-alpha * distance X Y) * ‖renormalized‖ :=
  hcompress X Y renormalized

/-- Weighted Cauchy contact renormalization, including the finite-bank bound,
existence and uniqueness of the limit, and its quasilocal collar estimate. -/
theorem quasilocal_contact_renormalization {m : ℕ}
    (L : Fin m → B) (phi : Fin m → B →L[ℂ] ℂ)
    (contact : ℕ → B)
    (hCauchy : CauchySeq
      (fun n => contact n - countertermProjection L phi (contact n)))
    (compress : Region → Region → B →L[ℂ] B)
    (distance : Region → Region → ℝ) (alpha : ℝ)
    (hcompress : ∀ X Y T,
      ‖compress X Y T‖
        ≤ Real.exp (-alpha * distance X Y) * ‖T‖) :
    (∀ T, ‖countertermProjection L phi T‖
      ≤ countertermConditioning L phi * ‖T‖) ∧
    ∃! renormalized : B,
      Tendsto
        (fun n => contact n - countertermProjection L phi (contact n))
        atTop (nhds renormalized) ∧
      ∀ X Y, ‖compress X Y renormalized‖
        ≤ Real.exp (-alpha * distance X Y) * ‖renormalized‖ := by
  refine ⟨norm_countertermProjection_le L phi, ?_⟩
  obtain ⟨R, hR, hRunique⟩ :=
    renormalizedContact_exists_unique L phi contact hCauchy
  refine ⟨R, ⟨hR, fun X Y =>
    renormalizedContact_collar_le compress distance alpha hcompress R X Y⟩, ?_⟩
  intro S hS
  exact hRunique S hS.1

end QuasilocalContactRenormalization
end NCG
