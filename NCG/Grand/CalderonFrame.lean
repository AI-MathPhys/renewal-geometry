/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SqrtPolar

/-!
# Universal Calderón frame identity
  (`thm:universal-Calderon-frame`, Gran-Tensor manuscript)

* `universal_calderon_frame`:
  (1) the operator Calderón reproducing identity as an exact
      matrix FTC: `∫₀ᴬ L·e^{−aL} da = I − e^{−AL}`;
  (2) the per-scale Gram of the analyzing family
      `(√L·F·Q)ᴴ(√L·F·Q) = Q·(F·L·F)·Q` for hermitian `F`
      (the half-kernel `e^{−aL/2}`) and hermitian `Q`;
  (3) the compressed boxed identity: for a reducing projection
      commuting with the generator,
      `Q·(I − e^{−AL})·Q = Q − e^{−AL}·Q`.

Rendering disclosed: the two-sided frame bounds
`(1−e^{−Am})Q ⪯ 𝒞*𝒞 ⪯ Q` and the `A = ∞` isometry are the
spectral reading of the proved identity on the reducing
subspace where `L ⪰ mQ`; the identification of the continuum
family `(𝒞x)(a)` with the integrand is the manuscript's
direct-integral bookkeeping.
-/

open Matrix NormedSpace intervalIntegral
open scoped ComplexOrder MatrixOrder Norms.Operator

-- `CFC.sqrt` mentions the matrix CFC instance (which needs
-- `DecidableEq`) in every statement; the linter cannot see it.
set_option linter.unusedDecidableInType false

namespace NCG

/-- `thm:universal-Calderon-frame`. -/
theorem universal_calderon_frame {n : Type*} [Fintype n]
    [DecidableEq n] (L Q : Matrix n n ℂ) (hL : L.PosSemidef)
    (hQH : Qᴴ = Q) (hQ2 : Q * Q = Q)
    (hcomm : L * Q = Q * L) (A : ℝ) :
    -- (1) the exact operator FTC
    ((∫ a in (0:ℝ)..A, L * exp (a • (-L)))
      = 1 - exp (A • (-L)))
    -- (2) the per-scale analyzing Gram
    ∧ (∀ F : Matrix n n ℂ, Fᴴ = F →
        (CFC.sqrt L * F * Q)ᴴ * (CFC.sqrt L * F * Q)
          = Q * (F * L * F) * Q)
    -- (3) the compressed boxed identity
    ∧ Q * ((1 : Matrix n n ℂ) - exp (A • (-L))) * Q
      = Q - exp (A • (-L)) * Q := by
  refine ⟨?_, ?_, ?_⟩
  · have hderiv : ∀ a : ℝ,
        HasDerivAt (fun t : ℝ => -exp (t • (-L)))
          (L * exp (a • (-L))) a := by
      intro a
      have h : HasDerivAt (fun t : ℝ => -exp (t • (-L)))
          (-(exp (a • (-L)) * -L)) a :=
        (hasDerivAt_exp_smul_const (-L) a).neg
      have hcm : Commute L (exp (a • (-L))) :=
        (((Commute.refl L).neg_right).smul_right a).exp_right
      have heq : -(exp (a • (-L)) * -L)
          = L * exp (a • (-L)) := by
        rw [Matrix.mul_neg, neg_neg]
        exact hcm.eq.symm
      rwa [heq] at h
    have hcont : Continuous
        (fun a : ℝ => L * exp (a • (-L))) := by
      have hexp : Continuous
          (fun a : ℝ => exp (a • (-L)) : ℝ → Matrix n n ℂ) :=
        exp_continuous.comp (continuous_id.smul continuous_const)
      exact continuous_const.mul hexp
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => -exp (t • (-L)))
      (fun a _ => hderiv a)
      (hcont.intervalIntegrable 0 A)
    rw [hint]
    rw [zero_smul, exp_zero]
    abel
  · intro F hF
    have hsH : (CFC.sqrt L)ᴴ = CFC.sqrt L := sqrt_isHermitian L
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hQH, hF, hsH]
    rw [show Q * (F * CFC.sqrt L)
          * (CFC.sqrt L * F * Q)
        = Q * (F * (CFC.sqrt L * CFC.sqrt L) * F) * Q from by
      simp only [Matrix.mul_assoc]]
    rw [sqrt_mul_self_eq L hL]
  · have hexpQ : exp (A • (-L)) * Q = Q * exp (A • (-L)) := by
      have hc : Commute (A • (-L)) Q := by
        change A • (-L) * Q = Q * (A • (-L))
        rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.neg_mul,
          Matrix.mul_neg, hcomm]
      exact hc.exp_left.eq
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hQ2]
    congr 1
    rw [show Q * exp (A • (-L)) * Q
        = exp (A • (-L)) * (Q * Q) from by
      rw [← hexpQ]
      simp only [Matrix.mul_assoc]]
    rw [hQ2]

end NCG
