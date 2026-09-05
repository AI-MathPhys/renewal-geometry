/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Second and fourth cumulants of the worked reset stream
  (`prop:worked-channel-cumulants`, GR_emergence)

For a compound-Poisson reset stream of rate `r` with centred
Gaussian step law of covariance `s²I`, the tilted cumulant
generating function along a direction `a` is
`Λ(t) = r(e^{(c/2)t²} - 1)` with `c = s²|a|²`.  Its derivatives at
the origin are computed honestly:

* `cgf_deriv_one` … `cgf_deriv_four` — the four derivative
  identities;
* `second_cumulant` — `K⁽²⁾(a,a) = Λ''(0) = rc = rs²|a|²`, the
  polarized form of `K⁽²⁾_{ij} = rs²δ_{ij}` (Gaussian scale
  `D = rs²`);
* `fourth_cumulant` — `K⁽⁴⁾(a,a,a,a) = Λ⁗(0) = 3rc² = 3rs⁴|a|⁴`,
  the polarized form of the fully symmetric
  `K⁽⁴⁾_{ijkl} = rs⁴(δ_{ij}δ_{kl}+δ_{ik}δ_{jl}+δ_{il}δ_{jk})`
  (isotropic quartic scale `Q = rs⁴`).

Both symmetric tensors are recovered from their diagonal by
polarization, and the one-dimensionality of the fully symmetric
`O(d)`-invariant quartic sector is the declared invariant-theory
input.
-/

namespace NCG

/-- First derivative: `Λ' = r·c·t·e^{(c/2)t²}`. -/
theorem cgf_deriv_one (r c t : ℝ) :
    HasDerivAt (fun t => r * (Real.exp (c / 2 * t ^ 2) - 1))
      (r * (c * t * Real.exp (c / 2 * t ^ 2))) t := by
  have h := (hasDerivAt_pow 2 t).const_mul (c / 2)
  have he : c / 2 * (((2 : ℕ) : ℝ) * t ^ (2 - 1)) = c * t := by
    push_cast
    ring
  have hu : HasDerivAt (fun t : ℝ => c / 2 * t ^ 2) (c * t) t :=
    h.congr_deriv he
  have hexp := (Real.hasDerivAt_exp (c / 2 * t ^ 2)).comp t hu
  refine ((hexp.sub_const 1).const_mul r).congr_deriv ?_
  ring

/-- Second derivative: `Λ'' = r(c + c²t²)e^{(c/2)t²}`. -/
theorem cgf_deriv_two (r c t : ℝ) :
    HasDerivAt (fun t => r * (c * t * Real.exp (c / 2 * t ^ 2)))
      (r * ((c + c ^ 2 * t ^ 2) * Real.exp (c / 2 * t ^ 2))) t := by
  have h := (hasDerivAt_pow 2 t).const_mul (c / 2)
  have he : c / 2 * (((2 : ℕ) : ℝ) * t ^ (2 - 1)) = c * t := by
    push_cast
    ring
  have hu : HasDerivAt (fun t : ℝ => c / 2 * t ^ 2) (c * t) t :=
    h.congr_deriv he
  have hexp := (Real.hasDerivAt_exp (c / 2 * t ^ 2)).comp t hu
  have hpoly : HasDerivAt (fun t : ℝ => c * t) c t :=
    ((hasDerivAt_id t).const_mul c).congr_deriv (mul_one c)
  refine ((hpoly.mul hexp).const_mul r).congr_deriv ?_
  simp only [Function.comp_apply]
  ring

/-- Third derivative: `Λ''' = r(3c²t + c³t³)e^{(c/2)t²}`. -/
theorem cgf_deriv_three (r c t : ℝ) :
    HasDerivAt
      (fun t => r * ((c + c ^ 2 * t ^ 2)
        * Real.exp (c / 2 * t ^ 2)))
      (r * ((3 * c ^ 2 * t + c ^ 3 * t ^ 3)
        * Real.exp (c / 2 * t ^ 2))) t := by
  have h := (hasDerivAt_pow 2 t).const_mul (c / 2)
  have he : c / 2 * (((2 : ℕ) : ℝ) * t ^ (2 - 1)) = c * t := by
    push_cast
    ring
  have hu : HasDerivAt (fun t : ℝ => c / 2 * t ^ 2) (c * t) t :=
    h.congr_deriv he
  have hexp := (Real.hasDerivAt_exp (c / 2 * t ^ 2)).comp t hu
  have hp2 := (hasDerivAt_const t c).add
    ((hasDerivAt_pow 2 t).const_mul (c ^ 2))
  have hpe : 0 + c ^ 2 * (((2 : ℕ) : ℝ) * t ^ (2 - 1))
      = 2 * c ^ 2 * t := by
    push_cast
    ring
  have hpoly : HasDerivAt (fun t : ℝ => c + c ^ 2 * t ^ 2)
      (2 * c ^ 2 * t) t := hp2.congr_deriv hpe
  refine ((hpoly.mul hexp).const_mul r).congr_deriv ?_
  simp only [Function.comp_apply]
  ring

/-- Fourth derivative: `Λ⁗ = r(3c² + 6c³t² + c⁴t⁴)e^{(c/2)t²}`. -/
theorem cgf_deriv_four (r c t : ℝ) :
    HasDerivAt
      (fun t => r * ((3 * c ^ 2 * t + c ^ 3 * t ^ 3)
        * Real.exp (c / 2 * t ^ 2)))
      (r * ((3 * c ^ 2 + 6 * c ^ 3 * t ^ 2 + c ^ 4 * t ^ 4)
        * Real.exp (c / 2 * t ^ 2))) t := by
  have h := (hasDerivAt_pow 2 t).const_mul (c / 2)
  have he : c / 2 * (((2 : ℕ) : ℝ) * t ^ (2 - 1)) = c * t := by
    push_cast
    ring
  have hu : HasDerivAt (fun t : ℝ => c / 2 * t ^ 2) (c * t) t :=
    h.congr_deriv he
  have hexp := (Real.hasDerivAt_exp (c / 2 * t ^ 2)).comp t hu
  have hp2 := ((hasDerivAt_id t).const_mul (3 * c ^ 2)).add
    ((hasDerivAt_pow 3 t).const_mul (c ^ 3))
  have hpe : 3 * c ^ 2 * 1 + c ^ 3 * (((3 : ℕ) : ℝ) * t ^ (3 - 1))
      = 3 * c ^ 2 + 3 * c ^ 3 * t ^ 2 := by
    push_cast
    ring
  have hpoly : HasDerivAt
      (fun t : ℝ => 3 * c ^ 2 * t + c ^ 3 * t ^ 3)
      (3 * c ^ 2 + 3 * c ^ 3 * t ^ 2) t := hp2.congr_deriv hpe
  refine ((hpoly.mul hexp).const_mul r).congr_deriv ?_
  simp only [Function.comp_apply]
  ring

/-- `prop:worked-channel-cumulants` (second cumulant):
`K⁽²⁾(a,a) = Λ''(0) = rc`, i.e. `rs²|a|²` at `c = s²|a|²` — the
polarized `K⁽²⁾_{ij} = rs²δ_{ij}` with Gaussian scale `D = rs²`. -/
theorem second_cumulant (r c : ℝ) :
    iteratedDeriv 2
      (fun t => r * (Real.exp (c / 2 * t ^ 2) - 1)) 0 = r * c := by
  have e1 : deriv (fun t => r * (Real.exp (c / 2 * t ^ 2) - 1))
      = fun t => r * (c * t * Real.exp (c / 2 * t ^ 2)) :=
    funext fun t => (cgf_deriv_one r c t).deriv
  rw [show iteratedDeriv 2
        (fun t => r * (Real.exp (c / 2 * t ^ 2) - 1))
      = deriv (iteratedDeriv 1
        (fun t => r * (Real.exp (c / 2 * t ^ 2) - 1)))
      from iteratedDeriv_succ, iteratedDeriv_one, e1]
  rw [(cgf_deriv_two r c 0).deriv]
  norm_num

/-- `prop:worked-channel-cumulants` (fourth cumulant):
`K⁽⁴⁾(a,a,a,a) = Λ⁗(0) = 3rc²`, i.e. `3rs⁴|a|⁴` at `c = s²|a|²` —
the polarized fully symmetric
`K⁽⁴⁾_{ijkl} = rs⁴(δ_{ij}δ_{kl}+δ_{ik}δ_{jl}+δ_{il}δ_{jk})` with
isotropic quartic scale `Q = rs⁴`. -/
theorem fourth_cumulant (r c : ℝ) :
    iteratedDeriv 4
      (fun t => r * (Real.exp (c / 2 * t ^ 2) - 1)) 0
      = 3 * r * c ^ 2 := by
  have e1 : deriv (fun t => r * (Real.exp (c / 2 * t ^ 2) - 1))
      = fun t => r * (c * t * Real.exp (c / 2 * t ^ 2)) :=
    funext fun t => (cgf_deriv_one r c t).deriv
  have e2 : deriv
      (fun t => r * (c * t * Real.exp (c / 2 * t ^ 2)))
      = fun t => r * ((c + c ^ 2 * t ^ 2)
        * Real.exp (c / 2 * t ^ 2)) :=
    funext fun t => (cgf_deriv_two r c t).deriv
  have e3 : deriv
      (fun t => r * ((c + c ^ 2 * t ^ 2)
        * Real.exp (c / 2 * t ^ 2)))
      = fun t => r * ((3 * c ^ 2 * t + c ^ 3 * t ^ 3)
        * Real.exp (c / 2 * t ^ 2)) :=
    funext fun t => (cgf_deriv_three r c t).deriv
  rw [show iteratedDeriv 4
        (fun t => r * (Real.exp (c / 2 * t ^ 2) - 1))
      = deriv (iteratedDeriv 3
        (fun t => r * (Real.exp (c / 2 * t ^ 2) - 1)))
      from iteratedDeriv_succ,
    show iteratedDeriv 3
        (fun t => r * (Real.exp (c / 2 * t ^ 2) - 1))
      = deriv (iteratedDeriv 2
        (fun t => r * (Real.exp (c / 2 * t ^ 2) - 1)))
      from iteratedDeriv_succ,
    show iteratedDeriv 2
        (fun t => r * (Real.exp (c / 2 * t ^ 2) - 1))
      = deriv (iteratedDeriv 1
        (fun t => r * (Real.exp (c / 2 * t ^ 2) - 1)))
      from iteratedDeriv_succ,
    iteratedDeriv_one, e1, e2, e3]
  rw [(cgf_deriv_four r c 0).deriv]
  norm_num
  ring

end NCG
