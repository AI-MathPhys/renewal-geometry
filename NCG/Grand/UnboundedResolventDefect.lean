/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Resolvent defect identity on graph-domain carriers

An unbounded operator is represented by a Banach graph-domain carrier, its
continuous inclusion into the ambient space, and its graph-bounded action.
This module proves the exact rectangular resolvent defect identity in that
representation.  No finite-dimensional or bounded-generator assumption is
made.
-/

noncomputable section

namespace NCG

universe u v w x y

variable {K : Type u} [NontriviallyNormedField K]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace K E]
variable {H : Type w} [NormedAddCommGroup H] [NormedSpace K H]
variable {DA : Type x} [NormedAddCommGroup DA] [NormedSpace K DA]
variable {DN : Type y} [NormedAddCommGroup DN] [NormedSpace K DN]

/-- Exact unbounded resolvent defect identity.  Here `iA` and `iN` are graph
domain inclusions, `A` and `N` are graph-bounded generator actions, `Vdom`
is the domain lift of `V`, and `RA`, `RN` are resolvents with codomains in
the corresponding graph domains. -/
theorem graphDomain_resolvent_defect
    (iA : DA →L[K] E) (A : DA →L[K] E)
    (iN : DN →L[K] H) (N : DN →L[K] H)
    (V : E →L[K] H) (Vdom : DA →L[K] DN)
    (R : DA →L[K] H) (RA : E →L[K] DA) (RN : H →L[K] DN)
    (z : K)
    (hVdom : iN.comp Vdom = V.comp iA)
    (hR : R = N.comp Vdom - V.comp A)
    (hRA : (z • iA - A).comp RA = 1)
    (hRN : RN.comp (z • iN - N) = 1) :
    iN.comp (RN.comp V) - V.comp (iA.comp RA) =
      iN.comp (RN.comp (R.comp RA)) := by
  ext f
  let xf : DA := RA f
  have hsource : z • iA xf - A xf = f := by
    simpa only [ContinuousLinearMap.comp_apply,
      sub_apply, smul_apply, one_apply_eq_self] using DFunLike.congr_fun hRA f
  have htarget : RN (z • iN (Vdom xf) - N (Vdom xf)) = Vdom xf := by
    simpa only [ContinuousLinearMap.comp_apply,
      sub_apply, smul_apply, one_apply_eq_self] using
        DFunLike.congr_fun hRN (Vdom xf)
  have hVpoint : iN (Vdom xf) = V (iA xf) := by
    exact DFunLike.congr_fun hVdom xf
  have hRpoint : R xf = N (Vdom xf) - V (A xf) := by
    simpa only [sub_apply,
      ContinuousLinearMap.comp_apply] using DFunLike.congr_fun hR xf
  have hinner :
      V f - (z • iN (Vdom xf) - N (Vdom xf)) = R xf := by
    rw [← hsource, map_sub, map_smul, ← hVpoint, hRpoint]
    module
  change iN (RN (V f)) - V (iA xf) = iN (RN (R xf))
  rw [← hVpoint, ← htarget]
  calc
    iN (RN (V f)) - iN (RN (z • iN (Vdom xf) - N (Vdom xf))) =
        iN (RN (V f - (z • iN (Vdom xf) - N (Vdom xf)))) := by
          simp only [map_sub]
    _ = iN (RN (R xf)) := by rw [hinner]

end NCG
