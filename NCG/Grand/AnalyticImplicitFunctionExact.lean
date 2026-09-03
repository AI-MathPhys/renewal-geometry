/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# Analytic implicit functions on product domains

Mathlib's product-domain implicit-function theorem constructs a canonical
local branch from a strict derivative and proves its differentiability.  This
file records the analytic upgrade: when the defining map is analytic, the
same canonical branch is analytic.  The proof applies the analytic inverse
theorem to the local homeomorphism already constructed by the implicit-
function theorem and then composes with the fixed-level inclusion.
-/

open Filter
open scoped Topology

noncomputable section

namespace NCG.AnalyticImplicitFunction

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [CharZero 𝕜]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [CompleteSpace E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [CompleteSpace E₂]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace F]

/-- The canonical product-domain implicit function associated with an
analytic map is analytic at the base point. -/
theorem analyticAt_implicitFunctionOfProdDomain
    {u : E₁ × E₂} {f : E₁ × E₂ → F}
    (hf : AnalyticAt 𝕜 f u)
    (if₂u : (fderiv 𝕜 f u ∘L
      ContinuousLinearMap.inr 𝕜 E₁ E₂).IsInvertible) :
    AnalyticAt 𝕜
      (hf.hasStrictFDerivAt.implicitFunctionOfProdDomain if₂u) u.1 := by
  let dfu : HasStrictFDerivAt f (fderiv 𝕜 f u) u :=
    hf.hasStrictFDerivAt
  let φ := dfu.implicitFunctionDataOfProdDomain if₂u
  have hprod : AnalyticAt 𝕜 φ.prodFun u := by
    change AnalyticAt 𝕜 (fun z => (f z, z.1)) u
    exact hf.prod analyticAt_fst
  have hsymm : AnalyticAt 𝕜 φ.toOpenPartialHomeomorph.symm
      (φ.toOpenPartialHomeomorph u) := by
    apply φ.toOpenPartialHomeomorph.analyticAt_symm'
      φ.pt_mem_toOpenPartialHomeomorph_source hprod
    exact φ.hasStrictFDerivAt.hasFDerivAt.fderiv
  have hinclusion : AnalyticAt 𝕜 (fun x : E₁ => (f u, x)) u.1 :=
    analyticAt_const.prod analyticAt_id
  have hbranch : AnalyticAt 𝕜
      (fun x : E₁ => φ.toOpenPartialHomeomorph.symm (f u, x)) u.1 := by
    change AnalyticAt 𝕜
      (φ.toOpenPartialHomeomorph.symm ∘ fun x : E₁ => (f u, x)) u.1
    apply hsymm.comp_of_eq hinclusion
    rfl
  have hsnd : AnalyticAt 𝕜
      (fun x : E₁ => (φ.toOpenPartialHomeomorph.symm (f u, x)).2) u.1 := by
    change AnalyticAt 𝕜
      ((fun z : E₁ × E₂ => z.2) ∘
        fun x : E₁ => φ.toOpenPartialHomeomorph.symm (f u, x)) u.1
    exact analyticAt_snd.comp hbranch
  simpa [HasStrictFDerivAt.implicitFunctionOfProdDomain_def,
    HasStrictFDerivAt.implicitFunctionDataOfProdDomain,
    ImplicitFunctionData.implicitFunction_apply, φ, dfu] using hsnd

end NCG.AnalyticImplicitFunction
