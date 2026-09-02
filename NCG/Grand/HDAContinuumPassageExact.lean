/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.HDACommutatorClosureExact
import NCG.Grand.HDASemidirectExact

/-!
# Passage of the finite HDA identities to a common continuum core

The finite cutoff brackets in `thm:finite-HDA` are already derived in
`HDACommutatorClosureExact` and `HDASemidirectExact`.  This file supplies its
last analytic sentence.  Once all generators and the three transported
right-hand sides converge in the common normed-algebra realization of a core,
continuity of multiplication, subtraction, and scalar multiplication carries
all three exact cutoff identities to the limit.
-/

open Filter Topology

namespace NCG
namespace HDAContinuum

/-- **Consistent label/source/metric convergence passes the three finite HDA
identities to the continuum.**  The seven limit objects are evaluations of
the limiting generators and transported labels on one common core. -/
theorem identities_pass_to_common_core
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (DvX DwX DbrX HNX HMX HellX HhhX : ℕ → A)
    (Dv Dw Dbr HN HM Hell Hhh : A)
    (hDv : Tendsto DvX atTop (nhds Dv))
    (hDw : Tendsto DwX atTop (nhds Dw))
    (hDbr : Tendsto DbrX atTop (nhds Dbr))
    (hHN : Tendsto HNX atTop (nhds HN))
    (hHM : Tendsto HMX atTop (nhds HM))
    (hHell : Tendsto HellX atTop (nhds Hell))
    (hHhh : Tendsto HhhX atTop (nhds Hhh))
    (hDD : ∀ cutoff,
      (-Complex.I) • (DvX cutoff * DwX cutoff - DwX cutoff * DvX cutoff) =
        DbrX cutoff)
    (hDH : ∀ cutoff,
      (-Complex.I) • (DvX cutoff * HNX cutoff - HNX cutoff * DvX cutoff) =
        HellX cutoff)
    (hHH : ∀ cutoff,
      (-Complex.I) • (HNX cutoff * HMX cutoff - HMX cutoff * HNX cutoff) =
        HhhX cutoff) :
    ((-Complex.I) • (Dv * Dw - Dw * Dv) = Dbr)
      ∧ ((-Complex.I) • (Dv * HN - HN * Dv) = Hell)
      ∧ ((-Complex.I) • (HN * HM - HM * HN) = Hhh) := by
  have hDDL : Tendsto
      (fun cutoff => (-Complex.I) •
        (DvX cutoff * DwX cutoff - DwX cutoff * DvX cutoff))
      atTop (nhds ((-Complex.I) • (Dv * Dw - Dw * Dv))) :=
    ((hDv.mul hDw).sub (hDw.mul hDv)).const_smul (-Complex.I)
  have hDHL : Tendsto
      (fun cutoff => (-Complex.I) •
        (DvX cutoff * HNX cutoff - HNX cutoff * DvX cutoff))
      atTop (nhds ((-Complex.I) • (Dv * HN - HN * Dv))) :=
    ((hDv.mul hHN).sub (hHN.mul hDv)).const_smul (-Complex.I)
  have hHHL : Tendsto
      (fun cutoff => (-Complex.I) •
        (HNX cutoff * HMX cutoff - HMX cutoff * HNX cutoff))
      atTop (nhds ((-Complex.I) • (HN * HM - HM * HN))) :=
    ((hHN.mul hHM).sub (hHM.mul hHN)).const_smul (-Complex.I)
  refine ⟨tendsto_nhds_unique hDDL ?_, tendsto_nhds_unique hDHL ?_,
    tendsto_nhds_unique hHHL ?_⟩
  · exact hDbr.congr' (Eventually.of_forall fun cutoff => (hDD cutoff).symm)
  · exact hHell.congr' (Eventually.of_forall fun cutoff => (hDH cutoff).symm)
  · exact hHhh.congr' (Eventually.of_forall fun cutoff => (hHH cutoff).symm)

/-- Exact cutoff reduction removes every Feshbach interface term; convergence
then leaves zero on the common core. -/
theorem feshbach_terms_tendsto_zero
    {A : Type*} [NormedAddCommGroup A]
    (cross : ℕ → A) (hcross : ∀ cutoff, cross cutoff = 0) :
    Tendsto cross atTop (nhds 0) := by
  have hc : cross = fun _ : ℕ => (0 : A) := funext hcross
  rw [hc]
  exact tendsto_const_nhds

end HDAContinuum
end NCG
