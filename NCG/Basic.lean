/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# NCG — a Lean 4 library for noncommutative geometry

This library formalizes noncommutative geometry (NCG) in the spectral-triple
formulation of Alain Connes, together with the *renewal spectral geometry*
of the companion manuscript

> A. Pélissier, *Renewal Spectral Geometry and the Emergence of Lorentzian
> Spacetime*.

Mathlib currently has no NCG development; this library is intended to grow
into a general-purpose formalization of:

* spectral triples `(𝒜, ℋ, D)` (`NCG.SpectralTriple`);
* Krein spaces, fundamental symmetries, and signed (Lorentzian) sectors
  (`NCG.Krein`);
* completely positive maps and channel monoids (`NCG.Algebra.CPMap`);
* renewal memories, predictive quotients, and the predictive order
  (`NCG.Renewal`);
* sign cocycles, principal `ℤ/2`-covers and their holonomy on predictive
  graphs (`NCG.Graph`);
* the diagonal (length-Dirac) operator models on which the manuscript's
  operator identities can be proved algebraically (`NCG.Operator`).

The design principle is that everything is stated at the level of generality
of the manuscript, but each analytic statement is first proved in a concrete
algebraic model (finitely supported vectors, diagonal operators, graph
covers), keeping the library `sorry`-free while the heavier operator-analytic
infrastructure (unbounded self-adjoint operators, compact resolvents,
Dixmier traces) is developed on top of Mathlib.
-/

namespace NCG

end NCG
