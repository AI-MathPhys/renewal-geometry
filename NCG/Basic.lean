/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# NCG — a Lean 4 library for noncommutative geometry

`NCG` is the *generic* layer of the Renewal Geometry formalization: the parts
of Alain Connes' noncommutative geometry (spectral triples, Krein spaces,
completely positive maps, Clifford/Jordan algebra, graph cohomology,
Perron–Frobenius theory) that Mathlib does not yet contain and that make no
reference to renewal processes.  The Renewal Geometry programme itself lives
in the companion library `RenewalGeometry`, which depends on this one.

Contents:

* completely positive maps, unital channel monoids, Schwarz maps, Choi's
  multiplicative domain, projective defects, Clifford/Jordan generation and
  spin factors (`NCG.Algebra`);
* spectral triples `(𝒜, ℋ, D)` (`NCG.SpectralTriple`);
* Krein spaces, fundamental symmetries, signed (Lorentzian) sectors and their
  classification by `H¹(G, ℤ/2)` (`NCG.Krein`);
* directed multigraphs, sign cocycles, principal `ℤ/2`- and `ℤ/4`-covers
  (`NCG.Graph`);
* diagonal (length-Dirac) operator models (`NCG.Operator`);
* the Perron–Frobenius theorem for irreducible nonnegative matrices, stated in
  the `Matrix` namespace against Mathlib's `Matrix.IsIrreducible`
  (`NCG.PerronFrobenius`).

Design rule: nothing in `NCG` imports `RenewalGeometry`
(checked by `scripts/check_layering.py`).
-/

namespace NCG

end NCG
