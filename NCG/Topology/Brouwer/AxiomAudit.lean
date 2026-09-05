/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Topology.Brouwer.FixedPoint

/-!
# Axiom audit for the Brouwer fixed-point foundation

The combinatorial cube theorem and its compact-convex consequence use only Lean's standard
classical and quotient principles.  This file is intentionally a buildable audit target rather
than part of the runtime API.
-/

#print axioms fixed_point_unit_cube
#print axioms fixed_point_unit_cube_isFixedPt
#print axioms brouwer_fixed_point
#print axioms brouwer_fixed_point_isFixedPt
#print axioms brouwer_fixedPoints_nonempty
