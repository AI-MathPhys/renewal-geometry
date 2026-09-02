/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RelativeUpstreamPrimitiveClosure

/-!
# Axiom audit for relative upstream primitive closure

The commands below record the trusted assumptions of the four principal
closure and irredundancy results.
-/

#print axioms NCG.RelativeUpstreamPrimitiveClosure.factorsThrough_signatureImage
#print axioms NCG.RelativeUpstreamPrimitiveClosure.four_rows_irredundant
#print axioms NCG.RelativeUpstreamPrimitiveClosure.four_pairs_remain_separating
#print axioms NCG.RelativeUpstreamPrimitiveClosure.downstream_packet_factors
