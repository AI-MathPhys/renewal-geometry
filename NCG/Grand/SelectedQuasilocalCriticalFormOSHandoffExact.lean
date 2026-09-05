/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/

import NCG.Grand.QuasilocalOSCompletion

/-!
# Selected quasilocal critical-form OS handoff

This file formalizes `thm:GTLOC-selected-handoff` at its stated abstraction
level.  The nine load-bearing rows are represented by nine distinct evidence
types, so no row can be silently reused as another.  The inherited
critical-form reconstruction consumes all nine rows and returns a sector with
separate proofs of selection, quasilocality, pair completeness, and genuine
interaction.

The conclusion is intentionally only one selected sector.  It contains no
complete-local-net or exhaustive-QFT field; those require the additional
source-completeness and fibre-elimination hypotheses named in the manuscript.
-/

namespace NCG.SelectedQuasilocalCriticalFormOSHandoff

/-- The exact endpoint claimed by the theorem, with its four logically
independent qualifiers retained as separate fields. -/
structure SelectedSectorCertificate
    (Sector : Type*)
    (Selected Quasilocal PairComplete Interacting : Sector → Prop) where
  sector : Sector
  selected : Selected sector
  quasilocal : Quasilocal sector
  pairComplete : PairComplete sector
  interacting : Interacting sector

/-- Evidence for hypotheses (H1)--(H9), kept in manuscript order. -/
structure HandoffPacket
    (SameHistoryCommonPhysical CriticalFirstPairLocality RouteLocality
      ContactAndDirectAction TransportOrTargetTail QuasilocalOSAlgebra
      LocalWhitening ConnectedWitness IndependentRows : Type*) where
  sameHistoryCommonPhysical : SameHistoryCommonPhysical
  criticalFirstPairLocality : CriticalFirstPairLocality
  routeLocality : RouteLocality
  contactAndDirectAction : ContactAndDirectAction
  transportOrTargetTail : TransportOrTargetTail
  quasilocalOSAlgebra : QuasilocalOSAlgebra
  localWhitening : LocalWhitening
  connectedWitness : ConnectedWitness
  independentRows : IndependentRows

/-- The inherited critical-form OS reconstruction theorem, exposed with all
nine inputs.  In particular, the independent line/reflection/boundary/UV row
cannot be inferred from the positive locality rows. -/
structure InheritedReconstruction
    (SameHistoryCommonPhysical CriticalFirstPairLocality RouteLocality
      ContactAndDirectAction TransportOrTargetTail QuasilocalOSAlgebra
      LocalWhitening ConnectedWitness IndependentRows Sector : Type*)
    (Selected Quasilocal PairComplete Interacting : Sector → Prop) where
  reconstruct :
    SameHistoryCommonPhysical →
    CriticalFirstPairLocality →
    RouteLocality →
    ContactAndDirectAction →
    TransportOrTargetTail →
    QuasilocalOSAlgebra →
    LocalWhitening →
    ConnectedWitness →
    IndependentRows →
    SelectedSectorCertificate Sector Selected Quasilocal PairComplete Interacting

/-- The canonical sector assembled by the inherited reconstruction. -/
def assemble_selected_quasilocal_critical_form_OS_sector
    {SameHistoryCommonPhysical CriticalFirstPairLocality RouteLocality
      ContactAndDirectAction TransportOrTargetTail QuasilocalOSAlgebra
      LocalWhitening ConnectedWitness IndependentRows Sector : Type*}
    {Selected Quasilocal PairComplete Interacting : Sector → Prop}
    (P : HandoffPacket SameHistoryCommonPhysical CriticalFirstPairLocality
      RouteLocality ContactAndDirectAction TransportOrTargetTail
      QuasilocalOSAlgebra LocalWhitening ConnectedWitness IndependentRows)
    (R : InheritedReconstruction SameHistoryCommonPhysical
      CriticalFirstPairLocality RouteLocality ContactAndDirectAction
      TransportOrTargetTail QuasilocalOSAlgebra LocalWhitening ConnectedWitness
      IndependentRows Sector Selected Quasilocal PairComplete Interacting) :
    SelectedSectorCertificate Sector Selected Quasilocal PairComplete
      Interacting :=
  R.reconstruct P.sameHistoryCommonPhysical P.criticalFirstPairLocality
    P.routeLocality P.contactAndDirectAction P.transportOrTargetTail
    P.quasilocalOSAlgebra P.localWhitening P.connectedWitness P.independentRows

/-- **`thm:GTLOC-selected-handoff`.**  Passing the literal nine-row packet to
the inherited reconstruction yields a selected quasilocal, pair-complete,
interacting OS sector. -/
theorem selected_quasilocal_critical_form_OS_handoff
    {SameHistoryCommonPhysical CriticalFirstPairLocality RouteLocality
      ContactAndDirectAction TransportOrTargetTail QuasilocalOSAlgebra
      LocalWhitening ConnectedWitness IndependentRows Sector : Type*}
    {Selected Quasilocal PairComplete Interacting : Sector → Prop}
    (P : HandoffPacket SameHistoryCommonPhysical CriticalFirstPairLocality
      RouteLocality ContactAndDirectAction TransportOrTargetTail
      QuasilocalOSAlgebra LocalWhitening ConnectedWitness IndependentRows)
    (R : InheritedReconstruction SameHistoryCommonPhysical
      CriticalFirstPairLocality RouteLocality ContactAndDirectAction
      TransportOrTargetTail QuasilocalOSAlgebra LocalWhitening ConnectedWitness
      IndependentRows Sector Selected Quasilocal PairComplete Interacting) :
    Nonempty (SelectedSectorCertificate Sector Selected Quasilocal PairComplete
      Interacting) :=
  ⟨assemble_selected_quasilocal_critical_form_OS_sector P R⟩

/-- The returned sector exposes each advertised endpoint property directly. -/
theorem selected_handoff_endpoint_properties
    {SameHistoryCommonPhysical CriticalFirstPairLocality RouteLocality
      ContactAndDirectAction TransportOrTargetTail QuasilocalOSAlgebra
      LocalWhitening ConnectedWitness IndependentRows Sector : Type*}
    {Selected Quasilocal PairComplete Interacting : Sector → Prop}
    (P : HandoffPacket SameHistoryCommonPhysical CriticalFirstPairLocality
      RouteLocality ContactAndDirectAction TransportOrTargetTail
      QuasilocalOSAlgebra LocalWhitening ConnectedWitness IndependentRows)
    (R : InheritedReconstruction SameHistoryCommonPhysical
      CriticalFirstPairLocality RouteLocality ContactAndDirectAction
      TransportOrTargetTail QuasilocalOSAlgebra LocalWhitening ConnectedWitness
      IndependentRows Sector Selected Quasilocal PairComplete Interacting) :
    let S := assemble_selected_quasilocal_critical_form_OS_sector P R
    Selected S.sector ∧ Quasilocal S.sector ∧ PairComplete S.sector ∧
      Interacting S.sector := by
  let S := assemble_selected_quasilocal_critical_form_OS_sector P R
  exact ⟨S.selected, S.quasilocal, S.pairComplete, S.interacting⟩

end NCG.SelectedQuasilocalCriticalFormOSHandoff
