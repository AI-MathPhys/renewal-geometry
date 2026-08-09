import NCG.Grand.GrandAudit

/-! # dimension closure of the commutant audit -/

namespace NCG

/-- `prop:commutant-audit`, dimension-comparison clause.  Once the two
generated algebras have been verified to lie in the two computed commutant
kernels, equality of their finite dimensions upgrades both inclusions to the
Howe-pair equalities. -/
theorem commutant_dimension_audit
    {n : Type*} [Fintype n] {s t : ℕ}
    (A : Fin s → Matrix n n ℂ) (B : Fin t → Matrix n n ℂ)
    (algA algB : Submodule ℂ (Matrix n n ℂ))
    (hBA : algB ≤ LinearMap.ker (commMap A))
    (hAB : algA ≤ LinearMap.ker (commMap B))
    (hdimBA : Module.finrank ℂ algB =
      Module.finrank ℂ (LinearMap.ker (commMap A)))
    (hdimAB : Module.finrank ℂ algA =
      Module.finrank ℂ (LinearMap.ker (commMap B))) :
    algB = LinearMap.ker (commMap A)
      ∧ algA = LinearMap.ker (commMap B) := by
  exact ⟨Submodule.eq_of_le_of_finrank_eq hBA hdimBA,
    Submodule.eq_of_le_of_finrank_eq hAB hdimAB⟩

end NCG
