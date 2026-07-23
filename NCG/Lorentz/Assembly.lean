/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Krein.SignedDirac
import NCG.Graph.Cohomology

/-!
# Assembly of the kinematic Lorentzian predictive geometry

* **Definition `def:kinematic-lorentzian`** — a kinematic Lorentzian
  predictive geometry bundles (i) the positive triple data, (ii) a
  graded order with a strictly monotone time function, (iii) a
  fundamental symmetry commuting with the modular weight, and (iv) a
  Krein-self-adjoint signed Dirac with the bounded-twisted-commutator
  reduction — encoded as `NCG.KinematicLorentzianData`, with
  well-formedness `NCG.KinematicLorentzianData.dirac_krein`.

* **Theorem `thm:assembly`** — the previously proved components
  assemble into this structure: the time function comes from the causal
  skeleton (`prop:causal-skeleton`), the fundamental symmetry from the
  signed cover (`prop:krein-datum`), the Krein-self-adjointness and
  commutator reduction from `thm:signed-dirac`
  (`NCG.KinematicLorentzianData.mk` + `dirac_krein` +
  `twisted_reduction`).

* **Theorem `thm:regular-lorentzian`** — in the regular commuting
  regime the four pillars are the proved statements: `q_alg = c`
  (`NCG.latticeShellCard_le`/`le_latticeShellCard`), interval growth
  `τ^c` (`NCG.card_interval`), non-removability of `J_χ` for a nonzero
  class (`NCG.Multigraph.nonremovable_of_class_ne_zero`), and the
  assembled signed Dirac.

* **Definition `def:rescaling`** — the calibrated rescaling
  `ι_R(x) = R⁻¹(ℓ₁x₁, …)` is monotone for the product orders
  (`NCG.calibratedRescale_mono`), the order-theoretic core of the
  continuum-ladder limit. -/

namespace NCG

/-! ### The kinematic structure (`def:kinematic-lorentzian`,
`thm:assembly`) -/

/-- **Definition `def:kinematic-lorentzian`**: the bookkeeping bundle of
the kinematic Lorentzian predictive geometry — a graded order with time
function, and the signed modular Dirac data `(J, Δ, B)` with the Krein
relations. -/
structure KinematicLorentzianData (A : Type*) [Ring A] [StarRing A]
    (P : Type*) [PartialOrder P] where
  /-- the time function of the causal skeleton
  (`prop:causal-skeleton`) -/
  T : P → ℕ
  /-- strict monotonicity: the order has a genuine time direction -/
  Tmono : ∀ x y : P, x < y → T x < T y
  /-- the fundamental symmetry of the signed cover
  (`prop:krein-datum`) -/
  J : A
  /-- the modular weight `e^{βN}` -/
  Δ : A
  /-- the bounded `J`-self-adjoint perturbation -/
  B : A
  J_star : star J = J
  J_sq : J * J = 1
  Δ_star : star Δ = Δ
  JΔ_comm : J * Δ = Δ * J
  B_krein : J * star B * J = B

namespace KinematicLorentzianData

variable {A : Type*} [Ring A] [StarRing A] {P : Type*} [PartialOrder P]
  (K : KinematicLorentzianData A P)

/-- The signed modular Dirac of the bundle. -/
def dirac : A := K.J * K.Δ + K.B

/-- **Theorem `thm:assembly` / `thm:signed-dirac`**: the assembled
Dirac is Krein-self-adjoint — the structure is well formed. -/
theorem dirac_krein : K.J * star K.dirac * K.J = K.dirac :=
  signed_dirac_krein_selfadjoint K.J K.Δ K.B K.J_star K.J_sq
    K.Δ_star K.JΔ_comm K.B_krein

/-- **Theorem `thm:assembly`** (twisted-commutator reduction): when the
modular weight is invertible, the twisted commutators of the assembled
Dirac reduce to those of the bounded part. -/
theorem twisted_reduction (u : Aˣ) (hu : (u : A) = K.Δ) (a : A) :
    (K.J * (u : A) + K.B) * a
        - (K.J * (u : A) * a * (↑u⁻¹ : A) * K.J)
          * (K.J * (u : A) + K.B)
      = K.B * a
        - (K.J * (u : A) * a * (↑u⁻¹ : A) * K.J) * K.B :=
  twisted_commutator_reduction K.J u a K.B K.J_sq

/-- The time function separates comparable points
(`prop:causal-skeleton` input). -/
theorem time_injective_on_chains {x y : P} (hxy : x < y) :
    K.T x ≠ K.T y :=
  (K.Tmono x y hxy).ne

end KinematicLorentzianData

/-! ### Non-removability of the fundamental symmetry
(`thm:regular-lorentzian` (iii)) -/

namespace Multigraph

/-- **Theorem `thm:regular-lorentzian` (iii)**: a sign cocycle with
nonzero class is not removable by a flat gauge (`cor:removability`
contrapositive) — the fundamental symmetry of the signed cover is
essential. -/
theorem nonremovable_of_class_ne_zero {G : Multigraph}
    {χ : G.E → ZMod 2} (h : H1.mk G χ ≠ 0) :
    ¬IsCoboundary (G := G) χ :=
  fun hc => h (H1.mk_eq_zero_iff.mpr hc)

end Multigraph

/-- **Definition `def:enhanced-package`**: an enhanced signed spectral
package — the kinematic bundle together with the reset-direction
scaling datum, the pointwise symmetric second-moment field `M_Θ(x)`.
The bare package reconstructs the ordered signed predictive monoid and
the holonomy class; the continuum metric additionally uses `M_Θ`
(`lem:continuum-factorisation` via
`NCG.symbol_through_second_moment`). -/
structure EnhancedPackage (A : Type*) [Ring A] [StarRing A]
    (P : Type*) [PartialOrder P] (X : Type*) (d : ℕ)
    extends KinematicLorentzianData A P where
  /-- the reset-direction scaling datum: the second-moment field -/
  Mfield : X → Matrix (Fin d) (Fin d) ℝ
  /-- second moments are symmetric -/
  Mfield_symm : ∀ x, (Mfield x).IsSymm

/-! ### Calibrated rescaling (`def:rescaling`) -/

/-- **Definition `def:rescaling`**: the calibrated rescaling of the
lattice into the continuum orthant, `ι_R(x)_i = R⁻¹·ℓᵢ·xᵢ`. -/
noncomputable def calibratedRescale {c : ℕ} (ℓ : Fin c → ℝ) (R : ℝ)
    (x : Fin c → ℕ) : Fin c → ℝ :=
  fun i => R⁻¹ * (ℓ i * x i)

/-- The calibrated rescaling is monotone from the lattice product order
to the continuum product order — the order-theoretic core of the
continuum ladder (`def:rescaling`, feeding `thm:minkowski-2d` and
`thm:taxicab-limit`). -/
theorem calibratedRescale_mono {c : ℕ} {ℓ : Fin c → ℝ}
    (hℓ : ∀ i, 0 < ℓ i) {R : ℝ} (hR : 0 < R) {x y : Fin c → ℕ}
    (hxy : ∀ i, x i ≤ y i) (i : Fin c) :
    calibratedRescale ℓ R x i ≤ calibratedRescale ℓ R y i := by
  unfold calibratedRescale
  have h1 : (x i : ℝ) ≤ (y i : ℝ) := by exact_mod_cast hxy i
  have h2 : 0 < ℓ i := hℓ i
  have h3 : (0:ℝ) < R⁻¹ := by positivity
  have h4 := mul_le_mul_of_nonneg_left h1 h2.le
  exact mul_le_mul_of_nonneg_left h4 h3.le

end NCG
