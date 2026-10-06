/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactQuadraticHamiltonian

/-!
# Finite-action and canonical provenance: assembly
  (`thm:supp-exact-action-provenance`, `eq:supp-exact-canonical-objects`,
  `lem:supp-initial-calculus` (value and linearization); emergent-spacetime manuscript)

Assembles clauses (i)–(iv) of `thm:supp-exact-action-provenance` for the actual objects
(`Λ = 0`, symmetric-square-root triad, stationary connection `statAst χ R`, Legendre chart at flat
data):

* `Lh_cplx`: for odd `N` the complexification of `D𝒞_h(0)` is `InitialConstraintLinearRange.Lh`.
* `canonicalHamiltonian_restricted_quadratic`: the restriction `X = (u, p) ↦ 𝓗_h(I + u, p, 1, 0)`
  has value `0`, gradient `0` and Hessian `2 H₂` at `X = 0` (`χ = 1`).
* The canonical objects of `eq:supp-exact-canonical-objects` are defined from the canonical
  Hamiltonian: `Hcan` (`𝓗_h(X, λ)`), `Pcan = ∇_λ 𝓗_h` (`⟨·,·⟩_h`-gradient), `Fcan = 𝕁∇_X 𝓗_h`,
  `Mcan = D_λ P_h`, `Bcan = D_X P_h F_h^{can}`; `initialConstraint_eq_Pcan`: the initial constraint
  map is `(-P_N, P_β)` at `λ = (1, 0)`.
* **`exact_action_provenance`** (clauses (i)–(iv) at flat data, `χ = 1`): an `N`-independent
  threshold `ε` such that for `0 < R`, `hR ≤ ε` the stationary connection is analytic near flat
  data (chart hypothesis discharged: `c_* = 2/3`), the Legendre chart hypothesis holds at flat
  data, the canonical Hamiltonian is analytic there with quadratic part `H₂`
  (`eq:supp-exact-H2`), and the original initial constraint map vanishes at flat data, is
  analytic there and has linearization the Fierz–Pauli rows `L_h`.
-/

open Filter Finset
open scoped Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace RenewalGeometry.ExactPhaseAction.QuadJet

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

open InitialConstraintLinearRange (sym6)
open OddPhaseDerivativeReal

variable {N : ℕ} [NeZero N]

/-! ### Faithfulness: the complexified linearization is `InitialConstraintLinearRange.Lh` -/

/-- The complexified `Sym₃` coordinate fields of a real metric/momentum field. -/
def cplx (u : MetF N) : Fin 6 → LatticeTorusPlancherel.Grid 3 N → ℂ := fun c x => ((u x c : ℝ) : ℂ)

theorem sym6_symm (i j : Fin 3) : sym6 i j = sym6 j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem delta_ofReal (hN : Odd N) (i : Fin 3) (f : Site N → ℝ) :
    InitialConstraintLinearRange.delta i (fun x => ((f x : ℝ) : ℂ)) = fun x => ((pd i f x : ℝ) : ℂ) :=
  (ofReal_pd hN i f).symm

theorem delta_cplx (hN : Odd N) (u : MetF N) (j : Fin 3) (c : Fin 6) :
    InitialConstraintLinearRange.delta j (cplx u c) = fun x => ((pd j (fun y => u y c) x : ℝ) : ℂ) :=
  delta_ofReal hN j (fun y => u y c)

/-- **The rows `D𝒞_h(0)` are `L_h`**: for odd `N`, the complexification of
`(R₁(u), -2δ_jπ^{ij})` is `InitialConstraintLinearRange.Lh` applied to the complexified fields
(`eq:supp-initial-linear-map`, the complex Fourier-multiplier encoding of `lem:supp-initial-range`). -/
theorem Lh_cplx (hN : Odd N) (u π : MetF N) :
    InitialConstraintLinearRange.Lh (cplx u, cplx π) =
      ((fun x => ((R1F u x : ℝ) : ℂ)), fun a x => ((divF π x a : ℝ) : ℂ)) := by
  refine Prod.ext ?_ ?_
  · have htr : (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 6 => PeriodicGridSobolev.Grid N → ℂ) 0 +
        LinearMap.proj (R := ℂ) (φ := fun _ : Fin 6 => PeriodicGridSobolev.Grid N → ℂ) 1 +
        LinearMap.proj (R := ℂ) (φ := fun _ : Fin 6 => PeriodicGridSobolev.Grid N → ℂ) 2) (cplx u) =
        fun y => ((trS (u y) : ℝ) : ℂ) := by
      funext y
      simp [cplx, trS, symMat, sym6, Fin.sum_univ_three]
    funext x
    simp only [InitialConstraintLinearRange.Lh, LinearMap.prodMap_apply,
      InitialConstraintLinearRange.rowS, LinearMap.sub_apply, LinearMap.sum_apply,
      LinearMap.comp_apply, InitialConstraintLinearRange.pr, LinearMap.proj_apply]
    rw [htr]
    simp only [Pi.sub_apply, Finset.sum_apply]
    rw [R1F]
    push_cast
    congr 1
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [delta_cplx hN, delta_ofReal hN i]
      rfl
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [delta_ofReal hN i (fun y => trS (u y)), delta_ofReal hN i]
  · funext a x
    simp only [InitialConstraintLinearRange.Lh, LinearMap.prodMap_apply,
      InitialConstraintLinearRange.rowV, LinearMap.pi_apply, LinearMap.smul_apply,
      LinearMap.sum_apply, LinearMap.comp_apply, InitialConstraintLinearRange.pr,
      LinearMap.proj_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, divF]
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [delta_cplx hN]
    simp only [symMat]
    rw [sym6_symm j a]


/-! ### The quadratic part in the canonical variables `X = (u, p)` -/

/-- The canonical Hamiltonian at unit lapse and zero shift as a function of `X = (u, p)`,
`γ = I + u` (Legendre chart at flat data). -/
def canonHres (χ R : ℝ) (X : MetF N × MetF N) : ℝ :=
  canonicalHamiltonian χ 0 sqrtTriad (statAst χ R) (zFlat N) (refMult (flatMet N + X.1)) X.2

theorem canonHres_eq (χ R : ℝ) :
    canonHres (N := N) χ R = fun X => canonH χ R (qFlat N + iotaX X) := by
  funext X
  simp only [canonHres, canonH]
  rw [← refMult_add]

/-- **Clause (iv) in the canonical variables** (`χ = 1`): `X = (u, p) ↦ 𝓗_h(I + u, p, 1, 0)`
vanishes at `X = 0` with zero gradient, and its Hessian there is `2 H₂(u, p)`
(`eq:supp-exact-H2`): `H₂` is the quadratic canonical part. -/
theorem canonicalHamiltonian_restricted_quadratic {R : ℝ} {U : Set (CoP N)}
    (hU : FlatChart 1 R U) :
    canonHres 1 R (0 : MetF N × MetF N) = 0 ∧ fderiv ℝ (canonHres 1 R) (0 : MetF N × MetF N) = 0 ∧
      ∀ u p : MetF N, fderiv ℝ (fderiv ℝ (canonHres 1 R)) 0 (u, p) (u, p) = 2 * H2 u p := by
  obtain ⟨h0, h1, h2⟩ := canonicalHamiltonian_quadratic_part_one hU
  have hH := analyticAt_canonH hU one_ne_zero
  have hq0 : qFlat N + iotaX (0 : MetF N × MetF N) = qFlat N := by simp
  have hH' : AnalyticAt ℝ (canonH 1 R) (qFlat N + iotaX (0 : MetF N × MetF N)) := by
    rw [hq0]; exact hH
  rw [canonHres_eq]
  refine ⟨by simp only [hq0, h0], ?_, fun u p => ?_⟩
  · have hA : HasFDerivAt (fun X : MetF N × MetF N => qFlat N + iotaX X) iotaX 0 :=
      (iotaX.hasFDerivAt).const_add _
    have h := HasFDerivAt.comp (g := canonH 1 R) (f := fun X : MetF N × MetF N => qFlat N + iotaX X)
      0 hH'.differentiableAt.hasFDerivAt hA
    have h' : HasFDerivAt (fun X : MetF N × MetF N => canonH 1 R (qFlat N + iotaX X))
        (fderiv ℝ (canonH 1 R) (qFlat N + iotaX 0) ∘L iotaX) 0 := h
    rw [h'.fderiv, hq0, h1, ContinuousLinearMap.zero_comp]
  · rw [fderiv_fderiv_affine (qFlat N) iotaX hH', hq0, iotaX_apply]
    exact h2 u p

/-! ### The canonical objects of `eq:supp-exact-canonical-objects` -/

/-- The canonical Hamiltonian `𝓗_h(X, λ)`, `X = (γ, π)`, `λ = (N, β)`, of the actual action. -/
def Hcan (χ R : ℝ) (X : MetF N × MetF N) (lam : (Site N → ℝ) × (Site N → Fin 3 → ℝ)) : ℝ :=
  canonicalHamiltonian χ 0 sqrtTriad (statAst χ R) (zFlat N) (X.1, lam.1, lam.2) X.2

/-- `P_h = ∇_λ 𝓗_h` (`⟨·,·⟩_h`-gradients along unit lapse and shift directions). -/
def Pcan (χ R : ℝ) (X : MetF N × MetF N) (lam : (Site N → ℝ) × (Site N → Fin 3 → ℝ)) :
    (Site N → ℝ) × (Site N → Fin 3 → ℝ) :=
  (fun x => (hN N ^ 3)⁻¹ * fderiv ℝ (fun q : ParF N × MetF N =>
      canonicalHamiltonian χ 0 sqrtTriad (statAst χ R) (zFlat N) q.1 q.2)
        ((X.1, lam.1, lam.2), X.2) (lapseDir x),
   fun x a => (hN N ^ 3)⁻¹ * fderiv ℝ (fun q : ParF N × MetF N =>
      canonicalHamiltonian χ 0 sqrtTriad (statAst χ R) (zFlat N) q.1 q.2)
        ((X.1, lam.1, lam.2), X.2) (shiftDir x a))

/-- The `Sym₃` weights of the grid pairing (`1` on the diagonal, `2` off it). -/
def wt6 : Fin 6 → ℝ := ![1, 1, 1, 2, 2, 2]

/-- The unit metric (or momentum) direction at site `x`, coordinate `c`. -/
def metDir (x : Site N) (c : Fin 6) : MetF N := Pi.single x (Pi.single c 1)

/-- `F_h^{can} = 𝕁∇_X 𝓗_h = (∇_π 𝓗_h, -∇_γ 𝓗_h)` (`⟨·,·⟩_h`-gradients). -/
def Fcan (χ R : ℝ) (X : MetF N × MetF N) (lam : (Site N → ℝ) × (Site N → Fin 3 → ℝ)) :
    MetF N × MetF N :=
  (fun x c => (hN N ^ 3)⁻¹ * (wt6 c)⁻¹ * fderiv ℝ (fun q : ParF N × MetF N =>
      canonicalHamiltonian χ 0 sqrtTriad (statAst χ R) (zFlat N) q.1 q.2)
        ((X.1, lam.1, lam.2), X.2) (((0 : MetF N), 0, 0), metDir x c),
   fun x c => -((hN N ^ 3)⁻¹ * (wt6 c)⁻¹ * fderiv ℝ (fun q : ParF N × MetF N =>
      canonicalHamiltonian χ 0 sqrtTriad (statAst χ R) (zFlat N) q.1 q.2)
        ((X.1, lam.1, lam.2), X.2) ((metDir x c, 0, 0), 0)))

/-- `M_h = D_λ P_h`. -/
def Mcan (χ R : ℝ) (X : MetF N × MetF N) (lam : (Site N → ℝ) × (Site N → Fin 3 → ℝ)) :=
  fderiv ℝ (Pcan χ R X) lam

/-- `B_h = D_X P_h F_h^{can}`. -/
def Bcan (χ R : ℝ) (X : MetF N × MetF N) (lam : (Site N → ℝ) × (Site N → Fin 3 → ℝ)) :
    (Site N → ℝ) × (Site N → Fin 3 → ℝ) :=
  fderiv ℝ (fun Y => Pcan χ R Y lam) X (Fcan χ R X lam)

/-- The original initial constraint map is the lapse–shift gradient of the same canonical
Hamiltonian at unit lapse and zero shift: `𝒞_h(X) = (-P_N, P_β)(X, 1, 0)`
(`eq:main-action-initial-constraints`). -/
theorem initialConstraint_eq_Pcan (χ R : ℝ) (X : MetF N × MetF N) :
    initialConstraint χ 0 sqrtTriad (statAst χ R) (zFlat N) X =
      (-(Pcan χ R X ((fun _ => 1), (fun _ => 0))).1, (Pcan χ R X ((fun _ => 1), (fun _ => 0))).2) :=
  rfl

/-! ### Assembly -/

/-- **`thm:supp-exact-action-provenance`, clauses (ii)–(iv) at flat data (`χ = 1`, `Λ = 0`),
with the chart hypotheses discharged.**  There is an `N`-independent `ε > 0` such that on every
regulator, for `0 < R`, `hR ≤ ε`:
(ii) the stationary connection of the phase-compatible action is analytic near flat data, solves
the stationary row in the closed `R`-ball and vanishes at flat data (`FlatChart`);
(iii) the reduced Lagrangian (stationary elimination with the symmetric-square-root ADM triad) is
on a Legendre chart at flat data (DeWitt velocity Hessian), and the canonical Hamiltonian
(`eq:supp-exact-H`) is analytic there;
(iv) the canonical Hamiltonian vanishes at flat data with zero gradient and quadratic part `H₂`
(`eq:supp-exact-H2`); the original initial constraint map vanishes at flat data, is analytic
there and its linearization is the Fierz–Pauli rows `(R₁(u), -2δ_jπ^{ij})`, which for odd `N`
is `InitialConstraintLinearRange.Lh` after complexification. -/
theorem exact_action_provenance :
    ∃ ε > 0, ∀ (N : ℕ) [NeZero N] (R : ℝ), 0 < R → hN N * R ≤ ε →
      (∃ U : Set (CoP N), FlatChart 1 R U) ∧
      LegendreChart (redLagr 1 0 sqrtTriad (statAst (N := N) 1 R)) (zFlat N) ∧
      AnalyticAt ℝ (canonH (N := N) 1 R) (qFlat N) ∧
      canonH (N := N) 1 R (qFlat N) = 0 ∧ fderiv ℝ (canonH (N := N) 1 R) (qFlat N) = 0 ∧
      (∀ u p : MetF N, fderiv ℝ (fderiv ℝ (canonH 1 R)) (qFlat N) ((u, 0, 0), p) ((u, 0, 0), p) =
        2 * H2 u p) ∧
      (∀ u p : MetF N, fderiv ℝ (fderiv ℝ (canonHres 1 R)) 0 (u, p) (u, p) = 2 * H2 u p) ∧
      Cmap (N := N) 1 R 0 = 0 ∧ AnalyticAt ℝ (Cmap (N := N) 1 R) 0 ∧
      (∀ u π : MetF N, fderiv ℝ (Cmap 1 R) 0 (u, π) = (R1F u, divF π)) ∧
      (Odd N → ∀ u π : MetF N, InitialConstraintLinearRange.Lh (cplx u, cplx π) =
        ((fun x => ((R1F u x : ℝ) : ℂ)), fun a x => ((divF π x a : ℝ) : ℂ))) := by
  obtain ⟨ε, hε, h⟩ := flat_chart 1 one_ne_zero
  refine ⟨ε, hε, fun N _ R hR hhR => ?_⟩
  obtain ⟨U, hU⟩ := h N R hR hhR
  obtain ⟨h0, h1, h2⟩ := canonicalHamiltonian_quadratic_part_one hU
  obtain ⟨c0, can, cder⟩ := fderiv_initialConstraint_flat hU one_ne_zero
  refine ⟨⟨U, hU⟩, legendreChart_flat hU one_ne_zero, analyticAt_canonH hU one_ne_zero, h0, h1, h2,
    (canonicalHamiltonian_restricted_quadratic hU).2.2, c0, can, fun u π => ?_,
    fun hNo u π => Lh_cplx hNo u π⟩
  rw [cder u π]
  simp

/-- The general-`χ` form of clause (iv): `D²𝓗_h(flat) = 2(χ⁻¹(‖p‖² - ½‖tr p‖²) + χ P(u))` and
`D𝒞_h(0)(u, π) = (χ R₁(u), -2δ_jπ^{ij})` (the display `eq:supp-exact-H2` is the case `χ = 1`). -/
theorem exact_action_provenance_chi (χ : ℝ) (hχ : χ ≠ 0) :
    ∃ ε > 0, ∀ (N : ℕ) [NeZero N] (R : ℝ), 0 < R → hN N * R ≤ ε →
      LegendreChart (redLagr χ 0 sqrtTriad (statAst (N := N) χ R)) (zFlat N) ∧
      canonH (N := N) χ R (qFlat N) = 0 ∧ fderiv ℝ (canonH (N := N) χ R) (qFlat N) = 0 ∧
      (∀ u p : MetF N, fderiv ℝ (fderiv ℝ (canonH χ R)) (qFlat N) ((u, 0, 0), p) ((u, 0, 0), p) =
        2 * (χ⁻¹ * kinH p + χ * potH u)) ∧
      (∀ u π : MetF N, fderiv ℝ (Cmap χ R) 0 (u, π) = (fun x => χ * R1F u x, divF π)) := by
  obtain ⟨ε, hε, h⟩ := flat_chart χ hχ
  refine ⟨ε, hε, fun N _ R hR hhR => ?_⟩
  obtain ⟨U, hU⟩ := h N R hR hhR
  obtain ⟨h0, h1, h2⟩ := canonicalHamiltonian_quadratic_part hU hχ
  exact ⟨legendreChart_flat hU hχ, h0, h1, h2, (fderiv_initialConstraint_flat hU hχ).2.2⟩

end RenewalGeometry.ExactPhaseAction.QuadJet
