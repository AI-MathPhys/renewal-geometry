/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactFierzPauliQuadratic

/-!
# The quadratic canonical Hamiltonian `H₂` of the actual action and the Fierz–Pauli rows
  (`eq:supp-exact-H2`, `thm:supp-exact-action-provenance` (iii)–(iv),
  `eq:main-action-initial-constraints`, `lem:supp-initial-calculus` (`DC_h(0) = L_h`);
  emergent-spacetime manuscript)

All objects are those of `ExactLegendreHamiltonian.lean` with the parameters instantiated
(`ExactReducedLagrangianJet.lean`): the triad is the symmetric square root (`sqrtTriad`), the
stationary connection is the selected zero `statAst χ R` of the stationary row, `Λ = 0`, and the
Legendre chart is based at flat data `zFlat` (`γ = I`, `N = 1`, `β = 0`, `V = 0`).

* `bilin_eq`: the Hessian `B = D²𝓛°_h(flat)` is the polarization of `2χ Q_FP`;
  `B_UV_V`, `B_UV_U`, `B_UV_N`, `B_UV_B`: its values on metric (`u`), velocity (`V`), lapse (`N`)
  and shift (`β`) directions.
* **`legendreChart_flat`**: the velocity Hessian at flat data is the DeWitt form
  `½χ h³ Σ (⟨V, V'⟩ - tr V tr V')`, which is invertible (`χ ≠ 0`): the Legendre-chart
  hypothesis of the manuscript holds at flat data.
* **`H2`** (`eq:supp-exact-H2`, verbatim on the odd grid, `‖f‖²_h = h³Σ_x|f(x)|²`):
  `H₂(u, p) = ‖p‖² - ½‖tr p‖² + ¼Σ_i‖δ_i u‖² - ½‖v‖² + ½⟨v, δt_u⟩ - ¼‖δt_u‖²`,
  `v_j = Σ_i δ_i u_{ij}`, `t_u = tr u`.
* **`canonicalHamiltonian_quadratic_part`** (clause (iv)): at flat data, unit lapse, zero shift,
  `Λ = 0`, the canonical Hamiltonian vanishes, has zero gradient, and its second derivative in
  `X = (u, p)` is `2 H₂^χ(u, p)` with `H₂^χ = χ⁻¹(‖p‖² - ½‖tr p‖²) + χ P(u)`; for `χ = 1` (the
  normalization the display requires) this is `2 H₂(u, p)` (`canonicalHamiltonian_quadratic_part_one`,
  also for the restricted map `X ↦ 𝓗_h(I + u, p, 1, 0)`).
* **`fderiv_initialConstraint_flat`** (`lem:supp-initial-calculus`, linear part): `𝒞_h(flat) = 0`,
  `𝒞_h` is analytic at flat data, and `D𝒞_h(0)(u, π) = (χ R₁(u), -2δ_jπ^{ij})`; for `χ = 1` and
  odd `N` the complexification is `InitialConstraintLinearRange.Lh` (`initialConstraint_linearization_eq_Lh`).
-/

open Filter Finset
open scoped Topology ContDiff

noncomputable section

set_option linter.unusedSectionVars false

namespace RenewalGeometry.ExactPhaseAction.QuadJet

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

open InitialConstraintLinearRange (sym6)
open OddPhaseDerivativeReal

variable {N : ℕ} [NeZero N]

/-! ### Directions and pointwise algebra -/

/-- The Frobenius pairing of two `Sym₃` coordinate vectors, `Σ_{pq} a_{pq} b_{pq}`. -/
def frob (a b : Fin 6 → ℝ) : ℝ := ∑ p, ∑ q, symMat a p q * symMat b p q

/-- The trace of a `Sym₃` coordinate vector. -/
def trS (a : Fin 6 → ℝ) : ℝ := ∑ p, symMat a p p

/-- A metric direction `((u, 0, 0), 0)`. -/
def dirU (u : MetF N) : ParF N × MetF N := ((u, 0, 0), 0)
/-- A velocity direction `((0, 0, 0), V)`. -/
def dirV (V : MetF N) : ParF N × MetF N := ((0, 0, 0), V)
/-- A lapse direction `((0, n, 0), 0)`. -/
def dirN (n : Site N → ℝ) : ParF N × MetF N := ((0, n, 0), 0)
/-- A shift direction `((0, 0, β), 0)`. -/
def dirB (β : Site N → Fin 3 → ℝ) : ParF N × MetF N := ((0, 0, β), 0)

theorem pd_zero_field {E : Type*} [AddCommGroup E] [Module ℝ E] (i : Fin 3) :
    pd i (0 : Site N → E) = 0 := map_zero _

theorem pd_add_field {E : Type*} [AddCommGroup E] [Module ℝ E] (i : Fin 3) (f g : Site N → E) :
    pd i (f + g) = pd i f + pd i g := map_add _ _ _

/-- The pointwise potential `P(u)(x) = ¼Σ_i|δ_iu|² - ½|v|² + ½ v·δt - ¼|δt|²` in jet form. -/
def potJ (a : Fin 3 → Fin 6 → ℝ) : ℝ :=
  (1 / 4 : ℝ) * (∑ i, frob (a i) (a i)) - (1 / 2 : ℝ) * (∑ j, (∑ i, symMat (a i) i j) ^ 2) +
    (1 / 2 : ℝ) * (∑ j, (∑ i, symMat (a i) i j) * trS (a j)) - (1 / 4 : ℝ) * (∑ j, trS (a j) ^ 2)

/-- The quadratic form polarized: `B(v, w) = χ (Q(v + w) - Q(v) - Q(w))`. -/
theorem bilin_eq {χ R : ℝ} {U : Set (CoP N)} (hU : FlatChart χ R U) (hχ : χ ≠ 0)
    (v w : ParF N × MetF N) :
    fderiv ℝ (fderiv ℝ (redLagr χ 0 sqrtTriad (statAst χ R))) (zFlat N) v w =
      χ * (QFP (v + w) - QFP v - QFP w) := by
  have hL := (redLagr_jet_flat hU hχ).1
  have hsymm := (hL.contDiffAt (n := ω)).isSymmSndFDerivAt_of_omega
  have h := hess_redLagr_flat hU hχ (v + w)
  simp only [map_add, add_apply] at h
  rw [hess_redLagr_flat hU hχ v, hess_redLagr_flat hU hχ w, hsymm w v] at h
  linarith

/-! ### The Hessian on metric, velocity, lapse and shift directions -/

section Chart

variable {χ R : ℝ} {U : Set (CoP N)} (hU : FlatChart χ R U) (hχ : χ ≠ 0)
include hU hχ

/-- Velocity–velocity block: the DeWitt form `½χ h³ Σ (⟨V, V'⟩ - tr V tr V')`. -/
theorem B_V_V (V V' : MetF N) :
    fderiv ℝ (fderiv ℝ (redLagr χ 0 sqrtTriad (statAst χ R))) (zFlat N) (dirV V) (dirV V') =
      χ * (hN N ^ 3 * ∑ x, (1 / 2 : ℝ) * (frob (V x) (V' x) - trS (V x) * trS (V' x))) := by
  rw [bilin_eq hU hχ]
  congr 1
  simp only [QFP, dirV, Prod.mk_add_mk, add_zero, pd_zero_field, Pi.zero_apply]
  rw [← mul_sub, ← mul_sub, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [T1fun, frob, trS, symMat, sym6, Fin.sum_univ_three, Pi.add_apply]
  simp
  ring

/-- `(u, V)`–velocity block. -/
theorem B_UV_V (u w V' : MetF N) :
    fderiv ℝ (fderiv ℝ (redLagr χ 0 sqrtTriad (statAst χ R))) (zFlat N) (dirU u + dirV w)
        (dirV V') =
      χ * (hN N ^ 3 * ∑ x, (1 / 2 : ℝ) * (frob (w x) (V' x) - trS (w x) * trS (V' x))) := by
  rw [bilin_eq hU hχ]
  congr 1
  simp only [QFP, dirU, dirV, Prod.mk_add_mk, add_zero, zero_add, pd_zero_field, Pi.zero_apply]
  rw [← mul_sub, ← mul_sub, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [T1fun, frob, trS, symMat, sym6, Fin.sum_univ_three, Pi.add_apply]
  simp
  ring

/-- `(u, V)`–metric block: `-2χ h³ Σ P(u)`. -/
theorem B_UV_U (u w : MetF N) :
    fderiv ℝ (fderiv ℝ (redLagr χ 0 sqrtTriad (statAst χ R))) (zFlat N) (dirU u + dirV w)
        (dirU u) =
      χ * (hN N ^ 3 * ∑ x, (-2 : ℝ) * potJ (fun i => pd i u x)) := by
  rw [bilin_eq hU hχ]
  congr 1
  simp only [QFP, dirU, dirV, Prod.mk_add_mk, add_zero, zero_add, pd_zero_field, Pi.zero_apply,
    pd_add_field, Pi.add_apply]
  rw [← mul_sub, ← mul_sub, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [T1fun, potJ, frob, trS, symMat, sym6, Fin.sum_univ_three, Pi.add_apply]
  simp
  ring

/-- `(u, V)`–lapse block. -/
theorem B_UV_N (u w : MetF N) (n : Site N → ℝ) :
    fderiv ℝ (fderiv ℝ (redLagr χ 0 sqrtTriad (statAst χ R))) (zFlat N) (dirU u + dirV w)
        (dirN n) =
      χ * (hN N ^ 3 * ∑ x, (-(∑ i, pd i n x * ∑ j, symMat (pd j u x) i j) +
        ∑ i, pd i n x * trS (pd i u x))) := by
  rw [bilin_eq hU hχ]
  congr 1
  simp only [QFP, dirU, dirV, dirN, Prod.mk_add_mk, add_zero, zero_add, pd_zero_field,
    Pi.zero_apply]
  rw [← mul_sub, ← mul_sub, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [T1fun, trS, symMat, sym6, Fin.sum_univ_three]
  simp

/-- `(u, V)`–shift block: `-½χ h³ Σ (⟨V, L_δβ⟩ - tr V tr L_δβ)`. -/
theorem B_UV_B (u w : MetF N) (β : Site N → Fin 3 → ℝ) :
    fderiv ℝ (fderiv ℝ (redLagr χ 0 sqrtTriad (statAst χ R))) (zFlat N) (dirU u + dirV w)
        (dirB β) =
      χ * (hN N ^ 3 * ∑ x, (-(1 / 2 : ℝ)) * ((∑ p, ∑ q, symMat (w x) p q *
        (pd p β x q + pd q β x p)) - trS (w x) * ∑ p, (pd p β x p + pd p β x p))) := by
  rw [bilin_eq hU hχ]
  congr 1
  simp only [QFP, dirU, dirV, dirB, Prod.mk_add_mk, add_zero, zero_add, pd_zero_field,
    Pi.zero_apply]
  rw [← mul_sub, ← mul_sub, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [T1fun, frob, trS, symMat, sym6, Fin.sum_univ_three, Pi.add_apply]
  simp
  ring

end Chart

/-! ### Generic: second derivatives under affine substitution -/

section GenericAffine

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

/-- Second derivatives transform tensorially under an affine substitution `q ↦ c + M q`. -/
theorem fderiv_fderiv_affine {H : Y → ℝ} (c : Y) (M : X →L[ℝ] Y) {q₀ : X}
    (hH : AnalyticAt ℝ H (c + M q₀)) (δ δ' : X) :
    fderiv ℝ (fderiv ℝ (fun q => H (c + M q))) q₀ δ δ' =
      fderiv ℝ (fderiv ℝ H) (c + M q₀) (M δ) (M δ') := by
  have hA : HasFDerivAt (fun q : X => c + M q) M q₀ := (M.hasFDerivAt).const_add c
  have hcont : ContinuousAt (fun q : X => c + M q) q₀ := hA.continuousAt
  have hev := hcont.eventually hH.eventually_analyticAt
  have hf : AnalyticAt ℝ (fun q => H (c + M q)) q₀ :=
    AnalyticAt.comp (g := H) (f := fun q : X => c + M q) hH
      (analyticAt_const.add (M.analyticAt q₀))
  rw [fderiv_fderiv_apply_eq hf.fderiv.differentiableAt]
  have hK : (fun q => fderiv ℝ (fun q => H (c + M q)) q δ') =ᶠ[𝓝 q₀]
      fun q => fderiv ℝ H (c + M q) (M δ') := by
    filter_upwards [hev] with q hq
    have h1 : HasFDerivAt (fun q : X => c + M q) M q := (M.hasFDerivAt).const_add c
    have h2 := HasFDerivAt.comp (g := H) (f := fun q : X => c + M q) q
      hq.differentiableAt.hasFDerivAt h1
    have h2' : HasFDerivAt (fun q => H (c + M q)) (fderiv ℝ H (c + M q) ∘L M) q := h2
    rw [h2'.fderiv]
    rfl
  rw [hK.fderiv_eq]
  have hg : DifferentiableAt ℝ (fun p => fderiv ℝ H p (M δ')) (c + M q₀) :=
    hH.fderiv.differentiableAt.clm_apply (differentiableAt_const _)
  have h3 := HasFDerivAt.comp (g := fun p => fderiv ℝ H p (M δ')) (f := fun q : X => c + M q) q₀
    hg.hasFDerivAt hA
  have h3' : HasFDerivAt (fun q => fderiv ℝ H (c + M q) (M δ'))
      (fderiv ℝ (fun p => fderiv ℝ H p (M δ')) (c + M q₀) ∘L M) q₀ := h3
  rw [h3'.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  rw [fderiv_clm_apply hH.fderiv.differentiableAt (differentiableAt_const _)]
  simp

/-- Second derivatives under a continuous linear substitution. -/
theorem fderiv_fderiv_clm {H : Y → ℝ} (M : X →L[ℝ] Y) {q₀ : X} (hH : AnalyticAt ℝ H (M q₀))
    (δ δ' : X) :
    fderiv ℝ (fderiv ℝ (fun q => H (M q))) q₀ δ δ' = fderiv ℝ (fderiv ℝ H) (M q₀) (M δ) (M δ') := by
  have h := fderiv_fderiv_affine (0 : Y) M (q₀ := q₀) (by simpa using hH) δ δ'
  simpa using h

end GenericAffine

/-! ### The Legendre chart at flat data -/

theorem frob_dev (a : Fin 6 → ℝ) :
    frob a (a - (trS a / 2) • flatSym) - trS a * trS (a - (trS a / 2) • flatSym) = frob a a := by
  simp only [frob, trS, symMat, sym6, flatSym, Fin.sum_univ_three, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  simp
  ring

theorem frob_self_eq_zero {a : Fin 6 → ℝ} (h : frob a a = 0) : a = 0 := by
  have e : frob a a = a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 + 2 * a 3 ^ 2 + 2 * a 4 ^ 2 + 2 * a 5 ^ 2 := by
    simp only [frob, symMat, sym6, Fin.sum_univ_three]; simp; ring
  rw [e] at h
  have p0 := sq_nonneg (a 0)
  have p1 := sq_nonneg (a 1)
  have p2 := sq_nonneg (a 2)
  have p3 := sq_nonneg (a 3)
  have p4 := sq_nonneg (a 4)
  have p5 := sq_nonneg (a 5)
  have z0 : a 0 ^ 2 = 0 := by linarith
  have z1 : a 1 ^ 2 = 0 := by linarith
  have z2 : a 2 ^ 2 = 0 := by linarith
  have z3 : a 3 ^ 2 = 0 := by linarith
  have z4 : a 4 ^ 2 = 0 := by linarith
  have z5 : a 5 ^ 2 = 0 := by linarith
  have hz : ∀ t : ℝ, t ^ 2 = 0 → t = 0 := fun t ht => pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ht
  funext c
  fin_cases c
  exacts [hz _ z0, hz _ z1, hz _ z2, hz _ z3, hz _ z4, hz _ z5]

theorem frob_self_nonneg (a : Fin 6 → ℝ) : 0 ≤ frob a a := by
  unfold frob
  exact Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => mul_self_nonneg _

section Chart

variable {χ R : ℝ} {U : Set (CoP N)} (hU : FlatChart χ R U) (hχ : χ ≠ 0)
include hU hχ

/-- **The velocity Hessian at flat data is the DeWitt form.** -/
theorem velHess_flat (V V' : MetF N) :
    velHess (redLagr χ 0 sqrtTriad (statAst χ R)) (zFlat N) V V' =
      χ * (hN N ^ 3 * ∑ x, (1 / 2 : ℝ) * (frob (V x) (V' x) - trS (V x) * trS (V' x))) := by
  rw [velHess_apply (redLagr_jet_flat hU hχ).1]
  exact B_V_V hU hχ V V'

/-- **The Legendre chart hypothesis holds at flat data** (`χ ≠ 0`): the reduced Lagrangian of the
actual action is analytic there and its velocity Hessian (the DeWitt form) is invertible. -/
theorem legendreChart_flat :
    LegendreChart (redLagr χ 0 sqrtTriad (statAst χ R)) (zFlat N) := by
  refine ⟨(redLagr_jet_flat hU hχ).1, ?_⟩
  set T := velHess (redLagr χ 0 sqrtTriad (statAst χ R)) (zFlat N) with hT
  have hinj : Function.Injective T := by
    rw [← T.coe_coe, ← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro V hV
    have h1 := congrArg (fun ℓ : MetF N →L[ℝ] ℝ => ℓ (fun x => V x - (trS (V x) / 2) • flatSym))
      (show T V = 0 from hV)
    simp only [hT, velHess_flat hU hχ, frob_dev, zero_apply] at h1
    have hh : 0 < hN N ^ 3 := pow_pos hN_pos 3
    have hsum : ∑ x, (1 / 2 : ℝ) * frob (V x) (V x) = 0 := by
      have := mul_eq_zero.1 h1
      rcases this with h | h
      · exact absurd h hχ
      · rcases mul_eq_zero.1 h with h' | h'
        · exact absurd h' hh.ne'
        · exact h'
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => mul_nonneg (by norm_num)
      (frob_self_nonneg (V x)))).1 hsum
    funext x
    have := hall x (Finset.mem_univ x)
    exact frob_self_eq_zero (by linarith)
  have hdim : Module.finrank ℝ (MetF N) = Module.finrank ℝ (MetF N →L[ℝ] ℝ) := by
    rw [← (LinearMap.toContinuousLinearMap : (MetF N →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _).finrank_eq,
      Subspace.dual_finrank_eq]
  let e := LinearMap.linearEquivOfInjective T.toLinearMap hinj hdim
  exact ⟨e.toContinuousLinearEquiv, by ext; rfl⟩

end Chart

/-! ### The quadratic canonical Hamiltonian `H₂` -/

/-- The divergence `v_j = Σ_i δ_i u_{ij}` at a site. -/
def divU (u : MetF N) (x : Site N) (j : Fin 3) : ℝ := ∑ i, symMat (pd i u x) i j

/-- The gradient of the trace, `(δ t_u)_j = δ_j tr u` at a site. -/
def gradTr (u : MetF N) (x : Site N) (j : Fin 3) : ℝ := pd j (fun y => trS (u y)) x

/-- **The unit-multiplier quadratic Hamiltonian `eq:supp-exact-H2`** on the odd grid
(`‖f‖²_h = h³ Σ_x |f(x)|²`, Frobenius norms for tensors, `X = (u, p)` in `Sym₃` coordinates):
`H₂(u, p) = ‖p‖² - ½‖tr p‖² + ¼Σ_i‖δ_i u‖² - ½‖v‖² + ½⟨v, δt_u⟩ - ¼‖δt_u‖²`. -/
def H2 (u p : MetF N) : ℝ :=
  hN N ^ 3 * ∑ x, frob (p x) (p x) - (1 / 2 : ℝ) * (hN N ^ 3 * ∑ x, trS (p x) ^ 2) +
    (1 / 4 : ℝ) * ∑ i, (hN N ^ 3 * ∑ x, frob (pd i u x) (pd i u x)) -
    (1 / 2 : ℝ) * (hN N ^ 3 * ∑ x, ∑ j, divU u x j ^ 2) +
    (1 / 2 : ℝ) * (hN N ^ 3 * ∑ x, ∑ j, divU u x j * gradTr u x j) -
    (1 / 4 : ℝ) * (hN N ^ 3 * ∑ x, ∑ j, gradTr u x j ^ 2)

/-- The kinetic part `‖p‖² - ½‖tr p‖²`. -/
def kinH (p : MetF N) : ℝ :=
  hN N ^ 3 * ∑ x, frob (p x) (p x) - (1 / 2 : ℝ) * (hN N ^ 3 * ∑ x, trS (p x) ^ 2)

/-- The potential part `P(u) = ¼Σ_i‖δ_i u‖² - ½‖v‖² + ½⟨v, δt_u⟩ - ¼‖δt_u‖²`. -/
def potH (u : MetF N) : ℝ := hN N ^ 3 * ∑ x, potJ (fun i => pd i u x)

/-- `tr` as a linear functional. -/
def trSLin : (Fin 6 → ℝ) →ₗ[ℝ] ℝ where
  toFun := trS
  map_add' a b := by simp [trS, symMat, Finset.sum_add_distrib]
  map_smul' c a := by simp [trS, symMat, Finset.mul_sum]

theorem gradTr_eq (u : MetF N) (x : Site N) (j : Fin 3) : gradTr u x j = trS (pd j u x) :=
  congrFun (pd_map j trSLin u) x

theorem H2_eq (u p : MetF N) : H2 u p = kinH p + potH u := by
  have hT3 : ∑ i, (hN N ^ 3 * ∑ x, frob (pd i u x) (pd i u x)) =
      hN N ^ 3 * ∑ x, ∑ i, frob (pd i u x) (pd i u x) := by
    rw [← Finset.mul_sum, Finset.sum_comm]
  have hpot : potH u = hN N ^ 3 * ((1 / 4 : ℝ) * (∑ x, ∑ i, frob (pd i u x) (pd i u x)) -
      (1 / 2 : ℝ) * (∑ x, ∑ j, divU u x j ^ 2) + (1 / 2 : ℝ) * (∑ x, ∑ j, divU u x j * gradTr u x j) -
      (1 / 4 : ℝ) * (∑ x, ∑ j, gradTr u x j ^ 2)) := by
    simp only [potH, potJ, gradTr_eq, divU, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum]
  rw [H2, kinH, hpot, hT3]
  ring

/-- The canonical Hamiltonian of the actual action (`Λ = 0`, symmetric-square-root triad,
stationary connection `statAst χ R`), Legendre chart based at flat data, as a function of
`((γ, N, β), π)`. -/
def canonH (χ R : ℝ) (q : ParF N × MetF N) : ℝ :=
  canonicalHamiltonian χ 0 sqrtTriad (statAst χ R) (zFlat N) q.1 q.2

/-- Flat canonical data: `γ = I`, `N = 1`, `β = 0`, `π = 0`. -/
def qFlat (N : ℕ) [NeZero N] : ParF N × MetF N := ((zFlat N).1, 0)

/-- The momentum map `(p, π) ↦ (p, ⟨π, ·⟩_h)`. -/
def momMap : (ParF N × MetF N) →L[ℝ] (ParF N × (MetF N →L[ℝ] ℝ)) :=
  (ContinuousLinearMap.fst ℝ (ParF N) (MetF N)).prod
    (pairCov.comp (ContinuousLinearMap.snd ℝ (ParF N) (MetF N)))

theorem canonH_eq (χ R : ℝ) : canonH (N := N) χ R = fun q =>
    legendreHam (redLagr χ 0 sqrtTriad (statAst χ R)) (zFlat N) (momMap q) := by
  funext q; simp [canonH, canonicalHamiltonian, momMap]

/-- The development `2p - (tr p) I` (the inverse DeWitt map up to `χ`). -/
def devP (p : Fin 6 → ℝ) : Fin 6 → ℝ := (2 : ℝ) • p - trS p • flatSym

theorem frob_devP (χ : ℝ) (hχ : χ ≠ 0) (p v : Fin 6 → ℝ) :
    χ * ((1 / 2 : ℝ) * (frob (χ⁻¹ • devP p) v - trS (χ⁻¹ • devP p) * trS v)) = frob p v := by
  simp only [frob, trS, devP, symMat, sym6, flatSym, Fin.sum_univ_three, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  simp
  field_simp
  ring

theorem frob_p_devP (χ : ℝ) (p : Fin 6 → ℝ) :
    frob p (χ⁻¹ • devP p) = χ⁻¹ * (2 * frob p p - trS p ^ 2) := by
  simp only [frob, trS, devP, symMat, sym6, flatSym, Fin.sum_univ_three, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  simp
  ring

section Chart

variable {χ R : ℝ} {U : Set (CoP N)} (hU : FlatChart χ R U) (hχ : χ ≠ 0)
include hU hχ

theorem velMom_flat :
    velMom (redLagr χ 0 sqrtTriad (statAst χ R)) (zFlat N) = 0 := by
  simp [velMom, (redLagr_jet_flat hU hχ).2.2.1]

theorem momMap_qFlat :
    momMap (qFlat N) = ((zFlat N).1, velMom (redLagr χ 0 sqrtTriad (statAst χ R)) (zFlat N)) := by
  rw [velMom_flat hU hχ]
  simp [momMap, qFlat]

/-- **Clause (iv) of `thm:supp-exact-action-provenance`** (general `χ ≠ 0`): at flat data with
unit lapse, zero shift and `Λ = 0`, the canonical Hamiltonian of the actual action vanishes, has
zero derivative, and its second derivative along `X = (u, p)` (metric perturbation `γ = I + u`,
momentum `p`, multipliers fixed) is `2(χ⁻¹(‖p‖² - ½‖tr p‖²) + χ P(u))`. -/
theorem canonicalHamiltonian_quadratic_part :
    canonH χ R (qFlat N) = 0 ∧ fderiv ℝ (canonH χ R) (qFlat N) = 0 ∧
      ∀ u p : MetF N, fderiv ℝ (fderiv ℝ (canonH χ R)) (qFlat N) ((u, 0, 0), p) ((u, 0, 0), p) =
        2 * (χ⁻¹ * kinH p + χ * potH u) := by
  have hc := legendreChart_flat hU hχ
  have hjet := redLagr_jet_flat hU hχ
  have hbase := momMap_qFlat hU hχ
  have hHan : AnalyticAt ℝ (legendreHam (redLagr χ 0 sqrtTriad (statAst (N := N) χ R)) (zFlat N)) (momMap (qFlat N)) := by
    rw [hbase]; exact analyticAt_legendreHam hc
  refine ⟨?_, ?_, fun u p => ?_⟩
  · rw [canonH_eq]
    show legendreHam (redLagr χ 0 sqrtTriad (statAst (N := N) χ R)) (zFlat N) (momMap (qFlat N)) = 0
    rw [hbase, legendreHam_apply_base hc, velMom_flat hU hχ, hjet.2.1]
    simp
  · rw [canonH_eq]
    have h : HasFDerivAt (fun q => legendreHam (redLagr χ 0 sqrtTriad (statAst (N := N) χ R))
        (zFlat N) (momMap q))
        (fderiv ℝ (legendreHam (redLagr χ 0 sqrtTriad (statAst (N := N) χ R)) (zFlat N))
          (momMap (qFlat N)) ∘L momMap) (qFlat N) :=
      HasFDerivAt.comp (g := legendreHam (redLagr χ 0 sqrtTriad (statAst (N := N) χ R)) (zFlat N))
        (f := fun q : ParF N × MetF N => momMap q) (qFlat N) hHan.differentiableAt.hasFDerivAt
        momMap.hasFDerivAt
    have h' := h
    rw [h'.fderiv]
    refine ContinuousLinearMap.ext fun δ => ?_
    rw [ContinuousLinearMap.comp_apply, hbase, fderiv_legendreHam_base hc, hjet.2.2.1]
    simp [zFlat]
  · rw [canonH_eq]
    refine (fderiv_fderiv_clm momMap hHan ((u, 0, 0), p) ((u, 0, 0), p)).trans ?_
    rw [hbase]
    set w : MetF N := fun x => χ⁻¹ • devP (p x) with hw
    have hwv : ∀ v : MetF N, fderiv ℝ (fderiv ℝ (redLagr χ 0 sqrtTriad (statAst (N := N) χ R))) (zFlat N) ((u, 0, 0), w) (0, v) =
        (momMap ((u, 0, 0), p) : ParF N × (MetF N →L[ℝ] ℝ)).2 v := by
      intro v
      have e1 : (((u, 0, 0), w) : ParF N × MetF N) = dirU u + dirV w := by
        simp [dirU, dirV]
      have e2 : ((0 : ParF N), v) = dirV v := rfl
      rw [e1, e2, B_UV_V hU hχ]
      show χ * (hN N ^ 3 * ∑ x, (1 / 2 : ℝ) * (frob (w x) (v x) - trS (w x) * trS (v x))) =
        pairH p v
      rw [pairH, ← mul_assoc, mul_comm χ, mul_assoc, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hw]
      exact frob_devP χ hχ (p x) (v x)
    rw [fderiv_fderiv_legendreHam hc _ _ w hwv]
    have e1 : (((u, 0, 0), w) : ParF N × MetF N) = dirU u + dirV w := by simp [dirU, dirV]
    have e3 : (momMap ((u, 0, 0), p) : ParF N × (MetF N →L[ℝ] ℝ)).1 = (u, 0, 0) := rfl
    rw [e3, show ((((u, 0, 0) : ParF N), (0 : MetF N)) : ParF N × MetF N) = dirU u from rfl]
    have e4 : (momMap ((u, 0, 0), p) : ParF N × (MetF N →L[ℝ] ℝ)).2 w = pairH p w := rfl
    rw [e4, show ((((u, 0, 0) : ParF N), w) : ParF N × MetF N) = dirU u + dirV w from e1,
      B_UV_U hU hχ]
    simp only [pairH, kinH, potH, hw]
    have hfrob : ∀ x, ∑ i, ∑ j, symMat (p x) i j * symMat (χ⁻¹ • devP (p x)) i j =
        χ⁻¹ * (2 * frob (p x) (p x) - trS (p x) ^ 2) := fun x => frob_p_devP χ (p x)
    simp only [hfrob, ← Finset.mul_sum, Finset.sum_sub_distrib]
    ring

end Chart

/-- **Clause (iv), the displayed normalization `χ = 1`**: the quadratic part of the canonical
Hamiltonian at flat data is exactly `H₂` of `eq:supp-exact-H2`:
`𝓗_h(flat) = 0`, `D𝓗_h(flat) = 0`, `D²𝓗_h(flat)((u, p), (u, p)) = 2 H₂(u, p)`. -/
theorem canonicalHamiltonian_quadratic_part_one {U : Set (CoP N)} {R : ℝ}
    (hU1 : FlatChart 1 R U) :
    canonH 1 R (qFlat N) = 0 ∧ fderiv ℝ (canonH 1 R) (qFlat N) = 0 ∧
      ∀ u p : MetF N, fderiv ℝ (fderiv ℝ (canonH 1 R)) (qFlat N) ((u, 0, 0), p) ((u, 0, 0), p) =
        2 * H2 u p := by
  obtain ⟨h0, h1, h2⟩ := canonicalHamiltonian_quadratic_part hU1 one_ne_zero
  refine ⟨h0, h1, fun u p => ?_⟩
  rw [h2, H2_eq]
  simp

/-! ### The lapse–shift rows: `D𝒞_h(0) = L_h` -/

/-- The embedding `X = (u, p) ↦ ((u, 0, 0), p)` of canonical data at fixed multipliers. -/
def iotaX : (MetF N × MetF N) →L[ℝ] (ParF N × MetF N) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => ((X.1, 0, 0), X.2)
      map_add' := fun X Y => by simp
      map_smul' := fun c X => by simp }

@[simp] theorem iotaX_apply (X : MetF N × MetF N) : iotaX X = ((X.1, 0, 0), X.2) := rfl

/-- The Legendre velocity of a momentum `π` at flat data: `χ⁻¹(2π - tr π I)`. -/
def wOf (χ : ℝ) (π : MetF N) : MetF N := fun x => χ⁻¹ • devP (π x)

/-- The scalar row `R₁(u) = Σ_{ij} δ_iδ_j u_{ij} - Σ_i δ_i² tr u` (`eq:supp-initial-linear-map`). -/
def R1F (u : MetF N) (x : Site N) : ℝ :=
  (∑ i, ∑ j, pd i (pd j (fun y => symMat (u y) i j)) x) - ∑ i, pd i (pd i (fun y => trS (u y))) x

/-- The vector row `-2 δ_j π^{ja}` (`eq:supp-initial-linear-map`). -/
def divF (π : MetF N) (x : Site N) (a : Fin 3) : ℝ :=
  -2 * ∑ j, pd j (fun y => symMat (π y) j a) x

/-- The initial constraint map as a function of `X = (u, π)`, `γ = I + u` (Legendre chart at
flat data). -/
def Cmap (χ R : ℝ) (X : MetF N × MetF N) : (Site N → ℝ) × (Site N → Fin 3 → ℝ) :=
  initialConstraint χ 0 sqrtTriad (statAst χ R) (zFlat N) (flatMet N + X.1, X.2)

theorem refMult_add (X : MetF N × MetF N) :
    ((refMult (flatMet N + X.1), X.2) : ParF N × MetF N) = qFlat N + iotaX X := by
  ext <;> simp [refMult, qFlat, zFlat]

theorem Cmap_eq (χ R : ℝ) (X : MetF N × MetF N) :
    Cmap χ R X = (fun x => -((hN N ^ 3)⁻¹ * fderiv ℝ (canonH χ R) (qFlat N + iotaX X) (lapseDir x)),
      fun x a => (hN N ^ 3)⁻¹ * fderiv ℝ (canonH χ R) (qFlat N + iotaX X) (shiftDir x a)) := by
  simp only [Cmap, initialConstraint, ← refMult_add]
  rfl

theorem sum_pd_single_mul (i : Fin 3) (F : Site N → ℝ) (x : Site N) :
    ∑ y, pd i (Pi.single x (1 : ℝ)) y * F y = -pd i F x := by
  have h := pd_skew i (LinearMap.mul ℝ ℝ) (Pi.single x (1 : ℝ)) F
  simp only [LinearMap.mul_apply'] at h
  rw [h]
  congr 1
  simp [Pi.single_apply]

theorem sum_mul_pd_single (i : Fin 3) (F : Site N → ℝ) (x : Site N) :
    ∑ y, F y * pd i (Pi.single x (1 : ℝ)) y = -pd i F x := by
  rw [← sum_pd_single_mul]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem pd_shift_single (p : Fin 3) (x : Site N) (a q : Fin 3) (y : Site N) :
    pd p ((Pi.single x (Pi.single a (1 : ℝ)) : Site N → Fin 3 → ℝ)) y q =
      (Pi.single a (1 : ℝ) : Fin 3 → ℝ) q * pd p (Pi.single x (1 : ℝ)) y := by
  rw [pd_pi_apply]
  have e : (fun z : Site N => ((Pi.single x (Pi.single a (1 : ℝ)) : Site N → Fin 3 → ℝ) : Site N → Fin 3 → ℝ) z q) =
      (Pi.single a (1 : ℝ) : Fin 3 → ℝ) q • (Pi.single x (1 : ℝ) : Site N → ℝ) := by
    funext z
    by_cases hz : z = x
    · subst hz; simp
    · simp [hz]
  rw [e, map_smul]
  rfl

theorem symMat_pd (u : MetF N) (j : Fin 3) (y : Site N) (p q : Fin 3) :
    symMat (pd j u y) p q = pd j (fun z => symMat (u z) p q) y := by
  simp only [symMat]
  rw [pd_pi_apply]

theorem shift_site_identity (χ : ℝ) (hχ : χ ≠ 0) (π : Fin 6 → ℝ) (b : Fin 3 → Fin 3 → ℝ) :
    -χ * ((-(1 / 2 : ℝ)) * ((∑ p, ∑ q, symMat (χ⁻¹ • devP π) p q * (b p q + b q p)) -
      trS (χ⁻¹ • devP π) * ∑ p, (b p p + b p p))) =
      2 * ∑ p, ∑ q, symMat π p q * b p q := by
  simp only [devP, symMat, sym6, trS, flatSym, Fin.sum_univ_three, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  simp
  field_simp
  ring

section Chart

variable {χ R : ℝ} {U : Set (CoP N)} (hU : FlatChart χ R U) (hχ : χ ≠ 0)
include hU hχ

theorem analyticAt_canonH : AnalyticAt ℝ (canonH χ R) (qFlat N) := by
  have hc := legendreChart_flat hU hχ
  have h := analyticAt_legendreHam hc
  rw [← momMap_qFlat hU hχ] at h
  rw [canonH_eq]
  exact AnalyticAt.comp (g := legendreHam (redLagr χ 0 sqrtTriad (statAst (N := N) χ R)) (zFlat N))
    (f := ⇑momMap) h (momMap.analyticAt (qFlat N))

/-- The linearized Legendre velocity: `D²𝓛°_h(flat)((u, 0, 0), w(π))(0, v) = ⟨π, v⟩_h`. -/
theorem hess_redLagr_mom (u π v : MetF N) :
    fderiv ℝ (fderiv ℝ (redLagr χ 0 sqrtTriad (statAst χ R))) (zFlat N) ((u, 0, 0), wOf χ π)
      (0, v) = pairH π v := by
  have e1 : (((u, 0, 0), wOf χ π) : ParF N × MetF N) = dirU u + dirV (wOf χ π) := by
    simp [dirU, dirV]
  have e2 : ((0 : ParF N), v) = dirV v := rfl
  rw [e1, e2, B_UV_V hU hχ, pairH, ← mul_assoc, mul_comm χ, mul_assoc, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  exact frob_devP χ hχ (π x) (v x)

/-- **Second derivative of the canonical Hamiltonian at flat data**, in a direction with fixed
multipliers: `D²𝓗_h(flat)(((u,0,0), π), d) = ⟨d_π, w(π)⟩_h - D²𝓛°_h((u,0,0), w(π))(d_p, 0)`. -/
theorem hess_canonH (u π : MetF N) (d : ParF N × MetF N) :
    fderiv ℝ (fderiv ℝ (canonH χ R)) (qFlat N) ((u, 0, 0), π) d =
      pairH d.2 (wOf χ π) -
        fderiv ℝ (fderiv ℝ (redLagr χ 0 sqrtTriad (statAst χ R))) (zFlat N)
          ((u, 0, 0), wOf χ π) (d.1, 0) := by
  have hc := legendreChart_flat hU hχ
  have hHan : AnalyticAt ℝ (legendreHam (redLagr χ 0 sqrtTriad (statAst (N := N) χ R)) (zFlat N))
      (momMap (qFlat N)) := by
    rw [momMap_qFlat hU hχ]; exact analyticAt_legendreHam hc
  rw [canonH_eq]
  refine (fderiv_fderiv_clm momMap hHan ((u, 0, 0), π) d).trans ?_
  rw [momMap_qFlat hU hχ]
  rw [fderiv_fderiv_legendreHam hc _ _ (wOf χ π) (fun v => hess_redLagr_mom hU hχ u π v)]
  rfl

/-- **`lem:supp-initial-calculus`, value and linearization**: at flat data the original initial
constraint map vanishes, is analytic, and its derivative is `D𝒞_h(0)(u, π) = (χ R₁(u), -2δ_jπ^{ij})`
(the Fierz–Pauli rows; `χ = 1` is the normalization of `eq:supp-initial-linear-map`). -/
theorem fderiv_initialConstraint_flat :
    Cmap χ R (0 : MetF N × MetF N) = 0 ∧
      AnalyticAt ℝ (Cmap χ R) (0 : MetF N × MetF N) ∧
      ∀ u π : MetF N, fderiv ℝ (Cmap χ R) 0 (u, π) = (fun x => χ * R1F u x, divF π) := by
  have hH := analyticAt_canonH hU hχ
  have hD0 : fderiv ℝ (canonH χ R) (qFlat N) = 0 := (canonicalHamiltonian_quadratic_part hU hχ).2.1
  have hq0 : qFlat N + iotaX (0 : MetF N × MetF N) = qFlat N := by simp
  -- analyticity of `X ↦ D𝓗_h(qFlat + ι X) d`
  have hgA : ∀ d : ParF N × MetF N, AnalyticAt ℝ
      (fun X : MetF N × MetF N => fderiv ℝ (canonH χ R) (qFlat N + iotaX X) d) 0 := by
    intro d
    have h1 : AnalyticAt ℝ (fun X : MetF N × MetF N => qFlat N + iotaX X) 0 :=
      analyticAt_const.add (iotaX.analyticAt (0 : MetF N × MetF N))
    have h2 : AnalyticAt ℝ (fderiv ℝ (canonH χ R)) ((fun X : MetF N × MetF N => qFlat N + iotaX X) 0) := by
      show AnalyticAt ℝ (fderiv ℝ (canonH (N := N) χ R)) (qFlat N + iotaX (0 : MetF N × MetF N))
      rw [hq0]; exact hH.fderiv
    have h3 := AnalyticAt.comp (g := fderiv ℝ (canonH χ R))
      (f := fun X : MetF N × MetF N => qFlat N + iotaX X) h2 h1
    exact AnalyticAt.comp
      (g := ⇑(ContinuousLinearMap.apply ℝ ℝ d : ((ParF N × MetF N) →L[ℝ] ℝ) →L[ℝ] ℝ))
      (f := fun X : MetF N × MetF N => fderiv ℝ (canonH χ R) (qFlat N + iotaX X))
      ((ContinuousLinearMap.apply ℝ ℝ d : ((ParF N × MetF N) →L[ℝ] ℝ) →L[ℝ] ℝ).analyticAt _) h3
  have hCeq : Cmap χ R = fun X => (fun x => -((hN N ^ 3)⁻¹ *
      fderiv ℝ (canonH χ R) (qFlat N + iotaX X) (lapseDir x)),
      fun x a => (hN N ^ 3)⁻¹ * fderiv ℝ (canonH χ R) (qFlat N + iotaX X) (shiftDir x a)) :=
    funext (Cmap_eq χ R)
  -- derivative of the scalar rows
  have hgD : ∀ d : ParF N × MetF N, HasFDerivAt
      (fun X : MetF N × MetF N => fderiv ℝ (canonH χ R) (qFlat N + iotaX X) d)
      ((ContinuousLinearMap.apply ℝ ℝ d : ((ParF N × MetF N) →L[ℝ] ℝ) →L[ℝ] ℝ).comp
        ((fderiv ℝ (fderiv ℝ (canonH χ R)) (qFlat N)).comp iotaX)) 0 := by
    intro d
    have h1 : HasFDerivAt (fun X : MetF N × MetF N => qFlat N + iotaX X) iotaX 0 :=
      (iotaX.hasFDerivAt).const_add _
    have h2 : HasFDerivAt (fderiv ℝ (canonH χ R)) (fderiv ℝ (fderiv ℝ (canonH χ R)) (qFlat N))
        ((fun X : MetF N × MetF N => qFlat N + iotaX X) 0) := by
      show HasFDerivAt _ _ (qFlat N + iotaX (0 : MetF N × MetF N))
      rw [hq0]; exact hH.fderiv.differentiableAt.hasFDerivAt
    have h3 := HasFDerivAt.comp (g := fderiv ℝ (canonH χ R))
      (f := fun X : MetF N × MetF N => qFlat N + iotaX X) 0 h2 h1
    exact HasFDerivAt.comp (g := ⇑(ContinuousLinearMap.apply ℝ ℝ d : ((ParF N × MetF N) →L[ℝ] ℝ) →L[ℝ] ℝ))
      (f := fun X : MetF N × MetF N => fderiv ℝ (canonH χ R) (qFlat N + iotaX X)) 0
      (ContinuousLinearMap.hasFDerivAt _) h3
  refine ⟨?_, ?_, fun u π => ?_⟩
  · rw [Cmap_eq, hq0, hD0]
    ext <;> simp
  · rw [hCeq]
    refine AnalyticAt.prod (AnalyticAt.pi fun x => ((analyticAt_const.mul (hgA _)).neg))
      (AnalyticAt.pi fun x => AnalyticAt.pi fun a => analyticAt_const.mul (hgA _))
  · have hN' : HasFDerivAt (fun X : MetF N × MetF N => (Cmap χ R X).1)
        (ContinuousLinearMap.pi fun x => -((hN N ^ 3)⁻¹ •
          (ContinuousLinearMap.apply ℝ ℝ (lapseDir x)).comp
            ((fderiv ℝ (fderiv ℝ (canonH χ R)) (qFlat N)).comp iotaX))) 0 := by
      rw [hCeq]
      refine hasFDerivAt_pi.2 fun x => ?_
      exact ((hgD (lapseDir x)).const_mul ((hN N ^ 3)⁻¹)).neg
    have hB' : HasFDerivAt (fun X : MetF N × MetF N => (Cmap χ R X).2)
        (ContinuousLinearMap.pi fun x => ContinuousLinearMap.pi fun a => (hN N ^ 3)⁻¹ •
          (ContinuousLinearMap.apply ℝ ℝ (shiftDir x a)).comp
            ((fderiv ℝ (fderiv ℝ (canonH χ R)) (qFlat N)).comp iotaX)) 0 := by
      rw [hCeq]
      refine hasFDerivAt_pi.2 fun x => hasFDerivAt_pi.2 fun a => ?_
      exact (hgD (shiftDir x a)).const_mul ((hN N ^ 3)⁻¹)
    have hfull : HasFDerivAt (Cmap χ R) (ContinuousLinearMap.prod
        (ContinuousLinearMap.pi fun x => -((hN N ^ 3)⁻¹ •
          (ContinuousLinearMap.apply ℝ ℝ (lapseDir x)).comp
            ((fderiv ℝ (fderiv ℝ (canonH χ R)) (qFlat N)).comp iotaX)))
        (ContinuousLinearMap.pi fun x => ContinuousLinearMap.pi fun a => (hN N ^ 3)⁻¹ •
          (ContinuousLinearMap.apply ℝ ℝ (shiftDir x a)).comp
            ((fderiv ℝ (fderiv ℝ (canonH χ R)) (qFlat N)).comp iotaX))) 0 :=
      hN'.prodMk hB'
    rw [hfull.fderiv]
    have hh : hN N ^ 3 ≠ 0 := pow_ne_zero 3 hN_ne_zero
    refine Prod.ext (funext fun x => ?_) (funext fun x => funext fun a => ?_)
    · simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.pi_apply,
        neg_apply, smul_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, iotaX_apply,
        smul_eq_mul]
      rw [hess_canonH hU hχ u π (lapseDir x)]
      have e1 : (((u, 0, 0), wOf χ π) : ParF N × MetF N) = dirU u + dirV (wOf χ π) := by
        simp [dirU, dirV]
      rw [e1, show ((lapseDir x).1, (0 : MetF N)) = dirN (Pi.single x (1 : ℝ)) from rfl,
        B_UV_N hU hχ]
      have hp : pairH (lapseDir x).2 (wOf χ π) = 0 := by simp [pairH, lapseDir, symMat]
      have hc1 : ∀ i, ∑ y, pd i (Pi.single x (1 : ℝ)) y * ∑ j, symMat (pd j u y) i j =
          -∑ j, pd i (pd j (fun z => symMat (u z) i j)) x := by
        intro i
        simp only [symMat_pd, Finset.mul_sum]
        rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun j _ => sum_pd_single_mul i _ x
      have hc2 : ∀ i, ∑ y, pd i (Pi.single x (1 : ℝ)) y * trS (pd i u y) =
          -pd i (pd i (fun z => trS (u z))) x := by
        intro i
        rw [← sum_pd_single_mul]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← gradTr_eq]
        rfl
      have hS : ∑ y, (-(∑ i, pd i (Pi.single x (1 : ℝ)) y * ∑ j, symMat (pd j u y) i j) +
          ∑ i, pd i (Pi.single x (1 : ℝ)) y * trS (pd i u y)) = R1F u x := by
        rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_comm,
          Finset.sum_comm (f := fun y i => pd i (Pi.single x (1 : ℝ)) y * trS (pd i u y))]
        simp only [hc1, hc2, R1F, Finset.sum_neg_distrib]
        ring
      rw [hp, hS]
      have hinv : (hN N ^ 3)⁻¹ * hN N ^ 3 = 1 := inv_mul_cancel₀ hh
      linear_combination (χ * R1F u x) * hinv
    · simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.pi_apply,
        smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.apply_apply, iotaX_apply, smul_eq_mul]
      rw [hess_canonH hU hχ u π (shiftDir x a)]
      have e1 : (((u, 0, 0), wOf χ π) : ParF N × MetF N) = dirU u + dirV (wOf χ π) := by
        simp [dirU, dirV]
      rw [e1, show ((shiftDir x a).1, (0 : MetF N)) = dirB ((Pi.single x (Pi.single a (1 : ℝ)) : Site N → Fin 3 → ℝ))
        from rfl, B_UV_B hU hχ]
      have hp : pairH (shiftDir x a).2 (wOf χ π) = 0 := by simp [pairH, shiftDir, symMat]
      rw [hp, zero_sub]
      have hsite : ∀ y, -χ * ((-(1 / 2 : ℝ)) * ((∑ p, ∑ q, symMat (wOf χ π y) p q *
          (pd p ((Pi.single x (Pi.single a (1 : ℝ)) : Site N → Fin 3 → ℝ)) y q +
            pd q ((Pi.single x (Pi.single a (1 : ℝ)) : Site N → Fin 3 → ℝ)) y p)) -
          trS (wOf χ π y) * ∑ p, (pd p ((Pi.single x (Pi.single a (1 : ℝ)) : Site N → Fin 3 → ℝ)) y p +
            pd p ((Pi.single x (Pi.single a (1 : ℝ)) : Site N → Fin 3 → ℝ)) y p))) =
          2 * ∑ p, symMat (π y) p a * pd p (Pi.single x (1 : ℝ)) y := by
        intro y
        rw [wOf, shift_site_identity χ hχ (π y)
          (fun p q => pd p ((Pi.single x (Pi.single a (1 : ℝ)) : Site N → Fin 3 → ℝ)) y q)]
        congr 1
        refine Finset.sum_congr rfl fun p _ => ?_
        simp only [pd_shift_single, Pi.single_apply, ite_mul, one_mul, zero_mul, mul_ite,
          mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      have hinv : (hN N ^ 3)⁻¹ * hN N ^ 3 = 1 := inv_mul_cancel₀ hh
      have hS : ∀ S : ℝ, (hN N ^ 3)⁻¹ * -(χ * (hN N ^ 3 * S)) = -χ * S := fun S => by
        linear_combination (-χ * S) * hinv
      rw [hS, Finset.mul_sum]
      simp only [hsite]
      rw [divF, ← Finset.mul_sum, Finset.sum_comm]
      have hp' : ∀ p : Fin 3, ∑ y, symMat (π y) p a * pd p (Pi.single x (1 : ℝ)) y =
          -pd p (fun y => symMat (π y) p a) x := fun p => sum_mul_pd_single p _ x
      simp only [hp', Finset.sum_neg_distrib]
      ring

end Chart

end RenewalGeometry.ExactPhaseAction.QuadJet
