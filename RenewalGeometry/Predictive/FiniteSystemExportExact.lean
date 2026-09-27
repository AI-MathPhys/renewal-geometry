/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Predictive.TenPanelReconstructionExact
/-!
# Finite coherent system export (`cor:finite-system-export`)

`cor:finite-system-export` of the spacetime–gauge duality manuscript, assembled from the
ten-panel reconstruction (`prop:ten-panel-reconstruction`) and the robust commutant stopping
test (`prop:reconstruction-error`) of `Predictive/TenPanelReconstructionExact.lean`.

The corollary says: for the normalized six-edge source class, ten fixed Hermitian environment
quadratures suffice to reconstruct all six edge coefficients on the acted-on carrier; with
Hilbert–Schmidt coefficient error `e_K` (`eq:appendix-reconstruction-error`) the star-closed
stacked commutator map changes in operator norm by at most `2√2 e_K`; hence an independently
verified protected commutant complement with measured least singular value `ŝ > 2√2 e_K` has
no additional commutant direction.

## Rendering of the three informal phrases (disclosed)

* *"independently verified protected commutant"*: a subspace `M` of the Hilbert–Schmidt
  space of the acted-on carrier that is known to lie in the kernel of the true stacked
  commutator map `𝒟` (`M ≤ ker 𝒟`); the *protected complement* is its orthogonal
  complement `Mᗮ`.
* *"measured least singular value `ŝ`"* of the reconstructed map `𝒟̂` on `Mᗮ`: the bound
  `ŝ ‖x‖ ≤ ‖𝒟̂ x‖` for all `x ∈ Mᗮ`.
* *"no additional commutant direction"*: `ker 𝒟 = M` exactly; equivalently every matrix `X`
  commuting with all six true coefficients and their adjoints has `X ∈ M`.

The reconstruction lives on the common carrier `E × R`, so the true coefficient is
`K_e ⊗ I_R`; the error `e_K` is the explicit budget `panelErrorBudget` of
`eq:appendix-reconstruction-error` computed from the Hilbert–Schmidt panel errors.
The frame hypotheses are those of `prop:ten-panel-reconstruction`
(`∑_e K_e = √2 I`, `∑_a Q_a = I`, `0 < ϑ < 1`, Helmert frame `OᵀO = I`, `Oᵀ𝟏 = 0`,
`OOᵀ = I − 𝟏𝟏ᵀ/6`).

* `jointCommutatorL2_opNorm_sub_le`: the `2 → 2` operator-norm form of the `2√2 e_K` bound
  (`eq:appendix-commutator-error`) for the continuous linear maps `𝒟̂ − 𝒟`.
* `no_additional_commutant_direction`: the stopping test in the kernel form, with the
  matrix-commutant reading.
* `finite_system_export`: the assembled corollary.
-/

open Matrix
open scoped Matrix.Norms.L2Operator Kronecker

namespace RenewalGeometry

open TenPanel

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The stacked commutator map of a coefficient tuple as a continuous linear map between the
Hilbert–Schmidt spaces (finite dimension). -/
def exportJointCommutatorCLM {s : ℕ} (c : Fin s → Matrix n n ℂ) :
    EuclideanSpace ℂ (n × n) →L[ℂ] EuclideanSpace ℂ (Fin s × (n × n)) :=
  LinearMap.toContinuousLinearMap (jointCommutatorL2 c)

@[simp] theorem exportJointCommutatorCLM_apply {s : ℕ} (c : Fin s → Matrix n n ℂ)
    (x : EuclideanSpace ℂ (n × n)) : exportJointCommutatorCLM c x = jointCommutatorL2 c x := rfl

/-- **`eq:appendix-commutator-error` in operator-norm form.**  If the Hilbert–Schmidt
coefficient error of `K̂` relative to `K` is at most `e_K`, the star-closed stacked commutator
maps satisfy `‖𝒟̂ − 𝒟‖_{2→2} ≤ 2√2 e_K`. -/
theorem jointCommutatorCLM_opNorm_sub_le {s : ℕ} (K' K : Fin s → Matrix n n ℂ)
    (eK : ℝ) (he : hsCoefficientError K' K ≤ eK) :
    ‖exportJointCommutatorCLM (starClosedStack K') - exportJointCommutatorCLM (starClosedStack K)‖
      ≤ 2 * Real.sqrt 2 * eK := by
  have heK : 0 ≤ eK := (hsCoefficientError_nonneg K' K).trans he
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  rw [_root_.sub_apply, exportJointCommutatorCLM_apply, exportJointCommutatorCLM_apply]
  exact starClosedStack_commutator_perturbation K' K eK he x

/-- **No additional commutant direction.**  Let `M` be an independently verified protected
commutant (`M ≤ ker 𝒟` for the true star-closed stacked commutator map `𝒟`) and suppose the
reconstructed map `𝒟̂` has measured least singular value `ŝ > 2√2 e_K` on the protected
complement `Mᗮ`.  Then `ker 𝒟 = M`, and every matrix commuting with all true coefficients and
their adjoints lies in `M`. -/
theorem no_additional_commutant_direction {s : ℕ} (K' K : Fin s → Matrix n n ℂ)
    (eK : ℝ) (he : hsCoefficientError K' K ≤ eK)
    (M : Submodule ℂ (EuclideanSpace ℂ (n × n)))
    (hM : M ≤ LinearMap.ker (jointCommutatorL2 (starClosedStack K))) (ŝ : ℝ)
    (hŝ : ∀ x ∈ Mᗮ, ŝ * ‖x‖ ≤ ‖jointCommutatorL2 (starClosedStack K') x‖)
    (hgap : 2 * Real.sqrt 2 * eK < ŝ) :
    LinearMap.ker (jointCommutatorL2 (starClosedStack K)) = M ∧
      ∀ X : Matrix n n ℂ, (∀ e, K e * X = X * K e) → (∀ e, (K e)ᴴ * X = X * (K e)ᴴ) →
        matrixL2 X ∈ M := by
  have hker := robust_commutant_stopping_test_ker K' K eK he M hM ŝ hŝ hgap
  refine ⟨hker, fun X hc hc' => ?_⟩
  rw [← hker]
  refine (matrixL2_mem_jointCommutator_ker_iff _ X).2 fun j => ?_
  unfold starClosedStack
  split_ifs
  · exact hc _
  · exact hc' _

variable {E R : Type*} [Fintype E] [DecidableEq E] [Fintype R] [DecidableEq R]

/-- **`cor:finite-system-export` (Finite coherent system export).**  For the normalized
six-edge source class (`∑_e K_e = √2 I`, `∑_a Q_a = I`, `0 < ϑ < 1`, Helmert frame `O`):

1. the ten fixed Hermitian quadratures `X_μ, Y_μ` reconstruct all six edge coefficients on the
   acted-on carrier, `D_μ ⊗ I = (2√3/√(ϑh)) (𝒫*(X_μ) + i 𝒫*(Y_μ))`,
   `K_e = I/√18 + ∑_μ O_{eμ} D_μ` (`eq:ten-panel-reconstruction`);
2. the linear reconstruction `K̂_e` from measured panels with Hilbert–Schmidt errors
   `ε_{X,μ}, ε_{Y,μ}` has Hilbert–Schmidt coefficient error at most
   `e_K = (2√3/√(ϑh)) (∑_μ (ε_{X,μ} + ε_{Y,μ})²)^{1/2}` (`eq:appendix-reconstruction-error`);
3. the star-closed stacked commutator map changes in `2 → 2` operator norm by at most
   `2√2 e_K` (`eq:appendix-commutator-error`);
4. an independently verified protected commutant `M ≤ ker 𝒟` whose protected complement `Mᗮ`
   carries a measured least singular value `ŝ > 2√2 e_K` of `𝒟̂` has no additional commutant
   direction: `ker 𝒟 = M`, and every matrix commuting with all `K_e ⊗ I` and their adjoints
   lies in `M`. -/
theorem finite_system_export {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ1 : ϑ < 1)
    {K : Fin 6 → Matrix E E ℂ} {Q : Fin 4 → Matrix R R ℂ} {O : Matrix (Fin 6) (Fin 5) ℝ}
    (hK : ∑ e, K e = ((Real.sqrt 2 : ℝ) : ℂ) • 1) (hQ : ∑ a, Q a = 1)
    (hO : Oᵀ * O = 1) (hcol : ∀ μ, ∑ e, O e μ = 0)
    (hproj : O * Oᵀ = 1 - ((6 : ℝ)⁻¹ : ℝ) • of fun _ _ => (1 : ℝ))
    (X' Y' : Fin 5 → Matrix (E × R) (E × R) ℂ) (εX εY : Fin 5 → ℝ)
    (hX : ∀ μ, ‖matrixL2 (X' μ
      - complementaryPullback (frameCoefficient ϑ K Q) (quadratureX O μ))‖ ≤ εX μ)
    (hY : ∀ μ, ‖matrixL2 (Y' μ
      - complementaryPullback (frameCoefficient ϑ K Q) (quadratureY O μ))‖ ≤ εY μ) :
    -- (1) ten-panel reconstruction of all six coefficients on the acted-on carrier
    ((∀ μ, edgeContrast O K μ ⊗ₖ (1 : Matrix R R ℂ)
        = ((reconstructionScale ϑ : ℝ) : ℂ)
          • (complementaryPullback (frameCoefficient ϑ K Q) (quadratureX O μ)
              + Complex.I • complementaryPullback (frameCoefficient ϑ K Q) (quadratureY O μ)))
      ∧ ∀ e, K e = (((Real.sqrt 18)⁻¹ : ℝ) : ℂ) • 1
          + ∑ μ, ((O e μ : ℝ) : ℂ) • edgeContrast O K μ)
    -- (2) Hilbert–Schmidt coefficient error of the linear reconstruction
    ∧ hsCoefficientError (reconstructedCoefficient ϑ O X' Y')
        (fun e => K e ⊗ₖ (1 : Matrix R R ℂ)) ≤ panelErrorBudget ϑ εX εY
    -- (3) operator-norm change of the star-closed stacked commutator map
    ∧ ‖exportJointCommutatorCLM (starClosedStack (reconstructedCoefficient ϑ O X' Y'))
        - exportJointCommutatorCLM (starClosedStack fun e => K e ⊗ₖ (1 : Matrix R R ℂ))‖
        ≤ 2 * Real.sqrt 2 * panelErrorBudget ϑ εX εY
    -- (4) the stopping test: no additional commutant direction
    ∧ ∀ (M : Submodule ℂ (EuclideanSpace ℂ ((E × R) × (E × R)))),
        M ≤ LinearMap.ker (jointCommutatorL2 (starClosedStack fun e => K e ⊗ₖ (1 : Matrix R R ℂ)))
        → ∀ ŝ : ℝ,
        (∀ x ∈ Mᗮ, ŝ * ‖x‖
          ≤ ‖jointCommutatorL2 (starClosedStack (reconstructedCoefficient ϑ O X' Y')) x‖) →
        2 * Real.sqrt 2 * panelErrorBudget ϑ εX εY < ŝ →
        LinearMap.ker (jointCommutatorL2 (starClosedStack fun e => K e ⊗ₖ (1 : Matrix R R ℂ)))
            = M
          ∧ ∀ X : Matrix (E × R) (E × R) ℂ,
              (∀ e, (K e ⊗ₖ (1 : Matrix R R ℂ)) * X = X * (K e ⊗ₖ (1 : Matrix R R ℂ))) →
              (∀ e, (K e ⊗ₖ (1 : Matrix R R ℂ))ᴴ * X = X * (K e ⊗ₖ (1 : Matrix R R ℂ))ᴴ) →
              matrixL2 X ∈ M := by
  obtain ⟨herr, -, -⟩ :=
    reconstruction_error hϑ hϑ1 hK hQ hO hcol hproj X' Y' εX εY hX hY
  refine ⟨ten_panel_reconstruction (Q := Q) hϑ hϑ1 hK hQ hcol hproj, herr,
    jointCommutatorCLM_opNorm_sub_le _ _ _ herr, fun M hM ŝ hŝ hgap =>
      no_additional_commutant_direction _ _ _ herr M hM ŝ hŝ hgap⟩

end

end RenewalGeometry
