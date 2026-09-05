/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.HermitianMoorePenroseInverse

/-!
# Brand-new EASY batch 03 (Gran-Tensor manuscript)

Exact formalizations of six brand-new manuscript records:

* `thm:SMOS-energy-commutator-anchor` — commutator Ward data determine the
  energy only after a vacuum anchor: if `D = E_Σ - H` commutes with the
  time-zero algebra on the cyclic domain `𝔄₀Ω`, then `DΩ = 0` forces `D = 0`
  on `𝔄₀Ω` and `DΩ = cΩ` forces `D = cI` on `𝔄₀Ω`
  (`smos_energy_commutator_zero_anchor`, `smos_energy_commutator_scalar_anchor`,
  `smos_energy_commutator_anchor`).
* `thm:SMOS-energy-trace-transport` — packet transport bound
  `‖(E_Y-H_Y)B_Y-(E_X-H_X)B_X‖ ≤ (ε_E+ε_H)M_B + M_D ε_B`
  (`smos_energy_trace_packet_transport`), plus the identical scale/trace
  incidence instance `smos_scale_trace_incidence_transport`.
* `thm:SMOS-trace-Pythagoras` — identity–nuisance–composite–new-anomaly
  deflation: mutual orthogonality of the three Moore–Penrose range
  projections, the four-term source decomposition and Gram Pythagoras, the
  supported anomaly coefficient synthesis, and
  `G_new = 0 ↔ Ran S_sc ⊆ Ran(I₀,N₀,O)`
  (`smos_trace_pythagoras_projections`, `smos_trace_source_decomposition`,
  `smos_trace_gram_pythagoras`, `smos_trace_beta_synthesis`,
  `smos_trace_new_gram_zero_iff`).
* `thm:SMOS-trace-scheme` — finite scheme covariance: `O₁' = O₁M`,
  range/anomaly-source/Gram invariance, `G_O' = MᴴG_O M`, and the coefficient
  covariance `β' ≡ M⁻¹β` on the supported operator quotient
  (`smos_trace_scheme_efficient_operator`,
  `smos_trace_scheme_range_invariance`,
  `smos_trace_scheme_anomaly_source_invariance`,
  `smos_trace_scheme_gram_congruence`, `smos_trace_scheme_beta_covariance`,
  `smos_trace_scheme_gram_invariance`, `smos_trace_scheme_invariants`).
* `thm:SMQG-Feshbach-covariance` — exact block LDU factorization,
  `det D = det E · det S`, retained block of the inverse `= S⁻¹`, and the
  reflected covariance compression `P = J₊ᴴ S⁻¹ J₋`
  (`smqg_feshbach_ldu`, `smqg_feshbach_det`,
  `smqg_feshbach_retained_inverse`, `smqg_feshbach_reflected_covariance`,
  `smqg_feshbach_covariance`).
* `thm:SMQG-relation-descent` — descent of the Gaussian kernel through the
  ordinary word relations forces the relation residual `Δ_rel = 0`, and a
  positive residual refutes joint occurrence
  (`smqg_relation_descent_residual_left`,
  `smqg_relation_descent_residual_right`, `smqg_relation_descent`,
  `smqg_relation_descent_converse`).

Rendering disclosed: the trace/scheme/relation records are about finite
declared source banks and word banks, and are rendered with finite complex
matrices; the Moore–Penrose Gram pseudoinverse `(AᴴA)†` is the repo's spectral
`hermitianMoorePenroseInverse`; the Hilbert–Schmidt norm squared is the sum of
squared entry norms; `Ran(I₀,N₀,O)` is the join of the three column ranges.
The scheme-covariance clause `β' = M⁻¹β` "on the supported operator quotient"
is rendered as `O₁'β' = O₁'(M⁻¹β)`, i.e. equality modulo `ker O₁'`, which is
exactly what the quotient asserts.  The commutator-anchor record is rendered
for a unital subalgebra of module endomorphisms acting on the algebraic cyclic
domain `𝔄₀Ω`; the transport record is stated in an arbitrary non-unital
normed ring, which covers both the energy incidence and the scale/trace
incidence of the manuscript.
-/

open Matrix
open Unitary

namespace NCG

/-! ## `thm:SMOS-energy-commutator-anchor` -/

section EnergyCommutatorAnchor

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- `thm:SMOS-energy-commutator-anchor` (ii): if `D = E_Σ - H` commutes with
every element of the represented unital time-zero algebra on the cyclic domain
`D₀ = 𝔄₀Ω`, and the vacuum is a `D`-eigenvector `DΩ = cΩ`, then `D = cI` on
`D₀`. -/
theorem smos_energy_commutator_scalar_anchor
    (𝔄 : Subalgebra ℂ (Module.End ℂ V)) (Ω : V) (Esig H : Module.End ℂ V)
    (_hHinv : ∀ A ∈ 𝔄, ∃ B ∈ 𝔄, H (A Ω) = B Ω)
    (_hEinv : ∀ A ∈ 𝔄, ∃ B ∈ 𝔄, Esig (A Ω) = B Ω)
    (hWard : ∀ A ∈ 𝔄, ∀ B ∈ 𝔄,
      ((Esig - H) * A - A * (Esig - H)) (B Ω) = 0)
    (c : ℂ) (hvac : (Esig - H) Ω = c • Ω) :
    ∀ A ∈ 𝔄, (Esig - H) (A Ω) = c • A Ω := by
  intro A hA
  have h1 := hWard A hA 1 (one_mem 𝔄)
  rw [Module.End.one_apply, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply, sub_eq_zero] at h1
  rw [h1, hvac, map_smul]

/-- `thm:SMOS-energy-commutator-anchor` (i): with the commutator Ward data and
the unnormalized vacuum anchor `DΩ = 0`, the energy defect `D = E_Σ - H`
vanishes on the whole cyclic domain `𝔄₀Ω`. -/
theorem smos_energy_commutator_zero_anchor
    (𝔄 : Subalgebra ℂ (Module.End ℂ V)) (Ω : V) (Esig H : Module.End ℂ V)
    (hHinv : ∀ A ∈ 𝔄, ∃ B ∈ 𝔄, H (A Ω) = B Ω)
    (hEinv : ∀ A ∈ 𝔄, ∃ B ∈ 𝔄, Esig (A Ω) = B Ω)
    (hWard : ∀ A ∈ 𝔄, ∀ B ∈ 𝔄,
      ((Esig - H) * A - A * (Esig - H)) (B Ω) = 0)
    (hvac : (Esig - H) Ω = 0) :
    ∀ A ∈ 𝔄, (Esig - H) (A Ω) = 0 := by
  intro A hA
  have h := smos_energy_commutator_scalar_anchor 𝔄 Ω Esig H hHinv hEinv hWard 0
    (by rw [hvac, zero_smul]) A hA
  rw [h, zero_smul]

/-- `thm:SMOS-energy-commutator-anchor` (bundle): the translation Ward
commutators determine the energy only up to the vacuum fibre — a zero vacuum
row gives `D = 0` on `𝔄₀Ω`, an eigenvalue row `DΩ = cΩ` gives `D = cI` on
`𝔄₀Ω`. -/
theorem smos_energy_commutator_anchor
    (𝔄 : Subalgebra ℂ (Module.End ℂ V)) (Ω : V) (Esig H : Module.End ℂ V)
    (hHinv : ∀ A ∈ 𝔄, ∃ B ∈ 𝔄, H (A Ω) = B Ω)
    (hEinv : ∀ A ∈ 𝔄, ∃ B ∈ 𝔄, Esig (A Ω) = B Ω)
    (hWard : ∀ A ∈ 𝔄, ∀ B ∈ 𝔄,
      ((Esig - H) * A - A * (Esig - H)) (B Ω) = 0) :
    ((Esig - H) Ω = 0 → ∀ A ∈ 𝔄, (Esig - H) (A Ω) = 0) ∧
      (∀ c : ℂ, (Esig - H) Ω = c • Ω → ∀ A ∈ 𝔄, (Esig - H) (A Ω) = c • A Ω) :=
  ⟨smos_energy_commutator_zero_anchor 𝔄 Ω Esig H hHinv hEinv hWard,
    fun c => smos_energy_commutator_scalar_anchor 𝔄 Ω Esig H hHinv hEinv hWard c⟩

end EnergyCommutatorAnchor

/-! ## `thm:SMOS-energy-trace-transport` -/

section EnergyTraceTransport

variable {𝒜 : Type*} [NonUnitalNormedRing 𝒜]

/-- `thm:SMOS-energy-trace-transport`: with common-core source maps of norm at
most `M_B`, source perturbation `ε_B`, energy/Hamiltonian perturbations
`ε_E, ε_H`, and defect bound `‖E_Z - H_Z‖ ≤ M_D`, the energy incidence
transports with
`‖(E_Y-H_Y)B_Y - (E_X-H_X)B_X‖ ≤ (ε_E+ε_H)M_B + M_D ε_B`. -/
theorem smos_energy_trace_packet_transport
    (BX BY EX EY HX HY : 𝒜) (MB MD epsB epsE epsH : ℝ)
    (_hBX : ‖BX‖ ≤ MB) (hBY : ‖BY‖ ≤ MB)
    (hB : ‖BY - BX‖ ≤ epsB) (hE : ‖EY - EX‖ ≤ epsE) (hH : ‖HY - HX‖ ≤ epsH)
    (hDX : ‖EX - HX‖ ≤ MD) (_hDY : ‖EY - HY‖ ≤ MD) :
    ‖(EY - HY) * BY - (EX - HX) * BX‖ ≤ (epsE + epsH) * MB + MD * epsB := by
  have hsplit : (EY - HY) * BY - (EX - HX) * BX
      = ((EY - EX) - (HY - HX)) * BY + (EX - HX) * (BY - BX) := by
    simp only [sub_mul, mul_sub]
    abel
  rw [hsplit]
  have h1 : ‖((EY - EX) - (HY - HX)) * BY‖ ≤ (epsE + epsH) * MB := by
    refine (norm_mul_le _ _).trans ?_
    have hEH : ‖(EY - EX) - (HY - HX)‖ ≤ epsE + epsH :=
      (norm_sub_le _ _).trans (add_le_add hE hH)
    exact mul_le_mul hEH hBY (norm_nonneg _)
      (add_nonneg ((norm_nonneg _).trans hE) ((norm_nonneg _).trans hH))
  have h2 : ‖(EX - HX) * (BY - BX)‖ ≤ MD * epsB := by
    refine (norm_mul_le _ _).trans ?_
    exact mul_le_mul hDX hB (norm_nonneg _) ((norm_nonneg _).trans hDX)
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

/-- `thm:SMOS-energy-trace-transport` (scale/trace incidence): the same
estimate after replacing `E - H` by `S_Θ - S_sc`; the abstract normed-ring
statement is instantiated verbatim on the direct scale/trace incidence. -/
theorem smos_scale_trace_incidence_transport
    (BX BY SThX SThY SscX SscY : 𝒜) (MB MD epsB epsS epsSc : ℝ)
    (hBX : ‖BX‖ ≤ MB) (hBY : ‖BY‖ ≤ MB)
    (hB : ‖BY - BX‖ ≤ epsB) (hS : ‖SThY - SThX‖ ≤ epsS)
    (hSc : ‖SscY - SscX‖ ≤ epsSc)
    (hDX : ‖SThX - SscX‖ ≤ MD) (hDY : ‖SThY - SscY‖ ≤ MD) :
    ‖(SThY - SscY) * BY - (SThX - SscX) * BX‖
      ≤ (epsS + epsSc) * MB + MD * epsB :=
  smos_energy_trace_packet_transport BX BY SThX SThY SscX SscY
    MB MD epsB epsS epsSc hBX hBY hB hS hSc hDX hDY

end EnergyTraceTransport

/-! ## Moore–Penrose range projections for the trace packet -/

section RangeProj

variable {m ι : Type*} [Fintype m] [Fintype ι] [DecidableEq ι]

/-- Gram pseudoinverse `(AᴴA)†` via the spectral Hermitian Moore–Penrose
inverse. -/
noncomputable def smosTraceGramPinv (A : Matrix m ι ℂ) : Matrix ι ι ℂ :=
  HermitianMoorePenroseInverse.hermitianMoorePenroseInverse (Aᴴ * A)
    (Matrix.isHermitian_conjTranspose_mul_self A)

/-- The Gram pseudoinverse is Hermitian. -/
theorem smosTraceGramPinv_conjTranspose (A : Matrix m ι ℂ) :
    (smosTraceGramPinv A)ᴴ = smosTraceGramPinv A :=
  HermitianMoorePenroseInverse.hermitianMoorePenroseInverse_isHermitian _ _

open scoped ComplexOrder in
/-- Key cancellation `A ((AᴴA)† (AᴴA)) = A`, by the `MᴴM = 0` trick. -/
theorem smosTraceGramPinv_cancel (A : Matrix m ι ℂ) :
    A * (smosTraceGramPinv A * (Aᴴ * A)) = A := by
  have hpen : Aᴴ * A * smosTraceGramPinv A * (Aᴴ * A) = Aᴴ * A :=
    HermitianMoorePenroseInverse.hermitianMoorePenroseInverse_penrose_left _ _
  have hGN : (Aᴴ * A) * (smosTraceGramPinv A * (Aᴴ * A) - 1) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, sub_eq_zero]
    exact hpen
  have hAN2 : (A * (smosTraceGramPinv A * (Aᴴ * A) - 1))ᴴ
      * (A * (smosTraceGramPinv A * (Aᴴ * A) - 1)) = 0 := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc Aᴴ A (smosTraceGramPinv A * (Aᴴ * A) - 1), hGN,
      Matrix.mul_zero]
  have hAN := Matrix.conjTranspose_mul_self_eq_zero.mp hAN2
  rwa [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hAN

/-- Moore–Penrose range projection `P_A = A (AᴴA)† Aᴴ`. -/
noncomputable def smosTraceRangeProj (A : Matrix m ι ℂ) : Matrix m m ℂ :=
  A * smosTraceGramPinv A * Aᴴ

/-- The range projection is Hermitian. -/
theorem smosTraceRangeProj_conjTranspose (A : Matrix m ι ℂ) :
    (smosTraceRangeProj A)ᴴ = smosTraceRangeProj A := by
  rw [smosTraceRangeProj, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, smosTraceGramPinv_conjTranspose,
    Matrix.mul_assoc]

/-- The range projection fixes its synthesis: `P_A A = A`. -/
theorem smosTraceRangeProj_mul_base (A : Matrix m ι ℂ) :
    smosTraceRangeProj A * A = A := by
  have e : smosTraceRangeProj A * A
      = A * (smosTraceGramPinv A * (Aᴴ * A)) := by
    simp only [smosTraceRangeProj, Matrix.mul_assoc]
  rw [e, smosTraceGramPinv_cancel]

/-- The range projection is idempotent. -/
theorem smosTraceRangeProj_idem (A : Matrix m ι ℂ) :
    smosTraceRangeProj A * smosTraceRangeProj A = smosTraceRangeProj A := by
  have e : smosTraceRangeProj A * smosTraceRangeProj A
      = smosTraceRangeProj A * A * (smosTraceGramPinv A * Aᴴ) := by
    simp only [smosTraceRangeProj, Matrix.mul_assoc]
  rw [e, smosTraceRangeProj_mul_base, smosTraceRangeProj, Matrix.mul_assoc]

/-- If `Aᴴ B = 0` (columns of `B` orthogonal to `Ran A`) then `P_A B = 0`. -/
theorem smosTraceRangeProj_mul_eq_zero_left {κ : Type*}
    (A : Matrix m ι ℂ) (B : Matrix m κ ℂ) (h : Aᴴ * B = 0) :
    smosTraceRangeProj A * B = 0 := by
  rw [smosTraceRangeProj, Matrix.mul_assoc, Matrix.mul_assoc, h,
    Matrix.mul_zero, Matrix.mul_zero]

/-- If `X B = 0` then `X P_B = 0`. -/
theorem mul_smosTraceRangeProj_eq_zero {a κ : Type*} [Fintype κ] [DecidableEq κ]
    (B : Matrix m κ ℂ) (X : Matrix a m ℂ) (h : X * B = 0) :
    X * smosTraceRangeProj B = 0 := by
  rw [smosTraceRangeProj, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h,
    Matrix.zero_mul, Matrix.zero_mul]

/-- Orthogonality of range projections is symmetric. -/
theorem smosTraceRangeProj_orth_symm {κ κ' : Type*}
    [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    (A : Matrix m κ ℂ) (B : Matrix m κ' ℂ)
    (h : smosTraceRangeProj A * smosTraceRangeProj B = 0) :
    smosTraceRangeProj B * smosTraceRangeProj A = 0 := by
  have h2 := congrArg Matrix.conjTranspose h
  rwa [Matrix.conjTranspose_mul, smosTraceRangeProj_conjTranspose,
    smosTraceRangeProj_conjTranspose, Matrix.conjTranspose_zero] at h2

/-- Two Moore–Penrose range projections that fix each other's synthesis are
equal. -/
theorem smosTraceRangeProj_eq_of_fix {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix m ι ℂ) (B : Matrix m κ ℂ)
    (hAB : smosTraceRangeProj A * B = B) (hBA : smosTraceRangeProj B * A = A) :
    smosTraceRangeProj A = smosTraceRangeProj B := by
  have h1 : smosTraceRangeProj A * smosTraceRangeProj B
      = smosTraceRangeProj B := by
    have e : smosTraceRangeProj A * smosTraceRangeProj B
        = smosTraceRangeProj A * B * (smosTraceGramPinv B * Bᴴ) := by
      simp only [smosTraceRangeProj, Matrix.mul_assoc]
    rw [e, hAB]
    simp only [smosTraceRangeProj, Matrix.mul_assoc]
  have h2 : smosTraceRangeProj B * smosTraceRangeProj A
      = smosTraceRangeProj A := by
    have e : smosTraceRangeProj B * smosTraceRangeProj A
        = smosTraceRangeProj B * A * (smosTraceGramPinv A * Aᴴ) := by
      simp only [smosTraceRangeProj, Matrix.mul_assoc]
    rw [e, hBA]
    simp only [smosTraceRangeProj, Matrix.mul_assoc]
  have h3 : smosTraceRangeProj B * smosTraceRangeProj A
      = smosTraceRangeProj B := by
    have h4 := congrArg Matrix.conjTranspose h1
    rwa [Matrix.conjTranspose_mul, smosTraceRangeProj_conjTranspose,
      smosTraceRangeProj_conjTranspose] at h4
  rw [← h2, h3]

/-- The range projection is invariant under an invertible recombination of the
synthesis columns: `P_{AM} = P_A`. -/
theorem smosTraceRangeProj_mul_invertible (A : Matrix m ι ℂ)
    (M : Matrix ι ι ℂ) [Invertible M] :
    smosTraceRangeProj (A * M) = smosTraceRangeProj A := by
  have hAB : smosTraceRangeProj (A * M) * A = A := by
    have h2 : smosTraceRangeProj (A * M) * (A * M) * ⅟M = A * M * ⅟M := by
      rw [smosTraceRangeProj_mul_base]
    rwa [Matrix.mul_invOf_cancel_right, ← Matrix.mul_assoc,
      Matrix.mul_invOf_cancel_right] at h2
  have hBA : smosTraceRangeProj A * (A * M) = A * M := by
    rw [← Matrix.mul_assoc, smosTraceRangeProj_mul_base]
  exact smosTraceRangeProj_eq_of_fix (A * M) A hAB hBA

/-- Every vector in the image of `P_A` lies in the column range of `A`. -/
theorem smosTraceRangeProj_mulVec_mem (A : Matrix m ι ℂ) (v : m → ℂ) :
    smosTraceRangeProj A *ᵥ v ∈ LinearMap.range A.mulVecLin := by
  refine LinearMap.mem_range.mpr ⟨(smosTraceGramPinv A * Aᴴ) *ᵥ v, ?_⟩
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← Matrix.mul_assoc]
  rfl

/-- A matrix annihilating every vector is zero. -/
theorem smosTrace_eq_zero_of_mulVec {a b : Type*} [Fintype b]
    (M : Matrix a b ℂ) (h : ∀ x, M *ᵥ x = 0) : M = 0 := by
  classical
  exact Matrix.ext_of_mulVec_single fun j => by rw [h, Matrix.zero_mulVec]

end RangeProj

/-! ## `thm:SMOS-trace-Pythagoras` -/

section TracePythagoras

variable {m p q r s : Type*} [Fintype m] [DecidableEq m]
  [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
  [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
variable (I₀ : Matrix m p ℂ) (N₀ : Matrix m q ℂ) (O : Matrix m r ℂ)
  (Ssc : Matrix m s ℂ)

/-- Deflated nuisance source `N₁ = (I - P_I) N₀`. -/
noncomputable def smosTraceNuisance : Matrix m q ℂ :=
  (1 - smosTraceRangeProj I₀) * N₀

/-- Deflated composite-anomaly source `O₁ = (I - P_I - P_N) O`. -/
noncomputable def smosTraceComposite : Matrix m r ℂ :=
  (1 - smosTraceRangeProj I₀ - smosTraceRangeProj (smosTraceNuisance I₀ N₀)) * O

/-- New scale-response source `S_new = (I - P_I - P_N - P_O) S_sc`. -/
noncomputable def smosTraceNewSource : Matrix m s ℂ :=
  (1 - smosTraceRangeProj I₀ - smosTraceRangeProj (smosTraceNuisance I₀ N₀)
      - smosTraceRangeProj (smosTraceComposite I₀ N₀ O)) * Ssc

/-- Minimum supported anomaly coefficient map
`β = (O₁ᴴO₁)† O₁ᴴ (I - P_I - P_N) S_sc`. -/
noncomputable def smosTraceBetaMap : Matrix r s ℂ :=
  smosTraceGramPinv (smosTraceComposite I₀ N₀ O)
    * (smosTraceComposite I₀ N₀ O)ᴴ
    * ((1 - smosTraceRangeProj I₀
        - smosTraceRangeProj (smosTraceNuisance I₀ N₀)) * Ssc)

omit [Fintype q] [DecidableEq q] in
/-- The identity projection annihilates the deflated nuisance source. -/
theorem smosTrace_projI_mul_nuisance :
    smosTraceRangeProj I₀ * smosTraceNuisance I₀ N₀ = 0 := by
  simp only [smosTraceNuisance]
  rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one,
    smosTraceRangeProj_idem, sub_self, Matrix.zero_mul]

/-- `P_I P_N = 0`. -/
theorem smosTrace_projI_mul_projN :
    smosTraceRangeProj I₀ * smosTraceRangeProj (smosTraceNuisance I₀ N₀) = 0 :=
  mul_smosTraceRangeProj_eq_zero _ _ (smosTrace_projI_mul_nuisance I₀ N₀)

/-- `P_N P_I = 0`. -/
theorem smosTrace_projN_mul_projI :
    smosTraceRangeProj (smosTraceNuisance I₀ N₀) * smosTraceRangeProj I₀ = 0 :=
  smosTraceRangeProj_orth_symm _ _ (smosTrace_projI_mul_projN I₀ N₀)

omit [Fintype r] [DecidableEq r] in
/-- The identity projection annihilates the deflated composite source. -/
theorem smosTrace_projI_mul_composite :
    smosTraceRangeProj I₀ * smosTraceComposite I₀ N₀ O = 0 := by
  simp only [smosTraceComposite]
  rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one,
    smosTraceRangeProj_idem, smosTrace_projI_mul_projN, sub_zero, sub_self,
    Matrix.zero_mul]

omit [Fintype r] [DecidableEq r] in
/-- The nuisance projection annihilates the deflated composite source. -/
theorem smosTrace_projN_mul_composite :
    smosTraceRangeProj (smosTraceNuisance I₀ N₀) * smosTraceComposite I₀ N₀ O
      = 0 := by
  simp only [smosTraceComposite]
  rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one,
    smosTraceRangeProj_idem, smosTrace_projN_mul_projI, sub_zero, sub_self,
    Matrix.zero_mul]

/-- `P_I P_O = 0`. -/
theorem smosTrace_projI_mul_projO :
    smosTraceRangeProj I₀ * smosTraceRangeProj (smosTraceComposite I₀ N₀ O)
      = 0 :=
  mul_smosTraceRangeProj_eq_zero _ _ (smosTrace_projI_mul_composite I₀ N₀ O)

/-- `P_O P_I = 0`. -/
theorem smosTrace_projO_mul_projI :
    smosTraceRangeProj (smosTraceComposite I₀ N₀ O) * smosTraceRangeProj I₀
      = 0 :=
  smosTraceRangeProj_orth_symm _ _ (smosTrace_projI_mul_projO I₀ N₀ O)

/-- `P_N P_O = 0`. -/
theorem smosTrace_projN_mul_projO :
    smosTraceRangeProj (smosTraceNuisance I₀ N₀)
      * smosTraceRangeProj (smosTraceComposite I₀ N₀ O) = 0 :=
  mul_smosTraceRangeProj_eq_zero _ _ (smosTrace_projN_mul_composite I₀ N₀ O)

/-- `P_O P_N = 0`. -/
theorem smosTrace_projO_mul_projN :
    smosTraceRangeProj (smosTraceComposite I₀ N₀ O)
      * smosTraceRangeProj (smosTraceNuisance I₀ N₀) = 0 :=
  smosTraceRangeProj_orth_symm _ _ (smosTrace_projN_mul_projO I₀ N₀ O)

/-- `(I - P_I) I₀ = 0`. -/
theorem smosTrace_one_sub_projI_mul_I :
    ((1 : Matrix m m ℂ) - smosTraceRangeProj I₀) * I₀ = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, smosTraceRangeProj_mul_base, sub_self]

omit [Fintype q] [DecidableEq q] in
/-- The deflated nuisance is orthogonal to the identity source. -/
theorem smosTrace_nuisance_conjTranspose_mul_I :
    (smosTraceNuisance I₀ N₀)ᴴ * I₀ = 0 := by
  simp only [smosTraceNuisance]
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, smosTraceRangeProj_conjTranspose,
    smosTrace_one_sub_projI_mul_I, Matrix.mul_zero]

/-- `P_N I₀ = 0`. -/
theorem smosTrace_projN_mul_I :
    smosTraceRangeProj (smosTraceNuisance I₀ N₀) * I₀ = 0 :=
  smosTraceRangeProj_mul_eq_zero_left _ _
    (smosTrace_nuisance_conjTranspose_mul_I I₀ N₀)

/-- `P_N N₀ = N₁`. -/
theorem smosTrace_projN_mul_N :
    smosTraceRangeProj (smosTraceNuisance I₀ N₀) * N₀
      = smosTraceNuisance I₀ N₀ := by
  have hsplit : smosTraceNuisance I₀ N₀ + smosTraceRangeProj I₀ * N₀ = N₀ := by
    simp only [smosTraceNuisance, Matrix.sub_mul, Matrix.one_mul,
      sub_add_cancel]
  calc smosTraceRangeProj (smosTraceNuisance I₀ N₀) * N₀
      = smosTraceRangeProj (smosTraceNuisance I₀ N₀)
          * (smosTraceNuisance I₀ N₀ + smosTraceRangeProj I₀ * N₀) := by
        rw [hsplit]
    _ = smosTraceRangeProj (smosTraceNuisance I₀ N₀) * smosTraceNuisance I₀ N₀
          + smosTraceRangeProj (smosTraceNuisance I₀ N₀)
            * (smosTraceRangeProj I₀ * N₀) := Matrix.mul_add _ _ _
    _ = smosTraceNuisance I₀ N₀ := by
        rw [smosTraceRangeProj_mul_base, ← Matrix.mul_assoc,
          smosTrace_projN_mul_projI, Matrix.zero_mul, add_zero]

/-- `(I - P_I - P_N) I₀ = 0`. -/
theorem smosTrace_resid2_mul_I :
    (1 - smosTraceRangeProj I₀
        - smosTraceRangeProj (smosTraceNuisance I₀ N₀)) * I₀ = 0 := by
  rw [Matrix.sub_mul, smosTrace_one_sub_projI_mul_I, smosTrace_projN_mul_I,
    sub_zero]

/-- `(I - P_I - P_N) N₀ = 0`. -/
theorem smosTrace_resid2_mul_N :
    (1 - smosTraceRangeProj I₀
        - smosTraceRangeProj (smosTraceNuisance I₀ N₀)) * N₀ = 0 := by
  rw [Matrix.sub_mul, smosTrace_projN_mul_N]
  simp only [smosTraceNuisance, sub_self]

/-- `(I - P_I - P_N)` is Hermitian. -/
theorem smosTrace_resid2_conjTranspose :
    (1 - smosTraceRangeProj I₀
        - smosTraceRangeProj (smosTraceNuisance I₀ N₀))ᴴ
      = 1 - smosTraceRangeProj I₀
          - smosTraceRangeProj (smosTraceNuisance I₀ N₀) := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, smosTraceRangeProj_conjTranspose,
    smosTraceRangeProj_conjTranspose]

omit [Fintype r] [DecidableEq r] in
/-- The deflated composite is orthogonal to the identity source. -/
theorem smosTrace_composite_conjTranspose_mul_I :
    (smosTraceComposite I₀ N₀ O)ᴴ * I₀ = 0 := by
  simp only [smosTraceComposite]
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
    smosTrace_resid2_conjTranspose, smosTrace_resid2_mul_I, Matrix.mul_zero]

omit [Fintype r] [DecidableEq r] in
/-- The deflated composite is orthogonal to the nuisance source. -/
theorem smosTrace_composite_conjTranspose_mul_N :
    (smosTraceComposite I₀ N₀ O)ᴴ * N₀ = 0 := by
  simp only [smosTraceComposite]
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
    smosTrace_resid2_conjTranspose, smosTrace_resid2_mul_N, Matrix.mul_zero]

/-- `P_O I₀ = 0`. -/
theorem smosTrace_projO_mul_I :
    smosTraceRangeProj (smosTraceComposite I₀ N₀ O) * I₀ = 0 :=
  smosTraceRangeProj_mul_eq_zero_left _ _
    (smosTrace_composite_conjTranspose_mul_I I₀ N₀ O)

/-- `P_O N₀ = 0`. -/
theorem smosTrace_projO_mul_N :
    smosTraceRangeProj (smosTraceComposite I₀ N₀ O) * N₀ = 0 :=
  smosTraceRangeProj_mul_eq_zero_left _ _
    (smosTrace_composite_conjTranspose_mul_N I₀ N₀ O)

/-- `P_O O = O₁`. -/
theorem smosTrace_projO_mul_O :
    smosTraceRangeProj (smosTraceComposite I₀ N₀ O) * O
      = smosTraceComposite I₀ N₀ O := by
  have hsplit : smosTraceComposite I₀ N₀ O
      + (smosTraceRangeProj I₀ * O
          + smosTraceRangeProj (smosTraceNuisance I₀ N₀) * O) = O := by
    simp only [smosTraceComposite, Matrix.sub_mul, Matrix.one_mul]
    abel
  calc smosTraceRangeProj (smosTraceComposite I₀ N₀ O) * O
      = smosTraceRangeProj (smosTraceComposite I₀ N₀ O)
          * (smosTraceComposite I₀ N₀ O
            + (smosTraceRangeProj I₀ * O
              + smosTraceRangeProj (smosTraceNuisance I₀ N₀) * O)) := by
        rw [hsplit]
    _ = smosTraceComposite I₀ N₀ O := by
        rw [Matrix.mul_add, Matrix.mul_add, smosTraceRangeProj_mul_base,
          ← Matrix.mul_assoc, smosTrace_projO_mul_projI, Matrix.zero_mul,
          ← Matrix.mul_assoc, smosTrace_projO_mul_projN, Matrix.zero_mul,
          add_zero, add_zero]

/-- `(I - P_I - P_N - P_O) I₀ = 0`. -/
theorem smosTrace_resid3_mul_I :
    (1 - smosTraceRangeProj I₀ - smosTraceRangeProj (smosTraceNuisance I₀ N₀)
        - smosTraceRangeProj (smosTraceComposite I₀ N₀ O)) * I₀ = 0 := by
  rw [Matrix.sub_mul, smosTrace_resid2_mul_I, smosTrace_projO_mul_I, sub_zero]

/-- `(I - P_I - P_N - P_O) N₀ = 0`. -/
theorem smosTrace_resid3_mul_N :
    (1 - smosTraceRangeProj I₀ - smosTraceRangeProj (smosTraceNuisance I₀ N₀)
        - smosTraceRangeProj (smosTraceComposite I₀ N₀ O)) * N₀ = 0 := by
  rw [Matrix.sub_mul, smosTrace_resid2_mul_N, smosTrace_projO_mul_N, sub_zero]

/-- `(I - P_I - P_N - P_O) O = 0`. -/
theorem smosTrace_resid3_mul_O :
    (1 - smosTraceRangeProj I₀ - smosTraceRangeProj (smosTraceNuisance I₀ N₀)
        - smosTraceRangeProj (smosTraceComposite I₀ N₀ O)) * O = 0 := by
  rw [Matrix.sub_mul, smosTrace_projO_mul_O]
  simp only [smosTraceComposite, sub_self]

/-- `(I - P_I - P_N - P_O)` is Hermitian. -/
theorem smosTrace_resid3_conjTranspose :
    (1 - smosTraceRangeProj I₀ - smosTraceRangeProj (smosTraceNuisance I₀ N₀)
        - smosTraceRangeProj (smosTraceComposite I₀ N₀ O))ᴴ
      = 1 - smosTraceRangeProj I₀
          - smosTraceRangeProj (smosTraceNuisance I₀ N₀)
          - smosTraceRangeProj (smosTraceComposite I₀ N₀ O) := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    smosTraceRangeProj_conjTranspose, smosTraceRangeProj_conjTranspose,
    smosTraceRangeProj_conjTranspose]

/-- `(I - P_I - P_N - P_O)` is idempotent. -/
theorem smosTrace_resid3_idem :
    (1 - smosTraceRangeProj I₀ - smosTraceRangeProj (smosTraceNuisance I₀ N₀)
        - smosTraceRangeProj (smosTraceComposite I₀ N₀ O))
      * (1 - smosTraceRangeProj I₀
          - smosTraceRangeProj (smosTraceNuisance I₀ N₀)
          - smosTraceRangeProj (smosTraceComposite I₀ N₀ O))
      = 1 - smosTraceRangeProj I₀
          - smosTraceRangeProj (smosTraceNuisance I₀ N₀)
          - smosTraceRangeProj (smosTraceComposite I₀ N₀ O) := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    smosTraceRangeProj_idem, smosTrace_projI_mul_projN,
    smosTrace_projN_mul_projI, smosTrace_projI_mul_projO,
    smosTrace_projO_mul_projI, smosTrace_projN_mul_projO,
    smosTrace_projO_mul_projN, sub_zero]
  abel

/-- `thm:SMOS-trace-Pythagoras` (projection panel): `P_I`, `P_N`, `P_O` are
mutually orthogonal Hermitian projections. -/
theorem smos_trace_pythagoras_projections :
    ((smosTraceRangeProj I₀)ᴴ = smosTraceRangeProj I₀ ∧
        smosTraceRangeProj I₀ * smosTraceRangeProj I₀ = smosTraceRangeProj I₀) ∧
      ((smosTraceRangeProj (smosTraceNuisance I₀ N₀))ᴴ
          = smosTraceRangeProj (smosTraceNuisance I₀ N₀) ∧
        smosTraceRangeProj (smosTraceNuisance I₀ N₀)
            * smosTraceRangeProj (smosTraceNuisance I₀ N₀)
          = smosTraceRangeProj (smosTraceNuisance I₀ N₀)) ∧
      ((smosTraceRangeProj (smosTraceComposite I₀ N₀ O))ᴴ
          = smosTraceRangeProj (smosTraceComposite I₀ N₀ O) ∧
        smosTraceRangeProj (smosTraceComposite I₀ N₀ O)
            * smosTraceRangeProj (smosTraceComposite I₀ N₀ O)
          = smosTraceRangeProj (smosTraceComposite I₀ N₀ O)) ∧
      smosTraceRangeProj I₀ * smosTraceRangeProj (smosTraceNuisance I₀ N₀) = 0 ∧
      smosTraceRangeProj (smosTraceNuisance I₀ N₀) * smosTraceRangeProj I₀ = 0 ∧
      smosTraceRangeProj I₀ * smosTraceRangeProj (smosTraceComposite I₀ N₀ O)
        = 0 ∧
      smosTraceRangeProj (smosTraceComposite I₀ N₀ O) * smosTraceRangeProj I₀
        = 0 ∧
      smosTraceRangeProj (smosTraceNuisance I₀ N₀)
          * smosTraceRangeProj (smosTraceComposite I₀ N₀ O) = 0 ∧
      smosTraceRangeProj (smosTraceComposite I₀ N₀ O)
          * smosTraceRangeProj (smosTraceNuisance I₀ N₀) = 0 :=
  ⟨⟨smosTraceRangeProj_conjTranspose I₀, smosTraceRangeProj_idem I₀⟩,
    ⟨smosTraceRangeProj_conjTranspose _, smosTraceRangeProj_idem _⟩,
    ⟨smosTraceRangeProj_conjTranspose _, smosTraceRangeProj_idem _⟩,
    smosTrace_projI_mul_projN I₀ N₀, smosTrace_projN_mul_projI I₀ N₀,
    smosTrace_projI_mul_projO I₀ N₀ O, smosTrace_projO_mul_projI I₀ N₀ O,
    smosTrace_projN_mul_projO I₀ N₀ O, smosTrace_projO_mul_projN I₀ N₀ O⟩

omit [Fintype s] [DecidableEq s] in
/-- `thm:SMOS-trace-Pythagoras` (source decomposition, eq.
`SMOS-trace-source-decomposition`):
`S_sc = P_I S_sc + P_N S_sc + P_O S_sc + S_new`. -/
theorem smos_trace_source_decomposition :
    Ssc = smosTraceRangeProj I₀ * Ssc
        + smosTraceRangeProj (smosTraceNuisance I₀ N₀) * Ssc
        + smosTraceRangeProj (smosTraceComposite I₀ N₀ O) * Ssc
        + smosTraceNewSource I₀ N₀ O Ssc := by
  simp only [smosTraceNewSource, Matrix.sub_mul, Matrix.one_mul]
  abel

omit [DecidableEq m] in
/-- Gram collapse for a Hermitian idempotent: `(PX)ᴴ(PX) = Xᴴ(PX)`. -/
theorem smosTrace_gram_collapse {κ : Type*} (P : Matrix m m ℂ)
    (X : Matrix m κ ℂ) (hH : Pᴴ = P) (hI : P * P = P) :
    (P * X)ᴴ * (P * X) = Xᴴ * (P * X) := by
  rw [Matrix.conjTranspose_mul, hH, Matrix.mul_assoc,
    ← Matrix.mul_assoc P P X, hI]

omit [Fintype s] [DecidableEq s] in
/-- `thm:SMOS-trace-Pythagoras` (Gram Pythagoras, eq.
`SMOS-trace-Gram-Pythagoras`):
`S_scᴴ S_sc = G_abs + G_triv + G_β + G_new`, the Grams of the four mutually
orthogonal summands. -/
theorem smos_trace_gram_pythagoras :
    Sscᴴ * Ssc
      = (smosTraceRangeProj I₀ * Ssc)ᴴ * (smosTraceRangeProj I₀ * Ssc)
        + (smosTraceRangeProj (smosTraceNuisance I₀ N₀) * Ssc)ᴴ
            * (smosTraceRangeProj (smosTraceNuisance I₀ N₀) * Ssc)
        + (smosTraceRangeProj (smosTraceComposite I₀ N₀ O) * Ssc)ᴴ
            * (smosTraceRangeProj (smosTraceComposite I₀ N₀ O) * Ssc)
        + (smosTraceNewSource I₀ N₀ O Ssc)ᴴ * smosTraceNewSource I₀ N₀ O Ssc := by
  rw [smosTrace_gram_collapse (smosTraceRangeProj I₀) Ssc
      (smosTraceRangeProj_conjTranspose I₀) (smosTraceRangeProj_idem I₀),
    smosTrace_gram_collapse (smosTraceRangeProj (smosTraceNuisance I₀ N₀)) Ssc
      (smosTraceRangeProj_conjTranspose _) (smosTraceRangeProj_idem _),
    smosTrace_gram_collapse (smosTraceRangeProj (smosTraceComposite I₀ N₀ O))
      Ssc (smosTraceRangeProj_conjTranspose _) (smosTraceRangeProj_idem _)]
  have hnew : (smosTraceNewSource I₀ N₀ O Ssc)ᴴ * smosTraceNewSource I₀ N₀ O Ssc
      = Sscᴴ * smosTraceNewSource I₀ N₀ O Ssc := by
    have h := smosTrace_gram_collapse
      (1 - smosTraceRangeProj I₀ - smosTraceRangeProj (smosTraceNuisance I₀ N₀)
        - smosTraceRangeProj (smosTraceComposite I₀ N₀ O)) Ssc
      (smosTrace_resid3_conjTranspose I₀ N₀ O) (smosTrace_resid3_idem I₀ N₀ O)
    simp only [smosTraceNewSource]
    exact h
  rw [hnew, ← Matrix.mul_add, ← Matrix.mul_add, ← Matrix.mul_add,
    ← smos_trace_source_decomposition I₀ N₀ O Ssc]

omit [Fintype s] [DecidableEq s] in
/-- The composite-anomaly synthesis of `β` (right-associated form):
`O₁ β = P_O ((I - P_I - P_N) S_sc)`. -/
theorem smosTrace_composite_mul_beta :
    smosTraceComposite I₀ N₀ O * smosTraceBetaMap I₀ N₀ O Ssc
      = smosTraceRangeProj (smosTraceComposite I₀ N₀ O)
          * ((1 - smosTraceRangeProj I₀
              - smosTraceRangeProj (smosTraceNuisance I₀ N₀)) * Ssc) := by
  simp only [smosTraceBetaMap, smosTraceRangeProj, Matrix.mul_assoc]

omit [Fintype s] [DecidableEq s] in
/-- `thm:SMOS-trace-Pythagoras` (T3, supported coefficient synthesis): the
minimum supported coefficient map `β` synthesizes the represented composite
anomaly, `O₁ β = P_O S_sc`. -/
theorem smos_trace_beta_synthesis :
    smosTraceComposite I₀ N₀ O * smosTraceBetaMap I₀ N₀ O Ssc
      = smosTraceRangeProj (smosTraceComposite I₀ N₀ O) * Ssc := by
  rw [smosTrace_composite_mul_beta, ← Matrix.mul_assoc]
  have h : smosTraceRangeProj (smosTraceComposite I₀ N₀ O)
      * (1 - smosTraceRangeProj I₀
          - smosTraceRangeProj (smosTraceNuisance I₀ N₀))
      = smosTraceRangeProj (smosTraceComposite I₀ N₀ O) := by
    rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one,
      smosTrace_projO_mul_projI, smosTrace_projO_mul_projN, sub_zero, sub_zero]
  rw [h]

omit [DecidableEq s] in
open scoped ComplexOrder in
/-- `thm:SMOS-trace-Pythagoras` (eq. `SMOS-trace-new-zero`):
`G_new = 0` iff the scale source range is contained in the declared bank range
`Ran(I₀, N₀, O)`. -/
theorem smos_trace_new_gram_zero_iff :
    (smosTraceNewSource I₀ N₀ O Ssc)ᴴ * smosTraceNewSource I₀ N₀ O Ssc = 0
      ↔ LinearMap.range Ssc.mulVecLin
          ≤ LinearMap.range I₀.mulVecLin ⊔ LinearMap.range N₀.mulVecLin
            ⊔ LinearMap.range O.mulVecLin := by
  have hI_mem : ∀ v, I₀ *ᵥ v ∈ LinearMap.range I₀.mulVecLin
      ⊔ LinearMap.range N₀.mulVecLin ⊔ LinearMap.range O.mulVecLin :=
    fun v => Submodule.mem_sup_left (Submodule.mem_sup_left
      (LinearMap.mem_range.mpr ⟨v, Matrix.mulVecLin_apply I₀ v⟩))
  have hN_mem : ∀ v, N₀ *ᵥ v ∈ LinearMap.range I₀.mulVecLin
      ⊔ LinearMap.range N₀.mulVecLin ⊔ LinearMap.range O.mulVecLin :=
    fun v => Submodule.mem_sup_left (Submodule.mem_sup_right
      (LinearMap.mem_range.mpr ⟨v, Matrix.mulVecLin_apply N₀ v⟩))
  have hO_mem : ∀ v, O *ᵥ v ∈ LinearMap.range I₀.mulVecLin
      ⊔ LinearMap.range N₀.mulVecLin ⊔ LinearMap.range O.mulVecLin :=
    fun v => Submodule.mem_sup_right
      (LinearMap.mem_range.mpr ⟨v, Matrix.mulVecLin_apply O v⟩)
  have hPI_mem : ∀ v, smosTraceRangeProj I₀ *ᵥ v ∈ LinearMap.range I₀.mulVecLin
      ⊔ LinearMap.range N₀.mulVecLin ⊔ LinearMap.range O.mulVecLin := by
    intro v
    obtain ⟨z, hz⟩ := smosTraceRangeProj_mulVec_mem I₀ v
    rw [← hz, Matrix.mulVecLin_apply]
    exact hI_mem z
  have hN1_mem : ∀ v, smosTraceNuisance I₀ N₀ *ᵥ v
      ∈ LinearMap.range I₀.mulVecLin ⊔ LinearMap.range N₀.mulVecLin
        ⊔ LinearMap.range O.mulVecLin := by
    intro v
    have e : smosTraceNuisance I₀ N₀ *ᵥ v
        = N₀ *ᵥ v - smosTraceRangeProj I₀ *ᵥ (N₀ *ᵥ v) := by
      simp only [smosTraceNuisance]
      rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [e]
    exact Submodule.sub_mem _ (hN_mem v) (hPI_mem _)
  have hPN_mem : ∀ v, smosTraceRangeProj (smosTraceNuisance I₀ N₀) *ᵥ v
      ∈ LinearMap.range I₀.mulVecLin ⊔ LinearMap.range N₀.mulVecLin
        ⊔ LinearMap.range O.mulVecLin := by
    intro v
    obtain ⟨z, hz⟩ := smosTraceRangeProj_mulVec_mem (smosTraceNuisance I₀ N₀) v
    rw [← hz, Matrix.mulVecLin_apply]
    exact hN1_mem z
  have hO1_mem : ∀ v, smosTraceComposite I₀ N₀ O *ᵥ v
      ∈ LinearMap.range I₀.mulVecLin ⊔ LinearMap.range N₀.mulVecLin
        ⊔ LinearMap.range O.mulVecLin := by
    intro v
    have e : smosTraceComposite I₀ N₀ O *ᵥ v
        = O *ᵥ v - smosTraceRangeProj I₀ *ᵥ (O *ᵥ v)
          - smosTraceRangeProj (smosTraceNuisance I₀ N₀) *ᵥ (O *ᵥ v) := by
      simp only [smosTraceComposite]
      rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.sub_mulVec,
        Matrix.one_mulVec]
    rw [e]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ (hO_mem v) (hPI_mem _))
      (hPN_mem _)
  have hPO_mem : ∀ v, smosTraceRangeProj (smosTraceComposite I₀ N₀ O) *ᵥ v
      ∈ LinearMap.range I₀.mulVecLin ⊔ LinearMap.range N₀.mulVecLin
        ⊔ LinearMap.range O.mulVecLin := by
    intro v
    obtain ⟨z, hz⟩ := smosTraceRangeProj_mulVec_mem (smosTraceComposite I₀ N₀ O) v
    rw [← hz, Matrix.mulVecLin_apply]
    exact hO1_mem z
  constructor
  · intro hG
    have hSnew : smosTraceNewSource I₀ N₀ O Ssc = 0 :=
      Matrix.conjTranspose_mul_self_eq_zero.mp hG
    intro y hy
    obtain ⟨x, rfl⟩ := hy
    rw [Matrix.mulVecLin_apply]
    have hdec := smos_trace_source_decomposition I₀ N₀ O Ssc
    rw [hSnew, add_zero] at hdec
    rw [hdec, Matrix.add_mulVec, Matrix.add_mulVec]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · rw [← Matrix.mulVec_mulVec]
      exact hPI_mem _
    · rw [← Matrix.mulVec_mulVec]
      exact hPN_mem _
    · rw [← Matrix.mulVec_mulVec]
      exact hPO_mem _
  · intro hle
    have hvec : ∀ x, smosTraceNewSource I₀ N₀ O Ssc *ᵥ x = 0 := by
      intro x
      have hmem : Ssc *ᵥ x ∈ LinearMap.range I₀.mulVecLin
          ⊔ LinearMap.range N₀.mulVecLin ⊔ LinearMap.range O.mulVecLin :=
        hle (LinearMap.mem_range.mpr ⟨x, Matrix.mulVecLin_apply Ssc x⟩)
      obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hmem
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hu
      obtain ⟨va, hva⟩ := ha
      obtain ⟨vb, hvb⟩ := hb
      obtain ⟨vw, hvw⟩ := hw
      have e : smosTraceNewSource I₀ N₀ O Ssc *ᵥ x
          = (1 - smosTraceRangeProj I₀
              - smosTraceRangeProj (smosTraceNuisance I₀ N₀)
              - smosTraceRangeProj (smosTraceComposite I₀ N₀ O))
            *ᵥ (Ssc *ᵥ x) := by
        simp only [smosTraceNewSource]
        rw [← Matrix.mulVec_mulVec]
      rw [e, ← huw, ← hab, ← hva, ← hvb, ← hvw, Matrix.mulVecLin_apply,
        Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_add,
        Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec, smosTrace_resid3_mul_I, smosTrace_resid3_mul_N,
        smosTrace_resid3_mul_O, Matrix.zero_mulVec, Matrix.zero_mulVec,
        Matrix.zero_mulVec, add_zero, add_zero]
    have hzero : smosTraceNewSource I₀ N₀ O Ssc = 0 :=
      smosTrace_eq_zero_of_mulVec _ hvec
    rw [hzero, Matrix.conjTranspose_zero, Matrix.mul_zero]

end TracePythagoras

/-! ## `thm:SMOS-trace-scheme` -/

section TraceScheme

variable {m p q r s p' : Type*} [Fintype m] [DecidableEq m]
  [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
  [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
  [Fintype p'] [DecidableEq p']
variable (I₀ : Matrix m p ℂ) (N₀ : Matrix m q ℂ) (O : Matrix m r ℂ)
  (Ssc : Matrix m s ℂ) (I₀' : Matrix m p' ℂ)

/-- `thm:SMOS-trace-scheme` (eq. `SMOS-efficient-operator-scheme`): an
admissible scheme change `N₀' = N₀U`, `O' = OM + N₀R + I₀R₀` preserving the
identity source range acts on the efficient operator by `O₁' = O₁ M`. -/
theorem smos_trace_scheme_efficient_operator
    (hPI : smosTraceRangeProj I₀' = smosTraceRangeProj I₀)
    (U : Matrix q q ℂ) [Invertible U] (M : Matrix r r ℂ) [Invertible M]
    (R : Matrix q r ℂ) (R₀ : Matrix p r ℂ) :
    smosTraceComposite I₀' (N₀ * U) (O * M + N₀ * R + I₀ * R₀)
      = smosTraceComposite I₀ N₀ O * M := by
  have hN' : smosTraceNuisance I₀' (N₀ * U) = smosTraceNuisance I₀ N₀ * U := by
    simp only [smosTraceNuisance, hPI, Matrix.mul_assoc]
  have hPN' : smosTraceRangeProj (smosTraceNuisance I₀' (N₀ * U))
      = smosTraceRangeProj (smosTraceNuisance I₀ N₀) := by
    rw [hN']
    exact smosTraceRangeProj_mul_invertible (smosTraceNuisance I₀ N₀) U
  simp only [smosTraceComposite, hPI, hPN']
  rw [Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, smosTrace_resid2_mul_N, smosTrace_resid2_mul_I,
    Matrix.zero_mul, Matrix.zero_mul, add_zero, add_zero]

/-- `thm:SMOS-trace-scheme` (anomaly range projector invariance):
`P_{O'} = P_O`. -/
theorem smos_trace_scheme_range_invariance
    (hPI : smosTraceRangeProj I₀' = smosTraceRangeProj I₀)
    (U : Matrix q q ℂ) [Invertible U] (M : Matrix r r ℂ) [Invertible M]
    (R : Matrix q r ℂ) (R₀ : Matrix p r ℂ) :
    smosTraceRangeProj (smosTraceComposite I₀' (N₀ * U) (O * M + N₀ * R + I₀ * R₀))
      = smosTraceRangeProj (smosTraceComposite I₀ N₀ O) := by
  rw [smos_trace_scheme_efficient_operator I₀ N₀ O I₀' hPI U M R R₀]
  exact smosTraceRangeProj_mul_invertible (smosTraceComposite I₀ N₀ O) M

omit [Fintype s] [DecidableEq s] in
/-- `thm:SMOS-trace-scheme` (eq. `SMOS-anomaly-range-invariance`): the
represented anomaly source `P_{O'} S_sc = P_O S_sc` is scheme invariant as an
ambient physical vector. -/
theorem smos_trace_scheme_anomaly_source_invariance
    (hPI : smosTraceRangeProj I₀' = smosTraceRangeProj I₀)
    (U : Matrix q q ℂ) [Invertible U] (M : Matrix r r ℂ) [Invertible M]
    (R : Matrix q r ℂ) (R₀ : Matrix p r ℂ) :
    smosTraceRangeProj (smosTraceComposite I₀' (N₀ * U) (O * M + N₀ * R + I₀ * R₀))
        * Ssc
      = smosTraceRangeProj (smosTraceComposite I₀ N₀ O) * Ssc := by
  rw [smos_trace_scheme_range_invariance I₀ N₀ O I₀' hPI U M R R₀]

/-- `thm:SMOS-trace-scheme` (eq. `SMOS-anomaly-coordinate-scheme`, Gram part):
`G_O' = Mᴴ G_O M`. -/
theorem smos_trace_scheme_gram_congruence
    (hPI : smosTraceRangeProj I₀' = smosTraceRangeProj I₀)
    (U : Matrix q q ℂ) [Invertible U] (M : Matrix r r ℂ) [Invertible M]
    (R : Matrix q r ℂ) (R₀ : Matrix p r ℂ) :
    (smosTraceComposite I₀' (N₀ * U) (O * M + N₀ * R + I₀ * R₀))ᴴ
        * smosTraceComposite I₀' (N₀ * U) (O * M + N₀ * R + I₀ * R₀)
      = Mᴴ * ((smosTraceComposite I₀ N₀ O)ᴴ * smosTraceComposite I₀ N₀ O) * M := by
  rw [smos_trace_scheme_efficient_operator I₀ N₀ O I₀' hPI U M R R₀,
    Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

omit [Fintype s] [DecidableEq s] in
/-- `thm:SMOS-trace-scheme` (eq. `SMOS-anomaly-coordinate-scheme`, coefficient
part): on the supported operator quotient the coefficient map transforms by
`β' = M⁻¹ β`, rendered as `O₁' β' = O₁' (M⁻¹ β)`, i.e. equality modulo
`ker O₁'`. -/
theorem smos_trace_scheme_beta_covariance
    (hPI : smosTraceRangeProj I₀' = smosTraceRangeProj I₀)
    (U : Matrix q q ℂ) [Invertible U] (M : Matrix r r ℂ) [Invertible M]
    (R : Matrix q r ℂ) (R₀ : Matrix p r ℂ) :
    smosTraceComposite I₀' (N₀ * U) (O * M + N₀ * R + I₀ * R₀)
        * smosTraceBetaMap I₀' (N₀ * U) (O * M + N₀ * R + I₀ * R₀) Ssc
      = smosTraceComposite I₀' (N₀ * U) (O * M + N₀ * R + I₀ * R₀)
        * (M⁻¹ * smosTraceBetaMap I₀ N₀ O Ssc) := by
  have hN' : smosTraceNuisance I₀' (N₀ * U) = smosTraceNuisance I₀ N₀ * U := by
    simp only [smosTraceNuisance, hPI, Matrix.mul_assoc]
  have hPN' : smosTraceRangeProj (smosTraceNuisance I₀' (N₀ * U))
      = smosTraceRangeProj (smosTraceNuisance I₀ N₀) := by
    rw [hN']
    exact smosTraceRangeProj_mul_invertible (smosTraceNuisance I₀ N₀) U
  have heff := smos_trace_scheme_efficient_operator I₀ N₀ O I₀' hPI U M R R₀
  have hPO' := smos_trace_scheme_range_invariance I₀ N₀ O I₀' hPI U M R R₀
  have hL : smosTraceComposite I₀' (N₀ * U) (O * M + N₀ * R + I₀ * R₀)
      * smosTraceBetaMap I₀' (N₀ * U) (O * M + N₀ * R + I₀ * R₀) Ssc
      = smosTraceRangeProj (smosTraceComposite I₀ N₀ O)
        * ((1 - smosTraceRangeProj I₀
            - smosTraceRangeProj (smosTraceNuisance I₀ N₀)) * Ssc) := by
    rw [smosTrace_composite_mul_beta, hPO', hPI, hPN']
  have hR : smosTraceComposite I₀' (N₀ * U) (O * M + N₀ * R + I₀ * R₀)
      * (M⁻¹ * smosTraceBetaMap I₀ N₀ O Ssc)
      = smosTraceRangeProj (smosTraceComposite I₀ N₀ O)
        * ((1 - smosTraceRangeProj I₀
            - smosTraceRangeProj (smosTraceNuisance I₀ N₀)) * Ssc) := by
    rw [heff, Matrix.mul_assoc (smosTraceComposite I₀ N₀ O) M,
      ← Matrix.mul_assoc M M⁻¹, Matrix.mul_inv_of_invertible, Matrix.one_mul,
      smosTrace_composite_mul_beta]
  rw [hL, hR]

omit [Fintype s] [DecidableEq s] in
/-- `thm:SMOS-trace-scheme` (eq. `SMOS-anomaly-Gram-invariance`): the physical
projected-source Gram `S_scᴴ P_{O'} S_sc = S_scᴴ P_O S_sc` is scheme
invariant. -/
theorem smos_trace_scheme_gram_invariance
    (hPI : smosTraceRangeProj I₀' = smosTraceRangeProj I₀)
    (U : Matrix q q ℂ) [Invertible U] (M : Matrix r r ℂ) [Invertible M]
    (R : Matrix q r ℂ) (R₀ : Matrix p r ℂ) :
    Sscᴴ * smosTraceRangeProj
          (smosTraceComposite I₀' (N₀ * U) (O * M + N₀ * R + I₀ * R₀)) * Ssc
      = Sscᴴ * smosTraceRangeProj (smosTraceComposite I₀ N₀ O) * Ssc := by
  rw [smos_trace_scheme_range_invariance I₀ N₀ O I₀' hPI U M R R₀]

omit [DecidableEq s] in
/-- `thm:SMOS-trace-scheme` (final clause): vanishing and rank of the
represented anomaly source are scheme invariant. -/
theorem smos_trace_scheme_invariants
    (hPI : smosTraceRangeProj I₀' = smosTraceRangeProj I₀)
    (U : Matrix q q ℂ) [Invertible U] (M : Matrix r r ℂ) [Invertible M]
    (R : Matrix q r ℂ) (R₀ : Matrix p r ℂ) :
    (smosTraceRangeProj
          (smosTraceComposite I₀' (N₀ * U) (O * M + N₀ * R + I₀ * R₀)) * Ssc = 0
        ↔ smosTraceRangeProj (smosTraceComposite I₀ N₀ O) * Ssc = 0) ∧
      (smosTraceRangeProj
          (smosTraceComposite I₀' (N₀ * U) (O * M + N₀ * R + I₀ * R₀)) * Ssc).rank
        = (smosTraceRangeProj (smosTraceComposite I₀ N₀ O) * Ssc).rank := by
  have h := smos_trace_scheme_anomaly_source_invariance I₀ N₀ O Ssc I₀' hPI U M R R₀
  exact ⟨by rw [h], by rw [h]⟩

end TraceScheme

/-! ## `thm:SMQG-Feshbach-covariance` -/

section FeshbachCovariance

variable {ρ τ : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype τ] [DecidableEq τ]
variable (A : Matrix ρ ρ ℂ) (B : Matrix ρ τ ℂ) (C : Matrix τ ρ ℂ)
  (E : Matrix τ τ ℂ)

/-- `thm:SMQG-Feshbach-covariance` (i), eq. QG.29: exact block LDU
factorization of the retained/tail precision block through the Schur operator
`S = A - BE⁻¹C`. -/
theorem smqg_feshbach_ldu [Invertible E] :
    fromBlocks A B C E
      = fromBlocks 1 (B * E⁻¹) 0 1
        * fromBlocks (A - B * E⁻¹ * C) 0 0 E
        * fromBlocks 1 0 (E⁻¹ * C) 1 := by
  have h := Matrix.fromBlocks_eq_of_invertible₂₂ A B C E
  rw [Matrix.invOf_eq_nonsing_inv] at h
  exact h

/-- `thm:SMQG-Feshbach-covariance` (ii), eq. QG.30: the hard determinant
factorization `det D = det E · det S`. -/
theorem smqg_feshbach_det [Invertible E] :
    (fromBlocks A B C E).det = E.det * (A - B * E⁻¹ * C).det := by
  have h := Matrix.det_fromBlocks₂₂ A B C E
  rw [Matrix.invOf_eq_nonsing_inv] at h
  exact h

/-- `thm:SMQG-Feshbach-covariance` (iii), eq. QG.31: on the invertible branch
the retained compression of the inverse is the inverse Schur operator,
`Π_{R₊} D⁻¹ ι_{R₋} = S⁻¹`. -/
theorem smqg_feshbach_retained_inverse [Invertible E]
    [Invertible (A - B * E⁻¹ * C)] :
    ((fromBlocks A B C E)⁻¹).toBlocks₁₁ = (A - B * E⁻¹ * C)⁻¹ := by
  haveI hS' : Invertible (A - B * ⅟E * C) :=
    (‹Invertible (A - B * E⁻¹ * C)›).copy _
      (by rw [Matrix.invOf_eq_nonsing_inv])
  haveI hD : Invertible (fromBlocks A B C E) :=
    Matrix.fromBlocks₂₂Invertible A B C E
  have hinv := Matrix.invOf_fromBlocks₂₂_eq A B C E
  rw [← Matrix.invOf_eq_nonsing_inv (fromBlocks A B C E), hinv,
    Matrix.toBlocks_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv (A - B * ⅟E * C),
    Matrix.invOf_eq_nonsing_inv E]

/-- `thm:SMQG-Feshbach-covariance` (iv), eq. QG.32: after the frozen
antiunitary source identification, the one-particle reflected covariance is
the Schur compression of the physical reflected source maps,
`P = J₊ᴴ S⁻¹ J₋`. -/
theorem smqg_feshbach_reflected_covariance [Invertible E]
    [Invertible (A - B * E⁻¹ * C)] {eph : Type*}
    (Jp Jm : Matrix ρ eph ℂ) :
    Jpᴴ * ((fromBlocks A B C E)⁻¹).toBlocks₁₁ * Jm
      = Jpᴴ * (A - B * E⁻¹ * C)⁻¹ * Jm := by
  rw [smqg_feshbach_retained_inverse A B C E]

/-- `thm:SMQG-Feshbach-covariance` (bundle): the complete conditional
reflected word kernel depends on the tail only through the Schur operator and
the scalar hard determinant factor. -/
theorem smqg_feshbach_covariance [Invertible E]
    [Invertible (A - B * E⁻¹ * C)] {eph : Type*} (Jp Jm : Matrix ρ eph ℂ) :
    (fromBlocks A B C E
        = fromBlocks 1 (B * E⁻¹) 0 1
          * fromBlocks (A - B * E⁻¹ * C) 0 0 E
          * fromBlocks 1 0 (E⁻¹ * C) 1) ∧
      (fromBlocks A B C E).det = E.det * (A - B * E⁻¹ * C).det ∧
      ((fromBlocks A B C E)⁻¹).toBlocks₁₁ = (A - B * E⁻¹ * C)⁻¹ ∧
      Jpᴴ * ((fromBlocks A B C E)⁻¹).toBlocks₁₁ * Jm
        = Jpᴴ * (A - B * E⁻¹ * C)⁻¹ * Jm :=
  ⟨smqg_feshbach_ldu A B C E, smqg_feshbach_det A B C E,
    smqg_feshbach_retained_inverse A B C E,
    smqg_feshbach_reflected_covariance A B C E Jp Jm⟩

end FeshbachCovariance

/-! ## `thm:SMQG-relation-descent` -/

section RelationDescent

/-- The spectral Hermitian Moore–Penrose inverse commutes with its matrix. -/
theorem smqg_hermitian_pinv_comm {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    A * HermitianMoorePenroseInverse.hermitianMoorePenroseInverse A hA
      = HermitianMoorePenroseInverse.hermitianMoorePenroseInverse A hA * A := by
  let phi := conjStarAlgAut Complex _ hA.eigenvectorUnitary
  let D : Matrix n n ℂ := Matrix.diagonal (Complex.ofReal ∘ hA.eigenvalues)
  let Rm : Matrix n n ℂ :=
    Matrix.diagonal (HermitianMoorePenroseInverse.reciprocalEigenvalue A hA)
  have hAphi : A = phi D := by simpa [phi, D] using hA.spectral_theorem
  have hDR : D * Rm = Rm * D := by
    have hgen : ∀ d e : n → ℂ,
        Matrix.diagonal d * Matrix.diagonal e
          = Matrix.diagonal e * Matrix.diagonal d := by
      intro d e
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      exact mul_comm _ _
    exact hgen _ _
  change A * phi Rm = phi Rm * A
  rw [hAphi]
  calc phi D * phi Rm = phi (D * Rm) := (map_mul phi D Rm).symm
    _ = phi (Rm * D) := by rw [hDR]
    _ = phi Rm * phi D := map_mul phi Rm D

variable {c f e : Type*} [Fintype c] [DecidableEq c] [Fintype f] [Fintype e]
variable (W₀ : Matrix f c ℂ) (W : Matrix e c ℂ) (Gam : Matrix e e ℂ)

/-- Ordinary word support projector `P_H = H H†` with `H = W₀ᴴW₀`. -/
noncomputable def smqgWordSupport (W₀ : Matrix f c ℂ) : Matrix c c ℂ :=
  (W₀ᴴ * W₀) * smosTraceGramPinv W₀

/-- The ordinary synthesis annihilates the co-support: `W₀ (I - H†H) = 0`. -/
theorem smqg_kernel_annihilation :
    W₀ * (1 - smosTraceGramPinv W₀ * (W₀ᴴ * W₀)) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, smosTraceGramPinv_cancel, sub_self]

omit [Fintype e] in
/-- Descent through the word relations kills the co-support:
`W (I - H†H) = 0` whenever `ker W₀ ⊆ ker W`. -/
theorem smqg_descent_annihilation
    (hdesc : ∀ x : c → ℂ, W₀ *ᵥ x = 0 → W *ᵥ x = 0) :
    W * (1 - smosTraceGramPinv W₀ * (W₀ᴴ * W₀)) = 0 := by
  apply smosTrace_eq_zero_of_mulVec
  intro x
  rw [← Matrix.mulVec_mulVec]
  apply hdesc
  rw [Matrix.mulVec_mulVec, smqg_kernel_annihilation, Matrix.zero_mulVec]

/-- The co-support of `P_H = H H†` is the conjugate transpose of the
co-support of `H† H`. -/
theorem smqg_word_cosupport_conjTranspose :
    ((1 : Matrix c c ℂ) - smosTraceGramPinv W₀ * (W₀ᴴ * W₀))ᴴ
      = 1 - smqgWordSupport W₀ := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    Matrix.conjTranspose_mul, smosTraceGramPinv_conjTranspose,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    smqgWordSupport]

/-- Left relation-residual matrix `(I - P_H) K_C` for the Gaussian word-kernel
prediction `K_C = Wᴴ Γ_∧(P) W`. -/
noncomputable def smqgLeftResidual (W₀ : Matrix f c ℂ) (W : Matrix e c ℂ)
    (Gam : Matrix e e ℂ) : Matrix c c ℂ :=
  (1 - smqgWordSupport W₀) * (Wᴴ * Gam * W)

/-- Right relation-residual matrix `K_C (I - P_H)` for the Gaussian
word-kernel prediction. -/
noncomputable def smqgRightResidual (W₀ : Matrix f c ℂ) (W : Matrix e c ℂ)
    (Gam : Matrix e e ℂ) : Matrix c c ℂ :=
  (Wᴴ * Gam * W) * (1 - smqgWordSupport W₀)

/-- `thm:SMQG-relation-descent` (left residual): if the one-sided synthesis
`W` descends through the ordinary word relations, the Gaussian word kernel
`K_C = Wᴴ Γ_∧(P) W` satisfies `(I - P_H) K_C = 0`. -/
theorem smqg_relation_descent_residual_left
    (hdesc : ∀ x : c → ℂ, W₀ *ᵥ x = 0 → W *ᵥ x = 0) :
    smqgLeftResidual W₀ W Gam = 0 := by
  unfold smqgLeftResidual
  have h1 := smqg_descent_annihilation W₀ W hdesc
  have h2 : (1 - smqgWordSupport W₀) * Wᴴ = 0 := by
    rw [← smqg_word_cosupport_conjTranspose, ← Matrix.conjTranspose_mul, h1,
      Matrix.conjTranspose_zero]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.zero_mul,
    Matrix.zero_mul]

/-- `thm:SMQG-relation-descent` (right residual): under descent the Gaussian
word kernel also satisfies `K_C (I - P_H) = 0`. -/
theorem smqg_relation_descent_residual_right
    (hdesc : ∀ x : c → ℂ, W₀ *ᵥ x = 0 → W *ᵥ x = 0) :
    smqgRightResidual W₀ W Gam = 0 := by
  unfold smqgRightResidual
  have hcomm : (W₀ᴴ * W₀) * smosTraceGramPinv W₀
      = smosTraceGramPinv W₀ * (W₀ᴴ * W₀) :=
    smqg_hermitian_pinv_comm (W₀ᴴ * W₀)
      (Matrix.isHermitian_conjTranspose_mul_self W₀)
  have h1 : W * (1 - smqgWordSupport W₀) = 0 := by
    rw [smqgWordSupport, hcomm]
    exact smqg_descent_annihilation W₀ W hdesc
  rw [Matrix.mul_assoc, h1, Matrix.mul_zero]

/-- Relation residual `Δ_rel = ‖(I-P_H)K_C‖²_HS + ‖K_C(I-P_H)‖²_HS` for the
Gaussian word-kernel prediction `K_C = Wᴴ Γ_∧(P) W`. -/
noncomputable def smqgRelationResidual (W₀ : Matrix f c ℂ) (W : Matrix e c ℂ)
    (Gam : Matrix e e ℂ) : ℝ :=
  (∑ i, ∑ j, ‖smqgLeftResidual W₀ W Gam i j‖ ^ 2)
    + ∑ i, ∑ j, ‖smqgRightResidual W₀ W Gam i j‖ ^ 2

/-- `thm:SMQG-relation-descent` (eq. QG.45): if the one-sided synthesis `W` is
well defined on the ordinary physical word quotient, the Gaussian prediction
automatically has vanishing relation residual `Δ_rel = 0`. -/
theorem smqg_relation_descent
    (hdesc : ∀ x : c → ℂ, W₀ *ᵥ x = 0 → W *ᵥ x = 0) :
    smqgRelationResidual W₀ W Gam = 0 := by
  unfold smqgRelationResidual
  rw [smqg_relation_descent_residual_left W₀ W Gam hdesc,
    smqg_relation_descent_residual_right W₀ W Gam hdesc]
  simp

/-- `thm:SMQG-relation-descent` (converse): a positive relation residual
proves that the proposed one-sided Gaussian synthesis and the ordinary word
relations cannot both occur on the declared physical carrier. -/
theorem smqg_relation_descent_converse
    (hpos : 0 < smqgRelationResidual W₀ W Gam) :
    ¬ (∀ x : c → ℂ, W₀ *ᵥ x = 0 → W *ᵥ x = 0) :=
  fun hdesc => hpos.ne' (smqg_relation_descent W₀ W Gam hdesc)

end RelationDescent

end NCG
