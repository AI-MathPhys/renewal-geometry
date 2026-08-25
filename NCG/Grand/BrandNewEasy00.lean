/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Brand-new easy records, batch 00 (Gran-Tensor manuscript)

Exact formalizations of the following brand-new manuscript records:

* `cor:GTLOC-local-counterterm-target` — target-relative local counterterm
  independence: the target is representative-independent exactly when it
  annihilates `Ran Π_ct`, and the minimum number of additional scalar Reads
  is `rank (T|_{Ran Π_ct})`.
* `cor:SMQG-assembly-before-elimination` — the retained covariance block of the
  completely assembled precision is the inverse of the Schur complement of the
  *summed* blocks, and separately eliminating the sectors and adding their
  Schur operators gives a different result (explicit counterexample, which
  propagates inside `P = S⁻¹`).
* `cth:GT-counterfeit-support` — the explicit `1×2/2×2` counterfeit-support
  witness (CERT.9): the counterfeit projection passes the formal test and the
  apparent Schur value is three, but the true support projection fails the
  test and the full block form takes the value `-1`.
* `cth:GTLOC-local-Gram-no-inverse` — path-Laplacian Gram floors
  `G_N = ε_N I + L_N`: uniformly bounded finite propagation and uniformly
  bounded weighted Schur norm, yet
  `‖G_N^{-1/2}‖_{μ,Sch} ≥ ‖G_N^{-1/2}‖ = ε_N^{-1/2} → ∞`.
* `cth:GTLOC-local-endpoint-hidden-route` — on `ℓ²({0,N})` with `H = 0` and
  the long hop `V_N`, the first Duhamel endpoint response vanishes while the
  pair response equals `t²`, although the intermediate state visits the far
  site.
* `cth:SMOS-Ward-source-escape` — nested cutoff spans with escaping stress
  source: `Q_r e_n = 0` for `n > r`.
* `cth:SMOS-energy-scalar-fibre` — `H + cI` has the same commutators with all
  observables as `H` while the vacuum energy shifts by `c`.
* `cth:SMOS-expectation-Ward` — the `ℂ²` witness: `⟨Ω, D_W Ω⟩ = 0` with
  `D_W ≠ 0`.
-/

open Matrix
open scoped InnerProductSpace

namespace NCG

/-! ### `cor:GTLOC-local-counterterm-target`
Target-relative local counterterm independence. -/

section CountertermTarget

variable {B Y : Type*} [AddCommGroup B] [Module ℂ B] [AddCommGroup Y] [Module ℂ Y]

/-- The quasilocal counterterm projector `Π_ct T = ∑ⱼ Lⱼ φⱼ(T)` built from a
predeclared finite counterterm bank `L₁,…,L_m` and dual calibration
`φ₁,…,φ_m` (eq:GTLOC-counterterm-projector). -/
noncomputable def ctProjector {m : ℕ} (L : Fin m → B)
    (phi : Fin m → (B →ₗ[ℂ] ℂ)) : B →ₗ[ℂ] B :=
  ∑ j, (phi j).smulRight (L j)

/-- Pointwise formula for the counterterm projector. -/
theorem ctProjector_apply {m : ℕ} (L : Fin m → B) (phi : Fin m → (B →ₗ[ℂ] ℂ))
    (x : B) : ctProjector L phi x = ∑ j, phi j x • L j := by
  simp [ctProjector]

/-- Under the duality calibration `φᵢ(Lⱼ) = δᵢⱼ`
(eq:GTLOC-counterterm-duality), `Π_ct` is a projector, so its range is the
space of local counterterm differences. -/
theorem ctProjector_idem {m : ℕ} (L : Fin m → B) (phi : Fin m → (B →ₗ[ℂ] ℂ))
    (hdual : ∀ i j, phi i (L j) = if i = j then 1 else 0) :
    (ctProjector L phi).comp (ctProjector L phi) = ctProjector L phi := by
  ext x
  simp only [LinearMap.comp_apply, ctProjector_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  calc ∑ k, phi k (L j) • L k
      = ∑ k, (if k = j then L k else 0) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hdual k j, ite_smul, one_smul, zero_smul]
    _ = L j := by
        rw [Finset.sum_ite_eq' Finset.univ j fun k => L k]
        simp

/-- **(eq:GTLOC-local-counterterm-target-zero)** The value of a selected
target `𝒯` is independent of the local counterterm representative — two
renormalized representatives differ by an element of `Ran Π_ct` — exactly
when `𝒯(Ran Π_ct) = {0}`. -/
theorem ctTarget_independent_iff {m : ℕ} (L : Fin m → B)
    (phi : Fin m → (B →ₗ[ℂ] ℂ)) (T : B →ₗ[ℂ] Y) :
    (∀ C₁ C₂ : B, C₁ - C₂ ∈ LinearMap.range (ctProjector L phi) → T C₁ = T C₂)
      ↔ ∀ u ∈ LinearMap.range (ctProjector L phi), T u = 0 := by
  constructor
  · intro h u hu
    have h0 : T u = T 0 := h u 0 (by simpa using hu)
    simpa using h0
  · intro h C₁ C₂ hC
    have h2 : T C₁ - T C₂ = 0 := by rw [← map_sub]; exact h _ hC
    exact sub_eq_zero.mp h2

/-- The counterterm carrier `Ran Π_ct` is finite-dimensional: it is contained
in the span of the finite counterterm bank. -/
theorem ctProjector_range_finiteDimensional {m : ℕ} (L : Fin m → B)
    (phi : Fin m → (B →ₗ[ℂ] ℂ)) :
    FiniteDimensional ℂ ↥(LinearMap.range (ctProjector L phi)) := by
  have hle : LinearMap.range (ctProjector L phi)
      ≤ Submodule.span ℂ (Set.range L) := by
    rintro x ⟨y, rfl⟩
    rw [ctProjector_apply]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have : FiniteDimensional ℂ ↥(Submodule.span ℂ (Set.range L)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range L)
  exact Submodule.finiteDimensional_of_le hle

/-- **(eq:GTLOC-local-counterterm-read-rank)** The minimum number of
additional scalar Reads identifying the target on the counterterm carrier is
the rank of `𝒯|_{Ran Π_ct}`: a bank of `k` scalar Reads on `Ran Π_ct`
identifies the target exactly when its joint kernel is contained in
`ker (𝒯|_{Ran Π_ct})`, and the least such `k` is
`rank (𝒯|_{Ran Π_ct}) = finrank (range (𝒯|_{Ran Π_ct}))`. -/
theorem ctTarget_read_floor {m : ℕ} (L : Fin m → B)
    (phi : Fin m → (B →ₗ[ℂ] ℂ)) (T : B →ₗ[ℂ] Y) :
    IsLeast {k : ℕ |
        ∃ read : Fin k → (↥(LinearMap.range (ctProjector L phi)) →ₗ[ℂ] ℂ),
          ∀ x : ↥(LinearMap.range (ctProjector L phi)),
            (∀ i, read i x = 0) →
              T.comp (LinearMap.range (ctProjector L phi)).subtype x = 0}
      (Module.finrank ℂ ↥(LinearMap.range
        (T.comp (LinearMap.range (ctProjector L phi)).subtype))) := by
  haveI hfd : FiniteDimensional ℂ ↥(LinearMap.range (ctProjector L phi)) :=
    ctProjector_range_finiteDimensional L phi
  set T' := T.comp (LinearMap.range (ctProjector L phi)).subtype with hT'
  constructor
  · -- attainability: the coordinate Reads of a basis of the target range
    set b := Module.finBasis ℂ ↥(LinearMap.range T') with hb
    refine ⟨fun i => (b.coord i).comp T'.rangeRestrict, fun x hx => ?_⟩
    have h0 : b.repr (T'.rangeRestrict x) = 0 := by
      ext i
      simpa [Module.Basis.coord_apply] using hx i
    have hz : T'.rangeRestrict x = 0 := b.repr.map_eq_zero_iff.mp h0
    have : (T'.rangeRestrict x : Y) = T' x := rfl
    rw [← this, hz, Submodule.coe_zero]
  · -- the floor: any identifying Read bank has at least `rank` members
    rintro k ⟨read, hread⟩
    set Phi : ↥(LinearMap.range (ctProjector L phi)) →ₗ[ℂ] (Fin k → ℂ) :=
      LinearMap.pi read with hPhi
    have hker : LinearMap.ker Phi ≤ LinearMap.ker T' := by
      intro x hx
      rw [LinearMap.mem_ker] at hx ⊢
      exact hread x fun i => by
        have := congrFun hx i
        simpa [hPhi] using this
    have h1 := LinearMap.finrank_range_add_finrank_ker T'
    have h2 := LinearMap.finrank_range_add_finrank_ker Phi
    have h3 : Module.finrank ℂ ↥(LinearMap.ker Phi)
        ≤ Module.finrank ℂ ↥(LinearMap.ker T') :=
      Submodule.finrank_mono hker
    have h4 : Module.finrank ℂ ↥(LinearMap.range Phi) ≤ k := by
      have h5 := Submodule.finrank_le (LinearMap.range Phi)
      have h6 : Module.finrank ℂ (Fin k → ℂ) = k := by
        simp
      omega
    omega

/-- **`cor:GTLOC-local-counterterm-target`** (bundled): representative
independence is equivalent to `𝒯(Ran Π_ct) = {0}`, and the minimum number of
additional scalar Reads is the rank of `𝒯|_{Ran Π_ct}`. -/
theorem ctTarget_local_counterterm {m : ℕ} (L : Fin m → B)
    (phi : Fin m → (B →ₗ[ℂ] ℂ)) (T : B →ₗ[ℂ] Y) :
    ((∀ C₁ C₂ : B, C₁ - C₂ ∈ LinearMap.range (ctProjector L phi) →
        T C₁ = T C₂)
      ↔ ∀ u ∈ LinearMap.range (ctProjector L phi), T u = 0) ∧
    IsLeast {k : ℕ |
        ∃ read : Fin k → (↥(LinearMap.range (ctProjector L phi)) →ₗ[ℂ] ℂ),
          ∀ x : ↥(LinearMap.range (ctProjector L phi)),
            (∀ i, read i x = 0) →
              T.comp (LinearMap.range (ctProjector L phi)).subtype x = 0}
      (Module.finrank ℂ ↥(LinearMap.range
        (T.comp (LinearMap.range (ctProjector L phi)).subtype))) :=
  ⟨ctTarget_independent_iff L phi T, ctTarget_read_floor L phi T⟩

end CountertermTarget

/-! ### `cor:SMQG-assembly-before-elimination`
Assembly before Gaussian elimination. -/

section AssemblyBeforeElimination

variable {m t : Type*} [Fintype m] [Fintype t] [DecidableEq m] [DecidableEq t]

/-- The retained Schur operator `S = A - B E⁻¹ C` (QG.28/QG.33) of a
retained/tail precision block. -/
noncomputable def sectorSchur (A : Matrix m m ℂ) (B : Matrix m t ℂ)
    (C : Matrix t m ℂ) (E : Matrix t t ℂ) : Matrix m m ℂ :=
  A - B * E⁻¹ * C

/-- **(QG.33, correct assembly)** For a precision operator that is a sum of
sector contributions, the correct reflected covariance is obtained by forming
the complete blocks and only then eliminating: the retained block of the
inverse of the fully assembled precision is the inverse of the Schur
complement of the summed blocks. -/
theorem assembled_schur_retained_block {ι : Type*} [Fintype ι]
    (A : ι → Matrix m m ℂ) (B : ι → Matrix m t ℂ) (C : ι → Matrix t m ℂ)
    (E : ι → Matrix t t ℂ) [Invertible (∑ i, E i)]
    [Invertible (sectorSchur (∑ i, A i) (∑ i, B i) (∑ i, C i) (∑ i, E i))] :
    ((Matrix.fromBlocks (∑ i, A i) (∑ i, B i) (∑ i, C i) (∑ i, E i))⁻¹).toBlocks₁₁
      = (sectorSchur (∑ i, A i) (∑ i, B i) (∑ i, C i) (∑ i, E i))⁻¹ := by
  have hS : sectorSchur (∑ i, A i) (∑ i, B i) (∑ i, C i) (∑ i, E i)
      = (∑ i, A i) - (∑ i, B i) * ⅟(∑ i, E i) * (∑ i, C i) := by
    rw [sectorSchur, Matrix.invOf_eq_nonsing_inv]
  haveI : Invertible ((∑ i, A i) - (∑ i, B i) * ⅟(∑ i, E i) * (∑ i, C i)) :=
    Invertible.copy ‹Invertible (sectorSchur (∑ i, A i) (∑ i, B i)
      (∑ i, C i) (∑ i, E i))› _ hS.symm
  haveI : Invertible
      (Matrix.fromBlocks (∑ i, A i) (∑ i, B i) (∑ i, C i) (∑ i, E i)) :=
    Matrix.fromBlocks₂₂Invertible _ _ _ _
  rw [← Matrix.invOf_eq_nonsing_inv, Matrix.invOf_fromBlocks₂₂_eq,
    Matrix.toBlocks_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv, hS]

/-- Entry formula for the inverse of a `1 × 1` complex matrix. -/
theorem inv_one_by_one (M : Matrix (Fin 1) (Fin 1) ℂ) :
    M⁻¹ 0 0 = (M 0 0)⁻¹ := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_one, Matrix.det_fin_one]
  simp [Ring.inverse_eq_inv']

/-- **(counterexample clause)** Separately eliminating the sectors and adding
their individual Schur operators generally differs from eliminating the
assembled blocks.  Explicit two-sector witness with `1 × 1` blocks
`A₁ = A₂ = 0`, `B₁ = C₁ = 1`, `B₂ = C₂ = 0`, `E₁ = E₂ = 1` (all tail blocks
and their sum are invertible): the assembled Schur value is `-1/2` while the
sum of the sector Schur values is `-1`. -/
theorem assembly_before_elimination_counterexample :
    (1 : Matrix (Fin 1) (Fin 1) ℂ) ≠ 0 ∧ IsUnit (1 : Matrix (Fin 1) (Fin 1) ℂ) ∧
    IsUnit ((1 : Matrix (Fin 1) (Fin 1) ℂ) + 1) ∧
    sectorSchur (0 + 0) ((1 : Matrix (Fin 1) (Fin 1) ℂ) + 0) (1 + 0) (1 + 1)
      ≠ sectorSchur 0 (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 1
        + sectorSchur (m := Fin 1) (t := Fin 1) 0 0 0 1 := by
  refine ⟨?_, isUnit_one, ?_, ?_⟩
  · intro h
    have := congrFun (congrFun h 0) 0
    simp at this
  · have hdet : ((1 : Matrix (Fin 1) (Fin 1) ℂ) + 1).det = 2 := by
      rw [Matrix.det_fin_one]
      norm_num [Matrix.add_apply, Matrix.one_apply]
    have : IsUnit ((1 : Matrix (Fin 1) (Fin 1) ℂ) + 1).det := by
      rw [hdet]; norm_num
    exact (Matrix.isUnit_iff_isUnit_det _).mpr this
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    have hL : sectorSchur (0 + 0) ((1 : Matrix (Fin 1) (Fin 1) ℂ) + 0) (1 + 0)
        (1 + 1) 0 0 = -(1/2 : ℂ) := by
      rw [sectorSchur]
      simp [Matrix.sub_apply]
      norm_num
    have hR : (sectorSchur 0 (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 1
        + sectorSchur (m := Fin 1) (t := Fin 1) 0 0 0 1) 0 0 = -1 := by
      simp [sectorSchur, Matrix.add_apply]
    rw [hL, hR] at h00
    norm_num at h00

/-- **(router dispersion inside `P = S⁻¹`)** The discrepancy of the
counterexample propagates inside the reflected covariance: the inverse of the
assembled Schur operator differs from the inverse of the sum of the sector
Schur operators (`-2 ≠ -1`). -/
theorem assembly_before_elimination_covariance :
    (sectorSchur (0 + 0) ((1 : Matrix (Fin 1) (Fin 1) ℂ) + 0) (1 + 0) (1 + 1))⁻¹
      ≠ (sectorSchur 0 (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 1
        + sectorSchur (m := Fin 1) (t := Fin 1) 0 0 0 1)⁻¹ := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  rw [inv_one_by_one, inv_one_by_one] at h00
  have hL : sectorSchur (0 + 0) ((1 : Matrix (Fin 1) (Fin 1) ℂ) + 0) (1 + 0)
      (1 + 1) 0 0 = -(1/2 : ℂ) := by
    rw [sectorSchur]
    simp [Matrix.sub_apply]
    norm_num
  have hR : (sectorSchur 0 (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 1
      + sectorSchur (m := Fin 1) (t := Fin 1) 0 0 0 1) 0 0 = -1 := by
    simp [sectorSchur, Matrix.add_apply]
  rw [hL, hR] at h00
  norm_num at h00

end AssemblyBeforeElimination

/-! ### `cth:GT-counterfeit-support`
A counterfeit support can hide an indefinite carrier (CERT.9). -/

section CounterfeitSupport

/-- The retained block `A = (3)` of the CERT.9 witness. -/
def counterfeitA : Matrix (Fin 1) (Fin 1) ℝ := !![3]

/-- The coupling block `B = (0 1)` of the CERT.9 witness. -/
def counterfeitB : Matrix (Fin 1) (Fin 2) ℝ := !![0, 1]

/-- The degenerate tail block `D = diag(2,0)` of the CERT.9 witness. -/
def counterfeitD : Matrix (Fin 2) (Fin 2) ℝ := !![2, 0; 0, 0]

/-- The Moore–Penrose pseudoinverse `D⁺ = diag(1/2, 0)` of the tail block. -/
noncomputable def counterfeitDpinv : Matrix (Fin 2) (Fin 2) ℝ := !![1/2, 0; 0, 0]

/-- The actual support projection `P_D = diag(1,0)` of the tail block. -/
def counterfeitPD : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

/-- `D⁺` satisfies all four Penrose equations, so it is *the* Moore–Penrose
pseudoinverse of `D`, and the associated support projection is
`D D⁺ = P_D`. -/
theorem counterfeit_penrose :
    counterfeitD * counterfeitDpinv * counterfeitD = counterfeitD ∧
    counterfeitDpinv * counterfeitD * counterfeitDpinv = counterfeitDpinv ∧
    (counterfeitD * counterfeitDpinv)ᴴ = counterfeitD * counterfeitDpinv ∧
    (counterfeitDpinv * counterfeitD)ᴴ = counterfeitDpinv * counterfeitD ∧
    counterfeitD * counterfeitDpinv = counterfeitPD := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    · ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [counterfeitD, counterfeitDpinv, counterfeitPD,
          Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]

/-- **(formal test with the counterfeit projection)** With the submitted
counterfeit support `P = I₂`, the formal test `B (I - P) = 0` vanishes
trivially. -/
theorem counterfeit_formal_test :
    counterfeitB * ((1 : Matrix (Fin 2) (Fin 2) ℝ) - 1) = 0 := by
  simp

/-- **(apparent Schur value)** The apparent (pseudoinverse) Schur value is
three: `A - B D⁺ Bᵀ = (3)`; in particular the apparent Schur complement is
positive semidefinite, so the counterfeit branch certifies a (false)
positive. -/
theorem counterfeit_apparent_schur :
    counterfeitA - counterfeitB * counterfeitDpinv * counterfeitBᴴ = !![3] ∧
    (counterfeitA - counterfeitB * counterfeitDpinv * counterfeitBᴴ).PosSemidef := by
  have hBD : counterfeitB * counterfeitDpinv = 0 := by
    ext i j
    fin_cases i; fin_cases j <;>
      norm_num [counterfeitB, counterfeitDpinv, Matrix.mul_apply,
        Fin.sum_univ_two]
  have h : counterfeitA - counterfeitB * counterfeitDpinv * counterfeitBᴴ
      = !![3] := by
    rw [hBD, Matrix.zero_mul, sub_zero]
    rfl
  refine ⟨h, ?_⟩
  rw [h]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    fin_cases i; fin_cases j
    norm_num [Matrix.conjTranspose_apply]
  · have hmv : (!![3] : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ x = fun _ => 3 * x 0 := by
      funext i
      fin_cases i
      simp [Matrix.mulVec, dotProduct]
    rw [hmv]
    have hdp : star x ⬝ᵥ (fun _ => 3 * x 0) = x 0 * (3 * x 0) := by
      simp [dotProduct]
    rw [hdp]
    nlinarith [mul_self_nonneg (x 0)]

/-- **(true support fails the test)** With the actual support projection
`P_D`, the incidence test does not vanish: `B (I - P_D) = B ≠ 0`. -/
theorem counterfeit_true_support_test :
    counterfeitB * ((1 : Matrix (Fin 2) (Fin 2) ℝ) - counterfeitPD)
      = counterfeitB ∧ counterfeitB ≠ 0 := by
  constructor
  · ext i j
    fin_cases i; fin_cases j <;>
      norm_num [counterfeitB, counterfeitPD, Matrix.mul_apply,
        Matrix.sub_apply, Matrix.one_apply, Fin.sum_univ_two]
  · intro h
    have := congrFun (congrFun h 0) 1
    norm_num [counterfeitB] at this

/-- The full block form of the CERT.9 witness. -/
def counterfeitBlock : Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks counterfeitA counterfeitB counterfeitBᴴ counterfeitD

/-- The witness vector `(x, y₁, y₂) = (1, 0, -2)`. -/
def counterfeitWitness : Fin 1 ⊕ Fin 2 → ℝ := Sum.elim ![1] ![0, -2]

/-- **(indefiniteness of the carrier)** The full block form takes the value
`-1` on the witness `(1, 0, -2)`. -/
theorem counterfeit_quadratic_value :
    counterfeitWitness ⬝ᵥ (counterfeitBlock *ᵥ counterfeitWitness) = -1 := by
  simp [counterfeitBlock, counterfeitWitness, counterfeitA, counterfeitB,
    counterfeitD, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Fin.sum_univ_two, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂]
  norm_num

/-- **`cth:GT-counterfeit-support`** (conclusion): the full block form is not
positive semidefinite, although the counterfeit test and the apparent Schur
value both certify positivity — accepting an arbitrary submitted support can
certify a false positive branch. -/
theorem counterfeit_not_posSemidef : ¬ counterfeitBlock.PosSemidef := by
  intro h
  have h2 := h.dotProduct_mulVec_nonneg counterfeitWitness
  have hstar : star counterfeitWitness = counterfeitWitness := by
    funext i
    simp
  rw [hstar, counterfeit_quadratic_value] at h2
  norm_num at h2

end CounterfeitSupport

/-! ### `cth:GTLOC-local-Gram-no-inverse`
A local Gram without a uniform floor need not have a local inverse. -/

section LocalGramNoInverse

open scoped MatrixOrder RealInnerProductSpace
open Filter

/-- The signed edge–vertex incidence matrix of the path `0 — 1 — ⋯ — N`. -/
def pathIncidence (N : ℕ) : Matrix (Fin N) (Fin (N + 1)) ℝ :=
  Matrix.of fun e v => if v = e.castSucc then 1 else if v = e.succ then -1 else 0

/-- The nearest-neighbour graph Laplacian `L_N = Bᴴ B` of the path of
length `N`. -/
def pathLaplacian (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  (pathIncidence N)ᴴ * pathIncidence N

/-- The floor-regularized reflected Gram
`G_N = ε I + L_N` (eq:GTLOC-local-Gram-floor-collapse). -/
def gramFloor (N : ℕ) (ε : ℝ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  ε • 1 + pathLaplacian N

/-- Each incidence row sums to zero. -/
theorem pathIncidence_row_sum (N : ℕ) (e : Fin N) :
    ∑ v, pathIncidence N e v = 0 := by
  have hne : (e.castSucc : Fin (N + 1)) ≠ e.succ := by
    intro h
    have h2 : (e.castSucc : Fin (N + 1)).val = (e.succ : Fin (N + 1)).val :=
      congrArg Fin.val h
    rw [Fin.val_castSucc, Fin.val_succ] at h2
    omega
  have hsplit : ∀ v : Fin (N + 1), pathIncidence N e v
      = (if v = e.castSucc then (1 : ℝ) else 0)
        + (if v = e.succ then (-1 : ℝ) else 0) := by
    intro v
    by_cases h1 : v = e.castSucc
    · simp [pathIncidence, h1, hne]
    · by_cases h2 : v = e.succ
      · simp [pathIncidence, h2, Ne.symm hne]
      · simp [pathIncidence, h1, h2]
  rw [Finset.sum_congr rfl fun v _ => hsplit v, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq' Finset.univ (e.castSucc) fun _ => (1 : ℝ),
    Finset.sum_ite_eq' Finset.univ (e.succ) fun _ => (-1 : ℝ)]
  simp

/-- The support of an incidence row lies on the two endpoints of its edge. -/
theorem pathIncidence_support {N : ℕ} {e : Fin N} {v : Fin (N + 1)}
    (h : pathIncidence N e v ≠ 0) : v.val = e.val ∨ v.val = e.val + 1 := by
  by_cases h1 : v = e.castSucc
  · exact Or.inl (by rw [h1, Fin.val_castSucc])
  by_cases h2 : v = e.succ
  · exact Or.inr (by rw [h2, Fin.val_succ])
  exact absurd (by simp [pathIncidence, h1, h2]) h

/-- Each incidence entry is bounded by one in absolute value. -/
theorem abs_pathIncidence_le {N : ℕ} (e : Fin N) (v : Fin (N + 1)) :
    |pathIncidence N e v| ≤ 1 := by
  rw [pathIncidence, Matrix.of_apply]
  split_ifs <;> norm_num

/-- An indicator sum over a subsingleton condition is at most one. -/
theorem sum_indicator_subsingleton_le_one {n : ℕ} (p : Fin n → Prop)
    [DecidablePred p] (hp : ∀ a b, p a → p b → a = b) :
    (∑ e : Fin n, if p e then (1 : ℝ) else 0) ≤ 1 := by
  rw [Finset.sum_boole]
  have hcard : ({e ∈ Finset.univ | p e} : Finset (Fin n)).card ≤ 1 :=
    Finset.card_le_one.mpr fun a ha b hb =>
      hp a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  exact_mod_cast hcard

/-- Each vertex meets at most two edges: the incidence column absolute sums
are bounded by two. -/
theorem sum_abs_pathIncidence_le (N : ℕ) (v : Fin (N + 1)) :
    ∑ e, |pathIncidence N e v| ≤ 2 := by
  have hterm : ∀ e : Fin N, |pathIncidence N e v|
      ≤ (if e.val = v.val then (1 : ℝ) else 0)
        + (if e.val + 1 = v.val then (1 : ℝ) else 0) := by
    intro e
    by_cases h1 : v = e.castSucc
    · have hv : e.val = v.val := by rw [h1, Fin.val_castSucc]
      have h0 : (0 : ℝ) ≤ if e.val + 1 = v.val then (1 : ℝ) else 0 := by
        positivity
      calc |pathIncidence N e v| ≤ 1 := abs_pathIncidence_le e v
        _ ≤ _ := by rw [if_pos hv]; linarith
    by_cases h2 : v = e.succ
    · have hv : e.val + 1 = v.val := by rw [h2, Fin.val_succ]
      have h0 : (0 : ℝ) ≤ if e.val = v.val then (1 : ℝ) else 0 := by
        positivity
      calc |pathIncidence N e v| ≤ 1 := abs_pathIncidence_le e v
        _ ≤ _ := by rw [if_pos hv]; linarith
    · have hz : pathIncidence N e v = 0 := by simp [pathIncidence, h1, h2]
      rw [hz, abs_zero]
      positivity
  calc ∑ e, |pathIncidence N e v|
      ≤ ∑ e : Fin N, ((if e.val = v.val then (1 : ℝ) else 0)
          + (if e.val + 1 = v.val then (1 : ℝ) else 0)) :=
        Finset.sum_le_sum fun e _ => hterm e
    _ = (∑ e : Fin N, if e.val = v.val then (1 : ℝ) else 0)
          + ∑ e : Fin N, if e.val + 1 = v.val then (1 : ℝ) else 0 :=
        Finset.sum_add_distrib
    _ ≤ 1 + 1 := by
        gcongr
        · exact sum_indicator_subsingleton_le_one _
            fun a b ha hb => Fin.ext (by omega)
        · exact sum_indicator_subsingleton_le_one _
            fun a b ha hb => Fin.ext (by omega)
    _ = 2 := by norm_num

/-- The path Laplacian annihilates the constant vector. -/
theorem pathLaplacian_mulVec_ones (N : ℕ) :
    pathLaplacian N *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  funext i
  simp only [pathLaplacian, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Matrix.conjTranspose_apply, star_trivial, mul_one, Pi.zero_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [← Finset.mul_sum, pathIncidence_row_sum]
  ring

/-- **(uniformly bounded finite propagation)** The Laplacian is tridiagonal:
its entries vanish beyond graph distance one, uniformly in `N`. -/
theorem pathLaplacian_propagation (N : ℕ) {i j : Fin (N + 1)}
    (h : 1 < Nat.dist i.val j.val) : pathLaplacian N i j = 0 := by
  rw [pathLaplacian, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [Matrix.conjTranspose_apply, star_trivial]
  rcases eq_or_ne (pathIncidence N e i) 0 with h0 | h0
  · rw [h0, zero_mul]
  rcases eq_or_ne (pathIncidence N e j) 0 with h1 | h1
  · rw [h1, mul_zero]
  exfalso
  rcases pathIncidence_support h0 with hi | hi <;>
    rcases pathIncidence_support h1 with hj | hj <;>
      (rw [Nat.dist] at h; omega)

/-- **(uniformly bounded finite propagation, regularized)** The Gram floor
`G_N` has propagation radius one uniformly in `N`. -/
theorem gramFloor_propagation (N : ℕ) (ε : ℝ) {i j : Fin (N + 1)}
    (h : 1 < Nat.dist i.val j.val) : gramFloor N ε i j = 0 := by
  have hij : i ≠ j := by
    intro h'
    rw [h', Nat.dist_self] at h
    omega
  rw [gramFloor, Matrix.add_apply, pathLaplacian_propagation N h,
    Matrix.smul_apply, Matrix.one_apply_ne hij]
  simp

/-- Entrywise bound `|L_N i j| ≤ 2` for the path Laplacian. -/
theorem abs_pathLaplacian_le (N : ℕ) (i j : Fin (N + 1)) :
    |pathLaplacian N i j| ≤ 2 := by
  rw [pathLaplacian, Matrix.mul_apply]
  calc |∑ e, (pathIncidence N)ᴴ i e * pathIncidence N e j|
      ≤ ∑ e, |(pathIncidence N)ᴴ i e * pathIncidence N e j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e, |pathIncidence N e i| := by
        refine Finset.sum_le_sum fun e _ => ?_
        rw [Matrix.conjTranspose_apply, star_trivial, abs_mul]
        calc |pathIncidence N e i| * |pathIncidence N e j|
            ≤ |pathIncidence N e i| * 1 :=
              mul_le_mul_of_nonneg_left (abs_pathIncidence_le e j)
                (abs_nonneg _)
          _ = |pathIncidence N e i| := mul_one _
    _ ≤ 2 := sum_abs_pathIncidence_le N i

/-- Entrywise bound `|G_N i j| ≤ ε + 2` for the Gram floor. -/
theorem abs_gramFloor_le (N : ℕ) {ε : ℝ} (hε : 0 ≤ ε) (i j : Fin (N + 1)) :
    |gramFloor N ε i j| ≤ ε + 2 := by
  rw [gramFloor, Matrix.add_apply, Matrix.smul_apply]
  calc |ε • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) i j
        + pathLaplacian N i j|
      ≤ |ε • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) i j|
        + |pathLaplacian N i j| := abs_add_le _ _
    _ ≤ ε + 2 := by
        gcongr
        · rw [smul_eq_mul, abs_mul, abs_of_nonneg hε]
          calc ε * |(1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) i j|
              ≤ ε * 1 := by
                gcongr
                rw [Matrix.one_apply]
                split_ifs <;> norm_num
            _ = ε := mul_one _
        · exact abs_pathLaplacian_le N i j

/-- The `μ`-weighted Schur norm on the path metric
(eq:GTLOC-weighted-Schur-norm): the maximum of the weighted row and column
absolute sums, with weights `e^{μ |i - j|}`. -/
noncomputable def pathSchurNorm {n : ℕ} [NeZero n] (μ : ℝ)
    (T : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  max
    (Finset.univ.sup' Finset.univ_nonempty fun i =>
      ∑ j, Real.exp (μ * Nat.dist i.val j.val) * |T i j|)
    (Finset.univ.sup' Finset.univ_nonempty fun j =>
      ∑ i, Real.exp (μ * Nat.dist i.val j.val) * |T i j|)

/-- At most three vertices lie within path distance one of a given vertex. -/
theorem card_pathClose_le (n : ℕ) (i : Fin n) :
    ({j ∈ Finset.univ | Nat.dist i.val j.val ≤ 1} : Finset (Fin n)).card
      ≤ 3 := by
  classical
  have hsub : ({j ∈ Finset.univ | Nat.dist i.val j.val ≤ 1} : Finset (Fin n)).card
      ≤ (Finset.Icc (i.val - 1) (i.val + 1)).card := by
    refine Finset.card_le_card_of_injOn Fin.val ?_ ?_
    · intro j hj
      have h2 := (Finset.mem_filter.mp hj).2
      rw [Nat.dist] at h2
      simp only [Finset.coe_Icc, Set.mem_Icc]
      omega
    · intro a _ b _ hab
      exact Fin.ext hab
  refine hsub.trans ?_
  rw [Nat.card_Icc]
  omega

/-- Weighted row-sum bound for the Gram floor: each `μ`-weighted absolute row
sum is bounded by `3 e^μ (ε + 2)`, uniformly in `N`. -/
theorem gramFloor_row_bound (N : ℕ) {ε μ : ℝ} (hε : 0 ≤ ε) (hμ : 0 ≤ μ)
    (i : Fin (N + 1)) :
    ∑ j, Real.exp (μ * Nat.dist i.val j.val) * |gramFloor N ε i j|
      ≤ 3 * (Real.exp μ * (ε + 2)) := by
  classical
  have hterm : ∀ j : Fin (N + 1),
      Real.exp (μ * Nat.dist i.val j.val) * |gramFloor N ε i j|
        ≤ if Nat.dist i.val j.val ≤ 1 then Real.exp μ * (ε + 2) else 0 := by
    intro j
    by_cases hd : Nat.dist i.val j.val ≤ 1
    · rw [if_pos hd]
      have h1 : Real.exp (μ * Nat.dist i.val j.val) ≤ Real.exp μ := by
        apply Real.exp_le_exp.mpr
        have h2 : (Nat.dist i.val j.val : ℝ) ≤ 1 := by exact_mod_cast hd
        nlinarith
      exact mul_le_mul h1 (abs_gramFloor_le N hε i j) (abs_nonneg _)
        (Real.exp_pos μ).le
    · rw [if_neg hd, gramFloor_propagation N ε (by omega)]
      simp
  calc ∑ j, Real.exp (μ * Nat.dist i.val j.val) * |gramFloor N ε i j|
      ≤ ∑ j : Fin (N + 1),
          (if Nat.dist i.val j.val ≤ 1 then Real.exp μ * (ε + 2) else 0) :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = ({j ∈ Finset.univ | Nat.dist i.val j.val ≤ 1} :
          Finset (Fin (N + 1))).card • (Real.exp μ * (ε + 2)) := by
        rw [← Finset.sum_filter, Finset.sum_const]
    _ ≤ 3 * (Real.exp μ * (ε + 2)) := by
        rw [nsmul_eq_mul]
        have hcard := card_pathClose_le (N + 1) i
        have hpos : 0 ≤ Real.exp μ * (ε + 2) := by positivity
        have : (({j ∈ Finset.univ | Nat.dist i.val j.val ≤ 1} :
            Finset (Fin (N + 1))).card : ℝ) ≤ 3 := by exact_mod_cast hcard
        nlinarith

/-- The Gram floor is symmetric. -/
theorem gramFloor_isHermitian (N : ℕ) (ε : ℝ) :
    (gramFloor N ε).IsHermitian := by
  rw [gramFloor]
  refine Matrix.IsHermitian.add ?_
    (Matrix.posSemidef_conjTranspose_mul_self (pathIncidence N)).1
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    star_trivial]

/-- Entrywise symmetry of the Gram floor. -/
theorem gramFloor_symm_apply (N : ℕ) (ε : ℝ) (i j : Fin (N + 1)) :
    gramFloor N ε i j = gramFloor N ε j i := by
  have h := (gramFloor_isHermitian N ε).apply i j
  rw [← h]
  simp

/-- **(uniformly bounded weighted Schur norm)** For every fixed `μ ≥ 0` the
weighted Schur norms of the Gram floors are bounded by `3 e^μ (ε + 2)`,
uniformly in `N`. -/
theorem pathSchurNorm_gramFloor_le (N : ℕ) {ε μ : ℝ} (hε : 0 ≤ ε)
    (hμ : 0 ≤ μ) :
    pathSchurNorm μ (gramFloor N ε) ≤ 3 * (Real.exp μ * (ε + 2)) := by
  rw [pathSchurNorm]
  apply max_le
  · exact Finset.sup'_le _ _ fun i _ => gramFloor_row_bound N hε hμ i
  · refine Finset.sup'_le _ _ fun j _ => ?_
    have hcong : ∀ i : Fin (N + 1),
        Real.exp (μ * Nat.dist i.val j.val) * |gramFloor N ε i j|
          = Real.exp (μ * Nat.dist j.val i.val) * |gramFloor N ε j i| := by
      intro i
      rw [Nat.dist_comm, gramFloor_symm_apply]
    rw [Finset.sum_congr rfl fun i _ => hcong i]
    exact gramFloor_row_bound N hε hμ j

/-- The path Laplacian is positive semidefinite. -/
theorem pathLaplacian_posSemidef (N : ℕ) : (pathLaplacian N).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self (pathIncidence N)

/-- The real dot square is nonnegative. -/
theorem dotProduct_self_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

/-- With a positive floor the Gram is positive definite. -/
theorem gramFloor_posDef (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (gramFloor N ε).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (gramFloor_isHermitian N ε)
    fun x hx => ?_
  have hL : 0 ≤ x ⬝ᵥ (pathLaplacian N *ᵥ x) := by
    have h := (pathLaplacian_posSemidef N).dotProduct_mulVec_nonneg x
    simpa [star_trivial] using h
  have hxx : 0 < x ⬝ᵥ x := by
    rcases lt_or_eq_of_le (dotProduct_self_nonneg x) with h | h
    · exact h
    · exfalso
      apply hx
      funext i
      have h2 : ∀ j ∈ Finset.univ, 0 ≤ x j * x j := fun j _ =>
        mul_self_nonneg (x j)
      have h3 := (Finset.sum_eq_zero_iff_of_nonneg h2).mp h.symm
      have h4 := h3 i (Finset.mem_univ i)
      exact mul_self_eq_zero.mp h4
  have hexpand : star x ⬝ᵥ (gramFloor N ε *ᵥ x)
      = ε * (x ⬝ᵥ x) + x ⬝ᵥ (pathLaplacian N *ᵥ x) := by
    rw [gramFloor, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, star_trivial]
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
  rw [hexpand]
  nlinarith

/-- The Gram floor eigenvector relation `G_N 𝟙 = ε 𝟙`. -/
theorem gramFloor_mulVec_ones (N : ℕ) (ε : ℝ) :
    gramFloor N ε *ᵥ (fun _ => (1 : ℝ)) = ε • fun _ => (1 : ℝ) := by
  rw [gramFloor, Matrix.add_mulVec, pathLaplacian_mulVec_ones, add_zero,
    Matrix.smul_mulVec, Matrix.one_mulVec]

/-- The inverse Gram eigenvector relation `G_N⁻¹ 𝟙 = ε⁻¹ 𝟙`. -/
theorem gramFloor_inv_mulVec_ones (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (gramFloor N ε)⁻¹ *ᵥ (fun _ => (1 : ℝ)) = ε⁻¹ • fun _ => (1 : ℝ) := by
  have hdet : IsUnit (gramFloor N ε).det :=
    (gramFloor_posDef N hε).det_pos.ne'.isUnit
  have h1 : (gramFloor N ε)⁻¹ *ᵥ (gramFloor N ε *ᵥ fun _ => (1 : ℝ))
      = fun _ => (1 : ℝ) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet,
      Matrix.one_mulVec]
  rw [gramFloor_mulVec_ones, Matrix.mulVec_smul] at h1
  calc (gramFloor N ε)⁻¹ *ᵥ (fun _ => (1 : ℝ))
      = ε⁻¹ • (ε • ((gramFloor N ε)⁻¹ *ᵥ fun _ => (1 : ℝ))) := by
        rw [smul_smul, inv_mul_cancel₀ hε.ne', one_smul]
    _ = ε⁻¹ • fun _ => (1 : ℝ) := by rw [h1]

/-- The OS-whitening inverse square root `G_N^{-1/2}`, via the continuous
functional calculus square root of `G_N⁻¹`. -/
noncomputable def invSqrtGram (N : ℕ) (ε : ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  CFC.sqrt (gramFloor N ε)⁻¹

/-- The CFC inverse square root is positive semidefinite. -/
theorem invSqrtGram_posSemidef (N : ℕ) (ε : ℝ) :
    (invSqrtGram N ε).PosSemidef :=
  (CFC.sqrt_nonneg ((gramFloor N ε)⁻¹)).posSemidef

/-- `G_N^{-1/2}` squares to `G_N⁻¹`: it is an exact inverse square root. -/
theorem invSqrtGram_mul_self (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    invSqrtGram N ε * invSqrtGram N ε = (gramFloor N ε)⁻¹ := by
  have h := CFC.sq_sqrt ((gramFloor N ε)⁻¹)
    ((gramFloor_posDef N hε).inv.posSemidef.nonneg)
  rw [sq] at h
  exact h

/-- Positive definite matrices have injective `mulVec`. -/
theorem posDef_real_mulVec_eq_zero {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosDef) {w : Fin n → ℝ} (h : M *ᵥ w = 0) : w = 0 := by
  by_contra hw
  have h2 := hM.dotProduct_mulVec_pos hw
  rw [h] at h2
  simp at h2

/-- The eigenvector relation for the inverse square root:
`G_N^{-1/2} 𝟙 = ε^{-1/2} 𝟙` (the CFC square-root norm mechanism). -/
theorem invSqrtGram_mulVec_ones (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    invSqrtGram N ε *ᵥ (fun _ => (1 : ℝ))
      = (Real.sqrt ε)⁻¹ • fun _ => (1 : ℝ) := by
  set S := invSqrtGram N ε with hS
  set c : ℝ := (Real.sqrt ε)⁻¹ with hc
  have hcpos : 0 < c := inv_pos.mpr (Real.sqrt_pos.mpr hε)
  have hcsq : c * c = ε⁻¹ := by
    rw [hc, ← mul_inv, Real.mul_self_sqrt hε.le]
  have hSc : ((c • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)) + S).PosDef := by
    refine Matrix.PosDef.add_posSemidef ?_ (invSqrtGram_posSemidef N ε)
    exact Matrix.PosDef.smul Matrix.PosDef.one hcpos
  have hkey : ((c • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)) + S) *ᵥ
      ((S *ᵥ fun _ => (1 : ℝ)) - c • fun _ => (1 : ℝ)) = 0 := by
    have hSS : S *ᵥ (S *ᵥ fun _ => (1 : ℝ)) = ε⁻¹ • fun _ => (1 : ℝ) := by
      rw [Matrix.mulVec_mulVec, hS, invSqrtGram_mul_self N hε,
        gramFloor_inv_mulVec_ones N hε]
    rw [Matrix.add_mulVec, Matrix.mulVec_sub, Matrix.mulVec_sub, hSS,
      Matrix.mulVec_smul, Matrix.mulVec_smul]
    simp only [Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul, hcsq]
    abel
  have hzero := posDef_real_mulVec_eq_zero hSc hkey
  exact sub_eq_zero.mp hzero

/-- **(weighted Schur norm lower bound)** For `μ ≥ 0`,
`‖G_N^{-1/2}‖_{μ,Sch} ≥ ε^{-1/2}`: the weighted Schur norm dominates the
constant-eigenvector row sum. -/
theorem pathSchurNorm_invSqrtGram_ge (N : ℕ) {ε μ : ℝ} (hε : 0 < ε)
    (hμ : 0 ≤ μ) :
    (Real.sqrt ε)⁻¹ ≤ pathSchurNorm μ (invSqrtGram N ε) := by
  set S := invSqrtGram N ε with hS
  have hrowsum : ∑ j, S 0 j = (Real.sqrt ε)⁻¹ := by
    have h := congrFun (invSqrtGram_mulVec_ones N hε) 0
    simpa [Matrix.mulVec, dotProduct, hS] using h
  have hcpos : (0 : ℝ) < (Real.sqrt ε)⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.mpr hε)
  have hrow : (Real.sqrt ε)⁻¹
      ≤ ∑ j, Real.exp (μ * Nat.dist (0 : Fin (N + 1)).val j.val) * |S 0 j| := by
    calc (Real.sqrt ε)⁻¹ = |∑ j, S 0 j| := by
          rw [hrowsum, abs_of_pos hcpos]
      _ ≤ ∑ j, |S 0 j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, Real.exp (μ * Nat.dist (0 : Fin (N + 1)).val j.val)
            * |S 0 j| := by
          refine Finset.sum_le_sum fun j _ => ?_
          refine le_mul_of_one_le_left (abs_nonneg _) ?_
          apply Real.one_le_exp
          positivity
  refine hrow.trans ?_
  rw [pathSchurNorm]
  exact le_max_of_le_left
    (Finset.le_sup' (fun i : Fin (N + 1) =>
        ∑ j, Real.exp (μ * Nat.dist i.val j.val) * |S i j|)
      (Finset.mem_univ (0 : Fin (N + 1))))

/-- Quadratic-form bound for the inverse square root:
`‖G_N^{-1/2} v‖² ≤ ε⁻¹ ‖v‖²`. -/
theorem invSqrtGram_quad_bound (N : ℕ) {ε : ℝ} (hε : 0 < ε)
    (v : Fin (N + 1) → ℝ) :
    (invSqrtGram N ε *ᵥ v) ⬝ᵥ (invSqrtGram N ε *ᵥ v) ≤ ε⁻¹ * (v ⬝ᵥ v) := by
  set S := invSqrtGram N ε with hS
  set G := gramFloor N ε with hG
  have hSsym : Sᵀ = S := by
    have h : Sᴴ = S := (invSqrtGram_posSemidef N ε).1
    calc Sᵀ = Sᴴ := by
          ext i j
          simp [Matrix.conjTranspose_apply]
      _ = S := h
  have e1 : (S *ᵥ v) ⬝ᵥ (S *ᵥ v) = v ⬝ᵥ (G⁻¹ *ᵥ v) := by
    rw [dotProduct_mulVec]
    have e2 : (S *ᵥ v) ᵥ* S = G⁻¹ *ᵥ v := by
      rw [← Matrix.mulVec_transpose, hSsym, Matrix.mulVec_mulVec, hS,
        invSqrtGram_mul_self N hε, hG]
    rw [e2]
    exact dotProduct_comm _ _
  rw [e1]
  set y := G⁻¹ *ᵥ v with hy
  have hdet : IsUnit G.det := (gramFloor_posDef N hε).det_pos.ne'.isUnit
  have hGy : G *ᵥ y = v := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
      Matrix.one_mulVec]
  have hL : 0 ≤ y ⬝ᵥ (pathLaplacian N *ᵥ y) := by
    have h := (pathLaplacian_posSemidef N).dotProduct_mulVec_nonneg y
    simpa [star_trivial] using h
  have ht : ε * (y ⬝ᵥ y) ≤ v ⬝ᵥ y := by
    have h1 : v ⬝ᵥ y = y ⬝ᵥ (G *ᵥ y) := by
      rw [← hGy, dotProduct_comm, hGy]
    rw [h1, hG, gramFloor, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
    linarith
  have hCS : (v ⬝ᵥ y) ^ 2 ≤ (v ⬝ᵥ v) * (y ⬝ᵥ y) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v y
    calc (v ⬝ᵥ y) ^ 2 = (∑ i, v i * y i) ^ 2 := by rw [dotProduct]
      _ ≤ (∑ i, v i ^ 2) * ∑ i, y i ^ 2 := h
      _ = (v ⬝ᵥ v) * (y ⬝ᵥ y) := by
          rw [dotProduct, dotProduct]
          congr 1 <;> exact Finset.sum_congr rfl fun i _ => (sq (_ : ℝ)) ▸ by
            ring
  have hyy : 0 ≤ y ⬝ᵥ y := dotProduct_self_nonneg y
  have hvv : 0 ≤ v ⬝ᵥ v := dotProduct_self_nonneg v
  have hvy : 0 ≤ v ⬝ᵥ y := le_trans (by positivity) ht
  rcases eq_or_lt_of_le hyy with ha | ha
  · have h0 : (v ⬝ᵥ y) ^ 2 ≤ 0 := by
      rw [← ha] at hCS
      simpa using hCS
    have h1 : v ⬝ᵥ y = 0 := by nlinarith [sq_nonneg (v ⬝ᵥ y)]
    rw [h1]
    positivity
  · have hεt : ε * (v ⬝ᵥ y) ≤ v ⬝ᵥ v := by
      nlinarith [mul_le_mul_of_nonneg_right ht hvy]
    calc v ⬝ᵥ y = ε⁻¹ * (ε * (v ⬝ᵥ y)) := by
          field_simp
      _ ≤ ε⁻¹ * (v ⬝ᵥ v) :=
          mul_le_mul_of_nonneg_left hεt (by positivity)

/-- **(exact operator norm)** The Euclidean operator norm of the inverse
square root is exactly `ε^{-1/2}`: `‖G_N^{-1/2}‖ = ε_N^{-1/2}`. -/
theorem opNorm_invSqrtGram (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (invSqrtGram N ε)‖
      = (Real.sqrt ε)⁻¹ := by
  set S := invSqrtGram N ε with hS
  set T := Matrix.toEuclideanCLM (𝕜 := ℝ) S with hT
  set c : ℝ := (Real.sqrt ε)⁻¹ with hc
  have hcpos : 0 < c := inv_pos.mpr (Real.sqrt_pos.mpr hε)
  have hcsq : c * c = ε⁻¹ := by
    rw [hc, ← mul_inv, Real.mul_self_sqrt hε.le]
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ hcpos.le
    intro x
    set v : Fin (N + 1) → ℝ := WithLp.ofLp x with hv
    have hx : x = WithLp.toLp 2 v := rfl
    have hTx : T x = WithLp.toLp 2 (S *ᵥ v) := by
      rw [hx, hT, Matrix.toEuclideanCLM_toLp]
    have hinner : ∀ a b : Fin (N + 1) → ℝ,
        ⟪(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin (N + 1))),
          WithLp.toLp 2 b⟫ = a ⬝ᵥ b := by
      intro a b
      rw [PiLp.inner_apply]
      simp [dotProduct, mul_comm]
    have hnorm2 : ‖T x‖ ^ 2 = (S *ᵥ v) ⬝ᵥ (S *ᵥ v) := by
      rw [← real_inner_self_eq_norm_sq, hTx, hinner]
    have hxnorm2 : ‖x‖ ^ 2 = v ⬝ᵥ v := by
      rw [← real_inner_self_eq_norm_sq, hx, hinner]
    have hbound : ‖T x‖ ^ 2 ≤ (c * ‖x‖) ^ 2 := by
      rw [hnorm2, mul_pow, hxnorm2]
      calc (S *ᵥ v) ⬝ᵥ (S *ᵥ v) ≤ ε⁻¹ * (v ⬝ᵥ v) :=
            invSqrtGram_quad_bound N hε v
        _ = c * c * (v ⬝ᵥ v) := by rw [hcsq]
        _ = c ^ 2 * (v ⬝ᵥ v) := by ring
    have h1 : ‖T x‖ = Real.sqrt (‖T x‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    have h2 : Real.sqrt ((c * ‖x‖) ^ 2) = c * ‖x‖ :=
      Real.sqrt_sq (by positivity)
    rw [h1, ← h2]
    exact Real.sqrt_le_sqrt hbound
  · set u : EuclideanSpace ℝ (Fin (N + 1)) :=
      WithLp.toLp 2 (fun _ => (1 : ℝ)) with hu
    have hTu : T u = c • u := by
      rw [hu, hT, Matrix.toEuclideanCLM_toLp, invSqrtGram_mulVec_ones N hε]
      rfl
    have hu0 : u ≠ 0 := by
      intro h
      have h1 : (fun _ => (1 : ℝ)) = (0 : Fin (N + 1) → ℝ) := by
        simpa [hu] using congrArg (WithLp.ofLp (p := 2)) h
      have := congrFun h1 0
      norm_num at this
    have hnu : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
    have hratio := ContinuousLinearMap.ratio_le_opNorm T u
    rw [hTu, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos] at hratio
    calc c = c * ‖u‖ / ‖u‖ := by field_simp
      _ ≤ ‖T‖ := hratio

/-- **(eq:GTLOC-inverse-locality-collapse, chain)** The weighted Schur norm
dominates the Euclidean operator norm of the whitening factor, which is
exactly `ε^{-1/2}`:
`‖G_N^{-1/2}‖_{μ,Sch} ≥ ‖G_N^{-1/2}‖ = ε_N^{-1/2}`. -/
theorem invSqrtGram_schur_ge_opNorm (N : ℕ) {ε μ : ℝ} (hε : 0 < ε)
    (hμ : 0 ≤ μ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (invSqrtGram N ε)‖
      ≤ pathSchurNorm μ (invSqrtGram N ε) := by
  rw [opNorm_invSqrtGram N hε]
  exact pathSchurNorm_invSqrtGram_ge N hε hμ

/-- With a collapsing floor `ε_N ↓ 0`, the exact operator norms
`ε_N^{-1/2}` blow up. -/
theorem invSqrt_floor_blowup {ε : ℕ → ℝ} (hε : ∀ N, 0 < ε N)
    (hlim : Tendsto ε atTop (nhds 0)) :
    Tendsto (fun N => (Real.sqrt (ε N))⁻¹) atTop atTop := by
  have h1 : Tendsto (fun N => Real.sqrt (ε N)) atTop
      (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h2 : Tendsto Real.sqrt (nhds 0) (nhds (Real.sqrt 0)) :=
        Real.continuous_sqrt.tendsto 0
      rw [Real.sqrt_zero] at h2
      exact h2.comp hlim
    · exact Filter.Eventually.of_forall fun N =>
        Set.mem_Ioi.mpr (Real.sqrt_pos.mpr (hε N))
  exact h1.inv_tendsto_nhdsGT_zero

/-- **`cth:GTLOC-local-Gram-no-inverse`** (bundled): for path-Laplacian Gram
floors `G_N = ε_N I + L_N` with `ε_N ↓ 0`,

* the `G_N` have propagation radius one uniformly in `N`;
* their `μ`-weighted Schur norms are uniformly bounded for every fixed
  `μ ≥ 0`;
* nevertheless `‖G_N^{-1/2}‖_{μ,Sch} ≥ ‖G_N^{-1/2}‖ = ε_N^{-1/2}` and the
  weighted Schur norms of the whitening factors tend to infinity.

Locality of the reflected Gram does not transport through OS whitening. -/
theorem localGram_no_local_inverse {ε : ℕ → ℝ} (hε : ∀ N, 0 < ε N)
    (hmono : Antitone ε) (hlim : Tendsto ε atTop (nhds 0)) {μ : ℝ}
    (hμ : 0 ≤ μ) :
    (∀ N, ∀ i j : Fin (N + 1), 1 < Nat.dist i.val j.val →
      gramFloor N (ε N) i j = 0) ∧
    (∀ N, pathSchurNorm μ (gramFloor N (ε N))
      ≤ 3 * (Real.exp μ * (ε 0 + 2))) ∧
    (∀ N, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (invSqrtGram N (ε N))‖
      = (Real.sqrt (ε N))⁻¹) ∧
    (∀ N, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (invSqrtGram N (ε N))‖
      ≤ pathSchurNorm μ (invSqrtGram N (ε N))) ∧
    Tendsto (fun N => pathSchurNorm μ (invSqrtGram N (ε N))) atTop atTop := by
  refine ⟨fun N i j h => gramFloor_propagation N (ε N) h, fun N => ?_,
    fun N => opNorm_invSqrtGram N (hε N),
    fun N => invSqrtGram_schur_ge_opNorm N (hε N) hμ, ?_⟩
  · calc pathSchurNorm μ (gramFloor N (ε N))
        ≤ 3 * (Real.exp μ * (ε N + 2)) :=
          pathSchurNorm_gramFloor_le N (hε N).le hμ
      _ ≤ 3 * (Real.exp μ * (ε 0 + 2)) := by
          have h := hmono (Nat.zero_le N)
          have := Real.exp_pos μ
          nlinarith
  · exact tendsto_atTop_mono
      (fun N => pathSchurNorm_invSqrtGram_ge N (hε N) hμ)
      (invSqrt_floor_blowup hε hlim)

end LocalGramNoInverse

/-! ### `cth:GTLOC-local-endpoint-hidden-route`
A local endpoint can hide an arbitrarily long pair excursion.

The carrier `ℓ²({0,N})` is two-dimensional; it is rendered as `ℂ²` with basis
index `0` for the site `0` and index `1` for the site at distance `N` (`N`
enters only through the route interpretation). -/

section EndpointHiddenRoute

open scoped Matrix.Norms.Operator

/-- The ordinary first Duhamel response
`𝔇_{t,H}(V) = ∫₀ᵗ e^{-(t-s)H} V e^{-sH} ds`. -/
noncomputable def duhamelFirst (H V : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  ∫ s in (0 : ℝ)..t,
    NormedSpace.exp (-((t - s) • H)) * V * NormedSpace.exp (-(s • H))

/-- The symmetric pair Duhamel response
`𝔔_{t,H}(V,W) = ∫₀ᵗ ∫₀^{s₂} (e^{-(t-s₂)H} V e^{-(s₂-s₁)H} W e^{-s₁H}
+ (V ↔ W)) ds₁ ds₂`. -/
noncomputable def duhamelPair (H V W : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  ∫ s₂ in (0 : ℝ)..t, ∫ s₁ in (0 : ℝ)..s₂,
    (NormedSpace.exp (-((t - s₂) • H)) * V
        * NormedSpace.exp (-((s₂ - s₁) • H)) * W * NormedSpace.exp (-(s₁ • H))
      + NormedSpace.exp (-((t - s₂) • H)) * W
        * NormedSpace.exp (-((s₂ - s₁) • H)) * V
        * NormedSpace.exp (-(s₁ • H)))

/-- The long hop `V_N = |e₀⟩⟨e_N| + |e_N⟩⟨e₀|` (eq:GTLOC-long-hop). -/
noncomputable def longHop : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.vecMulVec (Pi.single 0 1) (star (Pi.single 1 1))
    + Matrix.vecMulVec (Pi.single 1 1) (star (Pi.single 0 1))

/-- The long hop in explicit matrix form. -/
theorem longHop_eq : longHop = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [longHop, Matrix.vecMulVec_apply]

/-- The long hop squares to the identity. -/
theorem longHop_sq : longHop * longHop = 1 := by
  rw [longHop_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- With trivial Hamiltonian the first Duhamel response is `t V`. -/
theorem duhamelFirst_zero_ham (V : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) :
    duhamelFirst 0 V t = t • V := by
  rw [duhamelFirst]
  simp only [smul_zero, neg_zero, NormedSpace.exp_zero, one_mul, mul_one]
  rw [intervalIntegral.integral_const, sub_zero]

/-- With trivial Hamiltonian the symmetric pair Duhamel response is
`(t²/2)(VW + WV)`. -/
theorem duhamelPair_zero_ham (V W : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) :
    duhamelPair 0 V W t = (t ^ 2 / 2) • (V * W + W * V) := by
  rw [duhamelPair]
  simp only [smul_zero, neg_zero, NormedSpace.exp_zero, one_mul, mul_one]
  simp only [intervalIntegral.integral_const, sub_zero]
  rw [intervalIntegral.integral_smul_const, integral_id]
  norm_num

/-- The diagonal case: `𝔔_{t,0}(V,V) = t² V²`. -/
theorem duhamelPair_zero_ham_self (V : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) :
    duhamelPair 0 V V t = t ^ 2 • (V * V) := by
  have h2 : (t ^ 2 / 2 * 2 : ℝ) = t ^ 2 := by ring
  rw [duhamelPair_zero_ham, ← two_smul ℝ (V * V), smul_smul, h2]

/-- **(eq:GTLOC-long-hop-first-zero)** The first endpoint response vanishes:
`J* 𝔇_{t,0}(V_N) J = 0` for the source `J = e₀`. -/
theorem longHop_first_response_zero (t : ℝ) :
    star (Pi.single (0 : Fin 2) (1 : ℂ))
        ⬝ᵥ (duhamelFirst 0 longHop t *ᵥ Pi.single 0 1) = 0 := by
  rw [duhamelFirst_zero_ham, longHop_eq]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- **(eq:GTLOC-long-hop-pair-return)** The pair endpoint response returns
with full weight: `J* 𝔔_{t,0}(V_N, V_N) J = t²`. -/
theorem longHop_pair_response (t : ℝ) :
    star (Pi.single (0 : Fin 2) (1 : ℂ))
        ⬝ᵥ (duhamelPair 0 longHop longHop t *ᵥ Pi.single 0 1)
      = (t : ℂ) ^ 2 := by
  rw [duhamelPair_zero_ham_self, longHop_sq]
  simp [dotProduct, Pi.single_apply, Complex.real_smul]

/-- **(hidden excursion)** Between the two insertions the state is the far
site: the long hop maps the source `e₀` to `e_N`, so every ordered pair path
visits the site at distance `N`. -/
theorem longHop_route_excursion :
    longHop *ᵥ Pi.single (0 : Fin 2) (1 : ℂ) = Pi.single 1 1 := by
  funext i
  fin_cases i <;>
    simp [longHop_eq, Matrix.mulVec, dotProduct, Pi.single_apply]

/-- **`cth:GTLOC-local-endpoint-hidden-route`** (bundled): with `H = 0`,
`J = e₀` and the long hop `V_N`, the first endpoint response vanishes, the
pair endpoint response equals `t²`, and the intermediate state of every
ordered pair path is the site at distance `N` — endpoint locality,
first-response invisibility and route locality are logically distinct. -/
theorem endpoint_hidden_route (t : ℝ) :
    star (Pi.single (0 : Fin 2) (1 : ℂ))
        ⬝ᵥ (duhamelFirst 0 longHop t *ᵥ Pi.single 0 1) = 0 ∧
    star (Pi.single (0 : Fin 2) (1 : ℂ))
        ⬝ᵥ (duhamelPair 0 longHop longHop t *ᵥ Pi.single 0 1) = (t : ℂ) ^ 2 ∧
    longHop *ᵥ Pi.single (0 : Fin 2) (1 : ℂ) = Pi.single 1 1 :=
  ⟨longHop_first_response_zero t, longHop_pair_response t,
    longHop_route_excursion⟩

end EndpointHiddenRoute

/-! ### `cth:SMOS-Ward-source-escape`
Cutoffwise Ward closure can escape the local continuum.

The ambient continuum carrier is `ℓ²(ℕ, ℂ)`; the index `0` carries the
vacuum `Ω` and index `n ≥ 1` carries the cutoff-`n` stress source `e_n`. -/

section WardSourceEscape

/-- The orthonormal family `Ω = e₀, e₁, e₂, …` in `ℓ²(ℕ, ℂ)`. -/
noncomputable def wardVector (n : ℕ) : lp (fun _ : ℕ => ℂ) 2 :=
  lp.single 2 n 1

/-- The cutoff carrier `ℋ_n = Span{Ω, e₁, …, e_n}`. -/
noncomputable def wardCutoff (n : ℕ) :
    Submodule ℂ (lp (fun _ : ℕ => ℂ) 2) :=
  Submodule.span ℂ (wardVector '' Set.Iic n)

/-- The physical screen `Q_r = |Ω⟩⟨Ω| + ∑_{1 ≤ j ≤ r} |e_j⟩⟨e_j|`. -/
noncomputable def wardScreen (r : ℕ) :
    lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  ∑ j ∈ Finset.range (r + 1),
    (innerSL ℂ (wardVector j)).smulRight (wardVector j)

/-- The Ward family is orthonormal:
`⟪e_m, e_n⟫ = δ_{mn}`. -/
theorem wardVector_inner (m n : ℕ) :
    ⟪wardVector m, wardVector n⟫_ℂ = if m = n then 1 else 0 := by
  rw [wardVector, wardVector, lp.inner_single_left]
  rcases eq_or_ne m n with h | h
  · subst h
    simp
  · simp [h]

/-- **(unit stress Gram)** Every cutoff has a unit stress Gram:
`⟪e_n, e_n⟫ = 1`. -/
theorem wardVector_inner_self (n : ℕ) : ⟪wardVector n, wardVector n⟫_ℂ = 1 := by
  rw [wardVector_inner, if_pos rfl]

/-- The cutoff-`n` stress source lives inside its own cutoff carrier. -/
theorem wardVector_mem_cutoff (n : ℕ) : wardVector n ∈ wardCutoff n :=
  Submodule.subset_span (Set.mem_image_of_mem _ (Set.mem_Iic.mpr le_rfl))

/-- The vacuum lives inside every cutoff carrier. -/
theorem wardVacuum_mem_cutoff (n : ℕ) : wardVector 0 ∈ wardCutoff n :=
  Submodule.subset_span (Set.mem_image_of_mem _ (Set.mem_Iic.mpr n.zero_le))

/-- Pointwise formula for the physical screen. -/
theorem wardScreen_apply (r : ℕ) (f : lp (fun _ : ℕ => ℂ) 2) :
    wardScreen r f
      = ∑ j ∈ Finset.range (r + 1), ⟪wardVector j, f⟫_ℂ • wardVector j := by
  simp [wardScreen]

/-- The physical screen fixes every basis vector of its own range. -/
theorem wardScreen_fixes {r j : ℕ} (hj : j < r + 1) :
    wardScreen r (wardVector j) = wardVector j := by
  rw [wardScreen_apply]
  rw [Finset.sum_eq_single j
    (fun k _ hkj => by rw [wardVector_inner, if_neg hkj, zero_smul])
    (fun hj' => absurd (Finset.mem_range.mpr hj) hj')]
  rw [wardVector_inner, if_pos rfl, one_smul]

/-- The physical screen is idempotent — it is a projection. -/
theorem wardScreen_idem (r : ℕ) (f : lp (fun _ : ℕ => ℂ) 2) :
    wardScreen r (wardScreen r f) = wardScreen r f := by
  rw [wardScreen_apply r f, map_sum]
  simp only [map_smul]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [wardScreen_fixes (Finset.mem_range.mp hj)]

/-- **(eq:SMOS-stress-source-escape)** For every fixed physical screen `Q_r`
the cutoff-`n` stress source escapes: `Q_r e_n = 0` for `n > r`. -/
theorem wardScreen_escape {r n : ℕ} (h : r < n) :
    wardScreen r (wardVector n) = 0 := by
  rw [wardScreen_apply]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hj' : j ≠ n := by
    have := Finset.mem_range.mp hj
    omega
  rw [wardVector_inner, if_neg hj', zero_smul]

/-- **`cth:SMOS-Ward-source-escape`** (bundled): every cutoff has a unit
stress Gram on its own carrier and the source lives in the cutoff span, yet
every fixed physical screen annihilates all later sources — cutoffwise stress
closure with a noncollapsing source norm does not produce transported source
incidence on an exhausting atlas. -/
theorem ward_source_escape (n : ℕ) :
    ⟪wardVector n, wardVector n⟫_ℂ = 1 ∧ wardVector n ∈ wardCutoff n ∧
      ∀ r, r < n → wardScreen r (wardVector n) = 0 :=
  ⟨wardVector_inner_self n, wardVector_mem_cutoff n,
    fun _ hr => wardScreen_escape hr⟩

end WardSourceEscape

/-! ### `cth:SMOS-energy-scalar-fibre`
Correct dynamics do not fix the absolute energy. -/

section EnergyScalarFibre

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **(commutator clause)** For every real `c`, the shifted energy
`E_Σ = H + cI` has the same commutators with all represented observables as
`H`: it implements the same Heisenberg/Euclidean derivation. -/
theorem energyScalarFibre_commutator (H A : Module.End ℂ E) (c : ℝ) :
    (H + (c : ℂ) • (1 : Module.End ℂ E)) * A
        - A * (H + (c : ℂ) • (1 : Module.End ℂ E))
      = H * A - A * H := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul,
    mul_one]
  abel

/-- **(vacuum-energy clause)** The vacuum energy of `H + cI` differs from
that of `H` by exactly `c` on the unit vacuum vector. -/
theorem energyScalarFibre_vacuum (H : Module.End ℂ E) (c : ℝ) {Om : E}
    (hOm : ‖Om‖ = 1) :
    ⟪Om, (H + (c : ℂ) • (1 : Module.End ℂ E)) Om⟫_ℂ
      = ⟪Om, H Om⟫_ℂ + (c : ℂ) := by
  have happ : (H + (c : ℂ) • (1 : Module.End ℂ E)) Om
      = H Om + (c : ℂ) • Om := by
    simp
  rw [happ, inner_add_right, inner_smul_right]
  have hnorm : ⟪Om, Om⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hOm]
    norm_num
  rw [hnorm, mul_one]

/-- **(nonclosure clause)** The shift is invisible to commutator Ward data
but changes the operator: for `c ≠ 0` and a nonzero vacuum, `H + cI ≠ H`. -/
theorem energyScalarFibre_shift_ne (H : Module.End ℂ E) {c : ℝ} (hc : c ≠ 0)
    {Om : E} (hOm : ‖Om‖ = 1) :
    H + (c : ℂ) • (1 : Module.End ℂ E) ≠ H := by
  intro h
  have h1 : (c : ℂ) • (1 : Module.End ℂ E) = 0 := by
    have := congrArg (fun X => X - H) h
    simpa [add_sub_cancel_left] using this
  have h2 : (c : ℂ) • Om = 0 := by
    have := congrArg (fun X : Module.End ℂ E => X Om) h1
    simpa using this
  have hOm0 : Om ≠ 0 := by
    intro h3
    rw [h3, norm_zero] at hOm
    norm_num at hOm
  rcases smul_eq_zero.mp h2 with h4 | h4
  · exact hc (by exact_mod_cast h4)
  · exact hOm0 h4

/-- **`cth:SMOS-energy-scalar-fibre`** (bundled): `E_Σ = H + cI` has the same
commutators with all represented observables as `H`, its vacuum energy
differs by `c`, and yet it is a different operator whenever `c ≠ 0` —
commutator Ward data alone cannot close the energy identification. -/
theorem energy_scalar_fibre (H : Module.End ℂ E) (c : ℝ) {Om : E}
    (hOm : ‖Om‖ = 1) :
    (∀ A : Module.End ℂ E,
      (H + (c : ℂ) • (1 : Module.End ℂ E)) * A
          - A * (H + (c : ℂ) • (1 : Module.End ℂ E)) = H * A - A * H) ∧
    ⟪Om, (H + (c : ℂ) • (1 : Module.End ℂ E)) Om⟫_ℂ
        = ⟪Om, H Om⟫_ℂ + (c : ℂ) ∧
    (c ≠ 0 → H + (c : ℂ) • (1 : Module.End ℂ E) ≠ H) :=
  ⟨fun A => energyScalarFibre_commutator H A c,
    energyScalarFibre_vacuum H c hOm,
    fun hc => energyScalarFibre_shift_ne H hc hOm⟩

end EnergyScalarFibre

/-! ### `cth:SMOS-expectation-Ward`
Expectation Ward identities are insufficient. -/

section ExpectationWard

/-- The Ward defect operator `D_W = |e₂⟩⟨e₂|` on `ℂ²`. -/
noncomputable def expectationWardDefect : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.vecMulVec (Pi.single 1 1) (star (Pi.single 1 1))

/-- **(eq:SMOS-expectation-no-go, vacuum clause)** The vacuum expectation of
the Ward defect vanishes: `⟨Ω, D_W Ω⟩ = 0` for `Ω = e₁`. -/
theorem expectationWard_vacuum_zero :
    star (Pi.single (0 : Fin 2) (1 : ℂ))
        ⬝ᵥ (expectationWardDefect *ᵥ Pi.single 0 1) = 0 := by
  simp [expectationWardDefect, Matrix.vecMulVec_apply, Matrix.mulVec,
    dotProduct, Pi.single_apply]

/-- **(eq:SMOS-expectation-no-go, nonvanishing clause)** The Ward defect is a
nonzero operator: `D_W ≠ 0`. -/
theorem expectationWard_defect_ne_zero : expectationWardDefect ≠ 0 := by
  intro h
  have h1 := congrFun (congrFun h 1) 1
  simp [expectationWardDefect, Matrix.vecMulVec_apply] at h1

/-- **`cth:SMOS-expectation-Ward`** (bundled): a Ward identity tested only in
the vacuum expectation does not establish the operator identity — the
explicit `ℂ²` witness has zero vacuum expectation but is nonzero. -/
theorem expectation_ward_insufficient :
    star (Pi.single (0 : Fin 2) (1 : ℂ))
        ⬝ᵥ (expectationWardDefect *ᵥ Pi.single 0 1) = 0 ∧
    expectationWardDefect ≠ 0 :=
  ⟨expectationWard_vacuum_zero, expectationWard_defect_ne_zero⟩

end ExpectationWard

end NCG
