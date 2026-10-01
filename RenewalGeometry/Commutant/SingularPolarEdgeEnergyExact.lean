/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Algebra.OddChoiOccurrenceExact
import RenewalGeometry.Commutant.SingularPolarData
import RenewalGeometry.Commutant.SourceCoercivityInfluenceExact

/-!
# Exact singular polar-edge energy and support leakage (`prop:singular-polar-energy`)

Spacetime–gauge duality manuscript, `app:polar-details`.

For polar data `F = U P` (`P ⪰ 0`, `P² = FᴴF`, `U` a partial isometry `U UᴴU = U`), with
`p = UᴴU`, `q = UUᴴ`, `A = p R_E p`, `B = Uᴴ q R_H q U`, `S = (A + B)/2`, `Δ = B − A`:

* `singular_polar_energy` — the exact decomposition `eq:singular-polar-energy` of
  `ℰ_F(R_E,R_H) = ‖R_H F − F R_E‖² + ‖R_E Fᴴ − Fᴴ R_H‖²` into
  `2‖[S,P]‖² + ½‖{Δ,P}‖²` and the four support-mixing terms;
* `singular_polar_support_bound_of_floor` — for every `μ ≥ 0` with `P ⪰ μ p`,
  `ℰ_F ≥ μ² (‖[p,R_E]‖² + ‖[q,R_H]‖² + 2‖B − A‖²)` (`eq:singular-polar-support-bound`);
* `supportProj_eq` / `singular_polar_support_bound` — the bound with `μ` the least positive
  eigenvalue of `P` (`posFloor`, i.e. `λ_min(P|_{pE})`), using that the spectral support
  projection of `P` is `p`;
* `singular_polar_energy_eq_zero_iff` — `ℰ_F = 0` iff `[p,R_E] = 0`, `[q,R_H] = 0`,
  `B = A` (transport of the supported blocks by `U`) and `[A,P] = 0`;
* `singular_polar_energy_arbitrary` — the same for an arbitrary rectangular `F`, with the
  polar data of `exists_singular_polar_data`.

Rendering disclosed: the polar data are taken as hypotheses (`P ⪰ 0`, `F = UP`,
`P² = FᴴF`, `UUᴴU = U`, and a support inverse `P†P = p` for the bound), from which
`pP = Pp = P` is derived (`polar_support_absorb`); the final sentence about the blocks on
`ker F`, `ker Fᴴ` is reflected by the identity, in which `(1−p)R_E(1−p)` and
`(1−q)R_H(1−q)` do not occur.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace RenewalGeometry
namespace SingularPolarEnergy

open OddChoiOccurrence GeometricThresholdBank SourceCoercivityInfluence

/-! ## Hilbert–Schmidt helpers for rectangular matrices -/

section HS

variable {m k : Type*} [Fintype m] [Fintype k]

theorem hsSq_eq_trace_conjTranspose_mul (A : Matrix m k ℂ) :
    (Aᴴ * A).trace = (hsSq A : ℂ) := by
  rw [Matrix.trace_mul_comm, trace_mul_conjTranspose_eq_hsSq]

theorem hsSq_eq_re (A : Matrix m k ℂ) : hsSq A = (Aᴴ * A).trace.re := by
  rw [hsSq_eq_trace_conjTranspose_mul, Complex.ofReal_re]

theorem hsSq_neg (A : Matrix m k ℂ) : hsSq (-A) = hsSq A := by
  simp [hsSq]

theorem hsSq_smul' (c : ℂ) (A : Matrix m k ℂ) : hsSq (c • A) = ‖c‖ ^ 2 * hsSq A := by
  simp only [hsSq, Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]

theorem hsSq_add (Y Z : Matrix m k ℂ) :
    hsSq (Y + Z) = hsSq Y + hsSq Z + 2 * (Zᴴ * Y).trace.re := by
  rw [hsSq_eq_re, hsSq_eq_re Y, hsSq_eq_re Z, Matrix.conjTranspose_add, Matrix.add_mul,
    Matrix.mul_add, Matrix.mul_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add]
  have h : (Yᴴ * Z).trace = star (Zᴴ * Y).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [h]
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re]
  ring

theorem hsSq_parallelogram (Y Z : Matrix m k ℂ) :
    hsSq (Y + Z) + hsSq (Y - Z) = 2 * hsSq Y + 2 * hsSq Z := by
  rw [sub_eq_add_neg, hsSq_add, hsSq_add, hsSq_neg, Matrix.conjTranspose_neg, Matrix.neg_mul,
    Matrix.trace_neg, Complex.neg_re]
  ring

theorem hsSq_mul_le_of_posSemidef_left [DecidableEq m] {M : Matrix m m ℂ} (hM : M.PosSemidef)
    (X : Matrix m k ℂ) : 0 ≤ (Xᴴ * M * X).trace.re :=
  (Complex.le_def.mp (hM.conjTranspose_mul_mul_same X).trace_nonneg).1

variable [DecidableEq m]

/-- Left Pythagoras for an orthogonal projection `r`: `‖r X‖² = Re Tr(Xᴴ r X)`. -/
theorem hsSq_proj_mul {r : Matrix m m ℂ} (hr : r * r = r) (hrH : rᴴ = r) (X : Matrix m k ℂ) :
    (hsSq (r * X) : ℂ) = (Xᴴ * r * X).trace := by
  rw [← hsSq_eq_trace_conjTranspose_mul, Matrix.conjTranspose_mul, hrH, Matrix.mul_assoc,
    ← Matrix.mul_assoc r r, hr, Matrix.mul_assoc]

theorem hsSq_pythag_left {r : Matrix m m ℂ} (hr : r * r = r) (hrH : rᴴ = r) (X : Matrix m k ℂ) :
    hsSq X = hsSq (r * X) + hsSq ((1 - r) * X) := by
  have h1r : (1 - r) * (1 - r) = 1 - r := by
    rw [sub_mul, mul_sub, mul_sub, hr, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]; abel
  have h1rH : (1 - r)ᴴ = 1 - r := by rw [Matrix.conjTranspose_sub, hrH, Matrix.conjTranspose_one]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_add, hsSq_proj_mul hr hrH, hsSq_proj_mul h1r h1rH,
    ← hsSq_eq_trace_conjTranspose_mul, ← Matrix.trace_add, ← Matrix.add_mul, ← Matrix.mul_add,
    add_sub_cancel, Matrix.mul_one]

end HS

section HS2

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

theorem hsSq_conjTranspose' (A : Matrix m k ℂ) : hsSq Aᴴ = hsSq A := by
  simp only [hsSq, Matrix.conjTranspose_apply, norm_star]
  exact Finset.sum_comm

theorem hsSq_zero' : hsSq (0 : Matrix m k ℂ) = 0 := by simp [hsSq]

theorem hsSq_pythag_right [DecidableEq k] {r : Matrix k k ℂ} (hr : r * r = r) (hrH : rᴴ = r)
    (X : Matrix m k ℂ) : hsSq X = hsSq (X * r) + hsSq (X * (1 - r)) := by
  have h1rH : (1 - r)ᴴ = 1 - r := by rw [Matrix.conjTranspose_sub, hrH, Matrix.conjTranspose_one]
  rw [← hsSq_conjTranspose' X, hsSq_pythag_left hr hrH Xᴴ, ← hsSq_conjTranspose' (X * r),
    ← hsSq_conjTranspose' (X * (1 - r)), Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hrH,
    h1rH]

/-- A partial isometry is isometric on its initial support: `‖W X‖ = ‖X‖` if `WᴴW X = X`. -/
theorem hsSq_iso_left (W : Matrix m n ℂ) (X : Matrix n k ℂ) (hX : (Wᴴ * W) * X = X) :
    hsSq (W * X) = hsSq X := by
  apply Complex.ofReal_injective
  rw [← hsSq_eq_trace_conjTranspose_mul, ← hsSq_eq_trace_conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Wᴴ, hX]

theorem hsSq_iso_right (W : Matrix n m ℂ) (X : Matrix k n ℂ) (hX : X * (W * Wᴴ) = X) :
    hsSq (X * W) = hsSq X := by
  rw [← hsSq_conjTranspose' (X * W), Matrix.conjTranspose_mul, hsSq_iso_left Wᴴ Xᴴ, hsSq_conjTranspose']
  rw [Matrix.conjTranspose_conjTranspose]
  have := congrArg Matrix.conjTranspose hX
  rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    at this

end HS2

/-! ## Polar data -/

section Polar

variable {E H : Type*} [Fintype E] [DecidableEq E] [Fintype H] [DecidableEq H]

theorem absorb_UUhU {U : Matrix H E ℂ} (hUp : U * (Uᴴ * U) = U) {k : Type*} (X : Matrix E k ℂ) :
    U * (Uᴴ * (U * X)) = U * X := by
  rw [← Matrix.mul_assoc Uᴴ, ← Matrix.mul_assoc, hUp]

theorem conj_hUp {U : Matrix H E ℂ} (hUp : U * (Uᴴ * U) = U) : Uᴴ * (U * Uᴴ) = Uᴴ := by
  have := congrArg Matrix.conjTranspose hUp
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    at this
  rwa [Matrix.mul_assoc] at this

theorem absorb_UhUUh {U : Matrix H E ℂ} (hUp : U * (Uᴴ * U) = U) {k : Type*} (X : Matrix H k ℂ) :
    Uᴴ * (U * (Uᴴ * X)) = Uᴴ * X := by
  rw [← Matrix.mul_assoc U, ← Matrix.mul_assoc, conj_hUp hUp]

theorem absorb_PUhU {U : Matrix H E ℂ} {P : Matrix E E ℂ} (hPp : P * (Uᴴ * U) = P) {k : Type*}
    (X : Matrix E k ℂ) : P * (Uᴴ * (U * X)) = P * X := by
  rw [← Matrix.mul_assoc Uᴴ, ← Matrix.mul_assoc, hPp]

theorem absorb_UhUP {U : Matrix H E ℂ} {P : Matrix E E ℂ} (hpP : Uᴴ * (U * P) = P) {k : Type*}
    (X : Matrix E k ℂ) : Uᴴ * (U * (P * X)) = P * X := by
  rw [← Matrix.mul_assoc U P X, ← Matrix.mul_assoc Uᴴ (U * P) X, hpP]

/-- From `P² = FᴴF` with `F = UP`, `P = Pᴴ` and `U UᴴU = U`, the support projection
`p = UᴴU` absorbs `P` on both sides. -/
theorem polar_support_absorb {U : Matrix H E ℂ} {P : Matrix E E ℂ} (hPH : Pᴴ = P)
    (hUp : U * (Uᴴ * U) = U) (hPP : P * P = (U * P)ᴴ * (U * P)) :
    (Uᴴ * U) * P = P ∧ P * (Uᴴ * U) = P := by
  have hp : (Uᴴ * U) * (Uᴴ * U) = Uᴴ * U := by rw [Matrix.mul_assoc, hUp]
  have hpH : (Uᴴ * U)ᴴ = Uᴴ * U := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  set p := Uᴴ * U with hpdef
  have h1p : (1 - p) * (1 - p) = 1 - p := by
    rw [sub_mul, mul_sub, mul_sub, hp, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]; abel
  have hPpP : P * p * P = P * P := by
    rw [hPP, hpdef, Matrix.conjTranspose_mul, hPH]; simp only [Matrix.mul_assoc]
  have h1 : ((1 - p) * P)ᴴ * ((1 - p) * P) = 0 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hpH, hPH]
    calc P * (1 - p) * ((1 - p) * P) = P * ((1 - p) * (1 - p)) * P := by
          simp only [Matrix.mul_assoc]
      _ = P * (1 - p) * P := by rw [h1p]
      _ = P * P - P * p * P := by rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
      _ = 0 := by rw [hPpP, sub_self]
  have h2 : (1 - p) * P = 0 := Matrix.conjTranspose_mul_self_eq_zero.mp h1
  rw [sub_mul, Matrix.one_mul, sub_eq_zero] at h2
  refine ⟨h2.symm, ?_⟩
  have := congrArg Matrix.conjTranspose h2
  rwa [Matrix.conjTranspose_mul, hPH, hpH, eq_comm] at this

/-- `A = p R_E p`. -/
def polarA (U : Matrix H E ℂ) (RE : Matrix E E ℂ) : Matrix E E ℂ := (Uᴴ * U) * RE * (Uᴴ * U)

/-- `B = Uᴴ q R_H q U`. -/
def polarB (U : Matrix H E ℂ) (RH : Matrix H H ℂ) : Matrix E E ℂ :=
  Uᴴ * (U * Uᴴ) * RH * (U * Uᴴ) * U

/-- `S = (A + B)/2`. -/
noncomputable def polarS (U : Matrix H E ℂ) (RE : Matrix E E ℂ) (RH : Matrix H H ℂ) :
    Matrix E E ℂ := (2 : ℂ)⁻¹ • (polarA U RE + polarB U RH)

/-- `Δ = B − A`. -/
def polarDelta (U : Matrix H E ℂ) (RE : Matrix E E ℂ) (RH : Matrix H H ℂ) : Matrix E E ℂ :=
  polarB U RH - polarA U RE

/-- The polar-edge energy `ℰ_F(R_E,R_H) = ‖R_H F − F R_E‖² + ‖R_E Fᴴ − Fᴴ R_H‖²`. -/
noncomputable def polarEnergy (F : Matrix H E ℂ) (RE : Matrix E E ℂ) (RH : Matrix H H ℂ) : ℝ :=
  hsSq (RH * F - F * RE) + hsSq (RE * Fᴴ - Fᴴ * RH)

theorem parallelogram_split (A B P : Matrix E E ℂ) :
    B * P - P * A = ((2 : ℂ)⁻¹ • (A + B) * P - P * ((2 : ℂ)⁻¹ • (A + B)))
        + (2 : ℂ)⁻¹ • ((B - A) * P + P * (B - A)) ∧
    A * P - P * B = ((2 : ℂ)⁻¹ • (A + B) * P - P * ((2 : ℂ)⁻¹ • (A + B)))
        - (2 : ℂ)⁻¹ • ((B - A) * P + P * (B - A)) := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul,
    Matrix.mul_sub]
  constructor <;> module

/-- **`eq:singular-polar-energy`.** -/
theorem singular_polar_energy {U : Matrix H E ℂ} {P : Matrix E E ℂ} (hPH : Pᴴ = P)
    (hUp : U * (Uᴴ * U) = U) (hPP : P * P = (U * P)ᴴ * (U * P))
    (RE : Matrix E E ℂ) (RH : Matrix H H ℂ) :
    polarEnergy (U * P) RE RH =
      2 * hsSq (polarS U RE RH * P - P * polarS U RE RH)
      + (1 / 2) * hsSq (polarDelta U RE RH * P + P * polarDelta U RE RH)
      + hsSq (P * (Uᴴ * U) * RE * (1 - Uᴴ * U))
      + hsSq ((1 - Uᴴ * U) * RE * (Uᴴ * U) * P)
      + hsSq (P * Uᴴ * (U * Uᴴ) * RH * (1 - U * Uᴴ))
      + hsSq ((1 - U * Uᴴ) * RH * (U * Uᴴ) * U * P) := by
  obtain ⟨hpP, hPp⟩ := polar_support_absorb hPH hUp hPP
  have hpP' : Uᴴ * (U * P) = P := by rw [← Matrix.mul_assoc, hpP]
  have hUhUUh := conj_hUp hUp
  have hp : (Uᴴ * U) * (Uᴴ * U) = Uᴴ * U := by rw [Matrix.mul_assoc, hUp]
  have hpH : (Uᴴ * U)ᴴ = Uᴴ * U := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hq : (U * Uᴴ) * (U * Uᴴ) = U * Uᴴ := by
    rw [Matrix.mul_assoc, hUhUUh]
  have hqH : (U * Uᴴ)ᴴ = U * Uᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hFH : (U * P)ᴴ = P * Uᴴ := by rw [Matrix.conjTranspose_mul, hPH]
  -- the first incidence equation, block by block
  set E1 := RH * (U * P) - U * P * RE with hE1
  have hE1split : hsSq E1 = hsSq ((U * Uᴴ) * E1 * (Uᴴ * U))
      + hsSq ((U * Uᴴ) * E1 * (1 - Uᴴ * U)) + hsSq ((1 - U * Uᴴ) * E1 * (Uᴴ * U))
      + hsSq ((1 - U * Uᴴ) * E1 * (1 - Uᴴ * U)) := by
    rw [hsSq_pythag_left hq hqH E1, hsSq_pythag_right hp hpH ((U * Uᴴ) * E1),
      hsSq_pythag_right hp hpH ((1 - U * Uᴴ) * E1)]
    ring
  have b11 : (U * Uᴴ) * E1 * (Uᴴ * U)
      = U * (polarB U RH * P - P * polarA U RE) := by
    simp only [hE1, polarA, polarB, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
      absorb_UUhU hUp, absorb_UhUUh hUp, absorb_PUhU hPp, absorb_UhUP hpP', hUp, hUhUUh, hPp,
      hpP']
  have b12 : (U * Uᴴ) * E1 * (1 - Uᴴ * U) = -(U * (P * (Uᴴ * U) * RE * (1 - Uᴴ * U))) := by
    simp only [hE1, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_assoc, absorb_UUhU hUp, absorb_UhUUh hUp, absorb_PUhU hPp, absorb_UhUP hpP',
      hUp, hUhUUh, hPp, hpP']
    abel
  have b21 : (1 - U * Uᴴ) * E1 * (Uᴴ * U) = (1 - U * Uᴴ) * RH * (U * Uᴴ) * U * P := by
    simp only [hE1, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_assoc, absorb_UUhU hUp, absorb_UhUUh hUp, absorb_PUhU hPp, absorb_UhUP hpP',
      hUp, hUhUUh, hPp, hpP']
    abel
  have b22 : (1 - U * Uᴴ) * E1 * (1 - Uᴴ * U) = 0 := by
    simp only [hE1, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_assoc, absorb_UUhU hUp, absorb_UhUUh hUp, absorb_PUhU hPp, absorb_UhUP hpP',
      hUp, hUhUUh, hPp, hpP']
    abel
  -- the adjoint incidence equation, block by block
  set E2 := RE * (U * P)ᴴ - (U * P)ᴴ * RH with hE2
  have hE2split : hsSq E2 = hsSq ((Uᴴ * U) * E2 * (U * Uᴴ))
      + hsSq ((Uᴴ * U) * E2 * (1 - U * Uᴴ)) + hsSq ((1 - Uᴴ * U) * E2 * (U * Uᴴ))
      + hsSq ((1 - Uᴴ * U) * E2 * (1 - U * Uᴴ)) := by
    rw [hsSq_pythag_left hp hpH E2, hsSq_pythag_right hq hqH ((Uᴴ * U) * E2),
      hsSq_pythag_right hq hqH ((1 - Uᴴ * U) * E2)]
    ring
  have c11 : (Uᴴ * U) * E2 * (U * Uᴴ) = (polarA U RE * P - P * polarB U RH) * Uᴴ := by
    simp only [hE2, hFH, polarA, polarB, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
      absorb_UUhU hUp, absorb_UhUUh hUp, absorb_PUhU hPp, absorb_UhUP hpP', hUp, hUhUUh, hPp,
      hpP']
  have c12 : (Uᴴ * U) * E2 * (1 - U * Uᴴ) = -(P * Uᴴ * (U * Uᴴ) * RH * (1 - U * Uᴴ)) := by
    simp only [hE2, hFH, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_assoc, absorb_UUhU hUp, absorb_UhUUh hUp, absorb_PUhU hPp, absorb_UhUP hpP',
      hUp, hUhUUh, hPp, hpP']
    abel
  have c21 : (1 - Uᴴ * U) * E2 * (U * Uᴴ) = (1 - Uᴴ * U) * RE * (Uᴴ * U) * P * Uᴴ := by
    simp only [hE2, hFH, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_assoc, absorb_UUhU hUp, absorb_UhUUh hUp, absorb_PUhU hPp, absorb_UhUP hpP',
      hUp, hUhUUh, hPp, hpP']
    abel
  have c22 : (1 - Uᴴ * U) * E2 * (1 - U * Uᴴ) = 0 := by
    simp only [hE2, hFH, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_assoc, absorb_UUhU hUp, absorb_UhUUh hUp, absorb_PUhU hPp, absorb_UhUP hpP',
      hUp, hUhUUh, hPp, hpP']
    abel
  -- isometric transport of the supported blocks
  have i11 : hsSq (U * (polarB U RH * P - P * polarA U RE)) = hsSq (polarB U RH * P - P * polarA U RE) := by
    refine hsSq_iso_left U _ ?_
    simp only [polarA, polarB, Matrix.mul_sub, Matrix.mul_assoc, absorb_UUhU hUp,
      absorb_UhUUh hUp, absorb_PUhU hPp, absorb_UhUP hpP', hUp, hUhUUh, hPp, hpP']
  have i12 : hsSq (-(U * (P * (Uᴴ * U) * RE * (1 - Uᴴ * U))))
      = hsSq (P * (Uᴴ * U) * RE * (1 - Uᴴ * U)) := by
    rw [hsSq_neg]
    refine hsSq_iso_left U _ ?_
    simp only [Matrix.mul_assoc, absorb_UhUP hpP']
  have i21 : hsSq ((polarA U RE * P - P * polarB U RH) * Uᴴ)
      = hsSq (polarA U RE * P - P * polarB U RH) := by
    refine hsSq_iso_right Uᴴ _ ?_
    rw [Matrix.conjTranspose_conjTranspose]
    simp only [polarA, polarB, Matrix.sub_mul, Matrix.mul_assoc, absorb_UUhU hUp,
      absorb_UhUUh hUp, absorb_PUhU hPp, absorb_UhUP hpP', hUp, hUhUUh, hPp, hpP']
  have i22 : hsSq ((1 - Uᴴ * U) * RE * (Uᴴ * U) * P * Uᴴ)
      = hsSq ((1 - Uᴴ * U) * RE * (Uᴴ * U) * P) := by
    refine hsSq_iso_right Uᴴ _ ?_
    rw [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc _ P, hPp]
  -- parallelogram
  obtain ⟨hsplit1, hsplit2⟩ := parallelogram_split (polarA U RE) (polarB U RH) P
  have hpar := hsSq_parallelogram (polarS U RE RH * P - P * polarS U RE RH)
    ((2 : ℂ)⁻¹ • (polarDelta U RE RH * P + P * polarDelta U RE RH))
  rw [hsSq_smul'] at hpar
  have hhalf : ‖(2 : ℂ)⁻¹‖ ^ 2 = 1 / 4 := by norm_num
  rw [hhalf] at hpar
  have e1 : hsSq (polarB U RH * P - P * polarA U RE)
      = hsSq (polarS U RE RH * P - P * polarS U RE RH
          + (2 : ℂ)⁻¹ • (polarDelta U RE RH * P + P * polarDelta U RE RH)) := by
    rw [hsplit1]; rfl
  have e2 : hsSq (polarA U RE * P - P * polarB U RH)
      = hsSq (polarS U RE RH * P - P * polarS U RE RH
          - (2 : ℂ)⁻¹ • (polarDelta U RE RH * P + P * polarDelta U RE RH)) := by
    rw [hsplit2]; rfl
  unfold polarEnergy
  rw [← hE1, ← hE2, hE1split, hE2split, b11, b12, b21, b22, c11, c12, c21, c22, i11, i12, i21,
    i22, hsSq_neg, hsSq_zero', hsSq_zero', e1, e2]
  linarith

end Polar

/-! ## Support-leakage lower bound -/

section Bound

variable {E H : Type*} [Fintype E] [DecidableEq E] [Fintype H] [DecidableEq H]

theorem hsSq_commutator_proj {m : Type*} [Fintype m] [DecidableEq m] {r : Matrix m m ℂ}
    (hr : r * r = r) (hrH : rᴴ = r) (X : Matrix m m ℂ) :
    hsSq (r * X - X * r) = hsSq (r * X * (1 - r)) + hsSq ((1 - r) * X * r) := by
  have hr' : ∀ Y : Matrix m m ℂ, r * (r * Y) = r * Y := fun Y => by rw [← Matrix.mul_assoc, hr]
  have hsplit := hsSq_pythag_left hr hrH (r * X - X * r)
  rw [hsSq_pythag_right hr hrH (r * (r * X - X * r)),
    hsSq_pythag_right hr hrH ((1 - r) * (r * X - X * r))] at hsplit
  have b11 : r * (r * X - X * r) * r = 0 := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hr, hr']; abel
  have b12 : r * (r * X - X * r) * (1 - r) = r * X * (1 - r) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc,
      hr, hr']; abel
  have b21 : (1 - r) * (r * X - X * r) * r = -((1 - r) * X * r) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc,
      hr, hr']; abel
  have b22 : (1 - r) * (r * X - X * r) * (1 - r) = 0 := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc,
      hr, hr']; abel
  rw [b11, b12, b21, b22, hsSq_neg, hsSq_zero'] at hsplit
  linarith

theorem proj_comm_kill {m : Type*} [Fintype m] [DecidableEq m] {r X : Matrix m m ℂ}
    (hr : r * r = r) (hc : r * X = X * r) : r * X * (1 - r) = 0 ∧ (1 - r) * X * r = 0 := by
  constructor
  · rw [Matrix.mul_sub, Matrix.mul_one, hc, Matrix.mul_assoc, hr, sub_self]
  · rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul, Matrix.mul_assoc r X r, ← hc,
      ← Matrix.mul_assoc, hr, sub_self]

/-- `P ⪰ μ p` with `P = pPp` gives `P² ⪰ μ² p`. -/
theorem sq_sub_posSemidef {P p : Matrix E E ℂ} (hPH : Pᴴ = P) (hp : p * p = p) (hpH : pᴴ = p)
    (hpP : p * P = P) (hPp : P * p = P) {μ : ℝ} (hμ : 0 ≤ μ)
    (hfloor : (P - (μ : ℂ) • p).PosSemidef) :
    (P * P - ((μ ^ 2 : ℝ) : ℂ) • p).PosSemidef := by
  have hMH : (P - (μ : ℂ) • p)ᴴ = P - (μ : ℂ) • p := hfloor.1
  have h1 : (P - (μ : ℂ) • p)ᴴ * (P - (μ : ℂ) • p) + ((2 * μ : ℝ) : ℂ) • (P - (μ : ℂ) • p)
      = P * P - ((μ ^ 2 : ℝ) : ℂ) • p := by
    rw [hMH]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, hpP, hPp, hp,
      smul_smul, smul_sub]
    push_cast
    module
  rw [← h1]
  refine (Matrix.posSemidef_conjTranspose_mul_self _).add (hfloor.smul ?_)
  exact_mod_cast mul_nonneg zero_le_two hμ

theorem floor_left {P p : Matrix E E ℂ} (hPH : Pᴴ = P) (hp : p * p = p) (hpH : pᴴ = p)
    (hpP : p * P = P) (hPp : P * p = P) {μ : ℝ} (hμ : 0 ≤ μ)
    (hfloor : (P - (μ : ℂ) • p).PosSemidef) {k : Type*} [Fintype k] (X : Matrix E k ℂ)
    (hX : p * X = X) : μ ^ 2 * hsSq X ≤ hsSq (P * X) := by
  have h0 := hsSq_mul_le_of_posSemidef_left (sq_sub_posSemidef hPH hp hpH hpP hPp hμ hfloor) X
  have t1 : (Xᴴ * (P * P) * X).trace = (hsSq (P * X) : ℂ) := by
    rw [← hsSq_eq_trace_conjTranspose_mul, Matrix.conjTranspose_mul, hPH]
    simp only [Matrix.mul_assoc]
  have t2 : (Xᴴ * p * X).trace = (hsSq X : ℂ) := by
    rw [Matrix.mul_assoc, hX, hsSq_eq_trace_conjTranspose_mul]
  have e1 : (Xᴴ * (P * P - ((μ ^ 2 : ℝ) : ℂ) • p) * X).trace
      = ((hsSq (P * X) : ℝ) : ℂ) - ((μ ^ 2 : ℝ) : ℂ) * (hsSq X : ℂ) := by
    rw [show Xᴴ * (P * P - ((μ ^ 2 : ℝ) : ℂ) • p) * X
        = Xᴴ * (P * P) * X - ((μ ^ 2 : ℝ) : ℂ) • (Xᴴ * p * X) by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul],
      Matrix.trace_sub, Matrix.trace_smul, t1, t2, smul_eq_mul]
  rw [e1, Complex.sub_re, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.ofReal_re] at h0
  linarith

theorem floor_right {P p : Matrix E E ℂ} (hPH : Pᴴ = P) (hp : p * p = p) (hpH : pᴴ = p)
    (hpP : p * P = P) (hPp : P * p = P) {μ : ℝ} (hμ : 0 ≤ μ)
    (hfloor : (P - (μ : ℂ) • p).PosSemidef) {k : Type*} [Fintype k] (X : Matrix k E ℂ)
    (hX : X * p = X) : μ ^ 2 * hsSq X ≤ hsSq (X * P) := by
  have hX' : p * Xᴴ = Xᴴ := by
    have := congrArg Matrix.conjTranspose hX
    rwa [Matrix.conjTranspose_mul, hpH] at this
  have := floor_left hPH hp hpH hpP hPp hμ hfloor Xᴴ hX'
  have e : hsSq (P * Xᴴ) = hsSq (X * P) := by
    rw [← hsSq_conjTranspose' (X * P), Matrix.conjTranspose_mul, hPH]
  calc μ ^ 2 * hsSq X = μ ^ 2 * hsSq Xᴴ := by rw [hsSq_conjTranspose']
    _ ≤ hsSq (P * Xᴴ) := this
    _ = hsSq (X * P) := e

theorem floor_anticommutator {P p : Matrix E E ℂ} (hp : p * p = p) (hpH : pᴴ = p)
    {μ : ℝ} (hμ : 0 ≤ μ) (hfloor : (P - (μ : ℂ) • p).PosSemidef) (D : Matrix E E ℂ)
    (hpD : p * D = D) (hDp : D * p = D) :
    4 * μ ^ 2 * hsSq D ≤ hsSq (D * P + P * D) := by
  set M := P - (μ : ℂ) • p with hM
  have hsplit : D * P + P * D = (M * D + D * M) + ((2 * μ : ℝ) : ℂ) • D := by
    rw [hM]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, hpD, hDp]
    push_cast
    module
  rw [hsplit, hsSq_add, hsSq_smul']
  have hc : ‖((2 * μ : ℝ) : ℂ)‖ ^ 2 = 4 * μ ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]; ring
  rw [hc]
  have hcross : 0 ≤ ((((2 * μ : ℝ) : ℂ) • D)ᴴ * (M * D + D * M)).trace.re := by
    rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, Matrix.mul_add, Matrix.trace_add,
      Complex.add_re]
    have h1 := hsSq_mul_le_of_posSemidef_left hfloor D
    have h2 := hsSq_mul_le_of_posSemidef_left hfloor Dᴴ
    rw [Matrix.conjTranspose_conjTranspose] at h2
    have e2 : (Dᴴ * (D * M)).trace = (D * M * Dᴴ).trace := (Matrix.trace_mul_comm (D * M) Dᴴ).symm
    rw [← Matrix.mul_assoc, e2]
    have := mul_nonneg (mul_nonneg zero_le_two hμ) (add_nonneg h1 h2)
    linarith
  have := hsSq_nonneg (M * D + D * M)
  nlinarith

/-- **`eq:singular-polar-support-bound`** for every `μ ≥ 0` with `P ⪰ μ p`:
`ℰ_F ≥ μ² (‖[p,R_E]‖² + ‖[q,R_H]‖² + 2‖Uᴴ q R_H q U − p R_E p‖²)`. -/
theorem singular_polar_support_bound_of_floor {U : Matrix H E ℂ} {P : Matrix E E ℂ}
    (hPH : Pᴴ = P) (hUp : U * (Uᴴ * U) = U) (hPP : P * P = (U * P)ᴴ * (U * P))
    {μ : ℝ} (hμ : 0 ≤ μ) (hfloor : (P - (μ : ℂ) • (Uᴴ * U)).PosSemidef)
    (RE : Matrix E E ℂ) (RH : Matrix H H ℂ) :
    μ ^ 2 * (hsSq ((Uᴴ * U) * RE - RE * (Uᴴ * U)) + hsSq ((U * Uᴴ) * RH - RH * (U * Uᴴ))
        + 2 * hsSq (polarB U RH - polarA U RE))
      ≤ polarEnergy (U * P) RE RH := by
  obtain ⟨hpP, hPp⟩ := polar_support_absorb hPH hUp hPP
  have hpP' : Uᴴ * (U * P) = P := by rw [← Matrix.mul_assoc, hpP]
  have hUhUUh := conj_hUp hUp
  have hp : (Uᴴ * U) * (Uᴴ * U) = Uᴴ * U := by rw [Matrix.mul_assoc, hUp]
  have hpH : (Uᴴ * U)ᴴ = Uᴴ * U := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hq : (U * Uᴴ) * (U * Uᴴ) = U * Uᴴ := by rw [Matrix.mul_assoc, hUhUUh]
  have hqH : (U * Uᴴ)ᴴ = U * Uᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [singular_polar_energy hPH hUp hPP RE RH, hsSq_commutator_proj hp hpH,
    hsSq_commutator_proj hq hqH]
  -- the four support-mixing terms
  have m1 : μ ^ 2 * hsSq ((Uᴴ * U) * RE * (1 - Uᴴ * U))
      ≤ hsSq (P * (Uᴴ * U) * RE * (1 - Uᴴ * U)) := by
    have := floor_left hPH hp hpH hpP hPp hμ hfloor ((Uᴴ * U) * RE * (1 - Uᴴ * U)) (by
      simp only [Matrix.mul_assoc, absorb_UhUUh hUp])
    simpa only [Matrix.mul_assoc] using this
  have m2 : μ ^ 2 * hsSq ((1 - Uᴴ * U) * RE * (Uᴴ * U))
      ≤ hsSq ((1 - Uᴴ * U) * RE * (Uᴴ * U) * P) :=
    floor_right hPH hp hpH hpP hPp hμ hfloor _ (by rw [Matrix.mul_assoc _ (Uᴴ * U), hp])
  have m3 : μ ^ 2 * hsSq ((U * Uᴴ) * RH * (1 - U * Uᴴ))
      ≤ hsSq (P * Uᴴ * (U * Uᴴ) * RH * (1 - U * Uᴴ)) := by
    have := floor_left hPH hp hpH hpP hPp hμ hfloor (Uᴴ * ((U * Uᴴ) * RH * (1 - U * Uᴴ))) (by
      simp only [Matrix.mul_assoc, absorb_UhUUh hUp])
    rw [hsSq_iso_left Uᴴ _ (by
      rw [Matrix.conjTranspose_conjTranspose]; simp only [Matrix.mul_assoc, absorb_UUhU hUp,
        absorb_UhUUh hUp])] at this
    simpa only [Matrix.mul_assoc] using this
  have m4 : μ ^ 2 * hsSq ((1 - U * Uᴴ) * RH * (U * Uᴴ))
      ≤ hsSq ((1 - U * Uᴴ) * RH * (U * Uᴴ) * U * P) := by
    have := floor_right hPH hp hpH hpP hPp hμ hfloor (((1 - U * Uᴴ) * RH * (U * Uᴴ)) * U) (by
      simp only [Matrix.mul_assoc, hUp])
    rw [hsSq_iso_right U _ (by rw [Matrix.mul_assoc _ (U * Uᴴ), hq])] at this
    exact this
  -- the anticommutator term
  have hD1 : (Uᴴ * U) * polarDelta U RE RH = polarDelta U RE RH := by
    simp only [polarDelta, polarA, polarB, Matrix.mul_sub, Matrix.mul_assoc, absorb_UhUUh hUp]
  have hD2 : polarDelta U RE RH * (Uᴴ * U) = polarDelta U RE RH := by
    simp only [polarDelta, polarA, polarB, Matrix.sub_mul, Matrix.mul_assoc, hUp, hp]
  have man := floor_anticommutator hp hpH hμ hfloor _ hD1 hD2
  have hS := hsSq_nonneg (polarS U RE RH * P - P * polarS U RE RH)
  have hdef : polarB U RH - polarA U RE = polarDelta U RE RH := rfl
  rw [hdef]
  nlinarith

/-- The spectral support projection of `P` is `p = UᴴU` (given a support inverse `P†P = p`). -/
theorem supportProj_eq {U : Matrix H E ℂ} {P Pd : Matrix E E ℂ} (hP : P.PosSemidef)
    (hUp : U * (Uᴴ * U) = U) (hPP : P * P = (U * P)ᴴ * (U * P)) (hPdP : Pd * P = Uᴴ * U) :
    supportProj hP.1 = Uᴴ * U := by
  obtain ⟨_, hPp⟩ := polar_support_absorb hP.1 hUp hPP
  have hpH : (Uᴴ * U)ᴴ = Uᴴ * U := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hQH : (supportProj hP.1)ᴴ = supportProj hP.1 := (supportProj_posSemidef hP.1).1
  have h1 : (Uᴴ * U) * supportProj hP.1 = Uᴴ * U := by
    rw [← hPdP, Matrix.mul_assoc, mul_supportProj hP]
  have h2 : supportProj hP.1 * (Uᴴ * U) = supportProj hP.1 := by
    rw [supportProj_eq_pinv_mul hP.1, Matrix.mul_assoc, hPp]
  have := congrArg Matrix.conjTranspose h1
  rw [Matrix.conjTranspose_mul, hQH, hpH, h2] at this
  exact this

/-- **`eq:singular-polar-support-bound`** with `μ = λ_min(P|_{pE})`, the least positive
eigenvalue of `P` (`posFloor`). -/
theorem singular_polar_support_bound {U : Matrix H E ℂ} {P Pd : Matrix E E ℂ}
    (hP : P.PosSemidef) (hUp : U * (Uᴴ * U) = U) (hPP : P * P = (U * P)ᴴ * (U * P))
    (hPdP : Pd * P = Uᴴ * U) (RE : Matrix E E ℂ) (RH : Matrix H H ℂ) :
    0 < posFloor hP.1 ∧
    posFloor hP.1 ^ 2 * (hsSq ((Uᴴ * U) * RE - RE * (Uᴴ * U))
        + hsSq ((U * Uᴴ) * RH - RH * (U * Uᴴ)) + 2 * hsSq (polarB U RH - polarA U RE))
      ≤ polarEnergy (U * P) RE RH := by
  refine ⟨posFloor_pos hP.1, singular_polar_support_bound_of_floor hP.1 hUp hPP
    (posFloor_pos hP.1).le ?_ RE RH⟩
  have := floor_posSemidef hP
  rwa [supportProj_eq hP hUp hPP hPdP] at this

/-- **Zero clause of `prop:singular-polar-energy`**: the energy vanishes iff `R_E`, `R_H`
reduce the supports (`[p,R_E] = 0`, `[q,R_H] = 0`), the supported blocks are transported by
`U` (`Uᴴ q R_H q U = p R_E p`) and the supported source block commutes with `P`. -/
theorem singular_polar_energy_eq_zero_iff {U : Matrix H E ℂ} {P Pd : Matrix E E ℂ}
    (hP : P.PosSemidef) (hUp : U * (Uᴴ * U) = U) (hPP : P * P = (U * P)ᴴ * (U * P))
    (hPdP : Pd * P = Uᴴ * U) (RE : Matrix E E ℂ) (RH : Matrix H H ℂ) :
    polarEnergy (U * P) RE RH = 0 ↔
      ((Uᴴ * U) * RE = RE * (Uᴴ * U) ∧ (U * Uᴴ) * RH = RH * (U * Uᴴ) ∧
        polarB U RH = polarA U RE ∧ polarA U RE * P = P * polarA U RE) := by
  have hPH := hP.1
  have hUhUUh := conj_hUp hUp
  have hp : (Uᴴ * U) * (Uᴴ * U) = Uᴴ * U := by rw [Matrix.mul_assoc, hUp]
  have hq : (U * Uᴴ) * (U * Uᴴ) = U * Uᴴ := by rw [Matrix.mul_assoc, hUhUUh]
  have hid := singular_polar_energy hPH hUp hPP RE RH
  constructor
  · intro h0
    obtain ⟨hμ, hb⟩ := singular_polar_support_bound hP hUp hPP hPdP RE RH
    rw [h0] at hb
    have n1 := hsSq_nonneg ((Uᴴ * U) * RE - RE * (Uᴴ * U))
    have n2 := hsSq_nonneg ((U * Uᴴ) * RH - RH * (U * Uᴴ))
    have n3 := hsSq_nonneg (polarB U RH - polarA U RE)
    have hμ2 : 0 < posFloor hP.1 ^ 2 := by positivity
    have hsum : hsSq ((Uᴴ * U) * RE - RE * (Uᴴ * U)) + hsSq ((U * Uᴴ) * RH - RH * (U * Uᴴ))
        + 2 * hsSq (polarB U RH - polarA U RE) = 0 := by
      have := mul_nonneg hμ2.le (by positivity : (0 : ℝ) ≤ hsSq ((Uᴴ * U) * RE - RE * (Uᴴ * U))
        + hsSq ((U * Uᴴ) * RH - RH * (U * Uᴴ)) + 2 * hsSq (polarB U RH - polarA U RE))
      nlinarith
    have z1 : hsSq ((Uᴴ * U) * RE - RE * (Uᴴ * U)) = 0 := by linarith
    have z2 : hsSq ((U * Uᴴ) * RH - RH * (U * Uᴴ)) = 0 := by linarith
    have z3 : hsSq (polarB U RH - polarA U RE) = 0 := by linarith
    rw [hsSq_eq_zero_iff, sub_eq_zero] at z1 z2 z3
    refine ⟨z1, z2, z3, ?_⟩
    have hS : polarS U RE RH = polarA U RE := by
      rw [polarS, z3, ← two_smul ℂ (polarA U RE), smul_smul]; norm_num
    have hD : polarDelta U RE RH = 0 := by rw [polarDelta, z3, sub_self]
    rw [hS, hD] at hid
    have n4 := hsSq_nonneg (polarA U RE * P - P * polarA U RE)
    have n5 := hsSq_nonneg (P * (Uᴴ * U) * RE * (1 - Uᴴ * U))
    have n6 := hsSq_nonneg ((1 - Uᴴ * U) * RE * (Uᴴ * U) * P)
    have n7 := hsSq_nonneg (P * Uᴴ * (U * Uᴴ) * RH * (1 - U * Uᴴ))
    have n8 := hsSq_nonneg ((1 - U * Uᴴ) * RH * (U * Uᴴ) * U * P)
    have n9 := hsSq_nonneg ((0 : Matrix E E ℂ) * P + P * 0)
    have z4 : hsSq (polarA U RE * P - P * polarA U RE) = 0 := by linarith
    rw [hsSq_eq_zero_iff, sub_eq_zero] at z4
    exact z4
  · rintro ⟨c1, c2, c3, c4⟩
    have hS : polarS U RE RH = polarA U RE := by
      rw [polarS, c3, ← two_smul ℂ (polarA U RE), smul_smul]; norm_num
    have hD : polarDelta U RE RH = 0 := by rw [polarDelta, c3, sub_self]
    obtain ⟨k1, k2⟩ := proj_comm_kill hp c1
    obtain ⟨k3, k4⟩ := proj_comm_kill hq c2
    have e1 : P * (Uᴴ * U) * RE * (1 - Uᴴ * U) = 0 := by
      rw [show P * (Uᴴ * U) * RE * (1 - Uᴴ * U) = P * ((Uᴴ * U) * RE * (1 - Uᴴ * U)) by
        simp only [Matrix.mul_assoc], k1, Matrix.mul_zero]
    have e2 : (1 - Uᴴ * U) * RE * (Uᴴ * U) * P = 0 := by rw [k2, Matrix.zero_mul]
    have e3 : P * Uᴴ * (U * Uᴴ) * RH * (1 - U * Uᴴ) = 0 := by
      rw [show P * Uᴴ * (U * Uᴴ) * RH * (1 - U * Uᴴ) = P * Uᴴ * ((U * Uᴴ) * RH * (1 - U * Uᴴ)) by
        simp only [Matrix.mul_assoc], k3, Matrix.mul_zero]
    have e4 : (1 - U * Uᴴ) * RH * (U * Uᴴ) * U * P = 0 := by
      rw [k4, Matrix.zero_mul, Matrix.zero_mul]
    rw [hid, hS, hD, c4, sub_self, e1, e2, e3, e4]
    simp [hsSq_zero']

/-- **`prop:singular-polar-energy` for an arbitrary rectangular `F`**: with the polar data of
`exists_singular_polar_data`, the exact energy identity, the support-leakage bound with
`μ = λ_min(P|_{pE}) > 0`, and the zero clause. -/
theorem singular_polar_energy_arbitrary {e : ℕ} (F : Matrix H (Fin e) ℂ) :
    ∃ (U : Matrix H (Fin e) ℂ) (P : Matrix (Fin e) (Fin e) ℂ) (hP : P.PosSemidef),
      F = U * P ∧ P * P = Fᴴ * F ∧ U * (Uᴴ * U) = U ∧
      ∀ (RE : Matrix (Fin e) (Fin e) ℂ) (RH : Matrix H H ℂ),
        polarEnergy F RE RH =
            2 * hsSq (polarS U RE RH * P - P * polarS U RE RH)
            + (1 / 2) * hsSq (polarDelta U RE RH * P + P * polarDelta U RE RH)
            + hsSq (P * (Uᴴ * U) * RE * (1 - Uᴴ * U))
            + hsSq ((1 - Uᴴ * U) * RE * (Uᴴ * U) * P)
            + hsSq (P * Uᴴ * (U * Uᴴ) * RH * (1 - U * Uᴴ))
            + hsSq ((1 - U * Uᴴ) * RH * (U * Uᴴ) * U * P) ∧
        0 < posFloor hP.1 ∧
        posFloor hP.1 ^ 2 * (hsSq ((Uᴴ * U) * RE - RE * (Uᴴ * U))
            + hsSq ((U * Uᴴ) * RH - RH * (U * Uᴴ)) + 2 * hsSq (polarB U RH - polarA U RE))
          ≤ polarEnergy F RE RH ∧
        (polarEnergy F RE RH = 0 ↔
          ((Uᴴ * U) * RE = RE * (Uᴴ * U) ∧ (U * Uᴴ) * RH = RH * (U * Uᴴ) ∧
            polarB U RH = polarA U RE ∧ polarA U RE * P = P * polarA U RE)) := by
  obtain ⟨U, P, Pd, hP, hFUP, hPP, hUp, _, hPdP, _⟩ := exists_singular_polar_data F
  have hPP' : P * P = (U * P)ᴴ * (U * P) := by rw [hPP, hFUP]
  refine ⟨U, P, hP, hFUP, hPP, hUp, fun RE RH => ?_⟩
  subst hFUP
  exact ⟨singular_polar_energy hP.1 hUp hPP' RE RH,
    (singular_polar_support_bound hP hUp hPP' hPdP RE RH).1,
    (singular_polar_support_bound hP hUp hPP' hPdP RE RH).2,
    singular_polar_energy_eq_zero_iff hP hUp hPP' hPdP RE RH⟩

end Bound

end SingularPolarEnergy
end RenewalGeometry
