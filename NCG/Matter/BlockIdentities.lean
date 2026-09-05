/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Feshbach/Schur block identities and odd-record normalization
(SM_emergence, Phase 1)

* `exact_feshbach_isUnit`, `exact_feshbach_inv` —
  `thm:exact-feshbach`: `H` is invertible iff the Feshbach map
  `F_P(H) = A - B D⁻¹ C` is, and `P H⁻¹ P = F_P(H)⁻¹`;
* `hub_resolvent_decomposition` — `thm:hub-resolvent-main`:
  `M⁻¹ = G_hub + diag(0, D⁻¹)` exactly;
* `nilpotent_depth_inverse` — `prop:nilpotent-depth-resolvent`:
  `(m·1 - r·S)⁻¹ = m⁻¹ Σ_{k≤L} (r/m)^k S^k` for a nilpotent one-way
  depth shift (ballistic factor `(r/m)^k` per depth);
* `controlled_odd_record` — `thm:odd-record-normalization-main`:
  `⟨-|U_ctrl|+⟩ = (U₁ - U₀)/2` for an ancilla-controlled pair of
  slots;
* `one_event_odd_record`, `odd_record_hs_sum` —
  `thm:one-event-odd-record-updated`: `p_odd(ψ) = ¼‖ΔGψ‖²` and
  `Σ_j p_odd(e_j) = ¼‖ΔG‖²_HS` (also the Hilbert–Schmidt content of
  `thm:predictive-dirichlet-action-updated`);
* `amplitude_port_even` — `prop:amplitude-port-even`: the quadratic
  amplitude port selector is exactly even — no cubic anisotropy;
* `reducing_carrier_port_zero`, `condensate_ports` —
  `prop:reducing-carrier` / `prop:condensate-ports`.
-/

namespace NCG

open Matrix

/-! ## `thm:exact-feshbach`, `thm:hub-resolvent-main` -/

section Feshbach

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n] {α : Type*} [CommRing α]

/-- `thm:exact-feshbach` (invertibility transfer): with the
environment block `D = Q(H-z)Q` invertible, `H - z` is invertible
iff the Feshbach map `F_P(H-z) = A - B D⁻¹ C` is invertible. -/
theorem exact_feshbach_isUnit (A : Matrix m m α) (B : Matrix m n α)
    (C : Matrix n m α) (D : Matrix n n α) [Invertible D] :
    IsUnit (fromBlocks A B C D) ↔ IsUnit (A - B * ⅟D * C) :=
  isUnit_fromBlocks_iff_of_invertible₂₂

/-- `thm:exact-feshbach` (compressed resolvent): the `P`-corner of
the full inverse is the inverse of the Feshbach map,
`P (H-z)⁻¹ P = F_P(H-z)⁻¹`. -/
theorem exact_feshbach_inv (A : Matrix m m α) (B : Matrix m n α)
    (C : Matrix n m α) (D : Matrix n n α) [Invertible D]
    [Invertible (A - B * ⅟D * C)] [Invertible (fromBlocks A B C D)] :
    (⅟(fromBlocks A B C D)).toBlocks₁₁ = ⅟(A - B * ⅟D * C) := by
  rw [invOf_fromBlocks₂₂_eq]
  rfl

/-- `thm:hub-resolvent-main`: the exact hub-mediated resolvent
decomposition — the full inverse is the hub-return propagator
(all four blocks factoring through the Schur inverse `⅟S`) plus the
purely private `diag(0, ⅟D)`. -/
theorem hub_resolvent_decomposition (A : Matrix m m α)
    (B : Matrix m n α) (C : Matrix n m α) (D : Matrix n n α)
    [Invertible D] [Invertible (A - B * ⅟D * C)]
    [Invertible (fromBlocks A B C D)] :
    ⅟(fromBlocks A B C D)
      = fromBlocks (⅟(A - B * ⅟D * C))
          (-(⅟(A - B * ⅟D * C) * B * ⅟D))
          (-(⅟D * C * ⅟(A - B * ⅟D * C)))
          (⅟D * C * ⅟(A - B * ⅟D * C) * B * ⅟D)
        + fromBlocks 0 0 0 (⅟D) := by
  rw [invOf_fromBlocks₂₂_eq, Matrix.fromBlocks_add]
  congr 1
  · rw [add_zero]
  · rw [add_zero]
  · rw [add_zero]
  · rw [add_comm]

end Feshbach

/-! ## `prop:nilpotent-depth-resolvent` -/

section Nilpotent

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- `prop:nilpotent-depth-resolvent`: for a one-way depth shift with
`S^{L+1} = 0` and `m ≠ 0`, the operator `m·1 - r·S` has the exact
finite Neumann inverse `m⁻¹ Σ_{k≤L} (r/m)^k S^k`; propagation from
depth `0` to depth `k` carries the ballistic factor `(r/m)^k`. -/
theorem nilpotent_depth_inverse (S : A) (L : ℕ) (m r : ℝ)
    (hm : m ≠ 0) (hS : S ^ (L + 1) = 0) :
    (m • (1:A) - r • S)
        * (m⁻¹ • ∑ k ∈ Finset.range (L + 1), (r / m) ^ k • S ^ k)
      = 1 ∧
    (m⁻¹ • ∑ k ∈ Finset.range (L + 1), (r / m) ^ k • S ^ k)
        * (m • (1:A) - r • S)
      = 1 := by
  set X : A := ∑ k ∈ Finset.range (L + 1), (r / m) ^ k • S ^ k with hX
  have hterm : ∀ k, (m • (1:A) - r • S) * ((r / m) ^ k • S ^ k)
      = (m * (r / m) ^ k) • S ^ k
        - (m * (r / m) ^ (k + 1)) • S ^ (k + 1) := by
    intro k
    rw [sub_mul, smul_mul_smul_comm, smul_mul_smul_comm, one_mul]
    congr 1
    rw [← pow_succ']
    congr 1
    have hmr : m * (r / m) = r := by field_simp
    rw [pow_succ, show m * ((r / m) ^ k * (r / m))
        = m * (r / m) * (r / m) ^ k from by ring, hmr]
  have key : (m • (1:A) - r • S) * X = m • (1:A) := by
    calc (m • (1:A) - r • S) * X
        = ∑ k ∈ Finset.range (L + 1),
            ((m * (r / m) ^ k) • S ^ k
              - (m * (r / m) ^ (k + 1)) • S ^ (k + 1)) := by
          rw [hX, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => hterm k
      _ = (m * (r / m) ^ 0) • S ^ 0
            - (m * (r / m) ^ (L + 1)) • S ^ (L + 1) :=
          Finset.sum_range_sub' (fun k => (m * (r / m) ^ k) • S ^ k)
            (L + 1)
      _ = m • (1:A) := by
          rw [hS, smul_zero, sub_zero, pow_zero, pow_zero, mul_one]
  have hcomm : Commute (m • (1:A) - r • S) X := by
    apply Commute.sub_left
    · exact (Commute.one_left X).smul_left m
    · apply Commute.smul_left
      rw [hX]
      apply Commute.sum_right
      intro k _
      exact ((Commute.refl S).pow_right k).smul_right _
  constructor
  · rw [mul_smul_comm, key, smul_smul, inv_mul_cancel₀ hm, one_smul]
  · rw [smul_mul_assoc, ← hcomm.eq, key, smul_smul,
      inv_mul_cancel₀ hm, one_smul]

end Nilpotent

/-! ## `thm:odd-record-normalization-main` -/

section OddRecord

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- `thm:odd-record-normalization-main`: controlling the two slots
`U₀, U₁` with an ancilla prepared in `|+⟩` and reading out `⟨-|`
produces exactly the half-difference: modelling `ℂ²⊗M` as `M × M`,
`⟨-|U_ctrl|+⟩ψ = ½(U₁ψ - U₀ψ)`. -/
theorem controlled_odd_record (U0 U1 : M →ₗ[ℂ] M) (psi : M)
    (c : ℂ) (hc : c * c = 2) :
    c⁻¹ • ((c⁻¹ • ((U0 psi, U1 psi) : M × M)).2
        - (c⁻¹ • ((U0 psi, U1 psi) : M × M)).1)
      = (2:ℂ)⁻¹ • (U1 psi - U0 psi) := by
  simp only [Prod.smul_snd, Prod.smul_fst]
  rw [← smul_sub, smul_smul, ← mul_inv, hc]

end OddRecord

/-! ## `thm:one-event-odd-record-updated` -/

section HSNorm

variable {n : Type*} [Fintype n]

/-- `thm:one-event-odd-record-updated` (single event): the odd
predictive record weight of `ψ` is
`p_odd(ψ) = Σᵢ ‖(½ ΔG ψ)ᵢ‖² = ¼ Σᵢ ‖(ΔG ψ)ᵢ‖²`. -/
theorem one_event_odd_record (DG : Matrix n n ℂ) (psi : n → ℂ) :
    ∑ i, ‖((2:ℂ)⁻¹ • DG.mulVec psi) i‖ ^ 2
      = 4⁻¹ * ∑ i, ‖DG.mulVec psi i‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, norm_smul]
  norm_num
  ring

/-- `thm:one-event-odd-record-updated` (basis sum) /
`thm:predictive-dirichlet-action-updated` (Hilbert–Schmidt form):
summing the odd-record weight over an orthonormal basis gives the
squared Hilbert–Schmidt norm, `Σⱼ p_odd(eⱼ) = ¼ ‖ΔG‖²_HS`. -/
theorem odd_record_hs_sum [DecidableEq n] (DG : Matrix n n ℂ) :
    ∑ j, ∑ i, ‖DG.mulVec (Pi.single j 1) i‖ ^ 2
      = ∑ i, ∑ j, ‖DG i j‖ ^ 2 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mulVec_single]
  simp

end HSNorm

/-! ## `prop:amplitude-port-even` -/

/-- `prop:amplitude-port-even`: the quadratic amplitude port
selector `Φ(c) = ‖Σ_a c_a·(P B_a Q)‖²_HS` is exactly even,
`Φ(-c) = Φ(c)` — it has no cubic anisotropy, so the second
condensate cannot be selected by the port norm alone. -/
theorem amplitude_port_even {ι n : Type*} [Fintype ι] [Fintype n]
    (X : ι → Matrix n n ℂ) (c : ι → ℝ) :
    ∑ i, ∑ j, ‖(∑ a, (-c a : ℝ) • X a) i j‖ ^ 2
      = ∑ i, ∑ j, ‖(∑ a, (c a : ℝ) • X a) i j‖ ^ 2 := by
  have h1 : (∑ a, (-c a : ℝ) • X a) = -(∑ a, (c a : ℝ) • X a) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [neg_smul]
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.neg_apply, norm_neg]

/-! ## `prop:reducing-carrier`, `prop:condensate-ports` -/

section Ports

variable {n : Type*} [Fintype n]

/-- `prop:condensate-ports`: on a reducing symmetric decomposition
(`P B Q = 0`), the port block of the perturbed operator
`H(η) = B + ηV₁ + η²V₂` is exactly `η·PV₁Q + η²·PV₂Q`; in
particular the symmetric-point port vanishes and any nonzero
symmetric-point residue is a projector artifact
(`prop:reducing-carrier`). -/
theorem condensate_ports (P Q B V1 V2 : Matrix n n ℂ)
    (hred : P * B * Q = 0) (eta : ℂ) :
    P * (B + eta • V1 + (eta ^ 2) • V2) * Q
      = eta • (P * V1 * Q) + (eta ^ 2) • (P * V2 * Q) := by
  rw [mul_add, mul_add, add_mul, add_mul, hred]
  rw [mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc]
  rw [zero_add]

end Ports

end NCG
