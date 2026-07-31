/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# One-generation anomaly arithmetic and channel block no-gos
  (`thm:anomalies`, `thm:gauge-trace`, `prop:charge-transform`,
   `thm:kraus-block-nogo`, `cor:stinespring-intertwining` support,
   SM_emergence; also `thm:anomaly`, `thm:coupling` of the
   arithmetic monograph)

* `anomaly_su3_sq_u1` / `anomaly_su2_sq_u1` / `anomaly_u1_cubed` /
  `anomaly_grav_u1` / `anomaly_witten_doublets` — the five anomaly
  sums of one Standard-Model generation (left-handed Weyl
  convention `Q_L(1/6), u^c(-2/3), d^c(1/3), L_L(-1/2), e^c(1)`)
  vanish exactly, and the number of weak doublets is even;
* `gauge_trace_weinberg` — the common-trace normalization
  `g₁² = (3/5)g²` gives `sin²θ_W = 3/8` at matching;
* `charge_transform` — the singlet–adjoint transform
  `Q = A - B/√12`, `L = A + 3B/√12` is inverted by
  `A = (3Q+L)/4`, `B = (√12/4)(L-Q)`, with the Parseval identity
  `3QᴴQ + LᴴL = 4AᴴA + BᴴB`;
* `kraus_block_nogo` — for a completely positive channel,
  `P_t𝒯(P_s)P_t = Σ (P_tK_αP_s)(P_tK_αP_s)ᴴ`, and if this
  vanishes then every cross block `P_tK_αP_s` is zero.
-/

namespace NCG

open Matrix

/-- `SU(3)²·U(1)`: the hypercharge trace over colour triplets
vanishes: `2·(1/6) + (-2/3) + (1/3) = 0`. -/
theorem anomaly_su3_sq_u1 :
    2 * (1 / 6 : ℚ) + (-(2 / 3)) + (1 / 3) = 0 := by norm_num

/-- `SU(2)²·U(1)`: the hypercharge trace over weak doublets
vanishes: `3·(1/6) + (-1/2) = 0`. -/
theorem anomaly_su2_sq_u1 :
    3 * (1 / 6 : ℚ) + (-(1 / 2)) = 0 := by norm_num

/-- `U(1)³`: the hypercharge cube sum over the fifteen Weyl
components vanishes. -/
theorem anomaly_u1_cubed :
    6 * (1 / 6 : ℚ) ^ 3 + 3 * (-(2 / 3)) ^ 3 + 3 * (1 / 3) ^ 3
      + 2 * (-(1 / 2)) ^ 3 + 1 ^ 3 = 0 := by norm_num

/-- Mixed gravitational–`U(1)`: the hypercharge sum vanishes. -/
theorem anomaly_grav_u1 :
    6 * (1 / 6 : ℚ) + 3 * (-(2 / 3)) + 3 * (1 / 3)
      + 2 * (-(1 / 2)) + 1 = 0 := by norm_num

/-- The global mod-two `SU(2)` (Witten) anomaly: one generation has
an even number of weak doublets (three coloured plus one lepton). -/
theorem anomaly_witten_doublets : (3 + 1) % 2 = 0 := by norm_num

/-- `thm:gauge-trace`: the common finite trace fixes
`g₁² = (3/5)g²`, hence `sin²θ_W = g'²/(g² + g'²) = 3/8` at the
matching scale. -/
theorem gauge_trace_weinberg (g : ℝ) (hg : 0 < g) :
    (3 / 5) * g ^ 2 / (g ^ 2 + (3 / 5) * g ^ 2) = 3 / 8 := by
  have h : g ^ 2 > 0 := by positivity
  field_simp
  ring

/-- `prop:charge-transform`: the singlet–adjoint transform is
invertible and satisfies the Parseval identity
`3QᴴQ + LᴴL = 4AᴴA + BᴴB`. -/
theorem charge_transform {d : Type*} [Fintype d]
    (A B : Matrix d d ℂ) (s : ℝ) (hs : s ^ 2 = 12) (hs0 : s ≠ 0) :
    (3 • (A - ((1 : ℂ) / s) • B) + (A + ((3 : ℂ) / s) • B)
        = (4 : ℂ) • A)
      ∧ (((s : ℂ) / 4) • ((A + ((3 : ℂ) / s) • B)
          - (A - ((1 : ℂ) / s) • B)) = B)
      ∧ ((3 : ℂ) • ((A - ((1 : ℂ) / s) • B)ᴴ
            * (A - ((1 : ℂ) / s) • B))
          + (A + ((3 : ℂ) / s) • B)ᴴ * (A + ((3 : ℂ) / s) • B)
        = (4 : ℂ) • (Aᴴ * A) + Bᴴ * B) := by
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0
  have hsC2 : (s : ℂ) ^ 2 = 12 := by exact_mod_cast hs
  refine ⟨?_, ?_, ?_⟩
  · match_scalars
    all_goals ring
  · match_scalars
    · ring
    · field_simp
      ring
  · have hconj : ∀ c : ℂ, ∀ M : Matrix d d ℂ,
        (c • M)ᴴ = (starRingEnd ℂ) c • Mᴴ :=
      fun c M => Matrix.conjTranspose_smul c M
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
      hconj, hconj]
    have hstar1 : (starRingEnd ℂ) ((1 : ℂ) / s) = (1 : ℂ) / s := by
      rw [map_div₀]
      simp
    have hstar3 : (starRingEnd ℂ) ((3 : ℂ) / s) = (3 : ℂ) / s := by
      rw [map_div₀, map_ofNat]
      simp
    rw [hstar1, hstar3]
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul]
    rw [show ((1 : ℂ) / s) * ((1 : ℂ) / s) = 1 / 12 from by
      rw [div_mul_div_comm, one_mul, ← pow_two, hsC2]]
    rw [show ((3 : ℂ) / s) * ((3 : ℂ) / s) = 9 / 12 from by
      rw [div_mul_div_comm, ← pow_two ((s : ℂ)), hsC2]
      norm_num]
    match_scalars
    all_goals ring

/-- `thm:kraus-block-nogo` (block identity): for orthogonal
projections `P` (Hermitian idempotents),
`P_t·(Σ K ρ Kᴴ)|_{ρ = P_s}·P_t = Σ (P_tKP_s)(P_tKP_s)ᴴ`. -/
theorem kraus_block_identity {d ι : Type*} [Fintype d]
    [Fintype ι]
    (K : ι → Matrix d d ℂ) (Ps Pt : Matrix d d ℂ)
    (hPsH : Psᴴ = Ps) (hPs2 : Ps * Ps = Ps) (hPtH : Ptᴴ = Pt) :
    Pt * (∑ α, K α * Ps * (K α)ᴴ) * Pt
      = ∑ α, (Pt * K α * Ps) * (Pt * K α * Ps)ᴴ := by
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro α _
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hPsH,
    hPtH]
  rw [show Pt * K α * Ps * (Ps * ((K α)ᴴ * Pt))
      = Pt * (K α * (Ps * Ps) * (K α)ᴴ) * Pt from by
    simp only [Matrix.mul_assoc]]
  rw [hPs2]

/-- `thm:kraus-block-nogo` (vanishing): if the summed block
`Σ (P_tKP_s)(P_tKP_s)ᴴ` is zero, then every cross block
`P_tK_αP_s` vanishes. -/
theorem kraus_block_nogo {d ι : Type*} [Fintype d] [Fintype ι]
    (M : ι → Matrix d d ℂ)
    (hzero : (∑ α, M α * (M α)ᴴ) = 0) :
    ∀ α, M α = 0 := by
  have htr : ∀ α, (M α * (M α)ᴴ).trace
      = ∑ i, ∑ j, (Complex.normSq (M α i j) : ℂ) := by
    intro α
    rw [Matrix.trace]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.diag_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.conjTranspose_apply]
    rw [show M α i j * star (M α i j)
      = (starRingEnd ℂ) (M α i j) * M α i j from by
        rw [mul_comm]
        rfl,
      ← Complex.normSq_eq_conj_mul_self]
  have hsum : (∑ α, ∑ i, ∑ j,
      (Complex.normSq (M α i j) : ℂ)) = 0 := by
    calc (∑ α, ∑ i, ∑ j, (Complex.normSq (M α i j) : ℂ))
        = ∑ α, (M α * (M α)ᴴ).trace := by
          exact Finset.sum_congr rfl fun α _ => (htr α).symm
    _ = ((∑ α, M α * (M α)ᴴ)).trace := by
          rw [Matrix.trace_sum]
    _ = 0 := by rw [hzero, Matrix.trace_zero]
  have hreal : (∑ α, ∑ i, ∑ j, Complex.normSq (M α i j)) = 0 := by
    exact_mod_cast hsum
  intro α
  ext i j
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun α _ => Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _)).mp
    hreal α (Finset.mem_univ α)
  have hij := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg fun j _ =>
      Complex.normSq_nonneg _)).mp hterm i (Finset.mem_univ i)
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => Complex.normSq_nonneg _)).mp hij j
    (Finset.mem_univ j)
  simpa using Complex.normSq_eq_zero.mp h0

end NCG
