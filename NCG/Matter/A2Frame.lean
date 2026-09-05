/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Matter.K4Carrier

/-!
# The incident-port A₂ frame and the sequential generation flag
(SM_emergence, S₄ layer)

The harmonic representatives of the three ports incident to the
marked vertex `0`, and the records riding on them:

* `q01`, `q02`, `q03`, `hcyc` — the harmonic projections of the
  incident edges and the opposite-cycle line, as explicit carrier
  elements (via `k4Fill`);
* `a2_frame_sum`, `a2_frame_norm`, `a2_frame_inner` —
  `lem:incident-a2-frame`: `q₀₁ + q₀₂ + q₀₃ = 0`, `‖q₀ⱼ‖² = 1/2`,
  `⟨q₀ⱼ, q₀ₖ⟩ = -1/4`;
* `a2_frame_tight` — the resolution `Σ qq* = (3/4)P_std` on the
  frame plane;
* `hcyc_orthogonal`, `flag_heavy_line`, `flag_block_action` —
  `thm:sequential-generation-flag`: the opposite cycle `h` spans the
  heavy line (orthogonal to all ports), and the port operator acts
  on the standard plane by the explicit `2×2` block
  `[[b/2, -b/4], [-c/4, c/2]]`;
* `sequential_eigenvalues` — `corollary:exact-sequential-eigenvalues`:
  the standard-plane eigenvalues are
  `λ± = (b + c ± √(b² - bc + c²))/4`;
* `swap12_hcyc`, `swap23_hcyc`, `swap12_q01`, `swap23_q02`,
  `swap12_q03` — `thm:flavour-stabilizer-split`: under the
  stabilizer `S₃` of the marked vertex, the heavy line carries the
  sign representation (both generating transpositions negate `h`)
  and the ports are permuted (the standard doublet);
* `threshold_restoration` — `thm:threshold-restoration-main`: if the
  renewal edge is chirally symmetric (`Sγ = γS`, `γ² = 1`), the
  chiral block vanishes, `P_L S P_R = 0`.
-/

namespace NCG

open Matrix

/-! ## The harmonic incident ports -/

/-- Harmonic representative of the incident edge `{0,1}`. -/
noncomputable def q01 : Fin 4 → Fin 4 → ℂ := k4Fill ![1/2, -(1/4), 1/4]

/-- Harmonic representative of the incident edge `{0,2}`. -/
noncomputable def q02 : Fin 4 → Fin 4 → ℂ := k4Fill ![-(1/4), 1/2, -(1/4)]

/-- Harmonic representative of the incident edge `{0,3}`. -/
noncomputable def q03 : Fin 4 → Fin 4 → ℂ := k4Fill ![-(1/4), -(1/4), 0]

/-- The opposite-cycle line `h`: the `1 → 2 → 3 → 1` circulation
avoiding the marked vertex. -/
noncomputable def hcyc : Fin 4 → Fin 4 → ℂ := k4Fill ![0, 0, 1]

theorem q01_mem : q01 ∈ K4Carrier := k4Fill_mem _
theorem q02_mem : q02 ∈ K4Carrier := k4Fill_mem _
theorem q03_mem : q03 ∈ K4Carrier := k4Fill_mem _
theorem hcyc_mem : hcyc ∈ K4Carrier := k4Fill_mem _

/-- The unordered-edge pairing `⟨α, β⟩ = Σ_{i<j} α(ij)β(ij)`. -/
noncomputable def edgeInner (a b : Fin 4 → Fin 4 → ℂ) : ℂ :=
  a 0 1 * b 0 1 + a 0 2 * b 0 2 + a 0 3 * b 0 3
    + a 1 2 * b 1 2 + a 1 3 * b 1 3 + a 2 3 * b 2 3

/-! ## `lem:incident-a2-frame` -/

/-- `lem:incident-a2-frame` (sum): `q₀₁ + q₀₂ + q₀₃ = 0`. -/
theorem a2_frame_sum : q01 + q02 + q03 = 0 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [q01, q02, q03, k4Fill] <;> ring

/-- `lem:incident-a2-frame` (norms): `‖q₀ⱼ‖² = 1/2`. -/
theorem a2_frame_norm :
    edgeInner q01 q01 = 1/2 ∧ edgeInner q02 q02 = 1/2 ∧
    edgeInner q03 q03 = 1/2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (simp [edgeInner, q01, q02, q03, k4Fill]; norm_num)

/-- `lem:incident-a2-frame` (angles): `⟨q₀ⱼ, q₀ₖ⟩ = -1/4` for
`j ≠ k` — the `A₂` root-system geometry of the incident ports. -/
theorem a2_frame_inner :
    edgeInner q01 q02 = -(1/4) ∧ edgeInner q01 q03 = -(1/4) ∧
    edgeInner q02 q03 = -(1/4) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (simp [edgeInner, q01, q02, q03, k4Fill]; norm_num)

/-- `lem:incident-a2-frame` (tight-frame resolution,
`Σ qq* = (3/4)P_std`): with the Gram values of `a2_frame_norm` and
`a2_frame_inner`, the port resolution `Σ_j ⟨q₀ⱼ, ·⟩ q₀ⱼ` acts by
`3/4` on the spanning ports. -/
theorem a2_frame_tight :
    ((1/2 : ℂ) • q01 + (-(1/4) : ℂ) • q02 + (-(1/4) : ℂ) • q03
      = (3/4 : ℂ) • q01) ∧
    ((-(1/4) : ℂ) • q01 + (1/2 : ℂ) • q02 + (-(1/4) : ℂ) • q03
      = (3/4 : ℂ) • q02) := by
  constructor <;>
    · funext i j
      fin_cases i <;> fin_cases j <;>
        simp [q01, q02, q03, k4Fill] <;> ring_nf

/-! ## `thm:sequential-generation-flag` -/

/-- The heavy line is orthogonal to every port: `⟨q₀ⱼ, h⟩ = 0`. -/
theorem hcyc_orthogonal :
    edgeInner q01 hcyc = 0 ∧ edgeInner q02 hcyc = 0 ∧
    edgeInner q03 hcyc = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [edgeInner, q01, q02, q03, hcyc, k4Fill] <;> norm_num

/-- `thm:sequential-generation-flag` (heavy line): the flag operator
`Y(a,b,c) = a·P_h + b·q₀₁q₀₁* + c·q₀₂q₀₂*` acts on the opposite
cycle by the heavy eigenvalue `a` (with `‖h‖² = 3`). -/
theorem flag_heavy_line (a b c : ℂ) :
    (a * (edgeInner hcyc hcyc / 3)) • hcyc
      + (b * edgeInner q01 hcyc) • q01
      + (c * edgeInner q02 hcyc) • q02 = a • hcyc := by
  have h3 : edgeInner hcyc hcyc = 3 := by
    simp [edgeInner, hcyc, k4Fill]
    norm_num
  rw [h3, hcyc_orthogonal.1, hcyc_orthogonal.2.1]
  norm_num

/-- `thm:sequential-generation-flag` (standard-plane block): the
port operator acts on the flag plane by the exact `2×2` block
`[[b/2, -b/4], [-c/4, c/2]]` in the `(q₀₁, q₀₂)` frame. -/
theorem flag_block_action (b c : ℂ) :
    ((b * edgeInner q01 q01) • q01 + (c * edgeInner q02 q01) • q02
      = (b/2) • q01 + (-(c/4)) • q02) ∧
    ((b * edgeInner q01 q02) • q01 + (c * edgeInner q02 q02) • q02
      = (-(b/4)) • q01 + (c/2) • q02) := by
  have h21 : edgeInner q02 q01 = -(1/4) := by
    simp [edgeInner, q01, q02, k4Fill]
    norm_num
  constructor
  · rw [a2_frame_norm.1, h21]
    funext i j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · rw [a2_frame_inner.1, a2_frame_norm.2.1]
    funext i j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- `corollary:exact-sequential-eigenvalues`: the standard-plane
eigenvalues of the flag block are exactly
`λ± = (b + c ± √(b² - bc + c²))/4` — the roots of
`λ² - ((b+c)/2)λ + 3bc/16`. -/
theorem sequential_eigenvalues (b c : ℝ) :
    ((b + c + Real.sqrt (b^2 - b*c + c^2))/4)^2
      - (b + c)/2 * ((b + c + Real.sqrt (b^2 - b*c + c^2))/4)
      + 3*b*c/16 = 0 ∧
    ((b + c - Real.sqrt (b^2 - b*c + c^2))/4)^2
      - (b + c)/2 * ((b + c - Real.sqrt (b^2 - b*c + c^2))/4)
      + 3*b*c/16 = 0 := by
  have hnn : (0:ℝ) ≤ b^2 - b*c + c^2 := by
    nlinarith [sq_nonneg (b - c), sq_nonneg b, sq_nonneg c]
  have hsq := Real.sq_sqrt hnn
  constructor <;> nlinarith [hsq]

/-! ## `thm:flavour-stabilizer-split` -/

/-- Relabeling action of a vertex permutation on edge functions. -/
def permAct (sigma : Equiv.Perm (Fin 4))
    (a : Fin 4 → Fin 4 → ℂ) : Fin 4 → Fin 4 → ℂ :=
  fun i j => a (sigma⁻¹ i) (sigma⁻¹ j)

/-- The transposition `(1 2)` negates the opposite cycle. -/
theorem swap12_hcyc : permAct (Equiv.swap 1 2) hcyc = -hcyc := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [permAct, hcyc, k4Fill, Equiv.swap_apply_def]

/-- The transposition `(2 3)` negates the opposite cycle — together
with `swap12_hcyc`, both generators of the vertex stabilizer `S₃`
act on `ℂh` by the sign character. -/
theorem swap23_hcyc : permAct (Equiv.swap 2 3) hcyc = -hcyc := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [permAct, hcyc, k4Fill, Equiv.swap_apply_def]

/-- `(1 2)` exchanges the first two ports. -/
theorem swap12_q01 : permAct (Equiv.swap 1 2) q01 = q02 := by
  have e0 : (Equiv.swap (1:Fin 4) 2) 0 = 0 := by decide
  have e1 : (Equiv.swap (1:Fin 4) 2) 1 = 2 := by decide
  have e2 : (Equiv.swap (1:Fin 4) 2) 2 = 1 := by decide
  have e3 : (Equiv.swap (1:Fin 4) 2) 3 = 3 := by decide
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [permAct, q01, q02, k4Fill, e0, e1, e2, e3] <;> norm_num

/-- `(2 3)` exchanges the last two ports. -/
theorem swap23_q02 : permAct (Equiv.swap 2 3) q02 = q03 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [permAct, q02, q03, k4Fill, Equiv.swap_apply_def] <;>
    norm_num

/-- `(1 2)` fixes the opposite port — the ports carry the natural
permutation action of `S₃`, whose sum-zero part is the standard
doublet (`thm:flavour-stabilizer-split`,
`H¹(K₄;ℂ)|_{S₃} ≅ sgn ⊕ Std`). -/
theorem swap12_q03 : permAct (Equiv.swap 1 2) q03 = q03 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [permAct, q03, k4Fill, Equiv.swap_apply_def]

/-! ## `thm:threshold-restoration-main` -/

/-- `thm:threshold-restoration-main`: if the renewal edge is chirally
symmetric — the full operator commutes with the grading `γ`,
`γ² = 1` — then the chiral block vanishes:
`P_L S P_R = ((1+γ)/2)·S·((1-γ)/2) = 0`.  A nonzero off-diagonal
threshold self-energy therefore cannot simultaneously be a purely
emergent mass dressing and vanish at chiral restoration. -/
theorem threshold_restoration {A : Type*} [Ring A] [Algebra ℚ A]
    (S gamma : A) (hg : gamma * gamma = 1)
    (hcomm : S * gamma = gamma * S) :
    ((2:ℚ)⁻¹ • (1 + gamma)) * S * ((2:ℚ)⁻¹ • (1 - gamma)) = 0 := by
  have hkey : (1 + gamma) * S * (1 - gamma) = 0 := by
    have h1 : (1 + gamma) * S * (1 - gamma)
        = S + gamma * S - S * gamma - gamma * (S * gamma) := by
      noncomm_ring
    rw [h1, hcomm]
    rw [show gamma * (gamma * S) = (gamma * gamma) * S by noncomm_ring]
    rw [hg, one_mul]
    abel
  rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc, smul_smul,
    hkey, smul_zero]

end NCG
