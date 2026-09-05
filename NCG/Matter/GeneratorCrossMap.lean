/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Matter.SMEasyV5

/-!
# Cross-support generator map (`thm:generator-cross-map`, SM manuscript)

For a finite GKSL generator

  `𝓛(ρ) = -i[H,ρ] + Σ_α (V_αρV_α† - ½{V_α†V_α, ρ})`

and distinct central supports `P_s ⊥ P_t`, the cross-support map
`𝓡_{t←s}(X) = P_t 𝓛(P_sXP_s) P_t` is the manifestly completely
positive Kraus form

  `𝓡_{t←s}(X) = Σ_α B_α X B_α†`, `B_α = P_t V_α P_s`

(`generator_cross_map`): compressing the Hamiltonian and
anticommutator terms between orthogonal supports annihilates them,
and only the jump term survives.  The effect is
`A_{t←s} = P_t 𝓛(P_s) P_t = Σ_α B_α B_α†`, and it vanishes iff
every microscopic jump has zero `s→t` block (via
`kraus_block_nogo`).  Representation independence: the left side is
defined directly from `𝓛`, so two GKSL frames presenting the same
generator have identical cross maps (`cross_map_frame_independent`).
-/

open Matrix

namespace NCG

variable {n ι : Type*} [Fintype n] [Fintype ι]

/-- The finite GKSL generator in a chosen frame. -/
noncomputable def gksl (H : Matrix n n ℂ) (V : ι → Matrix n n ℂ)
    (ρ : Matrix n n ℂ) : Matrix n n ℂ :=
  (-Complex.I) • (H * ρ - ρ * H)
    + ∑ α, (V α * ρ * (V α)ᴴ
      - (1 / 2 : ℂ) • ((V α)ᴴ * V α * ρ + ρ * ((V α)ᴴ * V α)))

section

variable (Ps Pt : Matrix n n ℂ)

/-- Terms ending in `P_s` die under the `P_t` compression. -/
lemma end_kill (hst : Ps * Pt = 0) (M : Matrix n n ℂ) :
    Pt * (M * Ps) * Pt = 0 := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, hst, Matrix.mul_zero,
    Matrix.mul_zero]

/-- Terms starting with `P_s` die under the `P_t` compression. -/
lemma start_kill (hts : Pt * Ps = 0) (M : Matrix n n ℂ) :
    Pt * (Ps * M) * Pt = 0 := by
  rw [← Matrix.mul_assoc, hts, Matrix.zero_mul, Matrix.zero_mul]

/-- Only the jump term survives the cross compression. -/
lemma jump_survives (hPsH : Psᴴ = Ps) (hPtH : Ptᴴ = Pt)
    (Vα X : Matrix n n ℂ) :
    Pt * (Vα * (Ps * X * Ps) * Vαᴴ) * Pt
      = (Pt * Vα * Ps) * X * (Pt * Vα * Ps)ᴴ := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hPsH, hPtH]
  simp only [Matrix.mul_assoc]

/-- `thm:generator-cross-map`: the cross-support map is the Kraus
form over the cross blocks `B_α = P_tV_αP_s`; its effect is
`Σ_α B_αB_α†` and vanishes iff every jump has zero `s→t` block. -/
theorem generator_cross_map (H : Matrix n n ℂ)
    (V : ι → Matrix n n ℂ)
    (hPsH : Psᴴ = Ps) (hPtH : Ptᴴ = Pt) (hPs2 : Ps * Ps = Ps)
    (hts : Pt * Ps = 0) (hst : Ps * Pt = 0) :
    (∀ X, Pt * gksl H V (Ps * X * Ps) * Pt
      = ∑ α, (Pt * V α * Ps) * X * (Pt * V α * Ps)ᴴ)
    ∧ (Pt * gksl H V Ps * Pt
      = ∑ α, (Pt * V α * Ps) * (Pt * V α * Ps)ᴴ)
    ∧ (Pt * gksl H V Ps * Pt = 0 ↔ ∀ α, Pt * V α * Ps = 0) := by
  have hcross : ∀ X, Pt * gksl H V (Ps * X * Ps) * Pt
      = ∑ α, (Pt * V α * Ps) * X * (Pt * V α * Ps)ᴴ := by
    intro X
    rw [gksl, Matrix.mul_add, Matrix.add_mul]
    have hham : Pt * ((-Complex.I) • (H * (Ps * X * Ps)
        - (Ps * X * Ps) * H)) * Pt = 0 := by
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub,
        Matrix.sub_mul]
      rw [show H * (Ps * X * Ps) = (H * (Ps * X)) * Ps by
          simp only [Matrix.mul_assoc],
        show Ps * X * Ps * H = Ps * (X * (Ps * H)) by
          simp only [Matrix.mul_assoc],
        end_kill Ps Pt hst, start_kill Ps Pt hts, sub_self,
        smul_zero]
    have hdiss : Pt * (∑ α, (V α * (Ps * X * Ps) * (V α)ᴴ
        - (1 / 2 : ℂ) • ((V α)ᴴ * V α * (Ps * X * Ps)
          + (Ps * X * Ps) * ((V α)ᴴ * V α)))) * Pt
        = ∑ α, (Pt * V α * Ps) * X * (Pt * V α * Ps)ᴴ := by
      rw [Matrix.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Matrix.mul_sub, Matrix.sub_mul]
      have hanti : Pt * ((1 / 2 : ℂ) • ((V α)ᴴ * V α * (Ps * X * Ps)
          + (Ps * X * Ps) * ((V α)ᴴ * V α))) * Pt = 0 := by
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
          Matrix.add_mul]
        rw [show (V α)ᴴ * V α * (Ps * X * Ps)
            = ((V α)ᴴ * V α * (Ps * X)) * Ps by
              simp only [Matrix.mul_assoc],
          show Ps * X * Ps * ((V α)ᴴ * V α)
            = Ps * (X * (Ps * ((V α)ᴴ * V α))) by
              simp only [Matrix.mul_assoc],
          end_kill Ps Pt hst, start_kill Ps Pt hts, add_zero,
          smul_zero]
      rw [hanti, sub_zero, jump_survives Ps Pt hPsH hPtH]
    rw [hham, hdiss, zero_add]
  have heff : Pt * gksl H V Ps * Pt
      = ∑ α, (Pt * V α * Ps) * (Pt * V α * Ps)ᴴ := by
    have h3 : Ps * Ps * Ps = Ps := by rw [hPs2, hPs2]
    calc Pt * gksl H V Ps * Pt
        = Pt * gksl H V (Ps * Ps * Ps) * Pt := by rw [h3]
      _ = ∑ α, (Pt * V α * Ps) * Ps * (Pt * V α * Ps)ᴴ :=
          hcross Ps
      _ = ∑ α, (Pt * V α * Ps) * (Pt * V α * Ps)ᴴ := by
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [Matrix.mul_assoc, ← Matrix.mul_assoc,
            Matrix.mul_assoc (Pt * V α) Ps Ps, hPs2]
  refine ⟨hcross, heff, ?_⟩
  rw [heff]
  constructor
  · intro h
    exact kraus_block_nogo (fun α => Pt * V α * Ps) h
  · intro h
    rw [Finset.sum_congr rfl fun α _ => by
      rw [h α, Matrix.zero_mul]]
    exact Finset.sum_const_zero

/-- Representation independence: two GKSL frames presenting the
same generator have the same cross-support Kraus form. -/
theorem cross_map_frame_independent (H H' : Matrix n n ℂ)
    {ι' : Type*} [Fintype ι'] (V : ι → Matrix n n ℂ)
    (V' : ι' → Matrix n n ℂ)
    (hPsH : Psᴴ = Ps) (hPtH : Ptᴴ = Pt) (hPs2 : Ps * Ps = Ps)
    (hts : Pt * Ps = 0) (hst : Ps * Pt = 0)
    (heq : ∀ ρ, gksl H V ρ = gksl H' V' ρ) :
    ∀ X, ∑ α, (Pt * V α * Ps) * X * (Pt * V α * Ps)ᴴ
      = ∑ α, (Pt * V' α * Ps) * X * (Pt * V' α * Ps)ᴴ := by
  intro X
  rw [← (generator_cross_map Ps Pt H V hPsH hPtH hPs2 hts hst).1 X,
    heq,
    (generator_cross_map Ps Pt H' V' hPsH hPtH hPs2 hts hst).1 X]

/-- `corollary:failure-of-accessibility-for-the-displayed-source`:
a source whose jumps preserve the central supports (all cross
blocks vanish, the displayed block-preserving property) has zero
accessibility effect between any two distinct supports — in
particular `A_{L←R} = A_{R←L} = 0`, so the sector-resolving
accessibility premise fails. -/
theorem displayed_source_no_accessibility (H : Matrix n n ℂ)
    (V : ι → Matrix n n ℂ)
    (hPsH : Psᴴ = Ps) (hPtH : Ptᴴ = Pt) (hPs2 : Ps * Ps = Ps)
    (hts : Pt * Ps = 0) (hst : Ps * Pt = 0)
    (hblock : ∀ α, Pt * V α * Ps = 0) :
    Pt * gksl H V Ps * Pt = 0 :=
  (generator_cross_map Ps Pt H V hPsH hPtH hPs2 hts hst).2.2.mpr
    hblock

end

end NCG
