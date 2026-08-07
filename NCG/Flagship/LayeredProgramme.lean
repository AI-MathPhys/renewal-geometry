/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.ClockDischarge
import NCG.Flagship.NativeDeterminant
import NCG.Flagship.SingleWriterClifford
import NCG.Flagship.PhysicalConnection
import NCG.Flagship.DeformationAnomaly
import NCG.Flagship.MovingFrameMatter
import NCG.Flagship.EinsteinHandoff
import NCG.Flagship.OrientationPhase
import NCG.Flagship.Metrology
import NCG.Flagship.CharacterLeakage
import NCG.Flagship.CommonAction

/-!
# Strengthened layered renewal programme master theorem
  (`thm:layered-programme-master`, flagship manuscript)

The ten-item bundle, each item instantiated by the formal core of
its cited proved constituent records (the manuscript's proof is
exactly this citation list):

* (I)   the reduced Store–control entrance: integer record-group
        closure and the Lorentzian principal symbol
        (`reduced_hypothesis_spacetime`);
* (II)  the marked external `M₄(ℂ) ≅ Cl₁,₃(ℂ)` factor: the four
        anchor generators generate the full matrix algebra
        (`clifford_algebra_top`);
* (III) the metric instrument: the icosahedral invariant-
        multiplicity sum equals one
        (`determinant_multiplicity_one`) and the single-writer
        determinant loading `χ_W = det L`, `χ_W² = det G_W`
        (`single_writer_chi`);
* (IV)  the clock–geometry audit identity
        `D - B*A⁻¹B = S_geo*(I-P)S_geo` (`adm_gram_identity`);
* (V)   the fourfold connection alternative
        (`connection_branch_classification`) and the exact
        five-anomaly telescope (`five_term_telescope`);
* (VI)  the antisymmetric matter bracket
        (`matter_bracket_antisymmetric`) and unit relative
        amplitude (`species_amplitude_one`);
* (VII) the covariant coefficient handoff
        `2χ(G + Λ_cov g) = 2χG + Λ_H g`
        (`lambda_cov_coefficient`);
* (VIII) the sharp Dobrushin phase bound
        (`dobrushin_site_bound`);
* (IX)  independent metrology: `G_eff = ℓ*²/(16πχ)` inversion
        (`newton_from_stiffness`) and vacuum-loading blindness of
        normalized probabilities
        (`normalized_probability_gauge`);
* (X)   cutoff-stable Grand-Tensor structure: Gram-rank
        saturation (`saturation_rank`) and the exact leakage
        rank/vanishing alternative
        (`leakage_rank_and_vanishing`).

Rendering disclosed: each item's full prose content is the
conjunction of its cited constituent records in the ledger; the
clause displayed here is the representative formal core through
which those records enter, instantiated on the concrete index
types of the construction.  The entrance hypotheses of
`ass:predictive-clock-entry` are consumed inside the cited
records themselves.
-/

open Matrix

namespace NCG

/-- `thm:layered-programme-master`: the ten-item master bundle,
each clause the formal core of its cited proved constituents. -/
theorem layered_programme_master :
    -- (I) reduced Store–control entrance
    ((AddSubgroup.closure
        (Set.range fun i : Fin 3 => Pi.single i (1 : ℤ)) = ⊤)
      ∧ ∀ ξ0 ξ1 ξ2 ξ3 : ℂ,
        (ξ0 • gamma0 + ξ1 • gamma1 + ξ2 • gamma2 + ξ3 • gamma3)
          * (ξ0 • gamma0 + ξ1 • gamma1 + ξ2 • gamma2
            + ξ3 • gamma3)
        = (-ξ0 ^ 2 + ξ1 ^ 2 + ξ2 ^ 2 + ξ3 ^ 2)
            • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
    -- (II) the marked external M₄(ℂ) factor
    ∧ Algebra.adjoin ℂ ({gamma0, gamma1, gamma2, gamma3} :
        Set (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) = ⊤
    -- (III) metric instrument: invariant multiplicity one and
    -- the determinant loading
    ∧ ((27 - 15 + 12 * (((1 + Real.sqrt 5) / 2) ^ 3
          + (1 - (1 + Real.sqrt 5) / 2) ^ 3)) / 60 = 1
      ∧ ∀ L : Matrix (Fin 3) (Fin 3) ℝ,
        L.det ^ 2 = (Lᵀ * L).det)
    -- (IV) the clock–geometry ADM audit identity
    ∧ (∀ (Wy : Matrix (Fin 3) (Fin 3) ℂ)
        (ΦWx : Matrix (Fin 3) (Fin 3) ℂ),
        ΦWxᴴ * ΦWx
            - (Wyᴴ * ΦWx)ᴴ * (Wyᴴ * Wy)⁻¹ * (Wyᴴ * ΦWx)
          = ΦWxᴴ * (1 - Wy * (Wyᴴ * Wy)⁻¹ * Wyᴴ) * ΦWx)
    -- (V) the fourfold connection alternative and the anomaly
    -- telescope
    ∧ ((∀ closure metricity torsionfree faces : Prop,
        (closure ∧ metricity ∧ torsionfree ∧ faces)
        ∨ (closure ∧ metricity ∧ ¬torsionfree ∧ faces)
        ∨ (closure ∧ ¬metricity)
        ∨ (¬closure ∨ (closure ∧ metricity ∧ ¬faces)))
      ∧ ∀ X0 X1 X2 X3 X4 X5 : ℝ,
        X0 - X5 = (X0 - X1) + (X1 - X2) + (X2 - X3)
          + (X3 - X4) + (X4 - X5))
    -- (VI) exact matter bracket and unit relative amplitude
    ∧ ((∀ (edges : Finset ℕ) (Nx Ny Mx My d : ℕ → ℝ),
        ∑ e ∈ edges, (Nx e * My e - Mx e * Ny e) * d e
          = -∑ e ∈ edges, (Mx e * Ny e - Nx e * My e) * d e)
      ∧ ∀ lam : ℝ, 0 < lam → lam ^ 2 = 1 → lam = 1)
    -- (VII) the covariant coefficient handoff
    ∧ (∀ χ ΛH : ℝ, χ ≠ 0
        → ∀ G g : Matrix (Fin 4) (Fin 4) ℝ,
        (2 * χ) • (G + (ΛH / (2 * χ)) • g)
          = (2 * χ) • G + ΛH • g)
    -- (VIII) the sharp Dobrushin phase bound
    ∧ (∀ h K : ℝ, 0 ≤ K
        → (Real.tanh (h + K) - Real.tanh (h - K)) / 2
          ≤ Real.tanh K)
    -- (IX) independent metrology and vacuum-loading blindness
    ∧ ((∀ χ ℓ G : ℝ, 0 < χ → 0 < G
        → χ = ℓ ^ 2 / (16 * Real.pi * G)
        → G = ℓ ^ 2 / (16 * Real.pi * χ))
      ∧ ∀ (a : Fin 6 → ℂ) (c : ℝ) (i : Fin 6),
        (∑ j, ‖a j‖ ^ 2 ≠ 0)
        → ‖(Real.exp (-c) : ℂ) * a i‖ ^ 2
              / ∑ j, ‖(Real.exp (-c) : ℂ) * a j‖ ^ 2
            = ‖a i‖ ^ 2 / ∑ j, ‖a j‖ ^ 2)
    -- (X) cutoff-stable Grand-Tensor saturation and exact
    -- leakage alternative
    ∧ ((∀ C : Matrix (Fin 3) (Fin 3) ℂ,
        (Cᴴ * C).rank = C.rank)
      ∧ ∀ (V : Matrix (Fin 3) (Fin 3) ℂ)
          (T : Matrix (Fin 3) (Fin 3) ℂ),
        Vᴴ * V = 1 → Tᴴ = T
        → (Vᴴ * (T * T) * V
              - (Vᴴ * T * V) * (Vᴴ * T * V) = 0
            ↔ (1 - V * Vᴴ) * T * V = 0)) := by
  refine ⟨reduced_hypothesis_spacetime, clifford_algebra_top,
    ⟨determinant_multiplicity_one,
      fun L => (single_writer_chi L).2⟩,
    fun Wy ΦWx => adm_gram_identity Wy ΦWx,
    ⟨fun c m t f => connection_branch_classification c m t f,
      fun X0 X1 X2 X3 X4 X5 =>
        five_term_telescope X0 X1 X2 X3 X4 X5⟩,
    ⟨fun edges Nx Ny Mx My d =>
        matter_bracket_antisymmetric edges Nx Ny Mx My d,
      fun lam hpos hsq => species_amplitude_one lam hpos hsq⟩,
    fun χ ΛH hχ G g => lambda_cov_coefficient χ ΛH hχ G g,
    fun h K hK => dobrushin_site_bound h K hK,
    ⟨fun χ ℓ G hχ hG h => newton_from_stiffness χ ℓ G hχ hG h,
      fun a c i hsum =>
        normalized_probability_gauge a c i hsum⟩,
    ⟨fun C => saturation_rank C,
      fun V T hV hT =>
        (leakage_rank_and_vanishing V T hV hT).2⟩⟩

end NCG
