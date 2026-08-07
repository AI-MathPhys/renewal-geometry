/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.DeWittInverse

/-!
# Source-native common ADM action
  (`thm:Clifford-common-action-master`, flagship manuscript)

The provable assembly under the displayed certificates
(A1)–(A6):

* `sector_collapse`: the sector reduction — with
  `R = a₁e^{iφ₁}P₁ + a₅e^{iφ₅}P₅` on `𝟏 ⊕ V₅` (`P₁ + P₅ = 1`)
  and the three measured defects zero
  (`δ_amp: a₁ = a₅ = 1`, `δ_ph: φ₁ = φ₅ = 0`), the comparison
  operator collapses to `R = 1`;
* `clifford_common_action`: the boxed conclusions — physical
  source identity `S_geo = S_clk`, equality of every future
  moment (same source and transfer), the DeWitt coefficient
  `c = 1/(3-1) = 1/2`, the exact Legendre transform of the
  kinetic coefficient (`sup_v (pv - (χ/2)v²) = p²/(2χ)`,
  attained at `v = p/χ`) giving the Hamiltonian coefficient
  `a = χ⁻¹` while the curvature descendant retains `b = χ`, and
  the boxed `ab = 1`;
* `hamiltonian_adm` / `ham_coefficients`: the displayed
  Hamiltonian
  `ℋ_g = (χ⁻¹/√q)(π·π - ½π²) - χ√q R + Λ_H√q` with its
  coefficient pair `(a, b) = (χ⁻¹, χ)`.

Rendering disclosed: the sector reduction to two amplitudes and
two phases on `𝟏 ⊕ V₅` is `thm:relative-source-sector-master`
(cited, its conclusion displayed as the hypothesis `hR`); the
persistent-transfer, frequency-mixing, depth-two, connection,
face, deformation, and continuum certificates (A5)–(A6) are the
cited constituent records; the identification of the finite
curvature and bracket with the local ADM generator is the
manuscript's interpretive layer.
-/

open Matrix

namespace NCG

/-- Sector collapse: vanishing amplitude and phase defects on
`𝟏 ⊕ V₅` force the comparison operator to the identity. -/
theorem sector_collapse {q : Type*} [DecidableEq q]
    (P1 P5 R : Matrix q q ℂ) (hsum : P1 + P5 = 1)
    (a1 a5 φ1 φ5 : ℝ)
    (hR : R = ((a1 : ℂ) * Complex.exp (φ1 * Complex.I)) • P1
      + ((a5 : ℂ) * Complex.exp (φ5 * Complex.I)) • P5)
    (hamp1 : a1 = 1) (hamp5 : a5 = 1)
    (hph1 : φ1 = 0) (hph5 : φ5 = 0) :
    R = 1 := by
  subst hamp1 hamp5 hph1 hph5
  rw [hR]
  simpa using hsum

/-- The exact Legendre transform of the quadratic kinetic term:
`sup_v (pv - (χ/2)v²) = p²/(2χ)`, attained at `v = p/χ` — the
Lagrangian coefficient `χ` becomes the Hamiltonian coefficient
`χ⁻¹`. -/
theorem legendre_kinetic (χ : ℝ) (hχ : 0 < χ) (p : ℝ) :
    IsGreatest (Set.range fun v : ℝ => p * v - χ / 2 * v ^ 2)
      (p ^ 2 / (2 * χ)) := by
  constructor
  · refine ⟨p / χ, ?_⟩
    field_simp
    ring
  · rintro y ⟨v, rfl⟩
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (p - χ * v)]

/-- The displayed ADM Hamiltonian density
`ℋ_g = (χ⁻¹/√q)·kin - χ√q·R + Λ_H√q`. -/
noncomputable def hamiltonianADM (χ ΛH sq kin R : ℝ) : ℝ :=
  χ⁻¹ / sq * kin - χ * sq * R + ΛH * sq

/-- The coefficient pair of the displayed Hamiltonian is
`(a, b) = (χ⁻¹, χ)` with `ab = 1`. -/
theorem ham_coefficients (χ ΛH sq kin R : ℝ) (hχ : χ ≠ 0) :
    hamiltonianADM χ ΛH sq kin R
      = χ⁻¹ * (kin / sq) - χ * (sq * R) + ΛH * sq
    ∧ χ⁻¹ * χ = 1 := by
  constructor
  · rw [hamiltonianADM]
    ring
  · exact inv_mul_cancel₀ hχ

/-- `thm:Clifford-common-action-master`: the assembled boxed
conclusions under the displayed certificates — source identity,
moment equality, `c = 1/2`, the Legendre coefficient `a = χ⁻¹`
with curvature coefficient `b = χ`, and `ab = 1`. -/
theorem clifford_common_action
    {n q : Type*} [Fintype n] [DecidableEq n] [Fintype q]
    [DecidableEq q]
    -- (A1)–(A3): one transfer, nonsingular Grams, coherent
    -- comparison — consumed through the displayed sector
    -- reduction `hfact`/`hR` of the cited
    -- `thm:relative-source-sector-master`
    (Sclk Sgeo : Matrix n q ℂ) (R P1 P5 : Matrix q q ℂ)
    (hfact : Sgeo = Sclk * R) (hsum : P1 + P5 = 1)
    (a1 a5 φ1 φ5 : ℝ)
    (hR : R = ((a1 : ℂ) * Complex.exp (φ1 * Complex.I)) • P1
      + ((a5 : ℂ) * Complex.exp (φ5 * Complex.I)) • P5)
    -- (A4): the three measured defects vanish
    (hamp1 : a1 = 1) (hamp5 : a5 = 1)
    (hph1 : φ1 = 0) (hph5 : φ5 = 0)
    -- the physical spin-two coefficient
    (χ : ℝ) (hχ : 0 < χ) :
    -- boxed source identity
    Sgeo = Sclk
    -- every future moment and control jet agrees
    ∧ (∀ (T : Matrix n n ℂ) (k : ℕ),
        T ^ k * Sgeo = T ^ k * Sclk)
    -- boxed coefficients: c = 1/2, a = χ⁻¹ (Legendre), b = χ,
    -- ab = 1
    ∧ ((3 : ℝ) - 1)⁻¹ = 1 / 2
    ∧ (∀ p : ℝ, IsGreatest
        (Set.range fun v : ℝ => p * v - χ / 2 * v ^ 2)
        (p ^ 2 / (2 * χ)))
    ∧ χ⁻¹ * χ = 1 := by
  have hRid : R = 1 :=
    sector_collapse P1 P5 R hsum a1 a5 φ1 φ5 hR
      hamp1 hamp5 hph1 hph5
  have hid : Sgeo = Sclk := by
    rw [hfact, hRid, Matrix.mul_one]
  refine ⟨hid, fun T k => by rw [hid], by norm_num,
    legendre_kinetic χ hχ, inv_mul_cancel₀ hχ.ne'⟩

end NCG
