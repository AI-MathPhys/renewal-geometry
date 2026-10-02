/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.GowdyHermiteReadoutCurvature

/-!
# Algebraic vacuum identity for the Gowdy metric
  (vacuum clause of `thm:supp-gowdy-full-curvature`; emergent-spacetime supplement)

* `J2`: second-order jets `(f, f_t, f_θ, f_tt, f_tθ, f_θθ)` with the Leibniz rule (`J2.mul`), the
  chain rule for `exp` (`J2.exp`), sums and scalar multiples.
* `gowdyEntryJets`: the jets of the entries of the Gowdy metric `eq:supp-gowdy-metric` computed
  from the jets of `t, log t, P, Q, λ` (the `(t, θ)`-block is `∓ exp(λ/2 - (log t)/2)`).
* `jetOfEntries`, `gowdyAlgJet`: the coordinate metric 2-jet `(g⁻¹, ∂g, ∂²g)` (fields independent
  of `x, y`).
* `ricci_gowdy_alg_bd` (one lemma per component) and `ricci_gowdy_algebraic`: **the Ricci tensor
  `CoordinateCurvatureJet.ricciJet` of this jet vanishes identically** once
  `P_tt = P_θθ - P_t/t + e^{2P}(Q_t² - Q_θ²)`, `Q_tt = Q_θθ - Q_t/t - 2P_tQ_t + 2P_θQ_θ`,
  `λ_t = t(P_t² + P_θ² + e^{2P}(Q_t² + Q_θ²))`, `λ_θ = 2t(P_tP_θ + e^{2P}Q_tQ_θ)` and the
  derivatives of the last two hold (the second-order form of the frame system
  `eq:supp-gowdy-frame-system` with the constraints `eq:supp-gowdy-coordinate-constraints`).
  No residual: every component reduces to zero.
-/

open Set Filter Topology
open scoped BigOperators ContDiff

set_option linter.unusedSectionVars false

namespace RenewalGeometry.GowdyStaggered.HermiteReadout

open CubicHermiteRemainder CoordinateCurvatureJet

noncomputable section

/-! ### Two-jets in `(t, θ)` and their arithmetic -/

/-- A second-order jet `(f, ∂_t f, ∂_θ f, ∂_t² f, ∂_t∂_θ f, ∂_θ² f)` at a point of `ℝ²`. -/
structure J2 where
  v : ℝ
  t : ℝ
  θ : ℝ
  tt : ℝ
  tθ : ℝ
  θθ : ℝ

namespace J2

/-- Sum of jets. -/
def add (j k : J2) : J2 := ⟨j.v + k.v, j.t + k.t, j.θ + k.θ, j.tt + k.tt, j.tθ + k.tθ, j.θθ + k.θθ⟩

/-- Scalar multiple of a jet. -/
def cmul (c : ℝ) (j : J2) : J2 := ⟨c * j.v, c * j.t, c * j.θ, c * j.tt, c * j.tθ, c * j.θθ⟩

/-- Leibniz rule. -/
def mul (j k : J2) : J2 :=
  ⟨j.v * k.v, j.t * k.v + j.v * k.t, j.θ * k.v + j.v * k.θ,
    j.tt * k.v + 2 * (j.t * k.t) + j.v * k.tt, j.tθ * k.v + j.t * k.θ + j.θ * k.t + j.v * k.tθ,
    j.θθ * k.v + 2 * (j.θ * k.θ) + j.v * k.θθ⟩

/-- Chain rule for `exp`. -/
def exp (j : J2) : J2 :=
  ⟨Real.exp j.v, Real.exp j.v * j.t, Real.exp j.v * j.θ, Real.exp j.v * (j.t ^ 2 + j.tt),
    Real.exp j.v * (j.t * j.θ + j.tθ), Real.exp j.v * (j.θ ^ 2 + j.θθ)⟩

/-- The zero jet. -/
def zero : J2 := ⟨0, 0, 0, 0, 0, 0⟩

end J2

/-- Jet of the clock `t`. -/
def jClock (t : ℝ) : J2 := ⟨t, 1, 0, 0, 0, 0⟩

/-- Jet of `log t`. -/
def jLogClock (t : ℝ) : J2 := ⟨Real.log t, 1 / t, 0, -(1 / t ^ 2), 0, 0⟩

/-- Jets of the Gowdy metric entries from the jets of `t, log t, P, Q, λ`. -/
def gowdyEntryJets (jT jl jP jQ jL : J2) : Fin 4 → Fin 4 → J2 :=
  let jA := J2.exp (J2.add (J2.cmul (1 / 2) jL) (J2.cmul (-(1 / 2)) jl))
  let jE := J2.exp jP
  let jEi := J2.exp (J2.cmul (-1) jP)
  ![![J2.cmul (-1) jA, J2.zero, J2.zero, J2.zero],
    ![J2.zero, jA, J2.zero, J2.zero],
    ![J2.zero, J2.zero, J2.mul jT jE, J2.mul (J2.mul jT jE) jQ],
    ![J2.zero, J2.zero, J2.mul (J2.mul jT jE) jQ,
      J2.add (J2.mul (J2.mul jT jE) (J2.mul jQ jQ)) (J2.mul jT jEi)]]

/-- The metric 2-jet assembled from an inverse metric and entry jets. -/
def jetOfEntries (ginv : Fin 4 → Fin 4 → ℝ) (E : Fin 4 → Fin 4 → J2) : Jet :=
  (ginv, fun i e j => ![(E e j).t, (E e j).θ, 0, 0] i,
    fun d i e j => ![![(E e j).tt, (E e j).tθ, 0, 0], ![(E e j).tθ, (E e j).θθ, 0, 0],
      ![0, 0, 0, 0], ![0, 0, 0, 0]] d i)


/-- The Gowdy metric 2-jet at a point with clock `t` and field jets `jP, jQ, jL`. -/
def gowdyAlgJet (t P Q L : ℝ) (jP jQ jL : J2) : Jet :=
  jetOfEntries (gowdyInvMetric ![t, P, Q, L])
    (gowdyEntryJets (jClock t) (jLogClock t) jP jQ jL)

/-- Component `(0,0)` of the algebraic vacuum identity. -/
theorem ricci_gowdy_alg_00 {t P Q L Pt Pθ Ptθ Pθθ Qt Qθ Qtθ Qθθ Ptt Qtt Lt Lθ Ltt Ltθ Lθθ : ℝ}
    (ht : 0 < t)
    (hPtt : Ptt = Pθθ - Pt / t + Real.exp P ^ 2 * (Qt ^ 2 - Qθ ^ 2))
    (hQtt : Qtt = Qθθ - Qt / t - 2 * Pt * Qt + 2 * Pθ * Qθ)
    (hLt : Lt = t * (Pt ^ 2 + Pθ ^ 2 + Real.exp P ^ 2 * (Qt ^ 2 + Qθ ^ 2)))
    (hLθ : Lθ = 2 * t * (Pt * Pθ + Real.exp P ^ 2 * Qt * Qθ))
    (hLtt : Ltt = (Pt ^ 2 + Pθ ^ 2 + Real.exp P ^ 2 * (Qt ^ 2 + Qθ ^ 2)) +
      t * (2 * Pt * Ptt + 2 * Pθ * Ptθ + 2 * Real.exp P ^ 2 * Pt * (Qt ^ 2 + Qθ ^ 2) +
        Real.exp P ^ 2 * (2 * Qt * Qtt + 2 * Qθ * Qtθ)))
    (hLtθ : Ltθ = t * (2 * Pt * Ptθ + 2 * Pθ * Pθθ + 2 * Real.exp P ^ 2 * Pθ * (Qt ^ 2 + Qθ ^ 2) +
        Real.exp P ^ 2 * (2 * Qt * Qtθ + 2 * Qθ * Qθθ)))
    (hLθθ : Lθθ = 2 * t * (Ptθ * Pθ + Pt * Pθθ + 2 * Real.exp P ^ 2 * Pθ * Qt * Qθ +
        Real.exp P ^ 2 * (Qtθ * Qθ + Qt * Qθθ))) :
    ricciJet (gowdyAlgJet t P Q L ⟨P, Pt, Pθ, Ptt, Ptθ, Pθθ⟩ ⟨Q, Qt, Qθ, Qtt, Qtθ, Qθθ⟩
      ⟨L, Lt, Lθ, Ltt, Ltθ, Lθθ⟩) 0 0 = 0 := by
  subst hPtt hQtt hLtt hLtθ hLθθ hLt hLθ
  have key : Real.exp (1 / 2 * L + -(1 / 2) * Real.log t) = Real.exp (L / 2) / Real.sqrt t := by
    rw [Real.exp_add, show -(1 / 2) * Real.log t = -(Real.log t / 2) by ring, Real.exp_neg,
      Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht]
    ring_nf
  have key2 : Real.exp (-1 * P) = (Real.exp P)⁻¹ := by rw [neg_one_mul, Real.exp_neg]
  have v0 : (![t, P, Q, L] : Fin 4 → ℝ) 0 = t := rfl
  have v1 : (![t, P, Q, L] : Fin 4 → ℝ) 1 = P := rfl
  have v2 : (![t, P, Q, L] : Fin 4 → ℝ) 2 = Q := rfl
  have v3 : (![t, P, Q, L] : Fin 4 → ℝ) 3 = L := rfl
  simp only [gowdyAlgJet, gowdyEntryJets, J2.exp, J2.add, J2.cmul, J2.mul, jClock, jLogClock,
    J2.zero, key, key2, gowdyInvMetric, v0, v1, v2, v3, Real.exp_neg]
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ t = s ^ 2 :=
    ⟨Real.sqrt t, Real.sqrt_pos.2 ht, (Real.sq_sqrt ht.le).symm⟩
  have hu := Real.exp_pos (L / 2)
  have he := Real.exp_pos P
  rw [Real.sqrt_sq hs.le]
  generalize Real.exp (L / 2) = u at hu ⊢
  generalize Real.exp P = e at he ⊢
  simp [ricciJet, ricci, riemann, christoffel, dChristoffel, dInvMetric, jetOfEntries,
    Fin.sum_univ_four]
  try field_simp
  try ring

/-- Component `(0,1)` of the algebraic vacuum identity. -/
theorem ricci_gowdy_alg_01 {t P Q L Pt Pθ Ptθ Pθθ Qt Qθ Qtθ Qθθ Ptt Qtt Lt Lθ Ltt Ltθ Lθθ : ℝ}
    (ht : 0 < t)
    (hPtt : Ptt = Pθθ - Pt / t + Real.exp P ^ 2 * (Qt ^ 2 - Qθ ^ 2))
    (hQtt : Qtt = Qθθ - Qt / t - 2 * Pt * Qt + 2 * Pθ * Qθ)
    (hLt : Lt = t * (Pt ^ 2 + Pθ ^ 2 + Real.exp P ^ 2 * (Qt ^ 2 + Qθ ^ 2)))
    (hLθ : Lθ = 2 * t * (Pt * Pθ + Real.exp P ^ 2 * Qt * Qθ))
    (hLtt : Ltt = (Pt ^ 2 + Pθ ^ 2 + Real.exp P ^ 2 * (Qt ^ 2 + Qθ ^ 2)) +
      t * (2 * Pt * Ptt + 2 * Pθ * Ptθ + 2 * Real.exp P ^ 2 * Pt * (Qt ^ 2 + Qθ ^ 2) +
        Real.exp P ^ 2 * (2 * Qt * Qtt + 2 * Qθ * Qtθ)))
    (hLtθ : Ltθ = t * (2 * Pt * Ptθ + 2 * Pθ * Pθθ + 2 * Real.exp P ^ 2 * Pθ * (Qt ^ 2 + Qθ ^ 2) +
        Real.exp P ^ 2 * (2 * Qt * Qtθ + 2 * Qθ * Qθθ)))
    (hLθθ : Lθθ = 2 * t * (Ptθ * Pθ + Pt * Pθθ + 2 * Real.exp P ^ 2 * Pθ * Qt * Qθ +
        Real.exp P ^ 2 * (Qtθ * Qθ + Qt * Qθθ))) :
    ricciJet (gowdyAlgJet t P Q L ⟨P, Pt, Pθ, Ptt, Ptθ, Pθθ⟩ ⟨Q, Qt, Qθ, Qtt, Qtθ, Qθθ⟩
      ⟨L, Lt, Lθ, Ltt, Ltθ, Lθθ⟩) 0 1 = 0 := by
  subst hPtt hQtt hLtt hLtθ hLθθ hLt hLθ
  have key : Real.exp (1 / 2 * L + -(1 / 2) * Real.log t) = Real.exp (L / 2) / Real.sqrt t := by
    rw [Real.exp_add, show -(1 / 2) * Real.log t = -(Real.log t / 2) by ring, Real.exp_neg,
      Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht]
    ring_nf
  have key2 : Real.exp (-1 * P) = (Real.exp P)⁻¹ := by rw [neg_one_mul, Real.exp_neg]
  have v0 : (![t, P, Q, L] : Fin 4 → ℝ) 0 = t := rfl
  have v1 : (![t, P, Q, L] : Fin 4 → ℝ) 1 = P := rfl
  have v2 : (![t, P, Q, L] : Fin 4 → ℝ) 2 = Q := rfl
  have v3 : (![t, P, Q, L] : Fin 4 → ℝ) 3 = L := rfl
  simp only [gowdyAlgJet, gowdyEntryJets, J2.exp, J2.add, J2.cmul, J2.mul, jClock, jLogClock,
    J2.zero, key, key2, gowdyInvMetric, v0, v1, v2, v3, Real.exp_neg]
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ t = s ^ 2 :=
    ⟨Real.sqrt t, Real.sqrt_pos.2 ht, (Real.sq_sqrt ht.le).symm⟩
  have hu := Real.exp_pos (L / 2)
  have he := Real.exp_pos P
  rw [Real.sqrt_sq hs.le]
  generalize Real.exp (L / 2) = u at hu ⊢
  generalize Real.exp P = e at he ⊢
  simp [ricciJet, ricci, riemann, christoffel, dChristoffel, dInvMetric, jetOfEntries,
    Fin.sum_univ_four]
  try field_simp
  try ring

/-- Component `(0,2)` of the algebraic vacuum identity. -/
theorem ricci_gowdy_alg_02 {t P Q L Pt Pθ Ptθ Pθθ Qt Qθ Qtθ Qθθ Ptt Qtt Lt Lθ Ltt Ltθ Lθθ : ℝ}
    (ht : 0 < t)
    (hPtt : Ptt = Pθθ - Pt / t + Real.exp P ^ 2 * (Qt ^ 2 - Qθ ^ 2))
    (hQtt : Qtt = Qθθ - Qt / t - 2 * Pt * Qt + 2 * Pθ * Qθ)
    (hLt : Lt = t * (Pt ^ 2 + Pθ ^ 2 + Real.exp P ^ 2 * (Qt ^ 2 + Qθ ^ 2)))
    (hLθ : Lθ = 2 * t * (Pt * Pθ + Real.exp P ^ 2 * Qt * Qθ))
    (hLtt : Ltt = (Pt ^ 2 + Pθ ^ 2 + Real.exp P ^ 2 * (Qt ^ 2 + Qθ ^ 2)) +
      t * (2 * Pt * Ptt + 2 * Pθ * Ptθ + 2 * Real.exp P ^ 2 * Pt * (Qt ^ 2 + Qθ ^ 2) +
        Real.exp P ^ 2 * (2 * Qt * Qtt + 2 * Qθ * Qtθ)))
    (hLtθ : Ltθ = t * (2 * Pt * Ptθ + 2 * Pθ * Pθθ + 2 * Real.exp P ^ 2 * Pθ * (Qt ^ 2 + Qθ ^ 2) +
        Real.exp P ^ 2 * (2 * Qt * Qtθ + 2 * Qθ * Qθθ)))
    (hLθθ : Lθθ = 2 * t * (Ptθ * Pθ + Pt * Pθθ + 2 * Real.exp P ^ 2 * Pθ * Qt * Qθ +
        Real.exp P ^ 2 * (Qtθ * Qθ + Qt * Qθθ))) :
    ricciJet (gowdyAlgJet t P Q L ⟨P, Pt, Pθ, Ptt, Ptθ, Pθθ⟩ ⟨Q, Qt, Qθ, Qtt, Qtθ, Qθθ⟩
      ⟨L, Lt, Lθ, Ltt, Ltθ, Lθθ⟩) 0 2 = 0 := by
  subst hPtt hQtt hLtt hLtθ hLθθ hLt hLθ
  have key : Real.exp (1 / 2 * L + -(1 / 2) * Real.log t) = Real.exp (L / 2) / Real.sqrt t := by
    rw [Real.exp_add, show -(1 / 2) * Real.log t = -(Real.log t / 2) by ring, Real.exp_neg,
      Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht]
    ring_nf
  have key2 : Real.exp (-1 * P) = (Real.exp P)⁻¹ := by rw [neg_one_mul, Real.exp_neg]
  have v0 : (![t, P, Q, L] : Fin 4 → ℝ) 0 = t := rfl
  have v1 : (![t, P, Q, L] : Fin 4 → ℝ) 1 = P := rfl
  have v2 : (![t, P, Q, L] : Fin 4 → ℝ) 2 = Q := rfl
  have v3 : (![t, P, Q, L] : Fin 4 → ℝ) 3 = L := rfl
  simp only [gowdyAlgJet, gowdyEntryJets, J2.exp, J2.add, J2.cmul, J2.mul, jClock, jLogClock,
    J2.zero, key, key2, gowdyInvMetric, v0, v1, v2, v3, Real.exp_neg]
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ t = s ^ 2 :=
    ⟨Real.sqrt t, Real.sqrt_pos.2 ht, (Real.sq_sqrt ht.le).symm⟩
  have hu := Real.exp_pos (L / 2)
  have he := Real.exp_pos P
  rw [Real.sqrt_sq hs.le]
  generalize Real.exp (L / 2) = u at hu ⊢
  generalize Real.exp P = e at he ⊢
  simp [ricciJet, ricci, riemann, christoffel, dChristoffel, dInvMetric, jetOfEntries,
    Fin.sum_univ_four]
  try field_simp
  try ring

/-- Component `(0,3)` of the algebraic vacuum identity. -/
theorem ricci_gowdy_alg_03 {t P Q L Pt Pθ Ptθ Pθθ Qt Qθ Qtθ Qθθ Ptt Qtt Lt Lθ Ltt Ltθ Lθθ : ℝ}
    (ht : 0 < t)
    (hPtt : Ptt = Pθθ - Pt / t + Real.exp P ^ 2 * (Qt ^ 2 - Qθ ^ 2))
    (hQtt : Qtt = Qθθ - Qt / t - 2 * Pt * Qt + 2 * Pθ * Qθ)
    (hLt : Lt = t * (Pt ^ 2 + Pθ ^ 2 + Real.exp P ^ 2 * (Qt ^ 2 + Qθ ^ 2)))
    (hLθ : Lθ = 2 * t * (Pt * Pθ + Real.exp P ^ 2 * Qt * Qθ))
    (hLtt : Ltt = (Pt ^ 2 + Pθ ^ 2 + Real.exp P ^ 2 * (Qt ^ 2 + Qθ ^ 2)) +
      t * (2 * Pt * Ptt + 2 * Pθ * Ptθ + 2 * Real.exp P ^ 2 * Pt * (Qt ^ 2 + Qθ ^ 2) +
        Real.exp P ^ 2 * (2 * Qt * Qtt + 2 * Qθ * Qtθ)))
    (hLtθ : Ltθ = t * (2 * Pt * Ptθ + 2 * Pθ * Pθθ + 2 * Real.exp P ^ 2 * Pθ * (Qt ^ 2 + Qθ ^ 2) +
        Real.exp P ^ 2 * (2 * Qt * Qtθ + 2 * Qθ * Qθθ)))
    (hLθθ : Lθθ = 2 * t * (Ptθ * Pθ + Pt * Pθθ + 2 * Real.exp P ^ 2 * Pθ * Qt * Qθ +
        Real.exp P ^ 2 * (Qtθ * Qθ + Qt * Qθθ))) :
    ricciJet (gowdyAlgJet t P Q L ⟨P, Pt, Pθ, Ptt, Ptθ, Pθθ⟩ ⟨Q, Qt, Qθ, Qtt, Qtθ, Qθθ⟩
      ⟨L, Lt, Lθ, Ltt, Ltθ, Lθθ⟩) 0 3 = 0 := by
  subst hPtt hQtt hLtt hLtθ hLθθ hLt hLθ
  have key : Real.exp (1 / 2 * L + -(1 / 2) * Real.log t) = Real.exp (L / 2) / Real.sqrt t := by
    rw [Real.exp_add, show -(1 / 2) * Real.log t = -(Real.log t / 2) by ring, Real.exp_neg,
      Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht]
    ring_nf
  have key2 : Real.exp (-1 * P) = (Real.exp P)⁻¹ := by rw [neg_one_mul, Real.exp_neg]
  have v0 : (![t, P, Q, L] : Fin 4 → ℝ) 0 = t := rfl
  have v1 : (![t, P, Q, L] : Fin 4 → ℝ) 1 = P := rfl
  have v2 : (![t, P, Q, L] : Fin 4 → ℝ) 2 = Q := rfl
  have v3 : (![t, P, Q, L] : Fin 4 → ℝ) 3 = L := rfl
  simp only [gowdyAlgJet, gowdyEntryJets, J2.exp, J2.add, J2.cmul, J2.mul, jClock, jLogClock,
    J2.zero, key, key2, gowdyInvMetric, v0, v1, v2, v3, Real.exp_neg]
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ t = s ^ 2 :=
    ⟨Real.sqrt t, Real.sqrt_pos.2 ht, (Real.sq_sqrt ht.le).symm⟩
  have hu := Real.exp_pos (L / 2)
  have he := Real.exp_pos P
  rw [Real.sqrt_sq hs.le]
  generalize Real.exp (L / 2) = u at hu ⊢
  generalize Real.exp P = e at he ⊢
  simp [ricciJet, ricci, riemann, christoffel, dChristoffel, dInvMetric, jetOfEntries,
    Fin.sum_univ_four]
  try field_simp
  try ring

/-- Component `(1,0)` of the algebraic vacuum identity. -/
theorem ricci_gowdy_alg_10 {t P Q L Pt Pθ Ptθ Pθθ Qt Qθ Qtθ Qθθ Ptt Qtt Lt Lθ Ltt Ltθ Lθθ : ℝ}
    (ht : 0 < t)
    (hPtt : Ptt = Pθθ - Pt / t + Real.exp P ^ 2 * (Qt ^ 2 - Qθ ^ 2))
    (hQtt : Qtt = Qθθ - Qt / t - 2 * Pt * Qt + 2 * Pθ * Qθ)
    (hLt : Lt = t * (Pt ^ 2 + Pθ ^ 2 + Real.exp P ^ 2 * (Qt ^ 2 + Qθ ^ 2)))
    (hLθ : Lθ = 2 * t * (Pt * Pθ + Real.exp P ^ 2 * Qt * Qθ))
    (hLtt : Ltt = (Pt ^ 2 + Pθ ^ 2 + Real.exp P ^ 2 * (Qt ^ 2 + Qθ ^ 2)) +
      t * (2 * Pt * Ptt + 2 * Pθ * Ptθ + 2 * Real.exp P ^ 2 * Pt * (Qt ^ 2 + Qθ ^ 2) +
        Real.exp P ^ 2 * (2 * Qt * Qtt + 2 * Qθ * Qtθ)))
    (hLtθ : Ltθ = t * (2 * Pt * Ptθ + 2 * Pθ * Pθθ + 2 * Real.exp P ^ 2 * Pθ * (Qt ^ 2 + Qθ ^ 2) +
        Real.exp P ^ 2 * (2 * Qt * Qtθ + 2 * Qθ * Qθθ)))
    (hLθθ : Lθθ = 2 * t * (Ptθ * Pθ + Pt * Pθθ + 2 * Real.exp P ^ 2 * Pθ * Qt * Qθ +
        Real.exp P ^ 2 * (Qtθ * Qθ + Qt * Qθθ))) :
    ricciJet (gowdyAlgJet t P Q L ⟨P, Pt, Pθ, Ptt, Ptθ, Pθθ⟩ ⟨Q, Qt, Qθ, Qtt, Qtθ, Qθθ⟩
      ⟨L, Lt, Lθ, Ltt, Ltθ, Lθθ⟩) 1 0 = 0 := by
  subst hPtt hQtt hLtt hLtθ hLθθ hLt hLθ
  have key : Real.exp (1 / 2 * L + -(1 / 2) * Real.log t) = Real.exp (L / 2) / Real.sqrt t := by
    rw [Real.exp_add, show -(1 / 2) * Real.log t = -(Real.log t / 2) by ring, Real.exp_neg,
      Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht]
    ring_nf
  have key2 : Real.exp (-1 * P) = (Real.exp P)⁻¹ := by rw [neg_one_mul, Real.exp_neg]
  have v0 : (![t, P, Q, L] : Fin 4 → ℝ) 0 = t := rfl
  have v1 : (![t, P, Q, L] : Fin 4 → ℝ) 1 = P := rfl
  have v2 : (![t, P, Q, L] : Fin 4 → ℝ) 2 = Q := rfl
  have v3 : (![t, P, Q, L] : Fin 4 → ℝ) 3 = L := rfl
  simp only [gowdyAlgJet, gowdyEntryJets, J2.exp, J2.add, J2.cmul, J2.mul, jClock, jLogClock,
    J2.zero, key, key2, gowdyInvMetric, v0, v1, v2, v3, Real.exp_neg]
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ t = s ^ 2 :=
    ⟨Real.sqrt t, Real.sqrt_pos.2 ht, (Real.sq_sqrt ht.le).symm⟩
  have hu := Real.exp_pos (L / 2)
  have he := Real.exp_pos P
  rw [Real.sqrt_sq hs.le]
  generalize Real.exp (L / 2) = u at hu ⊢
  generalize Real.exp P = e at he ⊢
  simp [ricciJet, ricci, riemann, christoffel, dChristoffel, dInvMetric, jetOfEntries,
    Fin.sum_univ_four]
  try field_simp
  try ring

/-- Component `(1,1)` of the algebraic vacuum identity. -/
theorem ricci_gowdy_alg_11 {t P Q L Pt Pθ Ptθ Pθθ Qt Qθ Qtθ Qθθ Ptt Qtt Lt Lθ Ltt Ltθ Lθθ : ℝ}
    (ht : 0 < t)
    (hPtt : Ptt = Pθθ - Pt / t + Real.exp P ^ 2 * (Qt ^ 2 - Qθ ^ 2))
    (hQtt : Qtt = Qθθ - Qt / t - 2 * Pt * Qt + 2 * Pθ * Qθ)
    (hLt : Lt = t * (Pt ^ 2 + Pθ ^ 2 + Real.exp P ^ 2 * (Qt ^ 2 + Qθ ^ 2)))
    (hLθ : Lθ = 2 * t * (Pt * Pθ + Real.exp P ^ 2 * Qt * Qθ))
    (hLtt : Ltt = (Pt ^ 2 + Pθ ^ 2 + Real.exp P ^ 2 * (Qt ^ 2 + Qθ ^ 2)) +
      t * (2 * Pt * Ptt + 2 * Pθ * Ptθ + 2 * Real.exp P ^ 2 * Pt * (Qt ^ 2 + Qθ ^ 2) +
        Real.exp P ^ 2 * (2 * Qt * Qtt + 2 * Qθ * Qtθ)))
    (hLtθ : Ltθ = t * (2 * Pt * Ptθ + 2 * Pθ * Pθθ + 2 * Real.exp P ^ 2 * Pθ * (Qt ^ 2 + Qθ ^ 2) +
        Real.exp P ^ 2 * (2 * Qt * Qtθ + 2 * Qθ * Qθθ)))
    (hLθθ : Lθθ = 2 * t * (Ptθ * Pθ + Pt * Pθθ + 2 * Real.exp P ^ 2 * Pθ * Qt * Qθ +
        Real.exp P ^ 2 * (Qtθ * Qθ + Qt * Qθθ))) :
    ricciJet (gowdyAlgJet t P Q L ⟨P, Pt, Pθ, Ptt, Ptθ, Pθθ⟩ ⟨Q, Qt, Qθ, Qtt, Qtθ, Qθθ⟩
      ⟨L, Lt, Lθ, Ltt, Ltθ, Lθθ⟩) 1 1 = 0 := by
  subst hPtt hQtt hLtt hLtθ hLθθ hLt hLθ
  have key : Real.exp (1 / 2 * L + -(1 / 2) * Real.log t) = Real.exp (L / 2) / Real.sqrt t := by
    rw [Real.exp_add, show -(1 / 2) * Real.log t = -(Real.log t / 2) by ring, Real.exp_neg,
      Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht]
    ring_nf
  have key2 : Real.exp (-1 * P) = (Real.exp P)⁻¹ := by rw [neg_one_mul, Real.exp_neg]
  have v0 : (![t, P, Q, L] : Fin 4 → ℝ) 0 = t := rfl
  have v1 : (![t, P, Q, L] : Fin 4 → ℝ) 1 = P := rfl
  have v2 : (![t, P, Q, L] : Fin 4 → ℝ) 2 = Q := rfl
  have v3 : (![t, P, Q, L] : Fin 4 → ℝ) 3 = L := rfl
  simp only [gowdyAlgJet, gowdyEntryJets, J2.exp, J2.add, J2.cmul, J2.mul, jClock, jLogClock,
    J2.zero, key, key2, gowdyInvMetric, v0, v1, v2, v3, Real.exp_neg]
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ t = s ^ 2 :=
    ⟨Real.sqrt t, Real.sqrt_pos.2 ht, (Real.sq_sqrt ht.le).symm⟩
  have hu := Real.exp_pos (L / 2)
  have he := Real.exp_pos P
  rw [Real.sqrt_sq hs.le]
  generalize Real.exp (L / 2) = u at hu ⊢
  generalize Real.exp P = e at he ⊢
  simp [ricciJet, ricci, riemann, christoffel, dChristoffel, dInvMetric, jetOfEntries,
    Fin.sum_univ_four]
  try field_simp
  try ring

/-- Component `(1,2)` of the algebraic vacuum identity. -/
theorem ricci_gowdy_alg_12 {t P Q L Pt Pθ Ptθ Pθθ Qt Qθ Qtθ Qθθ Ptt Qtt Lt Lθ Ltt Ltθ Lθθ : ℝ}
    (ht : 0 < t)
    (hPtt : Ptt = Pθθ - Pt / t + Real.exp P ^ 2 * (Qt ^ 2 - Qθ ^ 2))
    (hQtt : Qtt = Qθθ - Qt / t - 2 * Pt * Qt + 2 * Pθ * Qθ)
    (hLt : Lt = t * (Pt ^ 2 + Pθ ^ 2 + Real.exp P ^ 2 * (Qt ^ 2 + Qθ ^ 2)))
    (hLθ : Lθ = 2 * t * (Pt * Pθ + Real.exp P ^ 2 * Qt * Qθ))
    (hLtt : Ltt = (Pt ^ 2 + Pθ ^ 2 + Real.exp P ^ 2 * (Qt ^ 2 + Qθ ^ 2)) +
      t * (2 * Pt * Ptt + 2 * Pθ * Ptθ + 2 * Real.exp P ^ 2 * Pt * (Qt ^ 2 + Qθ ^ 2) +
        Real.exp P ^ 2 * (2 * Qt * Qtt + 2 * Qθ * Qtθ)))
    (hLtθ : Ltθ = t * (2 * Pt * Ptθ + 2 * Pθ * Pθθ + 2 * Real.exp P ^ 2 * Pθ * (Qt ^ 2 + Qθ ^ 2) +
        Real.exp P ^ 2 * (2 * Qt * Qtθ + 2 * Qθ * Qθθ)))
    (hLθθ : Lθθ = 2 * t * (Ptθ * Pθ + Pt * Pθθ + 2 * Real.exp P ^ 2 * Pθ * Qt * Qθ +
        Real.exp P ^ 2 * (Qtθ * Qθ + Qt * Qθθ))) :
    ricciJet (gowdyAlgJet t P Q L ⟨P, Pt, Pθ, Ptt, Ptθ, Pθθ⟩ ⟨Q, Qt, Qθ, Qtt, Qtθ, Qθθ⟩
      ⟨L, Lt, Lθ, Ltt, Ltθ, Lθθ⟩) 1 2 = 0 := by
  subst hPtt hQtt hLtt hLtθ hLθθ hLt hLθ
  have key : Real.exp (1 / 2 * L + -(1 / 2) * Real.log t) = Real.exp (L / 2) / Real.sqrt t := by
    rw [Real.exp_add, show -(1 / 2) * Real.log t = -(Real.log t / 2) by ring, Real.exp_neg,
      Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht]
    ring_nf
  have key2 : Real.exp (-1 * P) = (Real.exp P)⁻¹ := by rw [neg_one_mul, Real.exp_neg]
  have v0 : (![t, P, Q, L] : Fin 4 → ℝ) 0 = t := rfl
  have v1 : (![t, P, Q, L] : Fin 4 → ℝ) 1 = P := rfl
  have v2 : (![t, P, Q, L] : Fin 4 → ℝ) 2 = Q := rfl
  have v3 : (![t, P, Q, L] : Fin 4 → ℝ) 3 = L := rfl
  simp only [gowdyAlgJet, gowdyEntryJets, J2.exp, J2.add, J2.cmul, J2.mul, jClock, jLogClock,
    J2.zero, key, key2, gowdyInvMetric, v0, v1, v2, v3, Real.exp_neg]
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ t = s ^ 2 :=
    ⟨Real.sqrt t, Real.sqrt_pos.2 ht, (Real.sq_sqrt ht.le).symm⟩
  have hu := Real.exp_pos (L / 2)
  have he := Real.exp_pos P
  rw [Real.sqrt_sq hs.le]
  generalize Real.exp (L / 2) = u at hu ⊢
  generalize Real.exp P = e at he ⊢
  simp [ricciJet, ricci, riemann, christoffel, dChristoffel, dInvMetric, jetOfEntries,
    Fin.sum_univ_four]
  try field_simp
  try ring

/-- Component `(1,3)` of the algebraic vacuum identity. -/
theorem ricci_gowdy_alg_13 {t P Q L Pt Pθ Ptθ Pθθ Qt Qθ Qtθ Qθθ Ptt Qtt Lt Lθ Ltt Ltθ Lθθ : ℝ}
    (ht : 0 < t)
    (hPtt : Ptt = Pθθ - Pt / t + Real.exp P ^ 2 * (Qt ^ 2 - Qθ ^ 2))
    (hQtt : Qtt = Qθθ - Qt / t - 2 * Pt * Qt + 2 * Pθ * Qθ)
    (hLt : Lt = t * (Pt ^ 2 + Pθ ^ 2 + Real.exp P ^ 2 * (Qt ^ 2 + Qθ ^ 2)))
    (hLθ : Lθ = 2 * t * (Pt * Pθ + Real.exp P ^ 2 * Qt * Qθ))
    (hLtt : Ltt = (Pt ^ 2 + Pθ ^ 2 + Real.exp P ^ 2 * (Qt ^ 2 + Qθ ^ 2)) +
      t * (2 * Pt * Ptt + 2 * Pθ * Ptθ + 2 * Real.exp P ^ 2 * Pt * (Qt ^ 2 + Qθ ^ 2) +
        Real.exp P ^ 2 * (2 * Qt * Qtt + 2 * Qθ * Qtθ)))
    (hLtθ : Ltθ = t * (2 * Pt * Ptθ + 2 * Pθ * Pθθ + 2 * Real.exp P ^ 2 * Pθ * (Qt ^ 2 + Qθ ^ 2) +
        Real.exp P ^ 2 * (2 * Qt * Qtθ + 2 * Qθ * Qθθ)))
    (hLθθ : Lθθ = 2 * t * (Ptθ * Pθ + Pt * Pθθ + 2 * Real.exp P ^ 2 * Pθ * Qt * Qθ +
        Real.exp P ^ 2 * (Qtθ * Qθ + Qt * Qθθ))) :
    ricciJet (gowdyAlgJet t P Q L ⟨P, Pt, Pθ, Ptt, Ptθ, Pθθ⟩ ⟨Q, Qt, Qθ, Qtt, Qtθ, Qθθ⟩
      ⟨L, Lt, Lθ, Ltt, Ltθ, Lθθ⟩) 1 3 = 0 := by
  subst hPtt hQtt hLtt hLtθ hLθθ hLt hLθ
  have key : Real.exp (1 / 2 * L + -(1 / 2) * Real.log t) = Real.exp (L / 2) / Real.sqrt t := by
    rw [Real.exp_add, show -(1 / 2) * Real.log t = -(Real.log t / 2) by ring, Real.exp_neg,
      Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht]
    ring_nf
  have key2 : Real.exp (-1 * P) = (Real.exp P)⁻¹ := by rw [neg_one_mul, Real.exp_neg]
  have v0 : (![t, P, Q, L] : Fin 4 → ℝ) 0 = t := rfl
  have v1 : (![t, P, Q, L] : Fin 4 → ℝ) 1 = P := rfl
  have v2 : (![t, P, Q, L] : Fin 4 → ℝ) 2 = Q := rfl
  have v3 : (![t, P, Q, L] : Fin 4 → ℝ) 3 = L := rfl
  simp only [gowdyAlgJet, gowdyEntryJets, J2.exp, J2.add, J2.cmul, J2.mul, jClock, jLogClock,
    J2.zero, key, key2, gowdyInvMetric, v0, v1, v2, v3, Real.exp_neg]
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ t = s ^ 2 :=
    ⟨Real.sqrt t, Real.sqrt_pos.2 ht, (Real.sq_sqrt ht.le).symm⟩
  have hu := Real.exp_pos (L / 2)
  have he := Real.exp_pos P
  rw [Real.sqrt_sq hs.le]
  generalize Real.exp (L / 2) = u at hu ⊢
  generalize Real.exp P = e at he ⊢
  simp [ricciJet, ricci, riemann, christoffel, dChristoffel, dInvMetric, jetOfEntries,
    Fin.sum_univ_four]
  try field_simp
  try ring

/-- Component `(2,0)` of the algebraic vacuum identity. -/
theorem ricci_gowdy_alg_20 {t P Q L Pt Pθ Ptθ Pθθ Qt Qθ Qtθ Qθθ Ptt Qtt Lt Lθ Ltt Ltθ Lθθ : ℝ}
    (ht : 0 < t)
    (hPtt : Ptt = Pθθ - Pt / t + Real.exp P ^ 2 * (Qt ^ 2 - Qθ ^ 2))
    (hQtt : Qtt = Qθθ - Qt / t - 2 * Pt * Qt + 2 * Pθ * Qθ)
    (hLt : Lt = t * (Pt ^ 2 + Pθ ^ 2 + Real.exp P ^ 2 * (Qt ^ 2 + Qθ ^ 2)))
    (hLθ : Lθ = 2 * t * (Pt * Pθ + Real.exp P ^ 2 * Qt * Qθ))
    (hLtt : Ltt = (Pt ^ 2 + Pθ ^ 2 + Real.exp P ^ 2 * (Qt ^ 2 + Qθ ^ 2)) +
      t * (2 * Pt * Ptt + 2 * Pθ * Ptθ + 2 * Real.exp P ^ 2 * Pt * (Qt ^ 2 + Qθ ^ 2) +
        Real.exp P ^ 2 * (2 * Qt * Qtt + 2 * Qθ * Qtθ)))
    (hLtθ : Ltθ = t * (2 * Pt * Ptθ + 2 * Pθ * Pθθ + 2 * Real.exp P ^ 2 * Pθ * (Qt ^ 2 + Qθ ^ 2) +
        Real.exp P ^ 2 * (2 * Qt * Qtθ + 2 * Qθ * Qθθ)))
    (hLθθ : Lθθ = 2 * t * (Ptθ * Pθ + Pt * Pθθ + 2 * Real.exp P ^ 2 * Pθ * Qt * Qθ +
        Real.exp P ^ 2 * (Qtθ * Qθ + Qt * Qθθ))) :
    ricciJet (gowdyAlgJet t P Q L ⟨P, Pt, Pθ, Ptt, Ptθ, Pθθ⟩ ⟨Q, Qt, Qθ, Qtt, Qtθ, Qθθ⟩
      ⟨L, Lt, Lθ, Ltt, Ltθ, Lθθ⟩) 2 0 = 0 := by
  subst hPtt hQtt hLtt hLtθ hLθθ hLt hLθ
  have key : Real.exp (1 / 2 * L + -(1 / 2) * Real.log t) = Real.exp (L / 2) / Real.sqrt t := by
    rw [Real.exp_add, show -(1 / 2) * Real.log t = -(Real.log t / 2) by ring, Real.exp_neg,
      Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht]
    ring_nf
  have key2 : Real.exp (-1 * P) = (Real.exp P)⁻¹ := by rw [neg_one_mul, Real.exp_neg]
  have v0 : (![t, P, Q, L] : Fin 4 → ℝ) 0 = t := rfl
  have v1 : (![t, P, Q, L] : Fin 4 → ℝ) 1 = P := rfl
  have v2 : (![t, P, Q, L] : Fin 4 → ℝ) 2 = Q := rfl
  have v3 : (![t, P, Q, L] : Fin 4 → ℝ) 3 = L := rfl
  simp only [gowdyAlgJet, gowdyEntryJets, J2.exp, J2.add, J2.cmul, J2.mul, jClock, jLogClock,
    J2.zero, key, key2, gowdyInvMetric, v0, v1, v2, v3, Real.exp_neg]
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ t = s ^ 2 :=
    ⟨Real.sqrt t, Real.sqrt_pos.2 ht, (Real.sq_sqrt ht.le).symm⟩
  have hu := Real.exp_pos (L / 2)
  have he := Real.exp_pos P
  rw [Real.sqrt_sq hs.le]
  generalize Real.exp (L / 2) = u at hu ⊢
  generalize Real.exp P = e at he ⊢
  simp [ricciJet, ricci, riemann, christoffel, dChristoffel, dInvMetric, jetOfEntries,
    Fin.sum_univ_four]
  try field_simp
  try ring

/-- Component `(2,1)` of the algebraic vacuum identity. -/
theorem ricci_gowdy_alg_21 {t P Q L Pt Pθ Ptθ Pθθ Qt Qθ Qtθ Qθθ Ptt Qtt Lt Lθ Ltt Ltθ Lθθ : ℝ}
    (ht : 0 < t)
    (hPtt : Ptt = Pθθ - Pt / t + Real.exp P ^ 2 * (Qt ^ 2 - Qθ ^ 2))
    (hQtt : Qtt = Qθθ - Qt / t - 2 * Pt * Qt + 2 * Pθ * Qθ)
    (hLt : Lt = t * (Pt ^ 2 + Pθ ^ 2 + Real.exp P ^ 2 * (Qt ^ 2 + Qθ ^ 2)))
    (hLθ : Lθ = 2 * t * (Pt * Pθ + Real.exp P ^ 2 * Qt * Qθ))
    (hLtt : Ltt = (Pt ^ 2 + Pθ ^ 2 + Real.exp P ^ 2 * (Qt ^ 2 + Qθ ^ 2)) +
      t * (2 * Pt * Ptt + 2 * Pθ * Ptθ + 2 * Real.exp P ^ 2 * Pt * (Qt ^ 2 + Qθ ^ 2) +
        Real.exp P ^ 2 * (2 * Qt * Qtt + 2 * Qθ * Qtθ)))
    (hLtθ : Ltθ = t * (2 * Pt * Ptθ + 2 * Pθ * Pθθ + 2 * Real.exp P ^ 2 * Pθ * (Qt ^ 2 + Qθ ^ 2) +
        Real.exp P ^ 2 * (2 * Qt * Qtθ + 2 * Qθ * Qθθ)))
    (hLθθ : Lθθ = 2 * t * (Ptθ * Pθ + Pt * Pθθ + 2 * Real.exp P ^ 2 * Pθ * Qt * Qθ +
        Real.exp P ^ 2 * (Qtθ * Qθ + Qt * Qθθ))) :
    ricciJet (gowdyAlgJet t P Q L ⟨P, Pt, Pθ, Ptt, Ptθ, Pθθ⟩ ⟨Q, Qt, Qθ, Qtt, Qtθ, Qθθ⟩
      ⟨L, Lt, Lθ, Ltt, Ltθ, Lθθ⟩) 2 1 = 0 := by
  subst hPtt hQtt hLtt hLtθ hLθθ hLt hLθ
  have key : Real.exp (1 / 2 * L + -(1 / 2) * Real.log t) = Real.exp (L / 2) / Real.sqrt t := by
    rw [Real.exp_add, show -(1 / 2) * Real.log t = -(Real.log t / 2) by ring, Real.exp_neg,
      Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht]
    ring_nf
  have key2 : Real.exp (-1 * P) = (Real.exp P)⁻¹ := by rw [neg_one_mul, Real.exp_neg]
  have v0 : (![t, P, Q, L] : Fin 4 → ℝ) 0 = t := rfl
  have v1 : (![t, P, Q, L] : Fin 4 → ℝ) 1 = P := rfl
  have v2 : (![t, P, Q, L] : Fin 4 → ℝ) 2 = Q := rfl
  have v3 : (![t, P, Q, L] : Fin 4 → ℝ) 3 = L := rfl
  simp only [gowdyAlgJet, gowdyEntryJets, J2.exp, J2.add, J2.cmul, J2.mul, jClock, jLogClock,
    J2.zero, key, key2, gowdyInvMetric, v0, v1, v2, v3, Real.exp_neg]
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ t = s ^ 2 :=
    ⟨Real.sqrt t, Real.sqrt_pos.2 ht, (Real.sq_sqrt ht.le).symm⟩
  have hu := Real.exp_pos (L / 2)
  have he := Real.exp_pos P
  rw [Real.sqrt_sq hs.le]
  generalize Real.exp (L / 2) = u at hu ⊢
  generalize Real.exp P = e at he ⊢
  simp [ricciJet, ricci, riemann, christoffel, dChristoffel, dInvMetric, jetOfEntries,
    Fin.sum_univ_four]
  try field_simp
  try ring

/-- Component `(2,2)` of the algebraic vacuum identity. -/
theorem ricci_gowdy_alg_22 {t P Q L Pt Pθ Ptθ Pθθ Qt Qθ Qtθ Qθθ Ptt Qtt Lt Lθ Ltt Ltθ Lθθ : ℝ}
    (ht : 0 < t)
    (hPtt : Ptt = Pθθ - Pt / t + Real.exp P ^ 2 * (Qt ^ 2 - Qθ ^ 2))
    (hQtt : Qtt = Qθθ - Qt / t - 2 * Pt * Qt + 2 * Pθ * Qθ)
    (hLt : Lt = t * (Pt ^ 2 + Pθ ^ 2 + Real.exp P ^ 2 * (Qt ^ 2 + Qθ ^ 2)))
    (hLθ : Lθ = 2 * t * (Pt * Pθ + Real.exp P ^ 2 * Qt * Qθ))
    (hLtt : Ltt = (Pt ^ 2 + Pθ ^ 2 + Real.exp P ^ 2 * (Qt ^ 2 + Qθ ^ 2)) +
      t * (2 * Pt * Ptt + 2 * Pθ * Ptθ + 2 * Real.exp P ^ 2 * Pt * (Qt ^ 2 + Qθ ^ 2) +
        Real.exp P ^ 2 * (2 * Qt * Qtt + 2 * Qθ * Qtθ)))
    (hLtθ : Ltθ = t * (2 * Pt * Ptθ + 2 * Pθ * Pθθ + 2 * Real.exp P ^ 2 * Pθ * (Qt ^ 2 + Qθ ^ 2) +
        Real.exp P ^ 2 * (2 * Qt * Qtθ + 2 * Qθ * Qθθ)))
    (hLθθ : Lθθ = 2 * t * (Ptθ * Pθ + Pt * Pθθ + 2 * Real.exp P ^ 2 * Pθ * Qt * Qθ +
        Real.exp P ^ 2 * (Qtθ * Qθ + Qt * Qθθ))) :
    ricciJet (gowdyAlgJet t P Q L ⟨P, Pt, Pθ, Ptt, Ptθ, Pθθ⟩ ⟨Q, Qt, Qθ, Qtt, Qtθ, Qθθ⟩
      ⟨L, Lt, Lθ, Ltt, Ltθ, Lθθ⟩) 2 2 = 0 := by
  subst hPtt hQtt hLtt hLtθ hLθθ hLt hLθ
  have key : Real.exp (1 / 2 * L + -(1 / 2) * Real.log t) = Real.exp (L / 2) / Real.sqrt t := by
    rw [Real.exp_add, show -(1 / 2) * Real.log t = -(Real.log t / 2) by ring, Real.exp_neg,
      Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht]
    ring_nf
  have key2 : Real.exp (-1 * P) = (Real.exp P)⁻¹ := by rw [neg_one_mul, Real.exp_neg]
  have v0 : (![t, P, Q, L] : Fin 4 → ℝ) 0 = t := rfl
  have v1 : (![t, P, Q, L] : Fin 4 → ℝ) 1 = P := rfl
  have v2 : (![t, P, Q, L] : Fin 4 → ℝ) 2 = Q := rfl
  have v3 : (![t, P, Q, L] : Fin 4 → ℝ) 3 = L := rfl
  simp only [gowdyAlgJet, gowdyEntryJets, J2.exp, J2.add, J2.cmul, J2.mul, jClock, jLogClock,
    J2.zero, key, key2, gowdyInvMetric, v0, v1, v2, v3, Real.exp_neg]
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ t = s ^ 2 :=
    ⟨Real.sqrt t, Real.sqrt_pos.2 ht, (Real.sq_sqrt ht.le).symm⟩
  have hu := Real.exp_pos (L / 2)
  have he := Real.exp_pos P
  rw [Real.sqrt_sq hs.le]
  generalize Real.exp (L / 2) = u at hu ⊢
  generalize Real.exp P = e at he ⊢
  simp [ricciJet, ricci, riemann, christoffel, dChristoffel, dInvMetric, jetOfEntries,
    Fin.sum_univ_four]
  try field_simp
  try ring

/-- Component `(2,3)` of the algebraic vacuum identity. -/
theorem ricci_gowdy_alg_23 {t P Q L Pt Pθ Ptθ Pθθ Qt Qθ Qtθ Qθθ Ptt Qtt Lt Lθ Ltt Ltθ Lθθ : ℝ}
    (ht : 0 < t)
    (hPtt : Ptt = Pθθ - Pt / t + Real.exp P ^ 2 * (Qt ^ 2 - Qθ ^ 2))
    (hQtt : Qtt = Qθθ - Qt / t - 2 * Pt * Qt + 2 * Pθ * Qθ)
    (hLt : Lt = t * (Pt ^ 2 + Pθ ^ 2 + Real.exp P ^ 2 * (Qt ^ 2 + Qθ ^ 2)))
    (hLθ : Lθ = 2 * t * (Pt * Pθ + Real.exp P ^ 2 * Qt * Qθ))
    (hLtt : Ltt = (Pt ^ 2 + Pθ ^ 2 + Real.exp P ^ 2 * (Qt ^ 2 + Qθ ^ 2)) +
      t * (2 * Pt * Ptt + 2 * Pθ * Ptθ + 2 * Real.exp P ^ 2 * Pt * (Qt ^ 2 + Qθ ^ 2) +
        Real.exp P ^ 2 * (2 * Qt * Qtt + 2 * Qθ * Qtθ)))
    (hLtθ : Ltθ = t * (2 * Pt * Ptθ + 2 * Pθ * Pθθ + 2 * Real.exp P ^ 2 * Pθ * (Qt ^ 2 + Qθ ^ 2) +
        Real.exp P ^ 2 * (2 * Qt * Qtθ + 2 * Qθ * Qθθ)))
    (hLθθ : Lθθ = 2 * t * (Ptθ * Pθ + Pt * Pθθ + 2 * Real.exp P ^ 2 * Pθ * Qt * Qθ +
        Real.exp P ^ 2 * (Qtθ * Qθ + Qt * Qθθ))) :
    ricciJet (gowdyAlgJet t P Q L ⟨P, Pt, Pθ, Ptt, Ptθ, Pθθ⟩ ⟨Q, Qt, Qθ, Qtt, Qtθ, Qθθ⟩
      ⟨L, Lt, Lθ, Ltt, Ltθ, Lθθ⟩) 2 3 = 0 := by
  subst hPtt hQtt hLtt hLtθ hLθθ hLt hLθ
  have key : Real.exp (1 / 2 * L + -(1 / 2) * Real.log t) = Real.exp (L / 2) / Real.sqrt t := by
    rw [Real.exp_add, show -(1 / 2) * Real.log t = -(Real.log t / 2) by ring, Real.exp_neg,
      Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht]
    ring_nf
  have key2 : Real.exp (-1 * P) = (Real.exp P)⁻¹ := by rw [neg_one_mul, Real.exp_neg]
  have v0 : (![t, P, Q, L] : Fin 4 → ℝ) 0 = t := rfl
  have v1 : (![t, P, Q, L] : Fin 4 → ℝ) 1 = P := rfl
  have v2 : (![t, P, Q, L] : Fin 4 → ℝ) 2 = Q := rfl
  have v3 : (![t, P, Q, L] : Fin 4 → ℝ) 3 = L := rfl
  simp only [gowdyAlgJet, gowdyEntryJets, J2.exp, J2.add, J2.cmul, J2.mul, jClock, jLogClock,
    J2.zero, key, key2, gowdyInvMetric, v0, v1, v2, v3, Real.exp_neg]
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ t = s ^ 2 :=
    ⟨Real.sqrt t, Real.sqrt_pos.2 ht, (Real.sq_sqrt ht.le).symm⟩
  have hu := Real.exp_pos (L / 2)
  have he := Real.exp_pos P
  rw [Real.sqrt_sq hs.le]
  generalize Real.exp (L / 2) = u at hu ⊢
  generalize Real.exp P = e at he ⊢
  simp [ricciJet, ricci, riemann, christoffel, dChristoffel, dInvMetric, jetOfEntries,
    Fin.sum_univ_four]
  try field_simp
  try ring

/-- Component `(3,0)` of the algebraic vacuum identity. -/
theorem ricci_gowdy_alg_30 {t P Q L Pt Pθ Ptθ Pθθ Qt Qθ Qtθ Qθθ Ptt Qtt Lt Lθ Ltt Ltθ Lθθ : ℝ}
    (ht : 0 < t)
    (hPtt : Ptt = Pθθ - Pt / t + Real.exp P ^ 2 * (Qt ^ 2 - Qθ ^ 2))
    (hQtt : Qtt = Qθθ - Qt / t - 2 * Pt * Qt + 2 * Pθ * Qθ)
    (hLt : Lt = t * (Pt ^ 2 + Pθ ^ 2 + Real.exp P ^ 2 * (Qt ^ 2 + Qθ ^ 2)))
    (hLθ : Lθ = 2 * t * (Pt * Pθ + Real.exp P ^ 2 * Qt * Qθ))
    (hLtt : Ltt = (Pt ^ 2 + Pθ ^ 2 + Real.exp P ^ 2 * (Qt ^ 2 + Qθ ^ 2)) +
      t * (2 * Pt * Ptt + 2 * Pθ * Ptθ + 2 * Real.exp P ^ 2 * Pt * (Qt ^ 2 + Qθ ^ 2) +
        Real.exp P ^ 2 * (2 * Qt * Qtt + 2 * Qθ * Qtθ)))
    (hLtθ : Ltθ = t * (2 * Pt * Ptθ + 2 * Pθ * Pθθ + 2 * Real.exp P ^ 2 * Pθ * (Qt ^ 2 + Qθ ^ 2) +
        Real.exp P ^ 2 * (2 * Qt * Qtθ + 2 * Qθ * Qθθ)))
    (hLθθ : Lθθ = 2 * t * (Ptθ * Pθ + Pt * Pθθ + 2 * Real.exp P ^ 2 * Pθ * Qt * Qθ +
        Real.exp P ^ 2 * (Qtθ * Qθ + Qt * Qθθ))) :
    ricciJet (gowdyAlgJet t P Q L ⟨P, Pt, Pθ, Ptt, Ptθ, Pθθ⟩ ⟨Q, Qt, Qθ, Qtt, Qtθ, Qθθ⟩
      ⟨L, Lt, Lθ, Ltt, Ltθ, Lθθ⟩) 3 0 = 0 := by
  subst hPtt hQtt hLtt hLtθ hLθθ hLt hLθ
  have key : Real.exp (1 / 2 * L + -(1 / 2) * Real.log t) = Real.exp (L / 2) / Real.sqrt t := by
    rw [Real.exp_add, show -(1 / 2) * Real.log t = -(Real.log t / 2) by ring, Real.exp_neg,
      Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht]
    ring_nf
  have key2 : Real.exp (-1 * P) = (Real.exp P)⁻¹ := by rw [neg_one_mul, Real.exp_neg]
  have v0 : (![t, P, Q, L] : Fin 4 → ℝ) 0 = t := rfl
  have v1 : (![t, P, Q, L] : Fin 4 → ℝ) 1 = P := rfl
  have v2 : (![t, P, Q, L] : Fin 4 → ℝ) 2 = Q := rfl
  have v3 : (![t, P, Q, L] : Fin 4 → ℝ) 3 = L := rfl
  simp only [gowdyAlgJet, gowdyEntryJets, J2.exp, J2.add, J2.cmul, J2.mul, jClock, jLogClock,
    J2.zero, key, key2, gowdyInvMetric, v0, v1, v2, v3, Real.exp_neg]
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ t = s ^ 2 :=
    ⟨Real.sqrt t, Real.sqrt_pos.2 ht, (Real.sq_sqrt ht.le).symm⟩
  have hu := Real.exp_pos (L / 2)
  have he := Real.exp_pos P
  rw [Real.sqrt_sq hs.le]
  generalize Real.exp (L / 2) = u at hu ⊢
  generalize Real.exp P = e at he ⊢
  simp [ricciJet, ricci, riemann, christoffel, dChristoffel, dInvMetric, jetOfEntries,
    Fin.sum_univ_four]
  try field_simp
  try ring

/-- Component `(3,1)` of the algebraic vacuum identity. -/
theorem ricci_gowdy_alg_31 {t P Q L Pt Pθ Ptθ Pθθ Qt Qθ Qtθ Qθθ Ptt Qtt Lt Lθ Ltt Ltθ Lθθ : ℝ}
    (ht : 0 < t)
    (hPtt : Ptt = Pθθ - Pt / t + Real.exp P ^ 2 * (Qt ^ 2 - Qθ ^ 2))
    (hQtt : Qtt = Qθθ - Qt / t - 2 * Pt * Qt + 2 * Pθ * Qθ)
    (hLt : Lt = t * (Pt ^ 2 + Pθ ^ 2 + Real.exp P ^ 2 * (Qt ^ 2 + Qθ ^ 2)))
    (hLθ : Lθ = 2 * t * (Pt * Pθ + Real.exp P ^ 2 * Qt * Qθ))
    (hLtt : Ltt = (Pt ^ 2 + Pθ ^ 2 + Real.exp P ^ 2 * (Qt ^ 2 + Qθ ^ 2)) +
      t * (2 * Pt * Ptt + 2 * Pθ * Ptθ + 2 * Real.exp P ^ 2 * Pt * (Qt ^ 2 + Qθ ^ 2) +
        Real.exp P ^ 2 * (2 * Qt * Qtt + 2 * Qθ * Qtθ)))
    (hLtθ : Ltθ = t * (2 * Pt * Ptθ + 2 * Pθ * Pθθ + 2 * Real.exp P ^ 2 * Pθ * (Qt ^ 2 + Qθ ^ 2) +
        Real.exp P ^ 2 * (2 * Qt * Qtθ + 2 * Qθ * Qθθ)))
    (hLθθ : Lθθ = 2 * t * (Ptθ * Pθ + Pt * Pθθ + 2 * Real.exp P ^ 2 * Pθ * Qt * Qθ +
        Real.exp P ^ 2 * (Qtθ * Qθ + Qt * Qθθ))) :
    ricciJet (gowdyAlgJet t P Q L ⟨P, Pt, Pθ, Ptt, Ptθ, Pθθ⟩ ⟨Q, Qt, Qθ, Qtt, Qtθ, Qθθ⟩
      ⟨L, Lt, Lθ, Ltt, Ltθ, Lθθ⟩) 3 1 = 0 := by
  subst hPtt hQtt hLtt hLtθ hLθθ hLt hLθ
  have key : Real.exp (1 / 2 * L + -(1 / 2) * Real.log t) = Real.exp (L / 2) / Real.sqrt t := by
    rw [Real.exp_add, show -(1 / 2) * Real.log t = -(Real.log t / 2) by ring, Real.exp_neg,
      Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht]
    ring_nf
  have key2 : Real.exp (-1 * P) = (Real.exp P)⁻¹ := by rw [neg_one_mul, Real.exp_neg]
  have v0 : (![t, P, Q, L] : Fin 4 → ℝ) 0 = t := rfl
  have v1 : (![t, P, Q, L] : Fin 4 → ℝ) 1 = P := rfl
  have v2 : (![t, P, Q, L] : Fin 4 → ℝ) 2 = Q := rfl
  have v3 : (![t, P, Q, L] : Fin 4 → ℝ) 3 = L := rfl
  simp only [gowdyAlgJet, gowdyEntryJets, J2.exp, J2.add, J2.cmul, J2.mul, jClock, jLogClock,
    J2.zero, key, key2, gowdyInvMetric, v0, v1, v2, v3, Real.exp_neg]
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ t = s ^ 2 :=
    ⟨Real.sqrt t, Real.sqrt_pos.2 ht, (Real.sq_sqrt ht.le).symm⟩
  have hu := Real.exp_pos (L / 2)
  have he := Real.exp_pos P
  rw [Real.sqrt_sq hs.le]
  generalize Real.exp (L / 2) = u at hu ⊢
  generalize Real.exp P = e at he ⊢
  simp [ricciJet, ricci, riemann, christoffel, dChristoffel, dInvMetric, jetOfEntries,
    Fin.sum_univ_four]
  try field_simp
  try ring

/-- Component `(3,2)` of the algebraic vacuum identity. -/
theorem ricci_gowdy_alg_32 {t P Q L Pt Pθ Ptθ Pθθ Qt Qθ Qtθ Qθθ Ptt Qtt Lt Lθ Ltt Ltθ Lθθ : ℝ}
    (ht : 0 < t)
    (hPtt : Ptt = Pθθ - Pt / t + Real.exp P ^ 2 * (Qt ^ 2 - Qθ ^ 2))
    (hQtt : Qtt = Qθθ - Qt / t - 2 * Pt * Qt + 2 * Pθ * Qθ)
    (hLt : Lt = t * (Pt ^ 2 + Pθ ^ 2 + Real.exp P ^ 2 * (Qt ^ 2 + Qθ ^ 2)))
    (hLθ : Lθ = 2 * t * (Pt * Pθ + Real.exp P ^ 2 * Qt * Qθ))
    (hLtt : Ltt = (Pt ^ 2 + Pθ ^ 2 + Real.exp P ^ 2 * (Qt ^ 2 + Qθ ^ 2)) +
      t * (2 * Pt * Ptt + 2 * Pθ * Ptθ + 2 * Real.exp P ^ 2 * Pt * (Qt ^ 2 + Qθ ^ 2) +
        Real.exp P ^ 2 * (2 * Qt * Qtt + 2 * Qθ * Qtθ)))
    (hLtθ : Ltθ = t * (2 * Pt * Ptθ + 2 * Pθ * Pθθ + 2 * Real.exp P ^ 2 * Pθ * (Qt ^ 2 + Qθ ^ 2) +
        Real.exp P ^ 2 * (2 * Qt * Qtθ + 2 * Qθ * Qθθ)))
    (hLθθ : Lθθ = 2 * t * (Ptθ * Pθ + Pt * Pθθ + 2 * Real.exp P ^ 2 * Pθ * Qt * Qθ +
        Real.exp P ^ 2 * (Qtθ * Qθ + Qt * Qθθ))) :
    ricciJet (gowdyAlgJet t P Q L ⟨P, Pt, Pθ, Ptt, Ptθ, Pθθ⟩ ⟨Q, Qt, Qθ, Qtt, Qtθ, Qθθ⟩
      ⟨L, Lt, Lθ, Ltt, Ltθ, Lθθ⟩) 3 2 = 0 := by
  subst hPtt hQtt hLtt hLtθ hLθθ hLt hLθ
  have key : Real.exp (1 / 2 * L + -(1 / 2) * Real.log t) = Real.exp (L / 2) / Real.sqrt t := by
    rw [Real.exp_add, show -(1 / 2) * Real.log t = -(Real.log t / 2) by ring, Real.exp_neg,
      Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht]
    ring_nf
  have key2 : Real.exp (-1 * P) = (Real.exp P)⁻¹ := by rw [neg_one_mul, Real.exp_neg]
  have v0 : (![t, P, Q, L] : Fin 4 → ℝ) 0 = t := rfl
  have v1 : (![t, P, Q, L] : Fin 4 → ℝ) 1 = P := rfl
  have v2 : (![t, P, Q, L] : Fin 4 → ℝ) 2 = Q := rfl
  have v3 : (![t, P, Q, L] : Fin 4 → ℝ) 3 = L := rfl
  simp only [gowdyAlgJet, gowdyEntryJets, J2.exp, J2.add, J2.cmul, J2.mul, jClock, jLogClock,
    J2.zero, key, key2, gowdyInvMetric, v0, v1, v2, v3, Real.exp_neg]
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ t = s ^ 2 :=
    ⟨Real.sqrt t, Real.sqrt_pos.2 ht, (Real.sq_sqrt ht.le).symm⟩
  have hu := Real.exp_pos (L / 2)
  have he := Real.exp_pos P
  rw [Real.sqrt_sq hs.le]
  generalize Real.exp (L / 2) = u at hu ⊢
  generalize Real.exp P = e at he ⊢
  simp [ricciJet, ricci, riemann, christoffel, dChristoffel, dInvMetric, jetOfEntries,
    Fin.sum_univ_four]
  try field_simp
  try ring

/-- Component `(3,3)` of the algebraic vacuum identity. -/
theorem ricci_gowdy_alg_33 {t P Q L Pt Pθ Ptθ Pθθ Qt Qθ Qtθ Qθθ Ptt Qtt Lt Lθ Ltt Ltθ Lθθ : ℝ}
    (ht : 0 < t)
    (hPtt : Ptt = Pθθ - Pt / t + Real.exp P ^ 2 * (Qt ^ 2 - Qθ ^ 2))
    (hQtt : Qtt = Qθθ - Qt / t - 2 * Pt * Qt + 2 * Pθ * Qθ)
    (hLt : Lt = t * (Pt ^ 2 + Pθ ^ 2 + Real.exp P ^ 2 * (Qt ^ 2 + Qθ ^ 2)))
    (hLθ : Lθ = 2 * t * (Pt * Pθ + Real.exp P ^ 2 * Qt * Qθ))
    (hLtt : Ltt = (Pt ^ 2 + Pθ ^ 2 + Real.exp P ^ 2 * (Qt ^ 2 + Qθ ^ 2)) +
      t * (2 * Pt * Ptt + 2 * Pθ * Ptθ + 2 * Real.exp P ^ 2 * Pt * (Qt ^ 2 + Qθ ^ 2) +
        Real.exp P ^ 2 * (2 * Qt * Qtt + 2 * Qθ * Qtθ)))
    (hLtθ : Ltθ = t * (2 * Pt * Ptθ + 2 * Pθ * Pθθ + 2 * Real.exp P ^ 2 * Pθ * (Qt ^ 2 + Qθ ^ 2) +
        Real.exp P ^ 2 * (2 * Qt * Qtθ + 2 * Qθ * Qθθ)))
    (hLθθ : Lθθ = 2 * t * (Ptθ * Pθ + Pt * Pθθ + 2 * Real.exp P ^ 2 * Pθ * Qt * Qθ +
        Real.exp P ^ 2 * (Qtθ * Qθ + Qt * Qθθ))) :
    ricciJet (gowdyAlgJet t P Q L ⟨P, Pt, Pθ, Ptt, Ptθ, Pθθ⟩ ⟨Q, Qt, Qθ, Qtt, Qtθ, Qθθ⟩
      ⟨L, Lt, Lθ, Ltt, Ltθ, Lθθ⟩) 3 3 = 0 := by
  subst hPtt hQtt hLtt hLtθ hLθθ hLt hLθ
  have key : Real.exp (1 / 2 * L + -(1 / 2) * Real.log t) = Real.exp (L / 2) / Real.sqrt t := by
    rw [Real.exp_add, show -(1 / 2) * Real.log t = -(Real.log t / 2) by ring, Real.exp_neg,
      Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht]
    ring_nf
  have key2 : Real.exp (-1 * P) = (Real.exp P)⁻¹ := by rw [neg_one_mul, Real.exp_neg]
  have v0 : (![t, P, Q, L] : Fin 4 → ℝ) 0 = t := rfl
  have v1 : (![t, P, Q, L] : Fin 4 → ℝ) 1 = P := rfl
  have v2 : (![t, P, Q, L] : Fin 4 → ℝ) 2 = Q := rfl
  have v3 : (![t, P, Q, L] : Fin 4 → ℝ) 3 = L := rfl
  simp only [gowdyAlgJet, gowdyEntryJets, J2.exp, J2.add, J2.cmul, J2.mul, jClock, jLogClock,
    J2.zero, key, key2, gowdyInvMetric, v0, v1, v2, v3, Real.exp_neg]
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ t = s ^ 2 :=
    ⟨Real.sqrt t, Real.sqrt_pos.2 ht, (Real.sq_sqrt ht.le).symm⟩
  have hu := Real.exp_pos (L / 2)
  have he := Real.exp_pos P
  rw [Real.sqrt_sq hs.le]
  generalize Real.exp (L / 2) = u at hu ⊢
  generalize Real.exp P = e at he ⊢
  simp [ricciJet, ricci, riemann, christoffel, dChristoffel, dInvMetric, jetOfEntries,
    Fin.sum_univ_four]
  try field_simp
  try ring


/-- **Algebraic vacuum identity**: the Ricci tensor of the Gowdy metric 2-jet vanishes when the
jets of `P, Q, λ` satisfy the second-order frame relations and the `λ` constraints. -/
theorem ricci_gowdy_algebraic {t P Q L Pt Pθ Ptθ Pθθ Qt Qθ Qtθ Qθθ Ptt Qtt Lt Lθ Ltt Ltθ Lθθ : ℝ}
    (ht : 0 < t)
    (hPtt : Ptt = Pθθ - Pt / t + Real.exp P ^ 2 * (Qt ^ 2 - Qθ ^ 2))
    (hQtt : Qtt = Qθθ - Qt / t - 2 * Pt * Qt + 2 * Pθ * Qθ)
    (hLt : Lt = t * (Pt ^ 2 + Pθ ^ 2 + Real.exp P ^ 2 * (Qt ^ 2 + Qθ ^ 2)))
    (hLθ : Lθ = 2 * t * (Pt * Pθ + Real.exp P ^ 2 * Qt * Qθ))
    (hLtt : Ltt = (Pt ^ 2 + Pθ ^ 2 + Real.exp P ^ 2 * (Qt ^ 2 + Qθ ^ 2)) +
      t * (2 * Pt * Ptt + 2 * Pθ * Ptθ + 2 * Real.exp P ^ 2 * Pt * (Qt ^ 2 + Qθ ^ 2) +
        Real.exp P ^ 2 * (2 * Qt * Qtt + 2 * Qθ * Qtθ)))
    (hLtθ : Ltθ = t * (2 * Pt * Ptθ + 2 * Pθ * Pθθ + 2 * Real.exp P ^ 2 * Pθ * (Qt ^ 2 + Qθ ^ 2) +
        Real.exp P ^ 2 * (2 * Qt * Qtθ + 2 * Qθ * Qθθ)))
    (hLθθ : Lθθ = 2 * t * (Ptθ * Pθ + Pt * Pθθ + 2 * Real.exp P ^ 2 * Pθ * Qt * Qθ +
        Real.exp P ^ 2 * (Qtθ * Qθ + Qt * Qθθ))) :
    ricciJet (gowdyAlgJet t P Q L ⟨P, Pt, Pθ, Ptt, Ptθ, Pθθ⟩ ⟨Q, Qt, Qθ, Qtt, Qtθ, Qθθ⟩
      ⟨L, Lt, Lθ, Ltt, Ltθ, Lθθ⟩) = 0 := by
  funext b d
  fin_cases b <;> fin_cases d
  · exact ricci_gowdy_alg_00 ht hPtt hQtt hLt hLθ hLtt hLtθ hLθθ
  · exact ricci_gowdy_alg_01 ht hPtt hQtt hLt hLθ hLtt hLtθ hLθθ
  · exact ricci_gowdy_alg_02 ht hPtt hQtt hLt hLθ hLtt hLtθ hLθθ
  · exact ricci_gowdy_alg_03 ht hPtt hQtt hLt hLθ hLtt hLtθ hLθθ
  · exact ricci_gowdy_alg_10 ht hPtt hQtt hLt hLθ hLtt hLtθ hLθθ
  · exact ricci_gowdy_alg_11 ht hPtt hQtt hLt hLθ hLtt hLtθ hLθθ
  · exact ricci_gowdy_alg_12 ht hPtt hQtt hLt hLθ hLtt hLtθ hLθθ
  · exact ricci_gowdy_alg_13 ht hPtt hQtt hLt hLθ hLtt hLtθ hLθθ
  · exact ricci_gowdy_alg_20 ht hPtt hQtt hLt hLθ hLtt hLtθ hLθθ
  · exact ricci_gowdy_alg_21 ht hPtt hQtt hLt hLθ hLtt hLtθ hLθθ
  · exact ricci_gowdy_alg_22 ht hPtt hQtt hLt hLθ hLtt hLtθ hLθθ
  · exact ricci_gowdy_alg_23 ht hPtt hQtt hLt hLθ hLtt hLtθ hLθθ
  · exact ricci_gowdy_alg_30 ht hPtt hQtt hLt hLθ hLtt hLtθ hLθθ
  · exact ricci_gowdy_alg_31 ht hPtt hQtt hLt hLθ hLtt hLtθ hLθθ
  · exact ricci_gowdy_alg_32 ht hPtt hQtt hLt hLθ hLtt hLtθ hLθθ
  · exact ricci_gowdy_alg_33 ht hPtt hQtt hLt hLθ hLtt hLtθ hLθθ


end

end RenewalGeometry.GowdyStaggered.HermiteReadout
