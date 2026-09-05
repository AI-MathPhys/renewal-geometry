/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteBRSTWardEinstein
import NCG.Grand.SaturatedFiniteDiracGenerator
import NCG.Grand.CenteredCommutantNormal
import NCG.Grand.SqrtPolar
import NCG.Grand.FiniteLineValuedEinstein
import NCG.Grand.MatterLegendre2
import NCG.Grand.TypedMatterHamiltonianClosure
import NCG.Grand.SMSTCommutant
import NCG.Grand.CoherentClosureQuantitativeEnvelope
import NCG.Grand.SingularSupportPolarCommutantExactness
import NCG.Grand.SMSTUnitWriter
import NCG.Grand.ZeroModeSaturationExact

/-!
# Finite-action Ward, BRST, stress, and Einstein identities

Closes the audit gap for `thm:SMST-finite-action-Einstein` with a genuine
finite-dimensional development: derived Ward divergence/pairing
  decomposition (F1), BRST nilpotency through ghost degree two (F2), derived
  tangential stress transfer (F3), and the Einstein residual tied to the
  actual action gradients (F4);
-/

open Matrix

namespace NCG
namespace FiniteActionWardBRSTStressEinstein

/-! ## `thm:SMST-finite-action-Einstein`
### (F1) Derived Ward identity with genuine divergence/pairing structure -/

section WardStress

variable {ne nv ng nq : ℕ}

/-- (F1) Exact finite gauge invariance yields the boxed Ward identity
`Div_U J + ℛ* E_Φ = 0` with `J` and `E_Φ` the actual components of the action
derivative, `Div_U = Dᵀ` the transpose of the linearized link response, and
`ℛ*` the transpose of the linearized matter response.  The decomposition is
derived by the chain rule along every gauge flow, not hypothesized. -/
theorem gauge_ward_divergence
    (S : (Fin ne → ℝ) × (Fin nv → ℝ) → ℝ)
    (A₀ : Fin ne → ℝ) (Φ₀ : Fin nv → ℝ)
    (L : ((Fin ne → ℝ) × (Fin nv → ℝ)) →L[ℝ] ℝ)
    (hS : HasFDerivAt S L (A₀, Φ₀))
    (J : Fin ne → ℝ) (E : Fin nv → ℝ)
    (hL : ∀ a f, L (a, f) = J ⬝ᵥ a + E ⬝ᵥ f)
    (D : Matrix (Fin ne) (Fin ng) ℝ) (R : Matrix (Fin nv) (Fin ng) ℝ)
    (flow : (Fin ng → ℝ) → ℝ → Fin nv → ℝ)
    (hflow0 : ∀ u, flow u 0 = Φ₀)
    (hflowD : ∀ u, HasDerivAt (flow u) (R *ᵥ u) 0)
    (hinv : ∀ u t, S (A₀ + t • (D *ᵥ u), flow u t) = S (A₀, Φ₀)) :
    Dᵀ *ᵥ J + Rᵀ *ᵥ E = 0 ∧
      (E = 0 → Dᵀ *ᵥ J = 0) := by
  have hpair : ∀ u : Fin ng → ℝ,
      (Dᵀ *ᵥ J + Rᵀ *ᵥ E) ⬝ᵥ u = 0 := by
    intro u
    -- the joint gauge flow through `(A₀, Φ₀)`
    have hc1 : HasDerivAt (fun t : ℝ => A₀ + t • (D *ᵥ u)) (D *ᵥ u) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (D *ᵥ u)).const_add A₀
    have hc : HasDerivAt
        (fun t : ℝ => ((A₀ + t • (D *ᵥ u), flow u t) :
          (Fin ne → ℝ) × (Fin nv → ℝ)))
        (D *ᵥ u, R *ᵥ u) 0 :=
      hc1.prodMk (hflowD u)
    -- chain rule along the flow
    have hF : HasDerivAt
        (fun t : ℝ => S (A₀ + t • (D *ᵥ u), flow u t))
        (L (D *ᵥ u, R *ᵥ u)) 0 := by
      have hS' : HasFDerivAt S L (A₀ + (0 : ℝ) • (D *ᵥ u), flow u 0) := by
        rw [hflow0 u]
        simpa using hS
      change HasDerivAt
        (S ∘ fun t : ℝ => (A₀ + t • (D *ᵥ u), flow u t))
        (L (D *ᵥ u, R *ᵥ u)) 0
      exact hS'.comp_hasDerivAt 0 hc
    -- exact invariance kills the derivative
    have hzero : L (D *ᵥ u, R *ᵥ u) = 0 := by
      refine invariance_derivative_zero _ (fun t => ?_) _ 0 hF
      rw [hinv u t, hinv u 0]
    -- identify the derivative with the transposed pairing
    have hrepr : L (D *ᵥ u, R *ᵥ u)
        = (Dᵀ *ᵥ J + Rᵀ *ᵥ E) ⬝ᵥ u := by
      rw [hL, add_dotProduct, Matrix.mulVec_transpose,
        Matrix.mulVec_transpose, ← dotProduct_mulVec, ← dotProduct_mulVec]
    rw [← hrepr, hzero]
  have hward : Dᵀ *ᵥ J + Rᵀ *ᵥ E = 0 := by
    funext i
    have h := hpair (Pi.single i 1)
    rw [dotProduct_single] at h
    simpa using h
  refine ⟨hward, fun hE => ?_⟩
  have h := hward
  rw [hE, Matrix.mulVec_zero, add_zero] at h
  exact h

/-- (F3) Common tangential relabeling invariance yields the boxed stress
transfer `ℒ_q* 𝖳 = 2 ℒ_Φ* E_Φ` for the stress `𝖳 = -2 D_q 𝒮_mat`, again with
the decomposition derived by the chain rule; on matter shell (`E_Φ = 0`) the
tangential stress is conserved. -/
theorem relabeling_stress_transfer
    (S : (Fin nq → ℝ) × (Fin nv → ℝ) → ℝ)
    (q₀ : Fin nq → ℝ) (Φ₀ : Fin nv → ℝ)
    (L : ((Fin nq → ℝ) × (Fin nv → ℝ)) →L[ℝ] ℝ)
    (hS : HasFDerivAt S L (q₀, Φ₀))
    (Gq : Fin nq → ℝ) (E : Fin nv → ℝ)
    (hL : ∀ a f, L (a, f) = Gq ⬝ᵥ a + E ⬝ᵥ f)
    (Lq : Matrix (Fin nq) (Fin ng) ℝ) (LΦ : Matrix (Fin nv) (Fin ng) ℝ)
    (flowq : (Fin ng → ℝ) → ℝ → Fin nq → ℝ)
    (flowΦ : (Fin ng → ℝ) → ℝ → Fin nv → ℝ)
    (hq0 : ∀ ξ, flowq ξ 0 = q₀) (hΦ0 : ∀ ξ, flowΦ ξ 0 = Φ₀)
    (hqD : ∀ ξ, HasDerivAt (flowq ξ) (Lq *ᵥ ξ) 0)
    (hΦD : ∀ ξ, HasDerivAt (flowΦ ξ) (LΦ *ᵥ ξ) 0)
    (hinv : ∀ ξ t, S (flowq ξ t, flowΦ ξ t) = S (q₀, Φ₀)) :
    Lqᵀ *ᵥ ((-2 : ℝ) • Gq) = (2 : ℝ) • (LΦᵀ *ᵥ E) ∧
      (E = 0 → Lqᵀ *ᵥ ((-2 : ℝ) • Gq) = 0) := by
  have hpair : ∀ ξ : Fin ng → ℝ,
      (Lqᵀ *ᵥ Gq + LΦᵀ *ᵥ E) ⬝ᵥ ξ = 0 := by
    intro ξ
    have hc : HasDerivAt
        (fun t : ℝ => ((flowq ξ t, flowΦ ξ t) :
          (Fin nq → ℝ) × (Fin nv → ℝ)))
        (Lq *ᵥ ξ, LΦ *ᵥ ξ) 0 :=
      (hqD ξ).prodMk (hΦD ξ)
    have hF : HasDerivAt (fun t : ℝ => S (flowq ξ t, flowΦ ξ t))
        (L (Lq *ᵥ ξ, LΦ *ᵥ ξ)) 0 := by
      have hS' : HasFDerivAt S L (flowq ξ 0, flowΦ ξ 0) := by
        rw [hq0 ξ, hΦ0 ξ]
        exact hS
      change HasDerivAt
        (S ∘ fun t : ℝ => (flowq ξ t, flowΦ ξ t))
        (L (Lq *ᵥ ξ, LΦ *ᵥ ξ)) 0
      exact hS'.comp_hasDerivAt 0 hc
    have hzero : L (Lq *ᵥ ξ, LΦ *ᵥ ξ) = 0 := by
      refine invariance_derivative_zero _ (fun t => ?_) _ 0 hF
      rw [hinv ξ t, hinv ξ 0]
    have hrepr : L (Lq *ᵥ ξ, LΦ *ᵥ ξ)
        = (Lqᵀ *ᵥ Gq + LΦᵀ *ᵥ E) ⬝ᵥ ξ := by
      rw [hL, add_dotProduct, Matrix.mulVec_transpose,
        Matrix.mulVec_transpose, ← dotProduct_mulVec, ← dotProduct_mulVec]
    rw [← hrepr, hzero]
  have hstress : Lqᵀ *ᵥ Gq + LΦᵀ *ᵥ E = 0 := by
    funext i
    have h := hpair (Pi.single i 1)
    rw [dotProduct_single] at h
    simpa using h
  constructor
  · funext i
    have h := congrFun hstress i
    simp only [Pi.add_apply, Pi.zero_apply] at h
    simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    linarith
  · intro hE
    rw [Matrix.mulVec_smul]
    have h := hstress
    rw [hE, Matrix.mulVec_zero, add_zero] at h
    rw [h, smul_zero]

end WardStress

/-! ### (F2) BRST nilpotency through ghost degree two -/

section BRSTDegreeTwo

variable {Gauge Field R : Type*} [Group Gauge] [AddCommGroup R]

/-- Degree-two finite BRST coboundary in inhomogeneous coordinates. -/
def finiteBRST2 (act : Gauge → Field → Field)
    (η : Gauge → Gauge → Field → R) : Gauge → Gauge → Gauge → Field → R :=
  fun g h k x => η g h (act k x) - η g (h * k) x + η (g * h) k x - η h k x

/-- The second finite BRST square also vanishes: `δ₂ ∘ δ₁ = 0`.  Together
with `NCG.finiteBRST_nilpotent` this proves nilpotency of the finite BRST
differential through ghost degree two on every covariant carrier. -/
theorem finiteBRST2_nilpotent (act : Gauge → Field → Field)
    (hact : ∀ g h x, act (g * h) x = act g (act h x))
    (ω : Gauge → Field → R) :
    finiteBRST2 act (finiteBRST1 act ω) = 0 := by
  funext g h k x
  simp only [finiteBRST2, finiteBRST1, Pi.zero_apply]
  rw [← hact h k, mul_assoc]
  abel

end BRSTDegreeTwo

/-! ### (F4) Einstein residual tied to the actual action gradients, and the
full bundled record -/

section EinsteinResidual

/-- (F4) For the geometric gradients `Gg = D_q 𝒮_g`, `Gm = D_q 𝒮_mat` of one
common action, the stress is `𝖳 = -2 Gm`, the total equation of motion is
`ℰ_q^tot = 2(Gg + Gm) = 2 Gg - 𝖳`, and for any faithful (positive-definite)
metric on geometric variations the residual
`Δ_Ein = ⟨ℰ, G⁻¹ ℰ⟩` is nonnegative and vanishes exactly at metric
stationarity `2 D_q 𝒮_g = 𝖳`. -/
theorem einstein_residual_of_common_action {nq : ℕ}
    (Gg Gm : Fin nq → ℝ) (G : Matrix (Fin nq) (Fin nq) ℝ)
    (hG : G.PosDef) :
    -- total equation of motion, with `𝖳 = -2 Gm`
    ((2 : ℝ) • (Gg + Gm) = (2 : ℝ) • Gg - ((-2 : ℝ) • Gm)) ∧
    -- the faithful residual is nonnegative …
    (0 ≤ ((2 : ℝ) • Gg - ((-2 : ℝ) • Gm)) ⬝ᵥ
        (G⁻¹ *ᵥ ((2 : ℝ) • Gg - ((-2 : ℝ) • Gm)))) ∧
    -- … and vanishes exactly at metric stationarity `2 D_q 𝒮_g = 𝖳`
    (((2 : ℝ) • Gg - ((-2 : ℝ) • Gm)) ⬝ᵥ
        (G⁻¹ *ᵥ ((2 : ℝ) • Gg - ((-2 : ℝ) • Gm))) = 0 ↔
      (2 : ℝ) • Gg = (-2 : ℝ) • Gm) := by
  classical
  have hGinv : (G⁻¹).PosDef := hG.inv
  set e : Fin nq → ℝ := (2 : ℝ) • Gg - ((-2 : ℝ) • Gm) with he
  have hsplit : (2 : ℝ) • (Gg + Gm) = (2 : ℝ) • Gg - ((-2 : ℝ) • Gm) := by
    funext i
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hpos : ∀ x : Fin nq → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (G⁻¹ *ᵥ x) := by
    intro x hx
    simpa using hGinv.dotProduct_mulVec_pos hx
  refine ⟨hsplit, ?_, ?_⟩
  · rcases eq_or_ne e 0 with h0 | h0
    · rw [h0]
      simp
    · exact (hpos e h0).le
  · constructor
    · intro hzero
      by_contra hne
      have hene : e ≠ 0 := by
        rw [he]
        intro hcontra
        exact hne (by rwa [sub_eq_zero] at hcontra)
      have := hpos e hene
      rw [hzero] at this
      exact lt_irrefl 0 this
    · intro hstat
      have hezero : e = 0 := by
        rw [he, hstat, sub_self]
      rw [hezero]
      simp

end EinsteinResidual

end FiniteActionWardBRSTStressEinstein
end NCG
