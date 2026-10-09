/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactShiftWardEnvelope
import RenewalGeometry.Action.ExactActionProvenance
import RenewalGeometry.Gravity.ShiftWardPacket

/-!
# The constant-shift Ward packet of the literal canonical Hamiltonian
  (`lem:supp-exact-ward-orders`, `thm:supp-exact-harmonic-q4-zero`,
  `eq:supp-exact-ward-objects`, `eq:supp-exact-ward-mass-order`,
  `eq:supp-exact-harmonic-mass-column`, `eq:supp-exact-pure-harmonic-ray`;
  emergent-spacetime manuscript)

The Hamiltonian is the literal `𝓗_h` of the explicit action (`ExactShiftWard.Hlit`: Λ = 0,
symmetric-square-root triad, selected stationary connection, Legendre chart at flat data), in the
chart `X = (u, p)` (`γ = I + u`, `π = p`), `λ = (N, β)`, base point `(0, e)`, `e = (1, 0)`.

* `Jlit`: the symplectic Riesz map of the grid pairing `⟨·,·⟩_h` (`Sym₃` weights `1, 2`), so that
  `canF Hlit Jlit = 𝕁∇_X 𝓗_h` is `F^can` of `ExactActionProvenance.Fcan` (`canF_eq_Fcan`).
* `Blit c`: the bilinear form of `P_{c,2}(u, p) = ⟨p, δ_c u⟩_h`.
* `gradQ_Jlit` (Riesz + skew-adjointness of `δ_c`): `DP_{c,2}(Y)[𝕁ℓ] = -ℓ(δ_c Y)`; hence the
  quadratic constant-shift forms Poisson-commute (`comm_lit`, `[δ_c, δ_d] = 0`).
* **`shiftStructure_lit`**: the literal Hamiltonian has the shift structure of
  `ShiftWardPacket.ShiftStructure` (from `ExactShiftWard.Prow_eq`, `Qrow_isBigO`).
* `K1_lit`: the linear first-Poisson coefficient at a first field `Y` is
  `-Λ_μ(D𝒞_h(0)[δ_cY])`; it vanishes when `Y` solves the linearized constraints
  `R₁(Y_u) = 0`, `δ_jY_p^{ja} = 0` (`D𝒞_h(0)Y = 0`), because `δ_c` commutes with `D𝒞_h(0)`.
* **`wardPacketRay_lit`**: the full constant-shift Ward packet (`WardPacketRay`) of the literal
  Hamiltonian along any constraint-tangent first field.
* **`ward_orders_lit`** (`lem:supp-exact-ward-orders`) and **`harmonic_q4_zero_lit`**
  (`thm:supp-exact-harmonic-q4-zero`) for the literal Hamiltonian.

Disclosed renderings: general `χ ≠ 0` (the manuscript's normalization is `χ = 1`), the
symmetric-square-root triad, the regulator chart `hR ≤ ε` of `ExactActionProvenance`, and the
first field `Y` of the base family is constraint-tangent (`D𝒞_h(0)Y = 0`; the paper's first field
is the first jet of the joint constraint initializer `eq:supp-exact-joint-initializer`).
-/

open Filter Finset Metric Asymptotics
open scoped Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace RenewalGeometry.ExactPhaseAction.ShiftWard

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

open PalatiniEinsteinAlgebra OddPhaseDerivativeReal QuadJet
open ShiftWardPacket WardOrders HarmonicQuartic

variable {N : ℕ} [NeZero N]

/-! ### Pairing algebra -/

theorem frob_wt6 (a b : Fin 6 → ℝ) :
    ∑ i, ∑ j, symMat a i j * symMat b i j = ∑ k, wt6 k * a k * b k := by
  simp [symMat, InitialConstraintLinearRange.sym6, Fin.sum_univ_three, Fin.sum_univ_six, wt6]
  ring

theorem pairH_eq_wt6 (a b : MetF N) : pairH a b = hN N ^ 3 * ∑ x, ∑ k, wt6 k * a x k * b x k := by
  simp only [pairH, frob_wt6]

theorem pairH_comm (a b : MetF N) : pairH a b = pairH b a := by
  simp only [pairH_eq_wt6]
  congr 1
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun k _ => by ring

theorem dcMet_add (c : Fin 3 → ℝ) (u v : MetF N) : dcMet c (u + v) = dcMet c u + dcMet c v := by
  funext x; simp [dcMet, map_add, Finset.sum_add_distrib, smul_add]

theorem dcMet_smul (c : Fin 3 → ℝ) (t : ℝ) (u : MetF N) : dcMet c (t • u) = t • dcMet c u := by
  funext x; simp [dcMet, map_smul, Finset.smul_sum, smul_comm t]

theorem dcMet_neg (c : Fin 3 → ℝ) (u : MetF N) : dcMet c (-u) = -dcMet c u := by
  have := dcMet_smul c (-1) u; simpa using this

/-- The weighted site pairing `Σ_k w_k a_k b_k`. -/
def siteB : (Fin 6 → ℝ) →ₗ[ℝ] (Fin 6 → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun a b => ∑ k, wt6 k * a k * b k)
    (fun a a' b => by simp [Finset.sum_add_distrib, add_mul, mul_add])
    (fun t a b => by simp [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring)
    (fun a b b' => by simp [Finset.sum_add_distrib, mul_add])
    (fun t a b => by simp [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring)

theorem pairH_eq_siteB (a b : MetF N) : pairH a b = hN N ^ 3 * ∑ x, siteB (a x) (b x) := by
  simp [pairH_eq_wt6, siteB]

/-- `δ_c` is skew-adjoint for the grid pairing. -/
theorem pairH_dcMet_skew (c : Fin 3 → ℝ) (a b : MetF N) :
    pairH (dcMet c a) b = -pairH a (dcMet c b) := by
  simp only [pairH_eq_siteB, dcMet, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun x j => c j * (siteB (a x)) (pd j b x))]
  simp only [← Finset.mul_sum, pd_skew _ siteB]
  rw [← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The phase derivatives commute: `δ_cδ_d = δ_dδ_c`. -/
theorem dcMet_comm (c d : Fin 3 → ℝ) (u : MetF N) : dcMet c (dcMet d u) = dcMet d (dcMet c u) := by
  have hpd : ∀ k, pd k (dcMet d u) = ∑ j, d j • pd k (pd j u) := by
    intro k
    have : dcMet d u = ∑ j, d j • pd j u := by funext x; simp [dcMet, Finset.sum_apply]
    rw [this, map_sum]; simp [map_smul]
  have hpc : ∀ k, pd k (dcMet c u) = ∑ j, c j • pd k (pd j u) := by
    intro k
    have : dcMet c u = ∑ j, c j • pd j u := by funext x; simp [dcMet, Finset.sum_apply]
    rw [this, map_sum]; simp [map_smul]
  funext x
  simp only [dcMet, hpd, hpc, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [pd_comm, mul_comm]

/-! ### The symplectic Riesz map and the quadratic constant-shift form -/

/-- The `⟨·,·⟩_h`-Riesz representative of a functional on metric fields. -/
def rieszV (f : MetF N → ℝ) : MetF N := fun x k => (hN N ^ 3 * wt6 k)⁻¹ * f (metDir x k)

theorem eq_sum_metDir (v : MetF N) : v = ∑ x, ∑ k, v x k • metDir x k := by
  funext y m
  simp only [metDir, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  rw [Finset.sum_eq_single y (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  rw [Finset.sum_eq_single m (fun k _ hk => by simp [Ne.symm hk]) (by simp)]
  simp

theorem wt6_ne_zero (k : Fin 6) : wt6 k ≠ 0 := by fin_cases k <;> norm_num [wt6]

/-- **Riesz identity**: `⟨rieszV g, v⟩_h = g v`. -/
theorem pairH_rieszV (g : MetF N →L[ℝ] ℝ) (v : MetF N) : pairH (rieszV (fun w => g w)) v = g v := by
  have hh : hN N ≠ 0 := hN_ne_zero
  rw [pairH_eq_wt6]
  conv_rhs => rw [eq_sum_metDir v]
  simp only [map_sum, map_smul, smul_eq_mul, rieszV, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun k _ => ?_
  have hw := wt6_ne_zero k
  field_simp

theorem pairH_neg_left (a b : MetF N) : pairH (-a) b = -pairH a b := by
  rw [← pairCov_apply, ← pairCov_apply, map_neg]; rfl

theorem pairH_add_left (a a' b : MetF N) : pairH (a + a') b = pairH a b + pairH a' b := by
  rw [← pairCov_apply, ← pairCov_apply, ← pairCov_apply, map_add]; rfl

theorem pairH_add_right (a b b' : MetF N) : pairH a (b + b') = pairH a b + pairH a b' := by
  rw [← pairCov_apply, ← pairCov_apply, ← pairCov_apply, map_add]

theorem pairH_smul_left (t : ℝ) (a b : MetF N) : pairH (t • a) b = t * pairH a b := by
  rw [← pairCov_apply, ← pairCov_apply, map_smul]; rfl

theorem pairH_smul_right (t : ℝ) (a b : MetF N) : pairH a (t • b) = t * pairH a b := by
  rw [← pairCov_apply, ← pairCov_apply, map_smul]; rfl

/-- **The symplectic Riesz map** `ℓ ↦ (∇_p ℓ, -∇_u ℓ)` for `⟨·,·⟩_h`, so that `𝕁∇_X𝓗_h = Jlit(D_X𝓗_h)`. -/
def Jlit : (Xs N →L[ℝ] ℝ) →L[ℝ] Xs N :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ℓ => (rieszV (fun v => ℓ (0, v)), -rieszV (fun v => ℓ (v, 0)))
      map_add' := fun ℓ ℓ' => by
        ext x k <;> simp [rieszV, mul_add] <;> ring
      map_smul' := fun t ℓ => by
        ext x k <;> simp [rieszV] <;> ring }

theorem Jlit_fst (ℓ : Xs N →L[ℝ] ℝ) : (Jlit ℓ).1 = rieszV (fun v => ℓ (0, v)) := rfl

theorem Jlit_snd (ℓ : Xs N →L[ℝ] ℝ) : (Jlit ℓ).2 = -rieszV (fun v => ℓ (v, 0)) := rfl

/-- **The bilinear form of `P_{c,2}(u, p) = ⟨p, δ_c u⟩_h`.** -/
def Blit (c : Fin 3 → ℝ) : Xs N →L[ℝ] Xs N →L[ℝ] ℝ :=
  toCLM₂ (LinearMap.mk₂ ℝ (fun X X' : Xs N => pairH X'.2 (dcMet c X.1))
    (fun X Y X' => by simp [dcMet_add, pairH_add_right])
    (fun t X X' => by simp [dcMet_smul, pairH_smul_right])
    (fun X X' Y' => by simp [pairH_add_left])
    (fun t X X' => by simp [pairH_smul_left]))

theorem Blit_apply (c : Fin 3 → ℝ) (X X' : Xs N) : Blit c X X' = pairH X'.2 (dcMet c X.1) := rfl

theorem Blit_diag (c : Fin 3 → ℝ) (X : Xs N) : Blit c X X = qShift c X := rfl

/-- **`DP_{c,2}(Y)[𝕁ℓ] = -ℓ(δ_c Y)`** (Riesz identity and skew-adjointness of `δ_c`). -/
theorem gradQ_Jlit (c : Fin 3 → ℝ) (Y : Xs N) (ℓ : Xs N →L[ℝ] ℝ) :
    gradQ (Blit c) Y (Jlit ℓ) = -ℓ (dcMet c Y.1, dcMet c Y.2) := by
  simp only [gradQ, ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply, Blit_apply,
    Jlit_fst, Jlit_snd]
  have h1 : pairH (-rieszV (fun v => ℓ (v, 0))) (dcMet c Y.1) = -ℓ (dcMet c Y.1, 0) := by
    rw [pairH_neg_left]
    have := pairH_rieszV (ℓ.comp (ContinuousLinearMap.inl ℝ (MetF N) (MetF N))) (dcMet c Y.1)
    simpa using congrArg Neg.neg this
  have h2 : pairH Y.2 (dcMet c (rieszV (fun v => ℓ (0, v)))) = -ℓ (0, dcMet c Y.2) := by
    have hs := pairH_dcMet_skew c Y.2 (rieszV (fun v => ℓ (0, v)))
    rw [pairH_comm (dcMet c Y.2)] at hs
    have hr := pairH_rieszV (ℓ.comp (ContinuousLinearMap.inr ℝ (MetF N) (MetF N))) (dcMet c Y.2)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] at hr
    linarith
  rw [h1, h2]
  have : ((dcMet c Y.1, dcMet c Y.2) : Xs N) = (dcMet c Y.1, 0) + (0, dcMet c Y.2) := by simp
  rw [this, map_add]
  ring

/-- **The quadratic constant-shift forms Poisson-commute** (`[δ_c, δ_d] = 0`). -/
theorem comm_lit (c d : Fin 3 → ℝ) (X : Xs N) :
    gradQ (Blit c) X (Jlit (gradQ (Blit d) X)) = 0 := by
  rw [gradQ_Jlit]
  simp only [gradQ, ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply, Blit_apply]
  rw [pairH_dcMet_skew, dcMet_comm]
  ring

/-! ### `δ_c` commutes with the linearized constraint rows -/

theorem symMat_dcMet (c : Fin 3 → ℝ) (u : MetF N) (y : Site N) (i j : Fin 3) :
    symMat (dcMet c u y) i j = ∑ k, c k * pd k (fun y' => symMat (u y') i j) y := by
  simp only [symMat, dcMet, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => by rw [pd_pi_apply]

theorem pd_sum_smul (f : Fin 3 → Site N → ℝ) (c : Fin 3 → ℝ) (i : Fin 3) :
    pd i (fun y => ∑ k, c k * f k y) = fun y => ∑ k, c k * pd i (f k) y := by
  have : (fun y => ∑ k, c k * f k y) = ∑ k, c k • f k := by
    funext y; simp [Finset.sum_apply]
  rw [this, map_sum]
  funext y
  simp [Finset.sum_apply, map_smul]

theorem trS_dcMet (c : Fin 3 → ℝ) (u : MetF N) (y : Site N) :
    trS (dcMet c u y) = ∑ k, c k * pd k (fun y' => trS (u y')) y := by
  have h : (fun y' => trS (u y')) = fun y' => ∑ p, symMat (u y') p p := rfl
  simp only [trS, symMat_dcMet, h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  have : (fun y' => ∑ p, symMat (u y') p p) = ∑ p, fun y' => symMat (u y') p p := by
    funext y'; simp [Finset.sum_apply]
  rw [this, map_sum, Finset.sum_apply]

theorem dcMet_eq_sum (c : Fin 3 → ℝ) (u : MetF N) : dcMet c u = ∑ k, c k • pd k u := by
  funext x; simp [dcMet, Finset.sum_apply]

/-- `R₁` as a function of the symmetric components. -/
theorem R1F_eq_fun (u : MetF N) : R1F u = (∑ i, ∑ j, pd i (pd j (fun y => symMat (u y) i j))) -
    ∑ i, pd i (pd i (fun y => trS (u y))) := by
  funext y; simp [R1F, Finset.sum_apply]

theorem R1F_add (u v : MetF N) : R1F (u + v) = R1F u + R1F v := by
  have h1 : ∀ i j, (fun y => symMat ((u + v) y) i j) =
      (fun y => symMat (u y) i j) + fun y => symMat (v y) i j := by
    intro i j; funext y; simp [symMat]
  have h2 : (fun y => trS ((u + v) y)) = (fun y => trS (u y)) + fun y => trS (v y) := by
    funext y; simp [trS, symMat, Finset.sum_add_distrib]
  rw [R1F_eq_fun, R1F_eq_fun, R1F_eq_fun]
  simp only [h1, h2, map_add, Finset.sum_add_distrib]
  abel

theorem R1F_smul (t : ℝ) (u : MetF N) : R1F (t • u) = t • R1F u := by
  have h1 : ∀ i j, (fun y => symMat ((t • u) y) i j) = t • fun y => symMat (u y) i j := by
    intro i j; funext y; simp [symMat]
  have h2 : (fun y => trS ((t • u) y)) = t • fun y => trS (u y) := by
    funext y; simp [trS, symMat, Finset.mul_sum]
  rw [R1F_eq_fun, R1F_eq_fun]
  simp only [h1, h2, map_smul, ← Finset.smul_sum, smul_sub]

theorem R1F_sum (f : Fin 3 → MetF N) : R1F (∑ k, f k) = ∑ k, R1F (f k) := by
  simp only [Fin.sum_univ_three, R1F_add]

/-- `R₁(δ_k u) = δ_k R₁(u)`. -/
theorem R1F_pd (k : Fin 3) (u : MetF N) : R1F (pd k u) = pd k (R1F u) := by
  have h1 : ∀ i j, (fun y => symMat (pd k u y) i j) = pd k (fun y => symMat (u y) i j) := by
    intro i j; funext y; simp only [symMat]; rw [pd_pi_apply]
  have h2 : (fun y => trS (pd k u y)) = pd k (fun y => trS (u y)) := by
    have : (fun y => trS (u y)) = ∑ p, fun y => symMat (u y) p p := by
      funext y; simp [trS, Finset.sum_apply]
    rw [this, map_sum]
    funext y
    simp only [trS, Finset.sum_apply]
    exact Finset.sum_congr rfl fun p _ => by rw [← h1 p p]
  rw [R1F_eq_fun, R1F_eq_fun]
  simp only [h1, h2, map_sub, map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [pd_comm k i, pd_comm k j]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [pd_comm k i, pd_comm k i]

theorem R1F_dcMet_eq_zero (c : Fin 3 → ℝ) {u : MetF N} (h : R1F u = 0) : R1F (dcMet c u) = 0 := by
  rw [dcMet_eq_sum, R1F_sum]
  simp [R1F_smul, R1F_pd, h]

theorem divF_eq_fun (π : MetF N) (a : Fin 3) :
    (fun y => divF π y a) = (-2 : ℝ) • ∑ j, pd j (fun y => symMat (π y) j a) := by
  funext y; simp [divF, Finset.sum_apply]

/-- `div(δ_k π) = δ_k div π`. -/
theorem divF_pd (k : Fin 3) (π : MetF N) (a : Fin 3) :
    (fun y => divF (pd k π) y a) = pd k (fun y => divF π y a) := by
  have h1 : ∀ j, (fun y => symMat (pd k π y) j a) = pd k (fun y => symMat (π y) j a) := by
    intro j; funext y; simp only [symMat]; rw [pd_pi_apply]
  rw [divF_eq_fun, divF_eq_fun]
  simp only [h1, map_smul, map_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [pd_comm]

theorem pd_fun_add (j : Fin 3) (f g : Site N → ℝ) :
    pd j (fun y => f y + g y) = pd j f + pd j g := by
  rw [show (fun y => f y + g y) = f + g from rfl, map_add]

theorem pd_fun_smul (j : Fin 3) (t : ℝ) (f : Site N → ℝ) :
    pd j (fun y => t * f y) = t • pd j f := by
  rw [show (fun y => t * f y) = t • f from rfl, map_smul]

theorem divF_add (π π' : MetF N) : divF (π + π') = divF π + divF π' := by
  funext x a
  simp only [divF, symMat, Pi.add_apply, pd_fun_add, Finset.sum_add_distrib]
  ring

theorem divF_smul (t : ℝ) (π : MetF N) : divF (t • π) = t • divF π := by
  funext x a
  simp only [divF, symMat, Pi.smul_apply, smul_eq_mul, pd_fun_smul, Finset.mul_sum]
  simp only [← Finset.mul_sum]
  ring

theorem divF_dcMet_eq_zero (c : Fin 3 → ℝ) {π : MetF N} (h : divF π = 0) : divF (dcMet c π) = 0 := by
  rw [dcMet_eq_sum]
  simp only [Fin.sum_univ_three, divF_add, divF_smul]
  have hk : ∀ k, divF (pd k π) = 0 := by
    intro k; funext x a
    have := congrFun (divF_pd k π a) x
    rw [this]
    have h0 : (fun y => divF π y a) = fun _ => (0 : ℝ) := by funext y; rw [h]; rfl
    rw [h0, pd_const]; rfl
  simp [hk]

/-! ### The literal Hamiltonian: shift structure and Ward packet -/

/-- The linear functional `(n, b) ↦ h³(-Σ_x μ_N(x) n(x) + Σ_{x,a} μ_β(x)^a b(x)^a)` pairing the
initial constraint rows `𝒞_h = (-P_N, P_β)` with a multiplier direction `μ`. -/
def lamPair (μ : Lam N) : ((Site N → ℝ) × (Site N → Fin 3 → ℝ)) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun nb => hN N ^ 3 * (-(∑ x, μ.1 x * nb.1 x) + ∑ x, ∑ a, μ.2 x a * nb.2 x a)
      map_add' := fun nb nb' => by
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
        ring
      map_smul' := fun t nb => by
        simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        have h1 : ∑ x, μ.1 x * (t * nb.1 x) = t * ∑ x, μ.1 x * nb.1 x := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
        have h2 : ∑ x, ∑ a, μ.2 x a * (t * nb.2 x a) = t * ∑ x, ∑ a, μ.2 x a * nb.2 x a := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ => by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
        rw [h1, h2]; ring }

theorem lamPair_apply (μ : Lam N) (nb : (Site N → ℝ) × (Site N → Fin 3 → ℝ)) :
    lamPair μ nb = hN N ^ 3 * (-(∑ x, μ.1 x * nb.1 x) + ∑ x, ∑ a, μ.2 x a * nb.2 x a) := rfl

theorem multDir_eq (μ : Lam N) : ((((0 : MetF N), μ.1, μ.2), (0 : MetF N)) : ParF N × MetF N) =
    (∑ x, μ.1 x • lapseDir x) + ∑ x, ∑ a, μ.2 x a • shiftDir x a := by
  refine Prod.ext (Prod.ext ?_ (Prod.ext ?_ ?_)) ?_
  · funext y k; simp [lapseDir, shiftDir, Prod.fst_sum, Finset.sum_apply]
  · funext y; simp [lapseDir, shiftDir, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  · funext y a
    simp [lapseDir, shiftDir, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  · funext y k; simp [lapseDir, shiftDir, Prod.snd_sum, Finset.sum_apply]

theorem embX_lamE (X : Xs N) : embX (X, lamE N) = qFlat N + iotaX X := by
  simp [embX, lamE, qFlat, zFlat, refMult]

/-- The multiplier derivative of `𝓗_h` on the slice `λ = e` is the constraint pairing of `𝒞_h`. -/
theorem fderiv_canonH_multDir (χ R : ℝ) (μ : Lam N) (X : Xs N) :
    fderiv ℝ (canonH χ R) (embX (X, lamE N)) ((((0 : MetF N), μ.1, μ.2), (0 : MetF N))) =
      lamPair μ (Cmap χ R X) := by
  have hh : hN N ^ 3 ≠ 0 := pow_ne_zero 3 hN_ne_zero
  have hh1 : hN N ≠ 0 := hN_ne_zero
  rw [multDir_eq, map_add, map_sum, map_sum, Cmap_eq, lamPair_apply, embX_lamE]
  simp only [map_sum, map_smul, smul_eq_mul, mul_neg, Finset.sum_neg_distrib, neg_neg]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun x _ => by field_simp
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by field_simp

/-- **The constant-shift rows are the literal `P_c = ∂_λ𝓗_h[(0, c)]`.** -/
theorem rowP_shiftLam (χ R : ℝ) (c : Fin 3 → ℝ) :
    rowP (Hlit (N := N) χ R) (shiftLam c) = Prow (N := N) χ R c := rfl

section Chart

variable {χ R : ℝ} {U : Set (CoP N)} (hU : FlatChart χ R U) (hχ : χ ≠ 0)
include hU hχ

theorem analyticAt_embX (z : Xs N × Lam N) : AnalyticAt ℝ (embX (N := N)) z := by
  have h : (embX (N := N)) = fun z => (((flatMet N, 0, 0), 0) : ParF N × MetF N) + embL z :=
    funext embX_eq
  rw [h]; exact analyticAt_const.add ((embL (N := N)).analyticAt z)

theorem analyticAt_Hlit : AnalyticAt ℝ (Hlit χ R) (pE N) := by
  have h := analyticAt_canonH hU hχ
  rw [← embX_pE] at h
  exact AnalyticAt.comp (g := canonH χ R) (f := embX) h (analyticAt_embX hU hχ _)

theorem hasFDerivAt_Hlit : ∀ᶠ z in 𝓝 (pE N),
    HasFDerivAt (Hlit χ R) ((fderiv ℝ (canonH χ R) (embX z)).comp embL) z := by
  have h := (analyticAt_canonH hU hχ).eventually_analyticAt
  rw [← embX_pE] at h
  filter_upwards [(continuous_embX (N := N)).continuousAt.eventually h] with z hz
  exact hz.differentiableAt.hasFDerivAt.comp z (hasFDerivAt_embX z)

theorem rowX_Hlit_pE : rowX (Hlit χ R) (pE N) = 0 := by
  have h0 : fderiv ℝ (canonH χ R) (qFlat N) = 0 := (canonicalHamiltonian_quadratic_part hU hχ).2.1
  have hd := (hasFDerivAt_Hlit hU hχ).self_of_nhds
  simp only [rowX, hd.fderiv, embX_pE, h0, ContinuousLinearMap.zero_comp]

/-- **The literal canonical Hamiltonian has the constant-shift structure.** -/
theorem shiftStructure_lit :
    ShiftStructure (Hlit χ R) Jlit (lamE N) (shiftLam (N := N)) Blit where
  analytic := analyticAt_Hlit hU hχ
  F0 := rowX_Hlit_pE hU hχ
  cubic c := by
    obtain ⟨C, hC⟩ := Qrow_isBigO hU hχ c
    refine ⟨C, ?_⟩
    filter_upwards [hC, Prow_eq hU hχ c] with z h1 h2
    have : rowP (Hlit χ R) (shiftLam c) z - Blit c z.1 z.1 = Qrow χ R c z := by
      rw [Blit_diag]
      change Prow χ R c z - qShift c z.1 = _
      rw [h2]; ring
    rw [this]; exact h1
  comm := comm_lit

/-- **`F^can` is `𝕁∇_X𝓗_h`** of `ExactActionProvenance.Fcan`, in the chart. -/
theorem canF_eq_Fcan : ∀ᶠ z in 𝓝 (pE N),
    canF (Hlit χ R) Jlit z = Fcan χ R (flatMet N + z.1.1, z.1.2) z.2 := by
  filter_upwards [hasFDerivAt_Hlit hU hχ] with z hz
  have hcan : canonH χ R = fun q : ParF N × MetF N =>
      canonicalHamiltonian χ 0 sqrtTriad (statAst χ R) (zFlat N) q.1 q.2 := rfl
  refine Prod.ext (funext fun x => funext fun k => ?_) (funext fun x => funext fun k => ?_)
  · simp only [canF, Jlit_fst, rieszV, rowX, hz.fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply, Fcan, ← hcan, mul_inv]
    rfl
  · simp only [canF, Jlit_snd, rieszV, rowX, hz.fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply, Fcan, ← hcan, mul_inv, Pi.neg_apply]
    rfl

/-- The `X`-gradient of the row `P_μ` at the base point is the linearized constraint pairing:
`D_XP_μ(0, e)[w] = Λ_μ(D𝒞_h(0)w) = Λ_μ(χ R₁(w_u), δ_jw_p^{ja})`. -/
theorem rowX_rowP_lit (μ : Lam N) (w : Xs N) :
    rowX (rowP (Hlit χ R) μ) (pE N) w = lamPair μ ((fun x => χ * R1F w.1 x, divF w.2)) := by
  -- near the base point the row is `z ↦ D𝓗_h(embX z)(embL(0, μ))`
  have hev : rowP (Hlit χ R) μ =ᶠ[𝓝 (pE N)] fun z =>
      fderiv ℝ (canonH χ R) (embX z) ((((0 : MetF N), μ.1, μ.2), (0 : MetF N))) := by
    filter_upwards [hasFDerivAt_Hlit hU hχ] with z hz
    simp only [rowP, hz.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    rfl
  have hg : AnalyticAt ℝ (fun z : Xs N × Lam N =>
      fderiv ℝ (canonH χ R) (embX z) ((((0 : MetF N), μ.1, μ.2), (0 : MetF N)))) (pE N) := by
    have h := (analyticAt_canonH hU hχ).fderiv
    rw [← embX_pE] at h
    exact (ContinuousLinearMap.analyticAt (ContinuousLinearMap.apply ℝ ℝ
      ((((0 : MetF N), μ.1, μ.2), (0 : MetF N)) : ParF N × MetF N)) _).comp
      (AnalyticAt.comp (g := fderiv ℝ (canonH χ R)) (f := embX) h (analyticAt_embX hU hχ _))
  have h1 : rowX (rowP (Hlit χ R) μ) (pE N) = rowX (fun z : Xs N × Lam N =>
      fderiv ℝ (canonH χ R) (embX z) ((((0 : MetF N), μ.1, μ.2), (0 : MetF N)))) (pE N) := by
    simp only [rowX, hev.fderiv_eq]
  rw [h1]
  -- the slice function is `Λ_μ ∘ 𝒞_h`
  have hslice := hasFDerivAt_slice (X := Xs N) (L := Lam N) (x := 0) (lam := lamE N)
    hg.differentiableAt
  have hfun : (fun X : Xs N => fderiv ℝ (canonH χ R) (embX (X, lamE N))
      ((((0 : MetF N), μ.1, μ.2), (0 : MetF N)))) = fun X => lamPair μ (Cmap χ R X) := by
    funext X; exact fderiv_canonH_multDir χ R μ X
  rw [hfun] at hslice
  obtain ⟨-, hCan, hCder⟩ := fderiv_initialConstraint_flat hU hχ
  have hC : HasFDerivAt (fun X : Xs N => lamPair μ (Cmap χ R X))
      ((lamPair μ).comp (fderiv ℝ (Cmap χ R) 0)) 0 :=
    (lamPair μ).hasFDerivAt.comp 0 hCan.differentiableAt.hasFDerivAt
  have := hslice.unique hC
  have hw := congrArg (fun T => T w) this
  simp only [ContinuousLinearMap.comp_apply] at hw
  rw [show rowX (fun z : Xs N × Lam N => fderiv ℝ (canonH χ R) (embX z)
      ((((0 : MetF N), μ.1, μ.2), (0 : MetF N)))) (pE N) w =
      (fderiv ℝ (fun z : Xs N × Lam N => fderiv ℝ (canonH χ R) (embX z)
        ((((0 : MetF N), μ.1, μ.2), (0 : MetF N)))) (0, lamE N))
        (ContinuousLinearMap.inl ℝ (Xs N) (Lam N) w) from rfl, hw, hCder]

/-- **The linear first-Poisson coefficient vanishes at a constraint-tangent first field**:
if `R₁(Y_u) = 0` and `δ_jY_p^{ja} = 0` (`D𝒞_h(0)Y = 0`), then `𝕂₁(Y)c = 0` for every constant
shift `c`. -/
theorem K1_lit (c : Fin 3 → ℝ) (Y0 : Xs N) (hY1 : R1F Y0.1 = 0) (hY2 : divF Y0.2 = 0) :
    (gradQ (Blit c) Y0).comp (Jlit.comp ((fderiv ℝ (rowX (Hlit χ R)) (pE N)).comp
      (ContinuousLinearMap.inr ℝ (Xs N) (Lam N)))) = 0 := by
  refine ContinuousLinearMap.ext fun μ => ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply]
  rw [gradQ_Jlit, fderiv_rowX_inr (analyticAt_Hlit hU hχ), rowX_rowP_lit hU hχ,
    R1F_dcMet_eq_zero c hY1, divF_dcMet_eq_zero c hY2]
  simp [lamPair_apply]

/-- **The constant-shift Ward packet of the literal canonical Hamiltonian** (rows `P_{e_i}`,
harmonic directions all constant shifts), along every constraint-tangent first field `Y`. -/
theorem wardPacketRay_lit (Y0 : Xs N) (hY1 : R1F Y0.1 = 0) (hY2 : divF Y0.2 = 0) :
    WardPacketRay (fun i : Fin 3 => Prow χ R (Pi.single i 1)) (canF (Hlit χ R) Jlit) (lamE N)
      (shiftLam (N := N)) Y0 :=
  wardPacketRay_of_shift (fun i : Fin 3 => (Pi.single i 1 : Fin 3 → ℝ)) (shiftStructure_lit hU hχ)
    Y0 fun i => K1_lit hU hχ _ Y0 hY1 hY2

end Chart

/-! ### The records -/

/-- The constant-shift Ward row `ℬ_c = D_XP_c F^can` of the literal Hamiltonian. -/
def wardRowLit (χ R : ℝ) (c : Fin 3 → ℝ) : Xs N × Lam N → ℝ :=
  wardRow (rowX (Prow χ R c)) (canF (Hlit χ R) (Jlit (N := N)))

/-- **`lem:supp-exact-ward-orders` for the literal canonical Hamiltonian.**  For every `χ ≠ 0`
there is an `N`-independent regulator threshold such that, for the literal `𝓗_h`
(`ExactShiftWard.Hlit`), every literal constant shift `c` and every first field `Y` solving the
linearized constraints (`R₁(Y_u) = 0`, `δ_jY_p^{ja} = 0`):
1. `‖Dℬ_c(z)‖ = O(‖z - (0, e)‖)` on a neighbourhood of `(0, e)` (so `‖D_Xℬ_c‖ = O(a)` along
   every family `z_a - (0, e) = O(a)`);
2. along every family `X_a = aY + O(a²)`, `λ_a = e + O(a)`: `‖D_λℬ_c(z_a)‖ = O(a²)`;
3. for every literal constant shift `d`, `D_λℬ_c[H_c d] = O(‖z - (0, e)‖³)` on a neighbourhood
   of `(0, e)` (hence `O(a³)` along every family `z_a - (0, e) = O(a)`). -/
theorem ward_orders_lit (χ : ℝ) (hχ : χ ≠ 0) :
    ∃ ε > 0, ∀ (N : ℕ) [NeZero N] (R : ℝ), 0 < R → hN N * R ≤ ε →
      ∀ (c : Fin 3 → ℝ) (Y0 : Xs N), R1F Y0.1 = 0 → divF Y0.2 = 0 →
        VanishesToOrder (fderiv ℝ (wardRowLit χ R c)) (pE N) 1 ∧
        (∀ z : ℝ → Xs N × Lam N, (fun a => (z a).1 - a • Y0) =O[𝓝[>] 0] (fun a => a ^ 2) →
          (fun a => (z a).2 - lamE N) =O[𝓝[>] 0] (fun a => a) →
          (fun a => (fderiv ℝ (wardRowLit χ R c) (z a)).comp
            (ContinuousLinearMap.inr ℝ (Xs N) (Lam N))) =O[𝓝[>] 0] fun a => a ^ 2) ∧
        ∀ d : Fin 3 → ℝ, VanishesToOrder (fun z => (fderiv ℝ (wardRowLit χ R c) z).comp
          (ContinuousLinearMap.inr ℝ (Xs N) (Lam N)) (shiftLam d)) (pE N) 3 := by
  obtain ⟨ε, hε, h⟩ := flat_chart χ hχ
  refine ⟨ε, hε, fun N _ R hR hhR c Y0 hY1 hY2 => ?_⟩
  obtain ⟨U, hU⟩ := h N R hR hhR
  have S := shiftStructure_lit hU hχ
  have e0 : pE N = ((0 : Xs N), lamE N) := rfl
  have hwr : wardRowLit χ R c = wardRow (rowX (rowP (Hlit χ R) (shiftLam c)))
      (canF (Hlit χ R) (Jlit (N := N))) := by
    unfold wardRowLit; rw [rowP_shiftLam]
  rw [e0, hwr]
  set P := rowP (Hlit (N := N) χ R) (shiftLam c) with hPdef
  have hPan : AnalyticAt ℝ P ((0 : Xs N), lamE N) := rowP_analyticAt S.analytic (shiftLam c)
  have hP4 : ContDiffAt ℝ 4 (rowX P) ((0 : Xs N), lamE N) := (rowX_analyticAt hPan).contDiffAt
  have hM : massRow (rowX P) ((0 : Xs N), lamE N) = 0 :=
    massRow_eq_zero_of_mass _ _ hPan.contDiffAt (ward_hmass1 S c).self_of_nhds
  have hK1 : (fderiv ℝ (rowX P) ((0 : Xs N), lamE N) (Y0, 0)).comp
      ((fderiv ℝ (canF (Hlit χ R) (Jlit (N := N))) ((0 : Xs N), lamE N)).comp
        (ContinuousLinearMap.inr ℝ (Xs N) (Lam N))) = 0 := by
    rw [ward_K1_eq S c Y0]
    exact K1_lit hU hχ c Y0 hY1 hY2
  obtain ⟨o1, o2, o3⟩ := ward_orders_ray (rowX P) (canF (Hlit χ R) (Jlit (N := N))) (lamE N)
    hP4 (canF_analyticAt S).contDiffAt (ward_hF0 S) (ward_hP0 S c) hM Y0 hK1
  exact ⟨o1, o2, fun d => o3 (shiftLam d) (ward_hFν S d) (ward_hM2 S c (shiftLam d))
    (ward_hQ S c d)⟩

/-- **`thm:supp-exact-harmonic-q4-zero` for the literal canonical Hamiltonian.**  For every
`χ ≠ 0` there is an `N`-independent regulator threshold such that: for every literal constant-shift
row `c`, every harmonic constant shift `d`, every second-record base family with the prepared first
field `Y` fixed (`X_a = aY + O(a²)`, `λ_a = e + O(a)`, `Y` constraint-tangent), every
exact-constrained pure-harmonic ray tangent `δX = O(a⁵)`, `δλ = a²H_c d + O(a³)`
(`eq:supp-exact-pure-harmonic-ray`) and every bounded rate `r_*`, if the constant-shift row of the
directional residual of `𝓕_a(Q) = ℬ(Q) + 𝓜(Q) a r_*(a)` is analytic in `a`, its Taylor
coefficients of order `≤ 4` vanish; in particular `q₄(ξ; J_H d) = 0`. -/
theorem harmonic_q4_zero_lit (χ : ℝ) (hχ : χ ≠ 0) :
    ∃ ε > 0, ∀ (N : ℕ) [NeZero N] (R : ℝ), 0 < R → hN N * R ≤ ε →
      ∀ (c d : Fin 3 → ℝ) (Y0 : Xs N), R1F Y0.1 = 0 → divF Y0.2 = 0 →
      ∀ (z : ℝ → Xs N × Lam N) (δX : ℝ → Xs N) (δlam : ℝ → Lam N) (r : ℝ → Lam N),
        (fun a => (z a).1 - a • Y0) =O[𝓝[>] 0] (fun a => a ^ 2) →
        (fun a => (z a).2 - lamE N) =O[𝓝[>] 0] (fun a => a) →
        δX =O[𝓝[>] 0] (fun a => a ^ 5) →
        (fun a => δlam a - a ^ 2 • shiftLam d) =O[𝓝[>] 0] (fun a => a ^ 3) →
        r =O[𝓝[>] 0] (fun _ => (1 : ℝ)) →
        ∀ pq : FormalMultilinearSeries ℝ ℝ ℝ,
          HasFPowerSeriesAt (fun a => dirResidualRow (Prow χ R c) (canF (Hlit χ R) (Jlit (N := N))) (z a)
            (δX a, δlam a) (a • r a)) pq 0 →
          (∀ j ≤ 4, pq.coeff j = 0) ∧ pq.coeff 4 = 0 := by
  obtain ⟨ε, hε, h⟩ := flat_chart χ hχ
  refine ⟨ε, hε, fun N _ R hR hhR c d Y0 hY1 hY2 z δX δlam r hz1 hz2 hδX hδlam hr pq hq => ?_⟩
  obtain ⟨U, hU⟩ := h N R hR hhR
  have S := shiftStructure_lit hU hχ
  rw [← rowP_shiftLam χ R c] at hq
  set P := rowP (Hlit (N := N) χ R) (shiftLam c) with hPdef
  have hPan : AnalyticAt ℝ P ((0 : Xs N), lamE N) := rowP_analyticAt S.analytic (shiftLam c)
  have hK1 : (fderiv ℝ (rowX P) ((0 : Xs N), lamE N) (Y0, 0)).comp
      ((fderiv ℝ (canF (Hlit χ R) (Jlit (N := N))) ((0 : Xs N), lamE N)).comp
        (ContinuousLinearMap.inr ℝ (Xs N) (Lam N))) = 0 := by
    rw [ward_K1_eq S c Y0]
    exact K1_lit hU hχ c Y0 hY1 hY2
  exact harmonic_q4_zero_ray P (canF (Hlit χ R) (Jlit (N := N))) (lamE N) (shiftLam d)
    hPan.contDiffAt (canF_analyticAt S).contDiffAt (ward_hF0 S) (ward_hP0 S c) Y0 hK1
    (ward_hFν S d) (ward_hM2 S c (shiftLam d)) (ward_hQ S c d) (ward_hmass0 S c)
    (ward_hmass1 S c) z hz1 hz2 δX δlam hδX hδlam r hr hq

/-- **The literal Ward packet** (`WardPacketRay`) on the chart threshold: for every `χ ≠ 0`,
for `hR ≤ ε`, the rows `P_{e_i}` of the literal canonical Hamiltonian and `F^can` satisfy every
field of the constant-shift Ward packet along every constraint-tangent first field. -/
theorem wardPacket_lit (χ : ℝ) (hχ : χ ≠ 0) :
    ∃ ε > 0, ∀ (N : ℕ) [NeZero N] (R : ℝ), 0 < R → hN N * R ≤ ε →
      ∀ Y0 : Xs N, R1F Y0.1 = 0 → divF Y0.2 = 0 →
        WardPacketRay (fun i : Fin 3 => Prow χ R (Pi.single i 1)) (canF (Hlit χ R) (Jlit (N := N)))
          (lamE N) (shiftLam (N := N)) Y0 := by
  obtain ⟨ε, hε, h⟩ := flat_chart χ hχ
  refine ⟨ε, hε, fun N _ R hR hhR Y0 hY1 hY2 => ?_⟩
  obtain ⟨U, hU⟩ := h N R hR hhR
  exact wardPacketRay_lit hU hχ Y0 hY1 hY2

/-- **Bridge to the slope chain**: the literal Ward packet gives
`ExactSlowRankTwo.HarmonicAnnihilation` as soon as the rows of the harmonic compatibility
derivative `D𝔠_H(Ξ(q))[J_H c]` are identified with the quartic coefficients of the literal
constant-shift residual rows along realized pure-harmonic rays (the graded-chart input (C3) of
`ass:supp-graded-exact-chart`, not derived in the manuscript). -/
theorem harmonicAnnihilation_lit (χ : ℝ) (hχ : χ ≠ 0) :
    ∃ ε > 0, ∀ (N : ℕ) [NeZero N] (R : ℝ), 0 < R → hN N * R ≤ ε →
      ∀ (Y0 : Xs N), R1F Y0.1 = 0 → divF Y0.2 = 0 →
      ∀ {Rr Zg V Ho : Type} [NormedAddCommGroup Rr] [NormedSpace ℝ Rr]
        [NormedAddCommGroup Zg] [NormedSpace ℝ Zg] [NormedAddCommGroup V] [NormedSpace ℝ V]
        [NormedAddCommGroup Ho] [NormedSpace ℝ Ho]
        (ℓ : Fin 3 → Ho →L[ℝ] ℝ), (∀ y : Ho, (∀ i, ℓ i y = 0) → y = 0) →
        ∀ (E : Rr →L[ℝ] V) (Jg : Zg →L[ℝ] V) (JH : (Fin 3 → ℝ) →L[ℝ] V)
          (γ : Rr × (Fin 3 → ℝ) → Zg) (cH : V → Ho),
        (∀ c : Fin 3 → ℝ, ∀ᶠ q in 𝓝 (0 : Rr × (Fin 3 → ℝ)), ∃ (z : ℝ → Xs N × Lam N)
          (δX : ℝ → Xs N) (δlam : ℝ → Lam N) (r : ℝ → Lam N),
          (fun a => (z a).1 - a • Y0) =O[𝓝[>] 0] (fun a => a ^ 2) ∧
          (fun a => (z a).2 - lamE N) =O[𝓝[>] 0] (fun a => a) ∧
          δX =O[𝓝[>] 0] (fun a => a ^ 5) ∧
          (fun a => δlam a - a ^ 2 • shiftLam c) =O[𝓝[>] 0] (fun a => a ^ 3) ∧
          r =O[𝓝[>] 0] (fun _ => (1 : ℝ)) ∧
          ∀ i, ∃ pq : FormalMultilinearSeries ℝ ℝ ℝ,
            HasFPowerSeriesAt (fun a => dirResidualRow (Prow χ R (Pi.single i 1))
              (canF (Hlit χ R) (Jlit (N := N))) (z a) (δX a, δlam a) (a • r a)) pq 0 ∧
            ℓ i (fderiv ℝ cH (ExactSlowBranch.reducedChart E Jg JH γ q) (JH c)) = pq.coeff 4) →
        ExactSlowRankTwo.HarmonicAnnihilation E Jg JH γ cH := by
  obtain ⟨ε, hε, h⟩ := wardPacket_lit χ hχ
  refine ⟨ε, hε, fun N _ R hR hhR Y0 hY1 hY2 => ?_⟩
  intro Rr Zg V Ho _ _ _ _ _ _ _ _ ℓ hsep E Jg JH γ cH hray
  exact harmonicAnnihilation_of_ward_ray ℓ hsep _ _ (lamE N) (shiftLam (N := N)) Y0
    (h N R hR hhR Y0 hY1 hY2) E Jg JH γ cH hray

/-- Non-vacuity: the zero first field is constraint-tangent, so `ward_orders_lit` applies. -/
example (χ : ℝ) (hχ : χ ≠ 0) : ∃ ε > 0, ∀ (N : ℕ) [NeZero N] (R : ℝ), 0 < R → hN N * R ≤ ε →
    ∀ c : Fin 3 → ℝ, VanishesToOrder (fderiv ℝ (wardRowLit (N := N) χ R c)) (pE N) 1 := by
  obtain ⟨ε, hε, h⟩ := ward_orders_lit χ hχ
  refine ⟨ε, hε, fun N _ R hR hhR c => ?_⟩
  have h0 : R1F (0 : Xs N).1 = 0 := by
    have := R1F_smul (N := N) 0 0; simpa using this
  have h1 : divF (0 : Xs N).2 = 0 := by
    have := divF_smul (N := N) 0 0; simpa using this
  exact (h N R hR hhR c 0 h0 h1).1

/-! ### The uniform linear first-Poisson identity fails for the literal Hamiltonian -/

/-- The cosine momentum mode `π = cos(2πx₀/N) e₁₁`. -/
def cosMom (N : ℕ) [NeZero N] : MetF N :=
  fun x => Pi.single 0 (Real.cos (2 * Real.pi * (x 0).val / N))

theorem omega_pos (h3 : 3 ≤ N) : 0 < omega N := by
  unfold omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hs : 0 < Real.sin (Real.pi / N) := by
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    rw [div_lt_iff₀ hN0]
    have : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
    nlinarith [Real.pi_pos]
  positivity

/-- `div(δ₀ π)` of the cosine mode at the origin, row `a = 0`: `2ω_N²`. -/
theorem divF_pd_cosMom (hNodd : Odd N) (h3 : 3 ≤ N) :
    divF (dcMet (Pi.single 0 1) (cosMom N)) 0 0 = 2 * omega N ^ 2 := by
  have hdc : dcMet (Pi.single 0 1) (cosMom N) = pd 0 (cosMom N) := by
    funext x; simp [dcMet, Fin.sum_univ_three, Pi.single_apply]
  rw [hdc]
  have hcomp : ∀ (k : Fin 6) (y : Site N), pd 0 (cosMom N) y k =
      if k = 0 then pd 0 (fun x : Site N => Real.cos (2 * Real.pi * (x 0).val / N)) y else 0 := by
    intro k y
    rw [pd_pi_apply]
    by_cases hk : k = 0
    · subst hk; simp [cosMom]
    · simp only [cosMom, Pi.single_apply, hk, if_false]
      have : (fun x : Site N => (0 : ℝ)) = fun _ => 0 := rfl
      rw [this, pd_const]; rfl
  set f : Site N → ℝ := fun x => Real.cos (2 * Real.pi * (x 0).val / N) with hf
  have hj0 : (fun y => symMat (pd 0 (cosMom N) y) 0 0) = pd 0 f := by
    funext y; simp only [symMat]; rw [show InitialConstraintLinearRange.sym6 0 0 = 0 from rfl, hcomp]
    rfl
  have hj1 : (fun y => symMat (pd 0 (cosMom N) y) 1 0) = fun _ => 0 := by
    funext y; simp only [symMat]; rw [show InitialConstraintLinearRange.sym6 1 0 = 3 from rfl, hcomp]
    rfl
  have hj2 : (fun y => symMat (pd 0 (cosMom N) y) 2 0) = fun _ => 0 := by
    funext y; simp only [symMat]; rw [show InitialConstraintLinearRange.sym6 2 0 = 4 from rfl, hcomp]
    rfl
  simp only [divF, Fin.sum_univ_three, hj0, hj1, hj2, pd_const, Pi.zero_apply, add_zero]
  rw [hf, pd_cos hNodd h3]
  have h2 : pd 0 (fun x : Site N => -omega N * Real.sin (2 * Real.pi * (x 0).val / N)) =
      fun x => -omega N * (omega N * Real.cos (2 * Real.pi * (x 0).val / N)) := by
    rw [show (fun x : Site N => -omega N * Real.sin (2 * Real.pi * (x 0).val / N)) =
      (-omega N) • fun x : Site N => Real.sin (2 * Real.pi * (x 0).val / N) from rfl, map_smul,
      pd_sin hNodd h3]
    rfl
  rw [h2]
  simp
  ring

/-- **The uniform linear first-Poisson identity of `HarmonicQuartic.WardPacket` fails for the
literal canonical Hamiltonian** (odd `N ≥ 3`, `χ ≠ 0`): for the constant shift `c = e₁`, the
coefficient `D(D_XP_c)(0, e)[w] ∘ D_λF(0, e)` is nonzero at `w = (0, cos(2πx₀/N) e₁₁)`.  Hence the
linear first-Poisson coefficient can vanish only on the first-field ray (`K1_lit`), and the
uniform packet `HarmonicQuartic.WardPacket` is not satisfied. -/
theorem not_uniform_K1_lit {χ R : ℝ} {U : Set (CoP N)} (hU : FlatChart χ R U) (hχ : χ ≠ 0)
    (hNodd : Odd N) (h3 : 3 ≤ N) :
    ∃ w : Xs N × Lam N, (fderiv ℝ (rowX (Prow χ R (Pi.single 0 1))) ((0 : Xs N), lamE N) w).comp
      ((fderiv ℝ (canF (Hlit χ R) (Jlit (N := N))) ((0 : Xs N), lamE N)).comp
        (ContinuousLinearMap.inr ℝ (Xs N) (Lam N))) ≠ 0 := by
  have S := shiftStructure_lit hU hχ
  obtain ⟨b, hbdef⟩ : ∃ b : Site N → Fin 3 → ℝ,
      b = divF (dcMet (Pi.single 0 1) (cosMom N)) := ⟨_, rfl⟩
  have hb00 : b 0 0 = 2 * omega N ^ 2 := by rw [hbdef]; exact divF_pd_cosMom hNodd h3
  refine ⟨(((0 : MetF N), cosMom N), 0), fun h => ?_⟩
  have hK := congrArg (fun T => T ((0 : Site N → ℝ), b)) h
  simp only [ContinuousLinearMap.zero_apply] at hK
  rw [← rowP_shiftLam χ R, ward_K1_eq S (Pi.single 0 1) ((0 : MetF N), cosMom N)] at hK
  simp only [ContinuousLinearMap.comp_apply] at hK
  have hA : AnalyticAt ℝ (Hlit χ R) ((0 : Xs N), lamE N) := analyticAt_Hlit hU hχ
  have hrow : ∀ (μ : Lam N) (w : Xs N), rowX (rowP (Hlit χ R) μ) ((0 : Xs N), lamE N) w =
      lamPair μ ((fun x => χ * R1F w.1 x, divF w.2)) := rowX_rowP_lit hU hχ
  rw [gradQ_Jlit, fderiv_rowX_inr hA, hrow] at hK
  have hR0 : R1F (dcMet (Pi.single 0 1) (0 : MetF N)) = 0 := by
    have : dcMet (Pi.single 0 1) (0 : MetF N) = 0 := by
      have := dcMet_smul (N := N) (Pi.single 0 1) 0 0; simpa using this
    rw [this]
    have := R1F_smul (N := N) 0 0; simpa using this
  have hK2 : lamPair ((0 : Site N → ℝ), b) ((fun x => χ * R1F (dcMet (Pi.single 0 1) (0 : MetF N)) x,
      divF (dcMet (Pi.single 0 1) (cosMom N)))) = 0 := by
    have := hK; simpa using this
  rw [hR0, ← hbdef, lamPair_apply] at hK2
  simp only [Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, neg_zero, zero_add] at hK2
  -- `h³ Σ b² = 0` forces `b = 0`, contradicting `b(0)₀ = 2ω² ≠ 0`
  have hb : b 0 0 ≠ 0 := by
    rw [hb00]
    have := omega_pos (N := N) h3
    positivity
  have h1 : 0 < ∑ x, ∑ a, b x a * b x a := by
    have hle : b 0 0 * b 0 0 ≤ ∑ x, ∑ a, b x a * b x a := by
      have h2 : b 0 0 * b 0 0 ≤ ∑ a, b 0 a * b 0 a :=
        Finset.single_le_sum (f := fun a => b 0 a * b 0 a) (fun a _ => mul_self_nonneg _)
          (Finset.mem_univ 0)
      exact h2.trans (Finset.single_le_sum (f := fun x => ∑ a, b x a * b x a)
        (fun x _ => Finset.sum_nonneg fun a _ => mul_self_nonneg _) (Finset.mem_univ 0))
    exact lt_of_lt_of_le (mul_self_pos.2 hb) hle
  have hpos : 0 < hN N ^ 3 * ∑ x, ∑ a, b x a * b x a := mul_pos (pow_pos hN_pos 3) h1
  linarith

/-- Consequently the uniform packet `HarmonicQuartic.WardPacket` is **not** satisfied by the
literal rows (odd `N ≥ 3`): only the ray packet `WardPacketRay` holds. -/
theorem not_wardPacket_lit {χ R : ℝ} {U : Set (CoP N)} (hU : FlatChart χ R U) (hχ : χ ≠ 0)
    (hNodd : Odd N) (h3 : 3 ≤ N) {Yh : Type*} (νH : Yh → Lam N) :
    ¬ HarmonicQuartic.WardPacket (fun i : Fin 3 => Prow χ R (Pi.single i 1))
      (canF (Hlit χ R) (Jlit (N := N))) (lamE N) νH := by
  intro hW
  obtain ⟨w, hw⟩ := not_uniform_K1_lit hU hχ hNodd h3
  exact hw (hW.hK1 0 w)

end RenewalGeometry.ExactPhaseAction.ShiftWard
