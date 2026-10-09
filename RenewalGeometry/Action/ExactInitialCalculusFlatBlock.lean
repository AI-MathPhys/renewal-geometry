/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactInitialCalculusRows
import RenewalGeometry.Action.ExactQuadraticHamiltonian

/-!
# The flat block of the joint stationary/Legendre solve is a fixed site-wise isomorphism
  (infrastructure for `lem:supp-initial-calculus`: "the velocity Hessian at flat data is the flat
  block, invertible with an `N`-independent bound"; emergent-spacetime manuscript)

The joint residual of the stationary connection `A` and the Legendre velocity `V` linearizes at
flat data to the SITE-WISE map on the 30 local unknowns `J30 = (Fin 4 × Fin 6) ⊕ Fin 6`
`M(a, V) = (C₀ a + f_P(V), (c ↦ legLoc(0, 0, a)_c))`, with `C₀ = χ · cartFlat` the flat Cartan block,
`f_P(V)` the `∂_tΠ`-part of the load and `legLoc` the Legendre row.

* `fLocP`, `fLoc_eq_add`: the `∂_tΠ`-part of the site-wise load.
* `legLoc χ v p a c = frob(p, e_c) + Σ_i ⟨D_γΠ_i(I + v)[e_c], ι a_i⟩`: the Legendre row at a site.
* `cartLoc_one` (`C(1) = χ cartFlat`), `fLocP_PdLoc_zero` (`f_P(V) = χ G(V)`, `G = Gfun(0, V, 0, 0)`),
  `legLoc_zero` (`legLoc(0, 0, a)_c = -⟨χ G(e_c), a⟩_b`).
* `bdot_cartFlatInv_comm`: `C₀⁻¹` is `b`-self-adjoint; `flatB_one`: `⟨G(I), C₀⁻¹G(V)⟩_b = tr V`
  (polarization of `site_identity`).
* **`MlocLin_injective`** and **`Mloc`** (`χ ≠ 0`): the flat block is a linear isomorphism of
  `ℝ^{J30}`; it does not depend on the cutoff.
-/

open Filter Finset Metric
open scoped Topology

noncomputable section

namespace RenewalGeometry.ExactPhaseAction.InitialCalculus

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

set_option linter.unusedSectionVars false

open QuadJet
open InitialConstraintLinearRange (sym6)

/-! ### The `∂_tΠ` part of the load and the Legendre row -/

/-- The `∂_tΠ`-part of the site-wise load. -/
def fLocP (P : Fin 3 → M4) : LocVal := fun μ => Fin.cases 0 (fun i => coord (-P i)) μ

theorem fLoc_eq_add (dP : Fin 3 → Fin 4 → Fin 4 → ℝ) (dS : Fin 3 → Fin 3 → Fin 4 → Fin 4 → ℝ)
    (P : Fin 3 → M4) : fLoc dP dS P = fLoc dP dS 0 + fLocP P := by
  funext μ
  cases μ using Fin.cases with
  | zero => simp [fLoc, fLocP]
  | succ i => simp [fLoc, fLocP, coord_add, coord_neg]; abel

/-- **The Legendre row at one site**: `frob(p, e_c) + Σ_i ⟨D_γΠ_i(I + v)[e_c], ι a_i⟩`. -/
def legLoc (χ : ℝ) (v p : Fin 6 → ℝ) (a : LocVal) (c : Fin 6) : ℝ :=
  frob p (Pi.single c 1) + ∑ i, pairing (PdLoc χ v (Pi.single c 1) i) (iota (a i.succ))

/-! ### The flat values -/

theorem cartLoc_one (χ : ℝ) (a : LocVal) : cartLoc χ 1 a = χ • cartFlat a := by
  have h := cartanOp_flat (N := 1) χ (fun _ => a) 0
  simpa [cartanOp_apply] using h

theorem PdLoc_zero_left (χ : ℝ) (V : Fin 6 → ℝ) (i : Fin 3) :
    PdLoc χ 0 V i = Matrix.of (piArrADer χ i (admLinD (V, 0, 0))) := by
  ext K L
  simp only [PdLoc, add_zero, Matrix.of_apply]
  rw [fderiv_piEntry_flat]

theorem piLinVec_zero : piLinVec 0 = 0 := by
  funext i k; fin_cases i <;> fin_cases k <;> simp [piLinVec]

theorem sigLinVec_zero : sigLinVec 0 = 0 := by
  funext i j k; fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [sigLinVec]

theorem symMat_zero' : symMat (0 : Fin 6 → ℝ) = 0 := by funext i j; simp [symMat]

theorem admLinA_zero : admLinA (0 : M3) 0 0 = 0 := by
  funext I μ; rw [admLinA_eq]; fin_cases I <;> fin_cases μ <;> rfl

/-- **`f_P(D_γΠ(I)[V]) = χ G(V)`** with `G = Gfun(0, V, 0, 0)` the linearized load. -/
theorem fLocP_PdLoc_zero (χ : ℝ) (V : Fin 6 → ℝ) :
    fLocP (fun i => PdLoc χ 0 V i) = χ • Gfun 0 V 0 0 := by
  funext μ k
  cases μ using Fin.cases with
  | zero =>
    simp only [fLocP, Fin.cases_zero, Pi.zero_apply, Pi.smul_apply, Gfun]
    simp [symMat_zero', admLinA_zero, piLinVec_zero]
  | succ i =>
    simp only [fLocP, Fin.cases_succ, Pi.smul_apply, Gfun, coord_neg, Pi.neg_apply]
    rw [PdLoc_zero_left]
    have h := coordP_dualA_palLinA_pi χ (admLinD (V, 0, 0)) i
    have h2 : coord (Matrix.of (piArrADer χ i (admLinD (V, 0, 0)))) = χ • piLinVec (admLinD (V, 0, 0)) i := by
      rw [piArrADer_apply]; exact h
    rw [h2]
    simp [symMat_zero', admLinA_zero, sigLinVec_zero, admLinD_apply]

/-- **The flat Legendre row**: `legLoc(0, 0, a)_c = -⟨χ G(e_c), a⟩_b`. -/
theorem legLoc_zero (χ : ℝ) (a : LocVal) (c : Fin 6) :
    legLoc χ 0 0 a c = -bdot (χ • Gfun 0 (Pi.single c 1) 0 0) a := by
  rw [← fLocP_PdLoc_zero]
  simp only [legLoc, bdot, fLocP, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ, pairing_iota]
  simp [frob, symMat, coord_neg, Finset.sum_neg_distrib]
  ring

/-! ### The Schur complement -/

set_option maxHeartbeats 4000000 in
-- a bilinear identity in 48 variables
/-- `C₀⁻¹` is `b`-self-adjoint. -/
theorem bdot_cartFlatInv_comm (y y' : LocVal) :
    bdot y (cartFlatInv y') = bdot y' (cartFlatInv y) := by
  simp only [bdot, cartFlatInv, gram, Fin.sum_univ_four, Fin.sum_univ_six]
  simp
  ring

theorem Gfun_add (V W : Fin 6 → ℝ) : Gfun 0 (V + W) 0 0 = Gfun 0 V 0 0 + Gfun 0 W 0 0 := by
  rw [Gfun_eq_Gexp, Gfun_eq_Gexp, Gfun_eq_Gexp]
  funext μ k
  fin_cases μ <;> fin_cases k <;> simp [Gexp] <;> ring

theorem Gfun_smul (t : ℝ) (V : Fin 6 → ℝ) : Gfun 0 (t • V) 0 0 = t • Gfun 0 V 0 0 := by
  rw [Gfun_eq_Gexp, Gfun_eq_Gexp]
  funext μ k
  fin_cases μ <;> fin_cases k <;> simp [Gexp] <;> ring

theorem bdot_add_left' (u u' v : LocVal) : bdot (u + u') v = bdot u v + bdot u' v := by
  simp only [bdot, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem bdot_smul_left' (t : ℝ) (u v : LocVal) : bdot (t • u) v = t * bdot u v := by
  simp only [bdot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem bdot_add_right' (u v v' : LocVal) : bdot u (v + v') = bdot u v + bdot u v' := by
  simp only [bdot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem cartFlatInv_add (y y' : LocVal) : cartFlatInv (y + y') = cartFlatInv y + cartFlatInv y' := by
  funext μ k
  fin_cases μ <;> fin_cases k <;> simp [cartFlatInv] <;> ring

/-- The flat Schur form `B(W, V) = ⟨G(W), C₀⁻¹G(V)⟩_b`. -/
def flatB (W V : Fin 6 → ℝ) : ℝ := bdot (Gfun 0 W 0 0) (cartFlatInv (Gfun 0 V 0 0))

theorem flatB_comm (W V : Fin 6 → ℝ) : flatB W V = flatB V W := bdot_cartFlatInv_comm _ _

theorem flatB_self (V : Fin 6 → ℝ) : flatB V V = -2 * T1fun 0 V 0 0 := by
  have h := site_identity 0 V 0 0
  have hD : D1fun 0 = 0 := by simp [D1fun]
  rw [hD, add_zero] at h
  unfold flatB; linarith

theorem flatB_add_left (W W' V : Fin 6 → ℝ) : flatB (W + W') V = flatB W V + flatB W' V := by
  unfold flatB; rw [Gfun_add, bdot_add_left']

/-- **Polarization**: `B(I, V) = tr V`. -/
theorem flatB_one (V : Fin 6 → ℝ) : flatB flatSym V = V 0 + V 1 + V 2 := by
  have h1 := flatB_self (flatSym + V)
  have h2 := flatB_self flatSym
  have h3 := flatB_self V
  have hexp : flatB (flatSym + V) (flatSym + V) = flatB flatSym flatSym + 2 * flatB flatSym V +
      flatB V V := by
    have e1 : flatB (flatSym + V) (flatSym + V) =
        flatB flatSym (flatSym + V) + flatB V (flatSym + V) := flatB_add_left _ _ _
    rw [e1, flatB_comm flatSym (flatSym + V), flatB_comm V (flatSym + V), flatB_add_left,
      flatB_add_left, flatB_comm V flatSym]
    ring
  have hT : T1fun 0 (flatSym + V) 0 0 - T1fun 0 flatSym 0 0 - T1fun 0 V 0 0 =
      -(V 0 + V 1 + V 2) := by
    simp only [T1fun, sym6, Fin.sum_univ_three, flatSym]
    simp
    ring
  linarith

theorem frob_self_eq_zero' {V : Fin 6 → ℝ} (h : T1fun 0 V 0 0 = 0) (htr : V 0 + V 1 + V 2 = 0) :
    V = 0 := by
  have hq : (∑ p : Fin 3, ∑ q : Fin 3, V (sym6 p q) ^ 2) = 0 := by
    simp only [T1fun, sym6, Fin.sum_univ_three] at h ⊢
    simp at h ⊢
    nlinarith
  simp only [sym6, Fin.sum_univ_three] at hq
  simp at hq
  funext c
  fin_cases c <;> simp <;> nlinarith [sq_nonneg (V 0), sq_nonneg (V 1), sq_nonneg (V 2),
    sq_nonneg (V 3), sq_nonneg (V 4), sq_nonneg (V 5)]

/-! ### The site-wise flat block -/

/-- The 30 local unknowns: connection `(μ, k)` and velocity `c`. -/
abbrev J30 := (Fin 4 × Fin 6) ⊕ Fin 6

/-- The connection part of a local unknown. -/
def aOf (w : J30 → ℝ) : LocVal := fun μ k => w (Sum.inl (μ, k))

/-- The velocity part of a local unknown. -/
def vOf (w : J30 → ℝ) : Fin 6 → ℝ := fun c => w (Sum.inr c)

/-- The site-wise flat block `M(a, V) = (C₀ a + f_P(V), legLoc(0, 0, a))`. -/
def MlocFun (χ : ℝ) (w : J30 → ℝ) : J30 → ℝ :=
  Sum.elim (fun m => (cartLoc χ 1 (aOf w) + fLocP (fun i => PdLoc χ 0 (vOf w) i)) m.1 m.2)
    (fun c => legLoc χ 0 0 (aOf w) c)

theorem MlocFun_eq (χ : ℝ) (w : J30 → ℝ) : MlocFun χ w = Sum.elim
    (fun m => (χ • (cartFlat (aOf w) + Gfun 0 (vOf w) 0 0)) m.1 m.2)
    (fun c => -bdot (χ • Gfun 0 (Pi.single c 1) 0 0) (aOf w)) := by
  funext m
  cases m with
  | inl m => simp [MlocFun, cartLoc_one, fLocP_PdLoc_zero, smul_add]; ring
  | inr c => simp [MlocFun, legLoc_zero]

/-- The flat block as a linear map. -/
def MlocLin (χ : ℝ) : (J30 → ℝ) →ₗ[ℝ] (J30 → ℝ) where
  toFun := MlocFun χ
  map_add' w w' := by
    rw [MlocFun_eq, MlocFun_eq, MlocFun_eq]
    funext m
    cases m with
    | inl m =>
      obtain ⟨μ, k⟩ := m
      have ha : aOf (w + w') = aOf w + aOf w' := rfl
      have hv : vOf (w + w') = vOf w + vOf w' := rfl
      simp only [Sum.elim_inl, Pi.add_apply, ha, hv, Gfun_add]
      fin_cases μ <;> fin_cases k <;> simp [cartFlat] <;> ring
    | inr c =>
      have ha : aOf (w + w') = aOf w + aOf w' := rfl
      simp only [Sum.elim_inr, Pi.add_apply, ha, bdot_add_right']
      ring
  map_smul' t w := by
    rw [MlocFun_eq, MlocFun_eq]
    funext m
    cases m with
    | inl m =>
      obtain ⟨μ, k⟩ := m
      have ha : aOf (t • w) = t • aOf w := rfl
      have hv : vOf (t • w) = t • vOf w := rfl
      simp only [Sum.elim_inl, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ha, hv, Gfun_smul]
      fin_cases μ <;> fin_cases k <;> simp [cartFlat] <;> ring
    | inr c =>
      have ha : aOf (t • w) = t • aOf w := rfl
      simp only [Sum.elim_inr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ha]
      rw [bdot_smul_right]
      ring

theorem MlocLin_apply (χ : ℝ) (w : J30 → ℝ) : MlocLin χ w = MlocFun χ w := rfl

/-- **The flat block is injective** (`χ ≠ 0`). -/
theorem MlocLin_injective {χ : ℝ} (hχ : χ ≠ 0) : Function.Injective (MlocLin χ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  rw [MlocLin_apply, MlocFun_eq] at hw
  set a := aOf w
  set V := vOf w
  have h1 : ∀ μ k, (χ • (cartFlat a + Gfun 0 V 0 0)) μ k = 0 := fun μ k =>
    congrFun hw (Sum.inl (μ, k))
  have h2 : ∀ c, -bdot (χ • Gfun 0 (Pi.single c 1) 0 0) a = 0 := fun c => congrFun hw (Sum.inr c)
  have hcf : cartFlat a = -Gfun 0 V 0 0 := by
    funext μ k
    have := h1 μ k
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at this
    have h' := (mul_eq_zero.mp this).resolve_left hχ
    simp only [Pi.neg_apply]
    linarith
  have ha : a = -cartFlatInv (Gfun 0 V 0 0) := by
    have := congrArg cartFlatInv hcf
    rw [cartFlatInv_cartFlat] at this
    rw [this]
    have hneg : -Gfun 0 V 0 0 = (-1 : ℝ) • Gfun 0 V 0 0 := by simp
    rw [hneg]
    funext μ k
    fin_cases μ <;> fin_cases k <;> simp [cartFlatInv] <;> ring
  -- `B(e_c, V) = 0` for every `c`, hence `B(W, V) = 0` for every `W`
  have hB : ∀ c, flatB (Pi.single c 1) V = 0 := by
    intro c
    have h := h2 c
    rw [bdot_smul_left', ha] at h
    have hn : bdot (Gfun 0 (Pi.single c 1) 0 0) (-cartFlatInv (Gfun 0 V 0 0)) =
        -flatB (Pi.single c 1) V := by
      unfold flatB; simp [bdot, Finset.sum_neg_distrib]
    rw [hn] at h
    have h' : χ * flatB (Pi.single c 1) V = 0 := by linarith
    exact (mul_eq_zero.mp h').resolve_left hχ
  have hBall : ∀ W, flatB W V = 0 := by
    intro W
    have hW : W = ∑ c, W c • (Pi.single c 1 : Fin 6 → ℝ) := by
      funext k; simp [Finset.sum_apply, Pi.single_apply]
    rw [hW]
    have hlin : ∀ (s : Finset (Fin 6)), flatB (∑ c ∈ s, W c • (Pi.single c 1 : Fin 6 → ℝ)) V = 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty]
        unfold flatB
        rw [show (0 : Fin 6 → ℝ) = (0 : ℝ) • (0 : Fin 6 → ℝ) by simp, Gfun_smul, zero_smul]
        simp [bdot]
      | insert c s hc ih =>
        rw [Finset.sum_insert hc, flatB_add_left, ih, add_zero]
        unfold flatB
        rw [Gfun_smul, bdot_smul_left']
        have := hB c
        unfold flatB at this
        rw [this, mul_zero]
    exact hlin _
  have htr : V 0 + V 1 + V 2 = 0 := by rw [← flatB_one]; exact hBall flatSym
  have hT : T1fun 0 V 0 0 = 0 := by
    have := flatB_self V
    rw [hBall V] at this
    linarith
  have hV : V = 0 := frob_self_eq_zero' hT htr
  have ha0 : a = 0 := by
    rw [ha, hV]
    have : Gfun 0 (0 : Fin 6 → ℝ) 0 0 = 0 := by
      rw [show (0 : Fin 6 → ℝ) = (0 : ℝ) • (0 : Fin 6 → ℝ) by simp, Gfun_smul, zero_smul]
    rw [this]
    funext μ k
    fin_cases μ <;> fin_cases k <;> simp [cartFlatInv]
  funext m
  cases m with
  | inl m => exact congrFun (congrFun ha0 m.1) m.2
  | inr c => exact congrFun hV c

/-- **The flat block as a linear isomorphism of the 30 local unknowns** (`χ ≠ 0`). -/
def Mloc {χ : ℝ} (hχ : χ ≠ 0) : (J30 → ℝ) ≃ₗ[ℝ] (J30 → ℝ) :=
  LinearEquiv.ofInjectiveEndo (MlocLin χ) (MlocLin_injective hχ)

theorem Mloc_apply {χ : ℝ} (hχ : χ ≠ 0) (w : J30 → ℝ) : Mloc hχ w = MlocFun χ w := rfl

end RenewalGeometry.ExactPhaseAction.InitialCalculus
