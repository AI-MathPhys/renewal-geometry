/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactReducedLagrangianJet

/-!
# The quadratic reduced Lagrangian at flat data is the Fierz–Pauli Lagrangian
  (`thm:supp-exact-action-provenance` (iv), `eq:supp-exact-H2`, the paragraph after it: "the exact
  quadratic Ward identities follow because the phase derivatives commute"; emergent-spacetime
  manuscript)

`ExactReducedLagrangianJet.lean` reduces the Hessian of the reduced Lagrangian of the actual
action at flat data to `-χ h³ Σ_x ⟨C₀⁻¹ G, G⟩_b` with `G = χ⁻¹ F₁` the linearized load.  Here:

* `site_identity` (exact polynomial identity at one site, in the 36 jet variables
  `δ_i u_{pq}, V_{pq}, δ_i N, δ_i β^q`): `-½⟨G, C₀⁻¹G⟩_b = T₁ + D₁`, where `T₁` is the Fierz–Pauli
  density and `D₁` is a sum of nine antisymmetrized products `δ_i f δ_j g - δ_j f δ_i g`.
* `loadDer_eq` (explicit linearized load): `F₁ v (x) = χ · Gfun(jets of v at x)`, computed from
  `DΠ_i(1)`, `DΣ_ij(1)` (`ExactFlatLinearization.lean`), `DE(I) = ½ id` (symmetric-square-root
  triad) and the commutation of `δ_i` with linear maps.
* `sum_pd_mul_swap`: `Σ_x δ_i f δ_j g = Σ_x δ_j f δ_i g` (skew-adjointness and commutation of the
  phase derivatives), hence `Σ_x D₁ = 0` — the quadratic Ward identity.
* **`hess_redLagr_flat`**: `D²𝓛°_h(flat)(v, v) = 2χ Q_FP(v)` with the Fierz–Pauli form
  `Q_FP(u, V, N, β) = ¼(‖W‖² - ‖tr W‖²) - P(u) + ⟨N, R₁(u)⟩`, `W = V - L_δβ`,
  `(L_δβ)_{pq} = δ_pβ_q + δ_qβ_p`, `P(u) = ¼Σ‖δ_i u‖² - ½‖v‖² + ½⟨v, δt_u⟩ - ¼‖δt_u‖²`,
  `R₁(u) = Σ δ_iδ_j u_{ij} - Σ δ_i² tr u`.
-/

open Filter Finset
open scoped Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace RenewalGeometry.ExactPhaseAction.QuadJet

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

open InitialConstraintLinearRange (sym6)

variable {N : ℕ} [NeZero N]

/-! ### The single-site algebra -/

/-- The linearized ADM coframe `δe` from `(δE, δN, δβ)`: `δe⁰₀ = δN`, `δe⁰_j = 0`,
`δeᵃ₀ = δβ^a`, `δeᵃ_j = δE_{aj}`. -/
def admLinA (S : M3) (n : ℝ) (b : Fin 3 → ℝ) : A4 :=
  fun I μ => Fin.cases (motive := fun _ => ℝ) (Fin.cases (motive := fun _ => ℝ) n (fun _ => 0) μ)
    (fun a => Fin.cases (motive := fun _ => ℝ) (b a) (fun j => S a j) μ) I

theorem admLinA_eq (S : M3) (n : ℝ) (b : Fin 3 → ℝ) :
    admLinA S n b = ![![n, 0, 0, 0], ![b 0, S 0 0, S 0 1, S 0 2], ![b 1, S 1 0, S 1 1, S 1 2],
      ![b 2, S 2 0, S 2 1, S 2 2]] := by
  funext I μ
  fin_cases I <;> fin_cases μ <;> rfl

/-- The linearized load per unit `χ` at one site, from the jets `a i = δ_i u`, `V`, `n i = δ_i N`,
`b i = δ_i β` (`u`, `V` in `Sym₃` coordinates). -/
def Gfun (a : Fin 3 → Fin 6 → ℝ) (V : Fin 6 → ℝ) (n : Fin 3 → ℝ) (b : Fin 3 → Fin 3 → ℝ) :
    LocVal := fun μ k =>
  Fin.cases (motive := fun _ => ℝ)
    (∑ i, piLinVec (admLinA ((1 / 2 : ℝ) • symMat (a i)) (n i) (b i)) i k)
    (fun i => -piLinVec (admLinA ((1 / 2 : ℝ) • symMat V) 0 0) i k -
      ∑ j, sigLinVec (admLinA ((1 / 2 : ℝ) • symMat (a j)) (n j) (b j)) j i k) μ

/-- The Fierz–Pauli density at one site in jet variables. -/
def T1fun (a : Fin 3 → Fin 6 → ℝ) (V : Fin 6 → ℝ) (n : Fin 3 → ℝ) (b : Fin 3 → Fin 3 → ℝ) : ℝ :=
  let W : Fin 3 → Fin 3 → ℝ := fun p q => V (sym6 p q) - (b p q + b q p)
  let um : Fin 3 → Fin 3 → Fin 3 → ℝ := fun i p q => a i (sym6 p q)
  let ta : Fin 3 → ℝ := fun i => ∑ p, um i p p
  let vv : Fin 3 → ℝ := fun j => ∑ i, um i i j
  (1 / 4 : ℝ) * ((∑ p, ∑ q, W p q ^ 2) - (∑ p, W p p) ^ 2) -
    ((1 / 4 : ℝ) * (∑ i, ∑ p, ∑ q, um i p q ^ 2) - (1 / 2 : ℝ) * (∑ j, vv j ^ 2) +
      (1 / 2 : ℝ) * (∑ j, vv j * ta j) - (1 / 4 : ℝ) * (∑ j, ta j ^ 2)) +
    (-(∑ i, n i * ∑ j, um j i j) + ∑ i, n i * ta i)

/-- The antisymmetrized remainder `D₁` (nine terms `δ_i f δ_j g - δ_j f δ_i g`). -/
def D1fun (a : Fin 3 → Fin 6 → ℝ) : ℝ :=
  -(1 / 2 : ℝ) * (a 0 0 * a 1 3 - a 1 0 * a 0 3) - (1 / 2 : ℝ) * (a 0 0 * a 2 4 - a 2 0 * a 0 4) +
  (1 / 2 : ℝ) * (a 0 1 * a 1 3 - a 1 1 * a 0 3) + (1 / 2 : ℝ) * (a 0 2 * a 2 4 - a 2 2 * a 0 4) -
  (1 / 2 : ℝ) * (a 0 3 * a 2 5 - a 2 3 * a 0 5) - (1 / 2 : ℝ) * (a 0 4 * a 1 5 - a 1 4 * a 0 5) -
  (1 / 2 : ℝ) * (a 1 1 * a 2 5 - a 2 1 * a 1 5) + (1 / 2 : ℝ) * (a 1 2 * a 2 5 - a 2 2 * a 1 5) -
  (1 / 2 : ℝ) * (a 1 3 * a 2 4 - a 2 3 * a 1 4)

/-- The linearized load per unit `χ`, entry by entry. -/
def Gexp (a : Fin 3 → Fin 6 → ℝ) (V : Fin 6 → ℝ) (n : Fin 3 → ℝ) (b : Fin 3 → Fin 3 → ℝ) :
    LocVal :=
  ![![(a 0 1/2 + a 0 2/2 - a 1 3/2 - a 2 4/2), (-a 0 3/2 + a 1 0/2 + a 1 2/2 - a 2 5/2),
      (-a 0 4/2 - a 1 5/2 + a 2 0/2 + a 2 1/2), (0), (0), (0)],
    ![(-V 1/2 - V 2/2 + b 1 1 + b 2 2), (V 3/2 - b 1 0), (V 4/2 - b 2 0), (-a 1 4/2 + a 2 3/2),
      (-a 1 5/2 + a 2 1/2 + n 2), (-a 1 2/2 + a 2 5/2 - n 1)],
    ![(V 3/2 - b 0 1), (-V 0/2 - V 2/2 + b 0 0 + b 2 2), (V 5/2 - b 2 1), (a 0 4/2 - a 2 0/2 - n 2),
      (a 0 5/2 - a 2 3/2), (a 0 2/2 - a 2 4/2 + n 0)],
    ![(V 4/2 - b 0 2), (V 5/2 - b 1 2), (-V 0/2 - V 1/2 + b 0 0 + b 1 1), (-a 0 3/2 + a 1 0/2 + n 1),
      (-a 0 1/2 + a 1 3/2 - n 0), (-a 0 5/2 + a 1 4/2)]]

set_option maxHeartbeats 2000000 in
-- 24 entries
theorem Gfun_eq_Gexp (a : Fin 3 → Fin 6 → ℝ) (V : Fin 6 → ℝ) (n : Fin 3 → ℝ)
    (b : Fin 3 → Fin 3 → ℝ) : Gfun a V n b = Gexp a V n b := by
  funext μ k
  refine Fin.cases ?_ (fun i => ?_) μ
  · simp only [Gfun, Fin.cases_zero]
    fin_cases k <;>
      simp [Gexp, piLinVec, sigLinVec, admLinA_eq, symMat, sym6, Fin.sum_univ_three] <;> ring
  · simp only [Gfun, Fin.cases_succ]
    fin_cases i <;> fin_cases k <;>
      simp [Gexp, piLinVec, sigLinVec, admLinA_eq, symMat, sym6, Fin.sum_univ_three] <;> ring

set_option maxHeartbeats 2000000 in
-- the flat Cartan quadratic form in the 24 coordinates
theorem bdot_cartFlatInv_eq (y : LocVal) : bdot y (cartFlatInv y) =
    y 0 0^2 - 2*y 0 0*y 2 5 + 2*y 0 0*y 3 4 + y 0 1^2 + 2*y 0 1*y 1 5 - 2*y 0 1*y 3 3 + y 0 2^2 -
    2*y 0 2*y 1 4 + 2*y 0 2*y 2 3 - y 0 3^2 - 2*y 0 3*y 2 2 + 2*y 0 3*y 3 1 - y 0 4^2 +
    2*y 0 4*y 1 2 - 2*y 0 4*y 3 0 - y 0 5^2 - 2*y 0 5*y 1 1 + 2*y 0 5*y 2 0 - y 1 0^2 +
    2*y 1 0*y 2 1 + 2*y 1 0*y 3 2 - y 1 1^2 - 2*y 1 1*y 2 0 - y 1 2^2 - 2*y 1 2*y 3 0 + y 1 3^2 -
    2*y 1 3*y 2 4 - 2*y 1 3*y 3 5 + y 1 4^2 + 2*y 1 4*y 2 3 + y 1 5^2 + 2*y 1 5*y 3 3 - y 2 0^2 -
    y 2 1^2 + 2*y 2 1*y 3 2 - y 2 2^2 - 2*y 2 2*y 3 1 + y 2 3^2 + y 2 4^2 - 2*y 2 4*y 3 5 + y 2 5^2 +
    2*y 2 5*y 3 4 - y 3 0^2 - y 3 1^2 - y 3 2^2 + y 3 3^2 + y 3 4^2 + y 3 5^2 := by
  simp only [bdot, cartFlatInv, gram, Fin.sum_univ_four, Fin.sum_univ_six]
  simp
  ring

set_option maxHeartbeats 4000000 in
-- one polynomial identity in 36 variables
/-- **The single-site identity**: `-½⟨G, C₀⁻¹G⟩_b = T₁ + D₁`. -/
theorem site_identity (a : Fin 3 → Fin 6 → ℝ) (V : Fin 6 → ℝ) (n : Fin 3 → ℝ)
    (b : Fin 3 → Fin 3 → ℝ) :
    -(1 / 2 : ℝ) * bdot (Gfun a V n b) (cartFlatInv (Gfun a V n b)) = T1fun a V n b + D1fun a := by
  rw [Gfun_eq_Gexp, bdot_cartFlatInv_eq]
  simp only [Gexp, T1fun, D1fun, sym6, Fin.sum_univ_three]
  simp
  ring

/-! ### The linearized ADM coframe -/

theorem admLinA_add (S S' : M3) (n n' : ℝ) (b b' : Fin 3 → ℝ) :
    admLinA (S + S') (n + n') (b + b') = admLinA S n b + admLinA S' n' b' := by
  rw [admLinA_eq, admLinA_eq, admLinA_eq]
  funext I μ
  fin_cases I <;> fin_cases μ <;> simp

theorem admLinA_smul (c : ℝ) (S : M3) (n : ℝ) (b : Fin 3 → ℝ) :
    admLinA (c • S) (c * n) (c • b) = c • admLinA S n b := by
  rw [admLinA_eq, admLinA_eq]
  funext I μ
  fin_cases I <;> fin_cases μ <;> simp

/-- Point data `(g, n, β)` of the ADM coframe at one site. -/
abbrev PtD := (Fin 6 → ℝ) × ℝ × (Fin 3 → ℝ)

/-- The ADM coframe array `(g, n, β) ↦ admCoframe(E(g), n, β)` with the symmetric-square-root
triad. -/
def admU (p : PtD) : A4 := fun I μ => admCoframe (sqrtTriad (symMat p.1)) p.2.1 p.2.2 I μ

/-- The flat point data `(I, 1, 0)`. -/
def flatP : PtD := (flatSym, 1, 0)

theorem admU_flat : admU flatP = one4 := by
  funext I μ
  simp only [admU, flatP, symMat_flatSym, sqrtTriad_one, one4]
  rw [show (one3 : M3) = (1 : Matrix (Fin 3) (Fin 3) ℝ) from rfl, admCoframe_flat]

/-- The linearized ADM coframe `(w, n, b) ↦ δe(½ w, n, b)` as a linear map. -/
def admLinL : PtD →ₗ[ℝ] A4 where
  toFun d := admLinA ((1 / 2 : ℝ) • symMat d.1) d.2.1 d.2.2
  map_add' d d' := by
    rw [← admLinA_add]
    congr 1
    funext i j; simp [symMat, mul_add]
  map_smul' c d := by
    rw [RingHom.id_apply, ← admLinA_smul]
    congr 1
    funext i j; simp [symMat]; ring

/-- The linearized ADM coframe as a continuous linear map. -/
def admLinD : PtD →L[ℝ] A4 := LinearMap.toContinuousLinearMap admLinL

@[simp] theorem admLinD_apply (d : PtD) :
    admLinD d = admLinA ((1 / 2 : ℝ) • symMat d.1) d.2.1 d.2.2 := rfl

/-- `symMat` as a continuous linear map. -/
def symMatL : (Fin 6 → ℝ) →L[ℝ] M3 :=
  LinearMap.toContinuousLinearMap
    { toFun := symMat
      map_add' := fun c d => by funext i j; simp [symMat]
      map_smul' := fun c d => by funext i j; simp [symMat] }

@[simp] theorem symMatL_apply (c : Fin 6 → ℝ) : symMatL c = symMat c := rfl

theorem hasFDerivAt_triad_flatP :
    HasFDerivAt (fun p : PtD => sqrtTriad (symMat p.1))
      (((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ M3).comp
        (symMatL.comp (ContinuousLinearMap.fst ℝ (Fin 6 → ℝ) (ℝ × (Fin 3 → ℝ))))) flatP := by
  have h1 : HasFDerivAt sqrtTriad ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ M3)
      ((fun p : PtD => symMat p.1) flatP) := by
    simp only [flatP, symMat_flatSym]; exact hasFDerivAt_sqrtTriad
  exact HasFDerivAt.comp (g := sqrtTriad) (f := fun p : PtD => symMat p.1) flatP h1
    (symMatL.comp (ContinuousLinearMap.fst ℝ (Fin 6 → ℝ) (ℝ × (Fin 3 → ℝ)))).hasFDerivAt

/-- **Derivative of the ADM coframe at flat data**: `D e(I, 1, 0)(w, n, b) = δe(½ w, n, b)`
(the symmetric square root has `DE(I) = ½ id`). -/
theorem hasFDerivAt_admU : HasFDerivAt admU admLinD flatP := by
  have hT := hasFDerivAt_triad_flatP
  have hTe : ∀ a j : Fin 3, HasFDerivAt (fun p : PtD => sqrtTriad (symMat p.1) a j)
      ((ContinuousLinearMap.proj j).comp ((ContinuousLinearMap.proj a).comp
        (((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ M3).comp
          (symMatL.comp (ContinuousLinearMap.fst ℝ (Fin 6 → ℝ) (ℝ × (Fin 3 → ℝ))))))) flatP :=
    fun a j => HasFDerivAt.comp (g := ⇑((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => Fin 3 → ℝ) a)))
      (f := fun p : PtD => sqrtTriad (symMat p.1)) flatP (ContinuousLinearMap.hasFDerivAt _) hT
  have hβ : ∀ j : Fin 3, HasFDerivAt (fun p : PtD => p.2.2 j)
      ((ContinuousLinearMap.proj j).comp ((ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ)).comp
        (ContinuousLinearMap.snd ℝ (Fin 6 → ℝ) (ℝ × (Fin 3 → ℝ))))) flatP :=
    fun j => ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j).comp
      ((ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ)).comp
        (ContinuousLinearMap.snd ℝ (Fin 6 → ℝ) (ℝ × (Fin 3 → ℝ))))).hasFDerivAt
  have hn : HasFDerivAt (fun p : PtD => p.2.1)
      ((ContinuousLinearMap.fst ℝ ℝ (Fin 3 → ℝ)).comp
        (ContinuousLinearMap.snd ℝ (Fin 6 → ℝ) (ℝ × (Fin 3 → ℝ)))) flatP :=
    ((ContinuousLinearMap.fst ℝ ℝ (Fin 3 → ℝ)).comp
        (ContinuousLinearMap.snd ℝ (Fin 6 → ℝ) (ℝ × (Fin 3 → ℝ)))).hasFDerivAt
  rw [hasFDerivAt_pi']
  intro I
  rw [hasFDerivAt_pi']
  intro μ
  cases I using Fin.cases with
  | zero =>
    cases μ using Fin.cases with
    | zero =>
      refine hn.congr_fderiv (ContinuousLinearMap.ext fun d => ?_)
      simp [admLinA]
    | succ j =>
      refine (hasFDerivAt_const (0 : ℝ) flatP).congr_fderiv (ContinuousLinearMap.ext fun d => ?_)
      simp [admLinA]
  | succ a =>
    cases μ using Fin.cases with
    | zero =>
      have hs : HasFDerivAt (fun p : PtD => ∑ j, sqrtTriad (symMat p.1) a j * p.2.2 j)
          (∑ j, (sqrtTriad (symMat flatP.1) a j • (ContinuousLinearMap.proj j).comp
            ((ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ)).comp
              (ContinuousLinearMap.snd ℝ (Fin 6 → ℝ) (ℝ × (Fin 3 → ℝ)))) +
            flatP.2.2 j • (ContinuousLinearMap.proj j).comp ((ContinuousLinearMap.proj a).comp
              (((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ M3).comp
                (symMatL.comp (ContinuousLinearMap.fst ℝ (Fin 6 → ℝ) (ℝ × (Fin 3 → ℝ)))))))) flatP :=
        HasFDerivAt.fun_sum fun j _ => (hTe a j).mul (hβ j)
      refine hs.congr_fderiv (ContinuousLinearMap.ext fun d => ?_)
      simp [admLinA, flatP, symMat_flatSym, sqrtTriad_one, one3_apply]
    | succ j =>
      refine (hTe a j).congr_fderiv (ContinuousLinearMap.ext fun d => ?_)
      simp [admLinA]

/-! ### Derivatives of the coefficient arrays and of the load -/

/-- `Π_i(e)` as an array. -/
def piArrA (χ : ℝ) (i : Fin 3) (e : A4) : A4 := dualA χ (palBil e e 0 i.succ)

/-- `Σ_ij(e)` as an array. -/
def sigArrA (χ : ℝ) (i j : Fin 3) (e : A4) : A4 := dualA χ (palBil e e i.succ j.succ)

/-- `DΠ_i(1)` as a continuous linear map on arrays. -/
def piArrADer (χ : ℝ) (i : Fin 3) : A4 →L[ℝ] A4 :=
  LinearMap.toContinuousLinearMap (dualALin χ ∘ₗ palLinALin 0 i.succ)

/-- `DΣ_ij(1)` as a continuous linear map on arrays. -/
def sigArrADer (χ : ℝ) (i j : Fin 3) : A4 →L[ℝ] A4 :=
  LinearMap.toContinuousLinearMap (dualALin χ ∘ₗ palLinALin i.succ j.succ)

theorem piArrADer_apply (χ : ℝ) (i : Fin 3) (δ : A4) :
    piArrADer χ i δ = dualA χ (palLinA δ 0 i.succ) := rfl

theorem sigArrADer_apply (χ : ℝ) (i j : Fin 3) (δ : A4) :
    sigArrADer χ i j δ = dualA χ (palLinA δ i.succ j.succ) := rfl

theorem hasFDerivAt_piArrA (χ : ℝ) (i : Fin 3) :
    HasFDerivAt (piArrA χ i) (piArrADer χ i) one4 := by
  refine hasFDerivAt_of_bilinear_remainder
    (toCLM₂ ((palBilLin 0 i.succ).compr₂ (dualALin χ))) fun δ => ?_
  simp only [piArrA, palBil_one4_add, dualA_add, toCLM₂_apply, LinearMap.compr₂_apply]
  simp [piArrADer, palBilLin, dualALin, palLinALin]
  abel

theorem hasFDerivAt_sigArrA (χ : ℝ) (i j : Fin 3) :
    HasFDerivAt (sigArrA χ i j) (sigArrADer χ i j) one4 := by
  refine hasFDerivAt_of_bilinear_remainder
    (toCLM₂ ((palBilLin i.succ j.succ).compr₂ (dualALin χ))) fun δ => ?_
  simp only [sigArrA, palBil_one4_add, dualA_add, toCLM₂_apply, LinearMap.compr₂_apply]
  simp [sigArrADer, palBilLin, dualALin, palLinALin]
  abel

/-- `coordP` as a continuous linear map. -/
def coordPCLM : A4 →L[ℝ] (Fin 6 → ℝ) := LinearMap.toContinuousLinearMap coordPLin

@[simp] theorem coordPCLM_apply (X : A4) : coordPCLM X = coordP X := rfl

/-- The point data of a configuration at a site. -/
def ptProjL (y : Site N) : (ParF N × MetF N) →ₗ[ℝ] PtD where
  toFun z := (z.1.1 y, z.1.2.1 y, z.1.2.2 y)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The point-data projection at a site. -/
def ptProj (y : Site N) : (ParF N × MetF N) →L[ℝ] PtD := LinearMap.toContinuousLinearMap (ptProjL y)

@[simp] theorem ptProj_apply (y : Site N) (z : ParF N × MetF N) :
    ptProj y z = (z.1.1 y, z.1.2.1 y, z.1.2.2 y) := rfl

theorem ptProj_flat (y : Site N) : ptProj y (zFlat N) = flatP := rfl

/-- The coframe array of a configuration at a site. -/
def eArr (z : ParF N × MetF N) (y : Site N) : A4 := admU (ptProj y z)

theorem eArr_flat (y : Site N) : eArr (zFlat N) y = one4 := by
  rw [eArr, ptProj_flat, admU_flat]

theorem hasFDerivAt_eArr (y : Site N) :
    HasFDerivAt (fun z => eArr z y) (admLinD.comp (ptProj y)) (zFlat N) := by
  have h1 : HasFDerivAt admU admLinD (ptProj y (zFlat N)) := by
    rw [ptProj_flat]; exact hasFDerivAt_admU
  exact HasFDerivAt.comp (g := admU) (f := fun z => ptProj y z) (zFlat N) h1
    (ptProj y).hasFDerivAt

/-- The coordinate field of `Π_i` along a configuration. -/
def piF (χ : ℝ) (i : Fin 3) (z : ParF N × MetF N) : Site N → Fin 6 → ℝ :=
  fun y => coordP (piArrA χ i (eArr z y))

/-- The coordinate field of `Σ_ji` along a configuration. -/
def sigF (χ : ℝ) (j i : Fin 3) (z : ParF N × MetF N) : Site N → Fin 6 → ℝ :=
  fun y => coordP (sigArrA χ j i (eArr z y))

theorem hasFDerivAt_piF (χ : ℝ) (i : Fin 3) :
    HasFDerivAt (piF (N := N) χ i) (ContinuousLinearMap.pi fun y =>
      coordPCLM.comp ((piArrADer χ i).comp (admLinD.comp (ptProj y)))) (zFlat N) := by
  show HasFDerivAt (fun z y => coordP (piArrA χ i (eArr z y))) _ _
  rw [hasFDerivAt_pi]
  intro y
  have h1 : HasFDerivAt (piArrA χ i) (piArrADer χ i) (eArr (zFlat N) y) := by
    rw [eArr_flat]; exact hasFDerivAt_piArrA χ i
  have h2 := HasFDerivAt.comp (g := piArrA χ i) (f := fun z => eArr z y) (zFlat N) h1
    (hasFDerivAt_eArr y)
  exact HasFDerivAt.comp (g := ⇑coordPCLM) (f := fun z => piArrA χ i (eArr z y)) (zFlat N)
    (coordPCLM.hasFDerivAt) h2

theorem hasFDerivAt_sigF (χ : ℝ) (j i : Fin 3) :
    HasFDerivAt (sigF (N := N) χ j i) (ContinuousLinearMap.pi fun y =>
      coordPCLM.comp ((sigArrADer χ j i).comp (admLinD.comp (ptProj y)))) (zFlat N) := by
  show HasFDerivAt (fun z y => coordP (sigArrA χ j i (eArr z y))) _ _
  rw [hasFDerivAt_pi]
  intro y
  have h1 : HasFDerivAt (sigArrA χ j i) (sigArrADer χ j i) (eArr (zFlat N) y) := by
    rw [eArr_flat]; exact hasFDerivAt_sigArrA χ j i
  have h2 := HasFDerivAt.comp (g := sigArrA χ j i) (f := fun z => eArr z y) (zFlat N) h1
    (hasFDerivAt_eArr y)
  exact HasFDerivAt.comp (g := ⇑coordPCLM) (f := fun z => sigArrA χ j i (eArr z y)) (zFlat N)
    (coordPCLM.hasFDerivAt) h2

/-- `Π_i` of the unit-lapse zero-shift ADM coframe as a function of the metric. -/
theorem piEntry_eq (χ : ℝ) (i : Fin 3) (K L : Fin 4) :
    piEntry χ sqrtTriad i K L = fun g => piArrA χ i (admU (g, 1, 0)) K L := by
  funext g
  simp only [piEntry, piArrA]
  rw [show admCoframe (sqrtTriad (symMat g)) 1 0 = Matrix.of (admU (g, 1, 0)) from rfl, piArr_of]
  rfl

/-- The derivative of `g ↦ Π_i(e(g, 1, 0))` at the flat metric. -/
theorem hasFDerivAt_piArrA_metric (χ : ℝ) (i : Fin 3) :
    HasFDerivAt (fun g : Fin 6 → ℝ => piArrA χ i (admU (g, 1, 0)))
      ((piArrADer χ i).comp (admLinD.comp (ContinuousLinearMap.inl ℝ (Fin 6 → ℝ)
        (ℝ × (Fin 3 → ℝ))))) flatSym := by
  have hin : HasFDerivAt (fun g : Fin 6 → ℝ => ((g, 1, 0) : PtD))
      (ContinuousLinearMap.inl ℝ (Fin 6 → ℝ) (ℝ × (Fin 3 → ℝ))) flatSym :=
    (hasFDerivAt_id flatSym).prodMk (hasFDerivAt_const _ _)
  have h1 : HasFDerivAt admU admLinD ((fun g : Fin 6 → ℝ => ((g, 1, 0) : PtD)) flatSym) :=
    hasFDerivAt_admU
  have h2 := HasFDerivAt.comp (g := admU) (f := fun g : Fin 6 → ℝ => ((g, 1, 0) : PtD)) flatSym
    h1 hin
  have h3 : HasFDerivAt (piArrA χ i) (piArrADer χ i)
      (admU ((fun g : Fin 6 → ℝ => ((g, 1, 0) : PtD)) flatSym)) := by
    show HasFDerivAt (piArrA χ i) (piArrADer χ i) (admU flatP)
    rw [admU_flat]; exact hasFDerivAt_piArrA χ i
  exact HasFDerivAt.comp (g := piArrA χ i)
    (f := fun g : Fin 6 → ℝ => admU (g, 1, 0)) flatSym h3 h2

/-- **`∂_tΠ_i` at flat data**: `D_γ[Π_i(e(γ))](w) = DΠ_i(1)[δe(½ w, 0, 0)]`. -/
theorem fderiv_piEntry_flat (χ : ℝ) (i : Fin 3) (K L : Fin 4) (w : Fin 6 → ℝ) :
    fderiv ℝ (piEntry χ sqrtTriad i K L) flatSym w = piArrADer χ i (admLinD (w, 0, 0)) K L := by
  rw [piEntry_eq]
  have h := hasFDerivAt_piArrA_metric χ i
  have hK : HasFDerivAt (fun g : Fin 6 → ℝ => piArrA χ i (admU (g, 1, 0)) K L)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) L).comp
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => Fin 4 → ℝ) K).comp
          ((piArrADer χ i).comp (admLinD.comp (ContinuousLinearMap.inl ℝ (Fin 6 → ℝ)
            (ℝ × (Fin 3 → ℝ))))))) flatSym :=
    HasFDerivAt.comp (g := ⇑((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) L).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => Fin 4 → ℝ) K)))
      (f := fun g : Fin 6 → ℝ => piArrA χ i (admU (g, 1, 0))) flatSym
      (ContinuousLinearMap.hasFDerivAt _) h
  rw [hK.fderiv]
  rfl

/-- The `Π`-velocity array of a configuration. -/
def PF (χ : ℝ) (i : Fin 3) (x : Site N) (z : ParF N × MetF N) : A4 :=
  fun K L => piDot χ sqrtTriad z.1.1 z.2 i x K L

theorem hasFDerivAt_PF (χ : ℝ) (i : Fin 3) (x : Site N) :
    HasFDerivAt (PF χ i x) ((piArrADer χ i).comp (admLinD.comp ((ContinuousLinearMap.inl ℝ
      (Fin 6 → ℝ) (ℝ × (Fin 3 → ℝ))).comp ((ContinuousLinearMap.proj x).comp
        (ContinuousLinearMap.snd ℝ (ParF N) (MetF N)))))) (zFlat N) := by
  have htr : AnalyticAt ℝ sqrtTriad (symMat flatSym) := by
    rw [symMat_flatSym]; exact analyticAt_sqrtTriad
  rw [hasFDerivAt_pi']
  intro K
  rw [hasFDerivAt_pi']
  intro L
  have hc0 := (analyticAt_piEntry χ htr i K L).fderiv.differentiableAt.hasFDerivAt
  have hγ : HasFDerivAt (fun z : ParF N × MetF N => z.1.1 x)
      ((ContinuousLinearMap.proj x).comp ((ContinuousLinearMap.fst ℝ (MetF N)
        ((Site N → ℝ) × (Site N → Fin 3 → ℝ))).comp
          (ContinuousLinearMap.fst ℝ (ParF N) (MetF N)))) (zFlat N) :=
    ((ContinuousLinearMap.proj x).comp ((ContinuousLinearMap.fst ℝ (MetF N)
        ((Site N → ℝ) × (Site N → Fin 3 → ℝ))).comp
          (ContinuousLinearMap.fst ℝ (ParF N) (MetF N)))).hasFDerivAt
  have hc := HasFDerivAt.comp (g := fderiv ℝ (piEntry χ sqrtTriad i K L))
    (f := fun z : ParF N × MetF N => z.1.1 x) (zFlat N) hc0 hγ
  have hu : HasFDerivAt (fun z : ParF N × MetF N => z.2 x)
      ((ContinuousLinearMap.proj x).comp (ContinuousLinearMap.snd ℝ (ParF N) (MetF N)))
      (zFlat N) :=
    ((ContinuousLinearMap.proj x).comp (ContinuousLinearMap.snd ℝ (ParF N) (MetF N))).hasFDerivAt
  have hcu := hc.clm_apply hu
  refine hcu.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  have h0 : (zFlat N).2 x = 0 := rfl
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, Function.comp_apply, h0, map_zero, add_zero]
  rw [show (zFlat N).1.1 x = flatSym from rfl, fderiv_piEntry_flat]
  rfl

/-! ### The explicit linearized load -/

open OddPhaseDerivativeReal in
/-- The phase derivative as a continuous linear map on coordinate fields. -/
def pdC (i : Fin 3) : (Site N → Fin 6 → ℝ) →L[ℝ] (Site N → Fin 6 → ℝ) :=
  LinearMap.toContinuousLinearMap (pd (N := N) i)

/-- `coord` as a linear map. -/
def coordLin : M4 →ₗ[ℝ] (Fin 6 → ℝ) where
  toFun := coord
  map_add' := coord_add
  map_smul' := coord_smul

open OddPhaseDerivativeReal in
theorem coord_pd (i : Fin 3) (F : Site N → M4) (x : Site N) :
    coord (pd i F x) = pd i (fun y => coord (F y)) x :=
  (congrFun (pd_map i coordLin F) x).symm

theorem coord_piArr_eArr (χ : ℝ) (i : Fin 3) (z : ParF N × MetF N) (y : Site N) :
    coord (piArr χ (coframeField sqrtTriad z.1 y) i) = coordP (piArrA χ i (eArr z y)) := by
  show coord (piArr χ (Matrix.of (eArr z y)) i) = _
  rw [piArr_of]; rfl

theorem coord_sigmaArr_eArr (χ : ℝ) (j i : Fin 3) (z : ParF N × MetF N) (y : Site N) :
    coord (sigmaArr χ (coframeField sqrtTriad z.1 y) j i) = coordP (sigArrA χ j i (eArr z y)) := by
  show coord (sigmaArr χ (Matrix.of (eArr z y)) j i) = _
  rw [sigmaArr_of]; rfl

open OddPhaseDerivativeReal in
/-- The temporal row of the load: `f°_0 = Σ_i δ_i coord Π_i`. -/
theorem loadF_zero (χ : ℝ) (z : ParF N × MetF N) (x : Site N) :
    loadF χ z x 0 = ∑ i, pd i (piF χ i z) x := by
  simp only [loadF, fPh, Fin.cases_zero, dataMap, load0Ph]
  rw [coord_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coord_pd]
  rfl

open OddPhaseDerivativeReal in
/-- The spatial rows of the load: `f°_i = -coord ∂_tΠ_i - Σ_j δ_j coord Σ_ji`. -/
theorem loadF_succ (χ : ℝ) (z : ParF N × MetF N) (x : Site N) (i : Fin 3) :
    loadF χ z x i.succ = -coordP (PF χ i x z) - ∑ j, pd j (sigF χ j i z) x := by
  simp only [loadF, fPh, Fin.cases_succ, dataMap, loadSpPh]
  rw [coord_add, coord_neg, coord_neg, coord_sum, sub_eq_add_neg]
  congr 1
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coord_pd]
  rfl

open OddPhaseDerivativeReal in
theorem pd_ptProj (i : Fin 3) (v : ParF N × MetF N) (x : Site N) :
    pd i (fun y => ptProj y v) x = (pd i v.1.1 x, pd i v.1.2.1 x, pd i v.1.2.2 x) := by
  have h1 := congrFun (pd_map i (LinearMap.fst ℝ (Fin 6 → ℝ) (ℝ × (Fin 3 → ℝ)))
    (fun y => ptProj y v)) x
  have h2 := congrFun (pd_map i ((LinearMap.fst ℝ ℝ (Fin 3 → ℝ)).comp
    (LinearMap.snd ℝ (Fin 6 → ℝ) (ℝ × (Fin 3 → ℝ)))) (fun y => ptProj y v)) x
  have h3 := congrFun (pd_map i ((LinearMap.snd ℝ ℝ (Fin 3 → ℝ)).comp
    (LinearMap.snd ℝ (Fin 6 → ℝ) (ℝ × (Fin 3 → ℝ)))) (fun y => ptProj y v)) x
  simp only [LinearMap.fst_apply, LinearMap.comp_apply, LinearMap.snd_apply, ptProj_apply] at h1 h2 h3
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simpa using h1.symm
  · simpa using h2.symm
  · simpa using h3.symm

open OddPhaseDerivativeReal in
/-- **The explicit linearized load** at flat data: `F₁ v (x) = χ · G(jets of v at x)`, with
`G = Gfun (δ_i u, V, δ_i N, δ_i β)`. -/
theorem loadDer_eq (χ : ℝ) (v : ParF N × MetF N) (x : Site N) :
    loadDer χ v x = χ • Gfun (fun i => pd i v.1.1 x) (v.2 x) (fun i => pd i v.1.2.1 x)
      (fun i => pd i v.1.2.2 x) := by
  have hL : HasFDerivAt (loadF χ) (loadDer χ) (zFlat N) :=
    (analyticAt_loadF χ).differentiableAt.hasFDerivAt
  have hcomp : ∀ μ : Fin 4, HasFDerivAt (fun z => loadF χ z x μ)
      (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => Fin 6 → ℝ) μ).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Site N => LocVal) x)).comp (loadDer χ))
      (zFlat N) := fun μ =>
    HasFDerivAt.comp (g := ⇑((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => Fin 6 → ℝ)
        μ).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Site N => LocVal) x)))
      (f := loadF χ) (zFlat N) (ContinuousLinearMap.hasFDerivAt _) hL
  have hpd : ∀ i, HasFDerivAt (fun z => pd i (piF χ i z) x)
      (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Site N => Fin 6 → ℝ) x).comp (pdC i)).comp
        (ContinuousLinearMap.pi fun y =>
          coordPCLM.comp ((piArrADer χ i).comp (admLinD.comp (ptProj y))))) (zFlat N) :=
    fun i => HasFDerivAt.comp (g := ⇑((ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Site N => Fin 6 → ℝ) x).comp (pdC i)))
      (f := piF χ i) (zFlat N) (ContinuousLinearMap.hasFDerivAt _) (hasFDerivAt_piF χ i)
  have hsd : ∀ i j, HasFDerivAt (fun z => pd j (sigF χ j i z) x)
      (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Site N => Fin 6 → ℝ) x).comp (pdC j)).comp
        (ContinuousLinearMap.pi fun y =>
          coordPCLM.comp ((sigArrADer χ j i).comp (admLinD.comp (ptProj y))))) (zFlat N) :=
    fun i j => HasFDerivAt.comp (g := ⇑((ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Site N => Fin 6 → ℝ) x).comp (pdC j)))
      (f := sigF χ j i) (zFlat N) (ContinuousLinearMap.hasFDerivAt _) (hasFDerivAt_sigF χ j i)
  -- the jet identity for a fixed continuous linear map of the point data
  have hjet : ∀ (i : Fin 3) (C : PtD →L[ℝ] (Fin 6 → ℝ)),
      pd i (fun y => C (ptProj y v)) x = C (pd i v.1.1 x, pd i v.1.2.1 x, pd i v.1.2.2 x) := by
    intro i C
    rw [pd_map_clm]
    exact congrArg C (pd_ptProj i v x)
  funext μ
  refine Fin.cases ?_ (fun i => ?_) μ
  · have h0 := hcomp 0
    have heq : (fun z => loadF χ z x 0) = fun z => ∑ i, pd i (piF χ i z) x :=
      funext fun z => loadF_zero χ z x
    rw [heq] at h0
    have hu := h0.unique (HasFDerivAt.fun_sum fun i _ => hpd i)
    have hv := congrArg (fun T : (ParF N × MetF N) →L[ℝ] (Fin 6 → ℝ) => T v) hu
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_sum',
      Finset.sum_apply] at hv
    rw [show loadDer χ v x 0 = _ from hv]
    funext k
    simp only [Gfun, Fin.cases_zero, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hjet i (coordPCLM.comp ((piArrADer χ i).comp admLinD))
    simp only [ContinuousLinearMap.comp_apply, coordPCLM_apply] at this
    have hpi : (ContinuousLinearMap.pi fun y =>
        coordPCLM.comp ((piArrADer χ i).comp (admLinD.comp (ptProj y)))) v =
        fun y => coordP (piArrADer χ i (admLinD (ptProj y v))) := rfl
    simp only [pdC, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      LinearMap.coe_toContinuousLinearMap']
    rw [hpi, this, piArrADer_apply, coordP_dualA_palLinA_pi, admLinD_apply]
    rfl
  · have h0 := hcomp i.succ
    have heq : (fun z => loadF χ z x i.succ) =
        fun z => -coordP (PF χ i x z) - ∑ j, pd j (sigF χ j i z) x :=
      funext fun z => loadF_succ χ z x i
    rw [heq] at h0
    have hP := HasFDerivAt.comp (g := ⇑coordPCLM) (f := PF χ i x) (zFlat N)
      (ContinuousLinearMap.hasFDerivAt _) (hasFDerivAt_PF χ i x)
    have hu := h0.unique (hP.neg.sub (HasFDerivAt.fun_sum fun j _ => hsd i j))
    have hv := congrArg (fun T : (ParF N × MetF N) →L[ℝ] (Fin 6 → ℝ) => T v) hu
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply] at hv
    rw [show loadDer χ v x i.succ = _ from hv]
    funext k
    simp only [Gfun, Fin.cases_succ, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.neg_apply,
      Finset.sum_apply, mul_sub, mul_neg, Finset.mul_sum]
    congr 1
    · simp only [coordPCLM_apply, piArrADer_apply, admLinD_apply]
      rw [coordP_dualA_palLinA_pi]
      simp
    · refine Finset.sum_congr rfl fun j _ => ?_
      have := hjet j (coordPCLM.comp ((sigArrADer χ j i).comp admLinD))
      simp only [ContinuousLinearMap.comp_apply, coordPCLM_apply] at this
      have hpi : (ContinuousLinearMap.pi fun y =>
          coordPCLM.comp ((sigArrADer χ j i).comp (admLinD.comp (ptProj y)))) v =
          fun y => coordP (sigArrADer χ j i (admLinD (ptProj y v))) := rfl
      simp only [pdC, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
        LinearMap.coe_toContinuousLinearMap']
      rw [hpi, this, sigArrADer_apply, coordP_dualA_palLinA_sig, admLinD_apply]
      rfl

/-! ### The quadratic Ward identity and the Fierz–Pauli form -/

open OddPhaseDerivativeReal in
/-- **Exact swap identity** (skew-adjointness and commutation of the phase derivatives):
`Σ_x δ_i f δ_j g = Σ_x δ_j f δ_i g`. -/
theorem sum_pd_mul_swap (i j : Fin 3) (f g : Site N → ℝ) :
    ∑ x, pd i f x * pd j g x = ∑ x, pd j f x * pd i g x := by
  have h1 := pd_skew i (LinearMap.mul ℝ ℝ) f (pd j g)
  have h2 := pd_skew j (LinearMap.mul ℝ ℝ) f (pd i g)
  simp only [LinearMap.mul_apply'] at h1 h2
  rw [h1, h2, pd_comm]

open OddPhaseDerivativeReal in
/-- The antisymmetrized products of jets of a `Sym₃` field sum to zero. -/
theorem sum_asym_eq_zero (u : Site N → Fin 6 → ℝ) (i j : Fin 3) (f g : Fin 6) :
    ∑ x, (pd i u x f * pd j u x g - pd j u x f * pd i u x g) = 0 := by
  simp only [pd_pi_apply, Finset.sum_sub_distrib]
  rw [sum_pd_mul_swap i j (fun y => u y f) (fun y => u y g)]
  ring

open OddPhaseDerivativeReal in
/-- **The quadratic Ward identity**: the remainder `D₁` sums to zero over the grid. -/
theorem sum_D1fun_eq_zero (u : Site N → Fin 6 → ℝ) :
    ∑ x, D1fun (fun i => pd i u x) = 0 := by
  have key : ∀ (i j : Fin 3) (f g : Fin 6),
      ∑ x, pd i u x f * pd j u x g = ∑ x, pd j u x f * pd i u x g := fun i j f g =>
    sub_eq_zero.1 (by rw [← Finset.sum_sub_distrib]; exact sum_asym_eq_zero u i j f g)
  simp only [D1fun, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [key 0 1 0 3, key 0 2 0 4, key 0 1 1 3, key 0 2 2 4, key 0 2 3 5, key 0 1 4 5, key 1 2 1 5,
    key 1 2 2 5, key 1 2 3 4]
  ring

open OddPhaseDerivativeReal in
/-- **The Fierz–Pauli quadratic form** of a configuration direction `v = ((u, N, β), V)`
(`Sym₃` coordinates), in jet form: `Q_FP(v) = h³ Σ_x T₁(δu, V, δN, δβ)(x)`. -/
def QFP (v : ParF N × MetF N) : ℝ :=
  hN N ^ 3 * ∑ x, T1fun (fun i => pd i v.1.1 x) (v.2 x) (fun i => pd i v.1.2.1 x)
    (fun i => pd i v.1.2.2 x)

section Chart

variable {χ R : ℝ} {U : Set (CoP N)} (hU : FlatChart χ R U)
include hU

open OddPhaseDerivativeReal in
/-- **`thm:supp-exact-action-provenance` (iv), Lagrangian form**: the Hessian of the reduced
Lagrangian of the actual action at flat data is `2χ` times the Fierz–Pauli form:
`D²𝓛°_h(flat)(v, v) = 2χ Q_FP(v)`. -/
theorem hess_redLagr_flat (hχ : χ ≠ 0) (v : ParF N × MetF N) :
    fderiv ℝ (fderiv ℝ (redLagr χ 0 sqrtTriad (statAst χ R))) (zFlat N) v v = 2 * χ * QFP v := by
  rw [(redLagr_jet_flat hU hχ).2.2.2 v v, QFP]
  have hsite : ∀ x, bdot (χ⁻¹ • cartFlatInv (loadDer χ v x)) (loadDer χ v x) =
      -2 * χ * (T1fun (fun i => pd i v.1.1 x) (v.2 x) (fun i => pd i v.1.2.1 x)
        (fun i => pd i v.1.2.2 x) + D1fun (fun i => pd i v.1.1 x)) := by
    intro x
    rw [loadDer_eq, cartFlatInv_smul, smul_smul, inv_mul_cancel₀ hχ, one_smul, bdot_smul_right,
      bdot_comm, ← site_identity]
    ring
  simp only [hsite, ← Finset.mul_sum, Finset.sum_add_distrib, sum_D1fun_eq_zero, add_zero]
  ring

end Chart

end RenewalGeometry.ExactPhaseAction.QuadJet
