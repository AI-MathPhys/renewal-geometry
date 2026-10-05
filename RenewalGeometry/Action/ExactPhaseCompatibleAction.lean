/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactActionLorentzAlgebra
import RenewalGeometry.Algebra.MatrixExpDerivative
import RenewalGeometry.Analysis.NormedAlgebraLogBCH

/-!
# The explicit completed finite Palatini/link action and its connection normal form
  (`eq:supp-exact-links`, `eq:supp-exact-link-curvatures`, `eq:supp-exact-full-palatini`,
  `eq:supp-exact-J`, `eq:supp-exact-compensators`, `eq:supp-exact-completed-action`,
  `eq:supp-exact-connection-normal-form`, `eq:supp-exact-connection-load`;
  subsection `subsec:supp-exact-action-provenance`, emergent-spacetime manuscript)

On the periodic cubic regulator `Site N = (ℤ/N)³` (lattice spacing `h`; the paper's regulator is
`N = 2m+1`, `h = 1/N`), with coframe `e : Site → M4`, temporal connection `A₀ : Site → 𝔰𝔬(1,3)`,
spatial connection `A_i : Site → 𝔰𝔬(1,3)` and its time derivative `Ȧ_i`:

* links `U_i = exp(h A_i)` (`eq:supp-exact-links`; `M4` carries the `ℓ∞`-operator norm, a
  complete normed algebra with `‖1‖ = 1`);
* the **literal electric curvature** `E_i = h⁻¹(U̇_i U_i⁻¹ + A₀ - Ad_{U_i} A_{0,+i})`
  (`electric`, `elecField`), where `U̇_i = D exp(hA_i)[hȦ_i]` is the velocity of the link along
  a curve with connection velocity `Ȧ_i` (`linkVel`) and `U_i⁻¹ = exp(-hA_i)`;
* the **literal plaquette curvature** `B_ij = h⁻² log(U_i U_{j,+i} U_{i,+j}⁻¹ U_j⁻¹)`
  (`plaquette`, `plaqField`) with the retained logarithm branch the Mercator series
  `log(1 + Y) = Σ (-1)ⁿ Yⁿ⁺¹/(n+1)` (`LogBCH.logOnePlus`, the principal chart `‖Y‖ < 1`);
* `𝒥_Z V = Σ_k (ad_Z)^k V/(k+1)!` (`calJ`, `eq:supp-exact-J`, via `OperatorHalfCoth.dexpJ`);
* the full Palatini density `χ det(e)(r(e,F) - 2Λ)` (`fullDensity`, `eq:supp-exact-full-palatini`),
  the compensators `𝒦_h`, `q_h`, `q` (`kinComp`, `qh`, `qc`; `eq:supp-exact-compensators`,
  with `(X₁,…,X₄) = (A_i, A_{j,+i}, -A_{i,+j}, -A_j)` and `½Σ_{r<s}[X_r,X_s]` =
  `LogBCH.commTerm`), the completed density and the **completed action**
  `𝒫^c_{h,D} = 𝒫^full + ∫⟨q - q_h - 𝒦_h, 1⟩_h dt - [Σ_i⟨b(Π_i, A_i), 1⟩_h]_0^T`
  (`completedDensity`, `completedAction`; `eq:supp-exact-completed-action`).

Connection normal form (`eq:supp-exact-connection-normal-form`, `eq:supp-exact-connection-load`):

* `electric_decomp`: `E_i = 𝒥_{hA_i}Ȧ_i - D_i^+A₀ - [A_i, A_{0,+i}] - ρ^E` with the explicit
  cubic link remainder `ρ^E = h⁻¹(Ad_{e^{hA_i}} - I - h ad_{A_i})A_{0,+i}` (`remE`), and the
  plaquette remainder `ρ^B = B_ij - (D_i^+A_j - D_j^+A_i) - ½Σ_{r<s}[X_r,X_s]` (`remB`);
* `completedDensity_eq` (pointwise exact identity): the completed density equals
  `-2χΛ det e + Σ_i b(Π_i, Ȧ_i) - Σ_i b(Π_i, D_i^+A₀) + Σ_{i<j} b(Σ_ij, D_i^+A_j - D_j^+A_i)
   + q(A) + r_h(e, A)` with `r_h = -Σ_i b(Π_i, ρ^E_i) + Σ_{i<j} b(Σ_ij, ρ^B_ij)` (`remDensity`):
  **the kinetic subtraction removes the nonlinear connection-velocity terms exactly**;
* `sum_pairing_Dp` (exact summation by parts `Σ_x b(P, D_i^+u) = -Σ_x b(D_i^-P, u)`) and
  `gridPair_completedDensity_eq`: `⟨completed density, 1⟩_h = ⟨-2χΛ det e + f_{h,0}·A₀ +
  Σ_i (f^sp_{h,i})·A_i + q(A) + r_h, 1⟩_h + ⟨Σ_i b(Π_i, Ȧ_i), 1⟩_h`, with
  `f_{h,0} = Σ_i D_i^-Π_i`, `f^sp_{h,i} = -Σ_{j≠i} D_j^-Σ_ji` (`load0`, `loadSp`);
* `completedAction_eq_normalForm`: after the exact time integration by parts, for `C¹` paths,
  `𝒫^c_{h,D} = ∫₀ᵀ⟨-2χΛ det e + f_h(e)·A + q_e(A) + r_h(e,A), 1⟩_h dt` with
  `f_{h,i} = -∂_tΠ_i - Σ_{j≠i}D_j^-Σ_ji`; the boundary term of `eq:supp-exact-completed-action`
  cancels exactly.  Here `f·A` is the `b`-pairing `Σ_μ b(f_μ, A_μ)` (the operator `𝖧` of
  `eq:supp-exact-connection-load` is read as the identification of `𝔰𝔬(1,3)` with its dual by the
  invariant pairing `b`), and `½AᵀC(e)A` is the Cartan quadratic form `q_e(A)` (`qc`).
-/

open Finset NormedSpace

noncomputable section

namespace RenewalGeometry.ExactPhaseAction

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

set_option linter.unusedSectionVars false

open MatrixExpDerivative OperatorHalfCoth LogBCH PalatiniEinsteinAlgebra

/-! ### Local link algebra -/

/-- The Lie bracket `[X, Y] = XY - YX`. -/
def bracket (X Y : M4) : M4 := X * Y - Y * X

/-- `𝒥_Z V = Σ_{k ≥ 0} (ad_Z)^k V/(k+1)!` (`eq:supp-exact-J`). -/
def calJ (Z V : M4) : M4 := dexpJ (adOp Z) V

/-- The velocity `U̇ = D exp(hA)[hȦ]` of the link `U = exp(hA)` along a curve of connections with
velocity `Ȧ = adot`. -/
def linkVel (h : ℝ) (a adot : M4) : M4 := fderiv ℝ exp (h • a) (h • adot)

/-- The literal electric curvature `E = h⁻¹(U̇U⁻¹ + A₀ - Ad_U A_{0,+})` of a link `U = exp(h a)`
with temporal connection `a0` at the base point and `a0s` at the shifted point
(`eq:supp-exact-link-curvatures`), `U⁻¹ = exp(-h a)`. -/
def electric (h : ℝ) (a a0 a0s adot : M4) : M4 :=
  h⁻¹ • (linkVel h a adot * exp (-(h • a)) + a0 - exp (h • a) * a0s * exp (-(h • a)))

/-- The exponent list `(hX₁, …, hX₄)` of the oriented plaquette `U_i U_{j,+i} U_{i,+j}⁻¹ U_j⁻¹`,
`(X₁, X₂, X₃, X₄) = (A_i, A_{j,+i}, -A_{i,+j}, -A_j)`. -/
def plaqList (h : ℝ) (ai ajs ais aj : M4) : List M4 :=
  [h • ai, h • ajs, -(h • ais), -(h • aj)]

/-- The literal plaquette curvature `B = h⁻² log(U_i U_{j,+i} U_{i,+j}⁻¹ U_j⁻¹)` on the retained
(principal Mercator-series) logarithm branch (`eq:supp-exact-link-curvatures`). -/
def plaquette (h : ℝ) (ai ajs ais aj : M4) : M4 :=
  (h ^ 2)⁻¹ • logOnePlus (expProd (plaqList h ai ajs ais aj) - 1)

/-- The unscaled plaquette list `(X₁, X₂, X₃, X₄)`. -/
def plaqX (ai ajs ais aj : M4) : List M4 := [ai, ajs, -ais, -aj]

/-- Electric link remainder `ρ^E = h⁻¹(Ad_{e^{ha}} - I - h ad_a) a0s` (cubic in the connection). -/
def remE (h : ℝ) (a a0s : M4) : M4 :=
  h⁻¹ • (exp (h • a) * a0s * exp (-(h • a)) - a0s - h • bracket a a0s)

/-- Plaquette remainder `ρ^B = B - h⁻¹ Σ_r X_r - ½ Σ_{r<s} [X_r, X_s]`. -/
def remB (h : ℝ) (ai ajs ais aj : M4) : M4 :=
  plaquette h ai ajs ais aj - h⁻¹ • (ai + ajs - ais - aj) - commTerm (plaqX ai ajs ais aj)

theorem linkVel_mul_exp_neg (h : ℝ) (a adot : M4) :
    linkVel h a adot * exp (-(h • a)) = h • calJ (h • a) adot := by
  unfold linkVel calJ
  erw [fderiv_exp_eq]
  rw [mul_assoc]
  erw [exp_mul_exp_neg]
  rw [mul_one, map_smul]

/-- **Exact decomposition of the electric link curvature**:
`E = 𝒥_{ha}ȧ + h⁻¹(a0 - a0s) - [a, a0s] - ρ^E`. -/
theorem electric_decomp {h : ℝ} (hh : h ≠ 0) (a a0 a0s adot : M4) :
    electric h a a0 a0s adot =
      calJ (h • a) adot + h⁻¹ • (a0 - a0s) - bracket a a0s - remE h a a0s := by
  unfold electric remE
  rw [linkVel_mul_exp_neg]
  have h1 : h⁻¹ • (h • calJ (h • a) adot) = calJ (h • a) adot := by
    rw [smul_smul, inv_mul_cancel₀ hh, one_smul]
  have h2 : h⁻¹ • (h • bracket a a0s) = bracket a a0s := by
    rw [smul_smul, inv_mul_cancel₀ hh, one_smul]
  simp only [smul_sub, smul_add, h1, h2]
  abel

theorem plaquette_decomp (h : ℝ) (ai ajs ais aj : M4) :
    plaquette h ai ajs ais aj =
      h⁻¹ • (ai + ajs - ais - aj) + commTerm (plaqX ai ajs ais aj) + remB h ai ajs ais aj := by
  unfold remB; abel

/-! ### The periodic regulator -/

/-- Sites of the periodic cubic regulator `(ℤ/N)³`. -/
abbrev Site (N : ℕ) := Fin 3 → ZMod N

variable {N : ℕ} [NeZero N]

/-- The coordinate unit vector `e_i`. -/
def unitVec (i : Fin 3) : Site N := Pi.single i 1

/-- Forward difference `D_i^+ u(x) = h⁻¹(u(x + e_i) - u(x))`. -/
def Dp (h : ℝ) (i : Fin 3) (u : Site N → M4) (x : Site N) : M4 :=
  h⁻¹ • (u (x + unitVec i) - u x)

/-- Backward difference `D_i^- u(x) = h⁻¹(u(x) - u(x - e_i))`. -/
def Dm (h : ℝ) (i : Fin 3) (u : Site N → M4) (x : Site N) : M4 :=
  h⁻¹ • (u x - u (x - unitVec i))

/-- The grid pairing with the constant `1`: `⟨f, 1⟩_h = h³ Σ_x f(x)`. -/
def gridPair (h : ℝ) (f : Site N → ℝ) : ℝ := h ^ 3 * ∑ x, f x

/-- The electric field `E_i(x)` of `eq:supp-exact-link-curvatures`. -/
def elecField (h : ℝ) (A0 : Site N → M4) (A Adot : Fin 3 → Site N → M4) (i : Fin 3)
    (x : Site N) : M4 :=
  electric h (A i x) (A0 x) (A0 (x + unitVec i)) (Adot i x)

/-- The plaquette field `B_ij(x)` of `eq:supp-exact-link-curvatures`. -/
def plaqField (h : ℝ) (A : Fin 3 → Site N → M4) (i j : Fin 3) (x : Site N) : M4 :=
  plaquette h (A i x) (A j (x + unitVec i)) (A i (x + unitVec j)) (A j x)

/-- The full Palatini density `χ det(e)(r(e, F) - 2Λ)` (`eq:supp-exact-full-palatini`). -/
def fullDensity (χ Λ h : ℝ) (e A0 : Site N → M4) (A Adot : Fin 3 → Site N → M4) (x : Site N) :
    ℝ :=
  χ * detR (e x) (fun i => elecField h A0 A Adot i x) (fun i j => plaqField h A i j x) -
    2 * χ * Λ * (e x).det

/-- The kinetic compensator `𝒦_h = Σ_i b(Π_i, (𝒥_{hA_i} - I)Ȧ_i)` (`eq:supp-exact-compensators`). -/
def kinComp (χ h : ℝ) (e : Site N → M4) (A Adot : Fin 3 → Site N → M4) (x : Site N) : ℝ :=
  ∑ i, pairing (piArr χ (e x) i) (calJ (h • A i x) (Adot i x) - Adot i x)

/-- The plaquette list `(A_i, A_{j,+i}, -A_{i,+j}, -A_j)` at `x`. -/
def plaqXField (A : Fin 3 → Site N → M4) (i j : Fin 3) (x : Site N) : List M4 :=
  plaqX (A i x) (A j (x + unitVec i)) (A i (x + unitVec j)) (A j x)

/-- The link quadratic compensator
`q_h = -Σ_i b(Π_i, [A_i, A_{0,+i}]) + ½Σ_{i<j}Σ_{r<s} b(Σ_ij, [X_r, X_s])`
(`eq:supp-exact-compensators`). -/
def qh (χ : ℝ) (e A0 : Site N → M4) (A : Fin 3 → Site N → M4) (x : Site N) : ℝ :=
  -(∑ i, pairing (piArr χ (e x) i) (bracket (A i x) (A0 (x + unitVec i)))) +
    sumLt fun i j => pairing (sigmaArr χ (e x) i j) (commTerm (plaqXField A i j x))

/-- The continuum Cartan quadratic form
`q = Σ_i b(Π_i, [A₀, A_i]) + Σ_{i<j} b(Σ_ij, [A_i, A_j])` (`eq:supp-exact-compensators`); this is
`½ AᵀC(e)A` of `eq:supp-exact-connection-normal-form`. -/
def qc (χ : ℝ) (e A0 : Site N → M4) (A : Fin 3 → Site N → M4) (x : Site N) : ℝ :=
  (∑ i, pairing (piArr χ (e x) i) (bracket (A0 x) (A i x))) +
    sumLt fun i j => pairing (sigmaArr χ (e x) i j) (bracket (A i x) (A j x))

/-- The completed signed density `χ det(e)(r - 2Λ) + q - q_h - 𝒦_h`. -/
def completedDensity (χ Λ h : ℝ) (e A0 : Site N → M4) (A Adot : Fin 3 → Site N → M4)
    (x : Site N) : ℝ :=
  fullDensity χ Λ h e A0 A Adot x + qc χ e A0 A x - qh χ e A0 A x - kinComp χ h e A Adot x

/-- The boundary functional `Σ_i ⟨b(Π_i, A_i), 1⟩_h`. -/
def boundaryTerm (χ h : ℝ) (e : Site N → M4) (A : Fin 3 → Site N → M4) : ℝ :=
  gridPair h fun x => ∑ i, pairing (piArr χ (e x) i) (A i x)

/-- **The completed signed action** `eq:supp-exact-completed-action` on a time interval `[0, T]`
for paths `e(t)`, `A₀(t)`, `A(t)` (the connection velocity is the time derivative of `A`):
`𝒫^c_{h,D} = ∫₀ᵀ ⟨χ det(e)(r - 2Λ) + q - q_h - 𝒦_h, 1⟩_h dt - [Σ_i⟨b(Π_i, A_i), 1⟩_h]_0^T`. -/
def completedAction (χ Λ h T : ℝ) (e A0 : ℝ → Site N → M4) (A : ℝ → Fin 3 → Site N → M4) : ℝ :=
  (∫ t in (0 : ℝ)..T, gridPair h (completedDensity χ Λ h (e t) (A0 t) (A t) (deriv A t))) -
    (boundaryTerm χ h (e T) (A T) - boundaryTerm χ h (e 0) (A 0))

/-! ### The connection normal form -/

/-- The link remainder density `r_h(e, A) = -Σ_i b(Π_i, ρ^E_i) + Σ_{i<j} b(Σ_ij, ρ^B_ij)`. -/
def remDensity (χ h : ℝ) (e A0 : Site N → M4) (A : Fin 3 → Site N → M4) (x : Site N) : ℝ :=
  -(∑ i, pairing (piArr χ (e x) i) (remE h (A i x) (A0 (x + unitVec i)))) +
    sumLt fun i j => pairing (sigmaArr χ (e x) i j)
      (remB h (A i x) (A j (x + unitVec i)) (A i (x + unitVec j)) (A j x))

theorem sumLt_add (f g : Fin 3 → Fin 3 → ℝ) :
    sumLt (fun i j => f i j + g i j) = sumLt f + sumLt g := by
  simp only [sumLt_eq]; ring

theorem sumLt_sub (f g : Fin 3 → Fin 3 → ℝ) :
    sumLt (fun i j => f i j - g i j) = sumLt f - sumLt g := by
  simp only [sumLt_eq]; ring

/-- **Pointwise connection normal form** of the completed density: the nonlinear
connection-velocity terms cancel exactly against `𝒦_h`, the quadratic link terms against
`q_h`, and what remains is linear in `Ȧ`, `D^+A`, plus `q(A)` and the link remainder. -/
theorem completedDensity_eq {h : ℝ} (hh : h ≠ 0) (χ Λ : ℝ) (e A0 : Site N → M4)
    (A Adot : Fin 3 → Site N → M4) (x : Site N) :
    completedDensity χ Λ h e A0 A Adot x =
      -2 * χ * Λ * (e x).det + (∑ i, pairing (piArr χ (e x) i) (Adot i x)) -
        (∑ i, pairing (piArr χ (e x) i) (Dp h i A0 x)) +
        (sumLt fun i j => pairing (sigmaArr χ (e x) i j) (Dp h i (A j) x - Dp h j (A i) x)) +
        qc χ e A0 A x + remDensity χ h e A0 A x := by
  unfold completedDensity fullDensity
  rw [palatini_contraction]
  have hE : ∀ i, elecField h A0 A Adot i x =
      calJ (h • A i x) (Adot i x) - Dp h i A0 x - bracket (A i x) (A0 (x + unitVec i)) -
        remE h (A i x) (A0 (x + unitVec i)) := by
    intro i
    unfold elecField Dp
    rw [electric_decomp hh]
    rw [show A0 x - A0 (x + unitVec i) = -(A0 (x + unitVec i) - A0 x) by abel, smul_neg]
    abel
  have hB : ∀ i j, plaqField h A i j x =
      (Dp h i (A j) x - Dp h j (A i) x) + commTerm (plaqXField A i j x) +
        remB h (A i x) (A j (x + unitVec i)) (A i (x + unitVec j)) (A j x) := by
    intro i j
    unfold plaqField Dp plaqXField
    rw [plaquette_decomp]
    congr 2
    rw [← smul_sub]
    congr 1
    abel
  simp only [hE, hB, pairing_add_right, pairing_sub_right, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, sumLt_add, sumLt_sub]
  unfold qh qc remDensity kinComp
  simp only [pairing_sub_right, Finset.sum_sub_distrib]
  ring

/-- Exact summation by parts on the periodic regulator:
`Σ_x b(P(x), D_i^+u(x)) = -Σ_x b(D_i^-P(x), u(x))`. -/
theorem sum_pairing_Dp (h : ℝ) (i : Fin 3) (P u : Site N → M4) :
    ∑ x, pairing (P x) (Dp h i u x) = -∑ x, pairing (Dm h i P x) (u x) := by
  unfold Dp Dm
  simp only [pairing_smul_right, pairing_smul_left, pairing_sub_right, pairing_sub_left,
    ← Finset.mul_sum, Finset.sum_sub_distrib]
  have hshift : ∑ x : Site N, pairing (P x) (u (x + unitVec i)) =
      ∑ x : Site N, pairing (P (x - unitVec i)) (u x) := by
    exact Fintype.sum_equiv (Equiv.addRight (unitVec i)) _ _ (fun x => by simp)
  rw [hshift]
  ring

/-- The temporal load `f_{h,0} = Σ_i D_i^-Π_i` (`eq:supp-exact-connection-load`). -/
def load0 (χ h : ℝ) (e : Site N → M4) (x : Site N) : M4 :=
  ∑ i, Dm h i (fun y => piArr χ (e y) i) x

/-- The spatial part `-Σ_{j≠i} D_j^-Σ_ji` of the load `f_{h,i}` (`eq:supp-exact-connection-load`). -/
def loadSp (χ h : ℝ) (e : Site N → M4) (i : Fin 3) (x : Site N) : M4 :=
  -∑ j, Dm h j (fun y => sigmaArr χ (e y) j i) x

theorem Dm_neg (h : ℝ) (j : Fin 3) (f : Site N → M4) (x : Site N) :
    Dm h j (fun y => -f y) x = -Dm h j f x := by
  simp [Dm, smul_sub, neg_sub_neg]; abel

theorem Dm_zero (h : ℝ) (j : Fin 3) (x : Site N) : Dm h j (fun _ => (0 : M4)) x = 0 := by
  simp [Dm]

/-- The paper's form of the spatial load: the `j = i` term vanishes (`Σ_ii = 0`). -/
theorem loadSp_eq_sum_ne (χ h : ℝ) (e : Site N → M4) (i : Fin 3) (x : Site N) :
    loadSp χ h e i x = -∑ j ∈ Finset.univ.filter (· ≠ i), Dm h j (fun y => sigmaArr χ (e y) j i) x := by
  unfold loadSp
  congr 1
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hj
  · rfl
  · push Not at hj; subst hj; simp [sigmaArr_diag, Dm_zero]

/-- Summation by parts of the plaquette linear term:
`Σ_x Σ_{i<j} b(Σ_ij, D_i^+A_j - D_j^+A_i) = Σ_x Σ_i b(-Σ_{j} D_j^-Σ_ji, A_i)`. -/
theorem sumLt_sigma_Dp (χ h : ℝ) (e : Site N → M4) (A : Fin 3 → Site N → M4) :
    ∑ x, (sumLt fun i j => pairing (sigmaArr χ (e x) i j) (Dp h i (A j) x - Dp h j (A i) x)) =
      ∑ x, ∑ i, pairing (loadSp χ h e i x) (A i x) := by
  simp only [sumLt_eq, pairing_sub_right, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    sum_pairing_Dp h _ (fun y => sigmaArr χ (e y) _ _)]
  have hs10 : ∀ y, sigmaArr χ (e y) 1 0 = -sigmaArr χ (e y) 0 1 := fun y => sigmaArr_swap χ (e y) 0 1
  have hs20 : ∀ y, sigmaArr χ (e y) 2 0 = -sigmaArr χ (e y) 0 2 := fun y => sigmaArr_swap χ (e y) 0 2
  have hs21 : ∀ y, sigmaArr χ (e y) 2 1 = -sigmaArr χ (e y) 1 2 := fun y => sigmaArr_swap χ (e y) 1 2
  unfold loadSp
  simp only [pairing_neg_left, pairing_sum_left, Fin.sum_univ_three, Finset.sum_neg_distrib,
    Finset.sum_add_distrib, hs10, hs20, hs21, sigmaArr_diag, Dm_neg, Dm_zero, pairing_zero_left,
    Finset.sum_const_zero]
  simp only [pairing_sub_left, pairing_add_left, zero_sub, pairing_neg_left, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.sum_neg_distrib, pairing_zero_left, Finset.sum_const_zero,
    sub_zero]
  ring

end RenewalGeometry.ExactPhaseAction
