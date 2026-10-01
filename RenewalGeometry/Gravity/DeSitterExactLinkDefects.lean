/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.NormedAlgebraLogBCH
import RenewalGeometry.Gravity.RelationalDeSitterBranch

/-!
# Exact links and finite Cartan defects of the de Sitter / flat regulator
(`thm:supp-finite-defects`, `eq:supp-exact-link`, `eq:supp-curvature-defect`,
`eq:supp-torsion-defect`, `eq:supp-diagonal-exhaustion`, `eq:supp-defect-summability`;
emergent-spacetime manuscript)

The Cartan data `eq:supp-desitter-cartan` of the homogeneous de Sitter branch,
`ϑ⁰ = dt`, `ϑᵃ = e^{Ht} dxᵃ`, `ωᵃ₀ = ω⁰ₐ = H ϑᵃ`, `ωᵃ_b = 0`, are encoded on the internal
index set `Idx = Option (Fin 3)` (`none` = 0) with values in real `Idx × Idx` matrices (L∞
operator norm).  `H = 0` is the flat regulator.

* `boost`, `connection`, `coframe`, `curvature`: `ω(V) = H e^{Ht} K(u)` for `V = (τ, u)`,
  `ϑ(V) = (τ, e^{Ht} u)`, and the curvature two-form.  Faithfulness checks:
  `boost_lorentz` (`Kᵀη + ηK = 0`, metric compatibility), `curvature_eq_cartan`
  (`Ω = dω + ω ∧ ω`, Cartan's second structure equation), `curvature_eq_desitter`
  (`Ωᴬ_B = H² ϑᴬ ∧ ϑ_B`, `eq:supp-desitter-curvature`) and `torsion_free` (`dϑ + ω ∧ ϑ = 0`).
* `edgeLink`, `edgeLink_exact`: the exact link `U_e = 𝒫 exp(−∫_e ω)` of every straight edge
  (any length) is `exp(−φ K(u))`; spatial links are `exp(−H e^{Ht} K(u))`, time links are `1`.
* `loopHolonomy`, `areaCurvature`, `curvatureDefect`: the face holonomy `U_{∂p}`, the curvature
  evaluated on the face bivector `|p| Ω(x_p)`, and the normalized defect
  `𝔯_p = |p|⁻¹ (log U_{∂p} + |p| Ω(x_p))` (principal logarithm `LogBCH.logOnePlus`).
* `norm_curvatureDefect_spatial_le`: for every closed spatial polygon (any face of any spatial
  mesh) `‖𝔯_p‖ ≤ 6 s³/|p|`, `s = |H| e^{Ht} ∑ ‖K(uᵢ)‖` (exact cancellation of the
  second-order BCH term against `Ω`).
* `norm_curvatureDefect_mixed_le`: the same for the edge × time-step faces of the product
  complex: `‖𝔯_p‖ ≤ (6 s³ + |H|e^{Ht}|Hh|³ ‖K(u)‖)/|p|`.
* `developedEdge`, `torsionSum`, `torsionDefect`: the covariant developed-edge closure
  `𝔱_p = |p|⁻¹ ∑_e U_{x_p←s(e)} E_e` with developed edges `E_e = ∫₀¹ U_{s(e)←γ(r)} ϑ(γ') dr`;
  `norm_torsionDefect_spatial_le`, `norm_torsionDefect_mixed_le`: `O(h³)/|p|` bounds (the first
  order parts cancel exactly).  The literal formula with a raw `∫_e ϑ` transported from `s(e)`
  has an `O(1)` defect on de Sitter, so the developed reading is the one formalised.
* `curvatureDefect_slab_le`, `torsionDefect_slab_le`: on `|t| ≤ T`, `0 < h ≤ h_T`, for
  shape-regular faces, both defects are `≤ C_T h` with `C_T = 1300 κ⁴ ((|H|+1)e^{|H|(T+1)})⁴`;
  `finiteDefects_flat`: all defects vanish for the flat regulator; `diagonal_exhaustion`,
  `finiteDefects_diagonal`: `h_n = 2^{−n²}`, `T_n = n` gives `∑ C_{T_n} h_n < ∞`.

Not formalised here: the Palatini first-variation part of `eq:supp-finite-defect-bound`
(`δS_h`, `δS` are not encoded).
-/

namespace RenewalGeometry.DeSitterExactLink

open NormedSpace _root_.Matrix Set
open scoped _root_.Matrix Interval

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- Internal Lorentz index: `none` is the time index `0`, `some a` the spatial index `a`. -/
abbrev Idx := Option (Fin 3)

/-- Lie-algebra valued coefficients: real `4 × 4` matrices (L∞ operator norm). -/
abbrev Gen := Matrix Idx Idx ℝ

/-- Coordinate tangent vectors `V = (τ, u)` of `ℝ × ℝ³`. -/
abbrev TVec := ℝ × (Fin 3 → ℝ)

instance : CompleteSpace Gen := FiniteDimensional.complete ℝ _

/-- Minkowski metric `η = diag(−1, 1, 1, 1)`. -/
def eta : Gen := Matrix.diagonal fun i => Option.elim i (-1) fun _ => 1

/-- Boost generator `K(u) = ∑ₐ uᵃ (E_{a0} + E_{0a})`. -/
def boostFun (u : Fin 3 → ℝ) : Gen := Matrix.of fun A B =>
  match A, B with
  | none, some b => u b
  | some a, none => u a
  | _, _ => 0

/-- The boost generator as a linear map `ℝ³ → 𝔰𝔬(1,3)`. -/
def boost : (Fin 3 → ℝ) →ₗ[ℝ] Gen where
  toFun := boostFun
  map_add' u v := by
    ext A B; cases A <;> cases B <;> simp [boostFun]
  map_smul' c u := by
    ext A B; cases A <;> cases B <;> simp [boostFun]

@[simp] theorem boost_apply_none_some (u : Fin 3 → ℝ) (b : Fin 3) : boost u none (some b) = u b :=
  rfl
@[simp] theorem boost_apply_some_none (u : Fin 3 → ℝ) (a : Fin 3) : boost u (some a) none = u a :=
  rfl
@[simp] theorem boost_apply_none_none (u : Fin 3 → ℝ) : boost u none none = 0 := rfl
@[simp] theorem boost_apply_some_some (u : Fin 3 → ℝ) (a b : Fin 3) :
    boost u (some a) (some b) = 0 := rfl

/-- **Metric compatibility**: `K(u)ᵀ η + η K(u) = 0`, i.e. every boost generator lies in
`𝔰𝔬(1,3)` (`ω_{AB} = −ω_{BA}`). -/
theorem boost_lorentz (u : Fin 3 → ℝ) : (boost u)ᵀ * eta + eta * boost u = 0 := by
  ext A B
  cases A <;> cases B <;> simp [eta, Matrix.mul_apply, Matrix.diagonal]

/-- `‖K(u)‖ ≤ 3 ‖u‖` (L∞ operator norm, sup norm on `ℝ³`). -/
theorem norm_boost_le (u : Fin 3 → ℝ) : ‖boost u‖ ≤ 3 * ‖u‖ := by
  rw [Matrix.linfty_opNorm_def]
  have hu : ∀ a, ‖u a‖₊ ≤ ‖u‖₊ := fun a => nnnorm_le_pi_nnnorm u a
  have key : ((Finset.univ : Finset Idx).sup fun i => ∑ j : Idx, ‖boost u i j‖₊) ≤ 3 * ‖u‖₊ := by
    refine Finset.sup_le fun i _ => ?_
    cases i with
    | none =>
      simp only [Fintype.sum_option, boost_apply_none_none, boost_apply_none_some, nnnorm_zero,
        zero_add, Fin.sum_univ_three]
      have := add_le_add (add_le_add (hu 0) (hu 1)) (hu 2)
      calc ‖u 0‖₊ + ‖u 1‖₊ + ‖u 2‖₊ ≤ ‖u‖₊ + ‖u‖₊ + ‖u‖₊ := this
        _ = 3 * ‖u‖₊ := by ring
    | some a =>
      simp only [Fintype.sum_option, boost_apply_some_none, boost_apply_some_some, nnnorm_zero,
        Finset.sum_const_zero, add_zero]
      calc ‖u a‖₊ ≤ ‖u‖₊ := hu a
        _ ≤ 3 * ‖u‖₊ := le_mul_of_one_le_left bot_le (by norm_num)
  have := NNReal.coe_le_coe.2 key
  simpa using this

/-! ### Cartan data -/

/-- Connection one-form `ω(V) = H e^{Ht} K(u)` at time `t` (independent of `x`). -/
noncomputable def connection (H t : ℝ) (V : TVec) : Gen := (H * Real.exp (H * t)) • boost V.2

/-- Coframe `ϑ(V) = (τ, e^{Ht} u)`. -/
noncomputable def coframe (H t : ℝ) (V : TVec) : Idx → ℝ :=
  fun A => Option.elim A V.1 fun a => Real.exp (H * t) * V.2 a

/-- Curvature two-form of the de Sitter connection,
`Ω(V, W) = H² e^{Ht} (τ_V K(u_W) − τ_W K(u_V)) + H² e^{2Ht} [K(u_V), K(u_W)]`. -/
noncomputable def curvature (H t : ℝ) (V W : TVec) : Gen :=
  (H ^ 2 * Real.exp (H * t)) • (V.1 • boost W.2 - W.1 • boost V.2)
    + (H ^ 2 * Real.exp (2 * H * t)) • (boost V.2 * boost W.2 - boost W.2 * boost V.2)

theorem hasDerivAt_connection (H t : ℝ) (W : TVec) :
    HasDerivAt (fun s => connection H s W) ((H * (Real.exp (H * t) * H)) • boost W.2) t := by
  have h1 : HasDerivAt (fun s => Real.exp (H * s)) (Real.exp (H * t) * H) t := by
    simpa using ((hasDerivAt_id t).const_mul H).exp
  exact (h1.const_mul H).smul_const (boost W.2)

/-- **Cartan's second structure equation** `Ω = dω + ω ∧ ω` for constant coordinate vector
fields `V, W` (the coefficients depend on `t` only): if `dW, dV` are the `t`-derivatives of
`ω(W), ω(V)` then `Ω(V,W) = τ_V dW − τ_W dV + [ω(V), ω(W)]`. -/
theorem curvature_eq_cartan (H t : ℝ) (V W : TVec) {dV dW : Gen}
    (hW : HasDerivAt (fun s => connection H s W) dW t)
    (hV : HasDerivAt (fun s => connection H s V) dV t) :
    curvature H t V W = V.1 • dW - W.1 • dV
      + (connection H t V * connection H t W - connection H t W * connection H t V) := by
  rw [hW.unique (hasDerivAt_connection H t W), hV.unique (hasDerivAt_connection H t V)]
  have e2 : Real.exp (2 * H * t) = Real.exp (H * t) * Real.exp (H * t) := by
    rw [← Real.exp_add]; ring_nf
  simp only [curvature, connection, smul_mul_smul_comm, e2]
  module

/-- The curvature is `Ωᴬ_B = H² (ϑᴬ(V) ϑ_B(W) − ϑᴬ(W) ϑ_B(V))`, `ϑ_B = η_{BB} ϑᴮ`
(`eq:supp-desitter-curvature`). -/
theorem curvature_eq_desitter (H t : ℝ) (V W : TVec) (A B : Idx) :
    curvature H t V W A B = H ^ 2 * (coframe H t V A * (eta B B * coframe H t W B)
      - coframe H t W A * (eta B B * coframe H t V B)) := by
  have e2 : Real.exp (2 * H * t) = Real.exp (H * t) * Real.exp (H * t) := by
    rw [← Real.exp_add]; ring_nf
  cases A <;> cases B
  · simp [curvature, coframe, eta, Matrix.mul_apply, Fintype.sum_option, e2]
    rw [Finset.sum_congr rfl fun x _ => mul_comm (W.2 x) (V.2 x)]; ring
  all_goals simp [curvature, coframe, eta, Matrix.mul_apply, Fintype.sum_option, e2]
  all_goals ring

/-- **Torsion-freeness** `dϑ + ω ∧ ϑ = 0` (Cartan's first structure equation with vanishing
torsion), componentwise. -/
theorem torsion_free (H t : ℝ) (V W : TVec) (A : Idx) :
    V.1 * deriv (fun s => coframe H s W A) t - W.1 * deriv (fun s => coframe H s V A) t
      + ((connection H t V) *ᵥ (coframe H t W)) A
      - ((connection H t W) *ᵥ (coframe H t V)) A = 0 := by
  have h1 : HasDerivAt (fun s => Real.exp (H * s)) (Real.exp (H * t) * H) t := by
    simpa using ((hasDerivAt_id t).const_mul H).exp
  cases A with
  | none =>
    simp only [coframe, Option.elim, deriv_const', mul_zero, sub_zero]
    simp [connection, Matrix.mulVec, dotProduct, Fintype.sum_option, coframe,
      Fin.sum_univ_three]
    ring
  | some a =>
    simp only [coframe, Option.elim]
    rw [(h1.mul_const (W.2 a)).deriv, (h1.mul_const (V.2 a)).deriv]
    simp [connection, Matrix.mulVec, dotProduct, Fintype.sum_option, coframe]
    ring

/-! ### Exact links -/

/-- Phase `φ(r) = ∫₀ʳ H e^{H(t+ρτ)} dρ` of the link along `γ(ρ) = (t + ρτ, x + ρu)`. -/
noncomputable def phase (H t τ r : ℝ) : ℝ := ∫ ρ in (0 : ℝ)..r, H * Real.exp (H * (t + ρ * τ))

theorem continuous_phaseIntegrand (H t τ : ℝ) :
    Continuous fun ρ : ℝ => H * Real.exp (H * (t + ρ * τ)) := by fun_prop

theorem hasDerivAt_phase (H t τ r : ℝ) :
    HasDerivAt (phase H t τ) (H * Real.exp (H * (t + r * τ))) r :=
  ((continuous_phaseIntegrand H t τ).integral_hasStrictDerivAt 0 r).hasDerivAt

@[simp] theorem phase_zero_tau (H t r : ℝ) : phase H t 0 r = r * (H * Real.exp (H * t)) := by
  simp [phase]; ring

/-- The exact link of the straight edge from `(t, x)` with displacement `V = (τ, u)`:
`U_e = exp(−φ(1) K(u))`. -/
noncomputable def edgeLink (H t : ℝ) (V : TVec) : Gen := exp (phase H t V.1 1 • (-boost V.2))

/-- The explicit transport `r ↦ exp(−φ(r) K(u))` solves `U' = −ω(γ') U` along the edge. -/
theorem isTransport_edge (H t : ℝ) (V : TVec) :
    PathOrderedExp.IsTransport (fun r => connection H (t + r * V.1) V) 0 1
      (fun r => exp (phase H t V.1 r • (-boost V.2))) := by
  intro r _
  have h := HasDerivAt.scomp r (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-boost V.2)
    (phase H t V.1 r)) (hasDerivAt_phase H t V.1 r)
  refine (h.congr_deriv ?_).hasDerivWithinAt
  simp only [connection, smul_mul_assoc, neg_mul, smul_neg]
  rfl

/-- **Exact links on straight edges of any length** (`eq:supp-exact-link`): every transport of
the de Sitter connection along the edge with initial value `1` ends at `edgeLink H t V`. -/
theorem edgeLink_exact (H t : ℝ) (V : TVec) {U : ℝ → Gen}
    (hU : PathOrderedExp.IsTransport (fun r => connection H (t + r * V.1) V) 0 1 U)
    (h1 : U 0 = 1) : U 1 = edgeLink H t V := by
  have hK : ∀ r ∈ Icc (0 : ℝ) 1, ‖connection H (t + r * V.1) V‖
      ≤ |H| * Real.exp (|H| * (|t| + |V.1|)) * ‖boost V.2‖ := by
    intro r hr
    have hexp : Real.exp (H * (t + r * V.1)) ≤ Real.exp (|H| * (|t| + |V.1|)) := by
      refine Real.exp_le_exp.2 ?_
      calc H * (t + r * V.1) ≤ |H * (t + r * V.1)| := le_abs_self _
        _ = |H| * |t + r * V.1| := abs_mul _ _
        _ ≤ |H| * (|t| + |V.1|) := by
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            calc |t + r * V.1| ≤ |t| + |r * V.1| := abs_add_le _ _
              _ ≤ |t| + |V.1| := by
                  have : |r * V.1| ≤ |V.1| := by
                    rw [abs_mul, abs_of_nonneg hr.1]
                    exact mul_le_of_le_one_left (abs_nonneg _) hr.2
                  linarith
    rw [connection, norm_smul, Real.norm_eq_abs, abs_mul, Real.abs_exp]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hexp (abs_nonneg H)) le_rfl (norm_nonneg _)
      (by positivity)
  have := PathOrderedExp.transport_unique hK hU (isTransport_edge H t V)
    (by simp [h1, phase]) ⟨zero_le_one, le_rfl⟩
  exact this

/-- Spatial links: `U = exp(−H e^{Ht} K(u))`. -/
theorem edgeLink_spatial (H t : ℝ) (u : Fin 3 → ℝ) :
    edgeLink H t (0, u) = exp ((H * Real.exp (H * t)) • (-boost u)) := by
  simp [edgeLink]

/-- Time links are trivial: `U = 1`. -/
theorem edgeLink_time (H t τ : ℝ) : edgeLink H t (τ, 0) = 1 := by
  simp [edgeLink]

/-- In the flat regulator (`H = 0`) every exact link is the identity. -/
theorem edgeLink_flat (t : ℝ) (V : TVec) : edgeLink 0 t V = 1 := by
  simp [edgeLink, phase]

/-- Exact links are metric-unitary: `Uᵀ η U = η` (they are exponentials of `𝔰𝔬(1,3)`
elements). -/
theorem edgeLink_metric_unitary (H t : ℝ) (V : TVec) :
    (edgeLink H t V)ᵀ * eta * edgeLink H t V = eta := by
  set X : Gen := phase H t V.1 1 • (-boost V.2)
  have hX : Xᵀ * eta + eta * X = 0 := by
    have := boost_lorentz V.2
    simp only [X, Matrix.transpose_smul, Matrix.transpose_neg, smul_mul_assoc, neg_mul,
      mul_smul_comm, mul_neg, ← smul_add, ← neg_add]
    rw [this]; simp
  have hη2 : eta * eta = 1 := by
    rw [eta, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; cases i <;> simp
  have hT : Xᵀ = eta * (-X) * eta := by
    have h1 : Xᵀ * eta = -(eta * X) := eq_neg_of_add_eq_zero_left hX
    calc Xᵀ = Xᵀ * eta * eta := by rw [mul_assoc, hη2, mul_one]
      _ = eta * (-X) * eta := by rw [h1, mul_neg]
  have hinv : eta⁻¹ = eta := Matrix.inv_eq_left_inv hη2
  have hunit : IsUnit eta := IsUnit.of_mul_eq_one _ hη2
  change (exp X)ᵀ * eta * exp X = eta
  rw [← Matrix.exp_transpose, hT]
  have := Matrix.exp_conj eta (-X) hunit
  rw [hinv] at this
  rw [this]
  have hc : exp (-X) * exp X = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl X)), neg_add_cancel]
    exact exp_zero
  calc eta * exp (-X) * eta * eta * exp X = eta * (exp (-X) * exp X) := by
        rw [mul_assoc (eta * exp (-X)) eta eta, hη2, mul_one, mul_assoc]
    _ = eta := by rw [hc, mul_one]


/-! ### Face holonomies and the normalized curvature defect -/

/-- Holonomy `U_{∂p} = U_{e_m} ⋯ U_{e_1}` of the closed polygonal loop starting at time `t`
with consecutive edge displacements `Vs` (exact links composed along the boundary). -/
noncomputable def loopHolonomy (H : ℝ) : ℝ → List TVec → Gen
  | _, [] => 1
  | t, V :: Vs => loopHolonomy H (t + V.1) Vs * edgeLink H t V

/-- `|p| Ω(x_p)`: the curvature at time `tm` evaluated on the area bivector
`½ ∑_{i<j} Vᵢ ∧ Vⱼ` of the loop (by bilinearity). -/
noncomputable def areaCurvature (H tm : ℝ) : List TVec → Gen
  | [] => 0
  | V :: Vs => (1 / 2 : ℝ) • curvature H tm V Vs.sum + areaCurvature H tm Vs

/-- **Normalized curvature defect** `𝔯_p = |p|⁻¹ (log U_{∂p} + |p| Ω(x_p))`
(`eq:supp-curvature-defect`), with the principal logarithm; `t` is the time of the base vertex
and `tm` the time of the face midpoint `x_p`. -/
noncomputable def curvatureDefect (H t tm : ℝ) (Vs : List TVec) (area : ℝ) : Gen :=
  area⁻¹ • (LogBCH.logOnePlus (loopHolonomy H t Vs - 1) + areaCurvature H tm Vs)

/-- The exponent `−H e^{Ht} K(u)` of a spatial link, as a linear map of `u`. -/
noncomputable def spatialGen (H t : ℝ) : (Fin 3 → ℝ) →ₗ[ℝ] Gen :=
  (H * Real.exp (H * t)) • (-boost)

theorem spatialGen_apply (H t : ℝ) (u : Fin 3 → ℝ) :
    spatialGen H t u = (H * Real.exp (H * t)) • (-boost u) := rfl

/-- Embedding of spatial displacements `u ↦ (0, u)`. -/
noncomputable abbrev spatialVec : (Fin 3 → ℝ) →ₗ[ℝ] TVec := LinearMap.inr ℝ ℝ (Fin 3 → ℝ)

theorem loopHolonomy_spatial (H t : ℝ) (us : List (Fin 3 → ℝ)) :
    loopHolonomy H t (us.map spatialVec) = LogBCH.expProd ((us.map (spatialGen H t)).reverse) := by
  induction us with
  | nil => simp [loopHolonomy]
  | cons u us ih =>
    simp only [List.map_cons, loopHolonomy, LinearMap.inr_apply, add_zero, ih, List.reverse_cons,
      LogBCH.expProd_append, LogBCH.expProd_singleton]
    rw [edgeLink_spatial]; rfl

theorem curvature_spatial (H t : ℝ) (u w : Fin 3 → ℝ) :
    curvature H t (0, u) (0, w)
      = (H ^ 2 * Real.exp (2 * H * t)) • (boost u * boost w - boost w * boost u) := by
  simp [curvature]

theorem commTerm_spatial (H t : ℝ) (us : List (Fin 3 → ℝ)) :
    LogBCH.commTerm (us.map (spatialGen H t)) = areaCurvature H t (us.map spatialVec) := by
  induction us with
  | nil => simp [LogBCH.commTerm, areaCurvature]
  | cons u us ih =>
    simp only [List.map_cons, LogBCH.commTerm, areaCurvature, ih, ← map_list_sum]
    congr 1
    rw [LinearMap.inr_apply, LinearMap.inr_apply, curvature_spatial, spatialGen_apply,
      spatialGen_apply]
    have e2 : Real.exp (2 * H * t) = Real.exp (H * t) * Real.exp (H * t) := by
      rw [← Real.exp_add]; ring_nf
    rw [e2]
    simp only [smul_mul_smul_comm, neg_mul_neg]
    module

theorem normSum_spatial (H t : ℝ) (us : List (Fin 3 → ℝ)) :
    LogBCH.normSum (us.map (spatialGen H t))
      = |H| * Real.exp (H * t) * (us.map fun u => ‖boost u‖).sum := by
  induction us with
  | nil => simp
  | cons u us ih =>
    rw [List.map_cons, LogBCH.normSum_cons, ih, spatialGen_apply, norm_smul, norm_neg,
      Real.norm_eq_abs, abs_mul, Real.abs_exp]
    simp only [List.map_cons, List.sum_cons]; ring

/-- **Curvature defect of a spatial face** (any closed polygon of the spatial mesh at time `t`,
edge vectors `uᵢ` with `∑ uᵢ = 0`): with `s = |H| e^{Ht} ∑ ‖K(uᵢ)‖ ≤ 1/4`,
`‖𝔯_p‖ ≤ 6 s³ / |p|`.  The second-order BCH term `½∑[Xᵢ,Xⱼ]` cancels `|p| Ω` exactly. -/
theorem norm_curvatureDefect_spatial_le (H t area : ℝ) (harea : 0 < area)
    (us : List (Fin 3 → ℝ)) (hclosed : us.sum = 0)
    (hs : |H| * Real.exp (H * t) * (us.map fun u => ‖boost u‖).sum ≤ 1 / 4) :
    ‖curvatureDefect H t t (us.map spatialVec) area‖
      ≤ 6 * (|H| * Real.exp (H * t) * (us.map fun u => ‖boost u‖).sum) ^ 3 / area := by
  set L := us.map (spatialGen H t)
  have hsum : L.reverse.sum = 0 := by
    rw [List.sum_reverse]; simp only [L]; rw [← map_list_sum, hclosed, map_zero]
  have hns : LogBCH.normSum L.reverse
      = |H| * Real.exp (H * t) * (us.map fun u => ‖boost u‖).sum := by
    rw [LogBCH.normSum_reverse, normSum_spatial]
  have hb := LogBCH.norm_log_expProd_sub_comm_le L.reverse (hns ▸ hs) hsum
  rw [hns, LogBCH.commTerm_reverse, sub_neg_eq_add, commTerm_spatial] at hb
  rw [curvatureDefect, loopHolonomy_spatial, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_pos harea, inv_mul_le_iff₀ harea]
  calc _ ≤ 6 * (|H| * Real.exp (H * t) * (us.map fun u => ‖boost u‖).sum) ^ 3 := hb
    _ = area * (6 * (|H| * Real.exp (H * t) * (us.map fun u => ‖boost u‖).sum) ^ 3 / area) := by
        field_simp

/-- Edge × time-step face of the product complex: `(t,x) → (t,x+u) → (t+h,x+u) → (t+h,x) →
(t,x)`. -/
def mixedLoop (h : ℝ) (u : Fin 3 → ℝ) : List TVec := [(0, u), (h, 0), (0, -u), (-h, 0)]

theorem loopHolonomy_mixed (H t h : ℝ) (u : Fin 3 → ℝ) :
    loopHolonomy H t (mixedLoop h u)
      = LogBCH.expProd [(H * Real.exp (H * (t + h))) • boost u,
          (H * Real.exp (H * t)) • (-boost u)] := by
  simp only [mixedLoop, loopHolonomy, edgeLink_time, add_zero, one_mul, mul_one,
    LogBCH.expProd_cons, LogBCH.expProd_nil, edgeLink_spatial, map_neg, neg_neg]
  rfl

theorem areaCurvature_mixed (H tm h : ℝ) (u : Fin 3 → ℝ) :
    areaCurvature H tm (mixedLoop h u) = -(h * H ^ 2 * Real.exp (H * tm)) • boost u := by
  simp [mixedLoop, areaCurvature, curvature, map_neg]
  module

/-- `|eˣ − 1 − x e^{x/2}| ≤ |x|³` for `|x| ≤ 1` (midpoint consistency of the time-face
holonomy). -/
theorem abs_exp_sub_one_sub_mul_exp_half_le {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp x - 1 - x * Real.exp (x / 2)| ≤ |x| ^ 3 := by
  have h3 := Real.exp_bound hx (n := 3) (by norm_num)
  have hx2 : |x / 2| ≤ 1 := by rw [abs_div]; norm_num; linarith [abs_nonneg x]
  have h2 := Real.exp_bound hx2 (n := 2) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h3 h2
  norm_num at h3 h2
  have e : Real.exp x - 1 - x * Real.exp (x / 2)
      = (Real.exp x - (1 + x + x ^ 2 / 2)) - x * (Real.exp (x / 2) - (1 + x / 2)) := by ring
  rw [e]
  have ha : |x * (Real.exp (x / 2) - (1 + x / 2))| ≤ |x| * (|x| ^ 2 * (3 / 16)) := by
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left (h2.trans (le_of_eq ?_)) (abs_nonneg _)
    rw [sq_abs]; ring
  have hb : |Real.exp x - (1 + x + x ^ 2 / 2)| ≤ |x| ^ 3 * (2 / 9) := by
    convert h3 using 2 <;> ring_nf
  calc _ ≤ |Real.exp x - (1 + x + x ^ 2 / 2)| + |x * (Real.exp (x / 2) - (1 + x / 2))| :=
        abs_sub _ _
    _ ≤ |x| ^ 3 * (2 / 9) + |x| * (|x| ^ 2 * (3 / 16)) := add_le_add hb ha
    _ ≤ |x| ^ 3 := by nlinarith [pow_nonneg (abs_nonneg x) 3]

/-- **Curvature defect of an edge × time-step face**: with
`s = (|H| e^{H(t+h)} + |H| e^{Ht}) ‖K(u)‖ ≤ 1/4` and `|Hh| ≤ 1`,
`‖𝔯_p‖ ≤ (6 s³ + |H| e^{Ht} |Hh|³ ‖K(u)‖)/|p|`, the curvature being evaluated at the face
midpoint `t + h/2`. -/
theorem norm_curvatureDefect_mixed_le (H t h area : ℝ) (harea : 0 < area) (u : Fin 3 → ℝ)
    (hs : (|H| * Real.exp (H * (t + h)) + |H| * Real.exp (H * t)) * ‖boost u‖ ≤ 1 / 4)
    (hHh : |H * h| ≤ 1) :
    ‖curvatureDefect H t (t + h / 2) (mixedLoop h u) area‖
      ≤ (6 * ((|H| * Real.exp (H * (t + h)) + |H| * Real.exp (H * t)) * ‖boost u‖) ^ 3
          + |H| * Real.exp (H * t) * |H * h| ^ 3 * ‖boost u‖) / area := by
  set a : Gen := (H * Real.exp (H * (t + h))) • boost u
  set b : Gen := (H * Real.exp (H * t)) • (-boost u)
  set L : List Gen := [a, b]
  have hns : LogBCH.normSum L
      = (|H| * Real.exp (H * (t + h)) + |H| * Real.exp (H * t)) * ‖boost u‖ := by
    simp only [L, a, b, LogBCH.normSum_cons, LogBCH.normSum_nil, norm_smul, norm_neg,
      Real.norm_eq_abs, abs_mul, Real.abs_exp]
    ring
  have hb := LogBCH.norm_log_expProd_sub_bch_le L (hns ▸ hs)
  rw [hns] at hb
  have hcomm : LogBCH.commTerm L = 0 := by
    simp only [L, a, b, LogBCH.commTerm, List.sum_cons, List.sum_nil, add_zero, mul_zero,
      zero_mul, sub_zero, smul_zero]
    simp only [smul_mul_smul_comm, mul_neg, neg_mul, smul_neg]
    rw [mul_comm (H * Real.exp (H * (t + h)))]; simp
  have hS : L.sum + areaCurvature H (t + h / 2) (mixedLoop h u)
      = (H * Real.exp (H * t) * (Real.exp (H * h) - 1 - H * h * Real.exp (H * h / 2)))
          • boost u := by
    rw [areaCurvature_mixed]
    simp only [L, a, b, List.sum_cons, List.sum_nil, add_zero, smul_neg]
    have e1 : Real.exp (H * (t + h)) = Real.exp (H * t) * Real.exp (H * h) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (H * (t + h / 2)) = Real.exp (H * t) * Real.exp (H * h / 2) := by
      rw [← Real.exp_add]; ring_nf
    rw [e1, e2]
    module
  have hdec : LogBCH.logOnePlus (loopHolonomy H t (mixedLoop h u) - 1)
        + areaCurvature H (t + h / 2) (mixedLoop h u)
      = (LogBCH.logOnePlus (LogBCH.expProd L - 1) - (L.sum + LogBCH.commTerm L))
        + (L.sum + areaCurvature H (t + h / 2) (mixedLoop h u)) := by
    rw [loopHolonomy_mixed, hcomm]; abel
  have hsc : ‖(H * Real.exp (H * t) * (Real.exp (H * h) - 1 - H * h * Real.exp (H * h / 2)))
      • boost u‖ ≤ |H| * Real.exp (H * t) * |H * h| ^ 3 * ‖boost u‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, Real.abs_exp]
    have := abs_exp_sub_one_sub_mul_exp_half_le hHh
    gcongr
  rw [curvatureDefect, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos harea,
    inv_mul_le_iff₀ harea, hdec, hS]
  calc _ ≤ 6 * ((|H| * Real.exp (H * (t + h)) + |H| * Real.exp (H * t)) * ‖boost u‖) ^ 3
          + |H| * Real.exp (H * t) * |H * h| ^ 3 * ‖boost u‖ :=
        (norm_add_le _ _).trans (add_le_add hb hsc)
    _ = _ := by field_simp

/-- **Flat regulator**: for `H = 0` every curvature defect vanishes. -/
theorem curvatureDefect_flat (t tm : ℝ) (Vs : List TVec) (area : ℝ) :
    curvatureDefect 0 t tm Vs area = 0 := by
  have hl : ∀ Ws : List TVec, ∀ t, loopHolonomy 0 t Ws = 1 := by
    intro Ws; induction Ws with
    | nil => intro t; rfl
    | cons V Ws ih => intro t; simp [loopHolonomy, ih, edgeLink_flat]
  have ha : ∀ Ws : List TVec, areaCurvature 0 tm Ws = 0 := by
    intro Ws; induction Ws with
    | nil => rfl
    | cons V Ws ih => simp [areaCurvature, ih, curvature]
  simp [curvatureDefect, hl, ha]

/-! ### Uniform slab bounds and the diagonal exhaustion -/

/-- `∑ ‖K(uᵢ)‖ ≤ 3 ∑ ‖uᵢ‖`. -/
theorem sum_norm_boost_le (us : List (Fin 3 → ℝ)) :
    (us.map fun u => ‖boost u‖).sum ≤ 3 * (us.map fun u => ‖u‖).sum := by
  induction us with
  | nil => simp
  | cons u us ih =>
    simp only [List.map_cons, List.sum_cons]
    have := norm_boost_le u
    linarith

theorem sum_norm_boost_nonneg (us : List (Fin 3 → ℝ)) :
    0 ≤ (us.map fun u => ‖boost u‖).sum :=
  List.sum_nonneg fun x hx => by
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 hx
    exact norm_nonneg _

/-- Slab growth factor `B_T = (|H| + 1) e^{|H|(T+1)}`. -/
noncomputable def slabScale (H T : ℝ) : ℝ := (|H| + 1) * Real.exp (|H| * (T + 1))

/-- **Slab constant** `C_T = 1300 κ⁴ B_T⁴ = 1300 κ⁴ (|H|+1)⁴ e^{4|H|(T+1)}` (at most exponential
growth in `T`). -/
noncomputable def slabConst (H κ T : ℝ) : ℝ := 1300 * κ ^ 4 * slabScale H T ^ 4

/-- Mesh threshold `h_T = 1/(24 κ B_T)` below which the principal logarithm is used. -/
noncomputable def slabMesh (H κ T : ℝ) : ℝ := 1 / (24 * κ * slabScale H T)

theorem one_le_slabScale (H T : ℝ) (hT : 0 ≤ T) : 1 ≤ slabScale H T := by
  unfold slabScale
  have h1 : 1 ≤ Real.exp (|H| * (T + 1)) := Real.one_le_exp (by positivity)
  nlinarith [abs_nonneg H]

theorem abs_mul_exp_le_slabScale (H T t h : ℝ) (ht : |t| ≤ T) (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    |H| * Real.exp (H * (t + h)) ≤ slabScale H T := by
  unfold slabScale
  have he : Real.exp (H * (t + h)) ≤ Real.exp (|H| * (T + 1)) := by
    refine Real.exp_le_exp.2 ?_
    calc H * (t + h) ≤ |H * (t + h)| := le_abs_self _
      _ = |H| * |t + h| := abs_mul _ _
      _ ≤ |H| * (T + 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          calc |t + h| ≤ |t| + |h| := abs_add_le _ _
            _ ≤ T + 1 := by rw [abs_of_nonneg h0]; linarith
  have := Real.exp_pos (H * (t + h))
  nlinarith [abs_nonneg H, Real.exp_pos (|H| * (T + 1))]

/-- **Uniform curvature-defect bound on a compact slab** (curvature part of
`eq:supp-finite-defect-bound`): for `|t| ≤ T`, mesh `0 < h ≤ h_T`, and shape-regular faces
(`∑ ‖uᵢ‖ ≤ κ h`, area `|p| ≥ h²/κ`), every spatial face and every edge × time-step face of the
product complex has `‖𝔯_p‖ ≤ C_T h`. -/
theorem curvatureDefect_slab_le (H κ T : ℝ) (hκ : 1 ≤ κ) (hT : 0 ≤ T) {h : ℝ} (hh0 : 0 < h)
    (hh : h ≤ slabMesh H κ T) {t : ℝ} (ht : |t| ≤ T) :
    (∀ (us : List (Fin 3 → ℝ)) (area : ℝ), us.sum = 0 → (us.map fun u => ‖u‖).sum ≤ κ * h →
        h ^ 2 / κ ≤ area →
        ‖curvatureDefect H t t (us.map spatialVec) area‖ ≤ slabConst H κ T * h) ∧
    (∀ (u : Fin 3 → ℝ) (area : ℝ), ‖u‖ ≤ κ * h → h ^ 2 / κ ≤ area →
        ‖curvatureDefect H t (t + h / 2) (mixedLoop h u) area‖ ≤ slabConst H κ T * h) := by
  set B := slabScale H T with hBdef
  have hB1 : 1 ≤ B := one_le_slabScale H T hT
  have hκ0 : 0 < κ := by linarith
  have hκBh : 24 * (κ * B * h) ≤ 1 := by
    have h24 : 0 < 24 * κ * B := by positivity
    have := hh
    rw [slabMesh, le_div_iff₀ h24] at this
    linarith
  have hh1 : h ≤ 1 := by nlinarith [mul_le_mul hκ hB1 zero_le_one (by linarith)]
  have hc : |H| * Real.exp (H * t) ≤ B := by
    simpa using abs_mul_exp_le_slabScale H T t 0 ht le_rfl zero_le_one
  have hc' : |H| * Real.exp (H * (t + h)) ≤ B :=
    abs_mul_exp_le_slabScale H T t h ht hh0.le hh1
  have hB3 : B ^ 3 ≤ B ^ 4 := pow_le_pow_right₀ hB1 (by norm_num)
  have harea_pos : 0 < h ^ 2 / κ := by positivity
  constructor
  · intro us area hclosed hus harea
    have hareapos : 0 < area := lt_of_lt_of_le harea_pos harea
    set S := (us.map fun u => ‖boost u‖).sum
    have hS0 : 0 ≤ S := sum_norm_boost_nonneg us
    have hS : S ≤ 3 * (κ * h) := (sum_norm_boost_le us).trans (by linarith)
    have hs : |H| * Real.exp (H * t) * S ≤ 3 * (κ * B * h) := by
      calc |H| * Real.exp (H * t) * S ≤ B * (3 * (κ * h)) :=
            mul_le_mul hc hS hS0 (by linarith)
        _ = 3 * (κ * B * h) := by ring
    have hs0 : 0 ≤ |H| * Real.exp (H * t) * S := by positivity
    have hbound := norm_curvatureDefect_spatial_le H t area hareapos us hclosed
      (by linarith)
    refine hbound.trans ?_
    calc 6 * (|H| * Real.exp (H * t) * S) ^ 3 / area
        ≤ 6 * (3 * (κ * B * h)) ^ 3 / (h ^ 2 / κ) := by gcongr
      _ = 162 * κ ^ 4 * B ^ 3 * h := by field_simp; ring
      _ ≤ 1300 * κ ^ 4 * B ^ 4 * h := by gcongr; norm_num
      _ = slabConst H κ T * h := by rw [slabConst]
  · intro u area hu harea
    have hareapos : 0 < area := lt_of_lt_of_le harea_pos harea
    have hK : ‖boost u‖ ≤ 3 * (κ * h) := (norm_boost_le u).trans (by linarith)
    have hK0 : 0 ≤ ‖boost u‖ := norm_nonneg _
    set s := (|H| * Real.exp (H * (t + h)) + |H| * Real.exp (H * t)) * ‖boost u‖
    have hs : s ≤ 6 * (κ * B * h) := by
      calc s ≤ (B + B) * (3 * (κ * h)) := mul_le_mul (add_le_add hc' hc) hK hK0 (by linarith)
        _ = 6 * (κ * B * h) := by ring
    have hs0 : 0 ≤ s := by positivity
    have hHh : |H * h| ≤ B * h := by
      rw [abs_mul, abs_of_pos hh0]
      have : |H| ≤ B := by
        have := Real.one_le_exp (by positivity : 0 ≤ |H| * (T + 1))
        simp only [hBdef, slabScale]; nlinarith [abs_nonneg H]
      exact mul_le_mul_of_nonneg_right this hh0.le
    have hBh : B * h ≤ 1 := by nlinarith
    have hbound := norm_curvatureDefect_mixed_le H t h area hareapos u (by linarith)
      ((hHh.trans hBh))
    refine hbound.trans ?_
    have hHh3 : |H * h| ^ 3 ≤ (B * h) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hHh 3
    calc (6 * s ^ 3 + |H| * Real.exp (H * t) * |H * h| ^ 3 * ‖boost u‖) / area
        ≤ (6 * (6 * (κ * B * h)) ^ 3 + B * (B * h) ^ 3 * (3 * (κ * h))) / (h ^ 2 / κ) := by
          gcongr
      _ = 1296 * κ ^ 4 * B ^ 3 * h + 3 * κ ^ 2 * B ^ 4 * h ^ 2 := by field_simp; ring
      _ ≤ 1296 * κ ^ 4 * B ^ 4 * h + 4 * κ ^ 4 * B ^ 4 * h := by
          have hκ2 : κ ^ 2 ≤ κ ^ 4 := pow_le_pow_right₀ hκ (by norm_num)
          have e1 : 1296 * κ ^ 4 * B ^ 3 * h ≤ 1296 * κ ^ 4 * B ^ 4 * h := by gcongr
          have e2 : 3 * κ ^ 2 * B ^ 4 * h ^ 2 ≤ 4 * κ ^ 4 * B ^ 4 * h := by
            have hh2 : h ^ 2 ≤ h := by nlinarith
            have h3 : (3 : ℝ) * κ ^ 2 ≤ 4 * κ ^ 4 := by nlinarith
            exact mul_le_mul (mul_le_mul_of_nonneg_right h3 (by positivity)) hh2
              (by positivity) (by positivity)
          linarith
      _ = slabConst H κ T * h := by rw [slabConst]; ring

/-- `∑ₙ e^{a n} 2^{−n²} < ∞` for every real `a`. -/
theorem summable_exp_mul_diagonalMesh (a : ℝ) :
    Summable fun n : ℕ => Real.exp (a * n) * RelationalDeSitterBranch.diagonalMesh n := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set M := (|a| + 1) ^ 2 / (4 * Real.log 2)
  refine Summable.of_nonneg_of_le (fun n => by
      have := RelationalDeSitterBranch.diagonalMesh_pos n; positivity)
    (fun n => ?_) (Real.summable_exp_neg_nat.mul_left (Real.exp M))
  have hd : RelationalDeSitterBranch.diagonalMesh n = Real.exp (-((n : ℝ) ^ 2 * Real.log 2)) := by
    rw [RelationalDeSitterBranch.diagonalMesh, Real.exp_neg, ← Real.log_rpow (by norm_num),
      Real.exp_log (by positivity)]
    rw [one_div, inv_pow, ← Real.rpow_natCast]
    norm_num
  rw [hd, ← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have hsq : 0 ≤ (2 * Real.log 2 * n - (|a| + 1)) ^ 2 := sq_nonneg _
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hM : M * (4 * Real.log 2) = (|a| + 1) ^ 2 := by
    simp only [M]; field_simp
  have ha : a * n ≤ |a| * n := mul_le_mul_of_nonneg_right (le_abs_self a) hn
  nlinarith

/-- **Diagonal exhaustion** (`eq:supp-diagonal-exhaustion`, `eq:supp-defect-summability`):
with `h_n = 2^{−n²}` and `T_n = n`, `∑ₙ C_{T_n} h_n < ∞`, and `h_n ≤ h_{T_n}` for all large
`n`, so that the slab bound `curvatureDefect_slab_le` applies along the exhaustion. -/
theorem diagonal_exhaustion (H κ : ℝ) (hκ : 1 ≤ κ) :
    Summable (fun n : ℕ => slabConst H κ n * RelationalDeSitterBranch.diagonalMesh n) ∧
    ∃ N : ℕ, ∀ n ≥ N, RelationalDeSitterBranch.diagonalMesh n ≤ slabMesh H κ n := by
  have hsum : Summable (fun n : ℕ => slabConst H κ n * RelationalDeSitterBranch.diagonalMesh n) := by
    have := (summable_exp_mul_diagonalMesh (4 * |H|)).mul_left
      (1300 * κ ^ 4 * (|H| + 1) ^ 4 * Real.exp (4 * |H|))
    refine this.congr fun n => ?_
    have e : Real.exp (|H| * ((n : ℝ) + 1)) ^ 4 = Real.exp (4 * |H|) * Real.exp (4 * |H| * n) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
    simp only [slabConst, slabScale, mul_pow, e]
    ring
  refine ⟨hsum, ?_⟩
  have ht := hsum.tendsto_atTop_zero
  have hev := (ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  have hB1 : 1 ≤ slabScale H n := one_le_slabScale H n (Nat.cast_nonneg n)
  have hpos := RelationalDeSitterBranch.diagonalMesh_pos n
  rw [slabMesh, le_div_iff₀ (by positivity)]
  have hle : 24 * κ * slabScale H n ≤ slabConst H κ n := by
    unfold slabConst
    have hκ4 : κ ≤ κ ^ 4 := by
      calc κ = κ ^ 1 := (pow_one κ).symm
        _ ≤ κ ^ 4 := pow_le_pow_right₀ hκ (by norm_num)
    have hB4 : slabScale H n ≤ slabScale H n ^ 4 := by
      calc slabScale H n = slabScale H n ^ 1 := (pow_one _).symm
        _ ≤ slabScale H n ^ 4 := pow_le_pow_right₀ hB1 (by norm_num)
    have : κ * slabScale H n ≤ κ ^ 4 * slabScale H n ^ 4 :=
      mul_le_mul hκ4 hB4 (by linarith) (by positivity)
    nlinarith
  nlinarith

/-! ### Developed edges and the normalized torsion defect -/

/-- The inverse sub-link `exp(φ K(u))` undoes the exact sub-link `exp(−φ K(u))`. -/
theorem exp_smul_boost_mul_inv (φ : ℝ) (u : Fin 3 → ℝ) :
    exp (φ • boost u) * exp (φ • (-boost u)) = 1 := by
  rw [smul_neg, ← Matrix.exp_add_of_commute (φ • boost u) (-(φ • boost u))
    ((Commute.refl (φ • boost u)).neg_right), add_neg_cancel]
  exact exp_zero

/-- **Developed edge** `E_e = ∫₀¹ U_{s(e)←γ(r)} ϑ_{γ(r)}(γ'(r)) dr` of the straight edge from
time `t` with displacement `V`; `U_{s(e)←γ(r)} = exp(φ(r) K(u))` is the inverse of the exact
sub-link `exp(−φ(r) K(u))` (`exp_smul_boost_mul_inv`). -/
noncomputable def developedEdge (H t : ℝ) (V : TVec) : Idx → ℝ :=
  ∫ r in (0 : ℝ)..1, (exp (phase H t V.1 r • boost V.2)) *ᵥ coframe H (t + r * V.1) V

/-- **Covariant developed-edge closure** `∑_e U_{x_p←s(e)} E_e` of the loop with edge
displacements `Vs` starting at `(t, x)`, transported to the reference point `x_p = (tm, xm)`
along straight segments by exact links. -/
noncomputable def torsionSum (H tm : ℝ) (xm : Fin 3 → ℝ) :
    ℝ → (Fin 3 → ℝ) → List TVec → (Idx → ℝ)
  | _, _, [] => 0
  | t, x, V :: Vs => (edgeLink H t (tm - t, xm - x)) *ᵥ developedEdge H t V
      + torsionSum H tm xm (t + V.1) (x + V.2) Vs

/-- **Normalized torsion defect** `𝔱_p = |p|⁻¹ ∑_{e ⊂ ∂p} U_{x_p←s(e)} E_e`
(`eq:supp-torsion-defect`, with developed edges). -/
noncomputable def torsionDefect (H t : ℝ) (x : Fin 3 → ℝ) (tm : ℝ) (xm : Fin 3 → ℝ)
    (Vs : List TVec) (area : ℝ) : Idx → ℝ :=
  area⁻¹ • torsionSum H tm xm t x Vs

/-- Right action `M ↦ M w` as a continuous linear map. -/
noncomputable def mulVecRight (w : Idx → ℝ) : Gen →L[ℝ] (Idx → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M *ᵥ w
      map_add' := fun M N => Matrix.add_mulVec M N w
      map_smul' := fun c M => by simp [Matrix.smul_mulVec] }

theorem developedEdge_spatial (H t : ℝ) (u : Fin 3 → ℝ) :
    developedEdge H t (0, u)
      = (∫ r in (0 : ℝ)..1, exp (r • ((H * Real.exp (H * t)) • boost u)))
          *ᵥ coframe H t (0, u) := by
  have h : ∀ r : ℝ, (exp (phase H t (0, u).1 r • boost (0, u).2)) *ᵥ
      coframe H (t + r * (0, u).1) (0, u)
      = mulVecRight (coframe H t (0, u)) (exp (r • ((H * Real.exp (H * t)) • boost u))) := by
    intro r
    simp [mulVecRight, smul_smul]
  simp_rw [developedEdge, h]
  exact (ContinuousLinearMap.intervalIntegral_comp_comm (mulVecRight (coframe H t (0, u)))
    ((LogBCH.continuous_exp_smul _).intervalIntegrable 0 1)).trans rfl

theorem norm_coframe_spatial_le (H t : ℝ) (u : Fin 3 → ℝ) :
    ‖coframe H t (0, u)‖ ≤ Real.exp (H * t) * ‖u‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun A => ?_
  cases A with
  | none => simp [coframe]; positivity
  | some a =>
    simp only [coframe, Option.elim, Real.norm_eq_abs, abs_mul, Real.abs_exp]
    exact mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm u a) (by positivity)

/-- First-order potential of the spatial closure sum:
`G(y) = (c e^{Ht} (½ y·y − x_p·y), e^{Ht} y)`, `c = H e^{Ht}`. -/
noncomputable def spatialPotential (H t : ℝ) (xm y : Fin 3 → ℝ) : Idx → ℝ :=
  fun A => Option.elim A
    (H * Real.exp (H * t) * Real.exp (H * t) * ((1 / 2 : ℝ) * (y ⬝ᵥ y) - xm ⬝ᵥ y))
    fun a => Real.exp (H * t) * y a

/-- The first-order part of one transported developed spatial edge is an exact increment:
`(1 + X + Y/2) ϑ(0,u) = G(x + u) − G(x)` with `X = −c K(x_p − x)`, `Y = c K(u)`. -/
theorem firstOrder_spatial_eq (H t : ℝ) (xm x u : Fin 3 → ℝ) :
    (1 + (H * Real.exp (H * t)) • (-boost (xm - x))
        + (1 / 2 : ℝ) • ((H * Real.exp (H * t)) • boost u)) *ᵥ coframe H t (0, u)
      = spatialPotential H t xm (x + u) - spatialPotential H t xm x := by
  funext A
  cases A with
  | none =>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_option, coframe,
      spatialPotential, Fin.sum_univ_three, Matrix.one_apply]
    ring
  | some a =>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_option, coframe,
      spatialPotential, Matrix.one_apply]
    ring

/-- **Torsion defect of a spatial face, general form**: for a polygon of spatial edges `us`
starting at `x`, with `‖x_p − x‖ + ∑‖uᵢ‖ ≤ D` and `3 |H| e^{Ht} D ≤ ρ ≤ 1`, the closure sum
differs from the exact increment `G(x + ∑uᵢ) − G(x)` by at most `20 ρ² e^{Ht} ∑ ‖uᵢ‖`. -/
theorem norm_torsionSum_spatial_sub_le (H t : ℝ) (xm : Fin 3 → ℝ) {D ρ : ℝ}
    (hρ : 3 * (|H| * Real.exp (H * t)) * D ≤ ρ) (hρ1 : ρ ≤ 1) :
    ∀ (us : List (Fin 3 → ℝ)) (x : Fin 3 → ℝ), ‖xm - x‖ + (us.map fun u => ‖u‖).sum ≤ D →
      ‖torsionSum H t xm t x (us.map spatialVec)
          - (spatialPotential H t xm (x + us.sum) - spatialPotential H t xm x)‖
        ≤ 20 * ρ ^ 2 * Real.exp (H * t) * (us.map fun u => ‖u‖).sum := by
  intro us
  induction us with
  | nil => intro x _; simp [torsionSum]
  | cons u us ih =>
    intro x hD
    simp only [List.map_cons, List.sum_cons] at hD ⊢
    have hD' : ‖xm - (x + u)‖ + (us.map fun u => ‖u‖).sum ≤ D := by
      have : ‖xm - (x + u)‖ ≤ ‖xm - x‖ + ‖u‖ := by
        rw [show xm - (x + u) = (xm - x) - u by abel]; exact norm_sub_le _ _
      linarith
    have ihx := ih (x + u) hD'
    set c := H * Real.exp (H * t)
    set X : Gen := c • (-boost (xm - x))
    set Y : Gen := c • boost u
    set B := ∫ r in (0 : ℝ)..1, exp (r • Y)
    have hc : |c| = |H| * Real.exp (H * t) := by
      simp only [c, abs_mul, Real.abs_exp]
    have hX : ‖X‖ ≤ ρ := by
      simp only [X, norm_smul, norm_neg, Real.norm_eq_abs, hc]
      refine le_trans ?_ hρ
      have := norm_boost_le (xm - x)
      have h1 : ‖xm - x‖ ≤ D := by
        have := List.sum_nonneg (l := us.map fun u => ‖u‖) (fun y hy => by
          obtain ⟨v, -, rfl⟩ := List.mem_map.1 hy; exact norm_nonneg _)
        linarith [norm_nonneg u]
      calc |H| * Real.exp (H * t) * ‖boost (xm - x)‖ ≤ |H| * Real.exp (H * t) * (3 * D) := by
            gcongr; linarith
        _ = 3 * (|H| * Real.exp (H * t)) * D := by ring
    have hY : ‖Y‖ ≤ ρ := by
      simp only [Y, norm_smul, Real.norm_eq_abs, hc]
      refine le_trans ?_ hρ
      have := norm_boost_le u
      have h1 : ‖u‖ ≤ D := by
        have := List.sum_nonneg (l := us.map fun u => ‖u‖) (fun y hy => by
          obtain ⟨v, -, rfl⟩ := List.mem_map.1 hy; exact norm_nonneg _)
        linarith [norm_nonneg (xm - x)]
      calc |H| * Real.exp (H * t) * ‖boost u‖ ≤ |H| * Real.exp (H * t) * (3 * D) := by
            gcongr; linarith
        _ = 3 * (|H| * Real.exp (H * t)) * D := by ring
    have hterm : (edgeLink H t (t - t, xm - x)) *ᵥ developedEdge H t (0, u)
        = (spatialPotential H t xm (x + u) - spatialPotential H t xm x)
          + (exp X * B - (1 + X + (1 / 2 : ℝ) • Y)) *ᵥ coframe H t (0, u) := by
      rw [sub_self, edgeLink_spatial, developedEdge_spatial, ← firstOrder_spatial_eq,
        Matrix.mulVec_mulVec, ← Matrix.add_mulVec]
      congr 1
      simp only [X, Y, B, c, smul_neg]
      abel
    have hrem : ‖(exp X * B - (1 + X + (1 / 2 : ℝ) • Y)) *ᵥ coframe H t (0, u)‖
        ≤ 20 * ρ ^ 2 * (Real.exp (H * t) * ‖u‖) :=
      (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul
        (LogBCH.norm_exp_mul_integral_exp_sub_le hX hY hρ1) (norm_coframe_spatial_le H t u)
        (norm_nonneg _) (by positivity))
    simp only [torsionSum, LinearMap.inr_apply, add_zero]
    rw [hterm]
    have e : spatialPotential H t xm (x + (u + us.sum)) - spatialPotential H t xm x
        = (spatialPotential H t xm (x + u) - spatialPotential H t xm x)
          + (spatialPotential H t xm (x + u + us.sum) - spatialPotential H t xm (x + u)) := by
      rw [add_assoc]; abel
    rw [e]
    calc ‖(spatialPotential H t xm (x + u) - spatialPotential H t xm x
            + (exp X * B - (1 + X + (1 / 2 : ℝ) • Y)) *ᵥ coframe H t (0, u)
            + torsionSum H t xm t (x + u) (us.map spatialVec))
          - (spatialPotential H t xm (x + u) - spatialPotential H t xm x
            + (spatialPotential H t xm (x + u + us.sum) - spatialPotential H t xm (x + u)))‖
        = ‖(exp X * B - (1 + X + (1 / 2 : ℝ) • Y)) *ᵥ coframe H t (0, u)
            + (torsionSum H t xm t (x + u) (us.map spatialVec)
              - (spatialPotential H t xm (x + u + us.sum)
                - spatialPotential H t xm (x + u)))‖ := by congr 1; abel
      _ ≤ 20 * ρ ^ 2 * (Real.exp (H * t) * ‖u‖)
          + 20 * ρ ^ 2 * Real.exp (H * t) * (us.map fun u => ‖u‖).sum :=
          (norm_add_le _ _).trans (add_le_add hrem ihx)
      _ = 20 * ρ ^ 2 * Real.exp (H * t) * (‖u‖ + (us.map fun u => ‖u‖).sum) := by ring

/-- **Torsion defect of a closed spatial face**: `‖𝔱_p‖ ≤ 20 ρ² e^{Ht} ∑‖uᵢ‖ / |p|` (the
first-order part telescopes to zero around the closed loop; the continuum torsion vanishes). -/
theorem norm_torsionDefect_spatial_le (H t area : ℝ) (harea : 0 < area) (xm x : Fin 3 → ℝ)
    (us : List (Fin 3 → ℝ)) (hclosed : us.sum = 0) {D ρ : ℝ}
    (hD : ‖xm - x‖ + (us.map fun u => ‖u‖).sum ≤ D)
    (hρ : 3 * (|H| * Real.exp (H * t)) * D ≤ ρ) (hρ1 : ρ ≤ 1) :
    ‖torsionDefect H t x t xm (us.map spatialVec) area‖
      ≤ 20 * ρ ^ 2 * Real.exp (H * t) * (us.map fun u => ‖u‖).sum / area := by
  have := norm_torsionSum_spatial_sub_le H t xm hρ hρ1 us x hD
  rw [hclosed, add_zero, sub_self, sub_zero] at this
  rw [torsionDefect, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos harea,
    inv_mul_le_iff₀ harea]
  refine this.trans (le_of_eq ?_)
  field_simp

/-- In the flat regulator every developed edge is the coordinate displacement. -/
theorem developedEdge_flat (t : ℝ) (V : TVec) :
    developedEdge 0 t V = fun A => Option.elim A V.1 fun a => V.2 a := by
  simp only [developedEdge, phase, zero_mul, intervalIntegral.integral_zero, zero_smul,
    exp_zero, Matrix.one_mulVec]
  have : ∀ r : ℝ, coframe 0 (t + r * V.1) V = fun A => Option.elim A V.1 fun a => V.2 a := by
    intro r; funext A; cases A <;> simp [coframe]
  simp [this]

/-- **Flat regulator**: the torsion closure of every closed loop vanishes. -/
theorem torsionSum_flat (tm : ℝ) (xm : Fin 3 → ℝ) :
    ∀ (Vs : List TVec) (t : ℝ) (x : Fin 3 → ℝ), Vs.sum = 0 → torsionSum 0 tm xm t x Vs = 0 := by
  have key : ∀ (Vs : List TVec) (t : ℝ) (x : Fin 3 → ℝ),
      torsionSum 0 tm xm t x Vs = fun A => Option.elim A Vs.sum.1 fun a => Vs.sum.2 a := by
    intro Vs
    induction Vs with
    | nil => intro t x; funext A; cases A <;> simp [torsionSum]
    | cons V Vs ih =>
      intro t x
      simp only [torsionSum, edgeLink_flat, Matrix.one_mulVec, developedEdge_flat, ih]
      funext A; cases A <;> simp
  intro Vs t x h
  rw [key, h]; funext A; cases A <;> simp

/-! ### Torsion defect of the edge × time-step faces -/

/-- The internal vector `(τ, 0)`. -/
def tvec (τ : ℝ) : Idx → ℝ := fun A => Option.elim A τ fun _ => 0

theorem norm_tvec_le (τ : ℝ) : ‖tvec τ‖ ≤ |τ| :=
  (pi_norm_le_iff_of_nonneg (abs_nonneg τ)).2 fun A => by
    cases A <;> simp [tvec]

/-- Time edges are developed trivially: `E = (τ, 0)`. -/
theorem developedEdge_time (H t τ : ℝ) : developedEdge H t (τ, 0) = tvec τ := by
  have hc : ∀ r : ℝ, coframe H (t + r * τ) (τ, 0) = tvec τ := by
    intro r; funext A; cases A <;> simp [coframe, tvec]
  simp [developedEdge, hc]

/-- `τ φ(1) = e^{H(t+τ)} − e^{Ht}` (fundamental theorem of calculus for the link phase). -/
theorem mul_phase_one (H t τ : ℝ) :
    τ * phase H t τ 1 = Real.exp (H * (t + τ)) - Real.exp (H * t) := by
  have hd : ∀ r : ℝ, HasDerivAt (fun r => Real.exp (H * (t + r * τ)))
      (τ * (H * Real.exp (H * (t + r * τ)))) r := by
    intro r
    have := ((((hasDerivAt_id r).mul_const τ).const_add t).const_mul H).exp
    simp only [id_eq] at this
    convert this using 1; ring
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1) (fun r _ => hd r)
    ((continuous_const.mul (continuous_phaseIntegrand H t τ)).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul] at this
  rw [phase, this]; simp

/-- `|φ(1) − H e^{Ht}| ≤ |H| e^{Ht} · 2|Hτ|` for `|Hτ| ≤ 1`. -/
theorem abs_phase_sub_le (H t τ : ℝ) (hτ : |H * τ| ≤ 1) :
    |phase H t τ 1 - H * Real.exp (H * t)| ≤ |H| * Real.exp (H * t) * (2 * |H * τ|) := by
  have e : phase H t τ 1 - H * Real.exp (H * t)
      = ∫ r in (0 : ℝ)..1, (H * Real.exp (H * (t + r * τ)) - H * Real.exp (H * t)) := by
    rw [intervalIntegral.integral_sub ((continuous_phaseIntegrand H t τ).intervalIntegrable 0 1)
      (continuous_const.intervalIntegrable 0 1)]
    simp [phase]
  rw [e]
  have h : ∀ r ∈ Ι (0 : ℝ) 1, ‖H * Real.exp (H * (t + r * τ)) - H * Real.exp (H * t)‖
      ≤ |H| * Real.exp (H * t) * (2 * |H * τ|) := by
    intro r hr
    rw [uIoc_of_le zero_le_one] at hr
    have hrτ : |H * (r * τ)| ≤ |H * τ| := by
      rw [show H * (r * τ) = r * (H * τ) by ring, abs_mul, abs_of_pos hr.1]
      exact mul_le_of_le_one_left (abs_nonneg _) hr.2
    have e2 : H * Real.exp (H * (t + r * τ)) - H * Real.exp (H * t)
        = H * Real.exp (H * t) * (Real.exp (H * (r * τ)) - 1) := by
      rw [mul_add, Real.exp_add]; ring
    rw [e2, Real.norm_eq_abs, abs_mul, abs_mul, Real.abs_exp]
    gcongr
    exact (Real.abs_exp_sub_one_le (hrτ.trans hτ)).trans (by linarith)
  have := intervalIntegral.norm_integral_le_of_norm_le_const h
  simpa using this

/-- The four transported developed edges of the edge × time-step face, with the face midpoint
`x_p = (t + h/2, x + u/2)` as reference point. -/
theorem torsionSum_mixed_eq (H t h : ℝ) (x u : Fin 3 → ℝ) :
    torsionSum H (t + h / 2) (x + (1 / 2 : ℝ) • u) t x (mixedLoop h u)
      = (exp (phase H t (h / 2) 1 • (-boost ((1 / 2 : ℝ) • u)))) *ᵥ developedEdge H t (0, u)
        + (exp (phase H t (h / 2) 1 • boost ((1 / 2 : ℝ) • u))) *ᵥ tvec h
        + (exp (phase H (t + h) (-(h / 2)) 1 • boost ((1 / 2 : ℝ) • u)))
            *ᵥ developedEdge H (t + h) (0, -u)
        + (exp (phase H (t + h) (-(h / 2)) 1 • (-boost ((1 / 2 : ℝ) • u)))) *ᵥ tvec (-h) := by
  have a1 : t + h / 2 - t = h / 2 := by ring
  have a2 : x + (1 / 2 : ℝ) • u - x = (1 / 2 : ℝ) • u := by abel
  have a3 : x + (1 / 2 : ℝ) • u - (x + u) = -((1 / 2 : ℝ) • u) := by module
  have a4 : t + h / 2 - (t + h) = -(h / 2) := by ring
  have a5 : x + (1 / 2 : ℝ) • u - (x + u + -u) = (1 / 2 : ℝ) • u := by abel
  simp only [mixedLoop, torsionSum, add_zero, edgeLink, developedEdge_time]
  rw [a1, a2, a3, a4, a5]
  simp only [map_neg, neg_neg]
  abel

/-- **Torsion defect of an edge × time-step face**: with `φ₀ = φ_t(h/2)`, `φ₁ = φ_{t+h}(−h/2)`,
`|φ₀|, |φ₁|, |H|e^{Ht}, |H|e^{H(t+h)} ≤ Λ`, `3 Λ ‖u‖ ≤ ρ ≤ 1` and `|Hh| ≤ 1`,
`‖𝔱_p‖ ≤ [20 ρ² (e^{Ht} + e^{H(t+h)}) ‖u‖ + 6 ρ² |h|
  + (3/2) ‖u‖² |H| |Hh| (e^{2Ht} + e^{2H(t+h)})] / |p|`.
The first-order spatial terms cancel exactly (`mul_phase_one`); the first-order time terms are
`O(‖u‖² h)`. -/
theorem norm_torsionDefect_mixed_le (H t h area : ℝ) (harea : 0 < area) (x u : Fin 3 → ℝ)
    {Λ ρ : ℝ} (hφ0 : |phase H t (h / 2) 1| ≤ Λ) (hφ1 : |phase H (t + h) (-(h / 2)) 1| ≤ Λ)
    (hc0 : |H| * Real.exp (H * t) ≤ Λ) (hc1 : |H| * Real.exp (H * (t + h)) ≤ Λ)
    (hρ : 3 * Λ * ‖u‖ ≤ ρ) (hρ1 : ρ ≤ 1) (hHh : |H * h| ≤ 1) :
    ‖torsionDefect H t x (t + h / 2) (x + (1 / 2 : ℝ) • u) (mixedLoop h u) area‖
      ≤ (20 * ρ ^ 2 * ((Real.exp (H * t) + Real.exp (H * (t + h))) * ‖u‖) + 6 * ρ ^ 2 * |h|
          + 3 / 2 * ‖u‖ ^ 2 * |H| * |H * h| * (Real.exp (H * t) ^ 2
            + Real.exp (H * (t + h)) ^ 2)) / area := by
  set φ0 := phase H t (h / 2) 1
  set φ1 := phase H (t + h) (-(h / 2)) 1
  set c0 := H * Real.exp (H * t)
  set c1 := H * Real.exp (H * (t + h))
  set E0 := Real.exp (H * t)
  set E1 := Real.exp (H * (t + h))
  set v : Fin 3 → ℝ := (1 / 2 : ℝ) • u
  have hΛ0 : 0 ≤ Λ := le_trans (abs_nonneg _) hφ0
  have hKv : ‖boost v‖ ≤ 3 * ‖u‖ := by
    refine (norm_boost_le v).trans ?_
    simp only [v, norm_smul]; norm_num
    nlinarith [norm_nonneg u]
  have hKu : ‖boost u‖ ≤ 3 * ‖u‖ := norm_boost_le u
  have hKnu : ‖boost (-u)‖ ≤ 3 * ‖u‖ := by rw [map_neg, norm_neg]; exact hKu
  have bnd : ∀ (a : ℝ) (w : Fin 3 → ℝ), |a| ≤ Λ → ‖boost w‖ ≤ 3 * ‖u‖ → ‖a • boost w‖ ≤ ρ := by
    intro a w ha hw
    rw [norm_smul, Real.norm_eq_abs]
    calc |a| * ‖boost w‖ ≤ Λ * (3 * ‖u‖) :=
          mul_le_mul ha hw (norm_nonneg _) hΛ0
      _ = 3 * Λ * ‖u‖ := by ring
      _ ≤ ρ := hρ
  have habs : ∀ y : ℝ, |y| ≤ Λ → |y| ≤ Λ := fun _ h => h
  have hc0' : |c0| ≤ Λ := by simpa [c0, abs_mul, Real.abs_exp] using hc0
  have hc1' : |c1| ≤ Λ := by simpa [c1, abs_mul, Real.abs_exp] using hc1
  -- the four exponents
  set X0 : Gen := φ0 • (-boost v)
  set Y0 : Gen := c0 • boost u
  set X1 : Gen := φ0 • boost v
  set X2 : Gen := φ1 • boost v
  set Y2 : Gen := c1 • boost (-u)
  set X3 : Gen := φ1 • (-boost v)
  have hX0 : ‖X0‖ ≤ ρ := by
    simpa [X0, smul_neg, norm_neg] using bnd φ0 v hφ0 hKv
  have hX1 : ‖X1‖ ≤ ρ := bnd φ0 v hφ0 hKv
  have hX2 : ‖X2‖ ≤ ρ := bnd φ1 v hφ1 hKv
  have hX3 : ‖X3‖ ≤ ρ := by
    simpa [X3, smul_neg, norm_neg] using bnd φ1 v hφ1 hKv
  have hY0 : ‖Y0‖ ≤ ρ := bnd c0 u hc0' hKu
  have hY2 : ‖Y2‖ ≤ ρ := bnd c1 (-u) hc1' hKnu
  set w0 := coframe H t (0, u)
  set w2 := coframe H (t + h) (0, -u)
  set B0 := ∫ r in (0 : ℝ)..1, exp (r • Y0)
  set B2 := ∫ r in (0 : ℝ)..1, exp (r • Y2)
  -- first-order part
  set F : Idx → ℝ := (1 + X0 + (1 / 2 : ℝ) • Y0) *ᵥ w0 + (1 + X1) *ᵥ tvec h
    + (1 + X2 + (1 / 2 : ℝ) • Y2) *ᵥ w2 + (1 + X3) *ᵥ tvec (-h)
  have hsplit : torsionSum H (t + h / 2) (x + (1 / 2 : ℝ) • u) t x (mixedLoop h u)
      = F + ((exp X0 * B0 - (1 + X0 + (1 / 2 : ℝ) • Y0)) *ᵥ w0
        + (exp X1 - 1 - X1) *ᵥ tvec h
        + (exp X2 * B2 - (1 + X2 + (1 / 2 : ℝ) • Y2)) *ᵥ w2
        + (exp X3 - 1 - X3) *ᵥ tvec (-h)) := by
    rw [torsionSum_mixed_eq, developedEdge_spatial, developedEdge_spatial]
    simp only [F, Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.add_mulVec]
    have r0 : (H * Real.exp (H * t)) • boost u = Y0 := rfl
    have r2 : (H * Real.exp (H * (t + h))) • boost (-u) = Y2 := rfl
    rw [r0, r2]
    simp only [X0, X1, X2, X3, B0, B2, w0, w2, v]
    abel
  -- the first-order part is purely temporal and small
  have hFsome : ∀ a : Fin 3, F (some a) = 0 := by
    intro a
    have hp0 : h / 2 * φ0 = Real.exp (H * (t + h / 2)) - E0 := mul_phase_one H t (h / 2)
    have hp1 : -(h / 2) * φ1 = Real.exp (H * (t + h / 2)) - E1 := by
      have := mul_phase_one H (t + h) (-(h / 2))
      rw [show t + h + -(h / 2) = t + h / 2 by ring] at this
      exact this
    simp [F, X0, X1, X2, X3, Y0, Y2, v, w0, w2, Matrix.add_mulVec, Matrix.mulVec, dotProduct,
      Fintype.sum_option, coframe, tvec, Matrix.one_apply]
    linear_combination (u a) * hp0 - (u a) * hp1
  have hFnone : F none = E0 * (u ⬝ᵥ u) / 2 * (c0 - φ0) + E1 * (u ⬝ᵥ u) / 2 * (c1 - φ1) := by
    simp [F, X0, X1, X2, X3, Y0, Y2, v, w0, w2, Matrix.add_mulVec, Matrix.mulVec, dotProduct,
      Fintype.sum_option, coframe, tvec, Matrix.one_apply, Fin.sum_univ_three]
    ring
  have huu : |u ⬝ᵥ u| ≤ 3 * ‖u‖ ^ 2 := by
    simp only [dotProduct, Fin.sum_univ_three]
    have h0 := norm_le_pi_norm u 0
    have h1 := norm_le_pi_norm u 1
    have h2 := norm_le_pi_norm u 2
    simp only [Real.norm_eq_abs] at h0 h1 h2
    rw [abs_of_nonneg (add_nonneg (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
      (mul_self_nonneg _))]
    nlinarith [abs_nonneg (u 0), abs_nonneg (u 1), abs_nonneg (u 2), sq_abs (u 0),
      sq_abs (u 1), sq_abs (u 2)]
  have hpc0 : |c0 - φ0| ≤ |H| * E0 * |H * h| := by
    have := abs_phase_sub_le H t (h / 2) (by
      rw [show H * (h / 2) = (H * h) / 2 by ring, abs_div, abs_two]
      linarith [abs_nonneg (H * h)])
    rw [abs_sub_comm]
    refine this.trans (le_of_eq ?_)
    rw [show H * (h / 2) = (H * h) / 2 by ring, abs_div, abs_two]; ring
  have hpc1 : |c1 - φ1| ≤ |H| * E1 * |H * h| := by
    have := abs_phase_sub_le H (t + h) (-(h / 2)) (by
      rw [show H * -(h / 2) = -((H * h) / 2) by ring, abs_neg, abs_div, abs_two]
      linarith [abs_nonneg (H * h)])
    rw [abs_sub_comm]
    refine this.trans (le_of_eq ?_)
    rw [show H * -(h / 2) = -((H * h) / 2) by ring, abs_neg, abs_div, abs_two]; ring
  have hnn : 0 ≤ 3 / 2 * ‖u‖ ^ 2 * |H| * |H * h| * (E0 ^ 2 + E1 ^ 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (abs_nonneg _))
      (abs_nonneg _)) (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hF : ‖F‖ ≤ 3 / 2 * ‖u‖ ^ 2 * |H| * |H * h| * (E0 ^ 2 + E1 ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg hnn).2 fun A => ?_
    cases A with
    | some a => rw [hFsome, norm_zero]; exact hnn
    | none =>
      rw [hFnone, Real.norm_eq_abs]
      have hE0 : 0 < E0 := Real.exp_pos _
      have hE1 : 0 < E1 := Real.exp_pos _
      calc |E0 * (u ⬝ᵥ u) / 2 * (c0 - φ0) + E1 * (u ⬝ᵥ u) / 2 * (c1 - φ1)|
          ≤ E0 * |u ⬝ᵥ u| / 2 * |c0 - φ0| + E1 * |u ⬝ᵥ u| / 2 * |c1 - φ1| := by
            refine (abs_add_le _ _).trans (le_of_eq ?_)
            rw [abs_mul, abs_mul, abs_div, abs_div, abs_mul, abs_mul, abs_of_pos hE0,
              abs_of_pos hE1, abs_two]
        _ ≤ E0 * (3 * ‖u‖ ^ 2) / 2 * (|H| * E0 * |H * h|)
            + E1 * (3 * ‖u‖ ^ 2) / 2 * (|H| * E1 * |H * h|) := by gcongr
        _ = 3 / 2 * ‖u‖ ^ 2 * |H| * |H * h| * (E0 ^ 2 + E1 ^ 2) := by ring
  -- the remainders
  have hw0 : ‖w0‖ ≤ E0 * ‖u‖ := norm_coframe_spatial_le H t u
  have hw2 : ‖w2‖ ≤ E1 * ‖u‖ := by
    simpa [norm_neg] using norm_coframe_spatial_le H (t + h) (-u)
  have hρ0 : 0 ≤ ρ := le_trans (mul_nonneg (mul_nonneg (by norm_num) hΛ0) (norm_nonneg u)) hρ
  have he3 : ∀ X : Gen, ‖X‖ ≤ ρ → ‖exp X - 1 - X‖ ≤ 3 * ρ ^ 2 := by
    intro X hX
    refine (LogBCH.norm_exp_sub_linear_le X).trans ?_
    have h1 : ‖X‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hX 2
    have h2 : Real.exp ‖X‖ ≤ 3 := by
      have := Real.exp_one_lt_d9
      have : Real.exp ‖X‖ ≤ Real.exp 1 := Real.exp_le_exp.2 (hX.trans hρ1)
      linarith
    nlinarith [sq_nonneg ‖X‖, Real.exp_pos ‖X‖]
  have r0 := (Matrix.linfty_opNorm_mulVec (exp X0 * B0 - (1 + X0 + (1 / 2 : ℝ) • Y0)) w0).trans
    (mul_le_mul (LogBCH.norm_exp_mul_integral_exp_sub_le hX0 hY0 hρ1) hw0 (norm_nonneg _)
      (by positivity))
  have r2 := (Matrix.linfty_opNorm_mulVec (exp X2 * B2 - (1 + X2 + (1 / 2 : ℝ) • Y2)) w2).trans
    (mul_le_mul (LogBCH.norm_exp_mul_integral_exp_sub_le hX2 hY2 hρ1) hw2 (norm_nonneg _)
      (by positivity))
  have r1 := (Matrix.linfty_opNorm_mulVec (exp X1 - 1 - X1) (tvec h)).trans
    (mul_le_mul (he3 X1 hX1) (norm_tvec_le h) (norm_nonneg _) (by positivity))
  have r3 := (Matrix.linfty_opNorm_mulVec (exp X3 - 1 - X3) (tvec (-h))).trans
    (mul_le_mul (he3 X3 hX3) (norm_tvec_le (-h)) (norm_nonneg _) (by positivity))
  rw [abs_neg] at r3
  rw [torsionDefect, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos harea,
    inv_mul_le_iff₀ harea, hsplit]
  calc _ ≤ ‖F‖ + (‖(exp X0 * B0 - (1 + X0 + (1 / 2 : ℝ) • Y0)) *ᵥ w0‖
          + ‖(exp X1 - 1 - X1) *ᵥ tvec h‖
          + ‖(exp X2 * B2 - (1 + X2 + (1 / 2 : ℝ) • Y2)) *ᵥ w2‖
          + ‖(exp X3 - 1 - X3) *ᵥ tvec (-h)‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl
          ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
            ((norm_add_le _ _).trans le_rfl) le_rfl)) le_rfl)))
    _ ≤ 3 / 2 * ‖u‖ ^ 2 * |H| * |H * h| * (E0 ^ 2 + E1 ^ 2)
          + (20 * ρ ^ 2 * (E0 * ‖u‖) + 3 * ρ ^ 2 * |h| + 20 * ρ ^ 2 * (E1 * ‖u‖)
            + 3 * ρ ^ 2 * |h|) := by gcongr
    _ = area * ((20 * ρ ^ 2 * ((E0 + E1) * ‖u‖) + 6 * ρ ^ 2 * |h|
          + 3 / 2 * ‖u‖ ^ 2 * |H| * |H * h| * (E0 ^ 2 + E1 ^ 2)) / area) := by
        field_simp; ring

/-! ### Uniform torsion bounds, the combined slab estimate and the exhaustion -/

theorem abs_phase_le (H t τ : ℝ) :
    |phase H t τ 1| ≤ |H| * Real.exp (|H| * (|t| + |τ|)) := by
  have h : ∀ r ∈ Ι (0 : ℝ) 1, ‖H * Real.exp (H * (t + r * τ))‖
      ≤ |H| * Real.exp (|H| * (|t| + |τ|)) := by
    intro r hr
    rw [uIoc_of_le zero_le_one] at hr
    rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (abs_nonneg _)
    calc H * (t + r * τ) ≤ |H * (t + r * τ)| := le_abs_self _
      _ = |H| * |t + r * τ| := abs_mul _ _
      _ ≤ |H| * (|t| + |τ|) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          calc |t + r * τ| ≤ |t| + |r * τ| := abs_add_le _ _
            _ ≤ |t| + |τ| := by
                have : |r * τ| ≤ |τ| := by
                  rw [abs_mul, abs_of_pos hr.1]
                  exact mul_le_of_le_one_left (abs_nonneg _) hr.2
                linarith
  have := intervalIntegral.norm_integral_le_of_norm_le_const h
  simpa [phase] using this

theorem exp_le_slabScale (H T s : ℝ) (hs : |s| ≤ T + 1) : Real.exp (H * s) ≤ slabScale H T := by
  unfold slabScale
  have h1 : Real.exp (H * s) ≤ Real.exp (|H| * (T + 1)) := by
    refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hs (abs_nonneg _)
  nlinarith [abs_nonneg H, Real.exp_pos (|H| * (T + 1))]

theorem abs_le_slabScale (H T : ℝ) (hT : 0 ≤ T) : |H| ≤ slabScale H T := by
  unfold slabScale
  have := Real.one_le_exp (by positivity : 0 ≤ |H| * (T + 1))
  nlinarith [abs_nonneg H]

/-- **Uniform torsion-defect bound on a compact slab** (torsion part of
`eq:supp-finite-defect-bound`): under the hypotheses of `curvatureDefect_slab_le`, every closed
spatial face (reference point within `κh` of the base vertex) and every edge × time-step face
(reference point its midpoint) has `‖𝔱_p‖ ≤ C_T h`. -/
theorem torsionDefect_slab_le (H κ T : ℝ) (hκ : 1 ≤ κ) (hT : 0 ≤ T) {h : ℝ} (hh0 : 0 < h)
    (hh : h ≤ slabMesh H κ T) {t : ℝ} (ht : |t| ≤ T) :
    (∀ (us : List (Fin 3 → ℝ)) (x xm : Fin 3 → ℝ) (area : ℝ), us.sum = 0 →
        (us.map fun u => ‖u‖).sum ≤ κ * h → ‖xm - x‖ ≤ κ * h → h ^ 2 / κ ≤ area →
        ‖torsionDefect H t x t xm (us.map spatialVec) area‖ ≤ slabConst H κ T * h) ∧
    (∀ (u x : Fin 3 → ℝ) (area : ℝ), ‖u‖ ≤ κ * h → h ^ 2 / κ ≤ area →
        ‖torsionDefect H t x (t + h / 2) (x + (1 / 2 : ℝ) • u) (mixedLoop h u) area‖
          ≤ slabConst H κ T * h) := by
  set B := slabScale H T with hBdef
  have hB1 : 1 ≤ B := one_le_slabScale H T hT
  have hκ0 : 0 < κ := by linarith
  have hκBh : 24 * (κ * B * h) ≤ 1 := by
    have h24 : 0 < 24 * κ * B := by positivity
    have := hh
    rw [slabMesh, le_div_iff₀ h24] at this
    linarith
  have hh1 : h ≤ 1 := by nlinarith [mul_le_mul hκ hB1 zero_le_one (by linarith)]
  have hHB : |H| ≤ B := abs_le_slabScale H T hT
  have hE0 : Real.exp (H * t) ≤ B := exp_le_slabScale H T t (by linarith)
  have hc : |H| * Real.exp (H * t) ≤ B := by
    simpa using abs_mul_exp_le_slabScale H T t 0 ht le_rfl zero_le_one
  have harea_pos : 0 < h ^ 2 / κ := by positivity
  have hB3 : B ^ 3 ≤ B ^ 4 := pow_le_pow_right₀ hB1 (by norm_num)
  constructor
  · intro us x xm area hclosed hus hxm harea
    have hareapos : 0 < area := lt_of_lt_of_le harea_pos harea
    set ρ := 6 * (κ * B * h)
    have hρ : 3 * (|H| * Real.exp (H * t)) * (2 * (κ * h)) ≤ ρ := by
      have := mul_le_mul_of_nonneg_right hc (by positivity : (0 : ℝ) ≤ 6 * (κ * h))
      simp only [ρ]; nlinarith
    have hρ1 : ρ ≤ 1 := by simp only [ρ]; linarith
    have hb := norm_torsionDefect_spatial_le H t area hareapos xm x us hclosed
      (D := 2 * (κ * h)) (by linarith) hρ hρ1
    refine hb.trans ?_
    have hS0 : 0 ≤ (us.map fun u => ‖u‖).sum := List.sum_nonneg fun y hy => by
      obtain ⟨v, -, rfl⟩ := List.mem_map.1 hy; exact norm_nonneg _
    calc 20 * ρ ^ 2 * Real.exp (H * t) * (us.map fun u => ‖u‖).sum / area
        ≤ 20 * ρ ^ 2 * B * (κ * h) / (h ^ 2 / κ) := by gcongr
      _ = 720 * κ ^ 4 * B ^ 3 * h := by simp only [ρ]; field_simp; ring
      _ ≤ 1300 * κ ^ 4 * B ^ 4 * h := by gcongr; norm_num
      _ = slabConst H κ T * h := by rw [slabConst]
  · intro u x area hu harea
    have hareapos : 0 < area := lt_of_lt_of_le harea_pos harea
    have hφ0 : |phase H t (h / 2) 1| ≤ B := by
      refine (abs_phase_le H t (h / 2)).trans ?_
      have : |t| + |h / 2| ≤ T + 1 := by
        rw [abs_of_pos (by linarith : (0 : ℝ) < h / 2)]; linarith
      simp only [hBdef, slabScale]
      have e1 : Real.exp (|H| * (|t| + |h / 2|)) ≤ Real.exp (|H| * (T + 1)) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left this (abs_nonneg _))
      nlinarith [abs_nonneg H, Real.exp_pos (|H| * (|t| + |h / 2|))]
    have hφ1 : |phase H (t + h) (-(h / 2)) 1| ≤ B := by
      refine (abs_phase_le H (t + h) (-(h / 2))).trans ?_
      have : |t + h| + |-(h / 2)| ≤ T + 1 := by
        rw [abs_neg, abs_of_pos (by linarith : (0 : ℝ) < h / 2)]
        have := abs_add_le t h
        rw [abs_of_pos hh0] at this
        have h24 : 24 * h ≤ 1 := by nlinarith [mul_le_mul hκ hB1 zero_le_one (by linarith)]
        linarith
      simp only [hBdef, slabScale]
      have e1 : Real.exp (|H| * (|t + h| + |-(h / 2)|)) ≤ Real.exp (|H| * (T + 1)) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left this (abs_nonneg _))
      nlinarith [abs_nonneg H, Real.exp_pos (|H| * (|t + h| + |-(h / 2)|))]
    have hc1 : |H| * Real.exp (H * (t + h)) ≤ B :=
      abs_mul_exp_le_slabScale H T t h ht hh0.le hh1
    have hE1 : Real.exp (H * (t + h)) ≤ B := exp_le_slabScale H T (t + h) (by
      have := abs_add_le t h; rw [abs_of_pos hh0] at this; linarith)
    set ρ := 3 * (κ * B * h)
    have hρ : 3 * B * ‖u‖ ≤ ρ := by
      have := mul_le_mul_of_nonneg_left hu (by positivity : (0 : ℝ) ≤ 3 * B)
      simp only [ρ]; nlinarith
    have hρ1 : ρ ≤ 1 := by simp only [ρ]; linarith
    have hHh : |H * h| ≤ B * h := by
      rw [abs_mul, abs_of_pos hh0]; exact mul_le_mul_of_nonneg_right hHB hh0.le
    have hBh : B * h ≤ 1 := by nlinarith
    have hb := norm_torsionDefect_mixed_le H t h area hareapos x u hφ0 hφ1 hc hc1 hρ hρ1
      (hHh.trans hBh)
    refine hb.trans ?_
    have hu0 : 0 ≤ ‖u‖ := norm_nonneg u
    have hE0' : 0 ≤ Real.exp (H * t) := (Real.exp_pos _).le
    have hE1' : 0 ≤ Real.exp (H * (t + h)) := (Real.exp_pos _).le
    calc (20 * ρ ^ 2 * ((Real.exp (H * t) + Real.exp (H * (t + h))) * ‖u‖) + 6 * ρ ^ 2 * |h|
          + 3 / 2 * ‖u‖ ^ 2 * |H| * |H * h| * (Real.exp (H * t) ^ 2
            + Real.exp (H * (t + h)) ^ 2)) / area
        ≤ (20 * ρ ^ 2 * ((B + B) * (κ * h)) + 6 * ρ ^ 2 * h
          + 3 / 2 * (κ * h) ^ 2 * B * (B * h) * (B ^ 2 + B ^ 2)) / (h ^ 2 / κ) := by
          rw [abs_of_pos hh0]; gcongr
      _ = (360 * κ ^ 4 * B ^ 3 + 54 * κ ^ 3 * B ^ 2 + 3 * κ ^ 3 * B ^ 4) * h := by
          simp only [ρ]; field_simp; ring
      _ ≤ 1300 * κ ^ 4 * B ^ 4 * h := by
          have hk3 : κ ^ 3 ≤ κ ^ 4 := pow_le_pow_right₀ hκ (by norm_num)
          have hb2 : B ^ 2 ≤ B ^ 4 := pow_le_pow_right₀ hB1 (by norm_num)
          have hk4 : 0 ≤ κ ^ 4 := by positivity
          have hb4 : 0 ≤ B ^ 4 := by positivity
          have h1 : 360 * κ ^ 4 * B ^ 3 ≤ 360 * κ ^ 4 * B ^ 4 := by gcongr
          have h2 : 54 * κ ^ 3 * B ^ 2 ≤ 54 * κ ^ 4 * B ^ 4 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hk3 (by norm_num)) hb2 (by positivity)
              (by positivity)
          have h3 : 3 * κ ^ 3 * B ^ 4 ≤ 3 * κ ^ 4 * B ^ 4 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk3 (by norm_num)) hb4
          have := add_le_add (add_le_add h1 h2) h3
          nlinarith
      _ = slabConst H κ T * h := by rw [slabConst]

/-- **`thm:supp-finite-defects`, curvature and torsion part, de Sitter and flat regulators**:
along the diagonal exhaustion `h_n = 2^{−n²}`, `T_n = n`, for all large `n` every spatial face
and every edge × time-step face of the product complex in the slab `[−n, n]` has normalized
curvature and torsion defects at most `C_{T_n} h_n`, and `∑ₙ C_{T_n} h_n < ∞`. -/
theorem finiteDefects_diagonal (H κ : ℝ) (hκ : 1 ≤ κ) :
    Summable (fun n : ℕ => slabConst H κ n * RelationalDeSitterBranch.diagonalMesh n) ∧
    ∃ N : ℕ, ∀ n ≥ N, ∀ t : ℝ, |t| ≤ n →
      let h := RelationalDeSitterBranch.diagonalMesh n
      (∀ (us : List (Fin 3 → ℝ)) (x xm : Fin 3 → ℝ) (area : ℝ), us.sum = 0 →
          (us.map fun u => ‖u‖).sum ≤ κ * h → ‖xm - x‖ ≤ κ * h → h ^ 2 / κ ≤ area →
          ‖curvatureDefect H t t (us.map spatialVec) area‖
            + ‖torsionDefect H t x t xm (us.map spatialVec) area‖
            ≤ 2 * (slabConst H κ n * h)) ∧
      (∀ (u x : Fin 3 → ℝ) (area : ℝ), ‖u‖ ≤ κ * h → h ^ 2 / κ ≤ area →
          ‖curvatureDefect H t (t + h / 2) (mixedLoop h u) area‖
            + ‖torsionDefect H t x (t + h / 2) (x + (1 / 2 : ℝ) • u) (mixedLoop h u) area‖
            ≤ 2 * (slabConst H κ n * h)) := by
  obtain ⟨hsum, N, hN⟩ := diagonal_exhaustion H κ hκ
  refine ⟨hsum, N, fun n hn t ht => ?_⟩
  have hT : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hpos := RelationalDeSitterBranch.diagonalMesh_pos n
  obtain ⟨c1, c2⟩ := curvatureDefect_slab_le H κ n hκ hT hpos (hN n hn) ht
  obtain ⟨t1, t2⟩ := torsionDefect_slab_le H κ n hκ hT hpos (hN n hn) ht
  refine ⟨fun us x xm area h0 hus hxm harea => ?_, fun u x area hu harea => ?_⟩
  · have := add_le_add (c1 us area h0 hus harea) (t1 us x xm area h0 hus hxm harea)
    linarith
  · have := add_le_add (c2 u area hu harea) (t2 u x area hu harea)
    linarith

/-- **Flat regulator**: all curvature defects and the torsion closure of every closed loop
vanish identically. -/
theorem finiteDefects_flat (t tm : ℝ) (x xm : Fin 3 → ℝ) (Vs : List TVec) (area : ℝ)
    (hclosed : Vs.sum = 0) :
    curvatureDefect 0 t tm Vs area = 0 ∧ torsionDefect 0 t x tm xm Vs area = 0 := by
  refine ⟨curvatureDefect_flat t tm Vs area, ?_⟩
  rw [torsionDefect, torsionSum_flat tm xm Vs t x hclosed, smul_zero]

/-- Non-vacuity: the unit-square face `u = h e₁` of the product complex satisfies the
shape-regularity hypotheses with `κ = 1`, `|p| = h²`. -/
example (h : ℝ) (hh : 0 < h) :
    ‖(fun a : Fin 3 => if a = 0 then h else 0)‖ ≤ 1 * h ∧ h ^ 2 / 1 ≤ h ^ 2 := by
  refine ⟨(pi_norm_le_iff_of_nonneg (by linarith)).2 fun a => ?_, by simp⟩
  by_cases ha : a = 0 <;> simp [ha, abs_of_pos hh, hh.le]

end RenewalGeometry.DeSitterExactLink
