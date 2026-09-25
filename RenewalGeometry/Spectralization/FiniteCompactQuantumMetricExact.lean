/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite compact quantum metric-space structure

Paper `predictive_spectral_geometry`, label `prop:finite-CQMS`.

Two layers:

* **Commutator seminorm identities** (`eq:Leibniz-Lip`).  For a
  `*`-representation `π` on a finite Hilbert space and a Hermitian Dirac
  matrix `D`, the seminorm `L_D(a) = ‖[D, π a]‖` (Euclidean operator norm)
  satisfies the Leibniz inequality
  `L_D(ab) ≤ ‖π a‖ L_D(b) + ‖π b‖ L_D(a)` and the star identity
  `L_D(a^*) = L_D(a)` (`lipD_mul_le`, `lipD_star`).

* **Finite-dimensional Lip-norm theory** (`eq:finite-state-metric`,
  `eq:finite-Poincare-Lip`).  On a finite-dimensional real normed space `V`
  (the self-adjoint part `A_sa`) with a continuous seminorm `L` whose kernel is
  exactly the line `ℝ 1`, and a normalized functional `τ` (the trace):
  - the Poincaré–Lip inequality `‖a - τ(a) 1‖ ≤ C L(a)`
    (`exists_poincare_lip`);
  - the Monge–Kantorovich distance `mk_L(φ, ψ)` of `eq:finite-state-metric` on
    states (normalized contractive functionals) is finite, bounded by
    `C ‖φ - ψ‖ ≤ 2C`, and bi-Lipschitz equivalent to the dual norm distance
    (`mkDist_le_opNorm`, `opNorm_le_mkDist`), so that `mk_L`-convergence of
    states is exactly norm convergence in the finite-dimensional dual
    (`tendsto_mkDist_iff`);
  - conversely, if some `a` with `L(a) = 0` is separated by two states (which
    happens exactly when the kernel is larger than `ℝ 1`), the supremum in
    `eq:finite-state-metric` is unbounded (`not_bddAbove_of_kernel`).

Disclosed gaps: the paper's `‖a‖` is written here as `‖π a‖` (equal for a
faithful representation); the identification of the norm topology of the
finite-dimensional dual with the weak-`*` topology is standard and not
formalized (we prove the bi-Lipschitz comparison with the dual norm).
-/

open Matrix Filter Topology
open scoped Matrix.Norms.L2Operator

namespace RenewalGeometry
namespace FiniteCompactQuantumMetric

/-! ## Commutator seminorm identities -/

section Commutator

variable {A H : Type*} [Ring A] [Algebra ℂ A] [StarRing A]
  [Fintype H] [DecidableEq H]

/-- The spectral seminorm `L_D(a) = ‖[D, π(a)]‖`. -/
noncomputable def lipD (D : Matrix H H ℂ) (π : A →⋆ₐ[ℂ] Matrix H H ℂ) (a : A) : ℝ :=
  ‖D * π a - π a * D‖

theorem lipD_nonneg (D : Matrix H H ℂ) (π : A →⋆ₐ[ℂ] Matrix H H ℂ) (a : A) :
    0 ≤ lipD D π a := norm_nonneg _

omit [DecidableEq H] in
/-- The commutator product rule `[D, XY] = [D, X] Y + X [D, Y]`. -/
theorem commutator_mul (D X Y : Matrix H H ℂ) :
    D * (X * Y) - X * Y * D = (D * X - X * D) * Y + X * (D * Y - Y * D) := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

/-- **Leibniz inequality** `eq:Leibniz-Lip`. -/
theorem lipD_mul_le (D : Matrix H H ℂ) (π : A →⋆ₐ[ℂ] Matrix H H ℂ) (a b : A) :
    lipD D π (a * b) ≤ ‖π a‖ * lipD D π b + ‖π b‖ * lipD D π a := by
  unfold lipD
  rw [map_mul, commutator_mul]
  calc ‖(D * π a - π a * D) * π b + π a * (D * π b - π b * D)‖
      ≤ ‖(D * π a - π a * D) * π b‖ + ‖π a * (D * π b - π b * D)‖ := norm_add_le _ _
    _ ≤ ‖D * π a - π a * D‖ * ‖π b‖ + ‖π a‖ * ‖D * π b - π b * D‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = ‖π a‖ * ‖D * π b - π b * D‖ + ‖π b‖ * ‖D * π a - π a * D‖ := by ring

/-- **Star identity** `eq:Leibniz-Lip`: for a Hermitian Dirac matrix,
`L_D(a^*) = L_D(a)`. -/
theorem lipD_star (D : Matrix H H ℂ) (hD : Dᴴ = D) (π : A →⋆ₐ[ℂ] Matrix H H ℂ) (a : A) :
    lipD D π (star a) = lipD D π a := by
  unfold lipD
  rw [map_star, Matrix.star_eq_conjTranspose]
  have h : D * (π a)ᴴ - (π a)ᴴ * D = -(D * π a - π a * D)ᴴ := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hD]
    abel
  rw [h, norm_neg, Matrix.l2_opNorm_conjTranspose]

end Commutator

/-! ## Finite-dimensional Lip-norm theory -/

section LipNorm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- A seminorm `L` on `V` whose kernel contains the unit `u`, and a normalized
linear functional `τ` (the trace) with `τ u = 1`. -/
structure LipData (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  L : V → ℝ
  continuous : Continuous L
  nonneg : ∀ v, 0 ≤ L v
  homog : ∀ (c : ℝ) v, L (c • v) = |c| * L v
  subadd : ∀ v w, L (v + w) ≤ L v + L w
  u : V
  L_u : L u = 0
  τ : V →ₗ[ℝ] ℝ
  τ_u : τ u = 1

/-- The kernel condition `Ker ∂ = ℂ 1` on the self-adjoint part. -/
def LipData.KernelConstants (P : LipData V) : Prop :=
  ∀ v, P.L v = 0 → ∃ c : ℝ, v = c • P.u

/-- A state: a contractive linear functional normalized at the unit. -/
def LipData.IsState (P : LipData V) (φ : V →L[ℝ] ℝ) : Prop :=
  φ P.u = 1 ∧ ‖φ‖ ≤ 1

/-- The set of values `|φ(a) - ψ(a)|`, `L(a) ≤ 1`, of `eq:finite-state-metric`. -/
def LipData.mkValues (P : LipData V) (φ ψ : V →L[ℝ] ℝ) : Set ℝ :=
  {d | ∃ v, P.L v ≤ 1 ∧ d = |φ v - ψ v|}

/-- The Monge–Kantorovich distance `mk_L(φ, ψ)` of `eq:finite-state-metric`. -/
noncomputable def LipData.mkDist (P : LipData V) (φ ψ : V →L[ℝ] ℝ) : ℝ :=
  sSup (P.mkValues φ ψ)

variable (P : LipData V)

omit [FiniteDimensional ℝ V] in
/-- Adding multiples of the unit does not change `L`. -/
theorem LipData.L_sub_smul_u (v : V) (c : ℝ) : P.L (v - c • P.u) = P.L v := by
  apply le_antisymm
  · calc P.L (v - c • P.u) = P.L (v + (-c) • P.u) := by rw [neg_smul, sub_eq_add_neg]
      _ ≤ P.L v + P.L ((-c) • P.u) := P.subadd _ _
      _ = P.L v := by rw [P.homog, P.L_u, mul_zero, add_zero]
  · calc P.L v = P.L ((v - c • P.u) + c • P.u) := by rw [sub_add_cancel]
      _ ≤ P.L (v - c • P.u) + P.L (c • P.u) := P.subadd _ _
      _ = P.L (v - c • P.u) := by rw [P.homog, P.L_u, mul_zero, add_zero]

omit [FiniteDimensional ℝ V] in
theorem LipData.τ_sub_smul_u (v : V) : P.τ (v - P.τ v • P.u) = 0 := by
  rw [map_sub, map_smul, P.τ_u, smul_eq_mul, mul_one, sub_self]

/-- The traceless unit sphere. -/
def LipData.tracelessSphere : Set V := {v | P.τ v = 0 ∧ ‖v‖ = 1}

theorem LipData.isCompact_tracelessSphere : IsCompact P.tracelessSphere := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact (isClosed_eq P.τ.continuous_of_finiteDimensional continuous_const).inter
      (isClosed_eq continuous_norm continuous_const)
  · refine (Metric.isBounded_closedBall (x := (0 : V)) (r := 1)).subset ?_
    intro v hv
    rw [Metric.mem_closedBall, dist_zero_right, hv.2]

/-- **Poincaré–Lip inequality** `eq:finite-Poincare-Lip`: when the kernel of `L`
is the line through the unit, `‖a - τ(a) 1‖ ≤ C L(a)` for a constant `C`. -/
theorem exists_poincare_lip (hker : P.KernelConstants) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v, ‖v - P.τ v • P.u‖ ≤ C * P.L v := by
  classical
  have hcompact := P.isCompact_tracelessSphere
  by_cases hne : P.tracelessSphere.Nonempty
  · obtain ⟨v₀, hv₀, hmin⟩ := hcompact.exists_isMinOn hne P.continuous.continuousOn
    have hm : 0 < P.L v₀ := by
      rcases (P.nonneg v₀).lt_or_eq with h | h
      · exact h
      · exfalso
        obtain ⟨c, hc⟩ := hker v₀ h.symm
        have hτ : P.τ v₀ = c := by rw [hc, map_smul, P.τ_u, smul_eq_mul, mul_one]
        rw [hv₀.1] at hτ
        have : v₀ = 0 := by rw [hc, ← hτ, zero_smul]
        have h1 := hv₀.2
        rw [this, norm_zero] at h1
        exact zero_ne_one h1
    refine ⟨(P.L v₀)⁻¹, inv_nonneg.mpr hm.le, fun v => ?_⟩
    set w := v - P.τ v • P.u with hw
    have hτw : P.τ w = 0 := P.τ_sub_smul_u v
    have hLw : P.L w = P.L v := P.L_sub_smul_u v _
    by_cases hw0 : w = 0
    · rw [hw0, norm_zero]
      exact mul_nonneg (inv_nonneg.mpr hm.le) (P.nonneg v)
    · have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      have hmem : ‖w‖⁻¹ • w ∈ P.tracelessSphere := by
        refine ⟨by rw [map_smul, hτw, smul_zero], ?_⟩
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnorm.ne']
      have hle : P.L v₀ ≤ P.L (‖w‖⁻¹ • w) := hmin hmem
      rw [P.homog, abs_of_pos (inv_pos.mpr hnorm), hLw] at hle
      -- `L v₀ ≤ ‖w‖⁻¹ * L v`, hence `‖w‖ ≤ L v / L v₀`
      rw [← div_eq_inv_mul, le_div_iff₀ hnorm] at hle
      rw [inv_mul_eq_div, le_div_iff₀ hm, mul_comm]
      exact hle
  · refine ⟨0, le_rfl, fun v => ?_⟩
    set w := v - P.τ v • P.u with hw
    have hτw : P.τ w = 0 := P.τ_sub_smul_u v
    have hw0 : w = 0 := by
      by_contra h
      have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr h
      apply hne
      refine ⟨‖w‖⁻¹ • w, by rw [map_smul, hτw, smul_zero], ?_⟩
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnorm.ne']
    rw [hw0, norm_zero, zero_mul]

/-- `L` is dominated by the norm: `L v ≤ K ‖v‖`. -/
theorem exists_L_le_norm : ∃ K : ℝ, 0 ≤ K ∧ ∀ v, P.L v ≤ K * ‖v‖ := by
  classical
  have hcompact : IsCompact (Metric.sphere (0 : V) 1) := isCompact_sphere 0 1
  by_cases hne : (Metric.sphere (0 : V) 1).Nonempty
  · obtain ⟨v₀, hv₀, hmax⟩ := hcompact.exists_isMaxOn hne P.continuous.continuousOn
    refine ⟨P.L v₀, P.nonneg v₀, fun v => ?_⟩
    by_cases hv : v = 0
    · rw [hv, norm_zero, mul_zero]
      have := P.homog 0 0
      rw [zero_smul, abs_zero, zero_mul] at this
      exact this.le
    · have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have hmem : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : V) 1 := by
        rw [mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ hnorm.ne']
      have hle : P.L (‖v‖⁻¹ • v) ≤ P.L v₀ := hmax hmem
      rw [P.homog, abs_of_pos (inv_pos.mpr hnorm)] at hle
      rw [← div_eq_inv_mul, div_le_iff₀ hnorm] at hle
      linarith
  · refine ⟨0, le_rfl, fun v => ?_⟩
    have hv : v = 0 := by
      by_contra h
      have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr h
      apply hne
      refine ⟨‖v‖⁻¹ • v, ?_⟩
      rw [mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ hnorm.ne']
    rw [hv, norm_zero, mul_zero]
    have := P.homog 0 0
    rw [zero_smul, abs_zero, zero_mul] at this
    exact this.le

omit [FiniteDimensional ℝ V] in
/-- Differences of states vanish on the unit, so they only see the traceless
part. -/
theorem LipData.sub_apply_eq {φ ψ : V →L[ℝ] ℝ} (hφ : P.IsState φ) (hψ : P.IsState ψ) (v : V) :
    φ v - ψ v = (φ - ψ) (v - P.τ v • P.u) := by
  simp only [_root_.sub_apply, map_sub, map_smul, hφ.1, hψ.1, smul_eq_mul]
  ring

omit [FiniteDimensional ℝ V] in
theorem LipData.L_zero : P.L 0 = 0 := by
  have := P.homog 0 0
  rwa [zero_smul, abs_zero, zero_mul] at this

omit [FiniteDimensional ℝ V] in
/-- Every value in the supremum of `eq:finite-state-metric` is bounded by
`C ‖φ - ψ‖`. -/
theorem LipData.abs_sub_le_of_L_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ v, ‖v - P.τ v • P.u‖ ≤ C * P.L v)
    {φ ψ : V →L[ℝ] ℝ} (hφ : P.IsState φ) (hψ : P.IsState ψ) {v : V} (hv : P.L v ≤ 1) :
    |φ v - ψ v| ≤ C * ‖φ - ψ‖ := by
  rw [P.sub_apply_eq hφ hψ]
  calc |(φ - ψ) (v - P.τ v • P.u)| = ‖(φ - ψ) (v - P.τ v • P.u)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖φ - ψ‖ * ‖v - P.τ v • P.u‖ := (φ - ψ).le_opNorm _
    _ ≤ ‖φ - ψ‖ * (C * P.L v) := mul_le_mul_of_nonneg_left (hC v) (norm_nonneg _)
    _ ≤ ‖φ - ψ‖ * (C * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv hC0) (norm_nonneg _)
    _ = C * ‖φ - ψ‖ := by ring

omit [FiniteDimensional ℝ V] in
theorem LipData.zero_mem_mkValues (φ ψ : V →L[ℝ] ℝ) : (0 : ℝ) ∈ P.mkValues φ ψ :=
  ⟨0, by rw [P.L_zero]; exact zero_le_one, by simp⟩

theorem LipData.bddAbove_mkValues {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ v, ‖v - P.τ v • P.u‖ ≤ C * P.L v)
    {φ ψ : V →L[ℝ] ℝ} (hφ : P.IsState φ) (hψ : P.IsState ψ) :
    BddAbove (P.mkValues φ ψ) := by
  refine ⟨C * ‖φ - ψ‖, ?_⟩
  rintro d ⟨v, hv, rfl⟩
  exact P.abs_sub_le_of_L_le hC0 hC hφ hψ hv

theorem LipData.mkDist_nonneg {φ ψ : V →L[ℝ] ℝ} (hbdd : BddAbove (P.mkValues φ ψ)) :
    0 ≤ P.mkDist φ ψ :=
  le_csSup hbdd (P.zero_mem_mkValues φ ψ)

/-- **Finiteness of `mk_L`**: `mk_L(φ, ψ) ≤ C ‖φ - ψ‖`. -/
theorem LipData.mkDist_le_opNorm {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ v, ‖v - P.τ v • P.u‖ ≤ C * P.L v)
    {φ ψ : V →L[ℝ] ℝ} (hφ : P.IsState φ) (hψ : P.IsState ψ) :
    P.mkDist φ ψ ≤ C * ‖φ - ψ‖ := by
  refine csSup_le ⟨0, P.zero_mem_mkValues φ ψ⟩ ?_
  rintro d ⟨v, hv, rfl⟩
  exact P.abs_sub_le_of_L_le hC0 hC hφ hψ hv

/-- The paper's bound `mk_L ≤ 2 C_δ`. -/
theorem LipData.mkDist_le_two_mul {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ v, ‖v - P.τ v • P.u‖ ≤ C * P.L v)
    {φ ψ : V →L[ℝ] ℝ} (hφ : P.IsState φ) (hψ : P.IsState ψ) :
    P.mkDist φ ψ ≤ 2 * C := by
  have h1 := P.mkDist_le_opNorm hC0 hC hφ hψ
  have h2 : ‖φ - ψ‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith [hφ.2, hψ.2])
  calc P.mkDist φ ψ ≤ C * ‖φ - ψ‖ := h1
    _ ≤ C * 2 := mul_le_mul_of_nonneg_left h2 hC0
    _ = 2 * C := by ring

omit [FiniteDimensional ℝ V] in
/-- `|φ(a) - ψ(a)| ≤ L(a) mk_L(φ, ψ)`. -/
theorem LipData.abs_sub_le_L_mul_mkDist (hker : P.KernelConstants)
    {φ ψ : V →L[ℝ] ℝ} (hbdd : BddAbove (P.mkValues φ ψ))
    (hφ : P.IsState φ) (hψ : P.IsState ψ) (v : V) :
    |φ v - ψ v| ≤ P.L v * P.mkDist φ ψ := by
  by_cases hL : P.L v = 0
  · obtain ⟨c, rfl⟩ := hker v hL
    rw [hL, zero_mul, map_smul, map_smul, hφ.1, hψ.1, sub_self, abs_zero]
  · have hpos : 0 < P.L v := lt_of_le_of_ne (P.nonneg v) (Ne.symm hL)
    have hmem : |φ ((P.L v)⁻¹ • v) - ψ ((P.L v)⁻¹ • v)| ∈ P.mkValues φ ψ :=
      ⟨(P.L v)⁻¹ • v, by rw [P.homog, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hL], rfl⟩
    have hle := le_csSup hbdd hmem
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← mul_sub, abs_mul,
      abs_of_pos (inv_pos.mpr hpos), ← div_eq_inv_mul, div_le_iff₀ hpos] at hle
    unfold LipData.mkDist
    linarith

/-- The dual norm is dominated by `mk_L`: `‖φ - ψ‖ ≤ K mk_L(φ, ψ)`. -/
theorem LipData.opNorm_le_mkDist (hker : P.KernelConstants)
    {φ ψ : V →L[ℝ] ℝ} (hbdd : BddAbove (P.mkValues φ ψ))
    (hφ : P.IsState φ) (hψ : P.IsState ψ) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ v, P.L v ≤ K * ‖v‖) :
    ‖φ - ψ‖ ≤ K * P.mkDist φ ψ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hK0 (P.mkDist_nonneg hbdd)) ?_
  intro v
  rw [_root_.sub_apply, Real.norm_eq_abs]
  calc |φ v - ψ v| ≤ P.L v * P.mkDist φ ψ := P.abs_sub_le_L_mul_mkDist hker hbdd hφ hψ v
    _ ≤ K * ‖v‖ * P.mkDist φ ψ := mul_le_mul_of_nonneg_right (hK v) (P.mkDist_nonneg hbdd)
    _ = K * P.mkDist φ ψ * ‖v‖ := by ring

/-- **`mk_L` induces the (weak-`*` = norm) topology of the finite-dimensional
state space**: `mk_L`-convergence of states is exactly norm convergence. -/
theorem LipData.tendsto_mkDist_iff (hker : P.KernelConstants)
    {C K : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, ‖v - P.τ v • P.u‖ ≤ C * P.L v)
    (hK0 : 0 ≤ K) (hK : ∀ v, P.L v ≤ K * ‖v‖)
    {ι : Type*} {l : Filter ι} {φ : ι → (V →L[ℝ] ℝ)} {ψ : V →L[ℝ] ℝ}
    (hφ : ∀ i, P.IsState (φ i)) (hψ : P.IsState ψ) :
    Tendsto (fun i => P.mkDist (φ i) ψ) l (𝓝 0) ↔ Tendsto φ l (𝓝 ψ) := by
  constructor
  · intro h
    refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
    refine squeeze_zero (fun i => norm_nonneg _) (fun i => ?_) (by simpa using h.const_mul K)
    exact P.opNorm_le_mkDist hker (P.bddAbove_mkValues hC0 hC (hφ i) hψ) (hφ i) hψ hK0 hK
  · intro h
    have h' := tendsto_iff_norm_sub_tendsto_zero.mp h
    refine squeeze_zero (fun i => P.mkDist_nonneg (P.bddAbove_mkValues hC0 hC (hφ i) hψ))
      (fun i => P.mkDist_le_opNorm hC0 hC (hφ i) hψ) (by simpa using h'.const_mul C)

omit [FiniteDimensional ℝ V] in
/-- **Converse clause**: if some `a` with `L(a) = 0` is separated by two
states, the supremum in `eq:finite-state-metric` is unbounded. -/
theorem LipData.not_bddAbove_of_kernel {v : V} (hv : P.L v = 0)
    {φ ψ : V →L[ℝ] ℝ} (hsep : φ v ≠ ψ v) :
    ¬ BddAbove (P.mkValues φ ψ) := by
  rintro ⟨b, hb⟩
  have hd : 0 < |φ v - ψ v| := abs_pos.mpr (sub_ne_zero.mpr hsep)
  set t : ℝ := (|b| + 1) / |φ v - ψ v| with ht
  have htpos : 0 < t := div_pos (by positivity) hd
  have hmem : |φ (t • v) - ψ (t • v)| ∈ P.mkValues φ ψ :=
    ⟨t • v, by rw [P.homog, hv, mul_zero]; exact zero_le_one, rfl⟩
  have hle := hb hmem
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← mul_sub, abs_mul, abs_of_pos htpos,
    ht, div_mul_cancel₀ _ hd.ne'] at hle
  linarith [le_abs_self b]

/-- **Proposition `prop:finite-CQMS`** (finite-dimensional Lip-norm clauses).
When the kernel of the seminorm `L` on the self-adjoint part is the line
through the unit, there are constants `C, K ≥ 0` with the Poincaré–Lip
inequality `‖a - τ(a) 1‖ ≤ C L(a)`, and for all states `φ, ψ` the
Monge–Kantorovich distance of `eq:finite-state-metric` is a well-defined
finite supremum, bounded by `C ‖φ - ψ‖ ≤ 2 C`, dominating `|φ(a) - ψ(a)| / L(a)`,
and bi-Lipschitz equivalent to the dual norm distance. -/
theorem finite_compact_quantum_metric (hker : P.KernelConstants) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧
      (∀ v, ‖v - P.τ v • P.u‖ ≤ C * P.L v) ∧
      (∀ v, P.L v ≤ K * ‖v‖) ∧
      ∀ φ ψ : V →L[ℝ] ℝ, P.IsState φ → P.IsState ψ →
        BddAbove (P.mkValues φ ψ) ∧
        0 ≤ P.mkDist φ ψ ∧
        P.mkDist φ ψ ≤ C * ‖φ - ψ‖ ∧
        P.mkDist φ ψ ≤ 2 * C ∧
        (∀ v, |φ v - ψ v| ≤ P.L v * P.mkDist φ ψ) ∧
        ‖φ - ψ‖ ≤ K * P.mkDist φ ψ := by
  obtain ⟨C, hC0, hC⟩ := exists_poincare_lip P hker
  obtain ⟨K, hK0, hK⟩ := exists_L_le_norm P
  refine ⟨C, K, hC0, hK0, hC, hK, fun φ ψ hφ hψ => ?_⟩
  have hbdd := P.bddAbove_mkValues hC0 hC hφ hψ
  exact ⟨hbdd, P.mkDist_nonneg hbdd, P.mkDist_le_opNorm hC0 hC hφ hψ,
    P.mkDist_le_two_mul hC0 hC hφ hψ, P.abs_sub_le_L_mul_mkDist hker hbdd hφ hψ,
    P.opNorm_le_mkDist hker hbdd hφ hψ hK0 hK⟩

end LipNorm

end FiniteCompactQuantumMetric
end RenewalGeometry
