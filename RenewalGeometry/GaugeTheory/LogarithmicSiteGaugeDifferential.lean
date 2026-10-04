/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Algebra.MatrixExpDerivative
import RenewalGeometry.DiscreteAnalysis.GridSobolevInequality

/-!
# The exact logarithmic site-gauge differential
  (`lem:native-log-gauge-differential`, eqs. `eq:native-gauge-differential`,
  `eq:native-gauge-energy-differential`; Einstein–SM action closure)

Setting.  The periodic grid `(ℤ/n)^ι` (unit steps `gridStep`, mesh `h ≠ 0`); the gauge group sits
in the units of a complete normed `ℝ`-algebra `𝔸` (for `SU(3) × SU(2)`: pairs of complex
matrices), the Lie-algebra fields `A_μ(x)`, `ξ_x` take values in `𝔸`, and `ad_A u = Au - uA`
(`MatrixExpDerivative.adOp`).  A logarithm chart is any map `Log : 𝔸 → 𝔸` that inverts `exp`
near each scaled link coordinate, `Log (e^Y) = Y` for `Y` near `h A_μ(x)` (a fixed
conjugation-invariant chart containing all `h A_μ(x)` is a special case; conjugation invariance is
not needed for the differential).

For the site gauge `q_x(t) = e^{tξ_x}` the logarithmic link coordinates are
`A^{q(t)}_μ(x) = h⁻¹ Log(q_x(t) e^{hA_μ(x)} q_{x+e_μ}(t)⁻¹)` (`gaugeCurve`).  With
`Z_μ = h ad_{A_μ}`, `m_μ ξ = ½(ξ + T_{μ,1} ξ)`, `D^+_μ ξ = h⁻¹(T_{μ,1}ξ - ξ)` and
`𝒦(Z) = (Z/2)coth(Z/2) = ½ 𝒥(Z)⁻¹(I + e^Z)` (`OperatorHalfCoth.halfCoth`):

* `gauge_differential` (**`eq:native-gauge-differential`**): if `𝒥(Z_μ(x))` is invertible
  (e.g. `‖h A_μ(x)‖ ≤ 1/8`), then `A^{q(0)} = A` and
  `d/dt A^{q(t)}_μ(x)|_{t=0} = -𝒦(Z_μ) D^+_μ ξ(x) - [A_μ(x), m_μ ξ(x)]`;
* `gauge_energy_differential` (**`eq:native-gauge-energy-differential`**): for a symmetric
  continuous bilinear form `⟨·,·⟩` on `𝔸` with `⟨A_μ(x), [A_μ(x), u]⟩ = 0` (true for every
  ad-invariant symmetric form, e.g. `Re tr(X^* Y)` on anti-Hermitian `A`),
  `d/dt ½‖A^{q(t)}‖²_{2,h}|_{t=0} = -⟨δ_h A, ξ⟩_{2,h}` with
  `‖a‖²_{2,h} = h^d Σ_{μ,x} ⟨a_μ(x), a_μ(x)⟩` and `δ_h A = -Σ_μ D^-_μ A_μ`
  (`eq:native-discrete-divergence`).

* `homotopy_derivative` (the exact chain rule used in `thm:finite-Coulomb-normalization`): along
  `A_s = h⁻¹ Log(q_x(s) e^{shB} q_{x+μ}(s)⁻¹)` with `q̇ = ξ q`,
  `Ȧ = 𝒥(h ad_A)⁻¹ Ad_{q_x} B - (𝒦(h ad_A) D^+ξ + [A, m ξ])`.

The proof is the paper's: the left-trivialized differential of `exp` is `𝒥(ad)`
(`MatrixExpDerivative.fderiv_exp_eq`), the derivative of the chart is its inverse
(`hasDerivAt_log_gauge_curve`), and `𝒥(Z)⁻¹(I - e^Z) = -Z`,
`½ 𝒥(Z)⁻¹ (I + e^Z) = 𝒦(Z)`; for the energy, `⟨A, 𝒦(Z) v⟩ = ⟨A, v⟩` because `⟨A, Z u⟩ = 0`.
-/

open NormedSpace Filter Topology Finset

namespace RenewalGeometry.LogGaugeDifferential

open MatrixExpDerivative OperatorHalfCoth GridSobolev

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [Nontrivial 𝔸]

/-- The logarithmic link coordinates of the gauge-transformed field along `q_x(t) = e^{tξ_x}`:
`A^{q(t)}_μ(x) = h⁻¹ Log(e^{tξ_x} e^{hA_μ(x)} e^{-tξ_{x+e_μ}})`. -/
def gaugeCurve (Log : 𝔸 → 𝔸) (h : ℝ) (A : ι → (ι → ZMod n) → 𝔸) (ξ : (ι → ZMod n) → 𝔸)
    (t : ℝ) (μ : ι) (x : ι → ZMod n) : 𝔸 :=
  h⁻¹ • Log (exp (t • ξ x) * exp (h • A μ x) * exp (-(t • ξ (x + gridStep μ))))

/-- The midpoint average `m_μ ξ = ½(ξ + T_{μ,1} ξ)`. -/
def midAvgA (μ : ι) (ξ : (ι → ZMod n) → 𝔸) (x : ι → ZMod n) : 𝔸 :=
  (1 / 2 : ℝ) • (ξ x + ξ (x + gridStep μ))

/-- The logarithmic gauge flux `𝒦(h ad_{A_μ}) D^+_μ ξ + [A_μ, m_μ ξ]`. -/
def gaugeFlux (h : ℝ) (A : ι → (ι → ZMod n) → 𝔸) (ξ : (ι → ZMod n) → 𝔸) (μ : ι)
    (x : ι → ZMod n) : 𝔸 :=
  halfCoth (h • adOp (A μ x)) (gridFwd h μ ξ x) + adOp (A μ x) (midAvgA μ ξ x)

/-- The discrete divergence `δ_h A = -Σ_μ D^-_μ A_μ`, `D^-_μ = h⁻¹(I - T_{μ,-1})`. -/
def codiffA (h : ℝ) (A : ι → (ι → ZMod n) → 𝔸) (x : ι → ZMod n) : 𝔸 :=
  -∑ μ, h⁻¹ • (A μ x - A μ (x - gridStep μ))

/-- The algebraic core of `eq:native-gauge-differential`:
`h⁻¹ 𝒥(Z)⁻¹ (a - e^Z b) = -(𝒦(Z) (h⁻¹(b - a)) + [A, ½(a + b)])` for `Z = h ad_A`. -/
theorem inverse_dexpJ_gauge_identity (h : ℝ) (hh : h ≠ 0) (A a b : 𝔸)
    (hJ : IsUnit (dexpJ (h • adOp A))) :
    h⁻¹ • Ring.inverse (dexpJ (h • adOp A)) (a - exp (h • adOp A) b) =
      -(halfCoth (h • adOp A) (h⁻¹ • (b - a)) + adOp A ((1 / 2 : ℝ) • (a + b))) := by
  set Z := h • adOp A with hZ
  set J := dexpJ Z
  set Ji := Ring.inverse J
  set E := exp Z
  have hEZ : ∀ w, Ji (E w - w) = Z w := by
    intro w
    have h1 : E - 1 = J * Z := (dexpJ_mul Z).symm
    have h2 : E w - w = J (Z w) := by
      have := congrArg (fun T : 𝔸 →L[ℝ] 𝔸 => T w) h1
      simpa using this
    rw [h2, ← ContinuousLinearMap.mul_apply, Ring.inverse_mul_cancel _ hJ]
    rfl
  have hK : ∀ v, halfCoth Z v = Ji ((1 / 2 : ℝ) • (v + E v)) := by
    intro v
    simp only [halfCoth, ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply]
    rfl
  set m : 𝔸 := (1 / 2 : ℝ) • (a + b)
  have hsplit : a - E b = -(E m - m) - (1 / 2 : ℝ) • ((b - a) + E (b - a)) := by
    simp only [m, map_smul, map_add, map_sub]
    module
  rw [hsplit, map_sub, map_neg, hEZ, ← hK, hZ, ContinuousLinearMap.smul_apply, map_smul]
  rw [smul_sub, smul_neg, smul_smul, inv_mul_cancel₀ hh, one_smul, map_smul]
  abel

/-- **`lem:native-log-gauge-differential`, eq. `eq:native-gauge-differential`.**  If the chart
inverts `exp` near every `h A_μ(x)` and every `𝒥(h ad_{A_μ(x)})` is invertible, then the gauge
curve starts at `A` and
`d/dt A^{q(t)}_μ(x)|_{t=0} = -𝒦(h ad_{A_μ}) D^+_μ ξ(x) - [A_μ(x), m_μ ξ(x)]`. -/
theorem gauge_differential (Log : 𝔸 → 𝔸) {h : ℝ} (hh : h ≠ 0) (A : ι → (ι → ZMod n) → 𝔸)
    (ξ : (ι → ZMod n) → 𝔸) (hLog : ∀ μ x, ∀ᶠ Y in 𝓝 (h • A μ x), Log (exp Y) = Y)
    (hJ : ∀ μ x, IsUnit (dexpJ (h • adOp (A μ x)))) :
    (∀ μ x, gaugeCurve Log h A ξ 0 μ x = A μ x) ∧
      ∀ μ x, HasDerivAt (fun t => gaugeCurve Log h A ξ t μ x) (-gaugeFlux h A ξ μ x) 0 := by
  refine ⟨fun μ x => ?_, fun μ x => ?_⟩
  · simp only [gaugeCurve, zero_smul, exp_zero, one_mul, neg_zero, mul_one]
    rw [(hLog μ x).self_of_nhds, smul_smul, inv_mul_cancel₀ hh, one_smul]
  · have hJ' : IsUnit (dexpJ (adOp (h • A μ x))) := by rw [adOp_smul]; exact hJ μ x
    have hd := (hasDerivAt_log_gauge_curve (h • A μ x) (ξ x) (ξ (x + gridStep μ)) hJ'
      (hLog μ x)).const_smul h⁻¹
    refine hd.congr_deriv ?_
    rw [adOp_smul, inverse_dexpJ_gauge_identity h hh (A μ x) _ _ (hJ μ x)]
    rfl

/-! ### The energy differential -/


/-! ### The exact chain rule along the Coulomb homotopy (`thm:finite-Coulomb-normalization`) -/

/-- The logarithmic links of the auxiliary homotopy `U^s = e^{s h B}` gauged by a time-dependent
site gauge `q(s)`: `A_s = h⁻¹ Log(q_x(s) e^{shB_μ(x)} q_{x+μ}(s)⁻¹)`
(`eq:native-Coulomb-homotopy-ODE`). -/
def homotopyCurve (Log : 𝔸 → 𝔸) (h : ℝ) (B : ι → (ι → ZMod n) → 𝔸)
    (q : ℝ → (ι → ZMod n) → 𝔸) (s : ℝ) (μ : ι) (x : ι → ZMod n) : 𝔸 :=
  h⁻¹ • Log (q s x * exp (s • (h • B μ x)) * Ring.inverse (q s (x + gridStep μ)))

/-- **The exact chain rule of the Coulomb homotopy**: if `q̇_x = ξ_x q_x` at `s₀` (with `q_x(s₀)`
invertible), the chart inverts `exp` near `h A_μ(x)` where
`q_x e^{s₀hB} q_{x+μ}⁻¹ = e^{hA_μ(x)}`, and `𝒥(h ad_{A_μ(x)})` is invertible, then
`d/ds A_s = 𝒥(h ad_A)⁻¹ Ad_{q_x} B - (𝒦(h ad_A) D^+ξ + [A, m ξ])`, i.e. `Ȧ = R - (flux)` with
`R = 𝒥(h ad_A)⁻¹ Ad_{q_x} B`, as used in the proof of `thm:finite-Coulomb-normalization`. -/
theorem homotopy_derivative (Log : 𝔸 → 𝔸) {h : ℝ} (hh : h ≠ 0) (B : ι → (ι → ZMod n) → 𝔸)
    (q : ℝ → (ι → ZMod n) → 𝔸) (ξ : (ι → ZMod n) → 𝔸) (s₀ : ℝ) (A : ι → (ι → ZMod n) → 𝔸)
    (μ : ι) (x : ι → ZMod n) (hq : ∀ y, HasDerivAt (fun s => q s y) (ξ y * q s₀ y) s₀)
    (hu : ∀ y, IsUnit (q s₀ y))
    (hA : q s₀ x * exp (s₀ • (h • B μ x)) * Ring.inverse (q s₀ (x + gridStep μ)) =
      exp (h • A μ x))
    (hLog : ∀ᶠ Y in 𝓝 (h • A μ x), Log (exp Y) = Y) (hJ : IsUnit (dexpJ (h • adOp (A μ x)))) :
    HasDerivAt (fun s => homotopyCurve Log h B q s μ x)
      (Ring.inverse (dexpJ (h • adOp (A μ x))) (q s₀ x * B μ x * Ring.inverse (q s₀ x)) -
        gaugeFlux h A ξ μ x) s₀ := by
  set y := x + gridStep μ
  set E := exp (s₀ • (h • B μ x))
  set Qi := Ring.inverse (q s₀ y)
  set Qx := Ring.inverse (q s₀ x)
  have hQ : q s₀ y * Qi = 1 := Ring.mul_inverse_cancel _ (hu y)
  have hQx' : Qx * q s₀ x = 1 := Ring.inverse_mul_cancel _ (hu x)
  -- derivative of the inverse
  have hinv : HasDerivAt (fun s => Ring.inverse (q s y)) (-(Qi * ξ y)) s₀ := by
    have h1 := (hasFDerivAt_ringInverse (𝕜 := ℝ) (hu y).unit).comp_hasDerivAt_of_eq s₀ (hq y)
      (hu y).unit_spec
    refine h1.congr_deriv ?_
    simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.mulLeftRight_apply]
    rw [← Ring.inverse_unit, (hu y).unit_spec, mul_assoc, mul_assoc, hQ, mul_one]
  have hE := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (h • B μ x) s₀
  have hγ := ((hq x).mul hE).mul hinv
  have hJ' : IsUnit (dexpJ (adOp (h • A μ x))) := by rw [adOp_smul]; exact hJ
  have hd := (hasDerivAt_log_comp (h • A μ x) hJ' hLog hγ hA).const_smul h⁻¹
  refine hd.congr_deriv ?_
  -- algebra: `γ' e^{-hA} = h q B q⁻¹ + (ξ_x - e^{Z} ξ_{x+μ})`
  have hm := exp_mul_exp_neg (h • A μ x)
  have hγ0 : q s₀ x * E * Qi = exp (h • A μ x) := hA
  have hEQ : E * Qi * exp (-(h • A μ x)) = Qx := by
    have h2 : q s₀ x * (E * Qi * exp (-(h • A μ x))) = 1 := by
      rw [← mul_assoc, ← mul_assoc, hγ0, hm]
    calc E * Qi * exp (-(h • A μ x)) = Qx * (q s₀ x * (E * Qi * exp (-(h • A μ x)))) := by
          rw [← mul_assoc, hQx', one_mul]
      _ = Qx := by rw [h2, mul_one]
  have hconj := exp_smul_adOp_apply (h • A μ x) (ξ y) 1
  rw [one_smul, one_smul] at hconj
  have key : (ξ x * q s₀ x * E + q s₀ x * (h • B μ x * E)) * Qi +
      q s₀ x * E * -(Qi * ξ y) = ξ x * exp (h • A μ x) + h • (q s₀ x * B μ x * (E * Qi)) -
        exp (h • A μ x) * ξ y := by
    rw [← hγ0]
    simp only [add_mul, mul_add, mul_neg, smul_mul_assoc, mul_smul_comm, mul_assoc]
    abel
  have key2 : ((ξ x * q s₀ x * E + q s₀ x * (h • B μ x * E)) * Qi +
      q s₀ x * E * -(Qi * ξ y)) * exp (-(h • A μ x)) =
        h • (q s₀ x * B μ x * Qx) + (ξ x - exp (adOp (h • A μ x)) (ξ y)) := by
    rw [key, hconj, sub_mul, add_mul, mul_assoc (ξ x), hm, mul_one, smul_mul_assoc,
      mul_assoc (q s₀ x * B μ x), hEQ, mul_assoc (exp (h • A μ x))]
    abel
  show h⁻¹ • Ring.inverse (dexpJ (adOp (h • A μ x)))
    (((ξ x * q s₀ x * E + q s₀ x * (h • B μ x * E)) * Qi + q s₀ x * E * -(Qi * ξ y)) *
      exp (-(h • A μ x))) = _
  rw [key2, adOp_smul, map_add, smul_add, map_smul, smul_smul, inv_mul_cancel₀ hh, one_smul,
    inverse_dexpJ_gauge_identity h hh (A μ x) (ξ x) (ξ y) hJ]
  simp only [gaugeFlux, midAvgA, gridFwd]
  abel

section Energy

variable (B : 𝔸 →L[ℝ] 𝔸 →L[ℝ] ℝ)

/-- If `⟨a, Z u⟩ = 0` for all `u`, then `⟨a, 𝒥(Z) w⟩ = ⟨a, w⟩` and `⟨a, e^Z w⟩ = ⟨a, w⟩`. -/
theorem pairing_series_eq (a : 𝔸) (Z : 𝔸 →L[ℝ] 𝔸) (hZ : ∀ u, B a (Z u) = 0) (w : 𝔸) :
    B a (dexpJ Z w) = B a w ∧ B a (exp Z w) = B a w := by
  set L : (𝔸 →L[ℝ] 𝔸) →L[ℝ] ℝ := (B a).comp (ContinuousLinearMap.apply ℝ 𝔸 w) with hL
  have hL' : ∀ T : 𝔸 →L[ℝ] 𝔸, L T = B a (T w) := fun T => rfl
  have hpow : ∀ k : ℕ, k ≠ 0 → B a ((Z ^ k) w) = 0 := by
    intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    rw [pow_succ', ContinuousLinearMap.mul_apply, hZ]
  have hz : ∀ (c : ℕ → ℝ) (k : ℕ), k ≠ 0 → L (c k • Z ^ k) = 0 := by
    intro c k hk
    rw [hL', ContinuousLinearMap.smul_apply, map_smul, hpow k hk, smul_zero]
  have h0 : ∀ c : ℝ, L (c • Z ^ 0) = c * B a w := by
    intro c
    rw [hL', pow_zero, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, map_smul,
      smul_eq_mul]
  constructor
  · have h1 := (hasSum_dexpJ Z).mapL L
    have h2 : HasSum (fun k => L (jCoeff k • Z ^ k)) (B a w) := by
      have := hasSum_single (f := fun k => L (jCoeff k • Z ^ k)) 0 (fun k hk => hz jCoeff k hk)
      rwa [h0, jCoeff_zero, one_mul] at this
    rw [← hL']
    exact h1.unique h2
  · have h1 := (exp_series_hasSum_exp' (𝕂 := ℝ) Z).mapL L
    have h2 : HasSum (fun k => L (((Nat.factorial k : ℝ)⁻¹) • Z ^ k)) (B a w) := by
      have := hasSum_single (f := fun k => L (((Nat.factorial k : ℝ)⁻¹) • Z ^ k)) 0
        (fun k hk => hz (fun k => ((Nat.factorial k : ℝ)⁻¹)) k hk)
      rwa [h0, Nat.factorial_zero, Nat.cast_one, inv_one, one_mul] at this
    rw [← hL']
    exact h1.unique h2

/-- **`⟨A, 𝒦(h ad_A) v⟩ = ⟨A, v⟩`** when `⟨A, [A, u]⟩ = 0` for all `u` (the paper's
`𝒦(h ad_A)^* A = A`). -/
theorem pairing_halfCoth (h : ℝ) (a : 𝔸) (hB : ∀ u, B a (a * u - u * a) = 0)
    (hJ : IsUnit (dexpJ (h • adOp a))) (v : 𝔸) :
    B a (halfCoth (h • adOp a) v) = B a v := by
  set Z := h • adOp a
  have hZ : ∀ u, B a (Z u) = 0 := by
    intro u
    simp only [Z, ContinuousLinearMap.smul_apply, adOp_apply, map_smul, hB, smul_zero]
  set u := halfCoth Z v
  have hu : dexpJ Z u = (1 / 2 : ℝ) • (v + exp Z v) := by
    simp only [u, halfCoth, ← ContinuousLinearMap.mul_apply, ← mul_assoc,
      Ring.mul_inverse_cancel _ hJ, one_mul, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply]
  have h1 := (pairing_series_eq B a Z hZ u).1
  have h2 := (pairing_series_eq B a Z hZ v).2
  rw [← h1, hu, map_smul, map_add, h2, smul_eq_mul]
  ring

variable [NeZero n]

/-- The gauge energy `½ ‖A^{q(t)}‖²_{2,h} = ½ h^d Σ_{μ,x} ⟨A^{q(t)}_μ(x), A^{q(t)}_μ(x)⟩`. -/
def gaugeEnergy (Log : 𝔸 → 𝔸) (h : ℝ) (A : ι → (ι → ZMod n) → 𝔸) (ξ : (ι → ZMod n) → 𝔸)
    (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (h ^ Fintype.card ι *
    ∑ μ, ∑ x, B (gaugeCurve Log h A ξ t μ x) (gaugeCurve Log h A ξ t μ x))

/-- Summation by parts: `Σ_{μ,x} ⟨A_μ(x), D^+_μ ξ(x)⟩ = Σ_x ⟨δ_h A(x), ξ(x)⟩`. -/
theorem sum_pairing_fwd (h : ℝ) (A : ι → (ι → ZMod n) → 𝔸)
    (ξ : (ι → ZMod n) → 𝔸) :
    ∑ μ, ∑ x, B (A μ x) (gridFwd h μ ξ x) = ∑ x, B (codiffA h A x) (ξ x) := by
  have hsh : ∀ μ, ∑ x, B (A μ x) (ξ (x + gridStep μ)) = ∑ x, B (A μ (x - gridStep μ)) (ξ x) := by
    intro μ
    exact Fintype.sum_equiv (Equiv.addRight (gridStep μ)) _ _ (fun x => by simp)
  have hL : ∀ μ, ∑ x, B (A μ x) (gridFwd h μ ξ x) =
      h⁻¹ * (∑ x, B (A μ (x - gridStep μ)) (ξ x) - ∑ x, B (A μ x) (ξ x)) := by
    intro μ
    simp only [gridFwd, map_smul, map_sub, smul_eq_mul, ← Finset.mul_sum, Finset.sum_sub_distrib,
      hsh μ]
  have hR : ∀ x, B (codiffA h A x) (ξ x) =
      ∑ μ, -(h⁻¹ * (B (A μ x) (ξ x) - B (A μ (x - gridStep μ)) (ξ x))) := by
    intro x
    simp only [codiffA, map_neg, map_sum, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.coe_sum', Finset.sum_apply, map_smul, ContinuousLinearMap.smul_apply,
      map_sub, ContinuousLinearMap.sub_apply, smul_eq_mul, Finset.sum_neg_distrib]
  simp only [hL, hR]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  ring

/-- **`lem:native-log-gauge-differential`, eq. `eq:native-gauge-energy-differential`.**  For a
symmetric continuous bilinear form with `⟨A_μ(x), [A_μ(x), u]⟩ = 0` (ad-invariance),
`d/dt ½‖A^{q(t)}‖²_{2,h}|_{t=0} = -⟨δ_h A, ξ⟩_{2,h}`. -/
theorem gauge_energy_differential (Log : 𝔸 → 𝔸) {h : ℝ} (hh : h ≠ 0)
    (A : ι → (ι → ZMod n) → 𝔸) (ξ : (ι → ZMod n) → 𝔸)
    (hLog : ∀ μ x, ∀ᶠ Y in 𝓝 (h • A μ x), Log (exp Y) = Y)
    (hJ : ∀ μ x, IsUnit (dexpJ (h • adOp (A μ x))))
    (hsymm : ∀ u v, B u v = B v u) (hB : ∀ μ x u, B (A μ x) (A μ x * u - u * A μ x) = 0) :
    HasDerivAt (gaugeEnergy B Log h A ξ)
      (-(h ^ Fintype.card ι * ∑ x, B (codiffA h A x) (ξ x))) 0 := by
  obtain ⟨h0, hd⟩ := gauge_differential Log hh A ξ hLog hJ
  have hterm : ∀ μ x, HasDerivAt (fun t => B (gaugeCurve Log h A ξ t μ x)
      (gaugeCurve Log h A ξ t μ x)) (-(2 * B (A μ x) (gridFwd h μ ξ x))) 0 := by
    intro μ x
    have hc : HasDerivAt (fun t => B (gaugeCurve Log h A ξ t μ x)) (B (-gaugeFlux h A ξ μ x)) 0 :=
      B.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hd μ x)
    refine (hc.clm_apply (hd μ x)).congr_deriv ?_
    rw [h0 μ x, hsymm (-gaugeFlux h A ξ μ x) (A μ x), map_neg, gaugeFlux, map_add,
      pairing_halfCoth B h (A μ x) (hB μ x) (hJ μ x), adOp_apply]
    simp only [midAvgA, hB μ x, add_zero]
    ring
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun μ _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun x _ => hterm μ x
  have := (hsum.const_mul (h ^ Fintype.card ι)).const_mul (1 / 2 : ℝ)
  refine this.congr_deriv ?_
  rw [← sum_pairing_fwd B h A ξ]
  simp only [Finset.sum_neg_distrib, ← Finset.mul_sum]
  ring

end Energy

/-- Non-vacuity: at any field `A` with `‖h A_μ(x)‖ ≤ 1/8` (in particular `A = 0`) all `𝒥`'s are
invertible, and a single local logarithm chart near each `h A_μ(x)` exists. -/
theorem gauge_hypotheses_nonvacuous {h : ℝ} (A : ι → (ι → ZMod n) → 𝔸)
    (hA : ∀ μ x, ‖h • A μ x‖ ≤ 1 / 8) (μ : ι) (x : ι → ZMod n) :
    IsUnit (dexpJ (h • adOp (A μ x))) ∧ ∃ Log : 𝔸 → 𝔸, ∀ᶠ Y in 𝓝 (h • A μ x), Log (exp Y) = Y := by
  have hJ := isUnit_dexpJ_adOp_of_norm_le _ (hA μ x)
  rw [adOp_smul] at hJ
  refine ⟨hJ, ?_⟩
  have hJ' := isUnit_dexpJ_adOp_of_norm_le _ (hA μ x)
  exact exists_log_chart _ hJ'

end

end RenewalGeometry.LogGaugeDifferential
