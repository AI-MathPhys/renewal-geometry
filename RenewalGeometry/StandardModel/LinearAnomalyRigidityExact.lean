/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.TensorExteriorAnomalyPacket

/-!
# Linear anomaly rigidity of the charged multiplicities (`thm:linear-anomaly-rigidity`)

`thm:linear-anomaly-rigidity` of the spacetime–gauge duality manuscript.  With the
determinant-normalized integer charge table `y(Q,u,d,L,e) = (1,4,-2,-3,-6)`
(`eq:hypercharges`) and nonnegative integer charged multiplicities `n_Q, n_u, n_d, n_L, n_e`
(`eq:charged-multiplicities`), the four normalized linear anomaly rows are
(`eq:linear-anomaly-rows`)

* `r_3 = 2 n_Q - n_u - n_d` (`SU(3)² U(1)`),
* `r_3Y = n_Q - 2 n_u + n_d` (colour-weighted hypercharge),
* `r_2Y = n_Q - n_L` (`SU(2)² U(1)`),
* `r_gY = n_Q - 2 n_u + n_d - n_L + n_e` (gravitational),

and `Δ_lin = r_3² + r_3Y² + r_2Y² + r_gY²` (`eq:linear-anomaly-residual`).

* `deltaLin_eq_zero_iff`: for `n_Q > 0`, `Δ_lin = 0 ⟺ n_Q = n_u = n_d = n_L = n_e = g > 0`
  (`eq:linear-anomaly-common-count`);
* `multiplicityCubicAnomaly_eq_zero_of_common`: on this branch the cubic `U(1)³` anomaly of the
  multiplicity packet is `g` times the vanishing one-generation cubic anomaly, hence zero;
* `weakDoubletCount_eq`: the number of left-handed weak doublets is `3g + g = 4g`, even;
* `deltaLin_ge_one_of_ne_zero`: `Δ_lin ≠ 0 ⟹ Δ_lin ≥ 1` (`eq:linear-anomaly-integer-gap`);
* `charged_carrier_eq_three_of_certified`: on the `Δ_lin = 0` branch, one charged multiplicity
  certified as three forces the charged multiplicity vector `(3,3,3,3,3)`;
* `linear_anomaly_rigidity`: the assembled statement.

Rendering disclosed: the tail clause "with no future-visible charged mirror or exotic sector"
is the inventory hypothesis `Δ_inv^F = 0` of `thm:canonical-chiral-projectors` (the complete
future-visible nontrivial gauge carrier consists of the five target chiral types), under which
the charged carrier is exactly the multiplicity vector; it is carried here as the statement
that all five charged multiplicities equal three.  Gauge-trivial singlets are not part of
the multiplicity vector and remain unconstrained.
-/

namespace RenewalGeometry
namespace LinearAnomalyRigidity

/-- The charged multiplicity vector `(n_Q, n_u, n_d, n_L, n_e)` of
`eq:charged-multiplicities`. -/
@[ext]
structure ChargedMultiplicities where
  /-- `n_Q`, copies of `Q = C ⊗ W₂`. -/
  nQ : ℤ
  /-- `n_u`, copies of `u = Λ²C*`. -/
  nu : ℤ
  /-- `n_d`, copies of `d = C`. -/
  nd : ℤ
  /-- `n_L`, copies of `L = W₂*`. -/
  nL : ℤ
  /-- `n_e`, copies of `e = Λ²W₂*`. -/
  ne : ℤ

/-- The multiplicity vector as a function on the five charged species, in the order
`(Q, u, d, L, e)` of `leftChiralMultiplicity`. -/
def ChargedMultiplicities.vec (n : ChargedMultiplicities) : Fin 5 → ℤ :=
  ![n.nQ, n.nu, n.nd, n.nL, n.ne]

/-- The common-count vector `(g, g, g, g, g)`. -/
def common (g : ℤ) : ChargedMultiplicities := ⟨g, g, g, g, g⟩

/-- `r_3 = 2 n_Q - n_u - n_d` (`eq:linear-anomaly-rows`). -/
def r3 (n : ChargedMultiplicities) : ℤ := 2 * n.nQ - n.nu - n.nd

/-- `r_3Y = n_Q - 2 n_u + n_d` (`eq:linear-anomaly-rows`). -/
def r3Y (n : ChargedMultiplicities) : ℤ := n.nQ - 2 * n.nu + n.nd

/-- `r_2Y = n_Q - n_L` (`eq:linear-anomaly-rows`). -/
def r2Y (n : ChargedMultiplicities) : ℤ := n.nQ - n.nL

/-- `r_gY = n_Q - 2 n_u + n_d - n_L + n_e` (`eq:linear-anomaly-rows`). -/
def rgY (n : ChargedMultiplicities) : ℤ := n.nQ - 2 * n.nu + n.nd - n.nL + n.ne

/-- `Δ_lin = r_3² + r_3Y² + r_2Y² + r_gY²` (`eq:linear-anomaly-residual`). -/
def deltaLin (n : ChargedMultiplicities) : ℤ :=
  r3 n ^ 2 + r3Y n ^ 2 + r2Y n ^ 2 + rgY n ^ 2

theorem deltaLin_nonneg (n : ChargedMultiplicities) : 0 ≤ deltaLin n := by
  unfold deltaLin; positivity

/-- `Δ_lin = 0` exactly when all four rows vanish. -/
theorem deltaLin_eq_zero_iff_rows (n : ChargedMultiplicities) :
    deltaLin n = 0 ↔ r3 n = 0 ∧ r3Y n = 0 ∧ r2Y n = 0 ∧ rgY n = 0 := by
  constructor
  · intro h
    have h' : r3 n ^ 2 + r3Y n ^ 2 + r2Y n ^ 2 + rgY n ^ 2 = 0 := h
    have h1 : r3 n ^ 2 = 0 := by
      linarith [sq_nonneg (r3 n), sq_nonneg (r3Y n), sq_nonneg (r2Y n), sq_nonneg (rgY n)]
    have h2 : r3Y n ^ 2 = 0 := by
      linarith [sq_nonneg (r3 n), sq_nonneg (r3Y n), sq_nonneg (r2Y n), sq_nonneg (rgY n)]
    have h3 : r2Y n ^ 2 = 0 := by
      linarith [sq_nonneg (r3 n), sq_nonneg (r3Y n), sq_nonneg (r2Y n), sq_nonneg (rgY n)]
    have h4 : rgY n ^ 2 = 0 := by
      linarith [sq_nonneg (r3 n), sq_nonneg (r3Y n), sq_nonneg (r2Y n), sq_nonneg (rgY n)]
    exact ⟨pow_eq_zero_iff two_ne_zero |>.mp h1, pow_eq_zero_iff two_ne_zero |>.mp h2,
      pow_eq_zero_iff two_ne_zero |>.mp h3, pow_eq_zero_iff two_ne_zero |>.mp h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    simp [deltaLin, h1, h2, h3, h4]

/-- **`eq:linear-anomaly-common-count`.**  For `n_Q > 0`,
`Δ_lin = 0 ⟺ n_Q = n_u = n_d = n_L = n_e =: g > 0`. -/
theorem deltaLin_eq_zero_iff (n : ChargedMultiplicities) (hQ : 0 < n.nQ) :
    deltaLin n = 0 ↔ ∃ g : ℤ, 0 < g ∧ n = common g := by
  rw [deltaLin_eq_zero_iff_rows]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨n.nQ, hQ, ?_⟩
    simp only [r3, r3Y, r2Y, rgY] at h1 h2 h3 h4
    ext <;> simp only [common] <;> omega
  · rintro ⟨g, -, rfl⟩
    simp only [r3, r3Y, r2Y, rgY, common]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- The cubic `U(1)³` anomaly of the charged multiplicity packet: each species `f` contributes
`n_f · dim(f) · y_f³` with the anomaly-forced weights `(a,b) = (-2,3)` of `thm:hypercharge`. -/
noncomputable def multiplicityCubicAnomaly (n : ChargedMultiplicities) : ℚ :=
  ∑ s, (n.vec s : ℚ) * leftChiralMultiplicity s * leftChiralCentralWeight (-2) 3 s ^ 3

/-- With a common count `g`, the packet cubic anomaly is `g` times the one-generation cubic
anomaly. -/
theorem multiplicityCubicAnomaly_common (g : ℤ) :
    multiplicityCubicAnomaly (common g) = (g : ℚ) * cubicCentralAnomaly (-2) 3 := by
  simp only [multiplicityCubicAnomaly, cubicCentralAnomaly, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hs : (common g).vec s = g := by
    fin_cases s <;> rfl
  rw [hs]; ring

/-- On the common-count branch the cubic anomaly vanishes automatically
(`thm:linear-anomaly-rigidity`, cubic clause). -/
theorem multiplicityCubicAnomaly_eq_zero_of_common (g : ℤ) :
    multiplicityCubicAnomaly (common g) = 0 := by
  rw [multiplicityCubicAnomaly_common, cubicCentralAnomaly_trace]
  norm_num

/-- The number of left-handed weak doublets: three colours of `Q` per copy plus one `L` per
copy. -/
def weakDoubletCount (n : ChargedMultiplicities) : ℤ := 3 * n.nQ + n.nL

/-- With a common count `g` there are `3g + g = 4g` weak doublets, an even number. -/
theorem weakDoubletCount_eq (g : ℤ) :
    weakDoubletCount (common g) = 4 * g ∧ Even (weakDoubletCount (common g)) := by
  refine ⟨by simp [weakDoubletCount, common]; ring, ?_⟩
  simp only [weakDoubletCount, common]
  exact ⟨2 * g, by ring⟩

/-- **`eq:linear-anomaly-integer-gap`.**  A nonzero residual is at least one. -/
theorem deltaLin_ge_one_of_ne_zero (n : ChargedMultiplicities) (h : deltaLin n ≠ 0) :
    1 ≤ deltaLin n := by
  have := deltaLin_nonneg n
  omega

/-- Tail clause: on the `Δ_lin = 0` branch with `n_Q > 0`, if one charged multiplicity is
certified as three then the charged multiplicity vector is `(3,3,3,3,3)`, i.e. the charged
carrier is `3Q ⊕ 3u ⊕ 3d ⊕ 3L ⊕ 3e`. -/
theorem charged_carrier_eq_three_of_certified (n : ChargedMultiplicities) (hQ : 0 < n.nQ)
    (hΔ : deltaLin n = 0)
    (hthree : n.nQ = 3 ∨ n.nu = 3 ∨ n.nd = 3 ∨ n.nL = 3 ∨ n.ne = 3) :
    n = common 3 := by
  obtain ⟨g, -, rfl⟩ := (deltaLin_eq_zero_iff n hQ).mp hΔ
  simp only [common] at hthree
  have hg : g = 3 := by
    rcases hthree with h | h | h | h | h <;> exact h
  rw [hg]

/-- **`thm:linear-anomaly-rigidity` (Linear anomaly rigidity of the charged multiplicities),
assembled.**  For integer multiplicities with `n_Q > 0`:
`Δ_lin = 0 ⟺` all five charged multiplicities equal a common `g > 0`; on that branch the cubic
`U(1)³` anomaly of the packet is `g` times the vanishing one-generation anomaly (hence zero) and
the weak-doublet count is `4g` (even); `Δ_lin ≠ 0 ⟹ Δ_lin ≥ 1`; and if one charged
multiplicity is certified as three the charged carrier is `3Q ⊕ 3u ⊕ 3d ⊕ 3L ⊕ 3e`. -/
theorem linear_anomaly_rigidity (n : ChargedMultiplicities) (hQ : 0 < n.nQ) :
    (deltaLin n = 0 ↔ ∃ g : ℤ, 0 < g ∧ n = common g)
    ∧ (∀ g : ℤ, multiplicityCubicAnomaly (common g) = (g : ℚ) * cubicCentralAnomaly (-2) 3
        ∧ multiplicityCubicAnomaly (common g) = 0)
    ∧ (∀ g : ℤ, weakDoubletCount (common g) = 4 * g ∧ Even (weakDoubletCount (common g)))
    ∧ (deltaLin n ≠ 0 → 1 ≤ deltaLin n)
    ∧ (deltaLin n = 0 → (n.nQ = 3 ∨ n.nu = 3 ∨ n.nd = 3 ∨ n.nL = 3 ∨ n.ne = 3) →
        n = common 3) :=
  ⟨deltaLin_eq_zero_iff n hQ,
    fun g => ⟨multiplicityCubicAnomaly_common g, multiplicityCubicAnomaly_eq_zero_of_common g⟩,
    weakDoubletCount_eq,
    deltaLin_ge_one_of_ne_zero n,
    charged_carrier_eq_three_of_certified n hQ⟩

end LinearAnomalyRigidity
end RenewalGeometry
