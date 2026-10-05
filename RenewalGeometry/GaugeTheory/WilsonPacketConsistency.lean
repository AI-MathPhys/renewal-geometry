/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.GaugeTheory.TransportPlaquetteConsistency
import RenewalGeometry.Analysis.NormedAlgebraLogBCH
import RenewalGeometry.Action.NativeScalingBlocksExact

/-!
# Literal Wilson packets versus the reconstructed connection (`eq:Wilson-packet-consistency`)

Clause (a) of `prop:Wilson-packet-transfer` (Einstein–SM action-closure manuscript, "Finite
Wilson packets and continuum covariant translations"): under the growing band
`eq:eq-growing-band` (`‖∂^α z‖ ≤ C_q B^{|α|}`, `hB ≤ c_res`) the literal packets of the native
action (`eq:native-plaquettes`, `eq:native-matter-links`) satisfy
`max_x |F^h(x) - F_{A_h}(x)| + max_x |K^h(x) - D_{A_h}H_h(x)| ≤ C h B²`.

The links are the literal exponential links `U_μ(x) = e^{hA_μ(x)}` of the nodal samples of the
reconstructed connection (the reconstruction interpolates the nodal record), and the plaquette is
`U_μ(x)U_ν(x+he_μ)U_μ(x+he_ν)⁻¹U_ν(x)⁻¹` with the analytic logarithm, exactly as
`NativeScaling.fieldStrength` of `Action/NativeScalingBlocksExact.lean`.  The point is the sharp
rate `h B²` (not `h · poly(B)`): every expansion below keeps track of the powers of `B`, using only
`‖A‖ ≤ c`, `‖DA‖ ≤ cB`, `Lip(DA) ≤ cB²` (the `|α| ≤ 2` part of the growing band), `B ≥ 1`
and `hB ≤ 1`.

* `norm_exp_edge_sub_le`: one exponential link with an `x`-dependent argument
  `exp(h(Z₀ + hZ₁ + R)) = 1 + hZ₀ + h²(Z₁ + Z₀²/2) + O(B²h³)`.
* `norm_mul_quad_sub_le`: product of two second-order expansions with absolute errors.
* `norm_expPlaquette_sub_le` (**four-link plaquette**): `‖P - (1 + h²(r - s + [X,Y]))‖ ≤ κ B²h³`.
* `norm_logExpPlaquette_sub_le`: the analytic-logarithm step with the sharp rate.
* `norm_fieldStrength_sub_curvature_le` (**curvature part of `eq:Wilson-packet-consistency`**):
  `‖F^h_{μν}(x) - F_{A,μν}(x)‖ ≤ C h B²` for a `C¹` connection with Lipschitz derivative.
* `norm_higgsPacket_sub_covDeriv_le` (**Higgs part**): `‖K^h_μ(x) - D_{A,μ}H(x)‖ ≤ C h B²`.
* `wilson_packet_consistency`: both parts for the literal grid packets
  `NativeScaling.fieldStrength` / `NativeScaling.higgsLink` of a record that samples the
  reconstructed fields.
-/

open NormedSpace

noncomputable section

namespace RenewalGeometry.WilsonPacket

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-! ### One exponential link -/

/-- The edge constant `27c³e^{3c} + c + 4c²`. -/
def edgeC (c : ℝ) : ℝ := 27 * c ^ 3 * Real.exp (3 * c) + c + 4 * c ^ 2

theorem edgeC_nonneg {c : ℝ} (hc : 0 ≤ c) : 0 ≤ edgeC c := by unfold edgeC; positivity

/-- **One exponential link with an `x`-dependent argument**: if `‖Z₀‖ ≤ c`, `‖Z₁‖ ≤ cB` and
`‖R‖ ≤ cB²h²` (`B ≥ 1`, `0 ≤ h ≤ 1`, `hB ≤ 1`), then
`‖exp(h(Z₀ + hZ₁ + R)) - (1 + hZ₀ + h²(Z₁ + Z₀²/2))‖ ≤ edgeC c · B² h³`. -/
theorem norm_exp_edge_sub_le {Z₀ Z₁ R : 𝔸} {h B c : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hB1 : 1 ≤ B) (hhB : h * B ≤ 1) (hZ₀ : ‖Z₀‖ ≤ c) (hZ₁ : ‖Z₁‖ ≤ c * B)
    (hR : ‖R‖ ≤ c * B ^ 2 * h ^ 2) :
    ‖exp (h • (Z₀ + h • Z₁ + R)) - (1 + h • Z₀ + h ^ 2 • (Z₁ + (1 / 2 : ℝ) • (Z₀ * Z₀)))‖ ≤
      edgeC c * B ^ 2 * h ^ 3 := by
  have hc : 0 ≤ c := (norm_nonneg _).trans hZ₀
  have hB0 : 0 ≤ B := by linarith
  set Z := Z₀ + h • Z₁ + R with hZdef
  have hhB0 : 0 ≤ h * B := mul_nonneg hh hB0
  have hsq : (h * B) ^ 2 ≤ h * B := by nlinarith
  have hD : ‖Z - Z₀‖ ≤ 2 * c * (h * B) := by
    have e : Z - Z₀ = h • Z₁ + R := by rw [hZdef]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
    have h1 : h * ‖Z₁‖ ≤ c * (h * B) := by nlinarith
    have h2 : c * B ^ 2 * h ^ 2 ≤ c * (h * B) := by
      have := mul_le_mul_of_nonneg_left hsq hc; nlinarith
    linarith
  have hZn : ‖Z‖ ≤ 3 * c := by
    have : Z = Z₀ + (Z - Z₀) := by abel
    rw [this]
    refine (norm_add_le _ _).trans ?_
    have : 2 * c * (h * B) ≤ 2 * c := by nlinarith
    linarith
  have hT := LogBCH.norm_exp_sub_quadratic_le (h • Z)
  have hhZ : ‖h • Z‖ ≤ 3 * c * h := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]; nlinarith
  have hT' : ‖exp (h • Z) - (1 + h • Z + (1 / 2 : ℝ) • ((h • Z) * (h • Z)))‖ ≤
      27 * c ^ 3 * Real.exp (3 * c) * B ^ 2 * h ^ 3 := by
    refine hT.trans ?_
    have e1 : ‖h • Z‖ ^ 3 ≤ (3 * c * h) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hhZ 3
    have e2 : Real.exp ‖h • Z‖ ≤ Real.exp (3 * c) :=
      Real.exp_le_exp.2 (hhZ.trans (by nlinarith))
    have hB2 : 1 ≤ B ^ 2 := by nlinarith
    calc ‖h • Z‖ ^ 3 * Real.exp ‖h • Z‖ ≤ (3 * c * h) ^ 3 * Real.exp (3 * c) :=
          mul_le_mul e1 e2 (Real.exp_pos _).le (by positivity)
      _ = 27 * c ^ 3 * Real.exp (3 * c) * 1 * h ^ 3 := by ring
      _ ≤ 27 * c ^ 3 * Real.exp (3 * c) * B ^ 2 * h ^ 3 := by gcongr
  have hid : exp (h • Z) - (1 + h • Z₀ + h ^ 2 • (Z₁ + (1 / 2 : ℝ) • (Z₀ * Z₀))) =
      (exp (h • Z) - (1 + h • Z + (1 / 2 : ℝ) • ((h • Z) * (h • Z)))) +
        (h • R + (h ^ 2 / 2) • (Z * (Z - Z₀) + (Z - Z₀) * Z₀)) := by
    have hlin : h • Z = h • Z₀ + h ^ 2 • Z₁ + h • R := by rw [hZdef]; module
    have hq : (h • Z) * (h • Z) = h ^ 2 • (Z * Z) := by
      rw [smul_mul_smul_comm, ← pow_two]
    rw [hq]
    simp only [mul_sub, sub_mul]
    generalize hE : exp (h • Z) = eZ
    rw [hlin]
    module
  rw [hid]
  refine (norm_add_le _ _).trans ?_
  have hR' : ‖h • R‖ ≤ c * B ^ 2 * h ^ 3 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
    calc h * ‖R‖ ≤ h * (c * B ^ 2 * h ^ 2) := mul_le_mul_of_nonneg_left hR hh
      _ = c * B ^ 2 * h ^ 3 := by ring
  have hQ : ‖(h ^ 2 / 2) • (Z * (Z - Z₀) + (Z - Z₀) * Z₀)‖ ≤ 4 * c ^ 2 * B ^ 2 * h ^ 3 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have k1 : ‖Z * (Z - Z₀) + (Z - Z₀) * Z₀‖ ≤ 8 * c ^ 2 * (h * B) := by
      refine (norm_add_le _ _).trans ?_
      have := (norm_mul_le Z (Z - Z₀)).trans
        (mul_le_mul hZn hD (norm_nonneg _) (by positivity))
      have := (norm_mul_le (Z - Z₀) Z₀).trans
        (mul_le_mul hD hZ₀ (norm_nonneg _) (by positivity))
      nlinarith
    have hBB : B ≤ B ^ 2 := by nlinarith
    calc h ^ 2 / 2 * ‖Z * (Z - Z₀) + (Z - Z₀) * Z₀‖ ≤ h ^ 2 / 2 * (8 * c ^ 2 * (h * B)) :=
          mul_le_mul_of_nonneg_left k1 (by positivity)
      _ = 4 * c ^ 2 * B * h ^ 3 := by ring
      _ ≤ 4 * c ^ 2 * B ^ 2 * h ^ 3 := by gcongr
  have := add_le_add hR' hQ
  calc _ ≤ 27 * c ^ 3 * Real.exp (3 * c) * B ^ 2 * h ^ 3 +
        ‖h • R + (h ^ 2 / 2) • (Z * (Z - Z₀) + (Z - Z₀) * Z₀)‖ := add_le_add hT' le_rfl
    _ ≤ 27 * c ^ 3 * Real.exp (3 * c) * B ^ 2 * h ^ 3 +
        (c * B ^ 2 * h ^ 3 + 4 * c ^ 2 * B ^ 2 * h ^ 3) :=
        add_le_add le_rfl ((norm_add_le _ _).trans this)
    _ = edgeC c * B ^ 2 * h ^ 3 := by unfold edgeC; ring

/-! ### Products of second-order expansions with absolute errors -/

omit [CompleteSpace 𝔸] in
/-- **Product of two second-order expansions** (absolute errors, no loss in the size of the
second-order coefficients): if `‖u - (1 + hA + h²B)‖ ≤ E`, `‖u' - (1 + hA' + h²B')‖ ≤ E'`,
`‖u'‖ ≤ M`, `‖A‖, ‖A'‖ ≤ α`, `‖B‖, ‖B'‖ ≤ β`, then
`‖uu' - (1 + h(A + A') + h²(B + B' + AA'))‖ ≤ EM + (1 + hα + h²β)E' + h³(2αβ + hβ²)`. -/
theorem norm_mul_quad_sub_le {u u' A A' Bq Bq' : 𝔸} {h α β E E' M : ℝ} (hh : 0 ≤ h)
    (hu : ‖u - (1 + h • A + h ^ 2 • Bq)‖ ≤ E) (hu' : ‖u' - (1 + h • A' + h ^ 2 • Bq')‖ ≤ E')
    (hM : ‖u'‖ ≤ M) (hA : ‖A‖ ≤ α) (hA' : ‖A'‖ ≤ α) (hB : ‖Bq‖ ≤ β) (hB' : ‖Bq'‖ ≤ β) :
    ‖u * u' - (1 + h • (A + A') + h ^ 2 • (Bq + Bq' + A * A'))‖ ≤
      E * M + (1 + h * α + h ^ 2 * β) * E' + h ^ 3 * (2 * α * β + h * β ^ 2) := by
  have hα : 0 ≤ α := (norm_nonneg _).trans hA
  have hβ : 0 ≤ β := (norm_nonneg _).trans hB
  have hE' : 0 ≤ E' := (norm_nonneg _).trans hu'
  set p := 1 + h • A + h ^ 2 • Bq
  set p' := 1 + h • A' + h ^ 2 • Bq'
  have hp : ‖p‖ ≤ 1 + h * α + h ^ 2 * β := by
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    rw [norm_one, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hh,
      abs_of_nonneg (by positivity)]
    have := mul_le_mul_of_nonneg_left hA hh
    have := mul_le_mul_of_nonneg_left hB (sq_nonneg h)
    linarith
  have hpp : p * p' - (1 + h • (A + A') + h ^ 2 • (Bq + Bq' + A * A')) =
      h ^ 3 • (A * Bq' + Bq * A') + h ^ 4 • (Bq * Bq') := by
    simp only [p, p', add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
      smul_add]
    module
  have e : u * u' - (1 + h • (A + A') + h ^ 2 • (Bq + Bq' + A * A')) =
      (u - p) * u' + p * (u' - p') +
        (h ^ 3 • (A * Bq' + Bq * A') + h ^ 4 • (Bq * Bq')) := by
    rw [← hpp]; noncomm_ring
  rw [e]
  have t1 : ‖(u - p) * u'‖ ≤ E * M :=
    (norm_mul_le _ _).trans (mul_le_mul hu hM (norm_nonneg _) ((norm_nonneg _).trans hu))
  have t2 : ‖p * (u' - p')‖ ≤ (1 + h * α + h ^ 2 * β) * E' :=
    (norm_mul_le _ _).trans (mul_le_mul hp hu' (norm_nonneg _) (by positivity))
  have t3 : ‖h ^ 3 • (A * Bq' + Bq * A') + h ^ 4 • (Bq * Bq')‖ ≤
      h ^ 3 * (2 * α * β + h * β ^ 2) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
    have hAB : ‖A * Bq' + Bq * A'‖ ≤ 2 * α * β := by
      refine (norm_add_le _ _).trans ?_
      have := (norm_mul_le A Bq').trans (mul_le_mul hA hB' (norm_nonneg _) hα)
      have := (norm_mul_le Bq A').trans (mul_le_mul hB hA' (norm_nonneg _) hβ)
      linarith
    have hBB : ‖Bq * Bq'‖ ≤ β ^ 2 := by
      have := (norm_mul_le Bq Bq').trans (mul_le_mul hB hB' (norm_nonneg _) hβ)
      nlinarith
    have := mul_le_mul_of_nonneg_left hAB (by positivity : (0 : ℝ) ≤ h ^ 3)
    have := mul_le_mul_of_nonneg_left hBB (by positivity : (0 : ℝ) ≤ h ^ 4)
    nlinarith
  calc _ ≤ ‖(u - p) * u'‖ + ‖p * (u' - p')‖ +
        ‖h ^ 3 • (A * Bq' + Bq * A') + h ^ 4 • (Bq * Bq')‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add t1 t2) t3

/-! ### The four-link exponential plaquette -/

/-- The constant `cb = c + c²/2` bounding the second-order coefficients of one link (in units of
`B`). -/
def cbC (c : ℝ) : ℝ := c + c ^ 2 / 2

/-- The constant of a product of two links. -/
def k2C (c : ℝ) : ℝ := edgeC c * (Real.exp (3 * c) + 1 + c + cbC c) + 2 * c * cbC c + cbC c ^ 2

/-- The constant `2cb + c²` bounding the second-order coefficient of a product of two links. -/
def cbbC (c : ℝ) : ℝ := 2 * cbC c + c ^ 2

/-- **The explicit plaquette constant** `κ(c)` (depends only on the sup bound `c`). -/
def plaqC (c : ℝ) : ℝ :=
  k2C c * Real.exp (6 * c) + (1 + 2 * c + cbbC c) * k2C c + 4 * c * cbbC c + cbbC c ^ 2

theorem cbC_nonneg {c : ℝ} (hc : 0 ≤ c) : 0 ≤ cbC c := by unfold cbC; positivity
theorem k2C_nonneg {c : ℝ} (hc : 0 ≤ c) : 0 ≤ k2C c := by
  unfold k2C; have := edgeC_nonneg hc; have := cbC_nonneg hc; positivity
theorem cbbC_nonneg {c : ℝ} (hc : 0 ≤ c) : 0 ≤ cbbC c := by
  unfold cbbC; have := cbC_nonneg hc; positivity
theorem plaqC_nonneg {c : ℝ} (hc : 0 ≤ c) : 0 ≤ plaqC c := by
  unfold plaqC; have := k2C_nonneg hc; have := cbbC_nonneg hc; positivity

/-- Normal form of one link: `exp(h(Z₀ + hZ₁ + R))` with the data of `norm_exp_edge_sub_le`. -/
theorem link_normalForm {Z₀ Z₁ R : 𝔸} {h B c : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hB1 : 1 ≤ B) (hhB : h * B ≤ 1) (hZ₀ : ‖Z₀‖ ≤ c) (hZ₁ : ‖Z₁‖ ≤ c * B)
    (hR : ‖R‖ ≤ c * B ^ 2 * h ^ 2) :
    ‖exp (h • (Z₀ + h • Z₁ + R)) - (1 + h • Z₀ + h ^ 2 • (Z₁ + (1 / 2 : ℝ) • (Z₀ * Z₀)))‖ ≤
        edgeC c * B ^ 2 * h ^ 3 ∧
      ‖Z₁ + (1 / 2 : ℝ) • (Z₀ * Z₀)‖ ≤ cbC c * B ∧
      ‖exp (h • (Z₀ + h • Z₁ + R))‖ ≤ Real.exp (3 * c) := by
  have hc : 0 ≤ c := (norm_nonneg _).trans hZ₀
  have hB0 : 0 ≤ B := by linarith
  refine ⟨norm_exp_edge_sub_le hh hh1 hB1 hhB hZ₀ hZ₁ hR, ?_, ?_⟩
  · refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have := (norm_mul_le Z₀ Z₀).trans (mul_le_mul hZ₀ hZ₀ (norm_nonneg _) hc)
    unfold cbC
    nlinarith
  · refine (LogBCH.norm_exp_le_real_exp _).trans (Real.exp_le_exp.2 ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
    have hhB0 : 0 ≤ h * B := mul_nonneg hh hB0
    have : ‖Z₀ + h • Z₁ + R‖ ≤ 3 * c := by
      have a1 := norm_add_le (Z₀ + h • Z₁) R
      have a2 := norm_add_le Z₀ (h • Z₁)
      have a3 : ‖h • Z₁‖ ≤ c := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]; nlinarith
      have a4 : ‖R‖ ≤ c := hR.trans (by
        have : (h * B) ^ 2 ≤ 1 := by nlinarith
        nlinarith)
      linarith
    nlinarith [norm_nonneg (Z₀ + h • Z₁ + R)]

/-- Real bookkeeping for `norm_mul_quad_sub_le` in the growing-band regime: absolute errors
`≤ k B² h³`, `≤ k' B² h³`, `α = a`, `β = bB` give a product error `≤ κ B² h³`. -/
theorem quad_bound {E E' M h B a b k k' m : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) (hB1 : 1 ≤ B)
    (hhB : h * B ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hE0 : 0 ≤ E) (hE'0 : 0 ≤ E')
    (hE : E ≤ k * B ^ 2 * h ^ 3) (hE' : E' ≤ k' * B ^ 2 * h ^ 3) (hM0 : 0 ≤ M) (hM : M ≤ m) :
    E * M + (1 + h * a + h ^ 2 * (b * B)) * E' + h ^ 3 * (2 * a * (b * B) + h * (b * B) ^ 2) ≤
      (k * m + (1 + a + b) * k' + 2 * a * b + b ^ 2) * B ^ 2 * h ^ 3 := by
  have hm : 0 ≤ m := hM0.trans hM
  have hB0 : 0 ≤ B := by linarith
  have h3 : 0 ≤ h ^ 3 := by positivity
  have t1 : E * M ≤ k * B ^ 2 * h ^ 3 * m :=
    (mul_le_mul_of_nonneg_left hM hE0).trans (mul_le_mul_of_nonneg_right hE hm)
  have hc1 : 1 + h * a + h ^ 2 * (b * B) ≤ 1 + a + b := by
    have : h * a ≤ a := mul_le_of_le_one_left ha hh1
    have : h ^ 2 * (b * B) ≤ b := by
      have : h ^ 2 * (b * B) = b * (h * (h * B)) := by ring
      rw [this]
      refine mul_le_of_le_one_right hb ?_
      nlinarith
    linarith
  have t2 : (1 + h * a + h ^ 2 * (b * B)) * E' ≤ (1 + a + b) * (k' * B ^ 2 * h ^ 3) :=
    mul_le_mul hc1 hE' hE'0 (by positivity)
  have hBB : B ≤ B ^ 2 := by nlinarith
  have t3 : h ^ 3 * (2 * a * (b * B) + h * (b * B) ^ 2) ≤ h ^ 3 * ((2 * a * b + b ^ 2) * B ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ h3
    have : 2 * a * (b * B) ≤ 2 * a * b * B ^ 2 := by
      have := mul_le_mul_of_nonneg_left hBB (by positivity : (0 : ℝ) ≤ 2 * a * b); nlinarith
    have : h * (b * B) ^ 2 ≤ b ^ 2 * B ^ 2 := by
      have : (b * B) ^ 2 = b ^ 2 * B ^ 2 := by ring
      rw [this]; exact mul_le_of_le_one_left (by positivity) hh1
    nlinarith
  nlinarith

/-- **The four-link exponential plaquette** (curvature part of `eq:Wilson-packet-consistency`,
before the logarithm): with link arguments `A_μ(x) = X`, `A_ν(x + he_μ) = Y + hr + R₂`,
`A_μ(x + he_ν) = X + hs + R₃`, `A_ν(x) = Y` (`r = ∂_μA_ν`, `s = ∂_νA_μ`, Taylor remainders
`‖R_i‖ ≤ cB²h²`), the literal plaquette `e^{hX} e^{h(Y+hr+R₂)} e^{-h(X+hs+R₃)} e^{-hY}`
satisfies `‖P - (1 + h²(r - s + [X,Y]))‖ ≤ κ(c) B² h³`. -/
theorem norm_expPlaquette_sub_le {X Y r s R₂ R₃ : 𝔸} {h B c : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hB1 : 1 ≤ B) (hhB : h * B ≤ 1) (hX : ‖X‖ ≤ c) (hY : ‖Y‖ ≤ c) (hr : ‖r‖ ≤ c * B)
    (hs : ‖s‖ ≤ c * B) (hR₂ : ‖R₂‖ ≤ c * B ^ 2 * h ^ 2) (hR₃ : ‖R₃‖ ≤ c * B ^ 2 * h ^ 2) :
    ‖exp (h • X) * exp (h • (Y + h • r + R₂)) * exp (-(h • (X + h • s + R₃))) *
        exp (-(h • Y)) - (1 + h ^ 2 • (r - s + (X * Y - Y * X)))‖ ≤ plaqC c * B ^ 2 * h ^ 3 := by
  have hc : 0 ≤ c := (norm_nonneg _).trans hX
  have hB0 : 0 ≤ B := by linarith
  have hcB : 0 ≤ c * B := by positivity
  have hcBh : 0 ≤ c * B ^ 2 * h ^ 2 := by positivity
  have z0 : ‖(0 : 𝔸)‖ ≤ c * B := by rw [norm_zero]; exact hcB
  have z0' : ‖(0 : 𝔸)‖ ≤ c * B ^ 2 * h ^ 2 := by rw [norm_zero]; exact hcBh
  have e1 : exp (h • X) = exp (h • (X + h • (0 : 𝔸) + 0)) := by simp
  have e3 : exp (-(h • (X + h • s + R₃))) = exp (h • (-X + h • (-s) + -R₃)) := by
    congr 1; module
  have e4 : exp (-(h • Y)) = exp (h • (-Y + h • (0 : 𝔸) + 0)) := by
    congr 1; module
  rw [e1, e3, e4]
  obtain ⟨l1, b1, n1⟩ := link_normalForm hh hh1 hB1 hhB hX z0 z0'
  obtain ⟨l2, b2, n2⟩ := link_normalForm hh hh1 hB1 hhB hY hr hR₂
  obtain ⟨l3, b3, n3⟩ := link_normalForm (Z₀ := -X) (Z₁ := -s) (R := -R₃) (c := c) hh hh1
    hB1 hhB (by rw [norm_neg]; exact hX) (by rw [norm_neg]; exact hs) (by rw [norm_neg]; exact hR₃)
  obtain ⟨l4, b4, n4⟩ := link_normalForm (Z₀ := -Y) (c := c) hh hh1 hB1 hhB (by rw [norm_neg]; exact hY) z0 z0'
  have hcb := cbC_nonneg hc
  have he := edgeC_nonneg hc
  have hE0 : 0 ≤ edgeC c * B ^ 2 * h ^ 3 := by positivity
  -- the two pairs
  have hk12 := quad_bound (a := c) (b := cbC c) (k := edgeC c) (k' := edgeC c)
    (m := Real.exp (3 * c)) hh hh1 hB1 hhB hc hcb hE0 hE0 le_rfl le_rfl (Real.exp_pos _).le le_rfl
  have hk2eq : (edgeC c * Real.exp (3 * c) + (1 + c + cbC c) * edgeC c + 2 * c * cbC c +
      cbC c ^ 2) * B ^ 2 * h ^ 3 = k2C c * B ^ 2 * h ^ 3 := by unfold k2C; ring
  have Q12 := (norm_mul_quad_sub_le (α := c) (β := cbC c * B) hh l1 l2 n2 hX hY b1 b2).trans
    (hk12.trans (le_of_eq hk2eq))
  have Q34 := (norm_mul_quad_sub_le (α := c) (β := cbC c * B) hh l3 l4 n4
    (by rw [norm_neg]; exact hX) (by rw [norm_neg]; exact hY) b3 b4).trans
    (hk12.trans (le_of_eq hk2eq))
  -- bounds on the pair coefficients
  have hA12 : ‖X + Y‖ ≤ 2 * c := (norm_add_le _ _).trans (by linarith)
  have hA34 : ‖-X + -Y‖ ≤ 2 * c := (norm_add_le _ _).trans (by rw [norm_neg, norm_neg]; linarith)
  have hBB : B ≤ B ^ 2 := by nlinarith
  have hcbb : cbbC c * B = 2 * (cbC c * B) + c ^ 2 * B := by unfold cbbC; ring
  have hc2 : c ^ 2 ≤ c ^ 2 * B := le_mul_of_one_le_right (sq_nonneg c) hB1
  have hcc : c * c = c ^ 2 := by ring
  have hB12 : ‖((0 : 𝔸) + (1 / 2 : ℝ) • (X * X)) + (r + (1 / 2 : ℝ) • (Y * Y)) + X * Y‖ ≤
      cbbC c * B := by
    have hXY := (norm_mul_le X Y).trans (mul_le_mul hX hY (norm_nonneg _) hc)
    calc _ ≤ ‖((0 : 𝔸) + (1 / 2 : ℝ) • (X * X)) + (r + (1 / 2 : ℝ) • (Y * Y))‖ + ‖X * Y‖ :=
          norm_add_le _ _
      _ ≤ (‖(0 : 𝔸) + (1 / 2 : ℝ) • (X * X)‖ + ‖r + (1 / 2 : ℝ) • (Y * Y)‖) + c * c :=
          add_le_add (norm_add_le _ _) hXY
      _ ≤ (cbC c * B + cbC c * B) + c * c := by gcongr
      _ ≤ cbbC c * B := by rw [hcbb]; linarith
  have hB34 : ‖(-s + (1 / 2 : ℝ) • (-X * -X)) + ((0 : 𝔸) + (1 / 2 : ℝ) • (-Y * -Y)) + -X * -Y‖ ≤
      cbbC c * B := by
    have hXY : ‖-X * -Y‖ ≤ c * c := (norm_mul_le (-X) (-Y)).trans
      (mul_le_mul ((norm_neg X).trans_le hX) ((norm_neg Y).trans_le hY) (norm_nonneg _) hc)
    calc _ ≤ ‖(-s + (1 / 2 : ℝ) • (-X * -X)) + ((0 : 𝔸) + (1 / 2 : ℝ) • (-Y * -Y))‖ +
          ‖-X * -Y‖ := norm_add_le _ _
      _ ≤ (‖-s + (1 / 2 : ℝ) • (-X * -X)‖ + ‖(0 : 𝔸) + (1 / 2 : ℝ) • (-Y * -Y)‖) + c * c :=
          add_le_add (norm_add_le _ _) hXY
      _ ≤ (cbC c * B + cbC c * B) + c * c := by gcongr
      _ ≤ cbbC c * B := by rw [hcbb]; linarith
  have hn34 : ‖exp (h • (-X + h • (-s) + -R₃)) * exp (h • (-Y + h • (0 : 𝔸) + 0))‖ ≤
      Real.exp (6 * c) := by
    refine (norm_mul_le _ _).trans ((mul_le_mul n3 n4 (norm_nonneg _) (Real.exp_pos _).le).trans
      (le_of_eq ?_))
    rw [← Real.exp_add]; ring_nf
  have hcbb0 := cbbC_nonneg hc
  have hk2 := k2C_nonneg hc
  have q := norm_mul_quad_sub_le (α := 2 * c) (β := cbbC c * B) hh Q12 Q34 hn34 hA12 hA34
    hB12 hB34
  have hfin := quad_bound (a := 2 * c) (b := cbbC c) (k := k2C c) (k' := k2C c)
    (m := Real.exp (6 * c)) hh hh1 hB1 hhB (by positivity) hcbb0 (by positivity) (by positivity)
    le_rfl le_rfl (by positivity) le_rfl
  have hA0 : X + Y + (-X + -Y) = 0 := by abel
  have hBsum : ((0 : 𝔸) + (1 / 2 : ℝ) • (X * X)) + (r + (1 / 2 : ℝ) • (Y * Y)) + X * Y +
      ((-s + (1 / 2 : ℝ) • (-X * -X)) + ((0 : 𝔸) + (1 / 2 : ℝ) • (-Y * -Y)) + -X * -Y) +
      (X + Y) * (-X + -Y) = r - s + (X * Y - Y * X) := by
    simp only [neg_mul_neg, mul_add, add_mul, mul_neg, neg_mul]
    module
  have htgt : (1 + h • (X + Y + (-X + -Y)) + h ^ 2 • (((0 : 𝔸) + (1 / 2 : ℝ) • (X * X)) +
      (r + (1 / 2 : ℝ) • (Y * Y)) + X * Y +
      ((-s + (1 / 2 : ℝ) • (-X * -X)) + ((0 : 𝔸) + (1 / 2 : ℝ) • (-Y * -Y)) + -X * -Y) +
      (X + Y) * (-X + -Y))) = 1 + h ^ 2 • (r - s + (X * Y - Y * X)) := by
    rw [hA0, hBsum, smul_zero, add_zero]
  rw [htgt, ← mul_assoc] at q
  refine q.trans (hfin.trans (le_of_eq ?_))
  unfold plaqC
  ring

/-! ### The analytic logarithm with the sharp rate -/

open ShiftedPlaquette in
/-- **Sharp logarithm step**: if `‖Pq - (1 + h²F)‖ ≤ C h³`, `‖F‖ ≤ N` and
`ζ = N h² + C h³ ≤ 1/2`, then `‖h⁻² log(Pq) - F‖ ≤ C h + 2 (N + C h)² h²`. -/
theorem norm_logPlaquette_sub_le_sharp {Pq F : 𝔸} {h C N : ℝ} (hh : 0 < h) (hF : ‖F‖ ≤ N)
    (hP : ‖Pq - (1 + h ^ 2 • F)‖ ≤ C * h ^ 3) (hsmall : N * h ^ 2 + C * h ^ 3 ≤ 1 / 2) :
    ‖(h ^ 2)⁻¹ • logOneAdd (Pq - 1) - F‖ ≤ C * h + 2 * (N + C * h) ^ 2 * h ^ 2 := by
  have hh2 : (0 : ℝ) < h ^ 2 := by positivity
  set z := Pq - 1
  have hz : ‖z‖ ≤ N * h ^ 2 + C * h ^ 3 := by
    have e : z = (Pq - (1 + h ^ 2 • F)) + h ^ 2 • F := by simp only [z]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh2.le]
    nlinarith [mul_le_mul_of_nonneg_left hF hh2.le]
  have hz1 : ‖z‖ < 1 := by linarith
  have hlog := TransportPlaquetteConsistency.norm_logOneAdd_sub_le hz1
  have hlog' : ‖logOneAdd z - z‖ ≤ 2 * (N * h ^ 2 + C * h ^ 3) ^ 2 := by
    refine hlog.trans ?_
    rw [div_le_iff₀ (by linarith)]
    have : ‖z‖ ^ 2 ≤ (N * h ^ 2 + C * h ^ 3) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
    nlinarith [norm_nonneg z]
  have e : (h ^ 2)⁻¹ • logOneAdd z - F =
      (h ^ 2)⁻¹ • ((logOneAdd z - z) + (Pq - (1 + h ^ 2 • F))) := by
    simp only [z, smul_add, smul_sub, smul_smul, inv_mul_cancel₀ hh2.ne', one_smul]
    abel
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hh2), inv_mul_le_iff₀ hh2]
  have hsum := (norm_add_le _ _).trans (add_le_add hlog' hP)
  refine hsum.trans (le_of_eq ?_)
  ring

/-! ### Smooth reconstructed fields: local Taylor bound -/

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Local first-order Taylor bound** on a convex set `S`: if `f` has derivative `f'` on `S`
and `f'` is `L`-Lipschitz on `S`, then `‖f(x+u) - f(x) - f'(x)u‖ ≤ L‖u‖²` for `x, x+u ∈ S`. -/
theorem norm_sub_sub_fderiv_le_on {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {S : Set E} (hS : Convex ℝ S) {f : E → G} {f' : E → E →L[ℝ] G} {L : ℝ}
    (hf : ∀ y ∈ S, HasFDerivAt f (f' y) y) (hL : ∀ y ∈ S, ∀ z ∈ S, ‖f' y - f' z‖ ≤ L * ‖y - z‖)
    {x u : E} (hx : x ∈ S) (hxu : x + u ∈ S) :
    ‖f (x + u) - f x - f' x u‖ ≤ L * ‖u‖ ^ 2 := by
  have hseg : segment ℝ x (x + u) ⊆ S := hS.segment_subset hx hxu
  have hL0 : 0 ≤ L ∨ u = 0 := by
    by_cases hu : u = 0
    · exact Or.inr hu
    · left
      have := (norm_nonneg _).trans (hL (x + u) hxu x hx)
      rw [add_sub_cancel_left] at this
      exact nonneg_of_mul_nonneg_left this (norm_pos_iff.2 hu)
  rcases hL0 with hL0 | hu
  swap
  · subst hu; simp
  set g : E → G := fun y => f y - f' x (y - x)
  have hg : ∀ y ∈ segment ℝ x (x + u),
      HasFDerivWithinAt g (f' y - f' x) (segment ℝ x (x + u)) y := by
    intro y hy
    have h2 : HasFDerivAt (fun y => f' x (y - x)) (f' x) y :=
      ((f' x).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const x)).congr_fderiv
        (ContinuousLinearMap.comp_id _)
    exact ((hf y (hseg hy)).sub h2).hasFDerivWithinAt
  have hbd : ∀ y ∈ segment ℝ x (x + u), ‖f' y - f' x‖ ≤ L * ‖u‖ := by
    intro y hy
    refine (hL y (hseg hy) x hx).trans (mul_le_mul_of_nonneg_left ?_ hL0)
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
    have : a • x + b • (x + u) - x = b • u := by
      rw [show a = 1 - b by linarith]; module
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
  have := (convex_segment x (x + u)).norm_image_sub_le_of_norm_hasFDerivWithin_le hg hbd
    (left_mem_segment ℝ x (x + u)) (right_mem_segment ℝ x (x + u))
  simp only [g, add_sub_cancel_left, sub_self, map_zero, sub_zero] at this
  calc ‖f (x + u) - f x - f' x u‖ = ‖f (x + u) - f' x u - f x‖ := by congr 1; abel
    _ ≤ L * ‖u‖ * ‖u‖ := this
    _ = L * ‖u‖ ^ 2 := by ring

/-- Taylor remainder along an edge `x ↦ x + h e` (`‖e‖ ≤ 1`) in the band normalisation:
`‖f(x+he) - f(x) - h f'(x)e‖ ≤ cB²h²`. -/
theorem norm_edge_taylor_le {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {S : Set E} (hS : Convex ℝ S) {f : E → G} {f' : E → E →L[ℝ] G} {c B h : ℝ}
    (hf : ∀ y ∈ S, HasFDerivAt f (f' y) y)
    (hL : ∀ y ∈ S, ∀ z ∈ S, ‖f' y - f' z‖ ≤ c * B ^ 2 * ‖y - z‖) (hc : 0 ≤ c) {x e : E}
    (he : ‖e‖ ≤ 1) (hh : 0 ≤ h) (hx : x ∈ S) (hxe : x + h • e ∈ S) :
    ‖f (x + h • e) - f x - h • f' x e‖ ≤ c * B ^ 2 * h ^ 2 := by
  have := norm_sub_sub_fderiv_le_on hS hf hL hx hxe
  rw [map_smul] at this
  refine this.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh, mul_pow]
  have : ‖e‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) he
  nlinarith [sq_nonneg h]

/-- `‖T e‖ ≤ a` for `‖T‖ ≤ a` and `‖e‖ ≤ 1`. -/
theorem norm_apply_le_of {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {T : E →L[ℝ] G} {e : E} {a : ℝ} (hT : ‖T‖ ≤ a) (he : ‖e‖ ≤ 1) : ‖T e‖ ≤ a :=
  (T.le_opNorm e).trans ((mul_le_mul hT he (norm_nonneg _) ((norm_nonneg _).trans hT)).trans
    (le_of_eq (mul_one a)))

/-- The constant `2c + 2c² + κ(c)` (bound of `‖F‖/B + κ h B` in the logarithm step). -/
def logC (c : ℝ) : ℝ := 2 * c + 2 * c ^ 2 + plaqC c

/-- **The curvature packet constant** `κ(c) + 2 logC(c)²`. -/
def curvC (c : ℝ) : ℝ := plaqC c + 2 * logC c ^ 2

/-- The resolution reserve `c_res(c) = 1/(2(logC(c) + 1))` of `eq:eq-growing-band`. -/
def cRes (c : ℝ) : ℝ := 1 / (2 * (logC c + 1))

theorem logC_nonneg {c : ℝ} (hc : 0 ≤ c) : 0 ≤ logC c := by
  unfold logC; have := plaqC_nonneg hc; positivity

theorem cRes_le_half {c : ℝ} (hc : 0 ≤ c) : cRes c ≤ 1 / 2 := by
  unfold cRes
  have := logC_nonneg hc
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

open ShiftedPlaquette in
/-- **Curvature part of `eq:Wilson-packet-consistency`.**  Let `A_μ, A_ν` be the components of a
reconstructed connection on a convex chart `S`, with the `|α| ≤ 2` part of the growing band
`eq:eq-growing-band`: `‖A‖ ≤ c`, `‖DA‖ ≤ cB`, `DA` is `cB²`-Lipschitz on `S`, `B ≥ 1`,
`0 < h ≤ 1` and `hB ≤ c_res(c)`.  For a node `x` with `x + he_μ, x + he_ν ∈ S`, the literal
logarithmic plaquette of the exponential links `U = e^{hA}`,
`F^h_{μν}(x) = h⁻² log(e^{hA_μ(x)} e^{hA_ν(x+he_μ)} e^{-hA_μ(x+he_ν)} e^{-hA_ν(x)})`, satisfies
`‖F^h_{μν}(x) - F_{A,μν}(x)‖ ≤ curvC(c) · h B²`, `F_{A,μν} = ∂_μA_ν - ∂_νA_μ + [A_μ, A_ν]`. -/
theorem norm_fieldStrength_sub_curvature_le {S : Set E} (hS : Convex ℝ S) {Aμ Aν : E → 𝔸}
    {Aμ' Aν' : E → E →L[ℝ] 𝔸} {c B h : ℝ}
    (hAμ : ∀ y ∈ S, HasFDerivAt Aμ (Aμ' y) y) (hAν : ∀ y ∈ S, HasFDerivAt Aν (Aν' y) y)
    (hKμ : ∀ y ∈ S, ‖Aμ y‖ ≤ c) (hKν : ∀ y ∈ S, ‖Aν y‖ ≤ c)
    (hDμ : ∀ y ∈ S, ‖Aμ' y‖ ≤ c * B) (hDν : ∀ y ∈ S, ‖Aν' y‖ ≤ c * B)
    (hLμ : ∀ y ∈ S, ∀ z ∈ S, ‖Aμ' y - Aμ' z‖ ≤ c * B ^ 2 * ‖y - z‖)
    (hLν : ∀ y ∈ S, ∀ z ∈ S, ‖Aν' y - Aν' z‖ ≤ c * B ^ 2 * ‖y - z‖)
    {eμ eν x : E} (heμ : ‖eμ‖ ≤ 1) (heν : ‖eν‖ ≤ 1) (hx : x ∈ S) (hxμ : x + h • eμ ∈ S)
    (hxν : x + h • eν ∈ S) (hh : 0 < h) (hh1 : h ≤ 1) (hB1 : 1 ≤ B) (hres : h * B ≤ cRes c) :
    ‖(h ^ 2)⁻¹ • logOneAdd (exp (h • Aμ x) * exp (h • Aν (x + h • eμ)) *
        exp (-(h • Aμ (x + h • eν))) * exp (-(h • Aν x)) - 1) -
      (Aν' x eμ - Aμ' x eν + (Aμ x * Aν x - Aν x * Aμ x))‖ ≤ curvC c * h * B ^ 2 := by
  have hc : 0 ≤ c := (norm_nonneg _).trans (hKμ x hx)
  have hB0 : 0 ≤ B := by linarith
  have hhB : h * B ≤ 1 := hres.trans ((cRes_le_half hc).trans (by norm_num))
  set X := Aμ x
  set Y := Aν x
  set r := Aν' x eμ
  set s := Aμ' x eν
  set R₂ := Aν (x + h • eμ) - Y - h • r
  set R₃ := Aμ (x + h • eν) - X - h • s
  have hR₂ : ‖R₂‖ ≤ c * B ^ 2 * h ^ 2 := norm_edge_taylor_le hS hAν hLν hc heμ hh.le hx hxμ
  have hR₃ : ‖R₃‖ ≤ c * B ^ 2 * h ^ 2 := norm_edge_taylor_le hS hAμ hLμ hc heν hh.le hx hxν
  have eY : Aν (x + h • eμ) = Y + h • r + R₂ := by simp only [R₂]; abel
  have eX : Aμ (x + h • eν) = X + h • s + R₃ := by simp only [R₃]; abel
  rw [eY, eX]
  have hP := norm_expPlaquette_sub_le hh.le hh1 hB1 hhB (hKμ x hx) (hKν x hx)
    (norm_apply_le_of (hDν x hx) heμ) (norm_apply_le_of (hDμ x hx) heν) hR₂ hR₃
  have hF : ‖r - s + (X * Y - Y * X)‖ ≤ (2 * c + 2 * c ^ 2) * B := by
    have a1 := norm_apply_le_of (hDν x hx) heμ
    have a2 := norm_apply_le_of (hDμ x hx) heν
    have a3 : ‖X * Y‖ ≤ c * c := (norm_mul_le _ _).trans
      (mul_le_mul (hKμ x hx) (hKν x hx) (norm_nonneg _) hc)
    have a4 : ‖Y * X‖ ≤ c * c := (norm_mul_le _ _).trans
      (mul_le_mul (hKν x hx) (hKμ x hx) (norm_nonneg _) hc)
    have b1 := norm_add_le (r - s) (X * Y - Y * X)
    have b2 := norm_sub_le r s
    have b3 := norm_sub_le (X * Y) (Y * X)
    have b4 : c ^ 2 ≤ c ^ 2 * B := le_mul_of_one_le_right (sq_nonneg c) hB1
    have b5 : c * c = c ^ 2 := by ring
    calc ‖r - s + (X * Y - Y * X)‖ ≤ (c * B + c * B) + (c * c + c * c) := by linarith
      _ ≤ (2 * c + 2 * c ^ 2) * B := by nlinarith
  have hpl := plaqC_nonneg hc
  have hP' : ‖exp (h • X) * exp (h • (Y + h • r + R₂)) * exp (-(h • (X + h • s + R₃))) *
      exp (-(h • Y)) - (1 + h ^ 2 • (r - s + (X * Y - Y * X)))‖ ≤ (plaqC c * B ^ 2) * h ^ 3 := by
    simpa only [mul_assoc] using hP
  have hlc := logC_nonneg hc
  have hsmall : (2 * c + 2 * c ^ 2) * B * h ^ 2 + plaqC c * B ^ 2 * h ^ 3 ≤ 1 / 2 := by
    have e : (2 * c + 2 * c ^ 2) * B * h ^ 2 + plaqC c * B ^ 2 * h ^ 3 =
        h * (h * B) * ((2 * c + 2 * c ^ 2) + plaqC c * (h * B)) := by ring
    rw [e]
    have hhB0 : 0 ≤ h * B := by positivity
    have k1 : (2 * c + 2 * c ^ 2) + plaqC c * (h * B) ≤ logC c := by
      unfold logC
      have : plaqC c * (h * B) ≤ plaqC c := mul_le_of_le_one_right hpl hhB
      linarith
    have k2 : h * (h * B) ≤ cRes c := by
      calc h * (h * B) ≤ 1 * (h * B) := mul_le_mul_of_nonneg_right hh1 hhB0
        _ ≤ cRes c := by rw [one_mul]; exact hres
    have k3 : cRes c * logC c ≤ 1 / 2 := by
      unfold cRes
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    calc h * (h * B) * ((2 * c + 2 * c ^ 2) + plaqC c * (h * B)) ≤ cRes c * logC c :=
          mul_le_mul k2 k1 (by positivity) (by unfold cRes; positivity)
      _ ≤ 1 / 2 := k3
  have hlog := norm_logPlaquette_sub_le_sharp hh hF hP' hsmall
  refine hlog.trans ?_
  have hNC : (2 * c + 2 * c ^ 2) * B + plaqC c * B ^ 2 * h ≤ logC c * B := by
    unfold logC
    have : plaqC c * B ^ 2 * h ≤ plaqC c * B := by
      have e2 : plaqC c * B ^ 2 * h = plaqC c * B * (h * B) := by ring
      rw [e2]
      exact mul_le_of_le_one_right (by positivity) hhB
    nlinarith
  have hsq : ((2 * c + 2 * c ^ 2) * B + plaqC c * B ^ 2 * h) ^ 2 ≤ (logC c * B) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hNC 2
  have hh2 : h ^ 2 ≤ h := by nlinarith
  calc plaqC c * B ^ 2 * h + 2 * ((2 * c + 2 * c ^ 2) * B + plaqC c * B ^ 2 * h) ^ 2 * h ^ 2
      ≤ plaqC c * B ^ 2 * h + 2 * (logC c * B) ^ 2 * h := by
        have := mul_le_mul hsq hh2 (by positivity) (by positivity)
        nlinarith
    _ = curvC c * h * B ^ 2 := by unfold curvC; ring

/-! ### The Higgs packet -/

/-- **The Higgs packet constant** `(c³eᶜ + c²/2)c + c + 2c²`. -/
def higgsC (c : ℝ) : ℝ := (c ^ 3 * Real.exp c + c ^ 2 / 2) * c + c + 2 * c ^ 2

theorem higgsC_nonneg {c : ℝ} (hc : 0 ≤ c) : 0 ≤ higgsC c := by unfold higgsC; positivity

/-- First-order exponential bound `‖e^{hX} - (1 + hX)‖ ≤ (c³eᶜ + c²/2) h²` for `‖X‖ ≤ c`,
`0 ≤ h ≤ 1`. -/
theorem norm_exp_smul_sub_linear_le {𝔅 : Type*} [NormedRing 𝔅] [NormedAlgebra ℝ 𝔅]
    [NormOneClass 𝔅] [CompleteSpace 𝔅] {X : 𝔅} {c h : ℝ} (hX : ‖X‖ ≤ c) (hh : 0 ≤ h)
    (hh1 : h ≤ 1) : ‖exp (h • X) - (1 + h • X)‖ ≤ (c ^ 3 * Real.exp c + c ^ 2 / 2) * h ^ 2 := by
  have hc : 0 ≤ c := (norm_nonneg _).trans hX
  have hq := LogBCH.norm_exp_sub_quadratic_le (h • X)
  have hhX : ‖h • X‖ ≤ c * h := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]; nlinarith
  have e : exp (h • X) - (1 + h • X) =
      (exp (h • X) - (1 + h • X + (1 / 2 : ℝ) • ((h • X) * (h • X)))) +
        (1 / 2 : ℝ) • ((h • X) * (h • X)) := by abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have t1 : ‖h • X‖ ^ 3 * Real.exp ‖h • X‖ ≤ c ^ 3 * Real.exp c * h ^ 2 := by
    have a : ‖h • X‖ ^ 3 ≤ (c * h) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hhX 3
    have b : Real.exp ‖h • X‖ ≤ Real.exp c := Real.exp_le_exp.2 (hhX.trans (by nlinarith))
    have : (c * h) ^ 3 ≤ c ^ 3 * h ^ 2 := by
      have : h ^ 3 ≤ h ^ 2 := by nlinarith
      calc (c * h) ^ 3 = c ^ 3 * h ^ 3 := by ring
        _ ≤ c ^ 3 * h ^ 2 := mul_le_mul_of_nonneg_left this (by positivity)
    calc ‖h • X‖ ^ 3 * Real.exp ‖h • X‖ ≤ (c * h) ^ 3 * Real.exp c :=
          mul_le_mul a b (Real.exp_pos _).le (by positivity)
      _ ≤ c ^ 3 * h ^ 2 * Real.exp c := mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
      _ = c ^ 3 * Real.exp c * h ^ 2 := by ring
  have t2 : ‖(1 / 2 : ℝ) • ((h • X) * (h • X))‖ ≤ c ^ 2 / 2 * h ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have := (norm_mul_le (h • X) (h • X)).trans
      (mul_le_mul hhX hhX (norm_nonneg _) (by positivity))
    nlinarith
  have := add_le_add (hq.trans t1) t2
  linarith

/-- **Higgs part of `eq:Wilson-packet-consistency`.**  Let `X = dρ_H(A_μ(x))` be the represented
connection at the node (`‖X‖ ≤ c`), so that the represented link is `ρ_H(U_μ(x)) = e^{hX}`, and
let `H` be the reconstructed Higgs field on a convex chart `S` with the growing band
`‖H‖ ≤ c`, `‖DH‖ ≤ cB`, `DH` `cB²`-Lipschitz, `B ≥ 1`, `0 < h ≤ 1`.  Then the literal Higgs
packet `K^h_μ(x) = h⁻¹(ρ_H(U_μ(x))H(x+he_μ) - H(x))` satisfies
`‖K^h_μ(x) - D_{A,μ}H(x)‖ ≤ higgsC(c) · h B²`, `D_{A,μ}H = ∂_μH + dρ_H(A_μ)H`. -/
theorem norm_higgsPacket_sub_covDeriv_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] [Nontrivial F] {S : Set E} (hS : Convex ℝ S) {X : F →L[ℝ] F} {H : E → F}
    {H' : E → E →L[ℝ] F} {c B h : ℝ} (hX : ‖X‖ ≤ c) (hH : ∀ y ∈ S, HasFDerivAt H (H' y) y)
    (hHc : ∀ y ∈ S, ‖H y‖ ≤ c) (hH'c : ∀ y ∈ S, ‖H' y‖ ≤ c * B)
    (hHL : ∀ y ∈ S, ∀ z ∈ S, ‖H' y - H' z‖ ≤ c * B ^ 2 * ‖y - z‖) {e x : E} (he : ‖e‖ ≤ 1)
    (hx : x ∈ S) (hxe : x + h • e ∈ S) (hh : 0 < h) (hh1 : h ≤ 1) (hB1 : 1 ≤ B) :
    ‖h⁻¹ • (exp (h • X) (H (x + h • e)) - H x) - (H' x e + X (H x))‖ ≤
      higgsC c * h * B ^ 2 := by
  have hc : 0 ≤ c := (norm_nonneg _).trans hX
  have hB0 : 0 ≤ B := by linarith
  have hU := norm_exp_smul_sub_linear_le hX hh.le hh1
  have hT := norm_edge_taylor_le hS hH hHL hc he hh.le hx hxe
  have := TransportPlaquetteConsistency.norm_covariantForwardDifference_sub_le hh hh1 hU hT
    (hHc _ hxe)
  refine this.trans ?_
  have a1 : ‖H' x e‖ ≤ c * B := norm_apply_le_of (hH'c x hx) he
  have hBB : B ≤ B ^ 2 := by nlinarith
  have hB2 : 1 ≤ B ^ 2 := by nlinarith
  have k : (c ^ 3 * Real.exp c + c ^ 2 / 2) * c + c * B ^ 2 + ‖X‖ * (‖H' x e‖ + c * B ^ 2) ≤
      higgsC c * B ^ 2 := by
    unfold higgsC
    have t1 : (c ^ 3 * Real.exp c + c ^ 2 / 2) * c ≤
        (c ^ 3 * Real.exp c + c ^ 2 / 2) * c * B ^ 2 :=
      le_mul_of_one_le_right (by positivity) hB2
    have t2 : ‖X‖ * (‖H' x e‖ + c * B ^ 2) ≤ c * (c * B ^ 2 + c * B ^ 2) := by
      refine mul_le_mul hX ?_ (by positivity) hc
      have : c * B ≤ c * B ^ 2 := mul_le_mul_of_nonneg_left hBB hc
      linarith
    nlinarith
  calc ((c ^ 3 * Real.exp c + c ^ 2 / 2) * c + c * B ^ 2 + ‖X‖ * (‖H' x e‖ + c * B ^ 2)) * h
      ≤ higgsC c * B ^ 2 * h := mul_le_mul_of_nonneg_right k hh.le
    _ = higgsC c * h * B ^ 2 := by ring

end Smooth

/-! ### The literal grid packets of a sampling record -/

section Grid

open ShiftedJetAction (Grid unitVec)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} [NeZero n]

/-- **`eq:Wilson-packet-consistency` for the literal packets of the native action.**
Let the grid record `A : Fin 4 → Grid n → 𝔸` (links `U_μ(x) = e^{hA_μ(x)}`) and `Hg` be the nodal
samples of reconstructed fields `𝒜, ℋ` at positions `p x` (with `p(x + e_ν) ↦ p x + h e_ν`
through the periodic identification: `A μ (x + e_ν) = 𝒜 μ (p x + h e_ν)`), and let the
represented Higgs links be `ρ_H(e^{ha}) = e^{h dρ(a)}`.  Under the `|α| ≤ 2` growing band on a
convex chart `S` containing the nodes and their forward neighbours, `B ≥ 1`, `0 < h ≤ 1`,
`hB ≤ c_res(c)`, every literal curvature and Higgs packet entry satisfies
`‖F^h_{μν}(x) - F_{𝒜,μν}(p x)‖ ≤ curvC(c) h B²` and `‖K^h_μ(x) - D_{𝒜,μ}ℋ(p x)‖ ≤ higgsC(c) h B²`
(here `NativeScaling.fieldStrength` and `NativeScaling.higgsLink` are the packets of
`eq:native-plaquettes`, `eq:native-matter-links`). -/
theorem wilson_packet_consistency {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] [Nontrivial F] {S : Set E} (hS : Convex ℝ S)
    (𝒜 : Fin 4 → E → 𝔸) (𝒜' : Fin 4 → E → E →L[ℝ] 𝔸) (ℋ : E → F) (ℋ' : E → E →L[ℝ] F)
    (dρ : 𝔸 → F →L[ℝ] F) (ρH : 𝔸 → F → F) (A : Fin 4 → Grid n → 𝔸) (Hg : Grid n → F)
    (p : Grid n → E) (e : Fin 4 → E) {c B h : ℝ}
    (h𝒜 : ∀ μ, ∀ y ∈ S, HasFDerivAt (𝒜 μ) (𝒜' μ y) y) (hK : ∀ μ, ∀ y ∈ S, ‖𝒜 μ y‖ ≤ c)
    (hD : ∀ μ, ∀ y ∈ S, ‖𝒜' μ y‖ ≤ c * B)
    (hL : ∀ μ, ∀ y ∈ S, ∀ z ∈ S, ‖𝒜' μ y - 𝒜' μ z‖ ≤ c * B ^ 2 * ‖y - z‖)
    (hℋ : ∀ y ∈ S, HasFDerivAt ℋ (ℋ' y) y) (hHc : ∀ y ∈ S, ‖ℋ y‖ ≤ c)
    (hH'c : ∀ y ∈ S, ‖ℋ' y‖ ≤ c * B) (hHL : ∀ y ∈ S, ∀ z ∈ S, ‖ℋ' y - ℋ' z‖ ≤ c * B ^ 2 * ‖y - z‖)
    (hdρ : ∀ μ x, ‖dρ (A μ x)‖ ≤ c) (hρ : ∀ μ x, ρH (exp (h • A μ x)) = ⇑(exp (h • dρ (A μ x))))
    (he : ∀ μ, ‖e μ‖ ≤ 1) (hp : ∀ x, p x ∈ S) (hpe : ∀ x μ, p x + h • e μ ∈ S)
    (hsA : ∀ μ x, A μ x = 𝒜 μ (p x)) (hsA' : ∀ μ ν x, A μ (x + unitVec n ν) = 𝒜 μ (p x + h • e ν))
    (hsH : ∀ x, Hg x = ℋ (p x)) (hsH' : ∀ x ν, Hg (x + unitVec n ν) = ℋ (p x + h • e ν))
    (hh : 0 < h) (hh1 : h ≤ 1) (hB1 : 1 ≤ B) (hres : h * B ≤ cRes c) :
    (∀ x μ ν, ‖NativeScaling.fieldStrength h A x μ ν -
        (𝒜' ν (p x) (e μ) - 𝒜' μ (p x) (e ν) + (𝒜 μ (p x) * 𝒜 ν (p x) - 𝒜 ν (p x) * 𝒜 μ (p x)))‖ ≤
        curvC c * h * B ^ 2) ∧
    (∀ x μ, ‖NativeScaling.higgsLink h ρH A Hg x μ -
        (ℋ' (p x) (e μ) + dρ (𝒜 μ (p x)) (ℋ (p x)))‖ ≤ higgsC c * h * B ^ 2) := by
  refine ⟨fun x μ ν => ?_, fun x μ => ?_⟩
  · unfold NativeScaling.fieldStrength NativeScaling.gaugePlaquette
    rw [hsA' ν μ x, hsA' μ ν x, hsA μ x, hsA ν x]
    exact norm_fieldStrength_sub_curvature_le hS (h𝒜 μ) (h𝒜 ν) (hK μ) (hK ν) (hD μ) (hD ν)
      (hL μ) (hL ν) (he μ) (he ν) (hp x) (hpe x μ) (hpe x ν) hh hh1 hB1 hres
  · unfold NativeScaling.higgsLink
    rw [hρ, hsH' x μ, hsH x, ← hsA]
    exact norm_higgsPacket_sub_covDeriv_le hS (hdρ μ x) hℋ hHc hH'c hHL (he μ) (hp x) (hpe x μ)
      hh hh1 hB1

end Grid

/-! ### Non-vacuity -/

open Set in

/-- Non-vacuity of the curvature bound: a constant connection on `ℝ` (values in `ℝ`) satisfies all
hypotheses at every admissible mesh. -/
example {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hres : h * 1 ≤ cRes 1) :=
  norm_fieldStrength_sub_curvature_le (𝔸 := ℝ) (S := (univ : Set ℝ)) convex_univ
    (Aμ := fun _ => (1 : ℝ)) (Aν := fun _ => (1 : ℝ)) (Aμ' := fun _ => 0) (Aν' := fun _ => 0)
    (c := 1) (B := 1) (fun y _ => hasFDerivAt_const _ _) (fun y _ => hasFDerivAt_const _ _)
    (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => by simp)
    (fun _ _ _ _ => by simp) (fun _ _ _ _ => by simp) (eμ := (1 : ℝ)) (eν := (1 : ℝ))
    (by simp) (by simp) (mem_univ (0 : ℝ)) (mem_univ _) (mem_univ _) hh hh1 le_rfl hres

open Set in
/-- Non-vacuity of the Higgs bound: the linear Higgs field `H(y) = y` on `[-1,1]` with a constant
represented connection. -/
example {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (X : ℝ →L[ℝ] ℝ) (hX : ‖X‖ ≤ 1) :=
  norm_higgsPacket_sub_covDeriv_le (S := Icc (-1 : ℝ) 1) (convex_Icc _ _) hX
    (H := fun y : ℝ => y) (H' := fun _ => ContinuousLinearMap.id ℝ ℝ) (c := 1) (B := 1)
    (fun y _ => hasFDerivAt_id y) (fun y hy => by simpa [abs_le] using hy)
    (fun _ _ => by simp)
    (fun _ _ _ _ => by simp) (e := (1 : ℝ)) (x := 0) (by simp) (by simp)
    (by simp only [smul_eq_mul, mul_one, zero_add, mem_Icc]; constructor <;> linarith) hh hh1 le_rfl

end RenewalGeometry.WilsonPacket
