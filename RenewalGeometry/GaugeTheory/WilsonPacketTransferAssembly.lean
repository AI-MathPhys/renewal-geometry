/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.GaugeTheory.WilsonPacketConsistency
import RenewalGeometry.GaugeTheory.WilsonModulusTransfer

/-!
# Finite packet and open-link transfer for the literal curvature and Higgs packets

Assembly of `prop:Wilson-packet-transfer` (Einstein–SM action-closure manuscript) for the two
literal packets of `eq:literal-finite-bosonic-packets`:

* the curvature packet `F^h_{μν}(z) = h⁻² log(e^{hA_μ(z)} e^{hA_ν(z+he_μ)} e^{-hA_μ(z+he_ν)}
  e^{-hA_ν(z)})` with the adjoint representation `ρ = Ad`, and continuum packet
  `F_{A,μν} = ∂_μA_ν - ∂_νA_μ + [A_μ, A_ν]`;
* the Higgs packet `K^h_κ(z) = h⁻¹(ρ_H(U_κ(z))H(z+he_κ) - H(z))`, `ρ_H(U_κ) = e^{h a_κ}`
  (`a = dρ_H(A)`), with continuum packet `D_{A,κ}H = ∂_κH + a_κ H`.

The links and packets are those of the nodal record of the reconstructed fields (the
reconstruction interpolates the record), at the nodes `z = h k`, `k ∈ ℤ⁴`, of the coordinate chart.

* `adCLM`, `exp_smul_adCLM_apply`: `exp(h ad X) Z = e^{hX} Z e^{-hX}` (`Ad ∘ exp = exp ∘ ad`).
* `openLinkPos_adCLM_apply`, `invLink_adCLM_apply`: the represented open link of `ρ = Ad` is the
  conjugation by the open link, `ρ(𝒰_m)Y = 𝒰_m Y 𝒰_m⁻¹`, for both signs of `m`.
* `norm_curvature_le`, `norm_curvature_sub_le`: the growing band gives `‖F_A‖ ≤ (2c+2c²)B`,
  `Lip(F_A) ≤ (2c + 4c²)B²`; `norm_covDeriv_le`, `norm_covDeriv_sub_le`: the same for `D_AH`.
* `wilson_packet_transfer_curvature`, `wilson_packet_transfer_higgs`: **`eq:Wilson-finite-screen`
  for the literal packet ⟹ `eq:Wilson-continuum-screen` for its continuum packet**, under
  `eq:eq-growing-band` (`|α| ≤ 2`, global on the chart) and `h B_h² → 0`.
-/

open NormedSpace Set Filter MeasureTheory Topology
open scoped ENNReal NNReal

noncomputable section

namespace RenewalGeometry.WilsonPacketTransfer

open WilsonPacket WilsonModulus TransportPlaquetteConsistency WilsonTransport

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-! ### The adjoint representation -/

/-- `ad X = [X, ·]` as a continuous linear map. -/
def adCLM (X : 𝔸) : 𝔸 →L[ℝ] 𝔸 :=
  ContinuousLinearMap.mul ℝ 𝔸 X - (ContinuousLinearMap.mul ℝ 𝔸).flip X

theorem adCLM_apply (X Z : 𝔸) : adCLM X Z = X * Z - Z * X := by
  simp [adCLM]

theorem adCLM_sub (X Y : 𝔸) : adCLM X - adCLM Y = adCLM (X - Y) := by
  ext Z; simp only [ContinuousLinearMap.sub_apply, adCLM_apply]; noncomm_ring

theorem adCLM_smul (h : ℝ) (X : 𝔸) : adCLM (h • X) = h • adCLM X := by
  ext Z; simp only [ContinuousLinearMap.smul_apply, adCLM_apply, smul_mul_assoc,
    mul_smul_comm, smul_sub]

theorem adCLM_neg (X : 𝔸) : adCLM (-X) = -adCLM X := by
  ext Z; simp only [ContinuousLinearMap.neg_apply, adCLM_apply]; noncomm_ring

theorem norm_adCLM_le (X : 𝔸) : ‖adCLM X‖ ≤ 2 * ‖X‖ := by
  refine (norm_sub_le _ _).trans ?_
  have h1 := ContinuousLinearMap.opNorm_mul_apply_le ℝ 𝔸 X
  have h2 : ‖(ContinuousLinearMap.mul ℝ 𝔸).flip X‖ ≤ ‖X‖ :=
    ((ContinuousLinearMap.mul ℝ 𝔸).flip.le_opNorm X).trans (by
      rw [ContinuousLinearMap.opNorm_flip]
      exact mul_le_of_le_one_left (norm_nonneg _) (ContinuousLinearMap.opNorm_mul_le ℝ 𝔸))
  linarith

/-- **`Ad ∘ exp = exp ∘ ad`**: `exp(ad X) Z = e^X Z e^{-X}`. -/
theorem exp_adCLM_apply (X Z : 𝔸) : exp (adCLM X) Z = exp X * Z * exp (-X) := by
  haveI : Nontrivial 𝔸 := NormOneClass.nontrivial
  let +nondep : NormedAlgebra ℚ (𝔸 →L[ℝ] 𝔸) := .restrictScalars ℚ ℝ (𝔸 →L[ℝ] 𝔸)
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ ℝ 𝔸
  let L : 𝔸 →+* (𝔸 →L[ℝ] 𝔸) :=
    { toFun := ContinuousLinearMap.mul ℝ 𝔸
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp [mul_assoc]
      map_zero' := by simp
      map_add' := fun x y => by simp }
  let R : 𝔸ᵐᵒᵖ →+* (𝔸 →L[ℝ] 𝔸) :=
    { toFun := fun x => (ContinuousLinearMap.mul ℝ 𝔸).flip (MulOpposite.unop x)
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp [mul_assoc]
      map_zero' := by simp
      map_add' := fun x y => by simp }
  have hL : Continuous L := (ContinuousLinearMap.mul ℝ 𝔸).continuous
  have hR : Continuous R :=
    (ContinuousLinearMap.mul ℝ 𝔸).flip.continuous.comp MulOpposite.continuous_unop
  have hsplit : adCLM X = L X + R (MulOpposite.op (-X)) := by
    ext Z; simp [L, R, adCLM_apply, sub_eq_add_neg]
  have hcomm : Commute (L X) (R (MulOpposite.op (-X))) := by
    ext Z; simp [L, R, mul_assoc]
  have e1 : exp (L X) = L (exp X) := (map_exp L hL X).symm
  have e2 : exp (R (MulOpposite.op (-X))) = R (exp (MulOpposite.op (-X))) :=
    (map_exp R hR _).symm
  rw [hsplit, exp_add_of_commute hcomm, e1, e2, exp_op]
  simp [L, R, mul_assoc]

/-- `exp(h ad X) Z = e^{hX} Z e^{-hX}`. -/
theorem exp_smul_adCLM_apply (h : ℝ) (X Z : 𝔸) :
    exp (h • adCLM X) Z = exp (h • X) * Z * exp (h • -X) := by
  rw [← adCLM_smul, exp_adCLM_apply, smul_neg]

section Links

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The represented open link of `ρ = Ad` is conjugation by the open link:
`ρ(𝒰_m(x)) Z = 𝒰_m(x) Z 𝒰_m(x)⁻¹` (`𝒰_m⁻¹ = V_m`). -/
theorem openLinkPos_adCLM_apply (A : E → 𝔸) (e x : E) (h : ℝ) :
    ∀ (m : ℕ) (Z : 𝔸), openLinkPos (fun y => adCLM (A y)) e x h m Z =
      openLinkPos A e x h m * Z * invLink A e x h m
  | 0, Z => by simp [openLinkPos, invLink, prodUpTo]
  | m + 1, Z => by
      simp only [openLinkPos, invLink, prodUpTo, ContinuousLinearMap.mul_apply]
      rw [exp_smul_adCLM_apply, openLinkPos_adCLM_apply A e x h m]
      simp only [invLink, mul_assoc]

/-- For negative displacements: `V_m(x)` represented by `Ad` is conjugation by `V_m(x)`. -/
theorem invLink_adCLM_apply (A : E → 𝔸) (e x : E) (h : ℝ) :
    ∀ (m : ℕ) (Z : 𝔸), invLink (fun y => adCLM (A y)) e x h m Z =
      invLink A e x h m * Z * openLinkPos A e x h m
  | 0, Z => by simp [openLinkPos, invLink, prodUpTo]
  | m + 1, Z => by
      have ih := invLink_adCLM_apply A e x h m
      simp only [invLink, prodUpTo, openLinkPos, ContinuousLinearMap.mul_apply] at ih ⊢
      rw [ih, ← adCLM_neg, ← adCLM_smul, exp_adCLM_apply, ← smul_neg, neg_neg]
      simp only [mul_assoc]

end Links

/-! ### Band bounds for the continuum packets -/

section Band

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Mean value: a derivative bound `‖f'‖ ≤ L` gives `‖f y - f z‖ ≤ L ‖y - z‖`. -/
theorem norm_sub_le_of_fderiv_bound {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → G} {f' : E → E →L[ℝ] G} {L : ℝ} (hf : ∀ y, HasFDerivAt f (f' y) y)
    (hb : ∀ y, ‖f' y‖ ≤ L) (y z : E) : ‖f y - f z‖ ≤ L * ‖y - z‖ :=
  convex_univ.norm_image_sub_le_of_norm_hasFDerivWithin_le (fun x _ => (hf x).hasFDerivWithinAt)
    (fun x _ => hb x) (mem_univ z) (mem_univ y)

/-- The continuum curvature packet `F_{A,μν} = ∂_μA_ν - ∂_νA_μ + [A_μ, A_ν]`. -/
def curv (Aμ Aν : E → 𝔸) (Aμ' Aν' : E → E →L[ℝ] 𝔸) (eμ eν : E) (y : E) : 𝔸 :=
  Aν' y eμ - Aμ' y eν + (Aμ y * Aν y - Aν y * Aμ y)

theorem norm_curv_le {Aμ Aν : E → 𝔸} {Aμ' Aν' : E → E →L[ℝ] 𝔸} {c B : ℝ} (hc : 0 ≤ c)
    (hB1 : 1 ≤ B) (hKμ : ∀ y, ‖Aμ y‖ ≤ c) (hKν : ∀ y, ‖Aν y‖ ≤ c) (hDμ : ∀ y, ‖Aμ' y‖ ≤ c * B)
    (hDν : ∀ y, ‖Aν' y‖ ≤ c * B) {eμ eν : E} (heμ : ‖eμ‖ ≤ 1) (heν : ‖eν‖ ≤ 1) (y : E) :
    ‖curv Aμ Aν Aμ' Aν' eμ eν y‖ ≤ (2 * c + 2 * c ^ 2) * B := by
  unfold curv
  have a1 := norm_apply_le_of (hDν y) heμ
  have a2 := norm_apply_le_of (hDμ y) heν
  have a3 : ‖Aμ y * Aν y‖ ≤ c * c :=
    (norm_mul_le _ _).trans (mul_le_mul (hKμ y) (hKν y) (norm_nonneg _) hc)
  have a4 : ‖Aν y * Aμ y‖ ≤ c * c :=
    (norm_mul_le _ _).trans (mul_le_mul (hKν y) (hKμ y) (norm_nonneg _) hc)
  have b1 := norm_add_le (Aν' y eμ - Aμ' y eν) (Aμ y * Aν y - Aν y * Aμ y)
  have b2 := norm_sub_le (Aν' y eμ) (Aμ' y eν)
  have b3 := norm_sub_le (Aμ y * Aν y) (Aν y * Aμ y)
  have b4 : c ^ 2 ≤ c ^ 2 * B := le_mul_of_one_le_right (sq_nonneg c) hB1
  have b5 : c * c = c ^ 2 := by ring
  nlinarith

theorem norm_curv_sub_le {Aμ Aν : E → 𝔸} {Aμ' Aν' : E → E →L[ℝ] 𝔸} {c B : ℝ} (hc : 0 ≤ c)
    (hB1 : 1 ≤ B) (hAμ : ∀ y, HasFDerivAt Aμ (Aμ' y) y) (hAν : ∀ y, HasFDerivAt Aν (Aν' y) y)
    (hKμ : ∀ y, ‖Aμ y‖ ≤ c) (hKν : ∀ y, ‖Aν y‖ ≤ c) (hDμ : ∀ y, ‖Aμ' y‖ ≤ c * B)
    (hDν : ∀ y, ‖Aν' y‖ ≤ c * B) (hLμ : ∀ y z, ‖Aμ' y - Aμ' z‖ ≤ c * B ^ 2 * ‖y - z‖)
    (hLν : ∀ y z, ‖Aν' y - Aν' z‖ ≤ c * B ^ 2 * ‖y - z‖) {eμ eν : E} (heμ : ‖eμ‖ ≤ 1)
    (heν : ‖eν‖ ≤ 1) (y z : E) :
    ‖curv Aμ Aν Aμ' Aν' eμ eν y - curv Aμ Aν Aμ' Aν' eμ eν z‖ ≤
      (2 * c + 4 * c ^ 2) * B ^ 2 * ‖y - z‖ := by
  set d := ‖y - z‖
  have hd : 0 ≤ d := norm_nonneg _
  have hB0 : 0 ≤ B := by linarith
  have hBB : B ≤ B ^ 2 := by nlinarith
  have lμ := norm_sub_le_of_fderiv_bound hAμ hDμ y z
  have lν := norm_sub_le_of_fderiv_bound hAν hDν y z
  have e : curv Aμ Aν Aμ' Aν' eμ eν y - curv Aμ Aν Aμ' Aν' eμ eν z =
      ((Aν' y - Aν' z) eμ - (Aμ' y - Aμ' z) eν) +
        (((Aμ y - Aμ z) * Aν y + Aμ z * (Aν y - Aν z)) -
          ((Aν y - Aν z) * Aμ y + Aν z * (Aμ y - Aμ z))) := by
    simp only [curv, ContinuousLinearMap.sub_apply, mul_sub, sub_mul]; abel
  rw [e]
  have t1 : ‖(Aν' y - Aν' z) eμ‖ ≤ c * B ^ 2 * d := norm_apply_le_of (hLν y z) heμ
  have t2 : ‖(Aμ' y - Aμ' z) eν‖ ≤ c * B ^ 2 * d := norm_apply_le_of (hLμ y z) heν
  have t3 : ‖(Aμ y - Aμ z) * Aν y + Aμ z * (Aν y - Aν z)‖ ≤ 2 * c ^ 2 * B * d := by
    refine (norm_add_le _ _).trans ?_
    have := (norm_mul_le (Aμ y - Aμ z) (Aν y)).trans
      (mul_le_mul lμ (hKν y) (norm_nonneg _) (by positivity))
    have := (norm_mul_le (Aμ z) (Aν y - Aν z)).trans
      (mul_le_mul (hKμ z) lν (norm_nonneg _) hc)
    nlinarith
  have t4 : ‖(Aν y - Aν z) * Aμ y + Aν z * (Aμ y - Aμ z)‖ ≤ 2 * c ^ 2 * B * d := by
    refine (norm_add_le _ _).trans ?_
    have := (norm_mul_le (Aν y - Aν z) (Aμ y)).trans
      (mul_le_mul lν (hKμ y) (norm_nonneg _) (by positivity))
    have := (norm_mul_le (Aν z) (Aμ y - Aμ z)).trans
      (mul_le_mul (hKν z) lμ (norm_nonneg _) hc)
    nlinarith
  have := (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add t1 t2))
    ((norm_sub_le _ _).trans (add_le_add t3 t4)))
  refine this.trans ?_
  have k : 4 * c ^ 2 * B * d ≤ 4 * c ^ 2 * B ^ 2 * d :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBB (by positivity)) hd
  nlinarith

/-- The continuum covariant Higgs derivative `D_{A,κ}H = ∂_κH + a_κ H`. -/
def covD {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : E → V →L[ℝ] V) (H : E → V)
    (H' : E → E →L[ℝ] V) (e : E) (y : E) : V :=
  H' y e + a y (H y)

theorem norm_covD_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {a : E → V →L[ℝ] V}
    {H : E → V} {H' : E → E →L[ℝ] V} {c B : ℝ} (hc : 0 ≤ c) (hB1 : 1 ≤ B) (ha : ∀ y, ‖a y‖ ≤ c)
    (hH : ∀ y, ‖H y‖ ≤ c) (hH' : ∀ y, ‖H' y‖ ≤ c * B) {e : E} (he : ‖e‖ ≤ 1) (y : E) :
    ‖covD a H H' e y‖ ≤ (c + c ^ 2) * B := by
  unfold covD
  refine (norm_add_le _ _).trans ?_
  have t1 := norm_apply_le_of (hH' y) he
  have t2 : ‖a y (H y)‖ ≤ c * c :=
    ((a y).le_opNorm _).trans (mul_le_mul (ha y) (hH y) (norm_nonneg _) hc)
  have : c ^ 2 ≤ c ^ 2 * B := le_mul_of_one_le_right (sq_nonneg c) hB1
  nlinarith

theorem norm_covD_sub_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a : E → V →L[ℝ] V} {H : E → V} {H' : E → E →L[ℝ] V} {c B : ℝ} (hc : 0 ≤ c) (hB1 : 1 ≤ B)
    (ha : ∀ y, ‖a y‖ ≤ c) (haL : ∀ y z, ‖a y - a z‖ ≤ c * B * ‖y - z‖)
    (hHd : ∀ y, HasFDerivAt H (H' y) y) (hH : ∀ y, ‖H y‖ ≤ c) (hH' : ∀ y, ‖H' y‖ ≤ c * B)
    (hHL : ∀ y z, ‖H' y - H' z‖ ≤ c * B ^ 2 * ‖y - z‖) {e : E} (he : ‖e‖ ≤ 1) (y z : E) :
    ‖covD a H H' e y - covD a H H' e z‖ ≤ (c + 2 * c ^ 2) * B ^ 2 * ‖y - z‖ := by
  set d := ‖y - z‖
  have hd : 0 ≤ d := norm_nonneg _
  have hB0 : 0 ≤ B := by linarith
  have hBB : B ≤ B ^ 2 := by nlinarith
  have lH := norm_sub_le_of_fderiv_bound hHd hH' y z
  have e' : covD a H H' e y - covD a H H' e z =
      (H' y - H' z) e + ((a y - a z) (H y) + a z (H y - H z)) := by
    simp only [covD, ContinuousLinearMap.sub_apply, map_sub]; abel
  rw [e']
  have t1 : ‖(H' y - H' z) e‖ ≤ c * B ^ 2 * d := norm_apply_le_of (hHL y z) he
  have t2 : ‖(a y - a z) (H y)‖ ≤ c * B * d * c :=
    ((a y - a z).le_opNorm _).trans (mul_le_mul (haL y z) (hH y) (norm_nonneg _) (by positivity))
  have t3 : ‖a z (H y - H z)‖ ≤ c * (c * B * d) :=
    ((a z).le_opNorm _).trans (mul_le_mul (ha z) lH (norm_nonneg _) hc)
  have := (norm_add_le _ _).trans (add_le_add t1 ((norm_add_le _ _).trans (add_le_add t2 t3)))
  refine this.trans ?_
  have k : 2 * c ^ 2 * B * d ≤ 2 * c ^ 2 * B ^ 2 * d :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBB (by positivity)) hd
  nlinarith

end Band

/-! ### The assembled transfer for the literal packets -/

section Assembly

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open ShiftedPlaquette in
/-- The literal curvature packet `F^h_{μν}(z)` of the nodal record of `A` (`eq:native-plaquettes`
with `U = e^{hA}`). -/
def litCurv (h : ℝ) (A : ι → (ι → ℝ) → 𝔸) (μ ν : ι) (z : ι → ℝ) : 𝔸 :=
  (h ^ 2)⁻¹ • logOneAdd (exp (h • A μ z) * exp (h • A ν (z + h • coordDir μ)) *
    exp (-(h • A μ (z + h • coordDir ν))) * exp (-(h • A ν z)) - 1)

/-- **`prop:Wilson-packet-transfer` for the literal curvature packet** (`ρ = Ad`).  Along meshes
`h_n ↓ 0` with derivative scales `B_n ≥ 1`, `h_nB_n ≤ c_res(c)` and `h_nB_n² → 0`, let the
reconstructed connections `A_n` obey the `|α| ≤ 2` growing band `‖A‖ ≤ c`, `‖DA‖ ≤ cB_n`,
`Lip(DA) ≤ cB_n²` (`eq:eq-growing-band`).  If the literal curvature packet `F^h_{μν}` of the nodal
record satisfies the finite Wilson screen `eq:Wilson-finite-screen` with the adjoint links
`ρ(𝒰_{κ,m}) = Ad(𝒰_{κ,m})` (`openLinkPos_adCLM_apply`: `ρ(𝒰)Y = 𝒰Y𝒰⁻¹`), then the continuum
packet `F_{A_n,μν}` satisfies the continuum covariant screen `eq:Wilson-continuum-screen` on every
bounded measurable chart `Q` whose `(ϱ₀+1)`-neighbourhood lies in `Q'`. -/
theorem wilson_packet_transfer_curvature (hs Bs : ℕ → ℝ) (A : ℕ → ι → (ι → ℝ) → 𝔸)
    (A' : ℕ → ι → (ι → ℝ) → (ι → ℝ) →L[ℝ] 𝔸) {c ϱ₀ : ℝ} (hc : 0 ≤ c) (hϱ₀ : 0 < ϱ₀)
    (hpos : ∀ n, 0 < hs n) (hB1 : ∀ n, 1 ≤ Bs n) (hres : ∀ n, hs n * Bs n ≤ cRes c)
    (hlim : Tendsto (fun n => hs n * Bs n ^ 2) atTop (𝓝 0))
    (hder : ∀ n μ y, HasFDerivAt (A n μ) (A' n μ y) y) (hK : ∀ n μ y, ‖A n μ y‖ ≤ c)
    (hD : ∀ n μ y, ‖A' n μ y‖ ≤ c * Bs n)
    (hL : ∀ n μ y z, ‖A' n μ y - A' n μ z‖ ≤ c * Bs n ^ 2 * ‖y - z‖) (μ ν : ι)
    {Q Q' : Set (ι → ℝ)} (hQ : MeasurableSet Q) (hQb : Bornology.IsBounded Q)
    (hQQ' : ∀ x ∈ Q, ∀ z, ‖z - x‖ ≤ ϱ₀ + 1 → z ∈ Q')
    (hscreen : ∀ ε > 0, ∃ ϱ > 0, ∀ᶠ n in atTop, ∀ κ (m : ℤ), m ≠ 0 → |(m : ℝ)| * hs n ≤ ϱ →
      ∀ S : Finset (ι → ℤ), (∀ k ∈ S, nodeOf (hs n) k ∈ Q' ∧
        nodeOf (hs n) k + ((m : ℝ) * hs n) • coordDir κ ∈ Q') →
      hs n ^ Fintype.card ι * ∑ k ∈ S, ‖openLink (fun y => adCLM (A n κ y)) (coordDir κ)
        (nodeOf (hs n) k) (hs n) m
          (litCurv (hs n) (A n) μ ν (nodeOf (hs n) k + ((m : ℝ) * hs n) • coordDir κ)) -
        litCurv (hs n) (A n) μ ν (nodeOf (hs n) k)‖ ^ 2 ≤ ε ^ 2) :
    ∀ ε > 0, ∃ ϱ > 0, ∀ᶠ n in atTop, ∀ κ, ∀ s : ℝ, |s| ≤ ϱ →
      eLpNorm (fun x => covTransport (fun y => adCLM (A n κ y)) (coordDir κ) x s
          (curv (A n μ) (A n ν) (A' n μ) (A' n ν) (coordDir μ) (coordDir ν)
            (x + s • coordDir κ)) -
        curv (A n μ) (A n ν) (A' n μ) (A' n ν) (coordDir μ) (coordDir ν) x)
        2 (volume.restrict Q) ≤ ENNReal.ofReal ε := by
  haveI : Nontrivial 𝔸 := NormOneClass.nontrivial
  set C := 2 * c + 4 * c ^ 2 + curvC c
  have hcv : 0 ≤ curvC c := by
    unfold curvC; have := plaqC_nonneg hc; positivity
  have hCc : 2 * c ≤ C := by simp only [C]; nlinarith
  have hC1 : 2 * c + 2 * c ^ 2 ≤ C := by simp only [C]; nlinarith
  have hC2 : 2 * c + 4 * c ^ 2 ≤ C := by simp only [C]; linarith
  have hC3 : curvC c ≤ C := by simp only [C]; nlinarith
  have he : ∀ κ : ι, ‖coordDir κ‖ ≤ 1 := norm_coordDir_le
  refine wilson_continuum_screen hs Bs (fun n κ y => adCLM (A n κ y))
    (fun n => curv (A n μ) (A n ν) (A' n μ) (A' n ν) (coordDir μ) (coordDir ν))
    (fun n => litCurv (hs n) (A n) μ ν) (c := C) (by positivity) hϱ₀ hpos hB1 hlim ?_ ?_ ?_ ?_ ?_
    hQ hQb hQQ' hscreen
  · intro n κ y
    exact (norm_adCLM_le _).trans ((mul_le_mul_of_nonneg_left (hK n κ y) (by norm_num)).trans hCc)
  · intro n κ y z
    rw [adCLM_sub]
    refine (norm_adCLM_le _).trans ?_
    have := norm_sub_le_of_fderiv_bound (hder n κ) (hD n κ) y z
    have hB := hB1 n
    calc 2 * ‖A n κ y - A n κ z‖ ≤ 2 * (c * Bs n * ‖y - z‖) := by linarith
      _ ≤ C * Bs n * ‖y - z‖ := by
          have : 0 ≤ Bs n * ‖y - z‖ := by positivity
          nlinarith
  · intro n y
    exact (norm_curv_le hc (hB1 n) (hK n μ) (hK n ν) (hD n μ) (hD n ν) (he μ) (he ν) y).trans
      (mul_le_mul_of_nonneg_right hC1 (by linarith [hB1 n]))
  · intro n y z
    refine (norm_curv_sub_le hc (hB1 n) (hder n μ) (hder n ν) (hK n μ) (hK n ν) (hD n μ) (hD n ν)
      (hL n μ) (hL n ν) (he μ) (he ν) y z).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2 (by positivity))
      (norm_nonneg _)
  · intro n k
    have hh1 : hs n ≤ 1 := by
      have h1 := hres n
      have h2 := cRes_le_half hc
      nlinarith [hB1 n, hpos n]
    have := norm_fieldStrength_sub_curvature_le (S := univ) convex_univ (fun y _ => hder n μ y)
      (fun y _ => hder n ν y) (fun y _ => hK n μ y) (fun y _ => hK n ν y)
      (fun y _ => hD n μ y) (fun y _ => hD n ν y) (fun y _ z _ => hL n μ y z)
      (fun y _ z _ => hL n ν y z) (he μ) (he ν) (mem_univ (nodeOf (hs n) k)) (mem_univ _)
      (mem_univ _) (hpos n) hh1 (hB1 n) (hres n)
    refine (le_of_eq_of_le ?_ this).trans ?_
    · rfl
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC3 (hpos n).le)
        (by positivity)

/-- The literal Higgs packet `K^h_κ(z) = h⁻¹(e^{h a_κ(z)} H(z + he_κ) - H(z))`
(`eq:native-matter-links`, `ρ_H(U_κ) = e^{h a_κ}`, `a = dρ_H(A)`). -/
def litHiggs {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (h : ℝ) (a : ι → (ι → ℝ) → V →L[ℝ] V) (H : (ι → ℝ) → V) (κ : ι) (z : ι → ℝ) : V :=
  h⁻¹ • (exp (h • a κ z) (H (z + h • coordDir κ)) - H z)

/-- **`prop:Wilson-packet-transfer` for the literal Higgs packet.**  With the represented
connection `a_n = dρ_H(A_n)` (`‖a‖ ≤ c`, `Lip(a) ≤ cB_n`) and the reconstructed Higgs fields
`H_n` under the `|α| ≤ 2` growing band, the finite Wilson screen of the literal Higgs packet
`K^h_κ` (links `ρ_H(U) = e^{ha}`) implies the continuum covariant screen of `D_{A_n,κ}H_n`. -/
theorem wilson_packet_transfer_higgs {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] [Nontrivial V] (hs Bs : ℕ → ℝ) (a : ℕ → ι → (ι → ℝ) → V →L[ℝ] V)
    (H : ℕ → (ι → ℝ) → V) (H' : ℕ → (ι → ℝ) → (ι → ℝ) →L[ℝ] V) {c ϱ₀ : ℝ} (hc : 0 ≤ c)
    (hϱ₀ : 0 < ϱ₀) (hpos : ∀ n, 0 < hs n) (hB1 : ∀ n, 1 ≤ Bs n) (hh1 : ∀ n, hs n ≤ 1)
    (hlim : Tendsto (fun n => hs n * Bs n ^ 2) atTop (𝓝 0))
    (ha : ∀ n κ y, ‖a n κ y‖ ≤ c) (haL : ∀ n κ y z, ‖a n κ y - a n κ z‖ ≤ c * Bs n * ‖y - z‖)
    (hHd : ∀ n y, HasFDerivAt (H n) (H' n y) y) (hH : ∀ n y, ‖H n y‖ ≤ c)
    (hH' : ∀ n y, ‖H' n y‖ ≤ c * Bs n)
    (hHL : ∀ n y z, ‖H' n y - H' n z‖ ≤ c * Bs n ^ 2 * ‖y - z‖) (κ₀ : ι)
    {Q Q' : Set (ι → ℝ)} (hQ : MeasurableSet Q) (hQb : Bornology.IsBounded Q)
    (hQQ' : ∀ x ∈ Q, ∀ z, ‖z - x‖ ≤ ϱ₀ + 1 → z ∈ Q')
    (hscreen : ∀ ε > 0, ∃ ϱ > 0, ∀ᶠ n in atTop, ∀ κ (m : ℤ), m ≠ 0 → |(m : ℝ)| * hs n ≤ ϱ →
      ∀ S : Finset (ι → ℤ), (∀ k ∈ S, nodeOf (hs n) k ∈ Q' ∧
        nodeOf (hs n) k + ((m : ℝ) * hs n) • coordDir κ ∈ Q') →
      hs n ^ Fintype.card ι * ∑ k ∈ S, ‖openLink (a n κ) (coordDir κ) (nodeOf (hs n) k) (hs n) m
          (litHiggs (hs n) (a n) (H n) κ₀ (nodeOf (hs n) k + ((m : ℝ) * hs n) • coordDir κ)) -
        litHiggs (hs n) (a n) (H n) κ₀ (nodeOf (hs n) k)‖ ^ 2 ≤ ε ^ 2) :
    ∀ ε > 0, ∃ ϱ > 0, ∀ᶠ n in atTop, ∀ κ, ∀ s : ℝ, |s| ≤ ϱ →
      eLpNorm (fun x => covTransport (a n κ) (coordDir κ) x s
          (covD (a n κ₀) (H n) (H' n) (coordDir κ₀) (x + s • coordDir κ)) -
        covD (a n κ₀) (H n) (H' n) (coordDir κ₀) x) 2 (volume.restrict Q) ≤ ENNReal.ofReal ε := by
  set C := c + 2 * c ^ 2 + higgsC c
  have hhc : 0 ≤ higgsC c := higgsC_nonneg hc
  have hCc : c ≤ C := by simp only [C]; nlinarith
  have hC1 : c + c ^ 2 ≤ C := by simp only [C]; nlinarith
  have hC2 : c + 2 * c ^ 2 ≤ C := by simp only [C]; linarith
  have hC3 : higgsC c ≤ C := by simp only [C]; nlinarith
  have he : ∀ κ : ι, ‖coordDir κ‖ ≤ 1 := norm_coordDir_le
  refine wilson_continuum_screen hs Bs a (fun n => covD (a n κ₀) (H n) (H' n) (coordDir κ₀))
    (fun n => litHiggs (hs n) (a n) (H n) κ₀) (c := C) (by positivity) hϱ₀ hpos hB1 hlim ?_ ?_ ?_
    ?_ ?_ hQ hQb hQQ' hscreen
  · intro n κ y; exact (ha n κ y).trans hCc
  · intro n κ y z
    refine (haL n κ y z).trans ?_
    have : 0 ≤ Bs n * ‖y - z‖ := by have := hB1 n; positivity
    nlinarith
  · intro n y
    exact (norm_covD_le hc (hB1 n) (ha n κ₀) (hH n) (hH' n) (he κ₀) y).trans
      (mul_le_mul_of_nonneg_right hC1 (by linarith [hB1 n]))
  · intro n y z
    refine (norm_covD_sub_le hc (hB1 n) (ha n κ₀) (haL n κ₀) (hHd n) (hH n) (hH' n) (hHL n)
      (he κ₀) y z).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2 (by positivity))
      (norm_nonneg _)
  · intro n k
    have := norm_higgsPacket_sub_covDeriv_le (S := univ) convex_univ (ha n κ₀ (nodeOf (hs n) k))
      (fun y _ => hHd n y) (fun y _ => hH n y) (fun y _ => hH' n y) (fun y _ z _ => hHL n y z)
      (he κ₀) (mem_univ (nodeOf (hs n) k)) (mem_univ _) (hpos n) (hh1 n) (hB1 n)
    refine (le_of_eq_of_le rfl this).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC3 (hpos n).le) (by positivity)

end Assembly

/-! ### Non-vacuity -/

theorem cRes_zero : cRes 0 = 1 / 2 := by
  simp [cRes, logC, plaqC, k2C, cbbC, cbC, edgeC]

/-- Non-vacuity of `wilson_packet_transfer_curvature`: the flat connection on the unit chart of
`ℝ¹` (meshes `h_n = 1/(2(n+1))`, `B_n = 1`) satisfies every hypothesis. -/
example := wilson_packet_transfer_curvature (𝔸 := ℝ) (ι := Fin 1)
    (fun n : ℕ => 1 / (2 * ((n : ℝ) + 1))) (fun _ => 1) (fun _ _ _ => 0) (fun _ _ _ => 0)
    (c := 0) (ϱ₀ := 1) (Q := Metric.closedBall 0 1) (Q' := univ) le_rfl one_pos
    (fun n => by positivity) (fun _ => le_rfl)
    (fun n => by
      rw [cRes_zero, mul_one, div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith)
    (by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 2)
      simp only [mul_zero] at this
      refine this.congr fun n => ?_
      field_simp)
    (fun _ _ _ => hasFDerivAt_const _ _) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
    (fun _ _ _ _ => by simp) 0 0 measurableSet_closedBall Metric.isBounded_closedBall
    (fun _ _ _ _ => mem_univ _)
    (fun ε hε => ⟨1, one_pos, Eventually.of_forall fun n κ m _ _ S _ => by
      simp [litCurv, ShiftedPlaquette.logOneAdd]; positivity⟩)

end RenewalGeometry.WilsonPacketTransfer
