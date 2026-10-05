/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.GaugeTheory.WilsonTransportConsistency
import RenewalGeometry.GaugeTheory.TransportPlaquetteConsistency

/-!
# Finite Wilson moduli versus continuum covariant translations (`prop:Wilson-packet-transfer`)

Einstein–SM action-closure manuscript, "Finite Wilson packets and continuum covariant
translations", `prop:Wilson-packet-transfer`, transport clause `eq:Wilson-transport-consistency`
and the consequence `eq:Wilson-finite-screen` ⟹ `eq:Wilson-continuum-screen`: "For a lattice
displacement `s = mh`, replace both endpoint continuum packets by the finite readers and continuum
transport by the open finite link.  The resulting errors are `O(hB_h²)` and `O(ϱhB_h)‖Y^d‖`; the
remaining term is exactly the Wilson difference.  For arbitrary `s` choose `m` with
`|s - mh| ≤ h`.  The growing-band reserve controls the final sub-cell displacement by `O(hB_h²)`."

## Setting

* `𝔅` is a complete normed real algebra with `‖1‖ = 1` acting on the fibre (in the applications
  `𝔅 = End(F)`); `a : E → 𝔅` is the represented reconstructed connection component `ρ(A_μ)`
  along the direction `e = e_μ` (`‖e‖ ≤ 1`), bounded by `K` and `Λ`-Lipschitz (`Λ ≍ B_h` under the
  growing band).
* The finite links are the literal `ρ(U_μ(x)) = e^{h a(x)}`; `openLink a e x h m`
  (`eq:open-finite-link`) is `U(x)U(x+he)⋯U(x+(m-1)he)` for `m ≥ 0` and the inverse ordered
  product for `m < 0`.
* Parallel transport: `forwardLink a e x t = P_{x+te ← x}` (transport of `t ↦ a(x+te)`,
  `TransportPlaquetteConsistency`), `backwardLink a e x t = P_{x ← x+te}`; the manuscript's
  `P^A_{μ,s}(x)` (transport from `x + se` back to `x`) is `covTransport a e x s` for both signs of
  `s`, and `𝒯_{μ,s}Y(x) = covTransport a e x s (Y(x + se))` (`eq:continuum-covariant-translation`).

## Main results

* `norm_openLinkPos_sub_backwardLink_le`: **`eq:Wilson-transport-consistency` in the manuscript's
  orientation**, `‖ρ(𝒰_{μ,m}(x)) - ρ(P^A_{μ,mh}(x))‖ ≤ C ϱ₀ h Λ` (both signs of `m`:
  `norm_prodInv_sub_forwardLink_le`).
* `norm_transfer_pos_le`, `norm_transfer_neg_le` (**pointwise transfer**): for `x` in the cell of a
  node `x₀` and `|s| = mh + r`, `0 ≤ r ≤ h`,
  `‖𝒯_sY(x) - Y(x) - (W_{±m}Y^d(x₀) - Y^d(x₀))‖ ≤ X⁴h(K + 3ΛT)M_Y + X(3L_Y h + 2ε)`
  (`T = ϱ₀ + 2`, `X = e^{KT}`, `M_Y`/`L_Y` the sup/Lipschitz bounds of the continuum packet, `ε` the
  nodal packet consistency of `eq:Wilson-packet-consistency`).
* `eLpNorm_le_of_cellwise` (**cell quadrature**): an `L²(Q)` function bounded by
  `‖G(node x)‖ + η` has norm `≤ (h^d Σ_{nodes}‖G‖²)^{1/2} + η |Q|^{1/2}`.
* `wilson_continuum_screen` (**`eq:Wilson-finite-screen` ⟹ `eq:Wilson-continuum-screen`**).
-/

open NormedSpace Set Filter MeasureTheory Topology
open scoped ENNReal NNReal

noncomputable section

namespace RenewalGeometry.WilsonModulus

open PathOrderedExp TransportPlaquetteConsistency WilsonTransport

variable {𝔅 : Type*} [NormedRing 𝔅] [NormedAlgebra ℝ 𝔅] [NormOneClass 𝔅] [CompleteSpace 𝔅]

/-! ### Exact transports along a coordinate line -/

section Transports

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The forward transport is the value of every transport from `1` on a longer segment. -/
theorem forwardLink_eq_apply {a : E → 𝔅} (hc : Continuous a) {K : ℝ} (hK : ∀ y, ‖a y‖ ≤ K)
    (e x : E) {s t : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) {U : ℝ → 𝔅} (hU0 : U 0 = 1)
    (hU : IsTransport (fun τ => a (x + τ • e)) 0 s U) : forwardLink a e x t = U t := by
  obtain ⟨V, hV0, hV, hVe⟩ := exists_forwardLink hc hK e x ht
  rw [hVe]
  exact transport_unique (K := K) (fun _ _ => hK _) hV (hU.mono le_rfl hts) (by rw [hV0, hU0])
    ⟨ht, le_rfl⟩

theorem norm_forwardLink_le {a : E → 𝔅} (hc : Continuous a) {K : ℝ} (hK : ∀ y, ‖a y‖ ≤ K)
    (e x : E) {t : ℝ} (ht : 0 ≤ t) : ‖forwardLink a e x t‖ ≤ Real.exp (K * t) := by
  obtain ⟨U, hU0, hU, hUe⟩ := exists_forwardLink hc hK e x ht
  rw [hUe]
  have := norm_transport_le (K := K) (fun _ _ => hK _) hU t ⟨ht, le_rfl⟩
  simpa [hU0] using this

theorem norm_backwardLink_le {a : E → 𝔅} (hc : Continuous a) {K : ℝ} (hK : ∀ y, ‖a y‖ ≤ K)
    (e x : E) {t : ℝ} (ht : 0 ≤ t) : ‖backwardLink a e x t‖ ≤ Real.exp (K * t) := by
  obtain ⟨U, hU0, hU, hUe⟩ := exists_backwardLink hc hK e x ht
  rw [hUe]
  have := norm_transport_le (K := K) (fun _ _ => by rw [norm_neg]; exact hK _) hU t ⟨ht, le_rfl⟩
  simpa [hU0] using this

/-- `P_{x ← x+te} P_{x+te ← x} = 1`. -/
theorem backwardLink_mul_forwardLink {a : E → 𝔅} (hc : Continuous a) {K : ℝ}
    (hK : ∀ y, ‖a y‖ ≤ K) (e x : E) {t : ℝ} (ht : 0 ≤ t) :
    backwardLink a e x t * forwardLink a e x t = 1 := by
  obtain ⟨R, hR0, hR, hRe⟩ := exists_backwardLink hc hK e x ht
  obtain ⟨P, hP0, hP, hPe⟩ := exists_forwardLink hc hK e x ht
  rw [hRe, hPe]
  exact reverse_transport_mul (K := K) ht (fun _ _ => hK _) hP hP0 (by simpa using hR) hR0

/-- `P_{x+te ← x} P_{x ← x+te} = 1`. -/
theorem forwardLink_mul_backwardLink {a : E → 𝔅} (hc : Continuous a) {K : ℝ}
    (hK : ∀ y, ‖a y‖ ≤ K) (e x : E) {t : ℝ} (ht : 0 ≤ t) :
    forwardLink a e x t * backwardLink a e x t = 1 := by
  obtain ⟨R, hR0, hR, hRe⟩ := exists_backwardLink hc hK e x ht
  obtain ⟨P, hP0, hP, hPe⟩ := exists_forwardLink hc hK e x ht
  rw [hRe, hPe]
  exact transport_mul_reverse (K := K) ht (fun _ _ => hK _) hP hP0 (by simpa using hR) hR0

/-- **Lipschitz dependence on the length**: `‖P_{x+t'e←x} - P_{x+te←x}‖ ≤ K e^{Kt'} (t' - t)`. -/
theorem norm_forwardLink_sub_length_le {a : E → 𝔅} (hc : Continuous a) {K : ℝ}
    (hK : ∀ y, ‖a y‖ ≤ K) (e x : E) {t t' : ℝ} (ht : 0 ≤ t) (htt : t ≤ t') :
    ‖forwardLink a e x t' - forwardLink a e x t‖ ≤ K * Real.exp (K * t') * (t' - t) := by
  obtain ⟨U, hU0, hU, hUe⟩ := exists_forwardLink hc hK e x (ht.trans htt)
  rw [hUe, forwardLink_eq_apply hc hK e x ht htt hU0 hU]
  have := norm_transport_sub_le_lipschitz (K := K) (fun _ _ => hK _) hU ⟨ht, htt⟩
    ⟨ht.trans htt, le_rfl⟩
  rw [hU0, norm_one, mul_one, sub_zero, abs_of_nonneg (by linarith)] at this
  exact this

/-- **Lipschitz dependence on the base point**: `‖P_{x+te←x} - P_{y+te←y}‖ ≤ δ t e^{2Kt}` when the
coefficients along the two parallel lines differ by at most `δ`. -/
theorem norm_forwardLink_sub_base_le {a : E → 𝔅} (hc : Continuous a) {K : ℝ}
    (hK : ∀ y, ‖a y‖ ≤ K) (e x y : E) {t δ : ℝ} (ht : 0 ≤ t) (hδ0 : 0 ≤ δ)
    (hδ : ∀ τ ∈ Icc (0 : ℝ) t, ‖a (x + τ • e) - a (y + τ • e)‖ ≤ δ) :
    ‖forwardLink a e x t - forwardLink a e y t‖ ≤ δ * t * Real.exp (2 * K * t) := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK x)
  obtain ⟨U, hU0, hU, hUe⟩ := exists_forwardLink hc hK e x ht
  obtain ⟨V, hV0, hV, hVe⟩ := exists_forwardLink hc hK e y ht
  rw [hUe, hVe]
  have := norm_transport_sub_transport_le (K := K) (fun _ _ => hK _) (fun _ _ => hK _) hδ hU hV
    (by rw [hU0, hV0]) t ⟨ht, le_rfl⟩
  rw [hU0, norm_one, one_mul, sub_zero] at this
  refine this.trans ((gronwallBound_zero_le hK0 (by positivity) ht).trans (le_of_eq ?_))
  rw [show 2 * K * t = K * t + K * t by ring, Real.exp_add]
  ring

/-! ### Open finite links -/

/-- The inverse open link `V_m(x) = U(x+(m-1)he)⁻¹ ⋯ U(x)⁻¹ = e^{-ha(x+(m-1)he)} ⋯ e^{-ha(x)}`. -/
def invLink (a : E → 𝔅) (e x : E) (h : ℝ) (m : ℕ) : 𝔅 :=
  prodUpTo (fun j => exp (h • (-a (x + ((j : ℝ) * h) • e)))) m

/-- The open finite link `𝒰_{μ,m}(x) = U(x)U(x+he)⋯U(x+(m-1)he)`, `U = e^{ha}`
(`eq:open-finite-link`, `m ≥ 0`). -/
def openLinkPos (a : E → 𝔅) (e x : E) (h : ℝ) : ℕ → 𝔅
  | 0 => 1
  | m + 1 => openLinkPos a e x h m * exp (h • a (x + ((m : ℝ) * h) • e))

/-- The open finite link for integer `m` (`eq:open-finite-link`; the inverse ordered product
`U(x-he)⁻¹ ⋯ U(x+mhe)⁻¹` for `m < 0`). -/
def openLink (a : E → 𝔅) (e x : E) (h : ℝ) (m : ℤ) : 𝔅 :=
  if 0 ≤ m then openLinkPos a e x h m.toNat
  else invLink a e (x + ((m : ℝ) * h) • e) h (-m).toNat

theorem exp_smul_mul_exp_neg (X : 𝔅) (h : ℝ) : exp (h • X) * exp (h • -X) = 1 := by
  let +nondep : NormedAlgebra ℚ 𝔅 := .restrictScalars ℚ ℝ 𝔅
  rw [smul_neg, ← exp_add_of_commute (Commute.refl _).neg_right, add_neg_cancel, exp_zero]

theorem exp_smul_neg_mul_exp (X : 𝔅) (h : ℝ) : exp (h • -X) * exp (h • X) = 1 := by
  let +nondep : NormedAlgebra ℚ 𝔅 := .restrictScalars ℚ ℝ 𝔅
  rw [smul_neg, ← exp_add_of_commute (Commute.refl _).neg_left, neg_add_cancel, exp_zero]

/-- `𝒰_m V_m = 1`. -/
theorem openLinkPos_mul_invLink (a : E → 𝔅) (e x : E) (h : ℝ) :
    ∀ m, openLinkPos a e x h m * invLink a e x h m = 1
  | 0 => by simp [openLinkPos, invLink, prodUpTo]
  | m + 1 => by
      have ih := openLinkPos_mul_invLink a e x h m
      simp only [openLinkPos, invLink, prodUpTo] at ih ⊢
      calc openLinkPos a e x h m * exp (h • a (x + ((m : ℝ) * h) • e)) *
            (exp (h • -a (x + ((m : ℝ) * h) • e)) *
              prodUpTo (fun j => exp (h • -a (x + ((j : ℝ) * h) • e))) m)
          = openLinkPos a e x h m * (exp (h • a (x + ((m : ℝ) * h) • e)) *
              exp (h • -a (x + ((m : ℝ) * h) • e))) *
              prodUpTo (fun j => exp (h • -a (x + ((j : ℝ) * h) • e))) m := by noncomm_ring
        _ = 1 := by rw [exp_smul_mul_exp_neg, mul_one, ih]

/-- `V_m 𝒰_m = 1`. -/
theorem invLink_mul_openLinkPos (a : E → 𝔅) (e x : E) (h : ℝ) :
    ∀ m, invLink a e x h m * openLinkPos a e x h m = 1
  | 0 => by simp [openLinkPos, invLink, prodUpTo]
  | m + 1 => by
      have ih := invLink_mul_openLinkPos a e x h m
      simp only [openLinkPos, invLink, prodUpTo] at ih ⊢
      calc exp (h • -a (x + ((m : ℝ) * h) • e)) *
            prodUpTo (fun j => exp (h • -a (x + ((j : ℝ) * h) • e))) m *
            (openLinkPos a e x h m * exp (h • a (x + ((m : ℝ) * h) • e)))
          = exp (h • -a (x + ((m : ℝ) * h) • e)) *
            (prodUpTo (fun j => exp (h • -a (x + ((j : ℝ) * h) • e))) m *
              openLinkPos a e x h m) * exp (h • a (x + ((m : ℝ) * h) • e)) := by noncomm_ring
        _ = 1 := by rw [ih, mul_one, exp_smul_neg_mul_exp]

theorem norm_exp_smul_le {X : 𝔅} {K h : ℝ} (hX : ‖X‖ ≤ K) (hh : 0 ≤ h) :
    ‖exp (h • X)‖ ≤ Real.exp (K * h) := by
  have hT := isTransport_const_exp (-X) 0 h
  have := norm_transport_le (ω := fun _ => -X) (K := K) (fun _ _ => by rwa [norm_neg]) hT h
    ⟨hh, le_rfl⟩
  simpa [norm_neg] using this

theorem norm_openLinkPos_le {a : E → 𝔅} {K : ℝ} (hK : ∀ y, ‖a y‖ ≤ K) (e x : E) {h : ℝ}
    (hh : 0 ≤ h) : ∀ m : ℕ, ‖openLinkPos a e x h m‖ ≤ Real.exp (K * (m * h))
  | 0 => by simp [openLinkPos]
  | m + 1 => by
      have ih := norm_openLinkPos_le hK e x hh m
      simp only [openLinkPos]
      refine (norm_mul_le _ _).trans ((mul_le_mul ih (norm_exp_smul_le (hK _) hh) (norm_nonneg _)
        (Real.exp_pos _).le).trans (le_of_eq ?_))
      rw [← Real.exp_add]; push_cast; ring_nf

theorem norm_invLink_le {a : E → 𝔅} {K : ℝ} (hK : ∀ y, ‖a y‖ ≤ K) (e x : E) {h : ℝ}
    (hh : 0 ≤ h) (m : ℕ) : ‖invLink a e x h m‖ ≤ Real.exp (K * (m * h)) := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK x)
  have := norm_prodUpTo_le (a := fun j => exp (h • (-a (x + ((j : ℝ) * h) • e))))
    (M := Real.exp (K * h)) (fun j => norm_exp_smul_le (by rw [norm_neg]; exact hK _) hh)
    (Real.exp_pos _).le m
  refine this.trans (le_of_eq ?_)
  rw [← Real.exp_nat_mul]; ring_nf

/-- **`eq:Wilson-transport-consistency` (inverse orientation)**: the inverse open link and the
forward transport over `m` edges satisfy `‖V_m(x) - P_{x+mhe←x}‖ ≤ (mh) Λ h e^{K(mh) + 2Kh}`
(`‖e‖ ≤ 1`, `Kh ≤ 1/2`). -/
theorem norm_invLink_sub_forwardLink_le {a : E → 𝔅} {K Λ : ℝ} (hK : ∀ y, ‖a y‖ ≤ K)
    (hΛ0 : 0 ≤ Λ) (hΛ : ∀ y z, ‖a y - a z‖ ≤ Λ * ‖y - z‖) {e : E} (he : ‖e‖ ≤ 1) (x : E)
    {h : ℝ} (hh : 0 ≤ h) (hKh : K * h ≤ 1 / 2) (m : ℕ) :
    ‖invLink a e x h m - forwardLink a e x (m * h)‖ ≤
      (m * h) * Λ * h * Real.exp (K * (m * h) + 2 * K * h) := by
  have hc : Continuous a := continuous_of_norm_sub_le hΛ0 hΛ
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK x)
  obtain ⟨W, hW0, hW, hWe⟩ := exists_forwardLink hc hK e x (by positivity : (0 : ℝ) ≤ m * h)
  rw [hWe]
  exact norm_openLink_sub_continuumTransport_le (ω := fun t => a (x + t • e)) hh hΛ0 hK0
    (fun t => hK _) (fun s t hst => by
      refine (hΛ _ _).trans (mul_le_mul_of_nonneg_left ?_ hΛ0)
      rw [show x + t • e - (x + s • e) = (t - s) • e by module, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by linarith)]
      exact mul_le_of_le_one_right (by linarith) he) hKh m hW hW0

/-- **`eq:Wilson-transport-consistency` in the manuscript's orientation** (`m ≥ 0`):
`‖ρ(𝒰_{μ,m}(x)) - ρ(P^A_{μ,mh}(x))‖ ≤ e^{2K mh} (mh) Λ h e^{K mh + 2Kh}`, i.e. `≤ C ϱ₀ h Λ`
for `mh ≤ ϱ₀`. -/
theorem norm_openLinkPos_sub_backwardLink_le {a : E → 𝔅} {K Λ : ℝ} (hK : ∀ y, ‖a y‖ ≤ K)
    (hΛ0 : 0 ≤ Λ) (hΛ : ∀ y z, ‖a y - a z‖ ≤ Λ * ‖y - z‖) {e : E} (he : ‖e‖ ≤ 1) (x : E)
    {h : ℝ} (hh : 0 ≤ h) (hKh : K * h ≤ 1 / 2) (m : ℕ) :
    ‖openLinkPos a e x h m - backwardLink a e x (m * h)‖ ≤
      Real.exp (2 * K * (m * h)) * ((m * h) * Λ * h * Real.exp (K * (m * h) + 2 * K * h)) := by
  have hc : Continuous a := continuous_of_norm_sub_le hΛ0 hΛ
  have hmh : (0 : ℝ) ≤ m * h := by positivity
  set U := openLinkPos a e x h m
  set V := invLink a e x h m
  set P := backwardLink a e x (m * h)
  set Q := forwardLink a e x (m * h)
  have e1 : U - P = U * (Q - V) * P := by
    have h1 : U * V = 1 := openLinkPos_mul_invLink a e x h m
    have h2 : Q * P = 1 := forwardLink_mul_backwardLink hc hK e x hmh
    calc U - P = U * (Q * P) - (U * V) * P := by rw [h1, h2, mul_one, one_mul]
      _ = U * (Q - V) * P := by noncomm_ring
  rw [e1]
  have hU := norm_openLinkPos_le hK e x hh m
  have hP := norm_backwardLink_le hc hK e x hmh
  have hQV := norm_invLink_sub_forwardLink_le hK hΛ0 hΛ he x hh hKh m
  rw [norm_sub_rev] at hQV
  calc ‖U * (Q - V) * P‖ ≤ ‖U‖ * ‖Q - V‖ * ‖P‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ Real.exp (K * (m * h)) * ((m * h) * Λ * h * Real.exp (K * (m * h) + 2 * K * h)) *
        Real.exp (K * (m * h)) := by gcongr
    _ = _ := by
      rw [show Real.exp (2 * K * (m * h)) = Real.exp (K * (m * h)) * Real.exp (K * (m * h)) by
        rw [← Real.exp_add]; ring_nf]
      ring

end Transports

/-! ### Transport closeness across a cell -/

section Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The horizon `T = ϱ₀ + 2` of the transfer estimates. -/
def horizon (ϱ₀ : ℝ) : ℝ := ϱ₀ + 2

/-- **Transport across a cell**: for base points with `‖x - x₀‖ ≤ 2h`, lengths `mh + r`
(`0 ≤ r ≤ h`, `mh ≤ ϱ₀`), `h ≤ 1`, `Kh ≤ 1/2`:
`‖P_{x+(mh+r)e←x} - V_m(x₀)‖ ≤ h X² (K + 3ΛT)`, `T = ϱ₀ + 2`, `X = e^{KT}`. -/
theorem norm_forwardLink_sub_invLink_le {a : E → 𝔅} {K Λ : ℝ} (hK : ∀ y, ‖a y‖ ≤ K)
    (hΛ0 : 0 ≤ Λ) (hΛ : ∀ y z, ‖a y - a z‖ ≤ Λ * ‖y - z‖) {e : E} (he : ‖e‖ ≤ 1) {x x₀ : E}
    {h r ϱ₀ : ℝ} {m : ℕ} (hx : ‖x - x₀‖ ≤ 2 * h) (hh : 0 ≤ h) (hh1 : h ≤ 1) (hKh : K * h ≤ 1 / 2)
    (hr0 : 0 ≤ r) (hrh : r ≤ h) (hm : m * h ≤ ϱ₀) :
    ‖forwardLink a e x (m * h + r) - invLink a e x₀ h m‖ ≤
      h * Real.exp (K * horizon ϱ₀) ^ 2 * (K + 3 * Λ * horizon ϱ₀) := by
  have hc : Continuous a := continuous_of_norm_sub_le hΛ0 hΛ
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK x)
  have hmh : (0 : ℝ) ≤ m * h := by positivity
  have hϱ : 0 ≤ ϱ₀ := hmh.trans hm
  set T := horizon ϱ₀ with hT
  set X := Real.exp (K * T)
  have hX1 : 1 ≤ X := Real.one_le_exp (mul_nonneg hK0 (by rw [hT]; unfold horizon; linarith))
  have hTnn : 0 ≤ T := by rw [hT]; unfold horizon; linarith
  -- length
  have d1 := norm_forwardLink_sub_length_le hc hK e x hmh (le_add_of_nonneg_right hr0)
  have d1' : ‖forwardLink a e x (m * h + r) - forwardLink a e x (m * h)‖ ≤ K * X * h := by
    refine d1.trans ?_
    have : Real.exp (K * (m * h + r)) ≤ X :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by rw [hT]; unfold horizon; linarith) hK0)
    have e2 : m * h + r - m * h = r := by ring
    rw [e2]
    exact mul_le_mul (mul_le_mul_of_nonneg_left this hK0) hrh hr0 (by positivity)
  -- base point
  have d2 := norm_forwardLink_sub_base_le hc hK e x x₀ hmh (by positivity : 0 ≤ Λ * (2 * h))
    (fun τ _ => (hΛ _ _).trans (by
      rw [show x + τ • e - (x₀ + τ • e) = x - x₀ by abel]
      exact mul_le_mul_of_nonneg_left hx hΛ0))
  have d2' : ‖forwardLink a e x (m * h) - forwardLink a e x₀ (m * h)‖ ≤
      2 * Λ * T * X ^ 2 * h := by
    refine d2.trans ?_
    have : Real.exp (2 * K * (m * h)) ≤ X ^ 2 := by
      rw [← Real.exp_nat_mul]
      exact Real.exp_le_exp.2 (by
        push_cast
        have : m * h ≤ T := by rw [hT]; unfold horizon; linarith
        nlinarith)
    have hmT : m * h ≤ T := by rw [hT]; unfold horizon; linarith
    calc Λ * (2 * h) * (m * h) * Real.exp (2 * K * (m * h)) ≤ Λ * (2 * h) * T * X ^ 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hmT (by positivity)) this (by positivity)
            (by positivity)
      _ = 2 * Λ * T * X ^ 2 * h := by ring
  -- open link
  have d3 := norm_invLink_sub_forwardLink_le hK hΛ0 hΛ he x₀ hh hKh m
  have d3' : ‖forwardLink a e x₀ (m * h) - invLink a e x₀ h m‖ ≤ T * Λ * h * X := by
    rw [norm_sub_rev]
    refine d3.trans ?_
    have hmT : m * h ≤ T := by rw [hT]; unfold horizon; linarith
    have : Real.exp (K * (m * h) + 2 * K * h) ≤ X :=
      Real.exp_le_exp.2 (by rw [hT]; unfold horizon; nlinarith)
    exact mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmT hΛ0) hh) this
      (Real.exp_pos _).le (by positivity)
  have hsplit : forwardLink a e x (m * h + r) - invLink a e x₀ h m =
      (forwardLink a e x (m * h + r) - forwardLink a e x (m * h)) +
        (forwardLink a e x (m * h) - forwardLink a e x₀ (m * h)) +
          (forwardLink a e x₀ (m * h) - invLink a e x₀ h m) := by abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  have hXX : X ≤ X ^ 2 := by nlinarith
  have := add_le_add (add_le_add d1' d2') d3'
  refine this.trans ?_
  have k1 : K * X * h ≤ K * X ^ 2 * h := by
    have := mul_le_mul_of_nonneg_left hXX hK0
    nlinarith
  have k2 : T * Λ * h * X ≤ Λ * T * X ^ 2 * h := by
    have := mul_le_mul_of_nonneg_left hXX (by positivity : 0 ≤ T * Λ * h)
    nlinarith
  nlinarith

/-- The pointwise transfer error `X⁴h(K + 3ΛT)M_Y + X(3L_Y h + 2ε)`. -/
def transErr (K Λ MY LY ε ϱ₀ h : ℝ) : ℝ :=
  Real.exp (K * horizon ϱ₀) ^ 4 * h * (K + 3 * Λ * horizon ϱ₀) * MY +
    Real.exp (K * horizon ϱ₀) * (3 * LY * h + 2 * ε)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [Nontrivial F]

/-- **Pointwise transfer, positive displacement** `s = mh + r`: for `‖x - x₀‖ ≤ h`,
`‖𝒯_sY(x) - Y(x) - (W_mY^d(x₀) - Y^d(x₀))‖ ≤ transErr`, where `𝒯_s Y(x) = P_{x←x+se} Y(x+se)`
and `W_m Y^d(x₀) = 𝒰_m(x₀) Y^d(x₀ + mhe)`. -/
theorem norm_transfer_pos_le {a : E → F →L[ℝ] F} {Y Yd : E → F} {K Λ MY LY ε ϱ₀ h r : ℝ}
    {m : ℕ} {e x x₀ : E} (hK : ∀ y, ‖a y‖ ≤ K) (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ y z, ‖a y - a z‖ ≤ Λ * ‖y - z‖) (he : ‖e‖ ≤ 1) (hY : ∀ y, ‖Y y‖ ≤ MY)
    (hLY0 : 0 ≤ LY) (hLY : ∀ y z, ‖Y y - Y z‖ ≤ LY * ‖y - z‖) (hε0 : ‖Yd x₀ - Y x₀‖ ≤ ε)
    (hε1 : ‖Yd (x₀ + (m * h) • e) - Y (x₀ + (m * h) • e)‖ ≤ ε) (hx : ‖x - x₀‖ ≤ h)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (hKh : K * h ≤ 1 / 2) (hr0 : 0 ≤ r) (hrh : r ≤ h)
    (hm : m * h ≤ ϱ₀) :
    ‖backwardLink a e x (m * h + r) (Y (x + (m * h + r) • e)) - Y x -
        (openLinkPos a e x₀ h m (Yd (x₀ + (m * h) • e)) - Yd x₀)‖ ≤
      transErr K Λ MY LY ε ϱ₀ h := by
  have hc : Continuous a := continuous_of_norm_sub_le hΛ0 hΛ
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK x)
  have hmh : (0 : ℝ) ≤ m * h := by positivity
  have hs0 : 0 ≤ m * h + r := by positivity
  have hε : 0 ≤ ε := (norm_nonneg _).trans hε0
  have hMY : 0 ≤ MY := (norm_nonneg _).trans (hY x)
  set T := horizon ϱ₀ with hT
  set X := Real.exp (K * T)
  have hϱ : 0 ≤ ϱ₀ := hmh.trans hm
  have hX1 : 1 ≤ X := Real.one_le_exp (mul_nonneg hK0 (by rw [hT]; unfold horizon; linarith))
  have hTnn : 0 ≤ T := by rw [hT]; unfold horizon; linarith
  set P := backwardLink a e x (m * h + r)
  set Q := forwardLink a e x (m * h + r)
  set U := openLinkPos a e x₀ h m
  set V := invLink a e x₀ h m
  have hPQ : P * Q = 1 := backwardLink_mul_forwardLink hc hK e x hs0
  have hVU : V * U = 1 := invLink_mul_openLinkPos a e x₀ h m
  have hP : ‖P‖ ≤ X := (norm_backwardLink_le hc hK e x hs0).trans
    (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by rw [hT]; unfold horizon; linarith) hK0))
  have hU : ‖U‖ ≤ X := (norm_openLinkPos_le hK e x₀ hh m).trans
    (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by rw [hT]; unfold horizon; linarith) hK0))
  have hQV : ‖Q - V‖ ≤ h * X ^ 2 * (K + 3 * Λ * T) :=
    norm_forwardLink_sub_invLink_le hK hΛ0 hΛ he (x₀ := x₀) (by linarith) hh hh1 hKh hr0 hrh hm
  have hPU : ‖P - U‖ ≤ X ^ 4 * h * (K + 3 * Λ * T) := by
    have e1 : P - U = -(P * (Q - V) * U) := by
      calc P - U = P * (V * U) - (P * Q) * U := by rw [hVU, hPQ, mul_one, one_mul]
        _ = -(P * (Q - V) * U) := by noncomm_ring
    rw [e1, norm_neg]
    calc ‖P * (Q - V) * U‖ ≤ ‖P‖ * ‖Q - V‖ * ‖U‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ X * (h * X ^ 2 * (K + 3 * Λ * T)) * X := by gcongr
      _ = X ^ 4 * h * (K + 3 * Λ * T) := by ring
  set y := x + (m * h + r) • e
  set y₀ := x₀ + (m * h) • e
  have hyy : ‖y - y₀‖ ≤ 2 * h := by
    rw [show y - y₀ = (x - x₀) + r • e by simp only [y, y₀]; module]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0]
    have : r * ‖e‖ ≤ h := (mul_le_of_le_one_right hr0 he).trans hrh
    linarith
  have hid : P (Y y) - Y x - (U (Yd y₀) - Yd x₀) =
      (P - U) (Y y) + U ((Y y - Y y₀) + (Y y₀ - Yd y₀)) + ((Yd x₀ - Y x₀) + (Y x₀ - Y x)) := by
    simp only [ContinuousLinearMap.sub_apply, map_add, map_sub]
    abel
  rw [hid]
  have t1 : ‖(P - U) (Y y)‖ ≤ X ^ 4 * h * (K + 3 * Λ * T) * MY :=
    ((P - U).le_opNorm _).trans (mul_le_mul hPU (hY y) (norm_nonneg _) (by positivity))
  have t2 : ‖U ((Y y - Y y₀) + (Y y₀ - Yd y₀))‖ ≤ X * (LY * (2 * h) + ε) := by
    refine (U.le_opNorm _).trans (mul_le_mul hU ?_ (norm_nonneg _) (by positivity))
    refine (norm_add_le _ _).trans (add_le_add ((hLY _ _).trans
      (mul_le_mul_of_nonneg_left hyy hLY0)) ?_)
    rw [norm_sub_rev]; exact hε1
  have t3 : ‖(Yd x₀ - Y x₀) + (Y x₀ - Y x)‖ ≤ ε + LY * h := by
    refine (norm_add_le _ _).trans (add_le_add hε0 ((hLY _ _).trans ?_))
    rw [norm_sub_rev]; exact mul_le_mul_of_nonneg_left hx hLY0
  have := add_le_add (add_le_add t1 t2) t3
  refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans (this.trans ?_))
  unfold transErr
  rw [← hT]
  have k : ε + LY * h ≤ X * (ε + LY * h) := le_mul_of_one_le_left (by positivity) hX1
  nlinarith

/-- **Pointwise transfer, negative displacement** `s = -(mh + r)`: for `‖x - x₀‖ ≤ h`,
`‖𝒯_sY(x) - Y(x) - (W_{-m}Y^d(x₀) - Y^d(x₀))‖ ≤ transErr`, where
`𝒯_s Y(x) = P_{x←x+se} Y(x+se)` with `P_{x←x+se}` the forward transport from `y = x + se`, and
`W_{-m}Y^d(x₀) = 𝒰_{-m}(x₀) Y^d(x₀ - mhe)`, `𝒰_{-m}(x₀) = V_m(x₀ - mhe)`. -/
theorem norm_transfer_neg_le {a : E → F →L[ℝ] F} {Y Yd : E → F} {K Λ MY LY ε ϱ₀ h r : ℝ}
    {m : ℕ} {e x x₀ : E} (hK : ∀ y, ‖a y‖ ≤ K) (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ y z, ‖a y - a z‖ ≤ Λ * ‖y - z‖) (he : ‖e‖ ≤ 1) (hY : ∀ y, ‖Y y‖ ≤ MY)
    (hLY0 : 0 ≤ LY) (hLY : ∀ y z, ‖Y y - Y z‖ ≤ LY * ‖y - z‖) (hε0 : ‖Yd x₀ - Y x₀‖ ≤ ε)
    (hε1 : ‖Yd (x₀ - (m * h) • e) - Y (x₀ - (m * h) • e)‖ ≤ ε) (hx : ‖x - x₀‖ ≤ h)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (hKh : K * h ≤ 1 / 2) (hr0 : 0 ≤ r) (hrh : r ≤ h)
    (hm : m * h ≤ ϱ₀) :
    ‖forwardLink a e (x - (m * h + r) • e) (m * h + r) (Y (x - (m * h + r) • e)) - Y x -
        (invLink a e (x₀ - (m * h) • e) h m (Yd (x₀ - (m * h) • e)) - Yd x₀)‖ ≤
      transErr K Λ MY LY ε ϱ₀ h := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK x)
  have hmh : (0 : ℝ) ≤ m * h := by positivity
  have hε : 0 ≤ ε := (norm_nonneg _).trans hε0
  have hMY : 0 ≤ MY := (norm_nonneg _).trans (hY x)
  set T := horizon ϱ₀ with hT
  set X := Real.exp (K * T)
  have hϱ : 0 ≤ ϱ₀ := hmh.trans hm
  have hX1 : 1 ≤ X := Real.one_le_exp (mul_nonneg hK0 (by rw [hT]; unfold horizon; linarith))
  have hTnn : 0 ≤ T := by rw [hT]; unfold horizon; linarith
  set y := x - (m * h + r) • e
  set y₀ := x₀ - (m * h) • e
  have hyy : ‖y - y₀‖ ≤ 2 * h := by
    rw [show y - y₀ = (x - x₀) - r • e by simp only [y, y₀]; module]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0]
    have : r * ‖e‖ ≤ h := (mul_le_of_le_one_right hr0 he).trans hrh
    linarith
  set Q := forwardLink a e y (m * h + r)
  set V := invLink a e y₀ h m
  have hV : ‖V‖ ≤ X := (norm_invLink_le hK e y₀ hh m).trans
    (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by rw [hT]; unfold horizon; linarith) hK0))
  have hQV : ‖Q - V‖ ≤ h * X ^ 2 * (K + 3 * Λ * T) :=
    norm_forwardLink_sub_invLink_le hK hΛ0 hΛ he hyy hh hh1 hKh hr0 hrh hm
  have hx' : x = y + (m * h + r) • e := by simp only [y]; abel
  have hid : Q (Y y) - Y x - (V (Yd y₀) - Yd x₀) =
      (Q - V) (Y y) + V ((Y y - Y y₀) + (Y y₀ - Yd y₀)) + ((Yd x₀ - Y x₀) + (Y x₀ - Y x)) := by
    simp only [ContinuousLinearMap.sub_apply, map_add, map_sub]
    abel
  rw [hid]
  have hX4 : X ^ 2 ≤ X ^ 4 := pow_le_pow_right₀ hX1 (by norm_num)
  have t1 : ‖(Q - V) (Y y)‖ ≤ X ^ 4 * h * (K + 3 * Λ * T) * MY := by
    refine ((Q - V).le_opNorm _).trans (mul_le_mul (hQV.trans ?_) (hY y) (norm_nonneg _)
      (by positivity))
    have : 0 ≤ h * (K + 3 * Λ * T) := by positivity
    nlinarith
  have t2 : ‖V ((Y y - Y y₀) + (Y y₀ - Yd y₀))‖ ≤ X * (LY * (2 * h) + ε) := by
    refine (V.le_opNorm _).trans (mul_le_mul hV ?_ (norm_nonneg _) (by positivity))
    refine (norm_add_le _ _).trans (add_le_add ((hLY _ _).trans
      (mul_le_mul_of_nonneg_left hyy hLY0)) ?_)
    rw [norm_sub_rev]; exact hε1
  have t3 : ‖(Yd x₀ - Y x₀) + (Y x₀ - Y x)‖ ≤ ε + LY * h := by
    refine (norm_add_le _ _).trans (add_le_add hε0 ((hLY _ _).trans ?_))
    rw [norm_sub_rev]; exact mul_le_mul_of_nonneg_left hx hLY0
  have := add_le_add (add_le_add t1 t2) t3
  refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans (this.trans ?_))
  unfold transErr
  rw [← hT]
  have k : ε + LY * h ≤ X * (ε + LY * h) := le_mul_of_one_le_left (by positivity) hX1
  nlinarith

end Pointwise

/-! ### Cells of the lattice `hℤ^ι` and cell quadrature -/

section Cells

variable {ι : Type*} [Fintype ι]

/-- The cell index `⌊x/h⌋ ∈ ℤ^ι` of a point. -/
def cellIdx (h : ℝ) (x : ι → ℝ) : ι → ℤ := fun i => ⌊x i / h⌋

/-- The node `h⌊x/h⌋` of the cell containing `x`. -/
def nodeOf (h : ℝ) (k : ι → ℤ) : ι → ℝ := fun i => h * k i

theorem measurable_cellIdx (h : ℝ) : Measurable (cellIdx (ι := ι) h) :=
  measurable_pi_lambda _ fun i => Int.measurable_floor.comp (by fun_prop)

theorem nodeOf_cellIdx_le {h : ℝ} (hh : 0 < h) (x : ι → ℝ) (i : ι) :
    nodeOf h (cellIdx h x) i ≤ x i ∧ x i < nodeOf h (cellIdx h x) i + h := by
  simp only [nodeOf, cellIdx]
  have h1 := Int.floor_le (x i / h)
  have h2 := Int.lt_floor_add_one (x i / h)
  constructor
  · rw [← le_div_iff₀' hh]; exact h1
  · have : x i < h * (⌊x i / h⌋ + 1) := by rw [← div_lt_iff₀' hh]; exact h2
    linarith

theorem norm_sub_nodeOf_le {h : ℝ} (hh : 0 < h) (x : ι → ℝ) :
    ‖x - nodeOf h (cellIdx h x)‖ ≤ h := by
  refine (pi_norm_le_iff_of_nonneg hh.le).2 fun i => ?_
  obtain ⟨h1, h2⟩ := nodeOf_cellIdx_le hh x i
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  linarith

theorem cellIdx_eq_iff {h : ℝ} (hh : 0 < h) (x : ι → ℝ) (k : ι → ℤ) :
    cellIdx h x = k ↔ x ∈ Set.univ.pi fun i => Ico (h * k i) (h * k i + h) := by
  simp only [Set.mem_univ_pi, mem_Ico, funext_iff, cellIdx, Int.floor_eq_iff]
  refine forall_congr' fun i => ?_
  rw [le_div_iff₀' hh, div_lt_iff₀' hh, mul_add, mul_one]

theorem volume_cell {h : ℝ} (hh : 0 < h) (k : ι → ℤ) :
    volume {x : ι → ℝ | cellIdx h x = k} = ENNReal.ofReal (h ^ Fintype.card ι) := by
  have : {x : ι → ℝ | cellIdx h x = k} = Set.univ.pi fun i => Ico (h * k i) (h * k i + h) := by
    ext x; exact cellIdx_eq_iff hh x k
  rw [this, Real.volume_pi_Ico]
  simp only [add_sub_cancel_left, Finset.prod_const, Finset.card_univ]
  rw [ENNReal.ofReal_pow hh.le]

/-- **Cell quadrature**: for a nonnegative function `φ` of the cell index and a measurable set
`Q` whose cell indices lie in the finite set `S`,
`∫⁻_Q φ(⌊x/h⌋) dx ≤ h^d Σ_{k ∈ S} φ(k)`. -/
theorem setLIntegral_cell_le {h : ℝ} (hh : 0 < h) {Q : Set (ι → ℝ)} (φ : (ι → ℤ) → ℝ≥0∞)
    (S : Finset (ι → ℤ)) (hS : ∀ x ∈ Q, cellIdx h x ∈ S) :
    ∫⁻ x in Q, φ (cellIdx h x) ≤ ENNReal.ofReal (h ^ Fintype.card ι) * ∑ k ∈ S, φ k := by
  have hmeas : ∀ k, MeasurableSet {x : ι → ℝ | cellIdx h x = k} := fun k =>
    measurable_cellIdx h (measurableSet_singleton k)
  calc ∫⁻ x in Q, φ (cellIdx h x)
      ≤ ∫⁻ x in Q, ∑ k ∈ S, {x : ι → ℝ | cellIdx h x = k}.indicator (fun _ => φ k) x := by
        refine setLIntegral_mono_ae ?_ (Eventually.of_forall fun x hx => ?_)
        · exact (Finset.measurable_sum _ fun k _ => (measurable_const.indicator (hmeas k))).aemeasurable
        · rw [Finset.sum_eq_single_of_mem (cellIdx h x) (hS x hx)]
          · simp
          · intro k _ hk
            simp only [Set.indicator_apply_eq_zero, mem_setOf_eq]
            intro hc; exact absurd hc.symm hk
    _ ≤ ∫⁻ x, ∑ k ∈ S, {x : ι → ℝ | cellIdx h x = k}.indicator (fun _ => φ k) x :=
        setLIntegral_le_lintegral _ _
    _ = ∑ k ∈ S, φ k * volume {x : ι → ℝ | cellIdx h x = k} := by
        rw [lintegral_finset_sum _ fun k _ => measurable_const.indicator (hmeas k)]
        refine Finset.sum_congr rfl fun k _ => ?_
        exact lintegral_indicator_const (hmeas k) (φ k)
    _ = ENNReal.ofReal (h ^ Fintype.card ι) * ∑ k ∈ S, φ k := by
        simp only [volume_cell hh, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- **`L²` cell transfer**: if `‖f(x)‖ ≤ ‖G(⌊x/h⌋)‖ + η` on `Q` and the discrete sum
`h^d Σ_{k ∈ S} ‖G(k)‖² ≤ ω²` (all cell indices of `Q` in `S`), then
`‖f‖_{L²(Q)} ≤ ω + η |Q|^{1/2}`. -/
theorem eLpNorm_le_of_cellwise {F : Type*} [NormedAddCommGroup F] {h η ω : ℝ} (hh : 0 < h)
    (hη : 0 ≤ η) (hω : 0 ≤ ω) {Q : Set (ι → ℝ)} (hQ : MeasurableSet Q) {f : (ι → ℝ) → F}
    {G : (ι → ℤ) → F} (S : Finset (ι → ℤ)) (hS : ∀ x ∈ Q, cellIdx h x ∈ S)
    (hf : ∀ x ∈ Q, ‖f x‖ ≤ ‖G (cellIdx h x)‖ + η)
    (hsum : h ^ Fintype.card ι * ∑ k ∈ S, ‖G k‖ ^ 2 ≤ ω ^ 2) :
    eLpNorm f 2 (volume.restrict Q) ≤
      ENNReal.ofReal ω + ENNReal.ofReal η * volume Q ^ (1 / 2 : ℝ) := by
  set g : (ι → ℝ) → ℝ := fun x => ‖G (cellIdx h x)‖
  have hgm : Measurable g := (measurable_of_countable (fun k => ‖G k‖)).comp (measurable_cellIdx h)
  have h1 : eLpNorm f 2 (volume.restrict Q) ≤ eLpNorm (fun x => g x + η) 2 (volume.restrict Q) :=
    eLpNorm_mono_ae_real ((ae_restrict_iff' hQ).2 (Eventually.of_forall hf))
  have h2 := eLpNorm_add_le (μ := volume.restrict Q) (p := 2) hgm.aestronglyMeasurable
    (aestronglyMeasurable_const (b := η)) (by norm_num)
  have h3 : eLpNorm (fun _ => η) 2 (volume.restrict Q) =
      ENNReal.ofReal η * volume Q ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_const' η (by norm_num) (by norm_num), Real.enorm_of_nonneg hη,
      Measure.restrict_apply_univ]
    norm_num
  have h4 : eLpNorm g 2 (volume.restrict Q) ≤ ENNReal.ofReal ω := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    have hint : ∫⁻ x in Q, ‖g x‖ₑ ^ (ENNReal.toReal 2) ≤ ENNReal.ofReal (ω ^ 2) := by
      have e1 : ∀ x, ‖g x‖ₑ ^ (ENNReal.toReal 2) =
          (fun k => ENNReal.ofReal (‖G k‖ ^ 2)) (cellIdx h x) := by
        intro x
        simp only [g, ENNReal.toReal_ofNat]
        rw [Real.enorm_of_nonneg (norm_nonneg _), ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _)
          (by norm_num)]
        norm_cast
      simp_rw [e1]
      refine (setLIntegral_cell_le hh (fun k => ENNReal.ofReal (‖G k‖ ^ 2)) S hS).trans ?_
      rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity), ← ENNReal.ofReal_mul
        (by positivity)]
      exact ENNReal.ofReal_le_ofReal hsum
    calc (∫⁻ x in Q, ‖g x‖ₑ ^ (ENNReal.toReal 2)) ^ (1 / ENNReal.toReal 2)
        ≤ ENNReal.ofReal (ω ^ 2) ^ (1 / ENNReal.toReal 2) :=
          ENNReal.rpow_le_rpow hint (by norm_num)
      _ = ENNReal.ofReal ω := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
        congr 1
        simp only [ENNReal.toReal_ofNat]
        rw [show (1 / 2 : ℝ) = ((2 : ℕ) : ℝ)⁻¹ by norm_num]
        exact Real.pow_rpow_inv_natCast hω (by norm_num)
  calc eLpNorm f 2 (volume.restrict Q) ≤ eLpNorm (fun x => g x + η) 2 (volume.restrict Q) := h1
    _ ≤ eLpNorm g 2 (volume.restrict Q) + eLpNorm (fun _ => η) 2 (volume.restrict Q) := h2
    _ ≤ ENNReal.ofReal ω + ENNReal.ofReal η * volume Q ^ (1 / 2 : ℝ) := by
        rw [h3]; exact add_le_add h4 le_rfl

end Cells

/-! ### The continuum covariant translation and the asymptotic transfer -/

section Screen

/-- The manuscript's transport `P^A_{μ,s}(x)` from `x + se` back to `x`, for both signs of `s`:
`P_{x←x+se}` (backward link) for `s ≥ 0`, and the forward transport from `x + se` to `x` for
`s < 0`. -/
def covTransport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : E → 𝔅) (e x : E)
    (s : ℝ) : 𝔅 :=
  if 0 ≤ s then backwardLink a e x s else forwardLink a e (x + s • e) (-s)

theorem openLink_natCast {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : E → 𝔅)
    (e x : E) (h : ℝ) (m : ℕ) : openLink a e x h (m : ℤ) = openLinkPos a e x h m := by
  simp [openLink]

theorem openLink_neg_natCast {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : E → 𝔅)
    (e x : E) (h : ℝ) (m : ℕ) :
    openLink a e x h (-(m : ℤ)) = invLink a e (x - (m * h) • e) h m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [openLink, openLinkPos, invLink, prodUpTo]
  · have : ¬ (0 ≤ -(m : ℤ)) := by omega
    simp only [openLink, this, if_false, neg_neg, Int.toNat_natCast, Int.cast_neg,
      Int.cast_natCast, neg_mul, neg_smul, ← sub_eq_add_neg]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [Nontrivial F]

/-- The coordinate direction `e_μ`. -/
def coordDir (μ : ι) : ι → ℝ := Pi.single μ 1

theorem norm_coordDir_le (μ : ι) : ‖coordDir μ‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  by_cases hi : i = μ
  · subst hi; simp [coordDir]
  · simp [coordDir, Pi.single_apply, hi]

/-- The constant of the transfer error in the growing-band regime. -/
def screenC (c ϱ₀ : ℝ) : ℝ :=
  Real.exp (c * horizon ϱ₀) ^ 4 * (c + 3 * c * horizon ϱ₀) * c + 5 * c * Real.exp (c * horizon ϱ₀)

theorem transErr_le_band {c B h ϱ₀ : ℝ} (hc : 0 ≤ c) (hB1 : 1 ≤ B) (hh : 0 ≤ h)
    (hϱ : 0 ≤ ϱ₀) :
    transErr c (c * B) (c * B) (c * B ^ 2) (c * h * B ^ 2) ϱ₀ h ≤ screenC c ϱ₀ * (h * B ^ 2) := by
  unfold transErr screenC
  set X := Real.exp (c * horizon ϱ₀)
  set T := horizon ϱ₀
  have hT : 0 ≤ T := by simp only [T, horizon]; linarith
  have hX : 0 ≤ X := (Real.exp_pos _).le
  have hBB : B ≤ B ^ 2 := by nlinarith
  have hB0 : 0 ≤ B := by linarith
  have k1 : X ^ 4 * h * (c + 3 * (c * B) * T) * (c * B) ≤
      X ^ 4 * (c + 3 * c * T) * c * (h * B ^ 2) := by
    have e1 : X ^ 4 * h * (c + 3 * (c * B) * T) * (c * B) =
        X ^ 4 * c * h * (c * B + 3 * c * T * B ^ 2) := by ring
    have e2 : X ^ 4 * (c + 3 * c * T) * c * (h * B ^ 2) =
        X ^ 4 * c * h * (c * B ^ 2 + 3 * c * T * B ^ 2) := by ring
    rw [e1, e2]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := mul_le_mul_of_nonneg_left hBB hc
    linarith
  have k2 : X * (3 * (c * B ^ 2) * h + 2 * (c * h * B ^ 2)) = 5 * c * X * (h * B ^ 2) := by ring
  rw [k2]
  linarith

/-- **`eq:Wilson-finite-screen` ⟹ `eq:Wilson-continuum-screen`** (`prop:Wilson-packet-transfer`,
consequence clause).  Along a sequence of meshes `h_n ↓ 0` with derivative scales `B_n ≥ 1`,
`h_n B_n² → 0`, let `a_n μ = ρ(A_{h_n,μ})` be the represented reconstructed connection
(`‖a‖ ≤ c`, `Lip(a) ≤ cB_n`), `Y_n` a continuum packet (`‖Y_n‖ ≤ cB_n`, `Lip(Y_n) ≤ cB_n²`, as
for `F_{A_h}` and `D_{A_h}H_h` under `eq:eq-growing-band`) and `Y^d_n` the literal finite packet
with the nodal consistency `‖Y^d_n - Y_n‖ ≤ c h_n B_n²` at every node
(`eq:Wilson-packet-consistency`, `wilson_packet_consistency`).  Let `Q` be a bounded measurable
chart whose `(ϱ₀ + 1)`-neighbourhood lies in the chart `Q'` over which the finite Wilson moduli are
summed.  If the finite screen holds (for every `ε` there is `ϱ` such that eventually
`h^d Σ ‖W_{μ,m}Y^d - Y^d‖² ≤ ε²` over every finite set of nodes of `Q'` whose `m`-shift stays in
`Q'`, for all `μ` and `0 < |m|h ≤ ϱ`), then the continuum covariant screen holds on `Q`:
for every `ε` there is `ϱ` with eventually `‖𝒯^{A_n}_{μ,s}Y_n - Y_n‖_{L²(Q)} ≤ ε` for all `μ` and
`|s| ≤ ϱ`. -/
theorem wilson_continuum_screen (hs Bs : ℕ → ℝ) (a : ℕ → ι → (ι → ℝ) → F →L[ℝ] F)
    (Y Yd : ℕ → (ι → ℝ) → F) {c ϱ₀ : ℝ} (hc : 0 ≤ c) (hϱ₀ : 0 < ϱ₀) (hpos : ∀ n, 0 < hs n)
    (hB1 : ∀ n, 1 ≤ Bs n) (hlim : Tendsto (fun n => hs n * Bs n ^ 2) atTop (𝓝 0))
    (hK : ∀ n μ y, ‖a n μ y‖ ≤ c) (hΛ : ∀ n μ y z, ‖a n μ y - a n μ z‖ ≤ c * Bs n * ‖y - z‖)
    (hY : ∀ n y, ‖Y n y‖ ≤ c * Bs n)
    (hLY : ∀ n y z, ‖Y n y - Y n z‖ ≤ c * Bs n ^ 2 * ‖y - z‖)
    (hnod : ∀ n k, ‖Yd n (nodeOf (hs n) k) - Y n (nodeOf (hs n) k)‖ ≤ c * hs n * Bs n ^ 2)
    {Q Q' : Set (ι → ℝ)} (hQ : MeasurableSet Q) (hQb : Bornology.IsBounded Q)
    (hQQ' : ∀ x ∈ Q, ∀ z, ‖z - x‖ ≤ ϱ₀ + 1 → z ∈ Q')
    (hscreen : ∀ ε > 0, ∃ ϱ > 0, ∀ᶠ n in atTop, ∀ μ (m : ℤ), m ≠ 0 → |(m : ℝ)| * hs n ≤ ϱ →
      ∀ S : Finset (ι → ℤ), (∀ k ∈ S, nodeOf (hs n) k ∈ Q' ∧
        nodeOf (hs n) k + ((m : ℝ) * hs n) • coordDir μ ∈ Q') →
      hs n ^ Fintype.card ι * ∑ k ∈ S, ‖openLink (a n μ) (coordDir μ) (nodeOf (hs n) k) (hs n) m
        (Yd n (nodeOf (hs n) k + ((m : ℝ) * hs n) • coordDir μ)) - Yd n (nodeOf (hs n) k)‖ ^ 2 ≤
        ε ^ 2) :
    ∀ ε > 0, ∃ ϱ > 0, ∀ᶠ n in atTop, ∀ μ, ∀ s : ℝ, |s| ≤ ϱ →
      eLpNorm (fun x => covTransport (a n μ) (coordDir μ) x s (Y n (x + s • coordDir μ)) - Y n x)
        2 (volume.restrict Q) ≤ ENNReal.ofReal ε := by
  classical
  intro ε hε
  obtain ⟨ϱ₁, hϱ₁, hev⟩ := hscreen (ε / 2) (by positivity)
  refine ⟨min ϱ₁ ϱ₀, lt_min hϱ₁ hϱ₀, ?_⟩
  -- the mesh tends to zero
  have hh0 : Tendsto hs atTop (𝓝 0) :=
    squeeze_zero (fun n => (hpos n).le) (fun n => le_mul_of_one_le_right (hpos n).le
      (one_le_pow₀ (hB1 n))) hlim
  have hvol : volume Q < ⊤ := hQb.measure_lt_top
  set V : ℝ := (volume Q ^ (1 / 2 : ℝ)).toReal
  have hVe : volume Q ^ (1 / 2 : ℝ) = ENNReal.ofReal V :=
    (ENNReal.ofReal_toReal (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hvol.ne)).symm
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have herr : Tendsto (fun n => screenC c ϱ₀ * (hs n * Bs n ^ 2) * V) atTop (𝓝 0) := by
    simpa using (hlim.const_mul (screenC c ϱ₀)).mul_const V
  obtain ⟨R, hR⟩ := hQb.subset_closedBall 0
  filter_upwards [hev, hh0.eventually (ge_mem_nhds (zero_lt_one : (0 : ℝ) < 1)),
    (hh0.const_mul c).eventually (ge_mem_nhds (by norm_num : (c * 0 : ℝ) < 1 / 2)),
    herr.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < ε / 2))] with n hn h1 h2 h3
  intro μ s hsϱ
  set h := hs n
  set B := Bs n
  set e : ι → ℝ := coordDir μ
  have hhp : 0 < h := hpos n
  have hB : 1 ≤ B := hB1 n
  have hcB : 0 ≤ c * B := by positivity
  have he : ‖e‖ ≤ 1 := norm_coordDir_le μ
  have hKh : c * h ≤ 1 / 2 := h2
  -- the lattice displacement
  set t := |s|
  set m : ℕ := ⌊t / h⌋₊
  set r := t - m * h
  have ht0 : 0 ≤ t := abs_nonneg s
  have hmt : m * h ≤ t := by
    have := Nat.floor_le (div_nonneg ht0 hhp.le)
    rw [le_div_iff₀ hhp] at this; exact this
  have htm : t < m * h + h := by
    have := Nat.lt_floor_add_one (t / h)
    rw [div_lt_iff₀ hhp] at this; linarith
  have hr0 : 0 ≤ r := by simp only [r]; linarith
  have hrh : r ≤ h := by simp only [r]; linarith
  have hst : t = m * h + r := by simp only [r]; ring
  have hmϱ : m * h ≤ ϱ₀ := hmt.trans (hsϱ.trans (min_le_right _ _))
  have hmϱ₁ : m * h ≤ ϱ₁ := hmt.trans (hsϱ.trans (min_le_left _ _))
  -- the finite set of cells meeting `Q`
  set box : Finset (ι → ℤ) := Finset.Icc (fun _ => ⌊-R / h⌋) (fun _ => ⌊R / h⌋)
  set S : Finset (ι → ℤ) := box.filter (fun k => ∃ x ∈ Q, cellIdx h x = k)
  have hS : ∀ x ∈ Q, cellIdx h x ∈ S := by
    intro x hx
    refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨fun i => ?_, fun i => ?_⟩, x, hx, rfl⟩
    · have hxi : |x i| ≤ R := by
        have := hR hx
        rw [Metric.mem_closedBall, dist_zero_right] at this
        exact (norm_le_pi_norm x i).trans this
      exact Int.floor_le_floor (by rw [div_le_div_iff_of_pos_right hhp]; linarith [abs_le.1 hxi])
    · have hxi : |x i| ≤ R := by
        have := hR hx
        rw [Metric.mem_closedBall, dist_zero_right] at this
        exact (norm_le_pi_norm x i).trans this
      exact Int.floor_le_floor (by rw [div_le_div_iff_of_pos_right hhp]; linarith [abs_le.1 hxi])
  have hSnode : ∀ k ∈ S, ∀ (j : ℤ), |(j : ℝ)| * h ≤ ϱ₀ →
      nodeOf h k ∈ Q' ∧ nodeOf h k + ((j : ℝ) * h) • e ∈ Q' := by
    intro k hk j hj
    obtain ⟨x, hx, rfl⟩ := (Finset.mem_filter.1 hk).2
    have hn := norm_sub_nodeOf_le hhp x
    rw [norm_sub_rev] at hn
    refine ⟨hQQ' x hx _ (by linarith), hQQ' x hx _ ?_⟩
    rw [show nodeOf h (cellIdx h x) + ((j : ℝ) * h) • e - x =
      (nodeOf h (cellIdx h x) - x) + ((j : ℝ) * h) • e by abel]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hhp]
    have : |(j : ℝ)| * h * ‖e‖ ≤ ϱ₀ := (mul_le_of_le_one_right (by positivity) he).trans hj
    linarith
  -- the error
  set η := transErr c (c * B) (c * B) (c * B ^ 2) (c * h * B ^ 2) ϱ₀ h
  have hη0 : 0 ≤ η := by
    unfold η transErr horizon; positivity
  have hηV : ENNReal.ofReal η * volume Q ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (ε / 2) := by
    rw [hVe, ← ENNReal.ofReal_mul hη0]
    refine ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_right
      (transErr_le_band hc hB hhp.le hϱ₀.le) hV0).trans h3)
  have hfin : ∀ ω : ℝ, 0 ≤ ω → ω ≤ ε / 2 → ∀ f : (ι → ℝ) → F,
      eLpNorm f 2 (volume.restrict Q) ≤ ENNReal.ofReal ω + ENNReal.ofReal η * volume Q ^ (1 / 2 : ℝ) →
      eLpNorm f 2 (volume.restrict Q) ≤ ENNReal.ofReal ε := by
    intro ω hω hωε f hf
    refine hf.trans ((add_le_add (ENNReal.ofReal_le_ofReal hωε) hηV).trans (le_of_eq ?_))
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    ring_nf
  have hnod' : ∀ k, ‖Yd n (nodeOf h k) - Y n (nodeOf h k)‖ ≤ c * h * B ^ 2 := hnod n
  by_cases hs0 : 0 ≤ s
  · -- positive displacement
    have hts : t = s := abs_of_nonneg hs0
    set G : (ι → ℤ) → F := fun k => openLinkPos (a n μ) e (nodeOf h k) h m
      (Yd n (nodeOf h k + (m * h) • e)) - Yd n (nodeOf h k)
    have hpt : ∀ x ∈ Q, ‖covTransport (a n μ) e x s (Y n (x + s • e)) - Y n x‖ ≤
        ‖G (cellIdx h x)‖ + η := by
      intro x hx
      have hx0 := norm_sub_nodeOf_le hhp x
      have hnode1 : nodeOf h (cellIdx h x) + (m * h) • e =
          nodeOf h (cellIdx h x + m • (Pi.single μ 1 : ι → ℤ)) := by
        funext i; simp only [nodeOf, Pi.add_apply, Pi.smul_apply, e, coordDir, smul_eq_mul]
        by_cases hi : i = μ
        · subst hi; simp; ring
        · simp [hi]
      have hp := norm_transfer_pos_le (a := a n μ) (Y := Y n) (Yd := Yd n) (m := m) (r := r)
        (x₀ := nodeOf h (cellIdx h x)) (x := x) (e := e) (ϱ₀ := ϱ₀) (hK n μ) hcB (hΛ n μ) he
        (hY n) (by positivity) (hLY n) (hnod' _) (by rw [hnode1]; exact hnod' _) hx0 hhp.le h1 hKh
        hr0 hrh hmϱ
      rw [← hst, hts] at hp
      have hcov : covTransport (a n μ) e x s = backwardLink (a n μ) e x s := by
        simp [covTransport, hs0]
      rw [hcov]
      calc _ ≤ ‖G (cellIdx h x)‖ + ‖backwardLink (a n μ) e x s (Y n (x + s • e)) - Y n x -
            G (cellIdx h x)‖ := by
            have := norm_le_insert' (backwardLink (a n μ) e x s (Y n (x + s • e)) - Y n x)
              (G (cellIdx h x))
            linarith [norm_sub_rev (backwardLink (a n μ) e x s (Y n (x + s • e)) - Y n x)
              (G (cellIdx h x))]
        _ ≤ ‖G (cellIdx h x)‖ + η := add_le_add le_rfl hp
    have hsum : h ^ Fintype.card ι * ∑ k ∈ S, ‖G k‖ ^ 2 ≤ (ε / 2) ^ 2 := by
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · have : ∀ k, G k = 0 := fun k => by simp [G, hm0, openLinkPos]
        simp only [this, norm_zero]; norm_num; positivity
      · have := hn μ (m : ℤ) (by exact_mod_cast hmpos.ne') (by
          rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg m)]; exact hmϱ₁) S
          (fun k hk => by
            have := hSnode k hk (m : ℤ) (by
              rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg m)]; exact hmϱ)
            simpa only [Int.cast_natCast] using this)
        simpa only [openLink_natCast, Int.cast_natCast, G] using this
    exact hfin (ε / 2) (by positivity) le_rfl _
      (eLpNorm_le_of_cellwise hhp hη0 (by positivity) hQ S hS hpt hsum)
  · -- negative displacement
    have hs0' : s < 0 := lt_of_not_ge hs0
    have hts : t = -s := abs_of_neg hs0'
    set G : (ι → ℤ) → F := fun k => invLink (a n μ) e (nodeOf h k - (m * h) • e) h m
      (Yd n (nodeOf h k - (m * h) • e)) - Yd n (nodeOf h k)
    have hpt : ∀ x ∈ Q, ‖covTransport (a n μ) e x s (Y n (x + s • e)) - Y n x‖ ≤
        ‖G (cellIdx h x)‖ + η := by
      intro x hx
      have hx0 := norm_sub_nodeOf_le hhp x
      have hnode1 : nodeOf h (cellIdx h x) - (m * h) • e =
          nodeOf h (cellIdx h x - m • (Pi.single μ 1 : ι → ℤ)) := by
        funext i; simp only [nodeOf, Pi.sub_apply, Pi.smul_apply, e, coordDir, smul_eq_mul]
        by_cases hi : i = μ
        · subst hi; simp; ring
        · simp [hi]
      have hp := norm_transfer_neg_le (a := a n μ) (Y := Y n) (Yd := Yd n) (m := m) (r := r)
        (x₀ := nodeOf h (cellIdx h x)) (x := x) (e := e) (ϱ₀ := ϱ₀) (hK n μ) hcB (hΛ n μ) he
        (hY n) (by positivity) (hLY n) (hnod' _) (by rw [hnode1]; exact hnod' _) hx0 hhp.le h1 hKh
        hr0 hrh hmϱ
      rw [← hst, hts] at hp
      have hcov : covTransport (a n μ) e x s = forwardLink (a n μ) e (x - (-s) • e) (-s) := by
        simp only [covTransport, hs0, if_false, neg_smul, sub_neg_eq_add]
      have hxs : x + s • e = x - (-s) • e := by rw [neg_smul, sub_neg_eq_add]
      rw [hcov, hxs]
      calc _ ≤ ‖G (cellIdx h x)‖ + ‖forwardLink (a n μ) e (x - (-s) • e) (-s)
            (Y n (x - (-s) • e)) - Y n x - G (cellIdx h x)‖ := by
            have := norm_le_insert' (forwardLink (a n μ) e (x - (-s) • e) (-s)
              (Y n (x - (-s) • e)) - Y n x) (G (cellIdx h x))
            linarith [norm_sub_rev (forwardLink (a n μ) e (x - (-s) • e) (-s)
              (Y n (x - (-s) • e)) - Y n x) (G (cellIdx h x))]
        _ ≤ ‖G (cellIdx h x)‖ + η := add_le_add le_rfl hp
    have hsum : h ^ Fintype.card ι * ∑ k ∈ S, ‖G k‖ ^ 2 ≤ (ε / 2) ^ 2 := by
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · have : ∀ k, G k = 0 := fun k => by simp [G, hm0, invLink, prodUpTo]
        simp only [this, norm_zero]; norm_num; positivity
      · have := hn μ (-(m : ℤ)) (by simp; omega) (by
          rw [Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg (Nat.cast_nonneg m)]
          exact hmϱ₁) S
          (fun k hk => by
            have := hSnode k hk (-(m : ℤ)) (by
              rw [Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg (Nat.cast_nonneg m)]
              exact hmϱ)
            exact this)
        have e1 : ∀ k, nodeOf h k + (((-(m : ℤ) : ℤ) : ℝ) * h) • coordDir μ =
            nodeOf h k - (m * h) • coordDir μ := by
          intro k; rw [Int.cast_neg, Int.cast_natCast, neg_mul, neg_smul, ← sub_eq_add_neg]
        simp only [openLink_neg_natCast, e1] at this
        exact this
    exact hfin (ε / 2) (by positivity) le_rfl _
      (eLpNorm_le_of_cellwise hhp hη0 (by positivity) hQ S hS hpt hsum)

end Screen

/-! ### Non-vacuity -/

/-- Non-vacuity of `wilson_continuum_screen`: the flat connection with vanishing packets on the
unit chart of `ℝ¹` (meshes `h_n = 1/(n+1)`, `B_n = 1`) satisfies every hypothesis. -/
example : ∀ ε > 0, ∃ ϱ > 0, ∀ᶠ n : ℕ in atTop, ∀ μ : Fin 1, ∀ s : ℝ, |s| ≤ ϱ →
    eLpNorm (fun x => covTransport (fun _ : Fin 1 → ℝ => (0 : ℝ →L[ℝ] ℝ)) (coordDir μ) x s
        ((fun _ : Fin 1 → ℝ => (0 : ℝ)) (x + s • coordDir μ)) - (fun _ : Fin 1 → ℝ => (0 : ℝ)) x)
      2 (volume.restrict (Metric.closedBall (0 : Fin 1 → ℝ) 1)) ≤ ENNReal.ofReal ε :=
  wilson_continuum_screen (fun n : ℕ => 1 / ((n : ℝ) + 1)) (fun _ => 1)
    (fun _ _ _ => (0 : ℝ →L[ℝ] ℝ)) (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)) (c := 0)
    (Q' := univ) le_rfl one_pos (fun n => by positivity) (fun _ => le_rfl)
    (by simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))) (fun _ _ _ => by simp)
    (fun _ _ _ _ => by simp) (fun _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ => by simp)
    measurableSet_closedBall Metric.isBounded_closedBall (fun _ _ _ _ => mem_univ _)
    (fun ε hε => ⟨1, one_pos, Eventually.of_forall fun n μ m _ _ S _ => by simp; positivity⟩)

end RenewalGeometry.WilsonModulus
