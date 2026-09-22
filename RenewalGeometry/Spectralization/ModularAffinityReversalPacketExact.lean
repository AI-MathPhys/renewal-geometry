/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Spectralization.FiniteGraphSpectralUniversalityFibreExact
/-!
# Modular affinity of the current fibre and the finite modular-reversal packet

This file covers, for `papers/predictive_spectral_geometry`,

* `lem:supp-zero-affinity` — a divergence-free current whose real affinity
  `a_e = artanh(j_e / c_e)` is an exact one-cochain (`[a] = 0`) vanishes
  (`zero_affinity_class_forces_reversibility`);
* `cor:supp-faithful-modular` — the modular class `[a]` is injective on the
  current fibre, so it determines the directed fluxes `q = c ± j` and the
  stationary rates `k = q / m` (`current_eq_of_affinity_class_eq`,
  `faithful_modular_enrichment`);
* `thm:supp-Tomita` — the six pointwise identities of the edge-reversal
  packet `(J_E, Δ_q, S_q, λ_E, ρ_E)` on `ℓ²(E^or)` and the reversible branch
  `Δ_q = I ↔ q_e = q_{ē}` (`reversalConj_comp_self`,
  `reversalConj_modularOperator_reversalConj`, `modularConjugation_sq`,
  `reversalConj_sourceMul_star_reversalConj`,
  `modularConjugation_sourceMul_star_modularConjugation`,
  `log_modularRatio_eq_two_mul_affinity`, `modularOperator_eq_id_iff`);
* `thm:supp-face-holonomy` — the face holonomy of the modular ratios equals
  `exp(2 F_a(p))` with `F_a(p) = Σ_e ε_{p,e} a_e`, and the descent
  criterion: every face holonomy is trivial iff every face-curvature residual
  vanishes (`faceHolonomy_eq_exp_faceCurvature`, `faceHolonomy_eq_one_iff`).

The oriented edge set `E^or` is modelled by a finite type with an involutive
reversal `bar` and a source map `s`; the terminal map is `t = s ∘ bar`.  All
positivity hypotheses are the paper's (`0 < q_e`, `|j_e| < c_e`).
-/

open Matrix Finset

namespace RenewalGeometry
namespace ModularAffinityReversalPacket

/-! ## The real affinity of a current in the fibre -/

section Affinity

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The real affinity `a_e = artanh(j_e / c_e)` of a current, eq. (supp-affinity). -/
noncomputable def affinity (c j : E → ℝ) : E → ℝ :=
  fun e => Real.artanh (j e / c e)

/-- The admissible current fibre `𝒥(G,c)` (def:supp-current-polytope) for a real
oriented incidence matrix `B`: divergence-free currents strictly inside the
conductance box. -/
def CurrentFibre (B : Matrix V E ℝ) (c : E → ℝ) : Set (E → ℝ) :=
  {j | B *ᵥ j = 0 ∧ ∀ e, |j e| < c e}

/-- A one-cochain is exact when it lies in `Ran Bᵀ`, i.e. its class in
`H¹(G;ℝ) = ℝ^E / Ran Bᵀ` vanishes. -/
def IsExact (B : Matrix V E ℝ) (a : E → ℝ) : Prop :=
  ∃ φ : V → ℝ, a = Bᵀ *ᵥ φ

theorem div_mem_Ioo_of_abs_lt {c j : ℝ} (hj : |j| < c) :
    j / c ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hc : 0 < c := (abs_nonneg j).trans_lt hj
  rw [abs_lt] at hj
  constructor
  · rw [lt_div_iff₀ hc]; linarith
  · rw [div_lt_iff₀ hc]; linarith

/-- Each modular pairing term `a_e j_e` is nonnegative on the fibre. -/
theorem artanh_div_mul_nonneg {c j : ℝ} (hj : |j| < c) :
    0 ≤ Real.artanh (j / c) * j := by
  have hc : 0 < c := (abs_nonneg j).trans_lt hj
  rcases le_total 0 j with h | h
  · exact mul_nonneg (Real.artanh_nonneg (div_nonneg h hc.le)) h
  · have h1 : Real.artanh (j / c) ≤ 0 :=
      Real.artanh_nonpos (div_nonpos_of_nonpos_of_nonneg h hc.le)
    have := mul_nonneg (neg_nonneg.mpr h1) (neg_nonneg.mpr h)
    simpa using this

/-- A vanishing modular pairing term forces the current to vanish. -/
theorem eq_zero_of_artanh_div_mul_eq_zero {c j : ℝ} (hj : |j| < c)
    (h : Real.artanh (j / c) * j = 0) : j = 0 := by
  have hc : 0 < c := (abs_nonneg j).trans_lt hj
  rcases mul_eq_zero.mp h with h0 | h0
  · have hmem := div_mem_Ioo_of_abs_lt hj
    rcases Real.artanh_eq_zero_iff.mp h0 with h1 | h1 | h1
    · exact absurd hmem.1 (not_lt.mpr h1)
    · exact (div_eq_zero_iff.mp h1).resolve_right hc.ne'
    · exact absurd hmem.2 (not_lt.mpr h1)
  · exact h0

/-- `lem:supp-zero-affinity` (Zero affinity class forces reversibility): if
`j ∈ 𝒥(G,c)` is divergence free and its affinity is exact, `[a] = 0`, then
`j = 0`. -/
theorem zero_affinity_class_forces_reversibility (B : Matrix V E ℝ) (c : E → ℝ)
    {j : E → ℝ} (hj : j ∈ CurrentFibre B c) (ha : IsExact B (affinity c j)) :
    j = 0 := by
  obtain ⟨φ, hφ⟩ := ha
  have hpair : ∑ e, affinity c j e * j e = 0 := by
    have h0 : φ ⬝ᵥ (B *ᵥ j) = 0 := by rw [hj.1, dotProduct_zero]
    rw [dotProduct_mulVec, ← mulVec_transpose, ← hφ] at h0
    simpa [dotProduct] using h0
  have hnn : ∀ e ∈ (univ : Finset E), 0 ≤ affinity c j e * j e :=
    fun e _ => artanh_div_mul_nonneg (hj.2 e)
  have hzero := (sum_eq_zero_iff_of_nonneg hnn).mp hpair
  funext e
  exact eq_zero_of_artanh_div_mul_eq_zero (hj.2 e) (hzero e (mem_univ e))

/-- Monotonicity of the affinity: `(a_e - a'_e)(j_e - j'_e) ≥ 0`. -/
theorem artanh_div_sub_mul_sub_nonneg {c j j' : ℝ} (hj : |j| < c) (hj' : |j'| < c) :
    0 ≤ (Real.artanh (j / c) - Real.artanh (j' / c)) * (j - j') := by
  have hc : 0 < c := (abs_nonneg j).trans_lt hj
  have hm := div_mem_Ioo_of_abs_lt hj
  have hm' := div_mem_Ioo_of_abs_lt hj'
  rcases le_total j' j with h | h
  · have h1 : j' / c ≤ j / c := (div_le_div_iff_of_pos_right hc).mpr h
    have h2 := (Real.artanh_le_artanh_iff hm' hm).mpr h1
    exact mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr h)
  · have h1 : j / c ≤ j' / c := (div_le_div_iff_of_pos_right hc).mpr h
    have h2 := (Real.artanh_le_artanh_iff hm hm').mpr h1
    have := mul_nonneg (neg_nonneg.mpr (sub_nonpos.mpr h2)) (neg_nonneg.mpr (sub_nonpos.mpr h))
    rw [neg_mul_neg] at this
    exact this

/-- Strict monotonicity of the affinity: a vanishing pairing term forces
`j_e = j'_e`. -/
theorem eq_of_artanh_div_sub_mul_sub_eq_zero {c j j' : ℝ} (hj : |j| < c) (hj' : |j'| < c)
    (h : (Real.artanh (j / c) - Real.artanh (j' / c)) * (j - j') = 0) : j = j' := by
  have hc : 0 < c := (abs_nonneg j).trans_lt hj
  rcases mul_eq_zero.mp h with h0 | h0
  · have h1 : Real.artanh (j / c) = Real.artanh (j' / c) := sub_eq_zero.mp h0
    have h2 := Real.artanh_injOn (div_mem_Ioo_of_abs_lt hj) (div_mem_Ioo_of_abs_lt hj') h1
    exact (div_left_inj' hc.ne').mp h2
  · exact sub_eq_zero.mp h0

/-- Injectivity of the modular class on the current fibre: two currents in
`𝒥(G,c)` whose affinities differ by an exact cochain coincide.  This is the
content of `cor:supp-faithful-modular` (and contains `lem:supp-zero-affinity`
as the case `j' = 0`). -/
theorem current_eq_of_affinity_class_eq (B : Matrix V E ℝ) (c : E → ℝ)
    {j j' : E → ℝ} (hj : j ∈ CurrentFibre B c) (hj' : j' ∈ CurrentFibre B c)
    (ha : IsExact B (affinity c j - affinity c j')) : j = j' := by
  obtain ⟨φ, hφ⟩ := ha
  have hpair : ∑ e, (affinity c j e - affinity c j' e) * (j e - j' e) = 0 := by
    have h0 : φ ⬝ᵥ (B *ᵥ (j - j')) = 0 := by
      rw [mulVec_sub, hj.1, hj'.1, sub_zero, dotProduct_zero]
    rw [dotProduct_mulVec, ← mulVec_transpose, ← hφ] at h0
    simpa [dotProduct] using h0
  have hnn : ∀ e ∈ (univ : Finset E),
      0 ≤ (affinity c j e - affinity c j' e) * (j e - j' e) :=
    fun e _ => artanh_div_sub_mul_sub_nonneg (hj.2 e) (hj'.2 e)
  have hzero := (sum_eq_zero_iff_of_nonneg hnn).mp hpair
  funext e
  exact eq_of_artanh_div_sub_mul_sub_eq_zero (hj.2 e) (hj'.2 e) (hzero e (mem_univ e))

open FiniteGraphSpectralUniversalityFibre in
/-- `cor:supp-faithful-modular` (Faithful metric–modular enrichment): for fixed
`(G, m, c)`, the modular class `[a]` of a fibre current determines the directed
stationary fluxes `q = c + j`, `q̄ = c - j` and the stationary generator rates
`k_{xy} = q_{xy} / m_x` (`forwardRate`/`reverseRate` of
`FiniteGraphSpectralUniversalityFibre`).  The metric data `(C(V), H_{m,c},
D_{m,c}, J, γ)` are functions of `(G, m, c)` alone, so the enrichment is
faithful on the fibre. -/
theorem faithful_modular_enrichment (B : Matrix V E ℝ) (m : V → ℝ) (tail head : E → V)
    (c : E → ℝ) {j j' : E → ℝ} (hj : j ∈ CurrentFibre B c) (hj' : j' ∈ CurrentFibre B c)
    (ha : IsExact B (affinity c j - affinity c j')) :
    forwardFlux c j = forwardFlux c j' ∧ reverseFlux c j = reverseFlux c j' ∧
      forwardRate m tail c j = forwardRate m tail c j' ∧
      reverseRate m head c j = reverseRate m head c j' := by
  have := current_eq_of_affinity_class_eq B c hj hj' ha
  subst this
  exact ⟨rfl, rfl, rfl, rfl⟩

end Affinity

/-! ## The finite modular-reversal packet on `ℓ²(E^or)` -/

section Reversal

variable {V Eor : Type*} (bar : Eor → Eor) (s : Eor → V) (q : Eor → ℝ)

/-- The reversal antiunitary `(J_E ξ)(e) = conj ξ(ē)`. -/
def reversalConj (ξ : Eor → ℂ) : Eor → ℂ := fun e => star (ξ (bar e))

/-- The modular ratio `q_e / q_{ē}`. -/
noncomputable def modularRatio (e : Eor) : ℝ := q e / q (bar e)

/-- The modular operator `(Δ_q ξ)(e) = (q_e / q_{ē}) ξ(e)`. -/
noncomputable def modularOperator (ξ : Eor → ℂ) : Eor → ℂ :=
  fun e => (modularRatio bar q e : ℂ) * ξ e

/-- The positive square root `Δ_q^{1/2}`. -/
noncomputable def modularSqrt (ξ : Eor → ℂ) : Eor → ℂ :=
  fun e => (Real.sqrt (modularRatio bar q e) : ℂ) * ξ e

/-- The modular conjugation `S_q = J_E Δ_q^{1/2}`. -/
noncomputable def modularConjugation : (Eor → ℂ) → (Eor → ℂ) :=
  reversalConj bar ∘ modularSqrt bar q

/-- Source multiplication `(λ_E(f) ξ)(e) = f(s(e)) ξ(e)`. -/
def sourceMul (f : V → ℂ) (ξ : Eor → ℂ) : Eor → ℂ := fun e => f (s e) * ξ e

/-- Terminal multiplication `(ρ_E(f) ξ)(e) = f(t(e)) ξ(e)` with `t(e) = s(ē)`. -/
def terminalMul (f : V → ℂ) (ξ : Eor → ℂ) : Eor → ℂ := fun e => f (s (bar e)) * ξ e

/-- The edge affinity read off the directed fluxes, `a_e = ½ log(q_e / q_{ē})`. -/
noncomputable def reversalAffinity (e : Eor) : ℝ :=
  (1 / 2 : ℝ) * Real.log (modularRatio bar q e)

variable {bar s q}

theorem star_ofReal_mul (x : ℝ) (z : ℂ) : star ((x : ℂ) * z) = (x : ℂ) * star z := by
  rw [star_mul', Complex.star_def, Complex.conj_ofReal, mul_comm]

/-- `J_E² = I` (thm:supp-Tomita). -/
theorem reversalConj_comp_self (hbar : Function.Involutive bar) :
    reversalConj bar ∘ reversalConj bar = id := by
  funext ξ e
  simp [reversalConj, hbar e]

/-- `q_{ē}/q_e = (q_e/q_{ē})⁻¹`. -/
theorem modularRatio_bar (hbar : Function.Involutive bar) (e : Eor) :
    modularRatio bar q (bar e) = (modularRatio bar q e)⁻¹ := by
  simp [modularRatio, hbar e, inv_div]

/-- `a_{ē} = -a_e`. -/
theorem reversalAffinity_bar (hbar : Function.Involutive bar) (e : Eor) :
    reversalAffinity bar q (bar e) = -reversalAffinity bar q e := by
  simp [reversalAffinity, modularRatio_bar hbar, Real.log_inv]

/-- `J_E Δ_q J_E` is the diagonal multiplier by `q_{ē}/q_e = (q_e/q_{ē})⁻¹`
(thm:supp-Tomita, second identity, explicit form). -/
theorem reversalConj_modularOperator_reversalConj (hbar : Function.Involutive bar)
    (ξ : Eor → ℂ) :
    reversalConj bar (modularOperator bar q (reversalConj bar ξ)) =
      fun e => ((modularRatio bar q e)⁻¹ : ℝ) * ξ e := by
  funext e
  simp only [reversalConj, modularOperator, hbar e, modularRatio_bar hbar]
  rw [star_ofReal_mul, star_star]

/-- `J_E Δ_q J_E = Δ_q⁻¹` (thm:supp-Tomita): the two multipliers are mutually
inverse. -/
theorem modularOperator_reversalConj_inverse (hbar : Function.Involutive bar)
    (hq : ∀ e, 0 < q e) (ξ : Eor → ℂ) :
    modularOperator bar q (reversalConj bar (modularOperator bar q (reversalConj bar ξ))) = ξ ∧
      reversalConj bar (modularOperator bar q (reversalConj bar (modularOperator bar q ξ))) = ξ := by
  have hr : ∀ e, modularRatio bar q e ≠ 0 :=
    fun e => (div_pos (hq e) (hq (bar e))).ne'
  constructor
  · rw [reversalConj_modularOperator_reversalConj hbar]
    funext e
    simp only [modularOperator]
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (hr e), Complex.ofReal_one, one_mul]
  · rw [reversalConj_modularOperator_reversalConj hbar]
    funext e
    simp only [modularOperator]
    rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (hr e), Complex.ofReal_one, one_mul]

/-- `√(q_{ē}/q_e) · √(q_e/q_{ē}) = 1`. -/
theorem sqrt_modularRatio_bar_mul (hbar : Function.Involutive bar) (hq : ∀ e, 0 < q e)
    (e : Eor) :
    Real.sqrt (modularRatio bar q (bar e)) * Real.sqrt (modularRatio bar q e) = 1 := by
  rw [modularRatio_bar hbar, Real.sqrt_inv]
  exact inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (div_pos (hq e) (hq (bar e))))

/-- `S_q² = I` (thm:supp-Tomita). -/
theorem modularConjugation_sq (hbar : Function.Involutive bar) (hq : ∀ e, 0 < q e)
    (ξ : Eor → ℂ) :
    modularConjugation bar q (modularConjugation bar q ξ) = ξ := by
  funext e
  simp only [modularConjugation, Function.comp, reversalConj, modularSqrt, hbar e]
  rw [star_ofReal_mul, star_star, ← mul_assoc, ← Complex.ofReal_mul,
    sqrt_modularRatio_bar_mul hbar hq, Complex.ofReal_one, one_mul]

/-- `J_E λ_E(f*) J_E = ρ_E(f)` (thm:supp-Tomita, opposite action). -/
theorem reversalConj_sourceMul_star_reversalConj (hbar : Function.Involutive bar)
    (f : V → ℂ) (ξ : Eor → ℂ) :
    reversalConj bar (sourceMul s (star ∘ f) (reversalConj bar ξ)) = terminalMul bar s f ξ := by
  funext e
  simp [reversalConj, sourceMul, terminalMul, hbar e, star_mul']

/-- `S_q λ_E(f*) S_q = ρ_E(f)` (thm:supp-Tomita, opposite action); since
`S_q² = I` the right factor is `S_q⁻¹`. -/
theorem modularConjugation_sourceMul_star_modularConjugation (hbar : Function.Involutive bar)
    (hq : ∀ e, 0 < q e) (f : V → ℂ) (ξ : Eor → ℂ) :
    modularConjugation bar q (sourceMul s (star ∘ f) (modularConjugation bar q ξ)) =
      terminalMul bar s f ξ := by
  funext e
  simp only [modularConjugation, Function.comp, reversalConj, modularSqrt, sourceMul,
    terminalMul, hbar e]
  rw [star_ofReal_mul, star_mul']
  simp only [star_star]
  have h := sqrt_modularRatio_bar_mul hbar hq e
  calc (Real.sqrt (modularRatio bar q (bar e)) : ℂ) *
        (f (s (bar e)) * ((Real.sqrt (modularRatio bar q e) : ℂ) * ξ e))
      = ((Real.sqrt (modularRatio bar q (bar e)) * Real.sqrt (modularRatio bar q e) : ℝ) : ℂ) *
          (f (s (bar e)) * ξ e) := by push_cast; ring
    _ = f (s (bar e)) * ξ e := by rw [h, Complex.ofReal_one, one_mul]

/-- `log Δ_q(e) = 2 a_e` (thm:supp-Tomita, logarithm statement). -/
theorem log_modularRatio_eq_two_mul_affinity (e : Eor) :
    Real.log (modularRatio bar q e) = 2 * reversalAffinity bar q e := by
  simp only [reversalAffinity]; ring

/-- `q_e / q_{ē} = exp(2 a_e)`. -/
theorem modularRatio_eq_exp (hq : ∀ e, 0 < q e) (e : Eor) :
    modularRatio bar q e = Real.exp (2 * reversalAffinity bar q e) := by
  have hpos : 0 < modularRatio bar q e := div_pos (hq e) (hq (bar e))
  rw [← log_modularRatio_eq_two_mul_affinity, Real.exp_log hpos]

/-- Consistency with the current-fibre affinity (eq:supp-affinity): when the
directed fluxes are `q_e = c_e + j_e`, `q_{ē} = c_e - j_e` with `|j_e| < c_e`,
the reversal affinity `½ log(q_e/q_{ē})` is `artanh(j_e / c_e)`. -/
theorem reversalAffinity_eq_artanh {c j : ℝ} (e : Eor) (hj : |j| < c)
    (hqe : q e = c + j) (hqbar : q (bar e) = c - j) :
    reversalAffinity bar q e = Real.artanh (j / c) := by
  have hc : 0 < c := (abs_nonneg j).trans_lt hj
  have hmem : j / c ∈ Set.Icc (-1 : ℝ) 1 := Set.Ioo_subset_Icc_self (div_mem_Ioo_of_abs_lt hj)
  rw [Real.artanh_eq_half_log hmem, reversalAffinity, modularRatio, hqe, hqbar]
  congr 2
  have hcj : c - j ≠ 0 := by rw [abs_lt] at hj; linarith
  field_simp

/-- The reversible branch is exactly `Δ_q = I` (thm:supp-Tomita): the modular
operator is the identity iff every directed flux equals its reverse. -/
theorem modularOperator_eq_id_iff (hq : ∀ e, 0 < q e) :
    modularOperator bar q = id ↔ ∀ e, q e = q (bar e) := by
  constructor
  · intro h e
    have h1 := congrFun (congrFun h (fun _ => (1 : ℂ))) e
    simp only [modularOperator, id, mul_one] at h1
    have h2 : modularRatio bar q e = 1 := by exact_mod_cast h1
    exact (div_eq_one_iff_eq (hq (bar e)).ne').mp h2
  · intro h
    funext ξ e
    simp [modularOperator, modularRatio, h e, div_self (hq (bar e)).ne']

end Reversal

/-! ## Face holonomy -/

section FaceHolonomy

variable {Eor P : Type*} [Fintype Eor] (bar : Eor → Eor) (q : Eor → ℝ)

/-- The face-curvature residual `F_a(p) = (d_1 a)(p) = Σ_e ε_{p,e} a_e` for the
signed face-incidence coefficients `ε_{p,e} ∈ ℤ` (the cellular coboundary
formula). -/
def faceCurvature (ε : P → Eor → ℤ) (a : Eor → ℝ) (p : P) : ℝ :=
  ∑ e, (ε p e : ℝ) * a e

/-- The modular face holonomy `Π_e (q_e / q_{ē})^{ε_{p,e}}` around the oriented
loaded two-cell `p` (eq:supp-face-holonomy); with `ε` the indicator of an
oriented cycle this is eq:supp-modular-cycle-holonomy. -/
noncomputable def faceHolonomy (ε : P → Eor → ℤ) (p : P) : ℝ :=
  ∏ e, modularRatio bar q e ^ ε p e

variable {bar q}

/-- `thm:supp-face-holonomy` (Face holonomy): the modular face holonomy equals
`exp(2 F_a(p))`. -/
theorem faceHolonomy_eq_exp_faceCurvature (hq : ∀ e, 0 < q e) (ε : P → Eor → ℤ) (p : P) :
    faceHolonomy bar q ε p =
      Real.exp (2 * faceCurvature ε (reversalAffinity bar q) p) := by
  unfold faceHolonomy faceCurvature
  rw [mul_sum, Real.exp_sum]
  refine prod_congr rfl fun e _ => ?_
  rw [modularRatio_eq_exp hq, ← Real.rpow_intCast, ← Real.exp_mul]
  congr 1; ring

/-- Descent criterion (thm:supp-face-holonomy): the face holonomy of `p` is
trivial iff the face-curvature residual at `p` vanishes. -/
theorem faceHolonomy_eq_one_iff (hq : ∀ e, 0 < q e) (ε : P → Eor → ℤ) (p : P) :
    faceHolonomy bar q ε p = 1 ↔ faceCurvature ε (reversalAffinity bar q) p = 0 := by
  rw [faceHolonomy_eq_exp_faceCurvature hq, Real.exp_eq_one_iff, mul_eq_zero]
  simp

/-- The modular transport descends to a flat cell-line packet (all face
holonomies trivial) exactly when every face-curvature residual vanishes. -/
theorem forall_faceHolonomy_eq_one_iff (hq : ∀ e, 0 < q e) (ε : P → Eor → ℤ) :
    (∀ p, faceHolonomy bar q ε p = 1) ↔
      ∀ p, faceCurvature ε (reversalAffinity bar q) p = 0 :=
  forall_congr' fun p => faceHolonomy_eq_one_iff hq ε p

end FaceHolonomy

end ModularAffinityReversalPacket
end RenewalGeometry
