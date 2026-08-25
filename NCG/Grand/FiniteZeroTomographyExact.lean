/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite zero tomography via Prony reconstruction

Exact formalization for `thm:GRH-finite-zero-tomography` (GRH.19–GRH.22).

* **GRH.19** (`signal`): the zero-side outputs of the translated profiles form an exact
  exponential-node signal `Y_k = ∑_ρ ζ_ρ^k • v_ρ`;
* **GRH.20** (`prony_unique`): the monic degree-`M` polynomial annihilating the block
  recurrence is unique and equals `∏_ρ (z - ζ_ρ)` — via a module-valued Vandermonde
  inversion (`vandermonde_smul_eq_zero`) and root counting;
* **GRH.21** (`node_unimodular_iff`, `node_injective`): `Re ρ = 1/2 ↔ |ζ_ρ| = 1`, and
  the node map `ρ ↦ e^{τ(ρ-1/2)}` is injective on the strip `|Im ρ| ≤ T` when
  `τT < π`;
* **GRH.22** (`hankel_factorization`, `comp_lower_bound`, `hankel_sigma_lower`): the
  Prony/Hankel map factors exactly as synthesis ∘ diagonal ∘ Vandermonde, so its
  singular floor is at least `m_vis σ_min(V)²`.
-/

open Polynomial Finset

namespace NCG
namespace ZeroTomography

variable {H : Type*} [AddCommGroup H] [Module ℂ H]

/-- **GRH.19**: the exponential-node signal `Y_k = ∑_ρ ζ_ρ^k • v_ρ`. -/
def signal {M : ℕ} (ζ : Fin M → ℂ) (v : Fin M → H) (k : ℕ) : H :=
  ∑ ρ, ζ ρ ^ k • v ρ

/-- Module-valued Vandermonde inversion: if `∑_ρ ζ_ρ^k • u_ρ = 0` for `M` consecutive
powers and the nodes are distinct, then every `u_ρ` vanishes. -/
theorem vandermonde_smul_eq_zero {M : ℕ} {ζ : Fin M → ℂ}
    (hζ : Function.Injective ζ) (u : Fin M → H)
    (h : ∀ k : Fin M, ∑ ρ, ζ ρ ^ (k : ℕ) • u ρ = 0) : u = 0 := by
  classical
  have hdet : (Matrix.vandermonde ζ).det ≠ 0 := by
    rw [Matrix.det_vandermonde]
    refine Finset.prod_ne_zero_iff.mpr fun i _ =>
      Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    exact sub_ne_zero.mpr fun hEq => (Finset.mem_Ioi.mp hj).ne' (hζ hEq)
  set W : Matrix (Fin M) (Fin M) ℂ := (Matrix.vandermonde ζ).transpose with hWdef
  have hWd : IsUnit W.det := by
    rw [hWdef, Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr hdet
  have hinv := Matrix.nonsing_inv_mul W hWd
  have hrow : ∀ k : Fin M, ∑ σ, W k σ • u σ = 0 := fun k => h k
  funext ρ
  change u ρ = 0
  calc u ρ = ∑ σ, ((W⁻¹ * W) ρ σ) • u σ := by
        rw [hinv]
        simp [Matrix.one_apply, ite_smul]
    _ = ∑ σ, ∑ k, (W⁻¹ ρ k * W k σ) • u σ := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [Matrix.mul_apply, Finset.sum_smul]
    _ = ∑ k, W⁻¹ ρ k • ∑ σ, W k σ • u σ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [smul_smul]
    _ = 0 := by simp [hrow]

/-- The block recurrence applied to the signal collapses to node evaluations. -/
theorem sum_coeff_signal {M : ℕ} (ζ : Fin M → ℂ) (v : Fin M → H)
    (Q : Polynomial ℂ) {n : ℕ} (hn : Q.natDegree < n) (k : ℕ) :
    ∑ i ∈ Finset.range n, Q.coeff i • signal ζ v (k + i)
      = ∑ ρ, (ζ ρ ^ k * Q.eval (ζ ρ)) • v ρ := by
  classical
  simp only [signal, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [Polynomial.eval_eq_sum_range' hn, Finset.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]
  congr 1
  rw [pow_add]
  ring

/-- Any polynomial vanishing at every node annihilates the signal recurrence. -/
theorem annihilates {M : ℕ} (ζ : Fin M → ℂ) (v : Fin M → H) (Q : Polynomial ℂ)
    (hroots : ∀ ρ, Q.eval (ζ ρ) = 0) {n : ℕ} (hn : Q.natDegree < n) (k : ℕ) :
    ∑ i ∈ Finset.range n, Q.coeff i • signal ζ v (k + i) = 0 := by
  rw [sum_coeff_signal ζ v Q hn k]
  simp [hroots]

/-- **GRH.20**: the monic degree-`M` annihilator of the block recurrence is unique and
equals `∏_ρ (z - ζ_ρ)`, provided the nodes are distinct and every retained loading is
nonzero. -/
theorem prony_unique {M : ℕ} {ζ : Fin M → ℂ} {v : Fin M → H}
    (hζ : Function.Injective ζ) (hv : ∀ ρ, v ρ ≠ 0)
    (P : Polynomial ℂ) (hP : P.Monic) (hdeg : P.natDegree = M)
    (hann : ∀ k : Fin M,
      ∑ i ∈ Finset.range (M + 1), P.coeff i • signal ζ v ((k : ℕ) + i) = 0) :
    P = ∏ ρ, (Polynomial.X - Polynomial.C (ζ ρ)) := by
  classical
  set Q : Polynomial ℂ := ∏ ρ, (Polynomial.X - Polynomial.C (ζ ρ)) with hQdef
  have hQmonic : Q.Monic :=
    Polynomial.monic_prod_of_monic _ _ fun ρ _ => Polynomial.monic_X_sub_C _
  have hQdeg : Q.natDegree = M := by
    rw [hQdef, Polynomial.natDegree_prod_of_monic _ _
      fun ρ _ => Polynomial.monic_X_sub_C _]
    simp
  have hQeval : ∀ ρ, Q.eval (ζ ρ) = 0 := by
    intro ρ
    rw [hQdef, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ ρ) (by simp)
  have hPeval : ∀ ρ, P.eval (ζ ρ) = 0 := by
    have hu : (fun ρ => P.eval (ζ ρ) • v ρ) = 0 := by
      refine vandermonde_smul_eq_zero hζ _ fun k => ?_
      have h1 := hann k
      rw [sum_coeff_signal ζ v P (by rw [hdeg]; exact Nat.lt_succ_self M)] at h1
      calc ∑ ρ, ζ ρ ^ (k : ℕ) • P.eval (ζ ρ) • v ρ
          = ∑ ρ, (ζ ρ ^ (k : ℕ) * P.eval (ζ ρ)) • v ρ :=
            Finset.sum_congr rfl fun ρ _ => smul_smul _ _ _
        _ = 0 := h1
    intro ρ
    have hpt := congrFun hu ρ
    simp only [Pi.zero_apply] at hpt
    rcases smul_eq_zero.mp hpt with h | h
    · exact h
    · exact absurd h (hv ρ)
  by_cases hM : M = 0
  · have hd0 : P.natDegree = 0 := hdeg.trans hM
    have hc0 : P.coeff 0 = 1 := by
      have hl := hP.leadingCoeff
      rwa [Polynomial.leadingCoeff, hd0] at hl
    have hP1 : P = 1 := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero hd0, hc0, map_one]
    subst hM
    rw [hP1, hQdef]
    simp
  · by_contra hne
    have hD0 : P - Q ≠ 0 := sub_ne_zero.mpr hne
    have hdegQP : Q.degree = P.degree := by
      rw [Polynomial.degree_eq_natDegree hP.ne_zero,
        Polynomial.degree_eq_natDegree hQmonic.ne_zero, hdeg, hQdeg]
    have hlc : P.leadingCoeff = Q.leadingCoeff := by
      rw [hP.leadingCoeff, hQmonic.leadingCoeff]
    have hDdeg : (P - Q).degree < P.degree :=
      Polynomial.degree_sub_lt hdegQP.symm hP.ne_zero hlc
    have hDnat : (P - Q).natDegree < M := by
      rw [Polynomial.natDegree_lt_iff_degree_lt hD0]
      exact hDdeg.trans_eq (by rw [Polynomial.degree_eq_natDegree hP.ne_zero, hdeg])
    have hDzero : P - Q = 0 := by
      refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hζ
        (fun ρ => ?_) (by simpa using hDnat)
      rw [Polynomial.eval_sub, hPeval, hQeval, sub_zero]
    exact hD0 hDzero

/-! ### GRH.21: node calculus of the strip -/

/-- **GRH.21**: `Re ρ = 1/2` iff the reconstructed node `ζ_ρ = e^{τ(ρ-1/2)}` is
unimodular. -/
theorem node_unimodular_iff {τ : ℝ} (hτ : 0 < τ) (ρ : ℂ) :
    ‖Complex.exp ((τ : ℂ) * (ρ - ((1 : ℝ) / 2 : ℝ)))‖ = 1 ↔ ρ.re = 1 / 2 := by
  rw [Complex.norm_exp]
  have hre : ((τ : ℂ) * (ρ - ((1 : ℝ) / 2 : ℝ))).re = τ * (ρ.re - 1 / 2) := by
    simp [Complex.mul_re, Complex.sub_re]
  rw [hre, show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm, Real.exp_eq_exp]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h0 | h0
    · exact absurd h0 hτ.ne'
    · linarith
  · intro h
    rw [h]
    ring

/-- The node map `ρ ↦ e^{τ(ρ-1/2)}` is injective on the strip `|Im ρ| ≤ T` when
`τT < π`. -/
theorem node_injective {τ T : ℝ} (hτ : 0 < τ) (hτT : τ * T < Real.pi)
    {ρ σ : ℂ} (hρ : |ρ.im| ≤ T) (hσ : |σ.im| ≤ T)
    (h : Complex.exp ((τ : ℂ) * (ρ - ((1 : ℝ) / 2 : ℝ)))
        = Complex.exp ((τ : ℂ) * (σ - ((1 : ℝ) / 2 : ℝ)))) : ρ = σ := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  have him : τ * ρ.im = τ * σ.im + (n : ℝ) * (2 * Real.pi) := by
    have h1 := congrArg Complex.im hn
    simpa [Complex.mul_im, Complex.add_im, Complex.sub_im, Complex.mul_re,
      Complex.I_re, Complex.I_im] using h1
  have hre : τ * ρ.re = τ * σ.re := by
    have h1 := congrArg Complex.re hn
    simpa [Complex.mul_re, Complex.add_re, Complex.sub_re, Complex.mul_im,
      Complex.I_re, Complex.I_im] using h1
  have hn0 : n = 0 := by
    have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
    have himabs : |ρ.im - σ.im| ≤ 2 * T := by
      have h1 := abs_le.mp hρ
      have h2 := abs_le.mp hσ
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have heq : |(n : ℝ)| * (2 * Real.pi) = τ * |ρ.im - σ.im| := by
      have h3 : τ * (ρ.im - σ.im) = (n : ℝ) * (2 * Real.pi) := by linarith
      calc |(n : ℝ)| * (2 * Real.pi) = |(n : ℝ) * (2 * Real.pi)| := by
            rw [abs_mul,
              abs_of_pos (show (0 : ℝ) < 2 * Real.pi by linarith)]
        _ = |τ * (ρ.im - σ.im)| := by rw [← h3]
        _ = τ * |ρ.im - σ.im| := by rw [abs_mul, abs_of_pos hτ]
    have hlt : |(n : ℝ)| * (2 * Real.pi) < 2 * Real.pi := by
      rw [heq]
      calc τ * |ρ.im - σ.im| ≤ τ * (2 * T) :=
            mul_le_mul_of_nonneg_left himabs hτ.le
        _ < 2 * Real.pi := by linarith
    have habs : |(n : ℝ)| < 1 := by
      by_contra hge
      have hge' : 1 ≤ |(n : ℝ)| := not_lt.mp hge
      nlinarith
    have hint : |n| < 1 := by exact_mod_cast habs
    have h5 := abs_lt.mp hint
    omega
  rw [hn0] at hn
  simp only [Int.cast_zero, zero_mul, add_zero] at hn
  have hτne : ((τ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hτ.ne'
  have := mul_left_cancel₀ hτne hn
  exact sub_left_injective.eq_iff.mp this

/-! ### GRH.22: the Prony singular floor -/

/-- Vandermonde-transpose application: `c ↦ (∑_i c_i ζ_ρ^i)_ρ`. -/
def vandApply {M : ℕ} (ζ : Fin M → ℂ) (c : Fin M → ℂ) : Fin M → ℂ :=
  fun ρ => ∑ i, c i * ζ ρ ^ (i : ℕ)

/-- Diagonal loading application: `u ↦ (u_ρ • v_ρ)_ρ`. -/
def diagApply {M : ℕ} (v : Fin M → H) (u : Fin M → ℂ) : Fin M → H :=
  fun ρ => u ρ • v ρ

/-- Synthesis application: `w ↦ (∑_ρ ζ_ρ^k • w_ρ)_k`. -/
def synthApply {M : ℕ} (ζ : Fin M → ℂ) (w : Fin M → H) : Fin M → H :=
  fun k => ∑ ρ, ζ ρ ^ (k : ℕ) • w ρ

/-- **GRH.22, exact factorization**: the Prony/Hankel map of the signal factors as
synthesis ∘ diagonal loading ∘ Vandermonde. -/
theorem hankel_factorization {M : ℕ} (ζ : Fin M → ℂ) (v : Fin M → H)
    (c : Fin M → ℂ) :
    (fun k : Fin M => ∑ i : Fin M, c i • signal ζ v ((k : ℕ) + (i : ℕ)))
      = synthApply ζ (diagApply v (vandApply ζ c)) := by
  classical
  funext k
  simp only [signal, synthApply, diagApply, vandApply, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  calc ∑ i : Fin M, c i • ζ ρ ^ ((k : ℕ) + (i : ℕ)) • v ρ
      = ∑ i : Fin M, (ζ ρ ^ (k : ℕ) * (c i * ζ ρ ^ (i : ℕ))) • v ρ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul]
        congr 1
        rw [pow_add]
        ring
    _ = (∑ i : Fin M, ζ ρ ^ (k : ℕ) * (c i * ζ ρ ^ (i : ℕ))) • v ρ :=
        (Finset.sum_smul).symm
    _ = (ζ ρ ^ (k : ℕ) * ∑ i : Fin M, c i * ζ ρ ^ (i : ℕ)) • v ρ := by
        rw [Finset.mul_sum]
    _ = ζ ρ ^ (k : ℕ) • (∑ i : Fin M, c i * ζ ρ ^ (i : ℕ)) • v ρ :=
        (smul_smul _ _ _).symm

/-- Lower bounds compose: a chain of maps with singular floors `σ_V`, `m_vis`, `σ_V`
has singular floor `m_vis σ_V²`. -/
theorem comp_lower_bound {X Y Z W : Type*} [NormedAddCommGroup X]
    [NormedAddCommGroup Y] [NormedAddCommGroup Z] [NormedAddCommGroup W]
    (B : X → Y) (D : Y → Z) (A : Z → W) {σV mvis : ℝ}
    (hσ : 0 ≤ σV) (hm : 0 ≤ mvis)
    (hB : ∀ x, σV * ‖x‖ ≤ ‖B x‖) (hD : ∀ y, mvis * ‖y‖ ≤ ‖D y‖)
    (hA : ∀ z, σV * ‖z‖ ≤ ‖A z‖) (x : X) :
    mvis * σV ^ 2 * ‖x‖ ≤ ‖A (D (B x))‖ := by
  have h1 := hB x
  have h2 := hD (B x)
  have h3 := hA (D (B x))
  nlinarith [mul_le_mul_of_nonneg_left h1 hm,
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hm) hσ,
    mul_le_mul_of_nonneg_left h2 hσ]

end ZeroTomography

namespace ZeroTomography

variable {H : Type*} [NormedAddCommGroup H] [Module ℂ H]

/-- **GRH.22**: the Prony/Hankel recurrence map has singular floor
`m_vis σ_min(V_ζ)²`, given the Vandermonde/synthesis floors `σ_min(V_ζ)` and the
visible-loading floor `m_vis`. -/
theorem hankel_sigma_lower {M : ℕ} (ζ : Fin M → ℂ) (v : Fin M → H)
    {σV mvis : ℝ} (hσ : 0 ≤ σV) (hm : 0 ≤ mvis)
    (hB : ∀ c : Fin M → ℂ, σV * ‖c‖ ≤ ‖vandApply ζ c‖)
    (hD : ∀ u : Fin M → ℂ, mvis * ‖u‖ ≤ ‖diagApply v u‖)
    (hA : ∀ w : Fin M → H, σV * ‖w‖ ≤ ‖synthApply ζ w‖)
    (c : Fin M → ℂ) :
    mvis * σV ^ 2 * ‖c‖
      ≤ ‖fun k : Fin M => ∑ i : Fin M, c i • signal ζ v ((k : ℕ) + (i : ℕ))‖ := by
  rw [hankel_factorization ζ v c]
  exact comp_lower_bound (vandApply ζ) (diagApply v) (synthApply ζ) hσ hm hB hD hA c

/-- **Bundle for `thm:GRH-finite-zero-tomography`**: given the row-subtracted outputs
(GRH.19 interface `hY`), the outputs have the exact exponential-node form (GRH.19),
the block recurrence has the unique monic annihilator `∏ (z - ζ_ρ)` reconstructing
every visible zero (GRH.20), and RH at finite height is equivalent to unimodularity of
every reconstructed node (GRH.21). -/
theorem grh_finite_zero_tomography {M : ℕ} {τ T : ℝ} (hτ : 0 < τ)
    (hτT : τ * T < Real.pi) (ρnode : Fin M → ℂ)
    (hdist : Function.Injective ρnode) (him : ∀ j, |(ρnode j).im| ≤ T)
    (v : Fin M → H) (hv : ∀ j, v j ≠ 0) (ζ : Fin M → ℂ)
    (hζdef : ∀ j, ζ j = Complex.exp ((τ : ℂ) * (ρnode j - ((1 : ℝ) / 2 : ℝ))))
    (Y : ℕ → H) (hY : ∀ k, Y k = signal ζ v k) :
    (∀ k, Y k = ∑ j, ζ j ^ k • v j) ∧
    (∀ P : Polynomial ℂ, P.Monic → P.natDegree = M →
      (∀ k : Fin M,
        ∑ i ∈ Finset.range (M + 1), P.coeff i • Y ((k : ℕ) + i) = 0) →
      P = ∏ j, (Polynomial.X - Polynomial.C (ζ j))) ∧
    ((∀ j, (ρnode j).re = 1 / 2) ↔ (∀ j, ‖ζ j‖ = 1)) := by
  have hζinj : Function.Injective ζ := by
    intro a b hab
    refine hdist (node_injective hτ hτT (him a) (him b) ?_)
    rw [← hζdef a, ← hζdef b]
    exact hab
  refine ⟨fun k => hY k, fun P hP hdeg hann => ?_, ?_⟩
  · refine prony_unique hζinj hv P hP hdeg fun k => ?_
    have h1 := hann k
    simp only [hY] at h1
    exact h1
  · constructor
    · intro hre j
      rw [hζdef j]
      exact (node_unimodular_iff hτ (ρnode j)).mpr (hre j)
    · intro huni j
      refine (node_unimodular_iff hτ (ρnode j)).mp ?_
      rw [← hζdef j]
      exact huni j

end ZeroTomography
end NCG
