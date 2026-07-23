/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Lorentz.PerronPressure

/-!
# Gauge covariance of the pressure (`prop:pressure-gauge-invariance`)

A vertex gauge `A ↦ A + f(x) − f(y)` rescales the reciprocal
capacities by `q_e ↦ q_e e^{(f(x)−f(y))/2}`, which conjugates the
pressure transfer by the positive diagonal `D_f = diag(e^{f/2})`
(`pressureKernel_gauge`).  The Gelfand–Fekete growth rate is
invariant under conjugation by positive diagonals
(`pRad_diag_conj`), so the pressure function `s ↦ r(s)` — and with
it its zero `β` and every object derived from the pressure function —
is gauge invariant (`pressureRate_gauge_invariant`).

The Doob-law clause (invariance of the edge law `p_e` and the vertex
law `π` built from the Perron vectors `h, ν` at the root) needs the
Perron eigenvectors, which the eigenvector-free pressure development
deliberately avoids; it is not formalized, as disclosed for
`thm:pressure-root`.
-/

namespace NCG

open Filter

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-! ## Conjugation invariance of the growth rate -/

theorem diag_conj_pow (A : Matrix V V ℝ) (dvec : V → ℝ)
    (hd : ∀ x, dvec x ≠ 0) :
    ∀ k : ℕ, (Matrix.diagonal dvec * A
        * Matrix.diagonal (fun x => (dvec x)⁻¹)) ^ k
      = Matrix.diagonal dvec * A ^ k
          * Matrix.diagonal fun x => (dvec x)⁻¹ := by
  have hDD : (Matrix.diagonal fun x => (dvec x)⁻¹)
      * Matrix.diagonal dvec = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    have h1 : (fun x => (dvec x)⁻¹ * dvec x) = fun _ => (1 : ℝ) :=
      funext fun x => inv_mul_cancel₀ (hd x)
    rw [h1, Matrix.diagonal_one]
  intro k
  induction k with
  | zero =>
    rw [pow_zero, pow_zero, Matrix.mul_one]
    rw [show (Matrix.diagonal dvec
        * Matrix.diagonal fun x => (dvec x)⁻¹) = 1 from by
      rw [Matrix.diagonal_mul_diagonal]
      have h1 : (fun x => dvec x * (dvec x)⁻¹) = fun _ => (1 : ℝ) :=
        funext fun x => mul_inv_cancel₀ (hd x)
      rw [h1, Matrix.diagonal_one]]
  | succ m ih =>
    rw [pow_succ, ih, pow_succ]
    calc Matrix.diagonal dvec * A ^ m
          * Matrix.diagonal (fun x => (dvec x)⁻¹)
          * (Matrix.diagonal dvec * A
            * Matrix.diagonal fun x => (dvec x)⁻¹)
        = Matrix.diagonal dvec * A ^ m
          * ((Matrix.diagonal fun x => (dvec x)⁻¹)
            * Matrix.diagonal dvec) * A
          * Matrix.diagonal (fun x => (dvec x)⁻¹) := by
          noncomm_ring
      _ = Matrix.diagonal dvec * (A ^ m * A)
          * Matrix.diagonal (fun x => (dvec x)⁻¹) := by
          rw [hDD]
          noncomm_ring

theorem diag_conj_entry (A : Matrix V V ℝ) (dvec : V → ℝ) (x y : V) :
    (Matrix.diagonal dvec * A
      * Matrix.diagonal fun v => (dvec v)⁻¹) x y
    = dvec x * A x y * (dvec y)⁻¹ := by
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- The Gelfand–Fekete growth rate is invariant under conjugation by
a positive diagonal. -/
theorem pRad_diag_conj {A : Matrix V V ℝ} (hA : EntryNonneg A)
    (hw : HasDiagWitness A) (dvec : V → ℝ) (hd : ∀ x, 0 < dvec x) :
    pRad (Matrix.diagonal dvec * A
      * Matrix.diagonal fun x => (dvec x)⁻¹) = pRad A := by
  classical
  set B := Matrix.diagonal dvec * A
    * Matrix.diagonal fun x => (dvec x)⁻¹ with hBdef
  -- pointwise sandwich constants from the diagonal range
  obtain ⟨x₀, -, hx₀⟩ := Finset.exists_min_image Finset.univ dvec
    Finset.univ_nonempty
  obtain ⟨x₁, -, hx₁⟩ := Finset.exists_max_image Finset.univ dvec
    Finset.univ_nonempty
  set c : ℝ := dvec x₀ * (dvec x₁)⁻¹ with hcdef
  set C : ℝ := dvec x₁ * (dvec x₀)⁻¹ with hCdef
  have hc : 0 < c := mul_pos (hd x₀) (inv_pos.mpr (hd x₁))
  have hC : 0 < C := mul_pos (hd x₁) (inv_pos.mpr (hd x₀))
  have hbounds : ∀ (k : ℕ) (x y : V),
      c * (A ^ k) x y ≤ (B ^ k) x y
        ∧ (B ^ k) x y ≤ C * (A ^ k) x y := by
    intro k x y
    rw [hBdef, diag_conj_pow A dvec (fun x => (hd x).ne'),
      diag_conj_entry]
    have hAk := entryNonneg_pow hA k x y
    constructor
    · have h1 : dvec x₀ ≤ dvec x := hx₀ x (Finset.mem_univ x)
      have h2 : (dvec x₁)⁻¹ ≤ (dvec y)⁻¹ :=
        one_div_le_one_div_of_le (hd y) (hx₁ y (Finset.mem_univ y))
          |>.trans_eq (by rw [one_div]) |>.trans_eq' (by rw [one_div])
      calc c * (A ^ k) x y = dvec x₀ * (A ^ k) x y * (dvec x₁)⁻¹ := by
            rw [hcdef]; ring
        _ ≤ dvec x * (A ^ k) x y * (dvec y)⁻¹ := by
            refine mul_le_mul ?_ h2 (inv_pos.mpr (hd x₁)).le ?_
            · exact mul_le_mul_of_nonneg_right h1 hAk
            · exact mul_nonneg (hd x).le hAk
    · have h1 : dvec x ≤ dvec x₁ := hx₁ x (Finset.mem_univ x)
      have h2 : (dvec y)⁻¹ ≤ (dvec x₀)⁻¹ :=
        one_div_le_one_div_of_le (hd x₀) (hx₀ y (Finset.mem_univ y))
          |>.trans_eq (by rw [one_div]) |>.trans_eq' (by rw [one_div])
      calc dvec x * (A ^ k) x y * (dvec y)⁻¹
          ≤ dvec x₁ * (A ^ k) x y * (dvec x₀)⁻¹ := by
            refine mul_le_mul ?_ h2 (inv_pos.mpr (hd y)).le ?_
            · exact mul_le_mul_of_nonneg_right h1 hAk
            · exact mul_nonneg (hd x₁).le hAk
        _ = C * (A ^ k) x y := by rw [hCdef]; ring
  have hBnn : EntryNonneg B := by
    intro x y
    have h3 := (hbounds 1 x y).1
    have h4 := entryNonneg_pow hA 1 x y
    have h5 : B x y = (B ^ 1) x y := by rw [pow_one]
    rw [h5]
    calc (0:ℝ) ≤ c * (A ^ 1) x y := by positivity
      _ ≤ (B ^ 1) x y := h3
  have hwB : HasDiagWitness B := by
    obtain ⟨x, m, hm, hpos⟩ := hw
    refine ⟨x, m, hm, ?_⟩
    have h6 := (hbounds m x x).1
    calc (0:ℝ) < c * (A ^ m) x x := mul_pos hc hpos
      _ ≤ (B ^ m) x x := h6
  -- entry sums are sandwiched, so the log growth rates agree
  have hsums : ∀ k : ℕ, c * entrySum (A ^ k) ≤ entrySum (B ^ k)
      ∧ entrySum (B ^ k) ≤ C * entrySum (A ^ k) := by
    intro k
    constructor
    · rw [entrySum, entrySum, Finset.mul_sum]
      refine Finset.sum_le_sum fun x _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun y _ => (hbounds k x y).1
    · rw [entrySum, entrySum, Finset.mul_sum]
      refine Finset.sum_le_sum fun x _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun y _ => (hbounds k x y).2
  have hlogA := tendsto_growthSeq hA hw
  have hlogB := tendsto_growthSeq hBnn hwB
  -- squeeze the logarithmic rates
  have hup : ∀ k : ℕ, 1 ≤ k → growthSeq B k / k
      ≤ Real.log C / k + growthSeq A k / k := by
    intro k hk
    have hkR : (0:ℝ) < k := by exact_mod_cast hk
    rw [← add_div, div_le_div_iff_of_pos_right hkR]
    unfold growthSeq
    calc Real.log (entrySum (B ^ k))
        ≤ Real.log (C * entrySum (A ^ k)) := by
          refine Real.log_le_log (entrySum_pow_pos hBnn hwB k) ?_
          exact (hsums k).2
      _ = Real.log C + Real.log (entrySum (A ^ k)) :=
          Real.log_mul hC.ne' (entrySum_pow_pos hA hw k).ne'
  have hlo : ∀ k : ℕ, 1 ≤ k → Real.log c / k + growthSeq A k / k
      ≤ growthSeq B k / k := by
    intro k hk
    have hkR : (0:ℝ) < k := by exact_mod_cast hk
    rw [← add_div, div_le_div_iff_of_pos_right hkR]
    unfold growthSeq
    calc Real.log c + Real.log (entrySum (A ^ k))
        = Real.log (c * entrySum (A ^ k)) :=
          (Real.log_mul hc.ne' (entrySum_pow_pos hA hw k).ne').symm
      _ ≤ Real.log (entrySum (B ^ k)) := by
          refine Real.log_le_log ?_ (hsums k).1
          exact mul_pos hc (entrySum_pow_pos hA hw k)
  have hshiftC : Tendsto
      (fun k : ℕ => Real.log C / k + growthSeq A k / k) atTop
      (nhds (Real.log (pRad A))) := by
    have h7 := (tendsto_const_div_atTop_nhds_zero_nat
      (Real.log C)).add hlogA
    rwa [zero_add] at h7
  have hshiftc : Tendsto
      (fun k : ℕ => Real.log c / k + growthSeq A k / k) atTop
      (nhds (Real.log (pRad A))) := by
    have h7 := (tendsto_const_div_atTop_nhds_zero_nat
      (Real.log c)).add hlogA
    rwa [zero_add] at h7
  have hle1 : Real.log (pRad B) ≤ Real.log (pRad A) := by
    refine le_of_tendsto_of_tendsto hlogB hshiftC ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    exact hup k hk
  have hle2 : Real.log (pRad A) ≤ Real.log (pRad B) := by
    refine le_of_tendsto_of_tendsto hshiftc hlogB ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    exact hlo k hk
  have hlog : Real.log (pRad B) = Real.log (pRad A) :=
    le_antisymm hle1 hle2
  calc pRad B = Real.exp (Real.log (pRad B)) :=
        (Real.exp_log (pRad_pos B)).symm
    _ = Real.exp (Real.log (pRad A)) := by rw [hlog]
    _ = pRad A := Real.exp_log (pRad_pos A)

/-! ## Gauge covariance of the pressure kernel -/

section Kernel

variable {E : Type*} [Fintype E]
variable {src tgt : E → V} {q ℓ : E → ℝ}

/-- **`prop:pressure-gauge-invariance` (conjugation identity)**: the
gauged capacities `q_e e^{(f(src e) − f(tgt e))/2}` produce the
diagonally conjugated transfer `D_f B(s) D_f^{-1}`. -/
theorem pressureKernel_gauge (f : V → ℝ) (s : ℝ) :
    pressureKernel src tgt
        (fun e => q e * Real.exp ((f (src e) - f (tgt e)) / 2)) ℓ s
      = Matrix.diagonal (fun x => Real.exp (f x / 2))
          * pressureKernel src tgt q ℓ s
          * Matrix.diagonal fun x => (Real.exp (f x / 2))⁻¹ := by
  ext x y
  rw [diag_conj_entry]
  show (∑ e ∈ Finset.univ.filter
      (fun e => src e = x ∧ tgt e = y),
      q e * Real.exp ((f (src e) - f (tgt e)) / 2)
        * Real.exp (-(s * ℓ e)))
    = Real.exp (f x / 2)
      * (∑ e ∈ Finset.univ.filter
          (fun e => src e = x ∧ tgt e = y),
          q e * Real.exp (-(s * ℓ e)))
      * (Real.exp (f y / 2))⁻¹
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun e he => ?_
  obtain ⟨hsrc, htgt⟩ := (Finset.mem_filter.mp he).2
  rw [hsrc, htgt]
  rw [show Real.exp ((f x - f y) / 2)
      = Real.exp (f x / 2) * (Real.exp (f y / 2))⁻¹ from by
    rw [← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring]
  ring

/-- **Proposition `prop:pressure-gauge-invariance`**: the pressure
rate function is invariant under every vertex gauge — hence so are
its zero `β` and every quantity derived from the pressure
function. -/
theorem pressureRate_gauge_invariant (f : V → ℝ)
    (hq : ∀ e, 0 ≤ q e)
    (hconn : HasDiagWitness (pressureKernel src tgt q ℓ 0))
    {ℓ₀ ℓ₁ : ℝ} (hℓ₀ : ∀ e, ℓ₀ ≤ ℓ e) (hℓ₁ : ∀ e, ℓ e ≤ ℓ₁)
    (s : ℝ) :
    pressureRate src tgt
        (fun e => q e * Real.exp ((f (src e) - f (tgt e)) / 2)) ℓ s
      = pressureRate src tgt q ℓ s := by
  unfold pressureRate
  rw [pressureKernel_gauge]
  exact pRad_diag_conj (pressureKernel_nonneg hq s)
    (pressureKernel_witness hq hℓ₀ hℓ₁ hconn s)
    (fun x => Real.exp (f x / 2)) fun x => Real.exp_pos _

end Kernel

end NCG
