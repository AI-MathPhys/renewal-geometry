/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallCoulombState

/-!
# The critical a-priori estimate for Coulomb gauge states, in terms of the curvature energy
  (stage D2/D3 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `norm_conj_entry_le` — unitary conjugation does not increase the Frobenius norm:
  `|(U F U^*)_{ij}| ≤ |F|_F`;
* `evM_curvMS`, `wCurv_embX_ae` — the weak curvature of a `𝔤`-valued Sobolev connection is the
  pointwise value of the Banach-algebra curvature `curvMS`;
* `evM_curvMS_matOfSmooth` — for a smooth connection, `curvMS` is the classical curvature
  (`curvatureW`);
* `coords_le_bL4`, `bL4_le_coords` — the coefficient `L⁴` norms and the matrix-entry `L⁴` norms
  are comparable (constants depending on the basis);
* `coulomb_state_apriori` (**main result**): there are `δ > 0`, `C` (depending on `m` and the
  basis only) such that for every `u ∈ H⁵(B, M_m(ℂ))` with `u u^* = 1` and every tangential
  Coulomb `𝔤`-valued `a = u·B` (`B` the smooth connection `B_f`) with coefficient `L⁴` norm
  `≤ δ`, the coefficient `L⁴` norm is `≤ C · E(B_f)^{1/2}`, `E` the curvature energy on the ball.
-/

open MeasureTheory Set Metric Filter Topology NormedSpace
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

set_option maxHeartbeats 400000
noncomputable section

namespace RenewalGeometry.BallAnalysis.BallAlg

open SobolevOpen BallReg SobAlg WeakCoulomb TanApprox

set_option linter.unusedSectionVars false

/-! ### Unitary invariance of the Frobenius norm -/

section Frobenius

variable {m : ℕ}

theorem sum_norm_sq_eq_trace (M : Matrix (Fin m) (Fin m) ℂ) :
    (∑ k, ∑ l, ‖M k l‖ ^ 2 : ℝ) = (Matrix.trace (M * star M)).re := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact (Complex.ofReal_re _).symm

/-- **Unitary conjugation bounds the entries by the Frobenius norm.** -/
theorem norm_conj_entry_le {U F : Matrix (Fin m) (Fin m) ℂ} (hU : star U * U = 1) (i j : Fin m) :
    ‖(U * F * star U) i j‖ ≤ Real.sqrt (∑ k, ∑ l, ‖F k l‖ ^ 2) := by
  have h1 : ∑ k, ∑ l, ‖(U * F * star U) k l‖ ^ 2 = ∑ k, ∑ l, ‖F k l‖ ^ 2 := by
    rw [sum_norm_sq_eq_trace, sum_norm_sq_eq_trace]
    congr 1
    have e : U * F * star U * star (U * F * star U) = U * (F * star F * star U) := by
      simp only [star_mul, star_star]
      rw [show U * F * star U * (U * (star F * star U)) = U * F * (star U * U) * (star F * star U) by
        simp only [Matrix.mul_assoc], hU, Matrix.mul_one]
      simp only [Matrix.mul_assoc]
    rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, hU, Matrix.mul_one]
  rw [← h1]
  apply Real.le_sqrt_of_sq_le
  exact (Finset.single_le_sum (f := fun l => ‖(U * F * star U) i l‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun k => ∑ l, ‖(U * F * star U) k l‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i))

end Frobenius

/-! ### Curvatures -/

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {m d : ℕ}

theorem evM_curvMS {s : ℕ} [Fact (3 ≤ s)] (X : Fin 4 → MatSob c r (s + 1) m) (μ ν : Fin 4) :
    evM (curvMS X μ ν) =ᵐ[volume.restrict (euclBall c r)] fun x =>
      evM (derM μ (X ν)) x - evM (derM ν (X μ)) x +
        (evM (X μ) x * evM (X ν) x - evM (X ν) x * evM (X μ) x) := by
  unfold curvMS
  filter_upwards [evM_add (derM μ (X ν) - derM ν (X μ))
      (rhoM (X μ) * rhoM (X ν) - rhoM (X ν) * rhoM (X μ)),
    evM_sub (derM μ (X ν)) (derM ν (X μ)),
    evM_sub (rhoM (X μ) * rhoM (X ν)) (rhoM (X ν) * rhoM (X μ)),
    evM_mul (rhoM (X μ)) (rhoM (X ν)), evM_mul (rhoM (X ν)) (rhoM (X μ))] with x h1 h2 h3 h4 h5
  rw [h1, h2, h3, h4, h5]
  rfl

/-- **The weak curvature of a `𝔤`-valued Sobolev connection is the pointwise curvature.** -/
theorem wCurv_embX_ae (L : LieBasis m d) (a : Fin 4 → Fin d → SobAlg c r 4) (μ ν : Fin 4)
    (i j : Fin m) :
    wCurv (fun ν i j x => evM (embX L (a ν)) x i j)
      (fun ν i j μ x => evM (derM μ (embX L (a ν))) x i j) μ ν i j =ᵐ[volume.restrict (euclBall c r)]
      fun x => evM (curvMS (fun μ => embX L (a μ)) μ ν) x i j := by
  filter_upwards [evM_curvMS (fun μ => embX L (a μ)) μ ν] with x hx
  rw [hx]
  simp only [wCurv, bComm, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply,
    ← Finset.sum_sub_distrib]

/-- **For a smooth connection, `curvMS` is the classical curvature.** -/
theorem evM_curvMS_matOfSmooth {Bf : CriticalGauge.MConn m}
    (hB : ∀ μ i j, ContDiff ℝ ∞ (fun x => Bf μ x i j)) (μ ν : Fin 4) :
    evM (curvMS (fun κ => matOfSmooth (c := c) (r := r) 4 (Bf κ) (hB κ)) μ ν)
      =ᵐ[volume.restrict (euclBall c r)] fun x => Matrix.of fun k l =>
        curvatureW (CriticalGauge.entries Bf) (CriticalGauge.entryGrad Bf) μ ν k l x := by
  have hd1 : evM (derM μ (matOfSmooth (c := c) (r := r) 4 (Bf ν) (hB ν)))
      =ᵐ[volume.restrict (euclBall c r)] pdM (Bf ν) μ := by
    rw [derM_matOfSmooth]
    exact evM_matOfSmooth (c := c) (r := r) (s := 3) (contDiff_pdM_entry (hB ν) μ)
  have hd2 : evM (derM ν (matOfSmooth (c := c) (r := r) 4 (Bf μ) (hB μ)))
      =ᵐ[volume.restrict (euclBall c r)] pdM (Bf μ) ν := by
    rw [derM_matOfSmooth]
    exact evM_matOfSmooth (c := c) (r := r) (s := 3) (contDiff_pdM_entry (hB μ) ν)
  filter_upwards [evM_curvMS (fun κ => matOfSmooth (c := c) (r := r) 4 (Bf κ) (hB κ)) μ ν,
    hd1, hd2, evM_matOfSmooth (c := c) (r := r) (s := 4) (hB μ),
    evM_matOfSmooth (c := c) (r := r) (s := 4) (hB ν)] with x h1 h2 h3 h4 h5
  rw [h1, h2, h3, h4, h5]
  ext k l
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply, curvatureW,
    CriticalGauge.entries, CriticalGauge.entryGrad, pdM, ← Finset.sum_sub_distrib]


/-! ### Comparison of coefficient and entry norms -/

theorem eLpNorm_sum_ofReal_mul_le' {μ : Measure (Fin 4 → ℝ)} {p : ℝ≥0∞} (hp : 1 ≤ p) {ι : Type*}
    (t : Finset ι) (f : ι → (Fin 4 → ℝ) → ℝ) (C : ι → ℂ)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) :
    eLpNorm (fun x => ∑ i ∈ t, ((f i x : ℝ) : ℂ) * C i) p μ ≤
      ∑ i ∈ t, ‖C i‖ₑ * eLpNorm (f i) p μ := by
  have e : (fun x => ∑ i ∈ t, ((f i x : ℝ) : ℂ) * C i) =
      ∑ i ∈ t, fun x => C i • ((f i x : ℝ) : ℂ) := by
    funext x; simp [Finset.sum_apply, mul_comm]
  rw [e]
  refine (eLpNorm_sum_le (fun i _ => (Complex.continuous_ofReal.comp_aestronglyMeasurable
    (hf i)).const_smul (C i)) hp).trans (Finset.sum_le_sum fun i _ => ?_)
  show eLpNorm (C i • fun x => ((f i x : ℝ) : ℂ)) p μ ≤ _
  rw [eLpNorm_const_smul]
  gcongr
  exact le_of_eq (eLpNorm_congr_norm_ae (Eventually.of_forall fun x => by simp))

/-- The coefficient `L⁴` norm `Σ_{ν,b} ‖a_ν^b‖_{L⁴(B)}`. -/
def coordL4 (a : Fin 4 → Fin d → SobAlg c r 4) : ℝ≥0∞ :=
  ∑ ν, ∑ b, eLpNorm (fn (a ν b)) 4 (volume.restrict (euclBall c r))

/-- The basis constant `Σ_{b,i,j} |e_b(i,j)|`. -/
def LieBasis.Ke (L : LieBasis m d) : ℝ≥0∞ := ∑ b, ∑ i, ∑ j, ‖L.e b i j‖ₑ

/-- The coordinate constant `Σ_{b,i,j} (|α_b(i,j)| + |β_b(i,j)|)`. -/
def LieBasis.Kκ (L : LieBasis m d) : ℝ≥0∞ := ∑ b, ∑ i, ∑ j, (‖L.α b i j‖ₑ + ‖L.β b i j‖ₑ)

theorem LieBasis.Ke_ne_top (L : LieBasis m d) : L.Ke ≠ ⊤ := by
  unfold LieBasis.Ke
  exact ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.sum_ne_top.mpr fun _ _ =>
    ENNReal.sum_ne_top.mpr fun _ _ => enorm_ne_top

theorem LieBasis.Kκ_ne_top (L : LieBasis m d) : L.Kκ ≠ ⊤ := by
  unfold LieBasis.Kκ
  exact ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.sum_ne_top.mpr fun _ _ =>
    ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.add_ne_top.mpr ⟨enorm_ne_top, enorm_ne_top⟩

theorem le_sum_three {ι κ T : Type*} [Fintype ι] [Fintype κ] [Fintype T]
    (f : ι → κ → T → ℝ≥0∞) (i : ι) (k : κ) (l : T) : f i k l ≤ ∑ i, ∑ k, ∑ l, f i k l :=
  (Finset.single_le_sum (f := fun l => f i k l) (fun _ _ => zero_le) (Finset.mem_univ l)).trans
    ((Finset.single_le_sum (f := fun k => ∑ l, f i k l) (fun _ _ => zero_le)
      (Finset.mem_univ k)).trans
      (Finset.single_le_sum (f := fun i => ∑ k, ∑ l, f i k l) (fun _ _ => zero_le)
        (Finset.mem_univ i)))

/-- **Entry norms by coefficient norms.** -/
theorem bL4_le_coords (L : LieBasis m d) (a : Fin 4 → Fin d → SobAlg c r 4) :
    bL4 c r (fun ν i j x => evM (embX L (a ν)) x i j) ≤ L.Ke * coordL4 a := by
  have h1 : ∀ ν i j, eLpNorm (fun x => evM (embX L (a ν)) x i j) 4
      (volume.restrict (euclBall c r)) ≤
      (∑ b, ‖L.e b i j‖ₑ) * ∑ b, eLpNorm (fn (a ν b)) 4 (volume.restrict (euclBall c r)) := by
    intro ν i j
    rw [eLpNorm_congr_ae (evM_embX_entry L (a ν) i j)]
    refine (eLpNorm_sum_ofReal_mul_le' (by norm_num) _ _ _ fun b =>
      (memLp_fn _).aestronglyMeasurable).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun b _ => ?_
    gcongr
    exact Finset.single_le_sum (f := fun b' => eLpNorm (fn (a ν b')) 4
        (volume.restrict (euclBall c r))) (fun _ _ => zero_le) (Finset.mem_univ b)
  have hK : ∑ i, ∑ j, ∑ b, ‖L.e b i j‖ₑ = L.Ke := by
    unfold LieBasis.Ke
    calc ∑ i, ∑ j, ∑ b, ‖L.e b i j‖ₑ = ∑ i, ∑ b, ∑ j, ‖L.e b i j‖ₑ :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ b, ∑ i, ∑ j, ‖L.e b i j‖ₑ := Finset.sum_comm
  calc bL4 c r (fun ν i j x => evM (embX L (a ν)) x i j)
      = ∑ ν, ∑ i, ∑ j, eLpNorm (fun x => evM (embX L (a ν)) x i j) 4
          (volume.restrict (euclBall c r)) := rfl
    _ ≤ ∑ ν, ∑ i, ∑ j, (∑ b, ‖L.e b i j‖ₑ) *
          ∑ b, eLpNorm (fn (a ν b)) 4 (volume.restrict (euclBall c r)) :=
        Finset.sum_le_sum fun ν _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          h1 ν i j
    _ = ∑ ν, L.Ke * ∑ b, eLpNorm (fn (a ν b)) 4 (volume.restrict (euclBall c r)) := by
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [← hK, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]
    _ = L.Ke * coordL4 a := by rw [← Finset.mul_sum]; rfl

/-- **Coefficient norms by entry norms.** -/
theorem coords_le_bL4 (L : LieBasis m d) (a : Fin 4 → Fin d → SobAlg c r 4) :
    coordL4 a ≤ L.Kκ * bL4 c r (fun ν i j x => evM (embX L (a ν)) x i j) := by
  have hm : ∀ ν i j, AEStronglyMeasurable (fun x => evM (embX L (a ν)) x i j)
      (volume.restrict (euclBall c r)) := fun ν i j => (memLp_evC _).aestronglyMeasurable
  have hterm : ∀ ν b i j, eLpNorm (fun x => (evM (embX L (a ν)) x i j).re * L.α b i j +
      (evM (embX L (a ν)) x i j).im * L.β b i j) 4 (volume.restrict (euclBall c r)) ≤
      (‖L.α b i j‖ₑ + ‖L.β b i j‖ₑ) * eLpNorm (fun x => evM (embX L (a ν)) x i j) 4
        (volume.restrict (euclBall c r)) := by
    intro ν b i j
    refine (eLpNorm_add_le ((Complex.continuous_re.comp_aestronglyMeasurable (hm ν i j)).mul_const _)
      ((Complex.continuous_im.comp_aestronglyMeasurable (hm ν i j)).mul_const _) (by norm_num)).trans ?_
    rw [add_mul]
    refine add_le_add ?_ ?_
    · rw [show (fun x => (evM (embX L (a ν)) x i j).re * L.α b i j) =
          L.α b i j • fun x => (evM (embX L (a ν)) x i j).re by funext x; simp [mul_comm],
        eLpNorm_const_smul]
      gcongr
      exact eLpNorm_mono fun x => by simpa using Complex.abs_re_le_norm _
    · rw [show (fun x => (evM (embX L (a ν)) x i j).im * L.β b i j) =
          L.β b i j • fun x => (evM (embX L (a ν)) x i j).im by funext x; simp [mul_comm],
        eLpNorm_const_smul]
      gcongr
      exact eLpNorm_mono fun x => by simpa using Complex.abs_im_le_norm _
  have h1 : ∀ ν b, eLpNorm (fn (a ν b)) 4 (volume.restrict (euclBall c r)) ≤
      (∑ i, ∑ j, (‖L.α b i j‖ₑ + ‖L.β b i j‖ₑ)) * ∑ i, ∑ j,
        eLpNorm (fun x => evM (embX L (a ν)) x i j) 4 (volume.restrict (euclBall c r)) := by
    intro ν b
    have e1 : fn (a ν b) =ᵐ[volume.restrict (euclBall c r)] fun x => ∑ i, ∑ j,
        ((evM (embX L (a ν)) x i j).re * L.α b i j + (evM (embX L (a ν)) x i j).im * L.β b i j) := by
      have := fn_coordL L (embX L (a ν)) b
      rw [coordL_embX] at this
      filter_upwards [this] with x hx
      rw [hx, LieBasis.κ_apply]
    rw [eLpNorm_congr_ae e1]
    have hmt : ∀ i j, AEStronglyMeasurable (fun x => (evM (embX L (a ν)) x i j).re * L.α b i j +
        (evM (embX L (a ν)) x i j).im * L.β b i j) (volume.restrict (euclBall c r)) := fun i j =>
      ((Complex.continuous_re.comp_aestronglyMeasurable (hm ν i j)).mul_const _).add
        ((Complex.continuous_im.comp_aestronglyMeasurable (hm ν i j)).mul_const _)
    have e2 : (fun x => ∑ i, ∑ j, ((evM (embX L (a ν)) x i j).re * L.α b i j +
        (evM (embX L (a ν)) x i j).im * L.β b i j)) = ∑ i, ∑ j, fun x =>
        ((evM (embX L (a ν)) x i j).re * L.α b i j + (evM (embX L (a ν)) x i j).im * L.β b i j) := by
      funext x; simp [Finset.sum_apply]
    rw [e2]
    refine (eLpNorm_sum_le (fun i _ => Finset.aestronglyMeasurable_sum _ fun j _ => hmt i j)
      (by norm_num)).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    refine (eLpNorm_sum_le (fun j _ => hmt i j) (by norm_num)).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => (hterm ν b i j).trans ?_
    gcongr
    exact (Finset.single_le_sum (f := fun j' => eLpNorm (fun x => evM (embX L (a ν)) x i j') 4
      (volume.restrict (euclBall c r))) (fun _ _ => zero_le) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i' => ∑ j', eLpNorm (fun x => evM (embX L (a ν)) x i' j') 4
        (volume.restrict (euclBall c r))) (fun _ _ => zero_le) (Finset.mem_univ i))
  calc coordL4 a = ∑ ν, ∑ b, eLpNorm (fn (a ν b)) 4 (volume.restrict (euclBall c r)) := rfl
    _ ≤ ∑ ν, ∑ b, (∑ i, ∑ j, (‖L.α b i j‖ₑ + ‖L.β b i j‖ₑ)) * ∑ i, ∑ j,
          eLpNorm (fun x => evM (embX L (a ν)) x i j) 4 (volume.restrict (euclBall c r)) :=
        Finset.sum_le_sum fun ν _ => Finset.sum_le_sum fun b _ => h1 ν b
    _ = ∑ ν, L.Kκ * ∑ i, ∑ j,
          eLpNorm (fun x => evM (embX L (a ν)) x i j) 4 (volume.restrict (euclBall c r)) := by
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [← Finset.sum_mul]; rfl
    _ = L.Kκ * bL4 c r (fun ν i j x => evM (embX L (a ν)) x i j) := by
        rw [← Finset.mul_sum]; rfl

theorem sum_slice_le (v : Fin 4 × Fin 4 × Fin m × Fin m → ℝ) (hv : ∀ p, 0 ≤ v p) (μ ν : Fin 4) :
    ∑ k, ∑ l, v (μ, ν, k, l) ≤ ∑ p, v p := by
  calc ∑ k, ∑ l, v (μ, ν, k, l) ≤ ∑ ν', ∑ k, ∑ l, v (μ, ν', k, l) :=
        Finset.single_le_sum (f := fun ν' => ∑ k, ∑ l, v (μ, ν', k, l))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hv _)
          (Finset.mem_univ ν)
    _ ≤ ∑ μ', ∑ ν', ∑ k, ∑ l, v (μ', ν', k, l) :=
        Finset.single_le_sum (f := fun μ' => ∑ ν', ∑ k, ∑ l, v (μ', ν', k, l))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
            Finset.sum_nonneg fun _ _ => hv _) (Finset.mem_univ μ)
    _ = ∑ p, v p := by simp only [Fintype.sum_prod_type]

/-! ### The a-priori estimate for Coulomb gauge states -/

/-- **The critical a-priori estimate for Coulomb gauge states**: there are `δ > 0` and `C < ∞`
(depending on the basis `L` only) such that for every unitary `u ∈ H⁵(B, M_m(ℂ))`, every smooth
connection `B_f` and every tangential Coulomb `𝔤`-valued `a = u·B_f` with coefficient `L⁴` norm
`≤ δ`, the coefficient `L⁴` norm is at most `C (∫_B |F_{B_f}|²)^{1/2}`. -/
theorem coulomb_state_apriori (L : LieBasis m d) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (u : MatSob c r 5 m), u * star u = 1 →
      ∀ (Bf : CriticalGauge.MConn m) (hB : ∀ μ i j, ContDiff ℝ ∞ (fun x => Bf μ x i j))
        (a : Fin 4 → Fin d → SobAlg c r 4), a ∈ TSp (c := c) (r := r) d → coulF L (a, 0) = 0 →
        (∀ μ, actM u (star u) (fun κ => matOfSmooth (c := c) (r := r) 4 (Bf κ) (hB κ)) μ =
          embX L (a μ)) →
        coordL4 a ≤ δ →
        coordL4 a ≤ C * (∫⁻ x in euclBall c r, ‖CriticalGauge.curvVec Bf x‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
  obtain ⟨δw, hδw, Cw, hW⟩ := coulomb_apriori_weak m
  refine ⟨(δw : ℝ≥0∞) / (L.Ke + 1), ENNReal.div_pos (by exact_mod_cast hδw.ne')
      (ENNReal.add_ne_top.mpr ⟨L.Ke_ne_top, ENNReal.one_ne_top⟩),
    L.Kκ * (Cw * (16 * (m : ℝ≥0∞) ^ 2)), ENNReal.mul_ne_top L.Kκ_ne_top
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (by simp [ENNReal.mul_eq_top])),
    fun u hu Bf hB a ha hcoul hact hS => ?_⟩
  set ρ := volume.restrict (euclBall c r)
  set E := (∫⁻ x in euclBall c r, ‖CriticalGauge.curvVec Bf x‖ₑ ^ 2) ^ (1 / 2 : ℝ)
  have hweak := isWeakBallCoulomb_embX L ha hcoul
  -- smallness of the entry norms
  have hsmall : bL4 c r (fun ν i j x => evM (embX L (a ν)) x i j) ≤ δw := by
    refine (bL4_le_coords L a).trans ?_
    calc L.Ke * coordL4 a ≤ L.Ke * ((δw : ℝ≥0∞) / (L.Ke + 1)) := by gcongr
      _ ≤ (L.Ke + 1) * ((δw : ℝ≥0∞) / (L.Ke + 1)) := by gcongr; exact le_self_add
      _ = δw := ENNReal.mul_div_cancel (by simp) (ENNReal.add_ne_top.mpr ⟨L.Ke_ne_top,
            ENNReal.one_ne_top⟩)
  obtain ⟨hX, -, -⟩ := hW c r hr.out _ _ hweak hsmall
  -- the curvature bound
  have hcurv : wCurvNorm c r (fun ν i j x => evM (embX L (a ν)) x i j)
      (fun ν i j μ x => evM (derM μ (embX L (a ν))) x i j) ≤ 16 * (m : ℝ≥0∞) ^ 2 * E := by
    -- the pointwise bound of each entry by the curvature norm of `B_f`
    have hU : ∀ᵐ x ∂ρ, star (evM u x) * evM u x = 1 := by
      filter_upwards [evM_mul u (star u), evM_star u, evM_one (c := c) (r := r) (s := 5) (m := m)]
        with x h1 h2 h3
      have : evM u x * star (evM u x) = 1 := by rw [← h2, ← h1, hu, h3]
      exact mul_eq_one_comm.mp this
    have hent : ∀ μ ν i j, ∀ᵐ x ∂ρ, ‖wCurv (fun ν i j x => evM (embX L (a ν)) x i j)
        (fun ν i j μ x => evM (derM μ (embX L (a ν))) x i j) μ ν i j x‖ ≤
        ‖CriticalGauge.curvVec Bf x‖ := by
      intro μ ν i j
      have hcov := curvMS_actM (s := 3) (mul_eq_one_comm.mp (mul_eq_one_comm.mp hu))
        (fun κ => matOfSmooth (c := c) (r := r) 4 (Bf κ) (hB κ)) μ ν
      have heq : (fun κ => embX L (a κ)) =
          actM u (star u) (fun κ => matOfSmooth (c := c) (r := r) 4 (Bf κ) (hB κ)) :=
        funext fun κ => (hact κ).symm
      filter_upwards [wCurv_embX_ae L a μ ν i j, hU,
        evM_mul (rhoM (rhoM u) * curvMS (fun κ => matOfSmooth (c := c) (r := r) 4 (Bf κ) (hB κ)) μ ν)
          (rhoM (rhoM (star u))),
        evM_mul (rhoM (rhoM u)) (curvMS (fun κ => matOfSmooth (c := c) (r := r) 4 (Bf κ) (hB κ)) μ ν),
        evM_star u, evM_curvMS_matOfSmooth (c := c) (r := r) hB μ ν] with x h1 h2 h3 h4 h5 h6
      rw [h1, heq, hcov, h3, h4, evM_rhoM, evM_rhoM, evM_rhoM, evM_rhoM, h5, h6]
      refine (norm_conj_entry_le h2 i j).trans ?_
      rw [EuclideanSpace.norm_eq]
      apply Real.sqrt_le_sqrt
      exact (le_of_eq rfl).trans (sum_slice_le (fun p => ‖CriticalGauge.curvVec Bf x p‖ ^ 2)
        (fun _ => sq_nonneg _) μ ν)
    have hE : eLpNorm (fun x => ‖CriticalGauge.curvVec Bf x‖) 2 ρ = E := by
      rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
      simp only [E, ENNReal.toReal_ofNat, enorm_norm]
      congr 1
      · refine lintegral_congr fun x => ?_
        rw [← ENNReal.rpow_natCast]
        norm_num
    unfold wCurvNorm
    calc ∑ μ, ∑ ν, ∑ i, ∑ j, eLpNorm (wCurv (fun ν i j x => evM (embX L (a ν)) x i j)
          (fun ν i j μ x => evM (derM μ (embX L (a ν))) x i j) μ ν i j) 2 ρ
        ≤ ∑ _μ : Fin 4, ∑ _ν : Fin 4, ∑ _i : Fin m, ∑ _j : Fin m,
            eLpNorm (fun x => ‖CriticalGauge.curvVec Bf x‖) 2 ρ := by
          refine Finset.sum_le_sum fun μ _ => Finset.sum_le_sum fun ν _ =>
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          refine eLpNorm_mono_ae ?_
          filter_upwards [hent μ ν i j] with x hx
          simpa using hx
      _ = 16 * (m : ℝ≥0∞) ^ 2 * E := by
          rw [hE]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  calc coordL4 a ≤ L.Kκ * bL4 c r (fun ν i j x => evM (embX L (a ν)) x i j) := coords_le_bL4 L a
    _ ≤ L.Kκ * (Cw * wCurvNorm c r (fun ν i j x => evM (embX L (a ν)) x i j)
          (fun ν i j μ x => evM (derM μ (embX L (a ν))) x i j)) := by gcongr
    _ ≤ L.Kκ * (Cw * (16 * (m : ℝ≥0∞) ^ 2 * E)) := by gcongr
    _ = L.Kκ * (Cw * (16 * (m : ℝ≥0∞) ^ 2)) * E := by ring

end RenewalGeometry.BallAnalysis.BallAlg
