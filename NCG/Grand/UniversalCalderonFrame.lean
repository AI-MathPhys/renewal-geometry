/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CalderonFrame
import NCG.Upstream.PrimitiveWeight

/-!
# sharp universal Calderón frame

This file completes `thm:universal-Calderon-frame`. Besides the exact
finite-cutoff identity already proved in `CalderonFrame`, it supplies the
sharp frame bounds under the spectral floor `L ≥ mQ`, proves quadratic
convergence of the cutoff Gram to `Q`, and specializes that limit to the
isometry statement on the reducing subspace `QH`.
-/

open Matrix NormedSpace Filter
open scoped ComplexOrder MatrixOrder

namespace NCG

set_option linter.unusedDecidableInType false
set_option maxHeartbeats 800000

theorem matrix_exp_eq_bare_cfc {d : ℕ}
    (R : Matrix (Fin d) (Fin d) ℂ) (hR : R.IsHermitian) (c : ℝ) :
    exp (c • R) = hR.cfc (fun x => Real.exp (c * x)) := by
  let U := hR.eigenvectorUnitary
  let D : Matrix (Fin d) (Fin d) ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ hR.eigenvalues)
  let Dc : Matrix (Fin d) (Fin d) ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ (fun x => c * x) ∘ hR.eigenvalues)
  have hdiag : c • D = Dc := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D, Dc, Function.comp_def]
    · simp [D, Dc, Matrix.diagonal_apply_ne _ hij]
  have hscaled : c • R =
      (U : Matrix (Fin d) (Fin d) ℂ) * Dc *
        star (U : Matrix (Fin d) (Fin d) ℂ) := by
    rw [hR.spectral_theorem]
    change c • ((U : Matrix (Fin d) (Fin d) ℂ) * D * star
      (U : Matrix (Fin d) (Fin d) ℂ)) = _
    rw [← smul_mul_assoc, ← mul_smul_comm, hdiag]
  rw [hscaled]
  change exp ((↑(Unitary.toUnits U) : Matrix (Fin d) (Fin d) ℂ) * Dc *
      (↑((Unitary.toUnits U)⁻¹) : Matrix (Fin d) (Fin d) ℂ)) = _
  rw [Matrix.exp_units_conj]
  dsimp only [Dc]
  rw [Matrix.exp_diagonal]
  rw [Pi.exp_def]
  simp_rw [← Complex.exp_eq_exp_ℂ]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  have hstar : (↑((Unitary.toUnits U)⁻¹) : Matrix (Fin d) (Fin d) ℂ) =
      star (U : Matrix (Fin d) (Fin d) ℂ) := rfl
  rw [hstar]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp [U, Function.comp_def, Complex.ofReal_exp]
  · simp [U, Matrix.IsHermitian.eigenvectorUnitary_apply]

theorem exp_neg_psd_bounds {d : ℕ}
    (R : Matrix (Fin d) (Fin d) ℂ) (hR : R.PosSemidef)
    (A : ℝ) (hA : 0 ≤ A) :
    (exp ((-A) • R)).PosSemidef ∧
      (1 - exp ((-A) • R)).PosSemidef := by
  let hRH : R.IsHermitian := hR.isHermitian
  have hexp : exp ((-A) • R) =
      hRH.cfc (fun x => Real.exp ((-A) * x)) :=
    matrix_exp_eq_bare_cfc R hRH (-A)
  constructor
  · rw [hexp]
    exact Upstream.PrimitiveWeight.cfc_posSemidef hRH
      (fun i => Real.exp_nonneg _)
  · have hone : hRH.cfc (fun _ => (1 : ℝ)) =
        (1 : Matrix (Fin d) (Fin d) ℂ) := by
      simpa using Upstream.PrimitiveWeight.cfc_const hRH 1
    rw [hexp, ← hone, Upstream.PrimitiveWeight.cfc_sub]
    apply Upstream.PrimitiveWeight.cfc_posSemidef hRH
    intro i
    apply sub_nonneg.mpr
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hA)
      (hR.eigenvalues_nonneg i)

theorem exp_smul_projection {d : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℂ) (hQH : Q.IsHermitian)
    (hQ2 : Q * Q = Q) (c : ℝ) :
    exp (c • Q) = 1 + (Real.exp c - 1) • Q := by
  rw [matrix_exp_eq_bare_cfc Q hQH c]
  have hpoint : ∀ i,
      Real.exp (c * hQH.eigenvalues i) =
        1 + (Real.exp c - 1) * hQH.eigenvalues i := by
    intro i
    have hi := (show IsIdempotentElem Q from hQ2).spectrum_subset ℝ
      (hQH.eigenvalues_mem_spectrum_real i)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with hi | hi
    · simp [hi]
    · simp [hi]
  rw [Upstream.PrimitiveWeight.cfc_congr hQH
    (f := fun x => Real.exp (c * x))
    (g := fun x => 1 + (Real.exp c - 1) * x) hpoint]
  rw [← Upstream.PrimitiveWeight.cfc_add hQH,
    ← Upstream.PrimitiveWeight.cfc_mul hQH,
    Upstream.PrimitiveWeight.cfc_const hQH,
    Upstream.PrimitiveWeight.cfc_const hQH]
  have hid : hQH.cfc (fun x => x) = Q := by
    change hQH.cfc id = Q
    exact Upstream.PrimitiveWeight.cfc_id' hQH
  rw [hid]
  ext i j
  simp [Matrix.smul_apply, Complex.real_smul]

/-- Sharp finite-cutoff Calderón bounds on a reducing projection. -/
theorem universal_calderon_frame_bounds {d : ℕ}
    (L Q : Matrix (Fin d) (Fin d) ℂ) (_hL : L.PosSemidef)
    (hQH : Q.IsHermitian) (hQ2 : Q * Q = Q)
    (hcomm : L * Q = Q * L) (m A : ℝ) (_hm : 0 < m) (hA : 0 < A)
    (hfloor : m • Q ≤ L) :
    (1 - Real.exp (-(A * m))) • Q ≤
        Q - exp ((-A) • L) * Q ∧
      Q - exp ((-A) • L) * Q ≤ Q := by
  let R : Matrix (Fin d) (Fin d) ℂ := L - m • Q
  let E : Matrix (Fin d) (Fin d) ℂ := exp ((-A) • R)
  have hR : R.PosSemidef := by
    exact Matrix.le_iff.mp hfloor
  have hQ : Q.PosSemidef := by
    rw [hQH.posSemidef_iff_eigenvalues_nonneg]
    intro i
    have hi := (show IsIdempotentElem Q from hQ2).spectrum_subset ℝ
      (hQH.eigenvalues_mem_spectrum_real i)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with hi | hi <;> simp [hi]
  have hRQ : Commute R Q := by
    change (L - m • Q) * Q = Q * (L - m • Q)
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
      Matrix.mul_smul, hcomm, hQ2]
  have hEQ : Commute E Q := by
    exact (hRQ.smul_left (-A)).exp_left
  have hE : E.PosSemidef := (exp_neg_psd_bounds R hR A hA.le).1
  have hIE : (1 - E).PosSemidef :=
    (exp_neg_psd_bounds R hR A hA.le).2
  have hEQpsd : (E * Q).PosSemidef := by
    have hc := hE.mul_mul_conjTranspose_same Q
    rw [hQH] at hc
    have heq : Q * E * Q = E * Q := by
      rw [← hEQ.eq, Matrix.mul_assoc, hQ2]
    rwa [heq] at hc
  have hIEQpsd : ((1 - E) * Q).PosSemidef := by
    have hc := hIE.mul_mul_conjTranspose_same Q
    rw [hQH] at hc
    have hcommIE : (1 - E) * Q = Q * (1 - E) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
        hEQ.eq]
    have heq : Q * (1 - E) * Q = (1 - E) * Q := by
      rw [← hcommIE, Matrix.mul_assoc, hQ2]
    rwa [heq] at hc
  have hdecomp : (-A) • L =
      (-A) • R + (-(A * m)) • Q := by
    dsimp only [R]
    module
  have hsplit : exp ((-A) • L) =
      E * exp ((-(A * m)) • Q) := by
    rw [hdecomp, Matrix.exp_add_of_commute]
    exact (hRQ.smul_left (-A)).smul_right (-(A * m))
  have hfactorQ : exp ((-A) • L) * Q =
      Real.exp (-(A * m)) • (E * Q) := by
    rw [hsplit, Matrix.mul_assoc,
      exp_smul_projection Q hQH hQ2 (-(A * m)), Matrix.add_mul,
      Matrix.one_mul, Matrix.smul_mul, hQ2]
    have hinner : Q + (Real.exp (-(A * m)) - 1) • Q =
        Real.exp (-(A * m)) • Q := by module
    rw [hinner, mul_smul_comm]
  constructor
  · rw [Matrix.le_iff, hfactorQ]
    have heq :
        (Q - Real.exp (-(A * m)) • (E * Q)) -
            (1 - Real.exp (-(A * m))) • Q =
          Real.exp (-(A * m)) • ((1 - E) * Q) := by
      rw [Matrix.sub_mul, Matrix.one_mul]
      module
    rw [heq]
    exact hIEQpsd.smul (Real.exp_nonneg _)
  · rw [Matrix.le_iff]
    have htail : (exp ((-A) • L) * Q).PosSemidef := by
      rw [hfactorQ]
      exact hEQpsd.smul (Real.exp_nonneg _)
    have heq : Q - (Q - exp ((-A) • L) * Q) =
        exp ((-A) • L) * Q := by abel
    rw [heq]
    exact htail

/-- As the cutoff tends to infinity, the compressed Calderón Gram
operator converges quadratically to the support projection. -/
theorem universal_calderon_frame_isometry_limit {d : ℕ}
    (L Q : Matrix (Fin d) (Fin d) ℂ) (hL : L.PosSemidef)
    (hQH : Q.IsHermitian) (hQ2 : Q * Q = Q)
    (hcomm : L * Q = Q * L) (m : ℝ) (hm : 0 < m)
    (hfloor : m • Q ≤ L) (x : Fin d → ℂ) :
    Tendsto
      (fun A : ℝ =>
        (star x ⬝ᵥ ((Q - exp ((-A) • L) * Q) *ᵥ x)).re)
      atTop (nhds ((star x ⬝ᵥ (Q *ᵥ x)).re)) := by
  let q : ℝ := (star x ⬝ᵥ (Q *ᵥ x)).re
  let f : ℝ → ℝ := fun A =>
    (star x ⬝ᵥ ((Q - exp ((-A) • L) * Q) *ᵥ x)).re
  have hlower : Tendsto
      (fun A : ℝ => (1 - Real.exp (-(A * m))) * q)
      atTop (nhds q) := by
    have hmul : Tendsto (fun A : ℝ => A * m) atTop atTop :=
      Tendsto.atTop_mul_const hm tendsto_id
    have hexp0 : Tendsto (fun A : ℝ => Real.exp (-(A * m)))
        atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hmul
    convert (tendsto_const_nhds.sub hexp0).mul_const q using 1 <;> simp
  have hlowEventually : ∀ᶠ A in atTop,
      (1 - Real.exp (-(A * m))) * q ≤ f A := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with A hA
    have hb := (universal_calderon_frame_bounds L Q hL hQH hQ2
      hcomm m A hm hA hfloor).1
    have hn := (Matrix.le_iff.mp hb).re_dotProduct_nonneg x
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec] at hn
    simp only [dotProduct_sub, dotProduct_smul] at hn
    change 0 ≤ f A -
      (((1 - Real.exp (-(A * m)) : ℝ) : ℂ) *
        (star x ⬝ᵥ (Q *ᵥ x))).re at hn
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] at hn
    exact sub_nonneg.mp hn
  have huppEventually : ∀ᶠ A in atTop, f A ≤ q := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with A hA
    have hb := (universal_calderon_frame_bounds L Q hL hQH hQ2
      hcomm m A hm hA hfloor).2
    have hn := (Matrix.le_iff.mp hb).re_dotProduct_nonneg x
    rw [Matrix.sub_mulVec] at hn
    simp only [dotProduct_sub] at hn
    change 0 ≤ q - f A at hn
    exact sub_nonneg.mp hn
  change Tendsto f atTop (nhds q)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlower tendsto_const_nhds hlowEventually huppEventually

/-- On vectors in the reducing subspace, the infinite-cutoff Gram is
the ambient squared norm: the universal Calderón transform is isometric. -/
theorem universal_calderon_frame_infinite_isometry {d : ℕ}
    (L Q : Matrix (Fin d) (Fin d) ℂ) (hL : L.PosSemidef)
    (hQH : Q.IsHermitian) (hQ2 : Q * Q = Q)
    (hcomm : L * Q = Q * L) (m : ℝ) (hm : 0 < m)
    (hfloor : m • Q ≤ L) (x : Fin d → ℂ) (hx : Q *ᵥ x = x) :
    Tendsto
      (fun A : ℝ =>
        (star x ⬝ᵥ ((Q - exp ((-A) • L) * Q) *ᵥ x)).re)
      atTop (nhds ((star x ⬝ᵥ x).re)) := by
  simpa only [hx] using
    universal_calderon_frame_isometry_limit L Q hL hQH hQ2 hcomm
      m hm hfloor x

end NCG
