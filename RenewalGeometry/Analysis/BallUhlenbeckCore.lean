/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallFinalTools

/-!
# Smooth representatives of Sobolev gauges and complex weak derivatives of matrix fields
  (stage D4 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `hasWeakPartial_re_im` — complex weak derivatives from real and imaginary parts;
* `hasWeakPartial_evM` — the entries of `X ∈ H^{s+1}(B, M_m(ℂ))` have the entries of `∂_i X` as
  complex weak derivatives;
* `exists_smooth_rep_matrix` (**main result**) — a matrix field `u ∈ H⁵(B, M_m(ℂ))` with lifts to
  every `H^{j+5}` has a representative `U`, `C^∞` on the open ball, with `U = u` and
  `∂_μU = ∂_μu` almost everywhere on the ball.
-/

open MeasureTheory Set Metric Filter Topology NormedSpace
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section

namespace RenewalGeometry.BallAnalysis.UhlenbeckCore

open SobolevOpen BallReg BallAlg SobAlg FinalTools

set_option linter.unusedSectionVars false

/-! ### Complex weak derivatives -/

theorem hasWeakPartial_re_im {Ω : Set (Fin 4 → ℝ)} {i : Fin 4} {u v g h : (Fin 4 → ℝ) → ℝ}
    (hu : HasWeakPartialR Ω i u g) (hv : HasWeakPartialR Ω i v h)
    (hul : MemLp u 2 (volume.restrict Ω)) (hvl : MemLp v 2 (volume.restrict Ω))
    (hgl : MemLp g 2 (volume.restrict Ω)) (hhl : MemLp h 2 (volume.restrict Ω)) :
    HasWeakPartial Ω i (fun x => ((u x : ℝ) : ℂ) + ((v x : ℝ) : ℂ) * Complex.I)
      (fun x => ((g x : ℝ) : ℂ) + ((h x : ℝ) : ℂ) * Complex.I) := by
  intro φ hφ
  have hu' := hasWeakPartialR_iff.mp hu φ hφ
  have hv' := hasWeakPartialR_iff.mp hv φ hφ
  have hli : ∀ {w : (Fin 4 → ℝ) → ℝ}, MemLp w 2 (volume.restrict Ω) →
      LocallyIntegrableOn (fun x => ((w x : ℝ) : ℂ)) Ω := fun hw =>
    locallyIntegrableOn_of_memLp hw.ofReal
  have i1 := hφ.integrable_mul (ψ := pd φ i) (continuous_pd (hφ.smooth.of_le (by simp)) i)
    (tsupport_pd_subset φ i) (hli hul)
  have i2 := hφ.integrable_mul (ψ := pd φ i) (continuous_pd (hφ.smooth.of_le (by simp)) i)
    (tsupport_pd_subset φ i) (hli hvl)
  have i3 := hφ.integrable_mul (ψ := φ) hφ.continuous le_rfl (hli hgl)
  have i4 := hφ.integrable_mul (ψ := φ) hφ.continuous le_rfl (hli hhl)
  have e1 : (fun x => ((pd φ i x : ℝ) : ℂ) * (((u x : ℝ) : ℂ) + ((v x : ℝ) : ℂ) * Complex.I)) =
      fun x => ((pd φ i x : ℝ) : ℂ) * ((u x : ℝ) : ℂ) +
        ((pd φ i x : ℝ) : ℂ) * ((v x : ℝ) : ℂ) * Complex.I := by funext x; ring
  have e2 : (fun x => ((φ x : ℝ) : ℂ) * (((g x : ℝ) : ℂ) + ((h x : ℝ) : ℂ) * Complex.I)) =
      fun x => ((φ x : ℝ) : ℂ) * ((g x : ℝ) : ℂ) + ((φ x : ℝ) : ℂ) * ((h x : ℝ) : ℂ) * Complex.I := by
    funext x; ring
  rw [e1, e2, integral_add i1 (i2.mul_const _), integral_add i3 (i4.mul_const _),
    integral_mul_const, integral_mul_const, hu', hv']
  ring

theorem hasWeakPartial_evC {c : Fin 4 → ℝ} {r : ℝ} [Fact (0 < r)] {s : ℕ} [Fact (3 ≤ s)]
    (z : Cx (SobAlg c r (s + 1))) (i : Fin 4) :
    HasWeakPartial (euclBall c r) i (evC z)
      (evC (⟨derS i z.re, derS i z.im⟩ : Cx (SobAlg c r s))) :=
  hasWeakPartial_re_im (weak_derS i z.re) (weak_derS i z.im) (memLp_fn _) (memLp_fn _)
    (memLp_fn _) (memLp_fn _)

theorem hasWeakPartial_evM {c : Fin 4 → ℝ} {r : ℝ} [Fact (0 < r)] {s : ℕ} [Fact (3 ≤ s)] {m : ℕ}
    (X : MatSob c r (s + 1) m) (i : Fin 4) (a b : Fin m) :
    HasWeakPartial (euclBall c r) i (fun x => evM X x a b) (fun x => evM (derM i X) x a b) :=
  hasWeakPartial_evC (X a b) i

theorem integral_test_eq_setIntegral_complex {Ω : Set (Fin 4 → ℝ)} {φ : (Fin 4 → ℝ) → ℝ}
    (hφ : IsTest Ω φ) (v : (Fin 4 → ℝ) → ℂ) :
    ∫ x, ((φ x : ℝ) : ℂ) * v x = ∫ x in Ω, ((φ x : ℝ) : ℂ) * v x := by
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
  rw [isTest_vanish hφ x hx]; simp

/-! ### Smooth representatives of matrix fields -/

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {m : ℕ}

/-- An `H⁵` element lifting to every level lies in every `H^k`. -/
theorem memHk_all_of_lift {X : SobAlg c r 5}
    (hX : ∀ j, ∃ Y : SobAlg c r (j + 5), restrS (by omega) Y = X) (k : ℕ) :
    MemHk (euclBall c r) k (fn X) := by
  obtain ⟨Y, hY⟩ := hX k
  rw [← hY, fn_restrS]
  exact (memHk_fn Y).mono (by omega)

/-- **Smooth representatives of Sobolev matrix fields with all lifts.** -/
theorem exists_smooth_rep_matrix {u : MatSob c r 5 m}
    (hlift : ∀ j, ∃ uj : MatSob c r (j + 5) m, restrM (by omega) uj = u) :
    ∃ U : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ,
      (∀ a b, ContDiffOn ℝ ∞ (fun x => U x a b) (euclBall c r)) ∧
      (∀ᵐ x ∂(volume.restrict (euclBall c r)), U x = evM u x) ∧
      ∀ μ, ∀ᵐ x ∂(volume.restrict (euclBall c r)), pdM U μ x = evM (derM μ u) x := by
  have hre : ∀ a b, ∀ j, ∃ Y : SobAlg c r (j + 5), restrS (by omega) Y = (u a b).re := by
    intro a b j
    obtain ⟨uj, huj⟩ := hlift j
    exact ⟨(uj a b).re, by rw [← huj]; rfl⟩
  have him : ∀ a b, ∀ j, ∃ Y : SobAlg c r (j + 5), restrS (by omega) Y = (u a b).im := by
    intro a b j
    obtain ⟨uj, huj⟩ := hlift j
    exact ⟨(uj a b).im, by rw [← huj]; rfl⟩
  choose fr hfr hfr1 hfr2 using fun a b =>
    SmoothRep.exists_smooth_rep c r hr.out (memHk_all_of_lift (hre a b))
  choose fi hfi hfi1 hfi2 using fun a b =>
    SmoothRep.exists_smooth_rep c r hr.out (memHk_all_of_lift (him a b))
  set U : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ := fun x => Matrix.of fun a b =>
    ((fr a b x : ℝ) : ℂ) + ((fi a b x : ℝ) : ℂ) * Complex.I
  have hBo := isOpen_euclBall c r
  have hUs : ∀ a b, ContDiffOn ℝ ∞ (fun x => U x a b) (euclBall c r) := fun a b =>
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn (hfr a b)).add
      ((Complex.ofRealCLM.contDiff.comp_contDiffOn (hfi a b)).mul contDiffOn_const))
  refine ⟨U, hUs, ?_, fun μ => ?_⟩
  · refine ae_matrix_of_entries fun a b => ?_
    filter_upwards [hfr1 a b, hfi1 a b] with x h1 h2
    simp only [U, Matrix.of_apply, evM_apply, evC, h1, h2]
  · refine ae_matrix_of_entries fun a b => ?_
    -- the classical derivative is a weak derivative of the entry, hence the Sobolev one
    have hcl : HasWeakPartial (euclBall c r) μ (fun x => U x a b) (pd (fun x => U x a b) μ) :=
      hasWeakPartial_of_contDiffOn hBo ((hUs a b).of_le (by simp)) μ
    have hcl' : HasWeakPartial (euclBall c r) μ (fun x => U x a b)
        (fun x => evM (derM μ u) x a b) := by
      have h1 := hasWeakPartial_evM u μ a b
      intro φ hφ
      have e : ∫ x, ((pd φ μ x : ℝ) : ℂ) * U x a b = ∫ x, ((pd φ μ x : ℝ) : ℂ) * evM u x a b := by
        rw [integral_test_eq_setIntegral_complex (isTest_pd hφ μ),
          integral_test_eq_setIntegral_complex (isTest_pd hφ μ)]
        refine integral_congr_ae ?_
        filter_upwards [hfr1 a b, hfi1 a b] with x h1 h2
        simp only [U, Matrix.of_apply, evM_apply, evC, h1, h2]
      rw [e]
      exact h1 φ hφ
    have hli1 : LocallyIntegrableOn (pd (fun x => U x a b) μ) (euclBall c r) :=
      (((hUs a b).continuousOn_fderiv_of_isOpen hBo (by simp)).clm_apply
        continuousOn_const).locallyIntegrableOn (measurableSet_euclBall c r)
    have hli2 : LocallyIntegrableOn (fun x => evM (derM μ u) x a b) (euclBall c r) :=
      locallyIntegrableOn_of_memLp (memLp_evC _)
    have := hcl.ae_eq hBo hcl' hli1 hli2
    rw [EventuallyEq, ae_restrict_iff' (measurableSet_euclBall c r)]
    filter_upwards [this] with x hx hxB
    exact hx hxB

end RenewalGeometry.BallAnalysis.UhlenbeckCore
