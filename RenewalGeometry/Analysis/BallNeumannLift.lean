/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallContinuityMethod

/-!
# Elliptic regularity lifts for Neumann fields in the Banach algebras `H^s(B)`
  (stages D2/D4 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `memHk_of_neumannS` — a weakly Neumann `X ∈ H⁵(B)` with `ΔX ∈ H^k(B)` lies in `H^{k+2}(B)`
  (uniqueness of the Lax–Milgram solution `component_eq_sol` with zero coefficients, and the
  Neumann regularity `neumann_Hk_weak`);
* `exists_lift_neumannS` — such an `X` is the restriction of an element of `H^{k+2}(B)`;
* `restrM`, `isNeumannS_re/im` and `exists_lift_neumannM` — the matrix-valued versions: a
  Neumann matrix field `u ∈ H⁵(B, M_m(ℂ))` whose Laplacian is the restriction of an `H^k` field
  lifts to `H^{k+2}(B, M_m(ℂ))`.
-/

open MeasureTheory Set Metric Filter Topology NormedSpace
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator RealInnerProductSpace

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallAlg

open SobolevOpen BallReg SobAlg

set_option linter.unusedSectionVars false

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {m : ℕ}

/-! ### Scalar fields -/

theorem isTangentialS_zero : IsTangentialS (c := c) (r := r) (fun _ => (0 : SobAlg c r 4)) :=
  mem_tanSub.mp (tanSub (c := c) (r := r)).zero_mem

/-- **Neumann regularity in `H^s(B)`**: a weakly Neumann mean-zero `X ∈ H⁵(B)` with
`ΔX ∈ H^k(B)` lies in `H^{k+2}(B)`. -/
theorem memHk_of_neumannS {k : ℕ} {X : SobAlg c r 5} (hN : IsNeumannS X) (hm : meanS X = 0)
    (hk : MemHk (euclBall c r) k (fn (lapS X))) : MemHk (euclBall c r) (k + 2) (fn X) := by
  set A : Fin 4 → Fin 1 → Fin 1 → SobAlg c r 4 := fun _ _ _ => 0
  have htan : ∀ k l, IsTangentialS (fun ν => A ν k l) := fun _ _ => isTangentialS_zero
  set η : Fin 1 → SobAlg c r 5 := fun _ => X
  have hm' : ∀ k, meanS (η k) = 0 := fun _ => hm
  have hlin : linOpS A η = fun _ => lapS X := by
    funext k
    simp only [linOpS, A, η, zero_mul]
    have : divS (fun _ : Fin 4 => (0 : SobAlg c r 4)) = 0 := by simp [divS]
    simp [this]
  have hw := weak_toXi htan (fun _ => hN) hm'
  have hξ : ∀ ζ, dirFormN c r 1 (toXi η hm') ζ + couplingN c r 1 (memLp_coefFn A) (toXi η hm') ζ =
      loadN (linOpS A η) ζ := by
    intro ζ
    rw [hw ζ, loadN_apply]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_fn_mul _ (Lp.memLp _), Lp.toLp_coeFn]
    congr 1
    exact (Lp.toLp_coeFn (fnL _) (memLp_fn _)).symm
  have hc := component_eq_sol htan hξ 0
  -- the data is `ΔX`
  have hcd : ((compData A (linOpS A η) (toXi η hm') 0 : L2B c r) : (Fin 4 → ℝ) → ℝ)
      =ᵐ[volume.restrict (euclBall c r)] fn (lapS X) := by
    have h0 : ∀ l, divData A 0 l (((toXi η hm' l : H1B0 c r) : H1Amb c r))
        =ᵐ[volume.restrict (euclBall c r)] fun _ => 0 := by
      intro l
      have hd : divS (fun ν => A ν 0 l) = 0 := by simp [divS, A]
      filter_upwards [fn_zero (c := c) (r := r) (s := 3), fn_zero (c := c) (r := r) (s := 4)]
        with z h1 h2
      simp only [divData, A, hd, h1, h2, zero_mul, Finset.sum_const_zero, add_zero]
    filter_upwards [compData_ae A (linOpS A η) (toXi η hm') 0, ae_all_iff.mpr h0] with z hz hz0
    rw [hz, hlin]
    simp [hz0]
  have h2 := neumann_Hk_weak c r k (hk.congr_ae hcd.symm)
  refine h2.congr_ae ?_
  have e1 : solFn c r (compData A (linOpS A η) (toXi η hm') 0) =
      (((toXi η hm' 0 : H1B0 c r) : H1Amb c r) none : (Fin 4 → ℝ) → ℝ) := by
    unfold solFn; rw [← hc]
  rw [e1, toXi_apply]
  exact toH1_none_ae X

theorem isNeumannS_one : IsNeumannS (1 : SobAlg c r 5) := by
  have h1 : ∀ ν, derS ν (1 : SobAlg c r 5) = 0 := fun ν => derS_one ν
  have hl : lapS (1 : SobAlg c r 5) = 0 := by simp [lapS, h1]
  have e1 : ∀ ν, fn (derS ν (1 : SobAlg c r 5)) =ᵐ[volume.restrict (euclBall c r)] fun _ => 0 :=
    fun ν => by rw [h1]; exact fn_zero
  have e2 : fn (lapS (1 : SobAlg c r 5)) =ᵐ[volume.restrict (euclBall c r)] fun _ => 0 := by
    rw [hl]; exact fn_zero
  have h0 : IsWeakTangential c r (fun _ => fun _ => (0 : ℝ)) (fun _ => 0) := fun φ hφ => by simp
  exact h0.congr_ae (fun ν => (e1 ν).symm) e2.symm

/-- **Lift of a Neumann field**: a weakly Neumann `X ∈ H⁵(B)` with `ΔX ∈ H^k(B)` is the
restriction of an element of `H^{k+2}(B)`. -/
theorem exists_lift_neumannS {k : ℕ} [Fact (3 ≤ k + 2)] (hk5 : 5 ≤ k + 2) {X : SobAlg c r 5}
    (hN : IsNeumannS X) (hk : MemHk (euclBall c r) k (fn (lapS X))) :
    ∃ X' : SobAlg c r (k + 2), restrS hk5 X' = X := by
  have hvol : volume (euclBall c r) ≠ ⊤ := ((measure_mono (euclBall_subset_closedBall c
    hr.out.le)).trans_lt (isCompact_closedBall c r).measure_lt_top).ne
  set t := meanS X / volB c r
  set X₀ := X - t • (1 : SobAlg c r 5)
  have hN₀ : IsNeumannS X₀ := by
    rw [isNeumannS_iff] at hN ⊢
    intro φ hφ
    have h1 := (isNeumannS_iff (c := c) (r := r) (1 : SobAlg c r 5)).mp isNeumannS_one φ hφ
    simp only [X₀, map_sub, map_smul, hN φ hφ, h1, smul_zero, sub_zero]
  have hvB : volB c r ≠ 0 := by
    have hpos : 0 < volume (euclBall c r) := (isOpen_euclBall c r).measure_pos volume
      ⟨c, by show sqDist c c < r ^ 2; simp [sqDist]; exact pow_pos hr.out 2⟩
    exact (ENNReal.toReal_pos hpos.ne' hvol).ne'
  have hm₀ : meanS X₀ = 0 := by
    rw [meanS_eq_inner, show X₀ = X - t • (1 : SobAlg c r 5) from rfl, map_sub, map_smul,
      inner_sub_right, inner_smul_right, ← meanS_eq_inner, ← meanS_eq_inner, meanS_one]
    simp only [t]
    field_simp
    ring
  have hlap : lapS X₀ = lapS X := by
    have h1 : ∀ ν, derS ν (1 : SobAlg c r 5) = 0 := fun ν => derS_one ν
    simp [X₀, lapS, map_sub, map_smul, h1]
  have h₀ := memHk_of_neumannS hN₀ hm₀ (by rw [hlap]; exact hk)
  have hX : MemHk (euclBall c r) (k + 2) (fn X) := by
    have h1 := h₀.add (memHk_const hvol t)
    refine h1.congr_ae ?_
    filter_upwards [fn_sub X (t • (1 : SobAlg c r 5)), fn_smul t (1 : SobAlg c r 5),
      fn_one (c := c) (r := r) (s := 5)] with x e1 e2 e3
    simp only [X₀] at e1 ⊢
    rw [e1, e2, e3]; ring
  obtain ⟨J, hJ, hJae⟩ := exists_mem_HsB_of_memHk c r hX
  refine ⟨ofJet ⟨J, hJ⟩, ext_fn ?_⟩
  rw [fn_restrS]
  exact hJae

end RenewalGeometry.BallAnalysis.BallAlg
