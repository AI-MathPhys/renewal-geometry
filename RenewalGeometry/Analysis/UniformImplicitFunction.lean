/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.DerivBoundBootstrap

/-!
# The uniform implicit function theorem with derivative bounds
  (infrastructure for `lem:supp-initial-calculus` (uniform stationary/Legendre solves),
  `lem:supp-initial-range`, `thm:supp-action-prepared-chart`; emergent-spacetime manuscript)

Let `E, Z, Y` be real Banach spaces and `F : E × Z → Y` with
* `DerivBound F (B(0, ρ)) (K + 2) M` (smooth, `‖D^k F‖ ≤ M` for `k ≤ K + 2`), `F 0 = 0`,
* `∂_z F(0) = T` an isomorphism with `‖T⁻¹‖ ≤ a`.

With the **explicit** radii `σ = min(ρ/2, 1/(8aM'))`, `δ = min(σ, σ/(2aM'))` (`M' = max(M, 1)`),
which depend only on `(M, a, ρ)`:

* `Hyp.exists_unique_zero`, `Hyp.imp_spec`, `Hyp.imp_unique`: for every `‖x‖ < δ` there is
  exactly one `z` with `‖z‖ ≤ σ` and `F(x, z) = 0`; this defines `Hyp.imp`, with `imp 0 = 0`;
* `Hyp.norm_imp_le`, `Hyp.norm_imp_sub_le`: `‖imp x‖ ≤ (8/7) a M ‖x‖` and
  `‖imp x - imp x'‖ ≤ (8/7) a M ‖x - x'‖`;
* `Hyp.hasFDerivAt_imp`: `D imp(x) = -(∂_zF)⁻¹ ∂_xF` at `(x, imp x)` (Mathlib's `C^n` implicit
  function theorem plus local uniqueness);
* **`Hyp.derivBound_imp`**: `DerivBound imp (B(0, δ)) (K + 2) (impC K M a ρ)` with the explicit
  constant `impC` depending only on `(K, M, a, ρ)` (derivative bootstrap of
  `DerivBoundBootstrap.lean`, using the uniform bounds for inversion near the identity).

Hence a family of implicit equations (e.g. indexed by the cutoff) with uniform `(K, M, a, ρ)` has
implicit functions defined on one common ball with uniform derivative bounds of every order: this
is exactly the "bounds on the inverse blocks must be retained; fixed cutoff analyticity alone is
not sufficient" mechanism of `lem:supp-initial-elimination-consistency`.
-/

open Set Filter Topology Metric
open scoped ContDiff Nat NNReal

namespace RenewalGeometry.UniformImplicit

open IteratedDerivBounds UniformDerivBounds

noncomputable section

set_option linter.unusedSectionVars false

variable {E Z Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

/-- The hypotheses of the uniform implicit function theorem. -/
structure Hyp (F : E × Z → Y) (T : Z ≃L[ℝ] Y) (K : ℕ) (M a ρ : ℝ) : Prop where
  hρ : 0 < ρ
  ha : 0 < a
  hT : ‖(T.symm : Y →L[ℝ] Z)‖ ≤ a
  hF : DerivBound F (ball 0 ρ) (K + 2) M
  hF0 : F 0 = 0
  hDF : fderiv ℝ F 0 ∘L ContinuousLinearMap.inr ℝ E Z = (T : Z →L[ℝ] Y)

/-- `M' = max(M, 1)`. -/
def Mp (M : ℝ) : ℝ := max M 1

/-- The radius `σ` of the solution ball. -/
def sig (M a ρ : ℝ) : ℝ := min (ρ / 2) (1 / (8 * a * Mp M))

/-- The radius `δ` of the parameter ball. -/
def del (M a ρ : ℝ) : ℝ := min (sig M a ρ) (sig M a ρ / (2 * a * Mp M))

theorem one_le_Mp (M : ℝ) : 1 ≤ Mp M := le_max_right _ _

theorem le_Mp (M : ℝ) : M ≤ Mp M := le_max_left _ _

theorem Mp_pos (M : ℝ) : 0 < Mp M := lt_of_lt_of_le one_pos (one_le_Mp M)

namespace Hyp

variable {F : E × Z → Y} {T : Z ≃L[ℝ] Y} {K : ℕ} {M a ρ : ℝ} (h : Hyp F T K M a ρ)
include h

theorem hM : 0 ≤ M := h.hF.nonneg (mem_ball_self h.hρ)

theorem sig_pos : 0 < sig M a ρ := by
  have := h.ha; have := Mp_pos M; have := h.hρ
  unfold sig; exact lt_min (by positivity) (by positivity)

theorem del_pos : 0 < del M a ρ := by
  have hs := h.sig_pos; have := h.ha; have := Mp_pos M
  unfold del; exact lt_min hs (by positivity)

theorem del_le_sig : del M a ρ ≤ sig M a ρ := min_le_left _ _

theorem two_sig_le : 2 * sig M a ρ ≤ ρ := by
  have : sig M a ρ ≤ ρ / 2 := min_le_left _ _
  linarith

theorem sig_lt : sig M a ρ < ρ := by
  have := h.sig_pos; have := h.two_sig_le; linarith

theorem aM_sig : a * Mp M * sig M a ρ ≤ 1 / 8 := by
  have h1 : sig M a ρ ≤ 1 / (8 * a * Mp M) := min_le_right _ _
  have := h.ha; have := Mp_pos M
  rw [le_div_iff₀ (by positivity)] at h1
  nlinarith

theorem aM_del : a * Mp M * del M a ρ ≤ sig M a ρ / 2 := by
  have h1 : del M a ρ ≤ sig M a ρ / (2 * a * Mp M) := min_le_right _ _
  have := h.ha; have := Mp_pos M
  rw [le_div_iff₀ (by positivity)] at h1
  nlinarith

theorem aM_le : a * M ≤ a * Mp M := mul_le_mul_of_nonneg_left (le_Mp M) h.ha.le

/-- The normalized normal derivative `S(w) = T⁻¹ ∂_zF(w)`. -/
def Sfun (T : Z ≃L[ℝ] Y) (F : E × Z → Y) (w : E × Z) : Z →L[ℝ] Z :=
  (T.symm : Y →L[ℝ] Z) ∘L (fderiv ℝ F w ∘L ContinuousLinearMap.inr ℝ E Z)

omit h in
theorem symm_comp_T : (T.symm : Y →L[ℝ] Z) ∘L (T : Z →L[ℝ] Y) = 1 := by
  ext z; simp

theorem Sfun_zero : Sfun T F 0 = 1 := by
  rw [Sfun, h.hDF, symm_comp_T]

/-- `‖DF(w) - DF(0)‖ ≤ M ‖w‖`. -/
theorem norm_fderiv_sub {w : E × Z} (hw : w ∈ ball (0 : E × Z) ρ) :
    ‖fderiv ℝ F w - fderiv ℝ F 0‖ ≤ M * ‖w‖ := by
  have := norm_fderiv_sub_le_of_derivBound h.hF isOpen_ball (convex_ball 0 ρ) hw
    (mem_ball_self h.hρ)
  simpa using this

theorem norm_Sfun_sub_one {w : E × Z} (hw : w ∈ ball (0 : E × Z) ρ) :
    ‖Sfun T F w - 1‖ ≤ a * M * ‖w‖ := by
  have e : Sfun T F w - 1 = (T.symm : Y →L[ℝ] Z) ∘L
      ((fderiv ℝ F w - fderiv ℝ F 0) ∘L ContinuousLinearMap.inr ℝ E Z) := by
    rw [← h.Sfun_zero, Sfun, Sfun]
    ext z; simp
  rw [e]
  calc ‖(T.symm : Y →L[ℝ] Z) ∘L ((fderiv ℝ F w - fderiv ℝ F 0) ∘L
        ContinuousLinearMap.inr ℝ E Z)‖
      ≤ ‖(T.symm : Y →L[ℝ] Z)‖ * (‖fderiv ℝ F w - fderiv ℝ F 0‖ *
          ‖ContinuousLinearMap.inr ℝ E Z‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ a * (M * ‖w‖ * 1) := by
        have h1 := h.norm_fderiv_sub hw
        have h2 := ContinuousLinearMap.norm_inr_le_one ℝ E Z
        have h3 : 0 ≤ M * ‖w‖ := mul_nonneg h.hM (norm_nonneg _)
        exact mul_le_mul h.hT (mul_le_mul h1 h2 (norm_nonneg _) h3)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) h.ha.le
    _ = a * M * ‖w‖ := by ring

/-- `‖F w - F w'‖ ≤ M ‖w - w'‖` on the ball. -/
theorem norm_F_sub {w w' : E × Z} (hw : w ∈ ball (0 : E × Z) ρ) (hw' : w' ∈ ball (0 : E × Z) ρ) :
    ‖F w - F w'‖ ≤ M * ‖w - w'‖ :=
  (convex_ball (0 : E × Z) ρ).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (h.hF.contDiffAt isOpen_ball hz).differentiableAt (by simp))
    (fun z hz => h.hF.norm_fderiv_le (by omega) hz) hw' hw

/-- The preconditioned map `Φ_x(z) = z - T⁻¹F(x, z)`. -/
def Phi (T : Z ≃L[ℝ] Y) (F : E × Z → Y) (x : E) (z : Z) : Z := z - T.symm (F (x, z))

theorem hasFDerivAt_Phi {x : E} {z : Z} (hw : (x, z) ∈ ball (0 : E × Z) ρ) :
    HasFDerivAt (Phi T F x) (1 - Sfun T F (x, z)) z := by
  have hF : HasFDerivAt F (fderiv ℝ F (x, z)) (x, z) :=
    ((h.hF.contDiffAt isOpen_ball hw).differentiableAt (by simp)).hasFDerivAt
  have h1 : HasFDerivAt (fun z' : Z => F (x, z')) (fderiv ℝ F (x, z) ∘L
      ContinuousLinearMap.inr ℝ E Z) z := hF.comp z (hasFDerivAt_prodMk_right x z)
  have h2 := (hasFDerivAt_id z).sub ((T.symm : Y →L[ℝ] Z).hasFDerivAt.comp z h1)
  have e1 : Phi T F x = fun z' => z' - T.symm (F (x, z')) := rfl
  have e2 : (1 : Z →L[ℝ] Z) - Sfun T F (x, z) = ContinuousLinearMap.id ℝ Z -
      (T.symm : Y →L[ℝ] Z) ∘L (fderiv ℝ F (x, z) ∘L ContinuousLinearMap.inr ℝ E Z) := rfl
  rw [e1, e2]
  exact h2

theorem mem_ball_of {x : E} {z : Z} (hx : ‖x‖ ≤ sig M a ρ) (hz : ‖z‖ ≤ sig M a ρ) :
    (x, z) ∈ ball (0 : E × Z) ρ := by
  rw [mem_ball_zero_iff, Prod.norm_def]
  exact lt_of_le_of_lt (max_le hx hz) h.sig_lt

theorem norm_prod_le_of {x : E} {z : Z} (hx : ‖x‖ ≤ sig M a ρ) (hz : ‖z‖ ≤ sig M a ρ) :
    ‖(x, z)‖ ≤ sig M a ρ := by
  rw [Prod.norm_def]; exact max_le hx hz

/-- `Φ_x` is a `1/8`-contraction on the closed `σ`-ball. -/
theorem Phi_lip {x : E} (hx : ‖x‖ ≤ sig M a ρ) {z z' : Z} (hz : ‖z‖ ≤ sig M a ρ)
    (hz' : ‖z'‖ ≤ sig M a ρ) : ‖Phi T F x z - Phi T F x z'‖ ≤ 1 / 8 * ‖z - z'‖ := by
  have hd : ∀ y ∈ closedBall (0 : Z) (sig M a ρ), HasFDerivWithinAt (Phi T F x)
      (1 - Sfun T F (x, y)) (closedBall (0 : Z) (sig M a ρ)) y := fun y hy =>
    (h.hasFDerivAt_Phi (h.mem_ball_of hx (mem_closedBall_zero_iff.mp hy))).hasFDerivWithinAt
  have hb : ∀ y ∈ closedBall (0 : Z) (sig M a ρ), ‖1 - Sfun T F (x, y)‖ ≤ 1 / 8 := by
    intro y hy
    have hy' := mem_closedBall_zero_iff.mp hy
    rw [norm_sub_rev]
    refine (h.norm_Sfun_sub_one (h.mem_ball_of hx hy')).trans ?_
    have h1 := h.norm_prod_le_of hx hy'
    have h2 := h.aM_sig
    have h3 := h.aM_le
    have ha := h.ha
    calc a * M * ‖(x, y)‖ ≤ a * Mp M * sig M a ρ := by
          gcongr
          · exact mul_nonneg ha.le (h.hM.trans (le_Mp M))
      _ ≤ 1 / 8 := h2
  exact (convex_closedBall (0 : Z) (sig M a ρ)).norm_image_sub_le_of_norm_hasFDerivWithin_le hd hb
    (mem_closedBall_zero_iff.mpr hz') (mem_closedBall_zero_iff.mpr hz)

theorem norm_Phi_zero {x : E} (hx : ‖x‖ < ρ) : ‖Phi T F x 0‖ ≤ a * M * ‖x‖ := by
  have hw : (x, (0 : Z)) ∈ ball (0 : E × Z) ρ := by
    rw [mem_ball_zero_iff, Prod.norm_def]; simpa using hx
  have h1 := h.norm_F_sub hw (mem_ball_self h.hρ)
  rw [h.hF0, sub_zero, sub_zero] at h1
  have hxz : ‖((x, (0 : Z)) : E × Z)‖ = ‖x‖ := by simp [Prod.norm_def]
  rw [hxz] at h1
  simp only [Phi, zero_sub, norm_neg]
  calc ‖T.symm (F (x, 0))‖ ≤ ‖(T.symm : Y →L[ℝ] Z)‖ * ‖F (x, 0)‖ :=
        (T.symm : Y →L[ℝ] Z).le_opNorm _
    _ ≤ a * (M * ‖x‖) := mul_le_mul h.hT h1 (norm_nonneg _) h.ha.le
    _ = a * M * ‖x‖ := by ring

theorem Phi_maps {x : E} (hx : ‖x‖ < del M a ρ) {z : Z} (hz : ‖z‖ ≤ sig M a ρ) :
    ‖Phi T F x z‖ ≤ sig M a ρ := by
  have hxs : ‖x‖ ≤ sig M a ρ := hx.le.trans h.del_le_sig
  have hxρ : ‖x‖ < ρ := lt_of_le_of_lt hxs h.sig_lt
  have h1 := h.Phi_lip hxs hz (by simpa using h.sig_pos.le : ‖(0 : Z)‖ ≤ sig M a ρ)
  have h2 := h.norm_Phi_zero hxρ
  rw [sub_zero] at h1
  have h3 : a * M * ‖x‖ ≤ sig M a ρ / 2 := by
    calc a * M * ‖x‖ ≤ a * Mp M * del M a ρ :=
          mul_le_mul h.aM_le hx.le (norm_nonneg _) (mul_nonneg h.ha.le (Mp_pos M).le)
      _ ≤ sig M a ρ / 2 := h.aM_del
  calc ‖Phi T F x z‖ ≤ ‖Phi T F x z - Phi T F x 0‖ + ‖Phi T F x 0‖ := norm_le_norm_sub_add _ _
    _ ≤ 1 / 8 * ‖z‖ + sig M a ρ / 2 := add_le_add h1 (h2.trans h3)
    _ ≤ sig M a ρ := by linarith [h.sig_pos]

omit h in
theorem Phi_eq_self_iff {x : E} {z : Z} : Phi T F x z = z ↔ F (x, z) = 0 := by
  unfold Phi
  constructor
  · intro hz
    have : T.symm (F (x, z)) = 0 := by
      have := congrArg (fun w => z - w) hz
      simpa using this
    simpa using congrArg T this
  · intro hz; simp [hz]

/-- **Existence and uniqueness** of the zero in the closed `σ`-ball. -/
theorem exists_unique_zero {x : E} (hx : ‖x‖ < del M a ρ) :
    ∃! z : Z, ‖z‖ ≤ sig M a ρ ∧ F (x, z) = 0 := by
  have hxs : ‖x‖ ≤ sig M a ρ := hx.le.trans h.del_le_sig
  set s : Set Z := closedBall 0 (sig M a ρ)
  have hsc : IsComplete s := isClosed_closedBall.isComplete
  have hmaps : MapsTo (Phi T F x) s s := fun z hz =>
    mem_closedBall_zero_iff.mpr (h.Phi_maps hx (mem_closedBall_zero_iff.mp hz))
  have hcon : ContractingWith (1 / 8 : ℝ≥0) (hmaps.restrict (Phi T F x) s s) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun z z' => ?_⟩
    simp only [Subtype.dist_eq, MapsTo.val_restrict_apply, dist_eq_norm]
    push_cast
    exact h.Phi_lip hxs (mem_closedBall_zero_iff.mp z.2) (mem_closedBall_zero_iff.mp z'.2)
  obtain ⟨y, hys, hfix, -⟩ := hcon.exists_fixedPoint' hsc hmaps (mem_closedBall_self h.sig_pos.le)
    (edist_ne_top _ _)
  refine ⟨y, ⟨mem_closedBall_zero_iff.mp hys, Phi_eq_self_iff.mp hfix⟩, ?_⟩
  rintro z ⟨hz, hFz⟩
  have hfz : Phi T F x z = z := Phi_eq_self_iff.mpr hFz
  have hfy : Phi T F x y = y := hfix
  have hl := h.Phi_lip hxs hz (mem_closedBall_zero_iff.mp hys)
  rw [hfz, hfy] at hl
  have : ‖z - y‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (z - y)]) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

end Hyp

/-- **The implicit function**: the unique zero `z` of `F(x, ·)` with `‖z‖ ≤ σ`
(`0` outside the parameter ball, where it is not used). -/
def imp (F : E × Z → Y) (M a ρ : ℝ) (x : E) : Z :=
  open Classical in
  if hx : ∃ z : Z, ‖z‖ ≤ sig M a ρ ∧ F (x, z) = 0 then hx.choose else 0

namespace Hyp

variable {F : E × Z → Y} {T : Z ≃L[ℝ] Y} {K : ℕ} {M a ρ : ℝ} (h : Hyp F T K M a ρ)
include h

theorem imp_spec {x : E} (hx : ‖x‖ < del M a ρ) :
    ‖imp F M a ρ x‖ ≤ sig M a ρ ∧ F (x, imp F M a ρ x) = 0 := by
  have hex : ∃ z : Z, ‖z‖ ≤ sig M a ρ ∧ F (x, z) = 0 := (h.exists_unique_zero hx).exists
  rw [imp, dite_cond_eq_true (eq_true hex)]
  exact hex.choose_spec

theorem imp_unique {x : E} (hx : ‖x‖ < del M a ρ) {z : Z} (hz : ‖z‖ ≤ sig M a ρ)
    (hFz : F (x, z) = 0) : z = imp F M a ρ x :=
  (h.exists_unique_zero hx).unique ⟨hz, hFz⟩ (h.imp_spec hx)

theorem imp_zero : imp F M a ρ (0 : E) = 0 := by
  have h0 : ‖(0 : E)‖ < del M a ρ := by simpa using h.del_pos
  have hF00 : F ((0 : E), (0 : Z)) = 0 := h.hF0
  exact (h.imp_unique h0 (by simpa using h.sig_pos.le) hF00).symm

theorem Phi_imp {x : E} (hx : ‖x‖ < del M a ρ) :
    Phi T F x (imp F M a ρ x) = imp F M a ρ x :=
  Phi_eq_self_iff.mpr (h.imp_spec hx).2

/-- `‖imp x‖ ≤ (8/7) a M ‖x‖`. -/
theorem norm_imp_le {x : E} (hx : ‖x‖ < del M a ρ) :
    ‖imp F M a ρ x‖ ≤ 8 / 7 * (a * M * ‖x‖) := by
  have hxs : ‖x‖ ≤ sig M a ρ := hx.le.trans h.del_le_sig
  have hxρ : ‖x‖ < ρ := lt_of_le_of_lt hxs h.sig_lt
  have hs := h.imp_spec hx
  have h1 := h.Phi_lip hxs hs.1 (by simpa using h.sig_pos.le : ‖(0 : Z)‖ ≤ sig M a ρ)
  rw [h.Phi_imp hx, sub_zero] at h1
  have h2 := h.norm_Phi_zero hxρ
  have h3 : ‖imp F M a ρ x‖ ≤ 1 / 8 * ‖imp F M a ρ x‖ + a * M * ‖x‖ := by
    calc ‖imp F M a ρ x‖ ≤ ‖imp F M a ρ x - Phi T F x 0‖ + ‖Phi T F x 0‖ :=
          norm_le_norm_sub_add _ _
      _ ≤ _ := add_le_add h1 h2
  linarith

/-- The implicit function is Lipschitz: `‖imp x - imp x'‖ ≤ (8/7) a M ‖x - x'‖`. -/
theorem norm_imp_sub_le {x x' : E} (hx : ‖x‖ < del M a ρ) (hx' : ‖x'‖ < del M a ρ) :
    ‖imp F M a ρ x - imp F M a ρ x'‖ ≤ 8 / 7 * (a * M * ‖x - x'‖) := by
  have hxs : ‖x‖ ≤ sig M a ρ := hx.le.trans h.del_le_sig
  have hxs' : ‖x'‖ ≤ sig M a ρ := hx'.le.trans h.del_le_sig
  have hs := h.imp_spec hx
  have hs' := h.imp_spec hx'
  set z := imp F M a ρ x
  set z' := imp F M a ρ x'
  have h1 := h.Phi_lip hxs hs.1 hs'.1
  rw [h.Phi_imp hx] at h1
  have h2 : ‖Phi T F x z' - Phi T F x' z'‖ ≤ a * M * ‖x - x'‖ := by
    have e : Phi T F x z' - Phi T F x' z' = T.symm (F (x', z') - F (x, z')) := by
      simp only [Phi, map_sub]; abel
    rw [e]
    have hw := h.mem_ball_of hxs hs'.1
    have hw' := h.mem_ball_of hxs' hs'.1
    have hF := h.norm_F_sub hw' hw
    have hn : ‖((x', z') : E × Z) - (x, z')‖ = ‖x - x'‖ := by
      rw [Prod.mk_sub_mk, sub_self, Prod.norm_def, norm_zero, norm_sub_rev]
      exact max_eq_left (norm_nonneg _)
    rw [hn] at hF
    calc ‖T.symm (F (x', z') - F (x, z'))‖ ≤ ‖(T.symm : Y →L[ℝ] Z)‖ * ‖F (x', z') - F (x, z')‖ :=
          (T.symm : Y →L[ℝ] Z).le_opNorm _
      _ ≤ a * (M * ‖x - x'‖) := mul_le_mul h.hT hF (norm_nonneg _) h.ha.le
      _ = a * M * ‖x - x'‖ := by ring
  have h3 : ‖z - z'‖ ≤ 1 / 8 * ‖z - z'‖ + a * M * ‖x - x'‖ := by
    have e : z - z' = (Phi T F x z - Phi T F x z') + (Phi T F x z' - Phi T F x' z') := by
      rw [h.Phi_imp hx, h.Phi_imp hx']; abel
    calc ‖z - z'‖ = ‖(Phi T F x z - Phi T F x z') + (Phi T F x z' - Phi T F x' z')‖ := by rw [← e]
      _ ≤ ‖Phi T F x z - Phi T F x z'‖ + ‖Phi T F x z' - Phi T F x' z'‖ := norm_add_le _ _
      _ ≤ 1 / 8 * ‖z - z'‖ + a * M * ‖x - x'‖ := by
          refine add_le_add ?_ h2
          rw [h.Phi_imp hx] at *
          exact h1
  linarith

theorem continuousAt_imp {x : E} (hx : ‖x‖ < del M a ρ) : ContinuousAt (imp F M a ρ) x := by
  have hU : ball (0 : E) (del M a ρ) ∈ 𝓝 x := isOpen_ball.mem_nhds (by simpa using hx)
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
  set c : ℝ := 8 / 7 * (a * M) + 1
  have hc : 0 < c := by have := mul_nonneg h.ha.le h.hM; positivity
  refine ⟨min r (ε / c), lt_min hr (by positivity), fun {y} hy => ?_⟩
  have hyr : dist y x < r := lt_of_lt_of_le hy (min_le_left _ _)
  have hyU : y ∈ ball (0 : E) (del M a ρ) := hrU (by simpa [dist_comm] using hyr)
  have hy' : ‖y‖ < del M a ρ := by simpa using hyU
  rw [dist_eq_norm] at hy ⊢
  have h1 := h.norm_imp_sub_le hy' hx
  have hyε : ‖y - x‖ < ε / c := lt_of_lt_of_le hy (min_le_right _ _)
  have haM : 0 ≤ a * M := mul_nonneg h.ha.le h.hM
  calc ‖imp F M a ρ y - imp F M a ρ x‖ ≤ 8 / 7 * (a * M * ‖y - x‖) := h1
    _ ≤ c * ‖y - x‖ := by
        have := norm_nonneg (y - x)
        have e : c * ‖y - x‖ = 8 / 7 * (a * M * ‖y - x‖) + ‖y - x‖ := by simp only [c]; ring
        rw [e]; linarith
    _ < c * (ε / c) := by gcongr
    _ = ε := by field_simp

/-- The derivative field `Ψ(w) = -S(w)⁻¹ T⁻¹ ∂_xF(w)` of the implicit function. -/
def Psi (T : Z ≃L[ℝ] Y) (F : E × Z → Y) (w : E × Z) : E →L[ℝ] Z :=
  -(Ring.inverse (Sfun T F w) ∘L
    ((T.symm : Y →L[ℝ] Z) ∘L (fderiv ℝ F w ∘L ContinuousLinearMap.inl ℝ E Z)))

/-- **Derivative of the implicit function**: `D imp(x) = -(∂_zF)⁻¹ ∂_xF` at `(x, imp x)`. -/
theorem hasFDerivAt_imp {x : E} (hx : ‖x‖ < del M a ρ) :
    HasFDerivAt (imp F M a ρ) (Psi T F (x, imp F M a ρ x)) x := by
  have hxs : ‖x‖ ≤ sig M a ρ := hx.le.trans h.del_le_sig
  have hs := h.imp_spec hx
  set u : E × Z := (x, imp F M a ρ x) with hu
  have huB : u ∈ ball (0 : E × Z) ρ := h.mem_ball_of hxs hs.1
  have hcd : ContDiffAt ℝ ∞ F u := h.hF.contDiffAt isOpen_ball huB
  have hSu : ‖Sfun T F u - 1‖ < 1 := by
    have h1 := h.norm_Sfun_sub_one huB
    have h2 : a * M * ‖u‖ ≤ 1 / 8 := by
      calc a * M * ‖u‖ ≤ a * Mp M * sig M a ρ :=
            mul_le_mul h.aM_le (h.norm_prod_le_of hxs hs.1) (norm_nonneg _)
              (mul_nonneg h.ha.le (Mp_pos M).le)
        _ ≤ 1 / 8 := h.aM_sig
    linarith
  obtain ⟨v, hv⟩ := exists_unit_of_norm_sub_one_lt hSu
  have hfac : fderiv ℝ F u ∘L ContinuousLinearMap.inr ℝ E Z = (T : Z →L[ℝ] Y) ∘L Sfun T F u := by
    ext z; simp [Sfun]
  have if₂ : (fderiv ℝ F u ∘L ContinuousLinearMap.inr ℝ E Z).IsInvertible := by
    rw [hfac, ← hv]
    exact ⟨(ContinuousLinearEquiv.unitsEquiv ℝ Z v).trans T, by ext z; simp⟩
  have pn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hψ := hcd.contDiffAt_implicitFunction pn if₂
  have heq := hcd.eventually_apply_eq_iff_implicitFunction pn if₂
  set ψ := hcd.implicitFunction pn if₂
  have hFu : F u = 0 := hs.2
  have hpair : Tendsto (fun x' => (x', imp F M a ρ x')) (𝓝 x) (𝓝 u) :=
    continuousAt_id.prodMk (h.continuousAt_imp hx)
  have hball : ∀ᶠ x' in 𝓝 x, ‖x'‖ < del M a ρ := by
    have : ball (0 : E) (del M a ρ) ∈ 𝓝 x := isOpen_ball.mem_nhds (by simpa using hx)
    filter_upwards [this] with x' hx'
    simpa using hx'
  have hev : imp F M a ρ =ᶠ[𝓝 x] ψ := by
    filter_upwards [hpair.eventually heq, hball] with x' h1 h2
    exact (h1.mp (by rw [hFu]; exact (h.imp_spec h2).2)).symm
  have hd : HasFDerivAt (imp F M a ρ) (fderiv ℝ ψ x) x :=
    ((hψ.differentiableAt (by simp)).hasFDerivAt).congr_of_eventuallyEq hev
  set D := fderiv ℝ ψ x
  have hchain : HasFDerivAt (fun x' => F (x', imp F M a ρ x'))
      (fderiv ℝ F u ∘L ((ContinuousLinearMap.id ℝ E).prod D)) x :=
    (hcd.differentiableAt (by simp)).hasFDerivAt.comp x ((hasFDerivAt_id x).prodMk hd)
  have hzero : fderiv ℝ F u ∘L ((ContinuousLinearMap.id ℝ E).prod D) = 0 := by
    have h0 : HasFDerivAt (fun x' => F (x', imp F M a ρ x')) (0 : E →L[ℝ] Y) x :=
      (hasFDerivAt_const (0 : Y) x).congr_of_eventuallyEq
        (hball.mono fun x' hx' => (h.imp_spec hx').2)
    exact hchain.unique h0
  have hsplit : (T.symm : Y →L[ℝ] Z) ∘L (fderiv ℝ F u ∘L ContinuousLinearMap.inl ℝ E Z) +
      Sfun T F u ∘L D = 0 := by
    ext e
    have h1 := congrArg (fun L => (T.symm : Y →L[ℝ] Z) (L e)) hzero
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply, map_zero] at h1
    have e2 : ((e, D e) : E × Z) = (e, 0) + (0, D e) := by simp
    rw [e2, map_add, map_add] at h1
    simpa [Sfun] using h1
  have hinv : Ring.inverse (Sfun T F u) * Sfun T F u = 1 := by
    rw [← hv, Ring.inverse_unit]; exact v.inv_mul
  have hSD : Sfun T F u ∘L D =
      -((T.symm : Y →L[ℝ] Z) ∘L (fderiv ℝ F u ∘L ContinuousLinearMap.inl ℝ E Z)) :=
    eq_neg_of_add_eq_zero_right hsplit
  have hDeq : D = Psi T F u := by
    calc D = (Ring.inverse (Sfun T F u) * Sfun T F u) ∘L D := by rw [hinv]; rfl
      _ = Ring.inverse (Sfun T F u) ∘L (Sfun T F u ∘L D) := rfl
      _ = Psi T F u := by
          rw [hSD, Psi]
          ext e; simp
  rw [← hDeq]
  exact hd

/-- The constant of `derivBound_Psi`. -/
def PsiC (K : ℕ) (M a : ℝ) : ℝ :=
  2 ^ (K + 1) * ((K + 1)! * invC K * max 1 (a * M) ^ (K + 1)) * (a * M)

theorem mapsTo_Sfun : MapsTo (Sfun T F) (ball (0 : E × Z) (2 * sig M a ρ)) (ball 1 (1 / 2)) := by
  intro w hw
  have hwρ : w ∈ ball (0 : E × Z) ρ := ball_subset_ball h.two_sig_le hw
  have h1 := h.norm_Sfun_sub_one hwρ
  have hw' : ‖w‖ < 2 * sig M a ρ := by simpa using hw
  rw [mem_ball, dist_eq_norm]
  have h2 : a * M * ‖w‖ ≤ a * Mp M * (2 * sig M a ρ) :=
    mul_le_mul h.aM_le hw'.le (norm_nonneg _) (mul_nonneg h.ha.le (Mp_pos M).le)
  have h3 := h.aM_sig
  nlinarith

/-- **Uniform derivative bounds for the derivative field** `Ψ` on the ball `B(0, 2σ)`. -/
theorem derivBound_Psi :
    DerivBound (Psi T F) (ball (0 : E × Z) (2 * sig M a ρ)) (K + 1) (PsiC K M a) := by
  set W := ball (0 : E × Z) (2 * sig M a ρ)
  have hW : W ⊆ ball 0 ρ := ball_subset_ball h.two_sig_le
  have hF1 : DerivBound (fderiv ℝ F) W (K + 1) M := (h.hF.fderiv isOpen_ball).subset hW
  have haM : 0 ≤ a * M := mul_nonneg h.ha.le h.hM
  set L1 : ((E × Z) →L[ℝ] Y) →L[ℝ] (Z →L[ℝ] Z) :=
    (ContinuousLinearMap.compL ℝ Z Y Z (T.symm : Y →L[ℝ] Z)).comp
      ((ContinuousLinearMap.compL ℝ Z (E × Z) Y).flip (ContinuousLinearMap.inr ℝ E Z)) with hL1def
  set L2 : ((E × Z) →L[ℝ] Y) →L[ℝ] (E →L[ℝ] Z) :=
    (ContinuousLinearMap.compL ℝ E Y Z (T.symm : Y →L[ℝ] Z)).comp
      ((ContinuousLinearMap.compL ℝ E (E × Z) Y).flip (ContinuousLinearMap.inl ℝ E Z)) with hL2def
  have hL1n : ‖L1‖ ≤ a := by
    refine ContinuousLinearMap.opNorm_le_bound _ h.ha.le fun L => ?_
    change ‖(T.symm : Y →L[ℝ] Z) ∘L (L ∘L ContinuousLinearMap.inr ℝ E Z)‖ ≤ a * ‖L‖
    calc ‖(T.symm : Y →L[ℝ] Z) ∘L (L ∘L ContinuousLinearMap.inr ℝ E Z)‖
        ≤ ‖(T.symm : Y →L[ℝ] Z)‖ * (‖L‖ * ‖ContinuousLinearMap.inr ℝ E Z‖) :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ a * (‖L‖ * 1) := by
          refine mul_le_mul h.hT ?_ (by positivity) h.ha.le
          exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_inr_le_one ℝ E Z)
            (norm_nonneg _)
      _ = a * ‖L‖ := by ring
  have hL2n : ‖L2‖ ≤ a := by
    refine ContinuousLinearMap.opNorm_le_bound _ h.ha.le fun L => ?_
    change ‖(T.symm : Y →L[ℝ] Z) ∘L (L ∘L ContinuousLinearMap.inl ℝ E Z)‖ ≤ a * ‖L‖
    calc ‖(T.symm : Y →L[ℝ] Z) ∘L (L ∘L ContinuousLinearMap.inl ℝ E Z)‖
        ≤ ‖(T.symm : Y →L[ℝ] Z)‖ * (‖L‖ * ‖ContinuousLinearMap.inl ℝ E Z‖) :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ a * (‖L‖ * 1) := by
          refine mul_le_mul h.hT ?_ (by positivity) h.ha.le
          exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_inl_le_one ℝ E Z)
            (norm_nonneg _)
      _ = a * ‖L‖ := by ring
  have hS : DerivBound (Sfun T F) W (K + 1) (a * M) :=
    (DerivBound.clm_comp (G := Z →L[ℝ] Z) hF1 isOpen_ball L1).mono le_rfl
      (mul_le_mul_of_nonneg_right hL1n h.hM)
  have hD : DerivBound (fun w => (T.symm : Y →L[ℝ] Z) ∘L (fderiv ℝ F w ∘L
      ContinuousLinearMap.inl ℝ E Z)) W (K + 1) (a * M) :=
    (DerivBound.clm_comp (G := E →L[ℝ] Z) hF1 isOpen_ball L2).mono le_rfl
      (mul_le_mul_of_nonneg_right hL2n h.hM)
  have hI := derivBound_comp (derivBound_inverse (Z := Z) K) isOpen_ball hS isOpen_ball
    h.mapsTo_Sfun
  have hInvC : 0 ≤ invC K := (derivBound_inverse (Z := Z) K).nonneg
    (mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2))
  have hC1 : 0 ≤ (K + 1)! * invC K * max 1 (a * M) ^ (K + 1) := by positivity
  have hB := DerivBound.bilinear (H := E →L[ℝ] Z) hI hD isOpen_ball
    (ContinuousLinearMap.compL ℝ E Z Z) hC1 haM
  have hB' := hB.neg
  refine (derivBound_congrOn hB' isOpen_ball fun w _ => rfl).mono le_rfl ?_
  have hle : ∀ c : ℝ, c ≤ 1 →
      c * 2 ^ (K + 1) * ((K + 1)! * invC K * max 1 (a * M) ^ (K + 1)) * (a * M) ≤ PsiC K M a := by
    intro c hc
    have h0 : 0 ≤ 2 ^ (K + 1) * ((K + 1)! * invC K * max 1 (a * M) ^ (K + 1)) * (a * M) := by
      positivity
    unfold PsiC
    have e : c * 2 ^ (K + 1) * ((K + 1)! * invC K * max 1 (a * M) ^ (K + 1)) * (a * M) =
        c * (2 ^ (K + 1) * ((K + 1)! * invC K * max 1 (a * M) ^ (K + 1)) * (a * M)) := by ring
    rw [e]
    nlinarith
  exact hle _ (ContinuousLinearMap.norm_compL_le ℝ E Z Z)

end Hyp

/-- The explicit derivative constant of the implicit function. -/
def impC (K : ℕ) (M a ρ : ℝ) : ℝ := bootC (Hyp.PsiC K M a) (sig M a ρ) (del M a ρ) (K + 2)

namespace Hyp

variable {F : E × Z → Y} {T : Z ≃L[ℝ] Y} {K : ℕ} {M a ρ : ℝ} (h : Hyp F T K M a ρ)
include h

/-- **The uniform implicit function theorem with derivative bounds**: on the ball `B(0, δ)` the
implicit function is `C^∞` with `‖D^k imp‖ ≤ impC K M a ρ` for `k ≤ K + 2`; the radius `δ` and
the constant depend only on `(K, M, a, ρ)`. -/
theorem derivBound_imp :
    DerivBound (imp F M a ρ) (ball 0 (del M a ρ)) (K + 2) (impC K M a ρ) := by
  refine derivBound_of_hasFDerivAt_eq isOpen_ball h.del_pos.le ball_subset_closedBall
    isOpen_ball h.derivBound_Psi ?_ ?_ ?_ h.sig_pos.le
  · intro x hx
    have hx' : ‖x‖ < del M a ρ := by simpa using hx
    have hs := h.imp_spec hx'
    rw [mem_ball_zero_iff]
    have := h.norm_prod_le_of (hx'.le.trans h.del_le_sig) hs.1
    have := h.sig_pos
    linarith
  · intro x hx
    exact h.hasFDerivAt_imp (by simpa using hx)
  · intro x hx
    exact (h.imp_spec (by simpa using hx)).1

end Hyp

/-- Non-vacuity: `F(x, z) = z - x` on `ℝ × ℝ` satisfies the hypotheses (with `T = id`). -/
example : Hyp (fun p : ℝ × ℝ => p.2 - p.1) (ContinuousLinearEquiv.refl ℝ ℝ) 0 2 1 1 where
  hρ := one_pos
  ha := one_pos
  hT := ContinuousLinearMap.norm_id_le
  hF := by
    have h := DerivBound.clm (ContinuousLinearMap.snd ℝ ℝ ℝ - ContinuousLinearMap.fst ℝ ℝ ℝ)
      (U := ball (0 : ℝ × ℝ) 1) zero_le_one ball_subset_closedBall 2
    refine (h.congr fun p => by simp).mono le_rfl ?_
    have h1 : ‖ContinuousLinearMap.snd ℝ ℝ ℝ - ContinuousLinearMap.fst ℝ ℝ ℝ‖ ≤ 2 :=
      (norm_sub_le _ _).trans (by
        linarith [ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ, ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ])
    simpa using h1
  hF0 := by simp
  hDF := by
    have h : HasFDerivAt (fun p : ℝ × ℝ => p.2 - p.1)
        (ContinuousLinearMap.snd ℝ ℝ ℝ - ContinuousLinearMap.fst ℝ ℝ ℝ) 0 :=
      (ContinuousLinearMap.snd ℝ ℝ ℝ - ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.congr_fderiv rfl
        |>.congr_of_eventuallyEq (Filter.Eventually.of_forall fun p => by simp)
    rw [h.fderiv]
    ext; simp

end

end RenewalGeometry.UniformImplicit
