/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.CharacteristicStrangSplittingConsistency
import RenewalGeometry.Gravity.GowdySplittingSecondOrderConsistency

/-!
# Characteristic-norm stability and one-step error of abstract characteristic Strang splitting
  (infrastructure for `prop:supp-gowdy-residual-control`, `eq:supp-gowdy-state-error`;
  emergent-spacetime supplement)

This file abstracts the `r = 0` stability analysis of the Gowdy split map
(`Gravity/GowdySplitCharacteristicStability.lean`) to an arbitrary normed state space `V`, so that
it can be applied to the *difference-quotient prolongations* of the scheme
(`DiscreteAnalysis/GridFaaDiBrunoProlongation.lean`), which yield the `C^r_ℓ` estimates.

* `CharData V`: three linear projections `Π₊, Π₋, Π₀` (right-moving, left-moving, non-moving
  parts), a source field `F` and two scalar densities `g±`.  `CGrid V N`: a grid state on
  `ZMod N` (local states and a scalar background `λ`).
* `CharData.transport`, `IsSrc`, `IsSplit`: the characteristic shift
  `Y_j ↦ Π₊Y_{j+1} + Π₋Y_{j-1} + Π₀Y_j`, `λ_j ↦ λ_j + (ℓ/2)[g₊(Y_j)+g₊(Y_{j+1})+g₋(Y_j)+g₋(Y_{j-1})]`,
  the implicit-midpoint source step at every site, and their symmetric composition
  (source half-step / transport / source half-step).
* `charNorm v = max (‖Π₊v‖, ‖Π₋v‖, ‖Π₀v‖)` and the grid distance
  `dist0 X Y = max (sup_j charNorm (X_j - Y_j), ‖λ - λ'‖_∞)`.
* `dist0_splitStep`: **the split step is `(1 + (9L + 8L_g)ℓ)`-Lipschitz in `dist0`** whenever the
  field is `L`-Lipschitz on a set containing all stage midpoints and the densities are
  `L_g`-Lipschitz with respect to their own characteristic part on a set containing the
  transported inputs (`3ℓL ≤ 1`, `2L_gℓ ≤ 1`).
* `oneStep_strang`: for a `C³` reference solution packaged as a
  `CharacteristicSplitting.StrangSetup`, every numerical split step `X → A → B` whose stages
  lie in the chart obeys
  `dist0 (B, 𝖲X_*(τ+ℓ)) ≤ (1 + (9L + 8L_g)ℓ) dist0 (X, 𝖲X_*(τ)) + C ℓ³`
  (stability + second-order consistency; the reference split step is constructed on the
  near-identity branch).
-/

open Set Finset
open scoped BigOperators

set_option linter.unusedSectionVars false

namespace RenewalGeometry.GridFaaDiBruno

noncomputable section

/-- Characteristic data of a semilinear characteristic system: projections onto the
right-moving, left-moving and non-moving parts, the source field and the two densities. -/
structure CharData (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  /-- right-moving projection -/
  Pp : V →ₗ[ℝ] V
  /-- left-moving projection -/
  Pm : V →ₗ[ℝ] V
  /-- non-moving projection -/
  P0 : V →ₗ[ℝ] V
  /-- source field -/
  F : V → V
  /-- right-moving density -/
  gp : V → ℝ
  /-- left-moving density -/
  gm : V → ℝ

/-- A grid state on the periodic grid `ZMod N`: local states and a scalar background. -/
@[ext]
structure CGrid (V : Type*) (N : ℕ) where
  /-- local state at each site -/
  site : ZMod N → V
  /-- background at each site -/
  lam : ZMod N → ℝ

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace CharData

variable (c : CharData V) {N : ℕ}

/-- Complementary contractive projections: `Π₊ + Π₋ + Π₀ = 1`, all of norm `≤ 1`, pairwise
annihilating and idempotent. -/
structure Proj : Prop where
  sum : ∀ v, c.Pp v + c.Pm v + c.P0 v = v
  norm_Pp : ∀ v, ‖c.Pp v‖ ≤ ‖v‖
  norm_Pm : ∀ v, ‖c.Pm v‖ ≤ ‖v‖
  norm_P0 : ∀ v, ‖c.P0 v‖ ≤ ‖v‖
  pp : ∀ v, c.Pp (c.Pp v) = c.Pp v
  pm : ∀ v, c.Pp (c.Pm v) = 0
  p0 : ∀ v, c.Pp (c.P0 v) = 0
  mp : ∀ v, c.Pm (c.Pp v) = 0
  mm : ∀ v, c.Pm (c.Pm v) = c.Pm v
  m0 : ∀ v, c.Pm (c.P0 v) = 0
  zp : ∀ v, c.P0 (c.Pp v) = 0
  zm : ∀ v, c.P0 (c.Pm v) = 0
  zz : ∀ v, c.P0 (c.P0 v) = c.P0 v

/-- The transport map at frozen time: characteristic shift of the sites and the trapezoidal
background update. -/
def transport (ℓ : ℝ) (X : CGrid V N) : CGrid V N where
  site j := c.Pp (X.site (j + 1)) + c.Pm (X.site (j - 1)) + c.P0 (X.site j)
  lam j := X.lam j + ℓ / 2 * ((c.gp (X.site j) + c.gp (X.site (j + 1))) +
    (c.gm (X.site j) + c.gm (X.site (j - 1))))

/-- An implicit-midpoint source step of duration `σ` at every site, background fixed. -/
def IsSrc (σ : ℝ) (X Y : CGrid V N) : Prop :=
  (∀ j, Y.site j = X.site j + σ • c.F ((1 / 2 : ℝ) • (X.site j + Y.site j))) ∧ Y.lam = X.lam

/-- The symmetric split step `X → A → B` with `h = ℓ`. -/
def IsSplit (ℓ : ℝ) (X A B : CGrid V N) : Prop :=
  c.IsSrc (ℓ / 2) X A ∧ c.IsSrc (ℓ / 2) (c.transport ℓ A) B

/-- The stage-one midpoints, the transported inputs and the stage-three midpoints of a split
step all lie in `K`. -/
def Env0 (K : Set V) (ℓ : ℝ) (X A B : CGrid V N) : Prop :=
  ∀ j, (1 / 2 : ℝ) • (X.site j + A.site j) ∈ K ∧ A.site j ∈ K ∧
    (1 / 2 : ℝ) • ((c.transport ℓ A).site j + B.site j) ∈ K

/-- The characteristic norm `max (‖Π₊v‖, ‖Π₋v‖, ‖Π₀v‖)`. -/
def charNorm (v : V) : ℝ := max ‖c.Pp v‖ (max ‖c.Pm v‖ ‖c.P0 v‖)

/-- The sup over the grid of the characteristic norm. -/
def charSup [NeZero N] (v : ZMod N → V) : ℝ := univ.sup' univ_nonempty fun j => c.charNorm (v j)

/-- The grid distance `max (sup_j charNorm (X_j - Y_j), ‖λ - λ'‖_∞)`. -/
def dist0 [NeZero N] (X Y : CGrid V N) : ℝ := max (c.charSup (X.site - Y.site)) ‖X.lam - Y.lam‖

/-! ### The characteristic norm -/

variable {c}

theorem charNorm_nonneg (v : V) : 0 ≤ c.charNorm v := (norm_nonneg _).trans (le_max_left _ _)

theorem norm_Pp_le_charNorm (v : V) : ‖c.Pp v‖ ≤ c.charNorm v := le_max_left _ _

theorem norm_Pm_le_charNorm (v : V) : ‖c.Pm v‖ ≤ c.charNorm v :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem norm_P0_le_charNorm (v : V) : ‖c.P0 v‖ ≤ c.charNorm v :=
  (le_max_right _ _).trans (le_max_right _ _)

theorem charNorm_le_norm (hc : c.Proj) (v : V) : c.charNorm v ≤ ‖v‖ :=
  max_le (hc.norm_Pp v) (max_le (hc.norm_Pm v) (hc.norm_P0 v))

theorem norm_le_three_mul_charNorm (hc : c.Proj) (v : V) : ‖v‖ ≤ 3 * c.charNorm v := by
  calc ‖v‖ = ‖c.Pp v + c.Pm v + c.P0 v‖ := by rw [hc.sum]
    _ ≤ ‖c.Pp v‖ + ‖c.Pm v‖ + ‖c.P0 v‖ := norm_add₃_le
    _ ≤ 3 * c.charNorm v := by
        linarith [norm_Pp_le_charNorm (c := c) v, norm_Pm_le_charNorm (c := c) v,
          norm_P0_le_charNorm (c := c) v]

theorem charNorm_add_le (v w : V) : c.charNorm (v + w) ≤ c.charNorm v + c.charNorm w := by
  unfold charNorm
  simp only [map_add]
  refine max_le ?_ (max_le ?_ ?_)
  · exact (norm_add_le _ _).trans (add_le_add (le_max_left _ _) (le_max_left _ _))
  · exact (norm_add_le _ _).trans (add_le_add ((le_max_left _ _).trans (le_max_right _ _))
      ((le_max_left _ _).trans (le_max_right _ _)))
  · exact (norm_add_le _ _).trans (add_le_add ((le_max_right _ _).trans (le_max_right _ _))
      ((le_max_right _ _).trans (le_max_right _ _)))

theorem charNorm_neg (v : V) : c.charNorm (-v) = c.charNorm v := by
  simp [charNorm, map_neg, norm_neg]

theorem charNorm_sub_comm (v w : V) : c.charNorm (v - w) = c.charNorm (w - v) := by
  rw [← neg_sub, charNorm_neg]

theorem charNorm_smul (a : ℝ) (v : V) : c.charNorm (a • v) = |a| * c.charNorm v := by
  unfold charNorm
  simp only [map_smul, norm_smul, Real.norm_eq_abs]
  rw [mul_max_of_nonneg _ _ (abs_nonneg a), mul_max_of_nonneg _ _ (abs_nonneg a)]

/-- **The characteristic shift is nonexpansive** in the characteristic norm. -/
theorem charNorm_shift_le (hc : c.Proj) (a b d : V) {D : ℝ} (ha : c.charNorm a ≤ D)
    (hb : c.charNorm b ≤ D) (hd : c.charNorm d ≤ D) :
    c.charNorm (c.Pp a + c.Pm b + c.P0 d) ≤ D := by
  unfold charNorm
  simp only [map_add, hc.pp, hc.pm, hc.p0, hc.mp, hc.mm, hc.m0, hc.zp, hc.zm, hc.zz, add_zero,
    zero_add]
  exact max_le ((norm_Pp_le_charNorm a).trans ha)
    (max_le ((norm_Pm_le_charNorm b).trans hb) ((norm_P0_le_charNorm d).trans hd))

/-! ### One implicit-midpoint step -/

/-- **Characteristic-norm stability of one implicit-midpoint step** (`3σL ≤ 1`):
`charNorm (Y - Y') ≤ (1 + 6σL) charNorm (X - X')` and the increments differ by at most
`6σL charNorm (X - X')`. -/
theorem charNorm_midpointStep (hc : c.Proj) {G : Set V} {L σ : ℝ}
    (hL : ∀ x ∈ G, ∀ y ∈ G, ‖c.F x - c.F y‖ ≤ L * ‖x - y‖) (hL0 : 0 ≤ L) (hσ : 0 ≤ σ)
    (hσL : 3 * σ * L ≤ 1) {X Y X' Y' : V}
    (hY : Y = X + σ • c.F ((1 / 2 : ℝ) • (X + Y)))
    (hY' : Y' = X' + σ • c.F ((1 / 2 : ℝ) • (X' + Y')))
    (hm : (1 / 2 : ℝ) • (X + Y) ∈ G) (hm' : (1 / 2 : ℝ) • (X' + Y') ∈ G) :
    c.charNorm (Y - Y') ≤ (1 + 6 * σ * L) * c.charNorm (X - X') ∧
      ‖(Y - X) - (Y' - X')‖ ≤ 6 * σ * L * c.charNorm (X - X') := by
  set m := (1 / 2 : ℝ) • (X + Y)
  set m' := (1 / 2 : ℝ) • (X' + Y')
  set a := c.charNorm (X - X')
  set b := c.charNorm (Y - Y')
  have ha := charNorm_nonneg (c := c) (X - X')
  have hb := charNorm_nonneg (c := c) (Y - Y')
  have hmm : m - m' = (1 / 2 : ℝ) • ((X - X') + (Y - Y')) := by
    simp only [m, m']; module
  have hcm : c.charNorm (m - m') ≤ (a + b) / 2 := by
    rw [hmm, charNorm_smul]
    have := charNorm_add_le (c := c) (X - X') (Y - Y')
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  have hd : ‖c.F m - c.F m'‖ ≤ 3 * L * ((a + b) / 2) := by
    calc ‖c.F m - c.F m'‖ ≤ L * ‖m - m'‖ := hL _ hm _ hm'
      _ ≤ L * (3 * c.charNorm (m - m')) :=
          mul_le_mul_of_nonneg_left (norm_le_three_mul_charNorm hc _) hL0
      _ ≤ L * (3 * ((a + b) / 2)) := by gcongr
      _ = 3 * L * ((a + b) / 2) := by ring
  have hinc : (Y - X) - (Y' - X') = σ • (c.F m - c.F m') := by
    have e1 : Y - X = σ • c.F m := by rw [hY]; abel
    have e2 : Y' - X' = σ • c.F m' := by rw [hY']; abel
    rw [e1, e2, smul_sub]
  have hincn : ‖(Y - X) - (Y' - X')‖ ≤ σ * (3 * L * ((a + b) / 2)) := by
    rw [hinc, norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ]
    exact mul_le_mul_of_nonneg_left hd hσ
  have hYY : Y - Y' = (X - X') + ((Y - X) - (Y' - X')) := by abel
  have hb' : b ≤ a + σ * (3 * L * ((a + b) / 2)) := by
    calc b = c.charNorm ((X - X') + ((Y - X) - (Y' - X'))) := by rw [← hYY]
      _ ≤ a + c.charNorm ((Y - X) - (Y' - X')) := charNorm_add_le _ _
      _ ≤ a + ‖(Y - X) - (Y' - X')‖ := by gcongr; exact charNorm_le_norm hc _
      _ ≤ a + σ * (3 * L * ((a + b) / 2)) := by gcongr
  have hc0 : 0 ≤ σ * L := mul_nonneg hσ hL0
  have hkey : b * (1 - 3 * (σ * L) / 2) ≤ a * (1 + 3 * (σ * L) / 2) := by nlinarith
  have hb2 : b ≤ (1 + 6 * σ * L) * a := by
    have h1 : 0 < 1 - 3 * (σ * L) / 2 := by nlinarith
    have h2 : a * (1 + 3 * (σ * L) / 2) ≤ (1 + 6 * σ * L) * a * (1 - 3 * (σ * L) / 2) := by
      have : 0 ≤ a * (σ * L) * (3 - 9 * (σ * L)) := by
        apply mul_nonneg (mul_nonneg ha hc0); nlinarith
      nlinarith
    exact le_of_mul_le_mul_right (hkey.trans h2) h1
  refine ⟨hb2, hincn.trans ?_⟩
  have : σ * (3 * L * ((a + b) / 2)) ≤ σ * (3 * L * ((a + (1 + 6 * σ * L) * a) / 2)) := by
    gcongr
  refine this.trans ?_
  have : 0 ≤ a * (σ * L) * (1 - 3 * (σ * L)) := mul_nonneg (mul_nonneg ha hc0) (by nlinarith)
  nlinarith

/-! ### Grid distances -/

variable [NeZero N]

theorem charNorm_le_charSup (v : ZMod N → V) (j : ZMod N) : c.charNorm (v j) ≤ c.charSup v :=
  Finset.le_sup' (fun j => c.charNorm (v j)) (mem_univ j)

theorem charSup_le {v : ZMod N → V} {C : ℝ} (h : ∀ j, c.charNorm (v j) ≤ C) :
    c.charSup v ≤ C :=
  Finset.sup'_le _ _ fun j _ => h j

theorem charSup_nonneg (v : ZMod N → V) : 0 ≤ c.charSup v :=
  (charNorm_nonneg _).trans (charNorm_le_charSup v 0)

theorem charSup_add_le (v w : ZMod N → V) : c.charSup (v + w) ≤ c.charSup v + c.charSup w :=
  charSup_le fun j => (charNorm_add_le (v j) (w j)).trans
    (add_le_add (charNorm_le_charSup v j) (charNorm_le_charSup w j))

theorem charSup_le_norm (hc : c.Proj) (v : ZMod N → V) : c.charSup v ≤ ‖v‖ :=
  charSup_le fun j => (charNorm_le_norm hc _).trans (norm_le_pi_norm v j)

theorem charNorm_le_dist0 (X Y : CGrid V N) (j : ZMod N) :
    c.charNorm (X.site j - Y.site j) ≤ c.dist0 X Y :=
  (charNorm_le_charSup (X.site - Y.site) j).trans (le_max_left _ _)

theorem abs_lam_le_dist0 (X Y : CGrid V N) (j : ZMod N) :
    |X.lam j - Y.lam j| ≤ c.dist0 X Y := by
  have := norm_le_pi_norm (X.lam - Y.lam) j
  rw [Pi.sub_apply, Real.norm_eq_abs] at this
  exact this.trans (le_max_right _ _)

theorem dist0_nonneg (X Y : CGrid V N) : 0 ≤ c.dist0 X Y :=
  (norm_nonneg _).trans (le_max_right _ _)

theorem dist0_le {X Y : CGrid V N} {C : ℝ}
    (hs : ∀ j, c.charNorm (X.site j - Y.site j) ≤ C) (hl : ∀ j, |X.lam j - Y.lam j| ≤ C) :
    c.dist0 X Y ≤ C := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hl 0)
  refine max_le (charSup_le fun j => hs j) ((pi_norm_le_iff_of_nonneg hC).2 fun j => ?_)
  rw [Pi.sub_apply, Real.norm_eq_abs]; exact hl j

theorem dist0_triangle (X Y Z : CGrid V N) :
    c.dist0 X Z ≤ c.dist0 X Y + c.dist0 Y Z := by
  refine dist0_le (fun j => ?_) (fun j => ?_)
  · have e : X.site j - Z.site j = (X.site j - Y.site j) + (Y.site j - Z.site j) := by abel
    rw [e]
    exact (charNorm_add_le _ _).trans (add_le_add (charNorm_le_dist0 X Y j)
      (charNorm_le_dist0 Y Z j))
  · have e : X.lam j - Z.lam j = (X.lam j - Y.lam j) + (Y.lam j - Z.lam j) := by ring
    rw [e]
    exact (abs_add_le _ _).trans (add_le_add (abs_lam_le_dist0 X Y j) (abs_lam_le_dist0 Y Z j))

/-! ### Source steps, transport and the split step -/

/-- **Grid source steps are `(1 + 6σL)`-Lipschitz in `dist0`**, with `6σL`-Lipschitz site
increments. -/
theorem dist0_srcStep (hc : c.Proj) {G : Set V} {L σ : ℝ}
    (hL : ∀ x ∈ G, ∀ y ∈ G, ‖c.F x - c.F y‖ ≤ L * ‖x - y‖) (hL0 : 0 ≤ L) (hσ : 0 ≤ σ)
    (hσL : 3 * σ * L ≤ 1) {X A X' A' : CGrid V N} (h : c.IsSrc σ X A) (h' : c.IsSrc σ X' A')
    (hm : ∀ j, (1 / 2 : ℝ) • (X.site j + A.site j) ∈ G)
    (hm' : ∀ j, (1 / 2 : ℝ) • (X'.site j + A'.site j) ∈ G) :
    c.dist0 A A' ≤ (1 + 6 * σ * L) * c.dist0 X X' ∧
      ∀ j, ‖(A.site j - X.site j) - (A'.site j - X'.site j)‖ ≤ 6 * σ * L * c.dist0 X X' := by
  have hk : 0 ≤ 6 * σ * L := by positivity
  have hD := dist0_nonneg (c := c) X X'
  have key := fun j => charNorm_midpointStep hc hL hL0 hσ hσL (h.1 j) (h'.1 j) (hm j) (hm' j)
  refine ⟨dist0_le (fun j => ?_) (fun j => ?_), fun j => ?_⟩
  · exact (key j).1.trans (mul_le_mul_of_nonneg_left (charNorm_le_dist0 X X' j) (by linarith))
  · rw [h.2, h'.2]
    have := abs_lam_le_dist0 (c := c) X X' j
    nlinarith
  · exact (key j).2.trans (mul_le_mul_of_nonneg_left (charNorm_le_dist0 X X' j) hk)

theorem transport_site_sub (ℓ : ℝ) (X X' : CGrid V N) (j : ZMod N) :
    (c.transport ℓ X).site j - (c.transport ℓ X').site j =
      c.Pp (X.site (j + 1) - X'.site (j + 1)) + c.Pm (X.site (j - 1) - X'.site (j - 1)) +
        c.P0 (X.site j - X'.site j) := by
  simp only [transport, map_sub]
  abel

/-- The background increments of two transported states differ by at most `2 L_g ℓ dist0`. -/
theorem transport_lam_increment_le {Lg ℓ : ℝ} (hℓ : 0 ≤ ℓ) {G : Set V}
    (hgp : ∀ x ∈ G, ∀ y ∈ G, |c.gp x - c.gp y| ≤ Lg * ‖c.Pp (x - y)‖)
    (hgm : ∀ x ∈ G, ∀ y ∈ G, |c.gm x - c.gm y| ≤ Lg * ‖c.Pm (x - y)‖) (hLg : 0 ≤ Lg)
    {X X' : CGrid V N} (hX : ∀ j, X.site j ∈ G) (hX' : ∀ j, X'.site j ∈ G) (j : ZMod N) :
    |((c.transport ℓ X).lam j - X.lam j) - ((c.transport ℓ X').lam j - X'.lam j)| ≤
      2 * Lg * ℓ * c.dist0 X X' := by
  have hp : ∀ k, |c.gp (X.site k) - c.gp (X'.site k)| ≤ Lg * c.dist0 X X' := fun k =>
    (hgp _ (hX k) _ (hX' k)).trans (mul_le_mul_of_nonneg_left
      ((norm_Pp_le_charNorm _).trans (charNorm_le_dist0 X X' k)) hLg)
  have hm : ∀ k, |c.gm (X.site k) - c.gm (X'.site k)| ≤ Lg * c.dist0 X X' := fun k =>
    (hgm _ (hX k) _ (hX' k)).trans (mul_le_mul_of_nonneg_left
      ((norm_Pm_le_charNorm _).trans (charNorm_le_dist0 X X' k)) hLg)
  simp only [transport]
  set a1 := c.gp (X.site j) - c.gp (X'.site j)
  set a2 := c.gp (X.site (j + 1)) - c.gp (X'.site (j + 1))
  set a3 := c.gm (X.site j) - c.gm (X'.site j)
  set a4 := c.gm (X.site (j - 1)) - c.gm (X'.site (j - 1))
  have e : X.lam j + ℓ / 2 * ((c.gp (X.site j) + c.gp (X.site (j + 1))) +
        (c.gm (X.site j) + c.gm (X.site (j - 1)))) - X.lam j -
      (X'.lam j + ℓ / 2 * ((c.gp (X'.site j) + c.gp (X'.site (j + 1))) +
        (c.gm (X'.site j) + c.gm (X'.site (j - 1)))) - X'.lam j) =
      ℓ / 2 * ((a1 + a2) + (a3 + a4)) := by simp only [a1, a2, a3, a4]; ring
  rw [e, abs_mul, abs_of_nonneg (by linarith : 0 ≤ ℓ / 2)]
  have h4 := abs_add_le (a1 + a2) (a3 + a4)
  have h5 := abs_add_le a1 a2
  have h6 := abs_add_le a3 a4
  have hsum : |(a1 + a2) + (a3 + a4)| ≤ 4 * (Lg * c.dist0 X X') := by
    linarith [hp j, hp (j + 1), hm j, hm (j - 1)]
  calc ℓ / 2 * |(a1 + a2) + (a3 + a4)| ≤ ℓ / 2 * (4 * (Lg * c.dist0 X X')) :=
        mul_le_mul_of_nonneg_left hsum (by linarith)
    _ = 2 * Lg * ℓ * c.dist0 X X' := by ring

/-- **The transport is `(1 + 2L_gℓ)`-Lipschitz in `dist0`.** -/
theorem dist0_transport (hc : c.Proj) {Lg ℓ : ℝ} (hℓ : 0 ≤ ℓ) {G : Set V}
    (hgp : ∀ x ∈ G, ∀ y ∈ G, |c.gp x - c.gp y| ≤ Lg * ‖c.Pp (x - y)‖)
    (hgm : ∀ x ∈ G, ∀ y ∈ G, |c.gm x - c.gm y| ≤ Lg * ‖c.Pm (x - y)‖) (hLg : 0 ≤ Lg)
    {X X' : CGrid V N} (hX : ∀ j, X.site j ∈ G) (hX' : ∀ j, X'.site j ∈ G) :
    c.dist0 (c.transport ℓ X) (c.transport ℓ X') ≤ (1 + 2 * Lg * ℓ) * c.dist0 X X' := by
  have hD := dist0_nonneg (c := c) X X'
  have hk : 0 ≤ 2 * Lg * ℓ := by positivity
  refine dist0_le (fun j => ?_) (fun j => ?_)
  · rw [transport_site_sub]
    refine (charNorm_shift_le hc _ _ _ (charNorm_le_dist0 X X' (j + 1))
      (charNorm_le_dist0 X X' (j - 1)) (charNorm_le_dist0 X X' j)).trans ?_
    nlinarith
  · have hinc := transport_lam_increment_le hℓ hgp hgm hLg hX hX' j
    have hl := abs_lam_le_dist0 (c := c) X X' j
    have e : (c.transport ℓ X).lam j - (c.transport ℓ X').lam j =
        (X.lam j - X'.lam j) + (((c.transport ℓ X).lam j - X.lam j) -
          ((c.transport ℓ X').lam j - X'.lam j)) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    nlinarith

/-- **The split map is `(1 + (9L + 8L_g)ℓ)`-Lipschitz in `dist0`** on the envelope `G`
(`3ℓL ≤ 1`, `2L_gℓ ≤ 1`). -/
theorem dist0_splitStep (hc : c.Proj) {G : Set V} {L Lg ℓ : ℝ}
    (hL : ∀ x ∈ G, ∀ y ∈ G, ‖c.F x - c.F y‖ ≤ L * ‖x - y‖) (hL0 : 0 ≤ L)
    (hgp : ∀ x ∈ G, ∀ y ∈ G, |c.gp x - c.gp y| ≤ Lg * ‖c.Pp (x - y)‖)
    (hgm : ∀ x ∈ G, ∀ y ∈ G, |c.gm x - c.gm y| ≤ Lg * ‖c.Pm (x - y)‖) (hLg : 0 ≤ Lg)
    (hℓ : 0 ≤ ℓ) (hℓL : 3 * ℓ * L ≤ 1) (hℓLg : 2 * Lg * ℓ ≤ 1)
    {X A B X' A' B' : CGrid V N} (hs : c.IsSplit ℓ X A B) (hs' : c.IsSplit ℓ X' A' B')
    (he : c.Env0 G ℓ X A B) (he' : c.Env0 G ℓ X' A' B') :
    c.dist0 B B' ≤ (1 + (9 * L + 8 * Lg) * ℓ) * c.dist0 X X' := by
  have hσ : 0 ≤ ℓ / 2 := by linarith
  have hσL : 3 * (ℓ / 2) * L ≤ 1 := by nlinarith
  have hD := dist0_nonneg (c := c) X X'
  obtain ⟨h1, -⟩ := dist0_srcStep hc hL hL0 hσ hσL hs.1 hs'.1 (fun j => (he j).1)
    (fun j => (he' j).1)
  have h2 := dist0_transport hc hℓ hgp hgm hLg (fun j => (he j).2.1) (fun j => (he' j).2.1)
  obtain ⟨h3, -⟩ := dist0_srcStep hc hL hL0 hσ hσL hs.2 hs'.2 (fun j => (he j).2.2)
    (fun j => (he' j).2.2)
  have e6 : 6 * (ℓ / 2) * L = 3 * ℓ * L := by ring
  rw [e6] at h1 h3
  have ha0 : 0 ≤ 3 * ℓ * L := by positivity
  have hb0 : 0 ≤ 2 * Lg * ℓ := by positivity
  calc c.dist0 B B' ≤ (1 + 3 * ℓ * L) * ((1 + 2 * Lg * ℓ) * ((1 + 3 * ℓ * L) *
        c.dist0 X X')) := by
        refine h3.trans (mul_le_mul_of_nonneg_left (h2.trans ?_) (by linarith))
        exact mul_le_mul_of_nonneg_left h1 (by linarith)
    _ ≤ (1 + (9 * L + 8 * Lg) * ℓ) * c.dist0 X X' := by
        rw [← mul_assoc, ← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ hD
        have : (3 * ℓ * L) * (3 * ℓ * L) ≤ 3 * ℓ * L := by nlinarith
        have : (3 * ℓ * L) * (2 * Lg * ℓ) ≤ 2 * Lg * ℓ := by nlinarith
        have : (3 * ℓ * L) * (3 * ℓ * L) * (2 * Lg * ℓ) ≤ 2 * Lg * ℓ := by nlinarith
        nlinarith

end CharData

/-! ### Grid sampling of a reference solution and the one-step error -/

/-- The grid sampling `j ↦ (Z(τ, θ_j), λ(τ, θ_j))`, `θ_j = j · 2π/N`. -/
def sampleGrid (Z : ℝ × ℝ → V) (lam : ℝ × ℝ → ℝ) (N : ℕ) (τ : ℝ) : CGrid V N where
  site j := Z (τ, GowdyStaggered.sampleAngle N j)
  lam j := lam (τ, GowdyStaggered.sampleAngle N j)

open CharacteristicSplitting

namespace StrangCharData

/-- The characteristic data of a Strang setup. -/
def data (S : StrangSetup V) : CharData V := ⟨S.Pp, S.Pm, S.P0, S.F, S.gp, S.gm⟩

end StrangCharData

open StrangCharData

variable {N : ℕ} [NeZero N]

/-- **The reference split step exists on the near-identity branch and lies in the chart.** -/
theorem strang_reference_step [CompleteSpace V] (S : StrangSetup V)
    (hZper : ∀ p : ℝ × ℝ, S.Z (p.1, p.2 + 2 * Real.pi) = S.Z p)
    (hN : 2 * Real.pi / N ≤ S.stepBound) (τ : ℝ) (hτ : S.t₀ ≤ τ)
    (hτh : τ + 2 * Real.pi / N ≤ S.t₁) :
    ∃ X₁ X₃ : CGrid V N, (data S).IsSplit (2 * Real.pi / N) (sampleGrid S.Z S.lam N τ) X₁ X₃ ∧
      (data S).Env0 S.K (2 * Real.pi / N) (sampleGrid S.Z S.lam N τ) X₁ X₃ ∧
      (∀ j, ‖X₁.site j - S.Z (τ, GowdyStaggered.sampleAngle N j)‖ ≤ S.δ) ∧
      (∀ j, ‖X₃.site j - ((data S).transport (2 * Real.pi / N) X₁).site j‖ ≤ S.δ) := by
  set ℓ := 2 * Real.pi / N with hℓ
  have hℓpos : 0 < ℓ := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  have hslab : ∀ k : ZMod N, ((τ, GowdyStaggered.sampleAngle N k) : ℝ × ℝ).1 ∈ Icc S.t₀ S.t₁ :=
    fun k => ⟨hτ, by show τ ≤ S.t₁; linarith⟩
  have h1 := fun k : ZMod N => S.stage_one_exists hℓpos hN (hslab k)
  choose Y hYd hY using h1
  let X₁ : CGrid V N := ⟨Y, (sampleGrid S.Z S.lam N τ).lam⟩
  have hnear : ∀ j, ‖((data S).transport ℓ X₁).site j -
      S.Z (τ + ℓ, GowdyStaggered.sampleAngle N j)‖ ≤ S.δ / 2 := by
    intro j
    have hZp : S.Z (τ, GowdyStaggered.sampleAngle N (j + 1)) =
        S.Z (τ, GowdyStaggered.sampleAngle N j + ℓ) :=
      GowdyStaggered.sample_succ S.Z hZper N τ j
    have hZm : S.Z (τ, GowdyStaggered.sampleAngle N (j - 1)) =
        S.Z (τ, GowdyStaggered.sampleAngle N j - ℓ) :=
      GowdyStaggered.sample_pred S.Z hZper N τ j
    have h1p := hY (j + 1)
    have h1m := hY (j - 1)
    have hd1p := hYd (j + 1)
    have hd1m := hYd (j - 1)
    rw [hZp] at h1p hd1p
    rw [hZm] at h1m hd1m
    exact S.transportCombine_near hℓpos hN hτ hτh h1m hd1m (hY j) (hYd j) h1p hd1p
  have h3 := fun j : ZMod N => S.stage_three_exists hℓpos hN hτ hτh (hnear j)
  choose Y3 hY3d hY3 using h3
  let X₃ : CGrid V N := ⟨Y3, ((data S).transport ℓ X₁).lam⟩
  have hδ := S.δ_pos
  refine ⟨X₁, X₃, ⟨⟨fun k => hY k, rfl⟩, ⟨fun k => hY3 k, rfl⟩⟩, fun j => ⟨?_, ?_, ?_⟩,
    fun k => hYd k, fun k => (hY3d k).trans (by linarith)⟩
  · apply S.tube _ (hslab j)
    show ‖(1 / 2 : ℝ) • (S.Z (τ, GowdyStaggered.sampleAngle N j) + Y j) -
      S.Z (τ, GowdyStaggered.sampleAngle N j)‖ ≤ S.δ
    rw [norm_midpoint_sub_left]
    linarith [hYd j, norm_nonneg (Y j - S.Z (τ, GowdyStaggered.sampleAngle N j))]
  · exact S.tube _ (hslab j) _ (hYd j)
  · apply S.tube (τ + ℓ, GowdyStaggered.sampleAngle N j) ⟨by simp; linarith, by simpa using hτh⟩
    set T := ((data S).transport ℓ X₁).site j
    have e : (1 / 2 : ℝ) • (T + Y3 j) - S.Z (τ + ℓ, GowdyStaggered.sampleAngle N j) =
        (T - S.Z (τ + ℓ, GowdyStaggered.sampleAngle N j)) + (1 / 2 : ℝ) • (Y3 j - T) := by module
    show ‖(1 / 2 : ℝ) • (T + Y3 j) - S.Z (τ + ℓ, GowdyStaggered.sampleAngle N j)‖ ≤ S.δ
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul]
    have := hY3d j
    have := hnear j
    norm_num
    linarith

/-- **The local error of the reference split step** (second-order consistency on the grid):
every near-identity reference split step from the sampled solution reproduces the sampled
solution at `τ + ℓ` up to `C ℓ³` in `dist0`, `C = max(stateConst, lamConst)`. -/
theorem strang_local_error_dist0 (S : StrangSetup V) (hc : (data S).Proj)
    (hZper : ∀ p : ℝ × ℝ, S.Z (p.1, p.2 + 2 * Real.pi) = S.Z p)
    (hN : 2 * Real.pi / N ≤ S.stepBound) (τ : ℝ) (hτ : S.t₀ ≤ τ)
    (hτh : τ + 2 * Real.pi / N ≤ S.t₁) (X₁ X₃ : CGrid V N)
    (hs : (data S).IsSplit (2 * Real.pi / N) (sampleGrid S.Z S.lam N τ) X₁ X₃)
    (hd₁ : ∀ j, ‖X₁.site j - S.Z (τ, GowdyStaggered.sampleAngle N j)‖ ≤ S.δ)
    (hd₃ : ∀ j, ‖X₃.site j - ((data S).transport (2 * Real.pi / N) X₁).site j‖ ≤ S.δ) :
    (data S).dist0 X₃ (sampleGrid S.Z S.lam N (τ + 2 * Real.pi / N)) ≤
      max S.stateConst S.lamConst * (2 * Real.pi / N) ^ 3 := by
  set ℓ := 2 * Real.pi / N with hℓ
  have hℓpos : 0 < ℓ := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  have hC1 : S.stateConst ≤ max S.stateConst S.lamConst := le_max_left _ _
  have hC2 : S.lamConst ≤ max S.stateConst S.lamConst := le_max_right _ _
  have hℓ3 : 0 ≤ ℓ ^ 3 := by positivity
  have key : ∀ j, ‖X₃.site j - S.Z (τ + ℓ, GowdyStaggered.sampleAngle N j)‖ ≤
      S.stateConst * ℓ ^ 3 ∧
      |S.lam (τ, GowdyStaggered.sampleAngle N j) + ℓ / 2 *
        ((S.gp (X₁.site j) + S.gp (X₁.site (j + 1))) +
          (S.gm (X₁.site j) + S.gm (X₁.site (j - 1)))) -
        S.lam (τ + ℓ, GowdyStaggered.sampleAngle N j)| ≤ S.lamConst * ℓ ^ 3 := by
    intro j
    set θ := GowdyStaggered.sampleAngle N j
    have hZp : S.Z (τ, GowdyStaggered.sampleAngle N (j + 1)) = S.Z (τ, θ + ℓ) :=
      GowdyStaggered.sample_succ S.Z hZper N τ j
    have hZm : S.Z (τ, GowdyStaggered.sampleAngle N (j - 1)) = S.Z (τ, θ - ℓ) :=
      GowdyStaggered.sample_pred S.Z hZper N τ j
    have hstage1 := hs.1.1
    have h1p := hstage1 (j + 1)
    have h1m := hstage1 (j - 1)
    have h10 := hstage1 j
    have hd1p := hd₁ (j + 1)
    have hd1m := hd₁ (j - 1)
    have hd10 := hd₁ j
    simp only [sampleGrid, data] at h1p h1m h10
    rw [hZp] at h1p hd1p
    rw [hZm] at h1m hd1m
    have h3 := hs.2.1 j
    have htr : ((data S).transport ℓ X₁).site j =
        S.transportCombine (X₁.site (j - 1)) (X₁.site j) (X₁.site (j + 1)) := rfl
    rw [htr] at h3
    have hd3 := hd₃ j
    rw [htr] at hd3
    exact S.local_error (h := ℓ) (τ := τ) (θ := θ) hℓpos hN hτ hτh h1m hd1m h10 hd10 h1p hd1p
      h3 hd3
  refine CharData.dist0_le (fun j => ?_) (fun j => ?_)
  · exact (CharData.charNorm_le_norm hc _).trans ((key j).1.trans
      (mul_le_mul_of_nonneg_right hC1 hℓ3))
  · have elam : X₃.lam j = S.lam (τ, GowdyStaggered.sampleAngle N j) + ℓ / 2 *
        ((S.gp (X₁.site j) + S.gp (X₁.site (j + 1))) +
          (S.gm (X₁.site j) + S.gm (X₁.site (j - 1)))) := by
      rw [hs.2.2]
      simp only [CharData.transport, hs.1.2, sampleGrid, data]
    rw [elam]
    exact (key j).2.trans (mul_le_mul_of_nonneg_right hC2 hℓ3)

/-- **One step of the error recursion for an abstract characteristic Strang splitting**: for a
numerical split step `X → A → B` with stages in the chart `K` of the setup,
`dist0 (B, 𝖲X_*(τ+ℓ)) ≤ (1 + (9L + 8L_g)ℓ) dist0 (X, 𝖲X_*(τ)) + max(stateConst, lamConst) ℓ³`. -/
theorem oneStep_strang [CompleteSpace V] (S : StrangSetup V) (hc : (data S).Proj)
    (hZper : ∀ p : ℝ × ℝ, S.Z (p.1, p.2 + 2 * Real.pi) = S.Z p)
    (hN : 2 * Real.pi / N ≤ S.stepBound) (hNL : 3 * (2 * Real.pi / N) * S.L ≤ 1)
    (hNLg : 2 * S.Lg * (2 * Real.pi / N) ≤ 1) (τ : ℝ) (hτ : S.t₀ ≤ τ)
    (hτh : τ + 2 * Real.pi / N ≤ S.t₁) (X A B : CGrid V N)
    (hs : (data S).IsSplit (2 * Real.pi / N) X A B)
    (he : (data S).Env0 S.K (2 * Real.pi / N) X A B) :
    (data S).dist0 B (sampleGrid S.Z S.lam N (τ + 2 * Real.pi / N)) ≤
      (1 + (9 * S.L + 8 * S.Lg) * (2 * Real.pi / N)) *
        (data S).dist0 X (sampleGrid S.Z S.lam N τ) +
      max S.stateConst S.lamConst * (2 * Real.pi / N) ^ 3 := by
  set ℓ := 2 * Real.pi / N with hℓ
  have hℓpos : 0 < ℓ := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  obtain ⟨X₁, X₃, hs₀, he₀, hd₁, hd₃⟩ := strang_reference_step S hZper hN τ hτ hτh
  have hloc := strang_local_error_dist0 S hc hZper hN τ hτ hτh X₁ X₃ hs₀ hd₁ hd₃
  have hlip := CharData.dist0_splitStep hc (G := S.K) S.F_lip S.L_nonneg
    (fun x hx y hy => S.gp_lip x hx y hy) (fun x hx y hy => S.gm_lip x hx y hy) S.Lg_nonneg
    hℓpos.le hNL hNLg hs hs₀ he he₀
  calc (data S).dist0 B (sampleGrid S.Z S.lam N (τ + ℓ))
      ≤ (data S).dist0 B X₃ + (data S).dist0 X₃ (sampleGrid S.Z S.lam N (τ + ℓ)) :=
        CharData.dist0_triangle _ _ _
    _ ≤ _ := add_le_add hlip hloc

end

end RenewalGeometry.GridFaaDiBruno
