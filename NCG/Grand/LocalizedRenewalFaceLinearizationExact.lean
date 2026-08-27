/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.StableRenewalFaceLinearization

/-!
# Local derivative-free renewal face linearization

The face score is constrained only on a neighbourhood of zero.  Repeated
halving first kills the local quadratic Cauchy defect.  A canonical dyadic
extension is then additive on the whole ambient space, locally bounded, and
hence a unique continuous real-linear functional.
-/

open Filter
open scoped Topology

namespace NCG
namespace LocalizedRenewalFaceLinearizationExact

/-- Dyadic contraction used by the local extension. -/
noncomputable def faceScale {E : Type*} [SMul ℝ E] (n : ℕ) (x : E) : E :=
  ((2 : ℝ)⁻¹ ^ n) • x

/-- The manuscript's localized exact branch.  `A` is defined on the ambient
space only to avoid subtype bookkeeping; every hypothesis concerns `U`, and
the conclusion only asserts agreement on `U`, so values outside `U` are
irrelevant. -/
theorem localized_renewal_face_linearization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (A : E → ℝ) (r H : ℝ)
    (hU : U ∈ 𝓝 (0 : E))
    (hhalf_mem : ∀ z ∈ U, (2 : ℝ)⁻¹ • z ∈ U)
    (hhalf : ∀ z ∈ U, A z = 2 * A ((2 : ℝ)⁻¹ • z))
    (hr : 0 < r)
    (hquasi : ∀ x y, x ∈ U → y ∈ U → x + y ∈ U →
      ‖x‖ ≤ r → ‖y‖ ≤ r → ‖x + y‖ ≤ r →
      |A (x + y) - A x - A y| ≤ H * ‖x‖ * ‖y‖)
    (hbounded : Bornology.IsBounded (A '' U)) :
    ∃! ell : E →L[ℝ] ℝ, ∀ x ∈ U, ell x = A x := by
  let q : ℝ := (2 : ℝ)⁻¹
  have hq0 : 0 ≤ q := by dsimp [q]; norm_num
  have hq1 : q < 1 := by dsimp [q]; norm_num
  have hqpow : Tendsto (fun n : ℕ => q ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hscale_succ (n : ℕ) (x : E) :
      faceScale (n + 1) x = q • faceScale n x := by
    simp [faceScale, q, pow_succ, mul_smul, mul_comm]
  have hscale_add (n : ℕ) (x y : E) :
      faceScale n (x + y) = faceScale n x + faceScale n y := by
    exact smul_add _ _ _
  have hscale_mem {x : E} (hx : x ∈ U) : ∀ n, faceScale n x ∈ U := by
    intro n
    induction n with
    | zero => simpa [faceScale] using hx
    | succ n ih =>
        rw [show n + 1 = Nat.succ n by rfl, hscale_succ]
        exact hhalf_mem _ ih
  have hdyadic {x : E} (hx : x ∈ U) : ∀ n,
      A x = (2 : ℝ) ^ n * A (faceScale n x) := by
    intro n
    induction n with
    | zero => simp [faceScale]
    | succ n ih =>
        rw [ih, hhalf (faceScale n x) (hscale_mem hx n),
          show faceScale (Nat.succ n) x = q • faceScale n x by
            simpa [Nat.succ_eq_add_one] using hscale_succ n x,
          pow_succ]
        ring
  have hlocal_add : ∀ x y,
      x ∈ U → y ∈ U → x + y ∈ U →
      ‖x‖ ≤ r → ‖y‖ ≤ r → ‖x + y‖ ≤ r →
      A (x + y) = A x + A y := by
    intro x y hx hy hxy hnx hny hnxy
    have hdefect : ∀ n : ℕ,
        |A (x + y) - A x - A y| ≤
          q ^ n * (H * ‖x‖ * ‖y‖) := by
      intro n
      have hxdy := hdyadic hx n
      have hydy := hdyadic hy n
      have hxydy := hdyadic hxy n
      rw [hscale_add] at hxydy
      have hnorm (z : E) : ‖faceScale n z‖ = q ^ n * ‖z‖ := by
        rw [faceScale, norm_smul, Real.norm_eq_abs, abs_of_nonneg]
        exact pow_nonneg hq0 n
      have hqle : q ^ n ≤ 1 := pow_le_one₀ hq0 hq1.le
      have hsx : ‖faceScale n x‖ ≤ r := by
        rw [hnorm]
        exact (mul_le_of_le_one_left (norm_nonneg x) hqle).trans hnx
      have hsy : ‖faceScale n y‖ ≤ r := by
        rw [hnorm]
        exact (mul_le_of_le_one_left (norm_nonneg y) hqle).trans hny
      have hsxy : ‖faceScale n x + faceScale n y‖ ≤ r := by
        rw [← hscale_add, hnorm]
        exact (mul_le_of_le_one_left (norm_nonneg (x + y)) hqle).trans hnxy
      have hqz := hquasi (faceScale n x) (faceScale n y)
        (hscale_mem hx n) (hscale_mem hy n)
        (by rw [← hscale_add]; exact hscale_mem hxy n)
        hsx hsy hsxy
      rw [hnorm, hnorm] at hqz
      have heq : A (x + y) - A x - A y =
          (2 : ℝ) ^ n *
            (A (faceScale n x + faceScale n y) -
              A (faceScale n x) - A (faceScale n y)) := by
        rw [hxydy, hxdy, hydy]
        ring
      rw [heq, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ n)]
      calc
        (2 : ℝ) ^ n *
            |A (faceScale n x + faceScale n y) -
              A (faceScale n x) - A (faceScale n y)| ≤
            (2 : ℝ) ^ n *
              (H * (q ^ n * ‖x‖) * (q ^ n * ‖y‖)) :=
          mul_le_mul_of_nonneg_left hqz (by positivity)
        _ = q ^ n * (H * ‖x‖ * ‖y‖) := by
          dsimp [q]
          rw [inv_pow]
          field_simp
    have hlim : Tendsto
        (fun n : ℕ => q ^ n * (H * ‖x‖ * ‖y‖)) atTop (𝓝 0) := by
      simpa using hqpow.mul_const (H * ‖x‖ * ‖y‖)
    have hle : |A (x + y) - A x - A y| ≤ 0 :=
      le_of_tendsto_of_tendsto tendsto_const_nhds hlim
        (Eventually.of_forall hdefect)
    have hz : A (x + y) - A x - A y = 0 :=
      abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
    linarith
  let Good : E → ℕ → Prop := fun x n =>
    faceScale n x ∈ U ∧ ‖faceScale n x‖ ≤ r
  have hgood_exists (x : E) : ∃ n, Good x n := by
    have hs : Tendsto (fun n : ℕ => faceScale n x) atTop (𝓝 0) := by
      simpa [faceScale, q] using hqpow.smul_const x
    have heU : ∀ᶠ n in atTop, faceScale n x ∈ U := hs.eventually hU
    have heR : ∀ᶠ n in atTop, ‖faceScale n x‖ ≤ r :=
      by
        simpa [dist_eq_norm] using
          hs.eventually (Metric.closedBall_mem_nhds (0 : E) hr)
    exact (heU.and heR).exists
  have hgood_succ {x : E} {n : ℕ} (hn : Good x n) : Good x (n + 1) := by
    constructor
    · rw [hscale_succ]
      exact hhalf_mem _ hn.1
    · rw [hscale_succ, norm_smul, Real.norm_eq_abs, abs_of_nonneg hq0]
      have hqle : q ≤ 1 := hq1.le
      exact (mul_le_of_le_one_left (norm_nonneg (faceScale n x)) hqle).trans hn.2
  have hgood_mono {x : E} {n m : ℕ} (hnm : n ≤ m) (hn : Good x n) : Good x m := by
    induction m, hnm using Nat.le_induction with
    | base => exact hn
    | succ m _ ih => exact hgood_succ ih
  let renorm : ℕ → E → ℝ := fun n x => (2 : ℝ) ^ n * A (faceScale n x)
  have hrenorm_succ {x : E} {n : ℕ} (hn : Good x n) :
      renorm n x = renorm (n + 1) x := by
    dsimp [renorm]
    rw [hhalf (faceScale n x) hn.1, hscale_succ, pow_succ]
    ring
  have hrenorm_mono {x : E} {n m : ℕ} (hnm : n ≤ m) (hn : Good x n) :
      renorm n x = renorm m x := by
    induction m, hnm using Nat.le_induction with
    | base => rfl
    | succ m hnm ih =>
        exact ih.trans (hrenorm_succ (hgood_mono hnm hn))
  let idx : E → ℕ := fun x => Classical.choose (hgood_exists x)
  have hidx (x : E) : Good x (idx x) := Classical.choose_spec (hgood_exists x)
  let B : E → ℝ := fun x => renorm (idx x) x
  have hB_eq {x : E} {n : ℕ} (hn : Good x n) : B x = renorm n x := by
    let k := max (idx x) n
    calc
      B x = renorm (idx x) x := rfl
      _ = renorm k x := hrenorm_mono (le_max_left _ _) (hidx x)
      _ = renorm n x := (hrenorm_mono (le_max_right _ _) hn).symm
  have hB_on_U {x : E} (hx : x ∈ U) : B x = A x := by
    obtain ⟨n, hn⟩ := hgood_exists x
    rw [hB_eq hn]
    exact (hdyadic hx n).symm
  have hBadd : ∀ x y, B (x + y) = B x + B y := by
    intro x y
    obtain ⟨nx, hx⟩ := hgood_exists x
    obtain ⟨ny, hy⟩ := hgood_exists y
    obtain ⟨nxy, hxy⟩ := hgood_exists (x + y)
    let n := max (max nx ny) nxy
    have hx' : Good x n := hgood_mono (le_trans (le_max_left _ _) (le_max_left _ _)) hx
    have hy' : Good y n := hgood_mono (le_trans (le_max_right _ _) (le_max_left _ _)) hy
    have hxy' : Good (x + y) n := hgood_mono (le_max_right _ _) hxy
    calc
      B (x + y) = renorm n (x + y) := hB_eq hxy'
      _ = (2 : ℝ) ^ n *
          (A (faceScale n x) + A (faceScale n y)) := by
        dsimp [renorm]
        rw [hscale_add,
          hlocal_add (faceScale n x) (faceScale n y)
            hx'.1 hy'.1 (by rw [← hscale_add]; exact hxy'.1)
            hx'.2 hy'.2 (by rw [← hscale_add]; exact hxy'.2)]
      _ = renorm n x + renorm n y := by dsimp [renorm]; ring
      _ = B x + B y := by rw [← hB_eq hx', ← hB_eq hy']
  obtain ⟨ell, hell, hell_unique⟩ :=
    additive_locallyBounded_toContinuousLinearMap B hBadd hU
      (by
        refine hbounded.subset ?_
        rintro y ⟨x, hx, rfl⟩
        exact ⟨x, hx, (hB_on_U hx).symm⟩)
  refine ⟨ell, ?_, ?_⟩
  · intro x hx
    exact (hell x).trans (hB_on_U hx)
  · intro g hg
    apply hell_unique
    intro x
    obtain ⟨n, hn⟩ := hgood_exists x
    have hrepr : (2 : ℝ) ^ n • faceScale n x = x := by
      simp [faceScale, smul_smul]
    calc
      g x = g ((2 : ℝ) ^ n • faceScale n x) :=
        congrArg g hrepr.symm
      _ = (2 : ℝ) ^ n * g (faceScale n x) := by
        rw [map_smul]
        rfl
      _ = (2 : ℝ) ^ n * A (faceScale n x) := by
        rw [hg _ hn.1]
      _ = renorm n x := rfl
      _ = B x := (hB_eq hn).symm

end LocalizedRenewalFaceLinearizationExact
end NCG
