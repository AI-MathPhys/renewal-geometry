/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.PeriodicCubeCalculus

/-!
# The `L²` energy inequality for symmetric hyperbolic systems on `[t₀,t₁] × 𝕋^d`

Generic infrastructure (no renewal notions) for `prop:dirac-stability` of the
Einstein–Standard-Model action-closure manuscript.

Space-time is `ℝ^{1+d} = Fin (d+1) → ℝ` with time coordinate `0`; a point is `Fin.cons t y`,
`y ∈ ℝ^d`.  Fields and coefficients are periodic under the spatial shifts `(0, k)`, `k ∈ ℤ^d`
(sections over `ℝ × 𝕋^d`), and spatial integrals are over the unit cube `[0,1]^d`.

For a first-order system with matrix coefficients `A^μ(t,y) ∈ ℂ^{N×N}` we write the principal part
`P w = Σ_μ A^μ ∂_μ w` (`princ`).  The hypotheses `SymHyp` are those of a **symmetric hyperbolic
system with `W^{1,∞}` coefficients**: `A^μ` Hermitian, bounded by `C_b` and `L`-Lipschitz on the
closed slab `[t₀,t₁] × ℝ^d` (the `W^{1,∞}` bound, without any differentiability of `A^μ`), and the
solution `w` is `C¹` on an open slab `(a,b) × ℝ^d ⊃ [t₀,t₁] × ℝ^d`.

* `dini_energy`: the energy `E(t) = ∫_{[0,1]^d} Re⟨w, A⁰w⟩` has right upper Dini derivative at most
  `(d+1)|N|²L ‖w(t)‖²_{L²} + 2∫ Re⟨P w, w⟩`.  The time derivative of `A⁰` is replaced by its
  Lipschitz constant (frozen-coefficient difference quotients), and the spatial terms
  `2∫Re⟨A^j∂_jw,w⟩` are bounded by the Lipschitz commutator lemma
  `PeriodicCube.neg_two_integral_ip_pd_le` (integration by parts on the torus).
* **`l2_energy_estimate`** (the `L²` energy inequality with Gronwall): if `A⁰ ≥ c > 0` on the slab
  and `‖P w‖ ≤ m + K₀‖w‖` pointwise with `m` continuous, then for `t ∈ [t₀,t₁]`
  `c ‖w(t)‖²_{L²} ≤ e^{K(t₁-t₀)} (|N|²C_b ‖w(t₀)‖²_{L²} + |N| ∫_{t₀}^{t₁} ‖m(τ)‖²_{L²} dτ)`,
  `K = ((d+1)|N|²L + |N|(1+2K₀))/c + 1`.  For the difference `w = Ψ_h - Ψ_j` of two solutions of
  `A_h^μ∂_μΨ + B_hΨ = r_h`, `A_j^μ∂_μΨ + B_jΨ = r_j`, `P_h w = r_h - r_j - B_h w - (A_h - A_j)∂Ψ_j -
  (B_h - B_j)Ψ_j`, which is the paper's `eq:dirac-L2-stability` (with an `L²_t` source).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.SymHypEnergy

open PeriodicCube
open SobolevOpen (pd)

set_option linter.unusedSectionVars false

variable {d : ℕ}

/-! ### Space-time coordinates -/

/-- The closed slab `[t₀, t₁] × ℝ^d`. -/
def slab (t₀ t₁ : ℝ) : Set (Fin (d + 1) → ℝ) := {x | x 0 ∈ Icc t₀ t₁}

/-- The open slab `(a, b) × ℝ^d`. -/
def openSlab (a b : ℝ) : Set (Fin (d + 1) → ℝ) := {x | x 0 ∈ Ioo a b}

theorem isOpen_openSlab (a b : ℝ) : IsOpen (openSlab (d := d) a b) :=
  isOpen_Ioo.preimage (continuous_apply 0)

theorem cons_mem_slab {t₀ t₁ t : ℝ} (y : Fin d → ℝ) :
    (Fin.cons t y : Fin (d + 1) → ℝ) ∈ slab t₀ t₁ ↔ t ∈ Icc t₀ t₁ := by
  simp [slab]

theorem cons_mem_openSlab {a b t : ℝ} (y : Fin d → ℝ) :
    (Fin.cons t y : Fin (d + 1) → ℝ) ∈ openSlab a b ↔ t ∈ Ioo a b := by
  simp [openSlab]

theorem slab_subset_openSlab {a t₀ t₁ b : ℝ} (ha : a < t₀) (hb : t₁ < b) :
    slab (d := d) t₀ t₁ ⊆ openSlab a b := fun x hx =>
  ⟨ha.trans_le hx.1, hx.2.trans_lt hb⟩

/-- The spatial shift `(0, k)`. -/
def sshift (k : Fin d → ℤ) : Fin (d + 1) → ℝ := Fin.cons 0 (zvec k)

/-- Spatial periodicity. -/
def IsSPeriodic {α : Type*} (f : (Fin (d + 1) → ℝ) → α) : Prop :=
  ∀ (k : Fin d → ℤ) (x : Fin (d + 1) → ℝ), f (x + sshift k) = f x

theorem cons_add_cons (t s : ℝ) (y z : Fin d → ℝ) :
    (Fin.cons t y : Fin (d + 1) → ℝ) + Fin.cons s z = Fin.cons (t + s) (y + z) := by
  ext i
  induction i using Fin.cases <;> simp

theorem IsSPeriodic.slice {α : Type*} {f : (Fin (d + 1) → ℝ) → α} (hf : IsSPeriodic f) (t : ℝ) :
    IsZPeriodic (fun y : Fin d → ℝ => f (Fin.cons t y)) := fun k y => by
  have := hf k (Fin.cons t y)
  rw [sshift, cons_add_cons, add_zero] at this
  exact this

theorem cons_time_eq (t s : ℝ) (y : Fin d → ℝ) :
    (Fin.cons (t + s) y : Fin (d + 1) → ℝ) = Fin.cons t y + s • ev 0 := by
  ext i
  induction i using Fin.cases <;> simp [Pi.single_apply]

theorem cons_space_eq (t s : ℝ) (y : Fin d → ℝ) (j : Fin d) :
    (Fin.cons t (y + s • ev j) : Fin (d + 1) → ℝ) = Fin.cons t y + s • ev j.succ := by
  ext i
  induction i using Fin.cases with
  | zero => simp
  | succ k => simp [Pi.single_apply]

theorem norm_cons_sub_space (t : ℝ) (y y' : Fin d → ℝ) :
    ‖(Fin.cons t y : Fin (d + 1) → ℝ) - Fin.cons t y'‖ ≤ ‖y - y'‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
  induction i using Fin.cases with
  | zero => simp
  | succ k =>
    simp only [Pi.sub_apply, Fin.cons_succ]
    exact norm_le_pi_norm (y - y') k

theorem norm_cons_sub_time (t s : ℝ) (y : Fin d → ℝ) :
    ‖(Fin.cons t y : Fin (d + 1) → ℝ) - Fin.cons s y‖ ≤ |t - s| := by
  refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr fun i => ?_
  induction i using Fin.cases with
  | zero => simp
  | succ k => simp

theorem contDiff_cons {n : WithTop ℕ∞} (t : ℝ) :
    ContDiff ℝ n (fun y : Fin d → ℝ => (Fin.cons t y : Fin (d + 1) → ℝ)) := by
  refine contDiff_pi.mpr fun i => ?_
  induction i using Fin.cases with
  | zero => simpa using contDiff_const
  | succ k => simpa using contDiff_apply ℝ ℝ k

theorem continuous_cons (t : ℝ) :
    Continuous (fun y : Fin d → ℝ => (Fin.cons t y : Fin (d + 1) → ℝ)) :=
  (contDiff_cons (n := 0) t).continuous

theorem continuous_cons2 :
    Continuous (fun p : ℝ × (Fin d → ℝ) => (Fin.cons p.1 p.2 : Fin (d + 1) → ℝ)) := by
  refine continuous_pi fun i => ?_
  induction i using Fin.cases with
  | zero => simpa using continuous_fst
  | succ k =>
    simp only [Fin.cons_succ]
    exact (continuous_apply k).comp continuous_snd

/-- The spatial partial derivative of a slice. -/
theorem pd_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (Fin (d + 1) → ℝ) → E} {t : ℝ} {y : Fin d → ℝ} (j : Fin d)
    (hf : DifferentiableAt ℝ f (Fin.cons t y)) :
    pd (fun y => f (Fin.cons t y)) j y = pd f j.succ (Fin.cons t y) := by
  have hs : DifferentiableAt ℝ (fun y => f (Fin.cons t y)) (y + (0 : ℝ) • ev j) := by
    rw [zero_smul, add_zero]
    exact hf.comp y ((contDiff_cons (n := 1) t).differentiable one_ne_zero y)
  have h1 := hasDerivAt_line (f := fun y => f (Fin.cons t y)) (x := y) j hs
  have h2 := hasDerivAt_line (f := f) (x := Fin.cons t y) j.succ (s := 0)
    (by rw [zero_smul, add_zero]; exact hf)
  simp only [zero_smul, add_zero] at h1 h2
  have he : (fun s : ℝ => f (Fin.cons t (y + s • ev j))) =
      fun s : ℝ => f (Fin.cons t y + s • ev j.succ) := by
    funext s; rw [cons_space_eq]
  rw [he] at h1
  exact h1.unique h2

/-- The time derivative along a slice. -/
theorem hasDerivAt_time {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (Fin (d + 1) → ℝ) → E} {t : ℝ} (y : Fin d → ℝ)
    (hf : DifferentiableAt ℝ f (Fin.cons t y)) :
    HasDerivAt (fun s : ℝ => f (Fin.cons s y)) (pd f 0 (Fin.cons t y)) t := by
  have he : (fun s : ℝ => f (Fin.cons s y)) =
      fun s : ℝ => f (Fin.cons 0 y + s • ev 0) := by
    funext s; rw [← cons_time_eq, zero_add]
  have hx : (Fin.cons 0 y + t • ev 0 : Fin (d + 1) → ℝ) = Fin.cons t y := by
    rw [← cons_time_eq, zero_add]
  rw [he]
  have := hasDerivAt_dir (f := f) (x := Fin.cons 0 y) (v := ev 0) (s := t) (by rw [hx]; exact hf)
  rw [hx] at this
  exact this

/-- Lipschitz in space along a slice. -/
theorem lipschitzWith_slice {E : Type*} [PseudoMetricSpace E] {f : (Fin (d + 1) → ℝ) → E}
    {L : ℝ≥0} {t₀ t₁ t : ℝ} (hf : LipschitzOnWith L f (slab t₀ t₁)) (ht : t ∈ Icc t₀ t₁) :
    LipschitzWith L (fun y : Fin d → ℝ => f (Fin.cons t y)) := by
  refine LipschitzWith.of_dist_le_mul fun y y' => ?_
  refine (hf.dist_le_mul _ ((cons_mem_slab y).mpr ht) _ ((cons_mem_slab y').mpr ht)).trans ?_
  gcongr
  rw [dist_eq_norm, dist_eq_norm]
  exact norm_cons_sub_space t y y'

/-! ### Continuity of slice integrals -/

/-- `t ↦ ∫_{[0,1]^d} Φ(t, y) dy` is continuous on `[t₀, t₁]` for `Φ` continuous on the slab. -/
theorem continuousOn_sliceIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : (Fin (d + 1) → ℝ) → E} {t₀ t₁ : ℝ} (h : t₀ ≤ t₁)
    (hΦ : ContinuousOn Φ (slab t₀ t₁)) :
    ContinuousOn (fun t => ∫ y in Icc (0 : Fin d → ℝ) 1, Φ (Fin.cons t y)) (Icc t₀ t₁) := by
  set P : ℝ → ℝ := fun t => (projIcc t₀ t₁ h t : ℝ) with hP
  have hPc : Continuous P := continuous_subtype_val.comp continuous_projIcc
  have hΨ : Continuous fun p : ℝ × (Fin d → ℝ) => Φ (Fin.cons (P p.1) p.2) := by
    refine hΦ.comp_continuous (continuous_cons2.comp ((hPc.comp continuous_fst).prodMk
      continuous_snd)) fun p => ?_
    exact (cons_mem_slab _).mpr (projIcc t₀ t₁ h p.1).2
  have hcont := continuous_parametric_integral_of_continuous
    (f := fun t y => Φ (Fin.cons (P t) y)) (μ := volume) hΨ (isCompact_Icc (a := 0) (b := 1))
  refine hcont.continuousOn.congr fun t ht => ?_
  simp only [hP, projIcc_of_mem h ht]

theorem integrableOn_cube_slice {E : Type*} [NormedAddCommGroup E]
    {Φ : (Fin (d + 1) → ℝ) → E} {t₀ t₁ t : ℝ} (hΦ : ContinuousOn Φ (slab t₀ t₁))
    (ht : t ∈ Icc t₀ t₁) :
    IntegrableOn (fun y : Fin d → ℝ => Φ (Fin.cons t y)) (Icc 0 1) := by
  refine integrableOn_cube_of_continuousOn (hΦ.comp_continuous (continuous_cons t)
    fun y => (cons_mem_slab y).mpr ht).continuousOn

theorem continuous_slice {E : Type*} [TopologicalSpace E]
    {Φ : (Fin (d + 1) → ℝ) → E} {t₀ t₁ t : ℝ} (hΦ : ContinuousOn Φ (slab t₀ t₁))
    (ht : t ∈ Icc t₀ t₁) : Continuous (fun y : Fin d → ℝ => Φ (Fin.cons t y)) :=
  hΦ.comp_continuous (continuous_cons t) fun y => (cons_mem_slab y).mpr ht

/-! ### Energy, data and hypotheses -/

variable {N : Type*} [Fintype N]

/-- The energy `E(t) = ∫_{[0,1]^d} Re⟨w, A⁰ w⟩(t, y) dy`. -/
def energy (A0 : (Fin (d + 1) → ℝ) → N → N → ℂ) (w : (Fin (d + 1) → ℝ) → N → ℂ) (t : ℝ) : ℝ :=
  ∫ y in Icc (0 : Fin d → ℝ) 1,
    ip (w (Fin.cons t y)) (mv (A0 (Fin.cons t y)) (w (Fin.cons t y)))

/-- The frozen-coefficient energy `s ↦ ∫ Re⟨w(s), A⁰(t) w(s)⟩`. -/
def frozen (A0 : (Fin (d + 1) → ℝ) → N → N → ℂ) (w : (Fin (d + 1) → ℝ) → N → ℂ) (t s : ℝ) : ℝ :=
  ∫ y in Icc (0 : Fin d → ℝ) 1,
    ip (w (Fin.cons s y)) (mv (A0 (Fin.cons t y)) (w (Fin.cons s y)))

/-- `‖w(t)‖²_{L²([0,1]^d)}` (sup norm on the fibre `ℂ^N`). -/
def l2sq (w : (Fin (d + 1) → ℝ) → N → ℂ) (t : ℝ) : ℝ :=
  ∫ y in Icc (0 : Fin d → ℝ) 1, ‖w (Fin.cons t y)‖ ^ 2

/-- The principal part `P w = Σ_μ A^μ ∂_μ w`. -/
def princ (A : Fin (d + 1) → (Fin (d + 1) → ℝ) → N → N → ℂ) (w : (Fin (d + 1) → ℝ) → N → ℂ)
    (x : Fin (d + 1) → ℝ) : N → ℂ :=
  ∑ μ, mv (A μ x) (pd w μ x)

/-- **Hypotheses of a symmetric hyperbolic system with `W^{1,∞}` coefficients** on the slab
`[t₀,t₁] × 𝕋^d` (solution `C¹` on the open slab `(a,b) × ℝ^d`): Hermitian coefficients, bounded
by `C_b` and `L`-Lipschitz on the closed slab, everything spatially `ℤ^d`-periodic. -/
structure SymHyp (A : Fin (d + 1) → (Fin (d + 1) → ℝ) → N → N → ℂ)
    (w : (Fin (d + 1) → ℝ) → N → ℂ) (a t₀ t₁ b : ℝ) (L : ℝ≥0) (Cb : ℝ) : Prop where
  ha : a < t₀
  h01 : t₀ < t₁
  hb : t₁ < b
  smooth : ContDiffOn ℝ 1 w (openSlab a b)
  wper : IsSPeriodic w
  Aper : ∀ μ, IsSPeriodic (A μ)
  herm : ∀ μ x i k, A μ x k i = star (A μ x i k)
  lip : ∀ μ, LipschitzOnWith L (A μ) (slab t₀ t₁)
  bound : ∀ μ, ∀ x ∈ slab t₀ t₁, ‖A μ x‖ ≤ Cb

namespace SymHyp

variable {A : Fin (d + 1) → (Fin (d + 1) → ℝ) → N → N → ℂ} {w : (Fin (d + 1) → ℝ) → N → ℂ}
  {a t₀ t₁ b : ℝ} {L : ℝ≥0} {Cb : ℝ}

theorem sub (h : SymHyp A w a t₀ t₁ b L Cb) : slab (d := d) t₀ t₁ ⊆ openSlab a b :=
  slab_subset_openSlab h.ha h.hb

theorem diff (h : SymHyp A w a t₀ t₁ b L Cb) {x : Fin (d + 1) → ℝ} (hx : x ∈ openSlab a b) :
    DifferentiableAt ℝ w x :=
  (h.smooth.differentiableOn one_ne_zero x hx).differentiableAt ((isOpen_openSlab a b).mem_nhds hx)

theorem w_cont (h : SymHyp A w a t₀ t₁ b L Cb) : ContinuousOn w (openSlab a b) :=
  h.smooth.continuousOn

theorem pd_cont (h : SymHyp A w a t₀ t₁ b L Cb) (μ : Fin (d + 1)) :
    ContinuousOn (pd w μ) (openSlab a b) :=
  (h.smooth.continuousOn_fderiv_of_isOpen (isOpen_openSlab a b) le_rfl).clm_apply
    continuousOn_const

theorem A_cont (h : SymHyp A w a t₀ t₁ b L Cb) (μ : Fin (d + 1)) :
    ContinuousOn (A μ) (slab t₀ t₁) :=
  (h.lip μ).continuousOn

theorem slice_contDiff (h : SymHyp A w a t₀ t₁ b L Cb) {t : ℝ} (ht : t ∈ Ioo a b) :
    ContDiff ℝ 1 (fun y : Fin d → ℝ => w (Fin.cons t y)) :=
  h.smooth.comp_contDiff (contDiff_cons t) fun y => (cons_mem_openSlab y).mpr ht

theorem mem_Ioo (h : SymHyp A w a t₀ t₁ b L Cb) {t : ℝ} (ht : t ∈ Icc t₀ t₁) : t ∈ Ioo a b :=
  ⟨h.ha.trans_le ht.1, ht.2.trans_lt h.hb⟩

theorem princ_cont (h : SymHyp A w a t₀ t₁ b L Cb) : ContinuousOn (princ A w) (slab t₀ t₁) := by
  have hA := h.A_cont
  have hp : ∀ μ, ContinuousOn (pd w μ) (slab t₀ t₁) := fun μ => (h.pd_cont μ).mono h.sub
  unfold princ mv
  fun_prop

end SymHyp

theorem continuous_ip' {X : Type*} [TopologicalSpace X] {u v : X → N → ℂ} (hu : Continuous u)
    (hv : Continuous v) : Continuous (fun x => ip (u x) (v x)) := by
  unfold ip
  fun_prop

theorem continuous_mv' {X : Type*} [TopologicalSpace X] {B : X → N → N → ℂ} {u : X → N → ℂ}
    (hB : Continuous B) (hu : Continuous u) : Continuous (fun x => mv (B x) (u x)) := by
  unfold mv
  fun_prop

theorem continuousOn_ip_mv {X : Type*} [TopologicalSpace X] {s : Set X} {B : X → N → N → ℂ}
    {u v : X → N → ℂ} (hB : ContinuousOn B s) (hu : ContinuousOn u s) (hv : ContinuousOn v s) :
    ContinuousOn (fun x => ip (mv (B x) (u x)) (v x)) s := by
  unfold ip mv
  fun_prop

theorem continuousOn_ip {X : Type*} [TopologicalSpace X] {s : Set X}
    {u v : X → N → ℂ} (hu : ContinuousOn u s) (hv : ContinuousOn v s) :
    ContinuousOn (fun x => ip (u x) (v x)) s := by
  unfold ip
  fun_prop

/-- Product rule for `s ↦ Re⟨u(s), B u(s)⟩`. -/
theorem hasDerivAt_ip_mv {u : ℝ → N → ℂ} {u' : N → ℂ} {x : ℝ} (B : N → N → ℂ)
    (hu : HasDerivAt u u' x) :
    HasDerivAt (fun s => ip (u s) (mv B (u s))) (ip u' (mv B (u x)) + ip (u x) (mv B u')) x := by
  have hc : ∀ i, HasDerivAt (fun s => u s i) (u' i) x := fun i => hasDerivAt_pi.mp hu i
  have h1 : HasDerivAt (fun s => ∑ i, star (u s i) * ∑ j, B i j * u s j)
      (∑ i, (star (u' i) * ∑ j, B i j * u x j + star (u x i) * ∑ j, B i j * u' j)) x := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    have hm : HasDerivAt (fun s => ∑ j, B i j * u s j) (∑ j, B i j * u' j) x :=
      HasDerivAt.fun_sum fun j _ => (hc j).const_mul (B i j)
    exact (hc i).star.mul hm
  have h2 := h1.complex_re
  convert h2 using 1 <;> simp only [ip, mv, Finset.sum_add_distrib, Complex.add_re]

section Dini

variable {A : Fin (d + 1) → (Fin (d + 1) → ℝ) → N → N → ℂ} {w : (Fin (d + 1) → ℝ) → N → ℂ}
  {a t₀ t₁ b : ℝ} {L : ℝ≥0} {Cb : ℝ}

/-- The frozen-coefficient energy is differentiable, with derivative `2∫Re⟨A⁰(t)∂ₜw, w⟩`. -/
theorem hasDerivAt_frozen (h : SymHyp A w a t₀ t₁ b L Cb) {t : ℝ} (ht : t ∈ Icc t₀ t₁) :
    HasDerivAt (frozen (A 0) w t)
      (∫ y in Icc (0 : Fin d → ℝ) 1,
        2 * ip (mv (A 0 (Fin.cons t y)) (pd w 0 (Fin.cons t y))) (w (Fin.cons t y))) t := by
  have htab := h.mem_Ioo ht
  set δ := min (t - a) (b - t) / 2 with hδ
  have hδ0 : 0 < δ := by
    have := htab.1; have := htab.2
    rw [hδ]; positivity
  have hδa : δ < t - a := by
    have : min (t - a) (b - t) ≤ t - a := min_le_left _ _
    have := htab.1
    rw [hδ]; linarith [lt_min (sub_pos.mpr htab.1) (sub_pos.mpr htab.2)]
  have hδb : δ < b - t := by
    have : min (t - a) (b - t) ≤ b - t := min_le_right _ _
    rw [hδ]; linarith [lt_min (sub_pos.mpr htab.1) (sub_pos.mpr htab.2)]
  set K : Set (Fin (d + 1) → ℝ) := (fun p : ℝ × (Fin d → ℝ) => (Fin.cons p.1 p.2 : Fin (d + 1) → ℝ))
    '' (Icc (t - δ) (t + δ) ×ˢ Icc 0 1) with hK
  have hKc : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image continuous_cons2
  have hKsub : K ⊆ openSlab a b := by
    rintro _ ⟨p, hp, rfl⟩
    refine (cons_mem_openSlab _).mpr ⟨?_, ?_⟩ <;> [linarith [hp.1.1]; linarith [hp.1.2]]
  obtain ⟨Cw, hCw⟩ := hKc.exists_bound_of_continuousOn (h.w_cont.mono hKsub)
  obtain ⟨Cp, hCp⟩ := hKc.exists_bound_of_continuousOn ((h.pd_cont 0).mono hKsub)
  have hmemK : ∀ s ∈ Metric.ball t δ, ∀ y ∈ Icc (0 : Fin d → ℝ) 1,
      (Fin.cons s y : Fin (d + 1) → ℝ) ∈ K := by
    intro s hs y hy
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    exact ⟨(s, y), ⟨⟨by linarith, by linarith⟩, hy⟩, rfl⟩
  have hball : ∀ s ∈ Metric.ball t δ, s ∈ Ioo a b := by
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    exact ⟨by linarith, by linarith⟩
  set B : (Fin d → ℝ) → N → N → ℂ := fun y => A 0 (Fin.cons t y) with hB
  have hBc : Continuous B := continuous_slice (h.A_cont 0) ht
  have hBb : ∀ y, ‖B y‖ ≤ Cb := fun y => h.bound 0 _ ((cons_mem_slab y).mpr ht)
  have hwc : ∀ s ∈ Ioo a b, Continuous fun y : Fin d → ℝ => w (Fin.cons s y) := fun s hs =>
    h.w_cont.comp_continuous (continuous_cons s) fun y => (cons_mem_openSlab y).mpr hs
  have hpc : ∀ s ∈ Ioo a b, Continuous fun y : Fin d → ℝ => pd w 0 (Fin.cons s y) := fun s hs =>
    (h.pd_cont 0).comp_continuous (continuous_cons s)
      fun y => (cons_mem_openSlab y).mpr hs
  have hF't : Continuous fun y => ip (pd w 0 (Fin.cons t y)) (mv (B y) (w (Fin.cons t y))) +
      ip (w (Fin.cons t y)) (mv (B y) (pd w 0 (Fin.cons t y))) := by
    exact (continuous_ip' (hpc t htab) (continuous_mv' hBc (hwc t htab))).add
      (continuous_ip' (hwc t htab) (continuous_mv' hBc (hpc t htab)))
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Icc (0 : Fin d → ℝ) 1)) (x₀ := t) (s := Metric.ball t δ)
    (F := fun s y => ip (w (Fin.cons s y)) (mv (B y) (w (Fin.cons s y))))
    (F' := fun s y => ip (pd w 0 (Fin.cons s y)) (mv (B y) (w (Fin.cons s y))) +
      ip (w (Fin.cons s y)) (mv (B y) (pd w 0 (Fin.cons s y))))
    (bound := fun _ => 2 * ((Fintype.card N : ℝ) ^ 2 * Cb * (Cp * Cw)))
    (Metric.ball_mem_nhds t hδ0)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds t hδ0) fun s hs =>
      (continuous_ip' (hwc s (hball s hs)) (continuous_mv' hBc (hwc s (hball s hs)))
        ).aestronglyMeasurable)
    ((integrableOn_cube_of_continuousOn
      (continuous_ip' (hwc t htab) (continuous_mv' hBc (hwc t htab))).continuousOn).integrable)
    hF't.aestronglyMeasurable ?_ (integrable_const _) ?_
  · refine (hmain.2.congr_deriv ?_)
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [← ip_mv_herm (fun i k => h.herm 0 _ i k), ip_comm (w _)]
    ring
  · refine ae_restrict_of_forall_mem measurableSet_Icc fun y hy s hs => ?_
    have hKm := hmemK s hs y hy
    have hw := hCw _ hKm
    have hp := hCp _ hKm
    have hb := hBb y
    have hb0 : 0 ≤ Cb := (norm_nonneg _).trans hb
    have hCw0 : 0 ≤ Cw := (norm_nonneg _).trans hw
    have hCp0 : 0 ≤ Cp := (norm_nonneg _).trans hp
    have e1 := abs_ip_mv_le (B y) (pd w 0 (Fin.cons s y)) (w (Fin.cons s y))
    have e2 := abs_ip_mv_le (B y) (w (Fin.cons s y)) (pd w 0 (Fin.cons s y))
    have k1 : (Fintype.card N : ℝ) ^ 2 * ‖B y‖ * (‖pd w 0 (Fin.cons s y)‖ * ‖w (Fin.cons s y)‖)
        ≤ (Fintype.card N : ℝ) ^ 2 * Cb * (Cp * Cw) := by gcongr
    have k2 : (Fintype.card N : ℝ) ^ 2 * ‖B y‖ * (‖w (Fin.cons s y)‖ * ‖pd w 0 (Fin.cons s y)‖)
        ≤ (Fintype.card N : ℝ) ^ 2 * Cb * (Cp * Cw) := by
      calc _ ≤ (Fintype.card N : ℝ) ^ 2 * Cb * (Cw * Cp) := by gcongr
        _ = _ := by ring
    rw [Real.norm_eq_abs]
    refine (abs_add_le _ _).trans ?_
    linarith [e1.trans k1, e2.trans k2]
  · refine ae_restrict_of_forall_mem measurableSet_Icc fun y _ s hs => ?_
    exact hasDerivAt_ip_mv (B y) (hasDerivAt_time y (h.diff ((cons_mem_openSlab y).mpr
      (hball s hs))))

end Dini

end RenewalGeometry.SymHypEnergy
