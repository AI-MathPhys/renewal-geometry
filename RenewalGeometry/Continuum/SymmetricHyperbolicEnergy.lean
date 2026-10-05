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
  have h2 := hasDerivAt_re h1
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

section Dini2

variable {A : Fin (d + 1) → (Fin (d + 1) → ℝ) → N → N → ℂ} {w : (Fin (d + 1) → ℝ) → N → ℂ}
  {a t₀ t₁ b : ℝ} {L : ℝ≥0} {Cb : ℝ}

theorem SymHyp.w_slice_cont (h : SymHyp A w a t₀ t₁ b L Cb) {t : ℝ} (ht : t ∈ Icc t₀ t₁) :
    Continuous fun y : Fin d → ℝ => w (Fin.cons t y) :=
  continuous_slice (h.w_cont.mono h.sub) ht

/-- Freezing the coefficient costs at most `|N|² L (z - t) ‖w(z)‖²`. -/
theorem energy_sub_frozen_le (h : SymHyp A w a t₀ t₁ b L Cb) {t z : ℝ} (ht : t ∈ Icc t₀ t₁)
    (hz : z ∈ Icc t₀ t₁) (htz : t ≤ z) :
    energy (A 0) w z - frozen (A 0) w t z ≤
      (Fintype.card N : ℝ) ^ 2 * L * (z - t) * l2sq w z := by
  have hwz := h.w_slice_cont hz
  have hAz := continuous_slice (h.A_cont 0) hz
  have hAt := continuous_slice (h.A_cont 0) ht
  unfold energy frozen l2sq
  rw [← integral_sub (integrableOn_cube_of_continuousOn
      (continuous_ip' hwz (continuous_mv' hAz hwz)).continuousOn)
    (integrableOn_cube_of_continuousOn
      (continuous_ip' hwz (continuous_mv' hAt hwz)).continuousOn), ← integral_const_mul]
  refine integral_mono (integrableOn_cube_of_continuousOn
      ((continuous_ip' hwz (continuous_mv' hAz hwz)).sub
        (continuous_ip' hwz (continuous_mv' hAt hwz))).continuousOn)
    (integrableOn_cube_of_continuousOn
      (continuous_const.mul ((hwz.norm).pow 2)).continuousOn) fun y => ?_
  simp only
  rw [← ip_sub_right, ← mv_sub_left]
  have h1 := abs_ip_mv_le (A 0 (Fin.cons z y) - A 0 (Fin.cons t y)) (w (Fin.cons z y))
    (w (Fin.cons z y))
  have h2 : ‖A 0 (Fin.cons z y) - A 0 (Fin.cons t y)‖ ≤ L * (z - t) := by
    have := (h.lip 0).norm_sub_le ((cons_mem_slab y).mpr hz) ((cons_mem_slab y).mpr ht)
    refine this.trans ?_
    gcongr
    refine (norm_cons_sub_time z t y).trans ?_
    rw [abs_of_nonneg (sub_nonneg.mpr htz)]
  calc _ ≤ _ := (le_abs_self _).trans h1
    _ ≤ (Fintype.card N : ℝ) ^ 2 * (L * (z - t)) * (‖w (Fin.cons z y)‖ * ‖w (Fin.cons z y)‖) := by
        gcongr
    _ = _ := by ring

/-- The frozen derivative `2∫Re⟨A⁰∂ₜw, w⟩` is at most `2∫Re⟨Pw, w⟩ + d|N|²L‖w‖²`: the spatial
terms of the principal part are controlled by the Lipschitz commutator lemma. -/
theorem frozen_deriv_le (h : SymHyp A w a t₀ t₁ b L Cb) {t : ℝ} (ht : t ∈ Icc t₀ t₁) :
    ∫ y in Icc (0 : Fin d → ℝ) 1,
        2 * ip (mv (A 0 (Fin.cons t y)) (pd w 0 (Fin.cons t y))) (w (Fin.cons t y)) ≤
      2 * (∫ y in Icc (0 : Fin d → ℝ) 1, ip (princ A w (Fin.cons t y)) (w (Fin.cons t y))) +
        d * ((Fintype.card N : ℝ) ^ 2 * L * l2sq w t) := by
  have hwt := h.w_slice_cont ht
  have hAc : ∀ μ, Continuous fun y : Fin d → ℝ => A μ (Fin.cons t y) := fun μ =>
    continuous_slice (h.A_cont μ) ht
  have hpc : ∀ μ, Continuous fun y : Fin d → ℝ => pd w μ (Fin.cons t y) := fun μ =>
    continuous_slice ((h.pd_cont μ).mono h.sub) ht
  have hdiff : ∀ y : Fin d → ℝ, DifferentiableAt ℝ w (Fin.cons t y) := fun y =>
    h.diff (h.sub ((cons_mem_slab y).mpr ht))
  -- the spatial terms
  have hspace : ∀ j : Fin d, -(2 * ∫ y in Icc (0 : Fin d → ℝ) 1,
      ip (mv (A j.succ (Fin.cons t y)) (pd w j.succ (Fin.cons t y))) (w (Fin.cons t y))) ≤
      (Fintype.card N : ℝ) ^ 2 * L * l2sq w t := by
    intro j
    have hc := neg_two_integral_ip_pd_le (A := fun y => A j.succ (Fin.cons t y))
      (f := fun y => w (Fin.cons t y)) (L := L) j (h.slice_contDiff (h.mem_Ioo ht))
      (h.wper.slice t) ((h.Aper j.succ).slice t) (fun y i k => h.herm j.succ _ i k)
      (lipschitzWith_slice (h.lip j.succ) ht)
    have he : ∫ y in Icc (0 : Fin d → ℝ) 1,
        ip (mv (A j.succ (Fin.cons t y)) (pd (fun y => w (Fin.cons t y)) j y)) (w (Fin.cons t y)) =
        ∫ y in Icc (0 : Fin d → ℝ) 1,
          ip (mv (A j.succ (Fin.cons t y)) (pd w j.succ (Fin.cons t y))) (w (Fin.cons t y)) :=
      integral_congr_ae (Eventually.of_forall fun y => by
        simp only [pd_slice j (hdiff y)])
    rw [he] at hc
    exact hc
  have hint : ∀ μ : Fin (d + 1), IntegrableOn (fun y : Fin d → ℝ =>
      ip (mv (A μ (Fin.cons t y)) (pd w μ (Fin.cons t y))) (w (Fin.cons t y))) (Icc 0 1) :=
    fun μ => integrableOn_cube_of_continuousOn
      (continuous_ip' (continuous_mv' (hAc μ) (hpc μ)) hwt).continuousOn
  have hsplit : ∀ y : Fin d → ℝ, ip (princ A w (Fin.cons t y)) (w (Fin.cons t y)) =
      ip (mv (A 0 (Fin.cons t y)) (pd w 0 (Fin.cons t y))) (w (Fin.cons t y)) +
        ∑ j : Fin d, ip (mv (A j.succ (Fin.cons t y)) (pd w j.succ (Fin.cons t y)))
          (w (Fin.cons t y)) := by
    intro y
    simp only [princ, Fin.sum_univ_succ, ip_add_left]
    congr 1
    induction (Finset.univ : Finset (Fin d)) using Finset.induction_on with
    | empty => simp [ip_zero_left]
    | insert k s hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, ip_add_left, ih]
  have hP : ∫ y in Icc (0 : Fin d → ℝ) 1, ip (princ A w (Fin.cons t y)) (w (Fin.cons t y)) =
      (∫ y in Icc (0 : Fin d → ℝ) 1,
        ip (mv (A 0 (Fin.cons t y)) (pd w 0 (Fin.cons t y))) (w (Fin.cons t y))) +
      ∑ j : Fin d, ∫ y in Icc (0 : Fin d → ℝ) 1,
        ip (mv (A j.succ (Fin.cons t y)) (pd w j.succ (Fin.cons t y))) (w (Fin.cons t y)) := by
    simp only [hsplit]
    rw [integral_add (hint 0) (integrable_finsetSum _ fun (j : Fin d) _ => hint j.succ),
      integral_finset_sum _ fun (j : Fin d) _ => hint j.succ]
  rw [integral_const_mul, hP, mul_add]
  have hsum : -(2 * ∑ j : Fin d, ∫ y in Icc (0 : Fin d → ℝ) 1,
      ip (mv (A j.succ (Fin.cons t y)) (pd w j.succ (Fin.cons t y))) (w (Fin.cons t y))) ≤
      d * ((Fintype.card N : ℝ) ^ 2 * L * l2sq w t) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    calc _ ≤ ∑ _j : Fin d, (Fintype.card N : ℝ) ^ 2 * L * l2sq w t :=
          Finset.sum_le_sum fun j _ => hspace j
      _ = _ := by simp
  linarith

/-- **Right Dini bound for the energy.** -/
theorem dini_energy (h : SymHyp A w a t₀ t₁ b L Cb) {t : ℝ} (ht : t ∈ Ico t₀ t₁) {r : ℝ}
    (hr : ((d : ℝ) + 1) * ((Fintype.card N : ℝ) ^ 2 * L * l2sq w t) +
      2 * (∫ y in Icc (0 : Fin d → ℝ) 1, ip (princ A w (Fin.cons t y)) (w (Fin.cons t y))) < r) :
    ∀ᶠ z in 𝓝[>] t, slope (energy (A 0) w) t z < r := by
  have ht' : t ∈ Icc t₀ t₁ := Ico_subset_Icc_self ht
  set κL : ℝ := (Fintype.card N : ℝ) ^ 2 * L with hκL
  have hG := hasDerivAt_frozen h ht'
  have hG' := frozen_deriv_le h ht'
  set G' := ∫ y in Icc (0 : Fin d → ℝ) 1,
    2 * ip (mv (A 0 (Fin.cons t y)) (pd w 0 (Fin.cons t y))) (w (Fin.cons t y))
  -- continuity of `‖w‖²` from the right
  have hl2 : ContinuousOn (l2sq w) (Icc t₀ t₁) := by
    unfold l2sq
    exact continuousOn_sliceIntegral (Φ := fun x => ‖w x‖ ^ 2) h.h01.le
      ((h.w_cont.mono h.sub).norm.pow 2)
  have hl2r : Tendsto (l2sq w) (𝓝[>] t) (𝓝 (l2sq w t)) := by
    have := (hl2 t ht').tendsto
    refine this.mono_left ?_
    rw [← nhdsWithin_Ioo_eq_nhdsGT ht.2]
    exact nhdsWithin_mono _ fun z hz => ⟨ht.1.trans hz.1.le, hz.2.le⟩
  have hslope : Tendsto (slope (frozen (A 0) w t) t) (𝓝[>] t) (𝓝 G') :=
    (hasDerivAt_iff_tendsto_slope.mp hG).mono_left (nhdsGT_le_nhdsNE t)
  have hlim := (hl2r.const_mul κL).add hslope
  have hlt : κL * l2sq w t + G' < r := by
    have : κL * l2sq w t + G' ≤ ((d : ℝ) + 1) * (κL * l2sq w t) +
        2 * (∫ y in Icc (0 : Fin d → ℝ) 1, ip (princ A w (Fin.cons t y)) (w (Fin.cons t y))) := by
      linarith
    linarith
  have hev := hlim (Iio_mem_nhds hlt)
  filter_upwards [hev, Ioo_mem_nhdsGT ht.2] with z hz hzI
  have hz' : z ∈ Icc t₀ t₁ := ⟨ht.1.trans hzI.1.le, hzI.2.le⟩
  have hzt : 0 < z - t := sub_pos.mpr hzI.1
  have hE := energy_sub_frozen_le h ht' hz' hzI.1.le
  have hEt : energy (A 0) w t = frozen (A 0) w t t := rfl
  simp only [mem_preimage, mem_Iio] at hz
  rw [slope_def_field] at hz ⊢
  refine lt_of_le_of_lt ?_ hz
  rw [div_le_iff₀ hzt, add_mul, div_mul_cancel₀ _ hzt.ne', hEt]
  have : κL * (z - t) * l2sq w z = κL * l2sq w z * (z - t) := by ring
  linarith

end Dini2

/-! ### Gronwall: the `L²` energy estimate -/

section Gronwall

variable {A : Fin (d + 1) → (Fin (d + 1) → ℝ) → N → N → ℂ} {w : (Fin (d + 1) → ℝ) → N → ℂ}
  {a t₀ t₁ b : ℝ} {L : ℝ≥0} {Cb : ℝ}

theorem energy_continuousOn (h : SymHyp A w a t₀ t₁ b L Cb) :
    ContinuousOn (energy (A 0) w) (Icc t₀ t₁) := by
  unfold energy
  exact continuousOn_sliceIntegral (Φ := fun x => ip (w x) (mv (A 0 x) (w x))) h.h01.le
    (continuousOn_ip (h.w_cont.mono h.sub) (by
      have h1 := h.A_cont 0
      have h2 := h.w_cont.mono h.sub
      unfold mv; fun_prop))

theorem l2sq_le_energy (h : SymHyp A w a t₀ t₁ b L Cb) {c : ℝ}
    (hpos : ∀ x ∈ slab t₀ t₁, ∀ ξ : N → ℂ, c * ∑ i, ‖ξ i‖ ^ 2 ≤ ip ξ (mv (A 0 x) ξ))
    (hc : 0 ≤ c) {t : ℝ} (ht : t ∈ Icc t₀ t₁) : c * l2sq w t ≤ energy (A 0) w t := by
  have hwt := h.w_slice_cont ht
  have hAt := continuous_slice (h.A_cont 0) ht
  unfold l2sq energy
  rw [← integral_const_mul]
  refine integral_mono (integrableOn_cube_of_continuousOn
      (continuous_const.mul (hwt.norm.pow 2)).continuousOn)
    (integrableOn_cube_of_continuousOn
      (continuous_ip' hwt (continuous_mv' hAt hwt)).continuousOn) fun y => ?_
  exact (mul_le_mul_of_nonneg_left (norm_sq_le_sum _) hc).trans
    (hpos _ ((cons_mem_slab y).mpr ht) _)

theorem energy_le_l2sq (h : SymHyp A w a t₀ t₁ b L Cb) {t : ℝ} (ht : t ∈ Icc t₀ t₁) :
    energy (A 0) w t ≤ (Fintype.card N : ℝ) ^ 2 * Cb * l2sq w t := by
  have hwt := h.w_slice_cont ht
  have hAt := continuous_slice (h.A_cont 0) ht
  unfold l2sq energy
  rw [← integral_const_mul]
  refine integral_mono (integrableOn_cube_of_continuousOn
      (continuous_ip' hwt (continuous_mv' hAt hwt)).continuousOn)
    (integrableOn_cube_of_continuousOn
      (continuous_const.mul (hwt.norm.pow 2)).continuousOn) fun y => ?_
  have h1 := abs_ip_mv_le (A 0 (Fin.cons t y)) (w (Fin.cons t y)) (w (Fin.cons t y))
  have h2 := h.bound 0 _ ((cons_mem_slab y).mpr ht)
  calc _ ≤ _ := (le_abs_self _).trans h1
    _ ≤ (Fintype.card N : ℝ) ^ 2 * Cb * (‖w (Fin.cons t y)‖ * ‖w (Fin.cons t y)‖) := by gcongr
    _ = _ := by ring

/-- **The `L²` energy inequality for symmetric hyperbolic systems with `W^{1,∞}` coefficients**
on `[t₀,t₁] × 𝕋^d` (generic form of `eq:dirac-L2-stability`).  If `A⁰ ≥ c > 0` on the slab and
the principal part satisfies `‖Σ_μ A^μ∂_μw‖ ≤ m + K₀‖w‖` pointwise on the slab, `m` continuous,
`K₀ ≥ 0`, then for every `t ∈ [t₀, t₁]`
`c ‖w(t)‖²_{L²} ≤ e^{K(t₁-t₀)} (|N|² C_b ‖w(t₀)‖²_{L²} + |N| ∫_{t₀}^{t₁} ‖m(τ)‖²_{L²} dτ)`,
`K = ((d+1)|N|²L + |N|(1 + 2K₀))/c + 1`. -/
theorem l2_energy_estimate (h : SymHyp A w a t₀ t₁ b L Cb) {c K₀ : ℝ} (hc : 0 < c)
    (hK₀ : 0 ≤ K₀)
    (hpos : ∀ x ∈ slab t₀ t₁, ∀ ξ : N → ℂ, c * ∑ i, ‖ξ i‖ ^ 2 ≤ ip ξ (mv (A 0 x) ξ))
    {m : (Fin (d + 1) → ℝ) → ℝ} (hm : ContinuousOn m (slab t₀ t₁))
    (hF : ∀ x ∈ slab t₀ t₁, ‖princ A w x‖ ≤ m x + K₀ * ‖w x‖) :
    ∀ t ∈ Icc t₀ t₁, c * l2sq w t ≤
      Real.exp (((((d : ℝ) + 1) * ((Fintype.card N : ℝ) ^ 2 * L) +
          Fintype.card N * (1 + 2 * K₀)) / c + 1) * (t₁ - t₀)) *
        ((Fintype.card N : ℝ) ^ 2 * Cb * l2sq w t₀ +
          Fintype.card N * ∫ τ in t₀..t₁, ∫ y in Icc (0 : Fin d → ℝ) 1, m (Fin.cons τ y) ^ 2) := by
  set n : ℝ := (Fintype.card N : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  set K1 : ℝ := (((d : ℝ) + 1) * (n ^ 2 * L) + n * (1 + 2 * K₀)) / c with hK1
  have hK10 : 0 ≤ K1 := by rw [hK1]; positivity
  set K : ℝ := K1 + 1 with hK
  have hK0 : 0 ≤ K := by linarith
  set e := energy (A 0) w with he
  set S : ℝ → ℝ := fun τ => n * ∫ y in Icc (0 : Fin d → ℝ) 1, m (Fin.cons τ y) ^ 2 with hS
  have hSc : ContinuousOn S (Icc t₀ t₁) :=
    continuousOn_const.mul (continuousOn_sliceIntegral (Φ := fun x => m x ^ 2) h.h01.le
      (hm.pow 2))
  have h01 := h.h01.le
  set P : ℝ → ℝ := fun τ => (projIcc t₀ t₁ h01 τ : ℝ) with hP
  have hPc : Continuous P := continuous_subtype_val.comp continuous_projIcc
  set St : ℝ → ℝ := fun τ => S (P τ) with hSt
  have hStc : Continuous St :=
    hSc.comp_continuous hPc fun τ => (projIcc t₀ t₁ h01 τ).2
  have hSnn : ∀ τ, 0 ≤ S τ := fun τ => mul_nonneg hn0 (setIntegral_nonneg measurableSet_Icc
    fun y _ => sq_nonneg _)
  have hStnn : ∀ τ, 0 ≤ St τ := fun τ => hSnn _
  have hStS : ∀ τ ∈ Icc t₀ t₁, St τ = S τ := fun τ hτ => by
    simp only [hSt, hP, projIcc_of_mem h01 hτ]
  -- pointwise bound for the Dini majorant
  have hg : ∀ t ∈ Icc t₀ t₁, ((d : ℝ) + 1) * (n ^ 2 * L * l2sq w t) +
      2 * (∫ y in Icc (0 : Fin d → ℝ) 1, ip (princ A w (Fin.cons t y)) (w (Fin.cons t y))) ≤
      K1 * e t + S t := by
    intro t ht
    have hwt := h.w_slice_cont ht
    have hPt : Continuous fun y : Fin d → ℝ => princ A w (Fin.cons t y) :=
      continuous_slice h.princ_cont ht
    have hmt : Continuous fun y : Fin d → ℝ => m (Fin.cons t y) := continuous_slice hm ht
    have h2 : 2 * (∫ y in Icc (0 : Fin d → ℝ) 1, ip (princ A w (Fin.cons t y)) (w (Fin.cons t y)))
        ≤ S t + n * (1 + 2 * K₀) * l2sq w t := by
      simp only [hS, l2sq]
      have c1 : Continuous fun y => n * m (Fin.cons t y) ^ 2 := continuous_const.mul (hmt.pow 2)
      have c2 : Continuous fun y => n * (1 + 2 * K₀) * ‖w (Fin.cons t y)‖ ^ 2 :=
        continuous_const.mul (hwt.norm.pow 2)
      have c3 : Continuous fun y => 2 * ip (princ A w (Fin.cons t y)) (w (Fin.cons t y)) :=
        continuous_const.mul (continuous_ip' hPt hwt)
      rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul, ← integral_add
        (integrableOn_cube_of_continuousOn c1.continuousOn)
        (integrableOn_cube_of_continuousOn c2.continuousOn)]
      refine integral_mono (integrableOn_cube_of_continuousOn c3.continuousOn)
        (integrableOn_cube_of_continuousOn (c1.add c2).continuousOn) fun y => ?_
      simp only
      have hx := (cons_mem_slab (t₀ := t₀) (t₁ := t₁) y).mpr ht
      have e1 := abs_ip_le (princ A w (Fin.cons t y)) (w (Fin.cons t y))
      have e2 := hF _ hx
      set p := ‖princ A w (Fin.cons t y)‖
      set q := ‖w (Fin.cons t y)‖
      set mm := m (Fin.cons t y)
      have hq : 0 ≤ q := norm_nonneg _
      have e3 : p * q ≤ (mm + K₀ * q) * q := mul_le_mul_of_nonneg_right e2 hq
      have e4 : 2 * (mm * q) ≤ mm ^ 2 + q ^ 2 := by nlinarith [sq_nonneg (mm - q)]
      have e5 : ip (princ A w (Fin.cons t y)) (w (Fin.cons t y)) ≤ n * (p * q) :=
        (le_abs_self _).trans e1
      have e6 : n * (p * q) ≤ n * ((mm + K₀ * q) * q) := mul_le_mul_of_nonneg_left e3 hn0
      have e7 : n * (2 * (mm * q)) ≤ n * (mm ^ 2 + q ^ 2) := mul_le_mul_of_nonneg_left e4 hn0
      nlinarith
    have h3 : c * l2sq w t ≤ e t := l2sq_le_energy h hpos hc.le ht
    have h4 : (((d : ℝ) + 1) * (n ^ 2 * L) + n * (1 + 2 * K₀)) * l2sq w t ≤ K1 * e t := by
      rw [hK1, div_mul_eq_mul_div, le_div_iff₀ hc]
      calc _ = (((d : ℝ) + 1) * (n ^ 2 * L) + n * (1 + 2 * K₀)) * l2sq w t * c := by ring
        _ ≤ (((d : ℝ) + 1) * (n ^ 2 * L) + n * (1 + 2 * K₀)) * e t := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = _ := by ring
    nlinarith
  -- comparison with `B_ε`
  have hcomp : ∀ ε > (0 : ℝ), ∀ t ∈ Icc t₀ t₁,
      e t ≤ Real.exp (K * (t - t₀)) * (e t₀ + ε + ∫ τ in t₀..t, St τ) := by
    intro ε hε
    have he0 : 0 ≤ e t₀ := (mul_nonneg hc.le (setIntegral_nonneg measurableSet_Icc
      fun y _ => sq_nonneg _)).trans (l2sq_le_energy h hpos hc.le ⟨le_rfl, h01⟩)
    have hBd : ∀ x, HasDerivAt (fun t => Real.exp (K * (t - t₀)) *
        (e t₀ + ε + ∫ τ in t₀..t, St τ))
        (K * (Real.exp (K * (x - t₀)) * (e t₀ + ε + ∫ τ in t₀..x, St τ)) +
          Real.exp (K * (x - t₀)) * St x) x := by
      intro x
      have h1 : HasDerivAt (fun t => Real.exp (K * (t - t₀))) (Real.exp (K * (x - t₀)) * K) x := by
        have := (((hasDerivAt_id x).sub_const t₀).const_mul K).exp
        simpa using this
      have h2 : HasDerivAt (fun t => e t₀ + ε + ∫ τ in t₀..t, St τ) (St x) x :=
        ((hStc.integral_hasStrictDerivAt t₀ x).hasDerivAt).const_add _
      exact (h1.mul h2).congr_deriv (by ring)
    refine image_le_of_liminf_slope_right_lt_deriv_boundary' (energy_continuousOn h)
      (f' := fun t => ((d : ℝ) + 1) * (n ^ 2 * L * l2sq w t) +
        2 * (∫ y in Icc (0 : Fin d → ℝ) 1, ip (princ A w (Fin.cons t y)) (w (Fin.cons t y))))
      (fun x hx r hr => (dini_energy h hx hr).frequently) ?_
      (fun x _ => (hBd x).continuousAt.continuousWithinAt) (fun x _ => (hBd x).hasDerivWithinAt)
      ?_
    · simp
      linarith
    · intro x hx hex
      have hx' : x ∈ Icc t₀ t₁ := Ico_subset_Icc_self hx
      have hgx := hg x hx'
      have hexp : 1 ≤ Real.exp (K * (x - t₀)) :=
        Real.one_le_exp (mul_nonneg hK0 (sub_nonneg.mpr hx.1))
      have hint0 : 0 ≤ ∫ τ in t₀..x, St τ :=
        intervalIntegral.integral_nonneg hx.1 fun τ _ => hStnn τ
      have hBpos : 0 < Real.exp (K * (x - t₀)) * (e t₀ + ε + ∫ τ in t₀..x, St τ) :=
        mul_pos (Real.exp_pos _) (by linarith)
      rw [hStS x hx'] at *
      have hSx : S x ≤ Real.exp (K * (x - t₀)) * S x := le_mul_of_one_le_left (hSnn x) hexp
      simp only [hn] at hgx ⊢
      rw [← hex] at hBpos ⊢
      nlinarith
  intro t ht
  have hct := l2sq_le_energy h hpos hc.le ht
  have he0 := energy_le_l2sq h (t := t₀) ⟨le_rfl, h01⟩
  have hexp : Real.exp (K * (t - t₀)) ≤ Real.exp (K * (t₁ - t₀)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [ht.2]) hK0)
  have hmono : ∫ τ in t₀..t, St τ ≤ ∫ τ in t₀..t₁, St τ :=
    intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (Eventually.of_forall fun τ => hStnn τ) (hStc.intervalIntegrable _ _)
  have hint0 : 0 ≤ ∫ τ in t₀..t, St τ := intervalIntegral.integral_nonneg ht.1 fun τ _ => hStnn τ
  have hSeq : ∫ τ in t₀..t₁, St τ =
      n * ∫ τ in t₀..t₁, ∫ y in Icc (0 : Fin d → ℝ) 1, m (Fin.cons τ y) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [uIcc_of_le h01] at hτ
    exact hStS τ hτ
  rw [← hSeq]
  have hE0 : 0 < Real.exp (K * (t₁ - t₀)) := Real.exp_pos _
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have h1 := hcomp (ε / Real.exp (K * (t₁ - t₀))) (div_pos hε hE0) t ht
  have hX : 0 ≤ e t₀ + ε / Real.exp (K * (t₁ - t₀)) + ∫ τ in t₀..t, St τ := by
    have := (mul_nonneg hc.le (setIntegral_nonneg measurableSet_Icc
      fun y _ => sq_nonneg _)).trans (l2sq_le_energy h hpos hc.le ⟨le_rfl, h01⟩)
    positivity
  calc c * l2sq w t ≤ e t := hct
    _ ≤ Real.exp (K * (t - t₀)) * (e t₀ + ε / Real.exp (K * (t₁ - t₀)) + ∫ τ in t₀..t, St τ) := h1
    _ ≤ Real.exp (K * (t₁ - t₀)) *
        (n ^ 2 * Cb * l2sq w t₀ + ε / Real.exp (K * (t₁ - t₀)) + ∫ τ in t₀..t₁, St τ) := by
      gcongr
    _ = Real.exp (K * (t₁ - t₀)) * (n ^ 2 * Cb * l2sq w t₀ + ∫ τ in t₀..t₁, St τ) + ε := by
      field_simp
      ring

end Gronwall

end RenewalGeometry.SymHypEnergy
