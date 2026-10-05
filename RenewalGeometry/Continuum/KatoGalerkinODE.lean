/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.KatoHartleyBasis
import RenewalGeometry.Continuum.SpectralGalerkinMidpoint

/-!
# The spectral Galerkin system of a quasilinear symmetric hyperbolic system on `𝕋^d`

Generic infrastructure (no renewal notions) for `thm:generated-dynamics`
(`eq:generated-Galerkin`, `eq:generated-midpoint`, `eq:generated-uniform`) of the
Einstein–Standard-Model action-closure manuscript.  The system is
`∂_tU + Σ_i A^i(U)∂_iU = F(U)` for `U = (u_b)_{b < n}` on `𝕋^d` (`ℤ^d`-periodic fields on `ℝ^d`,
the slab calculus of `SlabSobolevAlgebra`), with smooth real symmetric `A^i(v)` and smooth `F(v)`;
`G(U) = F(U) - Σ_i A^i(U)∂_iU` is `QLEnergy.genG`.

* `box N = {k ∈ ℤ^d : |k_i| ≤ N}` (the cutoff `N`), `GS d n N` the **Galerkin space**: the
  `ℝ^n`-valued trigonometric polynomials `Σ_{k ∈ box N} c_{b,k} cas_k` in the coordinates
  `a_{b,k} = √(wq q k) c_{b,k}`, so that the Euclidean norm of `a` is the classical `H^q` norm of
  the field (`energyQ_fld`).
* `GN`: the **projected generator** `P_N G` (Fourier truncation: `a ↦ (√wq · ⟨G(U), cas_k⟩)`);
  the projection disappears from the energy pairing: `inner_GN_self`
  (`⟪G_N a, a⟫ = ⟨U, G(U)⟩_{H^q}`), hence the cutoff-independent energy inequality
  `inner_GN_le` from `QLEnergy.pairQ_genG_le`; `contDiff_GN` (`G_N` is `C¹`; parametric
  integrals, `contDiff_one_integral_cube`).
* **`galerkin_uniform`** (`eq:generated-Galerkin` + uniform bound): for data `U₀` with
  `‖U₀‖_{H^q} ≤ R₀` there is `T > 0`, depending only on `R₀` (and `A, F, q, m, d, n`), such that
  for **every** cutoff `N` the Galerkin ODE `ȧ = G_N(a)`, `a(0) = P_N U₀`, has a solution on
  `[0, T]` with `‖a(t)‖ = ‖U_N(t)‖_{H^q} ≤ R` (`R = 2R₀ + 1`).
* **`midpoint_uniform`** (`eq:generated-midpoint`, `eq:generated-uniform`): for every cutoff the
  implicit midpoint recursion exists on the same `[0, T]` for all sufficiently small steps, with
  the cutoff-independent bound `‖U^j‖_{H^q} ≤ R`.

Disclosed rendering: `Σ = 𝕋^d` (the manuscript's `𝕋³` for `d = 3`); the coefficients are smooth
on all of `ℝ^n` (a chart is handled by a smooth cutoff extension); the step restriction in
`midpoint_uniform` is the abstract `τ ≤ τ_N` (Lipschitz constant of `G_N` on the ball), not the
explicit CFL form `τ(N + 1) ≤ c_*` of `eq:generated-CFL`, which needs the inverse inequality
`‖G_N(V) - G_N(W)‖_{H^q} ≤ C_R (N + 1) ‖V - W‖_{H^q}` (not formalised).
-/

open MeasureTheory Filter Topology Set Finset
open scoped BigOperators ContDiff Real RealInnerProductSpace

noncomputable section

namespace RenewalGeometry.KatoGalerkin

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy

set_option linter.unusedSectionVars false

variable {d n : ℕ}

/-! ### Parametric integrals over the cube -/

/-- A parametric integral over the unit cube of a jointly `C¹` integrand is `C¹` in the
(finite-dimensional) parameter. -/
theorem contDiff_one_integral_cube {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Φ : E × (Fin d → ℝ) → ℝ} (hΦ : ContDiff ℝ 1 Φ) :
    ContDiff ℝ 1 (fun a => ∫ y in Icc (0 : Fin d → ℝ) 1, Φ (a, y)) := by
  set Φ' : E → (Fin d → ℝ) → E →L[ℝ] ℝ := fun a y =>
    (fderiv ℝ Φ (a, y)).comp (ContinuousLinearMap.inl ℝ E (Fin d → ℝ)) with hΦ'
  have hcont : Continuous fun p : E × (Fin d → ℝ) => Φ' p.1 p.2 :=
    (hΦ.continuous_fderiv one_ne_zero).clm_comp continuous_const
  have hderiv : ∀ a y, HasFDerivAt (fun a => Φ (a, y)) (Φ' a y) a := fun a y =>
    ((hΦ.differentiable one_ne_zero (a, y)).hasFDerivAt).comp a (hasFDerivAt_prodMk_left a y)
  rw [contDiff_one_iff_hasFDerivAt]
  refine ⟨fun a => ∫ y in Icc (0 : Fin d → ℝ) 1, Φ' a y,
    continuous_parametric_integral_of_continuous (f := Φ') hcont isCompact_Icc, fun a₀ => ?_⟩
  obtain ⟨C, hC⟩ := ((isCompact_closedBall a₀ 1).prod (isCompact_Icc (a := (0 : Fin d → ℝ))
    (b := 1))).exists_bound_of_continuousOn hcont.continuousOn
  have hcΦ : Continuous Φ := hΦ.continuous
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C)
    (Metric.ball_mem_nhds a₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun a =>
      (hcΦ.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
  · exact integrableOn_cube_of_continuousOn
      (hcΦ.comp (Continuous.prodMk continuous_const continuous_id)).continuousOn
  · exact (hcont.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun y hy a ha => ?_)
    exact hC (a, y) ⟨Metric.ball_subset_closedBall ha, hy⟩
  · exact integrable_const C
  · exact Eventually.of_forall fun y a _ => hderiv a y

/-! ### The frequency box and the Galerkin space -/

/-- The frequency box `{k : |k_i| ≤ N}`. -/
def box (N : ℕ) : Finset (Fin d → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) N

theorem mem_box {N : ℕ} {k : Fin d → ℤ} : k ∈ box N ↔ ∀ i, |k i| ≤ N := by
  simp [box, abs_le]

theorem box_mono {N M : ℕ} (h : N ≤ M) : box (d := d) N ⊆ box M := fun k hk => by
  rw [mem_box] at hk ⊢
  exact fun i => (hk i).trans (by exact_mod_cast h)

/-- The Galerkin space of cutoff `N`: coefficient vectors `a_{b,k}`, `k ∈ box N`. -/
abbrev GS (d n N : ℕ) := EuclideanSpace ℝ (Fin n × (box (d := d) N))

/-- The `cas` coefficients `c_{b,k} = a_{b,k}/√(wq q k)` of the Galerkin state `a`. -/
def cf (q : ℕ) {N : ℕ} (a : GS d n N) (b : Fin n) (k : Fin d → ℤ) : ℝ :=
  if hk : k ∈ box N then a (b, ⟨k, hk⟩) / Real.sqrt (wq q k) else 0

/-- The trigonometric field of a Galerkin state. -/
def fld (q : ℕ) {N : ℕ} (a : GS d n N) (b : Fin n) : ST d → ℝ := tfs (box N) (cf q a b)

theorem contDiff_fld (q : ℕ) {N : ℕ} (a : GS d n N) (b : Fin n) : ContDiff ℝ ∞ (fld q a b) :=
  contDiff_tfs _ _

theorem isSPeriodic_fld (q : ℕ) {N : ℕ} (a : GS d n N) (b : Fin n) :
    IsSPeriodic (fld q a b) :=
  isSPeriodic_tfs _ _

theorem sqrt_wq_ne (q : ℕ) (k : Fin d → ℤ) : Real.sqrt (wq q k) ≠ 0 :=
  (Real.sqrt_pos.2 (wq_pos q k)).ne'

theorem wq_mul_cf_sq (q : ℕ) {N : ℕ} (a : GS d n N) (b : Fin n) (k : box (d := d) N) :
    wq q k.1 * cf q a b k.1 ^ 2 = a (b, k) ^ 2 := by
  rw [cf, dif_pos k.2, div_pow, Real.sq_sqrt (wq_nonneg q k.1)]
  field_simp [(wq_pos q k.1).ne']

/-- **The Euclidean norm of a Galerkin state is the `H^q` norm of its field.** -/
theorem energyQ_fld (q : ℕ) {N : ℕ} (a : GS d n N) (t : ℝ) :
    energyQ q (fld q a) t = ‖a‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type, energyQ]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [fld, Q_tfs, ← Finset.sum_coe_sort (box N)]
  exact Finset.sum_congr rfl fun k _ => wq_mul_cf_sq q a b k

/-! ### The projected generator -/

variable (A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ) (F : Fin n → (Fin n → ℝ) → ℝ)

/-- **The projected generator** `G_N = P_N G` in Galerkin coordinates:
`G_N(a)_{b,k} = √(wq q k) ⟨G(U)_b, cas_k⟩_{L²}` (Fourier truncation of `G(U)`, `U` the field
of `a`). -/
def GN (q : ℕ) {N : ℕ} (a : GS d n N) : GS d n N :=
  WithLp.toLp 2 fun p => Real.sqrt (wq q p.2.1) * coef (genG A F (fld q a) p.1) 0 p.2.1

theorem GN_apply (q : ℕ) {N : ℕ} (a : GS d n N) (p : Fin n × box (d := d) N) :
    GN A F q a p = Real.sqrt (wq q p.2.1) * coef (genG A F (fld q a) p.1) 0 p.2.1 := rfl

variable {A F}

theorem isSPeriodic_genG {u : Fin n → ST d → ℝ} (hu : ∀ b, IsSPeriodic (u b)) (a : Fin n) :
    IsSPeriodic (genG A F u a) := fun k x => by
  simp only [genG, compF, hu _ k x, isSPeriodic_pd (hu _) _ k x]

/-- **The projection disappears from the energy pairing**:
`⟪G_N a, a⟫ = ⟨U, G(U)⟩_{H^q}` (`U` the field of `a`). -/
theorem inner_GN_self (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a))
    (q : ℕ) {N : ℕ} (a : GS d n N) :
    ⟪GN A F q a, a⟫ = pairQ q (fld q a) (genG A F (fld q a)) 0 := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, pairQ]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h := pairWords_tfs q (box N) (cf q a b)
    (contDiff_genG hA hF (fun b => contDiff_fld q a b) b)
    (isSPeriodic_genG (fun b => isSPeriodic_fld q a b) b) 0
  have e : ∑ L ∈ wordsLE d q, ∫ y in Icc (0 : Fin d → ℝ) 1,
      sd L (fld q a b) (Fin.cons 0 y) * sd L (genG A F (fld q a) b) (Fin.cons 0 y) =
      ∑ L ∈ wordsLE d q, sint (fun x => sd L (tfs (box N) (cf q a b)) x *
        sd L (genG A F (fld q a) b) x) 0 := rfl
  rw [e, h, ← Finset.sum_coe_sort (box N)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [GN_apply, cf, dif_pos k.2, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial,
    RCLike.re_to_real]
  have hw := Real.mul_self_sqrt (wq_nonneg q k.1)
  have hs := sqrt_wq_ne q k.1
  generalize √(wq q k.1) = s at hw hs ⊢
  rw [← hw]
  field_simp

/-- **The cutoff-independent energy inequality of the Galerkin system** (from
`QLEnergy.pairQ_genG_le`): for `m > d/2`, `q ≥ 2m` and every radius `R` there is `K` with
`⟪G_N a, a⟫ ≤ K (1 + ‖a‖²)` for all cutoffs `N` and all `‖a‖ ≤ R`. -/
theorem inner_GN_le {m q : ℕ} (hm : (d : ℝ) / 2 < m) (hq : 2 * m ≤ q)
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hsym : ∀ i a b v, A i a b v = A i b a v)
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R : ℝ} (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (a : GS d n N), ‖a‖ ≤ R →
      ⟪GN A F q a, a⟫ ≤ K * (1 + ‖a‖ ^ 2) := by
  obtain ⟨K, hK0, hK⟩ := pairQ_genG_le (d := d) hm hq hA hsym hF hR
  refine ⟨K, hK0, fun N a ha => ?_⟩
  have h := hK (fld q a) (fun b => contDiff_fld q a b) (fun b => isSPeriodic_fld q a b) 0
    (by rw [energyQ_fld]; exact pow_le_pow_left₀ (norm_nonneg _) ha 2)
  rw [energyQ_fld] at h
  rwa [inner_GN_self hA hF]

/-! ### Smoothness of the projected generator -/

/-- The field of a Galerkin state as an explicit finite sum. -/
theorem fld_eq (q : ℕ) {N : ℕ} (a : GS d n N) (b : Fin n) (x : ST d) :
    fld q a b x = ∑ k : box (d := d) N, a (b, k) / Real.sqrt (wq q k.1) * casS k.1 x := by
  rw [fld, tfs, ← Finset.sum_coe_sort (box N)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cf, dif_pos k.2]

/-- The spatial derivatives of the field of a Galerkin state. -/
theorem pd_fld_eq (q : ℕ) {N : ℕ} (a : GS d n N) (b : Fin n) (i : Fin d) (x : ST d) :
    pd (fld q a b) i.succ x = ∑ k : box (d := d) N,
      a (b, k) / Real.sqrt (wq q k.1) * (2 * π * (k.1 i : ℝ) * casS (-k.1) x) := by
  have h := congrFun (sd_tfs [i] (box N) (cf q a b)) x
  simp only [sd_cons, sd_nil] at h
  rw [fld, h, ← Finset.sum_coe_sort (box N)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cf, dif_pos k.2, pd_casS_succ]

theorem contDiff_coord_fst {N : ℕ} (p : Fin n × box (d := d) N) :
    ContDiff ℝ ∞ (fun z : GS d n N × (Fin d → ℝ) => z.1 p) :=
  (EuclideanSpace.proj (𝕜 := ℝ) p).contDiff.comp contDiff_fst

theorem contDiff_casS_snd (k : Fin d → ℤ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] :
    ContDiff ℝ ∞ (fun z : E × (Fin d → ℝ) => casS k (Fin.cons 0 z.2 : ST d)) :=
  (contDiff_casS k).comp ((contDiff_cons 0).comp contDiff_snd)

/-- **The projected generator is `C¹`** (in fact its coordinates are parametric integrals of
jointly smooth integrands). -/
theorem contDiff_GN (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a))
    (q N : ℕ) : ContDiff ℝ 1 (GN (d := d) (n := n) A F q (N := N)) := by
  refine contDiff_piLp' 2 fun p => ?_
  set fv : GS d n N × (Fin d → ℝ) → Fin n → ℝ := fun z b' =>
    ∑ k : box (d := d) N, z.1 (b', k) / Real.sqrt (wq q k.1) * casS k.1 (Fin.cons 0 z.2 : ST d)
    with hfv
  set fd : GS d n N × (Fin d → ℝ) → Fin n → Fin d → ℝ := fun z b' i =>
    ∑ k : box (d := d) N, z.1 (b', k) / Real.sqrt (wq q k.1) *
      (2 * π * (k.1 i : ℝ) * casS (-k.1) (Fin.cons 0 z.2 : ST d)) with hfd
  set Φ : GS d n N × (Fin d → ℝ) → ℝ := fun z =>
    casS p.2.1 (Fin.cons 0 z.2 : ST d) * (F p.1 (fv z) -
      ∑ i, ∑ b', A i p.1 b' (fv z) * fd z b' i) with hΦ
  have hfvs : ContDiff ℝ ∞ fv := by
    refine contDiff_pi.2 fun b' => ContDiff.sum fun k _ => ?_
    exact ((contDiff_coord_fst (b', k)).div_const _).mul (contDiff_casS_snd k.1)
  have hfds : ∀ b' i, ContDiff ℝ ∞ fun z => fd z b' i := fun b' i =>
    ContDiff.sum fun k _ => ((contDiff_coord_fst (b', k)).div_const _).mul
      (contDiff_const.mul (contDiff_casS_snd (-k.1)))
  have hΦs : ContDiff ℝ ∞ Φ :=
    (contDiff_casS_snd p.2.1).mul (((hF p.1).comp hfvs).sub (ContDiff.sum fun i _ =>
      ContDiff.sum fun b' _ => ((hA i p.1 b').comp hfvs).mul (hfds b' i)))
  have e : (fun a : GS d n N => GN A F q a p) =
      fun a => Real.sqrt (wq q p.2.1) * ∫ y in Icc (0 : Fin d → ℝ) 1, Φ (a, y) := by
    funext a
    rw [GN_apply, coef, sint]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hΦ, genG, compF]
    have h1 : (fun b => fld q a b (Fin.cons 0 y : ST d)) = fv (a, y) := by
      funext b'; rw [fld_eq]
    have h2 : ∀ i b', pd (fld q a b') i.succ (Fin.cons 0 y : ST d) = fd (a, y) b' i :=
      fun i b' => pd_fld_eq q a b' i _
    simp only [h1, h2]
  rw [e]
  exact contDiff_const.mul (contDiff_one_integral_cube (hΦs.of_le (by exact_mod_cast le_top)))

/-! ### Galerkin initial data -/

/-- The Galerkin initial datum `P_N U₀` (Fourier truncation of `U₀` at time `0`). -/
def P0 (q N : ℕ) (U₀ : Fin n → ST d → ℝ) : GS d n N :=
  WithLp.toLp 2 fun p => Real.sqrt (wq q p.2.1) * coef (U₀ p.1) 0 p.2.1

theorem cf_P0 (q N : ℕ) (U₀ : Fin n → ST d → ℝ) (b : Fin n) (k : Fin d → ℤ) :
    cf q (P0 (d := d) q N U₀) b k = if k ∈ box N then coef (U₀ b) 0 k else 0 := by
  unfold cf
  split_ifs with hk
  · show Real.sqrt (wq q k) * coef (U₀ b) 0 k / Real.sqrt (wq q k) = _
    field_simp [sqrt_wq_ne q k]
  · rfl

/-- **The truncated data are bounded by the data**: `‖P_N U₀‖ ≤ ‖U₀‖_{H^q}` (Bessel in `H^q`). -/
theorem norm_P0_sq_le (q N : ℕ) {U₀ : Fin n → ST d → ℝ} (hU : ∀ b, ContDiff ℝ ∞ (U₀ b))
    (hUp : ∀ b, IsSPeriodic (U₀ b)) : ‖P0 (d := d) q N U₀‖ ^ 2 ≤ energyQ q U₀ 0 := by
  rw [← energyQ_fld q (P0 q N U₀) 0, energyQ, energyQ]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [fld, Q_tfs]
  have h := bessel_Hq q (box N) (hU b) (hUp b) 0
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun k hk => ?_)) h
  rw [cf_P0, if_pos hk]

/-! ### The cutoff-uniform Galerkin evolution -/

/-- **Existence of the spectral Galerkin evolution on a cutoff-independent interval with a
cutoff-independent `H^q` bound** (`eq:generated-Galerkin`, first-exit argument): for
`m > d/2`, `q ≥ 2m`, symmetric smooth `A^i` and smooth `F`, and every data radius `R₀`, there is
`T > 0` such that for **every** cutoff `N` and every smooth periodic datum `U₀` with
`‖U₀‖²_{H^q} ≤ R₀²`, the Galerkin ODE `ȧ = G_N(a)`, `a(0) = P_N U₀`, has a solution on `[0, T]`
with `‖U_N(t)‖_{H^q} = ‖a(t)‖ ≤ 2R₀ + 1`. -/
theorem galerkin_uniform {m q : ℕ} (hm : (d : ℝ) / 2 < m) (hq : 2 * m ≤ q)
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hsym : ∀ i a b v, A i a b v = A i b a v)
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ T > 0, ∃ K ≥ 0, ∀ (N : ℕ) (U₀ : Fin n → ST d → ℝ), (∀ b, ContDiff ℝ ∞ (U₀ b)) →
      (∀ b, IsSPeriodic (U₀ b)) → energyQ q U₀ 0 ≤ R₀ ^ 2 →
      ∃ γ : ℝ → GS d n N, γ 0 = P0 q N U₀ ∧ ∀ t ∈ Set.Icc 0 T,
        HasDerivWithinAt γ (GN A F q (γ t)) (Set.Icc 0 T) t ∧ ‖γ t‖ ≤ 2 * R₀ + 1 ∧
        1 + ‖γ t‖ ^ 2 ≤ Real.exp (2 * K * t) * (1 + ‖P0 (d := d) q N U₀‖ ^ 2) := by
  set R := 2 * R₀ + 1 with hR
  have hRpos : 0 < R := by linarith
  obtain ⟨K, hK0, hK⟩ := inner_GN_le (d := d) (n := n) hm hq hA hsym hF (R := 2 * R)
    (by linarith)
  have hratio : 1 < (1 + R ^ 2) / (1 + R₀ ^ 2) := by
    rw [one_lt_div (by positivity)]; nlinarith
  set T := Real.log ((1 + R ^ 2) / (1 + R₀ ^ 2)) / (2 * K + 1) with hT
  have hTpos : 0 < T := div_pos (Real.log_pos hratio) (by linarith)
  refine ⟨T, hTpos, K, hK0, fun N U₀ hU hUp hE => ?_⟩
  have hP0 : ‖P0 (d := d) q N U₀‖ ^ 2 ≤ R₀ ^ 2 := (norm_P0_sq_le q N hU hUp).trans hE
  have h0 : Real.exp (2 * K * T) * (1 + ‖P0 (d := d) q N U₀‖ ^ 2) ≤ 1 + R ^ 2 := by
    have h1 : Real.exp (2 * K * T) ≤ (1 + R ^ 2) / (1 + R₀ ^ 2) := by
      calc Real.exp (2 * K * T) ≤ Real.exp ((2 * K + 1) * T) :=
            Real.exp_le_exp.2 (by nlinarith)
        _ = (1 + R ^ 2) / (1 + R₀ ^ 2) := by
            rw [hT, mul_div_cancel₀ _ (by linarith : (2 * K + 1) ≠ 0),
              Real.exp_log (by positivity)]
    calc Real.exp (2 * K * T) * (1 + ‖P0 (d := d) q N U₀‖ ^ 2)
        ≤ (1 + R ^ 2) / (1 + R₀ ^ 2) * (1 + R₀ ^ 2) :=
          mul_le_mul h1 (by linarith) (by positivity) (by positivity)
      _ = 1 + R ^ 2 := div_mul_cancel₀ _ (by positivity)
  obtain ⟨γ, hγ0, hγ⟩ := SpectralGalerkin.galerkin_exists (contDiff_GN hA hF q N) hRpos
    hTpos.le (fun w hw => hK N w hw.le) h0 hK0
  exact ⟨γ, hγ0, fun t ht => hγ t ht⟩

/-! ### The fully finite midpoint recursion -/

theorem exists_bound_lip_GN (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b))
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) (q N : ℕ) (ρ : ℝ) :
    ∃ M L : ℝ, 0 ≤ M ∧ 0 ≤ L ∧ (∀ w : GS d n N, ‖w‖ ≤ ρ → ‖GN A F q w‖ ≤ M) ∧
      ∀ w w' : GS d n N, ‖w‖ ≤ ρ → ‖w'‖ ≤ ρ →
        ‖GN A F q w - GN A F q w'‖ ≤ L * ‖w - w'‖ := by
  have hG := contDiff_GN (d := d) (n := n) hA hF q N
  have hK : IsCompact (Metric.closedBall (0 : GS d n N) ρ) := isCompact_closedBall _ _
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hG.continuous.continuousOn
  obtain ⟨L, hL⟩ := hK.exists_bound_of_continuousOn (hG.continuous_fderiv one_ne_zero).continuousOn
  refine ⟨max M 0, max L 0, le_max_right _ _, le_max_right _ _, fun w hw => ?_,
    fun w w' hw hw' => ?_⟩
  · exact (hM w (by simpa using hw)).trans (le_max_left _ _)
  · have := (convex_closedBall (0 : GS d n N) ρ).norm_image_sub_le_of_norm_fderiv_le
      (f := GN A F q) (C := max L 0) (fun x _ => hG.differentiable one_ne_zero x)
      (fun x hx => (hL x hx).trans (le_max_left _ _)) (y := w) (x := w')
      (by simpa using hw') (by simpa using hw)
    exact this

/-- **The fully finite midpoint recursion with a cutoff-independent `H^q` bound**
(`eq:generated-midpoint`, `eq:generated-uniform`): there are `T > 0`, `R` (depending only on the
data radius `R₀`) such that for every cutoff `N` there is a step bound `τ_N > 0` with: for every
`0 < τ ≤ τ_N` and every datum `‖U₀‖²_{H^q} ≤ R₀²`, the implicit midpoint recursion
`U^{j+1} = U^j + τ G_N((U^j + U^{j+1})/2)`, `U⁰ = P_N U₀`, exists (uniquely in the step ball) for
all `jτ ≤ T`, with `‖U^j‖_{H^q} ≤ R`. -/
theorem midpoint_uniform {m q : ℕ} (hm : (d : ℝ) / 2 < m) (hq : 2 * m ≤ q)
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hsym : ∀ i a b v, A i a b v = A i b a v)
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ T > 0, ∃ R ≥ 0, ∀ N : ℕ, ∃ τN > 0, ∀ τ, 0 < τ → τ ≤ τN →
      ∀ U₀ : Fin n → ST d → ℝ, (∀ b, ContDiff ℝ ∞ (U₀ b)) → (∀ b, IsSPeriodic (U₀ b)) →
      energyQ q U₀ 0 ≤ R₀ ^ 2 →
      ∃ U : ℕ → GS d n N, U 0 = P0 q N U₀ ∧ ∀ j : ℕ, (j : ℝ) * τ ≤ T →
        ‖U j‖ ≤ R ∧ (((j : ℝ) + 1) * τ ≤ T →
          U (j + 1) = U j + τ • GN A F q (SpectralGalerkin.mid (U j) (U (j + 1)))) := by
  set R := 2 * R₀ + 1 with hR
  have hRpos : 0 < R := by linarith
  obtain ⟨K, hK0, hK⟩ := inner_GN_le (d := d) (n := n) hm hq hA hsym hF (R := 2 * R)
    (by linarith)
  have hratio : 1 < (1 + R ^ 2) / (1 + R₀ ^ 2) := by
    rw [one_lt_div (by positivity)]; nlinarith
  set T := Real.log ((1 + R ^ 2) / (1 + R₀ ^ 2)) / (4 * K + 1) with hT
  have hTpos : 0 < T := div_pos (Real.log_pos hratio) (by linarith)
  refine ⟨T, hTpos, R, hRpos.le, fun N => ?_⟩
  obtain ⟨M, L, hM0, hL0, hMb, hLb⟩ := exists_bound_lip_GN (d := d) (n := n) hA hF q N (2 * R)
  set τN := min (R / (M + 1)) (min (1 / (L + 1)) (1 / (2 * K + 1))) with hτN
  have hτNpos : 0 < τN := lt_min (div_pos hRpos (by linarith))
    (lt_min (div_pos one_pos (by linarith)) (div_pos one_pos (by linarith)))
  refine ⟨τN, hτNpos, fun τ hτ hττ U₀ hU hUp hE => ?_⟩
  have hτ1 : τ ≤ R / (M + 1) := hττ.trans (min_le_left _ _)
  have hτ2 : τ ≤ 1 / (L + 1) := hττ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hτ3 : τ ≤ 1 / (2 * K + 1) := hττ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hτM : τ * M ≤ R := by
    rw [le_div_iff₀ (by linarith)] at hτ1; nlinarith
  have hcfl : τ * L < 2 := by
    rw [le_div_iff₀ (by linarith)] at hτ2; nlinarith
  have hτK : τ * K ≤ 1 / 2 := by
    rw [le_div_iff₀ (by linarith)] at hτ3; nlinarith
  have hP0 : ‖P0 (d := d) q N U₀‖ ^ 2 ≤ R₀ ^ 2 := (norm_P0_sq_le q N hU hUp).trans hE
  have h0 : Real.exp (4 * K * T) * (1 + ‖P0 (d := d) q N U₀‖ ^ 2) ≤ 1 + R ^ 2 := by
    have h1 : Real.exp (4 * K * T) ≤ (1 + R ^ 2) / (1 + R₀ ^ 2) := by
      calc Real.exp (4 * K * T) ≤ Real.exp ((4 * K + 1) * T) :=
            Real.exp_le_exp.2 (by nlinarith)
        _ = (1 + R ^ 2) / (1 + R₀ ^ 2) := by
            rw [hT, mul_div_cancel₀ _ (by linarith : (4 * K + 1) ≠ 0),
              Real.exp_log (by positivity)]
    calc Real.exp (4 * K * T) * (1 + ‖P0 (d := d) q N U₀‖ ^ 2)
        ≤ (1 + R ^ 2) / (1 + R₀ ^ 2) * (1 + R₀ ^ 2) :=
          mul_le_mul h1 (by linarith) (by positivity) (by positivity)
      _ = 1 + R ^ 2 := div_mul_cancel₀ _ (by positivity)
  obtain ⟨U, hU0, hUj⟩ := SpectralGalerkin.midpoint_recursion hτ.le hM0 hL0 hK0 hRpos.le
    hMb hLb (fun w hw => hK N w hw) hτM hcfl hτK h0
  exact ⟨U, hU0, fun j hj => ⟨(hUj j hj).1, fun hj1 => ((hUj j hj).2.2 hj1).1⟩⟩

end RenewalGeometry.KatoGalerkin
