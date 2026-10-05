/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.SymmetricHyperbolicEnergy
import RenewalGeometry.Continuum.TorusSobolevTransfer

/-!
# Uniqueness for quasilinear symmetric hyperbolic systems and Sobolev-limit identification

Generic infrastructure (no renewal notions) for `lem:generated-physical-identification` of the
Einstein–Standard-Model action-closure manuscript (`app:generated-dynamics`).

* `QLSymSys`: a quasilinear first-order system `U_t + Σ_j A^j(U) ∂_j U = F(U)` for `ℂ^N`-valued
  fields on `ℝ × 𝕋^d` (`ℤ^d`-periodic in space), with Hermitian `A^j(·)` (the symmetric
  structure); `QLSymSys.Solves`: classical (`C¹`) periodic solutions on an open slab.
* **`QLSymSys.unique`** (uniqueness for symmetric hyperbolic systems): two classical solutions with
  the same Cauchy data at `t₀` coincide on `[t₀, t₁] × 𝕋^d`, provided the coefficients are Lipschitz
  and bounded on a set containing both solutions, `F` is Lipschitz there, one solution is
  Lipschitz on the slab and the other has bounded spatial derivatives.  Proof: the difference
  solves a linear symmetric hyperbolic system with `W^{1,∞}` coefficients `A^j(U)` and a zero-order
  forcing `F(U) - F(V) - (A^j(U) - A^j(V)) ∂_j V`, so the `L²` energy inequality
  (`SymHypEnergy.l2_energy_estimate`) with zero data forces `‖U(t) - V(t)‖_{L²} = 0`.
* `eq_zero_on_cube_of_integral_eq_zero`: a continuous field with zero `L²` norm on the unit cube
  vanishes on the cube.
* **`identify_of_sobolev_limit`** (Sobolev-limit identification): pointwise algebraic identities
  `Φ(F₁, …, F_m) = 0` (fields, first derivatives and equation residuals as components) satisfied
  by a sequence of continuous fields on `𝕋³` pass to any `H^s` limit, `s ≥ 2`.
* `AnalyticGermExistence`: the Cauchy–Kovalevskaya input of the lemma (local analytic physical
  solutions for the analytic constraint-compatible core), stated as a proposition — the named
  gap; `germ_eq_symmetric` identifies a physical germ solving the symmetric system with the
  symmetric solution of the same data (uniqueness).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace RenewalGeometry.SymHypUniqueness

open SymHypEnergy PeriodicCube
open SobolevOpen (pd)

set_option linter.unusedSectionVars false

variable {d : ℕ} {N : Type*} [Fintype N] [DecidableEq N]

/-! ### A continuous field with zero `L²` norm on the cube vanishes there -/

theorem eq_zero_on_cube_of_integral_eq_zero {g : (Fin d → ℝ) → N → ℂ} (hg : Continuous g)
    (h : ∫ y in Icc (0 : Fin d → ℝ) 1, ‖g y‖ ^ 2 = 0) : ∀ y ∈ Icc (0 : Fin d → ℝ) 1, g y = 0 := by
  have hint : IntegrableOn (fun y => ‖g y‖ ^ 2) (Icc (0 : Fin d → ℝ) 1) :=
    integrableOn_cube_of_continuousOn (hg.norm.pow 2).continuousOn
  have hae : (fun y => ‖g y‖ ^ 2) =ᵐ[volume.restrict (Icc (0 : Fin d → ℝ) 1)] 0 :=
    (setIntegral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun y => sq_nonneg _) hint).mp h
  set S : Set (Fin d → ℝ) := Set.pi univ fun _ => Ioo (0 : ℝ) 1 with hS
  have hSsub : S ⊆ Icc (0 : Fin d → ℝ) 1 := by
    intro y hy
    rw [← Set.pi_univ_Icc]
    exact fun i _ => Ioo_subset_Icc_self (hy i (mem_univ i))
  have hSopen : IsOpen S := isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo
  have hae' : (fun y => ‖g y‖ ^ 2) =ᵐ[volume.restrict S] 0 := ae_restrict_of_ae_restrict_of_subset
    hSsub hae
  have heq : EqOn (fun y => ‖g y‖ ^ 2) 0 S :=
    Measure.eqOn_open_of_ae_eq hae' hSopen (hg.norm.pow 2).continuousOn continuousOn_const
  have hz : EqOn g 0 S := fun y hy => by
    have := heq hy
    simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
      norm_eq_zero] at this
    exact this
  have hcl : EqOn g 0 (closure S) := hz.closure hg continuous_const
  have hclS : closure S = Icc (0 : Fin d → ℝ) 1 := by
    rw [hS, closure_pi_set, ← Set.pi_univ_Icc]
    congr 1; funext i
    exact closure_Ioo zero_ne_one
  intro y hy
  rw [← hclS] at hy
  exact hcl hy

/-! ### Quasilinear symmetric hyperbolic systems -/

/-- A quasilinear first-order system `U_t + Σ_j A^j(U) ∂_j U = F(U)` for `ℂ^N`-valued fields on
`ℝ^{1+d}` (time coordinate `0`). -/
structure QLSymSys (d : ℕ) (N : Type*) where
  /-- the coefficient matrices `A^j(U)` -/
  A : Fin d → (N → ℂ) → N → N → ℂ
  /-- the lower-order term `F(U)` -/
  F : (N → ℂ) → N → ℂ

namespace QLSymSys

variable (S : QLSymSys d N)

/-- `U` is a classical (`C¹`), spatially periodic solution on the open slab `(a, b) × ℝ^d`. -/
structure Solves (U : (Fin (d + 1) → ℝ) → N → ℂ) (a b : ℝ) : Prop where
  smooth : ContDiffOn ℝ 1 U (openSlab a b)
  per : IsSPeriodic U
  eqn : ∀ x ∈ openSlab a b,
    pd U 0 x + ∑ j : Fin d, mv (S.A j (U x)) (pd U j.succ x) = S.F (U x)

/-- The identity matrix. -/
def idM : N → N → ℂ := fun i k => if i = k then 1 else 0

theorem mv_idM (v : N → ℂ) : mv (idM : N → N → ℂ) v = v := by
  funext i; simp [mv, idM]

theorem norm_idM_le : ‖(idM : N → N → ℂ)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun k => ?_
  by_cases h : i = k <;> simp [idM, h]

/-- The coefficients of the linear system satisfied by `U - V`: `A⁰ = 1`, `A^{j+1} = A^j(U)`. -/
def diffCoeff (U : (Fin (d + 1) → ℝ) → N → ℂ) : Fin (d + 1) → (Fin (d + 1) → ℝ) → N → N → ℂ :=
  Fin.cons (fun _ => idM) fun j x => S.A j (U x)

theorem pd_sub {U V : (Fin (d + 1) → ℝ) → N → ℂ} {x : Fin (d + 1) → ℝ} (hU : DifferentiableAt ℝ U x)
    (hV : DifferentiableAt ℝ V x) (μ : Fin (d + 1)) : pd (U - V) μ x = pd U μ x - pd V μ x := by
  unfold pd
  rw [fderiv_sub hU hV]
  rfl

/-- **Uniqueness for quasilinear symmetric hyperbolic systems** (the uniqueness step of
`lem:generated-physical-identification`): let `U, V` be classical periodic solutions on
`(a, b) × ℝ^d ⊃ [t₀, t₁] × ℝ^d` taking values in a set `Ω` on the slab, on which `A^j` is Hermitian,
`L_A`-Lipschitz and bounded and `F` is `L_F`-Lipschitz; let `U` be Lipschitz on the slab and
`‖∂_j V‖ ≤ M_V` there.  If `U(t₀) = V(t₀)` then `U = V` on `[t₀, t₁] × ℝ^d`. -/
theorem unique {U V : (Fin (d + 1) → ℝ) → N → ℂ} {a t₀ t₁ b : ℝ} (ha : a < t₀) (h01 : t₀ < t₁)
    (hb : t₁ < b) (hU : S.Solves U a b) (hV : S.Solves V a b) {Ω : Set (N → ℂ)}
    (hUΩ : ∀ x ∈ slab t₀ t₁, U x ∈ Ω) (hVΩ : ∀ x ∈ slab t₀ t₁, V x ∈ Ω)
    (hherm : ∀ j v i k, S.A j v k i = star (S.A j v i k))
    {LA LF LU : ℝ≥0} {CA MV : ℝ} (hAlip : ∀ j, LipschitzOnWith LA (S.A j) Ω)
    (hAbd : ∀ j, ∀ v ∈ Ω, ‖S.A j v‖ ≤ CA) (hFlip : LipschitzOnWith LF S.F Ω)
    (hUlip : LipschitzOnWith LU U (slab t₀ t₁)) (hMV : 0 ≤ MV)
    (hVd : ∀ j : Fin d, ∀ x ∈ slab t₀ t₁, ‖pd V j.succ x‖ ≤ MV)
    (h0 : ∀ y : Fin d → ℝ, U (Fin.cons t₀ y) = V (Fin.cons t₀ y)) :
    ∀ x ∈ slab t₀ t₁, U x = V x := by
  set w := U - V with hw
  set A := S.diffCoeff U with hA
  have hdiffU : ∀ x ∈ openSlab a b, DifferentiableAt ℝ U x := fun x hx =>
    (hU.smooth.differentiableOn one_ne_zero x hx).differentiableAt
      ((isOpen_openSlab a b).mem_nhds hx)
  have hdiffV : ∀ x ∈ openSlab a b, DifferentiableAt ℝ V x := fun x hx =>
    (hV.smooth.differentiableOn one_ne_zero x hx).differentiableAt
      ((isOpen_openSlab a b).mem_nhds hx)
  have hsub : slab (d := d) t₀ t₁ ⊆ openSlab a b := slab_subset_openSlab ha hb
  -- the linear symmetric hyperbolic system for `w`
  have hsym : SymHyp A w a t₀ t₁ b (LA * LU) (max 1 CA) := by
    refine ⟨ha, h01, hb, hU.smooth.sub hV.smooth, fun k x => ?_, fun μ => ?_, fun μ x i k => ?_,
      fun μ => ?_, fun μ x hx => ?_⟩
    · show U (x + sshift k) - V (x + sshift k) = U x - V x
      rw [hU.per k x, hV.per k x]
    · refine Fin.cases ?_ (fun j => ?_) μ
      · intro k x; rfl
      · intro k x
        show S.A j (U (x + sshift k)) = S.A j (U x)
        rw [hU.per k x]
    · refine Fin.cases ?_ (fun j => ?_) μ
      · show idM k i = star (idM i k)
        by_cases h : i = k
        · subst h; simp [idM]
        · simp [idM, h, Ne.symm h]
      · exact hherm j (U x) i k
    · refine Fin.cases ?_ (fun j => ?_) μ
      · exact (LipschitzWith.const _).lipschitzOnWith.weaken bot_le
      · exact (hAlip j).comp hUlip (fun x hx => hUΩ x hx)
    · refine Fin.cases ?_ (fun j => ?_) μ
      · exact norm_idM_le.trans (le_max_left _ _)
      · exact (hAbd j _ (hUΩ x hx)).trans (le_max_right _ _)
  -- the principal part is a zero-order term
  set K₀ : ℝ := LF + d * (Fintype.card N * (LA * MV)) with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  have hprinc : ∀ x ∈ slab t₀ t₁, ‖princ A w x‖ ≤ (fun _ => (0 : ℝ)) x + K₀ * ‖w x‖ := by
    intro x hx
    have hxo := hsub hx
    have hpdw : ∀ μ, pd w μ x = pd U μ x - pd V μ x := fun μ =>
      pd_sub (hdiffU x hxo) (hdiffV x hxo) μ
    have e : princ A w x = (S.F (U x) - S.F (V x)) -
        ∑ j : Fin d, mv (S.A j (U x) - S.A j (V x)) (pd V j.succ x) := by
      have hUe := hU.eqn x hxo
      have hVe := hV.eqn x hxo
      unfold princ
      rw [Fin.sum_univ_succ]
      simp only [hA, diffCoeff, Fin.cons_zero, Fin.cons_succ, mv_idM, hpdw, mv_sub, mv_sub_left]
      rw [← hUe, ← hVe, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      abel
    rw [e]
    simp only [zero_add]
    have hwx : ‖w x‖ = ‖U x - V x‖ := rfl
    have hF := hFlip.norm_sub_le (hUΩ x hx) (hVΩ x hx)
    have hsum : ‖∑ j : Fin d, mv (S.A j (U x) - S.A j (V x)) (pd V j.succ x)‖ ≤
        d * (Fintype.card N * (LA * MV)) * ‖U x - V x‖ := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ j : Fin d, ‖mv (S.A j (U x) - S.A j (V x)) (pd V j.succ x)‖
          ≤ ∑ _j : Fin d, Fintype.card N * (LA * MV) * ‖U x - V x‖ :=
            Finset.sum_le_sum fun j _ => by
              refine (norm_mv_le _ _).trans ?_
              have h1 := (hAlip j).norm_sub_le (hUΩ x hx) (hVΩ x hx)
              have h2 := hVd j x hx
              have : ‖S.A j (U x) - S.A j (V x)‖ * ‖pd V j.succ x‖ ≤
                  (LA * ‖U x - V x‖) * MV :=
                mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
              calc (Fintype.card N : ℝ) * (‖S.A j (U x) - S.A j (V x)‖ * ‖pd V j.succ x‖)
                  ≤ Fintype.card N * ((LA * ‖U x - V x‖) * MV) :=
                    mul_le_mul_of_nonneg_left this (by positivity)
                _ = _ := by ring
        _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    rw [hwx]
    calc ‖S.F (U x) - S.F (V x) - ∑ j : Fin d, mv (S.A j (U x) - S.A j (V x)) (pd V j.succ x)‖
        ≤ ‖S.F (U x) - S.F (V x)‖ +
            ‖∑ j : Fin d, mv (S.A j (U x) - S.A j (V x)) (pd V j.succ x)‖ := norm_sub_le _ _
      _ ≤ LF * ‖U x - V x‖ + d * (Fintype.card N * (LA * MV)) * ‖U x - V x‖ :=
          add_le_add hF hsum
      _ = K₀ * ‖U x - V x‖ := by rw [hK₀]; ring
  have hpos : ∀ x ∈ slab t₀ t₁, ∀ ξ : N → ℂ, 1 * ∑ i, ‖ξ i‖ ^ 2 ≤ ip ξ (mv (A 0 x) ξ) := by
    intro x _ ξ
    simp only [hA, diffCoeff, Fin.cons_zero, mv_idM, one_mul, ip_self_eq, le_refl]
  have hest := l2_energy_estimate hsym one_pos hK₀0 hpos continuousOn_const hprinc
  -- zero data
  have hl0 : l2sq w t₀ = 0 := by
    unfold l2sq
    have : ∀ y : Fin d → ℝ, ‖w (Fin.cons t₀ y)‖ ^ 2 = 0 := fun y => by
      simp [hw, h0 y]
    simp [this]
  intro x hx
  have ht : x 0 ∈ Icc t₀ t₁ := hx
  have hb' := hest (x 0) ht
  rw [hl0] at hb'
  simp only [mul_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    MeasureTheory.integral_zero, intervalIntegral.integral_zero, one_mul] at hb'
  have hnn : 0 ≤ l2sq w (x 0) := setIntegral_nonneg measurableSet_Icc fun y _ => sq_nonneg _
  have hzero : l2sq w (x 0) = 0 := le_antisymm hb' hnn
  -- the slice vanishes on the cube, hence everywhere by periodicity
  have hcont : Continuous fun y : Fin d → ℝ => w (Fin.cons (x 0) y) :=
    hsym.w_slice_cont ht
  have hcube := eq_zero_on_cube_of_integral_eq_zero hcont hzero
  have hper : IsZPeriodic fun y : Fin d → ℝ => w (Fin.cons (x 0) y) :=
    hsym.wper.slice (x 0)
  have hfr : (fun i => Int.fract (Fin.tail x i)) ∈ Icc (0 : Fin d → ℝ) 1 :=
    ⟨fun i => Int.fract_nonneg _, fun i => (Int.fract_lt_one _).le⟩
  have := hcube _ hfr
  rw [hper.apply_fract (Fin.tail x), Fin.cons_self_tail] at this
  exact sub_eq_zero.mp this

end QLSymSys

/-! ### Sobolev-limit identification -/

open TorusSobolevTransfer PeriodicGridSobolev PeriodicGridSobolev.Composition
  PeriodicGridSobolev.Sampling

/-- **Sobolev-limit identification** (`lem:generated-physical-identification`, last step): if
continuous fields `F_k = (F_{k,1}, …, F_{k,m})` on `𝕋³` (fields, first derivatives, residual
components, …) converge in `H^s`, `s ≥ 2`, to continuous fields `F`, and satisfy pointwise
identities `Φ(F_k(x)) = 0` with `Φ` continuous, then `Φ(F(x)) = 0` everywhere. -/
theorem identify_of_sobolev_limit {ι : Type*} [Fintype ι] {s : ℕ} (hs : 2 ≤ s)
    {Fk : ℕ → ι → CT} {F : ι → CT} (hmem : ∀ k i, MemH s ⇑(Fk k i - F i))
    (hconv : ∀ i, Tendsto (fun k => sn s ⇑(Fk k i - F i)) atTop (𝓝 0))
    {Φ : (ι → ℂ) → ℂ} (hΦ : Continuous Φ)
    (hid : ∀ k x, Φ (fun i => Fk k i x) = 0) : ∀ x, Φ (fun i => F i x) = 0 := by
  intro x
  -- pointwise convergence from the embedding `H^s ⊂ C⁰`
  have hpt : ∀ i, Tendsto (fun k => Fk k i x) atTop (𝓝 (F i x)) := by
    intro i
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : ∀ k, ‖Fk k i x - F i x‖ ≤ Real.sqrt cEmb * sn s ⇑(Fk k i - F i) := fun k =>
      norm_apply_le_sn s hs (Fk k i - F i) (hmem k i) x
    have hlim : Tendsto (fun k => Real.sqrt cEmb * sn s ⇑(Fk k i - F i)) atTop (𝓝 0) := by
      simpa using (hconv i).const_mul (Real.sqrt cEmb)
    exact squeeze_zero (fun k => norm_nonneg _) hb hlim
  have hvec : Tendsto (fun k => fun i => Fk k i x) atTop (𝓝 fun i => F i x) :=
    tendsto_pi_nhds.mpr hpt
  have := (hΦ.tendsto _).comp hvec
  have h0 : Tendsto (fun k => Φ (fun i => Fk k i x)) atTop (𝓝 0) := by
    simp only [hid]; exact tendsto_const_nhds
  exact tendsto_nhds_unique this h0

/-! ### The Cauchy–Kovalevskaya input (named gap) -/

/-- **The analytic-germ input of `lem:generated-physical-identification`** (the named gap,
`ass:constrained-initial-solver`, last sentences): for every initial tuple `U₀` of the
constraint-compatible analytic core (`Core U₀`), the constrained physical Cauchy problem has a
local analytic solution whose actual first-jet state `Uphys` is *physical* (`Physical Uphys`: it
satisfies the Einstein–Standard-Model equations and the harmonic/temporal-gauge constraints) and
solves the symmetric system `S` on a slab `(t₀ - ε, t₀ + ε) × 𝕋^d` with data `U₀` (the latter by
`prop:actual-jet-writer`).  This is the Cauchy–Kovalevskaya step, not proved here. -/
def AnalyticGermExistence (S : QLSymSys d N) (t₀ : ℝ) (Core : ((Fin d → ℝ) → N → ℂ) → Prop)
    (Physical : ((Fin (d + 1) → ℝ) → N → ℂ) → Prop) : Prop :=
  ∀ U₀, Core U₀ → ∃ ε > 0, ∃ Uphys : (Fin (d + 1) → ℝ) → N → ℂ, Physical Uphys ∧
    S.Solves Uphys (t₀ - ε) (t₀ + ε) ∧ ∀ y, Uphys (Fin.cons t₀ y) = U₀ y

/-- **Identification of a physical germ with the symmetric solution**: a physical germ solving the
symmetric system with the same data as a symmetric solution `U` coincides with `U` on every common
slab (`QLSymSys.unique`), hence `U` is physical there. -/
theorem germ_eq_symmetric (S : QLSymSys d N) {U Uphys : (Fin (d + 1) → ℝ) → N → ℂ}
    {a t₀ t₁ b : ℝ} (ha : a < t₀) (h01 : t₀ < t₁) (hb : t₁ < b) (hU : S.Solves U a b)
    (hP : S.Solves Uphys a b) {Ω : Set (N → ℂ)}
    (hUΩ : ∀ x ∈ slab t₀ t₁, U x ∈ Ω) (hPΩ : ∀ x ∈ slab t₀ t₁, Uphys x ∈ Ω)
    (hherm : ∀ j v i k, S.A j v k i = star (S.A j v i k))
    {LA LF LU : ℝ≥0} {CA MV : ℝ} (hAlip : ∀ j, LipschitzOnWith LA (S.A j) Ω)
    (hAbd : ∀ j, ∀ v ∈ Ω, ‖S.A j v‖ ≤ CA) (hFlip : LipschitzOnWith LF S.F Ω)
    (hUlip : LipschitzOnWith LU U (slab t₀ t₁)) (hMV : 0 ≤ MV)
    (hPd : ∀ j : Fin d, ∀ x ∈ slab t₀ t₁, ‖pd Uphys j.succ x‖ ≤ MV)
    (h0 : ∀ y : Fin d → ℝ, U (Fin.cons t₀ y) = Uphys (Fin.cons t₀ y)) :
    ∀ x ∈ slab t₀ t₁, U x = Uphys x :=
  S.unique ha h01 hb hU hP hUΩ hPΩ hherm hAlip hAbd hFlip hUlip hMV hPd h0

/-- Non-vacuity of the uniqueness hypotheses: the zero system (`A = 0`, `F = 0`) and the zero
solution. -/
theorem zero_solves (a b : ℝ) :
    (⟨fun _ _ => 0, fun _ => 0⟩ : QLSymSys d N).Solves (fun _ => 0) a b := by
  refine ⟨contDiffOn_const, fun _ _ => rfl, fun x _ => ?_⟩
  simp [pd, mv_zero]

/-- Non-vacuity of the hypothesis packet of `QLSymSys.unique`: it is satisfiable (zero system,
zero solutions, `Ω = univ`). -/
example (a t₀ t₁ b : ℝ) (ha : a < t₀) (h01 : t₀ < t₁) (hb : t₁ < b) :
    ∀ x ∈ slab (d := d) t₀ t₁, (fun _ => (0 : N → ℂ)) x = (fun _ => (0 : N → ℂ)) x :=
  (⟨fun _ _ => 0, fun _ => 0⟩ : QLSymSys d N).unique (U := fun _ => 0) (V := fun _ => 0)
    ha h01 hb (zero_solves a b) (zero_solves a b) (Ω := univ) (fun _ _ => mem_univ _)
    (fun _ _ => mem_univ _) (fun _ _ _ _ => by simp) (LA := 0) (LF := 0) (LU := 0) (CA := 0)
    (MV := 0) (fun _ => (LipschitzWith.const _).lipschitzOnWith) (fun _ _ _ => by simp)
    (LipschitzWith.const _).lipschitzOnWith (LipschitzWith.const _).lipschitzOnWith le_rfl
    (fun _ _ _ => by simp [pd]) (fun _ => rfl)

end RenewalGeometry.SymHypUniqueness
