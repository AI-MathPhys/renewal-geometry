/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.DeterminantHodgeStrongConvergence
import RenewalGeometry.Continuum.NativeCriticalGridCompactness
import RenewalGeometry.GaugeTheory.DeterminantScreenFluxClosure

/-!
# Precompactness of the zero-flux Abelian coordinates of a screened sequence
  (`prop:periodic-determinant-normalization`, sequence clauses; Einstein–SM action closure)

The exact part of `prop:periodic-determinant-normalization` (the potential `a⁰ = δ_h Δ_h^† f`,
the cycle constants `c` with `L c_μ ∈ (-π, π]`, the site gauge, `δ_h(a⁰ + c) = 0`) is
`DeterminantFlux.periodic_determinant_normalization_exact`, and for screened sequences
`DeterminantScreenFlux.native_determinant_split`.  This file proves the sequence clauses: for a
screened bounded-curvature sequence (`DeterminantScreenFlux.CurvatureScreen`) with zero
determinant flux, the coordinates `a_h = a⁰_h + c_h` (for any constants with `|L c_μ| ≤ π`, in
particular those of the exact normalization) are strongly precompact in raw `L⁴`, their first
differences are strongly precompact in `L²`, their trigonometric reconstructions are strongly
precompact in `H¹`, and `h ‖a_h‖_{∞,h} → 0`.

Rendering.  The paper's box has side `L`, mesh `h = L/n`; reconstructions are taken on the unit
torus `𝕋⁴` (dilation by `L`), with the unit-torus coordinates `a'_h = L a_h` (so that
`a'_h = δ_{1/n} Δ_{1/n}^† (L² f_h) + L c_h`, `scaledPrimitive_unit`) and forward differences
`Dp = L · D⁺_h`; all these rescalings are by fixed constants.  Precompactness is stated
sequentially: every subsequence has a further subsequence converging in the stated topologies.

The proof is the paper's: `lem:determinant-screen-flux` (`determinant_screen_flux`, proved) gives
`L²` precompactness of `R_h^0 f_h`; the strong-convergence clause of
`lem:determinant-Hodge-stability` (`HodgeStrongConvergence.hodge_strong_convergence`, proved)
and `lem:native-reconstruction-identification` (`TorusTrigReconstruction.
native_reconstruction_identification`, proved) give the convergence of the potentials; the
bounded constants are extracted; `eq:native-link-coeff` (`NativeCriticalGrid.tendsto_meshSup`)
gives `h ‖a‖_∞ → 0` along every such subsequence, hence for the whole sequence.
-/

open MeasureTheory Set Finset Filter Topology UnitAddTorus
open scoped BigOperators Real ENNReal

namespace RenewalGeometry.DeterminantNormalizationSequence

open TorusTrigReconstruction HodgeStrongConvergence NativeCriticalGrid DeterminantScreenFlux
  DeterminantFlux GridHodge TorusPiecewiseConstantTranslation TorusSobolev DeterminantSplit
  SMDescentYukawa

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)

/-! ### Linear algebra of the primitive -/

section Linear

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ} [NeZero N]

theorem hodgePrimitive_smul (c : ℝ) (f : (ι → ZMod N) → ι → ι → ℝ) (x : ι → ZMod N) (ν : ι) :
    hodgePrimitive (fun x μ ν => c * f x μ ν) x ν = c * hodgePrimitive f x ν := by
  unfold hodgePrimitive
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  have e : comp (fun x μ ν => c * f x μ ν) κ ν = c • comp f κ ν := by
    funext x; simp [comp]
  rw [e, map_smul, bwd_smul]
  rfl

end Linear

/-! ### The screened sequence in unit-torus coordinates -/

variable {L : ℝ} {n : ℕ → ℕ} [∀ k, NeZero (n k)]
  {U : ∀ k, (Fin 4 → ZMod (n k)) → Fin 4 → SMGaugeGroup}
  {Lg : ∀ k, (Fin 4 → ZMod (n k)) → Fin 4 → Fin 4 → LiePair}

/-- The `U(1)` determinant links `u = χ(U)`. -/
def detLinks (U : ∀ k, (Fin 4 → ZMod (n k)) → Fin 4 → SMGaugeGroup) (k : ℕ) :
    (Fin 4 → ZMod (n k)) → Fin 4 → ℂ := fun x μ => smChi (U k x μ)

/-- The determinant curvature in unit-torus normalization, `L² f_h` (`f_h = h⁻² φ_h`). -/
def unitCurv (L : ℝ) (U : ∀ k, (Fin 4 → ZMod (n k)) → Fin 4 → SMGaugeGroup) (k : ℕ) :
    LatticeTorusPlancherel.Grid 4 (n k) → Fin 4 → Fin 4 → ℝ :=
  fun x μ ν => L ^ 2 * detCurvature (detLinks U k) (L / n k) x μ ν

/-- `δ_{1/n} Δ_{1/n}^† (L² f) = L · δ_h Δ_h^† f`. -/
theorem scaledPrimitive_unit (hL : 0 < L) (k : ℕ) (ν : Fin 4) (x : Fin 4 → ZMod (n k)) :
    scaledPrimitive ((n k : ℝ)⁻¹) (unitCurv L U k) ν x =
      L * detPotential (detLinks U k) (L / n k) x ν := by
  have hN : (0 : ℝ) < n k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (n k))
  simp only [scaledPrimitive, detPotential]
  rw [show unitCurv L U k = fun x μ ν => L ^ 2 * detCurvature (detLinks U k) (L / n k) x μ ν
    from rfl, hodgePrimitive_smul]
  field_simp

/-- The unit-torus coordinates `a'_h = L (a⁰_h + c_h)` (complexified). -/
def unitCoord (L : ℝ) (U : ∀ k, (Fin 4 → ZMod (n k)) → Fin 4 → SMGaugeGroup) (cst : ℕ → Fin 4 → ℝ)
    (k : ℕ) (ν : Fin 4) : LatticeTorusPlancherel.Grid 4 (n k) → ℂ :=
  fun x => ((L * (detPotential (detLinks U k) (L / n k) x ν + cst k ν) : ℝ) : ℂ)

theorem unitCoord_eq (hL : 0 < L) (cst : ℕ → Fin 4 → ℝ) (k : ℕ) (ν : Fin 4) :
    unitCoord L U cst k ν = primC (unitCurv L U) k ν + fun _ => ((L * cst k ν : ℝ) : ℂ) := by
  funext x
  simp only [unitCoord, primC, realC, Pi.add_apply, scaledPrimitive_unit hL]
  push_cast
  ring

/-! ### Components of the vector-valued curvature limit -/

/-- The complexified `p`-component of a packet. -/
def projC (p : PairIdx) : (PairIdx → ℝ) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.proj p)

theorem norm_projC_apply_le (p : PairIdx) (v : PairIdx → ℝ) : ‖projC p v‖ ≤ ‖v‖ := by
  simp only [projC, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply, Complex.norm_real]
  exact norm_le_pi_norm v p

theorem coeFn_pcLp' {E : Type*} [NormedAddCommGroup E] {M : ℕ} [NeZero M]
    (v : LatticeTorusPlancherel.Grid 4 M → E) :
    ((pcLp v : Lp E 2 (volume : Measure (UnitAddTorus (Fin 4)))) : UnitAddTorus (Fin 4) → E)
      =ᵐ[volume] pc v :=
  (memLp_pc v).coeFn_toLp

theorem tendsto_component {N : ℕ → ℕ} [∀ k, NeZero (N k)]
    {w : ∀ k, LatticeTorusPlancherel.Grid 4 (N k) → PairIdx → ℝ}
    {G : Lp (PairIdx → ℝ) 2 (volume : Measure (UnitAddTorus (Fin 4)))}
    (hw : Tendsto (fun k => ‖pcLp (w k) - G‖) atTop (𝓝 0)) (p : PairIdx) :
    Tendsto (fun k => ‖pcLp (fun x => projC p (w k x)) - (projC p).compLp G‖) atTop (𝓝 0) := by
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hw
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [Lp.coeFn_sub (pcLp (fun x => projC p (w k x))) ((projC p).compLp G),
    Lp.coeFn_sub (pcLp (w k)) G, coeFn_pcLp' (fun x => projC p (w k x)), coeFn_pcLp' (w k),
    (projC p).coeFn_compLp G] with y h1 h2 h3 h4 h5
  rw [h1, h2, Pi.sub_apply, Pi.sub_apply, h3, h4, h5]
  show ‖projC p (pc (w k) y) - projC p (G y)‖ ≤ _
  rw [← map_sub]
  exact norm_projC_apply_le p _

/-! ### Constants -/

/-- The constant function `c` as an element of `L²(𝕋⁴)`. -/
def constL (c : ℂ) : L²(UnitAddTorus (Fin 4)) := (memLp_const c).toLp _

theorem pcLp_const {M : ℕ} [NeZero M] (c : ℂ) :
    pcLp (fun _ : LatticeTorusPlancherel.Grid 4 M => c) = constL c := by
  apply Lp.ext
  filter_upwards [coeFn_pcLp' (fun _ : LatticeTorusPlancherel.Grid 4 M => c),
    (memLp_const (μ := (volume : Measure (UnitAddTorus (Fin 4)))) (p := 2) c).coeFn_toLp] with y h1 h2
  rw [h1]
  exact h2.symm

theorem norm_constL_sub_le (a b : ℂ) : ‖constL a - constL b‖ ≤ ‖a - b‖ := by
  have hae : ∀ᵐ y ∂(volume : Measure (UnitAddTorus (Fin 4))), ‖(constL a - constL b) y‖ ≤ ‖a - b‖ := by
    filter_upwards [Lp.coeFn_sub (constL a) (constL b),
      (memLp_const (μ := (volume : Measure (UnitAddTorus (Fin 4)))) (p := 2) a).coeFn_toLp,
      (memLp_const (μ := (volume : Measure (UnitAddTorus (Fin 4)))) (p := 2) b).coeFn_toLp]
      with y h1 h2 h3
    rw [h1, Pi.sub_apply]
    simp only [constL] at h2 h3 ⊢
    rw [h2, h3]
  refine (Lp.norm_le_of_ae_bound (norm_nonneg _) hae).trans (le_of_eq ?_)
  simp [measureUnivNNReal]

theorem Dp_add_const {M : ℕ} [NeZero M] (μ : Fin 4) (v : LatticeTorusPlancherel.Grid 4 M → ℂ)
    (c : ℂ) : Dp μ (v + fun _ => c) = Dp μ v := by
  funext x; simp only [Dp_apply, Pi.add_apply]; ring

/-! ### The curvature components -/

/-- The limit two-form built from a packet limit `G` (antisymmetric extension, scaled by `L²`). -/
def curvLimit (L : ℝ) (G : Lp (PairIdx → ℝ) 2 (volume : Measure (UnitAddTorus (Fin 4))))
    (μ ν : Fin 4) : L²(UnitAddTorus (Fin 4)) :=
  if h : μ < ν then ((L ^ 2 : ℝ) : ℂ) • (projC ⟨(μ, ν), h⟩).compLp G
  else if h' : ν < μ then (-(L ^ 2 : ℝ) : ℂ) • (projC ⟨(ν, μ), h'⟩).compLp G else 0

theorem pcLp_smul {M : ℕ} [NeZero M] (c : ℂ) (v : LatticeTorusPlancherel.Grid 4 M → ℂ) :
    pcLp (c • v) = c • pcLp v :=
  (memLp_pc v).toLp_const_smul c

theorem detCurvature_eq_detPacket {N : ℕ} (h : ℝ) (V : (Fin 4 → ZMod N) → Fin 4 → SMGaugeGroup)
    (x : Fin 4 → ZMod N) (p : PairIdx) :
    detCurvature (fun x μ => smChi (V x μ)) h x p.1.1 p.1.2 = detPacket h V x p := by
  simp only [detCurvature, detPacket, abPhase_eq_arg]

theorem tendsto_curv_components (hL : 0 < L) {m : ℕ → ℕ}
    {G : Lp (PairIdx → ℝ) 2 (volume : Measure (UnitAddTorus (Fin 4)))}
    (hw : Tendsto (fun k => ‖pcLp (detPacket (L / n (m k)) (U (m k))) - G‖) atTop (𝓝 0))
    (hsmall : ∀ᶠ k in atTop, ∀ x μ ν, |abPhase (detLinks U (m k)) x μ ν| < Real.pi / 3)
    (μ ν : Fin 4) :
    Tendsto (fun k => ‖pcLp (realC (comp (unitCurv L U (m k)) μ ν)) - curvLimit L G μ ν‖)
      atTop (𝓝 0) := by
  have hu : ∀ k x μ, detLinks U (m k) x μ ≠ 0 := fun k x μ => smChi_ne_zero _
  rcases lt_trichotomy μ ν with h | rfl | h
  · have e : ∀ k, realC (comp (unitCurv L U (m k)) μ ν) =
        ((L ^ 2 : ℝ) : ℂ) • fun x => projC ⟨(μ, ν), h⟩ (detPacket (L / n (m k)) (U (m k)) x) := by
      intro k; funext x
      simp only [realC, comp, unitCurv, Pi.smul_apply, smul_eq_mul, projC,
        ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.proj_apply,
        Complex.ofRealCLM_apply]
      rw [← detCurvature_eq_detPacket (L / n (m k)) (U (m k)) x ⟨(μ, ν), h⟩]
      push_cast; rfl
    have h1 := tendsto_component hw ⟨(μ, ν), h⟩
    simp only [e, curvLimit, dif_pos h, pcLp_smul, ← smul_sub, norm_smul]
    have h2 := h1.const_mul ‖((L ^ 2 : ℝ) : ℂ)‖
    rwa [mul_zero] at h2
  · have e : ∀ k, realC (comp (unitCurv L U (m k)) μ μ) = 0 := by
      intro k; funext x
      simp [realC, comp, unitCurv, detCurvature, abPhase_self _ (hu k)]
    simp only [e, curvLimit, lt_irrefl, dif_neg, not_false_eq_true]
    have : ∀ k, pcLp (0 : LatticeTorusPlancherel.Grid 4 (n (m k)) → ℂ) = 0 := by
      intro k; rw [← norm_eq_zero, norm_pcLp, gridNorm_zero]
    simp [this]
  · have h1 := tendsto_component hw ⟨(ν, μ), h⟩
    have hnot : ¬ μ < ν := not_lt.2 h.le
    have hlim : Tendsto (fun k => ‖(-(L ^ 2 : ℝ) : ℂ) • pcLp (fun x => projC ⟨(ν, μ), h⟩
        (detPacket (L / n (m k)) (U (m k)) x)) - curvLimit L G μ ν‖) atTop (𝓝 0) := by
      simp only [curvLimit, dif_neg hnot, dif_pos h, ← smul_sub, norm_smul]
      have h2 := h1.const_mul ‖((-(L ^ 2 : ℝ)) : ℂ)‖
      rwa [mul_zero] at h2
    refine hlim.congr' ?_
    filter_upwards [hsmall] with k hk
    congr 2
    rw [← pcLp_smul]
    congr 1
    funext x
    have hne : abPhase (detLinks U (m k)) x ν μ ≠ Real.pi := by
      intro hπ
      have := hk x ν μ
      rw [hπ, abs_of_pos Real.pi_pos] at this
      linarith [Real.pi_pos]
    simp only [realC, comp, unitCurv, Pi.smul_apply, smul_eq_mul, projC,
      ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.proj_apply,
      Complex.ofRealCLM_apply]
    rw [← detCurvature_eq_detPacket (L / n (m k)) (U (m k)) x ⟨(ν, μ), h⟩]
    simp only [detCurvature]
    rw [show (fun x μ => smChi (U (m k) x μ)) = detLinks U (m k) from rfl,
      abPhase_swap _ (hu k) x ν μ hne]
    push_cast
    ring

/-! ### The sequence clauses -/

/-- **`prop:periodic-determinant-normalization`, precompactness clauses.**  For a screened
bounded-curvature sequence with zero determinant flux and any constants `c_h` with
`|L c_{μ,h}| ≤ π` (those of the exact normalization `native_determinant_split`), every
subsequence of the unit-torus coordinates `a'_h = L (a⁰_h + c_h)` has a further subsequence along
which `R_h^0 a'_h` converges strongly in `L⁴` and `L²`, the first differences `R_h^0 D⁺_μ a'_h`
converge strongly in `L²` (to the weak derivatives of the limit), and the trigonometric
reconstructions converge strongly in `H¹`. -/
theorem precompact_sequence (S : CurvatureScreen L n U Lg)
    (hflux : ∀ᶠ k in atTop, ∀ μ ν, planeFlux (detLinks U k) 0 μ ν = 0)
    (cst : ℕ → Fin 4 → ℝ) (hcst : ∀ k μ, |L * cst k μ| ≤ Real.pi)
    (ψ : ℕ → ℕ) (hψ : Tendsto ψ atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ A : Fin 4 → L²(UnitAddTorus (Fin 4)), ∀ ν,
      MemLp (A ν : UnitAddTorus (Fin 4) → ℂ) 4 volume ∧
      Tendsto (fun k => eLpNorm (fun y => pc (unitCoord L U cst (ψ (φ k)) ν) y - A ν y) 4 volume)
        atTop (𝓝 0) ∧
      Tendsto (fun k => ‖pcLp (unitCoord L U cst (ψ (φ k)) ν) - A ν‖) atTop (𝓝 0) ∧
      (∀ μ, Tendsto (fun k => ‖pcLp (Dp μ (unitCoord L U cst (ψ (φ k)) ν)) - weakDeriv μ (A ν)‖)
        atTop (𝓝 0)) ∧
      Tendsto (fun k => sobSq 1 ⇑(trigLp (unitCoord L U cst (ψ (φ k)) ν) - A ν)) atTop (𝓝 0) := by
  have hL := S.pos
  -- precompactness of the curvature packets along `ψ`
  have hTB := (determinant_screen_flux S).2.2.2.1
  have hTB' : TotallyBounded (range fun k => pcLp (detPacket (L / n (ψ k)) (U (ψ k)))) :=
    hTB.subset (by rintro _ ⟨k, rfl⟩; exact ⟨ψ k, rfl⟩)
  obtain ⟨G, -, φ₁, hφ₁, hG⟩ := (hTB'.closure.isCompact_of_isClosed isClosed_closure).tendsto_subseq
    fun k => subset_closure (mem_range_self k)
  -- bounded constants
  have hbd : Bornology.IsBounded (Metric.closedBall (0 : Fin 4 → ℝ) Real.pi) :=
    Metric.isBounded_closedBall
  obtain ⟨cinf, -, φ₂, hφ₂, hc⟩ := tendsto_subseq_of_bounded hbd
    (x := fun k => fun μ => L * cst (ψ (φ₁ k)) μ) fun k => by
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg Real.pi_pos.le]
      intro μ
      rw [Real.norm_eq_abs]
      exact hcst _ μ
  set φ := φ₁ ∘ φ₂ with hφdef
  have hφ : StrictMono φ := hφ₁.comp hφ₂
  set m : ℕ → ℕ := fun k => ψ (φ k)
  have hm : Tendsto m atTop atTop := hψ.comp hφ.tendsto_atTop
  have hnm : Tendsto (fun k => n (m k)) atTop atTop := S.tendsto.comp hm
  have hw : Tendsto (fun k => ‖pcLp (detPacket (L / n (m k)) (U (m k))) - G‖) atTop (𝓝 0) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.1 hG).comp hφ₂.tendsto_atTop
    exact this
  have hsmall : ∀ᶠ k in atTop, ∀ x μ ν, |abPhase (detLinks U (m k)) x μ ν| < Real.pi / 3 := by
    have := (S.eventually_phase_small 1 one_pos)
    filter_upwards [hm.eventually this] with k hk x μ ν
    exact (hk x μ ν).trans_lt (by linarith [Real.pi_gt_three])
  have hmean : ∀ᶠ k in atTop, ∀ μ ν, ∑ x, unitCurv L U (m k) x μ ν = 0 := by
    filter_upwards [hsmall, hm.eventually hflux] with k hk hf μ ν
    have := (detCurvature_closed_meanZero (detLinks U (m k)) (fun x μ => norm_smChi _) hk hf
      (L / n (m k))).2 μ ν
    simp only [unitCurv, ← Finset.mul_sum, this, mul_zero]
  have hF := tendsto_curv_components hL hw hsmall
  obtain ⟨hu, -, hv, -⟩ := hodge_strong_convergence (d := 4) (n := fun k => n (m k)) hnm
    (f := fun k => unitCurv L U (m k)) hmean (F := curvLimit L G) hF
  -- the limits
  refine ⟨φ, hφ, fun ν => contPrimitive (curvLimit L G) ν + constL (cinf ν), fun ν => ?_⟩
  have hcν : Tendsto (fun k => ((L * cst (m k) ν : ℝ) : ℂ)) atTop (𝓝 ((cinf ν : ℝ) : ℂ)) := by
    have := (continuous_apply ν).continuousAt.tendsto.comp hc
    exact (Complex.continuous_ofReal.tendsto _).comp this
  have hu' : Tendsto (fun k => ‖pcLp (unitCoord L U cst (m k) ν) -
      (contPrimitive (curvLimit L G) ν + constL (cinf ν))‖) atTop (𝓝 0) := by
    have hup : Tendsto (fun k => ‖pcLp (primC (n := fun k => n (m k))
        (fun k => unitCurv L U (m k)) k ν) - contPrimitive (curvLimit L G) ν‖ +
        ‖((L * cst (m k) ν : ℝ) : ℂ) - cinf ν‖) atTop (𝓝 0) := by
      simpa using (hu ν).add (tendsto_iff_norm_sub_tendsto_zero.1 hcν)
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hup
    rw [unitCoord_eq hL, pcLp_add, pcLp_const]
    calc ‖pcLp (primC (unitCurv L U) (m k) ν) + constL ((L * cst (m k) ν : ℝ) : ℂ) -
          (contPrimitive (curvLimit L G) ν + constL (cinf ν))‖
        = ‖(pcLp (primC (unitCurv L U) (m k) ν) - contPrimitive (curvLimit L G) ν) +
            (constL ((L * cst (m k) ν : ℝ) : ℂ) - constL (cinf ν))‖ := by congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add le_rfl (norm_constL_sub_le _ _))
  have hv' : ∀ μ, Tendsto (fun k => ‖pcLp (Dp μ (unitCoord L U cst (m k) ν)) -
      weakDeriv μ (contPrimitive (curvLimit L G) ν)‖) atTop (𝓝 0) := by
    intro μ
    refine (hv μ ν).congr fun k => ?_
    rw [unitCoord_eq hL, Dp_add_const]
    rfl
  obtain ⟨hwd, -, hH, hL4, hconv4⟩ := native_reconstruction_identification hnm hu' hv'
  refine ⟨hL4, hconv4, hu', fun μ => ?_, hH⟩
  rw [hwd μ]
  exact hv' μ

/-- **`prop:periodic-determinant-normalization`, `h ‖a_h‖_{∞,h} → 0`**: the coordinates are
eventually principal (for the whole sequence). -/
theorem tendsto_mesh_mul_sup (S : CurvatureScreen L n U Lg)
    (hflux : ∀ᶠ k in atTop, ∀ μ ν, planeFlux (detLinks U k) 0 μ ν = 0)
    (cst : ℕ → Fin 4 → ℝ) (hcst : ∀ k μ, |L * cst k μ| ≤ Real.pi) (ν : Fin 4) :
    Tendsto (fun k => L / n k * Finset.univ.sup' Finset.univ_nonempty
      (fun x => |detPotential (detLinks U k) (L / n k) x ν + cst k ν|)) atTop (𝓝 0) := by
  have hL := S.pos
  refine tendsto_of_subseq_tendsto fun ψ hψ => ?_
  obtain ⟨φ, hφ, A, hA⟩ := precompact_sequence S hflux cst hcst ψ hψ
  obtain ⟨hmem, hconv, -⟩ := hA ν
  refine ⟨φ, ?_⟩
  have hnm : Tendsto (fun k => n (ψ (φ k))) atTop atTop :=
    S.tendsto.comp (hψ.comp hφ.tendsto_atTop)
  have h := tendsto_meshSup (E := ℂ) (n := fun k => n (ψ (φ k))) hnm
    (A := fun k => unitCoord L U cst (ψ (φ k)) ν) hmem hconv
  refine squeeze_zero (fun k => mul_nonneg (by positivity) ?_) (fun k => ?_) h
  · exact (abs_nonneg _).trans (Finset.le_sup' (fun x => |detPotential (detLinks U (ψ (φ k)))
      (L / n (ψ (φ k))) x ν + cst (ψ (φ k)) ν|) (Finset.mem_univ 0))
  · have hN : (0 : ℝ) < n (ψ (φ k)) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (n (ψ (φ k))))
    have hpos : 0 < L / n (ψ (φ k)) := by positivity
    rw [← le_div_iff₀' hpos]
    refine Finset.sup'_le _ _ fun x _ => ?_
    rw [le_div_iff₀' hpos]
    have := le_meshSup (unitCoord L U cst (ψ (φ k)) ν) x
    simp only [unitCoord, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hL] at this
    calc L / n (ψ (φ k)) * |detPotential (detLinks U (ψ (φ k))) (L / n (ψ (φ k))) x ν +
          cst (ψ (φ k)) ν| = (n (ψ (φ k)) : ℝ)⁻¹ * (L * |detPotential (detLinks U (ψ (φ k)))
          (L / n (ψ (φ k))) x ν + cst (ψ (φ k)) ν|) := by ring
      _ ≤ _ := this

/-- Non-vacuity: the trivial screened sequence (all links `1`) has zero determinant flux, so
the hypotheses are satisfiable (`DeterminantScreenFlux.curvatureScreen_trivial`). -/
theorem planeFlux_detLinks_trivial (k : ℕ) (μ ν : Fin 4) :
    planeFlux (detLinks (n := fun k => k + 1) (fun _ _ _ => (1 : SMGaugeGroup)) k) 0 μ ν = 0 :=
  planeFlux_trivial (k + 1) μ ν

end

end RenewalGeometry.DeterminantNormalizationSequence
