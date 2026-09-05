/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Lorentz.MultiplierResolvent

/-!
# Plancherel transport: position-space strong convergence

The position↔Fourier transport previously listed as the standing
symbol-level convention: Mathlib now provides the Fourier transform
on `L²` as a linear isometry equivalence
(`MeasureTheory.Lp.fourierTransformₗᵢ`), so the multiplication-model
convergence results transport to **position space** as genuine
statements about operators on `L²`:

* `mulL2` — multiplication by a bounded measurable operator field,
  packaged as a continuous linear map on `Lp E 2 μ` with operator
  norm at most the field bound;
* `mulL2_tendsto` — the strong convergence of
  `NCG/Lorentz/MultiplierResolvent.lean`, upgraded from the
  `eLpNorm` level to convergence in the `Lp` space;
* `strong_tendsto_conj` — strong convergence is preserved under
  conjugation by a linear isometry equivalence;
* `positionMultiplier` — the position-space operator
  `𝓕⁻¹ ∘ (mult by m) ∘ 𝓕` on `L²(E, F)`;
* `position_multiplier_tendsto` — **position-space strong
  convergence**: for uniformly bounded measurable symbol fields
  converging pointwise a.e. (e.g. the flat renewal resolvent
  symbols), the conjugated position-space operators converge
  strongly on `L²`.

Applied to the resolvent fields `rₙ(ξ) = (hₙ(ξ) − z)⁻¹` of the flat
renewal Hamiltonians, `positionMultiplier rₙ` **is** the resolvent of
the position-space Hamiltonian (the standard Fourier definition of a
function of a constant-coefficient operator), so this discharges the
Plancherel-transport clause of `thm:flat-limit`(iv)–(v): the
position-space resolvents and bounded functions of the Hamiltonians
converge strongly on `L²`, with no informal identification left.
-/

namespace NCG

open Filter MeasureTheory

/-! ## Multiplication operators as continuous linear maps on `L²` -/

section MulL2

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Multiplication by a bounded measurable operator field as a
continuous linear map on `L²`. -/
noncomputable def mulL2 (m : X → E →L[𝕜] E)
    (hm : AEStronglyMeasurable m μ) {M : ℝ} (hM0 : 0 ≤ M)
    (hb : ∀ᵐ x ∂μ, ‖m x‖ ≤ M) :
    Lp E 2 μ →L[𝕜] Lp E 2 μ := by
  refine LinearMap.mkContinuous
    { toFun := fun u => (memLp_clm_apply hm hb (Lp.memLp u)).toLp _
      map_add' := ?_
      map_smul' := ?_ } M ?_
  · intro u v
    rw [← MemLp.toLp_add, MemLp.toLp_eq_toLp_iff]
    filter_upwards [Lp.coeFn_add u v] with x hx
    rw [hx]
    simp
  · intro c u
    simp only [RingHom.id_apply]
    rw [← MemLp.toLp_const_smul, MemLp.toLp_eq_toLp_iff]
    filter_upwards [Lp.coeFn_smul c u] with x hx
    rw [hx]
    simp
  · intro u
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [Lp.norm_toLp]
    have h1 : eLpNorm (fun x => m x (u x)) 2 μ
        ≤ M.toNNReal • eLpNorm (⇑u) 2 μ := by
      refine eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul ?_ 2
      filter_upwards [hb] with x hx
      calc ‖m x (u x)‖ ≤ ‖m x‖ * ‖u x‖ := (m x).le_opNorm _
        _ ≤ ↑M.toNNReal * ‖u x‖ := by
            rw [Real.coe_toNNReal M hM0]
            exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    calc (eLpNorm (fun x => m x (u x)) 2 μ).toReal
        ≤ (M.toNNReal • eLpNorm (⇑u) 2 μ).toReal := by
          refine ENNReal.toReal_mono ?_ h1
          exact ENNReal.mul_ne_top ENNReal.coe_ne_top
            (Lp.eLpNorm_ne_top u)
      _ = M * ‖u‖ := by
          rw [ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul,
            ENNReal.coe_toReal, Real.coe_toNNReal M hM0,
            Lp.norm_def]

theorem mulL2_apply (m : X → E →L[𝕜] E)
    (hm : AEStronglyMeasurable m μ) {M : ℝ} (hM0 : 0 ≤ M)
    (hb : ∀ᵐ x ∂μ, ‖m x‖ ≤ M) (u : Lp E 2 μ) :
    mulL2 m hm hM0 hb u =ᵐ[μ] fun x => m x (u x) :=
  MemLp.coeFn_toLp (memLp_clm_apply hm hb (Lp.memLp u))

/-- **Strong convergence of multiplication operators on `L²`**, in
the `Lp` space: the `eLpNorm` convergence of
`multiplier_tendsto_eLpNorm` upgraded to the Bochner space. -/
theorem mulL2_tendsto
    {mn : ℕ → X → E →L[𝕜] E} {m : X → E →L[𝕜] E}
    {M : ℝ} (hM0 : 0 ≤ M)
    (hmn : ∀ n, AEStronglyMeasurable (mn n) μ)
    (hm : AEStronglyMeasurable m μ)
    (hbn : ∀ n, ∀ᵐ x ∂μ, ‖mn n x‖ ≤ M)
    (hb : ∀ᵐ x ∂μ, ‖m x‖ ≤ M)
    (u : Lp E 2 μ)
    (hconv : ∀ᵐ x ∂μ,
      Tendsto (fun n => mn n x (u x)) atTop (nhds (m x (u x)))) :
    Tendsto (fun n => mulL2 (mn n) (hmn n) hM0 (hbn n) u)
      atTop (nhds (mulL2 m hm hM0 hb u)) := by
  have hE := multiplier_tendsto_eLpNorm hM0 hmn hm hbn hb
    (Lp.memLp u) hconv
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have happly : ∀ (mm : X → E →L[𝕜] E) hmm hbb,
      mulL2 mm hmm hM0 hbb u
        = (memLp_clm_apply hmm hbb (Lp.memLp u)).toLp
            (fun x => mm x (u x)) := fun _ _ _ => rfl
  have hnorm : ∀ n,
      ‖mulL2 (mn n) (hmn n) hM0 (hbn n) u - mulL2 m hm hM0 hb u‖
      = (eLpNorm (fun x => mn n x (u x) - m x (u x)) 2 μ).toReal := by
    intro n
    rw [happly, happly, ← MemLp.toLp_sub, Lp.norm_toLp]
    rfl
  have h0 : Tendsto (fun n => (eLpNorm
      (fun x => mn n x (u x) - m x (u x)) 2 μ).toReal)
      atTop (nhds 0) := by
    have hcont := ENNReal.tendsto_toReal (a := 0) (by simp)
    have := hcont.comp hE
    simpa [Function.comp_def] using this
  refine h0.congr fun n => ?_
  rw [hnorm n]

end MulL2

/-! ## Conjugation transport -/

/-- Strong convergence is preserved by conjugation with a linear
isometry equivalence — the transport mechanism for carrying the
multiplier-model convergence to position space. -/
theorem strong_tendsto_conj {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {H H' : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    [NormedAddCommGroup H'] [NormedSpace 𝕜 H']
    (U : H ≃ₗᵢ[𝕜] H') {An : ℕ → H' → H'} {A : H' → H'}
    (h : ∀ v : H', Tendsto (fun n => An n v) atTop (nhds (A v))) :
    ∀ u : H, Tendsto (fun n => U.symm (An n (U u)))
      atTop (nhds (U.symm (A (U u)))) :=
  fun u => (U.symm.continuous.tendsto _).comp (h (U u))

/-! ## Position-space packaging via Plancherel -/

section Position

variable {E F : Type*}
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The position-space operator `𝓕⁻¹ ∘ (mult by m) ∘ 𝓕` on
`L²(E, F)`: for the resolvent symbol fields of the flat renewal
Hamiltonian this **is** the position-space resolvent. -/
noncomputable def positionMultiplier (m : E → F →L[ℂ] F)
    (hm : AEStronglyMeasurable m (volume : Measure E)) {M : ℝ}
    (hM0 : 0 ≤ M) (hb : ∀ᵐ x ∂(volume : Measure E), ‖m x‖ ≤ M)
    (u : Lp (α := E) F 2) : Lp (α := E) F 2 :=
  (Lp.fourierTransformₗᵢ E F).symm
    (mulL2 m hm hM0 hb ((Lp.fourierTransformₗᵢ E F) u))

/-- **Position-space strong convergence** (`thm:flat-limit`(iv)–(v),
Plancherel transport): for uniformly bounded measurable symbol
fields converging pointwise a.e., the position-space operators
`𝓕⁻¹ (mult mₙ) 𝓕` converge strongly on `L²(E, F)`.  Applied to the
flat renewal resolvent symbols `(hₙ(ξ) − z)⁻¹` (bounded by
`|Im z|⁻¹`, convergent by `tendsto_ring_inverse`), this is the
strong resolvent convergence of the position-space Hamiltonians;
applied to `f(hₙ(ξ))` via `cfc_tendsto_of_isSelfAdjoint`, it is the
`C₀` functional-calculus clause in position space. -/
theorem position_multiplier_tendsto
    {mn : ℕ → E → F →L[ℂ] F} {m : E → F →L[ℂ] F}
    {M : ℝ} (hM0 : 0 ≤ M)
    (hmn : ∀ n, AEStronglyMeasurable (mn n) (volume : Measure E))
    (hm : AEStronglyMeasurable m (volume : Measure E))
    (hbn : ∀ n, ∀ᵐ x ∂(volume : Measure E), ‖mn n x‖ ≤ M)
    (hb : ∀ᵐ x ∂(volume : Measure E), ‖m x‖ ≤ M)
    (u : Lp (α := E) F 2)
    (hconv : ∀ᵐ x ∂(volume : Measure E),
      Tendsto (fun n =>
          mn n x (((Lp.fourierTransformₗᵢ E F) u) x))
        atTop (nhds (m x (((Lp.fourierTransformₗᵢ E F) u) x)))) :
    Tendsto (fun n => positionMultiplier (mn n) (hmn n) hM0 (hbn n) u)
      atTop (nhds (positionMultiplier m hm hM0 hb u)) := by
  unfold positionMultiplier
  have h1 := mulL2_tendsto hM0 hmn hm hbn hb
    ((Lp.fourierTransformₗᵢ E F) u) hconv
  exact ((Lp.fourierTransformₗᵢ E F).symm.continuous.tendsto _).comp
    h1

end Position

end NCG
