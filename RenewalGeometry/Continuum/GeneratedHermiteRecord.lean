/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedRatesIdentified

/-!
# The cubic-Hermite record as a space-time field and its slice norms

Generic infrastructure (no renewal notions) for the readouts of `thm:generated-dynamics`
(Einstein–Standard-Model action-closure manuscript, `app:generated-dynamics`, "Physical Hermite
readout": "On each interval `[t_j, t_{j+1}]`, reconstruct the physical head by the cubic Hermite
polynomial having endpoint values equal to the generated heads and endpoint slopes equal to the
corresponding components of `G_N(U^j)` and `G_N(U^{j+1})`").

* `hc` — the Hermite curve of a cell in the Galerkin space; `recW`, `recWD`, `recWDD` — the record,
  its time derivative and second time derivative as smooth spatially periodic space-time fields
  (`pd_recW_zero`, `pd_recWD_zero`: the coordinate time derivatives are the Hermite derivatives);
  `coef_recW` etc.: their slice coefficients are the Galerkin coefficients of the Hermite curve.
* `sum_Q_le_of_sum_le` — Fourier-form bounds of finitely many fields give slice-norm bounds
  (`GenParseval`).
* **`exact_time_derivs`** — for a smooth solution `V` agreeing with a one-sided classical solution
  `U` on `[0, T']`: `∂_tV = G(U)` and the coefficient second derivative `D₂` of `U` is that of
  `∂_t²V` on the slices of `[0, T']`.
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff Real

noncomputable section

namespace RenewalGeometry.GenHermite

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy KatoGalerkin SpectralGalerkin
  CubicHermite

set_option linter.unusedSectionVars false

variable {d n : ℕ}

/-! ### The Hermite curve of a cell -/

section Curve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Hermite curve of the cell starting at `t₀`, as a function of time. -/
def hc (τ t₀ : ℝ) (U₀ U₁ V₀ V₁ : E) (t : ℝ) : E := hermite τ U₀ U₁ V₀ V₁ ((t - t₀) / τ)

/-- Its time derivative. -/
def hcD (τ t₀ : ℝ) (U₀ U₁ V₀ V₁ : E) (t : ℝ) : E := hermiteD τ U₀ U₁ V₀ V₁ ((t - t₀) / τ)

/-- Its second time derivative. -/
def hcDD (τ t₀ : ℝ) (U₀ U₁ V₀ V₁ : E) (t : ℝ) : E := hermiteDD τ U₀ U₁ V₀ V₁ ((t - t₀) / τ)

theorem contDiff_hc (τ t₀ : ℝ) (U₀ U₁ V₀ V₁ : E) : ContDiff ℝ ∞ (hc τ t₀ U₀ U₁ V₀ V₁) := by
  unfold hc hermite basisH basisG cubic
  fun_prop

theorem contDiff_hcD (τ t₀ : ℝ) (U₀ U₁ V₀ V₁ : E) : ContDiff ℝ ∞ (hcD τ t₀ U₀ U₁ V₀ V₁) := by
  unfold hcD hermiteD basisHD basisGD cubicD
  fun_prop

theorem hasDerivAt_hc {τ : ℝ} (hτ : τ ≠ 0) (t₀ : ℝ) (U₀ U₁ V₀ V₁ : E) (t : ℝ) :
    HasDerivAt (hc τ t₀ U₀ U₁ V₀ V₁) (hcD τ t₀ U₀ U₁ V₀ V₁ t) t :=
  hasDerivAt_hermite hτ t₀ U₀ U₁ V₀ V₁ t

theorem hasDerivAt_hcD (τ t₀ : ℝ) (U₀ U₁ V₀ V₁ : E) (t : ℝ) :
    HasDerivAt (hcD τ t₀ U₀ U₁ V₀ V₁) (hcDD τ t₀ U₀ U₁ V₀ V₁ t) t :=
  hasDerivAt_hermiteD τ t₀ U₀ U₁ V₀ V₁ t

end Curve

/-! ### Fields of a Galerkin curve -/

section Fields

/-- The field `x ↦ fld q (c (x₀)) b x` of a time-dependent Galerkin state. -/
def fldc (q : ℕ) {N : ℕ} (c : ℝ → GS d n N) (b : Fin n) (x : ST d) : ℝ := fld q (c (x 0)) b x

/-- `fld q a b x` as a continuous linear functional of the Galerkin state. -/
def fldL (q : ℕ) (N : ℕ) (b : Fin n) (x : ST d) : GS d n N →L[ℝ] ℝ :=
  ∑ k : KatoGalerkin.box (d := d) N, (casS k.1 x / Real.sqrt (wq q k.1)) •
    EuclideanSpace.proj ((b, k) : Fin n × KatoGalerkin.box (d := d) N)

theorem fldL_apply (q : ℕ) {N : ℕ} (b : Fin n) (x : ST d) (a : GS d n N) :
    fldL q N b x a = fld q a b x := by
  rw [fld_eq, fldL, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  have e : (EuclideanSpace.proj ((b, k) : Fin n × KatoGalerkin.box (d := d) N) :
      GS d n N →L[ℝ] ℝ) a = a (b, k) := rfl
  rw [e]
  ring

theorem contDiff_fldc (q : ℕ) {N : ℕ} {c : ℝ → GS d n N} (hc : ContDiff ℝ ∞ c) (b : Fin n) :
    ContDiff ℝ ∞ (fldc q c b) := by
  have e : fldc q c b = fun x => ∑ k : KatoGalerkin.box (d := d) N,
      (EuclideanSpace.proj ((b, k) : Fin n × KatoGalerkin.box (d := d) N) (c (x 0))) /
        Real.sqrt (wq q k.1) * casS k.1 x := by
    funext x; rw [fldc, fld_eq]; rfl
  rw [e]
  have h0 : ContDiff ℝ ∞ (fun x : ST d => x 0) := contDiff_apply ℝ ℝ 0
  have hcs : ∀ k : Fin d → ℤ, ContDiff ℝ ∞ (casS k) := contDiff_casS
  fun_prop

theorem isSPeriodic_fldc (q : ℕ) {N : ℕ} (c : ℝ → GS d n N) (b : Fin n) :
    IsSPeriodic (fldc q c b) := fun k x => by
  unfold fldc
  have h0 : (x + sshift k) 0 = x 0 := by simp [sshift]
  rw [h0, isSPeriodic_fld q (c (x 0)) b k x]

theorem coef_fldc (q : ℕ) {N : ℕ} (c : ℝ → GS d n N) (b : Fin n) (t : ℝ) (k : Fin d → ℤ) :
    coef (fldc q c b) t k = cf q (c t) b k := by
  rw [GenGalCons.coef_congr_slice (g := fld q (c t) b) (fun y => by simp [fldc]),
    KatoRates.coef_fld]

theorem fld_time_shift (q : ℕ) {N : ℕ} (a : GS d n N) (b : Fin n) (x : ST d) (s : ℝ) :
    fld q a b (x + s • ev (0 : Fin (d + 1))) = fld q a b x := by
  rw [fld_eq, fld_eq]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  unfold casS
  rw [map_add, map_smul, phL_single_zero, smul_zero, add_zero]

/-- **Coordinate time derivative of the field of a Galerkin curve.** -/
theorem pd_fldc_zero (q : ℕ) {N : ℕ} {c c' : ℝ → GS d n N} (hc : ContDiff ℝ ∞ c)
    (hd : ∀ t, HasDerivAt c (c' t) t) (b : Fin n) (x : ST d) :
    pd (fldc q c b) 0 x = fldc q c' b x := by
  refine (hasDerivAt_line0 (contDiff_fldc q hc b) x 0).unique ?_
  have e : (fun s : ℝ => fldc q c b (x + s • ev (0 : Fin (d + 1)))) =
      fun s => fldL q N b x (c (x 0 + s)) := by
    funext s
    rw [fldL_apply, fldc, ← fld_time_shift q _ b x s]
    simp
  rw [e]
  have h1 : HasDerivAt (fun s : ℝ => x 0 + s) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add (x 0)
  have h2 : HasDerivAt (fun s : ℝ => c (x 0 + s)) (c' (x 0)) 0 := by
    have := (hd (x 0 + 0)).scomp (0 : ℝ) h1
    simp only [one_smul, add_zero, Function.comp_def] at this
    exact this
  have h3 : HasDerivAt (fun s => fldL q N b x (c (x 0 + s))) (fldL q N b x (c' (x 0))) 0 :=
    (fldL q N b x).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
  rw [show fldc q c' b x = fldL q N b x (c' (x 0)) from (fldL_apply q b x (c' (x 0))).symm]
  exact h3

end Fields

/-! ### The record of a cell -/

section Record

variable {q N : ℕ} (τ t₀ : ℝ) (U₀ U₁ V₀ V₁ : GS d n N)

/-- **The record** of the cell `[t₀, t₀ + τ]`: the cubic Hermite field with nodal values `U₀, U₁`
and nodal slopes `V₀, V₁`. -/
def recW (q : ℕ) : Fin n → ST d → ℝ := fldc q (hc τ t₀ U₀ U₁ V₀ V₁)

/-- Its time derivative. -/
def recWD (q : ℕ) : Fin n → ST d → ℝ := fldc q (hcD τ t₀ U₀ U₁ V₀ V₁)

/-- Its second time derivative. -/
def recWDD (q : ℕ) : Fin n → ST d → ℝ := fldc q (hcDD τ t₀ U₀ U₁ V₀ V₁)

theorem contDiff_recW (b : Fin n) : ContDiff ℝ ∞ (recW τ t₀ U₀ U₁ V₀ V₁ q b) :=
  contDiff_fldc q (contDiff_hc τ t₀ U₀ U₁ V₀ V₁) b

theorem contDiff_recWD (b : Fin n) : ContDiff ℝ ∞ (recWD τ t₀ U₀ U₁ V₀ V₁ q b) :=
  contDiff_fldc q (contDiff_hcD τ t₀ U₀ U₁ V₀ V₁) b

theorem pd_recW_zero (hτ : τ ≠ 0) (b : Fin n) (x : ST d) :
    pd (recW τ t₀ U₀ U₁ V₀ V₁ q b) 0 x = recWD τ t₀ U₀ U₁ V₀ V₁ q b x :=
  pd_fldc_zero q (contDiff_hc τ t₀ U₀ U₁ V₀ V₁) (hasDerivAt_hc hτ t₀ U₀ U₁ V₀ V₁) b x

theorem pd_recWD_zero (b : Fin n) (x : ST d) :
    pd (recWD τ t₀ U₀ U₁ V₀ V₁ q b) 0 x = recWDD τ t₀ U₀ U₁ V₀ V₁ q b x :=
  pd_fldc_zero q (contDiff_hcD τ t₀ U₀ U₁ V₀ V₁) (hasDerivAt_hcD τ t₀ U₀ U₁ V₀ V₁) b x

theorem coef_recW (b : Fin n) (t : ℝ) (k : Fin d → ℤ) :
    coef (recW τ t₀ U₀ U₁ V₀ V₁ q b) t k =
      cf q (hermite τ U₀ U₁ V₀ V₁ ((t - t₀) / τ)) b k :=
  coef_fldc q _ b t k

theorem coef_recWD (b : Fin n) (t : ℝ) (k : Fin d → ℤ) :
    coef (recWD τ t₀ U₀ U₁ V₀ V₁ q b) t k =
      cf q (hermiteD τ U₀ U₁ V₀ V₁ ((t - t₀) / τ)) b k :=
  coef_fldc q _ b t k

theorem coef_recWDD (b : Fin n) (t : ℝ) (k : Fin d → ℤ) :
    coef (recWDD τ t₀ U₀ U₁ V₀ V₁ q b) t k =
      cf q (hermiteDD τ U₀ U₁ V₀ V₁ ((t - t₀) / τ)) b k :=
  coef_fldc q _ b t k

end Record

/-! ### From Fourier-form bounds to slice norms -/

/-- Fourier-form bounds of finitely many smooth periodic fields give slice-norm bounds. -/
theorem sum_Q_le_of_sum_le (r : ℕ) {f : Fin n → ST d → ℝ} (hf : ∀ b, ContDiff ℝ ∞ (f b))
    (hp : ∀ b, IsSPeriodic (f b)) {t B : ℝ}
    (h : ∀ S : Finset (Fin d → ℤ), ∑ b, ∑ k ∈ S, wq r k * coef (f b) t k ^ 2 ≤ B) :
    ∑ b, Q r (f b) t ≤ B := by
  have hs : HasSum (fun k => ∑ b, wq r k * coef (f b) t k ^ 2) (∑ b, Q r (f b) t) :=
    hasSum_sum fun b _ => GenParseval.hasSum_wq_coef_sq r (hf b) (hp b) t
  rw [← hs.tsum_eq]
  refine hs.summable.tsum_le_of_sum_le fun S => ?_
  rw [Finset.sum_comm]
  exact h S

/-! ### Time derivatives of a smooth solution agreeing with a one-sided solution -/

section Exact

variable {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}

theorem hasDerivAt_time {f : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (t : ℝ) (y : Fin d → ℝ) :
    HasDerivAt (fun s => f (Fin.cons s y)) (pd f 0 (Fin.cons t y)) t := by
  have h := KatoSmooth.hasDerivAt_line_at hf (Fin.cons 0 y) 0 t
  have e : ∀ s : ℝ, (Fin.cons 0 y : ST d) + s • ev (0 : Fin (d + 1)) = Fin.cons s y := by
    intro s; funext μ
    induction μ using Fin.cases with
    | zero => simp
    | succ i => simp [Pi.single_apply, Fin.succ_ne_zero]
  simp only [e] at h
  exact h

/-- **The time derivatives of a smooth solution agreeing with a one-sided classical solution.**
Let `U` be a one-sided classical solution on `[0, T]` (`∂_tU = G(U)` within `[0, T]`, with
coefficient second derivative `D₂` of `G(U)`), and let `V` be smooth with `V = U` on `[0, T']`,
`0 < T' ≤ T`.  Then on the slices of `[0, T']`: `∂_tV = G(U)` pointwise and
`c_k(∂_t²V) = D₂`. -/
theorem exact_time_derivs {T T' : ℝ} (hT' : 0 < T') (hTT : T' ≤ T) {U : Fin n → ST d → ℝ}
    {P : Fin n → Fin d → ST d → ℝ} {D₂ : Fin n → (Fin d → ℤ) → ℝ → ℝ}
    (hUt : ∀ b, ∀ t ∈ Icc 0 T, ∀ y, HasDerivWithinAt (fun σ => U b (Fin.cons σ y))
      (KatoGalerkin.genP A F U P b (Fin.cons t y)) (Icc 0 T) t)
    (hD₂ : ∀ b k, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun σ => coef (KatoGalerkin.genP A F U P b) σ k)
      (D₂ b k t) (Icc 0 T) t)
    {V : Fin n → ST d → ℝ} (hV : ∀ b, ContDiff ℝ ∞ (V b))
    (hUV : ∀ x ∈ slab (d := d) 0 T', ∀ b, U b x = V b x) :
    (∀ b, ∀ t ∈ Icc 0 T', ∀ y,
      pd (V b) 0 (Fin.cons t y) = KatoGalerkin.genP A F U P b (Fin.cons t y)) ∧
    (∀ b k, ∀ t ∈ Icc 0 T', coef (pd (pd (V b) 0) 0) t k = D₂ b k t) := by
  have hsub : Icc 0 T' ⊆ Icc 0 T := Icc_subset_Icc le_rfl hTT
  have huniq : UniqueDiffOn ℝ (Icc (0 : ℝ) T') := uniqueDiffOn_Icc hT'
  have h1 : ∀ b, ∀ t ∈ Icc 0 T', ∀ y,
      pd (V b) 0 (Fin.cons t y) = KatoGalerkin.genP A F U P b (Fin.cons t y) := by
    intro b t ht y
    have hU := (hUt b t (hsub ht) y).mono hsub
    have hVd := (hasDerivAt_time (hV b) t y).hasDerivWithinAt (s := Icc 0 T')
    have hcongr : HasDerivWithinAt (fun σ => U b (Fin.cons σ y)) (pd (V b) 0 (Fin.cons t y))
        (Icc 0 T') t :=
      hVd.congr (fun σ hσ => hUV _ (by simpa [slab] using hσ) b) (hUV _ (by simpa [slab] using ht) b)
    exact (huniq t ht).eq_deriv _ hcongr hU
  refine ⟨h1, fun b k t ht => ?_⟩
  have hc : ∀ σ ∈ Icc 0 T', coef (KatoGalerkin.genP A F U P b) σ k = coef (pd (V b) 0) σ k :=
    fun σ hσ => GenGalCons.coef_congr_slice (fun y => (h1 b σ hσ y).symm) k
  have hV2 := (KatoSmooth.hasDerivAt_coef_of_time (a := t - 1) (b := t + 1)
    (contDiff_pd_top (hV b) 0).continuous (contDiff_pd_top (contDiff_pd_top (hV b) 0) 0).continuous
    (fun t' _ y => hasDerivAt_time (contDiff_pd_top (hV b) 0) t' y) k
    (show t ∈ Ioo (t - 1) (t + 1) from ⟨by linarith, by linarith⟩)).hasDerivWithinAt
      (s := Icc 0 T')
  have hD := (hD₂ b k t (hsub ht)).mono hsub
  have hD' : HasDerivWithinAt (fun σ => coef (pd (V b) 0) σ k) (D₂ b k t) (Icc 0 T') t :=
    hD.congr (fun σ hσ => (hc σ hσ).symm) (hc t ht).symm
  exact (huniq t ht).eq_deriv _ hV2 hD'

end Exact

end RenewalGeometry.GenHermite
