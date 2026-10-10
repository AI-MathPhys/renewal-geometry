/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeClosureClosed
import RenewalGeometry.Action.NativeSelectedClosure

/-!
# `thm:native-selected-closure` for native records

Einstein–Standard-Model action-closure manuscript, `thm:native-selected-closure`
(`eq:selected-closure`).  The generic one-cutoff assembly `SelectedClosure.native_selected_closure`
carried the conclusion of `prop:coupled-bootstrap` as the hypothesis `hboot` and the output of
`thm:native-source` as `hsrc`, for an abstract alignment readout `al`, source budget `Ysrc` and
comparison quantity `Sx`.  Here both are discharged for native records: the records `x` of the
finite accepted process are native grid records `rec x`, their actual tuples are
`recTuple (rec x)`, `al = i_{h,k} + γ_{h,k}` (initial `H^k` state distance and harmonic defect),
`𝒴 = resB + resD`, `S` = the state/curvature/stress distance, and the selection row `g` is the
finite-action row norm `(h⁴Σ_{Q'}‖E_h^raw‖²)^{1/2}` of `eq:native-sigma`.

* **`native_selected_closure_records`** — one cutoff, constants uniform in the cutoff and the
  records: the failure probability is at most `eq:source-selection-failure`, and on every successful
  outcome the selected record satisfies
  `‖𝒰 - 𝒰_*‖_{C_tH^k} + ‖Riem‖_{L²H^{k-1}} + ‖T^{SM}‖_{L²H^k} ≤ C_*(α + C₁e(k+1)!F̄_{h,k})`
  (`eq:selected-closure`, `F̄` the composed budget `eq:selected-composed-budget`), provided
  `α + C₁e(k+1)!F̄_{h,k} ≤ d_*`, `hK ≤ c_res` and `T_{h,k+2} ≤ τ_*`.

Legality of the records (`LegalRec`): the chart/amplitude conditions of `thm:native-source` and the
tuple hypotheses of the dilated reconstruction (adapted Lorentz gauge, temporal internal gauge,
physical co-spinors, chart margin).
-/

open MeasureTheory Filter Topology Set Finset
open scoped Real Nat

namespace RenewalGeometry.RecordTuple

open DiscreteEulerConsistency (R4)
open NativeScaling (Mat)
open ShiftedJetAction (Grid)
open NativeDensity DiscreteEulerConsistency NativeModel SlabData ActualJetState
  ActualJetCompleteForcing ActualJetBridge CoupledBootstrap ActualJetSmooth SourceSelection
open TrigInterp (recon reconLow tau)
open NativeRate (eps0 forcingBudget)

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]
variable {m : ℕ} (M : SlabModel 𝔄 𝓗 𝓢 m)

open Classical in
/-- **The finite-action row norm** `σ(u) = (h⁴ Σ_{x ∈ Q'} ‖E_h^raw(u)(x) ∘ physF πg‖²)^{1/2}` of a
record on the buffered slab `Q' = [t₀ - b, t₁ + b) × 𝕋³` (`eq:native-sigma`; the raw rows on the
physical directions, gauge directions in the gauge Lie algebra `𝔤`). -/
def rowNorm (t₀ t₁ b : ℝ) (n : ℕ) [NeZero n] (u : Grid n → Field 𝔄 𝓗 𝓢) : ℝ :=
  Real.sqrt ((2 * π / n) ^ 4 * ∑ x ∈ Finset.univ.filter
      (fun x : Grid n => pos (2 * π / n) x ∈ NativeZeroSource.bufSlab (t₀ - b) (t₁ + b)),
      ‖(eulerRow (localAction M.toData (2 * π / n)) (2 * π / n) u x).comp
        (NativeTail.physF M.πg)‖ ^ 2)

theorem rowNorm_nonneg (t₀ t₁ b : ℝ) (n : ℕ) [NeZero n] (u : Grid n → Field 𝔄 𝓗 𝓢) :
    0 ≤ rowNorm M t₀ t₁ b n u := Real.sqrt_nonneg _

open Classical in
theorem sq_le_of_rowNorm_le {t₀ t₁ b : ℝ} {n : ℕ} [NeZero n] {u : Grid n → Field 𝔄 𝓗 𝓢}
    {s : ℝ} (h : rowNorm M t₀ t₁ b n u ≤ s) :
    (2 * π / n) ^ 4 * ∑ x ∈ Finset.univ.filter
      (fun x : Grid n => pos (2 * π / n) x ∈ NativeZeroSource.bufSlab (t₀ - b) (t₁ + b)),
      ‖(eulerRow (localAction M.toData (2 * π / n)) (2 * π / n) u x).comp
        (NativeTail.physF M.πg)‖ ^ 2 ≤ s ^ 2 := by
  have h0 : 0 ≤ (2 * π / n) ^ 4 * ∑ x ∈ Finset.univ.filter
      (fun x : Grid n => pos (2 * π / n) x ∈ NativeZeroSource.bufSlab (t₀ - b) (t₁ + b)),
      ‖(eulerRow (localAction M.toData (2 * π / n)) (2 * π / n) u x).comp
        (NativeTail.physF M.πg)‖ ^ 2 :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [← Real.sq_sqrt h0]
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2

/-- **Legal records** (the chart, amplitude and tuple conditions of `thm:native-source` and of
the actual-tuple map). -/
structure LegalRec (δ : ℝ) (Ke : Set Mat) (A t₀ : ℝ) (n : ℕ) [NeZero n]
    (u : Grid n → Field 𝔄 𝓗 𝓢) (K : ℝ) : Prop where
  low_chart : ∀ x, (reconLow n K u x).1 ∈ Ke
  low_amp : ∀ x, ‖reconLow n K u x‖ ≤ A
  chart : ∀ x, (recon n u x).1 ∈ Ke
  amp : ∀ x, ‖recon n u x‖ ≤ A
  tuple : TupleHyp M δ (dilField t₀ (recon n u))

/-- The slab model of the native slab data (abbreviation). -/
abbrev nSlab {δ : ℝ} (hδ : 0 < δ) {nX na nb : ℕ}
    (eX : (Fin nX → ℝ) ≃L[ℝ] StateP m (HSp M) 𝓢 (CoSpinor 𝓢))
    (eY : (Fin na → ℝ) ≃L[ℝ] BosP m (HSp M)) (eYD : (Fin nb → ℝ) ≃L[ℝ] 𝓢 × CoSpinor 𝓢)
    (k : ℕ) {t₀ t₁ : ℝ} (h01 : t₀ < t₁) :=
  slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁) (slabT_pos h01)

/-- **`thm:native-selected-closure`** (`eq:selected-closure` and the failure bound) for native
records at one cutoff, with `prop:coupled-bootstrap` and `thm:native-source` discharged. -/
theorem native_selected_closure_records {δ : ℝ} (hδ : 0 < δ) {nX na nb : ℕ}
    (eX : (Fin nX → ℝ) ≃L[ℝ] StateP m (HSp M) 𝓢 (CoSpinor 𝓢))
    (eY : (Fin na → ℝ) ≃L[ℝ] BosP m (HSp M)) (eYD : (Fin nb → ℝ) ≃L[ℝ] 𝓢 × CoSpinor 𝓢)
    (hAsym : ∀ j a b v, Aco (toSMData M δ) eX j a b v = Aco (toSMData M δ) eX j b a v)
    {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det) (A : ℝ) {k : ℕ}
    (hk : 4 ≤ k) {Ck : ℝ} (hCk : 0 < Ck) {t₀ t₁ b : ℝ} (hb : 0 < b) (h0 : b < t₀)
    (h1 : t₁ + b ≤ 2 * π) (h01 : t₀ < t₁) {Kr : Set (Fin nX → ℝ)} (hKr : IsCompact Kr)
    (hKO : Kr ⊆ chartC eX) {R₁ : ℝ} (hR₁ : 0 ≤ R₁) :
    ∃ C₁ cr τs Cst dst : ℝ, 0 ≤ C₁ ∧ 0 < cr ∧ 0 < τs ∧ 0 ≤ Cst ∧ 0 < dst ∧
    ∀ zs ∈ refSet (toSMData M δ) eX k (slabT t₀ t₁) Kr R₁,
    ∀ (n : ℕ) [NeZero n], Odd n →
    ∀ {Ω 𝒳 : Type} [Fintype Ω] [Fintype 𝒳] [DecidableEq 𝒳] [DecidableEq Ω]
      (proc : FiniteAcceptedProcess Ω 𝒳) (rec : 𝒳 → Grid n → Field 𝔄 𝓗 𝓢) (K : ℝ),
      1 ≤ K → 2 * π / n * K ≤ cr → (∀ x, LegalRec M δ Ke A t₀ n (rec x) K) →
    ∀ (a V : 𝒳 → ℝ) (rr : ℕ → 𝒳 → ℝ) {Am Ap κ δs sh Rr α : ℝ},
      (∀ x, Am ≤ a x ∧ a x ≤ Ap) → 0 < κ → 0 < δs → 0 < sh → 0 < Rr → 0 < α →
      (∀ x, 0 ≤ V x) → ∀ (J : ℕ), 0 < J →
      (∀ j < J, ∀ x, 0 < proc.survivingMass j x →
        proc.actionDrift a j x ≤
          -(κ * δs) * rowNorm M t₀ t₁ b n (rec x) ^ 2 + δs * rr j x) →
    ∀ (sel : Ω → ℕ),
      (∀ ω ∈ proc.S J, sel ω < J ∧ ∀ j < J,
        FiniteAcceptedProcess.score (fun x => rowNorm M t₀ t₁ b n (rec x)) V
          (fun x => (‖(nSlab M hδ eX eY eYD k h01).init (recTuple M hδ t₀ n (rec x) zs) -
            (nSlab M hδ eX eY eYD k h01).init zs‖ +
            (nSlab M hδ eX eY eYD k h01).harm (recTuple M hδ t₀ n (rec x) zs)) ^ 2)
          sh Rr α (proc.X (sel ω) ω) ≤
        FiniteAcceptedProcess.score (fun x => rowNorm M t₀ t₁ b n (rec x)) V
          (fun x => (‖(nSlab M hδ eX eY eYD k h01).init (recTuple M hδ t₀ n (rec x) zs) -
            (nSlab M hδ eX eY eYD k h01).init zs‖ +
            (nSlab M hδ eX eY eYD k h01).harm (recTuple M hδ t₀ n (rec x) zs)) ^ 2)
          sh Rr α (proc.X j ω)) →
    ∀ {t₂ c₂ tm cm : ℝ}, 0 ≤ c₂ → 0 ≤ cm →
      (∀ x, tau n K 2 (rec x) ≤ t₂ + c₂ * Real.sqrt (V x)) →
      (∀ x, tau n K (k + 2) (rec x) ≤ tm + cm * Real.sqrt (V x)) →
      tm + cm * Rr ≤ τs →
      α + C₁ * (Real.exp 1 * (k + 1)! *
        forcingBudget k Ck sh (2 * π / n) K (t₂ + c₂ * Rr) (tm + cm * Rr)) ≤ dst →
    (∑ ω ∈ Finset.univ.filter (fun ω => ω ∉ proc.S J ∨
        ¬ (rowNorm M t₀ t₁ b n (rec (proc.X (sel ω) ω)) ≤ sh ∧
          V (proc.X (sel ω) ω) ≤ Rr ^ 2 ∧
          (‖(nSlab M hδ eX eY eYD k h01).init (recTuple M hδ t₀ n (rec (proc.X (sel ω) ω)) zs) -
            (nSlab M hδ eX eY eYD k h01).init zs‖ +
            (nSlab M hδ eX eY eYD k h01).harm
              (recTuple M hδ t₀ n (rec (proc.X (sel ω) ω)) zs)) ^ 2 ≤ α ^ 2)), proc.P ω
      ≤ proc.exitProbability J + (Ap - Am) / (κ * δs * J * sh ^ 2)
        + proc.occupation J rr / (κ * sh ^ 2)
        + proc.occupation J (fun _ x => V x) / Rr ^ 2
        + proc.occupation J (fun _ x =>
            (‖(nSlab M hδ eX eY eYD k h01).init (recTuple M hδ t₀ n (rec x) zs) -
              (nSlab M hδ eX eY eYD k h01).init zs‖ +
              (nSlab M hδ eX eY eYD k h01).harm (recTuple M hδ t₀ n (rec x) zs)) ^ 2) / α ^ 2) ∧
    ∀ ω ∈ proc.S J, rowNorm M t₀ t₁ b n (rec (proc.X (sel ω) ω)) ≤ sh →
      V (proc.X (sel ω) ω) ≤ Rr ^ 2 →
      (‖(nSlab M hδ eX eY eYD k h01).init (recTuple M hδ t₀ n (rec (proc.X (sel ω) ω)) zs) -
          (nSlab M hδ eX eY eYD k h01).init zs‖ +
        (nSlab M hδ eX eY eYD k h01).harm
          (recTuple M hδ t₀ n (rec (proc.X (sel ω) ω)) zs)) ^ 2 ≤ α ^ 2 →
      dist ((nSlab M hδ eX eY eYD k h01).obs (recTuple M hδ t₀ n (rec (proc.X (sel ω) ω)) zs))
          ((nSlab M hδ eX eY eYD k h01).obs zs) ≤
        Cst * (α + C₁ * (Real.exp 1 * (k + 1)! *
          forcingBudget k Ck sh (2 * π / n) K (t₂ + c₂ * Rr) (tm + cm * Rr))) := by
  obtain ⟨C₁, cr, τs, hC₁, hcr, hτs, hsrc⟩ :=
    native_source_tuple M hδ eY eYD hKe hdet A k (by omega) hCk hb h0 h1 h01.le
  obtain ⟨dst, Cst, hdst, hCst, hconc⟩ := coupled_bootstrap (toSMData M δ) eX eY eYD
    (toSMData_smooth M hδ) hAsym hk (slabT_pos h01) hKr hKO hR₁
  refine ⟨C₁, cr, τs, Cst, dst, hC₁, hcr, hτs, hCst, hdst, ?_⟩
  intro zs hzs n _ hn Ω 𝒳 _ _ _ _ proc rec K hK hres hleg a V rr Am Ap κ δs sh Rr α ha hκ hδs
    hsh hRr hα hV J hJ hdrift sel hsel t₂ c₂ tm cm hc₂ hcm hr₂ hrm hT hsmall
  set S := nSlab M hδ eX eY eYD k h01 with hS
  set Z : 𝒳 → STuple M := fun x => recTuple M hδ t₀ n (rec x) zs with hZ
  set al : 𝒳 → ℝ := fun x => ‖S.init (Z x) - S.init zs‖ + S.harm (Z x) with hal_def
  have hal : ∀ x, 0 ≤ al x := fun x => add_nonneg (norm_nonneg _) (S.harm_nonneg _)
  set g : 𝒳 → ℝ := fun x => rowNorm M t₀ t₁ b n (rec x) with hg_def
  set Ysrc : 𝒳 → ℝ := fun x => if V x ≤ Rr ^ 2 then S.resB (Z x) + S.resD (Z x) else 0
    with hY_def
  set Sx : 𝒳 → ℝ := fun x => if V x ≤ Rr ^ 2 then dist (S.obs (Z x)) (S.obs zs) else 0
    with hSx_def
  have hK0 : 0 < K := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hh : 0 < 2 * π / n := by positivity
  have hτ₂0 : ∀ x, 0 ≤ tau n K 2 (rec x) := fun x => TrigInterp.tau_nonneg n hK0 _ _
  have hτm0 : ∀ x, 0 ≤ tau n K (k + 2) (rec x) := fun x => TrigInterp.tau_nonneg n hK0 _ _
  have hsrc' : ∀ x, g x ≤ sh → Ysrc x ≤
      C₁ * forcingBudget k Ck sh (2 * π / n) K (tau n K 2 (rec x)) (tau n K (k + 2) (rec x)) := by
    intro x hgx
    by_cases hVx : V x ≤ Rr ^ 2
    · simp only [hY_def, if_pos hVx, hZ]
      rw [recTuple_eq M hδ t₀ zs (hleg x).tuple]
      have hτx : tau n K (k + 2) (rec x) ≤ τs :=
        (SelectedClosure.reader_tail_le hcm hRr.le (hrm x) hVx).trans hT
      exact hsrc n hn (rec x) K sh hK hres hτx (hleg x).low_chart (hleg x).low_amp
        (hleg x).chart (hleg x).amp hsh.le (sq_le_of_rowNorm_le M hgx) (hleg x).tuple
    · simp only [hY_def, if_neg hVx]
      exact mul_nonneg hC₁ (SourceCompare.forcingBudget_nonneg k hCk.le hsh.le hh.le hK
        (hτ₂0 x) (hτm0 x))
  have hboot : ∀ x, al x + Ysrc x ≤ dst → Sx x ≤ Cst * (al x + Ysrc x) := by
    intro x hx
    by_cases hVx : V x ≤ Rr ^ 2
    · simp only [hSx_def, hY_def, if_pos hVx] at hx ⊢
      have hmis : S.mismatch (Z x) zs = al x + (S.resB (Z x) + S.resD (Z x)) := by
        unfold AposterioriShadow.SlabModel.mismatch; simp only [hal_def]; ring
      have := hconc zs hzs (Z x) trivial (by rw [hmis]; exact hx)
      rwa [hmis] at this
    · simp only [hSx_def, hY_def, if_neg hVx, add_zero]
      exact mul_nonneg hCst (hal x)
  have H := SelectedClosure.native_selected_closure proc a g V (fun x => al x ^ 2) rr ha hκ hδs
    hsh hRr hα (fun x => rowNorm_nonneg M _ _ _ _ _) hV J hJ hdrift sel hsel al hal
    (fun x => rfl) k (fun x => tau n K 2 (rec x)) (fun x => tau n K (k + 2) (rec x)) hτ₂0 hτm0
    hc₂ hcm hr₂ hrm Ysrc hCk.le hh hK0 hC₁ hsrc' Sx hCst hboot hsmall
  refine ⟨H.1, fun ω hω hgx hVx hWx => ?_⟩
  have := H.2 ω hω hgx hVx hWx
  simp only [hSx_def, if_pos hVx] at this
  exact this

end

end RenewalGeometry.RecordTuple

/-! ### `thm:native-source` with selected upper budgets, physical rows -/

namespace RenewalGeometry.SelectedNativeSource

open ShiftedJetAction (Grid unitVec stencil action)
open NativeScaling (Mat eta metric readerOmega omegaLink)
open ShiftedPlaquette NativeDensity DiscreteEulerConsistency NativeEulerConsistency NativeTail
open TrigInterp (recon reconLow tau)
open NativeRate (eps0 forcingBudget)
open NativeSourceThm

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)
variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]

open Classical in
/-- **`thm:native-source` with the selected upper budgets, physical rows** (source step of
`thm:native-selected-closure`, gauge rows in `𝔤` through `P_𝔤`; for a slab model `P_𝔤 = πg`).
As `SelectedNativeSource.selected_native_source`, with the selected row bound
`s_h ≥ ‖E_h^raw(u_h) ∘ physF P_𝔤‖_{0,h;Q'}` and the physical residual `𝓡_B^𝔤`: the zero-order
residual is `≤ C(s_h + hK³)`, the strong source is `≤ C e(k+1)! F̄_{h,k}`, the literal Cartan
discrepancy is `≤ C h K³`. -/
theorem selected_native_source_phys (Pg : 𝔄 →L[ℝ] 𝔄) {Ke : Set Mat} (hKe : IsCompact Ke)
    (hdet : ∀ e ∈ Ke, 0 < e.det) (A : ℝ) (k : ℕ) (hk : 1 ≤ k) {Ck : ℝ} (hCk : 0 < Ck)
    {t₀ t₁ δ : ℝ} (hδ : 0 < δ) (h0 : δ < t₀) (h1 : t₁ + δ ≤ 2 * π) :
    ∃ C c_res τs : ℝ, 0 ≤ C ∧ 0 < c_res ∧ 0 < τs ∧ ∀ (n : ℕ) [NeZero n], Odd n →
      ∀ (u : Grid n → Field 𝔄 𝓗 𝓢) (K sh T₂ Tm : ℝ), 1 ≤ K → (2 * π / n) * K ≤ c_res →
      Tm ≤ τs → tau n K 2 u ≤ T₂ → tau n K (k + 2) u ≤ Tm →
      (∀ x, (reconLow n K u x).1 ∈ Ke) → (∀ x, ‖reconLow n K u x‖ ≤ A) →
      (∀ x, (recon n u x).1 ∈ Ke) → (∀ x, ‖recon n u x‖ ≤ A) → 0 ≤ sh →
      (2 * π / n) ^ 4 * ∑ x ∈ Finset.univ.filter
          (fun x : Grid n => pos (2 * π / n) x ∈ NativeZeroSource.bufSlab (t₀ - δ) (t₁ + δ)),
          ‖(eulerRow (localAction D (2 * π / n)) (2 * π / n) u x).comp (physF Pg)‖ ^ 2 ≤ sh ^ 2 →
      (sobX 0 (NativeSlab.slab t₀ t₁) (RBP D Pg (recon n u)) +
          sobX 0 (NativeSlab.slab t₀ t₁) (RD D (recon n u)) ≤ C * eps0 sh (2 * π / n) K) ∧
      (sobX k (NativeSlab.slab t₀ t₁) (RBP D Pg (recon n u)) +
          sobX (k + 1) (NativeSlab.slab t₀ t₁) (RD D (recon n u)) ≤
        C * (Real.exp 1 * (k + 1)! * forcingBudget k Ck sh (2 * π / n) K T₂ Tm)) ∧
      (∀ (x : Grid n) (z : R4), ‖z - pos (2 * π / n) x‖ ≤ 2 * π / n → ∀ μ ν : Fin 4,
        ‖cartanCurvature (2 * π / n) (coframe u) x μ ν -
          matToOp ((recon n u z).1 * riemMat (fun z => (recon n u z).1) z μ ν *
            ((recon n u z).1)⁻¹)‖ ≤ C * (2 * π / n) * K ^ 3) := by
  obtain ⟨C, c_res, τs, hC, hc, hτs, hmain⟩ := native_source_phys D Pg hKe hdet A k hk hCk hδ h0 h1
  refine ⟨C, c_res, τs, hC, hc, hτs, ?_⟩
  intro n _ hn u K sh T₂ Tm hK hhK hTm hτ₂ hτm hKel hAl hKef hAf hsh hσ
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hh : 0 < 2 * π / n := div_pos Real.two_pi_pos hn0
  have hK0 : 0 < K := by linarith
  obtain ⟨hz, hs, hcart⟩ := hmain n hn u K sh hK hhK (hτm.trans hTm) hKel hAl hKef hAf hsh hσ
  refine ⟨hz, hs.trans (mul_le_mul_of_nonneg_left ?_ hC), hcart⟩
  exact SelectedClosure.forcingBudget_le_of_le k hCk.le hsh hh hK0
    (TrigInterp.tau_nonneg n hK0 _ u) hτ₂ (TrigInterp.tau_nonneg n hK0 _ u) hτm

end

end RenewalGeometry.SelectedNativeSource
