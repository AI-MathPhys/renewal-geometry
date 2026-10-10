/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeSlabSymmetric
import RenewalGeometry.Continuum.NativeRefSetNonempty
import RenewalGeometry.Continuum.NativeSelectedPolynomial

/-!
# `thm:native-closure`, `cor:native-rate`, `thm:native-selected-closure` without the symmetry
  hypothesis

Einstein–Standard-Model action-closure manuscript, `thm:native-closure` (`eq:native-geometry`),
`cor:native-rate` (`eq:native-example-rate`, dyadic summability), `thm:native-selected-closure`
(`eq:selected-closure`) and `cor:selected-polynomial` (record form).

The closed native-record theorems of `NativeClosureClosed`, `NativeRateClosed`,
`NativeSelectedClosed` and `NativeSelectedPolynomial` carried the symmetric-hyperbolic coordinate
condition `hAsym` of `prop:coupled-bootstrap` (the principal matrices `Aco (toSMData M δ) eX` are
symmetric in the state coordinates `eX`) as a hypothesis on arbitrary coordinates `eX`.  Here the
state coordinates are the **fixed orthonormal coordinates** `SlabSymmetric.slabX M` of the
positive block inner product of unitary block forms of the slab data (the paper's "fixed positive
component norm"; Frobenius form on `gl(m)`, a positive Higgs form, Clifford-unitary spinor forms,
`SlabSymmetric.slabX_orth`), in which the principal matrices are symmetric for every margin `δ`
(`SlabSymmetric.slabX_symm`, from `CoupledBootstrap.Aco_symm` and the Clifford unitarity of the
slab Clifford frame).  All statements below are therefore free of `hAsym`:

* `native_closure_unconditional` — `thm:native-closure` (`eq:native-geometry`);
* `native_rate_unconditional`, `native_closure_isBigO_unconditional`,
  `native_rate_example_unconditional`, `native_rate_dyadic_unconditional` — `cor:native-rate`;
* `native_selected_closure_records_unconditional`, `selected_record_bound_unconditional` —
  `thm:native-selected-closure`;
* `selected_polynomial_record_unconditional` — `cor:selected-polynomial` (record form).

Non-vacuity of the reference class: `RefSetNonempty.refSet_nonempty_slab` (flat vacuum, any slab
model with `Λ + κλ_Hv_H⁴ = 0`, in the coordinates `slabX`) and
`RefSetNonempty.refSet_nonempty_diracSlab`; see `refSet_nonempty_unconditional` below.

The other disclosures of `thm:native-closure` are unchanged (`Σ = 𝕋³`, adapted Lorentz gauge at
the nodes, `SlabModel` hypotheses, smoothed frame with margin `δ`, dyadic meshes rendered as
`h_j ≍ 2^{-j}`).
-/

open MeasureTheory Filter Topology Set Finset Asymptotics
open scoped Real Nat ENNReal

namespace RenewalGeometry.ClosureUnconditional

open DiscreteEulerConsistency (R4)
open NativeScaling (Mat)
open ShiftedJetAction (Grid)
open NativeDensity DiscreteEulerConsistency NativeModel SlabData ActualJetState
  ActualJetCompleteForcing ActualJetBridge CoupledBootstrap ActualJetSmooth SourceSelection
  RecordTuple SlabSymmetric
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

/-- **`thm:native-closure`** (`eq:native-geometry`) for native records. Unconditional form: the state coordinates are the fixed orthonormal coordinates `slabX M` of the positive block inner product, in which the principal matrices are symmetric (`slabX_symm`), so no symmetry hypothesis is assumed. -/
theorem native_closure_unconditional {δ : ℝ} (hδ : 0 < δ) {na nb : ℕ}
    (eY : (Fin na → ℝ) ≃L[ℝ] BosP m (HSp M)) (eYD : (Fin nb → ℝ) ≃L[ℝ] 𝓢 × CoSpinor 𝓢)
    {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det) (A : ℝ) {k : ℕ}
    (hk : 4 ≤ k) {Ck : ℝ} (hCk : 0 < Ck) {t₀ t₁ b : ℝ} (hb : 0 < b) (h0 : b < t₀)
    (h1 : t₁ + b ≤ 2 * π) (h01 : t₀ < t₁) {Kr : Set (Fin (ActualJetKato.dimS m (HSp M) 𝓢 (CoSpinor 𝓢)) → ℝ)} (hKr : IsCompact Kr)
    (hKO : Kr ⊆ chartC (slabX M)) {R₁ : ℝ} (hR₁ : 0 ≤ R₁) :
    ∃ C τs : ℝ, 0 ≤ C ∧ 0 < τs ∧ ∀ {ι : Type} (l : Filter ι) (N : ι → ℕ) [∀ i, NeZero (N i)]
      (u : ∀ i, Grid (N i) → Field 𝔄 𝓗 𝓢) (K σ : ι → ℝ),
      ∀ zs ∈ refSet (toSMData M δ) (slabX M) k (slabT t₀ t₁) Kr R₁,
      (∀ᶠ i in l, RecordHyp M δ Ke A t₀ t₁ b (N i) (u i) (K i) (σ i)) →
      Tendsto (fun i => 2 * π / N i * K i) l (𝓝 0) →
      (∀ᶠ i in l, tau (N i) (K i) (k + 2) (u i) ≤ τs) →
      Tendsto (fun i =>
        ‖(slabModel (toSMData M δ) (slabX M) eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).init (recTuple M hδ t₀ (N i) (u i) zs) -
          (slabModel (toSMData M δ) (slabX M) eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).init zs‖ +
        (slabModel (toSMData M δ) (slabX M) eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).harm (recTuple M hδ t₀ (N i) (u i) zs) +
        forcingBudget k Ck (σ i) (2 * π / N i) (K i) (tau (N i) (K i) 2 (u i))
          (tau (N i) (K i) (k + 2) (u i))) l (𝓝 0) →
      ∀ᶠ i in l, dist ((slabModel (toSMData M δ) (slabX M) eY eYD (toSMData_smooth M hδ) k
            (slabT t₀ t₁) (slabT_pos h01)).obs (recTuple M hδ t₀ (N i) (u i) zs))
          ((slabModel (toSMData M δ) (slabX M) eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).obs zs) ≤
        C * (‖(slabModel (toSMData M δ) (slabX M) eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).init (recTuple M hδ t₀ (N i) (u i) zs) -
          (slabModel (toSMData M δ) (slabX M) eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).init zs‖ +
        (slabModel (toSMData M δ) (slabX M) eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).harm (recTuple M hδ t₀ (N i) (u i) zs) +
        forcingBudget k Ck (σ i) (2 * π / N i) (K i) (tau (N i) (K i) 2 (u i))
          (tau (N i) (K i) (k + 2) (u i))) :=
  RecordTuple.native_closure M hδ (slabX M) eY eYD (slabX_symm M δ) hKe hdet A hk hCk hb h0 h1
    h01 hKr hKO hR₁

/-- **`cor:native-rate`** for native records (state, curvature and stress rate): with
`h = 2π/n → 0⁺`, `σ_h ≤ C_σh`, `1 ≤ K_h ≤ c₂h^{-β}`, `0 ≤ β < 1/(k+4)`, `eq:native-tail-rate`
`τ_{h,2} ≤ C_τhK_h`, `τ_{h,k+2} ≤ C_τhK_h²`, the hypotheses of `thm:native-source` on the records
and `i_{h,k} + γ_{h,k} = O(h^{1-β(k+4)}(1+|log h|)^{k+1})`, the state, curvature and Standard-Model
stress distances are `O(h^{1-β(k+4)}(1+|log h|)^{k+1})`.  The resolution `hK_h ≤ c_res` and the tail
threshold `τ_{h,k+2} ≤ τ_*` of `thm:native-source` are consequences of the rate hypotheses. Unconditional form: the state coordinates are the fixed orthonormal coordinates `slabX M` of the positive block inner product, in which the principal matrices are symmetric (`slabX_symm`), so no symmetry hypothesis is assumed. -/
theorem native_rate_unconditional {δ : ℝ} (hδ : 0 < δ) {na nb : ℕ}
    (eY : (Fin na → ℝ) ≃L[ℝ] BosP m (HSp M)) (eYD : (Fin nb → ℝ) ≃L[ℝ] 𝓢 × CoSpinor 𝓢)
    {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det) (A : ℝ) {k : ℕ}
    (hk : 4 ≤ k) {Ck : ℝ} (hCk : 0 < Ck) {t₀ t₁ b : ℝ} (hb : 0 < b) (h0 : b < t₀)
    (h1 : t₁ + b ≤ 2 * π) (h01 : t₀ < t₁) {Kr : Set (Fin (ActualJetKato.dimS m (HSp M) 𝓢 (CoSpinor 𝓢)) → ℝ)} (hKr : IsCompact Kr)
    (hKO : Kr ⊆ chartC (slabX M)) {R₁ : ℝ} (hR₁ : 0 ≤ R₁) {β c₂ Cσ Cτ : ℝ} (hβ : 0 ≤ β)
    (hβk : β < 1 / (k + 4)) (hCσ : 0 ≤ Cσ) :
    ∀ {ι : Type} (l : Filter ι) (N : ι → ℕ) [∀ i, NeZero (N i)]
      (u : ∀ i, Grid (N i) → Field 𝔄 𝓗 𝓢) (K σ : ι → ℝ),
      ∀ zs ∈ refSet (toSMData M δ) (slabX M) k (slabT t₀ t₁) Kr R₁,
      Tendsto (fun i => 2 * π / N i) l (𝓝[>] 0) →
      (∀ᶠ i in l, RecordHyp M δ Ke A t₀ t₁ b (N i) (u i) (K i) (σ i) ∧
        K i ≤ c₂ * (2 * π / N i) ^ (-β) ∧ σ i ≤ Cσ * (2 * π / N i) ∧
        tau (N i) (K i) 2 (u i) ≤ Cτ * (2 * π / N i * K i) ∧
        tau (N i) (K i) (k + 2) (u i) ≤ Cτ * (2 * π / N i * K i ^ 2)) →
      (fun i =>
        ‖(slabModel (toSMData M δ) (slabX M) eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).init (recTuple M hδ t₀ (N i) (u i) zs) -
          (slabModel (toSMData M δ) (slabX M) eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).init zs‖ +
        (slabModel (toSMData M δ) (slabX M) eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).harm (recTuple M hδ t₀ (N i) (u i) zs)) =O[l]
        (fun i => (2 * π / N i) ^ (1 - β * (k + 4)) *
          (1 + |Real.log (2 * π / N i)|) ^ (k + 1)) →
      (fun i => dist ((slabModel (toSMData M δ) (slabX M) eY eYD (toSMData_smooth M hδ) k
            (slabT t₀ t₁) (slabT_pos h01)).obs (recTuple M hδ t₀ (N i) (u i) zs))
          ((slabModel (toSMData M δ) (slabX M) eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).obs zs)) =O[l]
        (fun i => (2 * π / N i) ^ (1 - β * (k + 4)) *
          (1 + |Real.log (2 * π / N i)|) ^ (k + 1)) :=
  RecordTuple.native_rate M hδ (slabX M) eY eYD (slabX_symm M δ) hKe hdet A hk hCk hb h0 h1 h01
    hKr hKO hR₁ hβ hβk hCσ

/-- **Rates are inherited** (`thm:native-closure` in `O`-form): if `g → 0`,
`i_{h,k} + γ_{h,k} = O(g)` and `F_{h,k} = O(g)`, the state, curvature and stress distances are
`O(g)`. Unconditional form: the state coordinates are the fixed orthonormal coordinates `slabX M` of the positive block inner product, in which the principal matrices are symmetric (`slabX_symm`), so no symmetry hypothesis is assumed. -/
theorem native_closure_isBigO_unconditional {δ : ℝ} (hδ : 0 < δ) {na nb : ℕ}
    (eY : (Fin na → ℝ) ≃L[ℝ] BosP m (HSp M)) (eYD : (Fin nb → ℝ) ≃L[ℝ] 𝓢 × CoSpinor 𝓢)
    {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det) (A : ℝ) {k : ℕ}
    (hk : 4 ≤ k) {Ck : ℝ} (hCk : 0 < Ck) {t₀ t₁ b : ℝ} (hb : 0 < b) (h0 : b < t₀)
    (h1 : t₁ + b ≤ 2 * π) (h01 : t₀ < t₁) {Kr : Set (Fin (ActualJetKato.dimS m (HSp M) 𝓢 (CoSpinor 𝓢)) → ℝ)} (hKr : IsCompact Kr)
    (hKO : Kr ⊆ chartC (slabX M)) {R₁ : ℝ} (hR₁ : 0 ≤ R₁) :
    ∃ τs : ℝ, 0 < τs ∧ ∀ {ι : Type} (l : Filter ι) (N : ι → ℕ) [∀ i, NeZero (N i)]
      (u : ∀ i, Grid (N i) → Field 𝔄 𝓗 𝓢) (K σ g : ι → ℝ),
      ∀ zs ∈ refSet (toSMData M δ) (slabX M) k (slabT t₀ t₁) Kr R₁,
      (∀ᶠ i in l, RecordHyp M δ Ke A t₀ t₁ b (N i) (u i) (K i) (σ i)) →
      Tendsto (fun i => 2 * π / N i * K i) l (𝓝 0) →
      (∀ᶠ i in l, tau (N i) (K i) (k + 2) (u i) ≤ τs) →
      Tendsto g l (𝓝 0) →
      (fun i =>
        ‖(slabModel (toSMData M δ) (slabX M) eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).init (recTuple M hδ t₀ (N i) (u i) zs) -
          (slabModel (toSMData M δ) (slabX M) eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).init zs‖ +
        (slabModel (toSMData M δ) (slabX M) eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).harm (recTuple M hδ t₀ (N i) (u i) zs)) =O[l] g →
      (fun i => forcingBudget k Ck (σ i) (2 * π / N i) (K i) (tau (N i) (K i) 2 (u i))
          (tau (N i) (K i) (k + 2) (u i))) =O[l] g →
      (fun i => dist ((slabModel (toSMData M δ) (slabX M) eY eYD (toSMData_smooth M hδ) k
            (slabT t₀ t₁) (slabT_pos h01)).obs (recTuple M hδ t₀ (N i) (u i) zs))
          ((slabModel (toSMData M δ) (slabX M) eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).obs zs)) =O[l] g :=
  RecordTuple.native_closure_isBigO M hδ (slabX M) eY eYD (slabX_symm M δ) hKe hdet A hk hCk hb
    h0 h1 h01 hKr hKO hR₁

/-- **`eq:native-example-rate`**: `k = 4`, `1 ≤ K_h ≤ c₂h^{-1/18}`, `σ_h ≤ C_σh`,
`eq:native-tail-rate` and `i_{h,4} + γ_{h,4} = O(h^{1/2})` give `O(h^{1/2})` state, curvature and
Standard-Model stress convergence. Unconditional form: the state coordinates are the fixed orthonormal coordinates `slabX M` of the positive block inner product, in which the principal matrices are symmetric (`slabX_symm`), so no symmetry hypothesis is assumed. -/
theorem native_rate_example_unconditional {δ : ℝ} (hδ : 0 < δ) {na nb : ℕ}
    (eY : (Fin na → ℝ) ≃L[ℝ] BosP m (HSp M)) (eYD : (Fin nb → ℝ) ≃L[ℝ] 𝓢 × CoSpinor 𝓢)
    {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det) (A : ℝ)
    {Ck : ℝ} (hCk : 0 < Ck) {t₀ t₁ b : ℝ} (hb : 0 < b) (h0 : b < t₀)
    (h1 : t₁ + b ≤ 2 * π) (h01 : t₀ < t₁) {Kr : Set (Fin (ActualJetKato.dimS m (HSp M) 𝓢 (CoSpinor 𝓢)) → ℝ)} (hKr : IsCompact Kr)
    (hKO : Kr ⊆ chartC (slabX M)) {R₁ : ℝ} (hR₁ : 0 ≤ R₁) {c₂ Cσ Cτ : ℝ} (hCσ : 0 ≤ Cσ) :
    ∀ {ι : Type} (l : Filter ι) (N : ι → ℕ) [∀ i, NeZero (N i)]
      (u : ∀ i, Grid (N i) → Field 𝔄 𝓗 𝓢) (K σ : ι → ℝ),
      ∀ zs ∈ refSet (toSMData M δ) (slabX M) 4 (slabT t₀ t₁) Kr R₁,
      Tendsto (fun i => 2 * π / N i) l (𝓝[>] 0) →
      (∀ᶠ i in l, RecordHyp M δ Ke A t₀ t₁ b (N i) (u i) (K i) (σ i) ∧
        K i ≤ c₂ * (2 * π / N i) ^ (-(1 / 18 : ℝ)) ∧ σ i ≤ Cσ * (2 * π / N i) ∧
        tau (N i) (K i) 2 (u i) ≤ Cτ * (2 * π / N i * K i) ∧
        tau (N i) (K i) (4 + 2) (u i) ≤ Cτ * (2 * π / N i * K i ^ 2)) →
      (fun i =>
        ‖(slabModel (toSMData M δ) (slabX M) eY eYD (toSMData_smooth M hδ) 4 (slabT t₀ t₁)
            (slabT_pos h01)).init (recTuple M hδ t₀ (N i) (u i) zs) -
          (slabModel (toSMData M δ) (slabX M) eY eYD (toSMData_smooth M hδ) 4 (slabT t₀ t₁)
            (slabT_pos h01)).init zs‖ +
        (slabModel (toSMData M δ) (slabX M) eY eYD (toSMData_smooth M hδ) 4 (slabT t₀ t₁)
            (slabT_pos h01)).harm (recTuple M hδ t₀ (N i) (u i) zs)) =O[l]
        (fun i => (2 * π / N i) ^ (1 / 2 : ℝ)) →
      (fun i => dist ((slabModel (toSMData M δ) (slabX M) eY eYD (toSMData_smooth M hδ) 4
            (slabT t₀ t₁) (slabT_pos h01)).obs (recTuple M hδ t₀ (N i) (u i) zs))
          ((slabModel (toSMData M δ) (slabX M) eY eYD (toSMData_smooth M hδ) 4 (slabT t₀ t₁)
            (slabT_pos h01)).obs zs)) =O[l] (fun i => (2 * π / N i) ^ (1 / 2 : ℝ)) :=
  RecordTuple.native_rate_example M hδ (slabX M) eY eYD (slabX_symm M δ) hKe hdet A hCk hb h0 h1
    h01 hKr hKO hR₁ hCσ

/-- **Cofinal summability along dyadic-comparable chains** (`cor:native-rate`, last sentence):
for records indexed by `j` with `c₁2^{-j} ≤ h_j = 2π/n_j ≤ c₂'2^{-j}`, under the rate hypotheses
and `i + γ = O(h^{1-β(k+4)}(1+|log h|)^{k+1})`, the adjacent state, curvature and stress differences
are summable. Unconditional form: the state coordinates are the fixed orthonormal coordinates `slabX M` of the positive block inner product, in which the principal matrices are symmetric (`slabX_symm`), so no symmetry hypothesis is assumed. -/
theorem native_rate_dyadic_unconditional {δ : ℝ} (hδ : 0 < δ) {na nb : ℕ}
    (eY : (Fin na → ℝ) ≃L[ℝ] BosP m (HSp M)) (eYD : (Fin nb → ℝ) ≃L[ℝ] 𝓢 × CoSpinor 𝓢)
    {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det) (A : ℝ) {k : ℕ}
    (hk : 4 ≤ k) {Ck : ℝ} (hCk : 0 < Ck) {t₀ t₁ b : ℝ} (hb : 0 < b) (h0 : b < t₀)
    (h1 : t₁ + b ≤ 2 * π) (h01 : t₀ < t₁) {Kr : Set (Fin (ActualJetKato.dimS m (HSp M) 𝓢 (CoSpinor 𝓢)) → ℝ)} (hKr : IsCompact Kr)
    (hKO : Kr ⊆ chartC (slabX M)) {R₁ : ℝ} (hR₁ : 0 ≤ R₁) {β c₂ Cσ Cτ : ℝ} (hβ : 0 ≤ β)
    (hβk : β < 1 / (k + 4)) (hCσ : 0 ≤ Cσ) {c₁ c₂' : ℝ} (hc₁ : 0 < c₁) :
    ∀ (N : ℕ → ℕ) [∀ j, NeZero (N j)] (u : ∀ j, Grid (N j) → Field 𝔄 𝓗 𝓢) (K σ : ℕ → ℝ),
      ∀ zs ∈ refSet (toSMData M δ) (slabX M) k (slabT t₀ t₁) Kr R₁,
      (∀ j, c₁ * (1 / 2) ^ j ≤ 2 * π / N j ∧ 2 * π / N j ≤ c₂' * (1 / 2) ^ j) →
      (∀ᶠ j in atTop, RecordHyp M δ Ke A t₀ t₁ b (N j) (u j) (K j) (σ j) ∧
        K j ≤ c₂ * (2 * π / N j) ^ (-β) ∧ σ j ≤ Cσ * (2 * π / N j) ∧
        tau (N j) (K j) 2 (u j) ≤ Cτ * (2 * π / N j * K j) ∧
        tau (N j) (K j) (k + 2) (u j) ≤ Cτ * (2 * π / N j * K j ^ 2)) →
      (fun j =>
        ‖(slabModel (toSMData M δ) (slabX M) eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).init (recTuple M hδ t₀ (N j) (u j) zs) -
          (slabModel (toSMData M δ) (slabX M) eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).init zs‖ +
        (slabModel (toSMData M δ) (slabX M) eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).harm (recTuple M hδ t₀ (N j) (u j) zs)) =O[atTop]
        (fun j => (2 * π / N j) ^ (1 - β * (k + 4)) *
          (1 + |Real.log (2 * π / N j)|) ^ (k + 1)) →
      Summable (fun j => dist
        ((slabModel (toSMData M δ) (slabX M) eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).obs (recTuple M hδ t₀ (N (j + 1)) (u (j + 1)) zs))
        ((slabModel (toSMData M δ) (slabX M) eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).obs (recTuple M hδ t₀ (N j) (u j) zs))) :=
  RecordTuple.native_rate_dyadic M hδ (slabX M) eY eYD (slabX_symm M δ) hKe hdet A hk hCk hb h0
    h1 h01 hKr hKO hR₁ hβ hβk hCσ hc₁

/-- **`thm:native-selected-closure`** (`eq:selected-closure` and the failure bound) for native
records at one cutoff, with `prop:coupled-bootstrap` and `thm:native-source` discharged. Unconditional form: the state coordinates are the fixed orthonormal coordinates `slabX M` of the positive block inner product, in which the principal matrices are symmetric (`slabX_symm`), so no symmetry hypothesis is assumed. -/
theorem native_selected_closure_records_unconditional {δ : ℝ} (hδ : 0 < δ) {na nb : ℕ}
    (eY : (Fin na → ℝ) ≃L[ℝ] BosP m (HSp M)) (eYD : (Fin nb → ℝ) ≃L[ℝ] 𝓢 × CoSpinor 𝓢)
    {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det) (A : ℝ) {k : ℕ}
    (hk : 4 ≤ k) {Ck : ℝ} (hCk : 0 < Ck) {t₀ t₁ b : ℝ} (hb : 0 < b) (h0 : b < t₀)
    (h1 : t₁ + b ≤ 2 * π) (h01 : t₀ < t₁) {Kr : Set (Fin (ActualJetKato.dimS m (HSp M) 𝓢 (CoSpinor 𝓢)) → ℝ)} (hKr : IsCompact Kr)
    (hKO : Kr ⊆ chartC (slabX M)) {R₁ : ℝ} (hR₁ : 0 ≤ R₁) :
    ∃ C₁ cr τs Cst dst : ℝ, 0 ≤ C₁ ∧ 0 < cr ∧ 0 < τs ∧ 0 ≤ Cst ∧ 0 < dst ∧
    ∀ zs ∈ refSet (toSMData M δ) (slabX M) k (slabT t₀ t₁) Kr R₁,
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
          (fun x => (‖(nSlab M hδ (slabX M) eY eYD k h01).init (recTuple M hδ t₀ n (rec x) zs) -
            (nSlab M hδ (slabX M) eY eYD k h01).init zs‖ +
            (nSlab M hδ (slabX M) eY eYD k h01).harm (recTuple M hδ t₀ n (rec x) zs)) ^ 2)
          sh Rr α (proc.X (sel ω) ω) ≤
        FiniteAcceptedProcess.score (fun x => rowNorm M t₀ t₁ b n (rec x)) V
          (fun x => (‖(nSlab M hδ (slabX M) eY eYD k h01).init (recTuple M hδ t₀ n (rec x) zs) -
            (nSlab M hδ (slabX M) eY eYD k h01).init zs‖ +
            (nSlab M hδ (slabX M) eY eYD k h01).harm (recTuple M hδ t₀ n (rec x) zs)) ^ 2)
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
          (‖(nSlab M hδ (slabX M) eY eYD k h01).init (recTuple M hδ t₀ n (rec (proc.X (sel ω) ω)) zs) -
            (nSlab M hδ (slabX M) eY eYD k h01).init zs‖ +
            (nSlab M hδ (slabX M) eY eYD k h01).harm
              (recTuple M hδ t₀ n (rec (proc.X (sel ω) ω)) zs)) ^ 2 ≤ α ^ 2)), proc.P ω
      ≤ proc.exitProbability J + (Ap - Am) / (κ * δs * J * sh ^ 2)
        + proc.occupation J rr / (κ * sh ^ 2)
        + proc.occupation J (fun _ x => V x) / Rr ^ 2
        + proc.occupation J (fun _ x =>
            (‖(nSlab M hδ (slabX M) eY eYD k h01).init (recTuple M hδ t₀ n (rec x) zs) -
              (nSlab M hδ (slabX M) eY eYD k h01).init zs‖ +
              (nSlab M hδ (slabX M) eY eYD k h01).harm (recTuple M hδ t₀ n (rec x) zs)) ^ 2) / α ^ 2) ∧
    ∀ ω ∈ proc.S J, rowNorm M t₀ t₁ b n (rec (proc.X (sel ω) ω)) ≤ sh →
      V (proc.X (sel ω) ω) ≤ Rr ^ 2 →
      (‖(nSlab M hδ (slabX M) eY eYD k h01).init (recTuple M hδ t₀ n (rec (proc.X (sel ω) ω)) zs) -
          (nSlab M hδ (slabX M) eY eYD k h01).init zs‖ +
        (nSlab M hδ (slabX M) eY eYD k h01).harm
          (recTuple M hδ t₀ n (rec (proc.X (sel ω) ω)) zs)) ^ 2 ≤ α ^ 2 →
      dist ((nSlab M hδ (slabX M) eY eYD k h01).obs (recTuple M hδ t₀ n (rec (proc.X (sel ω) ω)) zs))
          ((nSlab M hδ (slabX M) eY eYD k h01).obs zs) ≤
        Cst * (α + C₁ * (Real.exp 1 * (k + 1)! *
          forcingBudget k Ck sh (2 * π / n) K (t₂ + c₂ * Rr) (tm + cm * Rr))) :=
  RecordTuple.native_selected_closure_records M hδ (slabX M) eY eYD (slabX_symm M δ) hKe hdet A
    hk hCk hb h0 h1 h01 hKr hKO hR₁

/-- **The deterministic selected closure on one record** (`eq:selected-closure`). Unconditional form: the state coordinates are the fixed orthonormal coordinates `slabX M` of the positive block inner product, in which the principal matrices are symmetric (`slabX_symm`), so no symmetry hypothesis is assumed. -/
theorem selected_record_bound_unconditional {δ : ℝ} (hδ : 0 < δ) {na nb : ℕ}
    (eY : (Fin na → ℝ) ≃L[ℝ] BosP m (HSp M)) (eYD : (Fin nb → ℝ) ≃L[ℝ] 𝓢 × CoSpinor 𝓢)
    {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det) (A : ℝ) {k : ℕ}
    (hk : 4 ≤ k) {Ck : ℝ} (hCk : 0 < Ck) {t₀ t₁ b : ℝ} (hb : 0 < b) (h0 : b < t₀)
    (h1 : t₁ + b ≤ 2 * π) (h01 : t₀ < t₁) {Kr : Set (Fin (ActualJetKato.dimS m (HSp M) 𝓢 (CoSpinor 𝓢)) → ℝ)} (hKr : IsCompact Kr)
    (hKO : Kr ⊆ chartC (slabX M)) {R₁ : ℝ} (hR₁ : 0 ≤ R₁) :
    ∃ C₁ cr τs Cst dst : ℝ, 0 ≤ C₁ ∧ 0 < cr ∧ 0 < τs ∧ 0 ≤ Cst ∧ 0 < dst ∧
    ∀ zs ∈ refSet (toSMData M δ) (slabX M) k (slabT t₀ t₁) Kr R₁,
    ∀ (n : ℕ) [NeZero n], Odd n → ∀ (u : Grid n → Field 𝔄 𝓗 𝓢) (K V sh Rr α t₂ c₂ tm cm : ℝ),
      1 ≤ K → 2 * π / n * K ≤ cr → LegalRec M δ Ke A t₀ n u K → 0 ≤ V → 0 < sh → 0 ≤ Rr →
      0 ≤ c₂ → 0 ≤ cm →
      tau n K 2 u ≤ t₂ + c₂ * Real.sqrt V → tau n K (k + 2) u ≤ tm + cm * Real.sqrt V →
      tm + cm * Rr ≤ τs → rowNorm M t₀ t₁ b n u ≤ sh → V ≤ Rr ^ 2 →
      ‖(nSlab M hδ (slabX M) eY eYD k h01).init (recTuple M hδ t₀ n u zs) -
          (nSlab M hδ (slabX M) eY eYD k h01).init zs‖ +
        (nSlab M hδ (slabX M) eY eYD k h01).harm (recTuple M hδ t₀ n u zs) ≤ α →
      α + C₁ * (Real.exp 1 * (k + 1)! *
        forcingBudget k Ck sh (2 * π / n) K (t₂ + c₂ * Rr) (tm + cm * Rr)) ≤ dst →
      dist ((nSlab M hδ (slabX M) eY eYD k h01).obs (recTuple M hδ t₀ n u zs))
          ((nSlab M hδ (slabX M) eY eYD k h01).obs zs) ≤
        Cst * (α + C₁ * (Real.exp 1 * (k + 1)! *
          forcingBudget k Ck sh (2 * π / n) K (t₂ + c₂ * Rr) (tm + cm * Rr))) :=
  RecordTuple.selected_record_bound M hδ (slabX M) eY eYD (slabX_symm M δ) hKe hdet A hk hCk hb
    h0 h1 h01 hKr hKO hR₁

/-- **`eq:selected-polynomial-rate` on every successful record of a fine grid.** Unconditional form: the state coordinates are the fixed orthonormal coordinates `slabX M` of the positive block inner product, in which the principal matrices are symmetric (`slabX_symm`), so no symmetry hypothesis is assumed. -/
theorem selected_polynomial_record_unconditional {δ : ℝ} (hδ : 0 < δ) {na nb : ℕ}
    (eY : (Fin na → ℝ) ≃L[ℝ] BosP m (HSp M)) (eYD : (Fin nb → ℝ) ≃L[ℝ] 𝓢 × CoSpinor 𝓢)
    {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det) (A : ℝ) {k : ℕ}
    (hk : 4 ≤ k) {Ck : ℝ} (hCk : 0 < Ck) {t₀ t₁ b : ℝ} (hb : 0 < b) (h0 : b < t₀)
    (h1 : t₁ + b ≤ 2 * π) (h01 : t₀ < t₁) {Kr : Set (Fin (ActualJetKato.dimS m (HSp M) 𝓢 (CoSpinor 𝓢)) → ℝ)} (hKr : IsCompact Kr)
    (hKO : Kr ⊆ chartC (slabX M)) {R₁ : ℝ} (hR₁ : 0 ≤ R₁)
    {q a bs c β c₁ c₂ CT : ℝ} (hc : 0 < c) (hβ0 : 0 < β) (hβb : β < bs / (k + 1))
    (hβk : β < 1 / (k + 4)) (ha : a < β * (q - k - 5)) (hc₁ : 0 < c₁)
    (hCT : 0 ≤ CT) :
    ∃ h₀ Cr : ℝ, 0 < h₀ ∧ ∀ zs ∈ refSet (toSMData M δ) (slabX M) k (slabT t₀ t₁) Kr R₁,
    ∀ (n : ℕ) [NeZero n], Odd n → 2 * π / n ≤ h₀ →
    ∀ (u : Grid n → Field 𝔄 𝓗 𝓢) (K V t₂ c₂r tm cm : ℝ), 1 ≤ K →
      c₁ * (2 * π / n) ^ (-β) ≤ K → K ≤ c₂ * (2 * π / n) ^ (-β) →
      LegalRec M δ Ke A t₀ n u K → 0 ≤ V → 0 ≤ c₂r → 0 ≤ cm →
      tau n K 2 u ≤ t₂ + c₂r * Real.sqrt V → tau n K (k + 2) u ≤ tm + cm * Real.sqrt V →
      t₂ + c₂r * (2 * π / n) ^ (-a) ≤ CT * (2 * π / n) ^ (-a) * K ^ (2 - q) →
      tm + cm * (2 * π / n) ^ (-a) ≤ CT * (2 * π / n) ^ (-a) * K ^ (2 - q) →
      rowNorm M t₀ t₁ b n u ≤ (2 * π / n) ^ bs → V ≤ ((2 * π / n) ^ (-a)) ^ 2 →
      ‖(nSlab M hδ (slabX M) eY eYD k h01).init (recTuple M hδ t₀ n u zs) -
          (nSlab M hδ (slabX M) eY eYD k h01).init zs‖ +
        (nSlab M hδ (slabX M) eY eYD k h01).harm (recTuple M hδ t₀ n u zs) ≤ (2 * π / n) ^ c →
      dist ((nSlab M hδ (slabX M) eY eYD k h01).obs (recTuple M hδ t₀ n u zs))
          ((nSlab M hδ (slabX M) eY eYD k h01).obs zs) ≤
        Cr * ((2 * π / n) ^ SelectedPolynomial.rho k q a bs c β *
          (1 + |Real.log (2 * π / n)|) ^ (k + 1)) :=
  RecordTuple.selected_polynomial_record M hδ (slabX M) eY eYD (slabX_symm M δ) hKe hdet A hk hCk
    hb h0 h1 h01 hKr hKO hR₁ hc hβ0 hβb hβk ha hc₁ hCT

/-- **Non-vacuity of the reference class** in the setting of `native_closure_unconditional`: for
every slab model with `Λ + κλ_Hv_H⁴ = 0` (in particular `diracSlab`), every margin, order and
slab `[t₀, t₁]`, there are a compact chart margin `K ⊆ chartC (slabX M)` and a bound `R₁ ≥ 0`
whose reference class contains an exact regular solution (the flat vacuum). -/
theorem refSet_nonempty_unconditional (hc : M.Λ + M.κ * (M.lamH * M.vH ^ 4) = 0) (δ : ℝ) (k : ℕ)
    (t₀ t₁ : ℝ) :
    ∃ (K : Set (Fin (ActualJetKato.dimS m (HSp M) 𝓢 (CoSpinor 𝓢)) → ℝ)) (R₁ : ℝ),
      IsCompact K ∧ K ⊆ chartC (slabX M) ∧ 0 ≤ R₁ ∧
      (refSet (toSMData M δ) (slabX M) k (slabT t₀ t₁) K R₁).Nonempty := by
  obtain ⟨K, R₁, h1, h2, h3, h4⟩ := RefSetNonempty.refSet_nonempty_slab M hc δ k (slabT t₀ t₁)
  exact ⟨K, R₁, h1, h2, h3, ⟨_, h4⟩⟩

end

end RenewalGeometry.ClosureUnconditional
