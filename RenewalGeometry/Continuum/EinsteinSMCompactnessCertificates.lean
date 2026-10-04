/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMRegulatorSequence
import RenewalGeometry.Analysis.SobolevBoxCompactness
import RenewalGeometry.OperatorLimits.SMSTPositiveScreenExact

/-!
# Reduced action convergence, compactness certificates and the classical strong packet
  (`def:reduced-topology`, `def:reduced-certificate`, `def:compactness-certificate`,
  `def:strong-packet`, Einstein–Standard-Model action-closure manuscript)

Rendering as in `EinsteinSMFieldSpaces.lean` / `EinsteinSMRegulatorSequence.lean`
(`M = (0,T) × 𝕋³` lifted to `ℝ⁴`, trivialised bundles — "after fixed local gauge and spin-frame
identifications" —, flat comparison metric and Lebesgue density `dV₀`).

**Compact charts.**  A compact smooth chart `K` is rendered as a closed coordinate box
`ChartBox T`: `Q = Π (a_i, b_i)` with `0 < a₀ < b₀ < T` and spatial sides `≤ 1` (so that `Q`
injects into `(0,T) × 𝕋³`); `L^p(K) = L^p(Q)` and `H¹(K) = W^{1,2}(Q)` of
`Analysis/SobolevOpenSet.lean` (weak derivatives tested against `C_c^∞(Q)`), as in the ledger
encoding of `prop:orlicz`.  "On every `K ⋐ M`" is rendered as "on every chart box": every
compact `K ⊂ M` is covered by finitely many chart boxes and all conditions below are local.

**Multi-component norms.**  A field with components `ι'` is a map `E4 → ι' → ℂ` (sup norm on
the fibre); `h1Norm Q u g = ‖u‖_{L²(Q)} + ‖g‖_{L²(Q)}` with `g` the gradient components (an
equivalent `H¹(Q)` norm), `MemH1` asks every component to lie in `W^{1,2}(Q)` with the given weak
gradient.  Precompactness in `L^p(Q)` (`LpPrecompact`) is total boundedness of the sequence:
finite `ε`-nets drawn from the sequence itself.  **Weak `H¹` convergence** (`WeakH1Tendsto`) is
encoded as: all terms and the limit in `W^{1,2}(Q)`, a uniform `W^{1,2}(Q)` bound, and
convergence of all `C_c^∞(Q)` test pairings of the components and of their gradients; for a
sequence in the Hilbert space `H¹(Q)` this is equivalent to weak convergence (bounded sequences
are weakly relatively compact, and the test pairings identify every weak cluster point).

**Packets.**  For smooth reconstructed fields the packets are the classical ones: the coframe
first-derivative packet `∂_i e^a_μ`, the curvature `F_{A} = dA + A∧A` (`curvatureF`), the
covariant Higgs gradient `D_AH` (`covDerivHiggs`) and the spinor first jets `∂_iΨ`.  For limit
fields (`LimitFields`) the packets are data identified *weakly* with the connection
(`HasWeakCurvature`: `F - A∧A = dA` in `𝒟'(Q)`; `HasWeakCovGrad`: `K - ρ_H(A)H = dH` in
`𝒟'(Q)`), so "the curvatures are identified with the reconstructed connections, not independent
weak tensor limits".

**Common compact screens** (`lem:screen`, literal): a sequence `Y_h` of a complex Hilbert space
has a common compact screen (`CommonCompactScreen`) if there are bounded `S_{h,R}` and compact
`S_R` (Mathlib `IsCompactOperator`), `R ∈ ℕ`, with `‖S_{h,R} - S_R‖ → 0` as `h → 0` for every
`R`, `lim_R sup_h ‖(I - S_{h,R})Y_h‖ = 0`, and `S_RY → Y` for every weak (subsequential) limit
`Y` of `(Y_h)` — the hypotheses of `lem:screen`, whose weak-limit clause is imposed on every weak
cluster point since the certificate is stated before extraction.  A packet has a common compact
screen in `L²(Q)` (`HasCommonCompactScreen`) if its `L²(Q; ℂ^{ι'})` representatives
(`EuclideanSpace` fibre, the Hilbert norm) have one.

**Coefficient banks** live in `(Fin 7 → ℝ) × (Ysec → M₃(ℂ))` through `bankCoords`; the physical
region is `κ, g₁, g₂, g₃, λ_H > 0`; "a compact subset of the physical parameter region" is
`IsCompactBankSet`.  The "fixed compact nondegenerate coframe chart" `𝒦_e` is a compact subset of
`coframeChart = {det e > 0, e⁰₀ > 0}` (oriented, time-oriented, nondegenerate — the conventions of
the library's `def:finite-interface` encoding).

## Contents

* `ReducedConvergence` (`def:reduced-topology`, on one chart box) and
  `RegulatorSequence.ReducedActionConvergence` (on every chart box);
* `ReducedCertificate` (`def:reduced-certificate`, items (R1)–(R5));
* `CompactnessCertificate` (`def:compactness-certificate`, items (C1)–(C5), with the Orlicz
  condition and the spinor routes `SpinorScreenRoute` (C4a) / `DiracStabilityRoute` (C4b), the
  latter carrying the hypotheses of `prop:dirac-stability`: `DiracStabilityHyp`);
* `StrongPacket` (`def:strong-packet`); `StrongPacket.limit_bank_physical` (the limiting bank is
  physical);
* non-vacuity: the flat regulator `flatRegulator` (constant identity coframe, zero gauge, Higgs and
  spinor fields, physical bank) satisfies all three certificates/convergences on every chart box
  (`flatRegulator_reducedCertificate`, `flatRegulator_compactnessCertificate`,
  `flatRegulator_reducedActionConvergence`, `flatRegulator_strongPacket`); the (C4b) route is
  also inhabited (`diracStabilityHyp_zero`, `flatRegulator_diracRoute`).
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal

noncomputable section

namespace RenewalGeometry
namespace EinsteinSM

open SobolevOpen (pd box IsTest MemW12)

/-! ### Chart boxes and multi-component norms -/

/-- A compact coordinate chart `K = Q̄ ⋐ M`, `Q = Π (a_i, b_i)`, time in `(0,T)`, spatial sides
`≤ 1`. -/
structure ChartBox (T : ℝ) where
  a : E4
  b : E4
  lt : ∀ i, a i < b i
  time_pos : 0 < a 0
  time_lt : b 0 < T
  spatial_le : ∀ i : Fin 3, b i.succ - a i.succ ≤ 1

namespace ChartBox

variable {T : ℝ}

/-- The open box. -/
def set (Q : ChartBox T) : Set E4 := box Q.a Q.b

/-- The comparison measure on the chart: `dV₀ = d⁴x` restricted to `Q`. -/
abbrev μ (Q : ChartBox T) : Measure E4 := volume.restrict Q.set

instance (Q : ChartBox T) : IsFiniteMeasure Q.μ :=
  isFiniteMeasure_restrict.mpr (SobolevOpen.volume_box_ne_top Q.a Q.b)

end ChartBox

variable {T : ℝ} {ι' : Type} [Fintype ι']

/-- `H¹(Q)` norm `‖u‖_{L²} + ‖∇u‖_{L²}` of a multi-component field with gradient data `g`. -/
def h1Norm (Q : ChartBox T) (u : E4 → ι' → ℂ) (g : E4 → Fin 4 → ι' → ℂ) : ℝ≥0∞ :=
  eLpNorm u 2 Q.μ + eLpNorm g 2 Q.μ

/-- `u ∈ H¹(Q)` with weak gradient `g` (every component in `W^{1,2}(Q)`). -/
def MemH1 (Q : ChartBox T) (u : E4 → ι' → ℂ) (g : E4 → Fin 4 → ι' → ℂ) : Prop :=
  ∀ c, MemW12 Q.set (fun x => u x c) (fun i x => g x i c)

/-- Uniform `H¹(Q)` bound. -/
def H1Bounded (Q : ChartBox T) (u : ℕ → E4 → ι' → ℂ) (g : ℕ → E4 → Fin 4 → ι' → ℂ) : Prop :=
  ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ n, h1Norm Q (u n) (g n) ≤ B

/-- Strong `H¹(Q)` convergence. -/
def H1Tendsto (Q : ChartBox T) (u : ℕ → E4 → ι' → ℂ) (g : ℕ → E4 → Fin 4 → ι' → ℂ)
    (u₀ : E4 → ι' → ℂ) (g₀ : E4 → Fin 4 → ι' → ℂ) : Prop :=
  Tendsto (fun n => h1Norm Q (u n - u₀) (g n - g₀)) atTop (𝓝 0)

/-- Weak `H¹(Q)` convergence (bounded in `W^{1,2}(Q)` + convergence of all test pairings of the
components and of their gradients; equivalent to weak convergence in the Hilbert space). -/
def WeakH1Tendsto (Q : ChartBox T) (u : ℕ → E4 → ι' → ℂ) (g : ℕ → E4 → Fin 4 → ι' → ℂ)
    (u₀ : E4 → ι' → ℂ) (g₀ : E4 → Fin 4 → ι' → ℂ) : Prop :=
  (∀ n, MemH1 Q (u n) (g n)) ∧ MemH1 Q u₀ g₀ ∧ H1Bounded Q u g ∧
  (∀ φ, IsTest Q.set φ → ∀ c, Tendsto (fun n => ∫ x, ((φ x : ℝ) : ℂ) * u n x c) atTop
    (𝓝 (∫ x, ((φ x : ℝ) : ℂ) * u₀ x c))) ∧
  (∀ φ, IsTest Q.set φ → ∀ i c, Tendsto (fun n => ∫ x, ((φ x : ℝ) : ℂ) * g n x i c) atTop
    (𝓝 (∫ x, ((φ x : ℝ) : ℂ) * g₀ x i c)))

/-- Uniform `L^p(μ)` bound. -/
def LpBounded {F : Type*} [NormedAddCommGroup F] (p : ℝ≥0∞) (μ : Measure E4)
    (u : ℕ → E4 → F) : Prop :=
  ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ n, eLpNorm (u n) p μ ≤ B

/-- Strong `L^p(μ)` convergence. -/
def LpTendsto {F : Type*} [NormedAddCommGroup F] (p : ℝ≥0∞) (μ : Measure E4)
    (u : ℕ → E4 → F) (u₀ : E4 → F) : Prop :=
  Tendsto (fun n => eLpNorm (u n - u₀) p μ) atTop (𝓝 0)

/-- Precompactness of a sequence in `L^p(μ)`: every term in `L^p` and the sequence is totally
bounded (finite `ε`-nets taken from the sequence). -/
def LpPrecompact {F : Type*} [NormedAddCommGroup F] (p : ℝ≥0∞) (μ : Measure E4)
    (u : ℕ → E4 → F) : Prop :=
  (∀ n, MemLp (u n) p μ) ∧
    ∀ ε > (0 : ℝ), ∃ s : Finset ℕ, ∀ n, ∃ m ∈ s, eLpNorm (u n - u m) p μ < ENNReal.ofReal ε

/-! ### Common compact screens (`lem:screen`) -/

/-- **Common compact screen** (the hypotheses of `lem:screen`): bounded `S_{h,R}`, compact `S_R`
with `‖S_{h,R} - S_R‖ → 0` (`h → 0`, each `R`), `lim_R sup_h ‖(I - S_{h,R})Y_h‖ = 0`, and
`S_R Y → Y` for every weak subsequential limit `Y` of `(Y_h)`. -/
def CommonCompactScreen {𝒴 : Type} [NormedAddCommGroup 𝒴] [InnerProductSpace ℂ 𝒴]
    (Y : ℕ → 𝒴) : Prop :=
  ∃ (Sh : ℕ → ℕ → 𝒴 →L[ℂ] 𝒴) (S : ℕ → 𝒴 →L[ℂ] 𝒴),
    (∀ R, IsCompactOperator (S R)) ∧
    (∀ R, Tendsto (fun h => ‖Sh h R - S R‖) atTop (𝓝 0)) ∧
    (∀ ε > (0 : ℝ), ∃ R₀, ∀ R ≥ R₀, ∀ h, ‖Y h - Sh h R (Y h)‖ ≤ ε) ∧
    (∀ φ : ℕ → ℕ, StrictMono φ → ∀ Ylim, SMSTChannel.WeakTendsto (Y ∘ φ) Ylim →
      Tendsto (fun R => S R Ylim) atTop (𝓝 Ylim))

/-- The Hilbert space `L²(Q; ℂ^{ι'})`. -/
abbrev L2Hilbert (Q : ChartBox T) (ι' : Type) [Fintype ι'] : Type :=
  Lp (EuclideanSpace ℂ ι') 2 Q.μ

/-- A packet sequence has a **common compact screen in `L²(Q)`**. -/
def HasCommonCompactScreen (Q : ChartBox T) (P : ℕ → E4 → ι' → ℂ) : Prop :=
  ∃ Y : ℕ → L2Hilbert Q ι',
    (∀ n, (Y n : E4 → EuclideanSpace ℂ ι') =ᵐ[Q.μ] fun x => WithLp.toLp 2 (P n x)) ∧
    CommonCompactScreen Y

/-- The zero sequence has a common compact screen (`S_{h,R} = S_R = 0`). -/
theorem commonCompactScreen_zero {𝒴 : Type} [NormedAddCommGroup 𝒴] [InnerProductSpace ℂ 𝒴] :
    CommonCompactScreen (fun _ : ℕ => (0 : 𝒴)) := by
  refine ⟨fun _ _ => 0, fun _ => 0, fun _ => isCompactOperator_zero, fun R => by simp,
    fun ε hε => ⟨0, fun _ _ _ => by simp [hε.le]⟩, fun φ _ Ylim hw => ?_⟩
  have h0 : Ylim = 0 := by
    have h1 := hw Ylim
    simp only [Function.comp_apply, inner_zero_right] at h1
    exact inner_self_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds h1).symm
  subst h0
  simp

theorem hasCommonCompactScreen_zero (Q : ChartBox T) :
    HasCommonCompactScreen Q (fun _ _ => (0 : ι' → ℂ)) := by
  refine ⟨fun _ => 0, fun n => ?_, commonCompactScreen_zero⟩
  filter_upwards [Lp.coeFn_zero (EuclideanSpace ℂ ι') 2 Q.μ] with x hx
  rw [hx]
  rfl

/-! ### Coefficient banks and coframe charts -/

variable {Ysec : Type} [Fintype Ysec]

/-- Coordinates of a coefficient bank in `(Fin 7 → ℝ) × (Ysec → M₃(ℂ))`. -/
def bankCoords (θ : CoefficientBank Ysec) : (Fin 7 → ℝ) × (Ysec → Matrix (Fin 3) (Fin 3) ℂ) :=
  (![θ.kappa, θ.Lambda, θ.g1, θ.g2, θ.g3, θ.lambdaH, θ.vH], θ.yukawa)

/-- The physical parameter region `κ, g₁, g₂, g₃, λ_H > 0`. -/
def physicalBanks : Set (CoefficientBank Ysec) :=
  {θ | 0 < θ.kappa ∧ 0 < θ.g1 ∧ 0 < θ.g2 ∧ 0 < θ.g3 ∧ 0 < θ.lambdaH}

/-- A compact subset of the physical parameter region. -/
def IsCompactBankSet (P : Set (CoefficientBank Ysec)) : Prop :=
  IsCompact (bankCoords '' P) ∧ P ⊆ physicalBanks

/-- Convergence of coefficient banks. -/
def BankTendsto (θ : ℕ → CoefficientBank Ysec) (θ₀ : CoefficientBank Ysec) : Prop :=
  Tendsto (fun n => bankCoords (θ n)) atTop (𝓝 (bankCoords θ₀))

/-- The oriented, time-oriented, nondegenerate coframe chart `{det e > 0, e⁰₀ > 0}`. -/
def coframeChart : Set CoframeFibre := {e | 0 < (Matrix.of e).det ∧ 0 < e 0 0}

/-- A fixed compact subset `𝒦_e` of the coframe chart. -/
def IsCompactCoframeSet (Ke : Set CoframeFibre) : Prop := IsCompact Ke ∧ Ke ⊆ coframeChart

/-! ### Packets -/

section Packets

variable {C : Type} [Fintype C]

/-- Coframe components as complex functions, index `(a, μ)`. -/
def coframeC (e : E4 → CoframeFibre) : E4 → Fin 4 × Fin 4 → ℂ :=
  fun x p => (e x p.1 p.2 : ℂ)

/-- Spinor components, index `(s, c)`. -/
def spinorC (Ψ : E4 → SpinorFibre C) : E4 → Fin 4 × C → ℂ := fun x p => Ψ x p.1 p.2

/-- Classical coframe first-derivative packet `∂_i e^a_μ`. -/
def coframeGrad (e : E4 → CoframeFibre) : E4 → Fin 4 → Fin 4 × Fin 4 → ℂ :=
  fun x i p => (pd e i x p.1 p.2 : ℂ)

/-- Classical spinor first-jet packet `∂_iΨ`. -/
def spinorGrad (Ψ : E4 → SpinorFibre C) : E4 → Fin 4 → Fin 4 × C → ℂ :=
  fun x i p => pd Ψ i x p.1 p.2

/-- Classical ordinary Higgs gradient `∂_iH`. -/
def higgsGrad (H : E4 → HiggsFibre) : E4 → Fin 4 → Fin 2 → ℂ := fun x i => pd H i x

/-- Flattened coframe first-derivative packet. -/
def coframeJetPacket (e : E4 → CoframeFibre) : E4 → Fin 4 × (Fin 4 × Fin 4) → ℂ :=
  fun x q => coframeGrad e x q.1 q.2

/-- Flattened curvature packet `F_{μν}`. -/
def curvaturePacket (A : E4 → ConnFibre) : E4 → Fin 4 × Fin 4 × Fin 5 × Fin 5 → ℂ :=
  fun x q => curvatureF A x q.1 q.2.1 q.2.2.1 q.2.2.2

/-- Flattened covariant-gradient packet `(D_AH)_μ`. -/
def covGradPacket (A : E4 → ConnFibre) (H : E4 → HiggsFibre) : E4 → Fin 4 × Fin 2 → ℂ :=
  fun x q => covDerivHiggs A H x q.1 q.2

/-- Flattened spinor first-jet packet. -/
def spinorJetPacket (Ψ : E4 → SpinorFibre C) : E4 → Fin 4 × (Fin 4 × C) → ℂ :=
  fun x q => spinorGrad Ψ x q.1 q.2

/-- The Higgs bundle norm `|H|`. -/
def higgsNorm (v : HiggsFibre) : ℝ := Real.sqrt (∑ i, Complex.normSq (v i))

/-- The pointwise inverse coframe (frame) as a fibre element. -/
def coframeInv (e : CoframeFibre) : CoframeFibre := fun μ a => (Matrix.of e)⁻¹ μ a

end Packets

/-- Limit fields `z = (e, A, H, Ψ, Ψ̄)` of limited regularity, with their packets as data:
weak coframe gradient, curvature, covariant Higgs gradient, weak spinor gradients. -/
structure LimitFields (C : Type) [Fintype C] where
  e : E4 → CoframeFibre
  de : E4 → Fin 4 → Fin 4 × Fin 4 → ℂ
  A : E4 → ConnFibre
  F : E4 → Fin 4 → Fin 4 → LieFibre
  H : E4 → HiggsFibre
  K : E4 → Fin 4 → HiggsFibre
  Ψ : E4 → SpinorFibre C
  dΨ : E4 → Fin 4 → Fin 4 × C → ℂ
  Ψb : E4 → SpinorFibre C
  dΨb : E4 → Fin 4 → Fin 4 × C → ℂ

/-- `F = dA + A∧A` in `𝒟'(Q)`: `∫ φ(F_{μν} - [A_μ,A_ν]) = -∫(∂_μφ A_ν - ∂_νφ A_μ)`. -/
def HasWeakCurvature (Q : ChartBox T) (A : E4 → ConnFibre) (F : E4 → Fin 4 → Fin 4 → LieFibre) :
    Prop :=
  ∀ μ ν i j, ∀ φ, IsTest Q.set φ →
    ∫ x, ((φ x : ℝ) : ℂ) * (F x μ ν i j - comm (A x μ) (A x ν) i j) =
      -∫ x, (((pd φ μ x : ℝ) : ℂ) * A x ν i j - ((pd φ ν x : ℝ) : ℂ) * A x μ i j)

/-- `K = D_AH = dH + ρ_H(A)H` in `𝒟'(Q)`: `∫ φ(K_μ - ρ_H(A_μ)H) = -∫ ∂_μφ H`. -/
def HasWeakCovGrad (Q : ChartBox T) (A : E4 → ConnFibre) (H : E4 → HiggsFibre)
    (K : E4 → Fin 4 → HiggsFibre) : Prop :=
  ∀ μ i, ∀ φ, IsTest Q.set φ →
    ∫ x, ((φ x : ℝ) : ℂ) * (K x μ i - higgsAct (A x μ) (H x) i) =
      -∫ x, ((pd φ μ x : ℝ) : ℂ) * H x i

/-! ### `def:reduced-topology` -/

section Defs

variable {C : Type} [Fintype C] {left : C → Bool}

/-- **`def:reduced-topology`: reduced action convergence on a compact chart `Q`** of smooth
reconstructed fields `z_h` with banks `θ_h` to limit fields `z` and bank `θ`. -/
structure ReducedConvergence (Q : ChartBox T) (z : ℕ → SmoothFields T left)
    (θ : ℕ → CoefficientBank Ysec) (L : LimitFields C) (θ₀ : CoefficientBank Ysec) : Prop where
  /-- `e_h(x), e(x) ∈ 𝒦_e` a.e., `𝒦_e` a fixed compact subset of one coframe chart -/
  coframe_chart : ∃ Ke, IsCompactCoframeSet Ke ∧ (∀ n, ∀ᵐ x ∂Q.μ, (z n).z.e x ∈ Ke) ∧
    ∀ᵐ x ∂Q.μ, L.e x ∈ Ke
  /-- the limit coframe lies in `H¹` with weak gradient `de` -/
  coframe_mem : MemH1 Q (coframeC L.e) L.de
  /-- `e_h → e` strongly in `H¹` -/
  coframe_tendsto : H1Tendsto Q (fun n => coframeC (z n).z.e) (fun n => coframeGrad (z n).z.e)
    (coframeC L.e) L.de
  /-- the limit connection is `ad P`-valued -/
  conn_lie : ∀ᵐ x ∂Q.μ, ∀ μ, L.A x μ ∈ smLie
  conn_mem : MemLp L.A 4 Q.μ
  /-- `A_h → A` in `L⁴` -/
  conn_tendsto : LpTendsto 4 Q.μ (fun n => (z n).z.A) L.A
  /-- the limit curvature is `F_A` (weakly), in `L²` -/
  curv_mem : MemLp L.F 2 Q.μ
  curv_weak : HasWeakCurvature Q L.A L.F
  /-- `F_{A_h} → F_A` in `L²` -/
  curv_tendsto : LpTendsto 2 Q.μ (fun n => curvatureF (z n).z.A) L.F
  higgs_mem : MemLp L.H 2 Q.μ
  /-- `H_h → H` in `L²` -/
  higgs_tendsto : LpTendsto 2 Q.μ (fun n => (z n).z.H) L.H
  /-- the limit covariant gradient is `D_AH` (weakly), in `L²` -/
  covgrad_mem : MemLp L.K 2 Q.μ
  covgrad_weak : HasWeakCovGrad Q L.A L.H L.K
  /-- `D_{A_h}H_h → D_AH` in `L²` -/
  covgrad_tendsto : LpTendsto 2 Q.μ (fun n => covDerivHiggs (z n).z.A (z n).z.H) L.K
  /-- `Ψ_h ⇀ Ψ` weakly in `H¹` -/
  spinor_weak : WeakH1Tendsto Q (fun n => spinorC (z n).z.Ψ) (fun n => spinorGrad (z n).z.Ψ)
    (spinorC L.Ψ) L.dΨ
  /-- `Ψ̄_h ⇀ Ψ̄` weakly in `H¹` -/
  cospinor_weak : WeakH1Tendsto Q (fun n => spinorC (z n).z.Ψb)
    (fun n => spinorGrad (z n).z.Ψb) (spinorC L.Ψb) L.dΨb
  /-- banks converge inside a compact physical parameter set -/
  bank_compact : ∃ P, IsCompactBankSet P ∧ ∀ n, θ n ∈ P
  bank_tendsto : BankTendsto θ θ₀

/-! ### `def:reduced-certificate` -/

/-- **`def:reduced-certificate`: the reduced compactness certificate on a chart `Q`.** -/
structure ReducedCertificate (Q : ChartBox T) (z : ℕ → SmoothFields T left)
    (θ : ℕ → CoefficientBank Ysec) : Prop where
  /-- (R1) coframe values a.e. in one fixed compact nondegenerate coframe chart -/
  coframe_chart : ∃ Ke, IsCompactCoframeSet Ke ∧ ∀ n, ∀ᵐ x ∂Q.μ, (z n).z.e x ∈ Ke
  /-- (R1) coframes bounded in `H¹` -/
  coframe_bounded : H1Bounded Q (fun n => coframeC (z n).z.e) (fun n => coframeGrad (z n).z.e)
  /-- (R1) common compact screen for the first-derivative packet in `L²` -/
  coframe_screen : HasCommonCompactScreen Q (fun n => coframeJetPacket (z n).z.e)
  /-- (R2) connections precompact in `L⁴` -/
  conn_precompact : LpPrecompact 4 Q.μ (fun n => (z n).z.A)
  /-- (R2) curvature packet bounded in `L²` -/
  curv_bounded : LpBounded 2 Q.μ (fun n => curvatureF (z n).z.A)
  /-- (R2) common compact screen for the curvature packet -/
  curv_screen : HasCommonCompactScreen Q (fun n => curvaturePacket (z n).z.A)
  /-- (R3) Higgs fields bounded in `L²` -/
  higgs_bounded : LpBounded 2 Q.μ (fun n => (z n).z.H)
  /-- (R3) covariant-gradient packet bounded in `L²` -/
  covgrad_bounded : LpBounded 2 Q.μ (fun n => covDerivHiggs (z n).z.A (z n).z.H)
  /-- (R3) common compact screen for the covariant-gradient packet -/
  covgrad_screen : HasCommonCompactScreen Q (fun n => covGradPacket (z n).z.A (z n).z.H)
  /-- (R4) spinors bounded in `H¹` (no spinor first-jet screen) -/
  spinor_bounded : H1Bounded Q (fun n => spinorC (z n).z.Ψ) (fun n => spinorGrad (z n).z.Ψ)
  cospinor_bounded : H1Bounded Q (fun n => spinorC (z n).z.Ψb) (fun n => spinorGrad (z n).z.Ψb)
  /-- (R5) banks in a compact subset of the physical parameter region -/
  bank_compact : ∃ P, IsCompactBankSet P ∧ ∀ n, θ n ∈ P

/-! ### `prop:dirac-stability` hypotheses and `def:compactness-certificate` -/

/-- The lifted compact subslab `I × Σ`, `I = [t₀, t₁]`. -/
def slab (t₀ t₁ : ℝ) : Set E4 := {x | x 0 ∈ Icc t₀ t₁}

/-- Its fundamental domain `I × [0,1)³`. -/
def slabFund (t₀ t₁ : ℝ) : Set E4 := {x | x 0 ∈ Icc t₀ t₁ ∧ ∀ i : Fin 3, x i.succ ∈ Ico 0 1}

/-- The fundamental cube `[0,1)³` of `Σ = 𝕋³`. -/
def cube3 : Set (Fin 3 → ℝ) := univ.pi fun _ => Ico 0 1

/-- `‖f(t,·)‖_{H²_x}`: `Σ_{j ≤ 2} ‖D^j_y f(t,y)‖_{L²(𝕋³)}`. -/
def spatialH2 {N : Type} [Fintype N] (f : E4 → N → ℂ) (t : ℝ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range 3,
    eLpNorm (fun y : Fin 3 → ℝ => ‖iteratedFDeriv ℝ j (fun y' => f (Fin.cons t y')) y‖) 2
      (volume.restrict cube3)

/-- Matrix–vector product on `N → ℂ`. -/
def mvec {N : Type} [Fintype N] (A : N → N → ℂ) (v : N → ℂ) : N → ℂ := fun i => ∑ j, A i j * v j

/-- **Hypotheses of `prop:dirac-stability`** for a sequence `ψ_h` on the subslab `I × Σ`:
first-order systems `A_h^μ ∂_μψ_h + B_hψ_h = r_h` (residual defined by the equation), with
Hermitian (symmetric hyperbolic) `A_h^μ`, uniformly positive `A_h^0`,
`sup_h(‖A_h^μ‖_{W^{1,∞}} + ‖B_h‖_{L^∞} + ‖ψ_h‖_{L^∞_tH²_x}) < ∞` (`W^{1,∞}` as bounded and
Lipschitz on the slab), coefficients Cauchy in `L^∞`, initial data `ψ_h(t₀)` Cauchy in `L²(Σ)`,
residuals Cauchy in `L²(I × Σ)`.  Coefficients are spatially periodic (sections over `I × 𝕋³`). -/
def DiracStabilityHyp (t₀ t₁ : ℝ) {N : Type} [Fintype N] (ψ : ℕ → E4 → N → ℂ) : Prop :=
  ∃ (Acoef : ℕ → Fin 4 → E4 → N → N → ℂ) (Bcoef : ℕ → E4 → N → N → ℂ),
    (∀ n μ k x, Acoef n μ (x + spatialShift k) = Acoef n μ x) ∧
    (∀ n k x, Bcoef n (x + spatialShift k) = Bcoef n x) ∧
    (∀ n μ x i j, Acoef n μ x j i = star (Acoef n μ x i j)) ∧
    (∃ c > (0 : ℝ), ∀ n, ∀ x ∈ slab t₀ t₁, ∀ ξ : N → ℂ,
      c * ∑ i, ‖ξ i‖ ^ 2 ≤ (∑ i, ∑ j, star (ξ i) * Acoef n 0 x i j * ξ j).re) ∧
    (∃ Cb : ℝ≥0, ∀ n, (∀ μ, (∀ x ∈ slab t₀ t₁, ‖Acoef n μ x‖ ≤ Cb) ∧
        LipschitzOnWith Cb (Acoef n μ) (slab t₀ t₁)) ∧
      (∀ᵐ x ∂(volume.restrict (slab t₀ t₁)), ‖Bcoef n x‖ ≤ Cb) ∧
      (∀ t ∈ Icc t₀ t₁, spatialH2 (ψ n) t ≤ Cb)) ∧
    (∀ ε > (0 : ℝ), ∃ N₀, ∀ m ≥ N₀, ∀ n ≥ N₀,
      (∀ μ, ∀ x ∈ slab t₀ t₁, ‖Acoef m μ x - Acoef n μ x‖ ≤ ε) ∧
      ∀ᵐ x ∂(volume.restrict (slab t₀ t₁)), ‖Bcoef m x - Bcoef n x‖ ≤ ε) ∧
    (∀ ε > (0 : ℝ), ∃ N₀, ∀ m ≥ N₀, ∀ n ≥ N₀,
      eLpNorm (fun y : Fin 3 → ℝ => ψ m (Fin.cons t₀ y) - ψ n (Fin.cons t₀ y)) 2
        (volume.restrict cube3) ≤ ENNReal.ofReal ε) ∧
    (∀ ε > (0 : ℝ), ∃ N₀, ∀ m ≥ N₀, ∀ n ≥ N₀,
      eLpNorm ((fun x => ∑ μ, mvec (Acoef m μ x) (pd (ψ m) μ x) + mvec (Bcoef m x) (ψ m x)) -
          (fun x => ∑ μ, mvec (Acoef n μ x) (pd (ψ n) μ x) + mvec (Bcoef n x) (ψ n x))) 2
        (volume.restrict (slabFund t₀ t₁)) ≤ ENNReal.ofReal ε)

/-- (C4a) the direct spinor compactness route. -/
def SpinorScreenRoute (Q : ChartBox T) (z : ℕ → SmoothFields T left) : Prop :=
  LpPrecompact 2 Q.μ (fun n => spinorC (z n).z.Ψ) ∧
  LpPrecompact 2 Q.μ (fun n => spinorC (z n).z.Ψb) ∧
  H1Bounded Q (fun n => spinorC (z n).z.Ψ) (fun n => spinorGrad (z n).z.Ψ) ∧
  H1Bounded Q (fun n => spinorC (z n).z.Ψb) (fun n => spinorGrad (z n).z.Ψb) ∧
  HasCommonCompactScreen Q (fun n => spinorJetPacket (z n).z.Ψ) ∧
  HasCommonCompactScreen Q (fun n => spinorJetPacket (z n).z.Ψb)

/-- (C4b) the Lorentzian Dirac-evolution route: on a compact subslab `[t₀,t₁] × 𝕋³ ⊃ Q`, the
reconstructed Dirac and dual-Dirac systems satisfy the hypotheses of `prop:dirac-stability`. -/
def DiracStabilityRoute (Q : ChartBox T) (z : ℕ → SmoothFields T left) : Prop :=
  ∃ t₀ t₁, 0 < t₀ ∧ t₀ < t₁ ∧ t₁ < T ∧ t₀ ≤ Q.a 0 ∧ Q.b 0 ≤ t₁ ∧
    DiracStabilityHyp t₀ t₁ (fun n => spinorC (z n).z.Ψ) ∧
    DiracStabilityHyp t₀ t₁ (fun n => spinorC (z n).z.Ψb)

/-- **`def:compactness-certificate`: the classical compactness certificate on a chart `Q`.** -/
structure CompactnessCertificate (Q : ChartBox T) (z : ℕ → SmoothFields T left)
    (θ : ℕ → CoefficientBank Ysec) : Prop where
  /-- (C1) coframes precompact in `L^∞` -/
  coframe_precompact : LpPrecompact ⊤ Q.μ (fun n => (z n).z.e)
  /-- (C1) uniformly nondegenerate -/
  coframe_nondegenerate : ∃ c > (0 : ℝ), ∀ n, ∀ᵐ x ∂Q.μ, c ≤ |(Matrix.of ((z n).z.e x)).det|
  /-- (C1) bounded in `H¹` -/
  coframe_bounded : H1Bounded Q (fun n => coframeC (z n).z.e) (fun n => coframeGrad (z n).z.e)
  /-- (C1) common compact screen for the first-derivative packet -/
  coframe_screen : HasCommonCompactScreen Q (fun n => coframeJetPacket (z n).z.e)
  /-- (C2) connections precompact in `L⁴` -/
  conn_precompact : LpPrecompact 4 Q.μ (fun n => (z n).z.A)
  /-- (C2) curvatures bounded in `L²` -/
  curv_bounded : LpBounded 2 Q.μ (fun n => curvatureF (z n).z.A)
  /-- (C2) common compact screen for the curvature packet -/
  curv_screen : HasCommonCompactScreen Q (fun n => curvaturePacket (z n).z.A)
  /-- (C3) Higgs fields bounded in `H¹` -/
  higgs_bounded : H1Bounded Q (fun n => (z n).z.H) (fun n => higgsGrad (z n).z.H)
  /-- (C3) covariant gradients bounded in `L²` -/
  covgrad_bounded : LpBounded 2 Q.μ (fun n => covDerivHiggs (z n).z.A (z n).z.H)
  /-- (C3) common compact screen for the covariant gradients -/
  covgrad_screen : HasCommonCompactScreen Q (fun n => covGradPacket (z n).z.A (z n).z.H)
  /-- (C3) Orlicz condition: an increasing superlinear `Φ` with `sup_h ∫_K Φ(|H_h|⁴) dV₀ < ∞` -/
  orlicz : ∃ Φ : ℝ → ℝ, Monotone Φ ∧ Tendsto (fun t => Φ t / t) atTop atTop ∧
    ∃ M : ℝ, ∀ n, ∫⁻ x in Q.set, ENNReal.ofReal (Φ (higgsNorm ((z n).z.H x) ^ 4)) ≤
      ENNReal.ofReal M
  /-- (C4) spinor route (C4a) or (C4b) -/
  spinor_route : SpinorScreenRoute Q z ∨ DiracStabilityRoute Q z
  /-- (C5) banks in a compact subset of `κ, g_j, λ_H > 0` -/
  bank_compact : ∃ P, IsCompactBankSet P ∧ ∀ n, θ n ∈ P

/-! ### `def:strong-packet` -/

/-- The local convergences of `def:strong-packet` on one chart. -/
structure StrongPacketOn (Q : ChartBox T) (z : ℕ → SmoothFields T left) (L : LimitFields C) :
    Prop where
  /-- `e_h → e` in `L^∞(K)` -/
  coframe_Linfty : LpTendsto ⊤ Q.μ (fun n => (z n).z.e) L.e
  /-- `e_h → e` in `H¹(K)` -/
  coframe_mem : MemH1 Q (coframeC L.e) L.de
  coframe_H1 : H1Tendsto Q (fun n => coframeC (z n).z.e) (fun n => coframeGrad (z n).z.e)
    (coframeC L.e) L.de
  /-- `sup_h (‖e_h‖_∞ + ‖e_h^{-1}‖_∞) < ∞` -/
  coframe_bound : ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ n,
    eLpNorm (z n).z.e ⊤ Q.μ + eLpNorm (fun x => coframeInv ((z n).z.e x)) ⊤ Q.μ ≤ B
  /-- the limit coframe is in the same orientation and signature chart -/
  limit_chart : ∀ᵐ x ∂Q.μ, L.e x ∈ coframeChart
  conn_lie : ∀ᵐ x ∂Q.μ, ∀ μ, L.A x μ ∈ smLie
  conn_mem : MemLp L.A 4 Q.μ
  /-- `A_h → A` in `L⁴(K)` -/
  conn_tendsto : LpTendsto 4 Q.μ (fun n => (z n).z.A) L.A
  curv_mem : MemLp L.F 2 Q.μ
  /-- the limiting curvature is `F_A` -/
  curv_weak : HasWeakCurvature Q L.A L.F
  /-- `F_{A_h} → F_A` in `L²(K)` -/
  curv_tendsto : LpTendsto 2 Q.μ (fun n => curvatureF (z n).z.A) L.F
  higgs_mem : MemLp L.H 4 Q.μ
  /-- `H_h → H` in `L⁴(K)` -/
  higgs_tendsto : LpTendsto 4 Q.μ (fun n => (z n).z.H) L.H
  covgrad_mem : MemLp L.K 2 Q.μ
  /-- the limiting Higgs derivative is `D_AH` -/
  covgrad_weak : HasWeakCovGrad Q L.A L.H L.K
  /-- `D_{A_h}H_h → D_AH` in `L²(K)` -/
  covgrad_tendsto : LpTendsto 2 Q.μ (fun n => covDerivHiggs (z n).z.A (z n).z.H) L.K
  /-- `Ψ_h → Ψ` in `H¹(K)` -/
  spinor_mem : MemH1 Q (spinorC L.Ψ) L.dΨ
  spinor_tendsto : H1Tendsto Q (fun n => spinorC (z n).z.Ψ) (fun n => spinorGrad (z n).z.Ψ)
    (spinorC L.Ψ) L.dΨ
  /-- `Ψ̄_h → Ψ̄` in `H¹(K)` -/
  cospinor_mem : MemH1 Q (spinorC L.Ψb) L.dΨb
  cospinor_tendsto : H1Tendsto Q (fun n => spinorC (z n).z.Ψb) (fun n => spinorGrad (z n).z.Ψb)
    (spinorC L.Ψb) L.dΨb

/-- **`def:strong-packet`: classical strong packet with limit `z = L`**: the local convergences
on every compact chart, `θ_h → θ` and `κ_h, g_{j,h}, λ_{H,h}` bounded away from zero. -/
structure StrongPacket (z : ℕ → SmoothFields T left) (θ : ℕ → CoefficientBank Ysec)
    (L : LimitFields C) (θ₀ : CoefficientBank Ysec) : Prop where
  local_conv : ∀ Q : ChartBox T, StrongPacketOn Q z L
  bank_tendsto : BankTendsto θ θ₀
  bank_pos : ∃ c > (0 : ℝ), ∀ n, c ≤ (θ n).kappa ∧ c ≤ (θ n).g1 ∧ c ≤ (θ n).g2 ∧
    c ≤ (θ n).g3 ∧ c ≤ (θ n).lambdaH

end Defs

omit [Fintype Ysec] in
/-- In a strong packet the limiting coefficient bank is physical (`κ, g_j, λ_H > 0`). -/
theorem StrongPacket.limit_bank_physical {C : Type} [Fintype C] {left : C → Bool}
    {z : ℕ → SmoothFields T left} {θ : ℕ → CoefficientBank Ysec} {L : LimitFields C}
    {θ₀ : CoefficientBank Ysec} (h : StrongPacket z θ L θ₀) : θ₀ ∈ physicalBanks := by
  obtain ⟨c, hc, hθ⟩ := h.bank_pos
  have hcoord : ∀ k : Fin 7, Tendsto (fun n => (bankCoords (θ n)).1 k) atTop
      (𝓝 ((bankCoords θ₀).1 k)) := fun k =>
    ((continuous_apply k).comp continuous_fst).continuousAt.tendsto.comp h.bank_tendsto
  have lim : ∀ k : Fin 7, (∀ n, c ≤ (bankCoords (θ n)).1 k) → 0 < (bankCoords θ₀).1 k :=
    fun k hk => lt_of_lt_of_le hc (ge_of_tendsto' (hcoord k) hk)
  refine ⟨lim 0 fun n => (hθ n).1, lim 2 fun n => (hθ n).2.1, lim 3 fun n => (hθ n).2.2.1,
    lim 4 fun n => (hθ n).2.2.2.1, lim 5 fun n => (hθ n).2.2.2.2⟩

/-! ### Regulator-level notions -/

namespace RegulatorSequence

variable {FC : FermionCarrier Ysec} (reg : RegulatorSequence T FC)

/-- **`def:reduced-topology`** for a regulator sequence: reduced action convergence of the
reconstructed fields on every compact chart. -/
def ReducedActionConvergence (L : LimitFields FC.C) (θ₀ : CoefficientBank Ysec) : Prop :=
  ∀ Q : ChartBox T, ReducedConvergence Q reg.fields reg.bank L θ₀

/-- **`def:reduced-certificate`** for a regulator sequence on a chart. -/
def SatisfiesReducedCertificate (Q : ChartBox T) : Prop :=
  ReducedCertificate Q reg.fields reg.bank

/-- **`def:compactness-certificate`** for a regulator sequence on a chart. -/
def SatisfiesCompactnessCertificate (Q : ChartBox T) : Prop :=
  CompactnessCertificate Q reg.fields reg.bank

/-- **`def:strong-packet`** for a regulator sequence. -/
def HasStrongPacket (L : LimitFields FC.C) (θ₀ : CoefficientBank Ysec) : Prop :=
  StrongPacket reg.fields reg.bank L θ₀

end RegulatorSequence

/-! ### Elementary facts for constant sequences -/

section Const

theorem pd_const' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (c : F) (i : Fin 4)
    (x : E4) : pd (fun _ : E4 => c) i x = 0 := by
  simp [pd]

theorem h1Bounded_const (Q : ChartBox T) (u₀ : ι' → ℂ) :
    H1Bounded Q (fun _ _ => u₀) (fun _ _ => 0) := by
  refine ⟨h1Norm Q (fun _ => u₀) (fun _ => 0), ?_, fun _ => le_rfl⟩
  unfold h1Norm
  exact ENNReal.add_ne_top.mpr ⟨(memLp_const u₀).eLpNorm_ne_top, by simp⟩

theorem h1Tendsto_const (Q : ChartBox T) (u : E4 → ι' → ℂ) (g : E4 → Fin 4 → ι' → ℂ) :
    H1Tendsto Q (fun _ => u) (fun _ => g) u g := by
  simp [H1Tendsto, h1Norm]

theorem lpTendsto_const {F : Type*} [NormedAddCommGroup F] (p : ℝ≥0∞) (μ : Measure E4)
    (u : E4 → F) : LpTendsto p μ (fun _ => u) u := by
  simp [LpTendsto]

theorem lpBounded_const {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞} {μ : Measure E4}
    {u : E4 → F} (hu : MemLp u p μ) : LpBounded p μ (fun _ => u) :=
  ⟨eLpNorm u p μ, hu.eLpNorm_ne_top, fun _ => le_rfl⟩

theorem lpPrecompact_const {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞} {μ : Measure E4}
    {u : E4 → F} (hu : MemLp u p μ) : LpPrecompact p μ (fun _ => u) :=
  ⟨fun _ => hu, fun ε hε => ⟨{0}, fun _ => ⟨0, by simp, by simp [hε]⟩⟩⟩

omit [Fintype ι'] in
theorem memH1_const (Q : ChartBox T) (u₀ : ι' → ℂ) : MemH1 Q (fun _ => u₀) (fun _ _ => 0) :=
  fun c => SobolevOpen.memW12_const_box Q.a Q.b (u₀ c)

theorem weakH1Tendsto_const (Q : ChartBox T) (u₀ : ι' → ℂ) :
    WeakH1Tendsto Q (fun _ _ => u₀) (fun _ _ => 0) (fun _ => u₀) (fun _ _ => 0) :=
  ⟨fun _ => memH1_const Q u₀, memH1_const Q u₀, h1Bounded_const Q u₀,
    fun _ _ _ => tendsto_const_nhds, fun _ _ _ _ => tendsto_const_nhds⟩

theorem hasWeakCurvature_zero (Q : ChartBox T) : HasWeakCurvature Q 0 0 := by
  intro μ ν i j φ _
  simp [comm, mmul]

theorem hasWeakCovGrad_zero (Q : ChartBox T) : HasWeakCovGrad Q 0 0 0 := by
  intro μ i φ _
  simp [higgsAct]

theorem coframeGrad_const (e₀ : CoframeFibre) : coframeGrad (fun _ : E4 => e₀) = 0 := by
  funext x i p
  simp [coframeGrad, pd_const']

theorem spinorGrad_zero {C : Type} [Fintype C] : spinorGrad (0 : E4 → SpinorFibre C) = 0 := by
  funext x i p
  simp [spinorGrad, pd]

theorem curvatureF_zero : curvatureF 0 = 0 := by
  funext x μ ν i j
  simp [curvatureF, pd, comm]

theorem covDerivHiggs_zero : covDerivHiggs 0 0 = 0 := by
  funext x μ i
  simp [covDerivHiggs, pd, higgsAct]

theorem higgsGrad_zero : higgsGrad (0 : E4 → HiggsFibre) = 0 := by
  funext x i
  simp [higgsGrad, pd]

theorem matrix_of_flatCoframe : Matrix.of flatCoframe = 1 := by
  ext i j
  simp [flatCoframe, Matrix.one_apply]

theorem flatCoframe_mem_chart : flatCoframe ∈ coframeChart :=
  ⟨by rw [matrix_of_flatCoframe, Matrix.det_one]; exact one_pos, by simp [flatCoframe]⟩

theorem isCompactCoframeSet_flat : IsCompactCoframeSet {flatCoframe} :=
  ⟨isCompact_singleton, singleton_subset_iff.mpr flatCoframe_mem_chart⟩

end Const

/-! ### Non-vacuity: the flat regulator -/

/-- A physical coefficient bank (`κ = g_j = λ_H = 1`, `Λ = v_H = 0`, `𝐘 = 0`). -/
def physicalBank : CoefficientBank Unit := ⟨1, 0, 1, 1, 1, 1, 0, fun _ => 0⟩

theorem physicalBank_mem : physicalBank ∈ physicalBanks :=
  ⟨one_pos, one_pos, one_pos, one_pos, one_pos⟩

theorem isCompactBankSet_physical : IsCompactBankSet {physicalBank} :=
  ⟨by rw [image_singleton]; exact isCompact_singleton,
    singleton_subset_iff.mpr physicalBank_mem⟩

/-- The one-site flat interface of `trivialGeometryInterface`, with the physical bank. -/
def flatInterface (h : ℝ) : TabulatedFiniteInterface h :=
  TabulatedFiniteInterface.ofTable h .minimal Unit ℝ (fun _ _ => 1) (fun _ _ => by simp)
    (fun _ _ => by simp) (fun _ _ => 0) Unit physicalBank
    (fun _ => 0) (fun _ q => q)
    (fun _ _ _ => by simp)
    (fun _ _ _ _ _ => by simp)
    (fun _ => 0) (fun _ => 0) 1 one_pos
    (by simp)
    (fun _ _ => rfl)
    ⊤ LinearMap.id
    (fun _ _ => rfl)
    (fun v => by rw [LinearMap.id_apply]; exact real_inner_self_nonneg)
    (fun v _ hv => by
      rw [LinearMap.id_apply, real_inner_self_eq_norm_sq]
      exact pow_pos (norm_pos_iff.mpr hv) 2)

/-- **The flat regulator**: constant identity coframe, zero gauge, Higgs and spinor fields,
physical bank, zero test lifts, over the cutoffs `1/(n+1)`. -/
def flatRegulator (T : ℝ) : RegulatorSequence T (trivialCarrier Unit) where
  r0 := 4
  four_le_r0 := le_rfl
  cutoff n := 1 / ((n : ℝ) + 1)
  cutoff_pos n := by positivity
  cutoff_tendsto := tendsto_one_div_add_atTop_nhds_zero_nat
  iface n := flatInterface _
  yukawaEquiv _ := Equiv.refl _
  config _ := (0 : ℝ)
  recon _ _ := constFields T _ 0 (fun _ => smLie.zero_mem) 0
  gravity_differentiable _ := differentiableAt_const _
  matter_differentiable _ := differentiableAt_const _
  sitePos _ _ := (0, 0)
  siteComp _ _ := LinearMap.id
  siteComp_sum _ q := by show ∑ _x : Unit, q = q; simp
  siteComp_idem _ _ _ := rfl
  siteComp_orth _ x y _ h := absurd (Subsingleton.elim (α := Unit) x y) h
  coframe_local _ _ q q' h := by simp only [LinearMap.id_apply] at h; rw [h]
  higgs_local _ _ q q' h := by simp only [LinearMap.id_apply] at h; rw [h]
  enlarge K := K.enlarge
  enlarge_sub K := K.subset_interior_enlarge
  lift _ _ := 0
  lift_support _ _ _ _ _ := by simp

/-- The flat limit fields. -/
def flatLimit : LimitFields Unit :=
  ⟨fun _ => flatCoframe, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

section FlatFacts

variable (T : ℝ) (n : ℕ)

@[simp] theorem flat_e : ((flatRegulator T).fields n).z.e = fun _ => flatCoframe := rfl
@[simp] theorem flat_A : ((flatRegulator T).fields n).z.A = 0 := rfl
@[simp] theorem flat_H : ((flatRegulator T).fields n).z.H = 0 := rfl
@[simp] theorem flat_Ψ : ((flatRegulator T).fields n).z.Ψ = 0 := rfl
@[simp] theorem flat_Ψb : ((flatRegulator T).fields n).z.Ψb = 0 := rfl
@[simp] theorem flat_bank : (flatRegulator T).bank n = physicalBank := rfl

end FlatFacts

theorem spinorC_zero {C : Type} [Fintype C] :
    spinorC (0 : E4 → SpinorFibre C) = fun _ _ => 0 := rfl

theorem coframeJetPacket_flat :
    coframeJetPacket (fun _ : E4 => flatCoframe) = fun _ _ => 0 := by
  funext x q
  simp [coframeJetPacket, coframeGrad_const]

theorem curvaturePacket_zero : curvaturePacket 0 = fun _ _ => 0 := by
  funext x q
  simp [curvaturePacket, curvatureF_zero]

theorem covGradPacket_zero : covGradPacket 0 0 = fun _ _ => 0 := by
  funext x q
  simp [covGradPacket, covDerivHiggs_zero]

theorem spinorJetPacket_zero {C : Type} [Fintype C] :
    spinorJetPacket (0 : E4 → SpinorFibre C) = fun _ _ => 0 := by
  funext x q
  simp [spinorJetPacket, spinorGrad_zero]

/-- **Non-vacuity of `def:reduced-certificate`**: the flat regulator satisfies (R1)–(R5) on
every chart. -/
theorem flatRegulator_reducedCertificate (T : ℝ) (Q : ChartBox T) :
    (flatRegulator T).SatisfiesReducedCertificate Q where
  coframe_chart := ⟨{flatCoframe}, isCompactCoframeSet_flat,
    fun n => Eventually.of_forall fun x => rfl⟩
  coframe_bounded := by
    simp only [flat_e, coframeGrad_const]
    exact h1Bounded_const Q _
  coframe_screen := by
    simp only [flat_e, coframeJetPacket_flat]
    exact hasCommonCompactScreen_zero Q
  conn_precompact := by
    simp only [flat_A]
    exact lpPrecompact_const MemLp.zero
  curv_bounded := by
    simp only [flat_A, curvatureF_zero]
    exact lpBounded_const MemLp.zero
  curv_screen := by
    simp only [flat_A, curvaturePacket_zero]
    exact hasCommonCompactScreen_zero Q
  higgs_bounded := by
    simp only [flat_H]
    exact lpBounded_const MemLp.zero
  covgrad_bounded := by
    simp only [flat_A, flat_H, covDerivHiggs_zero]
    exact lpBounded_const MemLp.zero
  covgrad_screen := by
    simp only [flat_A, flat_H, covGradPacket_zero]
    exact hasCommonCompactScreen_zero Q
  spinor_bounded := by
    simp only [flat_Ψ, spinorC_zero, spinorGrad_zero]
    exact h1Bounded_const Q 0
  cospinor_bounded := by
    simp only [flat_Ψb, spinorC_zero, spinorGrad_zero]
    exact h1Bounded_const Q 0
  bank_compact := ⟨{physicalBank}, isCompactBankSet_physical, fun n => by simp⟩

/-- **Non-vacuity of `def:compactness-certificate`** (route (C4a)): the flat regulator satisfies
(C1)–(C5) on every chart. -/
theorem flatRegulator_compactnessCertificate (T : ℝ) (Q : ChartBox T) :
    (flatRegulator T).SatisfiesCompactnessCertificate Q where
  coframe_precompact := by
    simp only [flat_e]
    exact lpPrecompact_const (memLp_const _)
  coframe_nondegenerate := by
    refine ⟨1, one_pos, fun n => Eventually.of_forall fun x => ?_⟩
    simp only [flat_e, matrix_of_flatCoframe, Matrix.det_one, abs_one, le_refl]
  coframe_bounded := (flatRegulator_reducedCertificate T Q).coframe_bounded
  coframe_screen := (flatRegulator_reducedCertificate T Q).coframe_screen
  conn_precompact := (flatRegulator_reducedCertificate T Q).conn_precompact
  curv_bounded := (flatRegulator_reducedCertificate T Q).curv_bounded
  curv_screen := (flatRegulator_reducedCertificate T Q).curv_screen
  higgs_bounded := by
    simp only [flat_H, higgsGrad_zero]
    exact h1Bounded_const Q 0
  covgrad_bounded := (flatRegulator_reducedCertificate T Q).covgrad_bounded
  covgrad_screen := (flatRegulator_reducedCertificate T Q).covgrad_screen
  orlicz := by
    refine ⟨Real.exp, Real.exp_monotone, ?_, (volume Q.set).toReal, fun n => ?_⟩
    · simpa only [pow_one] using Real.tendsto_exp_div_pow_atTop 1
    · simp only [flat_H, Pi.zero_apply, higgsNorm, map_zero, Finset.sum_const_zero,
        Real.sqrt_zero]
      norm_num
      exact (ENNReal.ofReal_toReal (SobolevOpen.volume_box_ne_top Q.a Q.b : volume Q.set ≠ ⊤)).ge
  spinor_route := Or.inl
    ⟨by simp only [flat_Ψ, spinorC_zero]; exact lpPrecompact_const MemLp.zero,
    by simp only [flat_Ψb, spinorC_zero]; exact lpPrecompact_const MemLp.zero,
    (flatRegulator_reducedCertificate T Q).spinor_bounded,
    (flatRegulator_reducedCertificate T Q).cospinor_bounded,
    by simp only [flat_Ψ, spinorJetPacket_zero]; exact hasCommonCompactScreen_zero Q,
    by simp only [flat_Ψb, spinorJetPacket_zero]; exact hasCommonCompactScreen_zero Q⟩
  bank_compact := (flatRegulator_reducedCertificate T Q).bank_compact

/-- **Non-vacuity of the hypotheses of `prop:dirac-stability`**: the zero sequence with
`A^0 = 1`, `A^j = 0`, `B = 0`. -/
theorem diracStabilityHyp_zero (t₀ t₁ : ℝ) {N : Type} [Fintype N] :
    DiracStabilityHyp t₀ t₁ (fun (_ : ℕ) (_ : E4) => (0 : N → ℂ)) := by
  classical
  refine ⟨fun _ μ _ i j => if μ = 0 ∧ i = j then 1 else 0, fun _ _ => 0, fun _ _ _ _ => rfl,
    fun _ _ _ => rfl, ?_, ⟨1, one_pos, ?_⟩, ⟨1, fun n => ⟨fun μ => ⟨?_, ?_⟩, ?_, ?_⟩⟩, ?_, ?_, ?_⟩
  · intro n μ x i j
    by_cases h1 : μ = 0 <;> by_cases h2 : i = j <;> simp [h1, h2, eq_comm]
  · intro n x _ ξ
    have h : ∀ i, (∑ j, star (ξ i) * (if (0 : Fin 4) = 0 ∧ i = j then (1 : ℂ) else 0) * ξ j) =
        ((‖ξ i‖ ^ 2 : ℝ) : ℂ) := by
      intro i
      simp [Complex.conj_mul']
    have h' : (∑ i, ∑ j, star (ξ i) * (if (0 : Fin 4) = 0 ∧ i = j then (1 : ℂ) else 0) *
        ξ j).re = ∑ i, ‖ξ i‖ ^ 2 := by
      rw [Finset.sum_congr rfl fun i _ => h i, ← Complex.ofReal_sum, Complex.ofReal_re]
    rw [one_mul]
    exact h'.ge
  · intro x _
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i =>
      (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => ?_
    show ‖(if μ = 0 ∧ i = j then (1 : ℂ) else 0)‖ ≤ 1
    split_ifs <;> simp
  · exact ((LipschitzWith.const _).weaken zero_le).lipschitzOnWith
  · exact Eventually.of_forall fun x => by simp
  · intro t _
    unfold spatialH2
    simp
  · intro ε hε
    exact ⟨0, fun m _ n _ => ⟨fun μ x _ => by simp [hε.le],
      Eventually.of_forall fun x => by simp [hε.le]⟩⟩
  · intro ε hε
    exact ⟨0, fun m _ n _ => by simp⟩
  · intro ε hε
    exact ⟨0, fun m _ n _ => by simp⟩

/-- **Non-vacuity of route (C4b)**: the flat regulator satisfies the Lorentzian Dirac-evolution
route on every chart (subslab `[a₀, b₀] × 𝕋³`). -/
theorem flatRegulator_diracRoute (T : ℝ) (Q : ChartBox T) :
    DiracStabilityRoute Q (flatRegulator T).fields :=
  ⟨Q.a 0, Q.b 0, Q.time_pos, Q.lt 0, Q.time_lt, le_rfl, le_rfl,
    by simp only [flat_Ψ, spinorC_zero]; exact diracStabilityHyp_zero _ _,
    by simp only [flat_Ψb, spinorC_zero]; exact diracStabilityHyp_zero _ _⟩

/-- **Non-vacuity of `def:reduced-topology`**: the flat regulator converges to the flat limit
in the reduced action topology on every chart. -/
theorem flatRegulator_reducedActionConvergence (T : ℝ) :
    (flatRegulator T).ReducedActionConvergence flatLimit physicalBank := fun Q =>
  { coframe_chart := ⟨{flatCoframe}, isCompactCoframeSet_flat,
      fun n => Eventually.of_forall fun x => rfl, Eventually.of_forall fun x => rfl⟩
    coframe_mem := memH1_const Q (fun p : Fin 4 × Fin 4 => (flatCoframe p.1 p.2 : ℂ))
    coframe_tendsto := by
      simp only [flat_e, coframeGrad_const]
      exact h1Tendsto_const Q _ _
    conn_lie := Eventually.of_forall fun x μ => smLie.zero_mem
    conn_mem := MemLp.zero
    conn_tendsto := by simp only [flat_A]; exact lpTendsto_const _ _ _
    curv_mem := MemLp.zero
    curv_weak := hasWeakCurvature_zero Q
    curv_tendsto := by simp only [flat_A, curvatureF_zero]; exact lpTendsto_const _ _ _
    higgs_mem := MemLp.zero
    higgs_tendsto := by simp only [flat_H]; exact lpTendsto_const _ _ _
    covgrad_mem := MemLp.zero
    covgrad_weak := hasWeakCovGrad_zero Q
    covgrad_tendsto := by
      simp only [flat_A, flat_H, covDerivHiggs_zero]; exact lpTendsto_const _ _ _
    spinor_weak := by
      simp only [flat_Ψ, spinorC_zero, spinorGrad_zero]
      exact weakH1Tendsto_const Q 0
    cospinor_weak := by
      simp only [flat_Ψb, spinorC_zero, spinorGrad_zero]
      exact weakH1Tendsto_const Q 0
    bank_compact := ⟨{physicalBank}, isCompactBankSet_physical, fun n => by simp⟩
    bank_tendsto := by
      unfold BankTendsto
      simp only [flat_bank]
      exact tendsto_const_nhds }

/-- **Non-vacuity of `def:strong-packet`**: the flat regulator has a classical strong packet
with the flat limit. -/
theorem flatRegulator_strongPacket (T : ℝ) :
    (flatRegulator T).HasStrongPacket flatLimit physicalBank where
  local_conv Q :=
    { coframe_Linfty := by simp only [flat_e]; exact lpTendsto_const _ _ _
      coframe_mem := memH1_const Q (fun p : Fin 4 × Fin 4 => (flatCoframe p.1 p.2 : ℂ))
      coframe_H1 := (flatRegulator_reducedActionConvergence T Q).coframe_tendsto
      coframe_bound := by
        simp only [flat_e]
        exact ⟨_, ENNReal.add_ne_top.mpr ⟨(memLp_const flatCoframe).eLpNorm_ne_top,
          (memLp_const (coframeInv flatCoframe)).eLpNorm_ne_top⟩, fun n => le_rfl⟩
      limit_chart := Eventually.of_forall fun x => flatCoframe_mem_chart
      conn_lie := Eventually.of_forall fun x μ => smLie.zero_mem
      conn_mem := MemLp.zero
      conn_tendsto := (flatRegulator_reducedActionConvergence T Q).conn_tendsto
      curv_mem := MemLp.zero
      curv_weak := hasWeakCurvature_zero Q
      curv_tendsto := (flatRegulator_reducedActionConvergence T Q).curv_tendsto
      higgs_mem := MemLp.zero
      higgs_tendsto := by simp only [flat_H]; exact lpTendsto_const _ _ _
      covgrad_mem := MemLp.zero
      covgrad_weak := hasWeakCovGrad_zero Q
      covgrad_tendsto := (flatRegulator_reducedActionConvergence T Q).covgrad_tendsto
      spinor_mem := memH1_const Q 0
      spinor_tendsto := by
        simp only [flat_Ψ, spinorC_zero, spinorGrad_zero]
        exact h1Tendsto_const Q _ _
      cospinor_mem := memH1_const Q 0
      cospinor_tendsto := by
        simp only [flat_Ψb, spinorC_zero, spinorGrad_zero]
        exact h1Tendsto_const Q _ _ }
  bank_tendsto := by
    unfold BankTendsto
    simp only [flat_bank]
    exact tendsto_const_nhds
  bank_pos := ⟨1, one_pos, fun n => by simp [physicalBank]⟩

end EinsteinSM
end RenewalGeometry
