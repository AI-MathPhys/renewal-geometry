/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import MathPhys.FieldTheory.Continuum.EinsteinSMContinuumAction
import MathPhys.FieldTheory.Analysis.SobolevBoxCompactness
import MathPhys.NCG.OperatorLimits.SMSTPositiveScreenExact

/-!
# Chart boxes, multi-component Sobolev norms and the reduced action topology
  (`def:reduced-topology`, Einstein–Standard-Model action-closure manuscript)

Analytic notions on compact coordinate charts of the lifted cylinder (`ChartBox`): multi-component
`H¹` and `L^p` norms, bounds and convergences (`h1Norm`, `MemH1`, `H1Bounded`, `H1Tendsto`,
`WeakH1Tendsto`, `LpBounded`, `LpTendsto`, `LpPrecompact`), common compact screens
(`CommonCompactScreen`, `HasCommonCompactScreen`), convergence and compactness of coupling
constants (`bankCoords`, `physicalBanks`, `IsCompactBankSet`, `BankTendsto`), the nondegenerate
coframe chart, the classical packets, limit fields with weakly identified curvature and covariant
Higgs gradient, the reduced action convergence `ReducedConvergence`, compact subslabs, elementary
facts for constant sequences and the flat limit.

Split out of `MathPhys.Continuum.EinsteinSMCompactnessCertificates` (which re-exports it,
see its module docstring for the rendering); names are unchanged.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal

noncomputable section

namespace MathPhys
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

/-- The lifted compact subslab `I × Σ`, `I = [t₀, t₁]`. -/
def slab (t₀ t₁ : ℝ) : Set E4 := {x | x 0 ∈ Icc t₀ t₁}

/-- Its fundamental domain `I × [0,1)³`. -/
def slabFund (t₀ t₁ : ℝ) : Set E4 := {x | x 0 ∈ Icc t₀ t₁ ∧ ∀ i : Fin 3, x i.succ ∈ Ico 0 1}

/-- The fundamental cube `[0,1)³` of `Σ = 𝕋³`. -/
def cube3 : Set (Fin 3 → ℝ) := univ.pi fun _ => Ico 0 1

end Defs

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

/-! ### Flat examples -/

/-- A physical coefficient bank (`κ = g_j = λ_H = 1`, `Λ = v_H = 0`, `𝐘 = 0`). -/
def physicalBank : CoefficientBank Unit := ⟨1, 0, 1, 1, 1, 1, 0, fun _ => 0⟩

theorem physicalBank_mem : physicalBank ∈ physicalBanks :=
  ⟨one_pos, one_pos, one_pos, one_pos, one_pos⟩

theorem isCompactBankSet_physical : IsCompactBankSet {physicalBank} :=
  ⟨by rw [image_singleton]; exact isCompact_singleton,
    singleton_subset_iff.mpr physicalBank_mem⟩

/-- The flat limit fields. -/
def flatLimit : LimitFields Unit :=
  ⟨fun _ => flatCoframe, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

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

end EinsteinSM
end MathPhys
