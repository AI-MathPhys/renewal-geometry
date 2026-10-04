/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.KatoInequalitySobolev
import RenewalGeometry.Analysis.CoulombHodgeAbsorption
import RenewalGeometry.Analysis.GaugeCovariantDerivative
import RenewalGeometry.Analysis.W12CompactnessBox
import RenewalGeometry.Continuum.CriticalCurvatureUniformIntegrabilityExact

/-!
# Critical gauge estimates: positive graph control, equivariant tests, Coulomb–Hodge
  absorption and the Uhlenbeck reduction (Einstein–Standard-Model action closure)

Records of the subsection "Equivariant tests and critical gauge compactness" and of
`subsec:critical-quotient`, in the **box rendering** of a bounded four-dimensional chart (a
coordinate box `Q = box a b ⊂ ℝ⁴`; fields with complex components; connections through their
matrix entries; fibre norms the Hermitian / Frobenius ones).

* `critical_positive_graph` (`lem:critical-positive-graph`): Kato–Sobolev
  `‖u‖_4 ≤ C_B(‖u‖_2 + ‖∇^{ref,A}u‖_2)` and the vector graph estimate
  `‖u‖_{H¹} ≤ C_B(1 + M_A)(‖u‖_2 + ‖∇^{ref,A}u‖_2)`, for the representation and its dual, with
  constants independent of the (unitary) connection, hence of the gauge.
* `equivTestSize`, `equivTestSize_gauge` (`lem:equivariant-tests`,
  `eq:equivariant-test-invariance`):
  the covariant test size `𝔫_z(v)` and its exact invariance `𝔫_{u·z}(u·v) = 𝔫_z(v)`.
* `critical_coulomb_hodge_box` (`lem:critical-Coulomb-Hodge`).
* `UhlenbeckSmallEnergyGauge` (named theorem: Uhlenbeck's small-energy Coulomb gauge on balls)
  and `critical_uhlenbeck_of_gauge` (`prop:critical-uhlenbeck` **conditional on that named
  theorem**): finite small-energy cover, local Coulomb gauges with uniform `W^{1,2}` bounds and
  small `L⁴` norms, and after extraction `A_h ⇀ A` in `W^{1,2}`, `A_h → A` in `L^q` (`q < 4`),
  `F_{A_h} ⇀ F_A`.
-/

open MeasureTheory Filter Topology Set Matrix
open scoped ENNReal NNReal ContDiff ComplexConjugate

noncomputable section

namespace RenewalGeometry.CriticalGauge

open SobolevOpen

set_option linter.unusedSectionVars false

/-! ## `lem:critical-positive-graph` -/

/-- **`lem:critical-positive-graph` (box rendering).**  On a coordinate box `Q ⊂ ℝ⁴` (the
normalized chart), for a fibre of rank `m` and a bound `G` on the smooth reference connection,
there is `C_B` such that for every `M_A`, every skew-Hermitian (metric-compatible) reference
connection `Γ` with `|Γ| ≤ G`, every unitary internal connection `A` (skew-Hermitian matrix
entries `ρ(A)_{μce}` with `‖ρ(A)_{μce}‖_{L⁴(Q)} ≤ M_A`) and every section `u` with `W^{1,2}(Q)`
components (in particular every section smooth up to the boundary),
`‖u_c‖_{L⁴} ≤ C_B (‖u‖_2 + ‖∇^{ref,A}u‖_2)` (`eq:critical-Kato-Sobolev`) and
`‖u_c‖_{W^{1,2}} ≤ C_B (1 + M_A)(‖u‖_2 + ‖∇^{ref,A}u‖_2)` (`eq:critical-vector-graph`), and
the same for every dual section `v` with the dual connection.  The constant depends only on `Q`,
`m`, `G`: not on `A`, hence not on the gauge transformation producing `A`. -/
theorem critical_positive_graph {a b : Fin 4 → ℝ} (hab : ∀ i, a i < b i) (m : ℕ) (G : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (MA : ℝ≥0) (Γ A : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ),
      IsSkewHermitianConn Γ → IsSkewHermitianConn A →
      (∀ μ c e, AEStronglyMeasurable (Γ μ c e) (volume.restrict (box a b))) →
      (∀ μ c e x, ‖Γ μ c e x‖ ≤ G) →
      (∀ μ c e, AEStronglyMeasurable (A μ c e) (volume.restrict (box a b))) →
      (∀ μ c e, eLpNorm (A μ c e) 4 (volume.restrict (box a b)) ≤ MA) →
      (∀ (u : Fin m → (Fin 4 → ℝ) → ℂ) (dU : Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ),
        (∀ c, MemW12 (box a b) (u c) (dU c)) → ∀ c,
          eLpNorm (u c) 4 (volume.restrict (box a b)) ≤
            C * (∑ e, eLpNorm (u e) 2 (volume.restrict (box a b)) +
              ∑ e, ∑ μ, eLpNorm (covD dU (fun μ c e x => Γ μ c e x + A μ c e x) u e μ) 2
                (volume.restrict (box a b))) ∧
          w12Norm (box a b) (u c) (dU c) ≤ C * (1 + MA) *
            (∑ e, eLpNorm (u e) 2 (volume.restrict (box a b)) +
              ∑ e, ∑ μ, eLpNorm (covD dU (fun μ c e x => Γ μ c e x + A μ c e x) u e μ) 2
                (volume.restrict (box a b)))) ∧
      (∀ (v : Fin m → (Fin 4 → ℝ) → ℂ) (dV : Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ),
        (∀ c, MemW12 (box a b) (v c) (dV c)) → ∀ c,
          eLpNorm (v c) 4 (volume.restrict (box a b)) ≤
            C * (∑ e, eLpNorm (v e) 2 (volume.restrict (box a b)) +
              ∑ e, ∑ μ, eLpNorm (covD dV (fun μ c e x => dualConn Γ μ c e x +
                dualConn A μ c e x) v e μ) 2 (volume.restrict (box a b))) ∧
          w12Norm (box a b) (v c) (dV c) ≤ C * (1 + MA) *
            (∑ e, eLpNorm (v e) 2 (volume.restrict (box a b)) +
              ∑ e, ∑ μ, eLpNorm (covD dV (fun μ c e x => dualConn Γ μ c e x +
                dualConn A μ c e x) v e μ) 2 (volume.restrict (box a b)))) := by
  have hd : Fintype.card (Fin 4) = 4 := by simp
  obtain ⟨CK, hCK⟩ := kato_sobolev_box hd hab
  obtain ⟨CG, hCG⟩ := covariant_graph_box hd hab m G
  obtain ⟨CGd, hCGd⟩ := covariant_graph_box_dual hd hab m G
  refine ⟨CK + CG + CGd, fun MA Γ A hΓ hA hΓm hΓG hAm hAM => ⟨fun u dU hW c => ⟨?_, ?_⟩,
    fun v dV hW c => ⟨?_, ?_⟩⟩⟩
  · refine (hCK m _ u dU (hΓ.add hA) (fun μ c e => (hΓm μ c e).add (hAm μ c e)) hW c).trans ?_
    gcongr
    exact le_add_right le_self_add
  · refine (hCG MA Γ A u dU hΓ hA hΓm hΓG hAm hAM hW c).trans ?_
    gcongr
    exact le_add_right le_add_self
  · have h𝒜 : IsSkewHermitianConn (fun μ c e x => dualConn Γ μ c e x + dualConn A μ c e x) :=
      (isSkewHermitianConn_dualConn hΓ).add (isSkewHermitianConn_dualConn hA)
    refine (hCK m _ v dV h𝒜 (fun μ c e => (hΓm μ e c).neg.add (hAm μ e c).neg) hW c).trans ?_
    gcongr
    exact le_add_right le_self_add
  · refine (hCGd MA Γ A v dV hΓ hA hΓm hΓG hAm hAM hW c).trans ?_
    gcongr
    exact le_add_self

/-! ## `lem:equivariant-tests`: the covariant test size and its gauge invariance -/

/-- **The covariant test size `𝔫_z(v)`** (`eq:equivariant-test-size`) of a physical test
`v = (k, a, η_H, η_Ψ, η_Ψ̄)` at a field configuration `z`, in the fixed comparison geometry `ρ`:
`‖k‖_{W^{1,∞}}` (entered as the gauge-independent number `Nk`) + `‖a‖_∞ + ‖D_A a‖_2`
(adjoint sector, Frobenius norm) + `‖η_H‖_∞ + ‖D_A η_H‖_2` (Higgs representation,
connection `𝒜_H = ρ_H(A)`) + `‖η_Ψ‖_∞ + ‖∇^{ref,A} η_Ψ‖_2` (spinor representation, total
connection `𝒜_F = Γ_ref + ρ_F(A)`) + `‖η_Ψ̄‖_∞ + ‖∇^{ref,A} η_Ψ̄‖_2` (dual connection
`-𝒜_Fᵀ`).  The `L²` norms of the covariant gradients are `Σ_μ ‖|∇_μ ·|‖_{L²}`. -/
def equivTestSize (ρ : Measure (Fin 4 → ℝ)) (Nk : ℝ≥0∞) {mG mH mF : ℕ}
    (A : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin mG) (Fin mG) ℂ)
    (a : (Fin 4 → ℝ) → Matrix (Fin mG) (Fin mG) ℂ)
    (𝒜H : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin mH) (Fin mH) ℂ) (ηH : (Fin 4 → ℝ) → Fin mH → ℂ)
    (𝒜F : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin mF) (Fin mF) ℂ)
    (ηF ηFb : (Fin 4 → ℝ) → Fin mF → ℂ) : ℝ≥0∞ :=
  Nk + adTestSize ρ A a + vecTestSize ρ 𝒜H ηH + vecTestSize ρ 𝒜F ηF +
    vecTestSize ρ (dualConnM 𝒜F) ηFb

/-- **`eq:equivariant-test-invariance`: `𝔫_{u·z}(u·v) = 𝔫_z(v)`.**  A smooth internal gauge
transformation acts by unitary matrices `u` (adjoint sector), `R_H` (Higgs representation) and
`R_F` (spinor representation); the represented connections transform by `R·𝒜 = R𝒜R^* - ∂R R^*`,
the tests by `a ↦ u a u^*`, `η_H ↦ R_H η_H`, `η_Ψ ↦ R_F η_Ψ`, `η_Ψ̄ ↦ η_Ψ̄ R_F^*`, and the
metric test `k` is unchanged.  Then the covariant test size is exactly invariant. -/
theorem equivTestSize_gauge (ρ : Measure (Fin 4 → ℝ)) (Nk : ℝ≥0∞) {mG mH mF : ℕ}
    {u : (Fin 4 → ℝ) → Matrix (Fin mG) (Fin mG) ℂ} {RH : (Fin 4 → ℝ) → Matrix (Fin mH) (Fin mH) ℂ}
    {RF : (Fin 4 → ℝ) → Matrix (Fin mF) (Fin mF) ℂ}
    (hu : ∀ y, u y ∈ unitaryGroup (Fin mG) ℂ) (hRH : ∀ y, RH y ∈ unitaryGroup (Fin mH) ℂ)
    (hRF : ∀ y, RF y ∈ unitaryGroup (Fin mF) ℂ) (hud : ∀ x, MDiffAt u x)
    (hRHd : ∀ x, MDiffAt RH x) (hRFd : ∀ x, MDiffAt RF x)
    (A : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin mG) (Fin mG) ℂ)
    {a : (Fin 4 → ℝ) → Matrix (Fin mG) (Fin mG) ℂ} (ha : ∀ x, MDiffAt a x)
    (𝒜H : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin mH) (Fin mH) ℂ) {ηH : (Fin 4 → ℝ) → Fin mH → ℂ}
    (hηH : ∀ x, VDiffAt ηH x) (𝒜F : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin mF) (Fin mF) ℂ)
    {ηF ηFb : (Fin 4 → ℝ) → Fin mF → ℂ} (hηF : ∀ x, VDiffAt ηF x) (hηFb : ∀ x, VDiffAt ηFb x) :
    equivTestSize ρ Nk (gaugeConn u A) (fun y => u y * a y * star (u y)) (gaugeConn RH 𝒜H)
        (fun y => RH y *ᵥ ηH y) (gaugeConn RF 𝒜F) (fun y => RF y *ᵥ ηF y)
        (fun y => dualGauge RF y *ᵥ ηFb y) =
      equivTestSize ρ Nk A a 𝒜H ηH 𝒜F ηF ηFb := by
  unfold equivTestSize
  rw [adTestSize_gauge ρ hu hud A ha, vecTestSize_gauge ρ hRH hRHd 𝒜H hηH,
    vecTestSize_gauge ρ hRF hRFd 𝒜F hηF, vecTestSize_gauge_dual ρ hRF hRFd 𝒜F hηFb]

/-- With the spinor connection `𝒜_F = Γ_ref + ρ_F(A)`, where the reference spin connection acts
trivially on the internal factor (commutes with `R_F`), the gauge acts on `ρ_F(A)` only:
`R_F·(Γ + ρ_F(A)) = Γ + R_F·ρ_F(A)`. -/
theorem equivTestSize_gauge_ref (ρ : Measure (Fin 4 → ℝ)) (Nk : ℝ≥0∞) {mG mH mF : ℕ}
    {u : (Fin 4 → ℝ) → Matrix (Fin mG) (Fin mG) ℂ} {RH : (Fin 4 → ℝ) → Matrix (Fin mH) (Fin mH) ℂ}
    {RF : (Fin 4 → ℝ) → Matrix (Fin mF) (Fin mF) ℂ}
    (hu : ∀ y, u y ∈ unitaryGroup (Fin mG) ℂ) (hRH : ∀ y, RH y ∈ unitaryGroup (Fin mH) ℂ)
    (hRF : ∀ y, RF y ∈ unitaryGroup (Fin mF) ℂ) (hud : ∀ x, MDiffAt u x)
    (hRHd : ∀ x, MDiffAt RH x) (hRFd : ∀ x, MDiffAt RF x)
    (A : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin mG) (Fin mG) ℂ)
    {a : (Fin 4 → ℝ) → Matrix (Fin mG) (Fin mG) ℂ} (ha : ∀ x, MDiffAt a x)
    (𝒜H : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin mH) (Fin mH) ℂ) {ηH : (Fin 4 → ℝ) → Fin mH → ℂ}
    (hηH : ∀ x, VDiffAt ηH x) (Γ ρF : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin mF) (Fin mF) ℂ)
    (hΓ : ∀ μ y, RF y * Γ μ y = Γ μ y * RF y)
    {ηF ηFb : (Fin 4 → ℝ) → Fin mF → ℂ} (hηF : ∀ x, VDiffAt ηF x) (hηFb : ∀ x, VDiffAt ηFb x) :
    equivTestSize ρ Nk (gaugeConn u A) (fun y => u y * a y * star (u y)) (gaugeConn RH 𝒜H)
        (fun y => RH y *ᵥ ηH y) (fun μ y => Γ μ y + gaugeConn RF ρF μ y)
        (fun y => RF y *ᵥ ηF y) (fun y => dualGauge RF y *ᵥ ηFb y) =
      equivTestSize ρ Nk A a 𝒜H ηH (fun μ y => Γ μ y + ρF μ y) ηF ηFb := by
  have e : (fun μ y => Γ μ y + gaugeConn RF ρF μ y) = gaugeConn RF (fun μ y => Γ μ y + ρF μ y) :=
    funext fun μ => funext fun y => (gaugeConn_add_commuting hRF Γ ρF hΓ μ y).symm
  rw [e]
  exact equivTestSize_gauge ρ Nk hu hRH hRF hud hRHd hRFd A ha 𝒜H hηH _ hηF hηFb

/-! ## `lem:critical-Coulomb-Hodge` -/

/-- **`lem:critical-Coulomb-Hodge` (box rendering).**  On a small-energy Coulomb box `Q`
(rendering of the ball `B`), there is a threshold `δ₀ > 0` (depending only on the dimension and
the matrix size) such that co-closed `W^{1,2}(Q)` connections `A_h, A` with `L⁴(Q)` entry norms
`≤ δ ≤ δ₀`, `A_h → A` in `L²(Q)` and `F_{A_h} → F_A` in `L²(Q)` satisfy `A_h → A` in `L⁴(K)` for
every compact `K ⊂ Q`. -/
theorem critical_coulomb_hodge_box (a b : Fin 4 → ℝ) (m : ℕ) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧ ∀ (A : ℕ → Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ)
      (dA : ℕ → Fin 4 → Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ)
      (A₀ : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ)
      (dA₀ : Fin 4 → Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ) (δ : ℝ≥0), δ ≤ δ₀ →
      (∀ h ν c e, MemW12 (box a b) (A h ν c e) (dA h ν c e)) →
      (∀ ν c e, MemW12 (box a b) (A₀ ν c e) (dA₀ ν c e)) →
      (∀ h c e, ∀ᵐ x ∂(volume.restrict (box a b)), ∑ μ, dA h μ c e μ x = 0) →
      (∀ c e, ∀ᵐ x ∂(volume.restrict (box a b)), ∑ μ, dA₀ μ c e μ x = 0) →
      (∀ h ν c e, eLpNorm (A h ν c e) 4 (volume.restrict (box a b)) ≤ δ) →
      (∀ ν c e, eLpNorm (A₀ ν c e) 4 (volume.restrict (box a b)) ≤ δ) →
      (∀ ν c e, Tendsto (fun h => eLpNorm (fun x => A h ν c e x - A₀ ν c e x) 2
        (volume.restrict (box a b))) atTop (𝓝 0)) →
      (∀ μ ν c e, Tendsto (fun h => eLpNorm (fun x => curvatureW (A h) (dA h) μ ν c e x -
        curvatureW A₀ dA₀ μ ν c e x) 2 (volume.restrict (box a b))) atTop (𝓝 0)) →
      ∀ K : Set (Fin 4 → ℝ), IsCompact K → K ⊆ box a b → ∀ ν c e,
        Tendsto (fun h => eLpNorm (fun x => A h ν c e x - A₀ ν c e x) 4 (volume.restrict K))
          atTop (𝓝 0) :=
  critical_coulomb_hodge (by simp) a b m

/-- Non-vacuity of `critical_coulomb_hodge_box`: the zero connection on the unit box. -/
example : ∀ K : Set (Fin 4 → ℝ), IsCompact K → K ⊆ box 0 1 →
    Tendsto (fun _ : ℕ => eLpNorm (fun x : Fin 4 → ℝ => (0 : ℂ) - 0) 4 (volume.restrict K))
      atTop (𝓝 0) := by
  obtain ⟨δ₀, -, h⟩ := critical_coulomb_hodge_box 0 1 1
  intro K hK hKQ
  have := h (fun _ _ _ _ _ => 0) (fun _ _ _ _ _ _ => 0) (fun _ _ _ _ => 0)
    (fun _ _ _ _ _ => 0) 0 zero_le (fun _ _ _ _ => by simpa using memW12_const_box 0 1 0)
    (fun _ _ _ => by simpa using memW12_const_box 0 1 0) (fun _ _ _ => by simp)
    (fun _ _ => by simp) (fun _ _ _ _ => by simp) (fun _ _ _ => by simp)
    (fun _ _ _ => by simp) (fun _ _ _ _ => by simp [curvatureW]) K hK hKQ 0 0 0
  exact this


/-! ## `prop:critical-uhlenbeck`: reduction to Uhlenbeck's small-energy gauge theorem -/

/-- Matrix-valued connections on `ℝ⁴`. -/
abbrev MConn (m : ℕ) := Fin 4 → (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ

/-- Matrix entries `A_{ν,ce}` of a matrix-valued connection. -/
def entries {m : ℕ} (A : MConn m) : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ :=
  fun ν c e y => A ν y c e

/-- Classical entry gradients `∂_μ A_{ν,ce}`. -/
def entryGrad {m : ℕ} (A : MConn m) : Fin 4 → Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ :=
  fun ν c e μ y => pd (fun y => A ν y c e) μ y

/-- The curvature `F_A = dA + [A ∧ A]` as a vector of `ℂ^{4×4×m×m}`; its Hermitian norm is the
pointwise curvature norm `|F_A|`. -/
def curvVec {m : ℕ} (A : MConn m) (x : Fin 4 → ℝ) :
    EuclideanSpace ℂ (Fin 4 × Fin 4 × Fin m × Fin m) :=
  WithLp.toLp 2 fun p => curvatureW (entries A) (entryGrad A) p.1 p.2.1 p.2.2.1 p.2.2.2 x

/-- The curvature energy `∫_S |F_A|²`. -/
def curvEnergy {m : ℕ} (A : MConn m) (S : Set (Fin 4 → ℝ)) : ℝ≥0∞ :=
  ∫⁻ x in S, ‖curvVec A x‖ₑ ^ 2

/-- The Euclidean ball `{x : |x - c| < r}`. -/
def eBall (c : Fin 4 → ℝ) (r : ℝ) : Set (Fin 4 → ℝ) := {x | ∑ i, (x i - c i) ^ 2 < r ^ 2}

/-- A smooth connection of a unitary bundle: smooth skew-Hermitian matrix-valued one-form. -/
structure IsSmoothUnitaryConn {m : ℕ} (A : MConn m) : Prop where
  smooth : ∀ μ c e, ContDiff ℝ ∞ (fun y => A μ y c e)
  skew : ∀ μ y, star (A μ y) = -A μ y

/-- **Uhlenbeck's small-energy Coulomb gauge theorem** (K. Uhlenbeck, *Connections with `L^p`
bounds on curvature*, Comm. Math. Phys. 83 (1982), Thm 1.3, case `p = n/2 = 2`), stated as a
named hypothesis for unitary groups `U(m)` on Euclidean balls of `ℝ⁴`: there are `ε_U > 0` and a
scale-invariant `C_U` such that for every ball `B_r(c)` there is `C_r` with the property that
every smooth unitary connection with `∫_{B_r(c)} |F_A|² ≤ ε_U` has a gauge transformation `R`
(unitary-valued and smooth on the ball) for which `Ã = R·A = R A R^* - ∂R R^*` is in Coulomb gauge
`d^*Ã = 0` on the ball, lies in `W^{1,2}(B_r(c))` with `‖Ã‖_{W^{1,2}} ≤ C_r ‖F_A‖_{L²}`, and
`‖Ã‖_{L⁴} ≤ C_U ‖F_A‖_{L²}`.  This is research-level elliptic gauge theory, **not proved here**;
`critical_uhlenbeck_of_gauge` shows that `prop:critical-uhlenbeck` follows from it. -/
def UhlenbeckSmallEnergyGauge (m : ℕ) : Prop :=
  ∃ εU : ℝ≥0, 0 < εU ∧ ∃ CU : ℝ≥0, ∀ (c : Fin 4 → ℝ) (r : ℝ), 0 < r → ∃ Cr : ℝ≥0,
    ∀ A : MConn m, IsSmoothUnitaryConn A → curvEnergy A (eBall c r) ≤ εU →
      ∃ R : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ,
        (∀ y ∈ eBall c r, R y ∈ unitaryGroup (Fin m) ℂ) ∧
        (∀ c' e', ContDiffOn ℝ ∞ (fun y => R y c' e') (eBall c r)) ∧
        (∀ x ∈ eBall c r, ∀ c' e', ∑ μ, entryGrad (gaugeConn R A) μ c' e' μ x = 0) ∧
        (∀ ν c' e', MemW12 (eBall c r) (entries (gaugeConn R A) ν c' e')
          (entryGrad (gaugeConn R A) ν c' e')) ∧
        (∀ ν c' e', w12Norm (eBall c r) (entries (gaugeConn R A) ν c' e')
          (entryGrad (gaugeConn R A) ν c' e') ≤ Cr * curvEnergy A (eBall c r) ^ (1 / 2 : ℝ)) ∧
        (∀ ν c' e', eLpNorm (entries (gaugeConn R A) ν c' e') 4 (volume.restrict (eBall c r)) ≤
          CU * curvEnergy A (eBall c r) ^ (1 / 2 : ℝ))

/-! ### Elementary geometry of the cover -/

theorem isOpen_eBall (c : Fin 4 → ℝ) (r : ℝ) : IsOpen (eBall c r) :=
  isOpen_lt (continuous_finset_sum _ fun i _ =>
    ((continuous_apply i).sub continuous_const).pow 2) continuous_const

theorem eBall_subset_ball (c : Fin 4 → ℝ) {r : ℝ} (hr : 0 < r) :
    eBall c r ⊆ Metric.ball c r := by
  intro x hx
  rw [Metric.mem_ball, dist_pi_lt_iff hr]
  intro i
  rw [Real.dist_eq, ← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq hr.le]
  refine Real.sqrt_lt_sqrt (sq_nonneg _) (lt_of_le_of_lt ?_ hx)
  exact Finset.single_le_sum (f := fun i => (x i - c i) ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ i)

/-- The inner cube of half-side `r/2` lies in the Euclidean ball of radius `r` (dimension 4). -/
theorem box_subset_eBall (c : Fin 4 → ℝ) {r : ℝ} (hr : 0 < r) :
    box (fun i => c i - r / 2) (fun i => c i + r / 2) ⊆ eBall c r := by
  intro x hx
  rw [mem_box] at hx
  show ∑ i, (x i - c i) ^ 2 < r ^ 2
  have h : ∀ i ∈ (Finset.univ : Finset (Fin 4)), (x i - c i) ^ 2 < (r / 2) ^ 2 := by
    intro i _
    have h1 := hx i
    exact sq_lt_sq' (by linarith [h1.1]) (by linarith [h1.2])
  calc ∑ i, (x i - c i) ^ 2 < ∑ _i : Fin 4, (r / 2) ^ 2 :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty h
    _ = r ^ 2 := by simp; ring

theorem _root_.RenewalGeometry.SobolevOpen.MemW12.mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω Ω' : Set (ι → ℝ)}
    {u : (ι → ℝ) → ℂ} {g : ι → (ι → ℝ) → ℂ} (hW : MemW12 Ω u g) (h : Ω' ⊆ Ω) :
    MemW12 Ω' u g :=
  ⟨hW.memLp.mono_measure (Measure.restrict_mono h le_rfl),
    fun i => (hW.memLp_grad i).mono_measure (Measure.restrict_mono h le_rfl),
    fun i φ hφ => hW.weak i φ (hφ.mono h)⟩

theorem w12Norm_mono {ι : Type*} [Fintype ι] {Ω Ω' : Set (ι → ℝ)} (h : Ω' ⊆ Ω)
    (u : (ι → ℝ) → ℂ) (g : ι → (ι → ℝ) → ℂ) : w12Norm Ω' u g ≤ w12Norm Ω u g := by
  exact add_le_add (eLpNorm_mono_measure _ (Measure.restrict_mono h le_rfl))
    (Finset.sum_le_sum fun i _ => eLpNorm_mono_measure _ (Measure.restrict_mono h le_rfl))

/-- Common subsequence for finitely many subsequence-stable properties. -/
theorem exists_common_subseq {N : ℕ} (P : Fin N → (ℕ → ℕ) → Prop)
    (hP : ∀ j (φ : ℕ → ℕ), StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ P j (φ ∘ ψ))
    (hmono : ∀ j (φ ψ : ℕ → ℕ), StrictMono ψ → P j φ → P j (φ ∘ ψ)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ j, P j φ := by
  have key : ∀ n : ℕ, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ j : Fin N, (j : ℕ) < n → P j φ := by
    intro n
    induction n with
    | zero => exact ⟨id, strictMono_id, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    | succ n ih =>
      obtain ⟨φ, hφ, hP'⟩ := ih
      by_cases hn : n < N
      · obtain ⟨ψ, hψ, hj⟩ := hP ⟨n, hn⟩ φ hφ
        refine ⟨φ ∘ ψ, hφ.comp hψ, fun j hjn => ?_⟩
        by_cases hjn' : (j : ℕ) = n
        · have : j = ⟨n, hn⟩ := Fin.ext hjn'
          subst this; exact hj
        · exact hmono j φ ψ hψ (hP' j (by omega))
      · exact ⟨φ, hφ, fun j hj => hP' j (by have := j.isLt; omega)⟩
  obtain ⟨φ, hφ, h⟩ := key N
  exact ⟨φ, hφ, fun j => h j j.isLt⟩

/-- Smallness: if `ε_* ≤ (η/(C_U+1))²` and `E ≤ ε_*` then `C_U E^{1/2} ≤ η`. -/
theorem mul_rpow_half_le {CU η εs : ℝ≥0} (hεs : εs ≤ (η / (CU + 1)) ^ 2) {E : ℝ≥0∞}
    (hE : E ≤ εs) : (CU : ℝ≥0∞) * E ^ (1 / 2 : ℝ) ≤ η := by
  have h1 : E ^ (1 / 2 : ℝ) ≤ ((εs ^ (1 / 2 : ℝ) : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_rpow_of_nonneg _ (by norm_num)]
    exact ENNReal.rpow_le_rpow hE (by norm_num)
  have h2 : εs ^ (1 / 2 : ℝ) ≤ η / (CU + 1) := by
    calc εs ^ (1 / 2 : ℝ) ≤ ((η / (CU + 1)) ^ 2) ^ (1 / 2 : ℝ) :=
          NNReal.rpow_le_rpow hεs (by norm_num)
      _ = η / (CU + 1) := by
          rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul]; norm_num
  have h3 : CU * (η / (CU + 1)) ≤ η := by
    rw [← NNReal.coe_le_coe]; push_cast
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [η.2, CU.2]
  calc (CU : ℝ≥0∞) * E ^ (1 / 2 : ℝ) ≤ CU * ((εs ^ (1 / 2 : ℝ) : ℝ≥0) : ℝ≥0∞) :=
        mul_le_mul_right h1 _
    _ ≤ η := by
        rw [← ENNReal.coe_mul, ENNReal.coe_le_coe]
        exact (mul_le_mul_right h2 CU).trans h3


/-! ### Compactness of a gauged sequence on one cube -/

/-- The conclusion of `prop:critical-uhlenbeck` on one Coulomb cube `Q` along a subsequence `φ`:
there are limits `A_∞ ∈ W^{1,2}(Q)` (weak gradients `G`) with `C_{φ k} → A_∞` in every `L^q(Q)`,
`1 ≤ q < 4`, `∂C_{φ k} ⇀ G` weakly in `L²(Q)` (weak `W^{1,2}` convergence), and
`F_{C_{φ k}} → F_{A_∞}` against every bounded measurable weight (weak curvature convergence). -/
def CoulombLimit {m : ℕ} (Q : Set (Fin 4 → ℝ)) (C : ℕ → MConn m) (φ : ℕ → ℕ) : Prop :=
  ∃ (Ainf : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ)
    (G : Fin 4 → Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ),
    (∀ ν c e, MemW12 Q (Ainf ν c e) (G ν c e)) ∧
    (∀ ν c e (q : ℝ≥0∞), 1 ≤ q → q < 4 → Tendsto (fun k => eLpNorm
      (entries (C (φ k)) ν c e - Ainf ν c e) q (volume.restrict Q)) atTop (𝓝 0)) ∧
    (∀ ν c e μ (w : (Fin 4 → ℝ) → ℝ), MemLp w 2 (volume.restrict Q) →
      Tendsto (fun k => ∫ x, w x • entryGrad (C (φ k)) ν c e μ x ∂(volume.restrict Q)) atTop
        (𝓝 (∫ x, w x • G ν c e μ x ∂(volume.restrict Q)))) ∧
    (∀ μ ν c e (w : (Fin 4 → ℝ) → ℝ), MemLp w ⊤ (volume.restrict Q) →
      Tendsto (fun k => ∫ x, w x • curvatureW (entries (C (φ k))) (entryGrad (C (φ k))) μ ν c e x
        ∂(volume.restrict Q)) atTop
        (𝓝 (∫ x, w x • curvatureW Ainf G μ ν c e x ∂(volume.restrict Q))))

theorem CoulombLimit.comp {m : ℕ} {Q : Set (Fin 4 → ℝ)} {C : ℕ → MConn m} {φ ψ : ℕ → ℕ}
    (h : CoulombLimit Q C φ) (hψ : StrictMono ψ) : CoulombLimit Q C (φ ∘ ψ) := by
  obtain ⟨Ainf, G, h1, h2, h3, h4⟩ := h
  exact ⟨Ainf, G, h1, fun ν c e q hq1 hq4 => (h2 ν c e q hq1 hq4).comp hψ.tendsto_atTop,
    fun ν c e μ w hw => (h3 ν c e μ w hw).comp hψ.tendsto_atTop,
    fun μ ν c e w hw => (h4 μ ν c e w hw).comp hψ.tendsto_atTop⟩

/-- **Weak `W^{1,2}` compactness and Rellich for gauged connections on one cube.**  A sequence
of connections whose entries are bounded in `W^{1,2}(Q)` has, along every subsequence, a further
subsequence with the `CoulombLimit` property. -/
theorem exists_coulombLimit {m : ℕ} {lo hi : Fin 4 → ℝ} (hlh : ∀ i, lo i < hi i)
    {C : ℕ → MConn m}
    (hW : ∀ k ν c e, MemW12 (box lo hi) (entries (C k) ν c e) (entryGrad (C k) ν c e))
    {B : ℝ≥0∞} (hBt : B ≠ ⊤)
    (hB : ∀ k ν c e, w12Norm (box lo hi) (entries (C k) ν c e) (entryGrad (C k) ν c e) ≤ B)
    (φ : ℕ → ℕ) : ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ CoulombLimit (box lo hi) C (φ ∘ ψ) := by
  set ρ := volume.restrict (box lo hi)
  have : IsFiniteMeasure ρ := isFiniteMeasure_restrict.mpr (volume_box_ne_top lo hi)
  set u : ℕ → Fin 4 × Fin m × Fin m → (Fin 4 → ℝ) → ℂ :=
    fun k p => entries (C (φ k)) p.1 p.2.1 p.2.2 with hu
  set g : ℕ → Fin 4 × Fin m × Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ :=
    fun k p => entryGrad (C (φ k)) p.1 p.2.1 p.2.2 with hg
  have hWu : ∀ k p, MemW12 (box lo hi) (u k p) (g k p) := fun k p => hW (φ k) p.1 p.2.1 p.2.2
  have hBu : ∀ k p, w12Norm (box lo hi) (u k p) (g k p) ≤ B := fun k p =>
    hB (φ k) p.1 p.2.1 p.2.2
  have hd : Fintype.card (Fin 4) = 4 := by simp
  obtain ⟨ψ, hψ, v, G, hvW, hLq, hweak⟩ := w12_compactness_box hd hlh u g hWu hBt hBu
  refine ⟨ψ, hψ, fun ν c e => v (ν, c, e), fun ν c e => G (ν, c, e), fun ν c e => hvW _,
    ?_, ?_, ?_⟩
  · intro ν c e q hq1 hq4
    exact hLq (ν, c, e) q hq1 hq4
  · intro ν c e μ w hw
    exact hweak (ν, c, e) μ w hw
  · intro μ ν c e w hw
    have hA : ∀ ν c e, LpTendsto ρ 2 (fun k => entries (C (φ (ψ k))) ν c e) (v (ν, c, e)) :=
      fun ν c e => ⟨fun k => (hW _ ν c e).memLp, (hvW (ν, c, e)).memLp,
        hLq (ν, c, e) 2 one_le_two (by norm_num)⟩
    exact tendsto_integral_curvatureW (ρ := ρ) (A := fun k => entries (C (φ (ψ k))))
      (dA := fun k => entryGrad (C (φ (ψ k)))) (A₀ := fun ν c e => v (ν, c, e))
      (dA₀ := fun ν c e => G (ν, c, e)) hA
      (fun k ν c e μ => (hW _ ν c e).memLp_grad μ) (fun ν c e μ => (hvW (ν, c, e)).memLp_grad μ)
      (fun ν c e μ w hw => hweak (ν, c, e) μ w hw) hw μ ν c e

/-! ### `prop:critical-uhlenbeck` from the named gauge theorem -/

/-- **`prop:critical-uhlenbeck`, conditional on `UhlenbeckSmallEnergyGauge`** (box rendering of
the chart `K = box a b`).  Let `A_h` be smooth unitary connections with
`sup_h ‖F_{A_h}‖_{L²(K)} < ∞` (`eq:critical-curvature-bound`) and uniformly integrable critical
curvature energy (`def:critical-curvature-ui`, `CriticalCurvatureUI`).  Then for every compact
`K' ⊂ K` and every `η > 0`, `K'` has a finite cover by cubes `Q_j ⊂ K` and cutoff-dependent local
gauges `R_{h,j}` (unitary on `Q_j`) in which `Ã_{h,j} = R_{h,j}·A_h` satisfies `d^*Ã_{h,j} = 0`
on `Q_j`, `sup_h ‖Ã_{h,j}‖_{W^{1,2}(Q_j)} < ∞` (`eq:critical-coulomb-bound`) and
`‖Ã_{h,j}‖_{L⁴(Q_j)} ≤ η`; and after extraction (one subsequence for all `j`),
`Ã_{h,j} ⇀ A_j` in `W^{1,2}(Q_j)`, `Ã_{h,j} → A_j` in `L^q(Q_j)` (`1 ≤ q < 4`) and
`F_{Ã_{h,j}} ⇀ F_{A_j}` (`eq:critical-coulomb-convergence`; the curvature limit is tested against
bounded weights, which together with the uniform `L²` bound is weak `L²` convergence). -/
theorem critical_uhlenbeck_of_gauge {m : ℕ} (hU : UhlenbeckSmallEnergyGauge m)
    {a b : Fin 4 → ℝ} (A : ℕ → MConn m) (hA : ∀ h, IsSmoothUnitaryConn (A h))
    (_hbd : ∃ M : ℝ≥0, ∀ h, curvEnergy (A h) (box a b) ≤ M)
    (hUI : CriticalCurvatureUI volume (box a b) (fun h x => curvVec (A h) x))
    {K' : Set (Fin 4 → ℝ)} (hK' : IsCompact K') (hK'Q : K' ⊆ box a b) {η : ℝ≥0} (hη : 0 < η) :
    ∃ (N : ℕ) (lo hi : Fin N → Fin 4 → ℝ), (∀ j i, lo j i < hi j i) ∧
      (∀ j, box (lo j) (hi j) ⊆ box a b) ∧ K' ⊆ ⋃ j, box (lo j) (hi j) ∧
      ∃ R : ℕ → Fin N → (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ,
        (∀ h j, ∀ y ∈ box (lo j) (hi j), R h j y ∈ unitaryGroup (Fin m) ℂ) ∧
        (∀ h j, ∀ x ∈ box (lo j) (hi j), ∀ c e,
          ∑ μ, entryGrad (gaugeConn (R h j) (A h)) μ c e μ x = 0) ∧
        (∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ h j ν c e,
          MemW12 (box (lo j) (hi j)) (entries (gaugeConn (R h j) (A h)) ν c e)
            (entryGrad (gaugeConn (R h j) (A h)) ν c e) ∧
          w12Norm (box (lo j) (hi j)) (entries (gaugeConn (R h j) (A h)) ν c e)
            (entryGrad (gaugeConn (R h j) (A h)) ν c e) ≤ B) ∧
        (∀ h j ν c e, eLpNorm (entries (gaugeConn (R h j) (A h)) ν c e) 4
          (volume.restrict (box (lo j) (hi j))) ≤ η) ∧
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          ∀ j, CoulombLimit (box (lo j) (hi j)) (fun h => gaugeConn (R h j) (A h)) φ := by
  obtain ⟨εU, hεU, CU, hU'⟩ := hU
  -- the energy threshold
  set εs : ℝ≥0 := min εU ((η / (CU + 1)) ^ 2)
  have hεs : 0 < εs := lt_min hεU (by positivity)
  obtain ⟨δ, hδ, hUIδ⟩ := (criticalCurvatureUI_iff _ _ _).mp hUI εs (by exact_mod_cast hεs)
  -- the radius
  obtain ⟨r0, hr0, hthick⟩ := hK'.exists_thickening_subset_open (isOpen_box a b) hK'Q
  set r : ℝ := min (r0 / 2) (min 1 δ / 2)
  have hr : 0 < r := lt_min (by positivity) (by have := lt_min one_pos hδ; positivity)
  have hrr0 : r < r0 := (min_le_left _ _).trans_lt (by linarith)
  have hvol : (2 * r) ^ Fintype.card (Fin 4) ≤ δ := by
    have h2r : 2 * r ≤ min 1 δ := by
      have := min_le_right (r0 / 2) (min 1 δ / 2); linarith
    have h0 : 0 ≤ 2 * r := by linarith
    have h1 : 2 * r ≤ 1 := h2r.trans (min_le_left _ _)
    simp only [Fintype.card_fin]
    calc (2 * r) ^ 4 ≤ (2 * r) ^ 1 := pow_le_pow_of_le_one h0 h1 (by norm_num)
      _ = 2 * r := pow_one _
      _ ≤ δ := h2r.trans (min_le_right _ _)
  -- balls around points of `K'`
  have hball : ∀ c ∈ K', eBall c r ⊆ box a b := by
    intro c hc x hx
    refine hthick (Metric.mem_thickening_iff.mpr ⟨c, hc, ?_⟩)
    exact (Metric.mem_ball.mp (eBall_subset_ball c hr hx)).trans hrr0
  have hballvol : ∀ c, volume (eBall c r) ≤ ENNReal.ofReal δ := fun c =>
    (measure_mono (eBall_subset_ball c hr)).trans (by
      rw [Real.volume_pi_ball c hr]; exact ENNReal.ofReal_le_ofReal hvol)
  have henergy : ∀ h, ∀ c ∈ K', curvEnergy (A h) (eBall c r) ≤ εs := fun h c hc =>
    hUIδ h (eBall c r) (isOpen_eBall c r).measurableSet (hball c hc) (hballvol c)
  -- the finite cover by inner cubes
  set clo : (Fin 4 → ℝ) → Fin 4 → ℝ := fun c i => c i - r / 2
  set chi : (Fin 4 → ℝ) → Fin 4 → ℝ := fun c i => c i + r / 2
  have hcube : ∀ c, box (clo c) (chi c) ⊆ eBall c r := fun c => box_subset_eBall c hr
  obtain ⟨t, ht⟩ := hK'.elim_finite_subcover (fun c : K' => box (clo c.1) (chi c.1))
    (fun c => isOpen_box _ _) (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, by
      rw [mem_box]; intro i; constructor <;> simp [clo, chi] <;> linarith⟩)
  set N := t.card
  set ctr : Fin N → Fin 4 → ℝ := fun j => (t.equivFin.symm j : K').1
  have hctr : ∀ j, ctr j ∈ K' := fun j => (t.equivFin.symm j : K').2
  refine ⟨N, fun j => clo (ctr j), fun j => chi (ctr j), fun j i => by simp [clo, chi]; linarith,
    fun j => (hcube _).trans (hball _ (hctr j)), ?_, ?_⟩
  · intro x hx
    obtain ⟨c, hct, hxc⟩ := mem_iUnion₂.mp (ht hx)
    refine mem_iUnion.mpr ⟨t.equivFin ⟨c, hct⟩, ?_⟩
    simpa [ctr] using hxc
  -- the gauges
  choose Cr hCr using fun j => hU' (ctr j) r hr
  have hsmall : ∀ h j, curvEnergy (A h) (eBall (ctr j) r) ≤ εU := fun h j =>
    (henergy h _ (hctr j)).trans (by exact_mod_cast min_le_left _ _)
  choose R hRu _hRs hRdiv hRW hRw12 hR4 using fun h j => hCr j (A h) (hA h) (hsmall h j)
  refine ⟨R, fun h j y hy => hRu h j y (hcube _ hy), fun h j x hx => hRdiv h j x (hcube _ hx),
    ?_, ?_, ?_⟩
  · -- uniform `W^{1,2}` bound
    refine ⟨∑ j, (Cr j : ℝ≥0∞) * (εU : ℝ≥0∞) ^ (1 / 2 : ℝ), ?_, fun h j ν c e =>
      ⟨(hRW h j ν c e).mono (hcube _), ?_⟩⟩
    · exact ENNReal.sum_ne_top.mpr fun j _ => ENNReal.mul_ne_top ENNReal.coe_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.coe_ne_top)
    · refine (w12Norm_mono (hcube _) _ _).trans ((hRw12 h j ν c e).trans ?_)
      refine le_trans ?_ (Finset.single_le_sum (f := fun j => (Cr j : ℝ≥0∞) *
        (εU : ℝ≥0∞) ^ (1 / 2 : ℝ)) (fun _ _ => zero_le) (Finset.mem_univ j))
      exact mul_le_mul_right (ENNReal.rpow_le_rpow (hsmall h j) (by norm_num)) _
  · -- small `L⁴` norms
    intro h j ν c e
    refine (eLpNorm_mono_measure _ (Measure.restrict_mono (hcube _) le_rfl)).trans
      ((hR4 h j ν c e).trans ?_)
    exact mul_rpow_half_le (min_le_right _ _) (henergy h _ (hctr j))
  · -- the common extraction
    obtain ⟨B, hBt, hB⟩ : ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ h j ν c e,
        w12Norm (box (clo (ctr j)) (chi (ctr j))) (entries (gaugeConn (R h j) (A h)) ν c e)
          (entryGrad (gaugeConn (R h j) (A h)) ν c e) ≤ B := by
      refine ⟨∑ j, (Cr j : ℝ≥0∞) * (εU : ℝ≥0∞) ^ (1 / 2 : ℝ), ENNReal.sum_ne_top.mpr
        fun j _ => ENNReal.mul_ne_top ENNReal.coe_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.coe_ne_top), fun h j ν c e => ?_⟩
      refine (w12Norm_mono (hcube _) _ _).trans ((hRw12 h j ν c e).trans ?_)
      refine le_trans ?_ (Finset.single_le_sum (f := fun j => (Cr j : ℝ≥0∞) *
        (εU : ℝ≥0∞) ^ (1 / 2 : ℝ)) (fun _ _ => zero_le) (Finset.mem_univ j))
      exact mul_le_mul_right (ENNReal.rpow_le_rpow (hsmall h j) (by norm_num)) _
    refine exists_common_subseq (fun j φ => CoulombLimit (box (clo (ctr j)) (chi (ctr j)))
      (fun h => gaugeConn (R h j) (A h)) φ) (fun j φ _ => ?_)
      (fun j φ ψ hψ hP => hP.comp hψ)
    exact exists_coulombLimit (fun i => by simp [clo, chi]; linarith)
      (fun h ν c e => (hRW h j ν c e).mono (hcube _)) hBt (fun h ν c e => hB h j ν c e) φ


/-! ### Non-vacuity -/

/-- The hypothesis packet of `critical_uhlenbeck_of_gauge` is satisfiable: the zero connection is
a smooth unitary connection with bounded and uniformly integrable curvature energy. -/
example : IsSmoothUnitaryConn (fun _ _ => (0 : Matrix (Fin 1) (Fin 1) ℂ)) ∧
    (∃ M : ℝ≥0, ∀ _h : ℕ, curvEnergy (fun _ _ => (0 : Matrix (Fin 1) (Fin 1) ℂ))
      (box 0 1) ≤ M) ∧
    CriticalCurvatureUI volume (box (0 : Fin 4 → ℝ) 1)
      (fun (_ : ℕ) x => curvVec (fun _ _ => (0 : Matrix (Fin 1) (Fin 1) ℂ)) x) := by
  have h0 : ∀ x, curvVec (fun _ _ => (0 : Matrix (Fin 1) (Fin 1) ℂ)) x = 0 := by
    intro x
    ext p
    simp [curvVec, curvatureW, entries, entryGrad, pd]
  have hE : ∀ S, curvEnergy (fun _ _ => (0 : Matrix (Fin 1) (Fin 1) ℂ)) S = 0 := by
    intro S; simp [curvEnergy, h0]
  refine ⟨⟨fun _ _ _ => contDiff_const, fun _ _ => by simp⟩, ⟨0, fun _ => by simp [hE]⟩, ?_⟩
  rw [criticalCurvatureUI_iff]
  intro ε hε
  exact ⟨1, one_pos, fun _ E _ _ _ => by simp [h0]⟩

/-- The hypotheses of `equivTestSize_gauge` are satisfiable (constant gauge transformations). -/
example (ρ : Measure (Fin 4 → ℝ)) :
    equivTestSize ρ 0 (gaugeConn (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ)) (fun _ _ => 0))
        (fun y => (1 : Matrix (Fin 1) (Fin 1) ℂ) * 0 * star 1)
        (gaugeConn (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ)) (fun _ _ => 0))
        (fun y => (1 : Matrix (Fin 1) (Fin 1) ℂ) *ᵥ 0)
        (gaugeConn (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ)) (fun _ _ => 0))
        (fun y => (1 : Matrix (Fin 1) (Fin 1) ℂ) *ᵥ 0)
        (fun y => dualGauge (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ)) y *ᵥ 0) =
      equivTestSize (mG := 1) (mH := 1) (mF := 1) ρ 0 (fun _ _ => 0) 0 (fun _ _ => 0) 0
        (fun _ _ => 0) 0 0 :=
  equivTestSize_gauge ρ 0 (fun _ => one_mem _) (fun _ => one_mem _) (fun _ => one_mem _)
    (fun _ _ _ => differentiableAt_const _) (fun _ _ _ => differentiableAt_const _)
    (fun _ _ _ => differentiableAt_const _) _ (fun _ _ _ => differentiableAt_const _) _
    (fun _ _ => differentiableAt_const _) _ (fun _ _ => differentiableAt_const _)
    (fun _ _ => differentiableAt_const _)

end RenewalGeometry.CriticalGauge
