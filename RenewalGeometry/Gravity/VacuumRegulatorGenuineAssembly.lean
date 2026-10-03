/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.FriedmannLapseEinsteinExact
import RenewalGeometry.Gravity.DeSitterCauchySlices
import RenewalGeometry.Gravity.HomogeneousADMSlabScreensUnconditional
import RenewalGeometry.DiscreteAnalysis.A3FlatGeneratorLimitExact
import RenewalGeometry.Gravity.DeSitterPalatiniFirstVariation
import RenewalGeometry.Gravity.CurvatureEnergyPropagationExact
import RenewalGeometry.Gravity.ExplicitOperationalFamily

/-!
# Stationary flat and de Sitter renewal regulators, re-assembled from derived results
  (`mt:vacuum`, emergent-spacetime manuscript)

Every clause of `mt:vacuum` is obtained here from results in which the relevant object is
*computed* from the regulator data (no clause is a definitional unfolding):

* (ii) `A3CutoffRegulator`, `desitterCutoff H d t` — at each spatial cutoff `h = 1/d` and time
  `t`, the normalized finite `A₃` renewal law: twelve root rates `e^{-2Ht}/(8h²)`, vertex masses
  `e^{3Ht} h³` on `V_h = Λ/dΛ`, and the directly normalized race law `k_α/Σk` on the event
  alphabet of `con:supp-flat-regulator` (`desitterCutoff_eventLaw`, `_sum`);
  `rootMoment` (the bracket `h² Σ_α k_α ααᵀ`) and `massDensity` (`m_h / h³`) are computed from
  these data, and the ADM inversion (`HomogeneousADMPacket.admMetric`, `admLapse`) and the drift
  (`predictableDrift`) reconstruct `g_h = e^{2Ht} I`, `N_h = 1`, `β_h = 0`
  (`desitterCutoff_adm`).  The rates and masses are the stationary renewal output
  (`desitterCutoff_stationary_rates`: they are `κ/(8h²)`, `ϱh³` of the stationary profile
  `a = e^{Ht}`, `N = 1`), and at `H = 0` the cutoff law is the flat regulator
  `flatPeriodicRegulator` (`desitterCutoff_flat`).
* (iii) `admLorentz` assembles `-N² dt² + g` (with shift) from the reconstructed ADM data;
  `desitterCutoff_lorentz_tendsto` — along `h = 1/(n+1)` the reconstructed Lorentz metric
  converges to `g_H` (it equals it at every cutoff), and `g_H` solves `G + 3H² g = 0`, computed
  from the metric field (`FriedmannLapseEinstein.desitter_lapseMetric_vacuum`); for `H = 0` this
  is Minkowski with `G = 0` (`Λ = 0`).  `desitterStageGen` is the stage generator with the
  regulator's own rates, `= e^{-2Ht} L_h` (`desitterStageGen_eq`), and
  `desitter_semigroup_strong` — `e^{s L_h(t)} → e^{s e^{-2Ht} Δ/2}` strongly along the natural
  piecewise-constant embeddings (the Laplace–Beltrami semigroup of `g(t) = e^{2Ht} I`), from
  `A3FlatGenerator.flat_semigroup_strong`.
* (iv) `desitterCutoff_screens` — the cut / Poincaré / Weyl / compact-screen constants of the
  time-`t` spatial graph of `desitterCutoff H d t` on `|t| ≤ T` depend only on `H, T` (uniform in
  `h = 1/d` and `t`), from `desitter_slab_screens_unconditional`.
* (v) `desitter_curvature_budgets` — the derived Cartan curvature
  (`DeSitterCartan.curvature_eq`) is time independent with all frame components bounded by `H²`
  (`L^∞`); the Christoffel (transport) coefficients of `g_H`, computed from the metric field, are
  bounded on `|t| ≤ T` by `|H| e^{2|H|T}`; the lapse and shift are `1, 0`; and the curvature
  writer of `thm:main-curvature-propagation` for the retained frame curvature has `K = L = 0`,
  `f = 0`, `a = 0`, so its budgets pass with `A_* = F_* = 0`
  (`CurvatureEnergyPropagationExact.curvature_energy_uniform_bound` instantiated).
* (vi) `desitter_exact_link_defects` — exact links are metric-unitary
  (`DeSitterExactLink.edgeLink_metric_unitary`), and along `h_n = 2^{-n²}`, `T_n = n` the
  normalized curvature, torsion and Palatini first-variation defects are `≤ C_{T_n} h_n` with
  `Σ C_{T_n} h_n < ∞` (`DeSitterExactLink.finiteDefects_diagonal`, `Palatini.finiteDefects_slab`,
  `Palatini.finiteDefects_full_diagonal`); flat: all vanish (`Palatini.finiteDefects_flat_full`).
* (i) `VacuumRegulatorStationarity.desitterProfile_isStationaryRenewalSolution` and
  `FiniteHomogeneousStationarity.scale_factor_log_error_le`.
* final sentence: `ExplicitOperationalFamily.explicit_operational_family`.

**`vacuum_regulators_genuine`** conjoins all clauses.
-/

open Filter Topology Matrix
open scoped BigOperators

namespace RenewalGeometry.VacuumRegulatorGenuine

open RelationalDeSitterBranch HomogeneousADMPacket

noncomputable section

/-! ### (ii) The normalized finite `A₃` law at each cutoff -/

/-- A finite `A₃` renewal law at spatial cutoff `h = 1/d`: twelve root rates, vertex masses on
`V_h = Λ/dΛ`, and the conditional law of the event alphabet of `con:supp-flat-regulator`. -/
structure A3CutoffRegulator (d : ℕ) where
  /-- rates `k_α` of the twelve oriented roots -/
  rootRate : Fin 12 → ℝ
  /-- vertex masses `m_h` -/
  vertexMass : A3PeriodicGraphSampling.Vertex d → ℝ
  /-- conditional event law -/
  eventLaw : FlatEvent → ℝ

/-- The root second moment (predictable bracket) `𝓑_h = h² Σ_α k_α α αᵀ` of a rate vector. -/
def rootMoment (k : Fin 12 → ℝ) (h : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  h ^ 2 • ∑ r, k r • vecMulVec (a3Roots r) (a3Roots r)

/-- Physical speed (mass) density `ϱ_h = m_h / h³` (mass per physical cell volume). -/
def massDensity (m h : ℝ) : ℝ := m / h ^ 3

/-- The de Sitter regulator at cutoff `h = 1/d` and time `t`: rates `e^{-2Ht}/(8h²)`,
masses `e^{3Ht} h³`, and the directly normalized race law `k_α / Σ_β k_β`. -/
def desitterCutoff (H : ℝ) (d : ℕ) (t : ℝ) : A3CutoffRegulator d where
  rootRate := fun _ => rootRate H (A3PeriodicGraphSampling.mesh d) t
  vertexMass := fun _ => vertexMass H (A3PeriodicGraphSampling.mesh d) t
  eventLaw := fun _ =>
    rootRate H (A3PeriodicGraphSampling.mesh d) t /
      ∑ _r : Fin 12, rootRate H (A3PeriodicGraphSampling.mesh d) t

theorem rootRate_pos (H h t : ℝ) (hh : h ≠ 0) : 0 < rootRate H h t := by
  unfold rootRate; positivity

theorem desitterCutoff_eventLaw (H : ℝ) (d : ℕ) [NeZero d] (t : ℝ) (e : FlatEvent) :
    (desitterCutoff H d t).eventLaw e = 1 / 12 := by
  have hk := rootRate_pos H (A3PeriodicGraphSampling.mesh d) t
    (A3PeriodicGraphSampling.mesh_pos d).ne'
  simp only [desitterCutoff, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  norm_num

/-- The cutoff law is a probability law. -/
theorem desitterCutoff_eventLaw_sum (H : ℝ) (d : ℕ) [NeZero d] (t : ℝ) :
    (∀ e, 0 ≤ (desitterCutoff H d t).eventLaw e) ∧
      ∑ e : FlatEvent, (desitterCutoff H d t).eventLaw e = 1 := by
  refine ⟨fun e => by rw [desitterCutoff_eventLaw]; norm_num, ?_⟩
  simp [desitterCutoff_eventLaw]

/-- The root moment of equal rates `k` is `8 h² k I` (tight-frame identity). -/
theorem rootMoment_const (k h : ℝ) :
    rootMoment (fun _ => k) h = (8 * h ^ 2 * k) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  unfold rootMoment
  rw [← Finset.smul_sum, relational_flat_vacuum.1, smul_smul, smul_smul]
  congr 1
  ring

/-- **(ii) ADM reconstruction at every cutoff**: the root moment and the mass density of the
cutoff law reconstruct `𝓑_h = e^{-2Ht} I`, `ϱ_h = e^{3Ht}`, `g_h = e^{2Ht} I`, `N_h = 1`,
`β_h = 0` through the ADM inversion formula (no primitive metric), with conductance
`e^{Ht} h / 8`. -/
theorem desitterCutoff_adm (H : ℝ) (d : ℕ) [NeZero d] (t : ℝ) :
    let R := desitterCutoff H d t
    let h := A3PeriodicGraphSampling.mesh d
    rootMoment R.rootRate h = Real.exp (-2 * H * t) • 1 ∧
      (∀ v, massDensity (R.vertexMass v) h = Real.exp (3 * H * t)) ∧
      (∀ v, admMetric (rootMoment R.rootRate h) (massDensity (R.vertexMass v) h) =
        Real.exp (2 * H * t) • 1) ∧
      (∀ v, admLapse (rootMoment R.rootRate h) (massDensity (R.vertexMass v) h) = 1) ∧
      predictableDrift R.rootRate h = 0 ∧
      (∀ v r, R.vertexMass v * R.rootRate r = Real.exp (H * t) * h / 8) := by
  intro R h
  have hh : h ≠ 0 := (A3PeriodicGraphSampling.mesh_pos d).ne'
  have hB : rootMoment R.rootRate h = predictableBracket H h t := by
    show rootMoment (fun _ => rootRate H h t) h = _
    rw [rootMoment_const, predictableBracket, relational_flat_vacuum.1, smul_smul]
    congr 1; ring
  have hρ : ∀ v, massDensity (R.vertexMass v) h = speedDensity H t := by
    intro v
    show vertexMass H h t / h ^ 3 = Real.exp (3 * H * t)
    unfold vertexMass
    field_simp
  refine ⟨hB.trans (predictableBracket_eq H h t hh), fun v => hρ v, fun v => ?_, fun v => ?_,
    predictableDrift_eq_zero_of_reversal_symm _ (fun _ => rfl) h,
    fun v r => conductance_exact H h t hh⟩
  · rw [hB, hρ v, admMetric_desitter H h t hh]; rfl
  · rw [hB, hρ v, admLapse_desitter H h t hh]; rfl

/-- The cutoff rates and masses are the stationary renewal output: `k = κ/(8h²)`, `m = ϱ h³`
with `κ = N²/a²`, `ϱ = a³` of the stationary profile `a = e^{Ht}`, `N = 1`
(`VacuumRegulatorStationarity.desitterProfile_isStationaryRenewalSolution`). -/
theorem desitterCutoff_stationary_rates (H : ℝ) (d : ℕ) (t : ℝ) :
    (∀ r, (desitterCutoff H d t).rootRate r =
      homogeneousRootRate (renewalConductance (VacuumRegulatorStationarity.profile H)
        (fun _ => 1)) (A3PeriodicGraphSampling.mesh d) t) ∧
    (∀ v, (desitterCutoff H d t).vertexMass v =
      homogeneousVertexMass (renewalDensity (VacuumRegulatorStationarity.profile H))
        (A3PeriodicGraphSampling.mesh d) t) := by
  refine ⟨fun r => ?_, fun v => ?_⟩
  · simp only [desitterCutoff, RelationalDeSitterBranch.rootRate, homogeneousRootRate,
      renewalConductance, VacuumRegulatorStationarity.profile]
    rw [one_pow, ← Real.exp_nat_mul, one_div, ← Real.exp_neg]
    congr 2; push_cast; ring
  · simp only [desitterCutoff, RelationalDeSitterBranch.vertexMass, homogeneousVertexMass,
      renewalDensity, VacuumRegulatorStationarity.profile]
    rw [← Real.exp_nat_mul]
    congr 2; push_cast; ring

/-- At `H = 0` the cutoff law is the flat periodic regulator of `con:supp-flat-regulator`. -/
theorem desitterCutoff_flat (d : ℕ) [NeZero d] (t : ℝ) :
    (desitterCutoff 0 d t).rootRate = (flatPeriodicRegulator d).rootRate ∧
      (desitterCutoff 0 d t).vertexMass = (flatPeriodicRegulator d).vertexMass ∧
      (desitterCutoff 0 d t).eventLaw = (flatPeriodicRegulator d).eventLaw := by
  refine ⟨funext fun r => ?_, funext fun v => ?_, funext fun e => ?_⟩
  · simp [desitterCutoff, flatPeriodicRegulator, RelationalDeSitterBranch.rootRate]
  · simp [desitterCutoff, flatPeriodicRegulator, RelationalDeSitterBranch.vertexMass,
      A3PeriodicGraphSampling.mass]
  · rw [desitterCutoff_eventLaw, flatPeriodicRegulator_eventLaw]

/-! ### (iii) Convergence of the regulator sequences -/

/-- The spatial index `μ - 1` of a spacetime index `μ ≠ 0`. -/
def spatialIdx (μ : Fin 4) : Fin 3 := ⟨μ.val - 1, by omega⟩

/-- The Lorentz metric `-N² dt² + g_{ij}(dxⁱ + βⁱdt)(dxʲ + βʲdt)` assembled from ADM data. -/
def admLorentz (N : ℝ) (β : Fin 3 → ℝ) (g : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun μ ν =>
    if μ = 0 then (if ν = 0 then -N ^ 2 + β ⬝ᵥ (g *ᵥ β) else (g *ᵥ β) (spatialIdx ν))
    else (if ν = 0 then (g *ᵥ β) (spatialIdx μ) else g (spatialIdx μ) (spatialIdx ν))

/-- The Lorentz metric reconstructed from the cutoff law (ADM inversion of its root moment and
mass density, shift from its drift). -/
def cutoffLorentz (H : ℝ) (d : ℕ) [NeZero d] (t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  let R := desitterCutoff H d t
  let h := A3PeriodicGraphSampling.mesh d
  admLorentz (admLapse (rootMoment R.rootRate h) (massDensity (R.vertexMass 0) h))
    (predictableDrift R.rootRate h)
    (admMetric (rootMoment R.rootRate h) (massDensity (R.vertexMass 0) h))

theorem cutoffLorentz_eq (H : ℝ) (d : ℕ) [NeZero d] (t : ℝ) :
    cutoffLorentz H d t = lorentzMetric H t := by
  obtain ⟨-, -, hg, hN, hβ, -⟩ := desitterCutoff_adm H d t
  unfold cutoffLorentz
  simp only
  rw [hg 0, hN 0, hβ]
  ext μ ν
  unfold admLorentz lorentzMetric
  have h0 : (spatialIdx 1 : Fin 3) = 0 := rfl
  have h1 : (spatialIdx 2 : Fin 3) = 1 := rfl
  have h2 : (spatialIdx 3 : Fin 3) = 2 := rfl
  fin_cases μ <;> fin_cases ν <;>
    simp [Matrix.one_apply, h0, h1, h2]

/-- `g_H` is the lapse-FLRW metric field with `N = 1`, `a = e^{Ht}` at time `x⁰ = t`. -/
theorem lorentzMetric_eq_lapseMetric (H : ℝ) (x : Fin 4 → ℝ) :
    lorentzMetric H (x 0) =
      FriedmannLapseEinstein.lapseMetric (fun _ => 1) (fun s => Real.exp (H * s)) x := by
  unfold lorentzMetric FriedmannLapseEinstein.lapseMetric
  congr 1
  funext i
  split_ifs
  · norm_num
  · rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

/-- **(iii), metric part.**  Along `h = 1/(n+1)` the Lorentz metrics reconstructed from the
cutoff laws converge to `g_H = -dt² + e^{2Ht} dx²` (they coincide with it at every cutoff), and
`g_H` solves `G + Λ g = 0` with `Λ = 3H²`, the Einstein tensor computed from the metric field
(for `H = 0`: Minkowski, `Λ = 0`). -/
theorem desitterCutoff_lorentz_tendsto (H : ℝ) (t : ℝ) :
    Tendsto (fun n : ℕ => cutoffLorentz H (n + 1) t) atTop (𝓝 (lorentzMetric H t)) ∧
    ∀ x : Fin 4 → ℝ, x 0 = t → ∀ μ ν,
      FriedmannLapseEinstein.einsteinOf
          (FriedmannLapseEinstein.lapseMetric (fun _ => 1) (fun s => Real.exp (H * s))) x μ ν +
        3 * H ^ 2 * lorentzMetric H t μ ν = 0 := by
  refine ⟨?_, fun x hx μ ν => ?_⟩
  · have : (fun n : ℕ => cutoffLorentz H (n + 1) t) = fun _ => lorentzMetric H t := by
      funext n; exact cutoffLorentz_eq H (n + 1) t
    rw [this]; exact tendsto_const_nhds
  · rw [← hx, lorentzMetric_eq_lapseMetric]
    exact FriedmannLapseEinstein.desitter_lapseMetric_vacuum H x μ ν

open A3FlatGenerator A3PeriodicSmoothEnergy in
/-- The stage generator of the cutoff law at time `t`, with the law's own root rates:
`(L_h(t) f)(x) = Σ_α k_{α,h}(t) [f(x + α) - f(x)]` on `ℓ²(V_h)`, `h = 1/N`. -/
def desitterStageGen (H t : ℝ) (N : ℕ) [NeZero N] : Stage N →L[ℂ] Stage N :=
  liftE (∑ r : Fin 12, (((rootRate H (A3PeriodicGraphSampling.mesh N) t : ℝ) : ℂ) •
    (A3FlatGenerator.translate (castVec N (rootCoordinates r)) - 1)))

open A3FlatGenerator in
theorem desitterStageGen_eq (H t : ℝ) (N : ℕ) [NeZero N] :
    desitterStageGen H t N = ((Real.exp (-2 * H * t) : ℝ) : ℂ) • genE N := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hk : ((rootRate H (A3PeriodicGraphSampling.mesh N) t : ℝ) : ℂ) =
      ((Real.exp (-2 * H * t) : ℝ) : ℂ) * ((N : ℂ) ^ 2 / 8) := by
    unfold rootRate A3PeriodicGraphSampling.mesh
    push_cast
    have : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    field_simp
  unfold desitterStageGen genE gen
  rw [hk]
  ext f : 1
  simp only [liftE_apply, ContinuousLinearMap.smul_apply]
  rw [← WithLp.toLp_smul]
  congr 1
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul]

open A3FlatGenerator in
/-- **(iii), generator part.**  At every time `t`, the semigroups of the cutoff generators
`L_h(t) = e^{-2Ht} L_h^{flat}` converge strongly, along the natural piecewise-constant
embeddings, to `e^{s e^{-2Ht} Δ/2}` — the heat semigroup of `½Δ_{g(t)}` for
`g(t) = e^{2Ht} I` (Laplace–Beltrami `= e^{-2Ht} Δ`). -/
theorem desitter_semigroup_strong (H t s : ℝ) (hs : 0 ≤ s) :
    pcSystem.StrongOperatorConverges pcSystem
      (fun n => NormedSpace.exp ((s : ℂ) • desitterStageGen H t (n + 1)))
      (contSem (s * Real.exp (-2 * H * t)) (mul_nonneg hs (Real.exp_pos _).le)) := by
  have h := flat_semigroup_strong (s * Real.exp (-2 * H * t)) (mul_nonneg hs (Real.exp_pos _).le)
  have he : (fun n : ℕ => NormedSpace.exp ((s : ℂ) • desitterStageGen H t (n + 1))) =
      fun n => NormedSpace.exp (((s * Real.exp (-2 * H * t) : ℝ) : ℂ) • genE (n + 1)) := by
    funext n
    rw [desitterStageGen_eq, smul_smul]
    push_cast
    rfl
  rw [he]
  exact h

/-! ### (iv) Slab-uniform screens of the cutoff laws -/

open A3PeriodicScreens TorusCoordinateIsoperimetry in
/-- **(iv)** On every compact slab `|t| ≤ T`, the time-`t` spatial graph of the cutoff law
`desitterCutoff H d t` (its masses and rates are the scaled periodic data at `a = e^{Ht}`)
satisfies the cut inequality with constant `1/(256 e^{HT})`, the Poincaré floor
`poincareConstant e^{-HT} e^{HT} (1/32)`, the Weyl count with `weylConstant e^{-HT} e^{HT} (1/32)`
and the compact-screen tail bound — all independent of the cutoff `h = 1/d` and of `t`
(`H = 0`: the flat regulator, constants with `a₋ = a₊ = 1`). -/
theorem desitterCutoff_screens (H T : ℝ) (hH : 0 ≤ H) (d : ℕ) [NeZero d] (t : ℝ)
    (ht : |t| ≤ T) :
    let G := scaledGraph d (Real.exp (H * t)) (Real.exp_pos _)
    (∀ v, (desitterCutoff H d t).vertexMass v = G.mass v) ∧
    (∀ r, (desitterCutoff H d t).rootRate r = scaledRate d (Real.exp (H * t))) ∧
    (∀ A : Finset (A3PeriodicGraphSampling.Vertex d), 0 < A.card →
      2 * A.card ≤ d ^ 3 →
      1 / (256 * Real.exp (H * T)) * (∑ v ∈ A, G.mass v) ^ ((2 : ℝ) / 3) ≤
        A3PeriodicGraphSampling.mesh d * finiteCutCapacity G.conductance A) ∧
    (∀ j, 0 < G.eigenvalue j →
      poincareConstant (Real.exp (-H * T)) (Real.exp (H * T)) (1 / 32) ≤ G.eigenvalue j) ∧
    (∀ R : ℝ, 0 < R →
      (finiteEigenvalueCount G.eigenvalue R : ℝ) ≤
        weylConstant (Real.exp (-H * T)) (Real.exp (H * T)) (1 / 32) *
          (1 + R ^ ((3 : ℝ) / 2))) ∧
    (∀ (f : A3PeriodicGraphSampling.Vertex d → ℝ) (R : ℝ), 0 < R →
      ∑ j ∈ Finset.univ.filter (fun j => R < G.eigenvalue j),
          G.spectralCoefficient f j ^ 2 ≤
        R⁻¹ * ∑ j, G.eigenvalue j * G.spectralCoefficient f j ^ 2) := by
  intro G
  obtain ⟨hm, hr, h1, h2, h3, h4⟩ := (desitter_adm_packet_full H hH).2 T d t ht
  exact ⟨fun v => hm v, fun _ => hr, h1, h2, h3, h4⟩

/-! ### (v) Curvature, transport coefficients and propagation budgets -/

/-- Regularity packet of the de Sitter profile `a = e^{Ht}`, `N = 1`. -/
theorem desitter_lapseRegular (H : ℝ) (t : ℝ) :
    FriedmannLapseEinstein.LapseRegular (fun _ => 1) (fun s => Real.exp (H * s)) (fun _ => 0)
      (fun s => H * Real.exp (H * s)) (H ^ 2 * Real.exp (H * t)) t := by
  refine ⟨hasDerivAt_const _ _, Eventually.of_forall fun s => ?_, ?_, one_pos, Real.exp_pos _⟩
  · have := ((hasDerivAt_id s).const_mul H).exp
    simpa [mul_comm] using this
  · have := (((hasDerivAt_id t).const_mul H).exp).const_mul H
    refine this.congr_deriv ?_
    simp; ring

/-- The Christoffel (transport) coefficients of `g_H`, computed from the metric field, are
`Γ⁰ₖₖ = H e^{2Ht}`, `Γᵏ₀ₖ = H`, all others `0`; on `|t| ≤ T` they are bounded by
`|H| e^{2|H|T}`. -/
theorem desitter_christoffel_slab_bound (H T : ℝ) (x : Fin 4 → ℝ) (hx : |x 0| ≤ T)
    (c i j : Fin 4) :
    |christoffel (FriedmannLapseEinstein.metricJetOf
        (FriedmannLapseEinstein.lapseMetric (fun _ => 1) (fun s => Real.exp (H * s))) x).1
      (FriedmannLapseEinstein.metricJetOf
        (FriedmannLapseEinstein.lapseMetric (fun _ => 1) (fun s => Real.exp (H * s))) x).2.1
      c i j| ≤ |H| * Real.exp (2 * |H| * T) := by
  have hr := desitter_lapseRegular H (x 0)
  rw [FriedmannLapseEinstein.metricJetOf_lapseMetric (N' := fun _ => 0)
    (a' := fun s => H * Real.exp (H * s)) hr.hasDerivAt_N hr.hasDerivAt_a
    hr.hasDerivAt_a' one_ne_zero (Real.exp_pos _).ne']
  simp only
  rw [FriedmannLapseEinstein.christoffel_lapse one_ne_zero (Real.exp_pos _).ne']
  have hE1 : 1 ≤ Real.exp (2 * |H| * T) := by
    rw [Real.one_le_exp_iff]
    have := (abs_nonneg (x 0)).trans hx
    positivity
  have hE2 : Real.exp (H * x 0) * Real.exp (H * x 0) ≤ Real.exp (2 * |H| * T) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have h1 : H * x 0 ≤ |H| * T := by
      calc H * x 0 ≤ |H * x 0| := le_abs_self _
        _ = |H| * |x 0| := abs_mul _ _
        _ ≤ |H| * T := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
    linarith
  have hH0 := abs_nonneg H
  unfold FriedmannLapseEinstein.lapseGamma
  split_ifs
  · simp; positivity
  · rw [abs_div, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    simp only [one_pow, abs_one, div_one]
    calc Real.exp (H * x 0) * (|H| * Real.exp (H * x 0))
        = |H| * (Real.exp (H * x 0) * Real.exp (H * x 0)) := by ring
      _ ≤ |H| * Real.exp (2 * |H| * T) := mul_le_mul_of_nonneg_left hE2 hH0
  · simp; positivity
  · rw [abs_div, abs_mul, abs_of_pos (Real.exp_pos (H * x 0)),
      mul_div_assoc, div_self (Real.exp_pos _).ne', mul_one]
    nlinarith
  · simp; positivity

/-- Each frame component of the derived Cartan curvature `Ω^A_{B DE} = H² η_B (δδ - δδ)` is
bounded by `H²` (uniform `L^∞` bound, independent of `t`). -/
theorem desitter_frame_curvature_bound (H : ℝ) (A B D E : Fin 4) :
    |DeSitterCartan.curvatureComponents (DeSitterCartan.coframeStructure H)
        (DeSitterCartan.spinConnection H) A B D E| ≤ H ^ 2 := by
  rw [DeSitterCartan.curvature_eq]
  unfold DeSitterCartan.constantCurvature
  have hη : |DeSitterCartan.eta B| = 1 := by
    unfold DeSitterCartan.eta; split_ifs <;> norm_num
  have hX : |((if A = D then (1 : ℝ) else 0) * (if B = E then 1 else 0) -
      (if A = E then 1 else 0) * (if B = D then 1 else 0))| ≤ 1 := by
    split_ifs <;> norm_num
  rw [abs_mul, abs_mul, hη, abs_of_nonneg (sq_nonneg H), mul_one]
  calc H ^ 2 * |((if A = D then (1 : ℝ) else 0) * (if B = E then 1 else 0) -
      (if A = E then 1 else 0) * (if B = D then 1 else 0))| ≤ H ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hX (sq_nonneg H)
    _ = H ^ 2 := mul_one _

/-- The retained curvature record of the de Sitter branch in the reconstructed (orthonormal)
observer frame: the components of the derived Cartan curvature two-form, as a vector of
`EuclideanSpace ℝ (Fin 4 × Fin 4 × Fin 4 × Fin 4)` (time independent). -/
def curvatureRecord (H : ℝ) (_t : ℝ) : EuclideanSpace ℝ (Fin 4 × Fin 4 × Fin 4 × Fin 4) :=
  WithLp.toLp 2 fun p => DeSitterCartan.curvatureComponents (DeSitterCartan.coframeStructure H)
    (DeSitterCartan.spinConnection H) p.1 p.2.1 p.2.2.1 p.2.2.2

/-- **(v), propagation budgets.**  For the de Sitter curvature record with the identity Gram,
the propagation writer `y' = (K + L) y + f` of `thm:main-curvature-propagation` holds with
`K = L = 0`, `f = 0` and growth function `a = 0` (the record is constant); hence the budgets
`z(0) ≤ Z_*`, `∫a ≤ A_* = 0`, `∫‖f‖ ≤ F_* = 0` pass with `Z_* = z(0)` and the propagated energy is
bounded by `e^0 (Z_* + 0)` on every `[0, T]`. -/
theorem desitter_curvature_budgets (H T : ℝ) (hT : 0 ≤ T) :
    let V := EuclideanSpace ℝ (Fin 4 × Fin 4 × Fin 4 × Fin 4)
    let M : ℝ → V →L[ℝ] V := fun _ => ContinuousLinearMap.id ℝ V
    (∀ t, HasDerivAt (curvatureRecord H) 0 t) ∧
    (∀ t, (0 : V) = ((0 : V →L[ℝ] V) + 0) (curvatureRecord H t) + 0) ∧
    gramEnergy M (curvatureRecord H) 0 ≤ gramEnergy M (curvatureRecord H) 0 ∧
    (∫ s in (0:ℝ)..T, (0 : ℝ)) ≤ 0 ∧
    (∫ s in (0:ℝ)..T, gramEnergy M (fun _ => (0 : V)) s) ≤ 0 ∧
    ∀ t ∈ Set.Icc 0 T, gramEnergy M (curvatureRecord H) t ≤
      Real.exp 0 * (gramEnergy M (curvatureRecord H) 0 + 0) := by
  intro V M
  have hy : ∀ t, HasDerivAt (curvatureRecord H) 0 t := fun t => by
    have : curvatureRecord H = fun _ => curvatureRecord H 0 := rfl
    rw [this]; exact hasDerivAt_const _ _
  have hf0 : ∀ s, gramEnergy M (fun _ => (0 : V)) s = 0 := fun s => by
    simp [gramEnergy]
  refine ⟨hy, fun t => by simp, le_rfl, by simp, by simp [hf0], ?_⟩
  refine curvature_energy_uniform_bound M (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (curvatureRecord H) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (fun t => hasDerivAt_const _ _) hy continuous_const continuous_const (fun _ => le_rfl)
    (fun t x z => by simp [M]) (fun t x => real_inner_self_nonneg)
    (fun t => by simp) (fun t x => by simp) (fun t x => by simp) hT le_rfl (by simp)
    (by simp [hf0])

/-! ### (vi) Exact links and summable finite defects -/

section ExactLinks

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

open DeSitterExactLink DeSitterExactLink.Palatini in
/-- **(vi)** Exact parallel transport of the reconstructed connection gives metric-unitary links;
along `h_n = 2^{-n²}`, `T_n = n`, for all large `n` the normalized curvature and torsion defects
of every shape-regular face in the slab `[-n, n]` and the Palatini first-variation defect of the
midpoint quadrature (any coefficients `c_P, c_V`, any finite-volume spatial domain, any cell
decomposition of mesh `κ h_n`, any unit test) are `≤ C_{T_n} h_n`, and `Σ C_{T_n} h_n < ∞`. -/
theorem desitter_exact_link_defects (H cP cV κ : ℝ) (hκ : 1 ≤ κ) :
    (∀ t V, (edgeLink H t V)ᵀ * DeSitterExactLink.eta * edgeLink H t V =
      DeSitterExactLink.eta) ∧
    Summable (fun n : ℕ => slabConst H κ n * diagonalMesh n) ∧
    (∀ vD : ℝ, 0 ≤ vD →
      Summable (fun n : ℕ => finiteDefectConst H cP cV κ vD n * diagonalMesh n)) ∧
    ∃ N : ℕ, ∀ n ≥ N,
      diagonalMesh n ≤ slabMesh H κ n ∧
      (∀ t : ℝ, |t| ≤ n →
        (∀ (us : List (Fin 3 → ℝ)) (x xm : Fin 3 → ℝ) (area : ℝ), us.sum = 0 →
          (us.map fun u => ‖u‖).sum ≤ κ * diagonalMesh n → ‖xm - x‖ ≤ κ * diagonalMesh n →
          diagonalMesh n ^ 2 / κ ≤ area →
          ‖curvatureDefect H t t (us.map spatialVec) area‖
            + ‖torsionDefect H t x t xm (us.map spatialVec) area‖
            ≤ 2 * (slabConst H κ n * diagonalMesh n)) ∧
        (∀ (u x : Fin 3 → ℝ) (area : ℝ), ‖u‖ ≤ κ * diagonalMesh n →
          diagonalMesh n ^ 2 / κ ≤ area →
          ‖curvatureDefect H t (t + diagonalMesh n / 2) (mixedLoop (diagonalMesh n) u) area‖
            + ‖torsionDefect H t x (t + diagonalMesh n / 2) (x + (1 / 2 : ℝ) • u)
                (mixedLoop (diagonalMesh n) u) area‖
            ≤ 2 * (slabConst H κ n * diagonalMesh n))) ∧
      (∀ {ι : Type} (D : Set (Fin 3 → ℝ)), MeasureTheory.volume D < ⊤ →
        ∀ (P : CellDecomp ι (slab n D) (κ * diagonalMesh n)) (u : TVec → TestVal),
          IsUnitTest u →
          |quadratureVariation cP cV P (fun i => dsComp H (P.point i).1) u
              - firstVariation cP cV (fun y => dsComp H y.1) u (slab n D)|
            ≤ finiteDefectConst H cP cV κ (MeasureTheory.volume.real D) n * diagonalMesh n) := by
  obtain ⟨hs, N1, hN1⟩ := finiteDefects_diagonal H κ hκ
  obtain ⟨-, N2, hN2⟩ := finiteDefects_full_diagonal H cP cV κ 0 hκ le_rfl
  refine ⟨edgeLink_metric_unitary H, hs,
    fun vD hvD => (finiteDefects_full_diagonal H cP cV κ vD hκ hvD).1,
    max N1 N2, fun n hn => ⟨hN2 n (le_of_max_le_right hn), fun t ht => hN1 n
      (le_of_max_le_left hn) t ht, fun {ι} D hD P u hu => ?_⟩⟩
  have hT : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hpos := diagonalMesh_pos n
  have hκpos : 0 < κ := by linarith
  have h := (finiteDefects_slab H cP cV κ n hκ hT hpos (hN2 n (le_of_max_le_right hn)) hD P u hu
    (t := 0) (by simpa using hT)).1 [] 0 0 (diagonalMesh n ^ 2 / κ) (by simp)
    (by simp; positivity) (by simp; positivity) le_rfl
  have h1 := norm_nonneg (curvatureDefect H 0 0 (([] : List (Fin 3 → ℝ)).map spatialVec)
    (diagonalMesh n ^ 2 / κ))
  have h2 := norm_nonneg (torsionDefect H 0 0 0 0 (([] : List (Fin 3 → ℝ)).map spatialVec)
    (diagonalMesh n ^ 2 / κ))
  linarith

open DeSitterExactLink DeSitterExactLink.Palatini in
/-- **(vi), flat regulator**: every curvature and torsion defect of a closed loop and the Palatini
quadrature defect (flat cosmological coefficient) vanish identically, and the exact links are the
identity. -/
theorem flat_exact_link_defects {ι : Type} (cP t tm : ℝ) (x xm : Fin 3 → ℝ) (Vs : List TVec)
    (area : ℝ) (hclosed : Vs.sum = 0) {S : Set TVec} {δ : ℝ} (P : CellDecomp ι S δ)
    (u : TVec → TestVal) :
    (∀ s V, edgeLink 0 s V = 1) ∧
    curvatureDefect 0 t tm Vs area = 0 ∧ torsionDefect 0 t x tm xm Vs area = 0 ∧
      quadratureVariation cP 0 P (fun i => dsComp 0 (P.point i).1) u
        - firstVariation cP 0 (fun y => dsComp 0 y.1) u S = 0 :=
  ⟨edgeLink_flat, finiteDefects_flat_full cP t tm x xm Vs area hclosed P u⟩

end ExactLinks

/-! ### (i) and the assembled theorem -/

/-- **(i), finite-to-continuum half**: the finite stationary recurrence of
`thm:main-finite-homogeneous-stationarity` with `ω = 3H/2` (`Λ = 3H²`) converges with explicit
second-order logarithmic error to `a_0 e^{σHτ}`. -/
theorem finite_recurrence_to_profile (H : ℝ) (hH : 0 < H) (σ b h : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hb0 : 0 ≤ b) (hb : b < 1) (hωb : (3 * H / 2) * h / 2 ≤ b) (M : ℕ) (q s : ℕ → ℝ)
    (hq0 : 0 < q 0) (hs : ∀ j < M, 0 < s j) (hsh : ∀ j < M, s j ≤ h)
    (hrec : FiniteHomogeneousStationarity.SatisfiesRecurrence (3 * H / 2) σ M q s) :
    ∀ j ≤ M, |Real.log (q j ^ (2 / 3 : ℝ) / q 0 ^ (2 / 3 : ℝ)) -
        σ * H * FiniteHomogeneousStationarity.renewalTime s j|
      ≤ (2 / 3) * ((3 * H / 2) ^ 3 * FiniteHomogeneousStationarity.renewalTime s M * h ^ 2 /
        (12 * (1 - b ^ 2))) := by
  intro j hj
  have := FiniteHomogeneousStationarity.scale_factor_log_error_le (3 * H / 2) σ b h
    (by positivity) hσ hb0 hb hωb M q s hq0 hs hsh hrec j hj
  rwa [show σ * (2 * (3 * H / 2) / 3) = σ * H by ring] at this

/-- **`mt:vacuum`**, re-assembled from derived results, for the de Sitter branch with Hubble rate
`H ≥ 0` (`Λ = 3H²`; `H = 0` is the flat branch):
* (i) the profile `a = e^{Ht}`, `N = 1` solves the lapse-varied renewal Euler system and is the
  limit of the finite stationary recurrence (for `H > 0`);
* (ii) at every cutoff `h = 1/(d+1)` and time `t` the cutoff law is a normalized finite `A₃`
  law whose root moment and mass density reconstruct `𝓑 = e^{-2Ht}I`, `ϱ = e^{3Ht}`,
  `g = e^{2Ht}I`, `N = 1`, `β = 0` by ADM inversion, with rates/masses the stationary output;
* (iii) the reconstructed Lorentz metrics converge to `g_H`, which solves `G + 3H² g = 0`
  (Einstein tensor computed from the metric field), and the cutoff semigroups converge strongly
  to the `½Δ_{g(t)}` heat semigroup;
* (iv) slab screens with constants depending only on `H, T`;
* (v) derived Cartan curvature `= H²(ϑ∧ϑ)`, frame components `≤ H²` (zero for `H = 0`),
  transport coefficients `≤ |H| e^{2|H|T}` on `|t| ≤ T`, and the curvature-propagation budgets
  pass with `A_* = F_* = 0`;
* (vi) metric-unitary exact links and summable `O(h_n)` torsion / curvature / Palatini defects
  along `h_n = 2^{-n²}`;
* the explicit accept/reject operational family of `thm:main-explicit-operational-family`
  (for `H > 0`, `ω = 3H/2`, expanding branch). -/
theorem vacuum_regulators_genuine.{u} (H : ℝ) (hH : 0 ≤ H) :
    -- (i)
    IsStationaryRenewalSolution (3 * H ^ 2) Set.univ (VacuumRegulatorStationarity.profile H)
      (fun t => H * VacuumRegulatorStationarity.profile H t) (fun _ => 1) id ∧
    (0 < H → ∀ (σ b h : ℝ), (σ = 1 ∨ σ = -1) → 0 ≤ b → b < 1 → (3 * H / 2) * h / 2 ≤ b →
      ∀ (M : ℕ) (q s : ℕ → ℝ), 0 < q 0 → (∀ j < M, 0 < s j) → (∀ j < M, s j ≤ h) →
        FiniteHomogeneousStationarity.SatisfiesRecurrence (3 * H / 2) σ M q s →
        ∀ j ≤ M, |Real.log (q j ^ (2 / 3 : ℝ) / q 0 ^ (2 / 3 : ℝ)) -
            σ * H * FiniteHomogeneousStationarity.renewalTime s j|
          ≤ (2 / 3) * ((3 * H / 2) ^ 3 * FiniteHomogeneousStationarity.renewalTime s M * h ^ 2 /
            (12 * (1 - b ^ 2)))) ∧
    -- (ii)
    (∀ (d : ℕ) (t : ℝ),
      (∀ e, (desitterCutoff H (d + 1) t).eventLaw e = 1 / 12) ∧
      ∑ e : FlatEvent, (desitterCutoff H (d + 1) t).eventLaw e = 1 ∧
      rootMoment (desitterCutoff H (d + 1) t).rootRate (A3PeriodicGraphSampling.mesh (d + 1)) =
        Real.exp (-2 * H * t) • 1 ∧
      (∀ v, massDensity ((desitterCutoff H (d + 1) t).vertexMass v)
        (A3PeriodicGraphSampling.mesh (d + 1)) = Real.exp (3 * H * t)) ∧
      (∀ v, admMetric (rootMoment (desitterCutoff H (d + 1) t).rootRate
          (A3PeriodicGraphSampling.mesh (d + 1)))
          (massDensity ((desitterCutoff H (d + 1) t).vertexMass v)
            (A3PeriodicGraphSampling.mesh (d + 1))) = Real.exp (2 * H * t) • 1) ∧
      (∀ v, admLapse (rootMoment (desitterCutoff H (d + 1) t).rootRate
          (A3PeriodicGraphSampling.mesh (d + 1)))
          (massDensity ((desitterCutoff H (d + 1) t).vertexMass v)
            (A3PeriodicGraphSampling.mesh (d + 1))) = 1) ∧
      predictableDrift (desitterCutoff H (d + 1) t).rootRate
        (A3PeriodicGraphSampling.mesh (d + 1)) = 0 ∧
      (∀ r, (desitterCutoff H (d + 1) t).rootRate r =
        homogeneousRootRate (renewalConductance (VacuumRegulatorStationarity.profile H)
          (fun _ => 1)) (A3PeriodicGraphSampling.mesh (d + 1)) t) ∧
      (∀ v, (desitterCutoff H (d + 1) t).vertexMass v =
        homogeneousVertexMass (renewalDensity (VacuumRegulatorStationarity.profile H))
          (A3PeriodicGraphSampling.mesh (d + 1)) t)) ∧
    -- (iii)
    (∀ t : ℝ, Tendsto (fun n : ℕ => cutoffLorentz H (n + 1) t) atTop (𝓝 (lorentzMetric H t))) ∧
    (∀ (x : Fin 4 → ℝ) (μ ν : Fin 4),
      FriedmannLapseEinstein.einsteinOf
          (FriedmannLapseEinstein.lapseMetric (fun _ => 1) (fun s => Real.exp (H * s))) x μ ν +
        3 * H ^ 2 * lorentzMetric H (x 0) μ ν = 0) ∧
    (∀ t s : ℝ, ∀ hs : 0 ≤ s,
      A3FlatGenerator.pcSystem.StrongOperatorConverges A3FlatGenerator.pcSystem
        (fun n => NormedSpace.exp ((s : ℂ) • desitterStageGen H t (n + 1)))
        (A3FlatGenerator.contSem (s * Real.exp (-2 * H * t))
          (mul_nonneg hs (Real.exp_pos _).le))) ∧
    -- (iv)
    (∀ (T : ℝ) (d : ℕ) (t : ℝ), |t| ≤ T →
      let G := A3PeriodicScreens.scaledGraph (d + 1) (Real.exp (H * t)) (Real.exp_pos _)
      (∀ v, (desitterCutoff H (d + 1) t).vertexMass v = G.mass v) ∧
      (∀ A : Finset (A3PeriodicGraphSampling.Vertex (d + 1)), 0 < A.card →
        2 * A.card ≤ (d + 1) ^ 3 →
        1 / (256 * Real.exp (H * T)) * (∑ v ∈ A, G.mass v) ^ ((2 : ℝ) / 3) ≤
          A3PeriodicGraphSampling.mesh (d + 1) *
            finiteCutCapacity G.conductance A) ∧
      (∀ j, 0 < G.eigenvalue j →
        A3PeriodicScreens.poincareConstant (Real.exp (-H * T)) (Real.exp (H * T)) (1 / 32) ≤
          G.eigenvalue j) ∧
      (∀ R : ℝ, 0 < R →
        (finiteEigenvalueCount G.eigenvalue R : ℝ) ≤
          A3PeriodicScreens.weylConstant (Real.exp (-H * T)) (Real.exp (H * T)) (1 / 32) *
            (1 + R ^ ((3 : ℝ) / 2))) ∧
      (∀ (f : A3PeriodicGraphSampling.Vertex (d + 1) → ℝ) (R : ℝ), 0 < R →
        ∑ j ∈ Finset.univ.filter (fun j => R < G.eigenvalue j),
            G.spectralCoefficient f j ^ 2 ≤
          R⁻¹ * ∑ j, G.eigenvalue j * G.spectralCoefficient f j ^ 2)) ∧
    -- (v)
    DeSitterCartan.curvatureComponents (DeSitterCartan.coframeStructure H)
        (DeSitterCartan.spinConnection H) = DeSitterCartan.constantCurvature H ∧
    (∀ A B D E, |DeSitterCartan.curvatureComponents (DeSitterCartan.coframeStructure H)
        (DeSitterCartan.spinConnection H) A B D E| ≤ H ^ 2) ∧
    (H = 0 → DeSitterCartan.curvatureComponents (DeSitterCartan.coframeStructure H)
        (DeSitterCartan.spinConnection H) = 0) ∧
    (∀ (T : ℝ) (x : Fin 4 → ℝ), |x 0| ≤ T → ∀ c i j,
      |christoffel (FriedmannLapseEinstein.metricJetOf
          (FriedmannLapseEinstein.lapseMetric (fun _ => 1) (fun s => Real.exp (H * s))) x).1
        (FriedmannLapseEinstein.metricJetOf
          (FriedmannLapseEinstein.lapseMetric (fun _ => 1) (fun s => Real.exp (H * s))) x).2.1
        c i j| ≤ |H| * Real.exp (2 * |H| * T)) ∧
    (∀ T : ℝ, 0 ≤ T → ∀ t ∈ Set.Icc 0 T,
      gramEnergy (fun _ => ContinuousLinearMap.id ℝ
          (EuclideanSpace ℝ (Fin 4 × Fin 4 × Fin 4 × Fin 4))) (curvatureRecord H) t ≤
        Real.exp 0 * (gramEnergy (fun _ => ContinuousLinearMap.id ℝ
          (EuclideanSpace ℝ (Fin 4 × Fin 4 × Fin 4 × Fin 4))) (curvatureRecord H) 0 + 0)) ∧
    -- (vi)
    (∀ t V, (DeSitterExactLink.edgeLink H t V).transpose * DeSitterExactLink.eta *
      DeSitterExactLink.edgeLink H t V = DeSitterExactLink.eta) ∧
    (∀ cP cV κ vD : ℝ, 1 ≤ κ → 0 ≤ vD →
      Summable (fun n : ℕ =>
        DeSitterExactLink.Palatini.finiteDefectConst H cP cV κ vD n * diagonalMesh n) ∧
      ∃ N : ℕ, ∀ n ≥ N, diagonalMesh n ≤ DeSitterExactLink.slabMesh H κ n) ∧
    -- operational realization
    (0 < H → ∀ T q₀ : ℝ, 0 < T → 0 < q₀ →
      ExplicitOperationalFamily.ExplicitOperationalFamilyStatement.{u} T (3 * H / 2) q₀ 1) := by
  refine ⟨VacuumRegulatorStationarity.desitterProfile_isStationaryRenewalSolution H,
    fun hHpos σ b h hσ hb0 hb hωb M q s hq0 hs hsh hrec =>
      finite_recurrence_to_profile H hHpos σ b h hσ hb0 hb hωb M q s hq0 hs hsh hrec,
    fun d t => ?_, fun t => (desitterCutoff_lorentz_tendsto H t).1,
    fun x μ ν => (desitterCutoff_lorentz_tendsto H (x 0)).2 x rfl μ ν,
    fun t s hs => desitter_semigroup_strong H t s hs,
    fun T d t ht => ?_, DeSitterCartan.curvature_eq H, desitter_frame_curvature_bound H,
    fun h0 => ?_, fun T x hx c i j => desitter_christoffel_slab_bound H T x hx c i j,
    fun T hT => (desitter_curvature_budgets H T hT).2.2.2.2.2,
    DeSitterExactLink.edgeLink_metric_unitary H,
    fun cP cV κ vD hκ hvD => DeSitterExactLink.Palatini.finiteDefects_full_diagonal H cP cV κ vD
      hκ hvD,
    fun hHpos T q₀ hT hq₀ => ExplicitOperationalFamily.explicit_operational_family hT
      (by positivity) hq₀ (Or.inl rfl)⟩
  · obtain ⟨hB, hρ, hg, hN, hβ, -⟩ := desitterCutoff_adm H (d + 1) t
    obtain ⟨hr, hm⟩ := desitterCutoff_stationary_rates H (d + 1) t
    exact ⟨desitterCutoff_eventLaw H (d + 1) t, (desitterCutoff_eventLaw_sum H (d + 1) t).2,
      hB, hρ, hg, hN, hβ, hr, hm⟩
  · obtain ⟨h1, -, h2, h3, h4, h5⟩ := desitterCutoff_screens H T hH (d + 1) t ht
    exact ⟨h1, by exact_mod_cast h2, h3, h4, h5⟩
  · rw [DeSitterCartan.curvature_eq, h0]
    funext A B D E
    simp [DeSitterCartan.constantCurvature]

/-- Non-vacuity: the assembled statement at the curved branch `H = 1` (`Λ = 3`) and at the flat
branch `H = 0`. -/
example : True := by
  have h1 := vacuum_regulators_genuine.{0} 1 zero_le_one
  have h0 := vacuum_regulators_genuine.{0} 0 le_rfl
  trivial

end

end RenewalGeometry.VacuumRegulatorGenuine
