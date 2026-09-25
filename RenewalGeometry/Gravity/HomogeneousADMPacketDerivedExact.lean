/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.RelationalSchedulerADM
import RenewalGeometry.Gravity.RelationalDeSitterBranch
import RenewalGeometry.Gravity.DeSitterCartanComponentsExact
import RenewalGeometry.DiscreteAnalysis.A3PeriodicScreensScalingExact

/-!
# Derived ADM packets of the flat and de Sitter renewal vacua
  (`con:supp-flat-regulator`, `thm:supp-flat-vacuum`,
  `thm:supp-desitter-adm`, emergent-spacetime supplement)

* `admMetric`, `admLapse` — the ADM inversion formula
  `g = ϱ^{2/3} (det 𝓑)^{1/3} 𝓑⁻¹`, `N = ϱ^{1/3} (det 𝓑)^{1/6}` of
  `thm:supp-adm-frame`; `admPacket_characterization` restates (A4) of
  `relational_scheduler_ADM`: `√det g = ϱ`, `N² g⁻¹ = 𝓑`;
* `predictableDrift`, `predictableDrift_eq_zero_of_reversal_symm` — the
  shift `β_h = h Σ_α k_α α` vanishes for reversal-symmetric root rates;
* `desitter_adm_packet` — for the rates `e^{-2Ht}/(8h²)` and masses
  `e^{3Ht}h³`: `𝓑_h = e^{-2Ht} I`, `ϱ_h = e^{3Ht}`, `g_h = e^{2Ht} I`
  (derived from `admMetric`), `N_h = 1` (derived from `admLapse`),
  `β_h = 0`, conductance `e^{Ht} h / 8`;
* `desitter_slab_screens` — on `|t| ≤ T` the cut / Poincaré / Weyl /
  compact-screen constants of the time-`t` spatial graph are those of
  `A3PeriodicScreens.periodic_screens` with `a₋ = e^{-HT}`, `a₊ = e^{HT}`,
  uniform in `h` and `t` (conditional on the coordinate-grid isoperimetric
  hypothesis of that lemma);
* `FlatPeriodicRegulator`, `flatPeriodicRegulator` — the flat periodic
  renewal regulator record: rates `1/(8h²)`, mass `h³`, identity router,
  identity slow row, zero reward, event alphabet = root-race outcomes ×
  one-point orientation fibre × one-point spectator fibre, with the
  directly normalized race law `k_α/Σk = 1/12`;
* `flat_adm_vacuum` — `𝓑_h = I`, `ϱ_h = 1`, `g_h = I`, `N_h = 1`,
  `β_h = 0`, conductance `h/8`, the Minkowski continuum
  `-dt² + dx²` with vanishing Christoffel symbols, Riemann/Ricci/scalar
  curvature and Einstein tensor, vanishing Cartan torsion and curvature of
  the constant coframe, and vanishing one-cell torsion / curvature /
  Palatini remainders;
* `flat_symbol_expansion` — the Fourier symbol
  `λ_h(k) = (4h²)⁻¹ Σ_{a=1}^{6} [1 - cos(2πh⟨r_a,k⟩)]` equals
  `2π²‖k‖² + O_k(h²)` with an explicit remainder (the pointwise content of
  `lem:supp-flat-symbol`; the strong-resolvent statement is not formalised).
-/

open Matrix
open scoped BigOperators

namespace RenewalGeometry.HomogeneousADMPacket

open RelationalDeSitterBranch

/-! ### The ADM inversion formula -/

/-- `eq:adm-inversion-main`: `g = ϱ^{2/3} (det 𝓑)^{1/3} 𝓑⁻¹`. -/
noncomputable def admMetric (B : Matrix (Fin 3) (Fin 3) ℝ) (ϱ : ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (ϱ ^ ((2 : ℝ) / 3) * B.det ^ ((1 : ℝ) / 3)) • B⁻¹

/-- `eq:adm-inversion-main`: `N = ϱ^{1/3} (det 𝓑)^{1/6}`. -/
noncomputable def admLapse (B : Matrix (Fin 3) (Fin 3) ℝ) (ϱ : ℝ) : ℝ :=
  ϱ ^ ((1 : ℝ) / 3) * B.det ^ ((1 : ℝ) / 6)

/-- (A4) of `relational_scheduler_ADM`: the formula solves
`√det g = ϱ`, `N² g⁻¹ = 𝓑`. -/
theorem admPacket_characterization (B : Matrix (Fin 3) (Fin 3) ℝ) (ϱ : ℝ)
    (hϱ : 0 < ϱ) (hB : 0 < B.det) :
    Real.sqrt (admMetric B ϱ).det = ϱ ∧
      (admLapse B ϱ) ^ 2 • (admMetric B ϱ)⁻¹ = B :=
  relational_scheduler_ADM.2.2.2.2.1 B ϱ hϱ hB

theorem det_smul_one (c : ℝ) :
    (c • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det = c ^ 3 := by
  rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]

theorem inv_smul_one (c : ℝ) (hc : c ≠ 0) :
    (c • (1 : Matrix (Fin 3) (Fin 3) ℝ))⁻¹ = c⁻¹ • 1 := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
    inv_mul_cancel₀ hc, one_smul]

/-! ### Reversal symmetry and the shift -/

/-- Reversal `α ↦ -α` on the twelve oriented roots `a3Roots`. -/
def a3Reverse : Fin 12 → Fin 12 := ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8]

theorem a3Reverse_involutive : Function.Involutive a3Reverse := by
  intro r; fin_cases r <;> rfl

theorem a3Roots_reverse (r : Fin 12) : a3Roots (a3Reverse r) = -a3Roots r := by
  fin_cases r <;> simp [a3Roots, a3Reverse]

/-- The predictable shift `β_h = h Σ_α k_α α` of the root race. -/
noncomputable def predictableDrift (k : Fin 12 → ℝ) (h : ℝ) : Fin 3 → ℝ :=
  h • ∑ r, k r • a3Roots r

/-- Reversal-symmetric rates have zero shift. -/
theorem predictableDrift_eq_zero_of_reversal_symm (k : Fin 12 → ℝ)
    (hk : ∀ r, k (a3Reverse r) = k r) (h : ℝ) :
    predictableDrift k h = 0 := by
  unfold predictableDrift
  have hsum : ∑ r, k r • a3Roots r = 0 := by
    funext i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have hrev : ∑ r, k (a3Reverse r) * a3Roots (a3Reverse r) i =
        ∑ r, k r * a3Roots r i :=
      Fintype.sum_equiv a3Reverse_involutive.toPerm _ _ (fun r => rfl)
    have hneg : ∑ r, k (a3Reverse r) * a3Roots (a3Reverse r) i =
        -∑ r, k r * a3Roots r i := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [hk, a3Roots_reverse]
      simp
    linarith
  rw [hsum, smul_zero]

/-! ### The de Sitter packet -/

theorem desitter_bracket_det (H h t : ℝ) (hh : h ≠ 0) :
    (predictableBracket H h t).det = Real.exp (-6 * H * t) := by
  rw [predictableBracket_eq H h t hh, det_smul_one, ← Real.exp_nat_mul]
  congr 1; push_cast; ring

/-- The spatial metric of `eq:supp-desitter-adm`, derived from the ADM
inversion formula at `𝓑 = e^{-2Ht} I`, `ϱ = e^{3Ht}`. -/
theorem admMetric_desitter (H h t : ℝ) (hh : h ≠ 0) :
    admMetric (predictableBracket H h t) (speedDensity H t) =
      spatialMetric H t := by
  unfold admMetric speedDensity spatialMetric
  rw [desitter_bracket_det H h t hh, predictableBracket_eq H h t hh,
    inv_smul_one _ (Real.exp_ne_zero _), smul_smul]
  congr 1
  rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_neg, ← Real.exp_add,
    ← Real.exp_add]
  congr 1; ring

/-- The lapse of `eq:supp-desitter-adm`, derived from the ADM inversion
formula: `N_h = (e^{3Ht})^{1/3} (e^{-6Ht})^{1/6} = 1`. -/
theorem admLapse_desitter (H h t : ℝ) (hh : h ≠ 0) :
    admLapse (predictableBracket H h t) (speedDensity H t) = lapse H t := by
  unfold admLapse speedDensity lapse
  rw [desitter_bracket_det H h t hh, ← Real.exp_mul, ← Real.exp_mul,
    ← Real.exp_add]
  rw [show 3 * H * t * (1 / 3) + -6 * H * t * (1 / 6) = 0 by ring, Real.exp_zero]

/-- `thm:supp-desitter-adm`, finite clauses: the boxed packet
`𝓑_h = e^{-2Ht} I`, `ϱ_h = e^{3Ht}`, `g_h = e^{2Ht} I`, `N_h = 1`,
`β_h = 0` — with `g_h, N_h` *derived* from the ADM inversion formula and
`β_h` from reversal symmetry — and the conductance `e^{Ht} h / 8`. -/
theorem desitter_adm_packet (H h t : ℝ) (hh : h ≠ 0) :
    predictableBracket H h t = Real.exp (-2 * H * t) • 1 ∧
      speedDensity H t = Real.exp (3 * H * t) ∧
      admMetric (predictableBracket H h t) (speedDensity H t) =
        Real.exp (2 * H * t) • 1 ∧
      admLapse (predictableBracket H h t) (speedDensity H t) = 1 ∧
      predictableDrift (fun _ => rootRate H h t) h = 0 ∧
      vertexMass H h t * rootRate H h t = Real.exp (H * t) * h / 8 :=
  ⟨predictableBracket_eq H h t hh, rfl, admMetric_desitter H h t hh,
    admLapse_desitter H h t hh,
    predictableDrift_eq_zero_of_reversal_symm _ (fun _ => rfl) h,
    conductance_exact H h t hh⟩

/-! ### Slab-uniform screens -/

open A3PeriodicScreens in
/-- The time-`t` de Sitter mass and rate are the scaled periodic-graph data
at scale `a = e^{Ht}` (mesh `h = 1/d`). -/
theorem desitter_mass_rate_scaled (H t : ℝ) (d : ℕ) [NeZero d] :
    (∀ v, vertexMass H (A3PeriodicGraphSampling.mesh d) t =
        scaledMass d (Real.exp (H * t)) v) ∧
      rootRate H (A3PeriodicGraphSampling.mesh d) t =
        scaledRate d (Real.exp (H * t)) := by
  constructor
  · intro v
    unfold vertexMass scaledMass
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  · unfold rootRate scaledRate
    rw [← Real.exp_neg, ← Real.exp_nat_mul]; push_cast; ring_nf

open A3PeriodicScreens in
/-- `thm:supp-desitter-adm`, slab clause: on `|t| ≤ T` the scale
`a(t) = e^{Ht}` lies in `[e^{-HT}, e^{HT}]`, so the cut, Poincaré, Weyl and
compact-screen constants of the time-`t` spatial graph are those of
`periodic_screens` with `a₋ = e^{-HT}`, `a₊ = e^{HT}` — independent of
`h = 1/d` and of `t`.  Conditional on `CoordinateGridIsoperimetry d c₀`. -/
theorem desitter_slab_screens (H T c₀ : ℝ) (hH : 0 ≤ H) (hc₀ : 0 < c₀)
    (d : ℕ) [NeZero d] (hiso : CoordinateGridIsoperimetry d c₀)
    (t : ℝ) (ht : |t| ≤ T) :
    let a := Real.exp (H * t)
    let hapos : 0 < a := Real.exp_pos _
    let G := scaledGraph d a hapos
    (∀ A : Finset (A3PeriodicGraphSampling.Vertex d), 0 < A.card →
      2 * A.card ≤ d ^ 3 →
      c₀ / (8 * Real.exp (H * T)) * (∑ v ∈ A, G.mass v) ^ ((2 : ℝ) / 3) ≤
        A3PeriodicGraphSampling.mesh d * finiteCutCapacity G.conductance A) ∧
    (∀ j, 0 < G.eigenvalue j →
      poincareConstant (Real.exp (-H * T)) (Real.exp (H * T)) c₀ ≤
        G.eigenvalue j) ∧
    (∀ R : ℝ, 0 < R →
      (finiteEigenvalueCount G.eigenvalue R : ℝ) ≤
        weylConstant (Real.exp (-H * T)) (Real.exp (H * T)) c₀ *
          (1 + R ^ ((3 : ℝ) / 2))) ∧
    (∀ (f : A3PeriodicGraphSampling.Vertex d → ℝ) (R : ℝ), 0 < R →
      ∑ j ∈ Finset.univ.filter (fun j => R < G.eigenvalue j),
          G.spectralCoefficient f j ^ 2 ≤
        R⁻¹ * ∑ j, G.eigenvalue j * G.spectralCoefficient f j ^ 2) := by
  intro a hapos G
  have hlow : Real.exp (-H * T) ≤ a := slab_scale_lower H T t hH ht
  have hup : a ≤ Real.exp (H * T) := by
    apply Real.exp_le_exp.mpr
    have := (abs_le.mp ht).2
    nlinarith
  exact periodic_screens d (Real.exp (-H * T)) (Real.exp (H * T)) a c₀
    (Real.exp_pos _) hlow hup hc₀ hiso

/-! ### The flat periodic renewal regulator -/

/-- Event alphabet of the flat regulator: a root-race outcome together
with a point of the (one-point) protected orientation fibre and of the
(one-point) spectator fibre. -/
abbrev FlatEvent := Fin 12 × Unit × Unit

/-- `con:supp-flat-regulator`: the data of the flat periodic renewal
regulator at mesh `h = 1/d` on the persistent spatial state space
`V_h = Λ/dΛ`. -/
structure FlatPeriodicRegulator (d : ℕ) where
  /-- mesh `h = d⁻¹` -/
  mesh : ℝ
  /-- the twelve exponential root branches, rate `k_α` -/
  rootRate : Fin 12 → ℝ
  /-- vertex mass `m_h` -/
  vertexMass : A3PeriodicGraphSampling.Vertex d → ℝ
  /-- root router (the root the race winner is routed to) -/
  rootRouter : Fin 12 → Fin 12
  /-- slow row (the deterministic slow update of the spatial state) -/
  slowRow : A3PeriodicGraphSampling.Vertex d → A3PeriodicGraphSampling.Vertex d
  /-- nonvacuum reward -/
  nonvacuumReward : A3PeriodicGraphSampling.Vertex d → ℝ
  /-- conditional law of the event, normalized directly -/
  eventLaw : FlatEvent → ℝ

/-- The flat periodic renewal regulator: rates `1/(8h²)`, mass `h³`,
identity router, identity slow row, zero reward, and the directly
normalized race law `k_α / Σ_β k_β`. -/
noncomputable def flatPeriodicRegulator (d : ℕ) : FlatPeriodicRegulator d where
  mesh := A3PeriodicGraphSampling.mesh d
  rootRate := fun _ => 1 / (8 * A3PeriodicGraphSampling.mesh d ^ 2)
  vertexMass := A3PeriodicGraphSampling.mass d
  rootRouter := id
  slowRow := id
  nonvacuumReward := 0
  eventLaw := fun _ =>
    (1 / (8 * A3PeriodicGraphSampling.mesh d ^ 2)) /
      ∑ _s : Fin 12, 1 / (8 * A3PeriodicGraphSampling.mesh d ^ 2)

/-- The race law is the uniform law `1/12` on the twelve roots. -/
theorem flatPeriodicRegulator_eventLaw (d : ℕ) [NeZero d] (e : FlatEvent) :
    (flatPeriodicRegulator d).eventLaw e = 1 / 12 := by
  unfold flatPeriodicRegulator
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hm := (A3PeriodicGraphSampling.mesh_pos d).ne'
  field_simp
  norm_num

/-- The event law is normalized. -/
theorem flatPeriodicRegulator_eventLaw_sum (d : ℕ) [NeZero d] :
    ∑ e : FlatEvent, (flatPeriodicRegulator d).eventLaw e = 1 := by
  simp [flatPeriodicRegulator_eventLaw]

/-- The regulator's rates and masses are the `H = 0` de Sitter data, its
spatial graph is the periodic `A₃` graph at scale `a = 1`, and mass times
rate is `h/8`. -/
theorem flatPeriodicRegulator_spatial (d : ℕ) [NeZero d] :
    (∀ r t, (flatPeriodicRegulator d).rootRate r =
        rootRate 0 (A3PeriodicGraphSampling.mesh d) t) ∧
      (∀ v t, (flatPeriodicRegulator d).vertexMass v =
        vertexMass 0 (A3PeriodicGraphSampling.mesh d) t) ∧
      (∀ v, (flatPeriodicRegulator d).vertexMass v =
        A3PeriodicScreens.scaledMass d 1 v) ∧
      A3PeriodicScreens.scaledConductance d 1 =
        A3PeriodicGraphSampling.conductance d ∧
      (∀ v r, (flatPeriodicRegulator d).vertexMass v *
        (flatPeriodicRegulator d).rootRate r =
          A3PeriodicGraphSampling.mesh d / 8) := by
  refine ⟨fun r t => ?_, fun v t => ?_, fun v => ?_, rfl, fun v r => ?_⟩
  · simp [flatPeriodicRegulator, RelationalDeSitterBranch.rootRate]
  · simp [flatPeriodicRegulator, RelationalDeSitterBranch.vertexMass,
      A3PeriodicGraphSampling.mass]
  · simp [flatPeriodicRegulator, A3PeriodicScreens.scaledMass,
      A3PeriodicGraphSampling.mass]
  · exact relational_flat_vacuum.2 _ (A3PeriodicGraphSampling.mesh_pos d).ne'

/-! ### The flat vacuum -/

theorem minkowski_gamma_zero : flrwGamma 1 0 = 0 := by
  funext c i j; unfold flrwGamma; split_ifs <;> simp

theorem minkowski_dGamma_zero : flrwdGamma 1 0 0 = 0 := by
  funext e c i j; unfold flrwdGamma; split_ifs <;> simp

theorem minkowski_riemann_zero :
    riemann (flrwGamma 1 0) (flrwdGamma 1 0 0) = 0 := by
  rw [minkowski_gamma_zero, minkowski_dGamma_zero]
  funext a b c d; simp [riemann]

theorem minkowski_ricci_zero :
    ricci (flrwGamma 1 0) (flrwdGamma 1 0 0) = 0 := by
  funext b d
  simp [ricci, minkowski_riemann_zero]

theorem minkowski_scalar_zero :
    scalarCurv (flrwGinv 1) (flrwGamma 1 0) (flrwdGamma 1 0 0) = 0 := by
  simp [scalarCurv, minkowski_ricci_zero]

/-- The `H = 0` relational metric is Minkowski `diag(-1,1,1,1)`. -/
theorem lorentzMetric_zero_eq_minkowski (t : ℝ) :
    lorentzMetric 0 t = flrwG 1 := by
  rw [lorentzMetric_eq_flrwG, zero_mul, Real.exp_zero]

/-- `thm:supp-flat-vacuum`, finite clauses: the boxed packet
`𝓑_h = I`, `ϱ_h = 1`, `g_h = I` (derived from the ADM inversion),
`N_h = 1` (derived), `β_h = 0`; conductance `h/8`; the Minkowski continuum
`-dt² + dx²` with vanishing Christoffel symbols (from the metric jet),
Riemann, Ricci, scalar curvature and Einstein tensor; vanishing Cartan
torsion and curvature of the constant coframe (`H = 0`); and vanishing
one-cell torsion / curvature / Palatini remainders. -/
theorem flat_adm_vacuum (h : ℝ) (hh : h ≠ 0) :
    (∀ t, predictableBracket 0 h t = 1) ∧
      (∀ t, speedDensity 0 t = 1) ∧
      (∀ t, admMetric (predictableBracket 0 h t) (speedDensity 0 t) = 1) ∧
      (∀ t, admLapse (predictableBracket 0 h t) (speedDensity 0 t) = 1) ∧
      (∀ t, predictableDrift (fun _ => rootRate 0 h t) h = 0) ∧
      (∀ t, vertexMass 0 h t * rootRate 0 h t = h / 8) ∧
      (∀ t, lorentzMetric 0 t = flrwG 1) ∧
      christoffel (flrwGinv 1) (flrwdg 1 0) = 0 ∧
      riemann (flrwGamma 1 0) (flrwdGamma 1 0 0) = 0 ∧
      ricci (flrwGamma 1 0) (flrwdGamma 1 0 0) = 0 ∧
      scalarCurv (flrwGinv 1) (flrwGamma 1 0) (flrwdGamma 1 0 0) = 0 ∧
      (∀ i j, ricci (flrwGamma 1 0) (flrwdGamma 1 0 0) i j -
        1 / 2 * flrwG 1 i j *
          scalarCurv (flrwGinv 1) (flrwGamma 1 0) (flrwdGamma 1 0 0) = 0) ∧
      DeSitterCartan.coframeStructure 0 = 0 ∧
      DeSitterCartan.spinConnection 0 = 0 ∧
      DeSitterCartan.torsionComponents (DeSitterCartan.coframeStructure 0)
        (DeSitterCartan.spinConnection 0) = 0 ∧
      DeSitterCartan.curvatureComponents (DeSitterCartan.coframeStructure 0)
        (DeSitterCartan.spinConnection 0) = 0 ∧
      torsionCellRemainder 0 h = 0 ∧
      curvatureCellRemainder 0 h = 0 ∧
      palatiniCellRemainder 0 h = 0 := by
  have hB : ∀ t, predictableBracket 0 h t = 1 := fun t => by
    rw [predictableBracket_eq 0 h t hh]; simp
  have hρ : ∀ t, speedDensity 0 t = 1 := fun t => by simp [speedDensity]
  refine ⟨hB, hρ, fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_,
    lorentzMetric_zero_eq_minkowski, ?_, minkowski_riemann_zero,
    minkowski_ricci_zero, minkowski_scalar_zero, fun i j => ?_, ?_, ?_,
    DeSitterCartan.torsion_free 0, ?_, ?_, ?_, ?_⟩
  · rw [admMetric_desitter 0 h t hh]; simp [spatialMetric]
  · rw [admLapse_desitter 0 h t hh]; rfl
  · exact predictableDrift_eq_zero_of_reversal_symm _ (fun _ => rfl) h
  · rw [conductance_exact 0 h t hh]; simp
  · rw [flrw_christoffel one_ne_zero 0, minkowski_gamma_zero]
  · rw [minkowski_ricci_zero, minkowski_scalar_zero]; simp
  · funext A B C; unfold DeSitterCartan.coframeStructure; split_ifs <;> simp
  · funext A B C; unfold DeSitterCartan.spinConnection; split_ifs <;> simp
  · rw [DeSitterCartan.curvature_eq]
    funext A B D E; unfold DeSitterCartan.constantCurvature; simp
  · unfold torsionCellRemainder scalarTimeLink; simp
  · unfold curvatureCellRemainder; simp
  · unfold palatiniCellRemainder scalarTimeLink; simp

/-! ### The flat Fourier symbol (`lem:supp-flat-symbol`, pointwise) -/

/-- One orientation of the six root pairs (`a3Roots 0,1,4,5,8,9`). -/
def orientedRoot : Fin 6 → (Fin 3 → ℝ) :=
  ![a3Roots 0, a3Roots 1, a3Roots 4, a3Roots 5, a3Roots 8, a3Roots 9]

/-- The pairing `⟨r_a, k⟩`. -/
def rootPairing (k : Fin 3 → ℝ) (a : Fin 6) : ℝ := ∑ i, orientedRoot a i * k i

/-- Root-frame identity for one orientation: `Σ_a ⟨r_a,k⟩² = 4‖k‖²`. -/
theorem orientedRoot_frame (k : Fin 3 → ℝ) :
    ∑ a, rootPairing k a ^ 2 = 4 * ∑ i, k i ^ 2 := by
  simp only [rootPairing, Fin.sum_univ_succ, Fin.sum_univ_zero, orientedRoot,
    a3Roots]
  simp
  ring

/-- The Fourier symbol `λ_h(k) = (4h²)⁻¹ Σ_{a=1}^{6} [1 - cos(2πh⟨r_a,k⟩)]`
of `-L_h` at the flat rates `1/(8h²)`. -/
noncomputable def flatSymbol (h : ℝ) (k : Fin 3 → ℝ) : ℝ :=
  (1 / (4 * h ^ 2)) *
    ∑ a, (1 - Real.cos (2 * Real.pi * h * rootPairing k a))

/-- Pointwise flat-generator limit with explicit remainder:
`|λ_h(k) - 2π²‖k‖²| ≤ (5/96)(2π)⁴ h² Σ_a ⟨r_a,k⟩⁴ / 4` whenever every
`|2πh⟨r_a,k⟩| ≤ 1`; hence `λ_h(k) → 2π²‖k‖²` as `h → 0`. -/
theorem flat_symbol_expansion (h : ℝ) (hh : h ≠ 0) (k : Fin 3 → ℝ)
    (hsmall : ∀ a, |2 * Real.pi * h * rootPairing k a| ≤ 1) :
    |flatSymbol h k - 2 * Real.pi ^ 2 * ∑ i, k i ^ 2| ≤
      5 / 96 * (2 * Real.pi) ^ 4 * h ^ 2 *
        (∑ a, rootPairing k a ^ 4) / 4 := by
  have hframe := orientedRoot_frame k
  have hh2 : 0 < h ^ 2 := by positivity
  -- rewrite the target difference as an average of cosine remainders
  have hdiff : flatSymbol h k - 2 * Real.pi ^ 2 * ∑ i, k i ^ 2 =
      (1 / (4 * h ^ 2)) *
        ∑ a, -(Real.cos (2 * Real.pi * h * rootPairing k a) -
          (1 - (2 * Real.pi * h * rootPairing k a) ^ 2 / 2)) := by
    unfold flatSymbol
    have hsplit : ∑ a, -(Real.cos (2 * Real.pi * h * rootPairing k a) -
        (1 - (2 * Real.pi * h * rootPairing k a) ^ 2 / 2)) =
        ∑ a, (1 - Real.cos (2 * Real.pi * h * rootPairing k a)) -
          (2 * Real.pi * h) ^ 2 / 2 * ∑ a, rootPairing k a ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    rw [hsplit, hframe, mul_sub]
    field_simp
  rw [hdiff, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (4 * h ^ 2))]
  have hbound : |∑ a, -(Real.cos (2 * Real.pi * h * rootPairing k a) -
      (1 - (2 * Real.pi * h * rootPairing k a) ^ 2 / 2))| ≤
      ∑ a, (2 * Real.pi * h * rootPairing k a) ^ 4 * (5 / 96) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [abs_neg]
    have hc := Real.cos_bound (hsmall a)
    have h4 : |2 * Real.pi * h * rootPairing k a| ^ 4 =
        (2 * Real.pi * h * rootPairing k a) ^ 4 := by
      rw [← abs_pow, abs_of_nonneg (by positivity)]
    rwa [h4] at hc
  calc 1 / (4 * h ^ 2) * |∑ a, -(Real.cos (2 * Real.pi * h * rootPairing k a) -
        (1 - (2 * Real.pi * h * rootPairing k a) ^ 2 / 2))|
      ≤ 1 / (4 * h ^ 2) *
          ∑ a, (2 * Real.pi * h * rootPairing k a) ^ 4 * (5 / 96) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 5 / 96 * (2 * Real.pi) ^ 4 * h ^ 2 * (∑ a, rootPairing k a ^ 4) / 4 := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun a _ => ?_
        field_simp

end RenewalGeometry.HomogeneousADMPacket
