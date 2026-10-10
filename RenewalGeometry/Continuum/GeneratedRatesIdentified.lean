/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.KatoGeneratedDynamics
import RenewalGeometry.Continuum.GeneratedGalerkinConsistency

/-!
# The rates of the generated dynamics, with the limit identified

Generic infrastructure (no renewal notions) for `thm:generated-dynamics` (Einstein–Standard-Model
action-closure manuscript, `eq:generated-Galerkin-rate`: "where `U` is the physical Sobolev
solution with initial datum `U₀`").  `GeneratedRatesId` is the rate package
`KatoGenDyn.GeneratedRates` of the fully finite approximation branch with one further clause: the
limit solution `U` against which all rates are measured **coincides with every smooth classical
solution with the same data** on its interval (`GenGalCons.galerkin_tendsto_smooth`: the Galerkin
solutions converge to every smooth solution; the rate `ρ = 0` identifies the limits mode by mode;
completeness of the Hartley basis).  The proof is that of `KatoGenDyn.generated_dynamics_rates`
with this clause added.

* **`generated_dynamics_rates_id`** — the identified rate package (`q = s + p + 8`).
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff Real RealInnerProductSpace

noncomputable section

namespace RenewalGeometry.GenRatesId

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy KatoGalerkin KatoSecond
  KatoTimeRate KatoRate2 KatoGenDyn
open KatoCausal (hmS hmS_apply hmS_add hmS_smul hmS_sub norm_hmS_sq cf_GN cf_sub')

set_option linter.unusedSectionVars false

variable {d n : ℕ}
variable {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}

/-- **The rate package of the fully finite approximation branch** (`thm:generated-dynamics`,
Fourier form; `q = s + p + 8`): there are `T > 0`, `R`, `c_* > 0`, `τ_* > 0`, `C` such that every
smooth periodic datum `U₀` with `‖U₀‖_{H^q} ≤ R₀` has a classical solution `U` on `[0, T] × 𝕋^d`
(spatial derivatives `P`, `∂_tU = G(U)`), with coefficients twice differentiable in time
(`d/dt c_k(U) = c_k(G(U))`, `d/dt c_k(G(U)) = D₂`), and for every cutoff `N`, step `τ` with
`τ(N+1) ≤ c_*`, `τ ≤ τ_*`, and every finite datum `U_{0,N}` (`‖U_{0,N}‖_{H^q} ≤ R₀`,
`‖U_{0,N} - U₀‖_{H^{s+4}} ≤ δ`) the midpoint recursion exists on `[0, T]` with `‖U^j‖_{H^q} ≤ R`,
`‖U^j - U(jτ)‖_{H^{s+4}} ≤ C(τ² + δ + ν)` and, on every cell, the Hermite readout satisfies
`‖z - U‖_{H^{s+2}}, ‖∂_tz - ∂_tU‖_{H^{s+2}} ≤ C(τ² + δ + ν)`, `‖∂_t²z - ∂_t²U‖_{H^s} ≤ C(τ + δ + ν)`
(`ν = (N+1)^{-p}`; all norms in Fourier form over arbitrary finite mode sets). -/
def GeneratedRatesId (A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ) (F : Fin n → (Fin n → ℝ) → ℝ)
    (s p : ℕ) (R₀ : ℝ) : Prop :=
    ∃ T > 0, ∃ R ≥ 0, ∃ cstar > 0, ∃ τstar > 0, ∃ C ≥ 0,
      ∀ U₀ : Fin n → ST d → ℝ, (∀ b, ContDiff ℝ ∞ (U₀ b)) → (∀ b, IsSPeriodic (U₀ b)) →
      energyQ (s + p + 8) U₀ 0 ≤ R₀ ^ 2 →
      ∃ (U : Fin n → ST d → ℝ) (P : Fin n → Fin d → ST d → ℝ)
        (D₂ : Fin n → (Fin d → ℤ) → ℝ → ℝ),
        (∀ b, Continuous (U b)) ∧ (∀ b, IsSPeriodic (U b)) ∧
        (∀ b y, U b (Fin.cons 0 y) = U₀ b (Fin.cons 0 y)) ∧
        (∀ b (i : Fin d) x, HasDerivAt (fun σ : ℝ => U b (x + σ • ev i.succ)) (P b i x) 0) ∧
        (∀ b, ∀ t ∈ Icc 0 T, ∀ y, HasDerivWithinAt (fun σ => U b (Fin.cons σ y))
          (genP A F U P b (Fin.cons t y)) (Icc 0 T) t) ∧
        (∀ b k, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun σ => coef (U b) σ k)
          (coef (genP A F U P b) t k) (Icc 0 T) t) ∧
        (∀ b k, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun σ => coef (genP A F U P b) σ k)
          (D₂ b k t) (Icc 0 T) t) ∧
        (∀ (V : Fin n → ST d → ℝ) (T' : ℝ), T' ≤ T → (∀ b, ContDiff ℝ ∞ (V b)) →
          (∀ b, IsSPeriodic (V b)) → (∀ b y, V b (Fin.cons 0 y) = U₀ b (Fin.cons 0 y)) →
          (∀ b, ∀ t ∈ Icc 0 T', ∀ y, pd (V b) 0 (Fin.cons t y) = genG A F V b (Fin.cons t y)) →
          ∀ x ∈ slab (d := d) 0 T', ∀ b, U b x = V b x) ∧
        ∀ (N : ℕ) (τ : ℝ), 0 < τ → τ * ((N : ℝ) + 1) ≤ cstar → τ ≤ τstar →
        ∀ (a₀ : GS d n N) (δ : ℝ), ‖a₀‖ ≤ R₀ → 0 ≤ δ →
        (∀ S : Finset (Fin d → ℤ), ∑ b, ∑ k ∈ S,
          wq (s + 4) k * (cf (s + p + 8) a₀ b k - coef (U₀ b) 0 k) ^ 2 ≤ δ ^ 2) →
        ∃ Ud : ℕ → GS d n N, Ud 0 = a₀ ∧
          (∀ j : ℕ, (j : ℝ) * τ ≤ T → ‖Ud j‖ ≤ R ∧ (((j : ℝ) + 1) * τ ≤ T →
            Ud (j + 1) = Ud j + τ • GN A F (s + p + 8) (SpectralGalerkin.mid (Ud j) (Ud (j + 1))))) ∧
          (∀ j : ℕ, (j : ℝ) * τ ≤ T → ∀ S : Finset (Fin d → ℤ),
            ∑ b, ∑ k ∈ S, wq (s + 4) k * (cf (s + p + 8) (Ud j) b k - coef (U b) (j * τ) k) ^ 2 ≤
              (C * (τ ^ 2 + δ + 1 / ((N : ℝ) + 1) ^ p)) ^ 2) ∧
          (∀ j : ℕ, ((j : ℝ) + 1) * τ ≤ T → ∀ θ ∈ Icc (0 : ℝ) 1, ∀ S : Finset (Fin d → ℤ),
            (∑ b, ∑ k ∈ S, wq (s + 2) k * (cf (s + p + 8) (SpectralGalerkin.hermite τ (Ud j)
                (Ud (j + 1)) (GN A F (s + p + 8) (Ud j)) (GN A F (s + p + 8) (Ud (j + 1))) θ) b k -
                coef (U b) (j * τ + θ * τ) k) ^ 2 ≤
              (C * (τ ^ 2 + δ + 1 / ((N : ℝ) + 1) ^ p)) ^ 2) ∧
            (∑ b, ∑ k ∈ S, wq (s + 2) k * (cf (s + p + 8) (SpectralGalerkin.hermiteD τ (Ud j)
                (Ud (j + 1)) (GN A F (s + p + 8) (Ud j)) (GN A F (s + p + 8) (Ud (j + 1))) θ) b k -
                coef (genP A F U P b) (j * τ + θ * τ) k) ^ 2 ≤
              (C * (τ ^ 2 + δ + 1 / ((N : ℝ) + 1) ^ p)) ^ 2) ∧
            (∑ b, ∑ k ∈ S, wq s k * (cf (s + p + 8) (SpectralGalerkin.hermiteDD τ (Ud j)
                (Ud (j + 1)) (GN A F (s + p + 8) (Ud j)) (GN A F (s + p + 8) (Ud (j + 1))) θ) b k -
                D₂ b k (j * τ + θ * τ)) ^ 2 ≤
              (C * (τ + δ + 1 / ((N : ℝ) + 1) ^ p)) ^ 2))

set_option maxHeartbeats 8000000 in
/-- **The fully finite approximation branch: rates** (`thm:generated-dynamics`,
`eq:generated-Galerkin-rate`, `eq:generated-time-rate`, `eq:generated-Hermite`; Fourier form).
Let `m_s > d/2`, `2m_s ≤ s + 1`, `1 ≤ p`, `m_s ≤ p + 3`, `q = s + p + 8`, `A^i` smooth real
symmetric, `F` smooth.  For every data radius `R₀` there are `T > 0`, `R`, `c_* > 0`, `τ_* > 0`
and `C` such that every smooth periodic datum `U₀` with `‖U₀‖_{H^q} ≤ R₀` has a classical solution
`U` on `[0, T] × 𝕋^d` (spatial derivatives `P`, `∂_tU = G(U) = F(U) - Σ_i A^i(U)P_i`) whose
coefficients are twice differentiable in time: `d/dt c_k(U) = c_k(G(U))`, `d/dt c_k(G(U)) = D₂`;
and for every cutoff `N`, step `τ > 0` with `τ(N+1) ≤ c_*`, `τ ≤ τ_*`, and every finite datum
`U_{0,N}` with `‖U_{0,N}‖_{H^q} ≤ R₀` and `‖U_{0,N} - U₀‖_{H^{s+4}} ≤ δ`, the implicit midpoint
recursion `U^{j+1} = U^j + τ G_N((U^j + U^{j+1})/2)`, `U^0 = U_{0,N}`, exists for `jτ ≤ T` with
`‖U^j‖_{H^q} ≤ R`, and (with `ν = (N+1)^{-p}`, for every finite mode set `S`):
* `‖U^j - U(jτ)‖_{H^{s+4}} ≤ C (τ² + δ + ν)`;
* on every cell `[jτ, (j+1)τ] ⊆ [0, T]`, the cubic Hermite readout `z` of the record (nodal values
  `U^j`, nodal slopes `G_N(U^j)`) satisfies, at `t = jτ + θτ`,
  `‖z - U(t)‖_{H^{s+2}} ≤ C (τ² + δ + ν)`, `‖∂_tz - ∂_tU(t)‖_{H^{s+2}} ≤ C (τ² + δ + ν)`,
  `‖∂_t²z - ∂_t²U(t)‖_{H^s} ≤ C (τ + δ + ν)` (`∂_tz = hermiteD`, `∂_t²z = hermiteDD`,
  `SpectralGalerkin.hasDerivAt_hermite`). -/
theorem generated_dynamics_rates_id {ms s p : ℕ} (hms : (d : ℝ) / 2 < ms) (hs : 2 * ms ≤ s + 1)
    (hp : 1 ≤ p) (hmsp : ms ≤ p + 3) (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b))
    (hsym : ∀ i a b v, A i a b v = A i b a v) (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R₀ : ℝ}
    (hR₀ : 0 ≤ R₀) :
    GeneratedRatesId A F s p R₀ := by
  unfold GeneratedRatesId
  have hms1 : 1 ≤ ms := by
    have : (0 : ℝ) < ms := lt_of_le_of_lt (by positivity) hms
    exact_mod_cast this
  -- Kato's theorem with the sharp rates, the midpoint scheme and the Galerkin data family
  obtain ⟨T₁, hT₁, RK, hRK, CK, hCK, Cdt, hCdt, hK⟩ := KatoRates.kato_sharp_rates_dt (d := d)
    (n := n) (ms := ms) (r := s + p + 7) hms (by omega) (by omega) hA hsym hF hR₀
  obtain ⟨T₂, hT₂, Rm, hRm, cstar, hc, τs, hτs, CM, -, hmid⟩ := KatoCFL.midpoint_uniform_cfl
    (d := d) (n := n) (m := ms) (q := s + p + 8) hms (by omega) hA hsym hF hR₀
  obtain ⟨T₃, hT₃, hgal⟩ := galerkin_uniform_data (d := d) (n := n) (ms := ms) (q := s + p + 8)
    hms (by omega) hA hsym hF hR₀
  set R := RK + Rm + (2 * R₀ + 1) with hRdef
  have hR : 0 ≤ R := by positivity
  have hRKR : RK ≤ R := by rw [hRdef]; linarith
  have hRmR : Rm ≤ R := by rw [hRdef]; linarith
  have hR₀R : 2 * R₀ + 1 ≤ R := by rw [hRdef]; linarith
  set T := min T₁ (min T₂ T₃) with hTdef
  have hT : 0 < T := lt_min hT₁ (lt_min hT₂ hT₃)
  have hTT₁ : T ≤ T₁ := min_le_left _ _
  have hTT₂ : T ≤ T₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hTT₃ : T ≤ T₃ := (min_le_right _ _).trans (min_le_right _ _)
  have hsub₁ : Icc 0 T ⊆ Icc 0 T₁ := Icc_subset_Icc le_rfl hTT₁
  -- the cutoff-uniform constants
  obtain ⟨K₁, hK₁0, h₁⟩ := midpoint_time_rate (d := d) (n := n) (A := A) (F := F) (ms := ms)
    (m := s + 4) (q := s + p + 8) hms (by omega) (by omega) (by omega) (by omega) hA hsym hF hR
  obtain ⟨C₁, hC₁0, hC₁⟩ := h₁ T hT.le
  obtain ⟨K₂, hK₂0, h₂⟩ := hermite_semidiscrete (d := d) (n := n) (A := A) (F := F) (ms := ms)
    (ρ := s + 2) (q := s + p + 8) hms (by omega) (by omega) (by omega) (by omega) hA hsym hF hR
  obtain ⟨C₂, hC₂0, hC₂⟩ := h₂ T hT.le
  obtain ⟨K₃, hK₃0, h₃⟩ := hermite_semidiscrete (d := d) (n := n) (A := A) (F := F) (ms := ms)
    (ρ := s) (q := s + p + 8) hms (by omega) hs (by omega) (by omega) hA hsym hF hR
  obtain ⟨C₃, hC₃0, hC₃⟩ := h₃ T hT.le
  obtain ⟨Ks, hKs0, hstab⟩ := galerkin_stable_hm (d := d) (n := n) (A := A) (F := F) (ms := ms)
    (m := s + 4) (q := s + p + 8) hms (by omega) (by omega) hA hsym hF hR
  obtain ⟨L₂, hL₂0, hL₂⟩ := GN_lip_hm (d := d) (n := n) (A := A) (F := F) (ms := ms) (ρ := s + 2)
    hms (by omega) hA hF hR
  obtain ⟨L₁, hL₁0, hL₁⟩ := GN_lip_hm (d := d) (n := n) (A := A) (F := F) (ms := ms) (ρ := s + 1)
    hms (by omega) hA hF hR
  obtain ⟨LD, hLD0, hLD⟩ := DGN_bound (d := d) (n := n) (A := A) (F := F) (ms := ms) (ρ := s)
    hms hs hA hF hR
  obtain ⟨LL, hLL0, hLL⟩ := DGN_lip (d := d) (n := n) (A := A) (F := F) (ms := ms) (ρ := s)
    hms hs hA hF hR
  obtain ⟨MA, hMA0, hMA⟩ := curve_lip (d := d) (n := n) (A := A) (F := F) (ms := ms)
    (ρ := s + 1) (q := s + p + 8) hms (by omega) (by omega) hA hF hR
  obtain ⟨C₄, hC₄0, h₄⟩ := second_limit (d := d) (n := n) (A := A) (F := F) (ms := ms) (ρ := s)
    (q := s + p + 8) hms hs (by omega) hA hF hR
  -- the overall constants
  set E := Real.exp (Ks * T) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  set A₀ := (1 + 4 * π ^ 2 * (d : ℝ)) ^ (s + 1) * CK + RK ^ 2 with hA₀
  set A₂ := (1 + 4 * π ^ 2 * (d : ℝ)) ^ (s + 2) * CK + RK ^ 2 with hA₂
  set A₄ := (1 + 4 * π ^ 2 * (d : ℝ)) ^ (s + 4) * CK + RK ^ 2 with hA₄
  have hA₀0 : 0 ≤ A₀ := by positivity
  have hA₂0 : 0 ≤ A₂ := by positivity
  have hA₄0 : 0 ≤ A₄ := by positivity
  set B₄ := C₄ * (A₀ + Cdt (s + 1) + 1) with hB₄
  have hB₄0 : 0 ≤ B₄ := by have := hCdt (s + 1); positivity
  set Lstab := 1 + L₂ + LD * L₁ + LL * MA with hLstab
  have hLstab1 : 1 ≤ Lstab := by
    have := mul_nonneg hLD0 hL₁0
    have := mul_nonneg hLL0 hMA0
    rw [hLstab]; linarith
  set C := C₁ + C₂ + C₃ + E * Lstab + Real.sqrt A₄ + Real.sqrt A₂ + Real.sqrt (Cdt (s + 2)) +
    Real.sqrt B₄ with hCdef
  have hs4 := Real.sqrt_nonneg A₄
  have hs2 := Real.sqrt_nonneg A₂
  have hsd := Real.sqrt_nonneg (Cdt (s + 2))
  have hsB := Real.sqrt_nonneg B₄
  have hELs : 0 ≤ E * Lstab := mul_nonneg hE0 (by linarith)
  have hC1 : C₁ ≤ C := by rw [hCdef]; linarith
  have hC2 : C₂ ≤ C := by rw [hCdef]; linarith
  have hC3 : C₃ ≤ C := by rw [hCdef]; linarith
  have hCE : E * Lstab ≤ C := by rw [hCdef]; linarith
  have hC4 : Real.sqrt A₄ ≤ C := by rw [hCdef]; linarith
  have hC5 : Real.sqrt A₂ ≤ C := by rw [hCdef]; linarith
  have hC6 : Real.sqrt (Cdt (s + 2)) ≤ C := by rw [hCdef]; linarith
  have hC7 : Real.sqrt B₄ ≤ C := by rw [hCdef]; linarith
  have hC0 : 0 ≤ C := hC1.trans' hC₁0
  have hEL1 : E ≤ C := (le_mul_of_one_le_right hE0 hLstab1).trans hCE
  have hL₂L : L₂ ≤ Lstab := by
    have := mul_nonneg hLD0 hL₁0
    have := mul_nonneg hLL0 hMA0
    rw [hLstab]; linarith
  have hL₃L : LD * L₁ + LL * MA ≤ Lstab := by
    rw [hLstab]; linarith
  have hEL2 : E * L₂ ≤ C := le_trans (mul_le_mul_of_nonneg_left hL₂L hE0) hCE
  have hEL3 : E * (LD * L₁ + LL * MA) ≤ C := le_trans (mul_le_mul_of_nonneg_left hL₃L hE0) hCE
  set τstar := min τs (1 / (K₁ + K₂ + K₃ + 1)) with hτstar
  refine ⟨T, hT, R, hR, cstar, hc, τstar, lt_min hτs (by positivity), C, hC0,
    fun U₀ hU₀ hUp hE₀ => ?_⟩
  obtain ⟨U, P, γ, hG, hUc, hUper, hU0, hP, hUt, hcoef, -, hr0, hr1⟩ := hK U₀ hU₀ hUp hE₀
  have hGc : ∀ N, GalCurve A F (s + p + 8) T R (γ N) := fun N =>
    galCurve_mono (q := s + p + 8) ⟨hG.deriv N, hG.bound N⟩ hTT₁ hRKR
  -- the second time derivative of the limit
  obtain ⟨D₂, hD₂d, hD₂r⟩ := h₄ T γ hGc (fun b k t => coef (U b) t k)
    (fun b k t => coef (genP A F U P b) t k)
    (fun N => A₀ / ((N : ℝ) + 1) ^ (2 * (s + p + 7 - (s + 1)) + 1))
    (fun N => Cdt (s + 1) / ((N : ℝ) + 1) ^ (2 * (s + p + 7 - (s + 1 + 1)) + 1))
    (antitone_rate hA₀0 _) (antitone_rate (hCdt _) _) (tendsto_rate (by omega))
    (tendsto_rate (by omega))
    (fun N t ht S => hr0 (s + 1) (by omega) N t (hsub₁ ht) S)
    (fun N t ht S => by
      simp only [cf_GN_ite]
      exact hr1 (s + 1) (by omega) (by omega) N t (hsub₁ ht) S)
  -- identification with every smooth solution (Galerkin consistency)
  have hunique : ∀ (V : Fin n → ST d → ℝ) (T' : ℝ), T' ≤ T → (∀ b, ContDiff ℝ ∞ (V b)) →
      (∀ b, IsSPeriodic (V b)) → (∀ b y, V b (Fin.cons 0 y) = U₀ b (Fin.cons 0 y)) →
      (∀ b, ∀ t ∈ Icc 0 T', ∀ y, pd (V b) 0 (Fin.cons t y) = genG A F V b (Fin.cons t y)) →
      ∀ x ∈ slab (d := d) 0 T', ∀ b, U b x = V b x := by
    intro V T' hT' hV hVp hV0 hVeq x hx b
    have hx0 : 0 ≤ x 0 := hx.1
    have hT'0 : 0 ≤ T' := hx0.trans hx.2
    have hsubT : Icc 0 T' ⊆ Icc 0 T₁ := Icc_subset_Icc le_rfl (hT'.trans hTT₁)
    have hlimV := GenGalCons.galerkin_tendsto_smooth (m := ms) (q := s + p + 7 + 1) hms
      (by omega) hA hsym hF hT'0 hRK hG.init (fun N t ht => (hG.deriv N t (hsubT ht)).mono hsubT)
      (fun N t ht => hG.bound N t (hsubT ht)) hV hVp hV0 hVeq
    have hcoefeq : ∀ k, coef (fun y => U b y - V b y) (x 0) k = 0 := by
      intro k
      have hlimU : Tendsto (fun N => cf (s + p + 7 + 1) (γ N (x 0)) b k) atTop
          (𝓝 (coef (U b) (x 0) k)) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        have hb := fun N => hr0 0 (Nat.zero_le _) N (x 0) (hsubT hx) {k}
        set c0 := (1 + 4 * π ^ 2 * (d : ℝ)) ^ 0 * CK + RK ^ 2 with hc0
        have hc00 : 0 ≤ c0 := by positivity
        have hlim0 : Tendsto (fun N : ℕ => Real.sqrt (c0 / ((N : ℝ) + 1) ^ (2 * (s + p + 7 - 0) + 1)))
            atTop (𝓝 0) := by
          have h1 : Tendsto (fun N : ℕ => c0 / ((N : ℝ) + 1) ^ (2 * (s + p + 7 - 0) + 1)) atTop
              (𝓝 0) := by
            have : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ (2 * (s + p + 7 - 0) + 1)) atTop atTop :=
              (tendsto_pow_atTop (by omega)).comp
                (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
            exact this.const_div_atTop c0
          have := (Real.continuous_sqrt.tendsto 0).comp h1
          rw [Real.sqrt_zero] at this
          exact this
        refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hlim0
        have h1 := hb N
        have hsingle : wq 0 k * (cf (s + p + 7 + 1) (γ N (x 0)) b k - coef (U b) (x 0) k) ^ 2 ≤
            ∑ b, ∑ k ∈ ({k} : Finset (Fin d → ℤ)), wq 0 k *
              (cf (s + p + 7 + 1) (γ N (x 0)) b k - coef (U b) (x 0) k) ^ 2 := by
          rw [Finset.sum_comm, Finset.sum_singleton]
          exact Finset.single_le_sum (f := fun b => wq 0 k *
            (cf (s + p + 7 + 1) (γ N (x 0)) b k - coef (U b) (x 0) k) ^ 2)
            (fun _ _ => mul_nonneg (wq_nonneg _ _) (sq_nonneg _)) (Finset.mem_univ b)
        have hw0 : wq (d := d) 0 k = 1 := by simp [wq, wordsLE, muL_nil]
        rw [hw0, one_mul] at hsingle
        rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt (hsingle.trans h1)
      have h := tendsto_nhds_unique hlimU (hlimV (x 0) hx b k)
      rw [coef_sub (hUc b) (hV b).continuous, h, sub_self]
    have h0 := eq_zero_of_coef_eq_zero ((hUc b).sub (hV b).continuous)
      (fun j y => by
        show U b (y + sshift j) - V b (y + sshift j) = U b y - V b y
        rw [hUper b j y, hVp b j y]) (x 0) hcoefeq (Fin.tail x)
    rw [Fin.cons_self_tail] at h0
    have h0' : U b x - V b x = 0 := h0
    linarith
  refine ⟨U, P, D₂, hUc, hUper, hU0, hP,
    fun b t ht y => (hUt b t (hsub₁ ht) y).mono hsub₁,
    fun b k t ht => (hcoef b k t (hsub₁ ht)).mono hsub₁, hD₂d, hunique,
    fun N τ hτ hcfl hτst a₀ δ ha₀ hδ hdata => ?_⟩
  -- the step restrictions
  have hτs' : τ ≤ τs := hτst.trans (min_le_left _ _)
  have hτK : τ * (K₁ + K₂ + K₃ + 1) ≤ 1 := by
    have h1 : τ ≤ 1 / (K₁ + K₂ + K₃ + 1) := hτst.trans (min_le_right _ _)
    rwa [le_div_iff₀ (by positivity)] at h1
  have eK : τ * (K₁ + K₂ + K₃ + 1) = τ * K₁ + τ * K₂ + τ * K₃ + τ := by ring
  have pK₁ := mul_nonneg hτ.le hK₁0
  have pK₂ := mul_nonneg hτ.le hK₂0
  have pK₃ := mul_nonneg hτ.le hK₃0
  have hτK₁ : τ * K₁ ≤ 1 := by linarith
  have hτK₂ : τ * K₂ ≤ 1 := by linarith
  have hτK₃ : τ * K₃ ≤ 1 := by linarith
  -- the midpoint record and the Galerkin trajectory from the same finite datum
  obtain ⟨Ud, hUd0, hUd⟩ := hmid N τ hτ hcfl hτs' a₀ ha₀
  obtain ⟨γa, hγa0, hGa⟩ := hgal N a₀ ha₀
  have hGa' : GalCurve A F (s + p + 8) T R γa := galCurve_mono hGa hTT₃ hR₀R
  have hGN : GalCurve A F (s + p + 8) T R (γ N) := hGc N
  have hUdR : ∀ j : ℕ, (j : ℝ) * τ ≤ T → ‖Ud j‖ ≤ R := fun j hj =>
    (hUd j (hj.trans hTT₂)).1.trans hRmR
  have hUdrec : ∀ j : ℕ, ((j : ℝ) + 1) * τ ≤ T →
      Ud (j + 1) = Ud j + τ • GN A F (s + p + 8) (SpectralGalerkin.mid (Ud j) (Ud (j + 1))) :=
    fun j hj => ((hUd j (by linarith [show ((j : ℝ) + 1) * τ = (j : ℝ) * τ + τ by ring])).2
      (hj.trans hTT₂)).1
  -- the data error and the Galerkin stability
  have hγN0 : γ N 0 = P0 (s + p + 7 + 1) N U₀ := hG.init N
  have hδ0 : ‖hmS (s + 4) (s + p + 8) (a₀ - γ N 0)‖ ≤ δ := by
    rw [hγN0]
    have h1 := norm_hmS_sub_P0_sq (s + 4) (s + p + 8) a₀ U₀
    have h2 := hdata (KatoGalerkin.box N)
    rw [← h1] at h2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hδ two_ne_zero).1 h2
  have hst : ∀ t ∈ Icc 0 T, ‖hmS (s + 4) (s + p + 8) (γa t - γ N t)‖ ≤ E * δ := by
    intro t ht
    refine (hstab N T γa (γ N) hGa' hGN t ht).trans ?_
    rw [hγa0]
    exact mul_le_mul (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hKs0)) hδ0
      (norm_nonneg _) (Real.exp_pos _).le
  have hlow : ∀ ρ, ρ ≤ s + 4 → ∀ t ∈ Icc 0 T, ‖hmS ρ (s + p + 8) (γa t - γ N t)‖ ≤ E * δ :=
    fun ρ hρ t ht => (norm_hmS_mono hρ _).trans (hst t ht)
  set ν := 1 / ((N : ℝ) + 1) ^ p with hν
  have hν0 : 0 ≤ ν := by positivity
  have hδ0' : ‖hmS (s + 3) (s + p + 8) (Ud 0 - γa 0)‖ = 0 := by
    rw [hUd0, hγa0, sub_self, hmS_zero, norm_zero]
  have hδ0'' : ‖hmS (s + 1) (s + p + 8) (Ud 0 - γa 0)‖ = 0 := by
    rw [hUd0, hγa0, sub_self, hmS_zero, norm_zero]
  refine ⟨Ud, hUd0, fun j hj => ⟨hUdR j hj, fun hj1 => hUdrec j hj1⟩, fun j hj S => ?_,
    fun j hj θ hθ S => ?_⟩
  · -- the time rate
    have ht : (j : ℝ) * τ ∈ Icc 0 T := ⟨by positivity, hj⟩
    have k1 : ∑ b, ∑ k ∈ S, wq (s + 4) k * (cf (s + p + 8) (Ud j) b k -
        cf (s + p + 8) (γa (j * τ)) b k) ^ 2 ≤ (C₁ * τ ^ 2) ^ 2 := by
      refine (sum_cf_sub_le_hmS _ _ _ _ S).trans (sq_le_sq_of_le' (norm_nonneg _) ?_)
      have h := hC₁ N τ hτ hτK₁ γa Ud hGa' hUdR hUdrec j hj
      rw [hUd0, hγa0, sub_self, hmS_zero, norm_zero, zero_add] at h
      exact h
    have k2 : ∑ b, ∑ k ∈ S, wq (s + 4) k * (cf (s + p + 8) (γa (j * τ)) b k -
        cf (s + p + 8) (γ N (j * τ)) b k) ^ 2 ≤ (E * δ) ^ 2 :=
      (sum_cf_sub_le_hmS _ _ _ _ S).trans (sq_le_sq_of_le' (norm_nonneg _) (hst _ ht))
    have k3 : ∑ b, ∑ k ∈ S, wq (s + 4) k * (cf (s + p + 8) (γ N (j * τ)) b k -
        coef (U b) (j * τ) k) ^ 2 ≤ (Real.sqrt A₄ * ν) ^ 2 :=
      (hr0 (s + 4) (by omega) N _ (hsub₁ ht) S).trans (rate_le_sq hA₄0 (by omega) N)
    refine (sum2_sq_triangle3 S (wq (s + 4)) (fun k => wq_nonneg _ _)
      (fun b k => cf (s + p + 8) (Ud j) b k) (fun b k => cf (s + p + 8) (γa (j * τ)) b k)
      (fun b k => cf (s + p + 8) (γ N (j * τ)) b k) (fun b k => coef (U b) (j * τ) k)
      (by positivity) (by positivity) (by positivity) k1 k2 k3).trans
      (sq_le_sq_of_le' (by positivity) ?_)
    rw [mul_add, mul_add]
    linarith [mul_le_mul_of_nonneg_right hC1 (sq_nonneg τ), mul_le_mul_of_nonneg_right hEL1 hδ,
      mul_le_mul_of_nonneg_right hC4 hν0]
  · -- the Hermite readout
    obtain ⟨hθ0, hθ1⟩ := hθ
    have hθτ : θ * τ ≤ τ := mul_le_of_le_one_left hτ.le hθ1
    have ht : (j : ℝ) * τ + θ * τ ∈ Icc 0 T :=
      ⟨by positivity, by linarith [show ((j : ℝ) + 1) * τ = (j : ℝ) * τ + τ by ring]⟩
    obtain ⟨g1, g2, -⟩ := hC₂ N τ hτ hτK₂ γa Ud hGa' hUdR hUdrec j hj θ ⟨hθ0, hθ1⟩
    obtain ⟨-, -, g3⟩ := hC₃ N τ hτ hτK₃ γa Ud hGa' hUdR hUdrec j hj θ ⟨hθ0, hθ1⟩
    rw [hδ0', zero_add] at g1 g2
    rw [hδ0'', zero_div, zero_add] at g3
    set t := (j : ℝ) * τ + θ * τ with htdef
    refine ⟨?_, ?_, ?_⟩
    · have k2 : ∑ b, ∑ k ∈ S, wq (s + 2) k * (cf (s + p + 8) (γa t) b k -
          cf (s + p + 8) (γ N t) b k) ^ 2 ≤ (E * δ) ^ 2 :=
        (sum_cf_sub_le_hmS _ _ _ _ S).trans (sq_le_sq_of_le' (norm_nonneg _)
          (hlow (s + 2) (by omega) t ht))
      have k3 : ∑ b, ∑ k ∈ S, wq (s + 2) k * (cf (s + p + 8) (γ N t) b k -
          coef (U b) t k) ^ 2 ≤ (Real.sqrt A₂ * ν) ^ 2 :=
        (hr0 (s + 2) (by omega) N _ (hsub₁ ht) S).trans (rate_le_sq hA₂0 (by omega) N)
      refine (sum2_sq_triangle3 S (wq (s + 2)) (fun k => wq_nonneg _ _) _
        (fun b k => cf (s + p + 8) (γa t) b k) (fun b k => cf (s + p + 8) (γ N t) b k)
        (fun b k => coef (U b) t k) (by positivity) (by positivity) (by positivity)
        ((sum_cf_sub_le_hmS _ _ _ _ S).trans (sq_le_sq_of_le' (norm_nonneg _) g1)) k2 k3).trans
        (sq_le_sq_of_le' (by positivity) ?_)
      rw [mul_add, mul_add]
      linarith [mul_le_mul_of_nonneg_right hC2 (sq_nonneg τ), mul_le_mul_of_nonneg_right hEL1 hδ,
        mul_le_mul_of_nonneg_right hC5 hν0]
    · have k2 : ∑ b, ∑ k ∈ S, wq (s + 2) k * (cf (s + p + 8) (GN A F (s + p + 8) (γa t)) b k -
          cf (s + p + 8) (GN A F (s + p + 8) (γ N t)) b k) ^ 2 ≤ (E * L₂ * δ) ^ 2 := by
        refine (sum_cf_sub_le_hmS _ _ _ _ S).trans (sq_le_sq_of_le' (norm_nonneg _) ?_)
        refine (hL₂ (s + p + 8) N _ _ (hGa'.ball (by omega) t ht) (hGN.ball (by omega) t ht)).trans ?_
        have := hlow (s + 3) (by omega) t ht
        calc L₂ * ‖hmS (s + 2 + 1) (s + p + 8) (γa t - γ N t)‖ ≤ L₂ * (E * δ) :=
              mul_le_mul_of_nonneg_left this hL₂0
          _ = E * L₂ * δ := by ring
      have k3 : ∑ b, ∑ k ∈ S, wq (s + 2) k * (cf (s + p + 8) (GN A F (s + p + 8) (γ N t)) b k -
          coef (genP A F U P b) t k) ^ 2 ≤ (Real.sqrt (Cdt (s + 2)) * ν) ^ 2 := by
        simp only [cf_GN_ite]
        exact (hr1 (s + 2) (by omega) (by omega) N _ (hsub₁ ht) S).trans
          (rate_le_sq (hCdt _) (by omega) N)
      refine (sum2_sq_triangle3 S (wq (s + 2)) (fun k => wq_nonneg _ _) _
        (fun b k => cf (s + p + 8) (GN A F (s + p + 8) (γa t)) b k)
        (fun b k => cf (s + p + 8) (GN A F (s + p + 8) (γ N t)) b k)
        (fun b k => coef (genP A F U P b) t k) (by positivity) (by positivity) (by positivity)
        ((sum_cf_sub_le_hmS _ _ _ _ S).trans (sq_le_sq_of_le' (norm_nonneg _) g2)) k2 k3).trans
        (sq_le_sq_of_le' (by positivity) ?_)
      rw [mul_add, mul_add]
      linarith [mul_le_mul_of_nonneg_right hC2 (sq_nonneg τ), mul_le_mul_of_nonneg_right hEL2 hδ,
        mul_le_mul_of_nonneg_right hC6 hν0]
    · have k2 : ∑ b, ∑ k ∈ S, wq s k *
          (cf (s + p + 8) (DGN A F (s + p + 8) (γa t) (GN A F (s + p + 8) (γa t))) b k -
          cf (s + p + 8) (DGN A F (s + p + 8) (γ N t) (GN A F (s + p + 8) (γ N t))) b k) ^ 2 ≤
          (E * (LD * L₁ + LL * MA) * δ) ^ 2 := by
        refine (sum_cf_sub_le_hmS _ _ _ _ S).trans (sq_le_sq_of_le' (norm_nonneg _) ?_)
        have e : DGN A F (s + p + 8) (γa t) (GN A F (s + p + 8) (γa t)) -
            DGN A F (s + p + 8) (γ N t) (GN A F (s + p + 8) (γ N t)) =
            DGN A F (s + p + 8) (γa t) (GN A F (s + p + 8) (γa t) - GN A F (s + p + 8) (γ N t)) +
              (DGN A F (s + p + 8) (γa t) (GN A F (s + p + 8) (γ N t)) -
                DGN A F (s + p + 8) (γ N t) (GN A F (s + p + 8) (γ N t))) := by
          rw [DGN_sub_right]; abel
        rw [e, hmS_add]
        have b1 := hGa'.ball (ρ := s + 1) (by omega) t ht
        have b2 := hGN.ball (ρ := s + 1) (by omega) t ht
        have b3 := hGa'.ball (ρ := s + 2) (by omega) t ht
        have b4 := hGN.ball (ρ := s + 2) (by omega) t ht
        have f1 := (hLD (s + p + 8) N (γa t) _ b1).trans (mul_le_mul_of_nonneg_left
          ((hL₁ (s + p + 8) N _ _ b3 b4).trans (mul_le_mul_of_nonneg_left
            (hlow (s + 2) (by omega) t ht) hL₁0)) hLD0)
        have f2 := (hLL (s + p + 8) N (γa t) (γ N t) (GN A F (s + p + 8) (γ N t)) b1 b2).trans
          (mul_le_mul (mul_le_mul_of_nonneg_left (hlow (s + 1) (by omega) t ht) hLL0)
            ((hMA N T (γ N) hGN).1 t ht) (norm_nonneg _) (by positivity))
        calc _ ≤ _ := norm_add_le _ _
          _ ≤ LD * (L₁ * (E * δ)) + LL * (E * δ) * MA := add_le_add f1 f2
          _ = E * (LD * L₁ + LL * MA) * δ := by ring
      have k3 : ∑ b, ∑ k ∈ S, wq s k *
          (cf (s + p + 8) (DGN A F (s + p + 8) (γ N t) (GN A F (s + p + 8) (γ N t))) b k -
          D₂ b k t) ^ 2 ≤ (Real.sqrt B₄ * ν) ^ 2 := by
        refine (hD₂r N t ht S).trans ?_
        have hsq : (Real.sqrt B₄ * ν) ^ 2 = C₄ * (A₀ + Cdt (s + 1) + 1) *
            (1 / ((N : ℝ) + 1) ^ (2 * p)) := by
          rw [mul_pow, Real.sq_sqrt hB₄0, hν, div_pow, one_pow, ← pow_mul, mul_comm p 2, hB₄]
        rw [hsq]
        have r1 := rate_le hA₀0 (j := 2 * p) (k := 2 * (s + p + 7 - (s + 1)) + 1) (by omega) N
        have r2 := rate_le (hCdt (s + 1)) (j := 2 * p)
          (k := 2 * (s + p + 7 - (s + 1 + 1)) + 1) (by omega) N
        have r3 := one_div_two_pi_pow_le_rate (j := s + p + 8 - 2 - s) (p := p) (by omega) N
        have e2 : A₀ / ((N : ℝ) + 1) ^ (2 * p) = A₀ * (1 / ((N : ℝ) + 1) ^ (2 * p)) := by ring
        have e3 : Cdt (s + 1) / ((N : ℝ) + 1) ^ (2 * p) =
            Cdt (s + 1) * (1 / ((N : ℝ) + 1) ^ (2 * p)) := by ring
        rw [e2] at r1; rw [e3] at r2
        calc C₄ * (A₀ / ((N : ℝ) + 1) ^ (2 * (s + p + 7 - (s + 1)) + 1) +
              Cdt (s + 1) / ((N : ℝ) + 1) ^ (2 * (s + p + 7 - (s + 1 + 1)) + 1) +
              1 / ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ (s + p + 8 - 2 - s))
            ≤ C₄ * (A₀ * (1 / ((N : ℝ) + 1) ^ (2 * p)) +
              Cdt (s + 1) * (1 / ((N : ℝ) + 1) ^ (2 * p)) + 1 / ((N : ℝ) + 1) ^ (2 * p)) :=
              mul_le_mul_of_nonneg_left (by linarith) hC₄0
          _ = C₄ * (A₀ + Cdt (s + 1) + 1) * (1 / ((N : ℝ) + 1) ^ (2 * p)) := by ring
      refine (sum2_sq_triangle3 S (wq s) (fun k => wq_nonneg _ _) _
        (fun b k => cf (s + p + 8) (DGN A F (s + p + 8) (γa t) (GN A F (s + p + 8) (γa t))) b k)
        (fun b k => cf (s + p + 8) (DGN A F (s + p + 8) (γ N t) (GN A F (s + p + 8) (γ N t))) b k)
        (fun b k => D₂ b k t) (by positivity) (by positivity) (by positivity)
        ((sum_cf_sub_le_hmS _ _ _ _ S).trans (sq_le_sq_of_le' (norm_nonneg _) g3)) k2 k3).trans
        (sq_le_sq_of_le' (by positivity) ?_)
      rw [mul_add, mul_add]
      linarith [mul_le_mul_of_nonneg_right hC3 hτ.le, mul_le_mul_of_nonneg_right hEL3 hδ,
        mul_le_mul_of_nonneg_right hC7 hν0]


end RenewalGeometry.GenRatesId
