/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedDynamicsClosed

/-!
# `cor:generated-nonempty`: the controlled finite class

Einstein–Standard-Model action-closure manuscript, `cor:generated-nonempty`
(`eq:generated-nonempty`, `Σ = 𝕋³`, decoupled spinors): for the constrained data class of the
generated dynamics, the fully finite spectral–midpoint evolution started from the **finite**
initial data `U_{0,N} = P_N U₀` (Fourier projection; no spacetime solution is sampled) exists on
a common slab and its cubic-Hermite records satisfy, on every cell and slice,
`‖Riem(g_{N,τ}) - Riem(g)‖_{H^s} + ‖R_B(z_{N,τ})‖_{H^s} ≤ C(N^{-p} + τ)`, the Dirac residual
`O(N^{-p} + τ²)` in `H^{s+1}`, and the stationarity `|D S^{cmp}[V]| ≤ C(N^{-p} + τ)‖V‖_{0,τ}`;
the dyadic rate budget `Σ_n (N_n^{-p} + τ_n)` along `N_n = 2^n` under the CFL condition is
summable.

* `P0_data_error` — `‖P_N U₀ - U₀‖²_{H^r} ≤ ‖U₀‖²_{H^{r+j}} / (2π(N+1))^{2j}` in Fourier form;
* **`GenReadout.generated_nonempty`**;
* a non-vacuity `example` (vanishing-coupling data, flat datum): the controlled finite class is
  nonempty.
-/

open Set Filter Topology
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenReadout

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy KatoGalerkin FrameCurvature
  HarmonicDefect ActualJetWriter ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge
  ActualJetBridge ActualJetState ActualJetCompleteForcing ActualJetRecon ActualJetKato GenHermite
  GenResMaps GenPhysIdFinal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

/-! ### The data error of the Fourier projection -/

section DataError

/-- **The data error of the Fourier projection** `P_N U₀` in Fourier form:
`Σ_b Σ_{k ∈ S₀} w_r(k)(c_k(P_N U₀) - c_k(U₀))² ≤ ‖U₀‖²_{H^{r+j}} / ((2π(N+1))²)^j`. -/
theorem P0_data_error {d n : ℕ} (q r j N : ℕ) (hrj : r + j = q) {U₀ : Fin n → ST d → ℝ}
    (hU : ∀ b, ContDiff ℝ ∞ (U₀ b)) (hUp : ∀ b, IsSPeriodic (U₀ b))
    (S₀ : Finset (Fin d → ℤ)) :
    ∑ b, ∑ k ∈ S₀, wq r k * (cf q (P0 (d := d) q N U₀) b k - coef (U₀ b) 0 k) ^ 2 ≤
      energyQ q U₀ 0 / ((2 * Real.pi * ((N : ℝ) + 1)) ^ 2) ^ j := by
  set X := ((2 * Real.pi * ((N : ℝ) + 1)) ^ 2) ^ j with hXdef
  have hX : 0 < X := by positivity
  rw [le_div_iff₀ hX, energyQ, Finset.sum_mul]
  refine Finset.sum_le_sum fun b _ => ?_
  refine le_trans ?_ (bessel_Hq q S₀ (hU b) (hUp b) 0)
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [cf_P0]
  split_ifs with hk
  · rw [sub_self]
    have := wq_nonneg q k
    have := sq_nonneg (coef (U₀ b) 0 k)
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul]
    positivity
  · have h := wq_tail hk r j
    rw [hrj] at h
    calc wq r k * (0 - coef (U₀ b) 0 k) ^ 2 * X = (wq r k * X) * coef (U₀ b) 0 k ^ 2 := by ring
      _ ≤ wq q k * coef (U₀ b) 0 k ^ 2 := mul_le_mul_of_nonneg_right h (sq_nonneg _)

theorem inv_X_le {N p j : ℕ} (hpj : p ≤ j) :
    1 / ((2 * Real.pi * ((N : ℝ) + 1)) ^ 2) ^ j ≤ (1 / ((N : ℝ) + 1) ^ p) ^ 2 := by
  have hN : (1 : ℝ) ≤ (N : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  have h1 : ((N : ℝ) + 1) ^ 2 ≤ (2 * Real.pi * ((N : ℝ) + 1)) ^ 2 := by
    have : (N : ℝ) + 1 ≤ 2 * Real.pi * ((N : ℝ) + 1) := by
      have := Real.pi_gt_three; nlinarith
    exact pow_le_pow_left₀ (by positivity) this 2
  have h2 : (((N : ℝ) + 1) ^ p) ^ 2 ≤ ((2 * Real.pi * ((N : ℝ) + 1)) ^ 2) ^ j := by
    calc (((N : ℝ) + 1) ^ p) ^ 2 = (((N : ℝ) + 1) ^ 2) ^ p := by
          rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ (((N : ℝ) + 1) ^ 2) ^ j := pow_le_pow_right₀ (by nlinarith) hpj
      _ ≤ ((2 * Real.pi * ((N : ℝ) + 1)) ^ 2) ^ j := pow_le_pow_left₀ (by positivity) h1 j
  rw [div_pow, one_pow]
  exact one_div_le_one_div_of_le (by positivity) h2

end DataError

/-! ### The summable dyadic budget -/

theorem summable_dyadic {p : ℕ} (hp : 1 ≤ p) {cstar : ℝ} (τd : ℕ → ℝ)
    (hτd : ∀ n, 0 ≤ τd n ∧ τd n * ((2 : ℝ) ^ n + 1) ≤ cstar) :
    Summable (fun n : ℕ => 1 / ((2 : ℝ) ^ n + 1) ^ p + τd n) := by
  have hc : 0 ≤ cstar := by
    have := hτd 0; nlinarith [this.1, this.2]
  have hg : Summable (fun n : ℕ => (1 + cstar) * (1 / 2 : ℝ) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  refine Summable.of_nonneg_of_le (fun n => add_nonneg (by positivity) (hτd n).1) (fun n => ?_) hg
  have h2 : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ n + 1 := by linarith
  have hpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have e1 : 1 / ((2 : ℝ) ^ n + 1) ^ p ≤ (1 / 2 : ℝ) ^ n := by
    have h3 : (2 : ℝ) ^ n ≤ ((2 : ℝ) ^ n + 1) ^ p := by
      calc (2 : ℝ) ^ n ≤ (2 : ℝ) ^ n + 1 := h2
        _ = ((2 : ℝ) ^ n + 1) ^ 1 := (pow_one _).symm
        _ ≤ ((2 : ℝ) ^ n + 1) ^ p := pow_le_pow_right₀ (by linarith) hp
    rw [one_div_pow, one_div]
    exact one_div_le_one_div_of_le hpos h3 |>.trans_eq' (by rw [one_div])
  have e2 : τd n ≤ cstar * (1 / 2 : ℝ) ^ n := by
    have h4 : τd n * (2 : ℝ) ^ n ≤ cstar := by
      have := (hτd n).2; nlinarith [(hτd n).1]
    rw [one_div_pow, ← div_eq_mul_one_div, le_div_iff₀ hpos]
    exact h4
  nlinarith

/-! ### The corollary -/

section Nonempty

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {SM : SMData (MatLie m) V S S'}
variable {bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ} {bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ}
  {bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ} {bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ}

set_option maxHeartbeats 4000000 in
/-- **`cor:generated-nonempty` on the actual-jet system** (`Σ = 𝕋³`, variational theory data,
decoupled spinors, `κ ≠ 0`).  For every constrained smooth periodic datum `U₀` of the generated
dynamics there are a physical smooth tuple `z` on `[0, t₁]` and, for all coordinates `e_B`, `e_D`
of the residual spaces, constants `C`, `C_st`, `η > 0` such that for every cutoff `N` and step `τ`
with `τ(N+1) ≤ c_*`, `τ ≤ τ_*`, `N^{-p} + τ ≤ η`, the implicit-midpoint record started from the
finite data `U_{0,N} = P_N U₀` exists on `[0, T]`, its cubic-Hermite reconstruction is
`C(N^{-p} + τ²)`-close in `H^{s+2}` (Fourier form) to the coordinate state of the exact solution on
`[0, t₁]` and has, on every cell `[jτ, (j+1)τ] ⊆ [0, t₁]`, its metric in the chart and on every
slice
`Σ_c ‖Riem(g_{N,τ}) - Riem(g)‖²_{H^s} ≤ (C(N^{-p} + τ))²`,
`Σ_k ‖(e_B R_B(z_{N,τ}))_k‖²_{H^s} ≤ (C(N^{-p} + τ))²`,
`Σ_k ‖(e_D R_D(z_{N,τ}))_k‖²_{H^{s+1}} ≤ (C(N^{-p} + τ²))²`, and the stationarity
`|D S^{cmp}[V]| ≤ C_st(N^{-p} + τ)‖V‖_{0,τ}` for every collar-fixed nodal variation on `[0, Jτ]`,
`Jτ ≤ t₁`; along `N_n = 2^n` with CFL steps the rate budgets are summable. -/
theorem generated_nonempty (hS : SMSmooth SM) (hU : UnitaryForms SM bG bV bS bS')
    (hVS : GenStress.VariationalStress SM) (hκ0 : SM.κ ≠ 0) {s p : ℕ} (hs : 3 ≤ s)
    (hp : 1 ≤ p) :
    ∃ κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ),
      (∀ v w, ipP bG bV bS bS' (κ.symm v) (κ.symm w) = ∑ i, v i * w i) ∧
      ∀ K₀ K : Set (Fin (dimS m V S S') → ℝ), IsCompact K → (∀ v ∈ K, MetChart (κ.symm v).1) →
      ∀ δK : ℝ, 0 < δK → Metric.cthickening δK K₀ ⊆ K →
      ∃ (A : Fin 3 → Fin (dimS m V S S') → Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ) (F : Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ),
        (∀ i a b, ContDiff ℝ ∞ (A i a b)) ∧ (∀ i a b v, A i a b v = A i b a v) ∧
        (∀ a, ContDiff ℝ ∞ (F a)) ∧
        (∀ v ∈ K, ∀ j a (w : Fin (dimS m V S S') → ℝ), ∑ b, A j a b v * w b =
          κ (toS (princ (frameU (ginvOf (κ.symm v).1.1)) SM.D.Fr SM.Db.Fr j
            (ofP (κ.symm w)))) a) ∧
        (∀ v ∈ K, ∀ a, F a v = κ (toS (Fsys SM (ofP (κ.symm v)))) a) ∧
        ∀ R₀ : ℝ, 0 ≤ R₀ → ∃ T > 0, ∃ R ≥ 0, ∃ cstar > 0, ∃ τstar > 0,
        (∀ τd : ℕ → ℝ, (∀ n, 0 ≤ τd n ∧ τd n * ((2 : ℝ) ^ n + 1) ≤ cstar) →
          Summable (fun n : ℕ => 1 / ((2 : ℝ) ^ n + 1) ^ p + τd n)) ∧
        ∀ U₀ : Fin (dimS m V S S') → ST 3 → ℝ,
          GenPhysIdClosed.ConstrainedData SM κ U₀ → (∀ b, ContDiff ℝ ∞ (U₀ b)) →
          (∀ b, IsSPeriodic (U₀ b)) → energyQ (s + p + 8) U₀ 0 ≤ R₀ ^ 2 →
          (∀ y, (fun c => U₀ c (Fin.cons 0 y)) ∈ K₀) →
          ∃ (z : Tuple m V S S') (t₁ : ℝ), 0 < t₁ ∧ t₁ ≤ T ∧
            (∀ x ∈ slab (d := 3) 0 t₁, bosF SM z x = 0 ∧ dirF SM z x = 0 ∧ CF z x = 0) ∧
            (∀ b y, stC κ SM z b (Fin.cons 0 y) = U₀ b (Fin.cons 0 y)) ∧
            ∀ {nB : ℕ} (eB : BosP m V →L[ℝ] (Fin nB → ℝ)) {nD : ℕ}
              (eD : S × S' →L[ℝ] (Fin nD → ℝ)),
            ∃ C ≥ 0, ∃ Cst ≥ 0, ∃ η > 0,
              ∀ (N : ℕ) (τ : ℝ), 0 < τ → τ * ((N : ℝ) + 1) ≤ cstar → τ ≤ τstar →
              1 / ((N : ℝ) + 1) ^ p + τ ≤ η →
              ∃ Ud : ℕ → GS 3 (dimS m V S S') N, Ud 0 = P0 (s + p + 8) N U₀ ∧
                (∀ j : ℕ, (j : ℝ) * τ ≤ T → ‖Ud j‖ ≤ R ∧ (((j : ℝ) + 1) * τ ≤ T →
                  Ud (j + 1) = Ud j + τ • GN A F (s + p + 8)
                    (SpectralGalerkin.mid (Ud j) (Ud (j + 1))))) ∧
                (∀ j : ℕ, ((j : ℝ) + 1) * τ ≤ t₁ → ∀ θ ∈ Icc (0 : ℝ) 1,
                  ∀ S₀ : Finset (Fin 3 → ℤ), ∑ b, ∑ k ∈ S₀, wq (s + 2) k *
                    (cf (s + p + 8) (SpectralGalerkin.hermite τ (Ud j) (Ud (j + 1))
                      (GN A F (s + p + 8) (Ud j)) (GN A F (s + p + 8) (Ud (j + 1))) θ) b k -
                      coef (stC κ SM z b) (j * τ + θ * τ) k) ^ 2 ≤
                    (C * (1 / ((N : ℝ) + 1) ^ p + τ ^ 2)) ^ 2) ∧
                (∀ j : ℕ, ((j : ℝ) + 1) * τ ≤ t₁ →
                  (∀ y ∈ openSlab (j * τ) ((j + 1) * τ), HeadChart κ (fun c =>
                    recW τ (j * τ) (Ud j) (Ud (j + 1)) (GN A F (s + p + 8) (Ud j))
                      (GN A F (s + p + 8) (Ud (j + 1))) (s + p + 8) c y)) ∧
                  ∀ t ∈ Ioo ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
                    ∑ c : Fin 4 × Fin 4 × Fin 4 × Fin 4, Q s (fun x =>
                      riemR (hjF κ (recW τ (j * τ) (Ud j) (Ud (j + 1))
                        (GN A F (s + p + 8) (Ud j)) (GN A F (s + p + 8) (Ud (j + 1)))
                        (s + p + 8)) x) c - riemR (hj2 z x) c) t ≤
                      (C * (1 / ((N : ℝ) + 1) ^ p + τ)) ^ 2 ∧
                    ∑ k, Q s (fun x => eB (bosR SM (hjF κ (recW τ (j * τ) (Ud j) (Ud (j + 1))
                      (GN A F (s + p + 8) (Ud j)) (GN A F (s + p + 8) (Ud (j + 1)))
                      (s + p + 8)) x)) k) t ≤ (C * (1 / ((N : ℝ) + 1) ^ p + τ)) ^ 2 ∧
                    ∑ k, Q (s + 1) (fun x => eD (GenResMaps.dirR SM (hjF κ (recW τ (j * τ)
                      (Ud j) (Ud (j + 1)) (GN A F (s + p + 8) (Ud j))
                      (GN A F (s + p + 8) (Ud (j + 1))) (s + p + 8)) x)) k) t ≤
                      (C * (1 / ((N : ℝ) + 1) ^ p + τ ^ 2)) ^ 2) ∧
                ∀ J : ℕ, (J : ℝ) * τ ≤ t₁ → ∀ v w : ℕ → GS 3 (dimS m V S S') N,
                  v 0 = 0 → w 0 = 0 → v J = 0 → w J = 0 →
                  ∃ D : ℝ, HasDerivAt (fun ε : ℝ => GenStat.Scmp κ SM (s + p + 8) τ J
                      (fun j => Ud j + ε • v j) (fun j => GN A F (s + p + 8) (Ud j) + ε • w j)) D 0 ∧
                    |D| ≤ Cst * (1 / ((N : ℝ) + 1) ^ p + τ) *
                      GenStat.vnorm (s + p + 8) τ J v w := by
  obtain ⟨κ, hκ, h⟩ := generated_dynamics_closed (bG := bG) (bV := bV) (bS := bS) (bS' := bS')
    hS hU hVS hκ0 hs hp
  refine ⟨κ, hκ, fun K₀ K hK hKc δK hδK hKδ => ?_⟩
  obtain ⟨A, F, hA, hsym, hF, hAK, hFK, h2⟩ := h K₀ K hK hKc δK hδK hKδ
  refine ⟨A, F, hA, hsym, hF, hAK, hFK, fun R₀ hR₀ => ?_⟩
  obtain ⟨T, hT, R, hR, cstar, hc, τs, hτs, h3⟩ := h2 R₀ hR₀
  refine ⟨T, hT, R, hR, cstar, hc, τs, hτs, fun τd hτd => summable_dyadic hp τd hτd,
    fun U₀ hCD hU₀ hUp hE hK₀ => ?_⟩
  obtain ⟨z, t₁, ht₁, ht₁T, hphys, hinit, h4⟩ := h3 U₀ hCD hU₀ hUp hE hK₀
  refine ⟨z, t₁, ht₁, ht₁T, hphys, hinit, fun {nB} eB {nD} eD => ?_⟩
  obtain ⟨C₁, hC₁0, Cz, hCz, Cst, hCst, η, hη, K2, -, -, h5⟩ := h4 eB eD
  set C : ℝ := max C₁ Cz with hCdef
  have hC0 : 0 ≤ C := le_max_of_le_left hC₁0
  have hR1 : 0 < R₀ + 1 := by linarith
  refine ⟨C * (R₀ + 1), by positivity, Cst * (R₀ + 1), by positivity, η / (R₀ + 1),
    div_pos hη hR1, fun N τ hτ hcfl hττ hsmall => ?_⟩
  set ν : ℝ := 1 / ((N : ℝ) + 1) ^ p with hν
  have hν0 : 0 ≤ ν := by positivity
  -- the finite data
  have hP0 : ‖P0 (d := 3) (s + p + 8) N U₀‖ ≤ R₀ := by
    have h1 := norm_P0_sq_le (d := 3) (s + p + 8) N hU₀ hUp
    have h2 : ‖P0 (d := 3) (s + p + 8) N U₀‖ ^ 2 ≤ R₀ ^ 2 := h1.trans hE
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hR₀ (by norm_num)).1 h2
  have hdata : ∀ S₀ : Finset (Fin 3 → ℤ), ∑ b, ∑ k ∈ S₀, wq (s + 4) k *
      (cf (s + p + 8) (P0 (d := 3) (s + p + 8) N U₀) b k - coef (U₀ b) 0 k) ^ 2 ≤
        (R₀ * ν) ^ 2 := by
    intro S₀
    refine (P0_data_error (s + p + 8) (s + 4) (p + 4) N (by omega) hU₀ hUp S₀).trans ?_
    have hX := inv_X_le (N := N) (p := p) (j := p + 4) (by omega)
    have hE0 : 0 ≤ energyQ (s + p + 8) U₀ 0 :=
      Finset.sum_nonneg fun b _ => Q_nonneg _ _ _
    calc energyQ (s + p + 8) U₀ 0 / ((2 * Real.pi * ((N : ℝ) + 1)) ^ 2) ^ (p + 4)
        = energyQ (s + p + 8) U₀ 0 * (1 / ((2 * Real.pi * ((N : ℝ) + 1)) ^ 2) ^ (p + 4)) :=
          div_eq_mul_one_div _ _
      _ ≤ R₀ ^ 2 * ν ^ 2 := mul_le_mul hE hX (by positivity) (sq_nonneg _)
      _ = (R₀ * ν) ^ 2 := by ring
  have hsm : τ + R₀ * ν + ν ≤ η := by
    have h1 : ν + τ ≤ η / (R₀ + 1) := hsmall
    have h2 : (ν + τ) * (R₀ + 1) ≤ η := by rwa [le_div_iff₀ hR1] at h1
    nlinarith
  obtain ⟨Ud, hUd0, hrec, hstate, hcells, hstat⟩ := h5 N τ hτ hcfl hττ (P0 (s + p + 8) N U₀)
    (R₀ * ν) hP0 (by positivity) hdata hsm
  have hb1 : τ + R₀ * ν + 1 / ((N : ℝ) + 1) ^ p ≤ (R₀ + 1) * (ν + τ) := by
    rw [← hν]; nlinarith
  have hb2 : τ ^ 2 + R₀ * ν + 1 / ((N : ℝ) + 1) ^ p ≤ (R₀ + 1) * (ν + τ ^ 2) := by
    rw [← hν]; nlinarith [sq_nonneg τ]
  have hsq' : ∀ C' a b : ℝ, 0 ≤ C' → C' ≤ C → 0 ≤ a → a ≤ (R₀ + 1) * b →
      (C' * a) ^ 2 ≤ (C * (R₀ + 1) * b) ^ 2 := fun C' a b hC' hCC ha hab =>
    pow_le_pow_left₀ (by positivity) (by nlinarith) 2
  have hsq : ∀ a b : ℝ, 0 ≤ a → a ≤ (R₀ + 1) * b → (C₁ * a) ^ 2 ≤ (C * (R₀ + 1) * b) ^ 2 :=
    fun a b ha hab => hsq' C₁ a b hC₁0 (le_max_left _ _) ha hab
  refine ⟨Ud, hUd0, hrec, fun j hj θ hθ S₀ => ?_, fun j hj => ?_,
    fun J hJ v w hv0 hw0 hvJ hwJ => ?_⟩
  · exact (hstate j hj θ hθ S₀).trans
      (hsq' Cz _ _ hCz (le_max_right _ _) (by positivity) hb2)
  · obtain ⟨-, hch, hb⟩ := hcells j hj
    refine ⟨hch, fun t ht => ?_⟩
    obtain ⟨e1, e2, e3⟩ := hb t ht
    exact ⟨e1.trans (hsq _ _ (by positivity) hb1), e2.trans (hsq _ _ (by positivity) hb1),
      e3.trans (hsq _ _ (by positivity) hb2)⟩
  · obtain ⟨D, hD, hDb⟩ := hstat J hJ v w hv0 hw0 hvJ hwJ
    refine ⟨D, hD, hDb.trans ?_⟩
    have hvn : 0 ≤ GenStat.vnorm (s + p + 8) τ J v w := Real.sqrt_nonneg _
    have : Cst * (τ + R₀ * ν + 1 / ((N : ℝ) + 1) ^ p) ≤ Cst * (R₀ + 1) * (ν + τ) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hb1 hCst
    exact mul_le_mul_of_nonneg_right this hvn

end Nonempty

/-! ### Non-vacuity -/

section NonVacuity

open CoupledBootstrap.FlatVacuum in
set_option maxHeartbeats 4000000 in
/-- **Non-vacuity of the controlled finite class**: for the vanishing-coupling data `trivSMM`
(variational, `κ = 1`) and the flat-vacuum datum, there are a cutoff `N`, a step `0 < τ ≤ t₁`
and the generated record `U^j` started from `P_N U₀` whose Hermite reconstruction satisfies the
Riemann readout bound of `eq:generated-nonempty` on every cell of `[0, t₁]`. -/
example : ∃ (κ : StateP 1 (MatLie 1) PUnit.{1} PUnit.{1} ≃ₗ[ℝ]
      (Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ℝ))
    (A : Fin 3 → Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) →
      Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) →
        (Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ℝ) → ℝ)
    (F : Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) →
      (Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ℝ) → ℝ)
    (z : Tuple 1 (MatLie 1) PUnit.{1} PUnit.{1}) (t₁ C : ℝ) (N : ℕ) (τ : ℝ)
    (Ud : ℕ → GS 3 (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) N),
    0 < τ ∧ τ ≤ t₁ ∧
      (∀ x ∈ slab (d := 3) 0 t₁, bosF trivSMM z x = 0 ∧ dirF trivSMM z x = 0 ∧ CF z x = 0) ∧
      Ud 0 = P0 12 N (GenPhysId.stU κ trivSMM flat) ∧
      ∀ j : ℕ, ((j : ℝ) + 1) * τ ≤ t₁ → ∀ t ∈ Ioo ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
        ∑ c : Fin 4 × Fin 4 × Fin 4 × Fin 4, Q 3 (fun x =>
          riemR (hjF κ (recW τ (j * τ) (Ud j) (Ud (j + 1)) (GN A F 12 (Ud j))
            (GN A F 12 (Ud (j + 1))) 12) x) c - riemR (hj2 z x) c) t ≤
          (C * (1 / ((N : ℝ) + 1) ^ 1 + τ)) ^ 2 := by
  have hκ1 : trivSMM.κ ≠ 0 := by simp [trivSMM]
  obtain ⟨κ, -, h⟩ := generated_nonempty trivSMM_smooth unitaryForms_triv
    GenStress.trivSMM_variationalStress hκ1 (s := 3) (p := 1) (by norm_num) le_rfl
  have hκc : Continuous κ.symm := (contDiff_linearEquiv κ.symm.toLinearMap).continuous
  have hO : IsOpen (κ.symm ⁻¹' chartSet (m := 1) (V := MatLie 1) (S := PUnit.{1})
      (S' := PUnit.{1})) := isOpen_chartSet.preimage hκc
  have hmem : κ minkState ∈ κ.symm ⁻¹' chartSet (m := 1) (V := MatLie 1) (S := PUnit.{1})
      (S' := PUnit.{1}) := by
    show MetChart (κ.symm (κ minkState)).1
    rw [LinearEquiv.symm_apply_apply]
    exact metChart_mink
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO _ hmem
  have hK : IsCompact (Metric.closedBall (κ minkState) (r / 2)) := isCompact_closedBall _ _
  have hKc : ∀ v ∈ Metric.closedBall (κ minkState) (r / 2), MetChart (κ.symm v).1 := fun v hv =>
    hball (Metric.closedBall_subset_ball (half_lt_self hr) hv)
  have hKδ : Metric.cthickening (r / 2) ({κ minkState} : Set _) ⊆
      Metric.closedBall (κ minkState) (r / 2) :=
    (Metric.cthickening_singleton _ (by positivity)).le
  obtain ⟨A, F, -, -, -, -, -, h2⟩ := h {κ minkState} _ hK hKc (r / 2) (by positivity) hKδ
  obtain ⟨T, -, R, -, cstar, hc, τs, hτs, -, h3⟩ :=
    h2 (Real.sqrt |energyQ 12 (GenPhysId.stU κ trivSMM flat) 0|) (Real.sqrt_nonneg _)
  obtain ⟨z, t₁, ht₁, -, hphys, -, h4⟩ := h3 (GenPhysId.stU κ trivSMM flat)
    ⟨flat, fun _ _ => rfl, GenPhysIdClosed.flat_sliceConstrained⟩
    (GenPhysId.contDiff_stU κ trivSMM flat) (GenPhysId.isSPeriodic_stU κ trivSMM flat)
    (by rw [Real.sq_sqrt (abs_nonneg _)]; exact le_abs_self _)
    (fun y => by
      show κ (stateF trivSMM flat (Fin.cons 0 y)) ∈ ({κ minkState} : Set _)
      rw [stateF_flat]; exact Set.mem_singleton _)
  obtain ⟨C, -, Cst, -, η, hη, h5⟩ :=
    h4 (0 : BosP 1 (MatLie 1) →L[ℝ] (Fin 0 → ℝ)) (0 : PUnit.{1} × PUnit.{1} →L[ℝ] (Fin 0 → ℝ))
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / η)
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hν : 1 / ((N : ℝ) + 1) ^ 1 ≤ η / 2 := by
    rw [pow_one, div_le_div_iff₀ hN1 (by norm_num)]
    have := (div_lt_iff₀ hη).1 hN
    nlinarith
  set τ : ℝ := min (min τs (cstar / ((N : ℝ) + 1))) (min (η / 2) t₁) with hτdef
  have hτ : 0 < τ := lt_min (lt_min hτs (div_pos hc hN1)) (lt_min (by positivity) ht₁)
  have hτ1 : τ ≤ τs := (min_le_left _ _).trans (min_le_left _ _)
  have hτ2 : τ ≤ cstar / ((N : ℝ) + 1) := (min_le_left _ _).trans (min_le_right _ _)
  have hτ3 : τ ≤ η / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hτ4 : τ ≤ t₁ := (min_le_right _ _).trans (min_le_right _ _)
  have hcfl : τ * ((N : ℝ) + 1) ≤ cstar := by
    rwa [le_div_iff₀ hN1] at hτ2
  obtain ⟨Ud, hUd0, -, -, hcells, -⟩ := h5 N τ hτ hcfl hτ1 (by linarith)
  exact ⟨κ, A, F, z, t₁, C, N, τ, Ud, hτ, hτ4, hphys, hUd0,
    fun j hj t ht => ((hcells j hj).2 t ht).1⟩

end NonVacuity

end RenewalGeometry.GenReadout
