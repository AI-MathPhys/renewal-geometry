/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedDynamicsNorms
import RenewalGeometry.Continuum.GeneratedDynamicsExtended

/-!
# `thm:generated-dynamics` and `cor:generated-nonempty` in the manuscript's norms

Einstein–Standard-Model action-closure manuscript, `thm:generated-dynamics`
(`eq:generated-initial-rate`, `eq:generated-first`, `eq:generated-bosonic`, `eq:generated-Dirac`,
`eq:generated-stationarity`) and `cor:generated-nonempty` (`eq:generated-nonempty`), `Σ = 𝕋³`.

The piecewise Hermite record `z_{N,τ}` is read, at every time `t ≥ 0`, on its cell
`j = cellIdx τ t` (`GenRecNodes.recF`, the cubic Hermite reconstruction from the nodal values
`U^j` and slopes `G_N(U^j)`).  The slice quantities of the manuscript are then functions of `t`:

* `stErr` — `‖z_{N,τ}(t) - z(t)‖_{H^r}` (coordinate state of the record minus that of the exact
  solution), `stErrD` — the same for `∂_t`;
* `riemErr` — `‖Riem(g_{N,τ})(t) - Riem(g)(t)‖_{H^r}`, `bosRes` — `‖R_B(z_{N,τ})(t)‖_{H^r}`,
  `dirRes` — `‖R_D(z_{N,τ})(t)‖_{H^r}` (in fixed coordinates `e_B`, `e_D` of the residual spaces).

**`generated_dynamics_norms`** bounds `sup_{[0,Jτ]}` (`C_t`) and `ess sup_{(0,Jτ)}` (`L^∞_t`) of these
quantities by `C(N^{-p} + τ²)` and `C(N^{-p} + τ)` for finite data with
`‖U_{0,N}‖_{H^q} ≤ R₀` and `‖U_{0,N} - U₀‖_{H^{s+4}} ≤ C₀N^{-p}` (the data rate of
`eq:generated-initial-rate`, replacing the data distance `δ` of `GenReadout.generated_dynamics_closed`).
**`initial_rate_P0`** proves `eq:generated-initial-rate` as stated for `U_{0,N} = P_N U₀`, and
**`generated_nonempty_norms`** is `cor:generated-nonempty` in these norms.
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal

noncomputable section

namespace RenewalGeometry.GenNorms

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy KatoGalerkin FrameCurvature
  HarmonicDefect ActualJetWriter ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge
  ActualJetBridge ActualJetState ActualJetCompleteForcing ActualJetRecon ActualJetKato GenHermite
  GenResMaps GenPhysIdFinal GenReadout

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {SM : SMData (MatLie m) V S S'}

/-! ### Slice norms of general finite families -/

section General

variable {ι : Type*} [Fintype ι]

/-- The slice norm `(Σ_i Q_r(f_i)(t))^{1/2}` of a finite family indexed by any finite type. -/
def sliceHι (r : ℕ) (f : ι → ST 3 → ℝ) (t : ℝ) : ℝ := Real.sqrt (∑ i, Q r (f i) t)

theorem sliceHι_le_iff {r : ℕ} {f : ι → ST 3 → ℝ} {t B : ℝ} (hB : 0 ≤ B) :
    sliceHι r f t ≤ B ↔ ∑ i, Q r (f i) t ≤ B ^ 2 := by
  unfold sliceHι
  rw [Real.sqrt_le_left hB]

theorem sliceH_eq_sliceHι {n : ℕ} (r : ℕ) (f : Fin n → ST 3 → ℝ) (t : ℝ) :
    sliceH r f t = sliceHι r f t := rfl

end General

/-! ### The slice quantities of the piecewise record -/

section Record

variable {n N : ℕ} (κ : StateP m V S S' ≃ₗ[ℝ] (Fin n → ℝ)) (SM)

/-- `‖z_{N,τ}(t) - z(t)‖_{H^r}`: the coordinate state of the cubic Hermite record (read on the cell
of `t`) minus the coordinate state of the exact solution. -/
def stErr (q r : ℕ) (τ : ℝ) (Ud Gs : ℕ → GS 3 n N) (z : Tuple m V S S') (t : ℝ) : ℝ :=
  sliceH r (fun b x => GenRecNodes.recF q τ Ud Gs (cellIdx τ t) b x - stC κ SM z b x) t

/-- `‖∂_tz_{N,τ}(t) - ∂_tz(t)‖_{H^r}`. -/
def stErrD (q r : ℕ) (τ : ℝ) (Ud Gs : ℕ → GS 3 n N) (z : Tuple m V S S') (t : ℝ) : ℝ :=
  sliceH r (fun b x => pd (GenRecNodes.recF q τ Ud Gs (cellIdx τ t) b) 0 x -
    pd (stC κ SM z b) 0 x) t

/-- `‖Riem(g_{N,τ})(t) - Riem(g)(t)‖_{H^r}` (all components). -/
def riemErr (q r : ℕ) (τ : ℝ) (Ud Gs : ℕ → GS 3 n N) (z : Tuple m V S S') (t : ℝ) : ℝ :=
  sliceHι r (fun (c : Fin 4 × Fin 4 × Fin 4 × Fin 4) x =>
    riemR (hjF κ (GenRecNodes.recF q τ Ud Gs (cellIdx τ t)) x) c - riemR (hj2 z x) c) t

/-- `‖R_B(z_{N,τ})(t)‖_{H^r}` in the coordinates `e_B`. -/
def bosRes {nB : ℕ} (eB : BosP m V →L[ℝ] (Fin nB → ℝ)) (q r : ℕ) (τ : ℝ)
    (Ud Gs : ℕ → GS 3 n N) (t : ℝ) : ℝ :=
  sliceH r (fun k x => eB (bosR SM (hjF κ (GenRecNodes.recF q τ Ud Gs (cellIdx τ t)) x)) k) t

/-- `‖R_D(z_{N,τ})(t)‖_{H^r}` in the coordinates `e_D`. -/
def dirRes {nD : ℕ} (eD : S × S' →L[ℝ] (Fin nD → ℝ)) (q r : ℕ) (τ : ℝ)
    (Ud Gs : ℕ → GS 3 n N) (t : ℝ) : ℝ :=
  sliceH r (fun k x => eD (dirR SM (hjF κ (GenRecNodes.recF q τ Ud Gs (cellIdx τ t)) x)) k) t

end Record


/-! ### Cell bounds in norm form -/

section CellBounds

variable {n N : ℕ}

theorem theta_mem {τ t : ℝ} (hτ : 0 < τ) {j : ℕ}
    (ht : t ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ)) :
    (t - j * τ) / τ ∈ Icc (0 : ℝ) 1 ∧ (j : ℝ) * τ + (t - j * τ) / τ * τ = t := by
  refine ⟨⟨div_nonneg (by linarith [ht.1]) hτ.le, ?_⟩, by field_simp; ring⟩
  rw [div_le_one hτ]; linarith [ht.2]

/-- **State bound on a closed cell, norm form**: the Fourier-form Hermite rate at every
`θ ∈ [0, 1]` gives `‖z_{N,τ}(t) - V(t)‖_{H^r} ≤ B` on the closed cell. -/
theorem sliceH_recW_le {q r : ℕ} {τ : ℝ} (hτ : 0 < τ) {j : ℕ} {U0 U1 G0 G1 : GS 3 n N}
    {Vf : Fin n → ST 3 → ℝ} (hV : ∀ b, ContDiff ℝ ∞ (Vf b)) (hVp : ∀ b, IsSPeriodic (Vf b))
    {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ θ ∈ Icc (0 : ℝ) 1, ∀ S₀ : Finset (Fin 3 → ℤ), ∑ b, ∑ k ∈ S₀, wq r k *
      (cf q (SpectralGalerkin.hermite τ U0 U1 G0 G1 θ) b k - coef (Vf b) (j * τ + θ * τ) k) ^ 2 ≤
        B ^ 2) {t : ℝ} (ht : t ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ)) :
    sliceH r (fun b x => recW τ (j * τ) U0 U1 G0 G1 q b x - Vf b x) t ≤ B := by
  obtain ⟨hθ, hθt⟩ := theta_mem hτ ht
  rw [sliceH_le_iff_fourier (fun b => (contDiff_recW τ _ _ _ _ _ b).sub (hV b))
    (fun b k x => by simp only [isSPeriodic_recW τ _ _ _ _ _ b k x, hVp b k x]) hB]
  intro S₀
  refine le_of_eq_of_le ?_ (h _ hθ S₀)
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
  rw [coef_sub (contDiff_recW τ _ _ _ _ _ b).continuous (hV b).continuous, coef_recW, hθt]

/-- **Time-derivative bound on a closed cell, norm form.** -/
theorem sliceH_recWD_le {q r : ℕ} {τ : ℝ} (hτ : 0 < τ) {j : ℕ} {U0 U1 G0 G1 : GS 3 n N}
    {Vf : Fin n → ST 3 → ℝ} (hV : ∀ b, ContDiff ℝ ∞ (Vf b)) (hVp : ∀ b, IsSPeriodic (Vf b))
    {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ θ ∈ Icc (0 : ℝ) 1, ∀ S₀ : Finset (Fin 3 → ℤ), ∑ b, ∑ k ∈ S₀, wq r k *
      (cf q (SpectralGalerkin.hermiteD τ U0 U1 G0 G1 θ) b k -
        coef (pd (Vf b) 0) (j * τ + θ * τ) k) ^ 2 ≤ B ^ 2)
    {t : ℝ} (ht : t ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ)) :
    sliceH r (fun b x => pd (recW τ (j * τ) U0 U1 G0 G1 q b) 0 x - pd (Vf b) 0 x) t ≤ B := by
  obtain ⟨hθ, hθt⟩ := theta_mem hτ ht
  have hWt : ∀ b, pd (recW τ (j * τ) U0 U1 G0 G1 q b) 0 = recWD τ (j * τ) U0 U1 G0 G1 q b :=
    fun b => funext fun x => pd_recW_zero τ _ U0 U1 G0 G1 hτ.ne' b x
  simp only [hWt]
  rw [sliceH_le_iff_fourier (fun b => (contDiff_recWD τ _ _ _ _ _ b).sub
      (contDiff_pd_top (hV b) 0))
    (fun b k x => by simp only [isSPeriodic_recWD τ _ _ _ _ _ b k x,
      isSPeriodic_pd (hVp b) 0 k x]) hB]
  intro S₀
  refine le_of_eq_of_le ?_ (h _ hθ S₀)
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
  rw [coef_sub (contDiff_recWD τ _ _ _ _ _ b).continuous (contDiff_pd_top (hV b) 0).continuous,
    coef_recWD, hθt]

end CellBounds

/-! ### The Dirac readout extends to the nodes -/

section DiracNodes

variable {n N : ℕ} (κ : StateP m V S S' ≃ₗ[ℝ] (Fin n → ℝ))

/-- The coordinate 2-jet map of a family of fields. -/
def jetMap (W : Fin n → ST 3 → ℝ) (x : ST 3) : J2I 3 × Fin n → ℝ := fun p => j2c W p x

theorem continuous_jetMap {W : Fin n → ST 3 → ℝ} (hW : ∀ b, ContDiff ℝ ∞ (W b)) :
    Continuous (jetMap W) :=
  continuous_pi fun p => (contDiff_jop2 p.1 (hW p.2)).continuous

theorem contDiff_jetMap {W : Fin n → ST 3 → ℝ} (hW : ∀ b, ContDiff ℝ ∞ (W b)) :
    ContDiff ℝ ∞ (jetMap W) :=
  contDiff_pi.2 fun p => contDiff_jop2 p.1 (hW p.2)

theorem jetMap_periodic {W : Fin n → ST 3 → ℝ} (hWp : ∀ b, IsSPeriodic (W b)) (k : Fin 3 → ℤ)
    (x : ST 3) : jetMap W (x + sshift k) = jetMap W x :=
  funext fun p => isSPeriodic_jop2 p.1 (hWp p.2) k x

/-- **A residual readout of the record is continuous in time on a closed cell** whose 2-jets lie in
the chart: `t ↦ Σ_k Q_r((e_D R_D(z_{N,τ}))_k)(t)` is continuous on `[jτ, (j+1)τ]`. -/
theorem continuousOn_dirQ {nD : ℕ} (eD : S × S' →L[ℝ] (Fin nD → ℝ)) {W : Fin n → ST 3 → ℝ}
    (hW : ∀ b, ContDiff ℝ ∞ (W b)) (hWp : ∀ b, IsSPeriodic (W b)) {a b : ℝ} (hab : a ≤ b)
    (hch : ∀ y : ST 3, y 0 ∈ Icc a b →
      headJ (m := m) (V := V) (S := S) (S' := S') κ (jetMap W y) ∈ chartJ2 m V S S') (r : ℕ) :
    ContinuousOn (fun t => ∑ k, Q r (fun x => eD (dirR SM (hjF κ W x)) k) t) (Icc a b) := by
  set U : Set (ST 3) := (fun y => headJ (m := m) (V := V) (S := S) (S' := S') κ (jetMap W y)) ⁻¹'
    chartJ2 m V S S' with hUdef
  have hU : IsOpen U := isOpen_chartJ2.preimage ((contDiff_headJ κ).continuous.comp
    (continuous_jetMap hW))
  refine continuousOn_finsetSum _ fun k _ => ?_
  refine continuousOn_Q_of_smooth_near (f := fun x => eD (dirR SM (hjF κ W x)) k) ?_ hU hab hch
    ?_ r
  · intro m' x
    show eD (dirR SM (hjF κ W (x + sshift m'))) k = eD (dirR SM (hjF κ W x)) k
    rw [hjF_eq κ hW, hjF_eq κ hW]
    have := jetMap_periodic hWp m' x
    unfold jetMap at this
    rw [this]
  · intro x hx
    have e : (fun x => eD (dirR SM (hjF κ W x)) k) =
        fun x => eD (dirR SM (headJ κ (jetMap W x))) k := funext fun x => by rw [hjF_eq κ hW]; rfl
    rw [e]
    have h1 : ContDiffAt ℝ ∞ (fun x => headJ (m := m) (V := V) (S := S) (S' := S') κ
        (jetMap W x)) x := ((contDiff_headJ κ).comp (contDiff_jetMap hW)).contDiffAt
    have h2 := (dirR_smooth SM hx).comp x h1
    have h3 : ContDiffAt ℝ ∞ (fun v : S × S' => eD v k) (dirR SM (headJ κ (jetMap W x))) :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin nD => ℝ) k).comp eD).contDiff.contDiffAt
    exact h3.comp x h2

end DiracNodes


/-! ### Elementary rate algebra -/

section RateAlgebra

theorem inv_succ_pow_le {N p : ℕ} (hN : 1 ≤ N) : 1 / ((N : ℝ) + 1) ^ p ≤ ((N : ℝ) ^ p)⁻¹ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [one_div]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hN0.le (by linarith) p)

theorem npow_inv_le_inv {N N₀ p : ℕ} (hp : 1 ≤ p) (hN₀ : 1 ≤ N₀) (hN : N₀ ≤ N) :
    ((N : ℝ) ^ p)⁻¹ ≤ 1 / (N₀ : ℝ) := by
  have h0 : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN₀
  have h1 : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
  have h2 : (N : ℝ) ≤ (N : ℝ) ^ p := by
    calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (N : ℝ) ^ p := pow_le_pow_right₀ (by linarith) hp
  rw [one_div]
  exact inv_anti₀ (by linarith) (h1.trans h2)

/-- `τ^a + C₀ν' + ν ≤ (C₀ + 1)(ν' + τ^a)` for `ν ≤ ν'`. -/
theorem rate_le {C₀ x ν ν' : ℝ} (hC₀ : 0 ≤ C₀) (hx : 0 ≤ x) (hν : ν ≤ ν') (_hν' : 0 ≤ ν') :
    x + C₀ * ν' + ν ≤ (C₀ + 1) * (ν' + x) := by
  nlinarith

end RateAlgebra

/-! ### `thm:generated-dynamics` in norm form -/

section Main

variable {bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ} {bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ}
  {bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ} {bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ}

set_option maxHeartbeats 8000000 in
/-- **`thm:generated-dynamics` on the actual-jet system in the manuscript's norms** (`Σ = 𝕋³`,
variational theory data with decoupled spinors, `κ ≠ 0`, `s ≥ 3`, `p ≥ 1`, `q = s + p + 8`).
There are Euclidean coordinates `κ` such that for every compact chart margin the realized
symmetric system `(A, F)` satisfies: for every data radius `R₀` there are `T`, `R`, `c_*`, `τ_*`
such that every constrained smooth periodic datum `U₀` with `‖U₀‖_{H^q} ≤ R₀` and values in `K₀`
generates a smooth physical tuple `z` on `[0, t₁]` (`R_B = R_D = 0`, harmonic gauge,
actual-jet state `U₀` at `t = 0`), and for all coordinates `e_B`, `e_D` of the residual spaces and
every data-rate constant `C₀` there are `C`, `N₀`, `τ₀ > 0` such that for every cutoff `N ≥ N₀`
and step `τ` with `τ(N+1) ≤ c_*`, `τ ≤ τ₀` (`eq:generated-CFL`), and every finite datum
`U_{0,N} = a₀` with `‖U_{0,N}‖_{H^q} ≤ R₀` and `‖U_{0,N} - U₀‖_{H^{s+4}} ≤ C₀N^{-p}`
(`eq:generated-initial-rate`), the implicit-midpoint record exists on `[0, T]` with
`‖U^j‖_{H^q} ≤ R` (`eq:generated-midpoint`, `eq:generated-uniform`), and on every grid interval
`[0, Jτ] ⊆ [0, t₁]`:
* `sup_t ‖z_{N,τ} - z‖_{H^{s+2}} ≤ C(N^{-p} + τ²)` and `sup_t ‖∂_tz_{N,τ} - ∂_tz‖_{H^{s+2}} ≤
  C(N^{-p} + τ²)` (`eq:generated-first`, coordinate states; the time derivative even in
  `H^{s+2} ⊇ H^{s+1}`);
* `ess sup_t ‖Riem(g_{N,τ}) - Riem(g)‖_{H^s} ≤ C(N^{-p} + τ)`, `ess sup_t ‖R_B(z_{N,τ})‖_{H^s} ≤
  C(N^{-p} + τ)` (`eq:generated-bosonic`);
* `sup_t ‖R_D(z_{N,τ})‖_{H^{s+1}} ≤ C(N^{-p} + τ²)` (`eq:generated-Dirac`, `C_t`: the open-cell
  bounds extend to the nodes by continuity);
* `|D S^{cmp}[V]| ≤ C(N^{-p} + τ)‖V‖_{0,τ}` for every collar-fixed nodal variation
  (`eq:generated-stationarity`). -/
theorem generated_dynamics_norms (hS : SMSmooth SM) (hU : UnitaryForms SM bG bV bS bS')
    (hVS : GenStress.VariationalStress SM) (hκ0 : SM.κ ≠ 0) {s p : ℕ} (hs : 3 ≤ s) (hp : 1 ≤ p) :
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
        ∀ R₀ : ℝ, 0 ≤ R₀ → ∃ T > 0, ∃ R ≥ 0, ∃ cstar > 0,
        ∀ U₀ : Fin (dimS m V S S') → ST 3 → ℝ,
          GenPhysIdClosed.ConstrainedData SM κ U₀ → (∀ b, ContDiff ℝ ∞ (U₀ b)) →
          (∀ b, IsSPeriodic (U₀ b)) → sliceH (s + p + 8) U₀ 0 ≤ R₀ →
          (∀ y, (fun c => U₀ c (Fin.cons 0 y)) ∈ K₀) →
          ∃ (z : Tuple m V S S') (t₁ : ℝ), 0 < t₁ ∧ t₁ ≤ T ∧
            (∀ x ∈ slab (d := 3) 0 t₁, bosF SM z x = 0 ∧ dirF SM z x = 0 ∧ CF z x = 0) ∧
            (∀ b y, stC κ SM z b (Fin.cons 0 y) = U₀ b (Fin.cons 0 y)) ∧
            ∀ {nB : ℕ} (eB : BosP m V →L[ℝ] (Fin nB → ℝ)) {nD : ℕ}
              (eD : S × S' →L[ℝ] (Fin nD → ℝ)) (C₀ : ℝ), 0 ≤ C₀ →
            ∃ C ≥ 0, ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∃ τ₀ > 0,
              ∀ (N : ℕ) (τ : ℝ), N₀ ≤ N → 0 < τ → τ * ((N : ℝ) + 1) ≤ cstar → τ ≤ τ₀ →
              ∀ a₀ : GS 3 (dimS m V S S') N,
                sliceH (s + p + 8) (fld (s + p + 8) a₀) 0 ≤ R₀ →
                sliceH (s + 4) (fun b x => fld (s + p + 8) a₀ b x - U₀ b x) 0 ≤
                  C₀ * ((N : ℝ) ^ p)⁻¹ →
              ∃ Ud : ℕ → GS 3 (dimS m V S S') N, Ud 0 = a₀ ∧
                (∀ j : ℕ, (j : ℝ) * τ ≤ T → ‖Ud j‖ ≤ R ∧ (((j : ℝ) + 1) * τ ≤ T →
                  Ud (j + 1) = Ud j + τ • GN A F (s + p + 8)
                    (SpectralGalerkin.mid (Ud j) (Ud (j + 1))))) ∧
                ∀ J : ℕ, 1 ≤ J → (J : ℝ) * τ ≤ t₁ →
                  supNorm (stErr SM κ (s + p + 8) (s + 2) τ Ud
                      (fun i => GN A F (s + p + 8) (Ud i)) z) 0 (J * τ) ≤
                    ENNReal.ofReal (C * (((N : ℝ) ^ p)⁻¹ + τ ^ 2)) ∧
                  supNorm (stErrD SM κ (s + p + 8) (s + 2) τ Ud
                      (fun i => GN A F (s + p + 8) (Ud i)) z) 0 (J * τ) ≤
                    ENNReal.ofReal (C * (((N : ℝ) ^ p)⁻¹ + τ ^ 2)) ∧
                  essNorm (riemErr κ (s + p + 8) s τ Ud
                      (fun i => GN A F (s + p + 8) (Ud i)) z) 0 (J * τ) ≤
                    ENNReal.ofReal (C * (((N : ℝ) ^ p)⁻¹ + τ)) ∧
                  essNorm (bosRes SM κ eB (s + p + 8) s τ Ud
                      (fun i => GN A F (s + p + 8) (Ud i))) 0 (J * τ) ≤
                    ENNReal.ofReal (C * (((N : ℝ) ^ p)⁻¹ + τ)) ∧
                  supNorm (dirRes SM κ eD (s + p + 8) (s + 1) τ Ud
                      (fun i => GN A F (s + p + 8) (Ud i))) 0 (J * τ) ≤
                    ENNReal.ofReal (C * (((N : ℝ) ^ p)⁻¹ + τ ^ 2)) ∧
                  ∀ v w : ℕ → GS 3 (dimS m V S S') N,
                    v 0 = 0 → w 0 = 0 → v J = 0 → w J = 0 →
                    ∃ D : ℝ, HasDerivAt (fun ε : ℝ => GenStat.Scmp κ SM (s + p + 8) τ J
                        (fun j => Ud j + ε • v j)
                        (fun j => GN A F (s + p + 8) (Ud j) + ε • w j)) D 0 ∧
                      |D| ≤ C * (((N : ℝ) ^ p)⁻¹ + τ) *
                        GenStat.vnorm (s + p + 8) τ J v w := by
  obtain ⟨κ, hκ, h⟩ := generated_dynamics_ext (bG := bG) (bV := bV) (bS := bS) (bS' := bS')
    hS hU hVS hκ0 hs hp
  refine ⟨κ, hκ, fun K₀ K hK hKc δK hδK hKδ => ?_⟩
  obtain ⟨A, F, hA, hsym, hF, hAK, hFK, h2⟩ := h K₀ K hK hKc δK hδK hKδ
  refine ⟨A, F, hA, hsym, hF, hAK, hFK, fun R₀ hR₀ => ?_⟩
  obtain ⟨T, hT, R, hR, cstar, hc, τs, hτs, h3⟩ := h2 R₀ hR₀
  refine ⟨T, hT, R, hR, cstar, hc, fun U₀ hCD hU₀ hUp hE hK₀ => ?_⟩
  have hE' : energyQ (s + p + 8) U₀ 0 ≤ R₀ ^ 2 := (sliceH_le_iff hR₀).1 hE
  obtain ⟨z, t₁, ht₁, ht₁T, hphys, hinit, h4⟩ := h3 U₀ hCD hU₀ hUp hE' hK₀
  refine ⟨z, t₁, ht₁, ht₁T, hphys, hinit, fun {nB} eB {nD} eD C₀ hC₀ => ?_⟩
  obtain ⟨C₁, hC₁0, Cz, hCz, Cst, hCst, η, hη, K2, -, hK2c, h5⟩ := h4 eB eD
  set Cm : ℝ := max C₁ (max Cz Cst) with hCm
  have hCm0 : 0 ≤ Cm := le_max_of_le_left hC₁0
  have hC₁m : C₁ ≤ Cm := le_max_left _ _
  have hCzm : Cz ≤ Cm := (le_max_left _ _).trans (le_max_right _ _)
  have hCstm : Cst ≤ Cm := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (2 * (C₀ + 1) / η)
  set N₀ : ℕ := k₀ + 1 with hN₀
  have hN₀1 : 1 ≤ N₀ := Nat.le_add_left 1 k₀
  refine ⟨Cm * (C₀ + 1), by positivity, N₀, hN₀1, min τs (η / 2), lt_min hτs (by positivity),
    fun N τ hN hτ hcfl hττ a₀ ha₀ hdist => ?_⟩
  have hN1 : 1 ≤ N := hN₀1.trans hN
  set νp : ℝ := ((N : ℝ) ^ p)⁻¹ with hνp
  have hνp0 : 0 ≤ νp := by positivity
  set ν : ℝ := 1 / ((N : ℝ) + 1) ^ p with hν
  have hν0 : 0 ≤ ν := by positivity
  have hννp : ν ≤ νp := inv_succ_pow_le hN1
  set δ : ℝ := C₀ * νp with hδ
  have hδ0 : 0 ≤ δ := by positivity
  -- the smallness of the data distance
  have hsm : τ + δ + ν ≤ η := by
    have h1 : νp ≤ 1 / (N₀ : ℝ) := npow_inv_le_inv hp hN₀1 hN
    have hN₀pos : (0 : ℝ) < N₀ := by exact_mod_cast hN₀1
    have h2 : (C₀ + 1) * (1 / (N₀ : ℝ)) ≤ η / 2 := by
      have hk : 2 * (C₀ + 1) / η < N₀ := by
        have : (k₀ : ℝ) < N₀ := by rw [hN₀]; push_cast; linarith
        linarith
      rw [div_lt_iff₀ hη] at hk
      rw [mul_one_div, div_le_iff₀ hN₀pos]
      nlinarith
    have h3 : (C₀ + 1) * νp ≤ η / 2 := (mul_le_mul_of_nonneg_left h1 (by linarith)).trans h2
    have h4 : τ ≤ η / 2 := hττ.trans (min_le_right _ _)
    nlinarith
  -- the finite data in the form of the readout package
  have ha₀' : ‖a₀‖ ≤ R₀ := by rwa [sliceH_fld] at ha₀
  have hdata : ∀ S₀ : Finset (Fin 3 → ℤ), ∑ b, ∑ k ∈ S₀, wq (s + 4) k *
      (cf (s + p + 8) a₀ b k - coef (U₀ b) 0 k) ^ 2 ≤ δ ^ 2 := by
    intro S₀
    have hf := (sliceH_le_iff_fourier (r := s + 4)
      (f := fun b x => fld (s + p + 8) a₀ b x - U₀ b x)
      (fun b => (contDiff_fld _ a₀ b).sub (hU₀ b))
      (fun b k x => by simp only [isSPeriodic_fld _ a₀ b k x, hUp b k x]) hδ0).1 hdist S₀
    refine le_of_eq_of_le ?_ hf
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
    rw [coef_sub (contDiff_fld _ a₀ b).continuous (hU₀ b).continuous, KatoRates.coef_fld]
  obtain ⟨Ud, hUd0, hrec, hstate, hderiv, hcells, hstat⟩ := h5 N τ hτ hcfl
    (hττ.trans (min_le_left _ _)) a₀ δ ha₀' hδ0 hdata hsm
  refine ⟨Ud, hUd0, hrec, fun J hJ hJt => ?_⟩
  -- the rate algebra
  have hr2 : τ ^ 2 + δ + ν ≤ (C₀ + 1) * (νp + τ ^ 2) := rate_le hC₀ (sq_nonneg τ) hννp hνp0
  have hr1 : τ + δ + ν ≤ (C₀ + 1) * (νp + τ) := rate_le hC₀ hτ.le hννp hνp0
  have hB2 : ∀ C' : ℝ, 0 ≤ C' → C' ≤ Cm → C' * (τ ^ 2 + δ + ν) ≤ Cm * (C₀ + 1) * (νp + τ ^ 2) :=
    fun C' hC' hCC => by
      calc C' * (τ ^ 2 + δ + ν) ≤ Cm * ((C₀ + 1) * (νp + τ ^ 2)) :=
            mul_le_mul hCC hr2 (by positivity) hCm0
        _ = _ := by ring
  have hB1 : ∀ C' : ℝ, 0 ≤ C' → C' ≤ Cm → C' * (τ + δ + ν) ≤ Cm * (C₀ + 1) * (νp + τ) :=
    fun C' hC' hCC => by
      calc C' * (τ + δ + ν) ≤ Cm * ((C₀ + 1) * (νp + τ)) :=
            mul_le_mul hCC hr1 (by positivity) hCm0
        _ = _ := by ring
  have hpos2 : 0 ≤ Cm * (C₀ + 1) * (νp + τ ^ 2) := by positivity
  have hpos1 : 0 ≤ Cm * (C₀ + 1) * (νp + τ) := by positivity
  -- the cell of a time of `[0, Jτ]`
  have hcell : ∀ t ∈ Icc (0 : ℝ) (J * τ), cellIdx τ t < J ∧
      t ∈ Icc ((cellIdx τ t : ℝ) * τ) (((cellIdx τ t : ℝ) + 1) * τ) ∧
      ((cellIdx τ t : ℝ) + 1) * τ ≤ t₁ := by
    intro t ht
    have hlt := cellIdx_lt hτ hJ ht.2
    refine ⟨hlt, cellIdx_mem hτ ht.1, ?_⟩
    have : ((cellIdx τ t : ℝ) + 1) ≤ J := by exact_mod_cast hlt
    nlinarith
  have hcellO : ∀ t ∈ Ioo (0 : ℝ) (J * τ), t ∉ Set.range (fun j : ℕ => (j : ℝ) * τ) →
      cellIdx τ t < J ∧
      t ∈ Ioo ((cellIdx τ t : ℝ) * τ) (((cellIdx τ t : ℝ) + 1) * τ) ∧
      ((cellIdx τ t : ℝ) + 1) * τ ≤ t₁ := by
    intro t ht hn
    obtain ⟨h1, -, h3⟩ := hcell t (Ioo_subset_Icc_self ht)
    exact ⟨h1, mem_open_cell hτ ht.1 hn, h3⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, fun v w hv0 hw0 hvJ hwJ => ?_⟩
  · -- `C_tH^{s+2}` state rate
    rw [supNorm_le_iff hpos2]
    intro t ht
    obtain ⟨-, hmem, hjt⟩ := hcell t ht
    exact (sliceH_recW_le hτ (contDiff_stC κ SM z) (isSPeriodic_stC κ SM z) (by positivity)
      (hstate _ hjt) hmem).trans (hB2 Cz hCz hCzm)
  · -- `C_tH^{s+2}` time-derivative rate
    rw [supNorm_le_iff hpos2]
    intro t ht
    obtain ⟨-, hmem, hjt⟩ := hcell t ht
    exact (sliceH_recWD_le hτ (contDiff_stC κ SM z) (isSPeriodic_stC κ SM z) (by positivity)
      (hderiv _ hjt) hmem).trans (hB2 Cz hCz hCzm)
  · -- `L^∞_tH^s` Riemann rate
    refine essNorm_le_of_off_countable (nodes_countable τ) fun t ht hn => ?_
    obtain ⟨-, hmem, hjt⟩ := hcellO t ht hn
    have hb := (((hcells _ hjt).2.2 t hmem).1)
    refine ((sliceHι_le_iff (by positivity)).2 hb).trans (hB1 C₁ hC₁0 hC₁m)
  · -- `L^∞_tH^s` bosonic residual
    refine essNorm_le_of_off_countable (nodes_countable τ) fun t ht hn => ?_
    obtain ⟨-, hmem, hjt⟩ := hcellO t ht hn
    have hb := (((hcells _ hjt).2.2 t hmem).2.1)
    exact ((sliceH_le_iff (by positivity)).2 hb).trans (hB1 C₁ hC₁0 hC₁m)
  · -- `C_tH^{s+1}` Dirac residual: open-cell bound and continuity up to the nodes
    rw [supNorm_le_iff hpos2]
    intro t ht
    obtain ⟨-, hmem, hjt⟩ := hcell t ht
    set j := cellIdx τ t with hjdef
    have hcont := continuousOn_dirQ κ (SM := SM) eD
      (fun b => GenRecNodes.contDiff_recF (s + p + 8) τ Ud (fun i => GN A F (s + p + 8) (Ud i)) j b)
      (fun b => GenRecNodes.isSPeriodic_recF (s + p + 8) τ Ud (fun i => GN A F (s + p + 8) (Ud i))
        j b)
      (by nlinarith : (j : ℝ) * τ ≤ ((j : ℝ) + 1) * τ)
      (fun y hy => hK2c _ ((hcells j hjt).1 y hy)) (s + 1)
    have hopen : ∀ t' ∈ Ioo ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
        ∑ k, Q (s + 1) (fun x => eD (dirR SM (hjF κ (GenRecNodes.recF (s + p + 8) τ Ud
          (fun i => GN A F (s + p + 8) (Ud i)) j) x)) k) t' ≤
          (C₁ * (τ ^ 2 + δ + ν)) ^ 2 := fun t' ht' => ((hcells j hjt).2.2 t' ht').2.2
    have hclosed := le_on_Icc_of_Ioo (by nlinarith) hcont hopen t hmem
    exact ((sliceH_le_iff (by positivity)).2 hclosed).trans (hB2 C₁ hC₁0 hC₁m)
  · -- stationarity
    obtain ⟨D, hD, hDb⟩ := hstat J hJt v w hv0 hw0 hvJ hwJ
    refine ⟨D, hD, hDb.trans ?_⟩
    have hvn : 0 ≤ GenStat.vnorm (s + p + 8) τ J v w := Real.sqrt_nonneg _
    exact mul_le_mul_of_nonneg_right (hB1 Cst hCst hCstm) hvn

end Main


/-! ### `eq:generated-initial-rate` for the projected data and `cor:generated-nonempty` -/

section Corollary

/-- **`eq:generated-initial-rate` exactly as stated for `U_{0,N} = P_N U₀`**: for a smooth
spatially periodic datum, `sup_N ‖U_{0,N}‖_{H^q} ≤ M_q := ‖U₀‖_{H^q}` and
`‖U_{0,N} - U₀‖_{H^{s+4}} ≤ M_q N^{-p}` for every `N ≥ 1` (`q = s + p + 8`). -/
theorem initial_rate_P0 {n : ℕ} {s p : ℕ} {U₀ : Fin n → ST 3 → ℝ} (hU : ∀ b, ContDiff ℝ ∞ (U₀ b))
    (hUp : ∀ b, IsSPeriodic (U₀ b)) :
    (∀ N : ℕ, sliceH (s + p + 8) (fld (s + p + 8) (P0 (d := 3) (s + p + 8) N U₀)) 0 ≤
      sliceH (s + p + 8) U₀ 0) ∧
    ∀ N : ℕ, 1 ≤ N →
      sliceH (s + 4) (fun b x => fld (s + p + 8) (P0 (d := 3) (s + p + 8) N U₀) b x - U₀ b x) 0 ≤
        sliceH (s + p + 8) U₀ 0 * ((N : ℝ) ^ p)⁻¹ := by
  have hM0 := sliceH_nonneg (s + p + 8) U₀ 0
  refine ⟨fun N => ?_, fun N hN => ?_⟩
  · rw [sliceH_fld]
    have h1 := norm_P0_sq_le (d := 3) (s + p + 8) N hU hUp
    have h2 : energyQ (s + p + 8) U₀ 0 = sliceH (s + p + 8) U₀ 0 ^ 2 := by
      unfold sliceH energyQ
      rw [Real.sq_sqrt (sum_Q_nonneg _ _ _)]
    rw [h2] at h1
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hM0 (by norm_num)).1 h1
  · have hB : 0 ≤ sliceH (s + p + 8) U₀ 0 * ((N : ℝ) ^ p)⁻¹ := by positivity
    rw [sliceH_le_iff_fourier (fun b => (contDiff_fld _ _ b).sub (hU b))
      (fun b k x => by simp only [isSPeriodic_fld _ _ b k x, hUp b k x]) hB]
    intro S₀
    have h1 := GenReadout.P0_data_error (d := 3) (s + p + 8) (s + 4) (p + 4) N (by omega) hU hUp S₀
    have hX := GenReadout.inv_X_le (N := N) (p := p) (j := p + 4) (by omega)
    have hE0 : 0 ≤ energyQ (s + p + 8) U₀ 0 := Finset.sum_nonneg fun b _ => Q_nonneg _ _ _
    have hEq : energyQ (s + p + 8) U₀ 0 = sliceH (s + p + 8) U₀ 0 ^ 2 := by
      unfold sliceH energyQ
      rw [Real.sq_sqrt (sum_Q_nonneg _ _ _)]
    have hνν := inv_succ_pow_le (p := p) hN
    have hν0 : 0 ≤ 1 / ((N : ℝ) + 1) ^ p := by positivity
    calc ∑ b, ∑ k ∈ S₀, wq (s + 4) k *
          coef (fun x => fld (s + p + 8) (P0 (d := 3) (s + p + 8) N U₀) b x - U₀ b x) 0 k ^ 2
        = ∑ b, ∑ k ∈ S₀, wq (s + 4) k *
          (cf (s + p + 8) (P0 (d := 3) (s + p + 8) N U₀) b k - coef (U₀ b) 0 k) ^ 2 := by
          refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
          rw [coef_sub (contDiff_fld _ _ b).continuous (hU b).continuous, KatoRates.coef_fld]
      _ ≤ energyQ (s + p + 8) U₀ 0 / ((2 * Real.pi * ((N : ℝ) + 1)) ^ 2) ^ (p + 4) := h1
      _ = energyQ (s + p + 8) U₀ 0 * (1 / ((2 * Real.pi * ((N : ℝ) + 1)) ^ 2) ^ (p + 4)) :=
          div_eq_mul_one_div _ _
      _ ≤ energyQ (s + p + 8) U₀ 0 * (1 / ((N : ℝ) + 1) ^ p) ^ 2 :=
          mul_le_mul_of_nonneg_left hX hE0
      _ ≤ sliceH (s + p + 8) U₀ 0 ^ 2 * (((N : ℝ) ^ p)⁻¹) ^ 2 := by
          rw [hEq]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hν0 hνν 2) (sq_nonneg _)
      _ = (sliceH (s + p + 8) U₀ 0 * ((N : ℝ) ^ p)⁻¹) ^ 2 := by ring

variable {bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ} {bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ}
  {bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ} {bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ}

set_option maxHeartbeats 8000000 in
/-- **`cor:generated-nonempty` in the manuscript's norms** (`Σ = 𝕋³`, variational theory data,
decoupled spinors, `κ ≠ 0`).  For every constrained smooth periodic datum `U₀` the finite data
`U_{0,N} = P_N U₀` satisfy `eq:generated-initial-rate` (`initial_rate_P0`), and for all residual
coordinates there are `C`, `N₀`, `τ₀ > 0` such that for every `N ≥ N₀` and CFL step `τ ≤ τ₀` the
record started from `U_{0,N}` exists on `[0, T]` and on every grid interval `[0, Jτ] ⊆ [0, t₁]`:
`‖z_{N,τ} - z‖_{C_tH^{s+2}} + ‖∂_tz_{N,τ} - ∂_tz‖_{C_tH^{s+2}} ≤ C(N^{-p} + τ²)`,
`‖Riem(g_{N,τ}) - Riem(g)‖_{L^∞_tH^s} + ‖R_B(z_{N,τ})‖_{L^∞_tH^s} ≤ C(N^{-p} + τ)`,
`‖R_D(z_{N,τ})‖_{C_tH^{s+1}} ≤ C(N^{-p} + τ²)` (`eq:generated-nonempty`) and
`|DS^{cmp}[V]| ≤ C(N^{-p} + τ)‖V‖_{0,τ}`; the dyadic budget `Σ_n (N_n^{-p} + τ_n)`,
`N_n = 2^n`, `τ_n(N_n + 1) ≤ c_*`, is summable. -/
theorem generated_nonempty_norms (hS : SMSmooth SM) (hU : UnitaryForms SM bG bV bS bS')
    (hVS : GenStress.VariationalStress SM) (hκ0 : SM.κ ≠ 0) {s p : ℕ} (hs : 3 ≤ s) (hp : 1 ≤ p) :
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
        ∀ R₀ : ℝ, 0 ≤ R₀ → ∃ T > 0, ∃ R ≥ 0, ∃ cstar > 0,
        (∀ τd : ℕ → ℝ, (∀ n, 0 ≤ τd n ∧ τd n * ((2 : ℝ) ^ n + 1) ≤ cstar) →
          Summable (fun n : ℕ => 1 / ((2 : ℝ) ^ n + 1) ^ p + τd n)) ∧
        ∀ U₀ : Fin (dimS m V S S') → ST 3 → ℝ,
          GenPhysIdClosed.ConstrainedData SM κ U₀ → (∀ b, ContDiff ℝ ∞ (U₀ b)) →
          (∀ b, IsSPeriodic (U₀ b)) → sliceH (s + p + 8) U₀ 0 ≤ R₀ →
          (∀ y, (fun c => U₀ c (Fin.cons 0 y)) ∈ K₀) →
          ∃ (z : Tuple m V S S') (t₁ : ℝ), 0 < t₁ ∧ t₁ ≤ T ∧
            (∀ x ∈ slab (d := 3) 0 t₁, bosF SM z x = 0 ∧ dirF SM z x = 0 ∧ CF z x = 0) ∧
            (∀ b y, stC κ SM z b (Fin.cons 0 y) = U₀ b (Fin.cons 0 y)) ∧
            ∀ {nB : ℕ} (eB : BosP m V →L[ℝ] (Fin nB → ℝ)) {nD : ℕ}
              (eD : S × S' →L[ℝ] (Fin nD → ℝ)),
            ∃ C ≥ 0, ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∃ τ₀ > 0,
              ∀ (N : ℕ) (τ : ℝ), N₀ ≤ N → 0 < τ → τ * ((N : ℝ) + 1) ≤ cstar → τ ≤ τ₀ →
              ∃ Ud : ℕ → GS 3 (dimS m V S S') N, Ud 0 = P0 (s + p + 8) N U₀ ∧
                (∀ j : ℕ, (j : ℝ) * τ ≤ T → ‖Ud j‖ ≤ R ∧ (((j : ℝ) + 1) * τ ≤ T →
                  Ud (j + 1) = Ud j + τ • GN A F (s + p + 8)
                    (SpectralGalerkin.mid (Ud j) (Ud (j + 1))))) ∧
                ∀ J : ℕ, 1 ≤ J → (J : ℝ) * τ ≤ t₁ →
                  supNorm (stErr SM κ (s + p + 8) (s + 2) τ Ud
                      (fun i => GN A F (s + p + 8) (Ud i)) z) 0 (J * τ) ≤
                    ENNReal.ofReal (C * (((N : ℝ) ^ p)⁻¹ + τ ^ 2)) ∧
                  supNorm (stErrD SM κ (s + p + 8) (s + 2) τ Ud
                      (fun i => GN A F (s + p + 8) (Ud i)) z) 0 (J * τ) ≤
                    ENNReal.ofReal (C * (((N : ℝ) ^ p)⁻¹ + τ ^ 2)) ∧
                  essNorm (riemErr κ (s + p + 8) s τ Ud
                      (fun i => GN A F (s + p + 8) (Ud i)) z) 0 (J * τ) ≤
                    ENNReal.ofReal (C * (((N : ℝ) ^ p)⁻¹ + τ)) ∧
                  essNorm (bosRes SM κ eB (s + p + 8) s τ Ud
                      (fun i => GN A F (s + p + 8) (Ud i))) 0 (J * τ) ≤
                    ENNReal.ofReal (C * (((N : ℝ) ^ p)⁻¹ + τ)) ∧
                  supNorm (dirRes SM κ eD (s + p + 8) (s + 1) τ Ud
                      (fun i => GN A F (s + p + 8) (Ud i))) 0 (J * τ) ≤
                    ENNReal.ofReal (C * (((N : ℝ) ^ p)⁻¹ + τ ^ 2)) ∧
                  ∀ v w : ℕ → GS 3 (dimS m V S S') N,
                    v 0 = 0 → w 0 = 0 → v J = 0 → w J = 0 →
                    ∃ D : ℝ, HasDerivAt (fun ε : ℝ => GenStat.Scmp κ SM (s + p + 8) τ J
                        (fun j => Ud j + ε • v j)
                        (fun j => GN A F (s + p + 8) (Ud j) + ε • w j)) D 0 ∧
                      |D| ≤ C * (((N : ℝ) ^ p)⁻¹ + τ) *
                        GenStat.vnorm (s + p + 8) τ J v w := by
  obtain ⟨κ, hκ, h⟩ := generated_dynamics_norms (bG := bG) (bV := bV) (bS := bS) (bS' := bS')
    hS hU hVS hκ0 hs hp
  refine ⟨κ, hκ, fun K₀ K hK hKc δK hδK hKδ => ?_⟩
  obtain ⟨A, F, hA, hsym, hF, hAK, hFK, h2⟩ := h K₀ K hK hKc δK hδK hKδ
  refine ⟨A, F, hA, hsym, hF, hAK, hFK, fun R₀ hR₀ => ?_⟩
  obtain ⟨T, hT, R, hR, cstar, hc, h3⟩ := h2 R₀ hR₀
  refine ⟨T, hT, R, hR, cstar, hc, fun τd hτd => GenReadout.summable_dyadic hp τd hτd,
    fun U₀ hCD hU₀ hUp hE hK₀ => ?_⟩
  obtain ⟨z, t₁, ht₁, ht₁T, hphys, hinit, h4⟩ := h3 U₀ hCD hU₀ hUp hE hK₀
  refine ⟨z, t₁, ht₁, ht₁T, hphys, hinit, fun {nB} eB {nD} eD => ?_⟩
  obtain ⟨C, hC, N₀, hN₀, τ₀, hτ₀, h5⟩ := h4 eB eD R₀ hR₀
  refine ⟨C, hC, N₀, hN₀, τ₀, hτ₀, fun N τ hN hτ hcfl hττ => ?_⟩
  obtain ⟨hsup, hrate⟩ := initial_rate_P0 (s := s) (p := p) hU₀ hUp
  have hN1 : 1 ≤ N := hN₀.trans hN
  have hd : sliceH (s + 4) (fun b x => fld (s + p + 8) (P0 (d := 3) (s + p + 8) N U₀) b x -
      U₀ b x) 0 ≤ R₀ * ((N : ℝ) ^ p)⁻¹ :=
    (hrate N hN1).trans (mul_le_mul_of_nonneg_right hE (by positivity))
  exact h5 N τ hN hτ hcfl hττ (P0 (s + p + 8) N U₀) ((hsup N).trans hE) hd

end Corollary


/-! ### Non-vacuity -/

section NonVacuity

open CoupledBootstrap.FlatVacuum in
set_option maxHeartbeats 4000000 in
/-- **Non-vacuity of the norm-form corollary**: for the vanishing-coupling data `trivSMM` and the
flat-vacuum datum there are a cutoff `N`, a step `τ > 0` with a grid interval `[0, τ] ⊆ [0, t₁]`
and the generated record from `P_N U₀` whose `C_tH^{s+2}` state error and `C_tH^{s+1}` Dirac
residual are bounded by `C(N^{-p} + τ²)`. -/
example : ∃ (κ : StateP 1 (MatLie 1) PUnit.{1} PUnit.{1} ≃ₗ[ℝ]
      (Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ℝ))
    (A : Fin 3 → Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) →
      Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) →
        (Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ℝ) → ℝ)
    (F : Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) →
      (Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ℝ) → ℝ)
    (z : Tuple 1 (MatLie 1) PUnit.{1} PUnit.{1}) (t₁ C : ℝ) (N : ℕ) (τ : ℝ)
    (Ud : ℕ → GS 3 (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) N),
    0 < τ ∧ τ ≤ t₁ ∧ 1 ≤ N ∧
      (∀ x ∈ slab (d := 3) 0 t₁, bosF trivSMM z x = 0 ∧ dirF trivSMM z x = 0 ∧ CF z x = 0) ∧
      Ud 0 = P0 12 N (GenPhysId.stU κ trivSMM flat) ∧
      supNorm (stErr trivSMM κ 12 5 τ Ud (fun i => GN A F 12 (Ud i)) z) 0 (((1 : ℕ) : ℝ) * τ) ≤
        ENNReal.ofReal (C * (((N : ℝ) ^ 1)⁻¹ + τ ^ 2)) ∧
      supNorm (dirRes trivSMM κ (0 : PUnit.{1} × PUnit.{1} →L[ℝ] (Fin 0 → ℝ)) 12 4 τ Ud
        (fun i => GN A F 12 (Ud i))) 0 (((1 : ℕ) : ℝ) * τ) ≤
        ENNReal.ofReal (C * (((N : ℝ) ^ 1)⁻¹ + τ ^ 2)) := by
  have hκ1 : trivSMM.κ ≠ 0 := by simp [trivSMM]
  obtain ⟨κ, -, h⟩ := generated_nonempty_norms trivSMM_smooth unitaryForms_triv
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
  obtain ⟨T, -, R, -, cstar, hc, -, h3⟩ :=
    h2 (sliceH 12 (GenPhysId.stU κ trivSMM flat) 0) (sliceH_nonneg _ _ _)
  obtain ⟨z, t₁, ht₁, -, hphys, -, h4⟩ := h3 (GenPhysId.stU κ trivSMM flat)
    ⟨flat, fun _ _ => rfl, GenPhysIdClosed.flat_sliceConstrained⟩
    (GenPhysId.contDiff_stU κ trivSMM flat) (GenPhysId.isSPeriodic_stU κ trivSMM flat) le_rfl
    (fun y => by
      show κ (stateF trivSMM flat (Fin.cons 0 y)) ∈ ({κ minkState} : Set _)
      rw [stateF_flat]; exact Set.mem_singleton _)
  obtain ⟨C, -, N₀, hN₀, τ₀, hτ₀, h5⟩ :=
    h4 (0 : BosP 1 (MatLie 1) →L[ℝ] (Fin 0 → ℝ)) (0 : PUnit.{1} × PUnit.{1} →L[ℝ] (Fin 0 → ℝ))
  have hN1 : (0 : ℝ) < (N₀ : ℝ) + 1 := by positivity
  set τ : ℝ := min (min τ₀ (cstar / ((N₀ : ℝ) + 1))) t₁ with hτdef
  have hτ : 0 < τ := lt_min (lt_min hτ₀ (div_pos hc hN1)) ht₁
  have hτ1 : τ ≤ τ₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hτ2 : τ ≤ cstar / ((N₀ : ℝ) + 1) := (min_le_left _ _).trans (min_le_right _ _)
  have hτ4 : τ ≤ t₁ := min_le_right _ _
  have hcfl : τ * ((N₀ : ℝ) + 1) ≤ cstar := by
    rwa [le_div_iff₀ hN1] at hτ2
  obtain ⟨Ud, hUd0, -, hJ⟩ := h5 N₀ τ le_rfl hτ hcfl hτ1
  obtain ⟨hs1, -, -, -, hd, -⟩ := hJ 1 le_rfl (by simpa using hτ4)
  exact ⟨κ, A, F, z, t₁, C, N₀, τ, Ud, hτ, hτ4, hN₀, hphys, hUd0, hs1, hd⟩

end NonVacuity

end RenewalGeometry.GenNorms
