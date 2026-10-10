/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedConstraintReduction
import RenewalGeometry.Continuum.ActualJetKatoRealization

/-!
# Identification of Kato's solution with physical solutions of the actual-jet system

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`
(`app:generated-dynamics`), the uniqueness step of its proof: "Its actual first jets satisfy
`eq:generated-extension` by `prop:actual-jet-writer`.  Uniqueness for the symmetric system
therefore identifies the independent [Sobolev] solution with those actual jets on their common
local interval."

Setting: the realized coefficient maps `A^j, F` of `ActualJetKato.actual_jet_kato_realization`
(Euclidean coordinates `κ` of the block inner product; on a compact chart set `K` they are the
actual-jet principal operators and forcing).  For a smooth tuple `z` we write `stU κ z` for the
coordinates of its actual-jet state field and `stP κ z` for their spatial derivatives.

* **`twoSided_of_symEq`**, **`twoSided_of_physical`** — if the actual-jet state of `z` solves the
  independent symmetric system on the open slab `(-ε, ε) × 𝕋³` (in particular if `z` is a
  physical solution there, `GenConstraint.IsPhysicalOn`) with states in `K`, then `stU κ z` is a
  classical two-sided solution of the realized symmetric system on `(-ε, ε)`
  (`GenConstraint.symEqAt_of_physical` + `ActualJetKato.genP_eq_actual_jet`).
* **`kato_eq_physical_state`** — every classical two-sided solution of the realized system with the
  same data coincides with the actual-jet state of `z` on `[0, t₁] × 𝕋³` for every `t₁` below
  both existence times (`KatoStab.twoSided_unique`): on that slab the head fields of the Kato
  solution **are** the physical fields of `z`.
* `PhysicalCauchyCore` — the physical-Cauchy clause of `ass:constrained-initial-solver` in
  physical terms ("on this core the constrained physical Cauchy problem admits locally unique
  analytic solutions with continuation controlled by the declared Sobolev bounds and field-chart
  margins"): one existence time per `H^q` radius for **physical solutions** (tuples with vanishing
  residuals and harmonic defect, states in the chart margin `K`); `CoreDense` — density of the core
  in the constrained class with a uniform `H^q` bound (used by the manuscript's proof).
* `physJets`, **`analyticCoreContinuation_of_physicalCauchy`** — the named input
  `KatoStab.AnalyticCoreContinuation` is **derived** (its `germ` clause, including "the germ solves
  the symmetric system" and "the germ satisfies the identities") from `PhysicalCauchyCore` and
  `CoreDense`, for every continuous family of first-jet identities vanishing on the first jets of
  physical states (`physJets`).
* **`generated_physical_identification_of_physicalCauchy`** — `lem:generated-physical-
  identification` for the actual-jet system under `PhysicalCauchyCore` and `CoreDense`: for every
  `H^q` radius `R₀` there is a Kato time `T > 0` (depending only on `R₀`) and `t₁ > 0` such that
  every constrained datum has a two-sided Kato solution on `(-T, T)` whose first jet lies, at
  every point of `[0, t₁] × 𝕋³`, in the closure of the first jets of physical solutions.

Disclosed: `Σ = 𝕋³`; smooth data with `H^q` bounds; the coefficient maps are the smooth cutoff
extensions of `actual_jet_kato_realization`.  `PhysicalCauchyCore` is the manuscript's assumption
(it is NOT proved here: the constraint propagation that would replace it is not formalised, and
propagation fails for non-variational theory data, `GenConstraintObs.kato_solution_not_physical`),
and
`CoreDense` is the approximation step of the manuscript's proof (Fourier-polynomial seeds and the
exact contraction of `prop:generated-initial`), which needs the map from conformal seeds to
actual-jet initial states (not formalised).
-/

open Filter Topology Set
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.GenPhysId

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk QLEnergy KatoGalerkin ActualJetSystem ActualJetSmooth
  ActualJetBridge ActualJetCompleteForcing ActualJetState ActualJetKato GenConstraint

set_option linter.unusedSectionVars false

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

/-- Coordinates of the actual-jet state field. -/
def stU (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ)) (SM : SMData (MatLie m) V S S')
    (z : Tuple m V S S') : Fin (dimS m V S S') → ST 3 → ℝ :=
  fun b y => κ (stateF SM z y) b

/-- Coordinates of its spatial derivatives. -/
def stP (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ)) (SM : SMData (MatLie m) V S S')
    (z : Tuple m V S S') : Fin (dimS m V S S') → Fin 3 → ST 3 → ℝ :=
  fun b i y => κ (pd (stateF SM z) i.succ y) b

section Coord

variable (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ)) (SM : SMData (MatLie m) V S S')
  (z : Tuple m V S S')

/-- The coordinate functional `v ↦ (κ v)_b` as a continuous linear map. -/
def coordL {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ}
    (κ : E ≃ₗ[ℝ] (Fin n → ℝ)) (b : Fin n) : E →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj b).comp (LinearMap.toContinuousLinearMap κ.toLinearMap)

theorem coordL_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (κ : E ≃ₗ[ℝ] (Fin n → ℝ)) (b : Fin n) (v : E) : coordL κ b v = κ v b :=
  rfl

theorem stU_eq (b : Fin (dimS m V S S')) : stU κ SM z b = fun y => coordL κ b (stateF SM z y) :=
  rfl

theorem contDiff_stU (b : Fin (dimS m V S S')) : ContDiff ℝ ∞ (stU κ SM z b) := by
  rw [stU_eq]
  exact (coordL κ b).contDiff.comp (contDiff_stateF SM z)

/-- `∂_μ(κ𝒰)_b = (κ∂_μ𝒰)_b`. -/
theorem pd_stU (b : Fin (dimS m V S S')) (μ : Fin 4) (y : ST 3) :
    pd (stU κ SM z b) μ y = κ (pd (stateF SM z) μ y) b := by
  have hd : DifferentiableAt ℝ (stateF SM z) y :=
    (contDiff_stateF SM z).differentiable (by simp) y
  have h : HasFDerivAt (fun y => coordL κ b (stateF SM z y))
      ((coordL κ b).comp (fderiv ℝ (stateF SM z) y)) y :=
    (coordL κ b).hasFDerivAt.comp y hd.hasFDerivAt
  unfold SobolevOpen.pd
  rw [stU_eq, h.fderiv]
  rfl

end Coord

/-! ### Physical tuples give classical solutions of the realized system -/

section TwoSided

variable {SM : SMData (MatLie m) V S S'} {κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ)}
  {K : Set (Fin (dimS m V S S') → ℝ)}
  {A : Fin 3 → Fin (dimS m V S S') → Fin (dimS m V S S') → (Fin (dimS m V S S') → ℝ) → ℝ}
  {F : Fin (dimS m V S S') → (Fin (dimS m V S S') → ℝ) → ℝ}

/-- At a point where the state lies in `K` and `𝒰(z)` solves the symmetric system, the realized
generator is the coordinate time derivative of the state. -/
theorem genP_stU_eq
    (hAK : ∀ v ∈ K, ∀ j a (w : Fin (dimS m V S S') → ℝ), ∑ b, A j a b v * w b =
      κ (toS (princ (frameU (ginvOf (κ.symm v).1.1)) SM.D.Fr SM.Db.Fr j (ofP (κ.symm w)))) a)
    (hFK : ∀ v ∈ K, ∀ a, F a v = κ (toS (Fsys SM (ofP (κ.symm v)))) a)
    (z : Tuple m V S S') {x : ST 3} (hxK : κ (stateF SM z x) ∈ K) (hS : SymEqAt SM z x)
    (b : Fin (dimS m V S S')) :
    genP A F (stU κ SM z) (stP κ SM z) b x = κ (pd (stateF SM z) 0 x) b := by
  have hx : (fun c => stU κ SM z c x) ∈ K := hxK
  rw [genP_eq_actual_jet hAK hFK (stU κ SM z) (stP κ SM z) x hx b]
  have e1 : κ.symm (fun c => stU κ SM z c x) = stateF SM z x := by
    show κ.symm (κ (stateF SM z x)) = _
    exact κ.symm_apply_apply _
  have e2 : ∀ j : Fin 3, κ.symm (fun c => stP κ SM z c j x) = pd (stateF SM z) j.succ x := by
    intro j
    show κ.symm (κ (pd (stateF SM z) j.succ x)) = _
    exact κ.symm_apply_apply _
  simp only [e1, e2]
  have hS' := congrArg (fun w => κ w b) hS
  simp only [map_add, map_sum, Pi.add_apply, Finset.sum_apply] at hS'
  have e3 : ∀ j : Fin 3, κ (toS (princ (frameU (ginvOf (stateF SM z x).1.1)) SM.D.Fr SM.Db.Fr j
      (ofP (pd (stateF SM z) j.succ x)))) b =
      κ (princL SM (stateF SM z x) j (pd (stateF SM z) j.succ x)) b := fun j => rfl
  simp only [e3]
  have e4 : κ (toS (Fsys SM (ofP (stateF SM z x)))) b = κ (toP (Fsys SM (ofP (stateF SM z x)))) b :=
    rfl
  rw [e4, ← hS']
  ring

/-- **A tuple whose actual-jet state solves the independent symmetric system on
`(-ε, ε) × 𝕋³` with states in `K` gives a classical two-sided solution of the realized system**
(its own data at `t = 0`). -/
theorem twoSided_of_symEq
    (hAK : ∀ v ∈ K, ∀ j a (w : Fin (dimS m V S S') → ℝ), ∑ b, A j a b v * w b =
      κ (toS (princ (frameU (ginvOf (κ.symm v).1.1)) SM.D.Fr SM.Db.Fr j (ofP (κ.symm w)))) a)
    (hFK : ∀ v ∈ K, ∀ a, F a v = κ (toS (Fsys SM (ofP (κ.symm v)))) a)
    (z : Tuple m V S S') {ε : ℝ} (hSym : ∀ y ∈ openSlab (-ε) ε, SymEqAt SM z y)
    (hK : ∀ y ∈ openSlab (-ε) ε, κ (stateF SM z y) ∈ K) :
    KatoGalerkin.TwoSidedSol A F (stU κ SM z) ε (stU κ SM z) (stP κ SM z) where
  contU b := (contDiff_stU κ SM z b).continuous
  contP b i := by
    have : stP κ SM z b i = fun y => coordL κ b (pd (stateF SM z) i.succ y) := rfl
    rw [this]
    exact (coordL κ b).continuous.comp
      (SobolevOpen.continuous_pd ((contDiff_stateF SM z).of_le (by simp)) i.succ)
  perU b k x := by
    show κ (stateF SM z (x + sshift k)) b = κ (stateF SM z x) b
    rw [isSPeriodic_stateF SM z k x]
  perP b i k x := by
    show κ (pd (stateF SM z) i.succ (x + sshift k)) b = κ (pd (stateF SM z) i.succ x) b
    rw [isSPeriodic_pd' (isSPeriodic_stateF SM z) i.succ k x]
  init _ _ := rfl
  space b i x := by
    have hd : DifferentiableAt ℝ (stU κ SM z b) x :=
      (contDiff_stU κ SM z b).differentiable (by simp) x
    have h := hasDerivAt_line0 hd i.succ
    rw [pd_stU] at h
    exact h
  time b t ht y := by
    set x : ST 3 := Fin.cons t y with hxdef
    have hx : x ∈ openSlab (-ε) ε := by simpa [openSlab, hxdef] using ht
    have hS := hSym x hx
    rw [genP_stU_eq hAK hFK z (hK x hx) hS b]
    have hd : DifferentiableAt ℝ (stU κ SM z b) x :=
      (contDiff_stU κ SM z b).differentiable (by simp) x
    have h := hasDerivAt_line0 hd 0
    rw [pd_stU] at h
    have e : (fun s : ℝ => stU κ SM z b (x + s • ev 0)) =
        fun s => stU κ SM z b (Fin.cons (t + s) y) := by
      funext s
      rw [KatoGalerkin.cons_line_zero]
      simp [hxdef]
    rw [e] at h
    have h2 : HasDerivAt (fun s : ℝ => stU κ SM z b (Fin.cons (t + (s - t)) y))
        (κ (pd (stateF SM z) 0 x) b) t := by
      have := HasDerivAt.comp_sub_const t t (f := fun s => stU κ SM z b (Fin.cons (t + s) y))
        (by rw [sub_self]; exact h)
      exact this
    simpa using h2

/-- **A physical solution on `(-ε, ε) × 𝕋³` with states in `K` is a classical two-sided solution
of the realized symmetric system** (its own data at `t = 0`; `GenConstraint.symEqAt_of_physical`). -/
theorem twoSided_of_physical
    (hAK : ∀ v ∈ K, ∀ j a (w : Fin (dimS m V S S') → ℝ), ∑ b, A j a b v * w b =
      κ (toS (princ (frameU (ginvOf (κ.symm v).1.1)) SM.D.Fr SM.Db.Fr j (ofP (κ.symm w)))) a)
    (hFK : ∀ v ∈ K, ∀ a, F a v = κ (toS (Fsys SM (ofP (κ.symm v)))) a)
    (z : Tuple m V S S') {ε : ℝ} (hP : IsPhysicalOn SM z (openSlab (-ε) ε))
    (hK : ∀ y ∈ openSlab (-ε) ε, κ (stateF SM z y) ∈ K) :
    KatoGalerkin.TwoSidedSol A F (stU κ SM z) ε (stU κ SM z) (stP κ SM z) :=
  twoSided_of_symEq hAK hFK z
    (fun _ hy => symEqAt_of_physical SM z (isOpen_openSlab _ _) hP hy) hK

/-- Two-sided solutions only see their data at `t = 0`. -/
theorem twoSided_congr_data {d n : ℕ} {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ}
    {F : Fin n → (Fin n → ℝ) → ℝ} {U₀ W₀ : Fin n → ST d → ℝ} {T : ℝ} {U : Fin n → ST d → ℝ}
    {P : Fin n → Fin d → ST d → ℝ} (h : KatoGalerkin.TwoSidedSol A F U₀ T U P)
    (h0 : ∀ b y, U₀ b (Fin.cons 0 y) = W₀ b (Fin.cons 0 y)) :
    KatoGalerkin.TwoSidedSol A F W₀ T U P where
  contU := h.contU
  contP := h.contP
  perU := h.perU
  perP := h.perP
  init b y := (h.init b y).trans (h0 b y)
  space := h.space
  time := h.time

/-- **Uniqueness identification** (`lem:generated-physical-identification`, "uniqueness for the
symmetric system therefore identifies the independent solution with those actual jets on their
common local interval"): if `z` is a physical solution on `(-ε, ε) × 𝕋³` with states in the chart
margin `K`, then every classical two-sided solution of the realized symmetric system on `(-T, T)`
with the same data at `t = 0` is the actual-jet state of `z` on `[0, t₁] × 𝕋³` for every
`0 < t₁ < min(T, ε)`; in particular its head fields are the physical fields of `z` there. -/
theorem kato_eq_physical_state (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b))
    (hsym : ∀ i a b v, A i a b v = A i b a v) (hF : ∀ a, ContDiff ℝ ∞ (F a))
    (hAK : ∀ v ∈ K, ∀ j a (w : Fin (dimS m V S S') → ℝ), ∑ b, A j a b v * w b =
      κ (toS (princ (frameU (ginvOf (κ.symm v).1.1)) SM.D.Fr SM.Db.Fr j (ofP (κ.symm w)))) a)
    (hFK : ∀ v ∈ K, ∀ a, F a v = κ (toS (Fsys SM (ofP (κ.symm v)))) a)
    (z : Tuple m V S S') {ε : ℝ} (hP : IsPhysicalOn SM z (openSlab (-ε) ε))
    (hK : ∀ y ∈ openSlab (-ε) ε, κ (stateF SM z y) ∈ K)
    {U₀ : Fin (dimS m V S S') → ST 3 → ℝ}
    (h0 : ∀ b y, U₀ b (Fin.cons 0 y) = stU κ SM z b (Fin.cons 0 y))
    {T : ℝ} {U : Fin (dimS m V S S') → ST 3 → ℝ} {P : Fin (dimS m V S S') → Fin 3 → ST 3 → ℝ}
    (hU : KatoGalerkin.TwoSidedSol A F U₀ T U P) {t₁ : ℝ} (ht₁ : 0 < t₁) (hT : t₁ < T)
    (hε : t₁ < ε) : ∀ x ∈ slab 0 t₁, ∀ b, U b x = κ (stateF SM z x) b :=
  KatoStab.twoSided_unique hA hsym hF hU
    (twoSided_congr_data (twoSided_of_physical hAK hFK z hP hK) fun b y => (h0 b y).symm) ht₁ hT hε

end TwoSided

/-! ### The physical-Cauchy input and the derived analytic-core interface -/

section Interface

variable (SM : SMData (MatLie m) V S S') (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ))
  (K : Set (Fin (dimS m V S S') → ℝ))

/-- **The physical-Cauchy clause of `ass:constrained-initial-solver`**, in physical terms: core
data are smooth and periodic, and for every `H^q` radius `R₀` there is one time `ε > 0` such that
every core datum of radius `≤ R₀` is the actual-jet state at `t = 0` of a **physical solution**
(`IsPhysicalOn`: vanishing Einstein, Yang–Mills, Higgs, Dirac residuals and harmonic defect) on
`(-ε, ε) × 𝕋³` whose states stay in the chart margin `K` ("locally unique analytic solutions with
continuation controlled by the declared Sobolev bounds and field-chart margins"; analyticity
itself is not used).  Nothing about the symmetric system is assumed. -/
structure PhysicalCauchyCore (q : ℕ) (Core : (Fin (dimS m V S S') → ST 3 → ℝ) → Prop) : Prop where
  core_smooth : ∀ W, Core W → (∀ b, ContDiff ℝ ∞ (W b)) ∧ ∀ b, IsSPeriodic (W b)
  germ : ∀ R₀ : ℝ, 0 ≤ R₀ → ∃ ε > 0, ∀ W, Core W → energyQ q W 0 ≤ R₀ ^ 2 →
    ∃ z : Tuple m V S S', IsPhysicalOn SM z (openSlab (-ε) ε) ∧
      (∀ y ∈ openSlab (-ε) ε, κ (stateF SM z y) ∈ K) ∧
      ∀ b y, stU κ SM z b (Fin.cons 0 y) = W b (Fin.cons 0 y)

/-- **Density of the core** in the constrained class with a uniform `H^q` bound (the
approximation step of the manuscript's proof). -/
def CoreDense (q : ℕ) (Constrained Core : (Fin (dimS m V S S') → ST 3 → ℝ) → Prop) : Prop :=
  ∀ U₀, Constrained U₀ → ∃ W : ℕ → Fin (dimS m V S S') → ST 3 → ℝ, (∀ k, Core (W k)) ∧
    (∀ k, energyQ q (W k) 0 ≤ energyQ q U₀ 0 + 1) ∧
    Tendsto (fun k => KatoStab.dataDist (W k) U₀) atTop (𝓝 0)

/-- **The first jets of physical solutions** (in the coordinates `κ`): `(κ𝒰(z)(y), κ∂𝒰(z)(y))`
for a tuple `z` physical on an open slab `(-ε, ε) × 𝕋³` containing `y`. -/
def physJets : Set ((Fin (dimS m V S S') → ℝ) × (Fin (3 + 1) → Fin (dimS m V S S') → ℝ)) :=
  {w | ∃ (z : Tuple m V S S') (ε : ℝ) (y : ST 3), IsPhysicalOn SM z (openSlab (-ε) ε) ∧
    y ∈ openSlab (-ε) ε ∧ w = (κ (stateF SM z y), fun μ => κ (pd (stateF SM z) μ y))}

theorem jet_stU_mem (z : Tuple m V S S') {ε : ℝ} (hP : IsPhysicalOn SM z (openSlab (-ε) ε))
    {y : ST 3} (hy : y ∈ openSlab (-ε) ε) :
    ((fun b => stU κ SM z b y), fun μ b => pd (stU κ SM z b) μ y) ∈ physJets SM κ := by
  refine ⟨z, ε, y, hP, hy, Prod.ext rfl ?_⟩
  funext μ b
  exact pd_stU κ SM z b μ y

variable {SM κ K}

/-- **`KatoStab.AnalyticCoreContinuation` is derived from the physical-Cauchy clause**: under
`PhysicalCauchyCore` and `CoreDense`, the named input of `KatoStab.kato_physical_identification`
holds for the realized system and every family of first-jet identities `Φ_j` vanishing on the
first jets of physical solutions: the germ of a core datum is the actual-jet state of its physical
solution, which solves the symmetric system (`twoSided_of_physical`) and satisfies the
identities. -/
theorem analyticCoreContinuation_of_physicalCauchy {ι : Type*}
    {A : Fin 3 → Fin (dimS m V S S') → Fin (dimS m V S S') → (Fin (dimS m V S S') → ℝ) → ℝ}
    {F : Fin (dimS m V S S') → (Fin (dimS m V S S') → ℝ) → ℝ}
    (hAK : ∀ v ∈ K, ∀ j a (w : Fin (dimS m V S S') → ℝ), ∑ b, A j a b v * w b =
      κ (toS (princ (frameU (ginvOf (κ.symm v).1.1)) SM.D.Fr SM.Db.Fr j (ofP (κ.symm w)))) a)
    (hFK : ∀ v ∈ K, ∀ a, F a v = κ (toS (Fsys SM (ofP (κ.symm v)))) a)
    {Φ : ι → (Fin (dimS m V S S') → ℝ) × (Fin (3 + 1) → Fin (dimS m V S S') → ℝ) → ℝ}
    (hΦ : ∀ j, ∀ w ∈ physJets SM κ, Φ j w = 0) {q : ℕ}
    {Constrained Core : (Fin (dimS m V S S') → ST 3 → ℝ) → Prop}
    (hPC : PhysicalCauchyCore SM κ K q Core) (hD : CoreDense q Constrained Core) :
    KatoStab.AnalyticCoreContinuation A F q Constrained Core Φ where
  core_smooth := hPC.core_smooth
  approx := hD
  germ R₀ hR₀ := by
    obtain ⟨ε, hε, h⟩ := hPC.germ R₀ hR₀
    refine ⟨ε, hε, fun W hW hE => ?_⟩
    obtain ⟨z, hP, hK, h0⟩ := h W hW hE
    refine ⟨stU κ SM z, stP κ SM z,
      twoSided_congr_data (twoSided_of_physical hAK hFK z hP hK) h0, fun x hx j => ?_⟩
    have hx' : x ∈ openSlab (-ε) ε := slab_subset_openSlab (by linarith) (by linarith) hx
    exact hΦ j _ (jet_stU_mem SM κ z hP hx')

end Interface

/-! ### Physical identification under the physical-Cauchy clause -/

section Main

variable {SM : SMData (MatLie m) V S S'} {bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ}
  {bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ} {bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ}

/-- **`lem:generated-physical-identification` for the actual-jet system under the physical-Cauchy
clause of `ass:constrained-initial-solver`** (`Σ = 𝕋³`).  For theory data with smooth sources and
forms with the Clifford unitarity relations there are Euclidean coordinates `κ` such that for
every compact chart margin `K` the realized symmetric coefficient maps `A^j, F` (the actual-jet
operators on `K`) satisfy: for every `H^q` radius `R₀` there is a Kato time `T > 0` (depending only
on `R₀`) such that, whenever the physical-Cauchy clause `PhysicalCauchyCore` holds for a core
which is dense in the constrained class (`CoreDense`), there is `t₁ > 0` such that every
constrained smooth periodic datum with `‖U₀‖_{H^q} ≤ R₀` has a two-sided Kato solution on
`(-T, T) × 𝕋³` whose first jet `(U, ∂U)` lies, at every point of `[0, t₁] × 𝕋³`, in the closure
of the first jets of physical solutions (`physJets`).  Consequently every continuous first-jet
identity valid for physical solutions (defining-jet identities, Einstein and matter residuals,
Gauss and harmonic constraints written on the first jets) holds for the Kato solution on
`[0, t₁] × 𝕋³` (`physical_identities_of_mem_closure`). -/
theorem generated_physical_identification_of_physicalCauchy (hS : SMSmooth SM)
    (hU : UnitaryForms SM bG bV bS bS') {mm r : ℕ} (hm : (3 : ℝ) / 2 < mm) (hq : 2 * mm ≤ r + 1)
    (hq2 : mm + 2 ≤ r + 1) :
    ∃ κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ),
      (∀ v w, ipP bG bV bS bS' (κ.symm v) (κ.symm w) = ∑ i, v i * w i) ∧
      ∀ K : Set (Fin (dimS m V S S') → ℝ), IsCompact K → (∀ v ∈ K, MetChart (κ.symm v).1) →
      ∃ (A : Fin 3 → Fin (dimS m V S S') → Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ) (F : Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ),
        (∀ i a b, ContDiff ℝ ∞ (A i a b)) ∧ (∀ i a b v, A i a b v = A i b a v) ∧
        (∀ a, ContDiff ℝ ∞ (F a)) ∧
        (∀ v ∈ K, ∀ j a (w : Fin (dimS m V S S') → ℝ), ∑ b, A j a b v * w b =
          κ (toS (princ (frameU (ginvOf (κ.symm v).1.1)) SM.D.Fr SM.Db.Fr j
            (ofP (κ.symm w)))) a) ∧
        (∀ v ∈ K, ∀ a, F a v = κ (toS (Fsys SM (ofP (κ.symm v)))) a) ∧
        ∀ R₀ : ℝ, 0 ≤ R₀ → ∃ T > 0, ∀ Constrained Core : (Fin (dimS m V S S') → ST 3 → ℝ) → Prop,
          PhysicalCauchyCore SM κ K (r + 1) Core → CoreDense (r + 1) Constrained Core →
          ∃ t₁ > 0, ∀ U₀ : Fin (dimS m V S S') → ST 3 → ℝ, Constrained U₀ →
            (∀ b, ContDiff ℝ ∞ (U₀ b)) → (∀ b, IsSPeriodic (U₀ b)) →
            energyQ (r + 1) U₀ 0 ≤ R₀ ^ 2 →
            ∃ (U : Fin (dimS m V S S') → ST 3 → ℝ)
              (P : Fin (dimS m V S S') → Fin 3 → ST 3 → ℝ),
              KatoGalerkin.TwoSidedSol A F U₀ T U P ∧
              ∀ x ∈ slab 0 t₁, ((fun c => U c x), fun μ c => pd (U c) μ x) ∈
                closure (physJets SM κ) := by
  obtain ⟨κ, hκ, hreal⟩ := actual_jet_kato_realization hS hU
  refine ⟨κ, hκ, fun K hK hKc => ?_⟩
  obtain ⟨A, F, hA, hsym, hF, hAK, hFK⟩ := hreal K hK hKc
  refine ⟨A, F, hA, hsym, hF, hAK, hFK, fun R₀ hR₀ => ?_⟩
  set Φ : Unit → (Fin (dimS m V S S') → ℝ) × (Fin (3 + 1) → Fin (dimS m V S S') → ℝ) → ℝ :=
    fun _ w => Metric.infDist w (physJets SM κ) with hΦdef
  have hΦc : ∀ j, Continuous (Φ j) := fun _ => Metric.continuous_infDist_pt _
  have hΦ0 : ∀ j, ∀ w ∈ physJets SM κ, Φ j w = 0 := fun _ w hw => Metric.infDist_zero_of_mem hw
  obtain ⟨T, hT, hmain⟩ := KatoStab.kato_physical_identification (d := 3) hm hq hq2 hA hsym hF
    hΦc hR₀
  refine ⟨T, hT, fun Constrained Core hPC hD => ?_⟩
  obtain ⟨t₁, ht₁, h⟩ := hmain Constrained Core
    (analyticCoreContinuation_of_physicalCauchy hAK hFK hΦ0 hPC hD)
  refine ⟨t₁, ht₁, fun U₀ hC hU₀ hUp hE => ?_⟩
  obtain ⟨U, P, hsol, hphys⟩ := h U₀ hC hU₀ hUp hE
  -- the set of physical jets is nonempty (the core is nonempty)
  have hne : (physJets SM κ).Nonempty := by
    obtain ⟨W, hWc, -, -⟩ := hD U₀ hC
    obtain ⟨ε, hε, hg⟩ := hPC.germ (Real.sqrt |energyQ (r + 1) (W 0) 0|) (Real.sqrt_nonneg _)
    obtain ⟨z, hP, -, -⟩ := hg (W 0) (hWc 0) (by
      rw [Real.sq_sqrt (abs_nonneg _)]; exact le_abs_self _)
    have hy : (Fin.cons 0 0 : ST 3) ∈ openSlab (-ε) ε := by
      show (0 : ℝ) ∈ Set.Ioo (-ε) ε
      exact ⟨by linarith, hε⟩
    exact ⟨_, jet_stU_mem SM κ z hP hy⟩
  refine ⟨U, P, hsol, fun x hx => ?_⟩
  rw [Metric.mem_closure_iff_infDist_zero hne]
  exact hphys x hx ()

/-- Every continuous first-jet identity valid on the first jets of physical solutions holds on
their closure. -/
theorem physical_identities_of_mem_closure {SM : SMData (MatLie m) V S S'}
    {κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ)}
    {Φ : (Fin (dimS m V S S') → ℝ) × (Fin (3 + 1) → Fin (dimS m V S S') → ℝ) → ℝ}
    (hΦc : Continuous Φ) (hΦ : ∀ w ∈ physJets SM κ, Φ w = 0) {w}
    (hw : w ∈ closure (physJets SM κ)) : Φ w = 0 := by
  have : physJets SM κ ⊆ Φ ⁻¹' {0} := fun w hw => hΦ w hw
  exact (closure_minimal this (isClosed_singleton.preimage hΦc)) hw

end Main

/-! ### Non-vacuity: the flat vacuum -/

section NonVacuity

open CoupledBootstrap.FlatVacuum

theorem isSPeriodic_stU (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ))
    (SM : SMData (MatLie m) V S S') (z : Tuple m V S S') (b : Fin (dimS m V S S')) :
    IsSPeriodic (stU κ SM z b) := fun k x => by
  show κ (stateF SM z (x + sshift k)) b = κ (stateF SM z x) b
  rw [isSPeriodic_stateF SM z k x]

/-- The flat-vacuum core (the actual-jet state of the flat vacuum). -/
def flatCore (κ : StateP 1 (MatLie 1) PUnit.{1} PUnit.{1} ≃ₗ[ℝ]
    (Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ℝ)) :
    (Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ST 3 → ℝ) → Prop :=
  fun W => W = stU κ trivSMM flat

/-- **Non-vacuity of `PhysicalCauchyCore`**: the flat vacuum (one physical solution, existing for
all times, states equal to the Minkowski state). -/
theorem physicalCauchyCore_flat (κ : StateP 1 (MatLie 1) PUnit.{1} PUnit.{1} ≃ₗ[ℝ]
    (Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ℝ)) (q : ℕ) :
    PhysicalCauchyCore trivSMM κ {κ minkState} q (flatCore κ) where
  core_smooth W hW := by
    subst hW
    exact ⟨contDiff_stU κ trivSMM flat, isSPeriodic_stU κ trivSMM flat⟩
  germ _ _ := ⟨1, one_pos, fun W hW _ => by
    subst hW
    refine ⟨flat, fun y _ => flat_isPhysicalOn y trivial, fun y _ => ?_, fun _ _ => rfl⟩
    rw [stateF_flat]
    exact Set.mem_singleton _⟩

theorem coreDense_flat (κ : StateP 1 (MatLie 1) PUnit.{1} PUnit.{1} ≃ₗ[ℝ]
    (Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ℝ)) (q : ℕ) :
    CoreDense q (flatCore κ) (flatCore κ) := fun U₀ hU₀ =>
  ⟨fun _ => U₀, fun _ => hU₀, fun _ => le_add_of_nonneg_right zero_le_one, by
    simp only [KatoStab.dataDist_self]; exact tendsto_const_nhds⟩

/-- **Non-vacuity of `generated_physical_identification_of_physicalCauchy`** (and of
`kato_eq_physical_state`): for the vanishing-coupling data `trivSMM` with the Frobenius forms, the
chart margin `{Minkowski state}` and the flat-vacuum core, the hypotheses hold and the conclusion
is produced for the flat datum. -/
example : ∃ (κ : StateP 1 (MatLie 1) PUnit.{1} PUnit.{1} ≃ₗ[ℝ]
      (Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ℝ))
    (A : Fin 3 → Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) →
      Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) →
        (Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ℝ) → ℝ)
    (F : Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) →
      (Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ℝ) → ℝ) (T t₁ : ℝ)
    (U : Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ST 3 → ℝ)
    (P : Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → Fin 3 → ST 3 → ℝ),
    0 < T ∧ 0 < t₁ ∧ KatoGalerkin.TwoSidedSol A F (stU κ trivSMM flat) T U P ∧
      ∀ x ∈ slab 0 t₁, ((fun c => U c x), fun μ c => pd (U c) μ x) ∈
        closure (physJets trivSMM κ) := by
  obtain ⟨κ, -, h⟩ := generated_physical_identification_of_physicalCauchy trivSMM_smooth
    unitaryForms_triv (mm := 2) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨A, F, -, -, -, -, -, h2⟩ := h {κ minkState} isCompact_singleton (by
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    rw [LinearEquiv.symm_apply_apply]
    exact metChart_mink)
  obtain ⟨T, hT, h3⟩ := h2 (Real.sqrt |energyQ (3 + 1) (stU κ trivSMM flat) 0|)
    (Real.sqrt_nonneg _)
  obtain ⟨t₁, ht₁, h4⟩ := h3 (flatCore κ) (flatCore κ) (physicalCauchyCore_flat κ _)
    (coreDense_flat κ _)
  obtain ⟨U, P, hsol, hjet⟩ := h4 (stU κ trivSMM flat) rfl (contDiff_stU κ trivSMM flat)
    (isSPeriodic_stU κ trivSMM flat) (by rw [Real.sq_sqrt (abs_nonneg _)]; exact le_abs_self _)
  exact ⟨κ, A, F, T, t₁, U, P, hT, ht₁, hsol, hjet⟩

end NonVacuity

end RenewalGeometry.GenPhysId
