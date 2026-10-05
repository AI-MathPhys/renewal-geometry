/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.SymmetricHyperbolicEnergy
import RenewalGeometry.Continuum.TorusWaveEnergyForced

/-!
# Linear `H^k` wave energy estimates on `[0, T] × 𝕋^d` with an `L¹`-in-time source

Generic infrastructure (no renewal notions) for `thm:hyperbolic` (`eq:hyperbolic-energy`) of the
Einstein–Standard-Model action-closure manuscript.

Space-time is `ℝ^{1+d} = Fin (d+1) → ℝ` (time coordinate `0`, points `Fin.cons t y`); fields are
`ℤ^d`-periodic in space (`SymHypEnergy.IsSPeriodic`, i.e. functions on `ℝ × 𝕋^d`); spatial integrals
are over the unit cube `[0,1]^d`.  Partial derivatives are `SobolevOpen.pd`.

## The `L²` level (`L2Hyp`)

A system of second-order equations with scalar principal part in normal form,
`∂ₜ²u_b = 2βⁱ ∂ᵢ∂ₜu_b + γ^{ij} ∂ᵢ∂ⱼu_b + L₀,b + F_b` on `[0, T] × 𝕋^d`, with `γ` symmetric and
uniformly positive, `|∂ᵢβⁱ|, |∂ₜγ^{ij}|, |∂ᵢγ^{ij}| ≤ M`, a lower-order part with
`Σ_b L₀,b² ≤ m(t)² Σ_b(|∂ₜu_b|² + |∇u_b|² + u_b²)` and a forcing `F`.

* `L2Hyp.hasDerivAt_energy`, `L2Hyp.integral_densT_eq` — the energy identity (differentiation
  under the integral, integration by parts on the torus `PeriodicCube.integral_pd_eq_zero`).
* **`L2Hyp.sqrt_energy_le`** — `√E(t) ≤ (√E(0) + c^{-1/2}∫₀ᵗ ‖F‖_{L²}) exp(½∫₀ᵗ k)`,
  `k = ((d+1)²M + 1 + 2m)/c`, `c = min(λ, 1)`; `L2Hyp.sqrt_energy_le_of_forcing` when
  `‖F‖_{L²} ≤ a√E + σ`.

## Commuting derivatives (`prolong`) and the `H^k` estimate

`WaveSys` records the coefficients `(β, γ, A, B, C)` of a linear system whose lower-order part is
`Σ_c (A_bc ∂ₜu_c + Bⁱ_bc ∂ᵢu_c + C_bc u_c)`.  **`WaveSys.prolong`** is the system satisfied by
`V = (u, ∂₁u, …, ∂_d u)` (index type `ι × Option (Fin d)`): differentiating the equation along
`∂_k` (Schwarz and Leibniz rules, `SysHyp.prolong_eqn`) produces the commutator terms
`2∂_kβⁱ ∂ᵢ∂ₜu + ∂_kγ^{ij}∂ᵢ∂ⱼu` and the derivatives of the lower-order coefficients, which are
again first-order in `V`.

* `SysHyp S u F T λ M r` — smooth spatially periodic fields, the equation on the slab, `γ`
  symmetric and `λ`-coercive, all *spatial* derivatives of order `≤ r` of the coefficients bounded
  by `M` (`DerivBound`, an `L^∞_t W^{r,∞}_x` bound) and `|∂ⱼβⁱ|, |∂_μγ^{ij}| ≤ M`.
* **`SysHyp.prolong`** — `SysHyp S u F T λ M (r+1) → SysHyp (prolong S) (pU u) (pU F) T λ (3M) r`;
  `SysHyp.prolongK` — the `k`-fold version (index type `PIdx d k ι`, constant `3^k M`).
* **`hk_energy`** — the order-`k` energy `E_k = energyK k` (the wave energy of the `k`-fold
  prolongation `pUK k u`, i.e. `Σ_w E(∂^w u)` over words `w ∈ Option (Fin d)^k`) satisfies
  `√E_k(t) ≤ (√E_k(0) + c^{-1/2}∫₀ᵗ ‖F(s)‖_{H^k}) exp(½∫₀ᵗ K_k)` for `SysHyp … k`, with an explicit
  `K_k` depending only on `d, |ι|, k, λ, M` (`‖F‖_{H^k} = normK k F`, the `L²` norm of the
  prolonged forcing).  `energyK_ge`: `E_k ≥ c ∫ (|∂ₜ∂^w u|² + |∇∂^w u|² + |∂^w u|²)` for every
  word `|w| ≤ k`, so `E_k` controls `‖u‖²_{H^{k+1}} + ‖∂ₜu‖²_{H^k}`.
* **`hk_energy_of_forcing`** (`eq:hyperbolic-energy`, abstract form) — when
  `‖F(t)‖_{H^k} ≤ a(t)√E_k(t) + σ(t)`:
  `√E_k(t) ≤ (√E_k(0) + c^{-1/2}∫₀ᵗ σ) exp(½∫₀ᵗ (K_k + 2c^{-1/2}a))`.
* **`energyK_tendsto_zero`** — for two-parameter families of difference systems with common
  constants, `∫₀ᵀ a_{h,j} ≤ A`, `E_k^{h,j}(0) → 0` and `∫₀ᵀ σ_{h,j} → 0`, the difference energies
  tend to zero uniformly on `[0, T]` (the convergence step of `thm:hyperbolic`).
* Non-vacuity: `flatSys_hyp` (constant coefficients, any order).
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.SlabWaveHk

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy

set_option linter.unusedSectionVars false

variable {d : ℕ}

/-- Space-time `ℝ^{1+d}`. -/
abbrev ST (d : ℕ) := Fin (d + 1) → ℝ

/-! ### Calculus on space-time -/

/-- **Symmetry of second partial derivatives** of a `C²` function. -/
theorem pd_pd_comm {f : ST d → ℝ} (hf : ContDiff ℝ 2 f) (μ ν : Fin (d + 1)) (x : ST d) :
    pd (pd f μ) ν x = pd (pd f ν) μ x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) x
  have hsymm := (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
  show fderiv ℝ (fun y => fderiv ℝ f y (Pi.single μ 1)) x (Pi.single ν 1) =
    fderiv ℝ (fun y => fderiv ℝ f y (Pi.single ν 1)) x (Pi.single μ 1)
  rw [fderiv_clm_apply hd (differentiableAt_const _), fderiv_clm_apply hd
    (differentiableAt_const _)]
  simp
  exact hsymm _ _

theorem contDiff_pd' {f : ST d → ℝ} {n : ℕ} (hf : ContDiff ℝ (n + 1) f) (μ : Fin (d + 1)) :
    ContDiff ℝ n (pd f μ) := by
  unfold pd
  exact (hf.fderiv_right (m := n) (by norm_cast)).clm_apply contDiff_const

theorem contDiff_pd_top {f : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (μ : Fin (d + 1)) :
    ContDiff ℝ ∞ (pd f μ) := by
  unfold pd
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem isSPeriodic_pd {f : ST d → ℝ} (hf : IsSPeriodic f) (μ : Fin (d + 1)) :
    IsSPeriodic (pd f μ) := fun k x => by
  unfold SobolevOpen.pd
  have h : (fun z => f (z + sshift k)) = f := funext fun z => hf k z
  rw [← fderiv_comp_add_right, h]

theorem isSPeriodic_mul {f g : ST d → ℝ} (hf : IsSPeriodic f) (hg : IsSPeriodic g) :
    IsSPeriodic (fun x => f x * g x) := fun k x => by simp only [hf k x, hg k x]

/-- **Integration by parts on the torus slice**: `∫_{[0,1]^d} ∂ᵢh(t, y) dy = 0`. -/
theorem integral_slice_pd_eq_zero {h : ST d → ℝ} (hh : ContDiff ℝ 1 h) (hper : IsSPeriodic h)
    (t : ℝ) (i : Fin d) : ∫ y in Icc (0 : Fin d → ℝ) 1, pd h i.succ (Fin.cons t y) = 0 := by
  have hs : ContDiff ℝ 1 (fun y : Fin d → ℝ => h (Fin.cons t y)) := hh.comp (contDiff_cons t)
  have e : ∀ y : Fin d → ℝ, pd h i.succ (Fin.cons t y) = pd (fun y => h (Fin.cons t y)) i y :=
    fun y => (pd_slice i ((hh.differentiable one_ne_zero) _)).symm
  simp only [e]
  exact integral_pd_eq_zero hs (hper.slice t) i

/-- The compact set `[0, T] × [0,1]^d` in space-time. -/
def box (T : ℝ) : Set (ST d) :=
  (fun p : ℝ × (Fin d → ℝ) => (Fin.cons p.1 p.2 : ST d)) '' (Icc 0 T ×ˢ Icc 0 1)

theorem isCompact_box (T : ℝ) : IsCompact (box (d := d) T) :=
  (isCompact_Icc.prod isCompact_Icc).image continuous_cons2

theorem cons_mem_box {T t : ℝ} (ht : t ∈ Icc 0 T) {y : Fin d → ℝ} (hy : y ∈ Icc 0 1) :
    (Fin.cons t y : ST d) ∈ box T :=
  ⟨(t, y), ⟨ht, hy⟩, rfl⟩

theorem integrableOn_slice {f : ST d → ℝ} (hf : Continuous f) (t : ℝ) :
    IntegrableOn (fun y : Fin d → ℝ => f (Fin.cons t y)) (Icc 0 1) :=
  integrableOn_cube_of_continuousOn (hf.comp (continuous_cons t)).continuousOn

theorem continuous_sliceInt {f : ST d → ℝ} (hf : Continuous f) :
    Continuous fun t => ∫ y in Icc (0 : Fin d → ℝ) 1, f (Fin.cons t y) := by
  have := continuous_parametric_integral_of_continuous (μ := (volume : Measure (Fin d → ℝ)))
    (f := fun t y => f (Fin.cons t y)) (hf.comp continuous_cons2) (isCompact_Icc (a := 0) (b := 1))
  exact this

/-! ### The `L²` energy of a forced wave system -/

variable {ι : Type*} [Fintype ι]

/-- The pointwise size `Σ_b (|∂ₜu_b|² + |∇u_b|² + u_b²)`. -/
def size (u : ι → ST d → ℝ) (x : ST d) : ℝ :=
  ∑ b, (pd (u b) 0 x ^ 2 + ∑ i : Fin d, pd (u b) i.succ x ^ 2 + u b x ^ 2)

/-- The energy density `Σ_b (|∂ₜu_b|² + γ^{ij}∂ᵢu_b∂ⱼu_b + u_b²)`. -/
def dens (γ : Fin d → Fin d → ST d → ℝ) (u : ι → ST d → ℝ) (x : ST d) : ℝ :=
  ∑ b, (pd (u b) 0 x ^ 2 + ∑ i : Fin d, ∑ j : Fin d, γ i j x * pd (u b) i.succ x * pd (u b) j.succ x +
    u b x ^ 2)

/-- The energy `E(t) = ∫_{[0,1]^d} dens(t, y) dy`. -/
def energy (γ : Fin d → Fin d → ST d → ℝ) (u : ι → ST d → ℝ) (t : ℝ) : ℝ :=
  ∫ y in Icc (0 : Fin d → ℝ) 1, dens γ u (Fin.cons t y)

/-- The `L²([0,1]^d)` norm of a field at time `t`. -/
def l2norm (F : ι → ST d → ℝ) (t : ℝ) : ℝ :=
  Real.sqrt (∫ y in Icc (0 : Fin d → ℝ) 1, ∑ b, F b (Fin.cons t y) ^ 2)

/-- The time derivative of the density. -/
def densT (γ : Fin d → Fin d → ST d → ℝ) (u : ι → ST d → ℝ) (x : ST d) : ℝ :=
  ∑ b, (2 * pd (u b) 0 x * pd (pd (u b) 0) 0 x +
    ∑ i : Fin d, ∑ j : Fin d, (pd (γ i j) 0 x * pd (u b) i.succ x * pd (u b) j.succ x +
      γ i j x * pd (pd (u b) 0) i.succ x * pd (u b) j.succ x +
      γ i j x * pd (u b) i.succ x * pd (pd (u b) 0) j.succ x) +
    2 * u b x * pd (u b) 0 x)

/-- The density derivative after the equation and the integrations by parts. -/
def densG (β : Fin d → ST d → ℝ) (γ : Fin d → Fin d → ST d → ℝ) (u L : ι → ST d → ℝ)
    (x : ST d) : ℝ :=
  ∑ b, (-(2 * ∑ i : Fin d, pd (β i) i.succ x * pd (u b) 0 x ^ 2) -
    2 * ∑ i : Fin d, ∑ j : Fin d, pd (γ i j) i.succ x * pd (u b) 0 x * pd (u b) j.succ x +
    ∑ i : Fin d, ∑ j : Fin d, pd (γ i j) 0 x * pd (u b) i.succ x * pd (u b) j.succ x +
    2 * u b x * pd (u b) 0 x + 2 * pd (u b) 0 x * L b x)

/-- The hypotheses of the `L²` energy estimate on `[0, T] × 𝕋^d`. -/
structure L2Hyp (β : Fin d → ST d → ℝ) (γ : Fin d → Fin d → ST d → ℝ) (u L₀ F : ι → ST d → ℝ)
    (m : ℝ → ℝ) (T lam M : ℝ) : Prop where
  cu : ∀ b, ContDiff ℝ 2 (u b)
  cβ : ∀ i, ContDiff ℝ 1 (β i)
  cγ : ∀ i j, ContDiff ℝ 1 (γ i j)
  cL : ∀ b, Continuous (L₀ b)
  cF : ∀ b, Continuous (F b)
  cm : Continuous m
  pu : ∀ b, IsSPeriodic (u b)
  pβ : ∀ i, IsSPeriodic (β i)
  pγ : ∀ i j, IsSPeriodic (γ i j)
  eqn : ∀ x : ST d, x 0 ∈ Icc 0 T → ∀ b, pd (pd (u b) 0) 0 x =
    2 * ∑ i : Fin d, β i x * pd (pd (u b) 0) i.succ x +
      ∑ i : Fin d, ∑ j : Fin d, γ i j x * pd (pd (u b) j.succ) i.succ x + L₀ b x + F b x
  γ_symm : ∀ i j x, γ i j x = γ j i x
  coer : ∀ x : ST d, x 0 ∈ Icc 0 T → ∀ ξ : Fin d → ℝ,
    lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, γ i j x * ξ i * ξ j
  bβ : ∀ x : ST d, x 0 ∈ Icc 0 T → ∀ i, |pd (β i) i.succ x| ≤ M
  bγt : ∀ x : ST d, x 0 ∈ Icc 0 T → ∀ i j, |pd (γ i j) 0 x| ≤ M
  bγx : ∀ x : ST d, x 0 ∈ Icc 0 T → ∀ i j, |pd (γ i j) i.succ x| ≤ M
  m_nonneg : ∀ t, 0 ≤ m t
  M_nonneg : 0 ≤ M
  bL : ∀ x : ST d, x 0 ∈ Icc 0 T → ∑ b, L₀ b x ^ 2 ≤ m (x 0) ^ 2 * size u x

namespace L2Hyp

variable {β : Fin d → ST d → ℝ} {γ : Fin d → Fin d → ST d → ℝ} {u L₀ F : ι → ST d → ℝ}
  {m : ℝ → ℝ} {T lam M : ℝ}

theorem cpd (h : L2Hyp β γ u L₀ F m T lam M) (b : ι) (μ : Fin (d + 1)) :
    ContDiff ℝ 1 (pd (u b) μ) := contDiff_pd' (n := 1) (h.cu b) μ

theorem continuous_pd (h : L2Hyp β γ u L₀ F m T lam M) (b : ι) (μ : Fin (d + 1)) :
    Continuous (pd (u b) μ) := (h.cpd b μ).continuous

theorem continuous_pd2 (h : L2Hyp β γ u L₀ F m T lam M) (b : ι) (μ ν : Fin (d + 1)) :
    Continuous (pd (pd (u b) μ) ν) := (contDiff_pd' (n := 0) (h.cpd b μ) ν).continuous

theorem continuous_pdβ (h : L2Hyp β γ u L₀ F m T lam M) (i : Fin d) (μ : Fin (d + 1)) :
    Continuous (pd (β i) μ) := (contDiff_pd' (n := 0) (h.cβ i) μ).continuous

theorem continuous_pdγ (h : L2Hyp β γ u L₀ F m T lam M) (i j : Fin d) (μ : Fin (d + 1)) :
    Continuous (pd (γ i j) μ) := (contDiff_pd' (n := 0) (h.cγ i j) μ).continuous

theorem continuous_dens (h : L2Hyp β γ u L₀ F m T lam M) : Continuous (dens γ u) := by
  unfold dens
  have := fun b => (h.cu b).continuous; have := fun b μ => h.continuous_pd b μ
  have := fun i j => (h.cγ i j).continuous
  fun_prop

theorem continuous_densT (h : L2Hyp β γ u L₀ F m T lam M) : Continuous (densT γ u) := by
  unfold densT
  have := fun b => (h.cu b).continuous; have := fun b μ => h.continuous_pd b μ
  have := fun b μ ν => h.continuous_pd2 b μ ν
  have := fun i j => (h.cγ i j).continuous; have := fun i j μ => h.continuous_pdγ i j μ
  fun_prop

theorem continuous_densG (h : L2Hyp β γ u L₀ F m T lam M) :
    Continuous (densG β γ u (fun b x => L₀ b x + F b x)) := by
  unfold densG
  have := fun b => (h.cu b).continuous; have := fun b μ => h.continuous_pd b μ
  have := fun i μ => h.continuous_pdβ i μ; have := fun i j μ => h.continuous_pdγ i j μ
  have := h.cL; have := h.cF
  fun_prop

theorem continuous_size (h : L2Hyp β γ u L₀ F m T lam M) : Continuous (size u) := by
  unfold size
  have := fun b => (h.cu b).continuous; have := fun b μ => h.continuous_pd b μ
  fun_prop

/-- The time derivative of the density along time lines. -/
theorem hasDerivAt_dens (h : L2Hyp β γ u L₀ F m T lam M) (t : ℝ) (y : Fin d → ℝ) :
    HasDerivAt (fun s => dens γ u (Fin.cons s y)) (densT γ u (Fin.cons t y)) t := by
  have dt := fun {f : ST d → ℝ} (hf : ContDiff ℝ 1 f) =>
    hasDerivAt_time (f := f) (t := t) y ((hf.differentiable one_ne_zero) _)
  unfold dens densT
  refine HasDerivAt.fun_sum fun b _ => ?_
  have hut := dt (h.cpd b 0)
  have hu := dt ((h.cu b).of_le (by norm_num))
  have hux : ∀ i : Fin d, HasDerivAt (fun s => pd (u b) i.succ (Fin.cons s y))
      (pd (pd (u b) 0) i.succ (Fin.cons t y)) t := fun i => by
    have := dt (h.cpd b i.succ)
    rwa [pd_pd_comm (h.cu b) i.succ 0] at this
  have h2 : HasDerivAt (fun s => ∑ i : Fin d, ∑ j : Fin d, γ i j (Fin.cons s y) *
      pd (u b) i.succ (Fin.cons s y) * pd (u b) j.succ (Fin.cons s y))
      (∑ i : Fin d, ∑ j : Fin d, (pd (γ i j) 0 (Fin.cons t y) * pd (u b) i.succ (Fin.cons t y) *
        pd (u b) j.succ (Fin.cons t y) +
        γ i j (Fin.cons t y) * pd (pd (u b) 0) i.succ (Fin.cons t y) *
          pd (u b) j.succ (Fin.cons t y) +
        γ i j (Fin.cons t y) * pd (u b) i.succ (Fin.cons t y) *
          pd (pd (u b) 0) j.succ (Fin.cons t y))) t := by
    refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
    refine (((dt (h.cγ i j)).fun_mul (hux i)).fun_mul (hux j)).congr_deriv ?_
    ring
  refine (((hut.fun_pow 2).add h2).add (hu.fun_pow 2)).congr_deriv ?_
  simp only [Nat.cast_ofNat]
  ring

/-- The pointwise algebra of the energy identity. -/
theorem densT_sub_densG_alg (ut utt u L : ℝ) (β βd : Fin d → ℝ) (γ γt γx : Fin d → Fin d → ℝ)
    (ux uxt : Fin d → ℝ) (uxx : Fin d → Fin d → ℝ) (hsym : ∀ i j, γ i j = γ j i)
    (heq : utt = 2 * ∑ i, β i * uxt i + ∑ i, ∑ j, γ i j * uxx i j + L) :
    (2 * ut * utt + ∑ i, ∑ j, (γt i j * ux i * ux j + γ i j * uxt i * ux j +
        γ i j * ux i * uxt j) + 2 * u * ut) -
      (-(2 * ∑ i, βd i * ut ^ 2) - 2 * ∑ i, ∑ j, γx i j * ut * ux j +
        ∑ i, ∑ j, γt i j * ux i * ux j + 2 * u * ut + 2 * ut * L) =
      ∑ i, 2 * (βd i * ut ^ 2 + β i * (2 * ut * uxt i)) +
        ∑ i, ∑ j, 2 * (γx i j * ut * ux j + γ i j * uxt i * ux j + γ i j * ut * uxx i j) := by
  have hswap : ∑ i, ∑ j, γ i j * ux i * uxt j = ∑ i, ∑ j, γ i j * uxt i * ux j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsym]; ring
  have e1 : ∑ i, ∑ j, (γt i j * ux i * ux j + γ i j * uxt i * ux j + γ i j * ux i * uxt j) =
      ∑ i, ∑ j, γt i j * ux i * ux j + ∑ i, ∑ j, γ i j * uxt i * ux j +
        ∑ i, ∑ j, γ i j * ux i * uxt j := by
    simp only [Finset.sum_add_distrib]
  have e2 : ∑ i, 2 * (βd i * ut ^ 2 + β i * (2 * ut * uxt i)) =
      2 * ∑ i, βd i * ut ^ 2 + 4 * ut * ∑ i, β i * uxt i := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e3 : ∑ i, ∑ j, 2 * (γx i j * ut * ux j + γ i j * uxt i * ux j + γ i j * ut * uxx i j) =
      2 * ∑ i, ∑ j, γx i j * ut * ux j + 2 * ∑ i, ∑ j, γ i j * uxt i * ux j +
        2 * ut * ∑ i, ∑ j, γ i j * uxx i j := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2, e3, hswap, heq]
  ring

/-- `densT - densG` is a sum of spatial derivatives (at points of the slab). -/
theorem densT_sub_densG (h : L2Hyp β γ u L₀ F m T lam M) {x : ST d} (hx : x 0 ∈ Icc 0 T) :
    densT γ u x - densG β γ u (fun b x => L₀ b x + F b x) x =
      ∑ b, (∑ i : Fin d, 2 * pd (fun z => β i z * pd (u b) 0 z ^ 2) i.succ x +
        ∑ i : Fin d, ∑ j : Fin d,
          2 * pd (fun z => γ i j z * pd (u b) 0 z * pd (u b) j.succ z) i.succ x) := by
  unfold densT densG
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hβ : ∀ i : Fin d, pd (fun z => β i z * pd (u b) 0 z ^ 2) i.succ x =
      pd (β i) i.succ x * pd (u b) 0 x ^ 2 +
        β i x * (2 * pd (u b) 0 x * pd (pd (u b) 0) i.succ x) := by
    intro i
    have e : (fun z => β i z * pd (u b) 0 z ^ 2) =
        fun z => β i z * (pd (u b) 0 z * pd (u b) 0 z) := by funext z; ring
    rw [e, SobolevOpen.pd_mul (h.cβ i) ((h.cpd b 0).mul (h.cpd b 0)), SobolevOpen.pd_mul (h.cpd b 0) (h.cpd b 0)]
    ring
  have hγ : ∀ i j : Fin d, pd (fun z => γ i j z * pd (u b) 0 z * pd (u b) j.succ z) i.succ x =
      pd (γ i j) i.succ x * pd (u b) 0 x * pd (u b) j.succ x +
        γ i j x * pd (pd (u b) 0) i.succ x * pd (u b) j.succ x +
        γ i j x * pd (u b) 0 x * pd (pd (u b) j.succ) i.succ x := by
    intro i j
    rw [SobolevOpen.pd_mul ((h.cγ i j).mul (h.cpd b 0)) (h.cpd b j.succ), SobolevOpen.pd_mul (h.cγ i j) (h.cpd b 0)]
    ring
  simp only [hβ, hγ]
  exact densT_sub_densG_alg _ _ _ _ (fun i => β i x) (fun i => pd (β i) i.succ x)
    (fun i j => γ i j x) (fun i j => pd (γ i j) 0 x) (fun i j => pd (γ i j) i.succ x)
    (fun i => pd (u b) i.succ x) (fun i => pd (pd (u b) 0) i.succ x)
    (fun i j => pd (pd (u b) j.succ) i.succ x) (fun i j => h.γ_symm i j x)
    (by rw [h.eqn x hx b]; ring)

theorem cons_zero_mem {t T : ℝ} (ht : t ∈ Icc 0 T) (y : Fin d → ℝ) :
    (Fin.cons t y : ST d) 0 ∈ Icc 0 T := by simpa using ht

/-- **The energy identity** `∫ densT = ∫ densG` at every `t ∈ [0, T]`. -/
theorem integral_densT_eq (h : L2Hyp β γ u L₀ F m T lam M) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∫ y in Icc (0 : Fin d → ℝ) 1, densT γ u (Fin.cons t y) =
      ∫ y in Icc (0 : Fin d → ℝ) 1, densG β γ u (fun b x => L₀ b x + F b x) (Fin.cons t y) := by
  set h1 : ι → Fin d → ST d → ℝ := fun b i z => β i z * pd (u b) 0 z ^ 2
  set h2 : ι → Fin d → Fin d → ST d → ℝ := fun b i j z => γ i j z * pd (u b) 0 z * pd (u b) j.succ z
  have c1 : ∀ b i, ContDiff ℝ 1 (h1 b i) := fun b i => (h.cβ i).mul ((h.cpd b 0).pow 2)
  have c2 : ∀ b i j, ContDiff ℝ 1 (h2 b i j) := fun b i j =>
    ((h.cγ i j).mul (h.cpd b 0)).mul (h.cpd b j.succ)
  have p1 : ∀ b i, IsSPeriodic (h1 b i) := fun b i k x => by
    simp only [h1, (h.pβ i) k x, isSPeriodic_pd (h.pu b) 0 k x]
  have p2 : ∀ b i j, IsSPeriodic (h2 b i j) := fun b i j k x => by
    simp only [h2, (h.pγ i j) k x, isSPeriodic_pd (h.pu b) 0 k x, isSPeriodic_pd (h.pu b) j.succ k x]
  have q1 : ∀ b i, Continuous (pd (h1 b i) i.succ) := fun b i =>
    (contDiff_pd' (n := 0) (c1 b i) i.succ).continuous
  have q2 : ∀ b i j, Continuous (pd (h2 b i j) i.succ) := fun b i j =>
    (contDiff_pd' (n := 0) (c2 b i j) i.succ).continuous
  have key : ∀ y : Fin d → ℝ, densT γ u (Fin.cons t y) =
      densG β γ u (fun b x => L₀ b x + F b x) (Fin.cons t y) +
      ∑ b, (∑ i : Fin d, 2 * pd (h1 b i) i.succ (Fin.cons t y) +
        ∑ i : Fin d, ∑ j : Fin d, 2 * pd (h2 b i j) i.succ (Fin.cons t y)) := fun y => by
    rw [← densT_sub_densG h (cons_zero_mem ht y)]; ring
  simp_rw [key]
  have hI : ∀ {f : ST d → ℝ}, Continuous f →
      Integrable (fun y : Fin d → ℝ => f (Fin.cons t y)) (volume.restrict (Icc 0 1)) :=
    fun hf => integrableOn_slice hf t
  have hsum : ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ b, (∑ i : Fin d, 2 * pd (h1 b i) i.succ (Fin.cons t y) +
      ∑ i : Fin d, ∑ j : Fin d, 2 * pd (h2 b i j) i.succ (Fin.cons t y)) = 0 := by
    rw [integral_finsetSum _ fun b _ => ?_]
    · refine Finset.sum_eq_zero fun b _ => ?_
      rw [integral_add, integral_finsetSum _ fun i _ => ?_, integral_finsetSum _ fun i _ => ?_]
      · simp only [integral_const_mul, integral_slice_pd_eq_zero (c1 b _) (p1 b _) t,
          mul_zero, Finset.sum_const_zero, zero_add]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [integral_finsetSum _ fun j _ => ?_]
        · simp only [integral_const_mul, integral_slice_pd_eq_zero (c2 b _ _) (p2 b _ _) t,
            mul_zero, Finset.sum_const_zero]
        · exact (hI (q2 b i j)).const_mul 2
      · exact integrable_finsetSum _ fun j _ => (hI (q2 b i j)).const_mul 2
      · exact (hI (q1 b i)).const_mul 2
      · exact integrable_finsetSum _ fun i _ => (hI (q1 b i)).const_mul 2
      · exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
          (hI (q2 b i j)).const_mul 2
    · exact (integrable_finsetSum _ fun i _ => (hI (q1 b i)).const_mul 2).add
        (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
          (hI (q2 b i j)).const_mul 2)
  rw [integral_add (hI h.continuous_densG) ?_, hsum, add_zero]
  exact integrable_finsetSum _ fun b _ =>
    (integrable_finsetSum _ fun i _ => (hI (q1 b i)).const_mul 2).add
      (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        (hI (q2 b i j)).const_mul 2)

theorem continuous_energy (h : L2Hyp β γ u L₀ F m T lam M) : Continuous (energy γ u) :=
  continuous_sliceInt h.continuous_dens

/-- **The energy is differentiable** with derivative `∫ densT`. -/
theorem hasDerivAt_energy (h : L2Hyp β γ u L₀ F m T lam M) (t : ℝ) :
    HasDerivAt (energy γ u) (∫ y in Icc (0 : Fin d → ℝ) 1, densT γ u (Fin.cons t y)) t := by
  set K : Set (ST d) := (fun p : ℝ × (Fin d → ℝ) => (Fin.cons p.1 p.2 : ST d)) ''
    (Icc (t - 1) (t + 1) ×ˢ Icc 0 1)
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image continuous_cons2
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn h.continuous_densT.continuousOn
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Icc (0 : Fin d → ℝ) 1))
    (F := fun s y => dens γ u (Fin.cons s y)) (F' := fun s y => densT γ u (Fin.cons s y))
    (x₀ := t) (bound := fun _ => C) (s := Ioo (t - 1) (t + 1))
    (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
    (Eventually.of_forall fun s => (h.continuous_dens.comp (continuous_cons s)).aestronglyMeasurable)
    (integrableOn_slice h.continuous_dens t)
    ((h.continuous_densT.comp (continuous_cons t)).aestronglyMeasurable)
    (by
      rw [ae_restrict_iff' measurableSet_Icc]
      refine Eventually.of_forall fun y hy s hs => ?_
      exact hC _ ⟨(s, y), ⟨Ioo_subset_Icc_self hs, hy⟩, rfl⟩)
    (integrable_const C)
    (Eventually.of_forall fun y s _ => h.hasDerivAt_dens s y)
  exact key.2

/-! #### Bounds -/

theorem two_mul_le_sq_add_sq (p q : ℝ) : 2 * p * q ≤ p ^ 2 + q ^ 2 := by
  nlinarith [sq_nonneg (p - q)]

/-- The pointwise bound of the non-forcing part of `densG`. -/
theorem densG0_pt (M ut u : ℝ) (βd : Fin d → ℝ) (γx γt : Fin d → Fin d → ℝ) (ux : Fin d → ℝ)
    (hM : 0 ≤ M) (hβ : ∀ i, |βd i| ≤ M) (hγx : ∀ i j, |γx i j| ≤ M)
    (hγt : ∀ i j, |γt i j| ≤ M) :
    -(2 * ∑ i, βd i * ut ^ 2) - 2 * ∑ i, ∑ j, γx i j * ut * ux j +
      ∑ i, ∑ j, γt i j * ux i * ux j + 2 * u * ut ≤
      ((d + 1) ^ 2 * M + 1) * (ut ^ 2 + ∑ i, ux i ^ 2 + u ^ 2) := by
  set S := ∑ i, ux i ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have ha : -(2 * ∑ i, βd i * ut ^ 2) ≤ 2 * d * M * ut ^ 2 := by
    have : ∑ i, -(βd i * ut ^ 2) ≤ ∑ _i : Fin d, M * ut ^ 2 := Finset.sum_le_sum fun i _ => by
      rw [← neg_mul]
      exact mul_le_mul_of_nonneg_right ((neg_le_abs _).trans (hβ i)) (sq_nonneg _)
    simp only [Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at this
    linarith
  have hb : -(2 * ∑ i, ∑ j, γx i j * ut * ux j) ≤ d * d * M * ut ^ 2 + d * M * S := by
    have : ∀ i j, -(γx i j * ut * ux j) ≤ M * (ut ^ 2 + ux j ^ 2) / 2 := fun i j => by
      rw [← neg_mul, ← neg_mul]
      exact TorusWaveEnergy.WaveData.abs_mul_le_half _ _ _ _ (by rw [abs_neg]; exact hγx i j)
    have h2 : ∑ i, ∑ j, -(γx i j * ut * ux j) ≤ ∑ _i : Fin d, ∑ j : Fin d, M * (ut ^ 2 + ux j ^ 2) / 2 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => this i j
    have h3 : ∑ _i : Fin d, ∑ j : Fin d, M * (ut ^ 2 + ux j ^ 2) / 2 =
        d * (d * (M * ut ^ 2 / 2) + M / 2 * S) := by
      have inner : ∑ j : Fin d, M * (ut ^ 2 + ux j ^ 2) / 2 = d * (M * ut ^ 2 / 2) + M / 2 * S := by
        have e : ∀ j, M * (ut ^ 2 + ux j ^ 2) / 2 = M * ut ^ 2 / 2 + M / 2 * ux j ^ 2 :=
          fun j => by ring
        simp only [e, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, S]
      rw [Finset.sum_congr rfl fun _ _ => inner]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp only [Finset.sum_neg_distrib] at h2
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith
  have hc : ∑ i, ∑ j, γt i j * ux i * ux j ≤ d * M * S := by
    have : ∀ i j, γt i j * ux i * ux j ≤ M * (ux i ^ 2 + ux j ^ 2) / 2 := fun i j =>
      TorusWaveEnergy.WaveData.abs_mul_le_half _ _ _ _ (hγt i j)
    have h2 : ∑ i, ∑ j, γt i j * ux i * ux j ≤ ∑ i, ∑ j, M * (ux i ^ 2 + ux j ^ 2) / 2 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => this i j
    have h3 : ∑ i : Fin d, ∑ j : Fin d, M * (ux i ^ 2 + ux j ^ 2) / 2 = d * M * S := by
      have e1 : ∑ i : Fin d, ∑ j : Fin d, M * (ux i ^ 2 + ux j ^ 2) / 2 =
          ∑ i : Fin d, ∑ _j : Fin d, M / 2 * ux i ^ 2 + ∑ _i : Fin d, ∑ j : Fin d, M / 2 * ux j ^ 2 := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [e1]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, S,
        ← Finset.mul_sum]
      ring
    linarith
  have hd : 2 * u * ut ≤ u ^ 2 + ut ^ 2 := by nlinarith [sq_nonneg (u - ut)]
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have e1 : 2 * d * M * ut ^ 2 + d * d * M * ut ^ 2 ≤ (d + 1) ^ 2 * M * ut ^ 2 := by
    have := sq_nonneg ut; nlinarith [mul_nonneg hM this]
  have e2 : d * M * S + d * M * S ≤ (d + 1) ^ 2 * M * S := by nlinarith [mul_nonneg hM hS]
  have e3 : 0 ≤ (d + 1) ^ 2 * M * u ^ 2 := by positivity
  nlinarith [sq_nonneg ut, sq_nonneg u]

/-- The non-forcing part of the density derivative. -/
def densG0 (β : Fin d → ST d → ℝ) (γ : Fin d → Fin d → ST d → ℝ) (u L : ι → ST d → ℝ)
    (x : ST d) : ℝ :=
  densG β γ u L x

theorem densG_split (β : Fin d → ST d → ℝ) (γ : Fin d → Fin d → ST d → ℝ) (u L₀ F : ι → ST d → ℝ)
    (x : ST d) : densG β γ u (fun b x => L₀ b x + F b x) x =
      densG β γ u L₀ x + 2 * ∑ b, pd (u b) 0 x * F b x := by
  unfold densG
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem densG_L0_le (h : L2Hyp β γ u L₀ F m T lam M) {x : ST d} (hx : x 0 ∈ Icc 0 T) :
    densG β γ u L₀ x ≤ ((d + 1) ^ 2 * M + 1 + 2 * m (x 0)) * size u x := by
  have hb : ∀ b, -(2 * ∑ i : Fin d, pd (β i) i.succ x * pd (u b) 0 x ^ 2) -
      2 * ∑ i : Fin d, ∑ j : Fin d, pd (γ i j) i.succ x * pd (u b) 0 x * pd (u b) j.succ x +
      ∑ i : Fin d, ∑ j : Fin d, pd (γ i j) 0 x * pd (u b) i.succ x * pd (u b) j.succ x +
      2 * u b x * pd (u b) 0 x ≤
      ((d + 1) ^ 2 * M + 1) * (pd (u b) 0 x ^ 2 + ∑ i : Fin d, pd (u b) i.succ x ^ 2 + u b x ^ 2) :=
    fun b => densG0_pt M _ _ _ _ _ _ h.M_nonneg (fun i => h.bβ x hx i)
      (fun i j => h.bγx x hx i j) (fun i j => h.bγt x hx i j)
  have hCS : ∑ b, pd (u b) 0 x * L₀ b x ≤ m (x 0) * size u x := by
    have h1 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun b => pd (u b) 0 x) (fun b => L₀ b x)
    have hs0 : 0 ≤ size u x := Finset.sum_nonneg fun b _ => by positivity
    have h2 : Real.sqrt (∑ b, pd (u b) 0 x ^ 2) ≤ Real.sqrt (size u x) := by
      refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun b _ => ?_)
      have : 0 ≤ ∑ i : Fin d, pd (u b) i.succ x ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      nlinarith [sq_nonneg (u b x)]
    have h3 : Real.sqrt (∑ b, L₀ b x ^ 2) ≤ m (x 0) * Real.sqrt (size u x) := by
      rw [← Real.sqrt_sq (h.m_nonneg (x 0)), ← Real.sqrt_mul (sq_nonneg _)]
      exact Real.sqrt_le_sqrt (h.bL x hx)
    have hs := Real.mul_self_sqrt hs0
    calc ∑ b, pd (u b) 0 x * L₀ b x ≤ Real.sqrt (∑ b, pd (u b) 0 x ^ 2) *
          Real.sqrt (∑ b, L₀ b x ^ 2) := h1
      _ ≤ Real.sqrt (size u x) * (m (x 0) * Real.sqrt (size u x)) :=
          mul_le_mul h2 h3 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = m (x 0) * size u x := by rw [mul_left_comm, hs]
  have hsplit : densG β γ u L₀ x = ∑ b, (-(2 * ∑ i : Fin d, pd (β i) i.succ x * pd (u b) 0 x ^ 2) -
      2 * ∑ i : Fin d, ∑ j : Fin d, pd (γ i j) i.succ x * pd (u b) 0 x * pd (u b) j.succ x +
      ∑ i : Fin d, ∑ j : Fin d, pd (γ i j) 0 x * pd (u b) i.succ x * pd (u b) j.succ x +
      2 * u b x * pd (u b) 0 x) + 2 * ∑ b, pd (u b) 0 x * L₀ b x := by
    unfold densG
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hs1 : ∑ b, (-(2 * ∑ i : Fin d, pd (β i) i.succ x * pd (u b) 0 x ^ 2) -
      2 * ∑ i : Fin d, ∑ j : Fin d, pd (γ i j) i.succ x * pd (u b) 0 x * pd (u b) j.succ x +
      ∑ i : Fin d, ∑ j : Fin d, pd (γ i j) 0 x * pd (u b) i.succ x * pd (u b) j.succ x +
      2 * u b x * pd (u b) 0 x) ≤ ((d + 1) ^ 2 * M + 1) * size u x := by
    calc _ ≤ ∑ b, ((d + 1) ^ 2 * M + 1) *
          (pd (u b) 0 x ^ 2 + ∑ i : Fin d, pd (u b) i.succ x ^ 2 + u b x ^ 2) :=
          Finset.sum_le_sum fun b _ => hb b
      _ = ((d + 1) ^ 2 * M + 1) * size u x := by rw [size, Finset.mul_sum]
  rw [hsplit]
  nlinarith

/-- The coercivity constant `c = min(λ, 1)`. -/
def cmin (lam : ℝ) : ℝ := min lam 1

theorem size_le_dens (h : L2Hyp β γ u L₀ F m T lam M) {x : ST d} (hx : x 0 ∈ Icc 0 T) :
    cmin lam * size u x ≤ dens γ u x := by
  unfold size dens
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  have hco := h.coer x hx (fun i => pd (u b) i.succ x)
  have hc1 : cmin lam ≤ 1 := min_le_right _ _
  have hcl : cmin lam ≤ lam := min_le_left _ _
  have h1 : cmin lam * pd (u b) 0 x ^ 2 ≤ pd (u b) 0 x ^ 2 := by
    have := sq_nonneg (pd (u b) 0 x); nlinarith
  have h2 : cmin lam * ∑ i : Fin d, pd (u b) i.succ x ^ 2 ≤ lam * ∑ i : Fin d, pd (u b) i.succ x ^ 2 :=
    mul_le_mul_of_nonneg_right hcl (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have h3 : cmin lam * u b x ^ 2 ≤ u b x ^ 2 := by
    have := sq_nonneg (u b x); nlinarith
  nlinarith

theorem size_nonneg (u : ι → ST d → ℝ) (x : ST d) : 0 ≤ size u x :=
  Finset.sum_nonneg fun b _ => by positivity

theorem dens_nonneg (h : L2Hyp β γ u L₀ F m T lam M) (hlam : 0 < lam) {x : ST d}
    (hx : x 0 ∈ Icc 0 T) : 0 ≤ dens γ u x :=
  le_trans (mul_nonneg (lt_min hlam one_pos).le (size_nonneg u x)) (size_le_dens h hx)

theorem energy_nonneg (h : L2Hyp β γ u L₀ F m T lam M) (hlam : 0 < lam) {t : ℝ}
    (ht : t ∈ Icc 0 T) : 0 ≤ energy γ u t :=
  setIntegral_nonneg measurableSet_Icc fun y _ => dens_nonneg h hlam (cons_zero_mem ht y)

theorem integral_size_le (h : L2Hyp β γ u L₀ F m T lam M) {t : ℝ} (ht : t ∈ Icc 0 T) :
    cmin lam * ∫ y in Icc (0 : Fin d → ℝ) 1, size u (Fin.cons t y) ≤ energy γ u t := by
  rw [← integral_const_mul]
  exact setIntegral_mono_on ((integrableOn_slice h.continuous_size t).const_mul _)
    (integrableOn_slice h.continuous_dens t) measurableSet_Icc
    fun y _ => size_le_dens h (cons_zero_mem ht y)

/-- **Cauchy–Schwarz on the cube**: `∫ Σ_b f_b g_b ≤ ‖f‖_{L²} ‖g‖_{L²}`. -/
theorem integral_sum_mul_le_cube {f g : (Fin d → ℝ) → ι → ℝ}
    (hf : ∀ b, Continuous fun y => f y b) (hg : ∀ b, Continuous fun y => g y b) :
    ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ b, f y b * g y b ≤
      Real.sqrt (∫ y in Icc (0 : Fin d → ℝ) 1, ∑ b, f y b ^ 2) *
        Real.sqrt (∫ y in Icc (0 : Fin d → ℝ) 1, ∑ b, g y b ^ 2) := by
  have hint : ∀ {F : (Fin d → ℝ) → ℝ}, Continuous F → IntegrableOn F (Icc 0 1) :=
    fun hF => integrableOn_cube_of_continuousOn hF.continuousOn
  refine TorusWaveEnergyForced.le_sqrt_mul_sqrt_of_forall
    (setIntegral_nonneg measurableSet_Icc fun y _ => Finset.sum_nonneg fun b _ => sq_nonneg _)
    (setIntegral_nonneg measurableSet_Icc fun y _ => Finset.sum_nonneg fun b _ => sq_nonneg _)
    fun ε hε => ?_
  have hpt : ∀ y, ∑ b, f y b * g y b ≤ (ε * ∑ b, f y b ^ 2 + (∑ b, g y b ^ 2) / ε) / 2 := by
    intro y
    rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_le_sum fun b _ => ?_
    have : 0 ≤ (ε * f y b - g y b) ^ 2 / ε := by positivity
    have e : (ε * f y b - g y b) ^ 2 / ε = ε * f y b ^ 2 + g y b ^ 2 / ε - 2 * (f y b * g y b) := by
      field_simp; ring
    linarith
  calc ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ b, f y b * g y b ≤
        ∫ y in Icc (0 : Fin d → ℝ) 1, (ε * ∑ b, f y b ^ 2 + (∑ b, g y b ^ 2) / ε) / 2 :=
        setIntegral_mono (hint (by fun_prop)) (hint (by fun_prop)) hpt
    _ = (ε * (∫ y in Icc (0 : Fin d → ℝ) 1, ∑ b, f y b ^ 2) +
          (∫ y in Icc (0 : Fin d → ℝ) 1, ∑ b, g y b ^ 2) / ε) / 2 := by
        rw [integral_div, integral_add (hint (by fun_prop)) (hint (by fun_prop)),
          integral_const_mul, integral_div]

/-- The growth rate `k(t) = ((d+1)²M + 1 + 2m(t))/c`. -/
def kcoef (d : ℕ) (M : ℝ) (m : ℝ → ℝ) (c : ℝ) (t : ℝ) : ℝ := ((d + 1) ^ 2 * M + 1 + 2 * m t) / c

theorem continuous_l2norm {F : ι → ST d → ℝ} (hF : ∀ b, Continuous (F b)) :
    Continuous (l2norm F) := by
  unfold l2norm
  exact (continuous_sliceInt (f := fun x => ∑ b, F b x ^ 2) (by fun_prop)).sqrt

/-- **The forced energy inequality** on `[0, T]`:
`E' ≤ k(t) E + 2 (c^{-1/2} ‖F(t)‖_{L²}) √E`. -/
theorem energy_deriv_le (h : L2Hyp β γ u L₀ F m T lam M) (hlam : 0 < lam) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ∫ y in Icc (0 : Fin d → ℝ) 1, densT γ u (Fin.cons t y) ≤
      kcoef d M m (cmin lam) t * energy γ u t +
        2 * ((Real.sqrt (cmin lam))⁻¹ * l2norm F t) * Real.sqrt (energy γ u t) := by
  set c := cmin lam
  have hc0 : 0 < c := lt_min hlam one_pos
  have hint : ∀ {f : ST d → ℝ}, Continuous f →
      IntegrableOn (fun y : Fin d → ℝ => f (Fin.cons t y)) (Icc 0 1) :=
    fun hf => integrableOn_slice hf t
  have hG0c : Continuous (densG β γ u L₀) := by
    unfold densG
    have := fun b => (h.cu b).continuous; have := fun b μ => h.continuous_pd b μ
    have := fun i μ => h.continuous_pdβ i μ; have := fun i j μ => h.continuous_pdγ i j μ
    have := h.cL
    fun_prop
  have hWc : Continuous fun x => ∑ b, pd (u b) 0 x * F b x := by
    have := fun b μ => h.continuous_pd b μ; have := h.cF; fun_prop
  rw [integral_densT_eq h ht]
  simp only [densG_split β γ u L₀ F]
  rw [integral_add (hint hG0c) ((hint hWc).const_mul 2), integral_const_mul]
  have hA : ∫ y in Icc (0 : Fin d → ℝ) 1, densG β γ u L₀ (Fin.cons t y) ≤
      kcoef d M m c t * energy γ u t := by
    have hK0 : 0 ≤ (d + 1) ^ 2 * M + 1 + 2 * m t := by
      have := h.m_nonneg t; have := h.M_nonneg; positivity
    calc ∫ y in Icc (0 : Fin d → ℝ) 1, densG β γ u L₀ (Fin.cons t y) ≤
          ∫ y in Icc (0 : Fin d → ℝ) 1, ((d + 1) ^ 2 * M + 1 + 2 * m t) * size u (Fin.cons t y) :=
          setIntegral_mono_on (hint hG0c) ((hint h.continuous_size).const_mul _) measurableSet_Icc
            fun y _ => by
              have := densG_L0_le h (cons_zero_mem ht y)
              simpa using this
      _ = ((d + 1) ^ 2 * M + 1 + 2 * m t) / c *
            (c * ∫ y in Icc (0 : Fin d → ℝ) 1, size u (Fin.cons t y)) := by
          rw [integral_const_mul]; field_simp
      _ ≤ kcoef d M m c t * energy γ u t :=
          mul_le_mul_of_nonneg_left (integral_size_le h ht) (div_nonneg hK0 hc0.le)
  have hB : ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ b, pd (u b) 0 (Fin.cons t y) * F b (Fin.cons t y) ≤
      (Real.sqrt c)⁻¹ * l2norm F t * Real.sqrt (energy γ u t) := by
    have h1 := integral_sum_mul_le_cube (f := fun y b => pd (u b) 0 (Fin.cons t y))
      (g := fun y b => F b (Fin.cons t y))
      (fun b => (h.continuous_pd b 0).comp (continuous_cons t))
      (fun b => (h.cF b).comp (continuous_cons t))
    have h2 : ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ b, pd (u b) 0 (Fin.cons t y) ^ 2 ≤
        energy γ u t / c := by
      rw [le_div_iff₀ hc0]
      refine le_trans ?_ (integral_size_le h ht)
      rw [mul_comm]
      refine mul_le_mul_of_nonneg_left (setIntegral_mono_on
        (hint (f := fun x => ∑ b, pd (u b) 0 x ^ 2) (by
        have := fun b => h.continuous_pd b 0; fun_prop)) (hint h.continuous_size)
        measurableSet_Icc fun y _ => ?_) hc0.le
      refine Finset.sum_le_sum fun b _ => ?_
      have : 0 ≤ ∑ i : Fin d, pd (u b) i.succ (Fin.cons t y) ^ 2 :=
        Finset.sum_nonneg fun i _ => sq_nonneg _
      nlinarith [sq_nonneg (u b (Fin.cons t y))]
    have h3 : Real.sqrt (∫ y in Icc (0 : Fin d → ℝ) 1, ∑ b, pd (u b) 0 (Fin.cons t y) ^ 2) ≤
        (Real.sqrt c)⁻¹ * Real.sqrt (energy γ u t) := by
      calc _ ≤ Real.sqrt (energy γ u t / c) := Real.sqrt_le_sqrt h2
        _ = (Real.sqrt c)⁻¹ * Real.sqrt (energy γ u t) := by
            rw [Real.sqrt_div' _ hc0.le, div_eq_inv_mul]
    calc _ ≤ Real.sqrt (∫ y in Icc (0 : Fin d → ℝ) 1, ∑ b, pd (u b) 0 (Fin.cons t y) ^ 2) *
          l2norm F t := h1
      _ ≤ (Real.sqrt c)⁻¹ * Real.sqrt (energy γ u t) * l2norm F t :=
          mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg _)
      _ = (Real.sqrt c)⁻¹ * l2norm F t * Real.sqrt (energy γ u t) := by ring
  nlinarith

/-- **The `L²` energy bound with an `L¹_t L²_x` source**: for `t ∈ [0, T]`,
`√E(t) ≤ (√E(0) + c^{-1/2}∫₀ᵗ ‖F‖_{L²}) exp(½ ∫₀ᵗ k)`. -/
theorem sqrt_energy_le (h : L2Hyp β γ u L₀ F m T lam M) (hlam : 0 < lam) :
    ∀ t ∈ Icc 0 T, Real.sqrt (energy γ u t) ≤
      (Real.sqrt (energy γ u 0) + ∫ s in (0)..t, (Real.sqrt (cmin lam))⁻¹ * l2norm F s) *
        Real.exp ((∫ s in (0)..t, kcoef d M m (cmin lam) s) / 2) := by
  intro t ht
  refine TorusWaveEnergyForced.sqrt_energy_gronwall
    (E' := fun s => ∫ y in Icc (0 : Fin d → ℝ) 1, densT γ u (Fin.cons s y))
    h.continuous_energy.continuousOn (fun s hs => energy_nonneg h hlam hs)
    (fun s _ => hasDerivAt_energy h s) (by unfold kcoef; have := h.cm; fun_prop)
    (continuous_const.mul (continuous_l2norm h.cF)) (fun s => ?_) (fun s => ?_)
    (fun s hs => energy_deriv_le h hlam (Ioo_subset_Icc_self hs)) t ht
  · unfold kcoef
    have := h.m_nonneg s; have := h.M_nonneg; have : 0 < cmin lam := lt_min hlam one_pos
    positivity
  · exact mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

end L2Hyp

/-! ### Linear systems with first-order lower part, and their prolongation -/

/-- The coefficients of a linear second-order system with scalar principal part and first-order
lower part `Σ_c (A_bc ∂ₜu_c + Σᵢ Bⁱ_bc ∂ᵢu_c + C_bc u_c)`. -/
structure WaveSys (d : ℕ) (ι : Type*) where
  β : Fin d → ST d → ℝ
  γ : Fin d → Fin d → ST d → ℝ
  A : ι → ι → ST d → ℝ
  B : Fin d → ι → ι → ST d → ℝ
  C : ι → ι → ST d → ℝ

namespace WaveSys

/-- The principal part `2βⁱ∂ᵢ∂ₜu_b + γ^{ij}∂ᵢ∂ⱼu_b`. -/
def princ (S : WaveSys d ι) (u : ι → ST d → ℝ) (b : ι) (x : ST d) : ℝ :=
  2 * ∑ i : Fin d, S.β i x * pd (pd (u b) 0) i.succ x +
    ∑ i : Fin d, ∑ j : Fin d, S.γ i j x * pd (pd (u b) j.succ) i.succ x

/-- The lower-order part `Σ_c (A_bc ∂ₜu_c + Σᵢ Bⁱ_bc ∂ᵢu_c + C_bc u_c)`. -/
def lower (S : WaveSys d ι) (u : ι → ST d → ℝ) (b : ι) (x : ST d) : ℝ :=
  ∑ c, (S.A b c x * pd (u c) 0 x + ∑ i : Fin d, S.B i b c x * pd (u c) i.succ x +
    S.C b c x * u c x)

variable [DecidableEq ι]

/-- **The prolonged system** satisfied by `V = (u, ∂₁u, …, ∂_d u)` (index `ι × Option (Fin d)`):
the principal part is unchanged; the commutators `2∂_kβⁱ ∂ᵢ∂ₜu + ∂_kγ^{ij} ∂ᵢ∂ⱼu` and the derivatives
of the lower-order coefficients enter the new lower-order coefficients. -/
def prolong (S : WaveSys d ι) : WaveSys d (ι × Option (Fin d)) where
  β := S.β
  γ := S.γ
  A := fun p q x => match p.2, q.2 with
    | none, none => S.A p.1 q.1 x
    | some k, none => pd (S.A p.1 q.1) k.succ x
    | some k, some i => (if p.1 = q.1 then 2 else 0) * pd (S.β i) k.succ x +
        (if i = k then 1 else 0) * S.A p.1 q.1 x
    | none, some _ => 0
  B := fun j p q x => match p.2, q.2 with
    | none, none => S.B j p.1 q.1 x
    | some k, none => pd (S.B j p.1 q.1) k.succ x
    | some k, some i => (if p.1 = q.1 then 1 else 0) * pd (S.γ j i) k.succ x +
        (if i = k then 1 else 0) * S.B j p.1 q.1 x
    | none, some _ => 0
  C := fun p q x => match p.2, q.2 with
    | none, none => S.C p.1 q.1 x
    | some k, none => pd (S.C p.1 q.1) k.succ x
    | some k, some i => (if i = k then 1 else 0) * S.C p.1 q.1 x
    | none, some _ => 0

end WaveSys

/-- The prolonged unknown `V = (u, ∂₁u, …, ∂_d u)`. -/
def pU (u : ι → ST d → ℝ) (p : ι × Option (Fin d)) : ST d → ℝ :=
  match p.2 with
  | none => u p.1
  | some k => pd (u p.1) k.succ

@[simp] theorem pU_none (u : ι → ST d → ℝ) (b : ι) : pU u (b, none) = u b := rfl
@[simp] theorem pU_some (u : ι → ST d → ℝ) (b : ι) (k : Fin d) :
    pU u (b, some k) = pd (u b) k.succ := rfl

/-! #### Iterated derivatives and `W^{r,∞}` bounds on the slab -/

/-- Iterated partial derivatives along a list of directions (innermost first). -/
def dW : List (Fin (d + 1)) → (ST d → ℝ) → ST d → ℝ
  | [], f => f
  | μ :: w, f => dW w (pd f μ)

/-- All spatial derivatives of order `≤ r` of `f` are bounded by `M` on `[0, T] × ℝ^d` (an
`L^∞_t W^{r,∞}_x` bound). -/
def DerivBound (T : ℝ) (r : ℕ) (f : ST d → ℝ) (M : ℝ) : Prop :=
  ∀ w : List (Fin d), w.length ≤ r → ∀ x : ST d, x 0 ∈ Icc 0 T →
    |dW (w.map Fin.succ) f x| ≤ M

theorem pd_lincomb {f g : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (a b : ℝ)
    (μ : Fin (d + 1)) : pd (fun x => a * f x + b * g x) μ = fun x => a * pd f μ x + b * pd g μ x := by
  funext x
  have hf' : DifferentiableAt ℝ f x := (hf.differentiable (by simp)) x
  have hg' : DifferentiableAt ℝ g x := (hg.differentiable (by simp)) x
  unfold pd
  rw [fderiv_fun_add (hf'.const_mul a) (hg'.const_mul b), fderiv_const_mul hf',
    fderiv_const_mul hg']
  simp

theorem dW_lincomb : ∀ (w : List (Fin (d + 1))) {f g : ST d → ℝ}, ContDiff ℝ ∞ f →
    ContDiff ℝ ∞ g → ∀ a b : ℝ, dW w (fun x => a * f x + b * g x) =
      fun x => a * dW w f x + b * dW w g x
  | [], _, _, _, _, _, _ => rfl
  | μ :: w, f, g, hf, hg, a, b => by
    simp only [dW]
    rw [pd_lincomb hf hg a b μ]
    exact dW_lincomb w (contDiff_pd_top hf μ) (contDiff_pd_top hg μ) a b

theorem dW_zero : ∀ (w : List (Fin (d + 1))), dW w (fun _ : ST d => (0 : ℝ)) = fun _ => 0
  | [] => rfl
  | μ :: w => by
    simp only [dW]
    have : pd (fun _ : ST d => (0 : ℝ)) μ = fun _ => 0 := by
      funext x; simp [pd]
    rw [this]; exact dW_zero w

theorem DerivBound.mono {T : ℝ} {r : ℕ} {f : ST d → ℝ} {M M' : ℝ} (h : DerivBound T r f M)
    (hM : M ≤ M') : DerivBound T r f M' := fun w hw x hx => (h w hw x hx).trans hM

theorem DerivBound.of_succ {T : ℝ} {r : ℕ} {f : ST d → ℝ} {M : ℝ} (h : DerivBound T (r + 1) f M) :
    DerivBound T r f M := fun w hw x hx => h w (hw.trans (Nat.le_succ r)) x hx

theorem DerivBound.pd {T : ℝ} {r : ℕ} {f : ST d → ℝ} {M : ℝ} (h : DerivBound T (r + 1) f M)
    (k : Fin d) : DerivBound T r (pd f k.succ) M := fun w hw x hx =>
  h (k :: w) (by simp only [List.length_cons]; omega) x hx

theorem DerivBound.lincomb {T : ℝ} {r : ℕ} {f g : ST d → ℝ} {M N : ℝ} (hf : DerivBound T r f M)
    (hg : DerivBound T r g N) (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g) {a b : ℝ}
    (ha : |a| ≤ 2) (hb : |b| ≤ 1) (hM : 0 ≤ M) : DerivBound T r (fun x => a * f x + b * g x)
      (2 * M + N) := fun w hw x hx => by
  rw [dW_lincomb (w.map Fin.succ) hfs hgs a b]
  have h1 := hf w hw x hx
  have h2 := hg w hw x hx
  calc |a * dW (w.map Fin.succ) f x + b * dW (w.map Fin.succ) g x| ≤
        |a| * |dW (w.map Fin.succ) f x| + |b| * |dW (w.map Fin.succ) g x| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ 2 * M + 1 * N := by
        gcongr
    _ = 2 * M + N := by ring

theorem DerivBound.zero {T : ℝ} {r : ℕ} {M : ℝ} (hM : 0 ≤ M) :
    DerivBound T r (fun _ : ST d => (0 : ℝ)) M := fun w _ x _ => by
  rw [dW_zero (w.map Fin.succ)]; simpa using hM

/-! #### The hypotheses of the `H^k` estimate -/

/-- Smooth spatially periodic fields solving the system `S` with forcing `F` on `[0, T] × 𝕋^d`,
`γ` symmetric and `λ`-coercive, all spatial coefficient derivatives of order `≤ r` bounded by `M`
(`DerivBound`), and the first derivatives `∂ⱼβⁱ`, `∂_μγ^{ij}` bounded by `M`. -/
structure SysHyp (S : WaveSys d ι) (u F : ι → ST d → ℝ) (T lam M : ℝ) (r : ℕ) : Prop where
  su : ∀ b, ContDiff ℝ ∞ (u b)
  sF : ∀ b, ContDiff ℝ ∞ (F b)
  sβ : ∀ i, ContDiff ℝ ∞ (S.β i)
  sγ : ∀ i j, ContDiff ℝ ∞ (S.γ i j)
  sA : ∀ b c, ContDiff ℝ ∞ (S.A b c)
  sB : ∀ i b c, ContDiff ℝ ∞ (S.B i b c)
  sC : ∀ b c, ContDiff ℝ ∞ (S.C b c)
  pu : ∀ b, IsSPeriodic (u b)
  pF : ∀ b, IsSPeriodic (F b)
  pβ : ∀ i, IsSPeriodic (S.β i)
  pγ : ∀ i j, IsSPeriodic (S.γ i j)
  pA : ∀ b c, IsSPeriodic (S.A b c)
  pB : ∀ i b c, IsSPeriodic (S.B i b c)
  pC : ∀ b c, IsSPeriodic (S.C b c)
  eqn : ∀ x : ST d, x 0 ∈ Icc 0 T → ∀ b,
    pd (pd (u b) 0) 0 x = S.princ u b x + S.lower u b x + F b x
  γ_symm : ∀ i j x, S.γ i j x = S.γ j i x
  coer : ∀ x : ST d, x 0 ∈ Icc 0 T → ∀ ξ : Fin d → ℝ,
    lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, S.γ i j x * ξ i * ξ j
  M_nonneg : 0 ≤ M
  bβ : ∀ i, DerivBound T r (S.β i) M
  bγ : ∀ i j, DerivBound T r (S.γ i j) M
  bA : ∀ b c, DerivBound T r (S.A b c) M
  bB : ∀ i b c, DerivBound T r (S.B i b c) M
  bC : ∀ b c, DerivBound T r (S.C b c) M
  bβx : ∀ x : ST d, x 0 ∈ Icc 0 T → ∀ i j : Fin d, |pd (S.β i) j.succ x| ≤ M
  bγ1 : ∀ x : ST d, x 0 ∈ Icc 0 T → ∀ (i j : Fin d) (μ : Fin (d + 1)), |pd (S.γ i j) μ x| ≤ M

/-! #### Differentiating the equation along a spatial direction -/

theorem hasDerivAt_line0 {f : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (x : ST d) (μ : Fin (d + 1)) :
    HasDerivAt (fun s : ℝ => f (x + s • ev μ)) (pd f μ x) 0 := by
  have := hasDerivAt_line (f := f) (x := x) μ (s := 0) ((hf.differentiable (by simp)) _)
  simpa using this

theorem line_time (x : ST d) (k : Fin d) (s : ℝ) : (x + s • ev k.succ) 0 = x 0 := by
  simp [Pi.single_apply, Fin.succ_ne_zero]

theorem pd2_swap {f : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (a b : Fin (d + 1)) :
    pd (pd f a) b = pd (pd f b) a :=
  funext fun x => pd_pd_comm (hf.of_le (by norm_cast)) a b x

theorem pd3_swap {f : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (a b c : Fin (d + 1)) :
    pd (pd (pd f a) b) c = pd (pd (pd f a) c) b :=
  funext fun x => pd_pd_comm ((contDiff_pd_top hf a).of_le (by norm_cast)) b c x

namespace SysHyp

variable [DecidableEq ι] {S : WaveSys d ι} {u F : ι → ST d → ℝ} {T lam M : ℝ} {r : ℕ}

theorem s_pd (h : SysHyp S u F T lam M r) (b : ι) (μ : Fin (d + 1)) :
    ContDiff ℝ ∞ (pd (u b) μ) := contDiff_pd_top (h.su b) μ

theorem s_pd2 (h : SysHyp S u F T lam M r) (b : ι) (μ ν : Fin (d + 1)) :
    ContDiff ℝ ∞ (pd (pd (u b) μ) ν) := contDiff_pd_top (h.s_pd b μ) ν

/-- The line derivative of the right-hand side of the equation along `e_{k+1}`. -/
theorem hasDerivAt_rhs (h : SysHyp S u F T lam M r) (b : ι) (k : Fin d) (x : ST d) :
    HasDerivAt (fun s : ℝ => S.princ u b (x + s • ev k.succ) + S.lower u b (x + s • ev k.succ) +
        F b (x + s • ev k.succ))
      ((2 * ∑ i : Fin d, (pd (S.β i) k.succ x * pd (pd (u b) 0) i.succ x +
          S.β i x * pd (pd (pd (u b) 0) i.succ) k.succ x) +
        ∑ i : Fin d, ∑ j : Fin d, (pd (S.γ i j) k.succ x * pd (pd (u b) j.succ) i.succ x +
          S.γ i j x * pd (pd (pd (u b) j.succ) i.succ) k.succ x)) +
       ∑ c, (pd (S.A b c) k.succ x * pd (u c) 0 x + S.A b c x * pd (pd (u c) 0) k.succ x +
          ∑ i : Fin d, (pd (S.B i b c) k.succ x * pd (u c) i.succ x +
            S.B i b c x * pd (pd (u c) i.succ) k.succ x) +
          (pd (S.C b c) k.succ x * u c x + S.C b c x * pd (u c) k.succ x)) +
       pd (F b) k.succ x) 0 := by
  have hl := fun {f : ST d → ℝ} (hf : ContDiff ℝ ∞ f) => hasDerivAt_line0 hf x k.succ
  unfold WaveSys.princ WaveSys.lower
  refine ((HasDerivAt.add ?_ ?_).add (hl (h.sF b)))
  · refine (((HasDerivAt.fun_sum fun i _ => ?_).const_mul 2).add
      (HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_))
    · exact ((hl (h.sβ i)).mul (hl (h.s_pd2 b 0 i.succ))).congr_deriv (by simp)
    · exact ((hl (h.sγ i j)).mul (hl (h.s_pd2 b j.succ i.succ))).congr_deriv (by simp)
  · refine HasDerivAt.fun_sum fun c _ => ?_
    refine (((hl (h.sA b c)).mul (hl (h.s_pd c 0))).add
      (HasDerivAt.fun_sum fun i _ => (hl (h.sB i b c)).mul (hl (h.s_pd c i.succ)))).add
      ((hl (h.sC b c)).mul (hl (h.su c)))
    |>.congr_deriv ?_
    simp only [zero_smul, add_zero, Finset.sum_add_distrib]

/-- The spatially differentiated equation: `∂_k∂ₜ²u_b = ∂_k(RHS)`. -/
theorem pd_eqn (h : SysHyp S u F T lam M r) {x : ST d} (hx : x 0 ∈ Icc 0 T) (b : ι) (k : Fin d) :
    pd (pd (pd (u b) 0) 0) k.succ x =
      (2 * ∑ i : Fin d, (pd (S.β i) k.succ x * pd (pd (u b) 0) i.succ x +
          S.β i x * pd (pd (pd (u b) 0) i.succ) k.succ x) +
        ∑ i : Fin d, ∑ j : Fin d, (pd (S.γ i j) k.succ x * pd (pd (u b) j.succ) i.succ x +
          S.γ i j x * pd (pd (pd (u b) j.succ) i.succ) k.succ x)) +
       ∑ c, (pd (S.A b c) k.succ x * pd (u c) 0 x + S.A b c x * pd (pd (u c) 0) k.succ x +
          ∑ i : Fin d, (pd (S.B i b c) k.succ x * pd (u c) i.succ x +
            S.B i b c x * pd (pd (u c) i.succ) k.succ x) +
          (pd (S.C b c) k.succ x * u c x + S.C b c x * pd (u c) k.succ x)) +
       pd (F b) k.succ x := by
  refine (hasDerivAt_line0 (h.s_pd2 b 0 0) x k.succ).unique ?_
  refine (h.hasDerivAt_rhs b k x).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  exact h.eqn _ (by rw [line_time]; exact hx) b

end SysHyp

theorem lower_prolong_none [DecidableEq ι] (S : WaveSys d ι) (u : ι → ST d → ℝ) (b : ι)
    (x : ST d) : S.prolong.lower (pU u) (b, none) x = S.lower u b x := by
  unfold WaveSys.lower
  rw [Fintype.sum_prod_type]
  simp [Fintype.sum_option, WaveSys.prolong]

theorem princ_prolong [DecidableEq ι] (S : WaveSys d ι) (u : ι → ST d → ℝ) (b : ι)
    (o : Option (Fin d)) (x : ST d) :
    S.prolong.princ (pU u) (b, o) x = 2 * ∑ i : Fin d, S.β i x * pd (pd (pU u (b, o)) 0) i.succ x +
      ∑ i : Fin d, ∑ j : Fin d, S.γ i j x * pd (pd (pU u (b, o)) j.succ) i.succ x := rfl

theorem lower_prolong_some [DecidableEq ι] (S : WaveSys d ι) (u : ι → ST d → ℝ) (b : ι)
    (k : Fin d) (x : ST d) : S.prolong.lower (pU u) (b, some k) x =
      ∑ c, (pd (S.A b c) k.succ x * pd (u c) 0 x +
        ∑ j : Fin d, pd (S.B j b c) k.succ x * pd (u c) j.succ x + pd (S.C b c) k.succ x * u c x) +
      ∑ c, ∑ i : Fin d,
        ((((if b = c then 2 else 0) * pd (S.β i) k.succ x +
          (if i = k then 1 else 0) * S.A b c x) * pd (pd (u c) i.succ) 0 x +
        ∑ j : Fin d, ((if b = c then 1 else 0) * pd (S.γ j i) k.succ x +
          (if i = k then 1 else 0) * S.B j b c x) * pd (pd (u c) i.succ) j.succ x) +
        (if i = k then 1 else 0) * S.C b c x * pd (u c) i.succ x) := by
  unfold WaveSys.lower
  rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Fintype.sum_option]
  simp only [WaveSys.prolong, pU_none, pU_some]

/-- `Σ_c Σ_i (if b = c then a else 0) f c i = a Σ_i f b i`. -/
theorem sum_sum_ite_left [DecidableEq ι] {κ : Type*} [Fintype κ] (b : ι) (a : ℝ)
    (f : ι → κ → ℝ) : ∑ c, ∑ i, (if b = c then a else 0) * f c i = a * ∑ i, f b i := by
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq, Finset.mul_sum]

/-- `Σ_c Σ_i (if i = k then 1 else 0) g c i = Σ_c g c k`. -/
theorem sum_sum_ite_right {κ : Type*} [Fintype κ] [DecidableEq κ] (k : κ) (g : ι → κ → ℝ) :
    ∑ c, ∑ i, (if i = k then 1 else 0) * g c i = ∑ c, g c k := by
  simp [ite_mul, Finset.sum_ite_eq']

namespace SysHyp

variable [DecidableEq ι] {S : WaveSys d ι} {u F : ι → ST d → ℝ} {T lam M : ℝ} {r : ℕ}

set_option maxHeartbeats 800000 in
/-- **The prolonged equation**: `V = (u, ∂u)` solves the prolonged system with forcing
`(F, ∂F)` on the slab. -/
theorem prolong_eqn (h : SysHyp S u F T lam M r) {x : ST d} (hx : x 0 ∈ Icc 0 T)
    (p : ι × Option (Fin d)) :
    pd (pd (pU u p) 0) 0 x = S.prolong.princ (pU u) p x + S.prolong.lower (pU u) p x +
      pU F p x := by
  obtain ⟨b, _ | k⟩ := p
  · rw [lower_prolong_none]
    exact h.eqn x hx b
  · have hE := h.pd_eqn hx b k
    have e0 : pd (pd (pd (u b) k.succ) 0) 0 = pd (pd (pd (u b) 0) 0) k.succ := by
      rw [pd2_swap (h.su b) k.succ 0, pd3_swap (h.su b) 0 k.succ 0]
    have e2 : ∀ i : Fin d, pd (pd (pd (u b) 0) i.succ) k.succ =
        pd (pd (pd (u b) k.succ) 0) i.succ := fun i => by
      rw [pd3_swap (h.su b) 0 i.succ k.succ, pd2_swap (h.su b) 0 k.succ]
    have e3 : ∀ i j : Fin d, pd (pd (pd (u b) j.succ) i.succ) k.succ =
        pd (pd (pd (u b) k.succ) j.succ) i.succ := fun i j => by
      rw [pd3_swap (h.su b) j.succ i.succ k.succ, pd2_swap (h.su b) j.succ k.succ]
    have e4 : ∀ c, pd (pd (u c) 0) k.succ = pd (pd (u c) k.succ) 0 := fun c =>
      pd2_swap (h.su c) 0 k.succ
    have e5 : ∀ c (i : Fin d), pd (pd (u c) i.succ) k.succ = pd (pd (u c) k.succ) i.succ :=
      fun c i => pd2_swap (h.su c) i.succ k.succ
    have e1 : ∀ i : Fin d, pd (pd (u b) 0) i.succ = pd (pd (u b) i.succ) 0 := fun i =>
      pd2_swap (h.su b) 0 i.succ
    simp only [pU_some]
    rw [e0, hE, princ_prolong, lower_prolong_some]
    simp only [pU_some]
    simp only [e2, e3]
    simp only [e4, e5, e1]
    -- the ite sums
    have hA : ∑ c, ∑ i : Fin d, (((if b = c then 2 else 0) * pd (S.β i) k.succ x +
          (if i = k then 1 else 0) * S.A b c x) * pd (pd (u c) i.succ) 0 x) =
        2 * ∑ i : Fin d, pd (S.β i) k.succ x * pd (pd (u b) i.succ) 0 x +
          ∑ c, S.A b c x * pd (pd (u c) k.succ) 0 x := by
      have := sum_sum_ite_left b 2 (fun c (i : Fin d) => pd (S.β i) k.succ x * pd (pd (u c) i.succ) 0 x)
      have h2 := sum_sum_ite_right k (fun c (i : Fin d) => S.A b c x * pd (pd (u c) i.succ) 0 x)
      rw [← this, ← h2, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hB : ∑ c, ∑ i : Fin d, ∑ j : Fin d, ((if b = c then 1 else 0) * pd (S.γ j i) k.succ x +
          (if i = k then 1 else 0) * S.B j b c x) * pd (pd (u c) i.succ) j.succ x =
        ∑ i : Fin d, ∑ j : Fin d, pd (S.γ i j) k.succ x * pd (pd (u b) j.succ) i.succ x +
          ∑ c, ∑ j : Fin d, S.B j b c x * pd (pd (u c) k.succ) j.succ x := by
      have h1 := sum_sum_ite_left b 1 (fun c (i : Fin d) =>
        ∑ j : Fin d, pd (S.γ j i) k.succ x * pd (pd (u c) i.succ) j.succ x)
      have h2 := sum_sum_ite_right k (fun c (i : Fin d) =>
        ∑ j : Fin d, S.B j b c x * pd (pd (u c) i.succ) j.succ x)
      have h3 : ∑ i : Fin d, ∑ j : Fin d, pd (S.γ j i) k.succ x * pd (pd (u b) i.succ) j.succ x =
          ∑ i : Fin d, ∑ j : Fin d, pd (S.γ i j) k.succ x * pd (pd (u b) j.succ) i.succ x :=
        Finset.sum_comm
      rw [← h3, ← one_mul (∑ i : Fin d, ∑ j : Fin d, pd (S.γ j i) k.succ x *
        pd (pd (u b) i.succ) j.succ x), ← h1, ← h2, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have hC : ∑ c, ∑ i : Fin d, (if i = k then 1 else 0) * S.C b c x * pd (u c) i.succ x =
        ∑ c, S.C b c x * pd (u c) k.succ x := by
      have := sum_sum_ite_right k (fun c (i : Fin d) => S.C b c x * pd (u c) i.succ x)
      rw [← this]
      exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => by ring
    have hsplit : ∑ c, ∑ i : Fin d,
        ((((if b = c then 2 else 0) * pd (S.β i) k.succ x +
          (if i = k then 1 else 0) * S.A b c x) * pd (pd (u c) i.succ) 0 x +
        ∑ j : Fin d, ((if b = c then 1 else 0) * pd (S.γ j i) k.succ x +
          (if i = k then 1 else 0) * S.B j b c x) * pd (pd (u c) i.succ) j.succ x) +
        (if i = k then 1 else 0) * S.C b c x * pd (u c) i.succ x) =
        ∑ c, ∑ i : Fin d, (((if b = c then 2 else 0) * pd (S.β i) k.succ x +
          (if i = k then 1 else 0) * S.A b c x) * pd (pd (u c) i.succ) 0 x) +
        ∑ c, ∑ i : Fin d, ∑ j : Fin d, ((if b = c then 1 else 0) * pd (S.γ j i) k.succ x +
          (if i = k then 1 else 0) * S.B j b c x) * pd (pd (u c) i.succ) j.succ x +
        ∑ c, ∑ i : Fin d, (if i = k then 1 else 0) * S.C b c x * pd (u c) i.succ x := by
      simp only [← Finset.sum_add_distrib]
    rw [hsplit, hA, hB, hC]
    simp only [Finset.sum_add_distrib, mul_add, Finset.mul_sum]
    ring

end SysHyp

theorem DerivBound.const_mul {T : ℝ} {r : ℕ} {f : ST d → ℝ} {M : ℝ} (hf : DerivBound T r f M)
    (hfs : ContDiff ℝ ∞ f) {a : ℝ} (ha : |a| ≤ 1) (hM : 0 ≤ M) :
    DerivBound T r (fun x => a * f x) M := fun w hw x hx => by
  have e := dW_lincomb (w.map Fin.succ) hfs hfs a 0
  simp only [zero_mul, add_zero] at e
  rw [e]
  calc |a * dW (w.map Fin.succ) f x| = |a| * |dW (w.map Fin.succ) f x| := abs_mul _ _
    _ ≤ 1 * M := mul_le_mul ha (hf w hw x hx) (abs_nonneg _) zero_le_one
    _ = M := one_mul M

theorem abs_ite_le (p : Prop) [Decidable p] {a : ℝ} (ha : 0 ≤ a) :
    |(if p then a else 0)| ≤ a := by
  split_ifs <;> simp [abs_of_nonneg ha, ha]

theorem isSPeriodic_lincomb {f g : ST d → ℝ} (hf : IsSPeriodic f) (hg : IsSPeriodic g) (a b : ℝ) :
    IsSPeriodic (fun x => a * f x + b * g x) := fun k x => by simp only [hf k x, hg k x]

theorem isSPeriodic_const (c : ℝ) : IsSPeriodic (fun _ : ST d => c) := fun _ _ => rfl

namespace SysHyp

variable [DecidableEq ι] {S : WaveSys d ι} {u F : ι → ST d → ℝ} {T lam M : ℝ} {r : ℕ}

set_option maxHeartbeats 800000 in
/-- **Prolongation**: if `u` solves the system `S` with forcing `F` and coefficient bounds of order
`r + 1`, then `V = (u, ∂u)` solves the prolonged system with forcing `(F, ∂F)` and coefficient
bounds of order `r` (constant `3M`). -/
theorem prolong (h : SysHyp S u F T lam M (r + 1)) :
    SysHyp S.prolong (pU u) (pU F) T lam (3 * M) r := by
  have hM := h.M_nonneg
  have hM3 : M ≤ 3 * M := by linarith
  have h2 : |(2 : ℝ)| ≤ 2 := by norm_num
  refine
    { su := ?_, sF := ?_, sβ := h.sβ, sγ := h.sγ, sA := ?_, sB := ?_, sC := ?_,
      pu := ?_, pF := ?_, pβ := h.pβ, pγ := h.pγ, pA := ?_, pB := ?_, pC := ?_,
      eqn := fun x hx p => h.prolong_eqn hx p, γ_symm := h.γ_symm, coer := h.coer,
      M_nonneg := by linarith,
      bβ := fun i => ((h.bβ i).of_succ).mono hM3, bγ := fun i j => ((h.bγ i j).of_succ).mono hM3,
      bA := ?_, bB := ?_, bC := ?_,
      bβx := fun x hx i j => (h.bβx x hx i j).trans hM3,
      bγ1 := fun x hx i j μ => (h.bγ1 x hx i j μ).trans hM3 }
  · rintro ⟨b, _ | k⟩
    · exact h.su b
    · exact contDiff_pd_top (h.su b) _
  · rintro ⟨b, _ | k⟩
    · exact h.sF b
    · exact contDiff_pd_top (h.sF b) _
  · rintro ⟨b, _ | k⟩ ⟨c, _ | i⟩
    · exact h.sA b c
    · exact contDiff_const
    · exact contDiff_pd_top (h.sA b c) _
    · exact (contDiff_const.mul (contDiff_pd_top (h.sβ i) _)).add (contDiff_const.mul (h.sA b c))
  · rintro j ⟨b, _ | k⟩ ⟨c, _ | i⟩
    · exact h.sB j b c
    · exact contDiff_const
    · exact contDiff_pd_top (h.sB j b c) _
    · exact (contDiff_const.mul (contDiff_pd_top (h.sγ j i) _)).add
        (contDiff_const.mul (h.sB j b c))
  · rintro ⟨b, _ | k⟩ ⟨c, _ | i⟩
    · exact h.sC b c
    · exact contDiff_const
    · exact contDiff_pd_top (h.sC b c) _
    · exact contDiff_const.mul (h.sC b c)
  · rintro ⟨b, _ | k⟩
    · exact h.pu b
    · exact isSPeriodic_pd (h.pu b) _
  · rintro ⟨b, _ | k⟩
    · exact h.pF b
    · exact isSPeriodic_pd (h.pF b) _
  · rintro ⟨b, _ | k⟩ ⟨c, _ | i⟩
    · exact h.pA b c
    · exact isSPeriodic_const 0
    · exact isSPeriodic_pd (h.pA b c) _
    · exact isSPeriodic_lincomb (isSPeriodic_pd (h.pβ i) _) (h.pA b c) _ _
  · rintro j ⟨b, _ | k⟩ ⟨c, _ | i⟩
    · exact h.pB j b c
    · exact isSPeriodic_const 0
    · exact isSPeriodic_pd (h.pB j b c) _
    · exact isSPeriodic_lincomb (isSPeriodic_pd (h.pγ j i) _) (h.pB j b c) _ _
  · rintro ⟨b, _ | k⟩ ⟨c, _ | i⟩
    · exact h.pC b c
    · exact isSPeriodic_const 0
    · exact isSPeriodic_pd (h.pC b c) _
    · exact fun n x => by
        show (if i = k then 1 else 0) * S.C b c (x + sshift n) = (if i = k then 1 else 0) * S.C b c x
        rw [h.pC b c n x]
  · rintro ⟨b, _ | k⟩ ⟨c, _ | i⟩
    · exact ((h.bA b c).of_succ).mono hM3
    · exact DerivBound.zero (by linarith)
    · exact ((h.bA b c).pd _).mono hM3
    · have := DerivBound.lincomb ((h.bβ i).pd k) ((h.bA b c).of_succ)
        (contDiff_pd_top (h.sβ i) _) (h.sA b c) (a := if b = c then 2 else 0)
        (b := if i = k then 1 else 0) (abs_ite_le _ (by norm_num)) (abs_ite_le _ zero_le_one) hM
      refine this.mono (by linarith)
  · rintro j ⟨b, _ | k⟩ ⟨c, _ | i⟩
    · exact ((h.bB j b c).of_succ).mono hM3
    · exact DerivBound.zero (by linarith)
    · exact ((h.bB j b c).pd _).mono hM3
    · have := DerivBound.lincomb ((h.bγ j i).pd k) ((h.bB j b c).of_succ)
        (contDiff_pd_top (h.sγ j i) _) (h.sB j b c) (a := if b = c then 1 else 0)
        (b := if i = k then 1 else 0) ((abs_ite_le _ zero_le_one).trans (by norm_num))
        (abs_ite_le _ zero_le_one) hM
      refine this.mono (by linarith)
  · rintro ⟨b, _ | k⟩ ⟨c, _ | i⟩
    · exact ((h.bC b c).of_succ).mono hM3
    · exact DerivBound.zero (by linarith)
    · exact ((h.bC b c).pd _).mono hM3
    · exact (((h.bC b c).of_succ).const_mul (h.sC b c) (abs_ite_le _ zero_le_one) hM).mono hM3

end SysHyp

/-! ### The `k`-fold prolongation and the `H^k` energy estimate -/

universe v

/-- The index type `ι × Option (Fin d) × ⋯` of the `k`-fold prolongation. -/
def PIdx (d : ℕ) : ℕ → Type v → Type v
  | 0, ι => ι
  | k + 1, ι => PIdx d k (ι × Option (Fin d))

/-- `PIdx` is finite. -/
def PIdx.fintype : (k : ℕ) → (ι : Type v) → [Fintype ι] → Fintype (PIdx d k ι)
  | 0, _, h => h
  | k + 1, ι, _ => PIdx.fintype k (ι × Option (Fin d))

/-- `PIdx` has decidable equality. -/
def PIdx.decEq : (k : ℕ) → (ι : Type v) → [DecidableEq ι] → DecidableEq (PIdx d k ι)
  | 0, _, h => h
  | k + 1, ι, _ => PIdx.decEq k (ι × Option (Fin d))

instance (k : ℕ) (ι : Type v) [Fintype ι] : Fintype (PIdx d k ι) := PIdx.fintype k ι
instance (k : ℕ) (ι : Type v) [DecidableEq ι] : DecidableEq (PIdx d k ι) := PIdx.decEq k ι

/-- The `k`-fold prolonged system. -/
def prolongK : (k : ℕ) → {ι : Type v} → [Fintype ι] → [DecidableEq ι] → WaveSys d ι →
    WaveSys d (PIdx d k ι)
  | 0, _, _, _, S => S
  | k + 1, _, _, _, S => prolongK k S.prolong

/-- The `k`-fold prolongation `(∂^w u)_{w ∈ Option (Fin d)^k}` of a field. -/
def pUK : (k : ℕ) → {ι : Type v} → (ι → ST d → ℝ) → PIdx d k ι → ST d → ℝ
  | 0, _, u => u
  | k + 1, _, u => pUK k (pU u)

theorem prolongK_γ : ∀ (k : ℕ) {ι : Type v} [Fintype ι] [DecidableEq ι] (S : WaveSys d ι),
    (prolongK k S).γ = S.γ
  | 0, _, _, _, _ => rfl
  | k + 1, _, _, _, S => prolongK_γ k S.prolong

theorem prolongK_β : ∀ (k : ℕ) {ι : Type v} [Fintype ι] [DecidableEq ι] (S : WaveSys d ι),
    (prolongK k S).β = S.β
  | 0, _, _, _, _ => rfl
  | k + 1, _, _, _, S => prolongK_β k S.prolong

/-- **Iterated prolongation**: bounds of order `r + k` give the `k`-fold prolonged system with
bounds of order `r` and constant `3^k M`. -/
theorem SysHyp.prolongK {T lam : ℝ} {r : ℕ} : ∀ (k : ℕ) {ι : Type v} [Fintype ι] [DecidableEq ι]
    {S : WaveSys d ι} {u F : ι → ST d → ℝ} {M : ℝ}, SysHyp S u F T lam M (r + k) →
    SysHyp (prolongK k S) (pUK k u) (pUK k F) T lam (3 ^ k * M) r
  | 0, _, _, _, S, u, F, M, h => by
    show SysHyp S u F T lam (3 ^ 0 * M) r
    rw [pow_zero, one_mul]; exact h
  | k + 1, _, _, _, S, u, F, M, h => by
    have := SysHyp.prolongK k (h.prolong (r := r + k))
    rw [show 3 ^ (k + 1) * M = 3 ^ k * (3 * M) by ring]
    exact this

/-- Pointwise bound of the first-order lower part. -/
theorem lower_sq_le (S : WaveSys d ι) (u : ι → ST d → ℝ) (x : ST d) {K : ℝ} (hK : 0 ≤ K)
    (hA : ∀ b c, |S.A b c x| ≤ K) (hB : ∀ i b c, |S.B i b c x| ≤ K) (hC : ∀ b c, |S.C b c x| ≤ K) :
    ∑ b, S.lower u b x ^ 2 ≤ (K * (Fintype.card ι + 1) ^ 2 * (d + 2)) ^ 2 * size u x := by
  set s := size u x
  have hs : 0 ≤ s := L2Hyp.size_nonneg u x
  set N : ℝ := (Fintype.card ι : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hterm : ∀ c, pd (u c) 0 x ^ 2 + ∑ i : Fin d, pd (u c) i.succ x ^ 2 + u c x ^ 2 ≤ s := fun c =>
    Finset.single_le_sum (f := fun c => pd (u c) 0 x ^ 2 + ∑ i : Fin d, pd (u c) i.succ x ^ 2 +
      u c x ^ 2) (fun c _ => by positivity) (Finset.mem_univ c)
  have hv0 : ∀ c, |pd (u c) 0 x| ≤ Real.sqrt s := fun c => Real.abs_le_sqrt (by
    have := hterm c; have : 0 ≤ ∑ i : Fin d, pd (u c) i.succ x ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    nlinarith [sq_nonneg (u c x)])
  have hvi : ∀ c (i : Fin d), |pd (u c) i.succ x| ≤ Real.sqrt s := fun c i => Real.abs_le_sqrt (by
    have := hterm c
    have h1 := Finset.single_le_sum (f := fun i : Fin d => pd (u c) i.succ x ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ i)
    nlinarith [sq_nonneg (u c x), sq_nonneg (pd (u c) 0 x)])
  have hvu : ∀ c, |u c x| ≤ Real.sqrt s := fun c => Real.abs_le_sqrt (by
    have := hterm c; have : 0 ≤ ∑ i : Fin d, pd (u c) i.succ x ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    nlinarith [sq_nonneg (pd (u c) 0 x)])
  have hss := Real.sqrt_nonneg s
  have hlow : ∀ b, |S.lower u b x| ≤ K * N * (d + 2) * Real.sqrt s := by
    intro b
    unfold WaveSys.lower
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ c, |S.A b c x * pd (u c) 0 x + ∑ i : Fin d, S.B i b c x * pd (u c) i.succ x +
        S.C b c x * u c x| ≤ K * (d + 2) * Real.sqrt s := by
      intro c
      have e1 : |S.A b c x * pd (u c) 0 x| ≤ K * Real.sqrt s := by
        rw [abs_mul]; exact mul_le_mul (hA b c) (hv0 c) (abs_nonneg _) hK
      have e2 : |∑ i : Fin d, S.B i b c x * pd (u c) i.succ x| ≤ d * (K * Real.sqrt s) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ i : Fin d, |S.B i b c x * pd (u c) i.succ x| ≤ ∑ _i : Fin d, K * Real.sqrt s :=
              Finset.sum_le_sum fun i _ => by
                rw [abs_mul]; exact mul_le_mul (hB i b c) (hvi c i) (abs_nonneg _) hK
          _ = d * (K * Real.sqrt s) := by simp
      have e3 : |S.C b c x * u c x| ≤ K * Real.sqrt s := by
        rw [abs_mul]; exact mul_le_mul (hC b c) (hvu c) (abs_nonneg _) hK
      calc _ ≤ |S.A b c x * pd (u c) 0 x| + |∑ i : Fin d, S.B i b c x * pd (u c) i.succ x| +
            |S.C b c x * u c x| := abs_add_three _ _ _
        _ ≤ K * Real.sqrt s + d * (K * Real.sqrt s) + K * Real.sqrt s := by linarith
        _ = K * (d + 2) * Real.sqrt s := by ring
    calc _ ≤ ∑ _c : ι, K * (d + 2) * Real.sqrt s := Finset.sum_le_sum fun c _ => this c
      _ = K * N * (d + 2) * Real.sqrt s := by simp [N]; ring
  have hsq : ∀ b, S.lower u b x ^ 2 ≤ (K * N * (d + 2)) ^ 2 * s := by
    intro b
    have h1 := hlow b
    have h2 := sq_le_sq' (neg_le_of_abs_le h1) (le_of_abs_le h1)
    rw [mul_pow, Real.sq_sqrt hs] at h2
    exact h2
  have hd2 : (0 : ℝ) ≤ d + 2 := by positivity
  calc ∑ b, S.lower u b x ^ 2 ≤ ∑ _b : ι, (K * N * (d + 2)) ^ 2 * s :=
        Finset.sum_le_sum fun b _ => hsq b
    _ = N * ((K * N * (d + 2)) ^ 2 * s) := by simp [N]
    _ ≤ (K * (N + 1) ^ 2 * (d + 2)) ^ 2 * s := by
        have hKd : 0 ≤ (K * (d + 2)) ^ 2 * s := by positivity
        have e : N * ((K * N * (d + 2)) ^ 2 * s) = N ^ 3 * ((K * (d + 2)) ^ 2 * s) := by ring
        have e' : (K * (N + 1) ^ 2 * (d + 2)) ^ 2 * s = (N + 1) ^ 4 * ((K * (d + 2)) ^ 2 * s) := by
          ring
        rw [e, e']
        refine mul_le_mul_of_nonneg_right ?_ hKd
        nlinarith [pow_le_pow_left₀ hN (le_add_of_nonneg_right zero_le_one : N ≤ N + 1) 3,
          pow_nonneg hN 3]

/-- The constant `M_k = 3^k M` bounding the coefficients of the `k`-fold prolongation. -/
def Mk (k : ℕ) (M : ℝ) : ℝ := 3 ^ k * M

/-- The lower-order constant `m_k = M_k (|ι_k| + 1)² (d + 2)` of the `k`-fold prolongation. -/
def mk (d : ℕ) (ι : Type v) [Fintype ι] (k : ℕ) (M : ℝ) : ℝ :=
  Mk k M * (Fintype.card (PIdx d k ι) + 1) ^ 2 * (d + 2)

/-- The order-`k` energy `E_k(t) = Σ_{w ∈ Option (Fin d)^k} E(∂^w u)(t)`: the wave energy of the
`k`-fold prolongation. -/
def energyK (k : ℕ) {ι : Type v} [Fintype ι] (γ : Fin d → Fin d → ST d → ℝ) (u : ι → ST d → ℝ)
    (t : ℝ) : ℝ :=
  energy γ (pUK k u) t

/-- The `H^k`-type norm `(Σ_w ‖∂^w F(t)‖²_{L²})^{1/2}` of the forcing. -/
def normK (k : ℕ) {ι : Type v} [Fintype ι] (F : ι → ST d → ℝ) (t : ℝ) : ℝ :=
  l2norm (pUK k F) t

/-- The `L²` hypotheses of an order-`0` system. -/
theorem SysHyp.toL2Hyp {ι : Type v} [Fintype ι] [DecidableEq ι] {S : WaveSys d ι}
    {u F : ι → ST d → ℝ} {T lam M : ℝ} (h : SysHyp S u F T lam M 0) :
    L2Hyp S.β S.γ u (S.lower u) F
      (fun _ => M * (Fintype.card ι + 1) ^ 2 * (d + 2)) T lam M where
  cu := fun b => (h.su b).of_le (by norm_cast)
  cβ := fun i => (h.sβ i).of_le (by norm_cast)
  cγ := fun i j => (h.sγ i j).of_le (by norm_cast)
  cL := fun b => by
    unfold WaveSys.lower
    have := fun c => (h.su c).continuous
    have := fun c μ => (contDiff_pd_top (h.su c) μ).continuous
    have := fun c c' => (h.sA c c').continuous
    have := fun i c c' => (h.sB i c c').continuous
    have := fun c c' => (h.sC c c').continuous
    fun_prop
  cF := fun b => (h.sF b).continuous
  cm := continuous_const
  pu := h.pu
  pβ := h.pβ
  pγ := h.pγ
  eqn := fun x hx b => by
    rw [h.eqn x hx b]; unfold WaveSys.princ; ring
  γ_symm := h.γ_symm
  coer := h.coer
  bβ := fun x hx i => h.bβx x hx i i
  bγt := fun x hx i j => h.bγ1 x hx i j 0
  bγx := fun x hx i j => h.bγ1 x hx i j i.succ
  m_nonneg := fun _ => by have := h.M_nonneg; positivity
  M_nonneg := h.M_nonneg
  bL := fun x hx => lower_sq_le S u x h.M_nonneg (fun b c => h.bA b c [] (by simp) x hx)
    (fun i b c => h.bB i b c [] (by simp) x hx) (fun b c => h.bC b c [] (by simp) x hx)

/-- **The linear `H^k` wave energy estimate with an `L¹_t H^k_x` source** on `[0, T] × 𝕋^d`:
for smooth periodic solutions of `∂ₜ²u = 2βⁱ∂ᵢ∂ₜu + γ^{ij}∂ᵢ∂ⱼu + Σ_c(A ∂ₜu + Bⁱ∂ᵢu + C u) + F`
with `γ` symmetric and `λ`-coercive, all spatial derivatives of order `≤ k` of the coefficients
and the first derivatives `∂ᵢβ`, `∂γ` bounded by `M` on the slab (`L^∞_t W^{k,∞}_x` coefficients),
the order-`k` energy satisfies, for `t ∈ [0, T]`,
`√E_k(t) ≤ (√E_k(0) + c^{-1/2} ∫₀ᵗ ‖F(s)‖_{H^k}) exp(½ ∫₀ᵗ K_k)`,
`K_k = ((d+1)² M_k + 1 + 2 m_k)/c`, `c = min(λ, 1)`, `M_k = 3^k M`,
`m_k = M_k (|ι_k| + 1)² (d + 2)` — constants depending only on `d, |ι|, k, λ, M`. -/
theorem hk_energy (k : ℕ) {ι : Type v} [Fintype ι] [DecidableEq ι] {S : WaveSys d ι}
    {u F : ι → ST d → ℝ} {T lam M : ℝ} (h : SysHyp S u F T lam M k) (hlam : 0 < lam) :
    ∀ t ∈ Icc 0 T, Real.sqrt (energyK k S.γ u t) ≤
      (Real.sqrt (energyK k S.γ u 0) + ∫ s in (0)..t, (Real.sqrt (L2Hyp.cmin lam))⁻¹ * normK k F s) *
        Real.exp ((∫ s in (0)..t, L2Hyp.kcoef d (Mk k M) (fun _ => mk d ι k M) (L2Hyp.cmin lam) s) /
          2) := by
  have hK := SysHyp.prolongK (r := 0) k (by rw [Nat.zero_add]; exact h)
  have hL := hK.toL2Hyp
  rw [prolongK_γ] at hL
  exact hL.sqrt_energy_le hlam

/-! ### Forcing controlled by the energy (`eq:hyperbolic-energy`) -/

/-- The `L²` estimate when the forcing is controlled by the energy itself:
`‖F(t)‖_{L²} ≤ a(t) √E(t) + σ(t)` with continuous `a, σ ≥ 0` gives
`√E(t) ≤ (√E(0) + c^{-1/2}∫₀ᵗ σ) exp(½∫₀ᵗ (k + 2c^{-1/2} a))`. -/
theorem L2Hyp.sqrt_energy_le_of_forcing {β : Fin d → ST d → ℝ} {γ : Fin d → Fin d → ST d → ℝ}
    {u L₀ F : ι → ST d → ℝ} {m : ℝ → ℝ} {T lam M : ℝ} (h : L2Hyp β γ u L₀ F m T lam M)
    (hlam : 0 < lam) {a σ : ℝ → ℝ} (ha : Continuous a) (hσ : Continuous σ) (ha0 : ∀ t, 0 ≤ a t)
    (hσ0 : ∀ t, 0 ≤ σ t)
    (hF : ∀ t ∈ Icc 0 T, l2norm F t ≤ a t * Real.sqrt (energy γ u t) + σ t) :
    ∀ t ∈ Icc 0 T, Real.sqrt (energy γ u t) ≤
      (Real.sqrt (energy γ u 0) + ∫ s in (0)..t, (Real.sqrt (L2Hyp.cmin lam))⁻¹ * σ s) *
        Real.exp ((∫ s in (0)..t, (L2Hyp.kcoef d M m (L2Hyp.cmin lam) s +
          2 * (Real.sqrt (L2Hyp.cmin lam))⁻¹ * a s)) / 2) := by
  intro t ht
  set q := (Real.sqrt (L2Hyp.cmin lam))⁻¹
  have hq : 0 ≤ q := inv_nonneg.2 (Real.sqrt_nonneg _)
  refine TorusWaveEnergyForced.sqrt_energy_gronwall
    (E' := fun s => ∫ y in Icc (0 : Fin d → ℝ) 1, densT γ u (Fin.cons s y))
    h.continuous_energy.continuousOn (fun s hs => L2Hyp.energy_nonneg h hlam hs)
    (fun s _ => L2Hyp.hasDerivAt_energy h s)
    ((by unfold L2Hyp.kcoef; have := h.cm; fun_prop : Continuous (L2Hyp.kcoef d M m
      (L2Hyp.cmin lam))).add (continuous_const.mul ha))
    (continuous_const.mul hσ) (fun s => ?_) (fun s => mul_nonneg hq (hσ0 s)) (fun s hs => ?_) t ht
  · have h1 : 0 ≤ L2Hyp.kcoef d M m (L2Hyp.cmin lam) s := by
      unfold L2Hyp.kcoef
      have := h.m_nonneg s; have := h.M_nonneg
      have : 0 < L2Hyp.cmin lam := lt_min hlam one_pos
      positivity
    have h2 : 0 ≤ 2 * q * a s := mul_nonneg (mul_nonneg zero_le_two hq) (ha0 s)
    show 0 ≤ L2Hyp.kcoef d M m (L2Hyp.cmin lam) s + 2 * q * a s
    linarith
  · have hsc := Ioo_subset_Icc_self hs
    have h1 := L2Hyp.energy_deriv_le h hlam hsc
    have hE := L2Hyp.energy_nonneg h hlam hsc
    have hsq := Real.mul_self_sqrt hE
    have h2 : 2 * (q * l2norm F s) * Real.sqrt (energy γ u s) ≤
        2 * q * a s * energy γ u s + 2 * (q * σ s) * Real.sqrt (energy γ u s) := by
      have := mul_le_mul_of_nonneg_left (hF s hsc) (mul_nonneg (mul_nonneg zero_le_two hq)
        (Real.sqrt_nonneg _) : 0 ≤ 2 * q * Real.sqrt (energy γ u s))
      have e : 2 * q * Real.sqrt (energy γ u s) * (a s * Real.sqrt (energy γ u s) + σ s) =
          2 * q * a s * (Real.sqrt (energy γ u s) * Real.sqrt (energy γ u s)) +
            2 * (q * σ s) * Real.sqrt (energy γ u s) := by ring
      rw [hsq] at e
      linarith
    show _ ≤ (L2Hyp.kcoef d M m (L2Hyp.cmin lam) s + 2 * q * a s) * energy γ u s +
      2 * (q * σ s) * Real.sqrt (energy γ u s)
    linarith

/-- **`eq:hyperbolic-energy` (abstract form)**: the order-`k` energy estimate when the forcing is
controlled by the energy, `‖F(t)‖_{H^k} ≤ a(t) √E_k(t) + σ(t)`:
`√E_k(t) ≤ (√E_k(0) + c^{-1/2}∫₀ᵗ σ) exp(½∫₀ᵗ (K_k + 2c^{-1/2} a))`. -/
theorem hk_energy_of_forcing (k : ℕ) {ι : Type v} [Fintype ι] [DecidableEq ι] {S : WaveSys d ι}
    {u F : ι → ST d → ℝ} {T lam M : ℝ} (h : SysHyp S u F T lam M k) (hlam : 0 < lam)
    {a σ : ℝ → ℝ} (ha : Continuous a) (hσ : Continuous σ) (ha0 : ∀ t, 0 ≤ a t)
    (hσ0 : ∀ t, 0 ≤ σ t)
    (hF : ∀ t ∈ Icc 0 T, normK k F t ≤ a t * Real.sqrt (energyK k S.γ u t) + σ t) :
    ∀ t ∈ Icc 0 T, Real.sqrt (energyK k S.γ u t) ≤
      (Real.sqrt (energyK k S.γ u 0) + ∫ s in (0)..t, (Real.sqrt (L2Hyp.cmin lam))⁻¹ * σ s) *
        Real.exp ((∫ s in (0)..t, (L2Hyp.kcoef d (Mk k M) (fun _ => mk d ι k M)
          (L2Hyp.cmin lam) s + 2 * (Real.sqrt (L2Hyp.cmin lam))⁻¹ * a s)) / 2) := by
  have hK := SysHyp.prolongK (r := 0) k (by rw [Nat.zero_add]; exact h)
  have hL := hK.toL2Hyp
  rw [prolongK_γ] at hL
  exact hL.sqrt_energy_le_of_forcing hlam ha hσ ha0 hσ0 hF

/-! ### The order-`k` energy controls every derivative of order `≤ k` -/

/-- Every iterated spatial derivative `∂^w u_b` of order `|w| ≤ k` is a component of the
`k`-fold prolongation. -/
theorem exists_pUK_eq : ∀ (k : ℕ) {ι : Type v} (u : ι → ST d → ℝ) (b : ι) (w : List (Fin d)),
    w.length ≤ k → ∃ p : PIdx d k ι, pUK k u p = dW (w.map Fin.succ) (u b)
  | 0, _, u, b, w, hw => by
    have : w = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hw)
    subst this
    exact ⟨b, rfl⟩
  | k + 1, _, u, b, [], _ => exists_pUK_eq k (pU u) (b, none) [] (Nat.zero_le _)
  | k + 1, _, u, b, μ :: w, hw => by
    have hw' : w.length ≤ k := by simp only [List.length_cons] at hw; omega
    exact exists_pUK_eq k (pU u) (b, some μ) w hw'

/-- **The order-`k` energy controls all derivatives of order `≤ k`**: for every word `w` with
`|w| ≤ k`, `c ∫ (|∂ₜ∂^w u_b|² + |∇∂^w u_b|² + |∂^w u_b|²) ≤ E_k(t)` — so `E_k` dominates
`c (‖u‖²_{H^{k+1}} + ‖∂ₜu‖²_{H^k})` (classical-derivative norms on the cube). -/
theorem energyK_ge (k : ℕ) {ι : Type v} [Fintype ι] [DecidableEq ι] {S : WaveSys d ι}
    {u F : ι → ST d → ℝ} {T lam M : ℝ} (h : SysHyp S u F T lam M k) (hlam : 0 < lam) {t : ℝ}
    (ht : t ∈ Icc 0 T) (b : ι) (w : List (Fin d)) (hw : w.length ≤ k) :
    L2Hyp.cmin lam * ∫ y in Icc (0 : Fin d → ℝ) 1,
      (pd (dW (w.map Fin.succ) (u b)) 0 (Fin.cons t y) ^ 2 +
        ∑ i : Fin d, pd (dW (w.map Fin.succ) (u b)) i.succ (Fin.cons t y) ^ 2 +
        dW (w.map Fin.succ) (u b) (Fin.cons t y) ^ 2) ≤ energyK k S.γ u t := by
  have hK := SysHyp.prolongK (r := 0) k (by rw [Nat.zero_add]; exact h)
  have hL := hK.toL2Hyp
  rw [prolongK_γ] at hL
  obtain ⟨p, hp⟩ := exists_pUK_eq k u b w hw
  rw [← hp]
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (lt_min hlam one_pos).le)
    (L2Hyp.integral_size_le hL ht)
  have hc := fun q μ => (contDiff_pd_top (hK.su q) μ).continuous
  have hc0 := fun q => (hK.su q).continuous
  refine setIntegral_mono_on (integrableOn_slice (f := fun x => pd (pUK k u p) 0 x ^ 2 +
      ∑ i : Fin d, pd (pUK k u p) i.succ x ^ 2 + pUK k u p x ^ 2) (by fun_prop) t)
    (integrableOn_slice hL.continuous_size t) measurableSet_Icc fun y _ => ?_
  exact Finset.single_le_sum (f := fun q => pd (pUK k u q) 0 (Fin.cons t y) ^ 2 +
    ∑ i : Fin d, pd (pUK k u q) i.succ (Fin.cons t y) ^ 2 + pUK k u q (Fin.cons t y) ^ 2)
    (fun _ _ => by positivity) (Finset.mem_univ p)

/-! ### Non-vacuity: constant coefficients -/

theorem pd_const (c : ℝ) (μ : Fin (d + 1)) : pd (fun _ : ST d => c) μ = fun _ => 0 := by
  funext x; simp [pd]

theorem DerivBound.const {T : ℝ} {r : ℕ} {c M : ℝ} (hc : |c| ≤ M) (hM : 0 ≤ M) :
    DerivBound T r (fun _ : ST d => c) M := by
  intro w _ x _
  cases w with
  | nil => exact hc
  | cons μ w =>
    show |dW (w.map Fin.succ) (SobolevOpen.pd (fun _ : ST d => c) μ.succ) x| ≤ M
    rw [pd_const, dW_zero]; simpa using hM

/-- The flat system `∂ₜ²u = Δu` (constant coefficients). -/
def flatSys (d : ℕ) (ι : Type*) : WaveSys d ι :=
  ⟨fun _ _ => 0, fun i j _ => if i = j then 1 else 0, fun _ _ _ => 0, fun _ _ _ _ => 0,
    fun _ _ _ => 0⟩

theorem flatSys_hyp {ι : Type*} [Fintype ι] (T : ℝ) (k : ℕ) :
    SysHyp (flatSys d ι) (fun _ _ => 0) (fun _ _ => 0) T 1 1 k where
  su := fun _ => contDiff_const
  sF := fun _ => contDiff_const
  sβ := fun _ => contDiff_const
  sγ := fun _ _ => contDiff_const
  sA := fun _ _ => contDiff_const
  sB := fun _ _ _ => contDiff_const
  sC := fun _ _ => contDiff_const
  pu := fun _ => isSPeriodic_const 0
  pF := fun _ => isSPeriodic_const 0
  pβ := fun _ => isSPeriodic_const 0
  pγ := fun _ _ => isSPeriodic_const _
  pA := fun _ _ => isSPeriodic_const 0
  pB := fun _ _ _ => isSPeriodic_const 0
  pC := fun _ _ => isSPeriodic_const 0
  eqn := fun x _ b => by
    simp [WaveSys.princ, WaveSys.lower, flatSys, pd_const]
  γ_symm := fun i j x => by simp only [flatSys, eq_comm]
  coer := fun x _ ξ => by
    simp only [flatSys, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp [sq]
  M_nonneg := zero_le_one
  bβ := fun _ => DerivBound.const (c := 0) (by simp) zero_le_one
  bγ := fun i j => DerivBound.const (c := if i = j then 1 else 0) (by split_ifs <;> simp)
    zero_le_one
  bA := fun _ _ => DerivBound.const (c := 0) (by simp) zero_le_one
  bB := fun _ _ _ => DerivBound.const (c := 0) (by simp) zero_le_one
  bC := fun _ _ => DerivBound.const (c := 0) (by simp) zero_le_one
  bβx := fun x _ i j => by simp [flatSys, pd_const]
  bγ1 := fun x _ i j μ => by simp [flatSys, pd_const]

/-- Non-vacuity of `hk_energy` (flat system, any order `k`, any index type). -/
example (T : ℝ) (k : ℕ) := hk_energy k (flatSys_hyp (d := 3) (ι := Fin 10) T k) one_pos

/-! ### Cauchy data and sources give uniform convergence of the difference energies -/

/-- **The convergence step of `thm:hyperbolic`** (abstract form): for a two-parameter family of
difference systems `(S h j, w h j, F h j)` with common constants `λ, M` (order `k`), forcing bounds
`‖F_{h,j}(t)‖_{H^k} ≤ a_{h,j}(t) √E_k + σ_{h,j}(t)` with `∫₀ᵀ a_{h,j} ≤ A` uniformly, initial
energies `E_k^{h,j}(0) → 0` and source integrals `∫₀ᵀ σ_{h,j} → 0` (Cauchy initial data and
sources), the difference energies tend to zero uniformly on `[0, T]`. -/
theorem energyK_tendsto_zero (k : ℕ) {ι : Type v} [Fintype ι] [DecidableEq ι]
    {S : ℕ → ℕ → WaveSys d ι} {w F : ℕ → ℕ → ι → ST d → ℝ} {T lam M A : ℝ}
    (h : ∀ i j, SysHyp (S i j) (w i j) (F i j) T lam M k) (hlam : 0 < lam) (hT : 0 ≤ T)
    {a σ : ℕ → ℕ → ℝ → ℝ} (ha : ∀ i j, Continuous (a i j)) (hσ : ∀ i j, Continuous (σ i j))
    (ha0 : ∀ i j t, 0 ≤ a i j t) (hσ0 : ∀ i j t, 0 ≤ σ i j t)
    (hF : ∀ i j, ∀ t ∈ Icc 0 T,
      normK k (F i j) t ≤ a i j t * Real.sqrt (energyK k (S i j).γ (w i j) t) + σ i j t)
    (hA : ∀ i j, ∫ s in (0)..T, a i j s ≤ A)
    (h0 : Tendsto (fun p : ℕ × ℕ => energyK k (S p.1 p.2).γ (w p.1 p.2) 0) atTop (𝓝 0))
    (hσT : Tendsto (fun p : ℕ × ℕ => ∫ s in (0)..T, σ p.1 p.2 s) atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ p : ℕ × ℕ in atTop, ∀ t ∈ Icc 0 T,
      Real.sqrt (energyK k (S p.1 p.2).γ (w p.1 p.2) t) ≤ ε := by
  intro ε hε
  set c := L2Hyp.cmin lam
  set q := (Real.sqrt c)⁻¹
  have hq : 0 ≤ q := inv_nonneg.2 (Real.sqrt_nonneg _)
  set K := L2Hyp.kcoef d (Mk k M) (fun _ => mk d ι k M) c 0
  set B := Real.exp ((K * T + 2 * q * A) / 2)
  have hB : 0 < B := Real.exp_pos _
  have hlim : Tendsto (fun p : ℕ × ℕ => Real.sqrt (energyK k (S p.1 p.2).γ (w p.1 p.2) 0) +
      q * ∫ s in (0)..T, σ p.1 p.2 s) atTop (𝓝 0) := by
    have := (h0.sqrt).add (hσT.const_mul q)
    simpa using this
  filter_upwards [hlim.eventually (gt_mem_nhds (show (0 : ℝ) < ε / B by positivity))] with p hp t ht
  have hE := hk_energy_of_forcing k (h p.1 p.2) hlam (ha p.1 p.2) (hσ p.1 p.2) (ha0 p.1 p.2)
    (hσ0 p.1 p.2) (hF p.1 p.2) t ht
  have hint : ∫ s in (0)..t, (L2Hyp.kcoef d (Mk k M) (fun _ => mk d ι k M) c s +
      2 * q * a p.1 p.2 s) ≤ K * T + 2 * q * A := by
    have hc1 : Continuous fun s : ℝ => L2Hyp.kcoef d (Mk k M) (fun _ => mk d ι k M) c s :=
      continuous_const
    rw [intervalIntegral.integral_add (f := fun s => L2Hyp.kcoef d (Mk k M) (fun _ => mk d ι k M) c s)
      (g := fun s => 2 * q * a p.1 p.2 s) (hc1.intervalIntegrable _ _)
      ((continuous_const.mul (ha p.1 p.2)).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul]
    have e1 : ∫ s in (0)..t, L2Hyp.kcoef d (Mk k M) (fun _ => mk d ι k M) c s = t * K := by
      simp [K, L2Hyp.kcoef]; ring
    have hK0 : 0 ≤ K := by
      simp only [K, L2Hyp.kcoef, Mk, mk]
      have := (h p.1 p.2).M_nonneg
      have : 0 < c := lt_min hlam one_pos
      positivity
    have e2 : ∫ s in (0)..t, a p.1 p.2 s ≤ ∫ s in (0)..T, a p.1 p.2 s :=
      intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        (Eventually.of_forall fun s => ha0 p.1 p.2 s) ((ha p.1 p.2).intervalIntegrable _ _)
    rw [e1]
    have := hA p.1 p.2
    have : t * K ≤ T * K := mul_le_mul_of_nonneg_right ht.2 hK0
    nlinarith
  have hσt : ∫ s in (0)..t, q * σ p.1 p.2 s ≤ q * ∫ s in (0)..T, σ p.1 p.2 s := by
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (Eventually.of_forall fun s => hσ0 p.1 p.2 s) ((hσ p.1 p.2).intervalIntegrable _ _)) hq
  have hexp : Real.exp ((∫ s in (0)..t, (L2Hyp.kcoef d (Mk k M) (fun _ => mk d ι k M) c s +
      2 * q * a p.1 p.2 s)) / 2) ≤ B := Real.exp_le_exp.2 (by linarith)
  have hX0 : 0 ≤ Real.sqrt (energyK k (S p.1 p.2).γ (w p.1 p.2) 0) +
      ∫ s in (0)..t, q * σ p.1 p.2 s :=
    add_nonneg (Real.sqrt_nonneg _) (intervalIntegral.integral_nonneg ht.1 fun s _ =>
      mul_nonneg hq (hσ0 p.1 p.2 s))
  calc Real.sqrt (energyK k (S p.1 p.2).γ (w p.1 p.2) t) ≤ _ := hE
    _ ≤ (Real.sqrt (energyK k (S p.1 p.2).γ (w p.1 p.2) 0) + q * ∫ s in (0)..T, σ p.1 p.2 s) * B :=
        mul_le_mul (by linarith) hexp (Real.exp_pos _).le (by linarith)
    _ ≤ ε / B * B := mul_le_mul_of_nonneg_right hp.le hB.le
    _ = ε := by field_simp

end SlabWaveHk

end RenewalGeometry
