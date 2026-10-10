/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.CubeReflectionAverage
import RenewalGeometry.Analysis.CubeCoulombApriori

/-!
# The linearised Coulomb operator with the Neumann condition on the cube: an isomorphism
  (stages B2–B3 of the cube rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript (K. Uhlenbeck, CMP 83 (1982), Thm 1.3, the
linear input of the implicit-function step of the continuity method on a domain).

On `Q₀ = (0,1/2)⁴`, for a matrix-valued connection `a ∈ L⁴(Q₀)` with small norm and **no
boundary condition**, and a datum `h ∈ L²(Q₀)` (matrix-valued one-form), the problem

  `d^*(dξ + [a, ξ]) = d^* h` in `Q₀`,  `(dξ + [a, ξ] - h)·ν = 0` on `∂Q₀`

is posed in the weak (natural Neumann) form `CubeWeakLinCoulomb`: for every `φ ∈ W^{1,2}(Q₀)`,
`Σ_μ ∫_{Q₀} conj(∂_μ φ) (dξ + [a,ξ])_μ = Σ_μ ∫_{Q₀} conj(∂_μ φ) h_μ`.  The inhomogeneous normal
datum `h·ν` (the "lift" of the boundary condition of the continuity method, where `h` is built
from the variation of the connection) is carried by the `L²` form `h` itself, so no trace theory
is needed at this level.

* `cCovLin`, `CubeWeakLinCoulomb`; `covLin_ext` (the torus `d_a` of the reflected data is the
  reflection of the cube `d_a`);
* `cubeWeak_iff_torusWeak` (**equivalence of the weak formulations**): for cube data, the cube
  equation tested against `W^{1,2}(Q₀)` is equivalent to the torus equation of the reflected data
  tested against all of `H¹(𝕋⁴)` (`avgEven`: testing against even functions suffices);
* `linearized_coulomb_cube` (**main theorem**): if `Σ_{μce} ‖a_{μ,ce}‖_{L⁴(Q₀)} ≤ 1/224` then for
  every `h ∈ L²(Q₀)` there is a unique mean-zero `ξ ∈ W^{1,2}(Q₀)` solving `CubeWeakLinCoulomb`,
  with `‖∂_μ ξ_{ce}‖_{L²(Q₀)} ≤ 2 Σ ‖h‖_{L²(Q₀)}`.  Proof: reflection, the torus isomorphism
  `UhlenbeckOpenness.linearized_coulomb_iso` restricted to the symmetric class
  (`linearized_coulomb_iso_even`), restriction.
-/

open MeasureTheory Filter Topology Set UnitAddTorus
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace RenewalGeometry.CubeNeumann

open SobolevOpen TorusSobolev UhlenbeckTorus UhlenbeckOpenness

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local notation "𝕋⁴" => UnitAddTorus (Fin 4)

variable {m : ℕ}

/-- The linearised covariant derivative `(d_a ξ)_μ = ∂_μ ξ + [a_μ, ξ]` on the cube (entries). -/
def cCovLin (a : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ) (ξ : Fin m → Fin m → (Fin 4 → ℝ) → ℂ)
    (dξ : Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ) (c e : Fin m) (μ : Fin 4) (x : Fin 4 → ℝ) :
    ℂ :=
  dξ c e μ x + ∑ k, (a μ c k x * ξ k e x - ξ c k x * a μ k e x)

/-- **The weak Neumann linearised Coulomb equation on the cube**: `d^* d_a ξ = d^* h` in `Q₀` with
the natural boundary condition `(d_a ξ - h)·ν = 0`, tested against all `φ ∈ W^{1,2}(Q₀)`. -/
def CubeWeakLinCoulomb (a : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ)
    (h : Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ) (ξ : Fin m → Fin m → (Fin 4 → ℝ) → ℂ)
    (dξ : Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ) : Prop :=
  ∀ (φ : (Fin 4 → ℝ) → ℂ) (gφ : Fin 4 → (Fin 4 → ℝ) → ℂ), MemW12 Q0 φ gφ → ∀ c e,
    ∑ μ, ∫ x in Q0, conj (gφ μ x) * cCovLin a ξ dξ c e μ x =
      ∑ μ, ∫ x in Q0, conj (gφ μ x) * h c e μ x

/-- Reflected connection. -/
def extA (a : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ) : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ :=
  fun μ c e => parExt {μ} (a μ c e)

/-- Reflected datum. -/
def extH (h : Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ) : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ :=
  fun c e μ => parExt {μ} (h c e μ)

/-- Reflected (even) gauge parameter. -/
def extXi (ξ : Fin m → Fin m → (Fin 4 → ℝ) → ℂ) : Fin m → Fin m → 𝕋⁴ → ℂ :=
  fun c e => parExt ∅ (ξ c e)

/-- Reflected gradient of the gauge parameter. -/
def extDXi (dξ : Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ) : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ :=
  fun c e μ => parExt {μ} (dξ c e μ)

theorem symmDiff_empty_singleton (μ : Fin 4) : symmDiff (∅ : Finset (Fin 4)) {μ} = {μ} := by
  ext; simp [Finset.mem_symmDiff]

theorem symmDiff_singleton_empty (μ : Fin 4) : symmDiff ({μ} : Finset (Fin 4)) ∅ = {μ} := by
  ext; simp [Finset.mem_symmDiff]

/-- The torus `d_a ξ` of reflected data is the reflection of the cube `d_a ξ`. -/
theorem covLin_ext (a : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ)
    (ξ : Fin m → Fin m → (Fin 4 → ℝ) → ℂ) (dξ : Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ)
    (c e : Fin m) (μ : Fin 4) :
    covLin (extA a) (extXi ξ) (extDXi dξ) c e μ = parExt {μ} (cCovLin a ξ dξ c e μ) := by
  funext t
  simp only [covLin, extA, extXi, extDXi, parExt_mul, symmDiff_empty_singleton,
    symmDiff_singleton_empty]
  have e : cCovLin a ξ dξ c e μ = fun x => dξ c e μ x +
      ∑ k, (a μ c k x * ξ k e x - ξ c k x * a μ k e x) := rfl
  rw [e, parExt_add, parExt_finset_sum]
  simp only [parExt_sub]

theorem memLp_cCovLin {a : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ}
    (ha : ∀ μ c e, MemLp (a μ c e) 4 (volume.restrict Q0))
    {ξ : Fin m → Fin m → (Fin 4 → ℝ) → ℂ} {dξ : Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ}
    (hξ : ∀ c e, MemW12 Q0 (ξ c e) (dξ c e)) (c e : Fin m) (μ : Fin 4) :
    MemLp (cCovLin a ξ dξ c e μ) 2 (volume.restrict Q0) := by
  have h4 : ∀ c e, MemLp (ξ c e) 4 (volume.restrict Q0) := fun c e => (sobolev_cube (hξ c e)).1
  unfold cCovLin
  refine ((hξ c e).memLp_grad μ).add (memLp_finsetSum _ fun k _ => ?_)
  exact ((h4 k e).mul' (ha μ c k) (r := 2)).sub ((ha μ k e).mul' (h4 c k) (r := 2))

/-- **Equivalence of the weak formulations** (cube with `W^{1,2}(Q₀)` tests versus torus with all
`H¹(𝕋⁴)` tests) for cube data. -/
theorem cubeWeak_iff_torusWeak {a : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ}
    (ha : ∀ μ c e, MemLp (a μ c e) 4 (volume.restrict Q0))
    {h : Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ}
    (hh : ∀ c e μ, MemLp (h c e μ) 2 (volume.restrict Q0))
    {ξ : Fin m → Fin m → (Fin 4 → ℝ) → ℂ} {dξ : Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ}
    (hξ : ∀ c e, MemW12 Q0 (ξ c e) (dξ c e)) :
    CubeWeakLinCoulomb a h ξ dξ ↔ WeakLinCoulomb (extA a) (extH h) (extXi ξ) (extDXi dξ) := by
  have hC := memLp_cCovLin ha hξ
  -- transfer of one test function on the cube side
  have key : ∀ (φ : (Fin 4 → ℝ) → ℂ) (gφ : Fin 4 → (Fin 4 → ℝ) → ℂ), MemW12 Q0 φ gφ →
      ∀ c e μ, (∫ t, conj (parExt {μ} (gφ μ) t) * covLin (extA a) (extXi ξ) (extDXi dξ) c e μ t =
        16 * ∫ x in Q0, conj (gφ μ x) * cCovLin a ξ dξ c e μ x) ∧
      (∫ t, conj (parExt {μ} (gφ μ) t) * extH h c e μ t =
        16 * ∫ x in Q0, conj (gφ μ x) * h c e μ x) := by
    intro φ gφ hφ c e μ
    refine ⟨?_, integral_conj_parExt_mul (hφ.memLp_grad μ) (hh c e μ)⟩
    rw [covLin_ext]
    exact integral_conj_parExt_mul (hφ.memLp_grad μ) (hC c e μ)
  have h16 : (16 : ℂ) ≠ 0 := by norm_num
  constructor
  · -- cube ⟹ torus: test against the even part
    intro hcube u gu hu hgu hdu c e
    set v := avgEven u
    set gv := avgEvenGrad gu
    have hv : MemLp v 2 volume := memLp_avgEven hu
    have hgv : ∀ μ, MemLp (gv μ) 2 volume := memLp_avgEvenGrad hgu
    have hdv : ∀ μ, IsTPartial μ v (gv μ) := isTPartial_avgEven hu hgu hdu
    have hpv : HasParity ∅ v := hasParity_avgEven u
    have hpgv : ∀ μ, HasParity {μ} (gv μ) := fun μ => by
      have := hpv.partial hv (hgv μ) (hdv μ); rwa [symmDiff_empty_singleton] at this
    -- the cube test function
    set φ : (Fin 4 → ℝ) → ℂ := fun x => v (chart0 x)
    set gφ : Fin 4 → (Fin 4 → ℝ) → ℂ := fun μ x => gv μ (chart0 x)
    have hφ : MemW12 Q0 φ gφ := memW12_restrict hv hgv hdv
    have egv : ∀ μ, gv μ =ᵐ[volume] parExt {μ} (gφ μ) := fun μ => parExt_restrict (hpgv μ)
    -- reduce to the even part on both sides
    have hFL : ∀ μ, HasParity {μ} (covLin (extA a) (extXi ξ) (extDXi dξ) c e μ) := fun μ => by
      rw [covLin_ext]; exact hasParity_parExt _ _
    have hFR : ∀ μ, HasParity {μ} (extH h c e μ) := fun μ => hasParity_parExt _ _
    have hmL : ∀ μ, MemLp (covLin (extA a) (extXi ξ) (extDXi dξ) c e μ) 2 volume := fun μ => by
      rw [covLin_ext]; exact memLp_parExt (by norm_num) (by norm_num) (hC c e μ)
    have hmR : ∀ μ, MemLp (extH h c e μ) 2 volume := fun μ =>
      memLp_parExt (by norm_num) (by norm_num) (hh c e μ)
    have eL : ∀ μ, ∫ x, conj (gu μ x) * covLin (extA a) (extXi ξ) (extDXi dξ) c e μ x =
        16 * ∫ x in Q0, conj (gφ μ x) * cCovLin a ξ dξ c e μ x := fun μ => by
      rw [← integral_conj_avgEvenGrad (hFL μ) (hmL μ) hgu, ← (key φ gφ hφ c e μ).1]
      exact integral_congr_ae ((egv μ).mono fun t ht => by simp only [gv] at ht ⊢; rw [ht])
    have eR : ∀ μ, ∫ x, conj (gu μ x) * extH h c e μ x =
        16 * ∫ x in Q0, conj (gφ μ x) * h c e μ x := fun μ => by
      rw [← integral_conj_avgEvenGrad (hFR μ) (hmR μ) hgu, ← (key φ gφ hφ c e μ).2]
      exact integral_congr_ae ((egv μ).mono fun t ht => by simp only [gv] at ht ⊢; rw [ht])
    simp only [eL, eR, ← Finset.mul_sum]
    rw [hcube φ gφ hφ c e]
  · -- torus ⟹ cube
    intro htorus φ gφ hφ c e
    obtain ⟨h1, h2, h3⟩ := isTPartial_parExt hφ
    have ht := htorus (parExt ∅ φ) (fun μ => parExt {μ} (gφ μ)) h1 h2 h3 c e
    simp only [fun μ => (key φ gφ hφ c e μ).1, fun μ => (key φ gφ hφ c e μ).2,
      ← Finset.mul_sum] at ht
    exact mul_left_cancel₀ h16 ht

theorem weakLinCoulomb_congr {a : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ}
    {h : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ} {ξ ξ' : Fin m → Fin m → 𝕋⁴ → ℂ}
    {dξ dξ' : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ} (hw : WeakLinCoulomb a h ξ dξ)
    (e1 : ∀ c e, ξ c e =ᵐ[volume] ξ' c e) (e2 : ∀ c e μ, dξ c e μ =ᵐ[volume] dξ' c e μ) :
    WeakLinCoulomb a h ξ' dξ' := by
  intro u gu hu hgu hdu c e
  have hall : ∀ᵐ x ∂volume, (∀ c e, ξ c e x = ξ' c e x) ∧ ∀ c e μ, dξ c e μ x = dξ' c e μ x :=
    (ae_all_iff.2 fun c => ae_all_iff.2 fun e => e1 c e).and
      (ae_all_iff.2 fun c => ae_all_iff.2 fun e => ae_all_iff.2 fun μ => e2 c e μ)
  rw [← hw u gu hu hgu hdu c e]
  refine Finset.sum_congr rfl fun μ _ => integral_congr_ae (hall.mono fun x hx => ?_)
  simp only [covLin, hx.1, hx.2]

/-- **The linearised Coulomb operator with the Neumann condition on the cube is an
isomorphism** `H¹(Q₀)/ℂ → (H¹(Q₀)/ℂ)^*` at every connection with small `L⁴(Q₀)` norm (no
boundary condition on the connection): for `Σ_{μce} ‖a_{μ,ce}‖_{L⁴(Q₀)} ≤ 1/224` and every
`h ∈ L²(Q₀)` there is a unique mean-zero `ξ ∈ W^{1,2}(Q₀)` with
`d^*(dξ + [a, ξ]) = d^* h` in `Q₀` and `(dξ + [a, ξ] - h)·ν = 0` on `∂Q₀` (weakly), and
`‖∂_μ ξ_{ce}‖_{L²(Q₀)} ≤ 2 Σ_{c'e'μ'} ‖h_{c'e'μ'}‖_{L²(Q₀)}`. -/
theorem linearized_coulomb_cube (a : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ)
    (ha : ∀ μ c e, MemLp (a μ c e) 4 (volume.restrict Q0))
    (hsmall : ∑ μ, ∑ c, ∑ e, eLpNorm (a μ c e) 4 (volume.restrict Q0) ≤ ENNReal.ofReal (1 / 224))
    (h : Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ)
    (hh : ∀ c e μ, MemLp (h c e μ) 2 (volume.restrict Q0)) :
    ∃ (ξ : Fin m → Fin m → (Fin 4 → ℝ) → ℂ) (dξ : Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ),
      (∀ c e, MemW12 Q0 (ξ c e) (dξ c e)) ∧ (∀ c e, ∫ x in Q0, ξ c e x = 0) ∧
      CubeWeakLinCoulomb a h ξ dξ ∧
      (∀ c e μ, eLpNorm (dξ c e μ) 2 (volume.restrict Q0) ≤
        2 * ∑ c', ∑ e', ∑ μ', eLpNorm (h c' e' μ') 2 (volume.restrict Q0)) ∧
      ∀ (ξ' : Fin m → Fin m → (Fin 4 → ℝ) → ℂ) (dξ' : Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ),
        (∀ c e, MemW12 Q0 (ξ' c e) (dξ' c e)) → (∀ c e, ∫ x in Q0, ξ' c e x = 0) →
        CubeWeakLinCoulomb a h ξ' dξ' → ∀ c e, ξ' c e =ᵐ[volume.restrict Q0] ξ c e := by
  -- reflected data
  have haT : ∀ μ c e, MemLp (extA a μ c e) 4 volume := fun μ c e =>
    memLp_parExt (by norm_num) (by norm_num) (ha μ c e)
  have haN : ∀ μ c e, eLpNorm (extA a μ c e) 4 volume =
      2 * eLpNorm (a μ c e) 4 (volume.restrict Q0) := fun μ c e => eLpNorm_parExt_four (ha μ c e)
  have hsmallT : ∑ μ, ∑ c, ∑ e, eLpNorm (extA a μ c e) 4 volume ≤ ENNReal.ofReal (1 / 112) := by
    simp only [haN, ← Finset.mul_sum]
    calc 2 * ∑ μ, ∑ c, ∑ e, eLpNorm (a μ c e) 4 (volume.restrict Q0)
        ≤ 2 * ENNReal.ofReal (1 / 224) := by gcongr
      _ = ENNReal.ofReal (1 / 112) := by
          rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]; norm_num
  have hhT : ∀ c e μ, MemLp (extH h c e μ) 2 volume := fun c e μ =>
    memLp_parExt (by norm_num) (by norm_num) (hh c e μ)
  have hNa : IsNeumannMForm (extA a) := fun μ c e => hasParity_parExt _ _
  have hNh : IsNeumannData (extH h) := fun c e μ => hasParity_parExt _ _
  obtain ⟨Ξ, dΞ, h1, h2, h3, h4, h5, h6, hev, hevd, h7⟩ :=
    linearized_coulomb_iso_even (extA a) haT hsmallT hNa (extH h) hhT hNh
  -- cube solution
  set ξ : Fin m → Fin m → (Fin 4 → ℝ) → ℂ := fun c e x => Ξ c e (chart0 x)
  set dξ : Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ := fun c e μ x => dΞ c e μ (chart0 x)
  have hW : ∀ c e, MemW12 Q0 (ξ c e) (dξ c e) := fun c e =>
    memW12_restrict (h1 c e) (h2 c e) (h3 c e)
  have eΞ : ∀ c e, Ξ c e =ᵐ[volume] extXi ξ c e := fun c e => parExt_restrict (hev c e)
  have edΞ : ∀ c e μ, dΞ c e μ =ᵐ[volume] extDXi dξ c e μ := fun c e μ =>
    parExt_restrict (hevd c e μ)
  have hmean : ∀ c e, ∫ x in Q0, ξ c e x = 0 := fun c e => by
    have := integral_Q0_eq_of_parExt (hW c e).memLp
    have hz : mFourierCoeff (parExt ∅ (ξ c e)) 0 = 0 := by
      have h' := congrFun (mFourierCoeff_congr_ae (eΞ c e)) 0
      rw [h4 c e] at h'; exact h'.symm
    rw [hz] at this
    exact (mul_eq_zero.1 this).resolve_left (by norm_num)
  have hweakT : WeakLinCoulomb (extA a) (extH h) (extXi ξ) (extDXi dξ) :=
    weakLinCoulomb_congr h5 eΞ edΞ
  refine ⟨ξ, dξ, hW, hmean, (cubeWeak_iff_torusWeak ha hh hW).2 hweakT, ?_, ?_⟩
  · -- the bound
    intro c e μ
    have hb := h6 c e μ
    rw [eLpNorm_congr_ae (edΞ c e μ), show extDXi dξ c e μ = parExt {μ} (dξ c e μ) from rfl,
      eLpNorm_parExt_two ((hW c e).memLp_grad μ)] at hb
    simp only [extH, fun c' e' μ' => eLpNorm_parExt_two (S := {μ'}) (hh c' e' μ'),
      ← Finset.mul_sum] at hb
    exact ennreal_cancel_four (hb.trans (le_of_eq (by ring)))
  · -- uniqueness
    intro ξ' dξ' hW' hmean' hweak' c e
    have hT' := (cubeWeak_iff_torusWeak ha hh hW').1 hweak'
    obtain ⟨-, -, -⟩ := isTPartial_parExt (hW' c e)
    have hu := h7 (extXi ξ') (extDXi dξ')
      (fun c e => (isTPartial_parExt (hW' c e)).1)
      (fun c e μ => (isTPartial_parExt (hW' c e)).2.1 μ)
      (fun c e μ => (isTPartial_parExt (hW' c e)).2.2 μ)
      (fun c e => by
        change mFourierCoeff (parExt ∅ (ξ' c e)) 0 = 0
        rw [← integral_Q0_eq_of_parExt (hW' c e).memLp, hmean' c e, mul_zero])
      hT' c e
    have hQ : MeasurableSet Q0 := (isOpen_box _ _).measurableSet
    have hr := TorusChart.ae_chart_of_ae one_pos Q0_subset_cubeAt hu
    filter_upwards [hr, ae_restrict_mem hQ] with x hx hxQ
    have := parExt_chart0 ∅ (ξ' c e) hxQ
    simp only [extXi] at hx
    rw [← this, hx]

/-- Non-vacuity: the hypotheses of `linearized_coulomb_cube` hold for `a = 0`, `h = 0`. -/
example (m : ℕ) : ∃ (ξ : Fin m → Fin m → (Fin 4 → ℝ) → ℂ)
    (dξ : Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ),
    CubeWeakLinCoulomb (m := m) (fun _ _ _ _ => 0) (fun _ _ _ _ => 0) ξ dξ := by
  obtain ⟨ξ, dξ, -, -, hw, -, -⟩ := linearized_coulomb_cube (m := m) (fun _ _ _ _ => 0)
    (fun _ _ _ => MemLp.zero) (by simp) (fun _ _ _ _ => 0) (fun _ _ _ => MemLp.zero)
  exact ⟨ξ, dξ, hw⟩

end RenewalGeometry.CubeNeumann
