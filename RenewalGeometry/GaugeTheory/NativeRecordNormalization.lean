/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.GaugeTheory.RootedCoulombCertificate

/-!
# The rooted Coulomb normalization with its logarithm chart
  (normalization clause of `thm:finite-Wilson-zero-defect`, Einstein–SM action closure)

`RootedCoulomb.rooted_coulomb_normalization` (the Coulomb clause of
`prop:rooted-gauge-certificate`) returns the normalized logarithmic coordinates
`A_μ(x) = h⁻¹ Log((g·U)_μ(x))` of the original links.  To transport the native records along the
normalizing site gauge one also needs that the normalized links lie in the logarithm chart, so
that `e^{hA_μ(x)} = (g·U)_μ(x)` exactly.  `rooted_coulomb_normalization_chart` is the same
statement with this chart clause (`‖(g·U)_μ(x) - 1‖ < 1`) kept: it is the endpoint `s = 1` of the
homotopy of `thm:finite-Coulomb-normalization`, which stays in the open domain `domO`.
-/

open NormedSpace Finset Set

namespace RenewalGeometry.NativeRecordNorm

open SeriesLogChart GridSobolev CoulombApriori CurvatureSplit FiniteCoulomb RootedWilson
  CoulombHomotopy RootedCoulomb

noncomputable section

variable {𝔸 : Type*} [CStarAlgebra 𝔸] [Nontrivial 𝔸] [FiniteDimensional ℝ 𝔸]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nontrivial E]
  [FiniteDimensional ℝ E]
variable (toE : 𝔸 ≃L[ℝ] E)
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-- **The rooted Coulomb normalization with its chart** (`prop:rooted-gauge-certificate`, Coulomb
clause, as used in `thm:finite-Wilson-zero-defect`): as `RootedCoulomb.rooted_coulomb_normalization`,
and in addition the normalized links `(g·U)_μ(x)` lie in the logarithm chart
`‖(g·U)_μ(x) - 1‖ < 1`, so that `e^{h A_μ(x)} = (g·U)_μ(x)`. -/
theorem rooted_coulomb_normalization_chart (hι : Fintype.card ι = 4)
    (hM1 : ∀ V ∈ unitary 𝔸, ∀ X, ‖toE (V * X * star V)‖ = ‖toE X‖)
    (hM2 : ∀ a : 𝔸, star a = -a → ∀ u, inner ℝ (toE a) (toE (a * u - u * a)) = 0)
    {L : ℝ} (hL : 0 < L) {εstar : ℝ} (hεstar : 0 < εstar) :
    ∃ εc Cc : ℝ, 0 < εc ∧ 0 < Cc ∧ ∀ (m : ℕ) [NeZero m] (h : ℝ), 0 < h → (m : ℝ) * h = L →
      ∀ (o : ι → ZMod m) (w : ∀ v, LatticeWalk (latSrc (ι := ι) (n := m)) latTgt v o)
        (U : (ι → ZMod m) × ι → unitary 𝔸),
      (∀ μ x, ‖((rootedWord w U (x, μ) : unitary 𝔸) : 𝔸) - 1‖ ≤ 1 / 64) →
      (∀ μ ν x, ‖litPlaq U μ ν x - 1‖ < 1) →
      oneL4 h (toE : 𝔸 →L[ℝ] E) (treeSeed h w U) + litCurvL2 toE h U ≤ εc →
      ∃ g : (ι → ZMod m) → unitary 𝔸,
        let A : ι → (ι → ZMod m) → 𝔸 := fun μ x =>
          h⁻¹ • logChart ((gaugeLinks latSrc latTgt g U (x, μ) : unitary 𝔸) : 𝔸)
        (∀ μ x, ‖((gaugeLinks latSrc latTgt g U (x, μ) : unitary 𝔸) : 𝔸) - 1‖ < 1) ∧
        (∀ μ x, star (A μ x) = -A μ x) ∧
        periodicHodgeCodiff h gridStep (bar (toE : 𝔸 →L[ℝ] E) A) = 0 ∧
        oneH1 h (toE : 𝔸 →L[ℝ] E) A + oneL4 h (toE : 𝔸 →L[ℝ] E) A ≤
          Cc * (oneL2 h (toE : 𝔸 →L[ℝ] E) (treeSeed h w U) + litCurvL2 toE h U +
            oneL4 h (toE : 𝔸 →L[ℝ] E) (treeSeed h w U) ^ 2) ∧
        oneL4 h (toE : 𝔸 →L[ℝ] E) A ≤ εstar := by
  obtain ⟨εc, Cc, hεc, hCc, H⟩ := finite_coulomb_normalization toE hι hM1 hM2 hL hεstar
  refine ⟨εc, Cc, hεc, hCc, fun m _ h hh hmh o w U hadm hplaq hcert => ?_⟩
  have hcurv := curvL2_treeSeed toE hM1 hh.ne' w U hadm hplaq
  rw [← hcurv] at hcert ⊢
  obtain ⟨q, hq, -, hskew, hcod, hest, hsmall, γ, -, hγ1, hdom, -⟩ :=
    H m h hh hmh (treeSeed h w U) (treeSeed_skew w U hadm) hcert
  have hdom1 := (hdom 1 ⟨zero_le_one, le_rfl⟩).1
  rw [hγ1] at hdom1
  set C := rootedPath w U
  refine ⟨fun x => ⟨q x, hq x⟩ * C x, ?_⟩
  have hP : ∀ μ x, ((gaugeLinks latSrc latTgt
      (fun x => (⟨q x, hq x⟩ : unitary 𝔸) * C x) U (x, μ) : unitary 𝔸) : 𝔸) =
      linkP h (treeSeed h w U) 1 q μ x := by
    intro μ x
    simp only [linkP, one_smul]
    rw [exp_treeSeed hh.ne' w U hadm]
    simp only [gaugeLinks_apply, latTgt, latSrc, Submonoid.coe_mul, coe_inv_unitary, star_mul,
      rootedWord, rootedPath, mul_assoc]
    rfl
  have hA : ∀ μ x, h⁻¹ • logChart ((gaugeLinks latSrc latTgt
      (fun x => (⟨q x, hq x⟩ : unitary 𝔸) * C x) U (x, μ) : unitary 𝔸) : 𝔸) =
      linkA h (treeSeed h w U) 1 q μ x := by
    intro μ x
    rw [hP]
    rfl
  simp only [hA]
  exact ⟨fun μ x => by rw [hP]; exact hdom1 μ x, hskew, hcod, hest, hsmall⟩

end

end RenewalGeometry.NativeRecordNorm
