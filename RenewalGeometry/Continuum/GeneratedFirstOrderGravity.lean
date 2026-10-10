/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.EinsteinHilbertCurveVariation

/-!
# The first-derivative (`ΓΓ`) representative of the Einstein–Hilbert density

Einstein–Standard-Model action-closure manuscript, `app:generated-dynamics`
(`eq:generated-comparison-action`: "`S^{(1)}` the complete first-derivative torsion-free
Einstein–Standard-Model action representative"), gravitational sector, in metric variables:

* `gamGam`, `wflux` (`w^λ = g^{μν}Γ^λ_{μν} - g^{λμ}Γ^ν_{μν}`, `EHJetVariation.fluxV` of the
  Christoffel symbols), **`L1EH g ∂g`** — the first-derivative Einstein–Hilbert density
  `√(-det g)(g^{μν}(Γ^α_{αl}Γ^l_{μν} - Γ^α_{νl}Γ^l_{μα}) - Γ^a_{aλ}w^λ - ∂_λg^{μν}Γ^λ_{μν}
  + ∂_λg^{λμ}Γ^ν_{μν})`, a function of the metric 1-jet only;
* **`volScal_eq`** (jet identity) — `√(-det g) R = L1EH + √(-det g)(∂_λw^λ + Γ^a_{aλ}w^λ)` with the
  jet divergence `EHJetVariation.fluxDivJ`;
* **`sum_pd_wflux_eq`** — for smooth Lorentzian metric fields the jet divergence is the actual
  divergence `Σ_λ ∂_λ(√(-det g) w^λ)`; hence (`volScal_eq_L1EH_add_div`)
  `√(-det g) R(g) = L1EH(j¹g) + Σ_λ ∂_λ(√(-det g) w^λ)`: the second-derivative Einstein–Hilbert
  density and its first-derivative representative differ by a divergence of a first-jet flux;
* **`eh_field_variation`** — the first variation of `√(-det g) R` along `g + εk`:
  `-√(-det g) G^{μν}k_{μν} + Σ_λ ∂_λ W^λ` with the first-jet Palatini flux
  `W^λ = EHFieldVariation.palatiniFlux g k λ`.
-/

namespace RenewalGeometry

namespace GenFOGrav

open Finset HarmonicDefect EHJetVariation EHFieldVariation ActualJetSystem
open SobolevOpen (pd)
open scoped ContDiff

noncomputable section

set_option linter.unusedSectionVars false

/-! ### Jet identities -/

section Jet

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The `ΓΓ` part of the scalar curvature. -/
def gamGam (gi : n → n → ℝ) (Γ : n → n → n → ℝ) : ℝ :=
  ∑ μ, ∑ ν, gi μ ν * (∑ α, ∑ l, Γ α α l * Γ l μ ν - ∑ α, ∑ l, Γ α ν l * Γ l μ α)

/-- The first-jet terms of the divergence. -/
def divLow (gi : n → n → ℝ) (dgi : n → n → n → ℝ) (Γ : n → n → n → ℝ) : ℝ :=
  ∑ lam, ((∑ μ, ∑ ν, dgi lam μ ν * Γ lam μ ν) - ∑ μ, ∑ ν, dgi lam lam μ * Γ ν μ ν) +
    ∑ lam, (∑ a, Γ a a lam) * fluxV gi Γ lam

/-- **The trace of the Ricci jet splits into second-derivative and `ΓΓ` parts.** -/
theorem trG_ricciJ (gi : n → n → ℝ) (Γ : n → n → n → ℝ) (D : n → n → n → n → ℝ)
    (hgi : ∀ a b, gi a b = gi b a) :
    trG gi (ricciJ Γ D) = gamGam gi Γ +
      ∑ lam, ((∑ μ, ∑ ν, gi μ ν * D lam lam μ ν) - ∑ μ, ∑ ν, gi lam μ * D lam ν μ ν) := by
  unfold trG ricciJ gamGam
  have e1 : ∑ μ, ∑ ν, gi μ ν * ∑ α, D α α μ ν = ∑ lam, ∑ μ, ∑ ν, gi μ ν * D lam lam μ ν := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun μ _ => Finset.sum_comm, Finset.sum_comm]
  have e2 : ∑ μ, ∑ ν, gi μ ν * ∑ α, D ν α μ α = ∑ lam, ∑ μ, ∑ ν, gi lam μ * D lam ν μ ν := by
    simp only [Finset.mul_sum]
    -- rename `ν ↦ lam`, `α ↦ ν`
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun lam _ => Finset.sum_congr rfl fun μ _ => ?_
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [hgi μ lam]
  have hsplit : ∀ μ ν, gi μ ν * (∑ α, D α α μ ν - ∑ α, D ν α μ α + ∑ α, ∑ l, Γ α α l * Γ l μ ν -
      ∑ α, ∑ l, Γ α ν l * Γ l μ α) = gi μ ν * (∑ α, ∑ l, Γ α α l * Γ l μ ν -
      ∑ α, ∑ l, Γ α ν l * Γ l μ α) + (gi μ ν * ∑ α, D α α μ ν - gi μ ν * ∑ α, D ν α μ α) :=
    fun μ ν => by ring
  simp only [hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [e1, e2, ← Finset.sum_sub_distrib]

/-- **The first-derivative Einstein–Hilbert density** (`ΓΓ` representative) on metric jets. -/
def L1EHJ (v : ℝ) (gi : n → n → ℝ) (dg : n → n → n → ℝ) : ℝ :=
  v * (gamGam gi (chr gi dg) - divLow gi (dginv gi dg) (chr gi dg))

/-- **Jet identity**: `v R = L1EH + v(∂_λw^λ + Γ^a_{aλ}w^λ)` (jet divergence). -/
theorem volScal_eq (v : ℝ) (gi : n → n → ℝ) (dg : n → n → n → ℝ) (ddg : n → n → n → n → ℝ)
    (hgi : ∀ a b, gi a b = gi b a) :
    v * scal gi dg ddg = L1EHJ v gi dg +
      v * (fluxDivJ gi (dginv gi dg) (chr gi dg) (dchr gi dg ddg) +
        ∑ lam, (∑ a, chr gi dg a a lam) * fluxV gi (chr gi dg) lam) := by
  unfold scal ricci
  rw [trG_ricciJ gi (chr gi dg) (dchr gi dg ddg) hgi]
  unfold L1EHJ divLow fluxDivJ
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

end Jet

/-! ### The field identities -/

section Field

/-- The first-derivative Einstein–Hilbert density of a metric 1-jet (`g⁻¹ = ginvOf g`). -/
def L1EH (g : Fin 4 → Fin 4 → ℝ) (dg : Fin 4 → Fin 4 → Fin 4 → ℝ) : ℝ :=
  L1EHJ (volM g) (ginvOf g) dg

/-- The flux field `√(-det g) w^λ` of the divergence. -/
def wfluxF (g : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ) (lam : Fin 4) (z : Fin 4 → ℝ) : ℝ :=
  volM (g z) * fluxV (ginvOf (g z)) (chr (ginvOf (g z)) (dF g z)) lam

theorem dchr_eq_chr (gi : Fin 4 → Fin 4 → ℝ) (dg : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (ddg : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (lam l μ ν : Fin 4) :
    chr (fun a b => dginv gi dg lam a b) dg l μ ν + chr gi (ddg lam) l μ ν =
      dchr gi dg ddg lam l μ ν := by
  unfold dchr dchr1 dchr2 chr
  ring

/-- **The divergence of the flux field is the jet divergence.** -/
theorem sum_pd_wflux_eq {g : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgs : ∀ z μ ν, g z μ ν = g z ν μ) (z : Fin 4 → ℝ) (hdet : (Matrix.of (g z)).det < 0) :
    ∑ lam, pd (wfluxF g lam) lam z =
      volM (g z) * (fluxDivJ (ginvOf (g z)) (dginv (ginvOf (g z)) (dF g z))
          (chr (ginvOf (g z)) (dF g z)) (dchr (ginvOf (g z)) (dF g z) (ddF g z)) +
        ∑ lam, (∑ a, chr (ginvOf (g z)) (dF g z) a a lam) *
          fluxV (ginvOf (g z)) (chr (ginvOf (g z)) (dF g z)) lam) := by
  have hgd : ∀ y, DifferentiableAt ℝ g y := fun y => hg.differentiable (by simp) y
  have hpg : ∀ α, ContDiff ℝ ∞ (pd g α) := fun α => contDiff_pd' hg α
  have hpgd : ∀ α y, DifferentiableAt ℝ (pd g α) y := fun α y =>
    (hpg α).differentiable (by simp) y
  have hdetd : DifferentiableAt ℝ (fun y => (Matrix.of (g y)).det) z :=
    (differentiable_det (g z)).comp z (hgd z)
  have hWd : ∀ lam, DifferentiableAt ℝ (wfluxF g lam) z := by
    intro lam
    have hgic : ∀ a b, DifferentiableAt ℝ (fun y => ginvOf (g y) a b) z := fun a b =>
      ((ActualJetSmooth.ContDiffAt.ginvOf hg.contDiffAt (hdet).ne a b).differentiableAt
        (by simp))
    have hdgc : ∀ α a b, DifferentiableAt ℝ (fun y => dF g y α a b) z := fun α a b =>
      differentiableAt_pi.1 (differentiableAt_pi.1 (hpgd α z) a) b
    have hvold : DifferentiableAt ℝ (fun y => volM (g y)) z := by
      unfold volM
      exact hdetd.neg.sqrt (by have := hdet; intro h; simp only [Pi.neg_apply] at h; linarith)
    unfold wfluxF fluxV chr
    fun_prop (disch := assumption)
  have hline : ∀ lam, HasDerivAt (fun s : ℝ => wfluxF g lam (z + s • Pi.single lam 1))
      ((1 / 2) * volM (g z) * trG (ginvOf (g z)) (dF g z lam) *
          fluxV (ginvOf (g z)) (chr (ginvOf (g z)) (dF g z)) lam +
        volM (g z) * ((∑ μ, ∑ ν, (dginv (ginvOf (g z)) (dF g z) lam μ ν *
            chr (ginvOf (g z)) (dF g z) lam μ ν +
          ginvOf (g z) μ ν * dchr (ginvOf (g z)) (dF g z) (ddF g z) lam lam μ ν)) -
          ∑ μ, ∑ ν, (dginv (ginvOf (g z)) (dF g z) lam lam μ *
            chr (ginvOf (g z)) (dF g z) ν μ ν +
          ginvOf (g z) lam μ * dchr (ginvOf (g z)) (dF g z) (ddF g z) lam ν μ ν))) 0 := by
    intro lam
    set ℓ : ℝ → Fin 4 → ℝ := fun s => z + s • Pi.single lam 1 with hℓ
    have hℓ0 : ℓ 0 = z := by simp [hℓ]
    have hG : ∀ μ ν, HasDerivAt (fun s => g (ℓ s) μ ν) (dF g z lam μ ν) 0 := fun μ ν =>
      hasDerivAt_line_apply lam (hgd z) μ ν
    have hdG : ∀ α μ ν, HasDerivAt (fun s => dF g (ℓ s) α μ ν) (ddF g z lam α μ ν) 0 :=
      fun α μ ν => hasDerivAt_line_apply lam (hpgd α z) μ ν
    have hgi : ∀ a b, HasDerivAt (fun s => ginvOf (g (ℓ s)) a b)
        (dginv (ginvOf (g z)) (dF g z) lam a b) 0 := by
      intro a b
      have h := JetCurve.hasDerivAt_ginvOf (g := fun s => g (ℓ s)) (t := 0) (dg := dF g z) lam
        (fun μ ν => hG μ ν) (by rw [hℓ0]; exact (hdet).ne) a b
      simpa [hℓ0] using h
    have hvol : HasDerivAt (fun s => volM (g (ℓ s)))
        ((1 / 2) * volM (g z) * trG (ginvOf (g z)) (dF g z lam)) 0 := by
      have h := hasDerivAt_volM_curve (G := fun s => g (ℓ s)) (k := dF g z lam) (t := 0)
        (fun μ ν => hG μ ν) (by rw [hℓ0]; exact hdet) (by rw [hℓ0]; exact hgs z)
      simpa [hℓ0] using h
    have hX : ∀ l μ ν, HasDerivAt
        (fun s => chr (ginvOf (g (ℓ s))) (dF g (ℓ s)) l μ ν)
        (dchr (ginvOf (g z)) (dF g z) (ddF g z) lam l μ ν) 0 := by
      intro l μ ν
      have h1 := hasDerivAt_chr' hgi hdG l μ ν
      rw [hℓ0] at h1
      exact h1.congr_deriv (dchr_eq_chr _ _ _ lam l μ ν)
    have hV : HasDerivAt (fun s => fluxV (ginvOf (g (ℓ s)))
        (chr (ginvOf (g (ℓ s))) (dF g (ℓ s))) lam)
        ((∑ μ, ∑ ν, (dginv (ginvOf (g z)) (dF g z) lam μ ν *
            chr (ginvOf (g z)) (dF g z) lam μ ν +
          ginvOf (g z) μ ν * dchr (ginvOf (g z)) (dF g z) (ddF g z) lam lam μ ν)) -
          ∑ μ, ∑ ν, (dginv (ginvOf (g z)) (dF g z) lam lam μ *
            chr (ginvOf (g z)) (dF g z) ν μ ν +
          ginvOf (g z) lam μ * dchr (ginvOf (g z)) (dF g z) (ddF g z) lam ν μ ν)) 0 := by
      unfold fluxV
      have h1 := HasDerivAt.fun_sum (u := Finset.univ) fun μ _ =>
        HasDerivAt.fun_sum (u := Finset.univ) fun ν _ => (hgi μ ν).fun_mul (hX lam μ ν)
      have h2 := HasDerivAt.fun_sum (u := Finset.univ) fun μ _ =>
        HasDerivAt.fun_sum (u := Finset.univ) fun ν _ => (hgi lam μ).fun_mul (hX ν μ ν)
      simp only [hℓ0] at h1 h2
      exact h1.fun_sub h2
    have h := hvol.fun_mul hV
    simp only [hℓ0] at h
    exact h
  have hpd : ∀ lam, pd (wfluxF g lam) lam z = _ := fun lam =>
    pd_eq_of_line' (hWd lam) (hline lam)
  simp only [hpd]
  have htr : ∀ lam, trG (ginvOf (g z)) (dF g z lam) =
      2 * ∑ a, chr (ginvOf (g z)) (dF g z) a a lam := by
    intro lam
    rw [EHJetVariation.trace_chr _ _ (ginvOf_symm' (hgs z)) (dF_symm hgd hgs z)]
    unfold trG
    ring
  simp only [htr]
  unfold fluxDivJ
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun lam _ => ?_
  ring

/-- **The Einstein–Hilbert density is its first-derivative representative plus a divergence**:
`√(-det g) R(g) = L1EH(j¹g) + Σ_λ ∂_λ(√(-det g) w^λ)` for smooth Lorentzian metric fields. -/
theorem volScal_eq_L1EH_add_div {g : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgs : ∀ z μ ν, g z μ ν = g z ν μ) (z : Fin 4 → ℝ) (hdet : (Matrix.of (g z)).det < 0) :
    volM (g z) * scal (ginvOf (g z)) (dF g z) (ddF g z) =
      L1EH (g z) (dF g z) + ∑ lam, pd (wfluxF g lam) lam z := by
  rw [sum_pd_wflux_eq hg hgs z hdet]
  exact volScal_eq _ _ _ _ (ginvOf_symm' (hgs z))

/-- **The divergence of the Palatini flux** (local form of
`EHFieldVariation.sum_pd_flux_eq`: `det g < 0` only at the point). -/
theorem sum_pd_flux_eq_loc {g k : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ} (hg : ContDiff ℝ ∞ g)
    (hk : ContDiff ℝ ∞ k) (hgs : ∀ z μ ν, g z μ ν = g z ν μ)
    (z : Fin 4 → ℝ) (hdet : (Matrix.of (g z)).det < 0) :
    ∑ lam, pd (palatiniFlux g k lam) lam z =
      volM (g z) * (fluxDivJ (ginvOf (g z)) (dginv (ginvOf (g z)) (dF g z))
          (chrVar (ginvOf (g z)) (dF g z) (k z) (dF k z))
          (dchrVar (ginvOf (g z)) (dF g z) (ddF g z) (k z) (dF k z) (ddF k z)) +
        ∑ lam, (∑ a, chr (ginvOf (g z)) (dF g z) a a lam) *
          fluxV (ginvOf (g z)) (chrVar (ginvOf (g z)) (dF g z) (k z) (dF k z)) lam) := by
  -- smoothness of the jet fields
  have hgd : ∀ y, DifferentiableAt ℝ g y := fun y => hg.differentiable (by simp) y
  have hkd : ∀ y, DifferentiableAt ℝ k y := fun y => hk.differentiable (by simp) y
  have hpg : ∀ α, ContDiff ℝ ∞ (pd g α) := fun α => contDiff_pd' hg α
  have hpk : ∀ α, ContDiff ℝ ∞ (pd k α) := fun α => contDiff_pd' hk α
  have hpgd : ∀ α y, DifferentiableAt ℝ (pd g α) y := fun α y =>
    (hpg α).differentiable (by simp) y
  have hpkd : ∀ α y, DifferentiableAt ℝ (pd k α) y := fun α y =>
    (hpk α).differentiable (by simp) y
  have hgic : ∀ a b, DifferentiableAt ℝ (fun y => ginvOf (g y) a b) z := fun a b =>
    ((ActualJetSmooth.ContDiffAt.ginvOf hg.contDiffAt (hdet).ne a b).differentiableAt
      (by simp))
  have hdgc : ∀ α a b, DifferentiableAt ℝ (fun y => dF g y α a b) z := fun α a b =>
    differentiableAt_pi.1 (differentiableAt_pi.1 (hpgd α z) a) b
  have hdkc : ∀ α a b, DifferentiableAt ℝ (fun y => dF k y α a b) z := fun α a b =>
    differentiableAt_pi.1 (differentiableAt_pi.1 (hpkd α z) a) b
  have hkc : ∀ a b, DifferentiableAt ℝ (fun y => k y a b) z := fun a b =>
    differentiableAt_pi.1 (differentiableAt_pi.1 (hkd z) a) b
  have hdetd : DifferentiableAt ℝ (fun y => (Matrix.of (g y)).det) z :=
    (differentiable_det (g z)).comp z (hgd z)
  have hvold : DifferentiableAt ℝ (fun y => volM (g y)) z := by
    unfold volM
    exact hdetd.neg.sqrt (by have := hdet; intro h; simp only [Pi.neg_apply] at h; linarith)
  have hWd : ∀ lam, DifferentiableAt ℝ (palatiniFlux g k lam) z := by
    intro lam
    unfold palatiniFlux fluxV chrVar chr ginvVar
    fun_prop (disch := assumption)
  -- the line derivative of each flux component
  have hline : ∀ lam, HasDerivAt (fun s : ℝ => palatiniFlux g k lam (z + s • Pi.single lam 1))
      ((1 / 2) * volM (g z) * trG (ginvOf (g z)) (dF g z lam) *
          fluxV (ginvOf (g z)) (chrVar (ginvOf (g z)) (dF g z) (k z) (dF k z)) lam +
        volM (g z) * ((∑ μ, ∑ ν, (dginv (ginvOf (g z)) (dF g z) lam μ ν *
            chrVar (ginvOf (g z)) (dF g z) (k z) (dF k z) lam μ ν +
          ginvOf (g z) μ ν * dchrVar (ginvOf (g z)) (dF g z) (ddF g z) (k z) (dF k z) (ddF k z)
            lam lam μ ν)) -
          ∑ μ, ∑ ν, (dginv (ginvOf (g z)) (dF g z) lam lam μ *
            chrVar (ginvOf (g z)) (dF g z) (k z) (dF k z) ν μ ν +
          ginvOf (g z) lam μ * dchrVar (ginvOf (g z)) (dF g z) (ddF g z) (k z) (dF k z) (ddF k z)
            lam ν μ ν))) 0 := by
    intro lam
    set ℓ : ℝ → Fin 4 → ℝ := fun s => z + s • Pi.single lam 1 with hℓ
    have hℓ0 : ℓ 0 = z := by simp [hℓ]
    -- curves of the jets
    have hG : ∀ μ ν, HasDerivAt (fun s => g (ℓ s) μ ν) (dF g z lam μ ν) 0 := fun μ ν =>
      hasDerivAt_line_apply lam (hgd z) μ ν
    have hK : ∀ μ ν, HasDerivAt (fun s => k (ℓ s) μ ν) (dF k z lam μ ν) 0 := fun μ ν =>
      hasDerivAt_line_apply lam (hkd z) μ ν
    have hdG : ∀ α μ ν, HasDerivAt (fun s => dF g (ℓ s) α μ ν) (ddF g z lam α μ ν) 0 :=
      fun α μ ν => hasDerivAt_line_apply lam (hpgd α z) μ ν
    have hdK : ∀ α μ ν, HasDerivAt (fun s => dF k (ℓ s) α μ ν) (ddF k z lam α μ ν) 0 :=
      fun α μ ν => hasDerivAt_line_apply lam (hpkd α z) μ ν
    have hgi : ∀ a b, HasDerivAt (fun s => ginvOf (g (ℓ s)) a b)
        (dginv (ginvOf (g z)) (dF g z) lam a b) 0 := by
      intro a b
      have h := JetCurve.hasDerivAt_ginvOf (g := fun s => g (ℓ s)) (t := 0) (dg := dF g z) lam
        (fun μ ν => hG μ ν) (by rw [hℓ0]; exact (hdet).ne) a b
      simpa [hℓ0] using h
    have hvol : HasDerivAt (fun s => volM (g (ℓ s)))
        ((1 / 2) * volM (g z) * trG (ginvOf (g z)) (dF g z lam)) 0 := by
      have h := hasDerivAt_volM_curve (G := fun s => g (ℓ s)) (k := dF g z lam) (t := 0)
        (fun μ ν => hG μ ν) (by rw [hℓ0]; exact hdet) (by rw [hℓ0]; exact hgs z)
      simpa [hℓ0] using h
    have hgV : ∀ a b, HasDerivAt (fun s => ginvVar (ginvOf (g (ℓ s))) (k (ℓ s)) a b)
        (dginvVar (ginvOf (g z)) (dF g z) (k z) (dF k z) lam a b) 0 := by
      intro a b
      have h := hasDerivAt_ginvVar' hgi hK a b
      rw [hℓ0] at h
      exact h.congr_deriv (ginvVar_deriv_eq _ _ _ _ lam a b)
    have hX : ∀ l μ ν, HasDerivAt
        (fun s => chrVar (ginvOf (g (ℓ s))) (dF g (ℓ s)) (k (ℓ s)) (dF k (ℓ s)) l μ ν)
        (dchrVar (ginvOf (g z)) (dF g z) (ddF g z) (k z) (dF k z) (ddF k z) lam l μ ν) 0 := by
      intro l μ ν
      have h1 := hasDerivAt_chr' hgV hdG l μ ν
      have h2 := hasDerivAt_chr' hgi hdK l μ ν
      rw [hℓ0] at h1 h2
      refine (h1.fun_add h2).congr_deriv ?_
      unfold dchrVar chr
      ring
    have hV : HasDerivAt (fun s => fluxV (ginvOf (g (ℓ s)))
        (chrVar (ginvOf (g (ℓ s))) (dF g (ℓ s)) (k (ℓ s)) (dF k (ℓ s))) lam)
        ((∑ μ, ∑ ν, (dginv (ginvOf (g z)) (dF g z) lam μ ν *
            chrVar (ginvOf (g z)) (dF g z) (k z) (dF k z) lam μ ν +
          ginvOf (g z) μ ν * dchrVar (ginvOf (g z)) (dF g z) (ddF g z) (k z) (dF k z) (ddF k z)
            lam lam μ ν)) -
          ∑ μ, ∑ ν, (dginv (ginvOf (g z)) (dF g z) lam lam μ *
            chrVar (ginvOf (g z)) (dF g z) (k z) (dF k z) ν μ ν +
          ginvOf (g z) lam μ * dchrVar (ginvOf (g z)) (dF g z) (ddF g z) (k z) (dF k z) (ddF k z)
            lam ν μ ν)) 0 := by
      unfold fluxV
      have h1 := HasDerivAt.fun_sum (u := Finset.univ) fun μ _ =>
        HasDerivAt.fun_sum (u := Finset.univ) fun ν _ => (hgi μ ν).fun_mul (hX lam μ ν)
      have h2 := HasDerivAt.fun_sum (u := Finset.univ) fun μ _ =>
        HasDerivAt.fun_sum (u := Finset.univ) fun ν _ => (hgi lam μ).fun_mul (hX ν μ ν)
      simp only [hℓ0] at h1 h2
      exact h1.fun_sub h2
    have h := hvol.fun_mul hV
    simp only [hℓ0] at h
    exact h
  -- assemble
  have hpd : ∀ lam, pd (palatiniFlux g k lam) lam z = _ := fun lam =>
    pd_eq_of_line' (hWd lam) (hline lam)
  simp only [hpd]
  have htr : ∀ lam, trG (ginvOf (g z)) (dF g z lam) =
      2 * ∑ a, chr (ginvOf (g z)) (dF g z) a a lam := by
    intro lam
    rw [EHJetVariation.trace_chr _ _ (ginvOf_symm' (hgs z)) (dF_symm hgd hgs z)]
    unfold trG
    ring
  simp only [htr]
  unfold fluxDivJ
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun lam _ => ?_
  ring

/-- **The first variation of the Einstein–Hilbert density along a variation field**:
`d/dε √(-det g_ε) R(g_ε) = -√(-det g) G^{μν}k_{μν} + Σ_λ ∂_λW^λ` at `ε = 0`, `g_ε = g + εk`,
with the first-jet Palatini flux `W^λ = palatiniFlux g k λ`. -/
theorem eh_field_variation {g k : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ} (hg : ContDiff ℝ ∞ g)
    (hk : ContDiff ℝ ∞ k) (hgs : ∀ z μ ν, g z μ ν = g z ν μ) (hks : ∀ z μ ν, k z μ ν = k z ν μ)
    (z : Fin 4 → ℝ) (hdet : (Matrix.of (g z)).det < 0) :
    HasDerivAt (fun ε : ℝ => volM (g z + ε • k z) *
        scal (ginvOf (g z + ε • k z)) (dF g z + ε • dF k z) (ddF g z + ε • ddF k z))
      (-(volM (g z) * ∑ μ, ∑ ν, einsteinUp (g z) (ginvOf (g z)) (dF g z) (ddF g z) μ ν * k z μ ν) +
        ∑ lam, pd (palatiniFlux g k lam) lam z) 0 := by
  have hgd : ∀ y, DifferentiableAt ℝ g y := fun y => hg.differentiable (by simp) y
  have hkd : ∀ y, DifferentiableAt ℝ k y := fun y => hk.differentiable (by simp) y
  have hlin : ∀ (a b : ℝ), HasDerivAt (fun ε : ℝ => a + ε * b) b 0 := fun a b => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const b).const_add a
  have h := hasDerivAt_volScal_curve (G := fun ε => g z + ε • k z) (dG := fun ε => dF g z + ε • dF k z)
    (ddG := fun ε => ddF g z + ε • ddF k z) (k := k z) (dk := dF k z) (ddk := ddF k z)
    (fun μ ν => by simpa using hlin (g z μ ν) (k z μ ν))
    (fun α μ ν => by simpa using hlin (dF g z α μ ν) (dF k z α μ ν))
    (fun β α μ ν => by simpa using hlin (ddF g z β α μ ν) (ddF k z β α μ ν))
    (by simpa using hdet) (by simpa using hgs z)
  simp only [zero_smul, add_zero] at h
  refine h.congr_deriv ?_
  have hinv : ∀ a c, ∑ b, g z a b * ginvOf (g z) b c = if a = c then 1 else 0 := by
    intro a c
    have h := Matrix.mul_nonsing_inv (Matrix.of (g z)) (isUnit_iff_ne_zero.mpr (hdet).ne)
    have := congrFun (congrFun h a) c
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simpa [ginvOf] using this
  rw [eh_jet_variation (g z) (ginvOf (g z)) (dF g z) (ddF g z) (k z) (dF k z) (ddF k z)
    (volM (g z)) (ginvOf_symm' (hgs z)) hinv (dF_symm hgd hgs z) (dF_symm hkd hks z),
    sum_pd_flux_eq_loc hg hk hgs z hdet]

end Field

end

end GenFOGrav

end RenewalGeometry
