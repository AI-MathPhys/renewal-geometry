/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedGaussPropagation

/-!
# Noether identities of the Einstein–Standard-Model theory data: the stress sector

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`
(`app:generated-dynamics`) and `prop:subsidiary`: the propagation of the harmonic constraint along
the independent symmetric system uses the **covariant conservation of the complete stress**
`∇^μT_{μν} = (combination of the Yang–Mills, Higgs and Dirac Euler residuals)` — the Noether
identity of diffeomorphism invariance of the matter Lagrangian, which the manuscript uses
implicitly (`prop:subsidiary`: the Ward residual `𝒲_ν = κ∇^μT_{μν}` vanishes on solutions).

## Jet algebra (generic, any finite index type)

* `contr_deriv`, `contr4_deriv` — the formal derivative of a two-index (four-index) contraction
  with the inverse metric, written through Christoffel-corrected derivatives (metric
  compatibility `∂g^{αβ} = -Γg - gΓ`);
* `g_compat` — `∂_eg_{μν} = Γ^l{}_{eμ}g_{lν} + Γ^l{}_{eν}g_{μl}`;
* `covF`, `covH` — the gauge and Levi-Civita covariant derivatives `D_eF_{μν}`, `D_eD_μH` of the
  field strength and of the covariant Higgs gradient; `covF_bianchi` — the covariant **Bianchi
  identity** `D_eF_{νβ} + D_νF_{βe} + D_βF_{eν} = 0`; `covH_comm` — `D_eD_νH - D_νD_eH = F_{eν}·H`.
* `ym_leibniz`, `higgs_leibniz` — covariant Leibniz rules for the Yang–Mills and Higgs stresses
  (ad-invariance of the inner products);
* **`ym_div`**, **`higgs_div`** — the divergence identities
  `∇^μT^{YM}_{μν} = g^{αβ}⟨D^μF_{μα}, F_{νβ}⟩`,
  `∇^μT^H_{μν} = 2⟨□_AH - S_H, D_νH⟩ + 2g^{ea}⟨D_aH, F_{eν}·H⟩`.

## The stress Noether structure (field level)

* `Tf` — the complete off-shell stress `T^{SM}` of a smooth tuple (`ActualJet.Tact`: Yang–Mills,
  Higgs and Dirac parts, with the actual normal spinor jets); `divT` — its covariant divergence
  `g^{ea}(∂_eT_{aν} - Γ^l{}_{ea}T_{lν} - Γ^l{}_{eν}T_{al})`;
* **`StressNoether SM`** — the stress Noether identity as a hypothesis **on the theory data**: for
  every smooth tuple and point, `∇^μT_{μν} = K(j¹z)(r^A, r_H, r_D, r̄_D)_ν` with `K` linear in the
  Yang–Mills, Higgs and Dirac residuals and coefficients depending only on the first jets;
* `VariationalStress SM` — variational Yang–Mills–Higgs data (`GenNoether.VariationalBosonic`)
  with symmetric ad-invariant inner products and vanishing Dirac stress form;
* **`divT_variational`** — for such data `∇^μT_{μν} = g^{αβ}⟨r^A_α, F_{νβ}⟩ + 2⟨r_H, D_νH⟩`
  (the current terms cancel against the Lorentz force through the moment map);
  **`stressNoether_of_variational`** — the proved instance; `adjSM_variationalStress`,
  `adjSM_stressNoether` (the concrete `gl(m)` Yang–Mills–adjoint-Higgs data), `trivSMM`.

Disclosure: the Dirac sector is not instantiated.  The library's co-spinor model (`SMData`:
`S' →ₗ S →ₗ ℝ` stress forms, no spinor pairing into the gauge algebra) cannot express the Dirac
current or the Yukawa source, so the variational instance requires the Dirac stress form to vanish
and the current/Higgs source to be spinor independent (spinors decoupled); `StressNoether` itself
is stated for the complete stress including the Dirac part.  The gauge algebra is `gl(m)` with
arbitrary potentials, so the concrete instance is the adjoint Higgs (see
`GenNoether.VariationalBosonic`).
-/

open Finset Set
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenStress

open SobolevOpen (pd)
open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci
  ActualJetBridge ActualJetCompleteForcing ActualJetRecon ActualJetState JetCurve GenNoether

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

/-! ### Real index algebra of contractions -/

section RealAlgebra

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Exchanging the outer and inner of three summations. -/
theorem sum3_swap13 {M : Type*} [AddCommMonoid M] (f : n → n → n → M) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ b, ∑ a, f a b c :=
  calc ∑ a, ∑ b, ∑ c, f a b c = ∑ b, ∑ a, ∑ c, f a b c := Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ a, f a b c := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c, ∑ b, ∑ a, f a b c := Finset.sum_comm

/-- Exchanging the outer and inner of four summations. -/
theorem sum4_swap14 {M : Type*} [AddCommMonoid M] (f : n → n → n → n → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ d, ∑ b, ∑ c, ∑ a, f a b c d :=
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ d, ∑ c, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun a _ => sum3_swap13 (f a)
    _ = ∑ d, ∑ a, ∑ c, ∑ b, f a b c d := Finset.sum_comm
    _ = ∑ d, ∑ b, ∑ c, ∑ a, f a b c d :=
        Finset.sum_congr rfl fun d _ => sum3_swap13 (fun a c b => f a b c d)

/-- Exchanging the outer and inner of five summations. -/
theorem sum5_swap15 {M : Type*} [AddCommMonoid M] (f : n → n → n → n → n → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e = ∑ e, ∑ b, ∑ c, ∑ d, ∑ a, f a b c d e :=
  calc ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e = ∑ a, ∑ e, ∑ c, ∑ d, ∑ b, f a b c d e :=
        Finset.sum_congr rfl fun a _ => sum4_swap14 (f a)
    _ = ∑ e, ∑ a, ∑ c, ∑ d, ∑ b, f a b c d e := Finset.sum_comm
    _ = ∑ e, ∑ b, ∑ c, ∑ d, ∑ a, f a b c d e :=
        Finset.sum_congr rfl fun e _ => sum4_swap14 (fun a c d b => f a b c d e)

/-- **The derivative of a two-index contraction**: if `∂g^{αβ} = -Γ^α{}_c g^{cβ} - Γ^β{}_c g^{αc}`
(`G l α = Γ^l{}_{eα}` for a fixed direction `e`), then
`∂(g^{αβ}P_{αβ}) = g^{αβ}((∂_1P)_{αβ} - Γ^l{}_αP_{lβ} + (∂_2P)_{αβ} - Γ^l{}_βP_{αl})`. -/
theorem contr_deriv (gi dgi : n → n → ℝ) (G : n → n → ℝ)
    (hdgi : ∀ α β, dgi α β = -∑ c, (G α c * gi c β + G β c * gi α c))
    (P dP1 dP2 : n → n → ℝ) :
    ∑ α, ∑ β, (dgi α β * P α β + gi α β * (dP1 α β + dP2 α β)) =
      ∑ α, ∑ β, gi α β * ((dP1 α β - ∑ l, G l α * P l β) + (dP2 α β - ∑ l, G l β * P α l)) := by
  have e1 : ∑ α, ∑ β, ∑ c, G α c * gi c β * P α β = ∑ α, ∑ β, ∑ l, gi α β * (G l α * P l β) := by
    rw [sum3_swap13 (fun α β l => gi α β * (G l α * P l β))]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => ?_
    ring
  have e2 : ∑ α, ∑ β, ∑ c, G β c * gi α c * P α β = ∑ α, ∑ β, ∑ l, gi α β * (G l β * P α l) := by
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun β _ => ?_
    ring
  have hL : ∑ α, ∑ β, (dgi α β * P α β + gi α β * (dP1 α β + dP2 α β)) =
      ∑ α, ∑ β, (gi α β * (dP1 α β + dP2 α β) -
        (∑ c, G α c * gi c β * P α β + ∑ c, G β c * gi α c * P α β)) := by
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    rw [hdgi]
    simp only [neg_mul, Finset.sum_mul, add_mul, Finset.sum_add_distrib]
    ring
  rw [hL]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [e1, e2]
  simp only [mul_add, mul_sub, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

/-- **The derivative of a four-index contraction** `g^{αγ}g^{βδ}P_{αβγδ}`, with the same metric
compatibility hypothesis. -/
theorem contr4_deriv (gi dgi : n → n → ℝ) (G : n → n → ℝ)
    (hdgi : ∀ α β, dgi α β = -∑ c, (G α c * gi c β + G β c * gi α c))
    (P dP : n → n → n → n → ℝ) :
    ∑ α, ∑ β, ∑ γ, ∑ δ, ((dgi α γ * gi β δ + gi α γ * dgi β δ) * P α β γ δ +
        gi α γ * gi β δ * dP α β γ δ) =
      ∑ α, ∑ β, ∑ γ, ∑ δ, gi α γ * gi β δ * (dP α β γ δ - ∑ l, G l α * P l β γ δ -
        ∑ l, G l β * P α l γ δ - ∑ l, G l γ * P α β l δ - ∑ l, G l δ * P α β γ l) := by
  -- the four Christoffel terms, each a relabelling of one half of `∂g^{-1}`
  have e1 : ∑ α, ∑ β, ∑ γ, ∑ δ, ∑ c, G α c * gi c γ * gi β δ * P α β γ δ =
      ∑ α, ∑ β, ∑ γ, ∑ δ, ∑ l, gi α γ * gi β δ * (G l α * P l β γ δ) := by
    rw [sum5_swap15 (fun α β γ δ l => gi α γ * gi β δ * (G l α * P l β γ δ))]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ =>
        Finset.sum_congr rfl fun e _ => ?_
    ring
  have e2 : ∑ α, ∑ β, ∑ γ, ∑ δ, ∑ c, G γ c * gi α c * gi β δ * P α β γ δ =
      ∑ α, ∑ β, ∑ γ, ∑ δ, ∑ l, gi α γ * gi β δ * (G l γ * P α β l δ) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [sum3_swap13 (fun γ δ l => gi a γ * gi b δ * (G l γ * P a b l δ))]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ =>
        Finset.sum_congr rfl fun e _ => ?_
    ring
  have e3 : ∑ α, ∑ β, ∑ γ, ∑ δ, ∑ c, gi α γ * (G β c * gi c δ) * P α β γ δ =
      ∑ α, ∑ β, ∑ γ, ∑ δ, ∑ l, gi α γ * gi β δ * (G l β * P α l γ δ) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sum4_swap14 (fun β γ δ l => gi a γ * gi β δ * (G l β * P a l γ δ))]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
    ring
  have e4 : ∑ α, ∑ β, ∑ γ, ∑ δ, ∑ c, gi α γ * (G δ c * gi β c) * P α β γ δ =
      ∑ α, ∑ β, ∑ γ, ∑ δ, ∑ l, gi α γ * gi β δ * (G l δ * P α β γ l) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
    ring
  have hL : ∑ α, ∑ β, ∑ γ, ∑ δ, ((dgi α γ * gi β δ + gi α γ * dgi β δ) * P α β γ δ +
        gi α γ * gi β δ * dP α β γ δ) =
      ∑ α, ∑ β, ∑ γ, ∑ δ, (gi α γ * gi β δ * dP α β γ δ -
        (∑ c, G α c * gi c γ * gi β δ * P α β γ δ +
          ∑ c, G γ c * gi α c * gi β δ * P α β γ δ +
          ∑ c, gi α γ * (G β c * gi c δ) * P α β γ δ +
          ∑ c, gi α γ * (G δ c * gi β c) * P α β γ δ)) := by
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
      Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => ?_
    rw [hdgi, hdgi]
    simp only [neg_mul, mul_neg, Finset.sum_mul, Finset.mul_sum, add_mul, mul_add,
      Finset.sum_add_distrib]
    ring
  rw [hL]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [e1, e2, e3, e4]
  simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  ring

/-- `Σ_l (Σ_σ g^{lσ}X_σ) g_{lν} = X_ν`. -/
theorem contract_inv (g gi : n → n → ℝ) (hg : ∀ a b, g a b = g b a)
    (hinv : ∀ a c, ∑ b, g a b * gi b c = if a = c then 1 else 0) (X : n → ℝ) (ν : n) :
    ∑ l, (∑ σ, gi l σ * X σ) * g l ν = X ν := by
  have : ∑ l, (∑ σ, gi l σ * X σ) * g l ν = ∑ σ, (∑ l, g ν l * gi l σ) * X σ := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun l _ => ?_
    rw [hg l ν]; ring
  rw [this]
  simp only [hinv, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- **Metric compatibility of the metric**: `Γ^l{}_{eμ}g_{lν} + Γ^l{}_{eν}g_{μl} = ∂_eg_{μν}`. -/
theorem g_compat (g gi : n → n → ℝ) (dg : n → n → n → ℝ) (hg : ∀ a b, g a b = g b a)
    (hinv : ∀ a c, ∑ b, g a b * gi b c = if a = c then 1 else 0)
    (hdg : ∀ α a b, dg α a b = dg α b a) (e μ ν : n) :
    ∑ l, (chr gi dg l e μ * g l ν + chr gi dg l e ν * g μ l) = dg e μ ν := by
  have h1 : ∀ μ ν, ∑ l, chr gi dg l e μ * g l ν =
      (1 / 2) * (dg e ν μ + dg μ ν e - dg ν e μ) := by
    intro μ ν
    have := contract_inv g gi hg hinv (fun σ => (1 / 2) * (dg e σ μ + dg μ σ e - dg σ e μ)) ν
    rw [← this]
    refine Finset.sum_congr rfl fun l _ => ?_
    unfold chr
    rw [Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    ring
  rw [Finset.sum_add_distrib, h1]
  have h2 : ∑ l, chr gi dg l e ν * g μ l = (1 / 2) * (dg e μ ν + dg ν μ e - dg μ e ν) := by
    rw [← h1]
    exact Finset.sum_congr rfl fun l _ => by rw [hg μ l]
  rw [h2, hdg e ν μ, hdg μ ν e, hdg ν e μ]
  ring

end RealAlgebra

/-! ### Covariant derivatives and the Yang–Mills stress -/

section GaugeAlgebra

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]

/-- **The covariant derivative of a field strength** in a fixed direction `e`:
`D_eF_{μν} = ∂_eF_{μν} - Γ^l{}_{eμ}F_{lν} - Γ^l{}_{eν}F_{μl} + [A_e, F_{μν}]`
(`G l α = Γ^l{}_{eα}`, `Ae = A_e`, `dFe = ∂_eF`). -/
def covF (G : n → n → ℝ) (Ae : 𝔤) (F dFe : n → n → 𝔤) (μ ν : n) : 𝔤 :=
  dFe μ ν - ∑ l, G l μ • F l ν - ∑ l, G l ν • F μ l + ⁅Ae, F μ ν⁆

variable (b : 𝔤 →ₗ[ℝ] 𝔤 →ₗ[ℝ] ℝ)

theorem b_covF_left (G : n → n → ℝ) (Ae : 𝔤) (F dFe : n → n → 𝔤) (μ ν : n) (Y : 𝔤) :
    b (covF G Ae F dFe μ ν) Y = b (dFe μ ν) Y - ∑ l, G l μ * b (F l ν) Y -
      ∑ l, G l ν * b (F μ l) Y + b ⁅Ae, F μ ν⁆ Y := by
  simp [covF, map_sub, map_add, map_sum, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]

theorem b_covF_right (G : n → n → ℝ) (Ae : 𝔤) (F dFe : n → n → 𝔤) (μ ν : n) (X : 𝔤) :
    b X (covF G Ae F dFe μ ν) = b X (dFe μ ν) - ∑ l, G l μ * b X (F l ν) -
      ∑ l, G l ν * b X (F μ l) + b X ⁅Ae, F μ ν⁆ := by
  simp [covF, map_sub, map_add, map_sum, map_smul, smul_eq_mul]

/-- The full contraction `g^{αγ}g^{βδ}⟨F_{αβ}, F_{γδ}⟩`. -/
def sq4 (gi : n → n → ℝ) (F : n → n → 𝔤) : ℝ :=
  ∑ α, ∑ β, ∑ γ, ∑ δ, gi α γ * gi β δ * b (F α β) (F γ δ)

/-- Its formal derivative in a direction (`dgie = ∂_eg^{-1}`, `dFe = ∂_eF`). -/
def dsq4 (gi dgie : n → n → ℝ) (F dFe : n → n → 𝔤) : ℝ :=
  ∑ α, ∑ β, ∑ γ, ∑ δ, ((dgie α γ * gi β δ + gi α γ * dgie β δ) * b (F α β) (F γ δ) +
    gi α γ * gi β δ * (b (dFe α β) (F γ δ) + b (F α β) (dFe γ δ)))

/-- The Yang–Mills stress `g^{αβ}⟨F_{μα}, F_{νβ}⟩ - ¼g_{μν}⟨F, F⟩` (as `ymStressB`, any index
type). -/
def ymT (g gi : n → n → ℝ) (F : n → n → 𝔤) (μ ν : n) : ℝ :=
  ∑ α, ∑ β, gi α β * b (F μ α) (F ν β) - (1 / 4) * g μ ν * sq4 b gi F

/-- The formal derivative of the Yang–Mills stress in a direction. -/
def dymT (g gi dge dgie : n → n → ℝ) (F dFe : n → n → 𝔤) (μ ν : n) : ℝ :=
  ∑ α, ∑ β, (dgie α β * b (F μ α) (F ν β) + gi α β * (b (dFe μ α) (F ν β) + b (F μ α) (dFe ν β))) -
    (1 / 4) * (dge μ ν * sq4 b gi F + g μ ν * dsq4 b gi dgie F dFe)

theorem ymT_fin4 (g gi : Fin 4 → Fin 4 → ℝ) (F : Fin 4 → Fin 4 → 𝔤) (μ ν : Fin 4) :
    ymT b g gi F μ ν = ymStressB b g gi F μ ν := rfl

/-- The derivative of the full contraction is the contraction of covariant derivatives. -/
theorem dsq4_eq (hinvb : ∀ X Y Z : 𝔤, b ⁅X, Y⁆ Z + b Y ⁅X, Z⁆ = 0) (gi dgie : n → n → ℝ)
    (G : n → n → ℝ) (hdgi : ∀ α β, dgie α β = -∑ c, (G α c * gi c β + G β c * gi α c))
    (Ae : 𝔤) (F dFe : n → n → 𝔤) :
    dsq4 b gi dgie F dFe = ∑ α, ∑ β, ∑ γ, ∑ δ, gi α γ * gi β δ *
      (b (covF G Ae F dFe α β) (F γ δ) + b (F α β) (covF G Ae F dFe γ δ)) := by
  unfold dsq4
  rw [contr4_deriv gi dgie G hdgi (fun α β γ δ => b (F α β) (F γ δ))
    (fun α β γ δ => b (dFe α β) (F γ δ) + b (F α β) (dFe γ δ))]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => ?_
  rw [b_covF_left, b_covF_right]
  have := hinvb Ae (F α β) (F γ δ)
  congr 1
  linear_combination -this

/-- **The covariant Leibniz rule for the Yang–Mills stress** (ad-invariance of `b`, metric
compatibility): `∂_eT_{μν} - Γ^l{}_{eμ}T_{lν} - Γ^l{}_{eν}T_{μl}` is the stress formula with
one field strength replaced by its covariant derivative `D_eF`. -/
theorem ym_leibniz (hinvb : ∀ X Y Z : 𝔤, b ⁅X, Y⁆ Z + b Y ⁅X, Z⁆ = 0) (g gi dge dgie : n → n → ℝ)
    (G : n → n → ℝ) (hdgi : ∀ α β, dgie α β = -∑ c, (G α c * gi c β + G β c * gi α c))
    (hdg : ∀ μ ν, dge μ ν = ∑ l, (G l μ * g l ν + G l ν * g μ l))
    (Ae : 𝔤) (F dFe : n → n → 𝔤) (μ ν : n) :
    dymT b g gi dge dgie F dFe μ ν - ∑ l, G l μ * ymT b g gi F l ν -
        ∑ l, G l ν * ymT b g gi F μ l =
      ∑ α, ∑ β, gi α β * (b (covF G Ae F dFe μ α) (F ν β) + b (F μ α) (covF G Ae F dFe ν β)) -
        (1 / 4) * g μ ν * ∑ α, ∑ β, ∑ γ, ∑ δ, gi α γ * gi β δ *
          (b (covF G Ae F dFe α β) (F γ δ) + b (F α β) (covF G Ae F dFe γ δ)) := by
  rw [← dsq4_eq b hinvb gi dgie G hdgi Ae F dFe]
  unfold dymT ymT
  rw [contr_deriv gi dgie G hdgi (fun α β => b (F μ α) (F ν β)) (fun α β => b (dFe μ α) (F ν β))
    (fun α β => b (F μ α) (dFe ν β)), hdg μ ν]
  -- expand the covariant derivatives in the two-index part
  have hR : ∀ α β, gi α β * (b (covF G Ae F dFe μ α) (F ν β) + b (F μ α) (covF G Ae F dFe ν β)) =
      gi α β * ((b (dFe μ α) (F ν β) - ∑ l, G l α * b (F μ l) (F ν β)) +
        (b (F μ α) (dFe ν β) - ∑ l, G l β * b (F μ α) (F ν l))) -
      (gi α β * ∑ l, G l μ * b (F l α) (F ν β) + gi α β * ∑ l, G l ν * b (F μ α) (F l β)) := by
    intro α β
    rw [b_covF_left, b_covF_right]
    have := hinvb Ae (F μ α) (F ν β)
    linear_combination gi α β * this
  simp only [hR, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  -- the Christoffel terms of the two-index part
  have hc1 : ∑ α, ∑ β, gi α β * ∑ l, G l μ * b (F l α) (F ν β) =
      ∑ l, G l μ * ∑ α, ∑ β, gi α β * b (F l α) (F ν β) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun α _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun α _ =>
      Finset.sum_congr rfl fun β _ => ?_
    ring
  have hc2 : ∑ α, ∑ β, gi α β * ∑ l, G l ν * b (F μ α) (F l β) =
      ∑ l, G l ν * ∑ α, ∑ β, gi α β * b (F μ α) (F l β) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun α _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun α _ =>
      Finset.sum_congr rfl fun β _ => ?_
    ring
  rw [hc1, hc2]
  have hs1 : ∑ l, G l μ * (∑ α, ∑ β, gi α β * b (F l α) (F ν β) - 1 / 4 * g l ν * sq4 b gi F) =
      ∑ l, G l μ * ∑ α, ∑ β, gi α β * b (F l α) (F ν β) -
        (1 / 4) * sq4 b gi F * ∑ l, G l μ * g l ν := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have hs2 : ∑ l, G l ν * (∑ α, ∑ β, gi α β * b (F μ α) (F l β) - 1 / 4 * g μ l * sq4 b gi F) =
      ∑ l, G l ν * ∑ α, ∑ β, gi α β * b (F μ α) (F l β) -
        (1 / 4) * sq4 b gi F * ∑ l, G l ν * g μ l := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have hs3 : ∑ l, (G l μ * g l ν + G l ν * g μ l) =
      ∑ l, G l μ * g l ν + ∑ l, G l ν * g μ l := Finset.sum_add_distrib
  rw [hs1, hs2]
  ring

end GaugeAlgebra

/-! ### The Bianchi identity and the Yang–Mills divergence -/

section YMDiv

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]

/-- Reversing four summations. -/
theorem sum4_rev {M : Type*} [AddCommMonoid M] (f : n → n → n → n → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ d, ∑ c, ∑ b, ∑ a, f a b c d := by
  rw [sum4_swap14]
  exact Finset.sum_congr rfl fun d _ => Finset.sum_comm

/-- Rotating three summations. -/
theorem sum3_rot {M : Type*} [AddCommMonoid M] (f : n → n → n → M) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ b, ∑ c, ∑ a, f a b c := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_comm

/-- The covariant derivative of an antisymmetric field strength is antisymmetric. -/
theorem covF_anti (G : n → n → ℝ) (Ae : 𝔤) (F dFe : n → n → 𝔤) (hF : ∀ a b, F b a = -F a b)
    (hdF : ∀ a b, dFe b a = -dFe a b) (μ ν : n) :
    covF G Ae F dFe ν μ = -covF G Ae F dFe μ ν := by
  unfold covF
  rw [hdF, hF μ ν, lie_neg]
  have h1 : ∑ l, G l ν • F l μ = -∑ l, G l ν • F μ l := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun l _ => by rw [hF μ l, smul_neg]
  have h2 : ∑ l, G l μ • F ν l = -∑ l, G l μ • F l ν := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun l _ => by rw [hF l ν, smul_neg]
  rw [h1, h2]
  abel

/-- **The Yang–Mills divergence identity** (algebraic form): for a symmetric bilinear form `b`, an
antisymmetric field strength `F` and an antisymmetric covariant derivative array `D e μ ν = D_eF_{μν}`
satisfying the Bianchi identity, the divergence of the covariant Leibniz form of the stress is
`g^{αβ}⟨D^μF_{μα}, F_{νβ}⟩`: the terms quadratic in `F ⊗ DF` cancel by the Bianchi identity. -/
theorem ym_div_alg (b : 𝔤 →ₗ[ℝ] 𝔤 →ₗ[ℝ] ℝ) (hb : ∀ X Y, b X Y = b Y X) (g gi : n → n → ℝ)
    (hgi : ∀ a c, gi a c = gi c a) (hinv : ∀ e c, ∑ a, gi e a * g a c = if e = c then 1 else 0)
    (F : n → n → 𝔤) (hF : ∀ a c, F c a = -F a c) (D : n → n → n → 𝔤)
    (hD : ∀ e a c, D e c a = -D e a c) (hB : ∀ e ν β, D e ν β + D ν β e + D β e ν = 0) (ν : n) :
    ∑ e, ∑ a, gi e a * (∑ α, ∑ β, gi α β * (b (D e a α) (F ν β) + b (F a α) (D e ν β)) -
        (1 / 4) * g a ν * ∑ α, ∑ β, ∑ γ, ∑ δ, gi α γ * gi β δ *
          (b (D e α β) (F γ δ) + b (F α β) (D e γ δ))) =
      ∑ α, ∑ β, gi α β * b (∑ e, ∑ a, gi e a • D e a α) (F ν β) := by
  set X : n → ℝ := fun e => ∑ α, ∑ β, ∑ γ, ∑ δ, gi α γ * gi β δ *
    (b (D e α β) (F γ δ) + b (F α β) (D e γ δ)) with hX
  set T1 := ∑ e, ∑ a, gi e a * ∑ α, ∑ β, gi α β * b (D e a α) (F ν β) with hT1
  set T2 := ∑ e, ∑ a, ∑ α, ∑ β, gi e a * gi α β * b (F a α) (D e ν β) with hT2
  have hsplit : ∑ e, ∑ a, gi e a * (∑ α, ∑ β, gi α β * (b (D e a α) (F ν β) + b (F a α) (D e ν β)) -
      (1 / 4) * g a ν * X e) = T1 + T2 - (1 / 4) * X ν := by
    have h3 : ∑ e, ∑ a, gi e a * ((1 / 4) * g a ν * X e) = (1 / 4) * X ν := by
      have : ∀ e, ∑ a, gi e a * ((1 / 4) * g a ν * X e) =
          (1 / 4) * X e * ∑ a, gi e a * g a ν := by
        intro e
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
      simp only [this, hinv, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true]
    have h12 : ∑ e, ∑ a, gi e a * ∑ α, ∑ β, gi α β * (b (D e a α) (F ν β) + b (F a α) (D e ν β)) =
        T1 + T2 := by
      rw [hT1, hT2, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
      ring
    rw [← h3, ← h12, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hsplit]
  -- the first term is the target
  have hT1' : T1 = ∑ α, ∑ β, gi α β * b (∑ e, ∑ a, gi e a • D e a α) (F ν β) := by
    rw [hT1]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    rw [sum4_swap]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
      Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  -- the Bianchi identity: `2 T2 = Σ g^{ea}g^{αβ}⟨F_{aα}, D_νF_{eβ}⟩`
  have hT2B : T2 = -∑ e, ∑ a, ∑ α, ∑ β, gi e a * gi α β * b (F a α) (D ν β e) -
      ∑ e, ∑ a, ∑ α, ∑ β, gi e a * gi α β * b (F a α) (D β e ν) := by
    rw [hT2, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    have h := hB e ν β
    have : D e ν β = -D ν β e - D β e ν := by
      rw [← sub_eq_zero]
      rw [← h]
      abel
    rw [this, map_sub, map_neg]
    ring
  have hswap : ∑ e, ∑ a, ∑ α, ∑ β, gi e a * gi α β * b (F a α) (D β e ν) = T2 := by
    rw [hT2, sum4_rev (fun e a α β => gi e a * gi α β * b (F a α) (D β e ν))]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun x _ =>
      Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
    simp only [hF x y, hD w ν z, map_neg, LinearMap.neg_apply, neg_neg, hgi z y, hgi x w]
    ring
  have hT2v : T2 = (1 / 2) * ∑ e, ∑ a, ∑ α, ∑ β, gi e a * gi α β * b (F a α) (D ν e β) := by
    have h2 : 2 * T2 = ∑ e, ∑ a, ∑ α, ∑ β, gi e a * gi α β * b (F a α) (D ν e β) := by
      have hh : T2 + T2 = -∑ e, ∑ a, ∑ α, ∑ β, gi e a * gi α β * b (F a α) (D ν β e) := by
        nth_rewrite 1 [hT2B]
        rw [hswap]
        ring
      have hneg : -∑ e, ∑ a, ∑ α, ∑ β, gi e a * gi α β * b (F a α) (D ν β e) =
          ∑ e, ∑ a, ∑ α, ∑ β, gi e a * gi α β * b (F a α) (D ν e β) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [hD ν β e, map_neg]
        ring
      rw [two_mul, hh, hneg]
    linarith
  -- `X_ν = 2 Σ g g ⟨F, D_νF⟩`
  have hXν : X ν = 2 * ∑ e, ∑ a, ∑ α, ∑ β, gi e a * gi α β * b (F a α) (D ν e β) := by
    rw [hX]
    simp only [mul_add, Finset.sum_add_distrib]
    have h1 : ∑ α, ∑ β, ∑ γ, ∑ δ, gi α γ * gi β δ * b (D ν α β) (F γ δ) =
        ∑ e, ∑ a, ∑ α, ∑ β, gi e a * gi α β * b (F a α) (D ν e β) := by
      -- `(α, β, γ, δ) ↦ (e, α', a, β')` with the pairs exchanged
      rw [Finset.sum_congr rfl fun α _ => sum3_rot _]
      refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun γ _ =>
        Finset.sum_congr rfl fun δ _ => Finset.sum_congr rfl fun β _ => ?_
      rw [hb (D ν α β), hgi β δ]
    have h2 : ∑ α, ∑ β, ∑ γ, ∑ δ, gi α γ * gi β δ * b (F α β) (D ν γ δ) =
        ∑ e, ∑ a, ∑ α, ∑ β, gi e a * gi α β * b (F a α) (D ν e β) := by
      rw [Finset.sum_congr rfl fun α _ => Finset.sum_comm, Finset.sum_comm]
      refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun α _ =>
        Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun δ _ => ?_
      rw [hgi α γ]
    rw [h1, h2]
    ring
  rw [hT1', hT2v, hXν]
  ring

end YMDiv

/-! ### The Bianchi identity of the actual field strength jets -/

section Bianchi

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]

/-- **The cyclic identity of the field-strength jets**:
`Σ_cyc (∂_γF_{μν} + [A_γ, F_{μν}]) = 0` for symmetric second jets of the potential (Jacobi). -/
theorem dFm_cyclic (A : Fin 4 → 𝔤) (dA : Fin 4 → Fin 4 → 𝔤) (ddA : Fin 4 → Fin 4 → Fin 4 → 𝔤)
    (hs : ∀ α β μ, ddA α β μ = ddA β α μ) (γ μ ν : Fin 4) :
    dFm A dA ddA γ μ ν + dFm A dA ddA μ ν γ + dFm A dA ddA ν γ μ +
      (⁅A γ, Fm A dA μ ν⁆ + ⁅A μ, Fm A dA ν γ⁆ + ⁅A ν, Fm A dA γ μ⁆) = 0 := by
  unfold dFm Fm fieldStrength
  rw [hs μ γ ν, hs ν γ μ, hs ν μ γ]
  have hj := lie_jacobi (A γ) (A μ) (A ν)
  rw [← lie_skew (dA γ μ) (A ν), ← lie_skew (dA μ ν) (A γ), ← lie_skew (dA ν γ) (A μ)]
  simp only [lie_add, lie_sub]
  calc _ = ⁅A γ, ⁅A μ, A ν⁆⁆ + ⁅A μ, ⁅A ν, A γ⁆⁆ + ⁅A ν, ⁅A γ, A μ⁆⁆ := by abel
    _ = 0 := hj

/-- **The covariant Bianchi identity** `D_eF_{νβ} + D_νF_{βe} + D_βF_{eν} = 0` for the jets of a
smooth potential and a torsion-free (symmetric) connection. -/
theorem covF_bianchi (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) (hΓ : ∀ l a c, Γ l a c = Γ l c a)
    (A : Fin 4 → 𝔤) (dA : Fin 4 → Fin 4 → 𝔤) (ddA : Fin 4 → Fin 4 → Fin 4 → 𝔤)
    (hs : ∀ α β μ, ddA α β μ = ddA β α μ) (e ν β : Fin 4) :
    covF (fun l α => Γ l e α) (A e) (Fm A dA) (dFm A dA ddA e) ν β +
      covF (fun l α => Γ l ν α) (A ν) (Fm A dA) (dFm A dA ddA ν) β e +
      covF (fun l α => Γ l β α) (A β) (Fm A dA) (dFm A dA ddA β) e ν = 0 := by
  unfold covF
  have hc := dFm_cyclic A dA ddA hs e ν β
  have hF : ∀ a c, Fm A dA c a = -Fm A dA a c := Fm_anti A dA
  have p1 : ∑ l, Γ l e ν • Fm A dA l β + ∑ l, Γ l ν e • Fm A dA β l = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun l _ => by rw [hΓ l ν e, hF β l, smul_neg]; abel
  have p2 : ∑ l, Γ l e β • Fm A dA ν l + ∑ l, Γ l β e • Fm A dA l ν = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun l _ => by rw [hΓ l β e, hF ν l, smul_neg]; abel
  have p3 : ∑ l, Γ l ν β • Fm A dA l e + ∑ l, Γ l β ν • Fm A dA e l = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun l _ => by rw [hΓ l β ν, hF e l, smul_neg]; abel
  beta_reduce
  calc _ = (dFm A dA ddA e ν β + dFm A dA ddA ν β e + dFm A dA ddA β e ν +
        (⁅A e, Fm A dA ν β⁆ + ⁅A ν, Fm A dA β e⁆ + ⁅A β, Fm A dA e ν⁆)) -
        ((∑ l, Γ l e ν • Fm A dA l β + ∑ l, Γ l ν e • Fm A dA β l) +
          (∑ l, Γ l e β • Fm A dA ν l + ∑ l, Γ l β e • Fm A dA l ν) +
          (∑ l, Γ l ν β • Fm A dA l e + ∑ l, Γ l β ν • Fm A dA e l)) := by abel
    _ = 0 := by rw [hc, p1, p2, p3]; simp

end Bianchi

/-! ### The Higgs stress -/

section HiggsAlgebra

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [LieRingModule 𝔤 V] [LieModule ℝ 𝔤 V]

/-- **The covariant derivative of the covariant Higgs gradient** in a direction `e`:
`D_eD_μH = ∂_eD_μH - Γ^l{}_{eμ}D_lH + A_e·D_μH`. -/
def covH (G : n → n → ℝ) (Ae : 𝔤) (DH dDHe : n → V) (μ : n) : V :=
  dDHe μ - ∑ l, G l μ • DH l + ⁅Ae, DH μ⁆

variable (bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)

theorem bV_covH_left (G : n → n → ℝ) (Ae : 𝔤) (DH dDHe : n → V) (μ : n) (w : V) :
    bV (covH G Ae DH dDHe μ) w = bV (dDHe μ) w - ∑ l, G l μ * bV (DH l) w + bV ⁅Ae, DH μ⁆ w := by
  simp [covH, map_sub, map_add, map_sum, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]

theorem bV_covH_right (G : n → n → ℝ) (Ae : 𝔤) (DH dDHe : n → V) (μ : n) (u : V) :
    bV u (covH G Ae DH dDHe μ) = bV u (dDHe μ) - ∑ l, G l μ * bV u (DH l) + bV u ⁅Ae, DH μ⁆ := by
  simp [covH, map_sub, map_add, map_sum, map_smul, smul_eq_mul]

/-- The Higgs stress `2⟨D_μH, D_νH⟩ - g_{μν}(g^{αβ}⟨D_αH, D_βH⟩ + λ(⟨H, H⟩ - v²)²)` (as
`higgsStressB`, any index type). -/
def hT (lam v : ℝ) (g gi : n → n → ℝ) (H : V) (DH : n → V) (μ ν : n) : ℝ :=
  2 * bV (DH μ) (DH ν) - g μ ν * (∑ α, ∑ β, gi α β * bV (DH α) (DH β) + lam * (bV H H - v ^ 2) ^ 2)

/-- Its formal derivative in a direction (`dHe = ∂_eH`, `dDHe = ∂_eDH`). -/
def dhT (lam v : ℝ) (g gi dge dgie : n → n → ℝ) (H dHe : V) (DH dDHe : n → V) (μ ν : n) : ℝ :=
  2 * (bV (dDHe μ) (DH ν) + bV (DH μ) (dDHe ν)) -
    (dge μ ν * (∑ α, ∑ β, gi α β * bV (DH α) (DH β) + lam * (bV H H - v ^ 2) ^ 2) +
      g μ ν * (∑ α, ∑ β, (dgie α β * bV (DH α) (DH β) +
        gi α β * (bV (dDHe α) (DH β) + bV (DH α) (dDHe β))) +
        lam * (2 * (bV H H - v ^ 2) * (bV dHe H + bV H dHe))))

theorem hT_fin4 (lam v : ℝ) (g gi : Fin 4 → Fin 4 → ℝ) (H : V) (DH : Fin 4 → V) (μ ν : Fin 4) :
    hT bV lam v g gi H DH μ ν = higgsStressB bV lam v g gi H DH μ ν := rfl

/-- **The covariant Leibniz rule for the Higgs stress** (gauge invariance and symmetry of `bV`,
metric compatibility). -/
theorem higgs_leibniz (hsV : ∀ u w, bV u w = bV w u)
    (hiV : ∀ (X : 𝔤) (u w : V), bV ⁅X, u⁆ w + bV u ⁅X, w⁆ = 0) (lam v : ℝ)
    (g gi dge dgie : n → n → ℝ) (G : n → n → ℝ)
    (hdgi : ∀ α β, dgie α β = -∑ c, (G α c * gi c β + G β c * gi α c))
    (hdg : ∀ μ ν, dge μ ν = ∑ l, (G l μ * g l ν + G l ν * g μ l)) (Ae : 𝔤) (H dHe : V)
    (DH dDHe : n → V) (μ ν : n) :
    dhT bV lam v g gi dge dgie H dHe DH dDHe μ ν - ∑ l, G l μ * hT bV lam v g gi H DH l ν -
        ∑ l, G l ν * hT bV lam v g gi H DH μ l =
      2 * (bV (covH G Ae DH dDHe μ) (DH ν) + bV (DH μ) (covH G Ae DH dDHe ν)) -
        g μ ν * (∑ α, ∑ β, gi α β * (bV (covH G Ae DH dDHe α) (DH β) +
          bV (DH α) (covH G Ae DH dDHe β)) +
          4 * lam * (bV H H - v ^ 2) * bV H (dHe + ⁅Ae, H⁆)) := by
  have hHH : bV H ⁅Ae, H⁆ = 0 := by
    have h := hiV Ae H H
    rw [hsV ⁅Ae, H⁆ H] at h
    linarith
  have hpot : bV dHe H + bV H dHe = 2 * bV H (dHe + ⁅Ae, H⁆) := by
    rw [map_add, hHH, hsV dHe H]
    ring
  have h2 : ∑ α, ∑ β, (dgie α β * bV (DH α) (DH β) +
      gi α β * (bV (dDHe α) (DH β) + bV (DH α) (dDHe β))) =
      ∑ α, ∑ β, gi α β * (bV (covH G Ae DH dDHe α) (DH β) + bV (DH α) (covH G Ae DH dDHe β)) := by
    rw [contr_deriv gi dgie G hdgi (fun α β => bV (DH α) (DH β)) (fun α β => bV (dDHe α) (DH β))
      (fun α β => bV (DH α) (dDHe β))]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    rw [bV_covH_left, bV_covH_right]
    have := hiV Ae (DH α) (DH β)
    linear_combination -(gi α β * this)
  have hμν : 2 * (bV (dDHe μ) (DH ν) + bV (DH μ) (dDHe ν)) =
      2 * (bV (covH G Ae DH dDHe μ) (DH ν) + bV (DH μ) (covH G Ae DH dDHe ν)) +
        ∑ l, G l μ * (2 * bV (DH l) (DH ν)) + ∑ l, G l ν * (2 * bV (DH μ) (DH l)) := by
    rw [bV_covH_left, bV_covH_right]
    have := hiV Ae (DH μ) (DH ν)
    rw [show ∑ l, G l μ * (2 * bV (DH l) (DH ν)) = 2 * ∑ l, G l μ * bV (DH l) (DH ν) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring,
      show ∑ l, G l ν * (2 * bV (DH μ) (DH l)) = 2 * ∑ l, G l ν * bV (DH μ) (DH l) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring]
    linear_combination -(2 * this)
  unfold dhT hT
  rw [h2, hpot, hμν, hdg μ ν]
  set W := ∑ α, ∑ β, gi α β * bV (DH α) (DH β) + lam * (bV H H - v ^ 2) ^ 2
  have hs1 : ∑ l, G l μ * (2 * bV (DH l) (DH ν) - g l ν * W) =
      ∑ l, G l μ * (2 * bV (DH l) (DH ν)) - W * ∑ l, G l μ * g l ν := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hs2 : ∑ l, G l ν * (2 * bV (DH μ) (DH l) - g μ l * W) =
      ∑ l, G l ν * (2 * bV (DH μ) (DH l)) - W * ∑ l, G l ν * g μ l := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [hs1, hs2, Finset.sum_add_distrib]
  ring

/-- **The Higgs divergence identity** (algebraic form): for symmetric `bV`, the divergence of the
covariant Leibniz form of the Higgs stress is
`2⟨□H, D_νH⟩ + 2g^{ea}⟨D_aH, D_eD_νH - D_νD_eH⟩ - 4λ(⟨H, H⟩ - v²)⟨H, D_νH⟩`, and with the
commutator `D_eD_νH - D_νD_eH = F_{eν}·H` the middle term is the Lorentz force. -/
theorem higgs_div_alg (hsV : ∀ u w, bV u w = bV w u) (lam v : ℝ) (g gi : n → n → ℝ)
    (hgi : ∀ a c, gi a c = gi c a) (hinv : ∀ e c, ∑ a, gi e a * g a c = if e = c then 1 else 0)
    (H : V) (DH : n → V) (D2 : n → n → V) (Fc : n → n → V)
    (hcomm : ∀ e ν, D2 e ν - D2 ν e = Fc e ν) (ν : n) :
    ∑ e, ∑ a, gi e a * (2 * (bV (D2 e a) (DH ν) + bV (DH a) (D2 e ν)) -
        g a ν * (∑ α, ∑ β, gi α β * (bV (D2 e α) (DH β) + bV (DH α) (D2 e β)) +
          4 * lam * (bV H H - v ^ 2) * bV H (DH e))) =
      2 * bV (∑ e, ∑ a, gi e a • D2 e a) (DH ν) + 2 * ∑ e, ∑ a, gi e a * bV (DH a) (Fc e ν) -
        4 * lam * (bV H H - v ^ 2) * bV H (DH ν) := by
  set Y : n → ℝ := fun e => ∑ α, ∑ β, gi α β * (bV (D2 e α) (DH β) + bV (DH α) (D2 e β)) +
    4 * lam * (bV H H - v ^ 2) * bV H (DH e) with hY
  have hsplit : ∑ e, ∑ a, gi e a * (2 * (bV (D2 e a) (DH ν) + bV (DH a) (D2 e ν)) -
      g a ν * Y e) = 2 * bV (∑ e, ∑ a, gi e a • D2 e a) (DH ν) +
        2 * ∑ e, ∑ a, gi e a * bV (DH a) (D2 e ν) - Y ν := by
    have h3 : ∑ e, ∑ a, gi e a * (g a ν * Y e) = Y ν := by
      have : ∀ e, ∑ a, gi e a * (g a ν * Y e) = Y e * ∑ a, gi e a * g a ν := by
        intro e
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
      simp only [this, hinv, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true]
    have h1 : bV (∑ e, ∑ a, gi e a • D2 e a) (DH ν) = ∑ e, ∑ a, gi e a * bV (D2 e a) (DH ν) := by
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [← h3, h1, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hsplit]
  have hYν : Y ν = 2 * ∑ e, ∑ a, gi e a * bV (DH a) (D2 ν e) +
      4 * lam * (bV H H - v ^ 2) * bV H (DH ν) := by
    rw [hY]
    simp only
    congr 1
    have h1 : ∑ α, ∑ β, gi α β * bV (D2 ν α) (DH β) = ∑ e, ∑ a, gi e a * bV (DH a) (D2 ν e) :=
      Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => by rw [hsV]
    have h2 : ∑ α, ∑ β, gi α β * bV (DH α) (D2 ν β) = ∑ e, ∑ a, gi e a * bV (DH a) (D2 ν e) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun a _ => by rw [hgi a e]
    simp only [mul_add, Finset.sum_add_distrib, h1, h2]
    ring
  rw [hYν]
  have hc : ∑ e, ∑ a, gi e a * bV (DH a) (D2 e ν) - ∑ e, ∑ a, gi e a * bV (DH a) (D2 ν e) =
      ∑ e, ∑ a, gi e a * bV (DH a) (Fc e ν) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hcomm e ν, map_sub]
    ring
  linear_combination 2 * hc

/-- **The covariant commutator of the Higgs jets**: `D_eD_νH - D_νD_eH = F_{eν}·H` for symmetric
second jets and a symmetric connection. -/
theorem covH_comm (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) (hΓ : ∀ l a c, Γ l a c = Γ l c a)
    (A : Fin 4 → 𝔤) (dA : Fin 4 → Fin 4 → 𝔤) (H : V) (dH : Fin 4 → V) (ddH : Fin 4 → Fin 4 → V)
    (hs : ∀ α β, ddH α β = ddH β α) (e ν : Fin 4) :
    covH (fun l α => Γ l e α) (A e) (ActualJetGauge.DH A H dH) (dDH A dA H dH ddH e) ν -
      covH (fun l α => Γ l ν α) (A ν) (ActualJetGauge.DH A H dH) (dDH A dA H dH ddH ν) e =
      ⁅Fm A dA e ν, H⁆ := by
  unfold covH
  have hc := covariant_commutator A dA H dH ddH hs e ν
  have hsum : ∑ l, Γ l e ν • ActualJetGauge.DH A H dH l = ∑ l, Γ l ν e • ActualJetGauge.DH A H dH l :=
    Finset.sum_congr rfl fun l _ => by rw [hΓ l e ν]
  beta_reduce
  rw [hsum]
  calc _ = (dDH A dA H dH ddH e ν - dDH A dA H dH ddH ν e) -
      (⁅A ν, ActualJetGauge.DH A H dH e⁆ - ⁅A e, ActualJetGauge.DH A H dH ν⁆) := by abel
    _ = ⁅Fm A dA e ν, H⁆ := by rw [hc]; abel

end HiggsAlgebra

/-! ### The stress Noether structure -/

section Structure

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable (SM : SMData (MatLie m) V S S') (z : Tuple m V S S')

/-- **The complete off-shell stress** `T^{SM}_{μν}` of a smooth tuple (`ActualJet.Tact`: the
Yang–Mills, Higgs and Dirac stresses of the theory data on the actual jets). -/
def Tf (y : ST 3) (μ ν : Fin 4) : ℝ := (z.jet y).Tact SM μ ν

/-- **Its covariant divergence** `∇^aT_{aν} = g^{ea}(∂_eT_{aν} - Γ^l{}_{ea}T_{lν} - Γ^l{}_{eν}T_{al})`
(Levi-Civita connection of the tuple's metric). -/
def divT (x : ST 3) (ν : Fin 4) : ℝ :=
  ∑ e, ∑ a, z.gi x e a * (pd (fun y => Tf SM z y a ν) e x -
    ∑ l, chr (z.gi x) (z.dg x) l e a * Tf SM z x l ν -
    ∑ l, chr (z.gi x) (z.dg x) l e ν * Tf SM z x a l)

/-- The matter residuals `(r^A, r_H, r_D, r̄_D)` of the tuple. -/
def resV (x : ST 3) : (Fin 4 → MatLie m) × V × S × S' :=
  ((bosF SM z x).2.1, (bosF SM z x).2.2, (dirF SM z x).1, (dirF SM z x).2)

/-- **The stress Noether identity as a hypothesis on the theory data**
(`lem:generated-physical-identification`, `prop:subsidiary`; implicit in the manuscript): for every
smooth field tuple and every point, the covariant divergence of the complete stress is a linear
combination of the Yang–Mills, Higgs and Dirac residuals, `∇^μT_{μν} = K(j¹z)(r^A, r_H, r_D, r̄_D)_ν`,
with coefficients depending only on the first jets (as for the stress of a diffeomorphism- and
gauge-invariant Lagrangian).  The Einstein residual does not enter. -/
structure StressNoether where
  /-- the coefficients of the residual combination -/
  K : FirstJet (MatLie m) V S S' → ((Fin 4 → MatLie m) × V × S × S') →ₗ[ℝ] (Fin 4 → ℝ)
  /-- the Noether identity -/
  div_eq : ∀ (z : Tuple m V S S') (x : ST 3) (ν : Fin 4),
    divT SM z x ν = K ((z.jet x).firstJet SM) (resV SM z x) ν

variable {SM}

/-- **The stress is conserved wherever the matter equations hold** (`∇^μT_{μν} = 0`), for theory
data satisfying the stress Noether identity. -/
theorem divT_eq_zero (hN : StressNoether SM) {x : ST 3} (hA : (bosF SM z x).2.1 = 0)
    (hH : (bosF SM z x).2.2 = 0) (hD : dirF SM z x = 0) (ν : Fin 4) : divT SM z x ν = 0 := by
  rw [hN.div_eq]
  have : resV SM z x = 0 := by
    unfold resV
    rw [hA, hH, hD]
    rfl
  rw [this, map_zero]
  rfl

end Structure

/-! ### Variational Yang–Mills–Higgs data -/

section Variational

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

/-- **Variational Yang–Mills–Higgs theory data with symmetric invariant forms**: the data of
`GenNoether.VariationalBosonic` (moment map, current `J = 2μ(H, DH)`, Higgs source
`S_H = 2λ(⟨H, H⟩ - v²)H`), the gauge form `⟨·,·⟩_𝔤` symmetric and ad-invariant, the Higgs form
symmetric, and the Dirac stress form zero (spinors decoupled from the metric; the co-spinor model
cannot express the Dirac stress/current, disclosed). -/
structure VariationalStress (SM : SMData (MatLie m) V S S') extends VariationalBosonic SM where
  ipG_symm : ∀ X Y : MatLie m, SM.ipG X Y = SM.ipG Y X
  ipG_inv : ∀ X Y Z : MatLie m, SM.ipG ⁅X, Y⁆ Z + SM.ipG Y ⁅X, Z⁆ = 0
  ipV_symm : ∀ u w : V, SM.ipV u w = SM.ipV w u
  P_zero : ∀ A B C, SM.TD.P A B C = 0
  P'_zero : ∀ A B C, SM.TD.P' A B C = 0
  P''_zero : ∀ A B w, SM.TD.P'' A B w = 0

/-- The Higgs form of variational data is gauge invariant (moment map, alternation, symmetry). -/
theorem VariationalStress.ipV_inv {SM : SMData (MatLie m) V S S'} (hV : VariationalStress SM)
    (X : MatLie m) (u w : V) : SM.ipV ⁅X, u⁆ w + SM.ipV u ⁅X, w⁆ = 0 := by
  rw [hV.ipV_symm u, ← hV.moment, ← hV.moment]
  have hanti : hV.μ w u = -hV.μ u w := by
    have h := hV.alt (u + w)
    simp only [map_add, LinearMap.add_apply, hV.alt, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_left h
  rw [hanti, map_neg, add_neg_cancel]

/-- The residual coefficients of the variational stress identity:
`K(j¹z)(r^A, r_H, r_D, r̄_D)_ν = g^{αβ}⟨r^A_α, F_{νβ}⟩ + 2⟨r_H, D_νH⟩`. -/
def stressK (SM : SMData (MatLie m) V S S') (fj : FirstJet (MatLie m) V S S') :
    ((Fin 4 → MatLie m) × V × S × S') →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun r := fun ν => ∑ α, ∑ β, fj.gi α β * SM.ipG (r.1 α) (fj.F ν β) +
    2 * SM.ipV r.2.1 (fj.DH ν)
  map_add' r r' := by
    funext ν
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add, LinearMap.add_apply, mul_add,
      Finset.sum_add_distrib]
    ring
  map_smul' c r := by
    funext ν
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    rw [mul_add, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun α _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun β _ => by ring
    · ring

end Variational

/-! ### The variational instance: field calculus -/

section Instance

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable {SM : SMData (MatLie m) V S S'} (z : Tuple m V S S')

/-- For variational data the stress is the Yang–Mills plus Higgs stress. -/
theorem Tf_eq (hV : VariationalStress SM) (y : ST 3) (μ ν : Fin 4) :
    Tf SM z y μ ν = ymT SM.ipG (z.g y) (z.gi y) (Fld z y) μ ν +
      hT SM.ipV SM.lamH SM.vH (z.g y) (z.gi y) (z.H y) (GenNoether.DHf z y) μ ν := by
  unfold Tf ActualJet.Tact
  have h0 : ∀ (g : Fin 4 → Fin 4 → ℝ) (ε : Fin 4 → ℝ) (e : Fin 4 → Fin 4 → ℝ) (H : V) (ψ : S)
      (X : Fin 4 → S) (ψb : S') (Xb : Fin 4 → S') (μ ν : Fin 4),
      SM.TD.coord g ε e H ψ X ψb Xb μ ν = 0 := by
    intro g ε e H ψ X ψb Xb μ ν
    simp [DiracStressForm.coord, DiracStressForm.frame, hV.P_zero, hV.P'_zero, hV.P''_zero]
  rw [h0, add_zero]
  rfl

theorem e0_line (x : ST 3) (δ : Fin 4) : x + (0 : ℝ) • ev δ = x := by simp

/-- The Yang–Mills stress along a coordinate line. -/
theorem line_ymT (b : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ) (x : ST 3) (δ μ ν : Fin 4) :
    HasDerivAt (fun s : ℝ => ymT b (z.g (x + s • ev δ)) (z.gi (x + s • ev δ))
      (Fld z (x + s • ev δ)) μ ν)
      (dymT b (z.g x) (z.gi x) (z.dg x δ) (dginv (z.gi x) (z.dg x) δ) (Fld z x)
        (dFm (z.jet x).A (z.jet x).dA (z.jet x).ddA δ) μ ν) 0 := by
  have hF : ∀ a c, HasDerivAt (fun s : ℝ => Fld z (x + s • ev δ) a c)
      (dFm (z.jet x).A (z.jet x).dA (z.jet x).ddA δ a c) 0 := fun a c => z.line_Fm x δ a c
  have hb : ∀ a c a' c', HasDerivAt (fun s : ℝ => b (Fld z (x + s • ev δ) a c)
      (Fld z (x + s • ev δ) a' c'))
      (b (dFm (z.jet x).A (z.jet x).dA (z.jet x).ddA δ a c) (Fld z x a' c') +
        b (Fld z x a c) (dFm (z.jet x).A (z.jet x).dA (z.jet x).ddA δ a' c')) 0 := by
    intro a c a' c'
    have h := hasDerivAt_bilin b (hF a c) (hF a' c')
    simp only [e0_line] at h
    exact h
  have hgi : ∀ a c, HasDerivAt (fun s : ℝ => z.gi (x + s • ev δ) a c)
      (dginv (z.gi x) (z.dg x) δ a c) 0 := fun a c => z.line_gi x δ a c
  have hg : ∀ a c, HasDerivAt (fun s : ℝ => z.g (x + s • ev δ) a c) (z.dg x δ a c) 0 :=
    fun a c => z.line_g x δ a c
  have h2 : HasDerivAt (fun s : ℝ => ∑ α, ∑ β, z.gi (x + s • ev δ) α β *
      b (Fld z (x + s • ev δ) μ α) (Fld z (x + s • ev δ) ν β))
      (∑ α, ∑ β, (dginv (z.gi x) (z.dg x) δ α β * b (Fld z x μ α) (Fld z x ν β) +
        z.gi x α β * (b (dFm (z.jet x).A (z.jet x).dA (z.jet x).ddA δ μ α) (Fld z x ν β) +
          b (Fld z x μ α) (dFm (z.jet x).A (z.jet x).dA (z.jet x).ddA δ ν β)))) 0 := by
    refine HasDerivAt.fun_sum fun α _ => HasDerivAt.fun_sum fun β _ => ?_
    have h := (hgi α β).fun_mul (hb μ α ν β)
    simp only [e0_line] at h
    exact h
  have h4 : HasDerivAt (fun s : ℝ => sq4 b (z.gi (x + s • ev δ)) (Fld z (x + s • ev δ)))
      (dsq4 b (z.gi x) (dginv (z.gi x) (z.dg x) δ) (Fld z x)
        (dFm (z.jet x).A (z.jet x).dA (z.jet x).ddA δ)) 0 := by
    unfold sq4 dsq4
    refine HasDerivAt.fun_sum fun α _ => HasDerivAt.fun_sum fun β _ =>
      HasDerivAt.fun_sum fun γ _ => HasDerivAt.fun_sum fun δ' _ => ?_
    have h := ((hgi α γ).fun_mul (hgi β δ')).fun_mul (hb α β γ δ')
    simp only [e0_line] at h
    exact h
  have hres := h2.sub (((hg μ ν).const_mul (1 / 4 : ℝ)).fun_mul h4)
  simp only [e0_line] at hres
  unfold ymT dymT
  refine hres.congr_deriv ?_
  ring

/-- The Higgs stress along a coordinate line. -/
theorem line_hT (bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (lam v : ℝ) (x : ST 3) (δ μ ν : Fin 4) :
    HasDerivAt (fun s : ℝ => hT bV lam v (z.g (x + s • ev δ)) (z.gi (x + s • ev δ))
      (z.H (x + s • ev δ)) (GenNoether.DHf z (x + s • ev δ)) μ ν)
      (dhT bV lam v (z.g x) (z.gi x) (z.dg x δ) (dginv (z.gi x) (z.dg x) δ) (z.H x) (pd z.H δ x)
        (GenNoether.DHf z x)
        (fun μ => dDH (z.A x) (fun μ ν => pd z.A μ x ν) (z.H x) (fun μ => pd z.H μ x)
          (fun δ μ => pd (pd z.H μ) δ x) δ μ) μ ν) 0 := by
  have hD : ∀ a, HasDerivAt (fun s : ℝ => GenNoether.DHf z (x + s • ev δ) a)
      (dDH (z.A x) (fun μ ν => pd z.A μ x ν) (z.H x) (fun μ => pd z.H μ x)
        (fun δ μ => pd (pd z.H μ) δ x) δ a) 0 := fun a => GenNoether.line_DHf z x δ a
  have hb : ∀ a c, HasDerivAt (fun s : ℝ => bV (GenNoether.DHf z (x + s • ev δ) a)
      (GenNoether.DHf z (x + s • ev δ) c))
      (bV (dDH (z.A x) (fun μ ν => pd z.A μ x ν) (z.H x) (fun μ => pd z.H μ x)
        (fun δ μ => pd (pd z.H μ) δ x) δ a) (GenNoether.DHf z x c) +
        bV (GenNoether.DHf z x a) (dDH (z.A x) (fun μ ν => pd z.A μ x ν) (z.H x)
          (fun μ => pd z.H μ x) (fun δ μ => pd (pd z.H μ) δ x) δ c)) 0 := by
    intro a c
    have h := hasDerivAt_bilin bV (hD a) (hD c)
    simp only [e0_line] at h
    exact h
  have hgi : ∀ a c, HasDerivAt (fun s : ℝ => z.gi (x + s • ev δ) a c)
      (dginv (z.gi x) (z.dg x) δ a c) 0 := fun a c => z.line_gi x δ a c
  have hg : ∀ a c, HasDerivAt (fun s : ℝ => z.g (x + s • ev δ) a c) (z.dg x δ a c) 0 :=
    fun a c => z.line_g x δ a c
  have hH := z.line_H x δ
  have hHH : HasDerivAt (fun s : ℝ => bV (z.H (x + s • ev δ)) (z.H (x + s • ev δ)))
      (bV (pd z.H δ x) (z.H x) + bV (z.H x) (pd z.H δ x)) 0 := by
    have h := hasDerivAt_bilin bV hH hH
    simp only [e0_line] at h
    exact h
  have hsum : HasDerivAt (fun s : ℝ => ∑ α, ∑ β, z.gi (x + s • ev δ) α β *
      bV (GenNoether.DHf z (x + s • ev δ) α) (GenNoether.DHf z (x + s • ev δ) β))
      (∑ α, ∑ β, (dginv (z.gi x) (z.dg x) δ α β *
        bV (GenNoether.DHf z x α) (GenNoether.DHf z x β) +
        z.gi x α β * (bV (dDH (z.A x) (fun μ ν => pd z.A μ x ν) (z.H x) (fun μ => pd z.H μ x)
          (fun δ μ => pd (pd z.H μ) δ x) δ α) (GenNoether.DHf z x β) +
          bV (GenNoether.DHf z x α) (dDH (z.A x) (fun μ ν => pd z.A μ x ν) (z.H x)
            (fun μ => pd z.H μ x) (fun δ μ => pd (pd z.H μ) δ x) δ β)))) 0 := by
    refine HasDerivAt.fun_sum fun α _ => HasDerivAt.fun_sum fun β _ => ?_
    have h := (hgi α β).fun_mul (hb α β)
    simp only [e0_line] at h
    exact h
  have hpot := ((hHH.sub_const (v ^ 2)).pow 2).const_mul lam
  have hres := ((hb μ ν).const_mul (2 : ℝ)).sub ((hg μ ν).fun_mul (hsum.add hpot))
  simp only [Pi.add_apply, Pi.pow_apply, e0_line] at hres
  unfold hT dhT
  refine hres.congr_deriv ?_
  simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]

end Instance

/-! ### The variational instance: the divergence identity -/

section InstanceDiv

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable {SM : SMData (MatLie m) V S S'} (z : Tuple m V S S')

theorem contDiffAt_ymT (b : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ) (μ ν : Fin 4) (y : ST 3) :
    ContDiffAt ℝ ∞ (fun y => ymT b (z.g y) (z.gi y) (Fld z y) μ ν) y := by
  have h1 : ∀ a c, ContDiffAt ℝ ∞ (fun y => z.gi y a c) y := fun a c =>
    (z.contDiff_gi a c).contDiffAt
  have h2 : ∀ a c, ContDiffAt ℝ ∞ (fun y => z.g y a c) y := fun a c =>
    (z.contDiff_gc a c).contDiffAt
  have h3 : ∀ a c, ContDiffAt ℝ ∞ (fun y => Fld z y a c) y := fun a c =>
    (contDiff_Fld z a c).contDiffAt
  unfold ymT sq4
  fun_prop

theorem contDiffAt_hT (bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (lam v : ℝ) (μ ν : Fin 4) (y : ST 3) :
    ContDiffAt ℝ ∞ (fun y => hT bV lam v (z.g y) (z.gi y) (z.H y) (GenNoether.DHf z y) μ ν) y := by
  have h1 : ∀ a c, ContDiffAt ℝ ∞ (fun y => z.gi y a c) y := fun a c =>
    (z.contDiff_gi a c).contDiffAt
  have h2 : ∀ a c, ContDiffAt ℝ ∞ (fun y => z.g y a c) y := fun a c =>
    (z.contDiff_gc a c).contDiffAt
  have h3 : ∀ a, ContDiffAt ℝ ∞ (fun y => GenNoether.DHf z y a) y := fun a =>
    (contDiff_pi.1 (GenNoether.contDiff_DHf z) a).contDiffAt
  have h4 : ContDiffAt ℝ ∞ z.H y := z.H_smooth.contDiffAt
  unfold hT
  fun_prop

/-- **The partial derivative of the stress** of variational data: the formal derivative of the
Yang–Mills and Higgs stresses on the actual jets. -/
theorem pd_Tf (hV : VariationalStress SM) (x : ST 3) (e a ν : Fin 4) :
    pd (fun y => Tf SM z y a ν) e x =
      dymT SM.ipG (z.g x) (z.gi x) (z.dg x e) (dginv (z.gi x) (z.dg x) e) (Fld z x)
        (dFm (z.jet x).A (z.jet x).dA (z.jet x).ddA e) a ν +
      dhT SM.ipV SM.lamH SM.vH (z.g x) (z.gi x) (z.dg x e) (dginv (z.gi x) (z.dg x) e) (z.H x)
        (pd z.H e x) (GenNoether.DHf z x)
        (fun μ => dDH (z.A x) (fun μ ν => pd z.A μ x ν) (z.H x) (fun μ => pd z.H μ x)
          (fun δ μ => pd (pd z.H μ) δ x) e μ) a ν := by
  have hfun : (fun y => Tf SM z y a ν) = fun y => ymT SM.ipG (z.g y) (z.gi y) (Fld z y) a ν +
      hT SM.ipV SM.lamH SM.vH (z.g y) (z.gi y) (z.H y) (GenNoether.DHf z y) a ν :=
    funext fun y => Tf_eq z hV y a ν
  rw [hfun]
  refine pd_eq_of_line ?_ ((line_ymT z SM.ipG x e a ν).add (line_hT z SM.ipV SM.lamH SM.vH x e a ν))
  exact ((contDiffAt_ymT z SM.ipG a ν x).add (contDiffAt_hT z SM.ipV SM.lamH SM.vH a ν x)
    ).differentiableAt (by simp)

end InstanceDiv

/-! ### The variational instance: assembly -/

section InstanceMain

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable {SM : SMData (MatLie m) V S S'} (z : Tuple m V S S')

/-- `Σ_a g^{ea}g_{ac} = δ_{ec}` along the tuple. -/
theorem gi_mul_g (x : ST 3) (e c : Fin 4) :
    ∑ a, z.gi x e a * z.g x a c = if e = c then 1 else 0 := by
  have h := z.hinv x c e
  rw [show (if e = c then (1 : ℝ) else 0) = if c = e then 1 else 0 by
    by_cases hce : c = e
    · subst hce; simp
    · simp [hce, Ne.symm hce]]
  rw [← h]
  exact Finset.sum_congr rfl fun a _ => by rw [z.gi_symm x e a, z.g_symm x a c, mul_comm]

/-- The Yang–Mills divergence is the contracted covariant derivative. -/
theorem ymDiv_eq_covF (x : ST 3) (α : Fin 4) :
    ymDiv (z.jet x).A (z.jet x).dA (z.jet x).ddA (z.gi x) (chr (z.gi x) (z.dg x)) α =
      ∑ e, ∑ a, z.gi x e a • covF (fun l β => chr (z.gi x) (z.dg x) l e β) (z.A x e) (Fld z x)
        (dFm (z.jet x).A (z.jet x).dA (z.jet x).ddA e) a α := by
  unfold ymDiv covF
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun a _ => ?_
  rw [z.gi_symm x a e, Finset.sum_add_distrib, ← sub_sub]
  rfl

/-- The covariant wave operator is the contracted covariant derivative. -/
theorem waveH_eq_covH (x : ST 3) :
    waveH (z.jet x).A (z.jet x).dA (z.jet x).H (z.jet x).dH (z.jet x).ddH (z.gi x)
        (chr (z.gi x) (z.dg x)) =
      ∑ e, ∑ a, z.gi x e a • covH (fun l β => chr (z.gi x) (z.dg x) l e β) (z.A x e)
        (GenNoether.DHf z x)
        (fun μ => dDH (z.A x) (fun μ ν => pd z.A μ x ν) (z.H x) (fun μ => pd z.H μ x)
          (fun δ μ => pd (pd z.H μ) δ x) e μ) a := by
  unfold waveH covH
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun a _ => ?_
  rw [z.gi_symm x a e]
  rfl

/-- **The stress Noether identity for variational Yang–Mills–Higgs data**:
`∇^μT_{μν} = g^{αβ}⟨r^A_α, F_{νβ}⟩ + 2⟨r_H, D_νH⟩` for every smooth tuple (covariant Leibniz
rules, the Bianchi identity, the covariant commutator `[D, D]H = F·H`, the moment map: the current
term `g^{αβ}⟨J_α, F_{νβ}⟩` of the Yang–Mills divergence cancels the Lorentz force of the Higgs
stress, and the potential term cancels against the Higgs source). -/
theorem divT_variational (hV : VariationalStress SM) (x : ST 3) (ν : Fin 4) :
    divT SM z x ν = stressK SM ((z.jet x).firstJet SM) (resV SM z x) ν := by
  have hgis : ∀ a c, z.gi x a c = z.gi x c a := z.gi_symm x
  have hdgs : ∀ α a c, z.dg x α a c = z.dg x α c a := z.dg_symm x
  have hΓs : ∀ l a c, chr (z.gi x) (z.dg x) l a c = chr (z.gi x) (z.dg x) l c a :=
    fun l a c => (GenNoether.chr_symm (z.gi x) (z.dg x) hdgs l c a)
  have hinv' := gi_mul_g z x
  -- the covariant derivative arrays
  set DF : Fin 4 → Fin 4 → Fin 4 → MatLie m := fun e μ α =>
    covF (fun l β => chr (z.gi x) (z.dg x) l e β) (z.A x e) (Fld z x)
      (dFm (z.jet x).A (z.jet x).dA (z.jet x).ddA e) μ α with hDF
  set D2 : Fin 4 → Fin 4 → V := fun e μ =>
    covH (fun l β => chr (z.gi x) (z.dg x) l e β) (z.A x e) (GenNoether.DHf z x)
      (fun μ => dDH (z.A x) (fun μ ν => pd z.A μ x ν) (z.H x) (fun μ => pd z.H μ x)
        (fun δ μ => pd (pd z.H μ) δ x) e μ) μ with hD2
  -- Leibniz rules in each direction
  have hL : ∀ e a, pd (fun y => Tf SM z y a ν) e x -
      ∑ l, chr (z.gi x) (z.dg x) l e a * Tf SM z x l ν -
      ∑ l, chr (z.gi x) (z.dg x) l e ν * Tf SM z x a l =
      (∑ α, ∑ β, z.gi x α β * (SM.ipG (DF e a α) (Fld z x ν β) +
          SM.ipG (Fld z x a α) (DF e ν β)) -
        (1 / 4) * z.g x a ν * ∑ α, ∑ β, ∑ γ, ∑ δ, z.gi x α γ * z.gi x β δ *
          (SM.ipG (DF e α β) (Fld z x γ δ) + SM.ipG (Fld z x α β) (DF e γ δ))) +
      (2 * (SM.ipV (D2 e a) (GenNoether.DHf z x ν) + SM.ipV (GenNoether.DHf z x a) (D2 e ν)) -
        z.g x a ν * (∑ α, ∑ β, z.gi x α β * (SM.ipV (D2 e α) (GenNoether.DHf z x β) +
          SM.ipV (GenNoether.DHf z x α) (D2 e β)) +
          4 * SM.lamH * (SM.ipV (z.H x) (z.H x) - SM.vH ^ 2) *
            SM.ipV (z.H x) (GenNoether.DHf z x e))) := by
    intro e a
    simp only [hDF, hD2]
    have hdgi : ∀ α β, dginv (z.gi x) (z.dg x) e α β = -∑ c,
        (chr (z.gi x) (z.dg x) α e c * z.gi x c β + chr (z.gi x) (z.dg x) β e c * z.gi x α c) :=
      fun α β => GenNoether.dginv_eq_chr (z.gi x) (z.dg x) hgis hdgs e α β
    have hdg : ∀ μ ν, z.dg x e μ ν = ∑ l, (chr (z.gi x) (z.dg x) l e μ * z.g x l ν +
        chr (z.gi x) (z.dg x) l e ν * z.g x μ l) := fun μ ν =>
      (g_compat (z.g x) (z.gi x) (z.dg x) (z.g_symm x) (z.hinv x) hdgs e μ ν).symm
    have h1 := ym_leibniz SM.ipG hV.ipG_inv (z.g x) (z.gi x) (z.dg x e)
      (dginv (z.gi x) (z.dg x) e) (fun l β => chr (z.gi x) (z.dg x) l e β) hdgi hdg (z.A x e)
      (Fld z x) (dFm (z.jet x).A (z.jet x).dA (z.jet x).ddA e) a ν
    have h2 := higgs_leibniz SM.ipV hV.ipV_symm hV.ipV_inv SM.lamH SM.vH (z.g x) (z.gi x)
      (z.dg x e) (dginv (z.gi x) (z.dg x) e) (fun l β => chr (z.gi x) (z.dg x) l e β) hdgi hdg
      (z.A x e) (z.H x) (pd z.H e x) (GenNoether.DHf z x)
      (fun μ => dDH (z.A x) (fun μ ν => pd z.A μ x ν) (z.H x) (fun μ => pd z.H μ x)
        (fun δ μ => pd (pd z.H μ) δ x) e μ) a ν
    have hDHe : pd z.H e x + ⁅z.A x e, z.H x⁆ = GenNoether.DHf z x e := rfl
    rw [hDHe] at h2
    rw [← h1, ← h2, pd_Tf z hV x e a ν]
    simp only [Tf_eq z hV x, mul_add, Finset.sum_add_distrib]
    ring
  -- the divergence
  have hsum : divT SM z x ν = ∑ e, ∑ a, z.gi x e a *
      (∑ α, ∑ β, z.gi x α β * (SM.ipG (DF e a α) (Fld z x ν β) +
          SM.ipG (Fld z x a α) (DF e ν β)) -
        (1 / 4) * z.g x a ν * ∑ α, ∑ β, ∑ γ, ∑ δ, z.gi x α γ * z.gi x β δ *
          (SM.ipG (DF e α β) (Fld z x γ δ) + SM.ipG (Fld z x α β) (DF e γ δ))) +
      ∑ e, ∑ a, z.gi x e a *
      (2 * (SM.ipV (D2 e a) (GenNoether.DHf z x ν) + SM.ipV (GenNoether.DHf z x a) (D2 e ν)) -
        z.g x a ν * (∑ α, ∑ β, z.gi x α β * (SM.ipV (D2 e α) (GenNoether.DHf z x β) +
          SM.ipV (GenNoether.DHf z x α) (D2 e β)) +
          4 * SM.lamH * (SM.ipV (z.H x) (z.H x) - SM.vH ^ 2) *
            SM.ipV (z.H x) (GenNoether.DHf z x e))) := by
    unfold divT
    simp only [hL, mul_add, Finset.sum_add_distrib]
  have hYM := ym_div_alg SM.ipG hV.ipG_symm (z.g x) (z.gi x) hgis hinv' (Fld z x)
    (fun a c => Fm_anti _ _ a c) DF
    (fun e a c => covF_anti _ _ _ _ (fun a c => Fm_anti _ _ a c)
      (fun a c => dFm_anti _ _ _ e a c) a c)
    (fun e ν β => covF_bianchi (chr (z.gi x) (z.dg x)) hΓs (z.jet x).A (z.jet x).dA
      (z.jet x).ddA (z.jet x).ddA_symm e ν β) ν
  have hH := higgs_div_alg SM.ipV hV.ipV_symm SM.lamH SM.vH (z.g x) (z.gi x) hgis hinv' (z.H x)
    (GenNoether.DHf z x) D2 (fun e ν => ⁅Fld z x e ν, z.H x⁆)
    (fun e ν => covH_comm (chr (z.gi x) (z.dg x)) hΓs (z.jet x).A (z.jet x).dA (z.jet x).H
      (z.jet x).dH (z.jet x).ddH (z.jet x).ddH_symm e ν) ν
  rw [hsum, hYM, hH]
  simp only [hDF, hD2]
  simp only [← ymDiv_eq_covF z x, ← waveH_eq_covH z x]
  -- the residuals
  have hrA : ∀ α, ymDiv (z.jet x).A (z.jet x).dA (z.jet x).ddA (z.gi x) (chr (z.gi x) (z.dg x)) α =
      (bosF SM z x).2.1 α + (2 : ℝ) • hV.μ (z.H x) (GenNoether.DHf z x α) := by
    intro α
    show _ = ymRes _ _ _ _ _ _ α + _
    unfold ymRes
    rw [hV.J_eq]
    exact (sub_add_cancel _ _).symm
  have hrH : waveH (z.jet x).A (z.jet x).dA (z.jet x).H (z.jet x).dH (z.jet x).ddH (z.gi x)
      (chr (z.gi x) (z.dg x)) = (bosF SM z x).2.2 +
        (2 * SM.lamH * (SM.ipV (z.H x) (z.H x) - SM.vH ^ 2)) • z.H x := by
    show _ = higgsRes _ _ _ _ _ _ _ _ + _
    unfold higgsRes
    rw [hV.SH_eq]
    exact (sub_add_cancel _ _).symm
  simp only [hrA, hrH, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  -- the Lorentz force cancels the current term
  have hmom : ∀ e a, SM.ipV (GenNoether.DHf z x a) ⁅Fld z x e ν, z.H x⁆ =
      SM.ipG (Fld z x e ν) (hV.μ (z.H x) (GenNoether.DHf z x a)) := by
    intro e a
    rw [hV.ipV_symm, hV.moment]
  have hcur : ∑ α, ∑ β, z.gi x α β * (2 * SM.ipG (hV.μ (z.H x) (GenNoether.DHf z x α))
      (Fld z x ν β)) + 2 * ∑ e, ∑ a, z.gi x e a * SM.ipV (GenNoether.DHf z x a)
        ⁅Fld z x e ν, z.H x⁆ = 0 := by
    simp only [hmom]
    have : ∑ e, ∑ a, z.gi x e a * SM.ipG (Fld z x e ν) (hV.μ (z.H x) (GenNoether.DHf z x a)) =
        -∑ α, ∑ β, z.gi x α β * SM.ipG (hV.μ (z.H x) (GenNoether.DHf z x α)) (Fld z x ν β) := by
      rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [show Fld z x β ν = -Fld z x ν β from Fm_anti _ _ ν β, map_neg, LinearMap.neg_apply,
        hV.ipG_symm, hgis β α]
      ring
    rw [this]
    have hA : ∑ α, ∑ β, z.gi x α β * (2 * SM.ipG (hV.μ (z.H x) (GenNoether.DHf z x α))
        (Fld z x ν β)) = 2 * ∑ α, ∑ β, z.gi x α β *
          SM.ipG (hV.μ (z.H x) (GenNoether.DHf z x α)) (Fld z x ν β) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun β _ => by ring
    rw [hA]
    ring
  simp only [stressK, LinearMap.coe_mk, AddHom.coe_mk, resV]
  simp only [mul_add, Finset.sum_add_distrib] at hcur ⊢
  change _ = ∑ α, ∑ β, z.gi x α β * SM.ipG ((bosF SM z x).2.1 α) (Fld z x ν β) +
    2 * SM.ipV (bosF SM z x).2.2 (GenNoether.DHf z x ν)
  linear_combination hcur

end InstanceMain

/-! ### The proved instances -/

section Instances

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

/-- **The stress Noether identity holds for variational Yang–Mills–Higgs data**
(`StressNoether` with `K(j¹z)(r^A, r_H, ·, ·)_ν = g^{αβ}⟨r^A_α, F_{νβ}⟩ + 2⟨r_H, D_νH⟩`). -/
def stressNoether_of_variational {SM : SMData (MatLie m) V S S'} (hV : VariationalStress SM) :
    StressNoether SM where
  K := stressK SM
  div_eq := fun z x ν => divT_variational z hV x ν

/-- The `gl(m)` Yang–Mills–adjoint-Higgs data (`GenNoether.adjSM`) are variational with
symmetric ad-invariant trace forms and no Dirac stress. -/
def adjSM_variationalStress (m : ℕ) (Λ κ lam v : ℝ) :
    VariationalStress (adjSM m Λ κ lam v) where
  toVariationalBosonic := adjSM_variational m Λ κ lam v
  ipG_symm := fun X Y => by
    show traceForm m X Y = traceForm m Y X
    rw [traceForm_apply, traceForm_apply, Matrix.trace_mul_comm]
  ipG_inv := fun X Y Z => by
    show traceForm m ⁅X, Y⁆ Z + traceForm m Y ⁅X, Z⁆ = 0
    rw [traceForm_apply, traceForm_apply, toMat_lie, toMat_lie, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.trace_sub, Matrix.trace_sub, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.trace_mul_comm (toMat Y) (toMat Z * toMat X), Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm (toMat Z), Matrix.mul_assoc]
    ring
  ipV_symm := fun u w => by
    show traceForm m u w = traceForm m w u
    rw [traceForm_apply, traceForm_apply, Matrix.trace_mul_comm]
  P_zero := fun _ _ _ => rfl
  P'_zero := fun _ _ _ => rfl
  P''_zero := fun _ _ _ => rfl

/-- **The concrete Standard-Model-type instance of the stress Noether identity**: the `gl(m)`
Yang–Mills–adjoint-Higgs data satisfy `StressNoether`. -/
def adjSM_stressNoether (m : ℕ) (Λ κ lam v : ℝ) : StressNoether (adjSM m Λ κ lam v) :=
  stressNoether_of_variational (adjSM_variationalStress m Λ κ lam v)

/-- The flat-vacuum data `trivSMM` are variational with vanishing forms. -/
def trivSMM_variationalStress : VariationalStress trivSMM where
  toVariationalBosonic := trivSMM_variational
  ipG_symm := fun _ _ => by simp [trivSMM]
  ipG_inv := fun _ _ _ => by simp [trivSMM]
  ipV_symm := fun _ _ => by simp [trivSMM]
  P_zero := fun _ _ _ => rfl
  P'_zero := fun _ _ _ => rfl
  P''_zero := fun _ _ _ => rfl

/-- The flat-vacuum data satisfy the stress Noether identity. -/
def trivSMM_stressNoether : StressNoether trivSMM :=
  stressNoether_of_variational trivSMM_variationalStress

/-- Non-vacuity: along every smooth tuple of the `gl(2)` Yang–Mills–adjoint-Higgs model the
divergence of the complete stress is the residual combination. -/
example (z : Tuple 2 (MatLie 2) PUnit PUnit) (x : ST 3) (ν : Fin 4) :
    divT (adjSM 2 0 1 1 1) z x ν = ∑ α, ∑ β, z.gi x α β *
      traceForm 2 ((bosF (adjSM 2 0 1 1 1) z x).2.1 α) (Fld z x ν β) +
      2 * traceForm 2 (bosF (adjSM 2 0 1 1 1) z x).2.2 (GenNoether.DHf z x ν) :=
  (adjSM_stressNoether 2 0 1 1 1).div_eq z x ν

end Instances

end RenewalGeometry.GenStress
