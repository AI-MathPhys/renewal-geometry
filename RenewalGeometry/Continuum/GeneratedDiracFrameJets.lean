/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedDiracAlgebra
import RenewalGeometry.Continuum.GeneratedResidualSmooth

/-!
# The adapted frame on metric 1-jets and its metric variation

Einstein–Standard-Model action-closure manuscript, `eq:dirac-density`, `eq:stress-definition`,
`app:generated-dynamics` (stationarity with the Dirac term).  The actual-jet model uses the
adapted frame `e = frU(g⁻¹)` (`GenResMaps.frR`), its frame-derivative jets
`∂_γe = frameJet(g⁻¹, ∂g⁻¹)` (`GenResMaps.deR`) and the connection coefficients
`G_{ABC} = ⟨∇_{e_A}e_B, e_C⟩` (`ActualJetSystem.Gfun`), all as functions of the metric 1-jet
`(g, ∂g)`.  This file proves, for every metric 1-jet in the Lorentzian chart:

* `compl_R`, `orth_R`, `decomp_R` — completeness and orthonormality of the adapted frame, and the
  frame decomposition `v = Σ_D ε_D⟨v, e_D⟩e_D`;
* `hasDerivAt_frR_line` — along a line of metrics the frame moves by the frame jet;
  `orth1_R` — the derivative of orthonormality;
* `GR`, `OmR` — the connection coefficients and the structure coefficients
  `Ω_{BAC} = ⟨[e_B, e_A], e_C⟩` on 1-jets; **`GR_anti`** (metric compatibility) and
  **`GR_tors`** (torsion-freeness `G_{BAC} - G_{ABC} = Ω_{BAC}`).
-/

open Finset Set Filter Topology
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenDFJ

open SobolevOpen (pd)
open FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame ActualJetSystem ActualJetSmooth
  ActualJetBridge GenResMaps JetCurve GenDAlg

set_option linter.unusedSectionVars false

/-! ### The chart -/

/-- A metric in the Lorentzian chart: nondegenerate, symmetric, with inverse in the chart of
the adapted frame. -/
def ChartM (g : Met) : Prop :=
  (Matrix.of g).det ≠ 0 ∧ IsLorChart (ginvOf g) ∧ ∀ μ ν, g μ ν = g ν μ

/-- **Completeness of the adapted frame**: `g^{μν} = Σ_A ε_A e_A{}^μ e_A{}^ν`. -/
theorem compl_R {g : Met} (hg : ChartM g) (μ ν : Fin 4) :
    ginvOf g μ ν = ∑ A, lorentzSign A * frR g A μ * frR g A ν := by
  have h := frameOf_adapted (ginvOf_symm hg.2.2) hg.2.1 μ ν
  rw [Fin.sum_univ_succ]
  simp only [lorentzSign, Fin.succ_ne_zero, ite_false, ite_true, one_mul]
  rw [h]
  simp only [frR]
  rw [neg_one_mul, neg_mul]
  rfl

theorem hinv_R {g : Met} (hg : ChartM g) (a c : Fin 4) :
    ∑ b, g a b * ginvOf g b c = if a = c then 1 else 0 := mul_ginvOf hg.1 a c

/-- **Orthonormality of the adapted frame**: `g(e_A, e_B) = ε_Aδ_{AB}`. -/
theorem orth_R {g : Met} (hg : ChartM g) (A B : Fin 4) :
    ipg g (frR g A) (frR g B) = if A = B then lorentzSign A else 0 :=
  orth_of_compl (hinv_R hg) lorentzSign_sq (compl_R hg) A B

/-- **The frame decomposition** `v^μ = Σ_D ε_D g(v, e_D) e_D{}^μ`. -/
theorem decomp_R {g : Met} (hg : ChartM g) (v : Fin 4 → ℝ) (μ : Fin 4) :
    v μ = ∑ D, lorentzSign D * ipg g v (frR g D) * frR g D μ := by
  have e : ∑ D, lorentzSign D * ipg g v (frR g D) * frR g D μ =
      ∑ a, ∑ b, g a b * v a * ginvOf g b μ := by
    simp only [ipg, compl_R hg, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun D _ => ?_
    ring
  rw [e]
  have h2 : ∀ a, ∑ b, g a b * v a * ginvOf g b μ = v a * (if a = μ then 1 else 0) := by
    intro a
    rw [← hinv_R hg a μ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  simp only [h2, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem eventually_chartM {g k : Met} (hg : ChartM g) (hk : ∀ μ ν, k μ ν = k ν μ) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), ChartM (g + ε • k) := by
  have hc : Continuous fun ε : ℝ => g + ε • k := by fun_prop
  have hdet : ContinuousAt (fun ε : ℝ => (Matrix.of (g + ε • k)).det) 0 :=
    (Continuous.matrix_det (A := fun M : Met => Matrix.of M) continuous_id).continuousAt.comp
      hc.continuousAt
  have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), (Matrix.of (g + ε • k)).det ≠ 0 := by
    have : (Matrix.of (g + (0 : ℝ) • k)).det ≠ 0 := by simpa using hg.1
    exact hdet.eventually (isOpen_ne.mem_nhds this)
  have hgi : ContinuousAt (fun ε : ℝ => ginvOf (g + ε • k)) 0 := by
    have : ContDiffAt ℝ ∞ (fun ε : ℝ => ginvOf (g + ε • k)) 0 :=
      ContDiffAt.ginvOf_fun (by fun_prop) (by simpa using hg.1)
    exact this.continuousAt
  have h2 : ∀ᶠ ε in 𝓝 (0 : ℝ), IsLorChart (ginvOf (g + ε • k)) :=
    eventually_chart hgi (by simpa using hg.2.1)
  filter_upwards [h1, h2] with ε h1 h2
  exact ⟨h1, h2, fun μ ν => by simp [hg.2.2 μ ν, hk μ ν]⟩

/-! ### Line derivatives of the frame -/

/-- **Along a line of metrics the adapted frame moves by its frame jet**:
`d/ds e(g + s·dg_δ)|_{s=0} = deR(g, dg)_δ`. -/
theorem hasDerivAt_frR_line {g : Met} (hg : ChartM g) (dgf : Fin 4 → Met) (δ A μ : Fin 4) :
    HasDerivAt (fun s : ℝ => frR (g + s • dgf δ) A μ) (deR g dgf δ A μ) 0 := by
  have hl : ∀ a b, HasDerivAt (fun s : ℝ => (g + s • dgf δ) a b) (dgf δ a b) 0 := fun a b => by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (dgf δ a b)).const_add (g a b)
    simpa using this
  have h0 : g + (0 : ℝ) • dgf δ = g := by simp
  have hgi : ∀ l σ, HasDerivAt (fun s : ℝ => ginvOf (g + s • dgf δ) l σ)
      (dginv (ginvOf g) dgf δ l σ) 0 := fun l σ => by
    have := hasDerivAt_ginvOf (g := fun s : ℝ => g + s • dgf δ) (t := 0) δ hl
      (by rw [h0]; exact hg.1) l σ
    simpa only [h0] using this
  have hgi' : HasDerivAt (fun s : ℝ => ginvOf (g + s • dgf δ))
      (fun l σ => dginv (ginvOf g) dgf δ l σ) 0 :=
    hasDerivAt_pi.2 fun l => hasDerivAt_pi.2 fun σ => hgi l σ
  have hc : IsLorChart ((fun s : ℝ => ginvOf (g + s • dgf δ)) 0) := by
    show IsLorChart (ginvOf (g + (0 : ℝ) • dgf δ)); rw [h0]; exact hg.2.1
  have := hasDerivAt_frU_comp hgi' hc A μ
  simp only [h0] at this
  exact this

/-- **The derivative of orthonormality**: `∂_γ(g(e_A, e_B)) = 0` on every metric 1-jet of the
chart with symmetric `∂_γg`. -/
theorem orth1_R {g : Met} (hg : ChartM g) (dg : Fin 4 → Met)
    (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ) (γ A B : Fin 4) :
    dipg g dg (frR g A) (fun γ μ => deR g dg γ A μ) (frR g B) (fun γ μ => deR g dg γ B μ) γ = 0 := by
  have hl : ∀ a b, HasDerivAt (fun s : ℝ => (g + s • dg γ) a b) (dg γ a b) 0 := fun a b => by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (dg γ a b)).const_add (g a b)
    simpa using this
  have h := hasDerivAt_ipg (g := fun s : ℝ => g + s • dg γ) (X := fun s => frR (g + s • dg γ) A)
    (Y := fun s => frR (g + s • dg γ) B) (t := 0) (dg := dg)
    (dX := fun γ μ => deR g dg γ A μ) (dY := fun γ μ => deR g dg γ B μ) γ hl
    (fun μ => hasDerivAt_frR_line hg dg γ A μ) (fun ν => hasDerivAt_frR_line hg dg γ B ν)
  have h0 : g + (0 : ℝ) • dg γ = g := by simp
  simp only [h0] at h
  have hev : (fun s : ℝ => ipg (g + s • dg γ) (frR (g + s • dg γ) A) (frR (g + s • dg γ) B)) =ᶠ[𝓝 0]
      fun _ => if A = B then lorentzSign A else 0 := by
    filter_upwards [eventually_chartM hg (hdg γ)] with s hs
    exact orth_R hs A B
  exact h.unique ((hasDerivAt_const (0 : ℝ) _).congr_of_eventuallyEq hev)

/-! ### Connection and structure coefficients on 1-jets -/

/-- The connection coefficients `G_{ABC} = ⟨∇_{e_A}e_B, e_C⟩` of the adapted frame on a metric
1-jet. -/
def GR (g : Met) (dg : Fin 4 → Met) (A B C : Fin 4) : ℝ :=
  Gfun g (ginvOf g) dg (frR g) (deR g dg) A B C

/-- The frame commutator `[e_B, e_A]^μ = Σ_γ(e_B{}^γ∂_γe_A{}^μ - e_A{}^γ∂_γe_B{}^μ)` on jets. -/
def commR (e : Fin 4 → Fin 4 → ℝ) (de : Fin 4 → Fin 4 → Fin 4 → ℝ) (B A : Fin 4) (μ : Fin 4) : ℝ :=
  ∑ γ, (e B γ * de γ A μ - e A γ * de γ B μ)

/-- The structure coefficients `Ω_{BAC} = g([e_B, e_A], e_C)` on a metric 1-jet. -/
def OmR (g : Met) (dg : Fin 4 → Met) (B A C : Fin 4) : ℝ :=
  ipg g (commR (frR g) (deR g dg) B A) (frR g C)

/-- **Metric compatibility of the frame connection** on metric 1-jets of the chart. -/
theorem GR_anti {g : Met} (hg : ChartM g) (dg : Fin 4 → Met)
    (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ) (A B C : Fin 4) : GR g dg A C B = -GR g dg A B C := by
  have hcomp := metric_compat g (ginvOf g) dg (hinv_R hg) hdg
  have h : ∀ γ, ipg g (fun μ => cv1 (chr (ginvOf g) dg) (frR g B) (fun γ μ => deR g dg γ B μ) γ μ)
      (frR g C) + ipg g (fun μ => cv1 (chr (ginvOf g) dg) (frR g C)
        (fun γ μ => deR g dg γ C μ) γ μ) (frR g B) = 0 := fun γ => by
    have h1 := dipg_eq g hg.2.2 dg (chr (ginvOf g) dg) hcomp (frR g B)
      (fun γ μ => deR g dg γ B μ) (frR g C) (fun γ μ => deR g dg γ C μ) γ
    rw [orth1_R hg dg hdg γ B C] at h1
    rw [ipg_comm g hg.2.2 (frR g B)] at h1
    linarith
  unfold GR Gfun
  rw [eq_neg_iff_add_eq_zero, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun γ _ => ?_
  rw [← mul_add, add_comm, h γ, mul_zero]

/-- **Torsion-freeness**: `G_{BAC} - G_{ABC} = Ω_{BAC}` on metric 1-jets (symmetric `∂g`). -/
theorem GR_tors (g : Met) (dg : Fin 4 → Met) (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ)
    (B A C : Fin 4) : GR g dg B A C - GR g dg A B C = OmR g dg B A C := by
  have hs : ∀ μ γ σ, chr (ginvOf g) dg μ γ σ = chr (ginvOf g) dg μ σ γ := fun μ γ σ =>
    chr_symm' (ginvOf g) dg hdg μ γ σ
  unfold GR Gfun OmR
  generalize chr (ginvOf g) dg = Γ at hs ⊢
  obtain ⟨Γ', rfl⟩ : ∃ Γ' : Fin 4 → Fin 4 → Fin 4 → ℝ, Γ = fun μ γ σ => Γ' μ γ σ + Γ' μ σ γ :=
    ⟨fun μ γ σ => Γ μ γ σ / 2, by
      funext μ γ σ; show Γ μ γ σ = Γ μ γ σ / 2 + Γ μ σ γ / 2; rw [hs μ γ σ]; ring⟩
  simp only [ipg, cv1, commR, Fin.sum_univ_four]
  ring

/-! ### The metric variation of the frame jets -/

/-- The first-order variation `ė = D e(g)[k]` of the adapted frame. -/
def edot (g k : Met) (A μ : Fin 4) : ℝ := deR g (fun _ => k) 0 A μ

/-- The first-order variation of the frame-derivative jets along the jet line
`(g + εk, ∂g + ε∂k)`. -/
def dedot (g : Met) (dg : Fin 4 → Met) (k : Met) (dk : Fin 4 → Met) (γ A μ : Fin 4) : ℝ :=
  deriv (fun ε : ℝ => deR (g + ε • k) (dg + ε • dk) γ A μ) 0

/-- The first-order variation of the connection coefficients along the jet line. -/
def Gdot (g : Met) (dg : Fin 4 → Met) (k : Met) (dk : Fin 4 → Met) (B A C : Fin 4) : ℝ :=
  deriv (fun ε : ℝ => GR (g + ε • k) (dg + ε • dk) B A C) 0

/-- The frame components `Λ_{AB} = g(ė_A, e_B)` of the frame variation. -/
def Lam (g k : Met) (A B : Fin 4) : ℝ := ipg g (edot g k A) (frR g B)

/-- The frame components `k_{AB} = k(e_A, e_B)` of the metric variation. -/
def kfr (g k : Met) (A B : Fin 4) : ℝ := ipg k (frR g A) (frR g B)

/-- The frame derivatives `dΛ_{B;AC} = e_B(Λ_{AC})` of the frame variation on jets. -/
def dLam (g : Met) (dg : Fin 4 → Met) (k : Met) (dk : Fin 4 → Met) (B A C : Fin 4) : ℝ :=
  ∑ γ, frR g B γ * dipg g dg (edot g k A) (fun γ μ => dedot g dg k dk γ A μ) (frR g C)
    (fun γ μ => deR g dg γ C μ) γ

section Line

variable {g : Met} (hg : ChartM g)
include hg

theorem hasDerivAt_edot (k : Met) (A μ : Fin 4) :
    HasDerivAt (fun s : ℝ => frR (g + s • k) A μ) (edot g k A μ) 0 :=
  hasDerivAt_frR_line hg (fun _ => k) 0 A μ

theorem contDiffAt_deR_line (dg : Fin 4 → Met) (k : Met) (dk : Fin 4 → Met) (γ A μ : Fin 4) :
    ContDiffAt ℝ ∞ (fun ε : ℝ => deR (g + ε • k) (dg + ε • dk) γ A μ) 0 := by
  have h1 : (Matrix.of (g + (0 : ℝ) • k)).det ≠ 0 := by simpa using hg.1
  have hgi : ContDiffAt ℝ ∞ (fun ε : ℝ => ginvOf (g + ε • k)) 0 :=
    ContDiffAt.ginvOf_fun (by fun_prop) h1
  have h2 : IsLorChart (ginvOf (g + (0 : ℝ) • k)) := by simpa using hg.2.1
  unfold deR
  refine ContDiffAt.frameJet hgi ?_ h2 γ A μ
  have : ContDiffAt ℝ ∞ (fun ε : ℝ => dg + ε • dk) 0 := by fun_prop
  unfold dginv
  rw [contDiffAt_pi]; intro γ'; rw [contDiffAt_pi]; intro l; rw [contDiffAt_pi]; intro σ
  have hgi' : ∀ a b, ContDiffAt ℝ ∞ (fun ε : ℝ => ginvOf (g + ε • k) a b) 0 := fun a b =>
    contDiffAt_pi.1 (contDiffAt_pi.1 hgi a) b
  have hd : ∀ a b, ContDiffAt ℝ ∞ (fun ε : ℝ => (dg + ε • dk) γ' a b) 0 := fun a b => by
    fun_prop
  fun_prop

theorem hasDerivAt_dedot (dg : Fin 4 → Met) (k : Met) (dk : Fin 4 → Met) (γ A μ : Fin 4) :
    HasDerivAt (fun ε : ℝ => deR (g + ε • k) (dg + ε • dk) γ A μ) (dedot g dg k dk γ A μ) 0 :=
  ((contDiffAt_deR_line hg dg k dk γ A μ).differentiableAt (by simp)).hasDerivAt

theorem line_const (w : Met) : ∀ a b, HasDerivAt (fun s : ℝ => (g + s • w) a b) (w a b) 0 :=
  fun a b => by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (w a b)).const_add (g a b)
    simpa using this

/-- **The frame variation preserves orthonormality to first order**:
`Λ_{AB} + Λ_{BA} = -k_{AB}`. -/
theorem Lam_add (k : Met) (hk : ∀ μ ν, k μ ν = k ν μ) (A B : Fin 4) :
    Lam g k A B + Lam g k B A = -kfr g k A B := by
  have h := hasDerivAt_ipg (g := fun s : ℝ => g + s • k) (X := fun s => frR (g + s • k) A)
    (Y := fun s => frR (g + s • k) B) (t := 0) (dg := fun _ => k)
    (dX := fun _ μ => edot g k A μ) (dY := fun _ μ => edot g k B μ) 0 (line_const hg k)
    (fun μ => hasDerivAt_edot hg k A μ) (fun ν => hasDerivAt_edot hg k B ν)
  have h0 : g + (0 : ℝ) • k = g := by simp
  simp only [h0] at h
  have hev : (fun s : ℝ => ipg (g + s • k) (frR (g + s • k) A) (frR (g + s • k) B)) =ᶠ[𝓝 0]
      fun _ => if A = B then lorentzSign A else 0 := by
    filter_upwards [eventually_chartM hg hk] with s hs
    exact orth_R hs A B
  have h2 := h.unique ((hasDerivAt_const (0 : ℝ) _).congr_of_eventuallyEq hev)
  unfold dipg at h2
  unfold Lam kfr
  rw [ipg_comm g hg.2.2 (edot g k B)]
  unfold ipg
  simp only [Finset.sum_add_distrib] at h2
  linarith

/-- **The frame variation in the frame**: `ė_A = Σ_D ε_DΛ_{AD}e_D`. -/
theorem edot_decomp (k : Met) (A μ : Fin 4) :
    edot g k A μ = ∑ D, lorentzSign D * Lam g k A D * frR g D μ :=
  decomp_R hg (edot g k A) μ

/-- **The derivative of completeness**: `∂_γg^{μν} = Σ_D ε_D(∂_γe_D{}^μe_D{}^ν + e_D{}^μ∂_γe_D{}^ν)`. -/
theorem compl1_R (dg : Fin 4 → Met) (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ) (γ μ ν : Fin 4) :
    dginv (ginvOf g) dg γ μ ν =
      ∑ D, lorentzSign D * (deR g dg γ D μ * frR g D ν + frR g D μ * deR g dg γ D ν) := by
  have h0 : g + (0 : ℝ) • dg γ = g := by simp
  have hL := hasDerivAt_ginvOf (g := fun s : ℝ => g + s • dg γ) (t := 0) γ (line_const hg (dg γ))
    (by rw [h0]; exact hg.1) μ ν
  simp only [h0] at hL
  have hR : HasDerivAt (fun s : ℝ => ∑ D, lorentzSign D * frR (g + s • dg γ) D μ *
      frR (g + s • dg γ) D ν)
      (∑ D, lorentzSign D * (deR g dg γ D μ * frR g D ν + frR g D μ * deR g dg γ D ν)) 0 := by
    refine HasDerivAt.fun_sum fun D _ => ?_
    have := (((hasDerivAt_frR_line hg dg γ D μ).const_mul (lorentzSign D)).fun_mul
      (hasDerivAt_frR_line hg dg γ D ν))
    simp only [h0] at this
    exact this.congr_deriv (by ring)
  have hev : (fun s : ℝ => ginvOf (g + s • dg γ) μ ν) =ᶠ[𝓝 0]
      fun s => ∑ D, lorentzSign D * frR (g + s • dg γ) D μ * frR (g + s • dg γ) D ν := by
    filter_upwards [eventually_chartM hg (hdg γ)] with s hs
    exact compl_R hs μ ν
  exact hL.unique (hR.congr_of_eventuallyEq hev)

/-- The coordinate derivative `∂_γΛ_{AD}` on jets. -/
def dLg (g : Met) (dg : Fin 4 → Met) (k : Met) (dk : Fin 4 → Met) (γ A D : Fin 4) : ℝ :=
  dipg g dg (edot g k A) (fun γ μ => dedot g dg k dk γ A μ) (frR g D) (fun γ μ => deR g dg γ D μ) γ

theorem dLam_eq (dg : Fin 4 → Met) (k : Met) (dk : Fin 4 → Met) (B A C : Fin 4) :
    dLam g dg k dk B A C = ∑ γ, frR g B γ * dLg g dg k dk γ A C := rfl

theorem compl_zero (dg : Fin 4 → Met) (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ) (γ a μ : Fin 4) :
    ∑ D, lorentzSign D * (∑ b, dg γ a b * frR g D b * frR g D μ +
      ∑ b, g a b * deR g dg γ D b * frR g D μ + ∑ b, g a b * frR g D b * deR g dg γ D μ) = 0 := by
  have e1 : ∑ D, lorentzSign D * (∑ b, dg γ a b * frR g D b * frR g D μ +
      ∑ b, g a b * deR g dg γ D b * frR g D μ + ∑ b, g a b * frR g D b * deR g dg γ D μ) =
      ∑ b, dg γ a b * (∑ D, lorentzSign D * frR g D b * frR g D μ) +
      ∑ b, g a b * (∑ D, lorentzSign D * (deR g dg γ D b * frR g D μ +
        frR g D b * deR g dg γ D μ)) := by
    simp only [Fin.sum_univ_four]; ring
  rw [e1]
  simp only [← compl_R hg, ← compl1_R hg dg hdg]
  unfold dginv
  have e2 : ∑ b, g a b * -∑ c, ∑ d, ginvOf g b c * dg γ c d * ginvOf g d μ =
      -∑ d, (∑ c, (∑ b, g a b * ginvOf g b c) * dg γ c d) * ginvOf g d μ := by
    simp only [Fin.sum_univ_four]; ring
  have hgi : ∀ d, ∑ c, (∑ b, g a b * ginvOf g b c) * dg γ c d = dg γ a d := fun d => by
    simp only [hinv_R hg, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true]
  rw [e2]
  simp only [hgi]
  ring

/-- **The variation of the frame jets in the frame**:
`δ(∂_γe_A) = Σ_D ε_D(∂_γΛ_{AD}e_D + Λ_{AD}∂_γe_D)`. -/
theorem dedot_decomp (dg : Fin 4 → Met) (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ) (k : Met)
    (dk : Fin 4 → Met) (γ A μ : Fin 4) :
    dedot g dg k dk γ A μ = ∑ D, lorentzSign D * (dLg g dg k dk γ A D * frR g D μ +
      Lam g k A D * deR g dg γ D μ) := by
  set v : Fin 4 → ℝ := fun μ => dedot g dg k dk γ A μ with hv
  set w : Fin 4 → ℝ := edot g k A with hw
  have key : ∑ D, lorentzSign D * (dLg g dg k dk γ A D * frR g D μ +
      Lam g k A D * deR g dg γ D μ) =
      ∑ D, lorentzSign D * ipg g v (frR g D) * frR g D μ +
      ∑ a, w a * ∑ D, lorentzSign D * (∑ b, dg γ a b * frR g D b * frR g D μ +
        ∑ b, g a b * deR g dg γ D b * frR g D μ + ∑ b, g a b * frR g D b * deR g dg γ D μ) := by
    simp only [dLg, Lam, dipg, ipg, hv, hw, Fin.sum_univ_four]
    ring
  rw [key]
  simp only [compl_zero hg dg hdg, mul_zero, Finset.sum_const_zero, add_zero]
  exact decomp_R hg v μ

/-- The variation of the frame commutator along the jet line. -/
def dcomm (g : Met) (dg : Fin 4 → Met) (k : Met) (dk : Fin 4 → Met) (B A μ : Fin 4) : ℝ :=
  ∑ γ, (edot g k B γ * deR g dg γ A μ + frR g B γ * dedot g dg k dk γ A μ -
    (edot g k A γ * deR g dg γ B μ + frR g A γ * dedot g dg k dk γ B μ))

theorem hasDerivAt_commR (dg : Fin 4 → Met) (k : Met) (dk : Fin 4 → Met) (B A μ : Fin 4) :
    HasDerivAt (fun ε : ℝ => commR (frR (g + ε • k)) (deR (g + ε • k) (dg + ε • dk)) B A μ)
      (dcomm g dg k dk B A μ) 0 := by
  have h0 : g + (0 : ℝ) • k = g := by simp
  have h0' : dg + (0 : ℝ) • dk = dg := by simp
  unfold commR dcomm
  refine HasDerivAt.fun_sum fun γ _ => ?_
  have h1 := (hasDerivAt_edot hg k B γ).fun_mul (hasDerivAt_dedot hg dg k dk γ A μ)
  have h2 := (hasDerivAt_edot hg k A γ).fun_mul (hasDerivAt_dedot hg dg k dk γ B μ)
  simp only [h0, h0'] at h1 h2
  exact h1.fun_sub h2

/-- **The frame commutator variation in the frame**:
`δ[e_B, e_A] = Σ_Dε_D(Λ_{BD}[e_D, e_A] + Λ_{AD}[e_B, e_D] + (e_B(Λ_{AD}) - e_A(Λ_{BD}))e_D)`. -/
theorem dcomm_decomp (dg : Fin 4 → Met) (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ) (k : Met)
    (dk : Fin 4 → Met) (B A μ : Fin 4) :
    dcomm g dg k dk B A μ = ∑ D, lorentzSign D * (Lam g k B D * commR (frR g) (deR g dg) D A μ +
      Lam g k A D * commR (frR g) (deR g dg) B D μ +
      (dLam g dg k dk B A D - dLam g dg k dk A B D) * frR g D μ) := by
  unfold dcomm
  simp only [edot_decomp hg, dedot_decomp hg dg hdg, dLam_eq hg, commR, Fin.sum_univ_four]
  ring

/-- **The variation of the structure coefficients**:
`δΩ_{BAC} = Σ_Dε_D(Ω_{BAD}k_{DC} + Λ_{BD}Ω_{DAC} + Λ_{AD}Ω_{BDC} + Ω_{BAD}Λ_{CD}) + e_B(Λ_{AC}) -
e_A(Λ_{BC})` (`GenDAlg.dOm`). -/
theorem hasDerivAt_OmR (dg : Fin 4 → Met) (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ) (k : Met)
    (dk : Fin 4 → Met) (B A C : Fin 4) :
    HasDerivAt (fun ε : ℝ => OmR (g + ε • k) (dg + ε • dk) B A C)
      (dOm lorentzSign (OmR g dg) (Lam g k) (kfr g k) (dLam g dg k dk) B A C) 0 := by
  have h0 : g + (0 : ℝ) • k = g := by simp
  have h0' : dg + (0 : ℝ) • dk = dg := by simp
  have h := hasDerivAt_ipg (g := fun s : ℝ => g + s • k)
    (X := fun s => commR (frR (g + s • k)) (deR (g + s • k) (dg + s • dk)) B A)
    (Y := fun s => frR (g + s • k) C) (t := 0) (dg := fun _ => k)
    (dX := fun _ μ => dcomm g dg k dk B A μ) (dY := fun _ μ => edot g k C μ) 0 (line_const hg k)
    (fun μ => hasDerivAt_commR hg dg k dk B A μ) (fun ν => hasDerivAt_edot hg k C ν)
  simp only [h0, h0'] at h
  refine h.congr_deriv ?_
  -- the three pieces
  have hc : ∀ μ, commR (frR g) (deR g dg) B A μ =
      ∑ D, lorentzSign D * OmR g dg B A D * frR g D μ := fun μ =>
    decomp_R hg (commR (frR g) (deR g dg) B A) μ
  have pa : ipg k (commR (frR g) (deR g dg) B A) (frR g C) =
      ∑ D, lorentzSign D * OmR g dg B A D * kfr g k D C := by
    have : commR (frR g) (deR g dg) B A = fun μ => ∑ D, (lorentzSign D * OmR g dg B A D) *
        frR g D μ := funext hc
    rw [this, ipg_sum_left]
    rfl
  have pb : ipg g (commR (frR g) (deR g dg) B A) (edot g k C) =
      ∑ D, lorentzSign D * Lam g k C D * OmR g dg B A D := by
    have : edot g k C = fun ν => ∑ D, (lorentzSign D * Lam g k C D) * frR g D ν :=
      funext (edot_decomp hg k C)
    rw [this, ipg_sum_right]
    rfl
  have pc : ipg g (fun μ => dcomm g dg k dk B A μ) (frR g C) =
      ∑ D, lorentzSign D * (Lam g k B D * OmR g dg D A C + Lam g k A D * OmR g dg B D C) +
        (dLam g dg k dk B A C - dLam g dg k dk A B C) := by
    have e1 : ipg g (fun μ => dcomm g dg k dk B A μ) (frR g C) =
        ∑ D, lorentzSign D * (Lam g k B D * OmR g dg D A C + Lam g k A D * OmR g dg B D C) +
        ∑ D, lorentzSign D * (dLam g dg k dk B A D - dLam g dg k dk A B D) *
          ipg g (frR g D) (frR g C) := by
      simp only [dcomm_decomp hg dg hdg, OmR, ipg, Fin.sum_univ_four]
      ring
    rw [e1]
    simp only [orth_R hg, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have : lorentzSign C * (dLam g dg k dk B A C - dLam g dg k dk A B C) * lorentzSign C =
        dLam g dg k dk B A C - dLam g dg k dk A B C := by
      have := ls_sq C
      linear_combination (dLam g dg k dk B A C - dLam g dg k dk A B C) * this
    rw [this]
  unfold dipg
  have hsplit : ∑ μ, ∑ ν, (k μ ν * commR (frR g) (deR g dg) B A μ * frR g C ν +
      g μ ν * dcomm g dg k dk B A μ * frR g C ν + g μ ν * commR (frR g) (deR g dg) B A μ *
        edot g k C ν) = ipg k (commR (frR g) (deR g dg) B A) (frR g C) +
      ipg g (fun μ => dcomm g dg k dk B A μ) (frR g C) +
      ipg g (commR (frR g) (deR g dg) B A) (edot g k C) := by
    simp only [ipg, ← Finset.sum_add_distrib]
  rw [hsplit, pa, pb, pc]
  unfold dOm
  have e : ∑ D, lorentzSign D * (OmR g dg B A D * kfr g k D C + Lam g k B D * OmR g dg D A C +
      Lam g k A D * OmR g dg B D C + OmR g dg B A D * Lam g k C D) =
      ∑ D, lorentzSign D * OmR g dg B A D * kfr g k D C +
      ∑ D, lorentzSign D * (Lam g k B D * OmR g dg D A C + Lam g k A D * OmR g dg B D C) +
      ∑ D, lorentzSign D * Lam g k C D * OmR g dg B A D := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun D _ => by ring
  rw [e]; ring

theorem contDiffAt_GR_line (dg : Fin 4 → Met) (k : Met) (dk : Fin 4 → Met) (B A C : Fin 4) :
    ContDiffAt ℝ ∞ (fun ε : ℝ => GR (g + ε • k) (dg + ε • dk) B A C) 0 := by
  have h1 : (Matrix.of (g + (0 : ℝ) • k)).det ≠ 0 := by simpa using hg.1
  have hgi : ContDiffAt ℝ ∞ (fun ε : ℝ => ginvOf (g + ε • k)) 0 :=
    ContDiffAt.ginvOf_fun (by fun_prop) h1
  have h2 : IsLorChart (ginvOf (g + (0 : ℝ) • k)) := by simpa using hg.2.1
  have hgi' : ∀ a b, ContDiffAt ℝ ∞ (fun ε : ℝ => ginvOf (g + ε • k) a b) 0 := fun a b =>
    contDiffAt_pi.1 (contDiffAt_pi.1 hgi a) b
  have hfr : ∀ a b, ContDiffAt ℝ ∞ (fun ε : ℝ => frR (g + ε • k) a b) 0 := fun a b =>
    ContDiffAt.frU_comp hgi h2 a b
  have hde : ∀ γ a b, ContDiffAt ℝ ∞ (fun ε : ℝ => deR (g + ε • k) (dg + ε • dk) γ a b) 0 :=
    fun γ a b => contDiffAt_deR_line hg dg k dk γ a b
  have hgg : ∀ a b, ContDiffAt ℝ ∞ (fun ε : ℝ => (g + ε • k) a b) 0 := fun a b => by fun_prop
  have hdgg : ∀ γ a b, ContDiffAt ℝ ∞ (fun ε : ℝ => (dg + ε • dk) γ a b) 0 := fun γ a b => by
    fun_prop
  unfold GR Gfun ipg cv1 chr
  fun_prop

theorem hasDerivAt_GR (dg : Fin 4 → Met) (k : Met) (dk : Fin 4 → Met) (B A C : Fin 4) :
    HasDerivAt (fun ε : ℝ => GR (g + ε • k) (dg + ε • dk) B A C) (Gdot g dg k dk B A C) 0 :=
  ((contDiffAt_GR_line hg dg k dk B A C).differentiableAt (by simp)).hasDerivAt

theorem eventually_dg (dg : Fin 4 → Met) (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ) (dk : Fin 4 → Met)
    (hdk : ∀ α μ ν, dk α μ ν = dk α ν μ) (ε : ℝ) :
    ∀ α μ ν, (dg + ε • dk) α μ ν = (dg + ε • dk) α ν μ := fun α μ ν => by
  simp [hdg α μ ν, hdk α μ ν]

/-- **The variation of the connection coefficients is the Koszul inversion of the variation of
the structure coefficients**: `δG = koszul(δΩ)`. -/
theorem Gdot_eq (dg : Fin 4 → Met) (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ) (k : Met)
    (hk : ∀ μ ν, k μ ν = k ν μ) (dk : Fin 4 → Met) (hdk : ∀ α μ ν, dk α μ ν = dk α ν μ)
    (B A C : Fin 4) :
    Gdot g dg k dk B A C =
      koszul (dOm lorentzSign (OmR g dg) (Lam g k) (kfr g k) (dLam g dg k dk)) B A C := by
  refine koszul_unique (fun B A C => ?_) (fun B A C => ?_) B A C
  · have h1 := hasDerivAt_GR hg dg k dk B C A
    have h2 := (hasDerivAt_GR hg dg k dk B A C).neg
    have hev : (fun ε : ℝ => GR (g + ε • k) (dg + ε • dk) B C A) =ᶠ[𝓝 0]
        fun ε => -GR (g + ε • k) (dg + ε • dk) B A C := by
      filter_upwards [eventually_chartM hg hk] with ε hε
      exact GR_anti hε _ (eventually_dg hg dg hdg dk hdk ε) B A C
    exact h1.unique (h2.congr_of_eventuallyEq hev)
  · have h1 := (hasDerivAt_GR hg dg k dk B A C).fun_sub (hasDerivAt_GR hg dg k dk A B C)
    have h2 := hasDerivAt_OmR hg dg hdg k dk B A C
    have hev : (fun ε : ℝ => GR (g + ε • k) (dg + ε • dk) B A C -
        GR (g + ε • k) (dg + ε • dk) A B C) = fun ε => OmR (g + ε • k) (dg + ε • dk) B A C :=
      funext fun ε => GR_tors _ _ (eventually_dg hg dg hdg dk hdk ε) B A C
    rw [hev] at h1
    exact h1.unique h2

end Line





end RenewalGeometry.GenDFJ
