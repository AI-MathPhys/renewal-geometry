/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedMatterEuler

/-!
# The first-derivative Einstein–Yang–Mills–Higgs action density `S^{(1)}`

Einstein–Standard-Model action-closure manuscript, `app:generated-dynamics`,
`eq:generated-comparison-action` ("`S^{(1)}` the complete first-derivative torsion-free
Einstein–Standard-Model action representative"), in the actual-jet variables
`(g_{μν}, A_μ ∈ gl(m), H)`:

* `HJ1` — the head 1-jets `(g, ∂g; A, ∂A; H, ∂H)` (a finite-dimensional normed space);
* **`L1SM`** — `(2κ)⁻¹ L1EH(g, ∂g) - (Λ/κ)√(-det g) + L_{YM} + L_H`: the `ΓΓ` (first-derivative)
  Einstein–Hilbert density with cosmological term and the Yang–Mills and Higgs densities;
  `contDiffOn_L1SM` — smooth on the Lorentzian chart `det g < 0`;
* `j1F` — the 1-jet of a triple of fields; `j1F_add_smul` — linearity;
* **`fderiv_L1SM_eq`** — the first variation of the density at the 1-jet of a smooth tuple along
  a smooth variation `(k, X, η)` splits into the gravitational part `(2κ)⁻¹DL1EH[k, ∂k]`, the
  cosmological and matter metric parts `-(Λ/κ)½√(-det g) tr_g k + ½√(-det g)T^{μν}k_{μν}`
  (Yang–Mills and Higgs stresses, `GenMatVar.hasDerivAt_LYM_metric`, `hasDerivAt_LHg_metric`)
  and the matter Euler rows minus the divergence of the matter flux
  (`GenMatEuler.matter_euler`).

Disclosed rendering: the Dirac sector carries no action term (decoupled spinors, as in
`lem:generated-physical-identification`; `SMData` has no spinor pairing, so no Dirac Lagrangian
is expressible); the gauge algebra is `gl(m)` with an invariant symmetric form, the Higgs sector
is the variational one of `GenStress.VariationalStress`.
-/

namespace RenewalGeometry

namespace GenFOAction

open HarmonicDefect EHJetVariation EHFieldVariation ActualJetSystem ActualJetRecon
  ActualJetSmooth ActualJetGauge SlabWaveHk ActualJetWriter ActualJetBridge ActualJetState
  GenMatVar GenNoether PeriodicCube GenFOGrav GenMatEuler
open SobolevOpen (pd)
open scoped ContDiff

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable (m V) in
/-- **The head 1-jets** `(g, ∂_αg; A, ∂_γA_μ; H, ∂_γH)`. -/
abbrev HJ1 := (Met × (Fin 4 → Met)) × ((Fin 4 → MatLie m) × (Fin 4 → Fin 4 → MatLie m)) ×
  (V × (Fin 4 → V))

/-- **The first-derivative Einstein–Yang–Mills–Higgs density** `S^{(1)}` on head 1-jets. -/
def L1SM (SM : SMData (MatLie m) V S S') (j : HJ1 m V) : ℝ :=
  (1 / (2 * SM.κ)) * L1EH j.1.1 j.1.2 - SM.Λ / SM.κ * volM j.1.1 +
    LYM SM j.1.1 j.2.1.1 j.2.1.2 + LHg SM j.1.1 j.2.1.1 j.2.2.1 j.2.2.2

variable (m V) in
/-- The Lorentzian chart of the 1-jets. -/
def chart1 : Set (HJ1 m V) := {j | (Matrix.of j.1.1).det < 0}

theorem isOpen_chart1 : IsOpen (chart1 m V) := by
  have hdet : Continuous fun j : HJ1 m V => (Matrix.of j.1.1).det :=
    Continuous.matrix_det (A := fun j : HJ1 m V => Matrix.of j.1.1)
      (continuous_fst.comp continuous_fst)
  exact isOpen_lt hdet continuous_const

/-- The volume density is smooth where `det g < 0`. -/
theorem contDiffAt_volM {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → Met} {x : E} (hg : ContDiffAt ℝ ∞ g x) (hdet : (Matrix.of (g x)).det < 0) :
    ContDiffAt ℝ ∞ (fun y => volM (g y)) x := by
  have hd : ContDiffAt ℝ ∞ (fun y => (Matrix.of (g y)).det) x := by
    simp only [Matrix.det_apply', Matrix.of_apply]
    fun_prop
  unfold volM
  exact hd.neg.sqrt (by linarith)

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}

theorem cd_chr {gi : E → Met} {dg : E → Fin 4 → Met}
    (hgi : ∀ a b, ContDiffAt ℝ ∞ (fun y => gi y a b) x)
    (hdg : ∀ α a b, ContDiffAt ℝ ∞ (fun y => dg y α a b) x) (l μ ν : Fin 4) :
    ContDiffAt ℝ ∞ (fun y => chr (gi y) (dg y) l μ ν) x := by
  unfold chr; fun_prop

theorem cd_dginv {gi : E → Met} {dg : E → Fin 4 → Met}
    (hgi : ∀ a b, ContDiffAt ℝ ∞ (fun y => gi y a b) x)
    (hdg : ∀ α a b, ContDiffAt ℝ ∞ (fun y => dg y α a b) x) (α l σ : Fin 4) :
    ContDiffAt ℝ ∞ (fun y => dginv (gi y) (dg y) α l σ) x := by
  unfold dginv; fun_prop

theorem cd_gamGam {gi : E → Met} {Γ : E → Fin 4 → Fin 4 → Fin 4 → ℝ}
    (hgi : ∀ a b, ContDiffAt ℝ ∞ (fun y => gi y a b) x)
    (hΓ : ∀ l μ ν, ContDiffAt ℝ ∞ (fun y => Γ y l μ ν) x) :
    ContDiffAt ℝ ∞ (fun y => gamGam (gi y) (Γ y)) x := by
  unfold gamGam; fun_prop

theorem cd_divLow {gi : E → Met} {dgi Γ : E → Fin 4 → Fin 4 → Fin 4 → ℝ}
    (hgi : ∀ a b, ContDiffAt ℝ ∞ (fun y => gi y a b) x)
    (hdgi : ∀ l μ ν, ContDiffAt ℝ ∞ (fun y => dgi y l μ ν) x)
    (hΓ : ∀ l μ ν, ContDiffAt ℝ ∞ (fun y => Γ y l μ ν) x) :
    ContDiffAt ℝ ∞ (fun y => divLow (gi y) (dgi y) (Γ y)) x := by
  unfold divLow fluxV; fun_prop

theorem cd_L1EH {g : E → Met} {dg : E → Fin 4 → Met} (hg : ContDiffAt ℝ ∞ g x)
    (hdg : ∀ α a b, ContDiffAt ℝ ∞ (fun y => dg y α a b) x) (hdet : (Matrix.of (g x)).det < 0) :
    ContDiffAt ℝ ∞ (fun y => L1EH (g y) (dg y)) x := by
  have hv := contDiffAt_volM hg hdet
  have hgi0 := ContDiffAt.ginvOf_fun hg hdet.ne
  have hgi : ∀ a b, ContDiffAt ℝ ∞ (fun y => ginvOf (g y) a b) x := fun a b =>
    contDiffAt_pi.1 (contDiffAt_pi.1 hgi0 a) b
  have hΓ := cd_chr hgi hdg
  have hdgi := cd_dginv hgi hdg
  have h1 := cd_gamGam hgi hΓ
  have h2 := cd_divLow hgi hdgi hΓ
  unfold L1EH L1EHJ
  exact hv.mul (h1.sub h2)

theorem cd_quadF (B : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ) {gi : E → Met}
    {F : E → Fin 4 → Fin 4 → MatLie m} (hgi : ∀ a b, ContDiffAt ℝ ∞ (fun y => gi y a b) x)
    (hF : ∀ a b, ContDiffAt ℝ ∞ (fun y => F y a b) x) :
    ContDiffAt ℝ ∞ (fun y => quadF B (gi y) (F y)) x := by
  unfold quadF
  have hB : ∀ a b c d, ContDiffAt ℝ ∞ (fun y => B (F y a b) (F y c d)) x := fun a b c d =>
    ContDiffAt.bilinApply B (hF a b) (hF c d)
  fun_prop

theorem cd_quadD (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {gi : E → Met} {D : E → Fin 4 → V}
    (hgi : ∀ a b, ContDiffAt ℝ ∞ (fun y => gi y a b) x)
    (hD : ∀ a, ContDiffAt ℝ ∞ (fun y => D y a) x) :
    ContDiffAt ℝ ∞ (fun y => quadD B (gi y) (D y)) x := by
  unfold quadD
  have hB : ∀ a b, ContDiffAt ℝ ∞ (fun y => B (D y a) (D y b)) x := fun a b =>
    ContDiffAt.bilinApply B (hD a) (hD b)
  fun_prop

end Smooth

/-- **`S^{(1)}` is smooth on the Lorentzian chart.** -/
theorem contDiffOn_L1SM (SM : SMData (MatLie m) V S S') :
    ContDiffOn ℝ ∞ (L1SM SM) (chart1 m V) := by
  intro j₀ hj
  have hj' : (Matrix.of j₀.1.1).det < 0 := hj
  refine ContDiffAt.contDiffWithinAt ?_
  have hg : ContDiffAt ℝ ∞ (fun j : HJ1 m V => j.1.1) j₀ := by fun_prop
  have hdg : ∀ α a b, ContDiffAt ℝ ∞ (fun j : HJ1 m V => j.1.2 α a b) j₀ := fun α a b => by
    fun_prop
  have hv := contDiffAt_volM hg hj'
  have hgi0 := ContDiffAt.ginvOf_fun hg hj'.ne
  have hgi : ∀ a b, ContDiffAt ℝ ∞ (fun j : HJ1 m V => ginvOf j.1.1 a b) j₀ := fun a b =>
    contDiffAt_pi.1 (contDiffAt_pi.1 hgi0 a) b
  have hEH := cd_L1EH hg hdg hj'
  have hF : ∀ a b, ContDiffAt ℝ ∞ (fun j : HJ1 m V => Fm j.2.1.1 j.2.1.2 a b) j₀ := fun a b => by
    unfold Fm fieldStrength
    have h1 : ContDiffAt ℝ ∞ (fun j : HJ1 m V => j.2.1.1 a) j₀ := by fun_prop
    have h2 : ContDiffAt ℝ ∞ (fun j : HJ1 m V => j.2.1.1 b) j₀ := by fun_prop
    exact ((by fun_prop : ContDiffAt ℝ ∞ (fun j : HJ1 m V => j.2.1.2 a b) j₀).sub
      (by fun_prop : ContDiffAt ℝ ∞ (fun j : HJ1 m V => j.2.1.2 b a) j₀)).add
      (ContDiffAt.lie_mat h1 h2)
  have hD : ∀ a, ContDiffAt ℝ ∞ (fun j : HJ1 m V =>
      ActualJetGauge.DH j.2.1.1 j.2.2.1 j.2.2.2 a) j₀ := fun a => by
    unfold ActualJetGauge.DH
    have h1 : ContDiffAt ℝ ∞ (fun j : HJ1 m V => j.2.1.1 a) j₀ := by fun_prop
    have h2 : ContDiffAt ℝ ∞ (fun j : HJ1 m V => j.2.2.1) j₀ := by fun_prop
    exact (by fun_prop : ContDiffAt ℝ ∞ (fun j : HJ1 m V => j.2.2.2 a) j₀).add
      (ContDiffAt.lie_mod h1 h2)
  have hYM := cd_quadF SM.ipG hgi hF
  have hHg := cd_quadD SM.ipV hgi hD
  have hHH : ContDiffAt ℝ ∞ (fun j : HJ1 m V => SM.ipV j.2.2.1 j.2.2.1) j₀ :=
    ContDiffAt.bilinApply SM.ipV (by fun_prop) (by fun_prop)
  unfold L1SM LYM LHg
  exact (((contDiffAt_const.mul hEH).sub (contDiffAt_const.mul hv)).add
    ((contDiffAt_const.mul hv).mul hYM)).add
    ((hv.mul (hHg.add (contDiffAt_const.mul ((hHH.sub contDiffAt_const).pow 2)))).neg)

/-! ### Jets of fields -/

/-- The 1-jet of a triple of fields. -/
def j1F (g : ST 3 → Met) (A : ST 3 → Fin 4 → MatLie m) (H : ST 3 → V) (x : ST 3) : HJ1 m V :=
  ((g x, fun α => pd g α x), (A x, fun γ μ => pd A γ x μ), (H x, fun γ => pd H γ x))

theorem continuous_j1F {g : ST 3 → Met} {A : ST 3 → Fin 4 → MatLie m} {H : ST 3 → V}
    (hg : ContDiff ℝ ∞ g) (hA : ContDiff ℝ ∞ A) (hH : ContDiff ℝ ∞ H) :
    Continuous (j1F g A H) := by
  have h1 : ∀ α, Continuous (pd g α) := fun α => (contDiff_pd hg α).continuous
  have h2 : ∀ γ, Continuous (pd A γ) := fun γ => (contDiff_pd hA γ).continuous
  have h3 : ∀ γ, Continuous (pd H γ) := fun γ => (contDiff_pd hH γ).continuous
  unfold j1F
  refine (hg.continuous.prodMk (continuous_pi h1)).prodMk
    ((hA.continuous.prodMk (continuous_pi fun γ => continuous_pi fun μ =>
      (continuous_apply μ).comp (h2 γ))).prodMk (hH.continuous.prodMk (continuous_pi h3)))

theorem pd_add_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f k : ST 3 → E}
    {x : ST 3} (hf : DifferentiableAt ℝ f x) (hk : DifferentiableAt ℝ k x) (ε : ℝ) (μ : Fin 4) :
    pd (fun y => f y + ε • k y) μ x = pd f μ x + ε • pd k μ x := by
  unfold SobolevOpen.pd
  have hk' : DifferentiableAt ℝ (fun y => ε • k y) x := hk.const_smul ε
  rw [fderiv_fun_add hf hk', fderiv_fun_const_smul hk]
  rfl

/-- **Linearity of the 1-jet.** -/
theorem j1F_add_smul {g k : ST 3 → Met} {A X : ST 3 → Fin 4 → MatLie m} {H η : ST 3 → V}
    (hg : ContDiff ℝ ∞ g) (hk : ContDiff ℝ ∞ k) (hA : ContDiff ℝ ∞ A) (hX : ContDiff ℝ ∞ X)
    (hH : ContDiff ℝ ∞ H) (hη : ContDiff ℝ ∞ η) (ε : ℝ) (x : ST 3) :
    j1F (fun y => g y + ε • k y) (fun y => A y + ε • X y) (fun y => H y + ε • η y) x =
      j1F g A H x + ε • j1F k X η x := by
  have dg := hg.differentiable (by simp) x
  have dk := hk.differentiable (by simp) x
  have dA := hA.differentiable (by simp) x
  have dX := hX.differentiable (by simp) x
  have dH := hH.differentiable (by simp) x
  have dη := hη.differentiable (by simp) x
  unfold j1F
  simp only [pd_add_smul dg dk, pd_add_smul dA dX, pd_add_smul dH dη]
  rfl

/-! ### The first variation of `S^{(1)}` at a smooth tuple -/

/-- The first-derivative Einstein–Hilbert density as a function on metric 1-jets. -/
def L1EHp (p : Met × (Fin 4 → Met)) : ℝ := L1EH p.1 p.2

theorem differentiableAt_L1EHp {p : Met × (Fin 4 → Met)} (hp : (Matrix.of p.1).det < 0) :
    DifferentiableAt ℝ L1EHp p := by
  have h := cd_L1EH (E := Met × (Fin 4 → Met)) (x := p) (g := fun q => q.1) (dg := fun q => q.2)
    (by fun_prop) (fun α a b => by fun_prop) hp
  exact h.differentiableAt (by simp)

theorem differentiableAt_L1SM (SM : SMData (MatLie m) V S S') {j : HJ1 m V}
    (hj : (Matrix.of j.1.1).det < 0) : DifferentiableAt ℝ (L1SM SM) j :=
  ((contDiffOn_L1SM SM).contDiffAt (isOpen_chart1.mem_nhds hj)).differentiableAt (by simp)

set_option maxHeartbeats 4000000 in
/-- **The first variation of `S^{(1)}` at the 1-jet of a smooth tuple** (variational data):
gravitational part, cosmological and matter-stress metric parts, and the matter Euler rows minus
the divergence of the matter flux. -/
theorem fderiv_L1SM_eq (SM : SMData (MatLie m) V S S') (hV : GenStress.VariationalStress SM)
    (z : Tuple m V S S') {k : ST 3 → Met} (hk : ContDiff ℝ ∞ k) (hks : ∀ y μ ν, k y μ ν = k y ν μ)
    {X : ST 3 → Fin 4 → MatLie m} (hX : ContDiff ℝ ∞ X) {η : ST 3 → V} (hη : ContDiff ℝ ∞ η)
    (x : ST 3) :
    fderiv ℝ (L1SM SM) (j1F z.g z.A z.H x) (j1F k X η x) =
      (1 / (2 * SM.κ)) * fderiv ℝ L1EHp (z.g x, fun α => pd z.g α x) (k x, fun α => pd k α x) -
      SM.Λ / SM.κ * ((1 / 2) * volM (z.g x) * trG (ginvOf (z.g x)) (k x)) +
      ((1 / 2) * volM (z.g x) * ∑ μ, ∑ ν, up (ginvOf (z.g x))
        (ymStressB SM.ipG (z.g x) (ginvOf (z.g x)) (Fm (z.A x) (fun γ μ => pd z.A γ x μ))) μ ν *
          k x μ ν +
       (1 / 2) * volM (z.g x) * ∑ μ, ∑ ν, up (ginvOf (z.g x))
        (higgsStressB SM.ipV SM.lamH SM.vH (z.g x) (ginvOf (z.g x)) (z.H x)
          (ActualJetGauge.DH (z.A x) (z.H x) (fun γ => pd z.H γ x))) μ ν * k x μ ν) +
      (∑ δ, SM.ipG (densR SM z x δ) (X x δ) + 2 * rho z x * SM.ipV ((bosF SM z x).2.2) (η x) -
        ∑ γ, pd (matFlux z SM X η γ) γ x) := by
  set j := j1F z.g z.A z.H x with hj
  have hdet : (Matrix.of (z.g x)).det < 0 := GenCell.Tuple_det_neg z x
  have hsym : ∀ μ ν, z.g x μ ν = z.g x ν μ := z.g_symm x
  set vG : HJ1 m V := ((k x, fun α => pd k α x), (0, 0), (0, 0)) with hvG
  set vM : HJ1 m V := ((0, 0), (X x, fun γ μ => pd X γ x μ), (η x, fun γ => pd η γ x)) with hvM
  have hsplit : j1F k X η x = vG + vM := by
    simp only [j1F, hvG, hvM, Prod.mk_add_mk, add_zero, zero_add]
  have hL := differentiableAt_L1SM SM (j := j) hdet
  rw [hsplit, map_add]
  have hline : ∀ v : HJ1 m V, HasDerivAt (fun ε : ℝ => L1SM SM (j + ε • v))
      (fderiv ℝ (L1SM SM) j v) 0 := fun v => by
    have hl : HasDerivAt (fun ε : ℝ => j + ε • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add j
    exact hL.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  -- the metric direction
  have hG : HasDerivAt (fun ε : ℝ => L1SM SM (j + ε • vG))
      ((1 / (2 * SM.κ)) * fderiv ℝ L1EHp (z.g x, fun α => pd z.g α x) (k x, fun α => pd k α x) -
        SM.Λ / SM.κ * ((1 / 2) * volM (z.g x) * trG (ginvOf (z.g x)) (k x)) +
        (1 / 2) * volM (z.g x) * ∑ μ, ∑ ν, up (ginvOf (z.g x))
          (ymStressB SM.ipG (z.g x) (ginvOf (z.g x)) (Fm (z.A x) (fun γ μ => pd z.A γ x μ))) μ ν *
            k x μ ν +
        (1 / 2) * volM (z.g x) * ∑ μ, ∑ ν, up (ginvOf (z.g x))
          (higgsStressB SM.ipV SM.lamH SM.vH (z.g x) (ginvOf (z.g x)) (z.H x)
            (ActualJetGauge.DH (z.A x) (z.H x) (fun γ => pd z.H γ x))) μ ν * k x μ ν) 0 := by
    have h1 : HasDerivAt (fun ε : ℝ => L1EHp ((z.g x, fun α => pd z.g α x) +
        ε • (k x, fun α => pd k α x)))
        (fderiv ℝ L1EHp (z.g x, fun α => pd z.g α x) (k x, fun α => pd k α x)) 0 := by
      have hl : HasDerivAt (fun ε : ℝ => (z.g x, fun α => pd z.g α x) +
          ε • (k x, fun α => pd k α x)) (k x, fun α => pd k α x) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (k x, fun α => pd k α x)).const_add
          (z.g x, fun α => pd z.g α x)
      exact (differentiableAt_L1EHp (p := (z.g x, fun α => pd z.g α x)) hdet).hasFDerivAt
        |>.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
    have h2 := hasDerivAt_vol_line (g := z.g x) (k := k x) hdet hsym
    have h3 := hasDerivAt_LYM_metric (g := z.g x) (k := k x) SM hV.ipG_symm hsym hdet (z.A x)
      (fun γ μ => pd z.A γ x μ)
    have h4 := hasDerivAt_LHg_metric (g := z.g x) (k := k x) SM hsym hdet (z.A x) (z.H x)
      (fun γ => pd z.H γ x)
    have h := (((h1.const_mul (1 / (2 * SM.κ))).sub (h2.const_mul (SM.Λ / SM.κ))).add h3).add h4
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ε => ?_)
    simp only [L1SM, L1EHp, hj, hvG, j1F, Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero]
    rfl
  -- the matter directions
  have hM : HasDerivAt (fun ε : ℝ => L1SM SM (j + ε • vM))
      (∑ δ, SM.ipG (densR SM z x δ) (X x δ) + 2 * rho z x * SM.ipV ((bosF SM z x).2.2) (η x) -
        ∑ γ, pd (matFlux z SM X η γ) γ x) 0 := by
    have h3 := hasDerivAt_LYM_gauge SM hV.ipG_symm hV.ipG_inv hsym (z.A x) (X x)
      (fun γ μ => pd z.A γ x μ) (fun γ μ => pd X γ x μ)
    have h4 := hasDerivAt_LHg_AH SM hV hsym (z.A x) (X x) (z.H x) (η x)
      (fun γ => pd z.H γ x) (fun γ => pd η γ x)
    have h := ((hasDerivAt_const (0 : ℝ) ((1 / (2 * SM.κ)) * L1EH (z.g x) (fun α => pd z.g α x) -
      SM.Λ / SM.κ * volM (z.g x))).add h3).add h4
    rw [← matter_euler z SM hV hX hη x]
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ε => ?_)).congr_deriv ?_
    · simp only [L1SM, hj, hvM, j1F, Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero]
      rfl
    · ring
  rw [hline vG |>.unique hG, hline vM |>.unique hM]
  ring

end

end GenFOAction

end RenewalGeometry
