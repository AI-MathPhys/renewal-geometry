/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedFirstOrderGravity
import RenewalGeometry.Continuum.GeneratedStressNoether

/-!
# The first-derivative Yang–Mills–Higgs densities and their metric variation

Einstein–Standard-Model action-closure manuscript, `app:generated-dynamics`
(`eq:generated-comparison-action`), matter sector of the first-derivative action `S^{(1)}` in the
actual-jet variables `(g, A, H)` (`gl(m)` potential, Higgs field):

* `LYM` — `-¼ √(-det g) g^{αγ}g^{βδ}⟨F_{αβ}, F_{γδ}⟩`, `F = ∂A - ∂A + [A, A]`;
* `LHg` — `-√(-det g)(g^{αβ}⟨D_αH, D_βH⟩ + λ(⟨H, H⟩ - v²)²)`;
* `up gi X` — `X^{μν} = g^{μa}g^{νb}X_{ab}`;
* **`hasDerivAt_LYM_metric`**, **`hasDerivAt_LHg_metric`** — the metric variations are the
  Yang–Mills and Higgs stresses of `prop:actual-jet-writer`:
  `d/dε L(g + εk) = ½√(-det g) T^{μν}k_{μν}` with `T = ymStressB`, `higgsStressB`.
-/

namespace RenewalGeometry

namespace GenMatVar

open Finset HarmonicDefect EHJetVariation EHFieldVariation ActualJetSystem ActualJetRecon ActualJetSmooth
  ActualJetGauge SlabWaveHk ActualJetWriter
open SobolevOpen (pd)
open scoped ContDiff

noncomputable section

set_option linter.unusedSectionVars false

/-! ### Contractions -/

/-- `X^{μν} = g^{μa}g^{νb}X_{ab}`. -/
def up (gi X : Fin 4 → Fin 4 → ℝ) (μ ν : Fin 4) : ℝ := ∑ a, ∑ b, gi μ a * gi ν b * X a b

/-- The quadratic form `Σ g^{αγ}g^{βδ}B(F_{αβ}, F_{γδ})`. -/
def quadF {𝔤 : Type*} [AddCommGroup 𝔤] [Module ℝ 𝔤] (B : 𝔤 →ₗ[ℝ] 𝔤 →ₗ[ℝ] ℝ)
    (gi : Fin 4 → Fin 4 → ℝ) (F : Fin 4 → Fin 4 → 𝔤) : ℝ :=
  ∑ α, ∑ β, ∑ γ, ∑ δ, gi α γ * gi β δ * B (F α β) (F γ δ)

/-- The quadratic form `Σ g^{αβ}B(D_α, D_β)`. -/
def quadD {W : Type*} [AddCommGroup W] [Module ℝ W] (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (gi : Fin 4 → Fin 4 → ℝ) (D : Fin 4 → W) : ℝ :=
  ∑ α, ∑ β, gi α β * B (D α) (D β)

/-! ### The densities -/

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

/-- **The Yang–Mills density** `-¼ √(-det g) g^{αγ}g^{βδ}⟨F_{αβ}, F_{γδ}⟩`. -/
def LYM (SM : SMData (MatLie m) V S S') (g : Fin 4 → Fin 4 → ℝ) (A : Fin 4 → MatLie m)
    (dA : Fin 4 → Fin 4 → MatLie m) : ℝ :=
  -(1 / 4) * volM g * quadF SM.ipG (ginvOf g) (Fm A dA)

/-- **The Higgs density** `-√(-det g)(g^{αβ}⟨D_αH, D_βH⟩ + λ(⟨H, H⟩ - v²)²)`. -/
def LHg (SM : SMData (MatLie m) V S S') (g : Fin 4 → Fin 4 → ℝ) (A : Fin 4 → MatLie m) (H : V)
    (dH : Fin 4 → V) : ℝ :=
  -(volM g * (quadD SM.ipV (ginvOf g) (ActualJetGauge.DH A H dH) +
    SM.lamH * (SM.ipV H H - SM.vH ^ 2) ^ 2))

/-! ### Metric variation -/

section MetricVariation

variable {g k : Fin 4 → Fin 4 → ℝ}

theorem hasDerivAt_gi_line (hdet : (Matrix.of g).det ≠ 0) (a b : Fin 4) :
    HasDerivAt (fun ε : ℝ => ginvOf (g + ε • k) a b) (ginvVar (ginvOf g) k a b) 0 := by
  have hG : ∀ μ ν, HasDerivAt (fun ε : ℝ => (g + ε • k) μ ν) (k μ ν) 0 := fun μ ν => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (k μ ν)).const_add (g μ ν)
  have h := JetCurve.hasDerivAt_ginvOf (g := fun ε : ℝ => g + ε • k) (t := 0)
    (dg := fun _ => k) 0 (fun μ ν => hG μ ν) (by simpa using hdet) a b
  simp only [zero_smul, add_zero] at h
  refine h.congr_deriv ?_
  unfold dginv ginvVar
  rfl

theorem hasDerivAt_vol_line (hdet : (Matrix.of g).det < 0) (hsym : ∀ μ ν, g μ ν = g ν μ) :
    HasDerivAt (fun ε : ℝ => volM (g + ε • k)) ((1 / 2) * volM g * trG (ginvOf g) k) 0 := by
  have hG : ∀ μ ν, HasDerivAt (fun ε : ℝ => (g + ε • k) μ ν) (k μ ν) 0 := fun μ ν => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (k μ ν)).const_add (g μ ν)
  have h := hasDerivAt_volM_curve (G := fun ε : ℝ => g + ε • k) (k := k) (t := 0) hG
    (by simpa using hdet) (by simpa using hsym)
  simpa using h

theorem hasDerivAt_quadF_line {𝔤 : Type*} [AddCommGroup 𝔤] [Module ℝ 𝔤]
    (B : 𝔤 →ₗ[ℝ] 𝔤 →ₗ[ℝ] ℝ) (F : Fin 4 → Fin 4 → 𝔤) (hdet : (Matrix.of g).det ≠ 0) :
    HasDerivAt (fun ε : ℝ => quadF B (ginvOf (g + ε • k)) F)
      (∑ α, ∑ β, ∑ γ, ∑ δ, (ginvVar (ginvOf g) k α γ * ginvOf g β δ +
        ginvOf g α γ * ginvVar (ginvOf g) k β δ) * B (F α β) (F γ δ)) 0 := by
  unfold quadF
  refine HasDerivAt.fun_sum fun α _ => HasDerivAt.fun_sum fun β _ =>
    HasDerivAt.fun_sum fun γ _ => HasDerivAt.fun_sum fun δ _ => ?_
  have h := ((hasDerivAt_gi_line (k := k) hdet α γ).fun_mul
    (hasDerivAt_gi_line (k := k) hdet β δ)).mul_const (B (F α β) (F γ δ))
  simpa using h

theorem hasDerivAt_quadD_line {W : Type*} [AddCommGroup W] [Module ℝ W]
    (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (D : Fin 4 → W) (hdet : (Matrix.of g).det ≠ 0) :
    HasDerivAt (fun ε : ℝ => quadD B (ginvOf (g + ε • k)) D)
      (∑ α, ∑ β, ginvVar (ginvOf g) k α β * B (D α) (D β)) 0 := by
  unfold quadD
  refine HasDerivAt.fun_sum fun α _ => HasDerivAt.fun_sum fun β _ => ?_
  exact (hasDerivAt_gi_line (k := k) hdet α β).mul_const _

/-- The symmetry of the varied quadratic form in the two inverse-metric slots. -/
theorem quadF_var_symm {𝔤 : Type*} [AddCommGroup 𝔤] [Module ℝ 𝔤] (B : 𝔤 →ₗ[ℝ] 𝔤 →ₗ[ℝ] ℝ)
    (F : Fin 4 → Fin 4 → 𝔤) (hF : ∀ a b, F b a = -F a b) (gi gi' : Fin 4 → Fin 4 → ℝ) :
    ∑ α, ∑ β, ∑ γ, ∑ δ, (gi' α γ * gi β δ + gi α γ * gi' β δ) * B (F α β) (F γ δ) =
      2 * ∑ α, ∑ β, ∑ γ, ∑ δ, gi' α γ * gi β δ * B (F α β) (F γ δ) := by
  have e : ∑ α, ∑ β, ∑ γ, ∑ δ, gi α γ * gi' β δ * B (F α β) (F γ δ) =
      ∑ α, ∑ β, ∑ γ, ∑ δ, gi' α γ * gi β δ * B (F α β) (F γ δ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun δ _ => Finset.sum_congr rfl fun γ _ => ?_
    have h1 := hF α β
    have h2 := hF γ δ
    simp only [h1, h2, map_neg, LinearMap.neg_apply, neg_neg]
    ring
  simp only [add_mul, Finset.sum_add_distrib]
  rw [e]
  ring

end MetricVariation

/-! ### Bilinear calculus -/

section Bilin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A bilinear form on a finite-dimensional space as a continuous bilinear map. -/
def bilinCLM (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).toLinearMap ∘ₗ B)

theorem bilinCLM_apply (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (u v : E) : bilinCLM B u v = B u v := rfl

/-- **Product rule for a bilinear form along curves.** -/
theorem hasDerivAt_bilin (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) {u v : ℝ → E} {u' v' : E} {t : ℝ}
    (hu : HasDerivAt u u' t) (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => B (u s) (v s)) (B u' (v t) + B (u t) v') t := by
  have h1 : HasDerivAt (fun s => bilinCLM B (u s)) (bilinCLM B u') t :=
    (bilinCLM B).hasFDerivAt.comp_hasDerivAt t hu
  have h := h1.clm_apply hv
  simpa [bilinCLM_apply, add_comm] using h

/-- **Product rule for a bilinear form along fields** (coordinate derivatives). -/
theorem pd_bilin (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) {u v : ST 3 → E} {x : ST 3}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) (μ : Fin 4) :
    pd (fun y => B (u y) (v y)) μ x = B (pd u μ x) (v x) + B (u x) (pd v μ x) := by
  have hd : DifferentiableAt ℝ (fun y => B (u y) (v y)) x := by
    have : (fun y => B (u y) (v y)) = fun y => bilinCLM B (u y) (v y) := rfl
    rw [this]
    exact ((bilinCLM B).differentiableAt.comp x hu).clm_apply hv
  refine ActualJetBridge.pd_eq_of_line hd ?_
  have hu' := ActualJetBridge.hasDerivAt_line0 hu μ
  have hv' := ActualJetBridge.hasDerivAt_line0 hv μ
  simpa using hasDerivAt_bilin B hu' hv'

end Bilin

/-! ### Gauge and Higgs variations at the jet level -/

section JetVariation

variable {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A bilinear map on finite-dimensional spaces as a continuous bilinear map. -/
def bilinCLM' (B : E →ₗ[ℝ] E' →ₗ[ℝ] F) : E →L[ℝ] E' →L[ℝ] F :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (E' →ₗ[ℝ] F) ≃ₗ[ℝ] (E' →L[ℝ] F)).toLinearMap ∘ₗ B)

/-- **Product rule for a vector-valued bilinear map along curves.** -/
theorem hasDerivAt_bilin' (B : E →ₗ[ℝ] E' →ₗ[ℝ] F) {u : ℝ → E} {v : ℝ → E'} {u' : E} {v' : E'}
    {t : ℝ} (hu : HasDerivAt u u' t) (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => B (u s) (v s)) (B u' (v t) + B (u t) v') t := by
  have h1 : HasDerivAt (fun s => bilinCLM' B (u s)) (bilinCLM' B u') t :=
    (bilinCLM' B).hasFDerivAt.comp_hasDerivAt t hu
  have h := h1.clm_apply hv
  have e : (fun s => B (u s) (v s)) = fun s => bilinCLM' B (u s) (v s) := rfl
  rw [e]
  exact h

theorem hasDerivAt_affine (c w : E) : HasDerivAt (fun ε : ℝ => c + ε • w) w 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add c

end JetVariation

section GaugeJet

/-- The Lie bracket of `gl(m)` as a bilinear map. -/
def lieB (m : ℕ) : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] MatLie m :=
  LinearMap.mk₂ ℝ (fun a b : MatLie m => ⁅a, b⁆) add_lie smul_lie lie_add lie_smul

/-- The variation of the field strength. -/
def dFvar (A X : Fin 4 → MatLie m) (dX : Fin 4 → Fin 4 → MatLie m) (α β : Fin 4) : MatLie m :=
  dX α β - dX β α + ⁅X α, A β⁆ + ⁅A α, X β⁆

theorem hasDerivAt_Fm_line (A X : Fin 4 → MatLie m) (dA dX : Fin 4 → Fin 4 → MatLie m)
    (α β : Fin 4) :
    HasDerivAt (fun ε : ℝ => Fm (A + ε • X) (dA + ε • dX) α β) (dFvar A X dX α β) 0 := by
  have h1 := hasDerivAt_affine (dA α β) (dX α β)
  have h2 := hasDerivAt_affine (dA β α) (dX β α)
  have h3 := hasDerivAt_bilin' (lieB m) (hasDerivAt_affine (A α) (X α))
    (hasDerivAt_affine (A β) (X β))
  have h := (h1.sub h2).add h3
  unfold Fm fieldStrength dFvar
  simp only [Pi.add_apply, Pi.smul_apply, zero_smul, add_zero] at h ⊢
  refine h.congr_deriv ?_
  simp only [lieB, LinearMap.mk₂_apply]
  abel

/-- The Yang–Mills jet density `ϱ g^{γα}g^{δβ}F_{αβ}`. -/
def DnJ (v : ℝ) (gi : Fin 4 → Fin 4 → ℝ) (F : Fin 4 → Fin 4 → MatLie m) (γ δ : Fin 4) :
    MatLie m :=
  v • ∑ α, ∑ β, (gi γ α * gi δ β) • F α β

theorem DnJ_anti (v : ℝ) (gi : Fin 4 → Fin 4 → ℝ) {F : Fin 4 → Fin 4 → MatLie m}
    (hF : ∀ a b, F b a = -F a b) (γ δ : Fin 4) : DnJ v gi F δ γ = -DnJ v gi F γ δ := by
  unfold DnJ
  rw [Finset.sum_comm, ← smul_neg]
  congr 1
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [hF α β, smul_neg, neg_neg, mul_comm]

/-- `B(Dn_{γδ}, Y) = v Σ g^{γα}g^{δβ}B(F_{αβ}, Y)`. -/
theorem ipG_DnJ (B : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ) (v : ℝ) (gi : Fin 4 → Fin 4 → ℝ)
    (F : Fin 4 → Fin 4 → MatLie m) (γ δ : Fin 4) (Y : MatLie m) :
    B (DnJ v gi F γ δ) Y = v * ∑ α, ∑ β, gi γ α * gi δ β * B (F α β) Y := by
  unfold DnJ
  simp only [map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul]

end GaugeJet

section GaugeVar

/-- `Σ_{γδ} B(Dn_{γδ}, Y_{δγ}) = -Σ_{γδ} B(Dn_{γδ}, Y_{γδ})`. -/
theorem sum_DnJ_swap (B : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ) (v : ℝ) (gi : Fin 4 → Fin 4 → ℝ)
    {F : Fin 4 → Fin 4 → MatLie m} (hF : ∀ a b, F b a = -F a b) (Y : Fin 4 → Fin 4 → MatLie m) :
    ∑ γ, ∑ δ, B (DnJ v gi F γ δ) (Y δ γ) = -∑ γ, ∑ δ, B (DnJ v gi F γ δ) (Y γ δ) := by
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [DnJ_anti v gi hF γ δ, map_neg, LinearMap.neg_apply, neg_neg]

/-- **The gauge variation of the Yang–Mills density** (jet level):
`d/dε LYM(A + εX, ∂A + ε∂X) = -Σ⟨𝔉^{γδ}, ∂_γX_δ⟩ + Σ⟨[A_γ, 𝔉^{γδ}], X_δ⟩`,
`𝔉 = √(-det g) g g F`. -/
theorem hasDerivAt_LYM_gauge (SM : SMData (MatLie m) V S S')
    (hG : ∀ X Y : MatLie m, SM.ipG X Y = SM.ipG Y X)
    (hI : ∀ X Y Z : MatLie m, SM.ipG ⁅X, Y⁆ Z + SM.ipG Y ⁅X, Z⁆ = 0)
    {g : Fin 4 → Fin 4 → ℝ} (hsym : ∀ μ ν, g μ ν = g ν μ) (A X : Fin 4 → MatLie m)
    (dA dX : Fin 4 → Fin 4 → MatLie m) :
    HasDerivAt (fun ε : ℝ => LYM SM g (A + ε • X) (dA + ε • dX))
      (-∑ γ, ∑ δ, SM.ipG (DnJ (volM g) (ginvOf g) (Fm A dA) γ δ) (dX γ δ) +
        ∑ γ, ∑ δ, SM.ipG ⁅A γ, DnJ (volM g) (ginvOf g) (Fm A dA) γ δ⁆ (X δ)) 0 := by
  set gi := ginvOf g with hgi
  have hgs : ∀ a b, gi a b = gi b a := ginvOf_symm' hsym
  set F := Fm A dA with hFdef
  have hFa : ∀ a b, F b a = -F a b := fun a b => Fm_anti A dA a b
  set δF := dFvar A X dX with hδF
  have hq : HasDerivAt (fun ε : ℝ => quadF SM.ipG gi (Fm (A + ε • X) (dA + ε • dX)))
      (∑ α, ∑ β, ∑ γ, ∑ δ, gi α γ * gi β δ *
        (SM.ipG (δF α β) (F γ δ) + SM.ipG (F α β) (δF γ δ))) 0 := by
    unfold quadF
    refine HasDerivAt.fun_sum fun α _ => HasDerivAt.fun_sum fun β _ =>
      HasDerivAt.fun_sum fun γ _ => HasDerivAt.fun_sum fun δ _ => ?_
    have h := hasDerivAt_bilin SM.ipG (hasDerivAt_Fm_line A X dA dX α β)
      (hasDerivAt_Fm_line A X dA dX γ δ)
    simp only [zero_smul, add_zero] at h
    exact h.const_mul _
  have h := hq.const_mul (-(1 / 4) * volM g)
  unfold LYM
  refine h.congr_deriv ?_
  -- symmetrize
  have e1 : ∑ α, ∑ β, ∑ γ, ∑ δ, gi α γ * gi β δ *
      (SM.ipG (δF α β) (F γ δ) + SM.ipG (F α β) (δF γ δ)) =
      2 * ∑ γ, ∑ δ, ∑ α, ∑ β, gi γ α * gi δ β * SM.ipG (F α β) (δF γ δ) := by
    have h1 : ∑ α, ∑ β, ∑ γ, ∑ δ, gi α γ * gi β δ * SM.ipG (δF α β) (F γ δ) =
        ∑ γ, ∑ δ, ∑ α, ∑ β, gi γ α * gi δ β * SM.ipG (F α β) (δF γ δ) := by
      refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
        Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => ?_
      rw [hG]
    have h2 : ∑ α, ∑ β, ∑ γ, ∑ δ, gi α γ * gi β δ * SM.ipG (F α β) (δF γ δ) =
        ∑ γ, ∑ δ, ∑ α, ∑ β, gi γ α * gi δ β * SM.ipG (F α β) (δF γ δ) := by
      rw [GenNoether.sum4_swap]
      refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ =>
        Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
      rw [hgs α γ, hgs β δ]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [h1, h2]
    ring
  -- the density
  have e2 : volM g * ∑ γ, ∑ δ, ∑ α, ∑ β, gi γ α * gi δ β * SM.ipG (F α β) (δF γ δ) =
      ∑ γ, ∑ δ, SM.ipG (DnJ (volM g) gi F γ δ) (δF γ δ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [ipG_DnJ]
  -- the four terms of `δF`
  have e3 : ∑ γ, ∑ δ, SM.ipG (DnJ (volM g) gi F γ δ) (δF γ δ) =
      2 * ∑ γ, ∑ δ, SM.ipG (DnJ (volM g) gi F γ δ) (dX γ δ) +
      2 * ∑ γ, ∑ δ, SM.ipG (DnJ (volM g) gi F γ δ) ⁅A γ, X δ⁆ := by
    have hsplit : ∀ γ δ, SM.ipG (DnJ (volM g) gi F γ δ) (δF γ δ) =
        SM.ipG (DnJ (volM g) gi F γ δ) (dX γ δ) - SM.ipG (DnJ (volM g) gi F γ δ) (dX δ γ) +
        SM.ipG (DnJ (volM g) gi F γ δ) (-⁅A δ, X γ⁆) +
        SM.ipG (DnJ (volM g) gi F γ δ) ⁅A γ, X δ⁆ := by
      intro γ δ
      simp only [hδF, dFvar, map_add, map_sub]
      rw [← lie_skew]
    simp only [hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [sum_DnJ_swap SM.ipG (volM g) gi hFa dX]
    have h4 := sum_DnJ_swap SM.ipG (volM g) gi hFa (fun a b => -⁅A a, X b⁆)
    beta_reduce at h4
    rw [h4]
    simp only [map_neg, Finset.sum_neg_distrib, neg_neg]
    ring
  -- invariance
  have e4 : ∑ γ, ∑ δ, SM.ipG (DnJ (volM g) gi F γ δ) ⁅A γ, X δ⁆ =
      -∑ γ, ∑ δ, SM.ipG ⁅A γ, DnJ (volM g) gi F γ δ⁆ (X δ) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun δ _ => ?_
    have := hI (A γ) (DnJ (volM g) gi F γ δ) (X δ)
    linarith
  rw [e1]
  have e5 : -(1 / 4) * volM g * (2 * ∑ γ, ∑ δ, ∑ α, ∑ β, gi γ α * gi δ β *
      SM.ipG (F α β) (δF γ δ)) = -(1 / 2) * (volM g * ∑ γ, ∑ δ, ∑ α, ∑ β, gi γ α * gi δ β *
      SM.ipG (F α β) (δF γ δ)) := by ring
  rw [e5, e2, e3, e4]
  ring

end GaugeVar

section HiggsVar

/-- The Lie-module action as a bilinear map. -/
def actB (m : ℕ) (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V] : MatLie m →ₗ[ℝ] V →ₗ[ℝ] V :=
  LinearMap.mk₂ ℝ (fun (a : MatLie m) (w : V) => ⁅a, w⁆) add_lie smul_lie lie_add lie_smul

/-- The Higgs jet density `ϱ g^{βα}D_αH`. -/
def DhJ (v : ℝ) (gi : Fin 4 → Fin 4 → ℝ) (D : Fin 4 → V) (β : Fin 4) : V :=
  v • ∑ α, gi β α • D α

theorem ipV_DhJ (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (v : ℝ) (gi : Fin 4 → Fin 4 → ℝ) (D : Fin 4 → V)
    (β : Fin 4) (Y : V) : B (DhJ v gi D β) Y = v * ∑ α, gi β α * B (D α) Y := by
  unfold DhJ
  simp only [map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul]

/-- **The gauge and Higgs variation of the Higgs density** (jet level, variational data):
`d/dε LHg(A + εX, H + εη, ∂H + ε∂η) = -2Σ⟨𝔇^β, ∂_βη⟩ + 2⟨Σ[A_β, 𝔇^β], η⟩ - Σ⟨2μ(H, 𝔇^β), X_β⟩
- 2√(-det g)⟨S_H, η⟩`, `𝔇^β = √(-det g) g^{βα}D_αH`. -/
theorem hasDerivAt_LHg_AH (SM : SMData (MatLie m) V S S') (hV : GenStress.VariationalStress SM)
    {g : Fin 4 → Fin 4 → ℝ} (hsym : ∀ μ ν, g μ ν = g ν μ) (A X : Fin 4 → MatLie m) (H η : V)
    (dH dη : Fin 4 → V) :
    HasDerivAt (fun ε : ℝ => LHg SM g (A + ε • X) (H + ε • η) (dH + ε • dη))
      (-(2 * ∑ β, SM.ipV (DhJ (volM g) (ginvOf g) (ActualJetGauge.DH A H dH) β) (dη β)) +
        2 * SM.ipV (∑ β, ⁅A β, DhJ (volM g) (ginvOf g) (ActualJetGauge.DH A H dH) β⁆) η -
        ∑ β, SM.ipG ((2 : ℝ) • hV.μ H (DhJ (volM g) (ginvOf g) (ActualJetGauge.DH A H dH) β))
          (X β) -
        2 * volM g * SM.ipV ((2 * SM.lamH * (SM.ipV H H - SM.vH ^ 2)) • H) η) 0 := by
  set gi := ginvOf g with hgi
  have hgs : ∀ a b, gi a b = gi b a := ginvOf_symm' hsym
  set D := ActualJetGauge.DH A H dH with hD
  set δD : Fin 4 → V := fun α => dη α + ⁅X α, H⁆ + ⁅A α, η⁆ with hδD
  have hDl : ∀ α, HasDerivAt (fun ε : ℝ => ActualJetGauge.DH (A + ε • X) (H + ε • η)
      (dH + ε • dη) α) (δD α) 0 := by
    intro α
    have h1 := hasDerivAt_affine (dH α) (dη α)
    have h2 := hasDerivAt_bilin' (actB m V) (hasDerivAt_affine (A α) (X α))
      (hasDerivAt_affine H η)
    have h := h1.add h2
    unfold ActualJetGauge.DH
    simp only [Pi.add_apply, Pi.smul_apply, zero_smul, add_zero] at h ⊢
    refine h.congr_deriv ?_
    simp only [hδD, actB, LinearMap.mk₂_apply]
    abel
  have hq : HasDerivAt (fun ε : ℝ => quadD SM.ipV gi
      (ActualJetGauge.DH (A + ε • X) (H + ε • η) (dH + ε • dη)))
      (∑ α, ∑ β, gi α β * (SM.ipV (δD α) (D β) + SM.ipV (D α) (δD β))) 0 := by
    unfold quadD
    refine HasDerivAt.fun_sum fun α _ => HasDerivAt.fun_sum fun β _ => ?_
    have h := hasDerivAt_bilin SM.ipV (hDl α) (hDl β)
    simp only [zero_smul, add_zero] at h
    exact h.const_mul _
  have hH := hasDerivAt_bilin SM.ipV (hasDerivAt_affine H η) (hasDerivAt_affine H η)
  simp only [zero_smul, add_zero] at hH
  have hpot : HasDerivAt (fun ε : ℝ => SM.lamH * (SM.ipV (H + ε • η) (H + ε • η) - SM.vH ^ 2) ^ 2)
      (SM.lamH * (2 * (SM.ipV H H - SM.vH ^ 2) * (SM.ipV η H + SM.ipV H η))) 0 := by
    have := ((hH.sub_const (SM.vH ^ 2)).pow 2).const_mul SM.lamH
    simpa using this
  have h := ((hq.add hpot).const_mul (volM g)).neg
  unfold LHg
  refine h.congr_deriv ?_
  -- algebra
  have e1 : ∑ α, ∑ β, gi α β * (SM.ipV (δD α) (D β) + SM.ipV (D α) (δD β)) =
      2 * ∑ α, ∑ β, gi α β * SM.ipV (D α) (δD β) := by
    have h1 : ∑ α, ∑ β, gi α β * SM.ipV (δD α) (D β) = ∑ α, ∑ β, gi α β * SM.ipV (D α) (δD β) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun α _ => ?_
      rw [hV.ipV_symm, hgs]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [h1]; ring
  have e2 : volM g * ∑ α, ∑ β, gi α β * SM.ipV (D α) (δD β) =
      ∑ β, SM.ipV (DhJ (volM g) gi D β) (δD β) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [ipV_DhJ]
    congr 1
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [hgs]
  have e3 : ∀ β, SM.ipV (DhJ (volM g) gi D β) (δD β) =
      SM.ipV (DhJ (volM g) gi D β) (dη β) + SM.ipG (X β) (hV.μ H (DhJ (volM g) gi D β)) -
        SM.ipV ⁅A β, DhJ (volM g) gi D β⁆ η := by
    intro β
    simp only [hδD, map_add]
    rw [hV.ipV_symm (DhJ (volM g) gi D β) ⁅X β, H⁆, ← hV.moment]
    have := hV.ipV_inv (A β) (DhJ (volM g) gi D β) η
    linarith
  rw [e1]
  have e4 : volM g * (2 * ∑ α, ∑ β, gi α β * SM.ipV (D α) (δD β)) =
      2 * (volM g * ∑ α, ∑ β, gi α β * SM.ipV (D α) (δD β)) := by ring
  have e5 : ∑ β, SM.ipG ((2 : ℝ) • hV.μ H (DhJ (volM g) gi D β)) (X β) =
      2 * ∑ β, SM.ipG (X β) (hV.μ H (DhJ (volM g) gi D β)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hV.ipG_symm]
  have e6 : SM.ipV (∑ β, ⁅A β, DhJ (volM g) gi D β⁆) η =
      ∑ β, SM.ipV ⁅A β, DhJ (volM g) gi D β⁆ η := by
    rw [map_sum, LinearMap.sum_apply]
  have e7 : SM.ipV ((2 * SM.lamH * (SM.ipV H H - SM.vH ^ 2)) • H) η =
      2 * SM.lamH * (SM.ipV H H - SM.vH ^ 2) * SM.ipV H η := by
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [mul_add, e4, e2, e5, e6, e7, hV.ipV_symm η H]
  simp only [e3, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

end HiggsVar

/-! ### Contraction identities -/

section Contraction

/-- `Σ_{μν} (g P g)^{μν} k_{μν} = Σ_{αγ} (g k g)^{αγ} P_{αγ}`. -/
theorem up_contract (gi P k : Fin 4 → Fin 4 → ℝ) (hgi : ∀ a b, gi a b = gi b a) :
    ∑ μ, ∑ ν, up gi P μ ν * k μ ν =
      ∑ α, ∑ γ, (∑ c, ∑ d, gi α c * k c d * gi d γ) * P α γ := by
  unfold up
  simp only [Finset.sum_mul]
  rw [GenNoether.sum4_swap]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun γ _ => ?_
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [hgi c α]
  ring

/-- `Σ_{μν} (g g g)^{μν} k_{μν} = tr_g k`. -/
theorem up_metric_contract {g : Fin 4 → Fin 4 → ℝ} (hdet : (Matrix.of g).det ≠ 0)
    (hsym : ∀ μ ν, g μ ν = g ν μ) (k : Fin 4 → Fin 4 → ℝ) :
    ∑ μ, ∑ ν, up (ginvOf g) g μ ν * k μ ν = trG (ginvOf g) k := by
  have hinv : ∀ a c, ∑ b, g a b * ginvOf g b c = if a = c then 1 else 0 := by
    intro a c
    have h := Matrix.mul_nonsing_inv (Matrix.of g) (isUnit_iff_ne_zero.mpr hdet)
    have := congrFun (congrFun h a) c
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simpa [ginvOf] using this
  have hgg : ∀ μ ν, up (ginvOf g) g μ ν = ginvOf g μ ν := by
    intro μ ν
    unfold up
    have e : ∀ a, ∑ b, ginvOf g μ a * ginvOf g ν b * g a b = ginvOf g μ a *
        (if a = ν then 1 else 0) := by
      intro a
      rw [← hinv a ν, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [ginvOf_symm' hsym ν b]
      ring
    simp only [e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  unfold trG
  simp only [hgg]

end Contraction

/-! ### The Yang–Mills and Higgs stresses as metric variations -/

section Stress

variable {g k : Fin 4 → Fin 4 → ℝ}

theorem ginvVar_eq (gi k : Fin 4 → Fin 4 → ℝ) (α γ : Fin 4) :
    ginvVar gi k α γ = -∑ c, ∑ d, gi α c * k c d * gi d γ := rfl

/-- **The metric variation of the Yang–Mills density is the Yang–Mills stress**:
`d/dε LYM(g + εk) = ½√(-det g) T_{YM}^{μν}k_{μν}`. -/
theorem hasDerivAt_LYM_metric (SM : SMData (MatLie m) V S S')
    (hG : ∀ X Y, SM.ipG X Y = SM.ipG Y X) (hsym : ∀ μ ν, g μ ν = g ν μ)
    (hdet : (Matrix.of g).det < 0) (A : Fin 4 → MatLie m) (dA : Fin 4 → Fin 4 → MatLie m) :
    HasDerivAt (fun ε : ℝ => LYM SM (g + ε • k) A dA)
      ((1 / 2) * volM g * ∑ μ, ∑ ν, up (ginvOf g) (ymStressB SM.ipG g (ginvOf g) (Fm A dA)) μ ν *
        k μ ν) 0 := by
  have hv := hasDerivAt_vol_line (k := k) hdet hsym
  have hQ := hasDerivAt_quadF_line (k := k) SM.ipG (Fm A dA) hdet.ne
  have h := (hv.const_mul (-(1 / 4) : ℝ)).fun_mul hQ
  unfold LYM
  simp only [zero_smul, add_zero] at h
  refine h.congr_deriv ?_
  rw [quadF_var_symm SM.ipG (Fm A dA) (fun a b => Fm_anti A dA a b) (ginvOf g)
    (ginvVar (ginvOf g) k)]
  set P : Fin 4 → Fin 4 → ℝ := fun α γ => ∑ β, ∑ δ, ginvOf g β δ * SM.ipG (Fm A dA α β) (Fm A dA γ δ)
    with hP
  have e1 : ∑ α, ∑ β, ∑ γ, ∑ δ, ginvVar (ginvOf g) k α γ * ginvOf g β δ *
      SM.ipG (Fm A dA α β) (Fm A dA γ δ) = ∑ α, ∑ γ, ginvVar (ginvOf g) k α γ * P α γ := by
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun γ _ => ?_
    simp only [hP, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun δ _ => ?_
    ring
  have e2 : ∑ μ, ∑ ν, up (ginvOf g) (ymStressB SM.ipG g (ginvOf g) (Fm A dA)) μ ν * k μ ν =
      ∑ μ, ∑ ν, up (ginvOf g) P μ ν * k μ ν -
        (1 / 4) * quadF SM.ipG (ginvOf g) (Fm A dA) * trG (ginvOf g) k := by
    have hsplit : ∀ μ ν, up (ginvOf g) (ymStressB SM.ipG g (ginvOf g) (Fm A dA)) μ ν =
        up (ginvOf g) P μ ν - (1 / 4) * quadF SM.ipG (ginvOf g) (Fm A dA) * up (ginvOf g) g μ ν := by
      intro μ ν
      unfold up
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [ymStressB, hP, quadF]
      ring
    simp only [hsplit, sub_mul, Finset.sum_sub_distrib]
    rw [← up_metric_contract hdet.ne hsym k, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ν _ => by ring
  rw [e1, e2, up_contract _ _ _ (ginvOf_symm' hsym)]
  simp only [ginvVar_eq, neg_mul, Finset.sum_neg_distrib]
  ring

/-- **The metric variation of the Higgs density is the Higgs stress**:
`d/dε LHg(g + εk) = ½√(-det g) T_H^{μν}k_{μν}`. -/
theorem hasDerivAt_LHg_metric (SM : SMData (MatLie m) V S S') (hsym : ∀ μ ν, g μ ν = g ν μ)
    (hdet : (Matrix.of g).det < 0) (A : Fin 4 → MatLie m) (H : V) (dH : Fin 4 → V) :
    HasDerivAt (fun ε : ℝ => LHg SM (g + ε • k) A H dH)
      ((1 / 2) * volM g * ∑ μ, ∑ ν, up (ginvOf g) (higgsStressB SM.ipV SM.lamH SM.vH g (ginvOf g) H
        (ActualJetGauge.DH A H dH)) μ ν * k μ ν) 0 := by
  have hv := hasDerivAt_vol_line (k := k) hdet hsym
  have hQ := hasDerivAt_quadD_line (k := k) SM.ipV (ActualJetGauge.DH A H dH) hdet.ne
  set Vp := SM.lamH * (SM.ipV H H - SM.vH ^ 2) ^ 2 with hVp
  have h := (hv.fun_mul (hQ.add_const Vp)).neg
  unfold LHg
  simp only [zero_smul, add_zero] at h
  refine h.congr_deriv ?_
  set D := ActualJetGauge.DH A H dH with hD
  set P : Fin 4 → Fin 4 → ℝ := fun α β => SM.ipV (D α) (D β) with hP
  have e2 : ∑ μ, ∑ ν, up (ginvOf g) (higgsStressB SM.ipV SM.lamH SM.vH g (ginvOf g) H D) μ ν *
      k μ ν = 2 * ∑ μ, ∑ ν, up (ginvOf g) P μ ν * k μ ν -
        (quadD SM.ipV (ginvOf g) D + Vp) * trG (ginvOf g) k := by
    have hsplit : ∀ μ ν, up (ginvOf g) (higgsStressB SM.ipV SM.lamH SM.vH g (ginvOf g) H D) μ ν =
        2 * up (ginvOf g) P μ ν - (quadD SM.ipV (ginvOf g) D + Vp) * up (ginvOf g) g μ ν := by
      intro μ ν
      unfold up
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [higgsStressB, hP, hVp, quadD]
      ring
    simp only [hsplit, sub_mul, Finset.sum_sub_distrib]
    rw [← up_metric_contract hdet.ne hsym k, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun μ _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun ν _ => by ring
    · refine Finset.sum_congr rfl fun μ _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun ν _ => by ring
  rw [e2, up_contract _ _ _ (ginvOf_symm' hsym)]
  have e3 : ∑ α, ∑ β, ginvVar (ginvOf g) k α β * SM.ipV (D α) (D β) =
      -∑ α, ∑ γ, (∑ c, ∑ d, ginvOf g α c * k c d * ginvOf g d γ) * P α γ := by
    simp only [ginvVar_eq, neg_mul, Finset.sum_neg_distrib, hP]
  rw [e3]
  ring

end Stress

end

end GenMatVar

end RenewalGeometry
