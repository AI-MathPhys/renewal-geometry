/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeModelMap

/-!
# Algebra of the coframe row: the Koszul cyclic identity, a Clifford anticommutator identity
and the torsion-free metric reader connection

Generic infrastructure for bridge step P3-stress of `thm:native-closure` (Einstein–Standard-Model
action-closure manuscript): the coframe (metric) row of the native Lagrangian.  The Dirac density
`v Re{(i/2)[Ψ̄γ^μ∇_μΨ - (∇_μΨ̄)γ^μΨ] - Ψ̄𝓜Ψ}` depends on the coframe through `v`, `γ^μ(e)` and the
spin connection `σ(ω(e, ∂e))`.  The spin connection enters only through the anticommutator
`Σ_μ {γ^μ, σ(ω_μ)}`, which sees only the totally antisymmetric part of the frame components of
`ω`.  This file proves the algebra behind the statement that a *symmetric* (metric) variation of the
coframe does not move this anticommutator.

* `cyclic_zero_of_torsion` — **Koszul cyclic identity**: if `U_{xyz} = -U_{xzy}`,
  `V_{xyz} = V_{xzy}` and `U_{xyz} - U_{zyx} = V_{xyz} - V_{zyx}`, then
  `U_{xyz} + U_{yzx} + U_{zxy} = 0`.
* `triple_eq` / `sum_triple_anticomm_eq_zero` — for Clifford generators
  (`γ^aγ^b + γ^bγ^a = 2η^{ab}`) and `U` antisymmetric in its last two slots with vanishing cyclic
  sum, `Σ_{xyz} U_{xyz}(γ^xγ^yγ^z + γ^yγ^zγ^x) = 0`.
* `readerOmega_eq`, `readerGamma_eq_chr`, `readerGamma_symm`, `compat_alg` — the reader connection
  `Ω_μ(e, q) = eΓ_μe⁻¹ - q_μe⁻¹` (`Γ` the Christoffel symbols of `g = eᵀηe` with first jet
  `qᵀηe + eᵀηq`) and the algebraic metric compatibility `gΓ_μ + Γ_μᵀg = ∂_μg`;
* **`readerOmega_antisym`** — `ηΩ_μ + Ω_μᵀη = 0` for every `(e, q)` with `det e ≠ 0`;
* **`readerOmega_torsion`** — torsion-freeness `(Ω_αe + q_α)_{aβ} = (Ω_βe + q_β)_{aα}`;
* `readerOmega_add`, `readerOmega_smul` — linearity in the jet `q`;
* **`anticomm_sum_zero`** — if `ηX_α` is antisymmetric, `ηY_α` symmetric and
  `(X_αe)_{aβ} - (X_βe)_{aα} = (Y_αe)_{aβ} - (Y_βe)_{aα}`, then
  `Σ_ν (γ^ν(e) σ(X_ν) + σ(X_ν) γ^ν(e)) = 0` (frame conversion, Koszul, Clifford).
-/

namespace RenewalGeometry

namespace NativeStressEuler

open Finset HarmonicDefect PalatiniEuler NativeDiracEuler
open NativeScaling (Mat eta metric readerOmega readerG readerGamma)
open NativeDensity
open scoped Matrix

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

/-! ### The Koszul cyclic identity -/

/-- **Koszul cyclic identity**: a tensor antisymmetric in its last two slots whose
"torsion" `U_{xyz} - U_{zyx}` is that of a tensor symmetric in its last two slots has vanishing
cyclic sum. -/
theorem cyclic_zero_of_torsion {ι : Type*} (U V : ι → ι → ι → ℝ)
    (hU : ∀ x y z, U x y z = -U x z y) (hV : ∀ x y z, V x y z = V x z y)
    (hT : ∀ x y z, U x y z - U z y x = V x y z - V z y x) (x y z : ι) :
    U x y z + U y z x + U z x y = 0 := by
  have h1 := hT x y z
  have h2 := hT y z x
  have h3 := hT z x y
  have a1 := hU z y x
  have a2 := hU x z y
  have a3 := hU y x z
  have b1 := hV x y z
  have b2 := hV y z x
  have b3 := hV z x y
  linarith

/-! ### A Clifford identity -/

section Clifford

variable {R : Type*} [Ring R] [Algebra ℝ R]

/-- The total antisymmetrisation (times `6`) of a triple product. -/
def A3 (γ : Fin 4 → R) (x y z : Fin 4) : R :=
  γ x * γ y * γ z - γ x * γ z * γ y + γ y * γ z * γ x - γ y * γ x * γ z +
    γ z * γ x * γ y - γ z * γ y * γ x

theorem A3_cyc (γ : Fin 4 → R) (x y z : Fin 4) : A3 γ y z x = A3 γ x y z := by
  unfold A3; abel

theorem sym_eta (a b : Fin 4) : eta a b = eta b a := PalatiniEuler.eta_symm a b

/-- `3(γ^xγ^yγ^z + γ^yγ^zγ^x) = A₃(x,y,z) + 6η^{yz}γ^x`. -/
theorem triple_eq (γ : Fin 4 → R) (hcl : ∀ a b, γ a * γ b + γ b * γ a = (2 * eta a b) • 1)
    (x y z : Fin 4) :
    (3 : ℝ) • (γ x * γ y * γ z + γ y * γ z * γ x) = A3 γ x y z + (6 * eta y z) • γ x := by
  have c : ∀ a b, γ a * γ b = (2 * eta a b) • 1 - γ b * γ a := fun a b => eq_sub_of_add_eq (hcl a b)
  have r1 : γ x * γ z * γ y = (2 * eta z y) • γ x - γ x * γ y * γ z := by
    rw [mul_assoc, c z y, mul_sub, mul_smul_comm, mul_one, ← mul_assoc]
  have r2 : γ y * γ x * γ z = (2 * eta y x) • γ z - γ x * γ y * γ z := by
    rw [c y x, sub_mul, smul_mul_assoc, one_mul]
  have r3 : γ y * γ z * γ x = (2 * eta z x) • γ y - (2 * eta y x) • γ z + γ x * γ y * γ z := by
    rw [mul_assoc, c z x, mul_sub, mul_smul_comm, mul_one, ← mul_assoc, r2]
    abel
  have r4 : γ z * γ x * γ y = (2 * eta z x) • γ y - (2 * eta z y) • γ x + γ x * γ y * γ z := by
    rw [c z x, sub_mul, smul_mul_assoc, one_mul, r1]
    abel
  have r5 : γ z * γ y * γ x = (2 * eta y x) • γ z - (2 * eta z x) • γ y + (2 * eta z y) • γ x -
      γ x * γ y * γ z := by
    rw [mul_assoc, c y x, mul_sub, mul_smul_comm, mul_one, ← mul_assoc, r4]
    abel
  unfold A3
  rw [r1, r2, r3, r4, r5]
  rw [sym_eta z y, sym_eta y x, sym_eta z x]
  module

/-- **`Σ_{xyz} U_{xyz}(γ^xγ^yγ^z + γ^yγ^zγ^x) = 0`** for `U` antisymmetric in its last two slots
with vanishing cyclic sum. -/
theorem sum_triple_anticomm_eq_zero (γ : Fin 4 → R)
    (hcl : ∀ a b, γ a * γ b + γ b * γ a = (2 * eta a b) • 1) (U : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hU : ∀ x y z, U x y z = -U x z y) (hC : ∀ x y z, U x y z + U y z x + U z x y = 0) :
    ∑ x, ∑ y, ∑ z, U x y z • (γ x * γ y * γ z + γ y * γ z * γ x) = 0 := by
  -- the trace part
  have htr : ∀ x, ∑ y, ∑ z, U x y z * eta y z = 0 := by
    intro x
    have h : ∑ y, ∑ z, U x y z * eta y z = ∑ y, ∑ z, U x z y * eta z y := Finset.sum_comm
    have h' : ∑ y, ∑ z, U x z y * eta z y = -∑ y, ∑ z, U x y z * eta y z := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [hU x z y, sym_eta z y]; ring
    linarith
  -- the antisymmetric part
  have hA : ∑ x, ∑ y, ∑ z, U x y z • A3 γ x y z = 0 := by
    set S := ∑ x, ∑ y, ∑ z, U x y z • A3 γ x y z with hS
    have e1 : ∑ x, ∑ y, ∑ z, U y z x • A3 γ x y z = S := by
      calc ∑ x, ∑ y, ∑ z, U y z x • A3 γ x y z = ∑ x, ∑ y, ∑ z, U y z x • A3 γ y z x := by
            simp only [A3_cyc]
        _ = ∑ y, ∑ x, ∑ z, U y z x • A3 γ y z x := Finset.sum_comm
        _ = ∑ y, ∑ z, ∑ x, U y z x • A3 γ y z x :=
            Finset.sum_congr rfl fun y _ => Finset.sum_comm
    have e2 : ∑ x, ∑ y, ∑ z, U z x y • A3 γ x y z = S := by
      calc ∑ x, ∑ y, ∑ z, U z x y • A3 γ x y z = ∑ x, ∑ y, ∑ z, U z x y • A3 γ z x y := by
            simp only [A3_cyc]
        _ = ∑ x, ∑ z, ∑ y, U z x y • A3 γ z x y :=
            Finset.sum_congr rfl fun x _ => Finset.sum_comm
        _ = ∑ z, ∑ x, ∑ y, U z x y • A3 γ z x y := Finset.sum_comm
    have e3 : S + ∑ x, ∑ y, ∑ z, U y z x • A3 γ x y z + ∑ x, ∑ y, ∑ z, U z x y • A3 γ x y z = 0 := by
      rw [hS, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun z _ => ?_
      rw [← add_smul, ← add_smul, hC x y z, zero_smul]
    rw [e1, e2] at e3
    have : (3 : ℝ) • S = 0 := by rw [show (3 : ℝ) • S = S + S + S by module]; exact e3
    exact (smul_eq_zero.1 this).resolve_left (by norm_num)
  have h3 : (3 : ℝ) • ∑ x, ∑ y, ∑ z, U x y z • (γ x * γ y * γ z + γ y * γ z * γ x) = 0 := by
    have e : (3 : ℝ) • ∑ x, ∑ y, ∑ z, U x y z • (γ x * γ y * γ z + γ y * γ z * γ x) =
        ∑ x, ∑ y, ∑ z, (U x y z • A3 γ x y z + (U x y z * (6 * eta y z)) • γ x) := by
      simp only [Finset.smul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
        Finset.sum_congr rfl fun z _ => ?_
      rw [smul_comm, triple_eq γ hcl, smul_add, smul_smul]
    rw [e]
    simp only [Finset.sum_add_distrib, hA, zero_add]
    have : ∀ x, ∑ y, ∑ z, (U x y z * (6 * eta y z)) • γ x =
        ((6 : ℝ) * ∑ y, ∑ z, U x y z * eta y z) • γ x := by
      intro x
      rw [Finset.mul_sum, Finset.sum_smul]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.mul_sum, Finset.sum_smul]
      refine Finset.sum_congr rfl fun z _ => ?_
      congr 1; ring
    simp only [this, htr, mul_zero, zero_smul, Finset.sum_const_zero]
  exact (smul_eq_zero.1 h3).resolve_left (by norm_num)

end Clifford

/-! ### The torsion-free metric reader connection -/

section Reader

/-- The Christoffel matrix `Γ_μ = (Γ^ρ_{μσ})_{ρσ}` of the reader. -/
def gam (e : Mat) (q : Fin 4 → Mat) (μ : Fin 4) : Mat := fun ρ σ => readerGamma e q ρ μ σ

theorem readerOmega_eq (e : Mat) (q : Fin 4 → Mat) (μ : Fin 4) :
    readerOmega e q μ = e * gam e q μ * e⁻¹ - q μ * e⁻¹ := by
  ext a b
  simp only [readerOmega, gam, Matrix.sub_apply, Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The reader Christoffel symbols are the Christoffel symbols of `(g, ∂g) = (eᵀηe, readerG)`. -/
theorem readerGamma_eq_chr (e : Mat) (q : Fin 4 → Mat) (ρ μ σ : Fin 4) :
    readerGamma e q ρ μ σ = chr (fun a b => (metric e)⁻¹ a b) (readerG e q) ρ μ σ := by
  unfold readerGamma chr
  congr 1
  · norm_num
  · refine Finset.sum_congr rfl fun s _ => ?_
    rw [readerG_symm e q μ σ s, readerG_symm e q σ μ s]

theorem readerGamma_symm (e : Mat) (q : Fin 4 → Mat) (ρ μ σ : Fin 4) :
    readerGamma e q ρ μ σ = readerGamma e q ρ σ μ := by
  rw [readerGamma_eq_chr, readerGamma_eq_chr]
  unfold chr
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [readerG_symm e q s μ σ]
  ring

theorem metric_mul_inv {e : Mat} (he : e.det ≠ 0) (a c : Fin 4) :
    ∑ b, metric e a b * (metric e)⁻¹ b c = if a = c then 1 else 0 := by
  rw [← Matrix.mul_apply, Matrix.mul_nonsing_inv _ (det_metric_ne_zero he).isUnit,
    Matrix.one_apply]

/-- **Algebraic metric compatibility** `gΓ_μ + Γ_μᵀg = readerG_μ = q_μᵀηe + eᵀηq_μ`. -/
theorem compat_alg {e : Mat} (he : e.det ≠ 0) (q : Fin 4 → Mat) (μ : Fin 4) :
    metric e * gam e q μ + (gam e q μ)ᵀ * metric e = readerG e q μ := by
  ext ν σ
  have hc := FrameCurvature.metric_compat (fun a b => metric e a b)
    (fun a b => (metric e)⁻¹ a b) (readerG e q) (metric_mul_inv he)
    (fun α a b => readerG_symm e q α a b) μ ν σ
  rw [hc, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [gam, Matrix.transpose_apply, readerGamma_eq_chr]
  rw [PalatiniEuler.metric_symm e σ l]
  ring

/-- **The reader connection is `η`-antisymmetric**: `ηΩ_μ + Ω_μᵀη = 0` (any jet `q`). -/
theorem readerOmega_antisym {e : Mat} (he : e.det ≠ 0) (q : Fin 4 → Mat) (μ : Fin 4) :
    eta * readerOmega e q μ + (readerOmega e q μ)ᵀ * eta = 0 := by
  set E := e
  set Q := q μ
  set G := gam e q μ
  have hu : IsUnit E.det := he.isUnit
  have hΩ : readerOmega e q μ = E * G * E⁻¹ - Q * E⁻¹ := readerOmega_eq e q μ
  have hc : Eᵀ * eta * E * G + Gᵀ * (Eᵀ * eta * E) = Qᵀ * eta * E + Eᵀ * eta * Q :=
    compat_alg he q μ
  have hEiE : E⁻¹ * E = 1 := Matrix.nonsing_inv_mul E hu
  have hEEi : E * E⁻¹ = 1 := Matrix.mul_nonsing_inv E hu
  set Ω := readerOmega e q μ
  have hΩE : Ω * E = E * G - Q := by
    rw [hΩ, Matrix.sub_mul, Matrix.mul_assoc, hEiE, Matrix.mul_one, Matrix.mul_assoc Q, hEiE,
      Matrix.mul_one]
  have h1 : Eᵀ * (eta * Ω) * E = Eᵀ * eta * E * G - Eᵀ * eta * Q := by
    calc Eᵀ * (eta * Ω) * E = Eᵀ * eta * (Ω * E) := by noncomm_ring
      _ = Eᵀ * eta * (E * G - Q) := by rw [hΩE]
      _ = _ := by noncomm_ring
  have h2 : Eᵀ * (Ωᵀ * eta) * E = Gᵀ * (Eᵀ * eta * E) - Qᵀ * eta * E := by
    have hT : Eᵀ * Ωᵀ = (E * G - Q)ᵀ := by rw [← hΩE, Matrix.transpose_mul]
    calc Eᵀ * (Ωᵀ * eta) * E = (Eᵀ * Ωᵀ) * eta * E := by noncomm_ring
      _ = (E * G - Q)ᵀ * eta * E := by rw [hT]
      _ = _ := by rw [Matrix.transpose_sub, Matrix.transpose_mul]; noncomm_ring
  have key : Eᵀ * (eta * Ω + Ωᵀ * eta) * E = 0 := by
    calc Eᵀ * (eta * Ω + Ωᵀ * eta) * E = Eᵀ * (eta * Ω) * E + Eᵀ * (Ωᵀ * eta) * E := by
          noncomm_ring
      _ = (Eᵀ * eta * E * G + Gᵀ * (Eᵀ * eta * E)) - (Qᵀ * eta * E + Eᵀ * eta * Q) := by
          rw [h1, h2]; abel
      _ = 0 := by rw [hc, sub_self]
  have hEt : (Eᵀ)⁻¹ * Eᵀ = 1 := Matrix.nonsing_inv_mul _ (by rw [Matrix.det_transpose]; exact hu)
  calc eta * Ω + Ωᵀ * eta = ((Eᵀ)⁻¹ * Eᵀ) * (eta * Ω + Ωᵀ * eta) * (E * E⁻¹) := by
        rw [hEt, hEEi, Matrix.one_mul, Matrix.mul_one]
    _ = (Eᵀ)⁻¹ * (Eᵀ * (eta * Ω + Ωᵀ * eta) * E) * E⁻¹ := by noncomm_ring
    _ = 0 := by rw [key]; simp

/-- **The reader connection is torsion-free**: `(Ω_αe + q_α)_{aβ} = (Ω_βe + q_β)_{aα}`. -/
theorem readerOmega_torsion {e : Mat} (he : e.det ≠ 0) (q : Fin 4 → Mat) (α β a : Fin 4) :
    (readerOmega e q α * e + q α) a β = (readerOmega e q β * e + q β) a α := by
  have hEiE : e⁻¹ * e = 1 := Matrix.nonsing_inv_mul e he.isUnit
  have h : ∀ γ, readerOmega e q γ * e + q γ = e * gam e q γ := by
    intro γ
    rw [readerOmega_eq, Matrix.sub_mul, Matrix.mul_assoc, hEiE, Matrix.mul_one,
      Matrix.mul_assoc (q γ), hEiE, Matrix.mul_one, sub_add_cancel]
  rw [h, h, Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  simp only [gam]
  rw [readerGamma_symm]

end Reader

/-! ### The anticommutator identity -/

section Anticomm

theorem mul_inv_sum {e : Mat} (he : e.det ≠ 0) (k d : Fin 4) :
    ∑ β, e k β * e⁻¹ β d = if k = d then 1 else 0 := by
  rw [← Matrix.mul_apply, Matrix.mul_nonsing_inv _ he.isUnit, Matrix.one_apply]

/-- Frame components of a coordinate family `X_α` of matrices: `Σ_α e_c^α X_α`,
`e_c^α = (e⁻¹)^α_c`. -/
def frameOf (e : Mat) (X : Fin 4 → Mat) (c : Fin 4) : Mat := ∑ α, e⁻¹ α c • X α

/-- Lowered frame components `(η Σ_α e_c^α X_α)_{ab}`. -/
def lowFrame (e : Mat) (X : Fin 4 → Mat) (c a b : Fin 4) : ℝ := (eta * frameOf e X c) a b

theorem frame_torsion {e : Mat} (he : e.det ≠ 0) (X : Fin 4 → Mat) (c a d : Fin 4) :
    ∑ α, ∑ β, e⁻¹ α c * e⁻¹ β d * (X α * e) a β = frameOf e X c a d := by
  unfold frameOf
  rw [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul]
  have : ∑ β, e⁻¹ α c * e⁻¹ β d * (X α * e) a β =
      e⁻¹ α c * ∑ k, X α a k * ∑ β, e k β * e⁻¹ β d := by
    simp only [Matrix.mul_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun β _ => ?_
    ring
  rw [this]
  simp only [mul_inv_sum he, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

theorem lowFrame_torsion {e : Mat} (he : e.det ≠ 0) (X Y : Fin 4 → Mat)
    (hT : ∀ α β a, (X α * e) a β - (X β * e) a α = (Y α * e) a β - (Y β * e) a α)
    (c a d : Fin 4) :
    lowFrame e X c a d - lowFrame e X d a c = lowFrame e Y c a d - lowFrame e Y d a c := by
  have hf : ∀ (Z : Fin 4 → Mat) (c d : Fin 4) (a : Fin 4),
      frameOf e Z c a d - frameOf e Z d a c =
        ∑ α, ∑ β, e⁻¹ α c * e⁻¹ β d * ((Z α * e) a β - (Z β * e) a α) := by
    intro Z c d a
    rw [← frame_torsion he Z c a d, ← frame_torsion he Z d a c]
    rw [Finset.sum_comm (f := fun α β => e⁻¹ α d * e⁻¹ β c * (Z α * e) a β)]
    simp only [mul_sub, Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    ring
  unfold lowFrame
  simp only [Matrix.mul_apply]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_sub, ← mul_sub, hf X c d k, hf Y c d k]
  congr 1
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  rw [hT]

theorem lowFrame_antisym {e : Mat} (X : Fin 4 → Mat)
    (hX : ∀ α, eta * X α + (X α)ᵀ * eta = 0) (c a b : Fin 4) :
    lowFrame e X c a b = -lowFrame e X c b a := by
  have h : eta * frameOf e X c + (frameOf e X c)ᵀ * eta = 0 := by
    unfold frameOf
    rw [Matrix.mul_sum, Matrix.transpose_sum, Matrix.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun α _ => ?_
    rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, ← smul_add, hX, smul_zero]
  have hT : (frameOf e X c)ᵀ * eta = (eta * frameOf e X c)ᵀ := by
    rw [Matrix.transpose_mul, PalatiniEuler.eta_transpose]
  rw [hT] at h
  have h' := congrFun (congrFun h a) b
  rw [Matrix.add_apply, Matrix.zero_apply, Matrix.transpose_apply] at h'
  unfold lowFrame
  linarith

theorem lowFrame_symm {e : Mat} (Y : Fin 4 → Mat) (hY : ∀ α, (eta * Y α)ᵀ = eta * Y α)
    (c a b : Fin 4) : lowFrame e Y c a b = lowFrame e Y c b a := by
  have h : (eta * frameOf e Y c)ᵀ = eta * frameOf e Y c := by
    unfold frameOf
    rw [Matrix.mul_sum, Matrix.transpose_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Matrix.mul_smul, Matrix.transpose_smul, hY]
  unfold lowFrame
  conv_rhs => rw [← h]
  rfl

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢]

/-- **The anticommutator identity**: if `ηX_α` is antisymmetric, `ηY_α` symmetric and the
torsions agree, `(X_αe)_{aβ} - (X_βe)_{aα} = (Y_αe)_{aβ} - (Y_βe)_{aα}`, then
`Σ_ν (γ^ν(e) σ(X_ν) + σ(X_ν) γ^ν(e)) = 0`. -/
theorem anticomm_sum_zero (D : Data 𝔄 𝓗 𝓢)
    (hcl : ∀ a b, D.γ a * D.γ b + D.γ b * D.γ a = (2 * eta a b) • 1)
    (hσ : ∀ om, D.σ om = sigmaOf D.γ om) {e : Mat} (he : e.det ≠ 0) (X Y : Fin 4 → Mat)
    (hX : ∀ α, eta * X α + (X α)ᵀ * eta = 0) (hY : ∀ α, (eta * Y α)ᵀ = eta * Y α)
    (hT : ∀ α β a, (X α * e) a β - (X β * e) a α = (Y α * e) a β - (Y β * e) a α) :
    ∑ ν, (gammaMu D ν e * D.σ (X ν) + D.σ (X ν) * gammaMu D ν e) = 0 := by
  set U := lowFrame e X with hUdef
  have hU : ∀ x y z, U x y z = -U x z y := fun x y z => lowFrame_antisym X hX x y z
  have hC : ∀ x y z, U x y z + U y z x + U z x y = 0 :=
    cyclic_zero_of_torsion U (lowFrame e Y) hU (lowFrame_symm Y hY)
      (fun x y z => lowFrame_torsion he X Y hT x y z)
  have hsum := sum_triple_anticomm_eq_zero D.γ hcl U hU hC
  -- rewrite the anticommutator sum in frame form
  have hσf : ∀ c, D.σ (frameOf e X c) =
      (1 / 4 : ℝ) • ∑ a, ∑ b, U c a b • (D.γ a * D.γ b) := by
    intro c
    rw [hσ]
    unfold sigmaOf
    congr 1
  have hframe : ∑ ν, (gammaMu D ν e * D.σ (X ν) + D.σ (X ν) * gammaMu D ν e) =
      ∑ c, (D.γ c * D.σ (frameOf e X c) + D.σ (frameOf e X c) * D.γ c) := by
    unfold gammaMu frameOf
    simp only [map_sum, map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
      Finset.sum_add_distrib, invEntry]
    congr 1 <;> exact Finset.sum_comm
  rw [hframe]
  simp only [hσf, mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul, ← smul_add,
    ← Finset.smul_sum, ← Finset.sum_add_distrib]
  rw [show (∑ x, ∑ y, ∑ z, U x y z • (D.γ x * (D.γ y * D.γ z) + D.γ y * D.γ z * D.γ x)) =
      ∑ x, ∑ y, ∑ z, U x y z • (D.γ x * D.γ y * D.γ z + D.γ y * D.γ z * D.γ x) from
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun z _ => by rw [← mul_assoc]]
  rw [hsum, smul_zero]

end Anticomm

end

end NativeStressEuler

end RenewalGeometry
