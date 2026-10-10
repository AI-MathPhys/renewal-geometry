/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeFrameBridge
import RenewalGeometry.Continuum.NativeModelExample
import RenewalGeometry.Continuum.NativeSlabFrameMargin
import RenewalGeometry.Gravity.ActualJetSmoothness

/-!
# The slab theory data of a native model (bridge step P2 of `thm:native-closure`)

Einstein–Standard-Model action-closure manuscript, `thm:native-closure` (bridge between the
native records of `thm:native-source` and the actual-tuple slab model of
`prop:coupled-bootstrap`).

`NativeModel.Model` carries the representation data of the native densities with the structure
of their physical reading.  To feed the slab model (`ActualJetSystem.SMData` over the Lie algebra
`ActualJetSmooth.MatLie m = gl(m, ℝ)` with a Lie module of Higgs fields), a native model needs:

* an identification of its gauge algebra with `gl(m, ℝ)`: an `ℝ`-algebra isomorphism
  `φ : 𝔄 ≃ₐ[ℝ] MatLie m` (the associative algebra `𝔄` carries the `NormedRing` structure the
  native action needs; `MatLie m` only its entrywise norm);
* **Lorentz covariance of the Yukawa map**: `𝓜_𝐘(H)` commutes with `γ^aγ^b`;
* **gauge equivariance of the Yukawa map**: `ρ_S(A)𝓜_𝐘(H) - 𝓜_𝐘(H)ρ_S(A) = 𝓜_𝐘(ρ_H(A)H)`;
* the gauge Lie set `gLie` is a linear subspace `gSub` (so that it is preserved by trigonometric
  reconstruction and by the dilation of the slab coordinates) which is a **Lie subalgebra** (closed
  under commutators) on which `⟨·,·⟩_𝐠` is **nondegenerate**, and `κ ≠ 0`.

**Gauge sector in `𝔤` (corrected encoding, g11).**  The gauge potential and its test directions
live in the gauge Lie algebra `𝔤 = gSub`; `𝔄` is only the ambient associative algebra of the
representations.  `πg` is the `⟨·,·⟩_𝐠`-orthogonal projection onto `𝔤` (`πg_mem`, `πg_of_mem`,
`ipA_πg`, `ipA_πg_symm`), and the slab Yang–Mills current `Jcur` is the `𝔤`-component of the
represented native current: `J_σ = g_{σν} φ(πg R⁻¹(curVal_ν))`.  Hence the slab Yang–Mills
equation of a `𝔤`-valued potential is exactly the vanishing of the native gauge rows in the
`𝔤`-directions (`RecordTuple.gauge_row_toTuple`); the rows in the non-gauge directions of `𝔄`
(e.g. the unit, `CalibrationBackreacting.unit_gauge_row`) are not imposed.

These are the hypotheses `DiracData.mass_cl` and `DiracData.mass_eq` of the slab Dirac blocks.

## Main definitions

* `SlabModel` — a native model with the data above.
* `HSp M` — the Higgs space as a Lie module over `MatLie m` (`⁅X, H⁆ = ρ_H(φ⁻¹X)H`).
* `diracD M`, `diracDb M` — the slab Dirac blocks: Clifford frame `c_a = ε_aJγ^a`
  (`NativeFrameBridge.slabCliff`) on spinors, and the transposed frame `c̄_a Ψ̄ = Ψ̄ ∘ c_a` on
  co-spinors, gauge actions `ρ_S`, `-(· ∘ ρ_S)`, mass maps `𝓜_𝐘`, `-(· ∘ 𝓜_𝐘)`.
* `Jcur`, `SH`, `TD` — the Yang–Mills current, the Higgs source and the symmetrised Dirac stress of
  the native Lagrangian written as functions of the slab variables (the current needs the frame;
  it is taken in the smoothed adapted frame `SlabData.frUs δ`, which is the adapted frame on the
  margin `Margin δ`).
* **`toSMData M δ`** — the slab theory data, with **`toSMData_smooth`** (`SMSmooth`).
* `diracSlab` — the concrete native model `NativeModelExample.diracModel` as a slab model
  (non-vacuity).
-/

open Finset
open scoped ContDiff

namespace RenewalGeometry.SlabData

open ActualJetSystem ActualJetSmooth NativeDensity NativeModel NativeFrameBridge
open NativeScaling (Mat eta)
open TwistedHalfRicci (CliffordFrame)

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

/-! ### Generic: transport of Clifford frames -/

section CliffGeneric

variable {ι : Type*} [DecidableEq ι]
variable {A B : Type*} [Ring A] [Algebra ℝ A] [Ring B] [Algebra ℝ B]

/-- The image of a Clifford frame under an algebra homomorphism. -/
def cliffMap (Fr : CliffordFrame ι A) (f : A →ₐ[ℝ] B) : CliffordFrame ι B where
  c a := f (Fr.c a)
  ε := Fr.ε
  sign_sq := Fr.sign_sq
  anticomm a b := by rw [← map_mul, ← map_mul, ← map_add, Fr.anticomm, map_smul, map_one]

/-- The image of a Clifford frame under an algebra anti-homomorphism. -/
def cliffAnti (Fr : CliffordFrame ι A) (f : A →ₗ[ℝ] B) (hf1 : f 1 = 1)
    (hmul : ∀ x y, f (x * y) = f y * f x) : CliffordFrame ι B where
  c a := f (Fr.c a)
  ε := Fr.ε
  sign_sq := Fr.sign_sq
  anticomm a b := by
    rw [← hmul, ← hmul, ← map_add, add_comm, Fr.anticomm, map_smul, hf1]

end CliffGeneric

/-! ### Generic: Riesz vectors of a nondegenerate form -/

section Riesz

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- The Riesz map `w ↦ B(·, w)` of a bilinear form, as a map into the algebraic dual. -/
def rieszL (B : W →L[ℝ] W →L[ℝ] ℝ) : W →ₗ[ℝ] Module.Dual ℝ W where
  toFun w := (B.flip w : W →L[ℝ] ℝ).toLinearMap
  map_add' w w' := by ext y; simp
  map_smul' r w := by ext y; simp

theorem rieszL_injective {B : W →L[ℝ] W →L[ℝ] ℝ} (hB : ∀ x, (∀ y, B y x = 0) → x = 0) :
    Function.Injective (rieszL B) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  exact hB w fun y => by simpa [rieszL] using LinearMap.congr_fun hw y

/-- The Riesz isomorphism `W ≃ W*` of a nondegenerate form. -/
def rieszE {B : W →L[ℝ] W →L[ℝ] ℝ} (hB : ∀ x, (∀ y, B y x = 0) → x = 0) :
    W ≃ₗ[ℝ] Module.Dual ℝ W :=
  (rieszL B).linearEquivOfInjective (rieszL_injective hB) Subspace.dual_finrank_eq.symm

/-- The Riesz vectors of the coordinate functionals of the standard basis. -/
def rieszBasisVec {B : W →L[ℝ] W →L[ℝ] ℝ} (hB : ∀ x, (∀ y, B y x = 0) → x = 0)
    (i : Fin (Module.finrank ℝ W)) : W :=
  (rieszE hB).symm ((Module.finBasis ℝ W).coord i)

/-- **The Riesz vector** of a (not necessarily linear) function `c`, through the standard basis:
`Σ_i c(b_i) w_i`; for linear `c` it represents `c` (`riesz_apply`). -/
def rieszVec {B : W →L[ℝ] W →L[ℝ] ℝ} (hB : ∀ x, (∀ y, B y x = 0) → x = 0) (c : W → ℝ) : W :=
  ∑ i, c (Module.finBasis ℝ W i) • rieszBasisVec hB i

theorem B_rieszBasisVec {B : W →L[ℝ] W →L[ℝ] ℝ} (hB : ∀ x, (∀ y, B y x = 0) → x = 0)
    (i : Fin (Module.finrank ℝ W)) (y : W) :
    B y (rieszBasisVec hB i) = (Module.finBasis ℝ W).coord i y := by
  have h : rieszL B (rieszBasisVec hB i) = (Module.finBasis ℝ W).coord i :=
    LinearEquiv.apply_symm_apply (rieszE hB) ((Module.finBasis ℝ W).coord i)
  exact LinearMap.congr_fun h y

/-- **The Riesz vector represents a linear functional**: `B(y, rieszVec c) = c(y)`. -/
theorem riesz_apply {B : W →L[ℝ] W →L[ℝ] ℝ} (hB : ∀ x, (∀ y, B y x = 0) → x = 0)
    (c : W →ₗ[ℝ] ℝ) (y : W) : B y (rieszVec hB c) = c y := by
  unfold rieszVec
  rw [map_sum]
  simp only [map_smul, B_rieszBasisVec, smul_eq_mul]
  conv_rhs => rw [← (Module.finBasis ℝ W).sum_repr y]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, Module.Basis.coord_apply, mul_comm]

theorem contDiff_rieszVec {B : W →L[ℝ] W →L[ℝ] ℝ} (hB : ∀ x, (∀ y, B y x = 0) → x = 0)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {c : E → W → ℝ}
    (hc : ∀ i, ContDiff ℝ ∞ (fun p => c p (Module.finBasis ℝ W i))) :
    ContDiff ℝ ∞ (fun p => rieszVec hB (c p)) := by
  unfold rieszVec
  exact ContDiff.sum fun i _ => (hc i).smul contDiff_const

end Riesz

/-! ### Slab models -/

/-- **A slab model**: a native model whose gauge algebra is identified with `gl(m, ℝ)`, with a
Lorentz-covariant and gauge-equivariant Yukawa map, a linear gauge Lie subspace and `κ ≠ 0`. -/
structure SlabModel (𝔄 𝓗 𝓢 : Type*) [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄]
    [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] (m : ℕ)
    extends Model 𝔄 𝓗 𝓢 where
  /-- the identification of the gauge algebra with `gl(m, ℝ)` -/
  φ : 𝔄 ≃ₐ[ℝ] MatLie m
  /-- Lorentz covariance of the Yukawa map -/
  yukawa_cl : ∀ H a b, yukawa H * (γ a * γ b) = γ a * γ b * yukawa H
  /-- gauge equivariance of the Yukawa map -/
  yukawa_eq : ∀ A H, ρS A * yukawa H - yukawa H * ρS A = yukawa (ρH A H)
  /-- the gauge Lie subspace -/
  gSub : Submodule ℝ 𝔄
  gLie_eq : (gSub : Set 𝔄) = gLie
  /-- the gauge Lie subspace is a Lie subalgebra (closed under commutators) -/
  gSub_lie : ∀ a ∈ gSub, ∀ b ∈ gSub, a * b - b * a ∈ gSub
  /-- the invariant form is nondegenerate on the gauge Lie algebra -/
  ipA_nondeg_g : ∀ x ∈ gSub, (∀ y ∈ gSub, ipA y x = 0) → x = 0
  κ_ne : κ ≠ 0

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable {m : ℕ}

/-! ### The orthogonal projection onto the gauge Lie algebra -/

section GaugeProj

variable [FiniteDimensional ℝ 𝔄] (M : SlabModel 𝔄 𝓗 𝓢 m)

/-- The invariant form restricted to the gauge Lie algebra `𝔤 = gSub`. -/
def SlabModel.gForm : M.gSub →L[ℝ] M.gSub →L[ℝ] ℝ :=
  M.ipA.bilinearComp M.gSub.subtypeL M.gSub.subtypeL

theorem SlabModel.gForm_apply (y x : M.gSub) : M.gForm y x = M.ipA y x := rfl

theorem SlabModel.gForm_nondeg : ∀ x : M.gSub, (∀ y, M.gForm y x = 0) → x = 0 := fun x hx =>
  Subtype.ext (M.ipA_nondeg_g x x.2 fun y hy => hx ⟨y, hy⟩)

/-- The functional `y ↦ ⟨y, x⟩_𝐠` on `𝔤`. -/
def SlabModel.gFun (x : 𝔄) : M.gSub →ₗ[ℝ] ℝ := ((M.ipA.flip x).comp M.gSub.subtypeL).toLinearMap

theorem SlabModel.gFun_apply (x : 𝔄) (y : M.gSub) : M.gFun x y = M.ipA y x := rfl

/-- The projection onto `𝔤` as a linear map into `𝔤`: the Riesz vector of `⟨·, x⟩_𝐠|_𝔤`. -/
def SlabModel.πgL : 𝔄 →ₗ[ℝ] M.gSub where
  toFun x := rieszVec (M.gForm_nondeg) (M.gFun x)
  map_add' x x' := by
    unfold rieszVec
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [SlabModel.gFun_apply, SlabModel.gFun_apply, SlabModel.gFun_apply, map_add, add_smul]
  map_smul' r x := by
    unfold rieszVec
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [SlabModel.gFun_apply, SlabModel.gFun_apply, map_smul, smul_eq_mul, smul_smul,
      RingHom.id_apply]

/-- **The `⟨·,·⟩_𝐠`-orthogonal projection of `𝔄` onto the gauge Lie algebra `𝔤`.** -/
def SlabModel.πg : 𝔄 →L[ℝ] 𝔄 := LinearMap.toContinuousLinearMap (M.gSub.subtype ∘ₗ M.πgL)

theorem SlabModel.πg_mem (x : 𝔄) : M.πg x ∈ M.gSub := (M.πgL x).2

/-- `⟨y, πg x⟩_𝐠 = ⟨y, x⟩_𝐠` for `y ∈ 𝔤`. -/
theorem SlabModel.ipA_πg {y : 𝔄} (hy : y ∈ M.gSub) (x : 𝔄) : M.ipA y (M.πg x) = M.ipA y x :=
  riesz_apply (M.gForm_nondeg) (M.gFun x) ⟨y, hy⟩

/-- `πg` fixes `𝔤`. -/
theorem SlabModel.πg_of_mem {x : 𝔄} (hx : x ∈ M.gSub) : M.πg x = x := by
  have h := M.ipA_nondeg_g (M.πg x - x) (M.gSub.sub_mem (M.πg_mem x) hx) fun y hy => by
    rw [map_sub, M.ipA_πg hy, sub_self]
  exact sub_eq_zero.1 h

theorem SlabModel.πg_πg (x : 𝔄) : M.πg (M.πg x) = M.πg x := M.πg_of_mem (M.πg_mem x)

/-- `πg` is `⟨·,·⟩_𝐠`-self-adjoint. -/
theorem SlabModel.ipA_πg_symm (x y : 𝔄) : M.ipA (M.πg x) y = M.ipA x (M.πg y) := by
  rw [← M.ipA_πg (M.πg_mem x) y, M.ipA_symm x, ← M.ipA_πg (M.πg_mem y) x, M.ipA_symm]

end GaugeProj

/-! ### The Higgs space as a Lie module over `gl(m)` -/

/-- The Higgs space of a slab model, as a Lie module over `MatLie m`. -/
def HSp (_M : SlabModel 𝔄 𝓗 𝓢 m) : Type _ := 𝓗

namespace HSp

variable (M : SlabModel 𝔄 𝓗 𝓢 m)

instance : NormedAddCommGroup (HSp M) := inferInstanceAs (NormedAddCommGroup 𝓗)
instance : NormedSpace ℝ (HSp M) := inferInstanceAs (NormedSpace ℝ 𝓗)
instance [FiniteDimensional ℝ 𝓗] : FiniteDimensional ℝ (HSp M) :=
  inferInstanceAs (FiniteDimensional ℝ 𝓗)

instance : LieRingModule (MatLie m) (HSp M) where
  bracket X v := (M.ρH (M.φ.symm X) : 𝓗 →L[ℝ] 𝓗) (show 𝓗 from v)
  add_lie X Y v := by
    show (M.ρH (M.φ.symm (X + Y)) : 𝓗 →L[ℝ] 𝓗) _ = _
    rw [map_add, map_add]; rfl
  lie_add X v w := map_add _ _ _
  leibniz_lie X Y v := by
    show (M.ρH (M.φ.symm X) : 𝓗 →L[ℝ] 𝓗) ((M.ρH (M.φ.symm Y) : 𝓗 →L[ℝ] 𝓗) _) =
      (M.ρH (M.φ.symm (X * Y - Y * X)) : 𝓗 →L[ℝ] 𝓗) _ +
        (M.ρH (M.φ.symm Y) : 𝓗 →L[ℝ] 𝓗) ((M.ρH (M.φ.symm X) : 𝓗 →L[ℝ] 𝓗) _)
    have e1 : ∀ (T1 T2 : 𝓗 →L[ℝ] 𝓗) (u : 𝓗), (T1 - T2) u = T1 u - T2 u := fun _ _ _ => rfl
    have e2 : ∀ (T1 T2 : 𝓗 →L[ℝ] 𝓗) (u : 𝓗), (T1 * T2) u = T1 (T2 u) := fun _ _ _ => rfl
    rw [map_sub, map_mul, map_mul, map_sub, map_mul, map_mul, e1, e2, e2]
    abel

instance : LieModule ℝ (MatLie m) (HSp M) where
  smul_lie t X v := by
    show (M.ρH (M.φ.symm (t • X)) : 𝓗 →L[ℝ] 𝓗) _ = t • _
    rw [map_smul, map_smul]; rfl
  lie_smul t X v := map_smul _ _ _

theorem lie_def (X : MatLie m) (v : HSp M) :
    ⁅X, v⁆ = (M.ρH (M.φ.symm X) : 𝓗 →L[ℝ] 𝓗) (show 𝓗 from v) := rfl

theorem lie_def' (X : MatLie m) (v : 𝓗) :
    (⁅X, (v : HSp M)⁆ : HSp M) = (M.ρH (M.φ.symm X) : 𝓗 →L[ℝ] 𝓗) v := rfl

theorem lie_def'' (X : MatLie m) (v : HSp M) :
    ⁅X, v⁆ = (M.ρH (M.φ.symm X) : 𝓗 →L[ℝ] 𝓗) v := rfl

end HSp

/-! ### The slab Dirac blocks -/

/-- Continuous linear operators as linear endomorphisms (an algebra homomorphism). -/
def toEndAlg : (𝓢 →L[ℝ] 𝓢) →ₐ[ℝ] Module.End ℝ 𝓢 where
  toRingHom := ContinuousLinearMap.toLinearMapRingHom
  commutes' r := by ext x; simp [Algebra.algebraMap_eq_smul_one]

theorem toEndAlg_apply (T : 𝓢 →L[ℝ] 𝓢) (x : 𝓢) : toEndAlg T x = T x := rfl

/-- The transposition `T ↦ (Ψ̄ ↦ Ψ̄ ∘ T)` on co-spinors (an algebra anti-homomorphism). -/
def transL : (𝓢 →L[ℝ] 𝓢) →ₗ[ℝ] Module.End ℝ (CoSpinor 𝓢) where
  toFun T := ((ContinuousLinearMap.compL ℝ 𝓢 𝓢 ℂ).flip T).toLinearMap
  map_add' S T := by ext φ x; simp
  map_smul' r T := by ext φ x; simp

theorem transL_apply (T : 𝓢 →L[ℝ] 𝓢) (φ : CoSpinor 𝓢) : transL T φ = φ.comp T := rfl

theorem transL_one : transL (1 : 𝓢 →L[ℝ] 𝓢) = 1 := by ext φ x; simp [transL_apply]

theorem transL_mul (S T : 𝓢 →L[ℝ] 𝓢) : transL (S * T) = transL T * transL S := by
  ext φ x; simp [transL_apply]

variable (M : SlabModel 𝔄 𝓗 𝓢 m)

/-- The gauge action of `gl(m)` on spinors, `X ↦ ρ_S(φ⁻¹X)`. -/
def rhoSL : MatLie m →ₗ[ℝ] (𝓢 →L[ℝ] 𝓢) :=
  M.ρS.toLinearMap.comp M.φ.symm.toLinearMap

theorem rhoSL_apply (X : MatLie m) : rhoSL M X = M.ρS (M.φ.symm X) := rfl

theorem rhoSL_lie (X Y : MatLie m) :
    rhoSL M ⁅X, Y⁆ = rhoSL M X * rhoSL M Y - rhoSL M Y * rhoSL M X := by
  simp only [rhoSL_apply, Ring.lie_def, map_sub, map_mul]

/-- The Yukawa map on the Higgs Lie module. -/
def yukL : HSp M →ₗ[ℝ] (𝓢 →L[ℝ] 𝓢) where
  toFun w := M.yukawa (show 𝓗 from w)
  map_add' v w := map_add M.yukawa (show 𝓗 from v) w
  map_smul' r v := map_smul M.yukawa r (show 𝓗 from v)

theorem yukL_apply (w : HSp M) : yukL M w = M.yukawa (show 𝓗 from w) := rfl

theorem gamma_comm_rhoS (A : 𝔄) (a : Fin 4) :
    M.ρS A * (slabCliff M.toModel).c a = (slabCliff M.toModel).c a * M.ρS A := by
  rw [slabCliff_c, mul_smul_comm, smul_mul_assoc]
  congr 1
  rw [← mul_assoc, ← M.J_rhoS, mul_assoc, M.gauge_cliff, ← mul_assoc]

theorem yukawa_comm_JJ (w : 𝓗) (c d : Fin 4) :
    M.yukawa w * (M.J * M.γ c * (M.J * M.γ d)) = M.J * M.γ c * (M.J * M.γ d) * M.yukawa w := by
  have hJ : M.J * M.γ c * (M.J * M.γ d) = M.J * M.J * (M.γ c * M.γ d) := by
    rw [mul_assoc M.J (M.γ c), ← mul_assoc (M.γ c), ← M.J_gamma c]; noncomm_ring
  rw [hJ]
  have hY : M.yukawa w * (M.J * M.J) = M.J * M.J * M.yukawa w := by
    rw [← mul_assoc, ← M.J_yukawa, mul_assoc, ← M.J_yukawa, mul_assoc]
  calc M.yukawa w * (M.J * M.J * (M.γ c * M.γ d)) =
        M.yukawa w * (M.J * M.J) * (M.γ c * M.γ d) := by noncomm_ring
    _ = M.J * M.J * (M.yukawa w * (M.γ c * M.γ d)) := by rw [hY]; noncomm_ring
    _ = M.J * M.J * (M.γ c * M.γ d * M.yukawa w) := by rw [M.yukawa_cl]
    _ = M.J * M.J * (M.γ c * M.γ d) * M.yukawa w := by noncomm_ring

theorem yukawa_comm_cc (w : 𝓗) (c d : Fin 4) :
    M.yukawa w * ((slabCliff M.toModel).c c * (slabCliff M.toModel).c d) =
      (slabCliff M.toModel).c c * (slabCliff M.toModel).c d * M.yukawa w := by
  simp only [slabCliff_c, smul_mul_smul_comm]
  rw [mul_smul_comm, smul_mul_assoc, yukawa_comm_JJ]

/-- **The slab Dirac block on spinors**: Clifford frame `c_a = ε_aJγ^a`, gauge action `ρ_S∘φ⁻¹`,
mass map `𝓜 = 0 + 𝓜_𝐘`. -/
def diracD : DiracData (MatLie m) (HSp M) 𝓢 where
  Fr := cliffMap (slabCliff M.toModel) toEndAlg
  ρ := toEndAlg.toLinearMap.comp (rhoSL M)
  ρ_lie X Y := by
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, rhoSL_lie, map_sub, map_mul]
  m0 := 0
  L := toEndAlg.toLinearMap.comp (yukL M)
  lorentz := slabCliff_lorentzian M.toModel
  comm X b := by
    show toEndAlg (rhoSL M X) * toEndAlg ((slabCliff M.toModel).c b) =
      toEndAlg ((slabCliff M.toModel).c b) * toEndAlg (rhoSL M X)
    rw [← map_mul, ← map_mul, rhoSL_apply, gamma_comm_rhoS]
  mass_cl w c d := by
    show (0 + toEndAlg (yukL M w)) * (toEndAlg ((slabCliff M.toModel).c c) *
        toEndAlg ((slabCliff M.toModel).c d)) =
      toEndAlg ((slabCliff M.toModel).c c) * toEndAlg ((slabCliff M.toModel).c d) *
        (0 + toEndAlg (yukL M w))
    simp only [zero_add, ← map_mul, yukL_apply]
    exact congrArg _ (yukawa_comm_cc M w c d)
  mass_eq X w := by
    show toEndAlg (rhoSL M X) * (0 + toEndAlg (yukL M w)) -
        (0 + toEndAlg (yukL M w)) * toEndAlg (rhoSL M X) = toEndAlg (yukL M ⁅X, w⁆)
    simp only [zero_add, ← map_mul, ← map_sub, rhoSL_apply, yukL_apply]
    exact congrArg _ (M.yukawa_eq (M.φ.symm X) w)

/-- The co-spinor gauge action `X ↦ -(·∘ρ_S(φ⁻¹X))`. -/
def negRho : MatLie m →ₗ[ℝ] Module.End ℝ (CoSpinor 𝓢) where
  toFun X := -transL (rhoSL M X)
  map_add' X Y := by ext φ x; simp [transL_apply, add_comm]
  map_smul' r X := by ext φ x; simp [transL_apply]

theorem negRho_apply (X : MatLie m) : negRho M X = -transL (rhoSL M X) := rfl



/-- The co-spinor mass map `w ↦ -(·∘𝓜_𝐘(w))`. -/
def negYuk : HSp M →ₗ[ℝ] Module.End ℝ (CoSpinor 𝓢) where
  toFun w := -transL (yukL M w)
  map_add' X Y := by ext φ x; simp [transL_apply, add_comm]
  map_smul' r X := by ext φ x; simp [transL_apply]

theorem negYuk_apply (w : HSp M) : negYuk M w = -transL (yukL M w) := rfl

/-- **The slab Dirac block on co-spinors**: Clifford frame `c̄_aΨ̄ = Ψ̄∘c_a`, gauge action
`-(·∘ρ_S)`, mass map `-(·∘𝓜_𝐘)`. -/
def diracDb : DiracData (MatLie m) (HSp M) (CoSpinor 𝓢) where
  Fr := cliffAnti (slabCliff M.toModel) transL transL_one transL_mul
  ρ := negRho M
  ρ_lie X Y := by
    ext φ x
    simp [negRho_apply, transL_apply, rhoSL_lie]
  m0 := 0
  L := negYuk M
  lorentz := slabCliff_lorentzian M.toModel
  comm X b := by
    ext φ x
    have h := congrArg (fun T => φ (T x)) (gamma_comm_rhoS M (M.φ.symm X) b)
    simp only [ContinuousLinearMap.mul_apply] at h
    simp [cliffAnti, negRho_apply, transL_apply, rhoSL_apply, h]
  mass_cl w c d := by
    ext φ x
    have h := congrArg (fun T => φ (T x)) (yukawa_comm_cc M w d c)
    simp only [ContinuousLinearMap.mul_apply] at h
    simp [cliffAnti, negYuk_apply, transL_apply, yukL_apply, SpinorProlongation.mass, h]
  mass_eq X w := by
    simp only [SpinorProlongation.mass, zero_add, negYuk_apply, negRho_apply]
    have h := M.yukawa_eq (M.φ.symm X) (show 𝓗 from w)
    ext φ x
    have h2 := congrArg (fun T => φ (T x)) h
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, map_sub] at h2
    have h3 : φ ((M.yukawa (show 𝓗 from (⁅X, w⁆ : HSp M))) x) =
        φ ((M.ρS (M.φ.symm X)) ((M.yukawa w) x)) - φ ((M.yukawa w) ((M.ρS (M.φ.symm X)) x)) :=
      h2.symm
    simp [transL_apply, yukL_apply, rhoSL_apply]
    linear_combination h3

/-! ### The currents, sources and stress of the native Lagrangian in slab variables -/

/-- The coordinate gamma matrices `γ^ν = Σ_a e_a{}^ν γ^a` in the smoothed adapted frame. -/
def gamU (δ : ℝ) (gi : Fin 4 → Fin 4 → ℝ) (ν : Fin 4) : 𝓢 →L[ℝ] 𝓢 :=
  ∑ a, frUs δ gi a ν • M.γ a

/-- The gauge-current functional `x ↦ -j(single ν x)/v` of the native Lagrangian (Higgs and Dirac
currents), in slab variables. -/
def curVal (δ : ℝ) (gi : Fin 4 → Fin 4 → ℝ) (H : 𝓗) (DH : Fin 4 → 𝓗) (ψ : 𝓢)
    (ψb : CoSpinor 𝓢) (ν : Fin 4) (x : 𝔄) : ℝ :=
  ∑ μ, gi ν μ * M.hermH (M.ρH x H) (DH μ) + ∑ μ, gi μ ν * M.hermH (DH μ) (M.ρH x H) -
    (Complex.I / 2 * (ψb (gamU M δ gi ν (M.ρS x ψ)) + ψb (M.ρS x (gamU M δ gi ν ψ)))).re

theorem re_I2_smul (r : ℝ) (a b : ℂ) :
    (Complex.I / 2 * ((r : ℂ) * a) + Complex.I / 2 * ((r : ℂ) * b)).re =
      r * (Complex.I / 2 * a + Complex.I / 2 * b).re := by
  rw [show Complex.I / 2 * ((r : ℂ) * a) + Complex.I / 2 * ((r : ℂ) * b) =
    (r : ℂ) * (Complex.I / 2 * a + Complex.I / 2 * b) by ring, Complex.re_ofReal_mul]

/-- `curVal` is linear in the gauge direction. -/
def curValL (δ : ℝ) (gi : Fin 4 → Fin 4 → ℝ) (H : 𝓗) (DH : Fin 4 → 𝓗) (ψ : 𝓢)
    (ψb : CoSpinor 𝓢) (ν : Fin 4) : 𝔄 →ₗ[ℝ] ℝ where
  toFun := curVal M δ gi H DH ψ ψb ν
  map_add' x y := by
    simp only [curVal, map_add, ContinuousLinearMap.add_apply, mul_add, Finset.sum_add_distrib,
      Complex.add_re, ContinuousLinearMap.map_add]
    ring
  map_smul' r x := by
    simp only [curVal, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, RingHom.id_apply,
      Complex.real_smul, mul_add]
    rw [re_I2_smul]
    simp only [Finset.mul_sum, mul_sub, mul_add]
    congr 1
    congr 1 <;> exact Finset.sum_congr rfl fun μ _ => by ring

variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]

/-- **The Yang–Mills current** of the native Lagrangian in slab variables: the `𝔤`-component
`J_σ = g_{σν} πg R⁻¹(curVal_ν)` of the represented matter current, transported to `gl(m)` by `φ`
(`R` the Riesz map of `⟨·,·⟩_𝐠`, `πg` the orthogonal projection onto the gauge Lie algebra; the
gauge field and its test directions live in `𝔤`). -/
def Jcur (δ : ℝ) (g gi : Fin 4 → Fin 4 → ℝ) (H : HSp M) (DH : Fin 4 → HSp M) (ψ : 𝓢)
    (ψb : CoSpinor 𝓢) (σ : Fin 4) : MatLie m :=
  ∑ ν, g σ ν • M.φ (M.πg (rieszVec M.ipA_nondeg (curVal M δ gi H DH ψ ψb ν)))

/-- The Higgs source functional `η ↦ DV(H)[η] + Re Ψ̄𝓜_𝐘(η)Ψ`. -/
def srcVal (H : 𝓗) (ψ : 𝓢) (ψb : CoSpinor 𝓢) (η : 𝓗) : ℝ :=
  M.lamH * (2 * (M.hermH H H - M.vH ^ 2) * (M.hermH η H + M.hermH H η)) +
    (ψb (M.yukawa η ψ)).re

def srcValL (H : 𝓗) (ψ : 𝓢) (ψb : CoSpinor 𝓢) : 𝓗 →ₗ[ℝ] ℝ where
  toFun := srcVal M H ψ ψb
  map_add' x y := by
    simp only [srcVal, map_add, ContinuousLinearMap.add_apply, Complex.add_re]; ring
  map_smul' r x := by
    simp only [srcVal, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, RingHom.id_apply,
      Complex.real_smul, Complex.re_ofReal_mul]
    ring

/-- **The Higgs source** of the native Lagrangian: `S_H = ½R_H⁻¹(srcVal)`, i.e.
`2⟨η, S_H⟩ = DV(H)[η] + Re Ψ̄𝓜_𝐘(η)Ψ`. -/
def SH (H : HSp M) (ψ : 𝓢) (ψb : CoSpinor 𝓢) : HSp M :=
  (1 / 2 : ℝ) • rieszVec M.hermH_nondeg (srcVal M H ψ ψb)

/-- The unsymmetrised frame Dirac-stress kernel
`P_{ABC}(Ψ̄, x) = η_{AB}Re((i/2)Ψ̄γ^Cx) - δ_{AC}η_{BB}Re((i/2)Ψ̄γ^Bx)`. -/
def Pu (A B C : Fin 4) (φ : CoSpinor 𝓢) (x : 𝓢) : ℝ :=
  eta A B * (Complex.I / 2 * φ (M.γ C x)).re -
    (if A = C then eta B B else 0) * (Complex.I / 2 * φ (M.γ B x)).re

/-- The symmetrised kernel as a bilinear map. -/
def Ps (A B C : Fin 4) : CoSpinor 𝓢 →ₗ[ℝ] 𝓢 →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun φ x => (1 / 2 : ℝ) * (Pu M A B C φ x + Pu M B A C φ x))
    (fun φ φ' x => by
      simp only [Pu, ContinuousLinearMap.add_apply, mul_add, Complex.add_re]; ring)
    (fun r φ x => by
      simp only [Pu, ContinuousLinearMap.smul_apply, smul_eq_mul, Complex.real_smul,
        Complex.re_ofReal_mul]
      rw [show Complex.I / 2 * ((r : ℂ) * φ (M.γ C x)) = (r : ℂ) * (Complex.I / 2 * φ (M.γ C x))
        by ring, show Complex.I / 2 * ((r : ℂ) * φ (M.γ B x)) =
          (r : ℂ) * (Complex.I / 2 * φ (M.γ B x)) by ring,
        show Complex.I / 2 * ((r : ℂ) * φ (M.γ A x)) = (r : ℂ) * (Complex.I / 2 * φ (M.γ A x))
          by ring, Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
      ring)
    (fun φ x x' => by
      simp only [Pu, map_add, Complex.add_re, mul_add]; ring)
    (fun r φ x => by
      simp only [Pu, map_smul, smul_eq_mul, Complex.real_smul, Complex.re_ofReal_mul]
      rw [show Complex.I / 2 * ((r : ℂ) * φ (M.γ C x)) = (r : ℂ) * (Complex.I / 2 * φ (M.γ C x))
        by ring, show Complex.I / 2 * ((r : ℂ) * φ (M.γ B x)) =
          (r : ℂ) * (Complex.I / 2 * φ (M.γ B x)) by ring,
        show Complex.I / 2 * ((r : ℂ) * φ (M.γ A x)) = (r : ℂ) * (Complex.I / 2 * φ (M.γ A x))
          by ring, Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
      ring)

theorem Ps_apply (A B C : Fin 4) (φ : CoSpinor 𝓢) (x : 𝓢) :
    Ps M A B C φ x = (1 / 2 : ℝ) * (Pu M A B C φ x + Pu M B A C φ x) := rfl

/-- The Yukawa kernel `P''_{AB}(H)(Ψ̄, x) = -η_{AB}Re Ψ̄𝓜_𝐘(H)x`. -/
def Pyuk (A B : Fin 4) (H : HSp M) : CoSpinor 𝓢 →ₗ[ℝ] 𝓢 →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun φ x => -(eta A B * (φ (M.yukawa (show 𝓗 from H) x)).re))
    (fun φ φ' x => by simp only [ContinuousLinearMap.add_apply, Complex.add_re]; ring)
    (fun r φ x => by
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, Complex.real_smul,
        Complex.re_ofReal_mul]; ring)
    (fun φ x x' => by simp only [map_add, Complex.add_re]; ring)
    (fun r φ x => by
      simp only [map_smul, smul_eq_mul, Complex.real_smul, Complex.re_ofReal_mul]; ring)

theorem Pyuk_apply (A B : Fin 4) (H : HSp M) (φ : CoSpinor 𝓢) (x : 𝓢) :
    Pyuk M A B H φ x = -(eta A B * (φ (M.yukawa (show 𝓗 from H) x)).re) := rfl

/-- **The symmetrised native Dirac stress** in frame form:
`T_{AB} = Σ_C (P_{ABC}(Ψ̄, X_C) - P_{ABC}(X̄_C, Ψ)) + P''_{AB}(H)(Ψ̄, Ψ)`. -/
def TD : ActualJetRecon.DiracStressForm 𝓢 (CoSpinor 𝓢) (HSp M) where
  P := Ps M
  P' A B C := -Ps M A B C
  P'' := Pyuk M

/-- **The slab theory data of a slab model** (smoothed adapted frame of margin `δ` in the current). -/
def toSMData (δ : ℝ) : SMData (MatLie m) (HSp M) 𝓢 (CoSpinor 𝓢) where
  Λ := M.Λ
  κ := M.κ
  D := diracD M
  Db := diracDb M
  Jcur := Jcur M δ
  SH := fun _ _ H ψ ψb => SH M H ψ ψb
  ipG := (M.ipA.toLinearMap₁₂ : 𝔄 →ₗ[ℝ] 𝔄 →ₗ[ℝ] ℝ).compl₁₂ M.φ.symm.toLinearMap
    M.φ.symm.toLinearMap
  ipV := (M.hermH.toLinearMap₁₂ : 𝓗 →ₗ[ℝ] 𝓗 →ₗ[ℝ] ℝ)
  lamH := M.lamH
  vH := M.vH
  TD := TD M

/-! ### Smoothness of the slab sources -/

theorem contDiff_phi : ContDiff ℝ ∞ (fun a : 𝔄 => M.φ a) := by
  let L : 𝔄 →L[ℝ] MatLie m := LinearMap.toContinuousLinearMap M.φ.toLinearMap
  exact L.contDiff

theorem contDiff_gamU {δ : ℝ} (hδ : 0 < δ) (ν : Fin 4) :
    ContDiff ℝ ∞ (fun gi : Fin 4 → Fin 4 → ℝ => gamU M δ gi ν) := by
  unfold gamU
  exact ContDiff.sum fun a _ => (contDiff_frUs hδ a ν).smul contDiff_const

/-- **The slab sources are smooth** (`SMSmooth`). -/
theorem toSMData_smooth {δ : ℝ} (hδ : 0 < δ) : SMSmooth (toSMData M δ) where
  J ν := by
    show ContDiff ℝ ∞ (fun p : Met × Met × HSp M × (Fin 4 → HSp M) × 𝓢 × CoSpinor 𝓢 =>
      Jcur M δ p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 ν)
    unfold Jcur
    refine ContDiff.sum fun σ _ => ?_
    have hs : ContDiff ℝ ∞ (fun p : Met × Met × HSp M × (Fin 4 → HSp M) × 𝓢 × CoSpinor 𝓢 =>
        p.1 ν σ) :=
      (contDiff_apply ℝ ℝ σ).comp ((contDiff_apply ℝ (Fin 4 → ℝ) ν).comp contDiff_fst)
    refine hs.smul ((contDiff_phi M).comp ((M.πg).contDiff.comp
      (contDiff_rieszVec M.ipA_nondeg fun i => ?_)))
    · set x := Module.finBasis ℝ 𝔄 i
      have hgi : ContDiff ℝ ∞ (fun p : Met × Met × HSp M × (Fin 4 → HSp M) × 𝓢 × CoSpinor 𝓢 =>
          p.2.1) := contDiff_fst.comp contDiff_snd
      have hG' : ∀ ν', ContDiff ℝ ∞ (fun p : Met × Met × HSp M × (Fin 4 → HSp M) × 𝓢 ×
          CoSpinor 𝓢 => gamU M δ p.2.1 ν') := fun ν' => (contDiff_gamU M hδ ν').comp hgi
      have hH : ContDiff ℝ ∞ (fun p : Met × Met × HSp M × (Fin 4 → HSp M) × 𝓢 × CoSpinor 𝓢 =>
          (show 𝓗 from p.2.2.1)) := contDiff_fst.comp (contDiff_snd.comp contDiff_snd)
      have hDH : ∀ μ, ContDiff ℝ ∞ (fun p : Met × Met × HSp M × (Fin 4 → HSp M) × 𝓢 ×
          CoSpinor 𝓢 => (show 𝓗 from p.2.2.2.1 μ)) := fun μ =>
        (contDiff_apply ℝ (HSp M) μ).comp
          (contDiff_fst.comp (contDiff_snd.comp (contDiff_snd.comp contDiff_snd)))
      have hψ : ContDiff ℝ ∞ (fun p : Met × Met × HSp M × (Fin 4 → HSp M) × 𝓢 × CoSpinor 𝓢 =>
          p.2.2.2.2.1) :=
        contDiff_fst.comp (contDiff_snd.comp (contDiff_snd.comp (contDiff_snd.comp contDiff_snd)))
      have hψb : ContDiff ℝ ∞ (fun p : Met × Met × HSp M × (Fin 4 → HSp M) × 𝓢 × CoSpinor 𝓢 =>
          p.2.2.2.2.2) :=
        contDiff_snd.comp (contDiff_snd.comp (contDiff_snd.comp (contDiff_snd.comp contDiff_snd)))
      have hgij : ∀ a b, ContDiff ℝ ∞ (fun p : Met × Met × HSp M × (Fin 4 → HSp M) × 𝓢 ×
          CoSpinor 𝓢 => p.2.1 a b) := fun a b =>
        (contDiff_apply ℝ ℝ b).comp ((contDiff_apply ℝ (Fin 4 → ℝ) a).comp hgi)
      have hρH : ContDiff ℝ ∞ (fun p : Met × Met × HSp M × (Fin 4 → HSp M) × 𝓢 × CoSpinor 𝓢 =>
          M.ρH x (show 𝓗 from p.2.2.1)) := (M.ρH x).contDiff.comp hH
      unfold curVal
      refine ((ContDiff.sum fun μ _ => (hgij σ μ).mul ((M.hermH.contDiff.comp hρH).clm_apply
        (hDH μ))).add (ContDiff.sum fun μ _ => (hgij μ σ).mul
          ((M.hermH.contDiff.comp (hDH μ)).clm_apply hρH))).sub ?_
      refine Complex.reCLM.contDiff.comp (contDiff_const.mul (ContDiff.add ?_ ?_))
      · exact hψb.clm_apply ((hG' σ).clm_apply ((M.ρS x).contDiff.comp hψ))
      · exact hψb.clm_apply ((M.ρS x).contDiff.comp ((hG' σ).clm_apply hψ))
  SH := by
    show ContDiff ℝ ∞ (fun p : Met × Met × HSp M × 𝓢 × CoSpinor 𝓢 =>
      SH M p.2.2.1 p.2.2.2.1 p.2.2.2.2)
    unfold SH
    refine ContDiff.smul contDiff_const (contDiff_rieszVec M.hermH_nondeg fun i => ?_)
    set η := Module.finBasis ℝ 𝓗 i
    have hH : ContDiff ℝ ∞ (fun p : Met × Met × HSp M × 𝓢 × CoSpinor 𝓢 => (show 𝓗 from p.2.2.1)) :=
      contDiff_fst.comp (contDiff_snd.comp contDiff_snd)
    have hψ : ContDiff ℝ ∞ (fun p : Met × Met × HSp M × 𝓢 × CoSpinor 𝓢 => p.2.2.2.1) :=
      contDiff_fst.comp (contDiff_snd.comp (contDiff_snd.comp contDiff_snd))
    have hψb : ContDiff ℝ ∞ (fun p : Met × Met × HSp M × 𝓢 × CoSpinor 𝓢 => p.2.2.2.2) :=
      contDiff_snd.comp (contDiff_snd.comp (contDiff_snd.comp contDiff_snd))
    unfold srcVal
    have hHH : ContDiff ℝ ∞ (fun p : Met × Met × HSp M × 𝓢 × CoSpinor 𝓢 =>
        M.hermH (show 𝓗 from p.2.2.1) (show 𝓗 from p.2.2.1)) :=
      (M.hermH.contDiff.comp hH).clm_apply hH
    have h1 : ContDiff ℝ ∞ (fun p : Met × Met × HSp M × 𝓢 × CoSpinor 𝓢 =>
        M.hermH η (show 𝓗 from p.2.2.1)) := (M.hermH η).contDiff.comp hH
    have h2 : ContDiff ℝ ∞ (fun p : Met × Met × HSp M × 𝓢 × CoSpinor 𝓢 =>
        M.hermH (show 𝓗 from p.2.2.1) η) := (M.hermH.contDiff.comp hH).clm_apply contDiff_const
    refine (contDiff_const.mul ((contDiff_const.mul (hHH.sub contDiff_const)).mul (h1.add h2))).add
      ?_
    exact Complex.reCLM.contDiff.comp (hψb.clm_apply ((M.yukawa η).contDiff.comp hψ))
  P2 A B := by
    show ContDiff ℝ ∞ (fun p : HSp M × CoSpinor 𝓢 × 𝓢 => Pyuk M A B p.1 p.2.1 p.2.2)
    simp only [Pyuk_apply]
    have hH : ContDiff ℝ ∞ (fun p : HSp M × CoSpinor 𝓢 × 𝓢 => (show 𝓗 from p.1)) := contDiff_fst
    refine (contDiff_const.mul (Complex.reCLM.contDiff.comp ?_)).neg
    exact (contDiff_fst.comp contDiff_snd).clm_apply
      ((M.yukawa.contDiff.comp hH).clm_apply (contDiff_snd.comp contDiff_snd))

end

/-! ### Non-vacuity: the concrete Dirac model as a slab model -/

section Example

open NativeModelExample

/-- The trivial gauge algebra `ℝ` as `gl(1, ℝ)`: `r ↦ r·1`. -/
noncomputable def phi1 : ℝ ≃ₐ[ℝ] MatLie 1 where
  toFun r := (r • (1 : Matrix (Fin 1) (Fin 1) ℝ) : Matrix (Fin 1) (Fin 1) ℝ)
  invFun A := (show Matrix (Fin 1) (Fin 1) ℝ from A) 0 0
  left_inv r := by simp
  right_inv A := by
    show ((show Matrix (Fin 1) (Fin 1) ℝ from A) 0 0 • (1 : Matrix (Fin 1) (Fin 1) ℝ)) =
      (show Matrix (Fin 1) (Fin 1) ℝ from A)
    ext i j
    fin_cases i; fin_cases j
    simp
  map_mul' r s := by
    show (r * s) • (1 : Matrix (Fin 1) (Fin 1) ℝ) =
      (r • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * (s • (1 : Matrix (Fin 1) (Fin 1) ℝ))
    rw [smul_mul_smul_comm, Matrix.one_mul]
  map_add' r s := by
    show (r + s) • (1 : Matrix (Fin 1) (Fin 1) ℝ) =
      r • (1 : Matrix (Fin 1) (Fin 1) ℝ) + s • (1 : Matrix (Fin 1) (Fin 1) ℝ)
    rw [add_smul]
  commutes' r := by
    show r • (1 : Matrix (Fin 1) (Fin 1) ℝ) = algebraMap ℝ (Matrix (Fin 1) (Fin 1) ℝ) r
    rw [Algebra.algebraMap_eq_smul_one]

/-- **The concrete native model of `NativeModelExample` is a slab model** (trivial gauge algebra
`gl(1)`, zero Yukawa map). -/
noncomputable def diracSlab : SlabModel ℝ ℝ Sp 1 where
  toModel := diracModel
  φ := phi1
  yukawa_cl H a b := by simp [diracModel]
  yukawa_eq A H := by simp [diracModel]
  gSub := ⊥
  gLie_eq := by simp [diracModel]
  gSub_lie a ha b hb := by
    rw [Submodule.mem_bot] at ha hb ⊢
    simp [ha, hb]
  ipA_nondeg_g x hx _ := (Submodule.mem_bot ℝ).1 hx
  κ_ne := by simp [diracModel]

example : SMSmooth (toSMData diracSlab 1) := toSMData_smooth diracSlab one_pos

end Example

end RenewalGeometry.SlabData
