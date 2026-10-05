/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.ActualJetSmoothness
import RenewalGeometry.Continuum.SlabMoserComposition

/-!
# The derivative-counted complete forcing bound (`lem:actual-jet-complete-forcing`)

Einstein–Standard-Model action-closure manuscript, `lem:actual-jet-complete-forcing`
(`eq:actual-jet-complete-forcing`): "Fix `k ≥ 4` and an actual-jet `H^k` ball with the stated chart
and foliation margins.  Let `𝓕_err` denote the sum of the residual and gauge-forcing terms on the
right of `eq:actual-jet-writer`.  Then
`‖𝓕_err‖_{H^k_x} ≤ C_M(‖R_B‖_{H^k} + ‖R_D‖_{H^{k+1}} + ‖C‖_{H^{k+1}} + ‖∂_tC‖_{H^k})`."

The forcing `𝓕_err = 𝓑(𝒰)(𝓔^{tr}, r^A, r_H, r_D, r̄_D) + Σ_j 𝒬^j(g)∂_j(r_D, r̄_D) + 𝔊(𝒰; C, ∂C)` is the
one of `ActualJetSystem.actual_jet_writer` (`Bsys`, `Qsys`, and the gauge forcing
`𝒥_C C + 𝒥_C^0∂_tC + Σ_j𝒥_C^j∂_jC` of `Gsys`), on the realized state space of
`ActualJetSmooth` (gauge algebra `gl(m, ℝ)`, finite-dimensional normed Higgs and spinor spaces).

* `Bsys_linear` — `𝓑(𝒰)` is linear in the residuals: the bosonic part (`BmL`) and the
  undifferentiated Dirac part (`DmL`); `QmL`, `GcL`, `G0L`, `GjL` — the differentiated Dirac
  residual and gauge-forcing coefficients as linear maps.
* `isOpen_chart` — the Lorentzian chart is open.
* **`actual_jet_complete_forcing`** — for `k ≥ 4` on `𝕋³`, every compact chart margin `K` and
  `H^k` radius `R`, there is `C_M` such that for every smooth periodic state field (any linear
  coordinates) with values in `K` on the slab and `‖𝒰(t)‖²_{H^k} ≤ R²`, every smooth periodic
  residual field and harmonic-defect field, each coordinate of `𝓕_err` satisfies
  `Q_k(𝓕_err) ≤ C_M (Σ Q_k(R_B) + Σ Q_{k+1}(R_D) + Σ Q_{k+1}(C) + Σ Q_k(∂_tC))`
  (squared form of `eq:actual-jet-complete-forcing`; the norms of vector fields are the component
  norms in the chosen coordinates).

Disclosed: `R_B = (𝓔^{tr}, r^A, r_H)` (the trace-reversed Einstein residual, related to the
Einstein row by the invertible trace reversal); the chart margin is a compact subset of the open
Lorentzian chart containing the slab values of the state.
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.ActualJetCompleteForcing

open RenewalGeometry ActualJetSystem ActualJetFrame ActualJetWriter HarmonicDefect FrameCurvature
  ActualJetRecon ActualJetGauge SpinorProlongation TwistedHalfRicci ActualJetSpinor ActualJetSmooth

set_option linter.unusedSectionVars false

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

/-- The coordinates of a state. -/
def toP (U : State (MatLie m) V S S') : StateP m V S S' :=
  ((U.g, U.p, U.q), (U.A, U.E, U.B, U.H, U.Pm, U.Q, U.ψ, U.X, U.ψb, U.Xb))

theorem toP_ofP (x : StateP m V S S') : toP (ofP x) = x := rfl

/-- The bosonic residuals `(𝓔^{tr}, r^A, r_H)`. -/
abbrev BosP (m : ℕ) (V : Type*) := Met × (Fin 4 → MatLie m) × V

theorem isOpen_chart : IsOpen {x : StateP m V S S' | MetChart x.1} := by
  have hdet : Continuous fun x : StateP m V S S' => (Matrix.of x.1.1).det :=
    Continuous.matrix_det (A := fun x : StateP m V S S' => Matrix.of x.1.1)
      (continuous_fst.comp continuous_fst)
  have h1 : IsOpen {x : StateP m V S S' | (Matrix.of x.1.1).det ≠ 0} :=
    isOpen_ne_fun hdet continuous_const
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hc : ContinuousAt (fun y : StateP m V S S' => ginvOf y.1.1) x := by
    have : ContDiffAt ℝ ∞ (fun y : StateP m V S S' => ginvOf y.1.1) x :=
      ContDiffAt.ginvOf_fun (by fun_prop) hx.1
    exact this.continuousAt
  have h2 : ∀ᶠ y in 𝓝 x, IsLorChart (ginvOf y.1.1) := eventually_chart hc hx.2
  filter_upwards [h1.mem_nhds hx.1, h2] with y hy1 hy2
  exact ⟨hy1, hy2⟩

section Linear

variable (SM : SMData (MatLie m) V S S')

theorem stressRes_add (D : DiracStressForm S S' V) (g : Fin 4 → Fin 4 → ℝ) (ε : Fin 4 → ℝ)
    (e : Fin 4 → Fin 4 → ℝ) (ψ : S) (ψb : S') (k k' : S) (kb kb' : S') (μ ν : Fin 4) :
    D.stressRes g ε e ψ ψb (k + k') (kb + kb') μ ν =
      D.stressRes g ε e ψ ψb k kb μ ν + D.stressRes g ε e ψ ψb k' kb' μ ν := by
  unfold DiracStressForm.stressRes
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun B _ => ?_
  simp only [map_add, LinearMap.add_apply]
  ring

theorem stressRes_smul (D : DiracStressForm S S' V) (g : Fin 4 → Fin 4 → ℝ) (ε : Fin 4 → ℝ)
    (e : Fin 4 → Fin 4 → ℝ) (ψ : S) (ψb : S') (c : ℝ) (k : S) (kb : S') (μ ν : Fin 4) :
    D.stressRes g ε e ψ ψb (c • k) (c • kb) μ ν = c * D.stressRes g ε e ψ ψb k kb μ ν := by
  unfold DiracStressForm.stressRes
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun B _ => ?_
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem traceRev_add' (g gi : Fin 4 → Fin 4 → ℝ) (T T' : Fin 4 → Fin 4 → ℝ) (μ ν : Fin 4) :
    traceRev g gi (fun a b => T a b + T' a b) μ ν = traceRev g gi T μ ν + traceRev g gi T' μ ν := by
  unfold traceRev trG
  simp only [mul_add, Finset.sum_add_distrib]
  ring

theorem traceRev_smul' (g gi : Fin 4 → Fin 4 → ℝ) (c : ℝ) (T : Fin 4 → Fin 4 → ℝ) (μ ν : Fin 4) :
    traceRev g gi (fun a b => c * T a b) μ ν = c * traceRev g gi T μ ν := by
  unfold traceRev trG
  have h : ∑ a, ∑ b, gi a b * (c * T a b) = c * ∑ a, ∑ b, gi a b * T a b := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [h]; ring

theorem frT2_add (e : Fin 4 → Fin 4 → ℝ) (T T' : Fin 4 → Fin 4 → ℝ) (a b : Fin 4) :
    frT2 e (fun x y => T x y + T' x y) a b = frT2 e T a b + frT2 e T' a b := by
  unfold frT2
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ν _ => by ring

theorem frT2_smul (e : Fin 4 → Fin 4 → ℝ) (c : ℝ) (T : Fin 4 → Fin 4 → ℝ) (a b : Fin 4) :
    frT2 e (fun x y => c * T x y) a b = c * frT2 e T a b := by
  unfold frT2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun ν _ => by ring

variable {S₀ : Type*} [NormedAddCommGroup S₀] [NormedSpace ℝ S₀] [FiniteDimensional ℝ S₀]

/-- The residual multiplier of the prolonged rows is linear in `(r_D, 𝓔^{tr}, T₁)`. -/
theorem XrowB_add (D : DiracData (MatLie m) V S₀) (κ : ℝ) (g gi : Fin 4 → Fin 4 → ℝ)
    (dg : Fin 4 → Fin 4 → Fin 4 → ℝ) (AF : AdaptedFrame) (de : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (A : Fin 4 → MatLie m) (ψ : S₀) (a : Fin 4) (rD rD' : S₀) (E E' T T' : Fin 4 → Fin 4 → ℝ) :
    XrowB D κ g gi dg AF de A ψ a (rD + rD') (fun x y => E x y + E' x y)
        (fun x y => T x y + T' x y) =
      XrowB D κ g gi dg AF de A ψ a rD E T + XrowB D κ g gi dg AF de A ψ a rD' E' T' := by
  have hc : ∀ b : Fin 4, (lorentzSign b * (frT2 AF.fr (fun x y => E x y + E' x y) a b -
      κ * frT2 AF.fr (traceRev g gi fun x y => T x y + T' x y) a b)) • D.Fr.c b =
      (lorentzSign b * (frT2 AF.fr E a b - κ * frT2 AF.fr (traceRev g gi T) a b)) • D.Fr.c b +
      (lorentzSign b * (frT2 AF.fr E' a b - κ * frT2 AF.fr (traceRev g gi T') a b)) • D.Fr.c b := by
    intro b
    rw [← add_smul]
    congr 1
    have : (traceRev g gi fun x y => T x y + T' x y) =
        fun x y => traceRev g gi T x y + traceRev g gi T' x y := by
      funext x y; exact traceRev_add' g gi T T' x y
    rw [this, frT2_add, frT2_add]
    ring
  unfold XrowB
  simp only [hc, Finset.sum_add_distrib, smul_add, add_smul]
  abel

theorem XrowB_smul (D : DiracData (MatLie m) V S₀) (κ : ℝ) (g gi : Fin 4 → Fin 4 → ℝ)
    (dg : Fin 4 → Fin 4 → Fin 4 → ℝ) (AF : AdaptedFrame) (de : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (A : Fin 4 → MatLie m) (ψ : S₀) (a : Fin 4) (c : ℝ) (rD : S₀) (E T : Fin 4 → Fin 4 → ℝ) :
    XrowB D κ g gi dg AF de A ψ a (c • rD) (fun x y => c * E x y) (fun x y => c * T x y) =
      c • XrowB D κ g gi dg AF de A ψ a rD E T := by
  have hc : ∀ b : Fin 4, (lorentzSign b * (frT2 AF.fr (fun x y => c * E x y) a b -
      κ * frT2 AF.fr (traceRev g gi fun x y => c * T x y) a b)) • D.Fr.c b =
      c • ((lorentzSign b * (frT2 AF.fr E a b - κ * frT2 AF.fr (traceRev g gi T) a b)) •
        D.Fr.c b) := by
    intro b
    rw [smul_smul]
    congr 1
    have : (traceRev g gi fun x y => c * T x y) = fun x y => c * traceRev g gi T x y := by
      funext x y; exact traceRev_smul' g gi c T x y
    rw [this, frT2_smul, frT2_smul]
    ring
  unfold XrowB
  simp only [hc]
  rw [← Finset.smul_sum]
  simp only [Module.End.smul_def, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum,
    smul_add, smul_sub, smul_neg, Finset.smul_sum]
  simp only [smul_comm c]

end Linear

section LinearMaps

variable (SM : SMData (MatLie m) V S S')

theorem XrowB_add'' {S₀ : Type*} [NormedAddCommGroup S₀] [NormedSpace ℝ S₀] [FiniteDimensional ℝ S₀]
    (D : DiracData (MatLie m) V S₀) (κ : ℝ) (g gi : Fin 4 → Fin 4 → ℝ)
    (dg : Fin 4 → Fin 4 → Fin 4 → ℝ) (AF : AdaptedFrame) (de : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (A : Fin 4 → MatLie m) (ψ : S₀) (a : Fin 4) (rD rD' : S₀) (E E' T T' : Fin 4 → Fin 4 → ℝ) :
    XrowB D κ g gi dg AF de A ψ a (rD + rD') (E + E') (T + T') =
      XrowB D κ g gi dg AF de A ψ a rD E T + XrowB D κ g gi dg AF de A ψ a rD' E' T' :=
  XrowB_add D κ g gi dg AF de A ψ a rD rD' E E' T T'

theorem XrowB_smul'' {S₀ : Type*} [NormedAddCommGroup S₀] [NormedSpace ℝ S₀]
    [FiniteDimensional ℝ S₀] (D : DiracData (MatLie m) V S₀) (κ : ℝ) (g gi : Fin 4 → Fin 4 → ℝ)
    (dg : Fin 4 → Fin 4 → Fin 4 → ℝ) (AF : AdaptedFrame) (de : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (A : Fin 4 → MatLie m) (ψ : S₀) (a : Fin 4) (c : ℝ) (rD : S₀) (E T : Fin 4 → Fin 4 → ℝ) :
    XrowB D κ g gi dg AF de A ψ a (c • rD) (c • E) (c • T) =
      c • XrowB D κ g gi dg AF de A ψ a rD E T :=
  XrowB_smul D κ g gi dg AF de A ψ a c rD E T

theorem stressR_add (fj : FirstJet (MatLie m) V S S') (r r' : ResP m V S S') :
    stressR SM fj (ofR (r + r')) = stressR SM fj (ofR r) + stressR SM fj (ofR r') := by
  funext μ ν
  simp only [stressR, ofR, Prod.fst_add, Prod.snd_add, Pi.add_apply, smul_add, map_add]
  exact stressRes_add _ _ _ _ _ _ _ _ _ _ μ ν

theorem stressR_smul (fj : FirstJet (MatLie m) V S S') (c : ℝ) (r : ResP m V S S') :
    stressR SM fj (ofR (c • r)) = c • stressR SM fj (ofR r) := by
  funext μ ν
  simp only [stressR, ofR, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
  rw [smul_comm (SM.D.Fr.c 0) c, smul_comm (SM.Db.Fr.c 0) c]
  exact stressRes_smul _ _ _ _ _ _ _ _ _ μ ν

theorem traceRev_addF (g gi : Fin 4 → Fin 4 → ℝ) (T T' : Fin 4 → Fin 4 → ℝ) (μ ν : Fin 4) :
    traceRev g gi (T + T') μ ν = traceRev g gi T μ ν + traceRev g gi T' μ ν :=
  traceRev_add' g gi T T' μ ν

theorem traceRev_smulF (g gi : Fin 4 → Fin 4 → ℝ) (c : ℝ) (T : Fin 4 → Fin 4 → ℝ) (μ ν : Fin 4) :
    traceRev g gi (c • T) μ ν = c * traceRev g gi T μ ν :=
  traceRev_smul' g gi c T μ ν

/-- `𝓑(𝒰)` is additive in the residuals. -/
theorem toP_Bsys_add (x : StateP m V S S') (r r' : ResP m V S S') :
    toP (Bsys SM (ofP x) (ofR (r + r'))) =
      toP (Bsys SM (ofP x) (ofR r)) + toP (Bsys SM (ofP x) (ofR r')) := by
  simp only [Bsys]
  rw [stressR_add]
  ext <;> simp only [toP, ofR, Prod.fst_add, Prod.snd_add, Pi.add_apply, Prod.mk_add_mk,
    smul_add, map_add, traceRev_addF, XrowB_add'', Finset.sum_add_distrib, neg_add, add_zero,
    Pi.zero_apply] <;> ring_nf

set_option linter.unusedTactic false in
/-- `𝓑(𝒰)` is homogeneous in the residuals. -/
theorem toP_Bsys_smul (x : StateP m V S S') (c : ℝ) (r : ResP m V S S') :
    toP (Bsys SM (ofP x) (ofR (c • r))) = c • toP (Bsys SM (ofP x) (ofR r)) := by
  simp only [Bsys]
  rw [stressR_smul]
  ext <;> simp only [toP, ofR, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, Prod.smul_mk,
    smul_eq_mul, map_smul, traceRev_smulF, XrowB_smul'', Finset.smul_sum, smul_zero,
    smul_neg, smul_sub, mul_sub, mul_neg, neg_mul, Module.End.smul_def, smul_smul] <;>
    first | (ring_nf; done) | (module; done) |
      (congr 1; exact Finset.sum_congr rfl fun i _ => by congr 1; ring) | skip

end LinearMaps

section Forcing

variable (SM : SMData (MatLie m) V S S')

/-- Bosonic residuals as residual coordinates. -/
def bosR (y : BosP m V) : ResP m V S S' := (y.1, y.2.1, y.2.2, 0, 0)

/-- Dirac residuals as residual coordinates. -/
def dirR (z : S × S') : ResP m V S S' := (0, 0, 0, z.1, z.2)

/-- The bosonic residual multiplier `R_B ↦ 𝓑(𝒰)(R_B, 0)`. -/
def BmL (x : StateP m V S S') : BosP m V →ₗ[ℝ] StateP m V S S' where
  toFun y := toP (Bsys SM (ofP x) (ofR (bosR (S := S) (S' := S') y)))
  map_add' y y' := by
    rw [show bosR (S := S) (S' := S') (y + y') = bosR y + bosR y' by ext <;> simp [bosR]]
    exact toP_Bsys_add SM x _ _
  map_smul' c y := by
    rw [show bosR (S := S) (S' := S') (c • y) = c • bosR y by ext <;> simp [bosR]]
    exact toP_Bsys_smul SM x c _

/-- The undifferentiated Dirac residual multiplier `R_D ↦ 𝓑(𝒰)(0, R_D)`. -/
def DmL (x : StateP m V S S') : (S × S') →ₗ[ℝ] StateP m V S S' where
  toFun z := toP (Bsys SM (ofP x) (ofR (dirR (m := m) (V := V) z)))
  map_add' z z' := by
    rw [show dirR (m := m) (V := V) (z + z') = dirR z + dirR z' by ext <;> simp [dirR]]
    exact toP_Bsys_add SM x _ _
  map_smul' c z := by
    rw [show dirR (m := m) (V := V) (c • z) = c • dirR z by ext <;> simp [dirR]]
    exact toP_Bsys_smul SM x c _

theorem Bsys_split (x : StateP m V S S') (r : ResP m V S S') :
    toP (Bsys SM (ofP x) (ofR r)) =
      BmL SM x (r.1, r.2.1, r.2.2.1) + DmL SM x (r.2.2.2.1, r.2.2.2.2) := by
  show _ = toP (Bsys SM (ofP x) (ofR (bosR _))) + toP (Bsys SM (ofP x) (ofR (dirR _)))
  rw [← toP_Bsys_add]
  congr 3
  ext <;> simp [bosR, dirR]

/-- The differentiated Dirac residual coefficients `∂_j(r_D, r̄_D) ↦ 𝒬^j(g)∂_j(r_D, r̄_D)`. -/
def QmL (j : Fin 3) (x : StateP m V S S') : (S × S') →ₗ[ℝ] StateP m V S S' where
  toFun z := toP (Qsys SM (ofP x) j z.1 z.2)
  map_add' z z' := by
    ext <;> simp only [toP, Qsys, Prod.fst_add, Prod.snd_add, Pi.add_apply, smul_add,
      Module.End.smul_def, map_add, neg_add, add_zero, Pi.zero_apply]
  map_smul' c z := by
    ext <;> simp only [toP, Qsys, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_zero,
      Module.End.smul_def, map_smul, smul_neg, RingHom.id_apply] <;>
      first | (module; done) | skip

/-- A state with only a metric `p`-block. -/
def pState (P : Met) : State (MatLie m) V S S' where
  g := fun _ _ => 0
  p := P
  q := fun _ _ _ => 0
  A := fun _ => 0
  E := fun _ => 0
  B := fun _ => 0
  H := 0
  Pm := 0
  Q := fun _ => 0
  ψ := 0
  X := fun _ => 0
  ψb := 0
  Xb := fun _ => 0

/-- The gauge-forcing coefficient `C ↦ 𝒥_C(𝒰)C`. -/
def GcL (x : StateP m V S S') : (Fin 4 → ℝ) →ₗ[ℝ] StateP m V S S' where
  toFun Cv := toP (pState (m := m) (V := V) (S := S) (S' := S') fun μ ν =>
    ∑ l, JC (frameU (ginvOf x.1.1)) x.1.1 (ginvOf x.1.1) (dgOf x.1) μ ν l * Cv l)
  map_add' Cv Cv' := by
    ext <;> simp only [toP, pState, Pi.add_apply, mul_add, Finset.sum_add_distrib, add_zero,
      Pi.zero_apply, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add]
  map_smul' c Cv := by
    ext <;> simp only [toP, pState, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, smul_zero,
      RingHom.id_apply, Prod.smul_fst, Prod.smul_snd, Prod.smul_mk, mul_zero] <;>
      first | (exact Finset.sum_congr rfl fun l _ => by ring) | skip

/-- The gauge-forcing coefficient `∂_αC ↦ 𝒥_C^α(g)∂_αC`. -/
def GdL (α : Fin 4) (x : StateP m V S S') : (Fin 4 → ℝ) →ₗ[ℝ] StateP m V S S' where
  toFun Cv := toP (pState (m := m) (V := V) (S := S) (S' := S') fun μ ν =>
    ∑ l, Jd (frameU (ginvOf x.1.1)) x.1.1 α μ ν l * Cv l)
  map_add' Cv Cv' := by
    ext <;> simp only [toP, pState, Pi.add_apply, mul_add, Finset.sum_add_distrib, add_zero,
      Pi.zero_apply, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add]
  map_smul' c Cv := by
    ext <;> simp only [toP, pState, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, smul_zero,
      RingHom.id_apply, Prod.smul_fst, Prod.smul_snd, Prod.smul_mk, mul_zero] <;>
      first | (exact Finset.sum_congr rfl fun l _ => by ring) | skip

/-- The gauge forcing of the actual-jet system in the linear form
`𝔊 = 𝒥_C C + 𝒥_C^0∂_tC + Σ_j𝒥_C^j∂_jC` (`eq:actual-jet-gauge-forcing`). -/
theorem Gsys_split (x : StateP m V S S') (ddg : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    toP (Gsys (𝔤 := MatLie m) (V := V) (S := S) (S' := S') (frameU (ginvOf x.1.1)) x.1.1
      (ginvOf x.1.1) (dgOf x.1) ddg) =
      GcL x (fun l => C (ginvOf x.1.1) (dgOf x.1) l) +
        GdL 0 x (fun l => dC (ginvOf x.1.1) (dgOf x.1) ddg 0 l) +
        ∑ j : Fin 3, GdL j.succ x (fun l => dC (ginvOf x.1.1) (dgOf x.1) ddg j.succ l) := by
  ext <;> simp only [toP, Gsys, GcL, GdL, pState, LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_add,
    Prod.snd_add, Pi.add_apply, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Finset.sum_const_zero,
    add_zero] <;> rfl

end Forcing

section Smooth

variable (SM : SMData (MatLie m) V S S')

theorem contDiffAt_toP {F : StateP m V S S' → State (MatLie m) V S S'} {x0 : StateP m V S S'}
    (hg : ContDiffAt ℝ ∞ (fun x => (F x).g) x0) (hp : ContDiffAt ℝ ∞ (fun x => (F x).p) x0)
    (hq : ContDiffAt ℝ ∞ (fun x => (F x).q) x0) (hA : ContDiffAt ℝ ∞ (fun x => (F x).A) x0)
    (hE : ContDiffAt ℝ ∞ (fun x => (F x).E) x0) (hB : ContDiffAt ℝ ∞ (fun x => (F x).B) x0)
    (hH : ContDiffAt ℝ ∞ (fun x => (F x).H) x0) (hPm : ContDiffAt ℝ ∞ (fun x => (F x).Pm) x0)
    (hQ : ContDiffAt ℝ ∞ (fun x => (F x).Q) x0) (hψ : ContDiffAt ℝ ∞ (fun x => (F x).ψ) x0)
    (hX : ContDiffAt ℝ ∞ (fun x => (F x).X) x0) (hψb : ContDiffAt ℝ ∞ (fun x => (F x).ψb) x0)
    (hXb : ContDiffAt ℝ ∞ (fun x => (F x).Xb) x0) :
    ContDiffAt ℝ ∞ (fun x => toP (F x)) x0 :=
  (hg.prodMk (hp.prodMk hq)).prodMk (hA.prodMk (hE.prodMk (hB.prodMk (hH.prodMk (hPm.prodMk
    (hQ.prodMk (hψ.prodMk (hX.prodMk (hψb.prodMk hXb)))))))))

theorem pi2 {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] {f : StateP m V S S' → Fin 4 →
    Fin 4 → M} {x0 : StateP m V S S'} (h : ∀ μ ν, ContDiffAt ℝ ∞ (fun x => f x μ ν) x0) :
    ContDiffAt ℝ ∞ f x0 :=
  contDiffAt_pi.mpr fun μ => contDiffAt_pi.mpr fun ν => h μ ν

theorem pi1 {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] {f : StateP m V S S' → Fin 3 → M}
    {x0 : StateP m V S S'} (h : ∀ a, ContDiffAt ℝ ∞ (fun x => f x a) x0) : ContDiffAt ℝ ∞ f x0 :=
  contDiffAt_pi.mpr h

theorem comp_pair {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α] {M : Type*}
    [NormedAddCommGroup M] [NormedSpace ℝ M] {f : StateP m V S S' × α → M}
    {x0 : StateP m V S S'} {r : α} (hf : ContDiffAt ℝ ∞ f (x0, r)) :
    ContDiffAt ℝ ∞ (fun x => f (x, r)) x0 :=
  hf.comp x0 (contDiffAt_id.prodMk contDiffAt_const)

/-- The residual multiplier is smooth in the state on the chart (fixed residual). -/
theorem contDiffAt_Bsys (r : ResP m V S S') {x0 : StateP m V S S'} (hx : MetChart x0.1) :
    ContDiffAt ℝ ∞ (fun x => toP (Bsys SM (ofP x) (ofR r))) x0 := by
  have hpair : ContDiffAt ℝ ∞ (fun x : StateP m V S S' => (x, r)) x0 :=
    contDiffAt_id.prodMk contDiffAt_const
  refine contDiffAt_toP ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [Bsys]; exact contDiffAt_const
  · exact pi2 fun μ ν => comp_pair (smooth_Bsys_p SM (r0 := r) hx μ ν)
  · simp only [Bsys]; exact contDiffAt_const
  · simp only [Bsys]; exact contDiffAt_const
  · exact pi1 fun a => comp_pair (smooth_Bsys_E SM (r0 := r) hx a)
  · simp only [Bsys]; exact contDiffAt_const
  · simp only [Bsys]; exact contDiffAt_const
  · exact comp_pair (smooth_Bsys_Pm SM (r0 := r) hx)
  · simp only [Bsys]; exact contDiffAt_const
  · exact comp_pair (smooth_Bsys_ψ SM (r0 := r) hx)
  · exact pi1 fun a => comp_pair (smooth_Bsys_X SM (r0 := r) hx a)
  · exact comp_pair (smooth_Bsys_ψb SM (r0 := r) hx)
  · exact pi1 fun a => comp_pair (smooth_Bsys_Xb SM (r0 := r) hx a)

theorem contDiffAt_Qsys (j : Fin 3) (z : S × S') {x0 : StateP m V S S'} (hx : MetChart x0.1) :
    ContDiffAt ℝ ∞ (fun x => toP (Qsys SM (ofP x) j z.1 z.2)) x0 := by
  have hpair : ContDiffAt ℝ ∞ (fun x : StateP m V S S' => (x, z)) x0 :=
    contDiffAt_id.prodMk contDiffAt_const
  refine contDiffAt_toP ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first
    | (simp only [Qsys]; exact contDiffAt_const)
    | exact pi1 fun a => comp_pair (smooth_Qsys_X SM (d0 := z) hx j a)
    | exact pi1 fun a => comp_pair (smooth_Qsys_Xb SM (d0 := z) hx j a)

theorem contDiffAt_pState {P : StateP m V S S' → Met} {x0 : StateP m V S S'}
    (h : ∀ μ ν, ContDiffAt ℝ ∞ (fun x => P x μ ν) x0) :
    ContDiffAt ℝ ∞ (fun x => toP (pState (m := m) (V := V) (S := S) (S' := S') (P x))) x0 := by
  refine contDiffAt_toP ?_ (pi2 h) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    (simp only [pState]; exact contDiffAt_const)

theorem contDiffAt_GcL (Cv : Fin 4 → ℝ) {x0 : StateP m V S S'} (hx : MetChart x0.1) :
    ContDiffAt ℝ ∞ (fun x => GcL (m := m) (V := V) (S := S) (S' := S') x Cv) x0 := by
  refine contDiffAt_pState fun μ ν => ?_
  have h1 : ContDiffAt ℝ ∞ (fun x : StateP m V S S' => x.1) x0 := contDiffAt_fst
  exact ContDiffAt.sum fun l _ => ((smooth_JC hx μ ν l).comp x0 h1).mul contDiffAt_const

theorem contDiffAt_GdL (α : Fin 4) (Cv : Fin 4 → ℝ) {x0 : StateP m V S S'} (hx : MetChart x0.1) :
    ContDiffAt ℝ ∞ (fun x => GdL (m := m) (V := V) (S := S) (S' := S') α x Cv) x0 := by
  refine contDiffAt_pState fun μ ν => ?_
  have h1 : ContDiffAt ℝ ∞ (fun x : StateP m V S S' => x.1) x0 := contDiffAt_fst
  exact ContDiffAt.sum fun l _ => ((smooth_Jd hx α μ ν l).comp x0 h1).mul contDiffAt_const

end Smooth

/-! ### The complete forcing bound -/

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 1024 in
/-- **`lem:actual-jet-complete-forcing`** (`eq:actual-jet-complete-forcing`, squared form).
Fix `k ≥ 4`, a compact chart margin `K` (a compact set of actual-jet states in the open
Lorentzian chart) and an `H^k` radius `R`.  There is `C_M` such that for every smooth periodic
actual-jet state field on `[0, T] × 𝕋³` (in any linear coordinates `eX`) with values in `K` on the
slab and `‖𝒰(t)‖²_{H^k} ≤ R²`, every smooth periodic bosonic residual field `R_B = (𝓔^{tr}, r^A, r_H)`
and Dirac residual field `R_D = (r_D, r̄_D)` (in any linear coordinates), and every smooth periodic
harmonic defect field `C` with time-derivative field `∂_tC`, each linear functional `p` of the
forcing
`𝓕_err = 𝓑(𝒰)(R_B, R_D) + Σ_j 𝒬^j(g)∂_jR_D + 𝒥_C(𝒰)C + 𝒥_C^0(g)∂_tC + Σ_j 𝒥_C^j(g)∂_jC`
of `eq:actual-jet-writer` (any smooth field agreeing with `p(𝓕_err)` on the slab) satisfies
`Q_k ≤ C_M (Σ Q_k(R_B) + Σ Q_{k+1}(R_D) + Σ Q_{k+1}(C) + Σ Q_k(∂_tC))` for `t ∈ [0, T]`. -/
theorem actual_jet_complete_forcing (SM : SMData (MatLie m) V S S') {k : ℕ} (hk : 4 ≤ k)
    {K : Set (StateP m V S S')} (hK : IsCompact K) (hKO : ∀ x ∈ K, MetChart x.1) {n a b : ℕ}
    (eX : (Fin n → ℝ) ≃L[ℝ] StateP m V S S') (eY : (Fin a → ℝ) →ₗ[ℝ] BosP m V)
    (eYD : (Fin b → ℝ) →ₗ[ℝ] S × S') (pZ : StateP m V S S' →ₗ[ℝ] ℝ) {R T : ℝ} (hR : 0 ≤ R) :
    ∃ CM : ℝ, 0 ≤ CM ∧ ∀ u : Fin n → SlabWaveHk.ST 3 → ℝ, (∀ i, ContDiff ℝ ∞ (u i)) →
      (∀ i, SymHypEnergy.IsSPeriodic (u i)) → ∀ {RB : Fin a → SlabWaveHk.ST 3 → ℝ}
      {RD : Fin b → SlabWaveHk.ST 3 → ℝ} {Cf dtC : Fin 4 → SlabWaveHk.ST 3 → ℝ},
      (∀ i, ContDiff ℝ ∞ (RB i)) → (∀ i, ContDiff ℝ ∞ (RD i)) →
      (∀ l, ContDiff ℝ ∞ (Cf l)) → (∀ l, ContDiff ℝ ∞ (dtC l)) →
      (∀ i, SymHypEnergy.IsSPeriodic (RB i)) → (∀ i, SymHypEnergy.IsSPeriodic (RD i)) →
      (∀ l, SymHypEnergy.IsSPeriodic (Cf l)) → (∀ l, SymHypEnergy.IsSPeriodic (dtC l)) →
      (∀ x : SlabWaveHk.ST 3, x 0 ∈ Icc 0 T → eX (fun i => u i x) ∈ K) → ∀ t ∈ Icc 0 T,
      QLEnergy.energyQ k u t ≤ R ^ 2 → ∀ F : SlabWaveHk.ST 3 → ℝ, ContDiff ℝ ∞ F →
      (∀ x : SlabWaveHk.ST 3, x 0 ∈ Icc 0 T → F x =
        pZ (toP (Bsys SM (ofP (eX fun i => u i x))
            (ofR (((eY fun i => RB i x).1, (eY fun i => RB i x).2.1, (eY fun i => RB i x).2.2,
              (eYD fun i => RD i x).1, (eYD fun i => RD i x).2)))) +
          ∑ j : Fin 3, toP (Qsys SM (ofP (eX fun i => u i x)) j
            (eYD fun i => SobolevOpen.pd (RD i) j.succ x).1
            (eYD fun i => SobolevOpen.pd (RD i) j.succ x).2) +
          GcL (eX fun i => u i x) (fun l => Cf l x) +
          GdL 0 (eX fun i => u i x) (fun l => dtC l x) +
          ∑ j : Fin 3, GdL j.succ (eX fun i => u i x) (fun l => SobolevOpen.pd (Cf l) j.succ x))) →
      SlabSobAlg.Q k F t ≤ CM * (∑ i, SlabSobAlg.Q k (RB i) t + ∑ i, SlabSobAlg.Q (k + 1) (RD i) t +
        ∑ l, SlabSobAlg.Q (k + 1) (Cf l) t + ∑ l, SlabSobAlg.Q k (dtC l) t) := by
  have hm : ((3 : ℕ) : ℝ) / 2 < (2 : ℕ) := by norm_num
  have hk' : 2 * 2 ≤ k + 1 := by omega
  set O := {x : StateP m V S S' | MetChart x.1} with hOdef
  have hO : IsOpen O := isOpen_chart
  have hKO' : K ⊆ O := fun x hx => hKO x hx
  have pZc : ContDiff ℝ ∞ pZ := (LinearMap.toContinuousLinearMap pZ).contDiff
  have hsm : ∀ {f : StateP m V S S' → StateP m V S S'},
      (∀ x0 ∈ O, ContDiffAt ℝ ∞ f x0) → ContDiffOn ℝ ∞ (fun x => pZ (f x)) O :=
    fun hf x0 hx0 => (pZc.contDiffAt.comp x0 (hf x0 hx0)).contDiffWithinAt
  obtain ⟨CM, hCM0, hCM⟩ := SlabMoser.writer_forcing_bound (d := 3) (n := n) hm hk' eX eY eYD pZ
    hO hK hKO' (BmL SM) (DmL SM) (fun j => QmL SM j) GcL (GdL 0) (fun j => GdL j.succ)
    (fun y => hsm fun x0 hx0 => contDiffAt_Bsys SM _ hx0)
    (fun y => hsm fun x0 hx0 => contDiffAt_Bsys SM _ hx0)
    (fun j y => hsm fun x0 hx0 => contDiffAt_Qsys SM j y hx0)
    (fun y => hsm fun x0 hx0 => contDiffAt_GcL y hx0)
    (fun y => hsm fun x0 hx0 => contDiffAt_GdL 0 y hx0)
    (fun j y => hsm fun x0 hx0 => contDiffAt_GdL j.succ y hx0) hR (T := T)
  refine ⟨CM, hCM0, ?_⟩
  intro u hu hup RB RD Cf dtC hRB hRD hC hdtC pRB pRD pC pdtC hKu t ht hEt F hF hFeq
  refine hCM u hu hup hRB hRD hC hdtC pRB pRD pC pdtC hKu t ht hEt F hF fun x hx => ?_
  rw [hFeq x hx, Bsys_split]
  simp only [map_add, map_sum]
  rfl

/-- Non-vacuity: a compact chart margin exists (the Minkowski state). -/
example : ∃ K : Set (StateP 1 (MatLie 1) PUnit PUnit), IsCompact K ∧ K.Nonempty ∧
    ∀ x ∈ K, MetChart x.1 :=
  ⟨{(((minkInv, 0, 0) : MetP), 0)}, isCompact_singleton, ⟨_, rfl⟩, by
    rintro x rfl; exact metChart_mink⟩

end RenewalGeometry.ActualJetCompleteForcing
