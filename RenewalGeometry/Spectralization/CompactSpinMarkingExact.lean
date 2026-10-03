/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Spectralization.DensitySymmetricSpinDiracExact
import RenewalGeometry.DiscreteAnalysis.CoframeRenewalPacketExact

/-!
# The metric bracket does not select the spin marking

Paper `predictive_spectral_geometry`, label `cth:supp-metric-no-coframe`:
"The positive bracket determines `g⁻¹` but not an oriented orthonormal coframe, a spin lift, or
a global spin structure.  A smooth rotation `R(x) ∈ SO(d)` changes the coframe and spin
connection without changing `g⁻¹` or the scalar Renewal generator, and a nontrivial `ℤ₂` spin
holonomy is invisible to every local metric bracket."

The bracket/generator side is `CoframeRenewalPacket` (the bracket converges to `g⁻¹`,
`abs_bracket_sub_inverseMetric_le`; packets are built from `g⁻¹` and `ρ`).  The spin side uses
the geometric objects of `DensitySymmetricSpinDiracExact` (frame `E`, coframe `e`, Levi-Civita
frame connection `ω`, spinor connection `Ω = ¼ ω_{ab} γ_a γ_b`).

**Frame rotations** (`E ↦ R E`, `e ↦ e Rᵀ`, `R(x) ∈ SO(d)`):
* jet level: `ginv_rotate`, `metric_rotate`, `metricDeriv_rotate`, `christoffel_rotate`
  (`g⁻¹`, `g`, `∂g`, `Γ` unchanged), `frameConnection_rotate` (**`ω' = R ω Rᵀ + R ∂Rᵀ`**,
  i.e. `ω' = R ω R⁻¹ + R dR⁻¹`), `spinorConnection_rotate` (the induced spinor connection);
  `frameConnection_rotate_changes`: the connection really changes (an explicit jet);
* on a chart: `spinConnectionField_rotate` (the same law for smooth fields `R(y)` with
  `R(y) ∈ SO(d)` on an open chart, with `∂R` the actual derivative), `ginv_rotate_field`,
  `density_rotate` (`ρ = det e` unchanged), `isDecomposition_rotate_iff` (a Renewal packet is a
  decomposition of `ρ g⁻¹` for `E` iff it is one for `R E`: the bracket and the scalar
  generator are literally the same).

**Spin lifts** (`IsSpinLift γ S R`: `S γ_b S⁻¹ = Σ_a R_{ab} γ_a`, the Clifford-module form of
the central extension `Spin(d) → SO(d)` with kernel `{±1}`):
* `IsSpinLift.neg`, `spinLift_ne_neg`: every lift `S` of `R` has the distinct companion `-S`
  over the same rotation, hence over the same coframe and the same `g⁻¹`;
* `IsSpinLift.conj_spinor`: the homogeneous part of the spinor connection transforms by
  conjugation with a lift, `S (¼ ω_{ab} γ_aγ_b) S⁻¹ = ¼ (R ω Rᵀ)_{ab} γ_aγ_b`;
* `isSpinLift_spinRot`, `spinRot_add_two_pi`, `spinRot_two_pi`: in `d = 2` the lift
  `S_θ = cos(θ/2) - sin(θ/2) γ_1γ_2` of the rotation `R_θ` satisfies `S_{θ+2π} = -S_θ`: the closed
  frame loop `θ ∈ [0, 2π]` has spin holonomy `-1`.

**Global spin structures on a cycle** (`ℤ₂` edge cochains on `ℤ/nℤ` modulo vertex gauge):
* `holonomy_gauge`: the holonomy `∏_k s_k` is gauge invariant; `holonomy_antiperiodic`: the
  antiperiodic structure has holonomy `-1`, so it is not gauge equivalent to the periodic one
  (`not_gauge_equiv_antiperiodic`);
* `exists_gauge_trivial_on_arc`: on the arc obtained by deleting one edge (a contractible
  subgraph) every structure is gauge trivial;
* `local_invariant_const` (**invisibility**): every gauge-invariant functional of the structure
  that only reads the arc takes the same value on all spin structures — in particular on the
  periodic and antiperiodic ones; `spinorBracket_sign`: quadratic transport brackets
  `(s U)ᴴ M (s U)` do not see the sign.
* `metric_does_not_select_spin_marking`: the assembled statement.
-/

open Matrix Finset Filter Topology
open RenewalGeometry.DensitySymmetricSpinDirac RenewalGeometry.FrozenWilsonCoreConsistency

namespace RenewalGeometry.CompactSpinMarking

variable {d N : ℕ}

/-! ### Frame rotations: jet level -/

section rotation

variable {E e R : Matrix (Fin d) (Fin d) ℝ} {dE de dR : Fin d → Matrix (Fin d) (Fin d) ℝ}

/-- The rotated frame derivative `∂(R E) = ∂R E + R ∂E`. -/
def rotFrameDeriv (E R : Matrix (Fin d) (Fin d) ℝ) (dE dR : Fin d → Matrix (Fin d) (Fin d) ℝ) :
    Fin d → Matrix (Fin d) (Fin d) ℝ := fun l => dR l * E + R * dE l

/-- The rotated coframe derivative `∂(e Rᵀ) = ∂e Rᵀ + e ∂Rᵀ`. -/
def rotCoframeDeriv (e R : Matrix (Fin d) (Fin d) ℝ) (de dR : Fin d → Matrix (Fin d) (Fin d) ℝ) :
    Fin d → Matrix (Fin d) (Fin d) ℝ := fun l => de l * Rᵀ + e * (dR l)ᵀ

/-- `g⁻¹` is unchanged by a frame rotation. -/
theorem ginv_rotate (hR : Rᵀ * R = 1) : ginv (R * E) = ginv E := by
  rw [ginv, ginv, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Rᵀ, hR,
    Matrix.one_mul]

/-- `g` is unchanged by a frame rotation. -/
theorem metric_rotate (hR : Rᵀ * R = 1) : metric (e * Rᵀ) = metric e := by
  rw [metric, metric, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
    ← Matrix.mul_assoc Rᵀ, hR, Matrix.one_mul]

/-- `∂g` is unchanged by a (smooth) frame rotation: uses `∂Rᵀ R + Rᵀ ∂R = 0`. -/
theorem metricDeriv_rotate (hR : Rᵀ * R = 1) (hdR : ∀ l, (dR l)ᵀ * R + Rᵀ * dR l = 0)
    (l : Fin d) :
    metricDeriv (e * Rᵀ) (rotCoframeDeriv e R de dR) l = metricDeriv e de l := by
  have h1 : metricDeriv (e * Rᵀ) (rotCoframeDeriv e R de dR) l =
      metricDeriv e de l + e * ((dR l)ᵀ * R + Rᵀ * dR l) * eᵀ := by
    simp only [metricDeriv, rotCoframeDeriv, Matrix.transpose_mul, Matrix.transpose_add,
      Matrix.transpose_transpose, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Rᵀ R, hR, Matrix.one_mul, ← Matrix.mul_assoc Rᵀ R (de l)ᵀ, hR,
      Matrix.one_mul]
    abel
  rw [h1, hdR l, Matrix.mul_zero, Matrix.zero_mul, add_zero]

/-- The Christoffel symbols are unchanged by a frame rotation. -/
theorem christoffel_rotate (hR : Rᵀ * R = 1) (hdR : ∀ l, (dR l)ᵀ * R + Rᵀ * dR l = 0)
    (j : Fin d) :
    christoffel (R * E) (e * Rᵀ) (rotCoframeDeriv e R de dR) j = christoffel E e de j := by
  have hlow : christoffelLower (e * Rᵀ) (rotCoframeDeriv e R de dR) j =
      christoffelLower e de j := by
    ext n l
    simp only [christoffelLower, metricDeriv_rotate (e := e) (de := de) hR hdR]
  rw [christoffel, christoffel, ginv_rotate hR, hlow]

/-- **The gauge law of the Levi-Civita frame connection** under a frame rotation:
`ω'_j = R ω_j Rᵀ + R (∂_j R)ᵀ` (`= R ω R⁻¹ + R ∂(R⁻¹)` for `R ∈ SO(d)`). -/
theorem frameConnection_rotate (hEe : E * e = 1) (hR : Rᵀ * R = 1)
    (hdR : ∀ l, (dR l)ᵀ * R + Rᵀ * dR l = 0) (j : Fin d) :
    frameConnection (R * E) (e * Rᵀ) (rotFrameDeriv E R dE dR) (rotCoframeDeriv e R de dR) j =
      R * frameConnection E e dE de j * Rᵀ + R * (dR j)ᵀ := by
  rw [frameConnection, frameConnection, christoffel_rotate hR hdR]
  have heE : eᵀ * Eᵀ = 1 := transpose_coframe_mul hEe
  simp only [rotFrameDeriv, Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_transpose,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc eᵀ Eᵀ, heE, Matrix.one_mul]
  abel

/-- The induced spinor connection of the rotated frame:
`Ω'_j = ¼ Σ_{ab} (R ω_j Rᵀ + R ∂_jRᵀ)_{ab} γ_a γ_b`. -/
theorem spinorConnection_rotate (γ : Fin d → Matrix (Fin N) (Fin N) ℂ) (hEe : E * e = 1)
    (hR : Rᵀ * R = 1) (hdR : ∀ l, (dR l)ᵀ * R + Rᵀ * dR l = 0) (j : Fin d) :
    spinorConnection (R * E) (e * Rᵀ) (rotFrameDeriv E R dE dR) (rotCoframeDeriv e R de dR) γ j =
      (1 / 4 : ℂ) • ∑ a, ∑ b,
        (((R * frameConnection E e dE de j * Rᵀ + R * (dR j)ᵀ) a b : ℝ) : ℂ) • (γ a * γ b) := by
  rw [spinorConnection, frameConnection_rotate hEe hR hdR]

/-- The rotated frame is again a frame/coframe pair, with the differentiated relation. -/
theorem rotate_frame_coframe (hEe : E * e = 1) (hR : Rᵀ * R = 1) :
    (R * E) * (e * Rᵀ) = 1 := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc E, hEe, Matrix.one_mul]
  exact mul_eq_one_comm.mp hR

/-- **The connection really changes.**  At a jet with `E = e = R = 1`, `∂E = ∂e = 0` (so
`ω = 0`) and `∂_0 R = J` the infinitesimal rotation of the `(0,1)`-plane, the rotated frame
connection is `ω'_0 = Jᵀ ≠ 0`, while `g⁻¹` is unchanged. -/
theorem frameConnection_rotate_changes :
    let J : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]
    let dR : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ := fun l => if l = 0 then J else 0
    frameConnection (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 (fun _ => 0) (fun _ => 0) 0 = 0 ∧
      frameConnection ((1 : Matrix (Fin 2) (Fin 2) ℝ) * 1) (1 * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ)
        (rotFrameDeriv 1 1 (fun _ => 0) dR) (rotCoframeDeriv 1 1 (fun _ => 0) dR) 0 ≠ 0 ∧
      ginv ((1 : Matrix (Fin 2) (Fin 2) ℝ) * 1) = ginv 1 := by
  intro J dR
  have hdR : ∀ l, (dR l)ᵀ * 1 + (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * dR l = 0 := by
    intro l
    by_cases hl : l = 0
    · simp only [dR, hl, ite_true, J, Matrix.transpose_one, Matrix.mul_one, Matrix.one_mul]
      ext i j; fin_cases i <;> fin_cases j <;> simp
    · simp [dR, hl]
  have hω0 : frameConnection (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 (fun _ => 0) (fun _ => 0) 0 = 0 := by
    have hl : christoffelLower (1 : Matrix (Fin 2) (Fin 2) ℝ) (fun _ => 0) 0 = 0 := by
      ext n l; simp [christoffelLower, metricDeriv]
    simp [frameConnection, christoffel, hl]
  refine ⟨hω0, ?_, by rw [Matrix.mul_one]⟩
  rw [frameConnection_rotate (by simp) (by simp) hdR, hω0]
  intro h
  have := congrFun (congrFun h 0) 1
  simp [dR, J] at this

end rotation

/-! ### Frame rotations on a chart -/

section chart

variable {E e R : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}

/-- The product rule for `partialMat`. -/
theorem partialMat_mul {A B : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ} {x : Fin d → ℝ}
    (hA : ∀ a b, DifferentiableAt ℝ (fun y => A y a b) x)
    (hB : ∀ a b, DifferentiableAt ℝ (fun y => B y a b) x) (l : Fin d) :
    partialMat (fun y => A y * B y) l x = partialMat A l x * B x + A x * partialMat B l x := by
  ext a c
  have hφ : HasDerivAt (fun t : ℝ => ∑ b, A (x + t • dir l) a b * B (x + t • dir l) b c)
      (∑ b, (partialMat A l x a b * B x b c + A x a b * partialMat B l x b c)) 0 := by
    apply HasDerivAt.fun_sum
    intro b _
    have h1 := hasDerivAt_line (hA a b) (dir l)
    have h2 := hasDerivAt_line (hB b c) (dir l)
    have := h1.mul h2
    simp only [zero_smul, add_zero] at this
    convert this using 1
    all_goals rfl
  have hl : HasLineDerivAt ℝ (fun y => ∑ b, A y a b * B y b c)
      (∑ b, (partialMat A l x a b * B x b c + A x a b * partialMat B l x b c)) x (dir l) := hφ
  have : partialMat (fun y => A y * B y) l x a c =
      lineDeriv ℝ (fun y => ∑ b, A y a b * B y b c) x (dir l) := rfl
  rw [this, hl.lineDeriv]
  simp [Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib]

theorem partialMat_transpose (M : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ) (l : Fin d)
    (x : Fin d → ℝ) : partialMat (fun y => (M y)ᵀ) l x = (partialMat M l x)ᵀ := by
  ext a b; rfl

/-- `∂Rᵀ R + Rᵀ ∂R = 0` for a rotation field on an open chart. -/
theorem partialMat_orthogonal {Q : Set (Fin d → ℝ)} (hQ : IsOpen Q) {x : Fin d → ℝ} (hx : x ∈ Q)
    (hRQ : ∀ y ∈ Q, (R y)ᵀ * R y = 1) (hR : ∀ a b, DifferentiableAt ℝ (fun y => R y a b) x)
    (l : Fin d) : (partialMat R l x)ᵀ * R x + (R x)ᵀ * partialMat R l x = 0 := by
  have := partialMat_frame_coframe (E := fun y => (R y)ᵀ) (e := R) hQ hx hRQ
    (fun a b => hR b a) hR l
  rwa [partialMat_transpose] at this

/-- **Gauge law on a chart.**  For a rotation field `R(y)` (`R(y)ᵀ R(y) = 1` on the open chart,
differentiable at `x`) the Levi-Civita spinor connection of the rotated frame `R E` (coframe
`e Rᵀ`) at `x` is `¼ Σ_{ab} (R ω_j Rᵀ + R ∂_jRᵀ)_{ab} γ_a γ_b`, with `ω_j` the frame connection
of `E` and `∂_j R` the actual derivative. -/
theorem spinConnectionField_rotate (γ : Fin d → Matrix (Fin N) (Fin N) ℂ)
    {Q : Set (Fin d → ℝ)} (hQ : IsOpen Q) {x : Fin d → ℝ} (hx : x ∈ Q)
    (hEe : ∀ y ∈ Q, E y * e y = 1) (hRQ : ∀ y ∈ Q, (R y)ᵀ * R y = 1)
    (hE : ∀ a b, DifferentiableAt ℝ (fun y => E y a b) x)
    (he : ∀ a b, DifferentiableAt ℝ (fun y => e y a b) x)
    (hR : ∀ a b, DifferentiableAt ℝ (fun y => R y a b) x) (j : Fin d) :
    spinConnectionField (fun y => R y * E y) (fun y => e y * (R y)ᵀ) γ j x =
      (1 / 4 : ℂ) • ∑ a, ∑ b,
        (((R x * frameConnection (E x) (e x) (fun l => partialMat E l x)
            (fun l => partialMat e l x) j * (R x)ᵀ + R x * (partialMat R j x)ᵀ) a b : ℝ) : ℂ) •
          (γ a * γ b) := by
  have hdE : (fun l => partialMat (fun y => R y * E y) l x) =
      rotFrameDeriv (E x) (R x) (fun l => partialMat E l x) (fun l => partialMat R l x) := by
    funext l; exact partialMat_mul hR hE l
  have hde : (fun l => partialMat (fun y => e y * (R y)ᵀ) l x) =
      rotCoframeDeriv (e x) (R x) (fun l => partialMat e l x) (fun l => partialMat R l x) := by
    funext l
    have := partialMat_mul (A := e) (B := fun y => (R y)ᵀ) he (fun a b => hR b a) l
    rw [partialMat_transpose] at this
    exact this
  simp only [spinConnectionField]
  rw [hdE, hde]
  exact spinorConnection_rotate γ (hEe x hx) (hRQ x hx)
    (fun l => partialMat_orthogonal hQ hx hRQ hR l) j

/-- `g⁻¹` is unchanged as a field. -/
theorem ginv_rotate_field (hRO : ∀ y, (R y)ᵀ * R y = 1) :
    (fun y => ginv (R y * E y)) = fun y => ginv (E y) := by
  funext y; exact ginv_rotate (hRO y)

/-- The density `ρ = det e` is unchanged by a rotation with `det R = 1`. -/
theorem density_rotate (hdet : ∀ y, (R y).det = 1) :
    density (fun y => e y * (R y)ᵀ) = density e := by
  funext y
  simp [density, Matrix.det_mul, Matrix.det_transpose, hdet y]

/-- **The scalar Renewal packet does not see the rotation.**  A `CoframePacket` decomposes
`ρ g⁻¹` for the frame `E` iff it decomposes it for the rotated frame `R E`; hence the same
packet — the same bracket `eq:supp-general-bracket` and the same scalar generator — serves
both frames. -/
theorem isDecomposition_rotate_iff {ι : Type*} [Fintype ι]
    (P : CoframeRenewalPacket.CoframePacket d ι)
    (hRO : ∀ y, R y ∈ Matrix.orthogonalGroup (Fin d) ℝ) :
    P.IsDecomposition (fun y => CoframeRenewalPacket.coframeInverseMetric (R y * E y)) ↔
      P.IsDecomposition (fun y => CoframeRenewalPacket.coframeInverseMetric (E y)) := by
  have h : (fun y => CoframeRenewalPacket.coframeInverseMetric (R y * E y)) =
      fun y => CoframeRenewalPacket.coframeInverseMetric (E y) := by
    funext y; exact CoframeRenewalPacket.coframeInverseMetric_rotate (E y) (R y) (hRO y)
  rw [h]

end chart

/-! ### Spin lifts -/

section spinLift

variable {γ : Fin d → Matrix (Fin N) (Fin N) ℂ}

/-- `S` is a spin lift of the rotation `R` in the Clifford module: `S` invertible and
`S γ_b S⁻¹ = Σ_a R_{ab} γ_a` (written `S γ_b = (Σ_a R_{ab} γ_a) S`).  This is the module
realisation of the central extension `Spin(d) → SO(d)`, whose kernel `{±1}` acts by `±I`. -/
def IsSpinLift (γ : Fin d → Matrix (Fin N) (Fin N) ℂ) (S : Matrix (Fin N) (Fin N) ℂ)
    (R : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  IsUnit S ∧ ∀ b, S * γ b = (∑ a, ((R a b : ℝ) : ℂ) • γ a) * S

/-- The central element `-1` of the extension: `-S` lifts the same rotation. -/
theorem IsSpinLift.neg {S : Matrix (Fin N) (Fin N) ℂ} {R : Matrix (Fin d) (Fin d) ℝ}
    (h : IsSpinLift γ S R) : IsSpinLift γ (-S) R :=
  ⟨h.1.neg, fun b => by rw [Matrix.neg_mul, h.2 b, Matrix.mul_neg]⟩

/-- **The spin lift is not determined by the rotation** (hence not by the coframe or `g⁻¹`):
a lift `S` and its companion `-S` are distinct. -/
theorem spinLift_ne_neg [NeZero N] {S : Matrix (Fin N) (Fin N) ℂ} (hS : IsUnit S) : S ≠ -S := by
  intro h
  have h2 : (2 : ℂ) • S = 0 := by
    rw [two_smul]; nth_rewrite 2 [h]; exact add_neg_cancel S
  have hS0 : S = 0 := by
    rcases smul_eq_zero.mp h2 with h | h
    · norm_num at h
    · exact h
  exact hS.ne_zero hS0

/-- **The homogeneous part of the spinor connection transforms by conjugation** with a spin
lift: `S (Σ ω_{ab} γ_a γ_b) = (Σ (R ω Rᵀ)_{ab} γ_a γ_b) S`. -/
theorem IsSpinLift.conj_spinor {S : Matrix (Fin N) (Fin N) ℂ} {R : Matrix (Fin d) (Fin d) ℝ}
    (h : IsSpinLift γ S R) (ω : Matrix (Fin d) (Fin d) ℝ) :
    S * ∑ a, ∑ b, ((ω a b : ℝ) : ℂ) • (γ a * γ b) =
      (∑ a, ∑ b, (((R * ω * Rᵀ) a b : ℝ) : ℂ) • (γ a * γ b)) * S := by
  have hpair : ∀ a b, S * (γ a * γ b) =
      (∑ c, ((R c a : ℝ) : ℂ) • γ c) * (∑ c, ((R c b : ℝ) : ℂ) • γ c) * S := by
    intro a b
    rw [← Matrix.mul_assoc, h.2 a, Matrix.mul_assoc, h.2 b, ← Matrix.mul_assoc]
  have step : ∀ F : Fin d → Fin d → Fin d → Fin d → Matrix (Fin N) (Fin N) ℂ,
      ∑ a, ∑ b, ∑ c, ∑ c', F a b c c' = ∑ c, ∑ c', ∑ a, ∑ b, F a b c c' := by
    intro F
    calc ∑ a, ∑ b, ∑ c, ∑ c', F a b c c' = ∑ a, ∑ c, ∑ b, ∑ c', F a b c c' :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ c, ∑ a, ∑ b, ∑ c', F a b c c' := Finset.sum_comm
      _ = ∑ c, ∑ a, ∑ c', ∑ b, F a b c c' :=
          Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ c, ∑ c', ∑ a, ∑ b, F a b c c' := Finset.sum_congr rfl fun c _ => Finset.sum_comm
  have hexpand : ∀ a b, ((ω a b : ℝ) : ℂ) • (S * (γ a * γ b)) =
      ∑ c, ∑ c', ((ω a b * R c a * R c' b : ℝ) : ℂ) • (γ c * γ c' * S) := by
    intro a b
    rw [hpair, Finset.sum_mul, Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c' _ => ?_
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    push_cast
    ring
  have hL : S * ∑ a, ∑ b, ((ω a b : ℝ) : ℂ) • (γ a * γ b) =
      ∑ c, ∑ c', ∑ a, ∑ b, ((ω a b * R c a * R c' b : ℝ) : ℂ) • (γ c * γ c' * S) := by
    rw [← step]
    simp only [Finset.mul_sum, Matrix.mul_smul, hexpand]
  have hR : (∑ a, ∑ b, (((R * ω * Rᵀ) a b : ℝ) : ℂ) • (γ a * γ b)) * S =
      ∑ c, ∑ c', ∑ a, ∑ b, ((ω a b * R c a * R c' b : ℝ) : ℂ) • (γ c * γ c' * S) := by
    simp only [Finset.sum_mul, Matrix.smul_mul]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Complex.ofReal_sum,
      Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    congr 1
    push_cast
    ring
  rw [hL, hR]

end spinLift

/-! ### The two-dimensional spin lift and its holonomy -/

section twoDim

variable {γ : Fin 2 → Matrix (Fin N) (Fin N) ℂ}

/-- The rotation by `θ` in the plane. -/
noncomputable def rot2 (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

/-- The spin lift `S_θ = cos(θ/2) - sin(θ/2) γ_1 γ_2` of `rot2 θ`. -/
noncomputable def spinRot (γ : Fin 2 → Matrix (Fin N) (Fin N) ℂ) (θ : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  ((Real.cos (θ / 2) : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) -
    ((Real.sin (θ / 2) : ℝ) : ℂ) • (γ 0 * γ 1)

theorem rot2_mem_specialOrthogonalGroup (θ : ℝ) :
    rot2 θ ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  have h := Real.sin_sq_add_cos_sq θ
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rot2, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith
  · rw [rot2, Matrix.det_fin_two_of]
    nlinarith

theorem rot2_add_two_pi (θ : ℝ) : rot2 (θ + 2 * Real.pi) = rot2 θ := by
  simp [rot2, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem rot2_zero : rot2 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rot2]

section clifford2

variable (hγ : IsClifford γ)
include hγ

theorem cl_sq0 : γ 0 * γ 0 = 1 := by
  have h := hγ 0 0
  simp only [ite_true] at h
  rw [← two_smul ℂ (γ 0 * γ 0)] at h
  exact smul_right_injective _ two_ne_zero h

theorem cl_sq1 : γ 1 * γ 1 = 1 := by
  have h := hγ 1 1
  simp only [ite_true] at h
  rw [← two_smul ℂ (γ 1 * γ 1)] at h
  exact smul_right_injective _ two_ne_zero h

theorem cl_anti : γ 1 * γ 0 = -(γ 0 * γ 1) := by
  have h := hγ 0 1
  simp only [show (0 : Fin 2) ≠ 1 by decide, ite_false, zero_smul] at h
  exact eq_neg_of_add_eq_zero_right h

theorem cl_P_g0 : γ 0 * γ 1 * γ 0 = -γ 1 := by
  rw [Matrix.mul_assoc, cl_anti hγ, Matrix.mul_neg, ← Matrix.mul_assoc, cl_sq0 hγ, Matrix.one_mul]

theorem cl_P_g1 : γ 0 * γ 1 * γ 1 = γ 0 := by
  rw [Matrix.mul_assoc, cl_sq1 hγ, Matrix.mul_one]

theorem cl_g0_P : γ 0 * (γ 0 * γ 1) = γ 1 := by
  rw [← Matrix.mul_assoc, cl_sq0 hγ, Matrix.one_mul]

theorem cl_g1_P : γ 1 * (γ 0 * γ 1) = -γ 0 := by
  rw [← Matrix.mul_assoc, cl_anti hγ, Matrix.neg_mul, Matrix.mul_assoc, cl_sq1 hγ, Matrix.mul_one]

theorem cl_P_P : γ 0 * γ 1 * (γ 0 * γ 1) = -1 := by
  rw [← Matrix.mul_assoc, cl_P_g0 hγ, Matrix.neg_mul, cl_sq1 hγ]

/-- `(c - s P)(c + s P) = c² + s²` for `P = γ_1 γ_2`, `P² = -1`. -/
theorem core_mul (c s : ℂ) :
    (c • (1 : Matrix (Fin N) (Fin N) ℂ) - s • (γ 0 * γ 1)) * (c • 1 + s • (γ 0 * γ 1)) =
      (c * c + s * s) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
  simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, cl_P_P hγ, smul_neg]
  module

theorem core_g0 (c s : ℂ) (hpy : s * s + c * c = 1) :
    (c • (1 : Matrix (Fin N) (Fin N) ℂ) - s • (γ 0 * γ 1)) * γ 0 =
      ((c * c - s * s) • γ 0 + (2 * s * c) • γ 1) * (c • 1 - s • (γ 0 * γ 1)) := by
  calc (c • (1 : Matrix (Fin N) (Fin N) ℂ) - s • (γ 0 * γ 1)) * γ 0 = c • γ 0 + s • γ 1 := by
        simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, cl_P_g0 hγ, smul_neg]
        abel
    _ = (c * (s * s + c * c)) • γ 0 + (s * (s * s + c * c)) • γ 1 := by
        rw [hpy, mul_one, mul_one]
    _ = _ := by
        simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.mul_one, cl_g0_P hγ, cl_g1_P hγ, smul_neg]
        module

theorem core_g1 (c s : ℂ) (hpy : s * s + c * c = 1) :
    (c • (1 : Matrix (Fin N) (Fin N) ℂ) - s • (γ 0 * γ 1)) * γ 1 =
      ((-(2 * s * c)) • γ 0 + (c * c - s * s) • γ 1) * (c • 1 - s • (γ 0 * γ 1)) := by
  calc (c • (1 : Matrix (Fin N) (Fin N) ℂ) - s • (γ 0 * γ 1)) * γ 1 = (-s) • γ 0 + c • γ 1 := by
        simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, cl_P_g1 hγ, neg_smul]
        abel
    _ = (-(s * (s * s + c * c))) • γ 0 + (c * (s * s + c * c)) • γ 1 := by
        rw [hpy, mul_one, mul_one]
    _ = _ := by
        simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.mul_one, cl_g0_P hγ, cl_g1_P hγ, smul_neg]
        module

/-- `S_θ S_{-θ} = 1`. -/
theorem spinRot_mul_neg (θ : ℝ) : spinRot γ θ * spinRot γ (-θ) = 1 := by
  have hc : Real.cos (-θ / 2) = Real.cos (θ / 2) := by rw [neg_div, Real.cos_neg]
  have hs : Real.sin (-θ / 2) = -Real.sin (θ / 2) := by rw [neg_div, Real.sin_neg]
  have hpy : ((Real.cos (θ / 2) : ℝ) : ℂ) * ((Real.cos (θ / 2) : ℝ) : ℂ) +
      ((Real.sin (θ / 2) : ℝ) : ℂ) * ((Real.sin (θ / 2) : ℝ) : ℂ) = 1 := by
    exact_mod_cast (by nlinarith [Real.sin_sq_add_cos_sq (θ / 2)] :
      Real.cos (θ / 2) * Real.cos (θ / 2) + Real.sin (θ / 2) * Real.sin (θ / 2) = 1)
  rw [spinRot, spinRot, hc, hs, Complex.ofReal_neg, neg_smul, sub_neg_eq_add, core_mul hγ, hpy,
    one_smul]

theorem isUnit_spinRot (θ : ℝ) : IsUnit (spinRot γ θ) :=
  ⟨⟨spinRot γ θ, spinRot γ (-θ), spinRot_mul_neg hγ θ,
    by simpa using spinRot_mul_neg hγ (-θ)⟩, rfl⟩

omit hγ in
theorem rot2_apply_00 (θ : ℝ) : rot2 θ 0 0 = Real.cos θ := rfl
omit hγ in
theorem rot2_apply_01 (θ : ℝ) : rot2 θ 0 1 = -Real.sin θ := rfl
omit hγ in
theorem rot2_apply_10 (θ : ℝ) : rot2 θ 1 0 = Real.sin θ := rfl
omit hγ in
theorem rot2_apply_11 (θ : ℝ) : rot2 θ 1 1 = Real.cos θ := rfl

theorem spinRot_mul_gamma (φ : ℝ) (b : Fin 2) :
    spinRot γ (2 * φ) * γ b = (∑ a, ((rot2 (2 * φ) a b : ℝ) : ℂ) • γ a) * spinRot γ (2 * φ) := by
  have hφ : 2 * φ / 2 = φ := by ring
  have hpy : ((Real.sin φ : ℝ) : ℂ) * ((Real.sin φ : ℝ) : ℂ) +
      ((Real.cos φ : ℝ) : ℂ) * ((Real.cos φ : ℝ) : ℂ) = 1 := by
    exact_mod_cast (by nlinarith [Real.sin_sq_add_cos_sq φ] :
      Real.sin φ * Real.sin φ + Real.cos φ * Real.cos φ = 1)
  have hcos : ((Real.cos (2 * φ) : ℝ) : ℂ) = ((Real.cos φ : ℝ) : ℂ) * ((Real.cos φ : ℝ) : ℂ) -
      ((Real.sin φ : ℝ) : ℂ) * ((Real.sin φ : ℝ) : ℂ) := by
    have : Real.cos (2 * φ) = Real.cos φ * Real.cos φ - Real.sin φ * Real.sin φ := by
      rw [Real.cos_two_mul]; nlinarith [Real.sin_sq_add_cos_sq φ]
    rw [this, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_mul]
  have hsin : ((Real.sin (2 * φ) : ℝ) : ℂ) =
      2 * ((Real.sin φ : ℝ) : ℂ) * ((Real.cos φ : ℝ) : ℂ) := by
    rw [Real.sin_two_mul, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [Fin.sum_univ_two, spinRot, hφ]
  fin_cases b
  · show _ * γ 0 = (((rot2 (2 * φ) 0 0 : ℝ) : ℂ) • γ 0 + ((rot2 (2 * φ) 1 0 : ℝ) : ℂ) • γ 1) * _
    rw [rot2_apply_00, rot2_apply_10, hcos, hsin]
    exact core_g0 hγ _ _ hpy
  · show _ * γ 1 = (((rot2 (2 * φ) 0 1 : ℝ) : ℂ) • γ 0 + ((rot2 (2 * φ) 1 1 : ℝ) : ℂ) • γ 1) * _
    rw [rot2_apply_01, rot2_apply_11, Complex.ofReal_neg, hcos, hsin]
    exact core_g1 hγ _ _ hpy

/-- **`S_θ` lifts `rot2 θ`**: `S_θ γ_b S_θ⁻¹ = Σ_a R(θ)_{ab} γ_a`. -/
theorem isSpinLift_spinRot (θ : ℝ) : IsSpinLift γ (spinRot γ θ) (rot2 θ) := by
  refine ⟨isUnit_spinRot hγ θ, fun b => ?_⟩
  obtain ⟨φ, rfl⟩ : ∃ φ, θ = 2 * φ := ⟨θ / 2, by ring⟩
  exact spinRot_mul_gamma hγ φ b

end clifford2

/-- **Spin holonomy of the closed frame loop.**  `S_{θ+2π} = -S_θ` while `R_{θ+2π} = R_θ`:
the lift of the closed loop `θ ∈ [0, 2π]` of rotations starts at `S_0 = 1` and ends at
`S_{2π} = -1`. -/
theorem spinRot_add_two_pi (θ : ℝ) : spinRot γ (θ + 2 * Real.pi) = -spinRot γ θ := by
  have h : (θ + 2 * Real.pi) / 2 = θ / 2 + Real.pi := by ring
  rw [spinRot, spinRot, h, Real.cos_add_pi, Real.sin_add_pi]
  simp only [Complex.ofReal_neg, neg_smul]
  abel

theorem spinRot_zero : spinRot γ 0 = 1 := by simp [spinRot]

theorem spinRot_two_pi : spinRot γ (2 * Real.pi) = -1 := by
  have := spinRot_add_two_pi (γ := γ) 0
  rw [zero_add, spinRot_zero] at this
  exact this

end twoDim

/-! ### Global spin structures on the `n`-cycle and their invisibility -/

section cycle

variable {n : ℕ} [NeZero n]

/-- A `ℤ₂`-valued edge cochain on the `n`-cycle `ℤ/nℤ` (edge `k → k + 1`): the relative spin
marking of a spin structure with respect to a reference one (spin structures over a fixed
oriented frame bundle form a torsor under `H¹(·; ℤ₂)`). -/
abbrev SpinCochain (n : ℕ) := ZMod n → ℤˣ

/-- The `ℤ₂` holonomy of the marking around the cycle. -/
def holonomy (s : SpinCochain n) : ℤˣ := ∏ k, s k

/-- A vertex gauge transformation `t` (change of spin frame by `±1` at each vertex). -/
def gauge (t : ZMod n → ℤˣ) (s : SpinCochain n) : SpinCochain n := fun k => t k * s k * t (k + 1)

theorem units_int_mul_self' (u : ℤˣ) : u * u = 1 := Int.units_mul_self u

/-- The holonomy is gauge invariant. -/
theorem holonomy_gauge (t : ZMod n → ℤˣ) (s : SpinCochain n) :
    holonomy (gauge t s) = holonomy s := by
  unfold holonomy gauge
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have hshift : ∏ k : ZMod n, t (k + 1) = ∏ k, t k :=
    Fintype.prod_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)
  rw [hshift, mul_comm (∏ k, t k), mul_assoc, units_int_mul_self', mul_one]

/-- The antiperiodic (non-bounding) marking: `-1` on the edge `0 → 1`. -/
def antiperiodic : SpinCochain n := fun k => if k = 0 then -1 else 1

theorem holonomy_one : holonomy (1 : SpinCochain n) = 1 := by simp [holonomy]

theorem holonomy_antiperiodic : holonomy (antiperiodic : SpinCochain n) = -1 := by
  simp [holonomy, antiperiodic, Finset.prod_ite_eq']

/-- **The two spin structures are globally different**: no gauge transformation maps the
periodic marking to the antiperiodic one (their holonomies are `1` and `-1`). -/
theorem not_gauge_equiv_antiperiodic (t : ZMod n → ℤˣ) :
    gauge t (1 : SpinCochain n) ≠ antiperiodic := by
  intro h
  have := congrArg holonomy h
  rw [holonomy_gauge, holonomy_one, holonomy_antiperiodic] at this
  exact absurd this (by decide)

/-- The arc obtained by deleting the edge `n - 1 → 0`: the edges `k` with `k.val + 1 < n`. -/
def OnArc (k : ZMod n) : Prop := k.val + 1 < n

/-- **Gauge triviality on the arc** (a contractible subgraph): every marking is gauge
equivalent to one that is `1` on all arc edges, via the parallel-transport gauge
`t_k = ∏_{i < k} s_i`. -/
theorem exists_gauge_trivial_on_arc (s : SpinCochain n) :
    ∃ t : ZMod n → ℤˣ, ∀ k, OnArc k → gauge t s k = 1 := by
  refine ⟨fun k => ∏ i ∈ Finset.range k.val, s (i : ZMod n), fun k hk => ?_⟩
  have hn1 : n ≠ 1 := by
    intro h; subst h; unfold OnArc at hk; have := k.val_lt; omega
  have hval : (k + 1).val = k.val + 1 := by
    rw [ZMod.val_add_of_lt, ZMod.val_one'' hn1]
    rwa [ZMod.val_one'' hn1]
  simp only [gauge, hval, Finset.prod_range_succ, ZMod.natCast_zmod_val]
  exact units_int_mul_self' _

/-- A functional of the marking that reads only the arc edges. -/
def ArcLocal {X : Type*} (F : SpinCochain n → X) : Prop :=
  ∀ s s' : SpinCochain n, (∀ k, OnArc k → s k = s' k) → F s = F s'

/-- A gauge-invariant functional of the marking. -/
def GaugeInvariant {X : Type*} (F : SpinCochain n → X) : Prop :=
  ∀ (t : ZMod n → ℤˣ) (s : SpinCochain n), F (gauge t s) = F s

/-- **Invisibility of the `ℤ₂` holonomy to every local bracket.**  A gauge-invariant
functional that only reads a contractible arc takes the same value on every spin marking; in
particular it cannot distinguish the periodic marking from the antiperiodic one, although
their holonomies differ. -/
theorem local_invariant_const {X : Type*} {F : SpinCochain n → X} (hloc : ArcLocal F)
    (hinv : GaugeInvariant F) (s s' : SpinCochain n) : F s = F s' := by
  have key : ∀ s : SpinCochain n, F s = F 1 := by
    intro s
    obtain ⟨t, ht⟩ := exists_gauge_trivial_on_arc s
    rw [← hinv t s]
    exact hloc _ _ fun k hk => by rw [ht k hk]; rfl
  rw [key s, key s']

/-- The holonomy separates the periodic and the antiperiodic markings; it is gauge invariant
but reads every edge of the cycle, so it is not arc-local. -/
theorem holonomy_ne : holonomy (1 : SpinCochain n) ≠ holonomy (antiperiodic : SpinCochain n) := by
  rw [holonomy_one, holonomy_antiperiodic]; decide

/-- **Quadratic transport brackets are sign-blind**: for a spinor transport `s U` with
`s = ±1`, `(s U)ᴴ M (s U) = Uᴴ M U`. -/
theorem spinorBracket_sign (u : ℤˣ) (U M : Matrix (Fin N) (Fin N) ℂ) :
    (((u : ℤ) : ℂ) • U)ᴴ * M * (((u : ℤ) : ℂ) • U) = Uᴴ * M * U := by
  have hu : ((u : ℤ) : ℂ) * ((u : ℤ) : ℂ) = 1 := by
    have : (u : ℤ) * (u : ℤ) = 1 := by rw [← Units.val_mul, units_int_mul_self', Units.val_one]
    exact_mod_cast this
  have hs : star ((u : ℤ) : ℂ) = ((u : ℤ) : ℂ) := by simp
  rw [Matrix.conjTranspose_smul, hs]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hu, one_smul]

end cycle

/-! ### The assembled statement -/

/-- **`cth:supp-metric-no-coframe`.**
1. *Coframe*: two distinct coframes, related by an `SO(d)` rotation, have the same `g⁻¹`
   (hence the same bracket and scalar generator).
2. *Spin lift*: every spin lift `S` of a rotation has the distinct companion lift `-S` over the
   same rotation.
3. *Global spin structure / `ℤ₂` holonomy*: on the `n`-cycle the periodic and antiperiodic
   markings have holonomies `1 ≠ -1` (so they are not gauge equivalent), yet every
   gauge-invariant functional reading only a contractible arc agrees on them. -/
theorem metric_does_not_select_spin_marking (hd : 2 ≤ d) (n : ℕ) [NeZero n] :
    (∃ E E' : Matrix (Fin d) (Fin d) ℝ, E ≠ E' ∧
      (∃ R ∈ Matrix.specialOrthogonalGroup (Fin d) ℝ, E' = R * E) ∧
      CoframeRenewalPacket.coframeInverseMetric E' = CoframeRenewalPacket.coframeInverseMetric E) ∧
    (∀ [NeZero N] (γ : Fin d → Matrix (Fin N) (Fin N) ℂ) (S : Matrix (Fin N) (Fin N) ℂ)
        (R : Matrix (Fin d) (Fin d) ℝ), IsSpinLift γ S R → S ≠ -S ∧ IsSpinLift γ (-S) R) ∧
    (holonomy (1 : SpinCochain n) ≠ holonomy (antiperiodic : SpinCochain n) ∧
      (∀ t, gauge t (1 : SpinCochain n) ≠ antiperiodic) ∧
      ∀ {X : Type} (F : SpinCochain n → X), ArcLocal F → GaugeInvariant F →
        F 1 = F antiperiodic) :=
  ⟨CoframeRenewalPacket.exists_distinct_coframes_same_metric hd,
    fun _ _ _ hS => ⟨spinLift_ne_neg hS.1, hS.neg⟩,
    holonomy_ne, not_gauge_equiv_antiperiodic,
    fun _F hloc hinv => local_invariant_const hloc hinv 1 antiperiodic⟩

/-- Non-vacuity of the spin-lift clause: with the Pauli generators, `S_θ` lifts the rotation
`R_θ ∈ SO(2)`, and `S_θ`, `-S_θ = S_{θ+2π}` are two distinct lifts of the same rotation. -/
theorem spinLift_nonvacuous (θ : ℝ) :
    IsSpinLift pauli (spinRot pauli θ) (rot2 θ) ∧
      IsSpinLift pauli (spinRot pauli (θ + 2 * Real.pi)) (rot2 θ) ∧
      spinRot pauli θ ≠ spinRot pauli (θ + 2 * Real.pi) ∧
      rot2 θ ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
  have h := isSpinLift_spinRot pauli_isClifford θ
  refine ⟨h, ?_, ?_, rot2_mem_specialOrthogonalGroup θ⟩
  · rw [spinRot_add_two_pi]; exact h.neg
  · rw [spinRot_add_two_pi]; exact spinLift_ne_neg h.1

end RenewalGeometry.CompactSpinMarking
