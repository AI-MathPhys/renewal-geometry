/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.ActualJetReconstruction
import RenewalGeometry.Gravity.AdaptedFrameOfMetric

/-!
# The assembled block-symmetric actual-jet system (`prop:actual-jet-writer`, clause (e))

Einstein–Standard-Model action-closure manuscript, `prop:actual-jet-writer`
(`eq:actual-jet-writer`, `eq:actual-jet-gauge-forcing`, `eq:actual-jet-state`).

This file defines the realified actual-jet state
`𝒰 = (g_{μν}, p_u, q_{u,a}, A_i, E_a, B_a, H, Π, Q_a, Ψ, X_a, Ψ̄, X̄_a)` (`State`), the principal
operators `𝒜^j(g)` (`princ`) and their **symmetry** for the block inner product (`princ_symm`),
for the jets at one point of an actual field tuple in exact temporal internal gauge
(`ActualJet`; the metric frame is the fixed algebraic frame `ActualJetFrame.frameOf` and its
derivative jets are the actual derivatives `ActualJetFrame.frameJet`).

Theory data (`SMData`): the cosmological and gravitational constants, two Dirac blocks (spinor and
dual spinor, each with a Lorentzian Clifford frame, a gauge action commuting with Clifford
multiplication, and an affine gauge-equivariant mass map `𝓜(H) = m₀ + 𝓜_H[H]`), the Yang–Mills
and Higgs sources `J(g, H, DH, Ψ, Ψ̄)`, `S_H(g, H, Ψ, Ψ̄)` (any functions of the undifferentiated
fields and of `DH`; e.g. the Standard-Model currents and `S_H = ∂V + Yukawa`), the invariant
inner products and Higgs potential constants of `eq:YM-stress`, `eq:H-stress`, and a stress of
Dirac–Yukawa type.
-/

namespace RenewalGeometry.ActualJetSystem

open Finset FrameCurvature ActualJetWriter ActualJetGauge ActualJetSpinor ActualJetRecon
  ActualJetFrame SpinorProlongation TwistedHalfRicci HarmonicDefect

noncomputable section

set_option linter.unusedSectionVars false

/-- The Lorentzian signs `ε = (-1, 1, 1, 1)`. -/
def lorentzSign (A : Fin 4) : ℝ := if A = 0 then -1 else 1

/-! ### Theory data -/

/-- **A Dirac block**: a Lorentzian Clifford frame on the (realified) spinor space `S`, the gauge
action on spinors commuting with Clifford multiplication, and an affine mass map
`𝓜(H) = m₀ + 𝓜_H[H]` commuting with the spin rotations and gauge equivariant. -/
structure DiracData (𝔤 V S : Type*) [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [AddCommGroup V] [Module ℝ V]
    [LieRingModule 𝔤 V] [LieModule ℝ 𝔤 V] [AddCommGroup S] [Module ℝ S] where
  Fr : CliffordFrame (Fin 4) (Module.End ℝ S)
  ρ : 𝔤 →ₗ[ℝ] Module.End ℝ S
  ρ_lie : ∀ x y, ρ ⁅x, y⁆ = ρ x * ρ y - ρ y * ρ x
  m0 : Module.End ℝ S
  L : V →ₗ[ℝ] Module.End ℝ S
  lorentz : IsLorentzian Fr
  comm : ∀ x b, ρ x * Fr.c b = Fr.c b * ρ x
  mass_cl : ∀ w c d, mass m0 L w * (Fr.c c * Fr.c d) = Fr.c c * Fr.c d * mass m0 L w
  mass_eq : ∀ x w, ρ x * mass m0 L w - mass m0 L w * ρ x = L ⁅x, w⁆

/-- **The theory data** of the Einstein–Standard-Model actual-jet system. -/
structure SMData (𝔤 V S S' : Type*) [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [AddCommGroup V] [Module ℝ V]
    [LieRingModule 𝔤 V] [LieModule ℝ 𝔤 V] [AddCommGroup S] [Module ℝ S] [AddCommGroup S']
    [Module ℝ S'] where
  Λ : ℝ
  κ : ℝ
  D : DiracData 𝔤 V S
  Db : DiracData 𝔤 V S'
  /-- the Yang–Mills source `J_ν(g, g⁻¹, H, DH, Ψ, Ψ̄)` -/
  Jcur : (Fin 4 → Fin 4 → ℝ) → (Fin 4 → Fin 4 → ℝ) → V → (Fin 4 → V) → S → S' → Fin 4 → 𝔤
  /-- the Higgs source `S_H(g, g⁻¹, H, Ψ, Ψ̄)` -/
  SH : (Fin 4 → Fin 4 → ℝ) → (Fin 4 → Fin 4 → ℝ) → V → S → S' → V
  ipG : 𝔤 →ₗ[ℝ] 𝔤 →ₗ[ℝ] ℝ
  ipV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ
  lamH : ℝ
  vH : ℝ
  TD : DiracStressForm S S' V

/-! ### Actual jets -/

/-- **The jets at one point of an actual field tuple in exact temporal internal gauge**: the
metric 2-jet with the 2-jet of the fixed algebraic adapted frame `frameOf(g)` (an orthonormal
`FrameJet`; its frame and first derivative jets are `frU` and the actual derivative
`frameJet`), the gauge potential 2-jet with `A_0 ≡ 0`, the Higgs 2-jet and the 2-jets of both
spinors.  The jet relations are those of smooth fields (symmetric second derivatives). -/
structure ActualJet (𝔤 V S S' : Type*) [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [AddCommGroup V]
    [Module ℝ V] [AddCommGroup S] [Module ℝ S] [AddCommGroup S'] [Module ℝ S'] where
  FJ : FrameJet (Fin 4) (Fin 4)
  chart : IsLorChart FJ.gi
  sign : FJ.ε = lorentzSign
  frame : ∀ A μ, FJ.e A μ = frU FJ.gi A μ
  dframe : ∀ γ A μ, FJ.de γ A μ = frameJet FJ.gi (fun γ l σ => dginv FJ.gi FJ.dg γ l σ) γ A μ
  A : Fin 4 → 𝔤
  dA : Fin 4 → Fin 4 → 𝔤
  ddA : Fin 4 → Fin 4 → Fin 4 → 𝔤
  temporal : A 0 = 0
  dtemporal : ∀ γ, dA γ 0 = 0
  ddA_symm : ∀ α β μ, ddA α β μ = ddA β α μ
  H : V
  dH : Fin 4 → V
  ddH : Fin 4 → Fin 4 → V
  ddH_symm : ∀ α β, ddH α β = ddH β α
  ψ : S
  cψ : Fin 4 → S
  ccψ : Fin 4 → Fin 4 → S
  ccψ_symm : ∀ δ γ, ccψ δ γ = ccψ γ δ
  ψb : S'
  cψb : Fin 4 → S'
  ccψb : Fin 4 → Fin 4 → S'
  ccψb_symm : ∀ δ γ, ccψb δ γ = ccψb γ δ

/-! ### The state -/

/-- **The realified actual-jet state** `eq:actual-jet-state`:
`(g_{μν}, p_u, q_{u,a}, A_i, E_a, B_a, H, Π, Q_a, Ψ, X_a, Ψ̄, X̄_a)` (`u = g_{μν}`; the spinor
blocks carry the tangential covariant jets `X_a = ∇_{e_a}Ψ`, `a = 1, 2, 3`). -/
structure State (𝔤 V S S' : Type*) where
  g : Fin 4 → Fin 4 → ℝ
  p : Fin 4 → Fin 4 → ℝ
  q : Fin 3 → Fin 4 → Fin 4 → ℝ
  A : Fin 3 → 𝔤
  E : Fin 3 → 𝔤
  B : Fin 3 → 𝔤
  H : V
  Pm : V
  Q : Fin 3 → V
  ψ : S
  X : Fin 3 → S
  ψb : S'
  Xb : Fin 3 → S'

/-! ### The principal operators -/

section Principal

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {S : Type*} [AddCommGroup S] [Module ℝ S]
variable {S' : Type*} [AddCommGroup S'] [Module ℝ S']

/-- The principal operator of a Dirac block: `x ↦ -βʲx - N Σ_i e_iʲ c_0c_i x`. -/
def diracP (AF : AdaptedFrame) (Fr : CliffordFrame (Fin 4) (Module.End ℝ S)) (j : Fin 3)
    (x : S) : S :=
  -(AF.β j • x) - AF.N • ∑ i : Fin 3, AF.E i j • ((Fr.c 0 * Fr.c i.succ) • x)

/-- **The principal operators `𝒜^j(g)`** of `eq:actual-jet-writer` on state increments: zero on
the algebraic head blocks `(g, A, H)`, the wave block `(p, q)` (`ActualJetWriter.waveSym`), the
Maxwell block `(E, B)` (`ActualJetGauge.maxwellSym`), the Higgs block `(Π, Q)`
(`ActualJetGauge.higgsSym`) and the Dirac blocks `-βʲ - N e_iʲc_0c_i` on `Ψ`, each `X_a`, `Ψ̄`,
each `X̄_a`.  They depend on the metric only, through the adapted frame `(N, β, e)`. -/
def princ (AF : AdaptedFrame) (Fr : CliffordFrame (Fin 4) (Module.End ℝ S))
    (Frb : CliffordFrame (Fin 4) (Module.End ℝ S')) (j : Fin 3) (W : State 𝔤 V S S') :
    State 𝔤 V S S' where
  g := fun _ _ => 0
  p := fun μ ν => -(AF.β j * W.p μ ν) - AF.N * ∑ a, AF.E a j * W.q a μ ν
  q := fun a μ ν => -(AF.N * AF.E a j * W.p μ ν) - AF.β j * W.q a μ ν
  A := fun _ => 0
  E := fun a => -(AF.β j • W.E a) - AF.N • ∑ b, ∑ c, eps3 a b c • (AF.E b j • W.B c)
  B := fun a => -(AF.β j • W.B a) + AF.N • ∑ b, ∑ c, eps3 a b c • (AF.E b j • W.E c)
  H := 0
  Pm := -(AF.β j • W.Pm) - AF.N • ∑ a, AF.E a j • W.Q a
  Q := fun a => -(AF.β j • W.Q a) - AF.N • (AF.E a j • W.Pm)
  ψ := diracP AF Fr j W.ψ
  X := fun a => diracP AF Fr j (W.X a)
  ψb := diracP AF Frb j W.ψb
  Xb := fun a => diracP AF Frb j (W.Xb a)

/-- The block inner product on states, from fixed bilinear forms on the gauge algebra, the Higgs
space and the two spinor spaces (positive definite in the paper's "fixed positive component
norm"; only bilinearity enters `princ_symm`). -/
def ipState (bG : 𝔤 →ₗ[ℝ] 𝔤 →ₗ[ℝ] ℝ) (bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ)
    (bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ) (W W' : State 𝔤 V S S') : ℝ :=
  ∑ μ, ∑ ν, (W.g μ ν * W'.g μ ν + W.p μ ν * W'.p μ ν + ∑ a, W.q a μ ν * W'.q a μ ν) +
  ∑ a, (bG (W.A a) (W'.A a) + bG (W.E a) (W'.E a) + bG (W.B a) (W'.B a)) +
  (bV W.H W'.H + bV W.Pm W'.Pm + ∑ a, bV (W.Q a) (W'.Q a)) +
  (bS W.ψ W'.ψ + ∑ a, bS (W.X a) (W'.X a)) +
  (bS' W.ψb W'.ψb + ∑ a, bS' (W.Xb a) (W'.Xb a))

/-- `c_0c_i` is self-adjoint for a bilinear form for which `c_0` is self-adjoint and `c_i`
(`i ≠ 0`) is skew (the realified unitary Clifford representation). -/
theorem c0ci_selfAdjoint (Fr : CliffordFrame (Fin 4) (Module.End ℝ S))
    (bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ) (hc0 : ∀ x y, bS (Fr.c 0 • x) y = bS x (Fr.c 0 • y))
    (hci : ∀ (i : Fin 3) x y, bS (Fr.c i.succ • x) y = -bS x (Fr.c i.succ • y)) (i : Fin 3)
    (x y : S) :
    bS ((Fr.c 0 * Fr.c i.succ) • x) y = bS x ((Fr.c 0 * Fr.c i.succ) • y) := by
  have hanti : Fr.c i.succ * Fr.c 0 = -(Fr.c 0 * Fr.c i.succ) := by
    have h := Fr.anticomm 0 i.succ
    simp only [(Fin.succ_ne_zero i).symm, ite_false, mul_zero, zero_smul] at h
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
  rw [mul_smul, hc0, hci, ← mul_smul, hanti, neg_smul, map_neg, neg_neg]

theorem diracP_symm (AF : AdaptedFrame) (Fr : CliffordFrame (Fin 4) (Module.End ℝ S))
    (bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ)
    (hself : ∀ (i : Fin 3) x y, bS ((Fr.c 0 * Fr.c i.succ) • x) y =
      bS x ((Fr.c 0 * Fr.c i.succ) • y)) (j : Fin 3) (x y : S) :
    bS (diracP AF Fr j x) y = bS x (diracP AF Fr j y) := by
  unfold diracP
  simp only [map_sub, map_neg, map_smul, map_sum, LinearMap.sub_apply, LinearMap.neg_apply,
    LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul, hself]

/-- **The principal operators are symmetric** for the block inner product
(`eq:actual-jet-writer`: "`𝒜^j` are symmetric in the fixed positive component norm after
realification"), whenever the Clifford generators satisfy the unitarity relations (`c_0`
self-adjoint, `c_i` skew) for the spinor forms. -/
theorem princ_symm (AF : AdaptedFrame) (Fr : CliffordFrame (Fin 4) (Module.End ℝ S))
    (Frb : CliffordFrame (Fin 4) (Module.End ℝ S')) (bG : 𝔤 →ₗ[ℝ] 𝔤 →ₗ[ℝ] ℝ)
    (bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ) (bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ)
    (hc0 : ∀ x y, bS (Fr.c 0 • x) y = bS x (Fr.c 0 • y))
    (hci : ∀ (i : Fin 3) x y, bS (Fr.c i.succ • x) y = -bS x (Fr.c i.succ • y))
    (hc0b : ∀ x y, bS' (Frb.c 0 • x) y = bS' x (Frb.c 0 • y))
    (hcib : ∀ (i : Fin 3) x y, bS' (Frb.c i.succ • x) y = -bS' x (Frb.c i.succ • y))
    (j : Fin 3) (W W' : State 𝔤 V S S') :
    ipState bG bV bS bS' (princ AF Fr Frb j W) W' =
      ipState bG bV bS bS' W (princ AF Fr Frb j W') := by
  have hD := diracP_symm AF Fr bS (c0ci_selfAdjoint Fr bS hc0 hci) j
  have hDb := diracP_symm AF Frb bS' (c0ci_selfAdjoint Frb bS' hc0b hcib) j
  unfold ipState
  have hwave : ∀ μ ν, (princ AF Fr Frb j W).g μ ν * W'.g μ ν +
      (princ AF Fr Frb j W).p μ ν * W'.p μ ν +
      ∑ a, (princ AF Fr Frb j W).q a μ ν * W'.q a μ ν =
      W.g μ ν * (princ AF Fr Frb j W').g μ ν + W.p μ ν * (princ AF Fr Frb j W').p μ ν +
      ∑ a, W.q a μ ν * (princ AF Fr Frb j W').q a μ ν := by
    intro μ ν
    simp only [princ, Fin.sum_univ_three]
    ring
  have hgauge : ∑ a, (bG ((princ AF Fr Frb j W).A a) (W'.A a) +
      bG ((princ AF Fr Frb j W).E a) (W'.E a) + bG ((princ AF Fr Frb j W).B a) (W'.B a)) =
      ∑ a, (bG (W.A a) ((princ AF Fr Frb j W').A a) + bG (W.E a) ((princ AF Fr Frb j W').E a) +
        bG (W.B a) ((princ AF Fr Frb j W').B a)) := by
    simp only [princ, map_sub, map_add, map_neg, map_smul, map_sum, map_zero,
      LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply,
      LinearMap.sum_apply, LinearMap.zero_apply, smul_eq_mul, Fin.sum_univ_three, eps3]
    norm_num
    ring
  have hhiggs : bV ((princ AF Fr Frb j W).H) W'.H + bV ((princ AF Fr Frb j W).Pm) W'.Pm +
      ∑ a, bV ((princ AF Fr Frb j W).Q a) (W'.Q a) =
      bV W.H ((princ AF Fr Frb j W').H) + bV W.Pm ((princ AF Fr Frb j W').Pm) +
      ∑ a, bV (W.Q a) ((princ AF Fr Frb j W').Q a) := by
    simp only [princ, map_sub, map_add, map_neg, map_smul, map_sum, map_zero,
      LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply,
      LinearMap.sum_apply, LinearMap.zero_apply, smul_eq_mul, Fin.sum_univ_three]
    ring
  rw [Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => hwave μ ν, hgauge,
    hhiggs]
  simp only [princ, hD, hDb]

end Principal

/-! ### Derived objects of an actual jet -/

section Derived

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [LieRingModule 𝔤 V] [LieModule ℝ 𝔤 V]
variable {S : Type*} [AddCommGroup S] [Module ℝ S]
variable {S' : Type*} [AddCommGroup S'] [Module ℝ S']
variable {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀]

/-- The residual-free normal spinor jet `X_0^♮ = c_0Σ_ic_iX_i - c_0𝓜(H)Ψ` (as a function of the
tangential state variables). -/
def XnatU (D : DiracData 𝔤 V S₀) (ψ : S₀) (Xt : Fin 3 → S₀) (H : V) : S₀ :=
  D.Fr.c 0 • ∑ i : Fin 3, D.Fr.c i.succ • Xt i - D.Fr.c 0 • (mass D.m0 D.L H • ψ)

namespace ActualJet

variable (J : ActualJet 𝔤 V S S')

/-- The adapted frame `frameOf(g)` of the actual metric. -/
def AF : AdaptedFrame := frameOf J.FJ.gi J.chart

theorem hfr (B μ : Fin 4) : J.FJ.e B μ = J.AF.fr B μ := (J.frame B μ).trans (frU_eq J.chart B μ)

theorem hadapt : J.AF.IsAdapted J.FJ.gi := frameOf_adapted J.FJ.gi_symm J.chart

/-- The Clifford signs of a Dirac block are the frame signs. -/
theorem hε (D : DiracData 𝔤 V S₀) : D.Fr.ε = J.FJ.ε := by
  rw [J.sign]
  funext A
  induction A using Fin.cases with
  | zero => rw [D.lorentz.1]; rfl
  | succ a => rw [D.lorentz.2 a]; simp [lorentzSign, Fin.succ_ne_zero]

/-- The twisted Levi-Civita spin-connection jets of a Dirac block (`FrameJet.toLCJet`). -/
def LJ (D : DiracData 𝔤 V S₀) : LCJet D.Fr :=
  J.FJ.toLCJet D.Fr (J.hε D) (fun μ => D.ρ (J.A μ)) (fun γ μ => D.ρ (J.dA γ μ))
    (fun μ b => D.comm (J.A μ) b)

/-- `X_A = ∇_{e_A}Ψ` (all four frame indices). -/
def Xs (D : DiracData 𝔤 V S₀) (ψ : S₀) (cψ : Fin 4 → S₀) (A : Fin 4) : S₀ :=
  cov (J.LJ D).ω ψ (dψf J.FJ cψ) A

/-- The coordinate derivative jets `∂_γX_a`. -/
def dXs (D : DiracData 𝔤 V S₀) (ψ : S₀) (cψ : Fin 4 → S₀) (ccψ : Fin 4 → Fin 4 → S₀)
    (γ a : Fin 4) : S₀ :=
  dXc J.FJ D.Fr (J.hε D) (fun μ => D.ρ (J.A μ)) (fun γ μ => D.ρ (J.dA γ μ))
    (fun μ b => D.comm (J.A μ) b) ψ cψ ccψ γ a

/-- The Dirac residual `r_D = 𝒟Ψ - 𝓜(H)Ψ`. -/
def rD (D : DiracData 𝔤 V S₀) (ψ : S₀) (cψ : Fin 4 → S₀) : S₀ :=
  resD D.Fr (J.LJ D).ω D.m0 D.L J.H ψ (dψf J.FJ cψ)

/-- The coordinate derivative jets `∂_γr_D` of the Dirac residual. -/
def drD (D : DiracData 𝔤 V S₀) (ψ : S₀) (cψ : Fin 4 → S₀) (ccψ : Fin 4 → Fin 4 → S₀)
    (γ : Fin 4) : S₀ :=
  drc J.FJ D.Fr (J.hε D) (fun μ => D.ρ (J.A μ)) (fun γ μ => D.ρ (J.dA γ μ))
    (fun μ b => D.comm (J.A μ) b) D.m0 D.L J.H J.dH ψ cψ ccψ γ

/-- The gauge action on the Higgs field along the frame, `ρ_H(A(e_a)) = e_a{}^μ A_μ·`. -/
def ρH (a : Fin 4) : V →ₗ[ℝ] V := ∑ μ, J.FJ.e a μ • LieModule.toEnd ℝ 𝔤 V (J.A μ)

theorem ρH_apply (a : Fin 4) (w : V) : J.ρH a w = ∑ μ, J.FJ.e a μ • ⁅J.A μ, w⁆ := by
  unfold ρH
  rw [LinearMap.sum_apply]
  rfl

/-- The covariant product rule hypothesis of `prop:spinor-prolongation`
(`[ω_a, 𝓜(w)] = 𝓜_H[ρ_H(A(e_a))w]`) from the gauge equivariance of the mass map. -/
theorem hMg (D : DiracData 𝔤 V S₀) (a : Fin 4) (w : V) :
    (J.LJ D).ρ a * mass D.m0 D.L w - mass D.m0 D.L w * (J.LJ D).ρ a = D.L (J.ρH a w) := by
  show (∑ μ, J.FJ.e a μ • D.ρ (J.A μ)) * mass D.m0 D.L w -
      mass D.m0 D.L w * (∑ μ, J.FJ.e a μ • D.ρ (J.A μ)) = _
  rw [J.ρH_apply, map_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, D.mass_eq, map_smul]


/-- **`eq:normal-spinor-jet`** for an actual jet: `X_0 = X_0^♮ - c_0r_D`. -/
theorem Xs_zero (D : DiracData 𝔤 V S₀) (ψ : S₀) (cψ : Fin 4 → S₀) :
    J.Xs D ψ cψ 0 = XnatU D ψ (fun i => J.Xs D ψ cψ i.succ) J.H - D.Fr.c 0 • J.rD D ψ cψ := by
  have h := normal_spinor_jet_resD D.Fr 0 D.lorentz.1 D.lorentz.ne_zero (J.LJ D).ω D.m0 D.L J.H
    ψ (dψf J.FJ cψ)
  rw [ActualJetWriter.sum_erase_zero] at h
  unfold Xs XnatU rD
  rw [h]

/-- The full spinor jet with the residual-free normal component. -/
def Xn (D : DiracData 𝔤 V S₀) (ψ : S₀) (cψ : Fin 4 → S₀) : Fin 4 → S₀ :=
  Fin.cases (XnatU D ψ (fun i => J.Xs D ψ cψ i.succ) J.H) (fun i => J.Xs D ψ cψ i.succ)

theorem Xs_eq_Xn (D : DiracData 𝔤 V S₀) (ψ : S₀) (cψ : Fin 4 → S₀) (A : Fin 4) :
    J.Xs D ψ cψ A = J.Xn D ψ cψ A - (if A = 0 then D.Fr.c 0 • J.rD D ψ cψ else 0) := by
  induction A using Fin.cases with
  | zero => rw [Xs_zero]; simp [Xn]
  | succ a => simp [Xn, Fin.succ_ne_zero]

end ActualJet

/-! ### The state and its derivative jets -/

namespace ActualJet

variable (J : ActualJet 𝔤 V S S') (SM : SMData 𝔤 V S S')

/-- **The actual-jet state** `𝒰(z)` of the jets (`eq:actual-jet-state`). -/
def state : State 𝔤 V S S' where
  g := J.FJ.g
  p := fun μ ν => J.AF.pJ (fun α => J.FJ.dg α μ ν)
  q := fun a μ ν => J.AF.qJ (fun α => J.FJ.dg α μ ν) a
  A := fun i => J.A i.succ
  E := elec J.AF J.A J.dA
  B := magn J.AF J.A J.dA
  H := J.H
  Pm := frV J.AF J.A J.H J.dH 0
  Q := fun a => frV J.AF J.A J.H J.dH a.succ
  ψ := J.ψ
  X := fun a => J.Xs SM.D J.ψ J.cψ a.succ
  ψb := J.ψb
  Xb := fun a => J.Xs SM.Db J.ψb J.cψb a.succ

/-- **The coordinate derivative jets `∂_γ𝒰`** of the state components (product rule on the jets). -/
def dstate (γ : Fin 4) : State 𝔤 V S S' where
  g := fun μ ν => J.FJ.dg γ μ ν
  p := fun μ ν => J.AF.dpJ J.FJ.de (fun α => J.FJ.dg α μ ν) (fun α β => J.FJ.ddg α β μ ν) γ
  q := fun a μ ν => J.AF.dqJ J.FJ.de (fun α => J.FJ.dg α μ ν) (fun α β => J.FJ.ddg α β μ ν) γ a
  A := fun i => J.dA γ i.succ
  E := fun a => delec J.AF J.FJ.de J.A J.dA J.ddA γ a
  B := fun a => dmagn J.AF J.FJ.de J.A J.dA J.ddA γ a
  H := J.dH γ
  Pm := dfrV J.AF J.FJ.de J.A J.dA J.H J.dH J.ddH γ 0
  Q := fun a => dfrV J.AF J.FJ.de J.A J.dA J.H J.dH J.ddH γ a.succ
  ψ := J.cψ γ
  X := fun a => J.dXs SM.D J.ψ J.cψ J.ccψ γ a.succ
  ψb := J.cψb γ
  Xb := fun a => J.dXs SM.Db J.ψb J.cψb J.ccψb γ a.succ

end ActualJet

/-! ### First jets and their reconstruction from the state -/

/-- The first jets entering the lower-order terms: metric and frame first jets, the gauge
potential, field strength, Higgs field and covariant gradient, both spinors with all four frame
covariant derivatives. -/
structure FirstJet (𝔤 V S S' : Type*) where
  g : Fin 4 → Fin 4 → ℝ
  gi : Fin 4 → Fin 4 → ℝ
  dg : Fin 4 → Fin 4 → Fin 4 → ℝ
  AF : AdaptedFrame
  de : Fin 4 → Fin 4 → Fin 4 → ℝ
  A : Fin 4 → 𝔤
  F : Fin 4 → Fin 4 → 𝔤
  H : V
  DH : Fin 4 → V
  ψ : S
  X : Fin 4 → S
  ψb : S'
  Xb : Fin 4 → S'

namespace ActualJet

variable (J : ActualJet 𝔤 V S S') (SM : SMData 𝔤 V S S')

/-- The first jets of an actual jet, with the residual-free normal spinor jets. -/
def firstJet : FirstJet 𝔤 V S S' where
  g := J.FJ.g
  gi := J.FJ.gi
  dg := J.FJ.dg
  AF := J.AF
  de := J.FJ.de
  A := J.A
  F := Fm J.A J.dA
  H := J.H
  DH := ActualJetGauge.DH J.A J.H J.dH
  ψ := J.ψ
  X := J.Xn SM.D J.ψ J.cψ
  ψb := J.ψb
  Xb := J.Xn SM.Db J.ψb J.cψb

end ActualJet

/-- The inverse metric as a function of the metric (matrix inverse). -/
def ginvOf (g : Fin 4 → Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ := fun i j => (Matrix.of g)⁻¹ i j

open scoped Classical in
/-- The fixed algebraic adapted frame of an inverse metric (`frameOf` on the Lorentzian chart). -/
def frameU (gi : Fin 4 → Fin 4 → ℝ) : AdaptedFrame :=
  if h : IsLorChart gi then frameOf gi h else flatFrame

/-- **Reconstruction of the first jets from the state**: `g⁻¹` (matrix inverse), the frame
`frameOf(g)`, `∂g` from `(p, q)` through the coframe, the frame derivative jets
`frameJet(g⁻¹, ∂g⁻¹)`, `A = (0, A_i)`, `F` from `(E, B)`, `DH` from `(Π, Q)`, and the normal
spinor jets from `eq:normal-spinor-jet` (residual-free part). -/
def recon (SM : SMData 𝔤 V S S') (U : State 𝔤 V S S') : FirstJet 𝔤 V S S' :=
  let gi := ginvOf U.g
  let AF := frameU gi
  let θ := cof U.g lorentzSign AF.fr
  let dg := fun γ μ ν => ∑ X, θ X γ * gradOfpq (U.p μ ν) (fun a => U.q a μ ν) X
  { g := U.g
    gi := gi
    dg := dg
    AF := AF
    de := frameJet gi (fun γ l σ => dginv gi dg γ l σ)
    A := Fin.cases 0 U.A
    F := fun μ ν => ∑ X, ∑ Y, (θ X μ * θ Y ν) • fieldOfEB U.E U.B X Y
    H := U.H
    DH := fun μ => ∑ X, θ X μ • gradOfPQ U.Pm U.Q X
    ψ := U.ψ
    X := Fin.cases (XnatU SM.D U.ψ U.X U.H) U.X
    ψb := U.ψb
    Xb := Fin.cases (XnatU SM.Db U.ψb U.Xb U.H) U.Xb }

namespace ActualJet

variable (J : ActualJet 𝔤 V S S') (SM : SMData 𝔤 V S S')

theorem ginvOf_eq : ginvOf J.FJ.g = J.FJ.gi := by
  have h : Matrix.of J.FJ.g * Matrix.of J.FJ.gi = 1 := by
    ext a c
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact J.FJ.hinv a c
  funext i j
  unfold ginvOf
  rw [Matrix.inv_eq_right_inv h]
  rfl

theorem frameU_eq' : frameU J.FJ.gi = J.AF := by
  unfold frameU
  rw [dif_pos J.chart]
  rfl

theorem cof_eq : cof J.FJ.g lorentzSign J.AF.fr = cof J.FJ.g J.FJ.ε J.FJ.e := by
  rw [J.sign]
  funext A μ
  unfold cof
  simp only [J.hfr]

/-- **The state determines the first jets** (up to the residual in the normal spinor jets):
`recon(𝒰(z)) = (g, g⁻¹, ∂g, frame, ∂frame, A, F, H, DH, Ψ, X^♮, Ψ̄, X̄^♮)`. -/
theorem recon_state : recon SM (J.state SM) = J.firstJet SM := by
  have hdg : (fun γ μ ν => ∑ X, cof J.FJ.g J.FJ.ε J.FJ.e X γ *
      gradOfpq (J.AF.pJ (fun α => J.FJ.dg α μ ν)) (fun a => J.AF.qJ (fun α => J.FJ.dg α μ ν) a)
        X) = J.FJ.dg := by
    funext γ μ ν
    rw [dg_recon J.FJ J.AF J.hfr γ μ ν]
  unfold recon firstJet state
  simp only [J.ginvOf_eq, J.frameU_eq', J.cof_eq]
  rw [hdg]
  congr 1
  · funext γ A μ
    rw [J.dframe]
  · funext μ
    induction μ using Fin.cases with
    | zero => exact J.temporal.symm
    | succ i => rfl
  · funext μ ν
    rw [Fm_recon J.AF J.A J.dA J.FJ J.hfr μ ν]
  · funext μ
    rw [DH_recon J.AF J.A J.FJ J.hfr J.H J.dH μ]

end ActualJet

end Derived

/-! ### The lower-order terms as functions of the first jets -/

section Lower

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [LieRingModule 𝔤 V] [LieModule ℝ 𝔤 V]
variable {S : Type*} [AddCommGroup S] [Module ℝ S]
variable {S' : Type*} [AddCommGroup S'] [Module ℝ S']
variable {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀]

/-- The lower-order part of the Yang–Mills divergence, from the field-strength array. -/
def ymCorrF (A : Fin 4 → 𝔤) (F : Fin 4 → Fin 4 → 𝔤) (gi : Fin 4 → Fin 4 → ℝ)
    (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) (ν : Fin 4) : 𝔤 :=
  ∑ μ, ∑ ρ, gi μ ρ • (∑ l, (Γ l ρ μ • F l ν + Γ l ρ ν • F μ l) - ⁅A ρ, F μ ν⁆)

/-- The `E`-row lower-order term from the field-strength array. -/
def LEf (AF : AdaptedFrame) (de : Fin 4 → Fin 4 → Fin 4 → ℝ) (A : Fin 4 → 𝔤)
    (F : Fin 4 → Fin 4 → 𝔤) (gi : Fin 4 → Fin 4 → ℝ) (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (a : Fin 3) : 𝔤 :=
  lowT AF de F 0 0 a.succ - ∑ b : Fin 3, lowT AF de F b.succ b.succ a.succ -
    ∑ ν, AF.fr a.succ ν • ymCorrF A F gi Γ ν

theorem LE_eq (AF : AdaptedFrame) (de : Fin 4 → Fin 4 → Fin 4 → ℝ) (A : Fin 4 → 𝔤)
    (dA : Fin 4 → Fin 4 → 𝔤) (gi : Fin 4 → Fin 4 → ℝ) (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (a : Fin 3) : LE AF de A dA gi Γ a = LEf AF de A (Fm A dA) gi Γ a := rfl

/-- The bracket contraction of the `B`-row from the field-strength array. -/
def brCf (AF : AdaptedFrame) (A : Fin 4 → 𝔤) (F : Fin 4 → Fin 4 → 𝔤) (b c : Fin 4) : 𝔤 :=
  ∑ μ, ∑ ν, ∑ γ, (AF.fr b μ * AF.fr c ν * AF.fr 0 γ) •
    (⁅A γ, F μ ν⁆ + ⁅A μ, F ν γ⁆ + ⁅A ν, F γ μ⁆)

/-- The `B`-row lower-order term from the field-strength array. -/
def LBf (AF : AdaptedFrame) (de : Fin 4 → Fin 4 → Fin 4 → ℝ) (A : Fin 4 → 𝔤)
    (F : Fin 4 → Fin 4 → 𝔤) (a : Fin 3) : 𝔤 :=
  -(1 / 2 : ℝ) • ∑ b, ∑ c, eps3 a b c • (lowT AF de F 0 b.succ c.succ +
    lowT AF de F b.succ c.succ 0 + lowT AF de F c.succ 0 b.succ - brCf AF A F b.succ c.succ)

theorem LB_eq (AF : AdaptedFrame) (de : Fin 4 → Fin 4 → Fin 4 → ℝ) (A : Fin 4 → 𝔤)
    (dA : Fin 4 → Fin 4 → 𝔤) (a : Fin 3) : LB AF de A dA a = LBf AF de A (Fm A dA) a := rfl

/-- `e_C(D_{e_B}H)` lower-order part from the covariant gradient array. -/
def lowVf (AF : AdaptedFrame) (de : Fin 4 → Fin 4 → Fin 4 → ℝ) (DH : Fin 4 → V) (C B : Fin 4) :
    V :=
  ∑ γ, AF.fr C γ • ∑ μ, de γ B μ • DH μ

/-- The `Q`-row lower-order term from the arrays. -/
def LQf (AF : AdaptedFrame) (de : Fin 4 → Fin 4 → Fin 4 → ℝ) (A : Fin 4 → 𝔤)
    (F : Fin 4 → Fin 4 → 𝔤) (H : V) (DH : Fin 4 → V) (a : Fin 3) : V :=
  lowVf AF de DH 0 a.succ - lowVf AF de DH a.succ 0 +
    ∑ γ, ∑ μ, (AF.fr 0 γ * AF.fr a.succ μ) • (⁅F γ μ, H⁆ + ⁅A μ, DH γ⁆ - ⁅A γ, DH μ⁆)

theorem LQ_eq (AF : AdaptedFrame) (de : Fin 4 → Fin 4 → Fin 4 → ℝ) (A : Fin 4 → 𝔤)
    (dA : Fin 4 → Fin 4 → 𝔤) (H : V) (dH : Fin 4 → V) (a : Fin 3) :
    LQ AF de A dA H dH a = LQf AF de A (Fm A dA) H (ActualJetGauge.DH A H dH) a := rfl

/-- The `Π`-row lower-order term from the arrays. -/
def LPif (AF : AdaptedFrame) (de : Fin 4 → Fin 4 → Fin 4 → ℝ) (A : Fin 4 → 𝔤) (DH : Fin 4 → V)
    (gi : Fin 4 → Fin 4 → ℝ) (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) : V :=
  lowVf AF de DH 0 0 - ∑ b : Fin 3, lowVf AF de DH b.succ b.succ -
    ∑ μ, ∑ ρ, gi μ ρ • (∑ l, Γ l ρ μ • DH l - ⁅A ρ, DH μ⁆)

theorem LPi_eq (AF : AdaptedFrame) (de : Fin 4 → Fin 4 → Fin 4 → ℝ) (A : Fin 4 → 𝔤) (H : V)
    (dH : Fin 4 → V) (gi : Fin 4 → Fin 4 → ℝ) (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    LPi AF de A H dH gi Γ = LPif AF de A (ActualJetGauge.DH A H dH) gi Γ := rfl

/-- The Levi-Civita frame connection coefficients `G_{ABC} = g(∇_{e_A}e_B, e_C)` as a function of
the metric and frame first jets. -/
def Gfun (g gi : Fin 4 → Fin 4 → ℝ) (dg : Fin 4 → Fin 4 → Fin 4 → ℝ) (e : Fin 4 → Fin 4 → ℝ)
    (de : Fin 4 → Fin 4 → Fin 4 → ℝ) (A B C : Fin 4) : ℝ :=
  ∑ γ, e A γ * ipg g (fun μ => cv1 (chr gi dg) (e B) (fun γ μ => de γ B μ) γ μ) (e C)

/-- The twisted spin connection `ω_A = ¼ε_cε_dG_{Acd}c_cc_d + ρ(A(e_A))` from the first jets. -/
def omegaU (D : DiracData 𝔤 V S₀) (g gi : Fin 4 → Fin 4 → ℝ) (dg : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (e : Fin 4 → Fin 4 → ℝ) (de : Fin 4 → Fin 4 → Fin 4 → ℝ) (A : Fin 4 → 𝔤) (B : Fin 4) :
    Module.End ℝ S₀ :=
  spinPart D.Fr (Gfun g gi dg e de B) + ∑ μ, e B μ • D.ρ (A μ)

/-- The frame gauge curvature `ρ(F(e_b, e_a))` from the field-strength array. -/
def rhoF (D : DiracData 𝔤 V S₀) (e : Fin 4 → Fin 4 → ℝ) (F : Fin 4 → Fin 4 → 𝔤) (b a : Fin 4) :
    Module.End ℝ S₀ :=
  ∑ μ, ∑ ν, (e b μ * e a ν) • D.ρ (F μ ν)

/-- Frame components of a coordinate 2-tensor. -/
def frT2 (e : Fin 4 → Fin 4 → ℝ) (T : Fin 4 → Fin 4 → ℝ) (a b : Fin 4) : ℝ :=
  ∑ μ, ∑ ν, e a μ * e b ν * T μ ν

/-- Frame components of the covariant Higgs gradient. -/
def DHf (e : Fin 4 → Fin 4 → ℝ) (DH : Fin 4 → V) (a : Fin 4) : V := ∑ μ, e a μ • DH μ

/-- The lower-order term of the prolonged spinor row (residual-free part; with the stress
`T₀` in the Ricci elimination). -/
def XrowF (D : DiracData 𝔤 V S₀) (κ Λ : ℝ) (g gi : Fin 4 → Fin 4 → ℝ)
    (dg : Fin 4 → Fin 4 → Fin 4 → ℝ) (AF : AdaptedFrame) (de : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (A : Fin 4 → 𝔤) (F : Fin 4 → Fin 4 → 𝔤) (H : V) (DH : Fin 4 → V) (ψ : S₀) (X : Fin 4 → S₀)
    (T0 : Fin 4 → Fin 4 → ℝ) (a : Fin 4) : S₀ :=
  -(omegaU D g gi dg AF.fr de A 0 • X a) +
    ∑ c, lcΓ lorentzSign (Gfun g gi dg AF.fr de) 0 a c • X c +
    D.Fr.c 0 • ∑ i : Fin 3, D.Fr.c i.succ • (omegaU D g gi dg AF.fr de A i.succ • X a -
      ∑ c, lcΓ lorentzSign (Gfun g gi dg AF.fr de) i.succ a c • X c) -
    D.Fr.c 0 • (mass D.m0 D.L H • X a + D.L (DHf AF.fr DH a) • ψ +
      ((1 / 2 : ℝ) • ∑ b, (lorentzSign b * (κ * frT2 AF.fr (traceRev g gi T0) a b +
        Λ * (if a = b then lorentzSign a else 0))) • D.Fr.c b) • ψ +
      (∑ b, lorentzSign b • (D.Fr.c b * rhoF D AF.fr F b a)) • ψ)

/-- The residual multiplier of the prolonged spinor row (normal-jet residual, connection times
`r_D`, Einstein residual and residual stress in the Ricci elimination). -/
def XrowB (D : DiracData 𝔤 V S₀) (κ : ℝ) (g gi : Fin 4 → Fin 4 → ℝ)
    (dg : Fin 4 → Fin 4 → Fin 4 → ℝ) (AF : AdaptedFrame) (de : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (A : Fin 4 → 𝔤) (ψ : S₀) (a : Fin 4) (rD : S₀) (Etr T1 : Fin 4 → Fin 4 → ℝ) : S₀ :=
  -(lcΓ lorentzSign (Gfun g gi dg AF.fr de) 0 a 0 • (D.Fr.c 0 • rD)) +
    D.Fr.c 0 • ∑ i : Fin 3, D.Fr.c i.succ •
      (lcΓ lorentzSign (Gfun g gi dg AF.fr de) i.succ a 0 • (D.Fr.c 0 • rD)) -
    D.Fr.c 0 • (omegaU D g gi dg AF.fr de A a • rD +
      ((1 / 2 : ℝ) • ∑ b, (lorentzSign b * (frT2 AF.fr Etr a b -
        κ * frT2 AF.fr (traceRev g gi T1) a b)) • D.Fr.c b) • ψ)

/-- The Dirac head-row lower-order term `(c_0Σ_ac_aω_a - ω_0 - c_0𝓜(H))Ψ`. -/
def psiF (D : DiracData 𝔤 V S₀) (g gi : Fin 4 → Fin 4 → ℝ) (dg : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (AF : AdaptedFrame) (de : Fin 4 → Fin 4 → Fin 4 → ℝ) (A : Fin 4 → 𝔤) (H : V) (ψ : S₀) :
    S₀ :=
  (D.Fr.c 0 * ∑ a : Fin 3, D.Fr.c a.succ * omegaU D g gi dg AF.fr de A a.succ -
    omegaU D g gi dg AF.fr de A 0 - D.Fr.c 0 * mass D.m0 D.L H) • ψ

/-- **The complete off-shell stress** `T^{SM} = T^{YM} + T^H + T^D` on the first jets
(`eq:YM-stress`, `eq:H-stress`, the Dirac–Yukawa form of the theory data). -/
def stressF (SM : SMData 𝔤 V S S') (fj : FirstJet 𝔤 V S S') (μ ν : Fin 4) : ℝ :=
  ymStressB SM.ipG fj.g fj.gi fj.F μ ν + higgsStressB SM.ipV SM.lamH SM.vH fj.g fj.gi fj.H fj.DH μ ν +
    SM.TD.coord fj.g lorentzSign fj.AF.fr fj.H fj.ψ fj.X fj.ψb fj.Xb μ ν

/-- The residuals of `eq:actual-jet-writer`: `(𝓔^{tr}, r^A, r_H, r_D, r̄_D)`. -/
structure Res (𝔤 V S S' : Type*) where
  Etr : Fin 4 → Fin 4 → ℝ
  rA : Fin 4 → 𝔤
  rH : V
  rD : S
  rDb : S'

/-- The residual part `𝒯_1(r_D, r̄_D)` of the stress. -/
def stressR (SM : SMData 𝔤 V S S') (fj : FirstJet 𝔤 V S S') (r : Res 𝔤 V S S') (μ ν : Fin 4) :
    ℝ :=
  SM.TD.stressRes fj.g lorentzSign fj.AF.fr fj.ψ fj.ψb (SM.D.Fr.c 0 • r.rD)
    (SM.Db.Fr.c 0 • r.rDb) μ ν

/-- The lower-order terms `𝓕` evaluated on first jets. -/
def lowerOf (SM : SMData 𝔤 V S S') (fj : FirstJet 𝔤 V S S') : State 𝔤 V S S' where
  g := fun μ ν => fj.dg 0 μ ν
  p := fun μ ν => fj.AF.N * (fj.AF.Lp fj.de (fun α => fj.dg α μ ν) - 2 * qRem fj.g fj.gi fj.dg μ ν +
    2 * SM.κ * traceRev fj.g fj.gi (stressF SM fj) μ ν + 2 * SM.Λ * fj.g μ ν)
  q := fun a μ ν => fj.AF.N * fj.AF.Lq fj.de (fun α => fj.dg α μ ν) a
  A := fun i => fj.F 0 i.succ
  E := fun a => fj.AF.N • (LEf fj.AF fj.de fj.A fj.F fj.gi (chr fj.gi fj.dg) a -
    ∑ ν, fj.AF.fr a.succ ν • SM.Jcur fj.g fj.gi fj.H fj.DH fj.ψ fj.ψb ν)
  B := fun a => fj.AF.N • LBf fj.AF fj.de fj.A fj.F a
  H := fj.DH 0
  Pm := fj.AF.N • (LPif fj.AF fj.de fj.A fj.DH fj.gi (chr fj.gi fj.dg) -
    SM.SH fj.g fj.gi fj.H fj.ψ fj.ψb)
  Q := fun a => fj.AF.N • LQf fj.AF fj.de fj.A fj.F fj.H fj.DH a
  ψ := fj.AF.N • psiF SM.D fj.g fj.gi fj.dg fj.AF fj.de fj.A fj.H fj.ψ
  X := fun a => fj.AF.N • XrowF SM.D SM.κ SM.Λ fj.g fj.gi fj.dg fj.AF fj.de fj.A fj.F fj.H fj.DH
    fj.ψ fj.X (stressF SM fj) a.succ
  ψb := fj.AF.N • psiF SM.Db fj.g fj.gi fj.dg fj.AF fj.de fj.A fj.H fj.ψb
  Xb := fun a => fj.AF.N • XrowF SM.Db SM.κ SM.Λ fj.g fj.gi fj.dg fj.AF fj.de fj.A fj.F fj.H
    fj.DH fj.ψb fj.Xb (stressF SM fj) a.succ

/-- **The forcing `𝓕(𝒰)`** of `eq:actual-jet-writer`: the lower-order terms on the reconstructed
first jets — a function of the state alone. -/
def Fsys (SM : SMData 𝔤 V S S') (U : State 𝔤 V S S') : State 𝔤 V S S' := lowerOf SM (recon SM U)

/-- **The residual term `𝓑(𝒰)(𝓔, r^A, r_H, r_D, r̄_D)`** of `eq:actual-jet-writer` (linear in the
residuals, no derivative of them). -/
def Bsys (SM : SMData 𝔤 V S S') (U : State 𝔤 V S S') (r : Res 𝔤 V S S') : State 𝔤 V S S' :=
  let fj := recon SM U
  { g := fun _ _ => 0
    p := fun μ ν => 2 * fj.AF.N * r.Etr μ ν -
      2 * fj.AF.N * SM.κ * traceRev fj.g fj.gi (stressR SM fj r) μ ν
    q := fun _ _ _ => 0
    A := fun _ => 0
    E := fun a => -(fj.AF.N • ∑ ν, fj.AF.fr a.succ ν • r.rA ν)
    B := fun _ => 0
    H := 0
    Pm := -(fj.AF.N • r.rH)
    Q := fun _ => 0
    ψ := -(fj.AF.N • (SM.D.Fr.c 0 • r.rD))
    X := fun a => fj.AF.N • XrowB SM.D SM.κ fj.g fj.gi fj.dg fj.AF fj.de fj.A fj.ψ a.succ r.rD
      r.Etr (stressR SM fj r)
    ψb := -(fj.AF.N • (SM.Db.Fr.c 0 • r.rDb))
    Xb := fun a => fj.AF.N • XrowB SM.Db SM.κ fj.g fj.gi fj.dg fj.AF fj.de fj.A fj.ψb a.succ r.rDb
      r.Etr (stressR SM fj r) }

/-- **The differentiated Dirac residual term `𝒬^j(g)∂_j(r_D, r̄_D)`**: only spatial derivatives
of the Dirac residuals, with coefficients depending on the metric only (through the frame). -/
def Qsys (SM : SMData 𝔤 V S S') (U : State 𝔤 V S S') (j : Fin 3) (dr : S) (drb : S') :
    State 𝔤 V S S' :=
  let AF := frameU (ginvOf U.g)
  { g := fun _ _ => 0
    p := fun _ _ => 0
    q := fun _ _ _ => 0
    A := fun _ => 0
    E := fun _ => 0
    B := fun _ => 0
    H := 0
    Pm := 0
    Q := fun _ => 0
    ψ := 0
    X := fun a => -(AF.N • (SM.D.Fr.c 0 • (AF.E a j • dr)))
    ψb := 0
    Xb := fun a => -(AF.N • (SM.Db.Fr.c 0 • (AF.E a j • drb))) }

/-- **The gauge forcing `𝔊(𝒰; C, ∂C) = 𝒥_C C + 𝒥_C^0∂_tC + Σ_j𝒥_C^j∂_jC`**
(`eq:actual-jet-gauge-forcing`): only the metric `p`-rows are forced. -/
def Gsys (AF : AdaptedFrame) (g gi : Fin 4 → Fin 4 → ℝ) (dg : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (ddg : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) : State 𝔤 V S S' where
  g := fun _ _ => 0
  p := fun μ ν => ∑ l, JC AF g gi dg μ ν l * C gi dg l + ∑ l, Jd AF g 0 μ ν l * dC gi dg ddg 0 l +
    ∑ j : Fin 3, ∑ l, Jd AF g j.succ μ ν l * dC gi dg ddg j.succ l
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

/-- **`eq:actual-jet-writer`, blockwise**: `∂_t𝒰 + Σ_j𝒜^j∂_j𝒰 = 𝓕 + 𝓑 + Σ_j𝒬^j + 𝔊` in every
block of the state. -/
def WriterEq (dU : Fin 4 → State 𝔤 V S S') (P : Fin 3 → State 𝔤 V S S' → State 𝔤 V S S')
    (F B G : State 𝔤 V S S') (Qj : Fin 3 → State 𝔤 V S S') : Prop :=
  (∀ μ ν, (dU 0).g μ ν + ∑ j, (P j (dU j.succ)).g μ ν =
    F.g μ ν + B.g μ ν + ∑ j, (Qj j).g μ ν + G.g μ ν) ∧
  (∀ μ ν, (dU 0).p μ ν + ∑ j, (P j (dU j.succ)).p μ ν =
    F.p μ ν + B.p μ ν + ∑ j, (Qj j).p μ ν + G.p μ ν) ∧
  (∀ a μ ν, (dU 0).q a μ ν + ∑ j, (P j (dU j.succ)).q a μ ν =
    F.q a μ ν + B.q a μ ν + ∑ j, (Qj j).q a μ ν + G.q a μ ν) ∧
  (∀ i, (dU 0).A i + ∑ j, (P j (dU j.succ)).A i = F.A i + B.A i + ∑ j, (Qj j).A i + G.A i) ∧
  (∀ a, (dU 0).E a + ∑ j, (P j (dU j.succ)).E a = F.E a + B.E a + ∑ j, (Qj j).E a + G.E a) ∧
  (∀ a, (dU 0).B a + ∑ j, (P j (dU j.succ)).B a = F.B a + B.B a + ∑ j, (Qj j).B a + G.B a) ∧
  ((dU 0).H + ∑ j, (P j (dU j.succ)).H = F.H + B.H + ∑ j, (Qj j).H + G.H) ∧
  ((dU 0).Pm + ∑ j, (P j (dU j.succ)).Pm = F.Pm + B.Pm + ∑ j, (Qj j).Pm + G.Pm) ∧
  (∀ a, (dU 0).Q a + ∑ j, (P j (dU j.succ)).Q a = F.Q a + B.Q a + ∑ j, (Qj j).Q a + G.Q a) ∧
  ((dU 0).ψ + ∑ j, (P j (dU j.succ)).ψ = F.ψ + B.ψ + ∑ j, (Qj j).ψ + G.ψ) ∧
  (∀ a, (dU 0).X a + ∑ j, (P j (dU j.succ)).X a = F.X a + B.X a + ∑ j, (Qj j).X a + G.X a) ∧
  ((dU 0).ψb + ∑ j, (P j (dU j.succ)).ψb = F.ψb + B.ψb + ∑ j, (Qj j).ψb + G.ψb) ∧
  (∀ a, (dU 0).Xb a + ∑ j, (P j (dU j.succ)).Xb a = F.Xb a + B.Xb a + ∑ j, (Qj j).Xb a + G.Xb a)

end Lower

/-! ### The residuals of an actual jet -/

section Residuals

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [LieRingModule 𝔤 V] [LieModule ℝ 𝔤 V]
variable {S : Type*} [AddCommGroup S] [Module ℝ S]
variable {S' : Type*} [AddCommGroup S'] [Module ℝ S']

namespace ActualJet

variable (J : ActualJet 𝔤 V S S') (SM : SMData 𝔤 V S S')

/-- The complete off-shell stress of the actual jet (with the actual normal spinor jets). -/
def Tact (μ ν : Fin 4) : ℝ :=
  ymStressB SM.ipG J.FJ.g J.FJ.gi (Fm J.A J.dA) μ ν +
    higgsStressB SM.ipV SM.lamH SM.vH J.FJ.g J.FJ.gi J.H (ActualJetGauge.DH J.A J.H J.dH) μ ν +
    SM.TD.coord J.FJ.g lorentzSign J.AF.fr J.H J.ψ (J.Xs SM.D J.ψ J.cψ) J.ψb
      (J.Xs SM.Db J.ψb J.cψb) μ ν

/-- **The physical residuals** of the actual jet: the trace-reversed Einstein residual
`𝓔^{tr}` (`𝓔 = G + Λg - κT^{SM}`), the Yang–Mills residual `r^A = ∇^μF_{μν} - J_ν`, the Higgs
residual `r_H = □_AH - S_H` and the two Dirac residuals. -/
def res : Res 𝔤 V S S' where
  Etr := traceRev J.FJ.g J.FJ.gi (fun a b => einstein J.FJ.g J.FJ.gi J.FJ.dg J.FJ.ddg a b +
    SM.Λ * J.FJ.g a b - SM.κ * J.Tact SM a b)
  rA := ymRes J.A J.dA J.ddA J.FJ.gi (chr J.FJ.gi J.FJ.dg)
    (SM.Jcur J.FJ.g J.FJ.gi J.H (ActualJetGauge.DH J.A J.H J.dH) J.ψ J.ψb)
  rH := higgsRes J.A J.dA J.H J.dH J.ddH J.FJ.gi (chr J.FJ.gi J.FJ.dg)
    (SM.SH J.FJ.g J.FJ.gi J.H J.ψ J.ψb)
  rD := J.rD SM.D J.ψ J.cψ
  rDb := J.rD SM.Db J.ψb J.cψb

/-- **Clause (d): the stress is the tangential-state stress plus a term linear in the Dirac
residuals**: `T^{SM}(z) = 𝒯_0(𝒰) - 𝒯_1(𝒰)(c_0r_D, c̄_0r̄_D)`. -/
theorem Tact_eq (μ ν : Fin 4) :
    J.Tact SM μ ν = stressF SM (recon SM (J.state SM)) μ ν -
      stressR SM (recon SM (J.state SM)) (J.res SM) μ ν := by
  rw [J.recon_state SM]
  unfold Tact stressF stressR firstJet res
  simp only
  rw [SM.TD.stress_elimination J.FJ.g lorentzSign J.AF.fr J.H J.ψ (J.Xs SM.D J.ψ J.cψ)
    (J.Xn SM.D J.ψ J.cψ) J.ψb (J.Xs SM.Db J.ψb J.cψb) (J.Xn SM.Db J.ψb J.cψb)
    (SM.D.Fr.c 0 • J.rD SM.D J.ψ J.cψ) (SM.Db.Fr.c 0 • J.rD SM.Db J.ψb J.cψb)
    (by rw [J.Xs_eq_Xn]; simp) (fun a => by rw [J.Xs_eq_Xn]; simp [Fin.succ_ne_zero])
    (by rw [J.Xs_eq_Xn]; simp) (fun a => by rw [J.Xs_eq_Xn]; simp [Fin.succ_ne_zero]) μ ν]
  ring

end ActualJet

end Residuals

/-! ### The rows of the assembled system -/

section Rows

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [LieRingModule 𝔤 V] [LieModule ℝ 𝔤 V]
variable {S : Type*} [AddCommGroup S] [Module ℝ S]
variable {S' : Type*} [AddCommGroup S'] [Module ℝ S']
variable {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀]

theorem traceRev_sub (g gi : Fin 4 → Fin 4 → ℝ) (T T' : Fin 4 → Fin 4 → ℝ) (μ ν : Fin 4) :
    traceRev g gi (fun a b => T a b - T' a b) μ ν = traceRev g gi T μ ν - traceRev g gi T' μ ν := by
  unfold traceRev trG
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

namespace ActualJet

variable (J : ActualJet 𝔤 V S S') (SM : SMData 𝔤 V S S')

theorem frameU_state : frameU (ginvOf (J.state SM).g) = J.AF := by
  show frameU (ginvOf J.FJ.g) = _
  rw [J.ginvOf_eq, J.frameU_eq']

theorem e_eq : J.FJ.e = J.AF.fr := funext₂ J.hfr

theorem G_eq : J.FJ.G = Gfun J.FJ.g J.FJ.gi J.FJ.dg J.AF.fr J.FJ.de := by
  rw [← J.e_eq]; rfl

/-- The twisted spin connection of the actual jet is `omegaU` of its first jets. -/
theorem LJ_ω (D : DiracData 𝔤 V S₀) (B : Fin 4) :
    (J.LJ D).ω B = omegaU D J.FJ.g J.FJ.gi J.FJ.dg J.AF.fr J.FJ.de J.A B := by
  show spinPart D.Fr (J.FJ.G B) + ∑ μ, J.FJ.e B μ • D.ρ (J.A μ) = _
  rw [J.G_eq, J.e_eq]; rfl

theorem LJ_G (D : DiracData 𝔤 V S₀) :
    lcΓ D.Fr.ε (J.LJ D).G = lcΓ lorentzSign (Gfun J.FJ.g J.FJ.gi J.FJ.dg J.AF.fr J.FJ.de) := by
  rw [J.hε, J.sign]
  show lcΓ lorentzSign J.FJ.G = _
  rw [J.G_eq]

/-- The frame gauge curvature of the actual jet is `ρ(F(e_b, e_a))`. -/
theorem LJ_F (D : DiracData 𝔤 V S₀) (b a : Fin 4) :
    (J.LJ D).F b a = rhoF D J.AF.fr (Fm J.A J.dA) b a := by
  unfold LJ
  rw [FrameJet.frameF_eq]
  unfold rhoF
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  rw [J.hfr, J.hfr]
  congr 1
  unfold Fm fieldStrength
  rw [map_add, map_sub, D.ρ_lie]

/-- The `g`-head rows: `∂_tg_{μν}` is algebraic in the state. -/
theorem row_g (μ ν : Fin 4) :
    (J.dstate SM 0).g μ ν + ∑ j, (princ (frameU (ginvOf (J.state SM).g)) SM.D.Fr SM.Db.Fr j
      (J.dstate SM j.succ)).g μ ν =
    (Fsys SM (J.state SM)).g μ ν + (Bsys SM (J.state SM) (J.res SM)).g μ ν +
      ∑ j, (Qsys SM (J.state SM) j (J.drD SM.D J.ψ J.cψ J.ccψ j.succ)
        (J.drD SM.Db J.ψb J.cψb J.ccψb j.succ)).g μ ν +
      (Gsys (𝔤 := 𝔤) (V := V) (S := S) (S' := S') (frameU (ginvOf (J.state SM).g))
        (J.state SM).g (ginvOf (J.state SM).g) J.FJ.dg J.FJ.ddg).g μ ν := by
  simp only [princ, Fsys, J.recon_state, lowerOf, firstJet, Bsys, Qsys, Gsys, dstate,
    Finset.sum_const_zero, add_zero]

end ActualJet

end Rows
namespace ActualJet

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [LieRingModule 𝔤 V] [LieModule ℝ 𝔤 V]
variable {S : Type*} [AddCommGroup S] [Module ℝ S]
variable {S' : Type*} [AddCommGroup S'] [Module ℝ S']
variable {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀]

variable (J : ActualJet 𝔤 V S S') (SM : SMData 𝔤 V S S')

/-- The metric `p`-rows (`lem:harmonic-defect-forcing`, gauge forcing `𝔊`). -/
theorem row_p (μ ν : Fin 4) :
    (J.dstate SM 0).p μ ν + ∑ j, (princ (frameU (ginvOf (J.state SM).g)) SM.D.Fr SM.Db.Fr j
      (J.dstate SM j.succ)).p μ ν =
    (Fsys SM (J.state SM)).p μ ν + (Bsys SM (J.state SM) (J.res SM)).p μ ν +
      ∑ j, (Qsys SM (J.state SM) j (J.drD SM.D J.ψ J.cψ J.ccψ j.succ)
        (J.drD SM.Db J.ψb J.cψb J.ccψb j.succ)).p μ ν +
      (Gsys (𝔤 := 𝔤) (V := V) (S := S) (S' := S') (frameU (ginvOf (J.state SM).g))
        (J.state SM).g (ginvOf (J.state SM).g) J.FJ.dg J.FJ.ddg).p μ ν := by
  have hrow := metric_p_row J.AF J.FJ.g J.FJ.gi J.FJ.dg J.FJ.ddg J.hadapt J.FJ.gi_symm J.FJ.hinv
    J.FJ.ddg_symm1 J.FJ.ddg_symm2 J.FJ.de (J.Tact SM) SM.Λ SM.κ μ ν
  have hT : J.Tact SM = fun a b => stressF SM (J.firstJet SM) a b -
      stressR SM (J.firstJet SM) (J.res SM) a b := by
    funext a b; rw [J.Tact_eq, J.recon_state]
  have hG := gaugeForce_eq J.AF J.FJ.g J.FJ.gi J.FJ.dg J.FJ.ddg J.FJ.dg_symm μ ν
  have hTr : traceRev J.FJ.g J.FJ.gi (J.Tact SM) μ ν =
      traceRev J.FJ.g J.FJ.gi (stressF SM (J.firstJet SM)) μ ν -
        traceRev J.FJ.g J.FJ.gi (stressR SM (J.firstJet SM) (J.res SM)) μ ν := by
    rw [hT, traceRev_sub]
  rw [hTr, hG] at hrow
  simp only [princ, Fsys, Bsys, Qsys, Gsys, dstate]
  simp only [J.recon_state]
  simp only [lowerOf, firstJet, state, J.ginvOf_eq, J.frameU_eq', Finset.sum_const_zero, add_zero]
  have hs : ∑ j : Fin 3, (-(J.AF.β j * J.AF.dpJ J.FJ.de (fun α => J.FJ.dg α μ ν)
      (fun α β => J.FJ.ddg α β μ ν) j.succ) - J.AF.N * ∑ a, J.AF.E a j *
        J.AF.dqJ J.FJ.de (fun α => J.FJ.dg α μ ν) (fun α β => J.FJ.ddg α β μ ν) j.succ a) =
      -∑ j, J.AF.β j * J.AF.dpJ J.FJ.de (fun α => J.FJ.dg α μ ν) (fun α β => J.FJ.ddg α β μ ν)
        j.succ - J.AF.N * ∑ a, ∑ j, J.AF.E a j *
          J.AF.dqJ J.FJ.de (fun α => J.FJ.dg α μ ν) (fun α β => J.FJ.ddg α β μ ν) j.succ a := by
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum, Finset.sum_comm]
  rw [hs]
  simp only [firstJet, res] at hrow ⊢
  linear_combination hrow

/-- The metric `q`-rows. -/
theorem row_q (a : Fin 3) (μ ν : Fin 4) :
    (J.dstate SM 0).q a μ ν + ∑ j, (princ (frameU (ginvOf (J.state SM).g)) SM.D.Fr SM.Db.Fr j
      (J.dstate SM j.succ)).q a μ ν =
    (Fsys SM (J.state SM)).q a μ ν + (Bsys SM (J.state SM) (J.res SM)).q a μ ν +
      ∑ j, (Qsys SM (J.state SM) j (J.drD SM.D J.ψ J.cψ J.ccψ j.succ)
        (J.drD SM.Db J.ψb J.cψb J.ccψb j.succ)).q a μ ν +
      (Gsys (𝔤 := 𝔤) (V := V) (S := S) (S' := S') (frameU (ginvOf (J.state SM).g))
        (J.state SM).g (ginvOf (J.state SM).g) J.FJ.dg J.FJ.ddg).q a μ ν := by
  have hrow := J.AF.q_row J.FJ.de (fun α => J.FJ.dg α μ ν) (fun α β => J.FJ.ddg α β μ ν)
    (fun α β => J.FJ.ddg_symm1 α β μ ν) a
  simp only [princ, Fsys, Bsys, Qsys, Gsys, dstate]
  simp only [J.recon_state]
  simp only [lowerOf, firstJet, state, J.ginvOf_eq, J.frameU_eq', Finset.sum_const_zero, add_zero]
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  have : ∑ j : Fin 3, J.AF.N * J.AF.E a j * J.AF.dpJ J.FJ.de (fun α => J.FJ.dg α μ ν)
      (fun α β => J.FJ.ddg α β μ ν) j.succ = J.AF.N * ∑ j, J.AF.E a j *
        J.AF.dpJ J.FJ.de (fun α => J.FJ.dg α μ ν) (fun α β => J.FJ.ddg α β μ ν) j.succ := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [this]
  linear_combination hrow

/-- The temporal-gauge head rows `∂_tA_i = F_{0i}`. -/
theorem row_A (i : Fin 3) :
    (J.dstate SM 0).A i + ∑ j, (princ (frameU (ginvOf (J.state SM).g)) SM.D.Fr SM.Db.Fr j
      (J.dstate SM j.succ)).A i =
    (Fsys SM (J.state SM)).A i + (Bsys SM (J.state SM) (J.res SM)).A i +
      ∑ j, (Qsys SM (J.state SM) j (J.drD SM.D J.ψ J.cψ J.ccψ j.succ)
        (J.drD SM.Db J.ψb J.cψb J.ccψb j.succ)).A i +
      (Gsys (𝔤 := 𝔤) (V := V) (S := S) (S' := S') (frameU (ginvOf (J.state SM).g))
        (J.state SM).g (ginvOf (J.state SM).g) J.FJ.dg J.FJ.ddg).A i := by
  simp only [princ, Fsys, Bsys, J.recon_state, lowerOf, firstJet, Qsys, Gsys, dstate,
    Finset.sum_const_zero, add_zero]
  exact temporal_head J.A J.dA J.temporal J.dtemporal i.succ

/-- The Higgs head row `∂_tH = D_tH` (temporal gauge). -/
theorem row_H :
    (J.dstate SM 0).H + ∑ j, (princ (frameU (ginvOf (J.state SM).g)) SM.D.Fr SM.Db.Fr j
      (J.dstate SM j.succ)).H =
    (Fsys SM (J.state SM)).H + (Bsys SM (J.state SM) (J.res SM)).H +
      ∑ j, (Qsys SM (J.state SM) j (J.drD SM.D J.ψ J.cψ J.ccψ j.succ)
        (J.drD SM.Db J.ψb J.cψb J.ccψb j.succ)).H +
      (Gsys (𝔤 := 𝔤) (V := V) (S := S) (S' := S') (frameU (ginvOf (J.state SM).g))
        (J.state SM).g (ginvOf (J.state SM).g) J.FJ.dg J.FJ.ddg).H := by
  simp only [princ, Fsys, Bsys, J.recon_state, lowerOf, firstJet, Qsys, Gsys, dstate,
    Finset.sum_const_zero, add_zero, ActualJetGauge.DH, J.temporal, zero_lie]

end ActualJet
namespace ActualJet

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [LieRingModule 𝔤 V] [LieModule ℝ 𝔤 V]
variable {S : Type*} [AddCommGroup S] [Module ℝ S]
variable {S' : Type*} [AddCommGroup S'] [Module ℝ S']
variable {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀]

variable (J : ActualJet 𝔤 V S S') (SM : SMData 𝔤 V S S')

theorem sum_neg_sub_smul {M : Type*} [AddCommGroup M] [Module ℝ M] (N : ℝ) (x y : Fin 3 → M) :
    ∑ j, (-(x j) - N • y j) = -(∑ j, x j) - N • ∑ j, y j := by
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.smul_sum]

theorem sum_neg_add_smul {M : Type*} [AddCommGroup M] [Module ℝ M] (N : ℝ) (x y : Fin 3 → M) :
    ∑ j, (-(x j) + N • y j) = -(∑ j, x j) + N • ∑ j, y j := by
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.smul_sum]

theorem sum_eps_comm {M : Type*} [AddCommGroup M] [Module ℝ M] (e : Fin 3 → Fin 3 → ℝ)
    (c : Fin 3 → Fin 3 → ℝ) (m : Fin 3 → Fin 3 → M) :
    ∑ j, ∑ b, ∑ d, c b d • (e b j • m j d) = ∑ b, ∑ d, c b d • ∑ j, e b j • m j d := by
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]

theorem sum_E_comm {M : Type*} [AddCommGroup M] [Module ℝ M] (e : Fin 3 → Fin 3 → ℝ)
    (m : Fin 3 → Fin 3 → M) :
    ∑ j, ∑ a, e a j • m j a = ∑ a, ∑ j, e a j • m j a := Finset.sum_comm

/-- The Yang–Mills (`E`) rows. -/
theorem row_E (a : Fin 3) :
    (J.dstate SM 0).E a + ∑ j, (princ (frameU (ginvOf (J.state SM).g)) SM.D.Fr SM.Db.Fr j
      (J.dstate SM j.succ)).E a =
    (Fsys SM (J.state SM)).E a + (Bsys SM (J.state SM) (J.res SM)).E a +
      ∑ j, (Qsys SM (J.state SM) j (J.drD SM.D J.ψ J.cψ J.ccψ j.succ)
        (J.drD SM.Db J.ψb J.cψb J.ccψb j.succ)).E a +
      (Gsys (𝔤 := 𝔤) (V := V) (S := S) (S' := S') (frameU (ginvOf (J.state SM).g))
        (J.state SM).g (ginvOf (J.state SM).g) J.FJ.dg J.FJ.ddg).E a := by
  have hrow := maxwell_E_row J.AF J.FJ.de J.A J.dA J.ddA J.FJ.gi J.hadapt (chr J.FJ.gi J.FJ.dg)
    (SM.Jcur J.FJ.g J.FJ.gi J.H (ActualJetGauge.DH J.A J.H J.dH) J.ψ J.ψb) a
  simp only [princ, Fsys, Bsys, Qsys, Gsys, dstate]
  simp only [J.recon_state]
  simp only [lowerOf, firstJet, state, J.ginvOf_eq, J.frameU_eq', Finset.sum_const_zero, add_zero]
  rw [sum_neg_sub_smul, sum_eps_comm]
  rw [show ∀ x y z : 𝔤, x + (-y - z) = x - y - z from fun x y z => by abel, hrow, ← LE_eq]
  unfold res
  simp only [smul_sub, smul_add, Finset.smul_sum, Finset.sum_add_distrib]
  abel

/-- The Bianchi (`B`) rows. -/
theorem row_B (a : Fin 3) :
    (J.dstate SM 0).B a + ∑ j, (princ (frameU (ginvOf (J.state SM).g)) SM.D.Fr SM.Db.Fr j
      (J.dstate SM j.succ)).B a =
    (Fsys SM (J.state SM)).B a + (Bsys SM (J.state SM) (J.res SM)).B a +
      ∑ j, (Qsys SM (J.state SM) j (J.drD SM.D J.ψ J.cψ J.ccψ j.succ)
        (J.drD SM.Db J.ψb J.cψb J.ccψb j.succ)).B a +
      (Gsys (𝔤 := 𝔤) (V := V) (S := S) (S' := S') (frameU (ginvOf (J.state SM).g))
        (J.state SM).g (ginvOf (J.state SM).g) J.FJ.dg J.FJ.ddg).B a := by
  have hrow := maxwell_B_row J.AF J.FJ.de J.A J.dA J.ddA J.ddA_symm a
  simp only [princ, Fsys, Bsys, Qsys, Gsys, dstate]
  simp only [J.recon_state]
  simp only [lowerOf, firstJet, state, J.ginvOf_eq, J.frameU_eq', Finset.sum_const_zero, add_zero]
  rw [sum_neg_add_smul, sum_eps_comm]
  rw [show ∀ x y z : 𝔤, x + (-y + z) = x - y + z from fun x y z => by abel, hrow, ← LB_eq]

/-- The Higgs `Π`-row. -/
theorem row_Pm :
    (J.dstate SM 0).Pm + ∑ j, (princ (frameU (ginvOf (J.state SM).g)) SM.D.Fr SM.Db.Fr j
      (J.dstate SM j.succ)).Pm =
    (Fsys SM (J.state SM)).Pm + (Bsys SM (J.state SM) (J.res SM)).Pm +
      ∑ j, (Qsys SM (J.state SM) j (J.drD SM.D J.ψ J.cψ J.ccψ j.succ)
        (J.drD SM.Db J.ψb J.cψb J.ccψb j.succ)).Pm +
      (Gsys (𝔤 := 𝔤) (V := V) (S := S) (S' := S') (frameU (ginvOf (J.state SM).g))
        (J.state SM).g (ginvOf (J.state SM).g) J.FJ.dg J.FJ.ddg).Pm := by
  have hrow := higgs_Pi_row J.AF J.FJ.de J.A J.dA J.H J.dH J.ddH J.FJ.gi J.hadapt
    (chr J.FJ.gi J.FJ.dg) (SM.SH J.FJ.g J.FJ.gi J.H J.ψ J.ψb)
  simp only [princ, Fsys, Bsys, Qsys, Gsys, dstate]
  simp only [J.recon_state]
  simp only [lowerOf, firstJet, state, J.ginvOf_eq, J.frameU_eq', Finset.sum_const_zero, add_zero]
  rw [sum_neg_sub_smul, sum_E_comm]
  rw [show ∀ x y z : V, x + (-y - z) = x - y - z from fun x y z => by abel, hrow, ← LPi_eq]
  unfold res
  simp only [smul_sub, smul_add]
  abel

/-- The Higgs `Q`-rows. -/
theorem row_Q (a : Fin 3) :
    (J.dstate SM 0).Q a + ∑ j, (princ (frameU (ginvOf (J.state SM).g)) SM.D.Fr SM.Db.Fr j
      (J.dstate SM j.succ)).Q a =
    (Fsys SM (J.state SM)).Q a + (Bsys SM (J.state SM) (J.res SM)).Q a +
      ∑ j, (Qsys SM (J.state SM) j (J.drD SM.D J.ψ J.cψ J.ccψ j.succ)
        (J.drD SM.Db J.ψb J.cψb J.ccψb j.succ)).Q a +
      (Gsys (𝔤 := 𝔤) (V := V) (S := S) (S' := S') (frameU (ginvOf (J.state SM).g))
        (J.state SM).g (ginvOf (J.state SM).g) J.FJ.dg J.FJ.ddg).Q a := by
  have hrow := higgs_Q_row J.AF J.FJ.de J.A J.dA J.H J.dH J.ddH J.ddH_symm a
  simp only [princ, Fsys, Bsys, Qsys, Gsys, dstate]
  simp only [J.recon_state]
  simp only [lowerOf, firstJet, state, J.ginvOf_eq, J.frameU_eq', Finset.sum_const_zero, add_zero]
  rw [sum_neg_sub_smul]
  rw [show ∀ x y z : V, x + (-y - z) = x - y - z from fun x y z => by abel, hrow, ← LQ_eq]

end ActualJet
namespace ActualJet

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [LieRingModule 𝔤 V] [LieModule ℝ 𝔤 V]
variable {S : Type*} [AddCommGroup S] [Module ℝ S]
variable {S' : Type*} [AddCommGroup S'] [Module ℝ S']
variable {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀]

variable (J : ActualJet 𝔤 V S S')

theorem e_eq' : J.FJ.e = J.AF.fr := funext₂ J.hfr

theorem sum_diracP (D : DiracData 𝔤 V S₀) (w : Fin 3 → S₀) :
    ∑ j, diracP J.AF D.Fr j (w j) = -(∑ j, J.AF.β j • w j) -
      J.AF.N • ∑ i : Fin 3, ∑ j, J.AF.E i j • ((D.Fr.c 0 * D.Fr.c i.succ) • w j) := by
  unfold diracP
  rw [sum_neg_sub_smul]
  congr 2
  exact Finset.sum_comm

/-- **The Dirac head row of a spinor block**: `∂_tΨ + Σ_j𝒜^j∂_jΨ = N(c_0Σc_aω_a - ω_0 - c_0𝓜)Ψ
- Nc_0r_D`. -/
theorem row_dirac (D : DiracData 𝔤 V S₀) (ψ : S₀) (cψ : Fin 4 → S₀) :
    cψ 0 + ∑ j, diracP J.AF D.Fr j (cψ j.succ) =
      J.AF.N • psiF D J.FJ.g J.FJ.gi J.FJ.dg J.AF J.FJ.de J.A J.H ψ -
        J.AF.N • (D.Fr.c 0 • J.rD D ψ cψ) := by
  have h := dirac_head_row J.AF D.Fr D.lorentz (J.LJ D).ω D.m0 D.L J.H ψ cψ
  have hfj : ActualJetWriter.frameJet J.AF cψ = dψf J.FJ cψ := by
    funext B; unfold ActualJetWriter.frameJet dψf; simp only [J.hfr]
  rw [hfj] at h
  rw [J.sum_diracP, show ∀ x y z : S₀, x + (-y - z) = x - y - z from fun x y z => by abel, h]
  unfold psiF rD
  simp only [J.LJ_ω]

end ActualJet
namespace ActualJet

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [LieRingModule 𝔤 V] [LieModule ℝ 𝔤 V]
variable {S : Type*} [AddCommGroup S] [Module ℝ S]
variable {S' : Type*} [AddCommGroup S'] [Module ℝ S']
variable {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀]

variable (J : ActualJet 𝔤 V S S')

theorem sum_split_ite {M : Type*} [AddCommGroup M] [Module ℝ M] (w : Fin 4 → ℝ) (X : Fin 4 → M)
    (k : M) : ∑ c, w c • (X c - (if c = 0 then k else 0)) = ∑ c, w c • X c - w 0 • k := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ (f := fun c => w c • X c)]
  simp only [ite_true, Fin.succ_ne_zero, ite_false, sub_zero, smul_sub]
  abel

theorem DH_frame (b : Fin 4) :
    SpinorProlongation.DH J.ρH J.H (fun b => ∑ δ, J.FJ.e b δ • J.dH δ) b =
      DHf J.AF.fr (ActualJetGauge.DH J.A J.H J.dH) b := by
  unfold SpinorProlongation.DH DHf ActualJetGauge.DH
  rw [J.ρH_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [J.hfr, smul_add]

theorem frT2_eq (T : Fin 4 → Fin 4 → ℝ) (a b : Fin 4) :
    ∑ μ, ∑ ν, J.FJ.e a μ * J.FJ.e b ν * T μ ν = frT2 J.AF.fr T a b := by
  unfold frT2; simp only [J.hfr]

/-- **The prolonged spinor rows of a spinor block** (`prop:spinor-prolongation` with the Ricci
term eliminated by `eq:trace-reversal-residual`): for every stress split `T = T₀ - T₁`,
`∂_tX_a + Σ_j𝒜^j∂_jX_a = N·XrowF(T₀) + N·XrowB(r_D, 𝓔^{tr}, T₁) - NΣ_j c_0e_aʲ∂_jr_D`. -/
theorem row_x (D : DiracData 𝔤 V S₀) (ψ : S₀) (cψ : Fin 4 → S₀) (ccψ : Fin 4 → Fin 4 → S₀)
    (hs : ∀ δ γ, ccψ δ γ = ccψ γ δ) (κ Λ : ℝ) (T T0 T1 : Fin 4 → Fin 4 → ℝ)
    (hT : ∀ x y, T x y = T0 x y - T1 x y) (a : Fin 3) :
    J.dXs D ψ cψ ccψ 0 a.succ + ∑ j, diracP J.AF D.Fr j (J.dXs D ψ cψ ccψ j.succ a.succ) =
      J.AF.N • XrowF D κ Λ J.FJ.g J.FJ.gi J.FJ.dg J.AF J.FJ.de J.A (Fm J.A J.dA) J.H
          (ActualJetGauge.DH J.A J.H J.dH) ψ (J.Xn D ψ cψ) T0 a.succ +
        J.AF.N • XrowB D κ J.FJ.g J.FJ.gi J.FJ.dg J.AF J.FJ.de J.A ψ a.succ (J.rD D ψ cψ)
          (traceRev J.FJ.g J.FJ.gi (fun x y => einstein J.FJ.g J.FJ.gi J.FJ.dg J.FJ.ddg x y +
            Λ * J.FJ.g x y - κ * T x y)) T1 +
        ∑ j, -(J.AF.N • (D.Fr.c 0 • (J.AF.E a j • J.drD D ψ cψ ccψ j.succ))) := by
  set dhf : Fin 4 → V := fun b => ∑ δ, J.FJ.e b δ • J.dH δ with hdhf
  have hx : J.dXs D ψ cψ ccψ 0 a.succ - ∑ j, J.AF.β j • J.dXs D ψ cψ ccψ j.succ a.succ -
      J.AF.N • ∑ i : Fin 3, ∑ j, J.AF.E i j • ((D.Fr.c 0 * D.Fr.c i.succ) •
        J.dXs D ψ cψ ccψ j.succ a.succ) =
      J.AF.N • (-((J.LJ D).ω 0 • J.Xs D ψ cψ a.succ) +
        ∑ c, lcΓ D.Fr.ε (J.LJ D).G 0 a.succ c • J.Xs D ψ cψ c +
        D.Fr.c 0 • ∑ i : Fin 3, D.Fr.c i.succ • ((J.LJ D).ω i.succ • J.Xs D ψ cψ a.succ -
          ∑ c, lcΓ D.Fr.ε (J.LJ D).G i.succ a.succ c • J.Xs D ψ cψ c) -
        D.Fr.c 0 • (mass D.m0 D.L J.H • J.Xs D ψ cψ a.succ +
          D.L (SpinorProlongation.DH J.ρH J.H dhf a.succ) • ψ +
          covResD D.Fr (J.LJ D).ω (J.LJ D).dω D.m0 D.L J.H dhf ψ (dψf J.FJ cψ)
            (ddψf J.FJ cψ ccψ) a.succ +
          ((1 / 2 : ℝ) • ∑ b, (D.Fr.ε b * ricciOf D.Fr.ε (J.LJ D).Rm a.succ b) • D.Fr.c b) • ψ +
          (∑ b, D.Fr.ε b • (D.Fr.c b * (J.LJ D).F b a.succ)) • ψ)) :=
    x_row J.FJ J.AF J.hfr D.Fr (J.hε D) D.lorentz (fun μ => D.ρ (J.A μ))
      (fun γ μ => D.ρ (J.dA γ μ)) (fun μ b => D.comm (J.A μ) b) D.m0 D.L J.ρH J.H dhf ψ cψ ccψ
      hs D.mass_cl (J.hMg D) a.succ
  have hdr : dresD D.Fr (J.LJ D).ω (J.LJ D).dω D.m0 D.L J.H dhf ψ (dψf J.FJ cψ)
      (ddψf J.FJ cψ ccψ) a.succ = ∑ j, J.AF.E a j • J.drD D ψ cψ ccψ j.succ :=
    dresD_tangential J.FJ J.AF J.hfr D.Fr (J.hε D) (fun μ => D.ρ (J.A μ))
      (fun γ μ => D.ρ (J.dA γ μ)) (fun μ b => D.comm (J.A μ) b) D.m0 D.L J.H J.dH ψ cψ ccψ a
  have hric : (1 / 2 : ℝ) • ∑ b, (D.Fr.ε b * ricciOf D.Fr.ε (J.LJ D).Rm a.succ b) • D.Fr.c b =
      (1 / 2 : ℝ) • ∑ b, (D.Fr.ε b * (κ * ∑ μ, ∑ ν, J.FJ.e a.succ μ * J.FJ.e b ν *
        traceRev J.FJ.g J.FJ.gi T μ ν + Λ * (if a.succ = b then J.FJ.ε a.succ else 0) +
        ∑ μ, ∑ ν, J.FJ.e a.succ μ * J.FJ.e b ν * traceRev J.FJ.g J.FJ.gi
          (fun x y => einstein J.FJ.g J.FJ.gi J.FJ.dg J.FJ.ddg x y + Λ * J.FJ.g x y -
            κ * T x y) μ ν)) • D.Fr.c b :=
    prolongation_ricci J.FJ D.Fr (J.hε D) (fun μ => D.ρ (J.A μ)) (fun γ μ => D.ρ (J.dA γ μ))
      (fun μ b => D.comm (J.A μ) b) T Λ κ a.succ
  have hTr : ∀ b, ∑ μ, ∑ ν, J.FJ.e a.succ μ * J.FJ.e b ν * traceRev J.FJ.g J.FJ.gi T μ ν =
      frT2 J.AF.fr (traceRev J.FJ.g J.FJ.gi T0) a.succ b -
        frT2 J.AF.fr (traceRev J.FJ.g J.FJ.gi T1) a.succ b := by
    intro b
    rw [J.frT2_eq]
    have : (fun x y => T x y) = fun x y => T0 x y - T1 x y := funext₂ hT
    unfold frT2
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [show traceRev J.FJ.g J.FJ.gi T μ ν = traceRev J.FJ.g J.FJ.gi (fun x y => T x y) μ ν from rfl,
      this, traceRev_sub]
    ring
  rw [J.sum_diracP, show ∀ x y z : S₀, x + (-y - z) = x - y - z from fun x y z => by abel, hx]
  unfold covResD
  rw [hdr, hric, J.DH_frame]
  have hG : (J.LJ D).G = Gfun J.FJ.g J.FJ.gi J.FJ.dg J.AF.fr J.FJ.de := J.G_eq
  simp only [hTr, J.frT2_eq, J.LJ_ω, hG, J.LJ_F, J.hε D, J.sign]
  simp only [J.Xs_eq_Xn, sum_split_ite, Fin.succ_ne_zero, ite_false, sub_zero]
  have hsp : ∀ b : Fin 4, (lorentzSign b * (κ * (frT2 J.AF.fr (traceRev J.FJ.g J.FJ.gi T0) a.succ b -
      frT2 J.AF.fr (traceRev J.FJ.g J.FJ.gi T1) a.succ b) +
      Λ * (if a.succ = b then lorentzSign a.succ else 0) +
      frT2 J.AF.fr (traceRev J.FJ.g J.FJ.gi (fun x y => einstein J.FJ.g J.FJ.gi J.FJ.dg J.FJ.ddg x y +
        Λ * J.FJ.g x y - κ * T x y)) a.succ b)) • D.Fr.c b =
      (lorentzSign b * (κ * frT2 J.AF.fr (traceRev J.FJ.g J.FJ.gi T0) a.succ b +
        Λ * (if a.succ = b then lorentzSign a.succ else 0))) • D.Fr.c b +
      (lorentzSign b * (frT2 J.AF.fr (traceRev J.FJ.g J.FJ.gi (fun x y =>
        einstein J.FJ.g J.FJ.gi J.FJ.dg J.FJ.ddg x y + Λ * J.FJ.g x y - κ * T x y)) a.succ b -
        κ * frT2 J.AF.fr (traceRev J.FJ.g J.FJ.gi T1) a.succ b)) • D.Fr.c b := by
    intro b; rw [← add_smul]; congr 1; ring
  simp only [hsp, Finset.sum_add_distrib, smul_add, add_smul]
  unfold XrowF XrowB rD
  simp only [smul_add, smul_sub, smul_neg, Finset.smul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib, neg_neg]
  abel

end ActualJet
namespace ActualJet

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [LieRingModule 𝔤 V] [LieModule ℝ 𝔤 V]
variable {S : Type*} [AddCommGroup S] [Module ℝ S]
variable {S' : Type*} [AddCommGroup S'] [Module ℝ S']

variable (J : ActualJet 𝔤 V S S') (SM : SMData 𝔤 V S S')

theorem Tact_split (x y : Fin 4) :
    J.Tact SM x y = stressF SM (J.firstJet SM) x y - stressR SM (J.firstJet SM) (J.res SM) x y := by
  rw [J.Tact_eq, J.recon_state]

theorem row_ψ :
    (J.dstate SM 0).ψ + ∑ j, (princ (frameU (ginvOf (J.state SM).g)) SM.D.Fr SM.Db.Fr j
      (J.dstate SM j.succ)).ψ =
    (Fsys SM (J.state SM)).ψ + (Bsys SM (J.state SM) (J.res SM)).ψ +
      ∑ j, (Qsys SM (J.state SM) j (J.drD SM.D J.ψ J.cψ J.ccψ j.succ)
        (J.drD SM.Db J.ψb J.cψb J.ccψb j.succ)).ψ +
      (Gsys (𝔤 := 𝔤) (V := V) (S := S) (S' := S') (frameU (ginvOf (J.state SM).g))
        (J.state SM).g (ginvOf (J.state SM).g) J.FJ.dg J.FJ.ddg).ψ := by
  simp only [princ, Fsys, Bsys, Qsys, Gsys, dstate]
  simp only [J.recon_state]
  simp only [lowerOf, firstJet, state, J.ginvOf_eq, J.frameU_eq', Finset.sum_const_zero, add_zero]
  rw [J.row_dirac SM.D J.ψ J.cψ]
  unfold res
  simp only [sub_eq_add_neg]

theorem row_ψb :
    (J.dstate SM 0).ψb + ∑ j, (princ (frameU (ginvOf (J.state SM).g)) SM.D.Fr SM.Db.Fr j
      (J.dstate SM j.succ)).ψb =
    (Fsys SM (J.state SM)).ψb + (Bsys SM (J.state SM) (J.res SM)).ψb +
      ∑ j, (Qsys SM (J.state SM) j (J.drD SM.D J.ψ J.cψ J.ccψ j.succ)
        (J.drD SM.Db J.ψb J.cψb J.ccψb j.succ)).ψb +
      (Gsys (𝔤 := 𝔤) (V := V) (S := S) (S' := S') (frameU (ginvOf (J.state SM).g))
        (J.state SM).g (ginvOf (J.state SM).g) J.FJ.dg J.FJ.ddg).ψb := by
  simp only [princ, Fsys, Bsys, Qsys, Gsys, dstate]
  simp only [J.recon_state]
  simp only [lowerOf, firstJet, state, J.ginvOf_eq, J.frameU_eq', Finset.sum_const_zero, add_zero]
  rw [J.row_dirac SM.Db J.ψb J.cψb]
  unfold res
  simp only [sub_eq_add_neg]

theorem row_X (a : Fin 3) :
    (J.dstate SM 0).X a + ∑ j, (princ (frameU (ginvOf (J.state SM).g)) SM.D.Fr SM.Db.Fr j
      (J.dstate SM j.succ)).X a =
    (Fsys SM (J.state SM)).X a + (Bsys SM (J.state SM) (J.res SM)).X a +
      ∑ j, (Qsys SM (J.state SM) j (J.drD SM.D J.ψ J.cψ J.ccψ j.succ)
        (J.drD SM.Db J.ψb J.cψb J.ccψb j.succ)).X a +
      (Gsys (𝔤 := 𝔤) (V := V) (S := S) (S' := S') (frameU (ginvOf (J.state SM).g))
        (J.state SM).g (ginvOf (J.state SM).g) J.FJ.dg J.FJ.ddg).X a := by
  have h := J.row_x SM.D J.ψ J.cψ J.ccψ J.ccψ_symm SM.κ SM.Λ (J.Tact SM)
    (stressF SM (J.firstJet SM)) (stressR SM (J.firstJet SM) (J.res SM)) (J.Tact_split SM) a
  simp only [princ, Fsys, Bsys, Qsys, Gsys, dstate]
  simp only [J.recon_state]
  simp only [lowerOf, state, J.ginvOf_eq, J.frameU_eq', add_zero]
  rw [h]
  simp only [firstJet, res]

theorem row_Xb (a : Fin 3) :
    (J.dstate SM 0).Xb a + ∑ j, (princ (frameU (ginvOf (J.state SM).g)) SM.D.Fr SM.Db.Fr j
      (J.dstate SM j.succ)).Xb a =
    (Fsys SM (J.state SM)).Xb a + (Bsys SM (J.state SM) (J.res SM)).Xb a +
      ∑ j, (Qsys SM (J.state SM) j (J.drD SM.D J.ψ J.cψ J.ccψ j.succ)
        (J.drD SM.Db J.ψb J.cψb J.ccψb j.succ)).Xb a +
      (Gsys (𝔤 := 𝔤) (V := V) (S := S) (S' := S') (frameU (ginvOf (J.state SM).g))
        (J.state SM).g (ginvOf (J.state SM).g) J.FJ.dg J.FJ.ddg).Xb a := by
  have h := J.row_x SM.Db J.ψb J.cψb J.ccψb J.ccψb_symm SM.κ SM.Λ (J.Tact SM)
    (stressF SM (J.firstJet SM)) (stressR SM (J.firstJet SM) (J.res SM)) (J.Tact_split SM) a
  simp only [princ, Fsys, Bsys, Qsys, Gsys, dstate]
  simp only [J.recon_state]
  simp only [lowerOf, state, J.ginvOf_eq, J.frameU_eq', add_zero]
  rw [h]
  simp only [firstJet, res]

end ActualJet

/-- **`prop:actual-jet-writer`** (`eq:actual-jet-writer`, `eq:actual-jet-gauge-forcing`).
For every actual jet `J` of a field tuple in exact temporal internal gauge (metric with its
algebraic adapted frame on the Lorentzian chart, gauge potential with `A_0 ≡ 0`, Higgs field,
spinor and dual spinor; both spinor rows retained) and all theory data, the actual-jet state
`𝒰 = 𝒰(J)` and its coordinate derivative jets satisfy, in every block,
`∂_t𝒰 + Σ_j 𝒜^j(g)∂_j𝒰 = 𝓕(𝒰) + 𝓑(𝒰)(𝓔^{tr}, r^A, r_H, r_D, r̄_D) + Σ_j 𝒬^j(g)∂_j(r_D, r̄_D)
  + 𝔊(𝒰; C, ∂C)`,
where
* `𝒜^j(g) = princ(frameOf(g))` depends only on the metric and is symmetric for the block inner
  product (`princ_symm`);
* `𝓕 = Fsys`, `𝓑 = Bsys` are functions of the state alone (`recon` reconstructs the first jets,
  `ActualJet.recon_state`), `𝓑` is linear in the residuals and involves none of their derivatives;
* `𝒬^j = Qsys` involves only the spatial derivatives `∂_jr_D, ∂_jr̄_D` (no `∂_tr_D`), with
  coefficients depending only on the metric (the frame);
* `𝔊 = Gsys = 𝒥_C C + 𝒥_C^0∂_tC + Σ_j𝒥_C^j∂_jC` (`eq:actual-jet-gauge-forcing`) with `C` the
  actual harmonic defect; it vanishes when `C = 0`, `∂C = 0` (`Gsys_zero`). -/
theorem actual_jet_writer {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    {V : Type*} [AddCommGroup V] [Module ℝ V] [LieRingModule 𝔤 V] [LieModule ℝ 𝔤 V]
    {S : Type*} [AddCommGroup S] [Module ℝ S] {S' : Type*} [AddCommGroup S'] [Module ℝ S']
    (J : ActualJet 𝔤 V S S') (SM : SMData 𝔤 V S S') :
    WriterEq (J.dstate SM) (fun j => princ (frameU (ginvOf (J.state SM).g)) SM.D.Fr SM.Db.Fr j)
      (Fsys SM (J.state SM)) (Bsys SM (J.state SM) (J.res SM))
      (Gsys (frameU (ginvOf (J.state SM).g)) (J.state SM).g (ginvOf (J.state SM).g) J.FJ.dg J.FJ.ddg)
      (fun j => Qsys SM (J.state SM) j (J.drD SM.D J.ψ J.cψ J.ccψ j.succ)
        (J.drD SM.Db J.ψb J.cψb J.ccψb j.succ)) :=
  ⟨J.row_g SM, J.row_p SM, J.row_q SM, J.row_A SM, J.row_E SM, J.row_B SM, J.row_H SM, J.row_Pm SM,
    J.row_Q SM, J.row_ψ SM, J.row_X SM, J.row_ψb SM, J.row_Xb SM⟩

/-- The gauge forcing is the harmonic-defect forcing of `lem:harmonic-defect-forcing`
(`𝔊 = -2N∇_{(μ}C_{ν)}`), and it vanishes when `C = 0` and `∂C = 0`. -/
theorem Gsys_eq {𝔤 V S S' : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [AddCommGroup V] [Module ℝ V]
    [LieRingModule 𝔤 V] [LieModule ℝ 𝔤 V] [AddCommGroup S] [Module ℝ S] [AddCommGroup S']
    [Module ℝ S'] (AF : AdaptedFrame) (g gi : Fin 4 → Fin 4 → ℝ)
    (dg : Fin 4 → Fin 4 → Fin 4 → ℝ) (ddg : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ) (μ ν : Fin 4) :
    (Gsys (𝔤 := 𝔤) (V := V) (S := S) (S' := S') AF g gi dg ddg).p μ ν =
      gaugeForce AF g gi dg ddg μ ν := by
  rw [gaugeForce_eq AF g gi dg ddg hdg]
  rfl

theorem Gsys_zero {𝔤 V S S' : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [AddCommGroup V] [Module ℝ V]
    [LieRingModule 𝔤 V] [LieModule ℝ 𝔤 V] [AddCommGroup S] [Module ℝ S] [AddCommGroup S']
    [Module ℝ S'] (AF : AdaptedFrame) (g gi : Fin 4 → Fin 4 → ℝ)
    (dg : Fin 4 → Fin 4 → Fin 4 → ℝ) (ddg : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hC : ∀ l, C gi dg l = 0) (hdC : ∀ α l, dC gi dg ddg α l = 0) (μ ν : Fin 4) :
    (Gsys (𝔤 := 𝔤) (V := V) (S := S) (S' := S') AF g gi dg ddg).p μ ν = 0 := by
  simp [Gsys, hC, hdC]

/-- `𝒬^j` depends on the state only through the metric. -/
theorem Qsys_metric {𝔤 V S S' : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [AddCommGroup V] [Module ℝ V]
    [LieRingModule 𝔤 V] [LieModule ℝ 𝔤 V] [AddCommGroup S] [Module ℝ S] [AddCommGroup S']
    [Module ℝ S'] (SM : SMData 𝔤 V S S') (U U' : State 𝔤 V S S') (h : U.g = U'.g) (j : Fin 3)
    (dr : S) (drb : S') : Qsys SM U j dr drb = Qsys SM U' j dr drb := by
  unfold Qsys; rw [h]

/-- `𝒜^j` depends on the state only through the metric. -/
theorem princ_metric {𝔤 V S S' : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [AddCommGroup V] [Module ℝ V]
    [LieRingModule 𝔤 V] [LieModule ℝ 𝔤 V] [AddCommGroup S] [Module ℝ S] [AddCommGroup S']
    [Module ℝ S']
    (Fr : CliffordFrame (Fin 4) (Module.End ℝ S)) (Frb : CliffordFrame (Fin 4) (Module.End ℝ S'))
    (U U' W : State 𝔤 V S S') (h : U.g = U'.g) (j : Fin 3) :
    princ (frameU (ginvOf U.g)) Fr Frb j W = princ (frameU (ginvOf U'.g)) Fr Frb j W := by
  rw [h]

/-! ### Non-vacuity: Minkowski space with vanishing fields -/

section NonVacuity

/-- The adapted frame of the Minkowski inverse metric is the coordinate frame. -/
theorem frU_minkInv : frU minkInv = fun A μ => if A = μ then 1 else 0 := by
  have hl : lapse minkInv = 1 := by simp [lapse, minkInv]
  have hs : ∀ j, shift minkInv j = 0 := by
    intro j; simp [shift, minkInv, (Fin.succ_ne_zero j).symm]
  have hL : ∀ j a, Lmat minkInv j a = if j = a then 1 else 0 := by
    intro j a
    fin_cases j <;> fin_cases a <;> simp [Lmat, L00, L10, L20, L11, L21, L22, hInv, minkInv]
  funext A μ
  induction A using Fin.cases with
  | zero =>
    induction μ using Fin.cases with
    | zero => simp [frU, hl]
    | succ j => simp [frU, hs, (Fin.succ_ne_zero j).symm]
  | succ a =>
    induction μ using Fin.cases with
    | zero => simp [frU, Fin.succ_ne_zero]
    | succ j => simp [frU, hL, Fin.succ_inj, eq_comm]

theorem minkInv_sq (a c : Fin 4) : ∑ b, minkInv a b * minkInv b c = if a = c then 1 else 0 := by
  fin_cases a <;> fin_cases c <;> simp [minkInv, Fin.sum_univ_four]

/-- The 2-jet of the Minkowski metric with its adapted frame (all derivatives zero). -/
def minkFrameJet : FrameJet (Fin 4) (Fin 4) where
  g := minkInv
  gi := minkInv
  dg := 0
  ddg := 0
  ε := lorentzSign
  e := frU minkInv
  de := 0
  dde := 0
  g_symm := minkInv_symm
  gi_symm := minkInv_symm
  hinv := minkInv_sq
  dg_symm := fun _ _ _ => rfl
  ddg_symm1 := fun _ _ _ _ => rfl
  ddg_symm2 := fun _ _ _ _ => rfl
  dde_symm := fun _ _ _ _ => rfl
  sign_sq := by intro A; unfold lorentzSign; split_ifs <;> norm_num
  orth := by
    intro A B
    rw [frU_minkInv]
    fin_cases A <;> fin_cases B <;> simp [ipg, minkInv, lorentzSign, Fin.sum_univ_four]
  compl := by
    intro μ ν
    rw [frU_minkInv]
    fin_cases μ <;> fin_cases ν <;> simp [minkInv, lorentzSign, Fin.sum_univ_four]
  orth1 := by intros; simp [dipg]
  orth2 := by intros; simp [ddipg]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The trivial Clifford frame on the zero spinor space (all relations hold). -/
def trivFrame : CliffordFrame (Fin 4) (Module.End ℝ PUnit) where
  c := fun _ => 0
  ε := lorentzSign
  sign_sq := by intro A; unfold lorentzSign; split_ifs <;> norm_num
  anticomm := fun _ _ => Subsingleton.elim _ _

/-- A Dirac block on the zero spinor space. -/
def trivDirac : DiracData ℝ ℝ PUnit where
  Fr := trivFrame
  ρ := 0
  ρ_lie := fun _ _ => Subsingleton.elim _ _
  m0 := 0
  L := 0
  lorentz := ⟨by simp [trivFrame, lorentzSign], fun a => by
    simp [trivFrame, lorentzSign, Fin.succ_ne_zero]⟩
  comm := fun _ _ => Subsingleton.elim _ _
  mass_cl := fun _ _ _ => Subsingleton.elim _ _
  mass_eq := fun _ _ => Subsingleton.elim _ _

/-- Theory data with vanishing couplings (abelian gauge algebra `ℝ`, Higgs space `ℝ`). -/
def trivSM : SMData ℝ ℝ PUnit PUnit where
  Λ := 0
  κ := 1
  D := trivDirac
  Db := trivDirac
  Jcur := fun _ _ _ _ _ _ _ => 0
  SH := fun _ _ _ _ _ => 0
  ipG := 0
  ipV := 0
  lamH := 0
  vH := 0
  TD := ⟨fun _ _ _ => 0, fun _ _ _ => 0, fun _ _ _ => 0⟩

/-- The Minkowski actual jet with vanishing gauge, Higgs and spinor fields. -/
def minkJet : ActualJet ℝ ℝ PUnit PUnit where
  FJ := minkFrameJet
  chart := minkInv_isLorChart
  sign := rfl
  frame := fun _ _ => rfl
  dframe := by
    intro γ A μ
    have h0 : (fun γ l σ => dginv minkFrameJet.gi minkFrameJet.dg γ l σ) = 0 := by
      funext γ l σ; simp [dginv, minkFrameJet]
    rw [h0]
    simp [ActualJetFrame.frameJet, minkFrameJet]
  A := 0
  dA := 0
  ddA := 0
  temporal := rfl
  dtemporal := fun _ => rfl
  ddA_symm := fun _ _ _ => rfl
  H := 0
  dH := 0
  ddH := 0
  ddH_symm := fun _ _ => rfl
  ψ := PUnit.unit
  cψ := 0
  ccψ := 0
  ccψ_symm := fun _ _ => rfl
  ψb := PUnit.unit
  cψb := 0
  ccψb := 0
  ccψb_symm := fun _ _ => rfl

/-- **Non-vacuity of `prop:actual-jet-writer`**: the hypotheses are satisfiable (Minkowski
space in its adapted frame with vanishing fields), and the theorem applies. -/
example : WriterEq (minkJet.dstate trivSM)
    (fun j => princ (frameU (ginvOf (minkJet.state trivSM).g)) trivSM.D.Fr trivSM.Db.Fr j)
    (Fsys trivSM (minkJet.state trivSM)) (Bsys trivSM (minkJet.state trivSM) (minkJet.res trivSM))
    (Gsys (frameU (ginvOf (minkJet.state trivSM).g)) (minkJet.state trivSM).g
      (ginvOf (minkJet.state trivSM).g) minkJet.FJ.dg minkJet.FJ.ddg)
    (fun j => Qsys trivSM (minkJet.state trivSM) j
      (minkJet.drD trivSM.D minkJet.ψ minkJet.cψ minkJet.ccψ j.succ)
      (minkJet.drD trivSM.Db minkJet.ψb minkJet.cψb minkJet.ccψb j.succ)) :=
  actual_jet_writer minkJet trivSM

end NonVacuity

end

end RenewalGeometry.ActualJetSystem
