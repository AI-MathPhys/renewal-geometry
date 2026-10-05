/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.FrameCurvatureJet
import RenewalGeometry.Gravity.ActualJetMaxwellHiggsRows

/-!
# The prolonged spinor rows in coordinates (`prop:actual-jet-writer`)

Einstein–Standard-Model action-closure manuscript, `prop:actual-jet-writer`: "For the tangential
spinor jets use `prop:spinor-prolongation`.  The contracted curvature there is the physical Ricci
tensor, so `eq:trace-reversal-residual` eliminates it … Since `e_a = e_a{}^j∂_j` for
`a = 1, 2, 3`, its residual derivative is `∇_a r_D = e_a{}^j∂_jr_D + (connection)·r_D` … Hence no
`∂_tr_D` is introduced."

Jets at one point (the convention of `SpinorProlongationJet` and `FrameCurvatureJet`): an
orthonormal frame jet `FJ : FrameCurvature.FrameJet (Fin 4) (Fin 4)` whose frame is the adapted
frame `AF` (`e_0 = N⁻¹(∂_t - βʲ∂_j)`, `e_a = e_aʲ∂_j`), a Clifford frame of the same (Lorentzian)
signature, the gauge potential `ρ(A_μ)` with its derivative jet, and the coordinate jets
`(Ψ, ∂Ψ, ∂²Ψ)` of a spinor.  The twisted Levi-Civita jets are `FJ.toLCJet`.

## Main results

* `dcov_eq`, `cov2_eq` — with `X_a = ∇_aΨ` and its **coordinate derivative jet** `∂_γX_a`
  (`dXc`, product rule), the frame derivative is `e_B(X_a) = e_B{}^γ∂_γX_a` and
  `∇²_{Ba}Ψ = e_B{}^γ∂_γX_a + ω_BX_a - Γ_{Ba}{}^cX_c`.
* **`x_row`** — the prolonged rows in coordinates on the adapted chart:
  `∂_tX_a - βʲ∂_jX_a - N Σ_{i,j} e_iʲ c_0c_i ∂_jX_a
    = N(-ω_0X_a + Γ_{0a}{}^cX_c + c_0Σ_i c_i(ω_iX_a - Γ_{ia}{}^cX_c) - c_0R_a)`,
  `R_a` the right side of `eq:spinor-prolongation`: the principal matrices are those of the
  Dirac head row (`-βʲ - N e_iʲc_0c_i`).
* `dresD_eq` — the frame derivative of the Dirac residual is the contraction of its coordinate
  derivative jet `∂_γr_D` (`drc`): for tangential `a`, `e_a(r_D) = e_aʲ∂_jr_D` (no `∂_tr_D`).
* **`prolongation_ricci`** — in `eq:spinor-prolongation` the Ricci term is eliminated by
  `eq:trace-reversal-residual` (`FrameJet.frame_trace_reversal`):
  `½Σ_b ε_bRic_{ab}c_b = ½Σ_b ε_b(κT^{tr}_{ab} + Λε_aδ_{ab} + 𝓔^{tr}_{ab})c_b`.
-/

namespace RenewalGeometry.ActualJetSpinor

open Finset SpinorProlongation TwistedHalfRicci FrameCurvature ActualJetWriter ActualJetGauge

noncomputable section

set_option linter.unusedSectionVars false

variable {A : Type*} [Ring A] [Algebra ℝ A]
variable {V : Type*} [AddCommGroup V] [Module A V] [Module ℝ V] [IsScalarTower ℝ A V]

section Jets

variable (FJ : FrameJet (Fin 4) (Fin 4)) (Fr : CliffordFrame (Fin 4) A) (hε : Fr.ε = FJ.ε)
  (ρA : Fin 4 → A) (dρA : Fin 4 → Fin 4 → A) (hcomm : ∀ μ b, ρA μ * Fr.c b = Fr.c b * ρA μ)

/-- The frame derivative jets `e_BΨ = e_B{}^γ∂_γΨ` of a spinor. -/
def dψf (cψ : Fin 4 → V) (B : Fin 4) : V := ∑ γ, FJ.e B γ • cψ γ

/-- The second frame derivative jets `e_B(e_CΨ)` (product rule). -/
def ddψf (cψ : Fin 4 → V) (ccψ : Fin 4 → Fin 4 → V) (B C : Fin 4) : V :=
  ∑ δ, FJ.e B δ • ∑ γ, (FJ.de δ C γ • cψ γ + FJ.e C γ • ccψ δ γ)

/-- The coordinate derivative jet `∂_γω_a` of the twisted spin connection. -/
def dωc (γ a : Fin 4) : A :=
  spinPart Fr (FJ.dGc γ a) + ∑ μ, (FJ.de γ a μ • ρA μ + FJ.e a μ • dρA γ μ)

/-- The coordinate derivative jet `∂_γX_a` of `X_a = ∇_{e_a}Ψ = e_a{}^μ∂_μΨ + ω_aΨ`. -/
def dXc (ψ : V) (cψ : Fin 4 → V) (ccψ : Fin 4 → Fin 4 → V) (γ a : Fin 4) : V :=
  ∑ μ, (FJ.de γ a μ • cψ μ + FJ.e a μ • ccψ γ μ) + dωc FJ Fr ρA dρA γ a • ψ +
    (FJ.toLCJet Fr hε ρA dρA hcomm).ω a • cψ γ

/-- `e_B(X_a) = e_B{}^γ∂_γX_a`: the frame derivative jet `dcov` of `prop:spinor-prolongation` is
the contraction of the coordinate derivative jet. -/
theorem dcov_eq (ψ : V) (cψ : Fin 4 → V) (ccψ : Fin 4 → Fin 4 → V) (B a : Fin 4) :
    dcov (FJ.toLCJet Fr hε ρA dρA hcomm).ω (FJ.toLCJet Fr hε ρA dρA hcomm).dω ψ (dψf FJ cψ)
        (ddψf FJ cψ ccψ) B a =
      ∑ δ, FJ.e B δ • dXc FJ Fr hε ρA dρA hcomm ψ cψ ccψ δ a := by
  set J := FJ.toLCJet Fr hε ρA dρA hcomm
  have hdω : J.dω B a = ∑ δ, FJ.e B δ • dωc FJ Fr ρA dρA δ a := by
    show spinPart Fr (fun x y => ∑ δ, FJ.e B δ * FJ.dGc δ a x y) +
        ∑ δ, FJ.e B δ • ∑ μ, (FJ.de δ a μ • ρA μ + FJ.e a μ • dρA δ μ) = _
    rw [spinPart_sum_smul]
    unfold dωc
    simp only [smul_add, Finset.sum_add_distrib]
  unfold dcov dXc ddψf dψf
  rw [hdω, Finset.sum_smul, Finset.smul_sum]
  simp only [smul_add, Finset.sum_add_distrib, smul_assoc]
  congr 1
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [smul_comm]

/-- `∇²_{Ba}Ψ = e_B{}^γ∂_γX_a + ω_BX_a - Γ_{Ba}{}^cX_c`. -/
theorem cov2_eq (ψ : V) (cψ : Fin 4 → V) (ccψ : Fin 4 → Fin 4 → V) (B a : Fin 4) :
    cov2 (lcΓ Fr.ε (FJ.toLCJet Fr hε ρA dρA hcomm).G) (FJ.toLCJet Fr hε ρA dρA hcomm).ω
        (FJ.toLCJet Fr hε ρA dρA hcomm).dω ψ (dψf FJ cψ) (ddψf FJ cψ ccψ) B a =
      ∑ δ, FJ.e B δ • dXc FJ Fr hε ρA dρA hcomm ψ cψ ccψ δ a +
        (FJ.toLCJet Fr hε ρA dρA hcomm).ω B • cov (FJ.toLCJet Fr hε ρA dρA hcomm).ω ψ
          (dψf FJ cψ) a -
        ∑ c, lcΓ Fr.ε (FJ.toLCJet Fr hε ρA dρA hcomm).G B a c •
          cov (FJ.toLCJet Fr hε ρA dρA hcomm).ω ψ (dψf FJ cψ) c := by
  unfold cov2
  rw [dcov_eq]

/-- The frame commutator relation for the spinor jets (`hψ` of `LCJet.spinor_prolongation`). -/
theorem hψ (cψ : Fin 4 → V) (ccψ : Fin 4 → Fin 4 → V) (hs : ∀ δ γ, ccψ δ γ = ccψ γ δ)
    (a b : Fin 4) :
    ddψf FJ cψ ccψ a b - ddψf FJ cψ ccψ b a =
      ∑ c, lcΛ Fr.ε (FJ.toLCJet Fr hε ρA dρA hcomm).G a b c • dψf FJ cψ c := by
  show _ = ∑ c, lcΛ Fr.ε FJ.G a b c • dψf FJ cψ c
  rw [hε]
  exact FJ.hψ_frame cψ ccψ hs a b

end Jets

/-! ### The prolonged rows in coordinates -/

section Rows

variable (FJ : FrameJet (Fin 4) (Fin 4)) (AF : AdaptedFrame) (hfr : ∀ B μ, FJ.e B μ = AF.fr B μ)
  (Fr : CliffordFrame (Fin 4) A) (hε : Fr.ε = FJ.ε) (hL : IsLorentzian Fr)
  (ρA : Fin 4 → A) (dρA : Fin 4 → Fin 4 → A) (hcomm : ∀ μ b, ρA μ * Fr.c b = Fr.c b * ρA μ)

include hfr in
theorem N_sum_e0 (X : Fin 4 → V) :
    AF.N • ∑ δ, FJ.e 0 δ • X δ = X 0 - ∑ j, AF.β j • X j.succ := by
  have := N_fD_zero AF X
  unfold fD at this
  rw [← this]
  simp only [hfr]

include hfr in
theorem sum_esucc (X : Fin 4 → V) (i : Fin 3) :
    ∑ δ, FJ.e i.succ δ • X δ = ∑ j, AF.E i j • X j.succ := by
  have := fD_succ AF X i
  unfold fD at this
  rw [← this]
  simp only [hfr]

include hfr hL in
/-- **The prolonged spinor rows in coordinates** (`prop:actual-jet-writer`): for every frame
index `a`, with `X_c = ∇_cΨ` and `∂_γX_a` the coordinate derivative jets,
`∂_tX_a - βʲ∂_jX_a - N Σ_{i,j} e_iʲ c_0c_i∂_jX_a =
  N(-ω_0X_a + Σ_c Γ_{0a}{}^cX_c + c_0Σ_i c_i(ω_iX_a - Σ_c Γ_{ia}{}^cX_c) - c_0R_a)`,
where `R_a` is the right side of `eq:spinor-prolongation` (`LCJet.spinor_prolongation`): the
principal matrices are `-βʲ - N e_iʲc_0c_i`, as for the Dirac head row. -/
theorem x_row {W : Type*} [AddCommGroup W] [Module ℝ W] (m0 : A) (L : W →ₗ[ℝ] A)
    (ρH : Fin 4 → W →ₗ[ℝ] W) (h : W) (dh : Fin 4 → W) (ψ : V) (cψ : Fin 4 → V)
    (ccψ : Fin 4 → Fin 4 → V) (hs : ∀ δ γ, ccψ δ γ = ccψ γ δ)
    (hMcl : ∀ w c d, mass m0 L w * (Fr.c c * Fr.c d) = Fr.c c * Fr.c d * mass m0 L w)
    (hMg : ∀ a w, (FJ.toLCJet Fr hε ρA dρA hcomm).ρ a * mass m0 L w -
      mass m0 L w * (FJ.toLCJet Fr hε ρA dρA hcomm).ρ a = L (ρH a w)) (a : Fin 4) :
    (dXc FJ Fr hε ρA dρA hcomm ψ cψ ccψ) 0 a - ∑ j, AF.β j • (dXc FJ Fr hε ρA dρA hcomm ψ cψ ccψ) j.succ a -
        AF.N • ∑ i : Fin 3, ∑ j, AF.E i j • ((Fr.c 0 * Fr.c i.succ) • (dXc FJ Fr hε ρA dρA hcomm ψ cψ ccψ) j.succ a) =
      AF.N • (-((FJ.toLCJet Fr hε ρA dρA hcomm).ω 0 • (cov (FJ.toLCJet Fr hε ρA dρA hcomm).ω ψ (dψf FJ cψ)) a) + ∑ c, lcΓ Fr.ε (FJ.toLCJet Fr hε ρA dρA hcomm).G 0 a c • (cov (FJ.toLCJet Fr hε ρA dρA hcomm).ω ψ (dψf FJ cψ)) c +
        Fr.c 0 • ∑ i : Fin 3, Fr.c i.succ • ((FJ.toLCJet Fr hε ρA dρA hcomm).ω i.succ • (cov (FJ.toLCJet Fr hε ρA dρA hcomm).ω ψ (dψf FJ cψ)) a - ∑ c, lcΓ Fr.ε (FJ.toLCJet Fr hε ρA dρA hcomm).G i.succ a c • (cov (FJ.toLCJet Fr hε ρA dρA hcomm).ω ψ (dψf FJ cψ)) c) -
        Fr.c 0 • (mass m0 L h • (cov (FJ.toLCJet Fr hε ρA dρA hcomm).ω ψ (dψf FJ cψ)) a + L (SpinorProlongation.DH ρH h dh a) • ψ +
          covResD Fr (FJ.toLCJet Fr hε ρA dρA hcomm).ω (FJ.toLCJet Fr hε ρA dρA hcomm).dω m0 L h dh ψ (dψf FJ cψ) (ddψf FJ cψ ccψ) a +
            ((1 / 2 : ℝ) • ∑ b, (Fr.ε b * ricciOf Fr.ε (FJ.toLCJet Fr hε ρA dρA hcomm).Rm a b) • Fr.c b) • ψ +
              (∑ b, Fr.ε b • (Fr.c b * (FJ.toLCJet Fr hε ρA dρA hcomm).F b a)) • ψ)) := by
  have hrow := ActualJetWriter.lc_prolonged_row Fr hL (FJ.toLCJet Fr hε ρA dρA hcomm) m0 L ρH h dh
    ψ (dψf FJ cψ) (ddψf FJ cψ ccψ) (hψ FJ Fr hε ρA dρA hcomm cψ ccψ hs) hMcl hMg a
  simp only [cov2_eq] at hrow
  set J := FJ.toLCJet Fr hε ρA dρA hcomm with hJ
  set X := cov J.ω ψ (dψf FJ cψ) with hX
  set dX := dXc FJ Fr hε ρA dρA hcomm ψ cψ ccψ with hdX
  set R := mass m0 L h • X a + L (SpinorProlongation.DH ρH h dh a) • ψ +
    covResD Fr J.ω J.dω m0 L h dh ψ (dψf FJ cψ) (ddψf FJ cψ ccψ) a +
      ((1 / 2 : ℝ) • ∑ b, (Fr.ε b * ricciOf Fr.ε J.Rm a b) • Fr.c b) • ψ +
        (∑ b, Fr.ε b • (Fr.c b * J.F b a)) • ψ with hR
  have h0 : ∑ δ, FJ.e 0 δ • dX δ a = Fr.c 0 • ∑ i : Fin 3, Fr.c i.succ •
      (∑ j, AF.E i j • dX j.succ a + (J.ω i.succ • X a - ∑ c, lcΓ Fr.ε J.G i.succ a c • X c)) -
      Fr.c 0 • R - (J.ω 0 • X a - ∑ c, lcΓ Fr.ε J.G 0 a c • X c) := by
    have e : ∀ i : Fin 3, ∑ δ, FJ.e i.succ δ • dX δ a + J.ω i.succ • X a -
        ∑ c, lcΓ Fr.ε J.G i.succ a c • X c = ∑ j, AF.E i j • dX j.succ a +
          (J.ω i.succ • X a - ∑ c, lcΓ Fr.ε J.G i.succ a c • X c) := by
      intro i
      rw [sum_esucc FJ AF hfr]
      abel
    simp only [e] at hrow

    calc ∑ δ, FJ.e 0 δ • dX δ a = (∑ δ, FJ.e 0 δ • dX δ a + J.ω 0 • X a -
          ∑ c, lcΓ Fr.ε J.G 0 a c • X c) - (J.ω 0 • X a - ∑ c, lcΓ Fr.ε J.G 0 a c • X c) := by abel
      _ = _ := by rw [hrow]
  have hN := N_sum_e0 FJ AF hfr (fun δ => dX δ a)
  rw [h0] at hN
  have hc : ∀ (i : Fin 3) (j : Fin 3), Fr.c 0 • Fr.c i.succ • AF.E i j • dX j.succ a =
      AF.E i j • ((Fr.c 0 * Fr.c i.succ) • dX j.succ a) := fun i j => by
    rw [mul_smul, smul_comm (Fr.c i.succ) (AF.E i j), smul_comm (Fr.c 0) (AF.E i j)]
  have hsplit : Fr.c 0 • ∑ i : Fin 3, Fr.c i.succ • (∑ j, AF.E i j • dX j.succ a +
      (J.ω i.succ • X a - ∑ c, lcΓ Fr.ε J.G i.succ a c • X c)) =
      ∑ i : Fin 3, ∑ j, AF.E i j • ((Fr.c 0 * Fr.c i.succ) • dX j.succ a) +
        Fr.c 0 • ∑ i : Fin 3, Fr.c i.succ •
          (J.ω i.succ • X a - ∑ c, lcΓ Fr.ε J.G i.succ a c • X c) := by
    simp only [smul_add, Finset.sum_add_distrib, Finset.smul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hc i j
  rw [hsplit] at hN
  rw [← hN]
  simp only [smul_sub, smul_add, smul_neg]
  abel

/-- The coordinate derivative jet `∂_γr_D` of the Dirac residual `r_D = Σ_b ε_bc_bX_b - 𝓜(H)Ψ`
(product rule; `dH γ = ∂_γH`). -/
def drc {W : Type*} [AddCommGroup W] [Module ℝ W] (m0 : A) (L : W →ₗ[ℝ] A) (h : W)
    (dH : Fin 4 → W) (ψ : V) (cψ : Fin 4 → V) (ccψ : Fin 4 → Fin 4 → V) (γ : Fin 4) : V :=
  ∑ b, Fr.ε b • (Fr.c b • dXc FJ Fr hε ρA dρA hcomm ψ cψ ccψ γ b) -
    (L (dH γ) • ψ + mass m0 L h • cψ γ)

/-- **The frame derivative of the Dirac residual is the contraction of its coordinate
derivative**: `e_a(r_D) = e_a{}^γ∂_γr_D`; for a tangential index only the spatial derivatives
`∂_jr_D` occur (`dresD_tangential`). -/
theorem dresD_eq {W : Type*} [AddCommGroup W] [Module ℝ W] (m0 : A) (L : W →ₗ[ℝ] A) (h : W)
    (dH : Fin 4 → W) (ψ : V) (cψ : Fin 4 → V) (ccψ : Fin 4 → Fin 4 → V) (a : Fin 4) :
    dresD Fr (FJ.toLCJet Fr hε ρA dρA hcomm).ω (FJ.toLCJet Fr hε ρA dρA hcomm).dω m0 L h
        (fun b => ∑ δ, FJ.e b δ • dH δ) ψ (dψf FJ cψ) (ddψf FJ cψ ccψ) a =
      ∑ δ, FJ.e a δ • drc FJ Fr hε ρA dρA hcomm m0 L h dH ψ cψ ccψ δ := by
  unfold dresD ddirac drc
  simp only [dcov_eq]
  unfold dψf
  simp only [map_sum, map_smul, Finset.smul_sum, smul_sub, smul_add,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_smul, smul_assoc]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun δ _ => Finset.sum_congr rfl fun b _ => ?_
    rw [smul_comm (Fr.c b) (FJ.e a δ), smul_comm (Fr.ε b) (FJ.e a δ)]
  · congr 1
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [smul_comm]

include hfr in
theorem dresD_tangential {W : Type*} [AddCommGroup W] [Module ℝ W] (m0 : A) (L : W →ₗ[ℝ] A)
    (h : W) (dH : Fin 4 → W) (ψ : V) (cψ : Fin 4 → V) (ccψ : Fin 4 → Fin 4 → V) (i : Fin 3) :
    dresD Fr (FJ.toLCJet Fr hε ρA dρA hcomm).ω (FJ.toLCJet Fr hε ρA dρA hcomm).dω m0 L h
        (fun b => ∑ δ, FJ.e b δ • dH δ) ψ (dψf FJ cψ) (ddψf FJ cψ ccψ) i.succ =
      ∑ j, AF.E i j • drc FJ Fr hε ρA dρA hcomm m0 L h dH ψ cψ ccψ j.succ := by
  rw [dresD_eq, sum_esucc FJ AF hfr]

/-- **Elimination of the Ricci term** of `eq:spinor-prolongation` by
`eq:trace-reversal-residual` (four dimensions, any stress `T`):
`½Σ_b ε_bRic_{ab}c_b = ½Σ_b ε_b(κT^{tr}(e_a, e_b) + Λε_aδ_{ab} + 𝓔^{tr}(e_a, e_b))c_b`. -/
theorem prolongation_ricci (T : Fin 4 → Fin 4 → ℝ) (Λ κ : ℝ) (a : Fin 4) :
    (1 / 2 : ℝ) • ∑ b, (Fr.ε b * ricciOf Fr.ε (FJ.toLCJet Fr hε ρA dρA hcomm).Rm a b) • Fr.c b =
      (1 / 2 : ℝ) • ∑ b, (Fr.ε b * (κ * ∑ μ, ∑ ν, FJ.e a μ * FJ.e b ν *
        HarmonicDefect.traceRev FJ.g FJ.gi T μ ν + Λ * (if a = b then FJ.ε a else 0) +
        ∑ μ, ∑ ν, FJ.e a μ * FJ.e b ν * HarmonicDefect.traceRev FJ.g FJ.gi
          (fun x y => HarmonicDefect.einstein FJ.g FJ.gi FJ.dg FJ.ddg x y + Λ * FJ.g x y -
            κ * T x y) μ ν)) • Fr.c b := by
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [FJ.frame_trace_reversal Fr hε ρA dρA hcomm (by simp) T Λ κ a b]

end Rows

end

end RenewalGeometry.ActualJetSpinor
