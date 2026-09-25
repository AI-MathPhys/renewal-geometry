/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Persistence of the ADM packet under summable bracket/speed defects
  (`mt:adm` clause (vii), ADM-packet part; `eq:adm-inversion-main`;
  emergent-spacetime manuscript)

The boxed ADM inversion `eq:adm-inversion-main`
`g = ϱ^{2/3} (det 𝓑)^{1/3} 𝓑⁻¹`, `N = ϱ^{1/3} (det 𝓑)^{1/6}` (`admMetric`,
`admLapse`; the same expressions as in `Gravity/RelationalSchedulerADM.lean`
clause (A4) and `Gravity/ADMFrameUniqueness.lean`) is continuous on the
nondegenerate cone `det 𝓑 > 0` (`admPacket_continuousAt`).  Consequently a
cofinal sequence of brackets and speed densities whose successive defects are
summable ("summably correctable" mixed-Gram/refinement defects) converges,
and whenever the limit bracket is nondegenerate the reconstructed ADM
metric and lapse converge to the ADM packet of the limit
(`adm_packet_persists_of_summable_defects`).

This is the ADM-packet part of clause (vii) of `mt:adm`; the dimension,
source-rank and pair-gap persistence are in
`Dimension/DimensionCofinal3Plus1.lean`, and the signed-inertia statement is
`Krein/OneLineSignedExtensionInertia.lean:oneLineSignedExtension_inertia_lorentz`.
The identification of the canonical cofinal limit quotient itself is not
formalised here.
-/

open Filter Topology

namespace RenewalGeometry

/-- Boxed ADM spatial metric `g = ϱ^{2/3} (det 𝓑)^{1/3} 𝓑⁻¹`
(`eq:adm-inversion-main`). -/
noncomputable def admMetric (B : Matrix (Fin 3) (Fin 3) ℝ) (ϱ : ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (ϱ ^ ((2 : ℝ) / 3) * B.det ^ ((1 : ℝ) / 3)) • B⁻¹

/-- Boxed ADM lapse `N = ϱ^{1/3} (det 𝓑)^{1/6}` (`eq:adm-inversion-main`). -/
noncomputable def admLapse (B : Matrix (Fin 3) (Fin 3) ℝ) (ϱ : ℝ) : ℝ :=
  ϱ ^ ((1 : ℝ) / 3) * B.det ^ ((1 : ℝ) / 6)

/-- The ADM inversion is continuous in the bracket and the speed density on
the nondegenerate cone `det 𝓑 > 0`. -/
theorem admPacket_continuousAt (B : Matrix (Fin 3) (Fin 3) ℝ) (ϱ : ℝ) (hB : 0 < B.det) :
    ContinuousAt (fun p : Matrix (Fin 3) (Fin 3) ℝ × ℝ => admMetric p.1 p.2) (B, ϱ) ∧
    ContinuousAt (fun p : Matrix (Fin 3) (Fin 3) ℝ × ℝ => admLapse p.1 p.2) (B, ϱ) := by
  have hdet : ContinuousAt (fun p : Matrix (Fin 3) (Fin 3) ℝ × ℝ => p.1.det) (B, ϱ) :=
    (continuous_fst.matrix_det).continuousAt
  have hsnd : ContinuousAt (fun p : Matrix (Fin 3) (Fin 3) ℝ × ℝ => p.2) (B, ϱ) :=
    continuous_snd.continuousAt
  have hinv : ContinuousAt (fun p : Matrix (Fin 3) (Fin 3) ℝ × ℝ => p.1⁻¹) (B, ϱ) := by
    have h1 : ContinuousAt (Ring.inverse : ℝ → ℝ) B.det := by
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hB.ne'
    exact (continuousAt_matrix_inv B h1).comp continuous_fst.continuousAt
  refine ⟨?_, ?_⟩
  · exact ((hsnd.rpow_const (Or.inr (by norm_num))).mul
      (hdet.rpow_const (Or.inr (by norm_num)))).smul hinv
  · exact (hsnd.rpow_const (Or.inr (by norm_num))).mul
      (hdet.rpow_const (Or.inr (by norm_num)))

/-- A real sequence with summable successive defects converges. -/
theorem real_tendsto_of_summable_defects (u : ℕ → ℝ)
    (hu : Summable fun n => |u (n + 1) - u n|) :
    ∃ l : ℝ, Tendsto u atTop (𝓝 l) := by
  refine cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist ?_)
  simp only [Real.dist_eq, Nat.succ_eq_add_one]
  exact hu.congr fun n => by rw [abs_sub_comm]

/-- Entrywise convergence of `3 × 3` matrices is convergence of matrices. -/
theorem matrix_tendsto_of_entries (B : ℕ → Matrix (Fin 3) (Fin 3) ℝ)
    (L : Fin 3 → Fin 3 → ℝ)
    (hL : ∀ i j, Tendsto (fun n => B n i j) atTop (𝓝 (L i j))) :
    Tendsto B atTop (𝓝 (Matrix.of L)) := by
  have h : Tendsto (fun n => (B n : Fin 3 → Fin 3 → ℝ)) atTop (𝓝 L) :=
    tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => hL i j
  exact h

/-- A sequence of brackets with summable entrywise successive defects
converges. -/
theorem matrix_tendsto_of_summable_defects (B : ℕ → Matrix (Fin 3) (Fin 3) ℝ)
    (hB : ∀ i j, Summable fun n => |B (n + 1) i j - B n i j|) :
    ∃ Blim : Matrix (Fin 3) (Fin 3) ℝ, Tendsto B atTop (𝓝 Blim) := by
  have hlim : ∀ i j, ∃ l : ℝ, Tendsto (fun n => B n i j) atTop (𝓝 l) :=
    fun i j => real_tendsto_of_summable_defects _ (hB i j)
  choose L hL using hlim
  exact ⟨Matrix.of L, matrix_tendsto_of_entries B L hL⟩

/-- The ADM packet is continuous along convergent brackets and speed
densities with nondegenerate limit bracket. -/
theorem admPacket_tendsto (B : ℕ → Matrix (Fin 3) (Fin 3) ℝ) (ϱ : ℕ → ℝ)
    (Blim : Matrix (Fin 3) (Fin 3) ℝ) (ϱlim : ℝ) (hdet : 0 < Blim.det)
    (hBt : Tendsto B atTop (𝓝 Blim)) (hϱt : Tendsto ϱ atTop (𝓝 ϱlim)) :
    Tendsto (fun n => admMetric (B n) (ϱ n)) atTop (𝓝 (admMetric Blim ϱlim)) ∧
    Tendsto (fun n => admLapse (B n) (ϱ n)) atTop (𝓝 (admLapse Blim ϱlim)) := by
  have hc := admPacket_continuousAt Blim ϱlim hdet
  have hprod : Tendsto (fun n => (B n, ϱ n)) atTop (𝓝 (Blim, ϱlim)) :=
    hBt.prodMk_nhds hϱt
  have h1 := hc.1.tendsto.comp hprod
  have h2 := hc.2.tendsto.comp hprod
  exact ⟨h1, h2⟩

/-- `mt:adm` (vii), ADM-packet part: brackets and speed densities with
summable successive defects converge, and if the limit bracket is
nondegenerate the reconstructed ADM metric and lapse converge to the ADM
packet of the limit. -/
theorem adm_packet_persists_of_summable_defects (B : ℕ → Matrix (Fin 3) (Fin 3) ℝ)
    (ϱ : ℕ → ℝ)
    (hB : ∀ i j, Summable fun n => |B (n + 1) i j - B n i j|)
    (hϱ : Summable fun n => |ϱ (n + 1) - ϱ n|) :
    ∃ Blim : Matrix (Fin 3) (Fin 3) ℝ, ∃ ϱlim : ℝ,
      Tendsto B atTop (𝓝 Blim) ∧ Tendsto ϱ atTop (𝓝 ϱlim) ∧
      (0 < Blim.det →
        Tendsto (fun n => admMetric (B n) (ϱ n)) atTop (𝓝 (admMetric Blim ϱlim)) ∧
        Tendsto (fun n => admLapse (B n) (ϱ n)) atTop (𝓝 (admLapse Blim ϱlim))) := by
  obtain ⟨Blim, hBt⟩ := matrix_tendsto_of_summable_defects B hB
  obtain ⟨ϱlim, hϱt⟩ := real_tendsto_of_summable_defects ϱ hϱ
  exact ⟨Blim, ϱlim, hBt, hϱt, fun hdet => admPacket_tendsto B ϱ Blim ϱlim hdet hBt hϱt⟩

end RenewalGeometry
