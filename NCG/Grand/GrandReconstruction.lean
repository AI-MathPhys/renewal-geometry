/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.BSDBridge

/-!
# Reconstruction and transport toolkit
  (`corollary:two-and-three-point-reconstruction`,
   `thm:Hodge-Dirac-transport`, `lem:one-complex-orbit-rank`,
   Gran-Tensor manuscript)

* `coefficient_recovery` / `three_point_reconstruction`: with an
  invertible basis Gram `G`, the coefficients of any expansion
  are recovered as `c = G⁻¹m` from its pairings — so the two-
  and three-point panels `G, M, J, u` determine multiplication
  (`c_{jk} = G⁻¹M_{·jk}`), involution (`d_j = G⁻¹J_{·j}`), and
  unit (`e = G⁻¹u`);
* `hodge_dirac_transport`: unitary chain maps intertwining the
  differentials transport the Hodge Laplacian
  (`U₁Δ = Δ'U₁` for `Δ = d₀d₀ᴴ + d₁ᴴd₁`) and identify the
  harmonic dimensions (`dim Ker Δ = dim Ker Δ'`);
* `one_complex_orbit_rank`: the real span of a conjugate orbit
  pair `{v, v̄}` has dimension at most two — no three
  independent real innovation directions from one complex
  character–Mellin orbit.

Rendering disclosed: the identification of the abstract pairing
panels with the physically measured two- and three-point word
moments is the Grand-Tensor loading bookkeeping; analytic
torsion and determinant-line clauses of the transport theorem
are the singular-value bookkeeping of the proved Laplacian
conjugation.
-/

open Matrix

namespace NCG

/-- Coefficient recovery: with invertible basis Gram `G` and
sesquilinear pairings `m_i = ⟨a_i, x⟩` of an expansion
`x = Σ c_l·a_l`, the coefficients are `c = G⁻¹m`. -/
theorem coefficient_recovery {d : ℕ}
    (G : Matrix (Fin d) (Fin d) ℂ) (hG : IsUnit G.det)
    (c m : Fin d → ℂ) (hm : G *ᵥ c = m) :
    c = G⁻¹ *ᵥ m := by
  rw [← hm, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hG,
    Matrix.one_mulVec]

/-- `corollary:two-and-three-point-reconstruction`: the panels
`G, M, J, u` determine multiplication, involution, and unit —
each coefficient family is `G⁻¹` applied to its pairing
column. -/
theorem three_point_reconstruction {d : ℕ}
    (G : Matrix (Fin d) (Fin d) ℂ) (hG : IsUnit G.det)
    -- multiplication: a_j a_k = Σ_l c_{jk}^l a_l with
    -- three-point pairings M_{i;jk} = ⟨a_i, a_j a_k⟩
    (cmul : Fin d → Fin d → Fin d → ℂ)
    (M : Fin d → Fin d → Fin d → ℂ)
    (hMul : ∀ j k, G *ᵥ (fun l => cmul j k l)
      = fun i => M i j k)
    -- involution: a_j* = Σ_l d_j^l a_l with J_{ij} = ⟨a_i, a_j*⟩
    (dinv : Fin d → Fin d → ℂ) (J : Fin d → Fin d → ℂ)
    (hInv : ∀ j, G *ᵥ (fun l => dinv j l) = fun i => J i j)
    -- unit: 1 = Σ_l e^l a_l with u_i = ⟨a_i, 1⟩
    (e : Fin d → ℂ) (u : Fin d → ℂ) (hU : G *ᵥ e = u) :
    (∀ j k, (fun l => cmul j k l)
        = G⁻¹ *ᵥ (fun i => M i j k))
    ∧ (∀ j, (fun l => dinv j l) = G⁻¹ *ᵥ (fun i => J i j))
    ∧ e = G⁻¹ *ᵥ u :=
  ⟨fun j k => coefficient_recovery G hG _ _ (hMul j k),
    fun j => coefficient_recovery G hG _ _ (hInv j),
    coefficient_recovery G hG e u hU⟩

/-- `thm:Hodge-Dirac-transport`: unitary chain maps intertwining
the differentials transport the Hodge Laplacian and identify the
harmonic dimensions. -/
theorem hodge_dirac_transport {c0 c1 c2 : Type*} [Fintype c0]
    [Fintype c1] [Fintype c2] [DecidableEq c0] [DecidableEq c1]
    [DecidableEq c2]
    (d0 d0' : Matrix c1 c0 ℂ) (d1 d1' : Matrix c2 c1 ℂ)
    (U0 : Matrix c0 c0 ℂ) (U1 : Matrix c1 c1 ℂ)
    (U2 : Matrix c2 c2 ℂ)
    (_hU0 : U0ᴴ * U0 = 1) (hU0' : U0 * U0ᴴ = 1)
    (hU1 : U1ᴴ * U1 = 1) (hU1' : U1 * U1ᴴ = 1)
    (hU2 : U2ᴴ * U2 = 1) (_hU2' : U2 * U2ᴴ = 1)
    (hc0 : U1 * d0 = d0' * U0) (hc1 : U2 * d1 = d1' * U1) :
    U1 * (d0 * d0ᴴ + d1ᴴ * d1)
      = (d0' * d0'ᴴ + d1'ᴴ * d1') * U1
    ∧ Module.finrank ℂ
        (LinearMap.ker (d0 * d0ᴴ + d1ᴴ * d1).mulVecLin)
      = Module.finrank ℂ
        (LinearMap.ker (d0' * d0'ᴴ + d1'ᴴ * d1').mulVecLin) := by
  have hadj0 : U0 * d0ᴴ = d0'ᴴ * U1 := by
    have h := congrArg Matrix.conjTranspose hc0
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
      at h
    calc U0 * d0ᴴ
        = U0 * d0ᴴ * (1 : Matrix c1 c1 ℂ) := by
          rw [Matrix.mul_one]
      _ = U0 * d0ᴴ * (U1ᴴ * U1) := by rw [hU1]
      _ = U0 * (d0ᴴ * U1ᴴ) * U1 := by
          simp only [Matrix.mul_assoc]
      _ = U0 * (U0ᴴ * d0'ᴴ) * U1 := by rw [h]
      _ = (U0 * U0ᴴ) * (d0'ᴴ * U1) := by
          simp only [Matrix.mul_assoc]
      _ = d0'ᴴ * U1 := by rw [hU0', Matrix.one_mul]
  have hadj1 : U1 * d1ᴴ = d1'ᴴ * U2 := by
    have h := congrArg Matrix.conjTranspose hc1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
      at h
    calc U1 * d1ᴴ
        = U1 * d1ᴴ * (1 : Matrix c2 c2 ℂ) := by
          rw [Matrix.mul_one]
      _ = U1 * d1ᴴ * (U2ᴴ * U2) := by rw [hU2]
      _ = U1 * (d1ᴴ * U2ᴴ) * U2 := by
          simp only [Matrix.mul_assoc]
      _ = U1 * (U1ᴴ * d1'ᴴ) * U2 := by rw [h]
      _ = (U1 * U1ᴴ) * (d1'ᴴ * U2) := by
          simp only [Matrix.mul_assoc]
      _ = d1'ᴴ * U2 := by rw [hU1', Matrix.one_mul]
  have hint : U1 * (d0 * d0ᴴ + d1ᴴ * d1)
      = (d0' * d0'ᴴ + d1'ᴴ * d1') * U1 := by
    rw [Matrix.mul_add, Matrix.add_mul]
    congr 1
    · calc U1 * (d0 * d0ᴴ)
          = (U1 * d0) * d0ᴴ := by rw [Matrix.mul_assoc]
        _ = d0' * (U0 * d0ᴴ) := by
            rw [hc0, Matrix.mul_assoc]
        _ = d0' * (d0'ᴴ * U1) := by rw [hadj0]
        _ = d0' * d0'ᴴ * U1 := by rw [Matrix.mul_assoc]
    · calc U1 * (d1ᴴ * d1)
          = (U1 * d1ᴴ) * d1 := by rw [Matrix.mul_assoc]
        _ = d1'ᴴ * (U2 * d1) := by
            rw [hadj1, Matrix.mul_assoc]
        _ = d1'ᴴ * (d1' * U1) := by rw [hc1]
        _ = d1'ᴴ * d1' * U1 := by rw [Matrix.mul_assoc]
  refine ⟨hint, ?_⟩
  have hU1unit : IsUnit U1 := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have hdet := congrArg Matrix.det hU1
    rw [Matrix.det_mul, Matrix.det_one] at hdet
    have hdet' : U1.det * U1ᴴ.det = 1 := by
      rwa [mul_comm] at hdet
    exact ⟨Units.mkOfMulEqOne _ _ hdet', rfl⟩
  have hconj : d0' * d0'ᴴ + d1'ᴴ * d1'
      = U1 * (d0 * d0ᴴ + d1ᴴ * d1) * U1⁻¹ := by
    rw [hint, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _
        ((Matrix.isUnit_iff_isUnit_det U1).mp hU1unit),
      Matrix.mul_one]
  rw [hconj, kernel_dim_conjugation _ _
    ((Matrix.isUnit_iff_isUnit_det U1).mp hU1unit)]

/-- `lem:one-complex-orbit-rank`: the real span of a conjugate
orbit pair `{v, v̄}` has dimension at most two. -/
theorem one_complex_orbit_rank {d : ℕ} (v : Fin d → ℂ) :
    Module.finrank ℝ
      (Submodule.span ℝ ({v, star v} : Set (Fin d → ℂ)))
      ≤ 2 := by
  classical
  rw [show ({v, star v} : Set (Fin d → ℂ))
      = (({v, star v} : Finset (Fin d → ℂ))
        : Set (Fin d → ℂ)) from by simp]
  refine le_trans (finrank_span_finset_le_card _) ?_
  exact le_trans (Finset.card_insert_le _ _) (by simp)

end NCG
