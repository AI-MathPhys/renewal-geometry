/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Metric reconstruction, the 3+1 endpoint, marked data, affine modular

* **Theorem `thm:metric-reconstruction` /
  Corollary `cor:symbol-reconstruction`** (polarisation core): the
  principal-symbol quadratic form determines the symmetric spatial
  block, `ξᵀAξ = ξᵀBξ` for all `ξ` forces `A = B`
  (`NCG.quadratic_determines_symm`); recovering `M` from `M² = κ⁻²A`
  is the unique positive square root (noted).

* **Corollary `cor:31-endpoint`** (normalisation): with the
  cross-polytope second moment `M = (1/d)·I` and clock normalisation
  `κ = d`, the multiplier coefficients are exactly the momenta,
  `κ·(Mξ)ᵢ = ξᵢ` (`NCG.endpoint_31_normalisation`) — with
  `NCG.KreinCliffordDatum.multiplier_square` the explicit endpoint
  symbol is the free Dirac symbol.

* **Definition `def:strictly-marked-dirac-datum` /
  Theorem `thm:marked-torus-classification`** (invariant core): the
  marked datum `(M, ρ)` is encoded (`NCG.MarkedDiracDatum`), and the
  retained deck scalars `(−1)^{ρ_k}` determine the marked class
  (`NCG.markedClass_injective`) — the classification separates marked
  classes through the deck representation.

* **Theorem `thm:affine-modular`**: the eigenoperator relation
  `[H, S_e] = β·S_e` and unit grading `[N, S_e] = S_e` place `H − βN`
  in the reset-shift commutant; the scalar-commutant axiom then gives
  `H = βN + c·1` (`NCG.affine_modular`). -/

namespace NCG

open Matrix

/-! ### Polarisation reconstruction
(`thm:metric-reconstruction`, `cor:symbol-reconstruction`) -/

section Reconstruction

variable {n : ℕ}

/-- Matrix entries from the symbol pairing:
`eᵢ ⬝ (M eⱼ) = Mᵢⱼ`. -/
theorem single_dotProduct_mulVec (M : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) :
    (Pi.single i (1:ℝ)) ⬝ᵥ (M *ᵥ Pi.single j 1) = M i j := by
  simp [dotProduct, Matrix.mulVec, Pi.single_apply, mul_ite, ite_mul,
    mul_zero, zero_mul, mul_one, one_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq']

/-- **Theorem `thm:metric-reconstruction`** (polarisation core): the
principal-symbol quadratic form determines the symmetric spatial block
`κ²M²` — evaluating on basis vectors and their sums recovers every
entry.  Recovering `M` itself is the unique positive square root of
`κ⁻²·(block)` (noted). -/
theorem quadratic_determines_symm (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (hB : B.IsSymm)
    (h : ∀ ξ : Fin n → ℝ, ξ ⬝ᵥ (A *ᵥ ξ) = ξ ⬝ᵥ (B *ᵥ ξ)) :
    A = B := by
  ext i j
  have hdiag : ∀ k, A k k = B k k := fun k => by
    have hk := h (Pi.single k 1)
    rwa [single_dotProduct_mulVec, single_dotProduct_mulVec] at hk
  have hpair := h (Pi.single i 1 + Pi.single j 1)
  simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct,
    single_dotProduct_mulVec] at hpair
  have hAsym : A j i = A i j := congrFun (congrFun hA i) j
  have hBsym : B j i = B i j := congrFun (congrFun hB i) j
  have h1 := hdiag i
  have h2 := hdiag j
  linarith

end Reconstruction

/-! ### The explicit `3+1` endpoint (`cor:31-endpoint`) -/

/-- **Corollary `cor:31-endpoint`** (normalisation): the cross-polytope
second moment `M = (1/d)·I` with the calibrated clock `κ = d` gives
multiplier coefficients equal to the momenta — the endpoint multiplier
squares to `|ξ|²·1` (`NCG.KreinCliffordDatum.multiplier_square`), the
free Dirac symbol. -/
theorem endpoint_31_normalisation {d : ℕ} (hd : 0 < d)
    (ξ : Fin d → ℝ) (i : Fin d) :
    (d : ℝ) * ((1 / d) * ξ i) = ξ i := by
  have hd' : ((d:ℕ):ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  rw [← mul_assoc, mul_one_div, div_self hd', one_mul]

/-! ### Marked Dirac data (`def:strictly-marked-dirac-datum`,
`thm:marked-torus-classification`) -/

/-- **Definition `def:strictly-marked-dirac-datum`**: a marked
flat-torus Dirac datum — the symmetric second-moment block together
with the marked `ℤ/2` winding class retained by the deck
representation. -/
structure MarkedDiracDatum (d : ℕ) where
  /-- the spatial second-moment block -/
  M : Matrix (Fin d) (Fin d) ℝ
  /-- the marked winding class -/
  ρ : Fin d → ZMod 2
  M_symm : M.IsSymm

/-- **Theorem `thm:marked-torus-classification`** (invariant core): the
retained deck scalars `(−1)^{ρ_k}` determine the marked class — the
deck representation separates marked flat-torus data. -/
theorem markedClass_injective {d : ℕ} :
    Function.Injective
      (fun ρ : Fin d → ZMod 2 => fun k => ((-1:ℤ)) ^ (ρ k).val) := by
  intro ρ ρ' h
  funext k
  have hk := congrFun h k
  simp only at hk
  have hval : ∀ x y : ZMod 2,
      ((-1:ℤ)) ^ x.val = (-1) ^ y.val → x = y := by decide
  exact hval _ _ hk

/-! ### The affine modular Hamiltonian (`thm:affine-modular`) -/

/-- **Theorem `thm:affine-modular`**: if `H` has every reset shift as a
`β`-eigenoperator (`[H, S_e] = β·S_e`) and the clock grades shifts by
one (`[N, S_e] = S_e`), then `H − βN` commutes with every shift; the
scalar-commutant hypothesis gives the affine form `H = βN + c·1`. -/
theorem affine_modular {A : Type*} [Ring A] [Algebra ℝ A]
    {ι : Type*} (S : ι → A) (H N : A) (β : ℝ)
    (hH : ∀ e, H * S e - S e * H = β • S e)
    (hN : ∀ e, N * S e - S e * N = S e)
    (hcomm : ∀ x : A, (∀ e, x * S e = S e * x) → ∃ c : ℝ, x = c • 1) :
    ∃ c : ℝ, H = β • N + c • 1 := by
  obtain ⟨c, hc⟩ := hcomm (H - β • N) (fun e => by
    have h1 : H * S e = S e * H + β • S e := by
      rw [← sub_eq_iff_eq_add']
      exact hH e
    have h2 : N * S e = S e * N + S e := by
      rw [← sub_eq_iff_eq_add']
      exact hN e
    calc (H - β • N) * S e
        = H * S e - β • (N * S e) := by
          rw [sub_mul, smul_mul_assoc]
      _ = (S e * H + β • S e) - β • (S e * N + S e) := by
          rw [h1, h2]
      _ = S e * H - β • (S e * N) := by
          rw [smul_add]
          abel
      _ = S e * (H - β • N) := by
          rw [mul_sub, mul_smul_comm])
  refine ⟨c, ?_⟩
  rw [← sub_eq_iff_eq_add']
  exact hc

end NCG
