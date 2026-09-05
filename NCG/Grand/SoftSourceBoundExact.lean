/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.OperationalConeExact

/-!
# The scale-matched soft-source bound

Machinery for `thm:GRH-soft-source-ledger` (GRH.4): if `G_s = A + sH` is a Hermitian
pencil with `‖H‖ ≤ ca` that is singular at some `s₀ ∈ [0,1]`, then

`∫₀¹ Tr[a²(G_s² + a²)⁻¹] ds ≥ arctan(c)/c`,

independently of the spectral floor and the dimension.  The proof pins a unit kernel
vector of `G_{s₀}`, bounds the quadratic form by Cauchy–Schwarz for the inverse
(`dot_inv_lower`), integrates the Cauchy kernel exactly (`integral_cauchy_kernel`), and
minimizes over the singular location by arctan superadditivity (`arctan_superadd`).
-/

open Matrix intervalIntegral

namespace NCG
namespace SoftSource

/-! ### Arctan superadditivity and the Cauchy-kernel integral -/

/-- Arctan is subadditive on the nonnegative axis. -/
theorem arctan_superadd {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.arctan (x + y) ≤ Real.arctan x + Real.arctan y := by
  rcases eq_or_lt_of_le hx with rfl | hx'
  · simp
  rcases eq_or_lt_of_le hy with rfl | hy'
  · simp
  rcases lt_or_ge (x * y) 1 with hxy | hxy
  · rw [Real.arctan_add hxy]
    refine Real.arctan_le_arctan_iff.mpr ?_
    rw [le_div_iff₀ (by nlinarith)]
    nlinarith [mul_pos (add_pos hx' hy') (mul_pos hx' hy')]
  · have hyx : x⁻¹ ≤ y := by
      rw [inv_eq_one_div, div_le_iff₀ hx']
      nlinarith
    have h1 : Real.pi / 2 ≤ Real.arctan x + Real.arctan y := by
      have h2 := Real.arctan_inv_of_pos hx'
      have h3 : Real.arctan x⁻¹ ≤ Real.arctan y := Real.arctan_le_arctan_iff.mpr hyx
      linarith
    linarith [Real.arctan_lt_pi_div_two (x + y)]

/-- The exact Cauchy-kernel integral with affine argument. -/
theorem integral_cauchy_kernel (c s₀ : ℝ) (hc : 0 < c) :
    (∫ s in (0:ℝ)..1, (1 + (c * (s - s₀)) ^ 2)⁻¹)
      = (Real.arctan (c * (1 - s₀)) - Real.arctan (c * (0 - s₀))) / c := by
  have hF : ∀ s : ℝ, HasDerivAt (fun s => Real.arctan (c * (s - s₀)) / c)
      ((1 + (c * (s - s₀)) ^ 2)⁻¹) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => c * (s - s₀)) c s := by
      simpa using ((hasDerivAt_id s).sub_const s₀).const_mul c
    have h2 := (Real.hasDerivAt_arctan' (c * (s - s₀))).comp s h1
    have h3 := h2.div_const c
    have hval : (1 + (c * (s - s₀)) ^ 2)⁻¹ * c / c = (1 + (c * (s - s₀)) ^ 2)⁻¹ := by
      field_simp
    rw [← hval]
    exact h3
  have hcont : Continuous fun s : ℝ => (1 + (c * (s - s₀)) ^ 2)⁻¹ := by
    refine Continuous.inv₀ ?_ fun s => by positivity
    exact continuous_const.add (((continuous_const.mul
      (continuous_id.sub continuous_const)).pow 2))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hF s)
    (hcont.intervalIntegrable 0 1)]
  ring

/-- The endpoint minimization: the singular location extremizes the Cauchy mass. -/
theorem cauchy_integral_lower {c : ℝ} (hc : 0 < c) {s₀ : ℝ} (h0 : 0 ≤ s₀)
    (h1 : s₀ ≤ 1) :
    Real.arctan c / c
      ≤ (Real.arctan (c * (1 - s₀)) - Real.arctan (c * (0 - s₀))) / c := by
  have hodd : Real.arctan (c * (0 - s₀)) = -Real.arctan (c * s₀) := by
    rw [show c * (0 - s₀) = -(c * s₀) from by ring, Real.arctan_neg]
  rw [hodd, sub_neg_eq_add]
  have hcore : Real.arctan c ≤ Real.arctan (c * (1 - s₀)) + Real.arctan (c * s₀) := by
    have h := arctan_superadd (x := c * (1 - s₀)) (y := c * s₀)
      (by nlinarith) (by nlinarith)
    rwa [show c * (1 - s₀) + c * s₀ = c from by ring] at h
  gcongr

/-! ### Cauchy–Schwarz for the inverse quadratic form -/

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Cauchy–Schwarz for the dot product. -/
theorem dot_sq_le (x y : n → ℝ) : (x ⬝ᵥ y) ^ 2 ≤ (x ⬝ᵥ x) * (y ⬝ᵥ y) := by
  rcases eq_or_ne (y ⬝ᵥ y) 0 with hy | hy
  · have hy0 : ∀ i, y i = 0 := by
      intro i
      have hsum : (∑ j, y j * y j) = 0 := hy
      have := Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => mul_self_nonneg (y j)) |>.mp hsum i (Finset.mem_univ i)
      nlinarith [this]
    have hxy : x ⬝ᵥ y = 0 := by
      rw [dotProduct]
      exact Finset.sum_eq_zero fun i _ => by rw [hy0 i, mul_zero]
    rw [hxy, hy]
    norm_num
  · have hkey := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) =>
      sq_nonneg ((y ⬝ᵥ y) * x i - (x ⬝ᵥ y) * y i)
    have hexp : (∑ i, ((y ⬝ᵥ y) * x i - (x ⬝ᵥ y) * y i) ^ 2)
        = (y ⬝ᵥ y) * ((y ⬝ᵥ y) * (x ⬝ᵥ x) - (x ⬝ᵥ y) ^ 2) := by
      have h1 : (∑ i, ((y ⬝ᵥ y) * x i - (x ⬝ᵥ y) * y i) ^ 2)
          = (y ⬝ᵥ y) ^ 2 * (x ⬝ᵥ x) - 2 * (y ⬝ᵥ y) * (x ⬝ᵥ y) * (x ⬝ᵥ y)
            + (x ⬝ᵥ y) ^ 2 * (y ⬝ᵥ y) := by
        have hterm : ∀ i, ((y ⬝ᵥ y) * x i - (x ⬝ᵥ y) * y i) ^ 2
            = (y ⬝ᵥ y) ^ 2 * (x i * x i) - 2 * (y ⬝ᵥ y) * (x ⬝ᵥ y) * (x i * y i)
              + (x ⬝ᵥ y) ^ 2 * (y i * y i) := fun i => by ring
        rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib,
          Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
        rfl
      rw [h1]
      ring
    rw [hexp] at hkey
    have hypos : 0 < y ⬝ᵥ y := by
      rcases lt_or_eq_of_le (Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) =>
        mul_self_nonneg (y i)) with h | h
      · exact h
      · exact absurd h.symm hy
    nlinarith

open scoped MatrixOrder

omit [DecidableEq n] in
/-- Transpose swap for real quadratic forms. -/
theorem dot_swap (T : Matrix n n ℝ) (u w : n → ℝ) :
    (T *ᵥ u) ⬝ᵥ w = u ⬝ᵥ (Tᵀ *ᵥ w) := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]

omit [DecidableEq n] in
/-- A nonzero vector has positive self-product. -/
theorem dot_self_pos {v : n → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v := by
  rcases lt_or_eq_of_le (Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) =>
    mul_self_nonneg (v i)) with h | h
  · exact h
  · exfalso
    apply hv
    funext i
    have h0 := Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ Finset.univ) => mul_self_nonneg (v j)) |>.mp h.symm i
      (Finset.mem_univ i)
    have hvi : v i = 0 := by nlinarith [h0]
    simpa using hvi

/-- **Cauchy–Schwarz for the inverse**: `⟨v, M⁻¹v⟩ ≥ ⟨v, Mv⟩⁻¹` on unit vectors. -/
theorem dot_inv_lower {M : Matrix n n ℝ} (hM : M.PosDef) {v : n → ℝ}
    (hv : v ⬝ᵥ v = 1) : (v ⬝ᵥ M *ᵥ v)⁻¹ ≤ v ⬝ᵥ M⁻¹ *ᵥ v := by
  classical
  have hM0 : 0 ≤ M := hM.posSemidef.nonneg
  set S := CFC.sqrt M with hSdef
  have hSH : Sᴴ = S := (CFC.sqrt_nonneg M).posSemidef.isHermitian
  have hSS : S * S = M := CFC.sqrt_mul_sqrt_self M hM0
  have hSunit : IsUnit S :=
    (CFC.isUnit_sqrt_iff M hM0).mpr ((isUnit_iff_isUnit_det M).mpr
      hM.det_pos.ne'.isUnit)
  have hSdet : IsUnit S.det := (isUnit_iff_isUnit_det S).mp hSunit
  have hSinv : S * S⁻¹ = 1 := mul_nonsing_inv S hSdet
  have hMinv : M⁻¹ = S⁻¹ * S⁻¹ := by
    rw [← hSS, Matrix.mul_inv_rev]
  have hST : Sᵀ = S := by
    have h := hSH
    rwa [conjTranspose_eq_transpose_of_trivial] at h
  have hSinvT : S⁻¹ᵀ = S⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hST]
  have hxy : (S *ᵥ v) ⬝ᵥ (S⁻¹ *ᵥ v) = 1 := by
    rw [dot_swap, hST, mulVec_mulVec, hSinv, one_mulVec, hv]
  have hxx : (S *ᵥ v) ⬝ᵥ (S *ᵥ v) = v ⬝ᵥ M *ᵥ v := by
    rw [dot_swap, hST, mulVec_mulVec, hSS]
  have hyy : (S⁻¹ *ᵥ v) ⬝ᵥ (S⁻¹ *ᵥ v) = v ⬝ᵥ M⁻¹ *ᵥ v := by
    rw [dot_swap, hSinvT, mulVec_mulVec, ← hMinv]
  have hcs := dot_sq_le (S *ᵥ v) (S⁻¹ *ᵥ v)
  rw [hxy, hxx, hyy] at hcs
  have hMv : 0 < v ⬝ᵥ M *ᵥ v := by
    have hvne : v ≠ 0 := by
      intro h0
      rw [h0] at hv
      simp [dotProduct] at hv
    have h := hM.dotProduct_mulVec_pos (x := v) hvne
    simpa [star_trivial] using h
  have h1 : 1 ≤ (v ⬝ᵥ M *ᵥ v) * (v ⬝ᵥ M⁻¹ *ᵥ v) := by nlinarith [hcs]
  calc (v ⬝ᵥ M *ᵥ v)⁻¹ = (v ⬝ᵥ M *ᵥ v)⁻¹ * 1 := (mul_one _).symm
    _ ≤ (v ⬝ᵥ M *ᵥ v)⁻¹ * ((v ⬝ᵥ M *ᵥ v) * (v ⬝ᵥ M⁻¹ *ᵥ v)) :=
        mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hMv).le
    _ = v ⬝ᵥ M⁻¹ *ᵥ v := by
        rw [← mul_assoc, inv_mul_cancel₀ hMv.ne', one_mul]

/-- The trace of a positive matrix dominates every unit quadratic form. -/
theorem trace_ge_dot {Q : Matrix n n ℝ} (hQ : Q.PosSemidef) {v : n → ℝ}
    (hv : v ⬝ᵥ v = 1) : v ⬝ᵥ Q *ᵥ v ≤ Q.trace := by
  classical
  have hPx : ∀ x : n → ℝ, ∀ i, (vecMulVec v v *ᵥ x) i = v i * (v ⬝ᵥ x) := by
    intro x i
    simp only [mulVec, dotProduct, vecMulVec_apply]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hP : (1 - vecMulVec v v).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · change (1 - vecMulVec v v)ᴴ = 1 - vecMulVec v v
      rw [conjTranspose_sub, conjTranspose_one]
      congr 1
      apply Matrix.ext
      intro i j
      simp [vecMulVec_apply, conjTranspose_apply, mul_comm]
    · rw [star_trivial, sub_mulVec, dotProduct_sub, one_mulVec]
      have hvv : x ⬝ᵥ (vecMulVec v v *ᵥ x) = (v ⬝ᵥ x) ^ 2 := by
        calc x ⬝ᵥ (vecMulVec v v *ᵥ x) = ∑ i, x i * (v i * (v ⬝ᵥ x)) := by
              rw [dotProduct]
              exact Finset.sum_congr rfl fun i _ => by rw [hPx x i]
          _ = (v ⬝ᵥ x) * ∑ i, x i * v i := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun i _ => by ring
          _ = (v ⬝ᵥ x) ^ 2 := by
              rw [show (∑ i, x i * v i) = x ⬝ᵥ v from rfl, dotProduct_comm]
              ring
      rw [hvv]
      have hcs := dot_sq_le v x
      rw [hv, one_mul] at hcs
      linarith
  have h2 := OperationalCone.trace_mul_nonneg hQ hP
  have h3 : (Q * (1 - vecMulVec v v)).trace = Q.trace - v ⬝ᵥ Q *ᵥ v := by
    rw [mul_sub, mul_one, trace_sub]
    congr 1
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.mul_apply, vecMulVec_apply]
    rw [show v ⬝ᵥ Q *ᵥ v = ∑ i, v i * ∑ j, Q i j * v j from rfl]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h3] at h2
  linarith

/-- The shifted pencil is positive definite. -/
theorem pencil_posDef (G : Matrix n n ℝ) (hG : G.IsHermitian) {a : ℝ} (ha : 0 < a) :
    (G * G + a ^ 2 • (1 : Matrix n n ℝ)).PosDef := by
  have h1 : (G * G).PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self G
    rwa [hG.eq] at h
  have h2 : (a ^ 2 • (1 : Matrix n n ℝ)).PosDef :=
    (Matrix.PosDef.one).smul (by positivity)
  have h3 : (a ^ 2 • (1 : Matrix n n ℝ) + G * G).PosDef := h2.add_posSemidef h1
  rwa [add_comm] at h3

/-- **GRH.4: the scale-matched soft-source lower bound.**  A Hermitian pencil with
`‖H‖ ≤ ca` that is singular somewhere in `[0,1]` accumulates at least `arctan(c)/c` of
integrated soft-source mass, independently of the spectral floor and the dimension. -/
theorem soft_source_bound (A H : Matrix n n ℝ) (hA : A.IsHermitian) (hH : H.IsHermitian)
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hHb : ∀ w : n → ℝ, (H *ᵥ w) ⬝ᵥ (H *ᵥ w) ≤ (c * a) ^ 2 * (w ⬝ᵥ w))
    {s₀ : ℝ} (h0 : 0 ≤ s₀) (h1 : s₀ ≤ 1) (hsing : (A + s₀ • H).det = 0) :
    Real.arctan c / c ≤ ∫ s in (0:ℝ)..1,
      (a ^ 2 • ((A + s • H) * (A + s • H) + a ^ 2 • (1 : Matrix n n ℝ))⁻¹).trace := by
  classical
  set G : ℝ → Matrix n n ℝ := fun s => A + s • H with hGdef
  have hGH : ∀ s, (G s).IsHermitian := by
    intro s
    change (A + s • H)ᴴ = A + s • H
    rw [conjTranspose_add, hA.eq, conjTranspose_smul, hH.eq, star_trivial]
  have hGT : ∀ s, (G s)ᵀ = G s := by
    intro s
    have h := (hGH s).eq
    rwa [conjTranspose_eq_transpose_of_trivial] at h
  have hMpos : ∀ s, ((G s) * (G s) + a ^ 2 • (1 : Matrix n n ℝ)).PosDef :=
    fun s => pencil_posDef (G s) (hGH s) ha
  -- a unit kernel vector at the singular location
  obtain ⟨v₀, hv₀ne, hv₀⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hsing
  have hv₀pos : 0 < v₀ ⬝ᵥ v₀ := dot_self_pos hv₀ne
  set v : n → ℝ := (Real.sqrt (v₀ ⬝ᵥ v₀))⁻¹ • v₀ with hvdef
  have hvunit : v ⬝ᵥ v = 1 := by
    rw [hvdef, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc]
    have hs := Real.sq_sqrt hv₀pos.le
    have hsne : Real.sqrt (v₀ ⬝ᵥ v₀) ≠ 0 := (Real.sqrt_pos.mpr hv₀pos).ne'
    field_simp
    nlinarith [hs]
  have hkerv : (G s₀) *ᵥ v = 0 := by
    rw [hvdef, mulVec_smul, hv₀, smul_zero]
  have hGsv : ∀ s, (G s) *ᵥ v = (s - s₀) • (H *ᵥ v) := by
    intro s
    have h := hkerv
    rw [hGdef] at h ⊢
    rw [add_mulVec, Matrix.smul_mulVec] at h ⊢
    have hA0 : A *ᵥ v = -(s₀ • (H *ᵥ v)) := eq_neg_of_add_eq_zero_left h
    rw [hA0, sub_smul]
    abel
  -- the pointwise trace bound
  have hpoint : ∀ s : ℝ, (1 + (c * (s - s₀)) ^ 2)⁻¹
      ≤ (a ^ 2 • ((G s) * (G s) + a ^ 2 • (1 : Matrix n n ℝ))⁻¹).trace := by
    intro s
    set M : Matrix n n ℝ := (G s) * (G s) + a ^ 2 • (1 : Matrix n n ℝ) with hMdef
    have hMps := hMpos s
    have hMinvPD : (M⁻¹).PosDef := (Matrix.posDef_inv_iff).mpr hMps
    have hquad : v ⬝ᵥ M *ᵥ v
        = (s - s₀) ^ 2 * ((H *ᵥ v) ⬝ᵥ (H *ᵥ v)) + a ^ 2 := by
      rw [hMdef, add_mulVec, dotProduct_add]
      congr 1
      · have hswap2 : v ⬝ᵥ ((G s) * (G s)) *ᵥ v
            = ((G s) *ᵥ v) ⬝ᵥ ((G s) *ᵥ v) := by
          rw [← mulVec_mulVec]
          have h := dot_swap (G s) v ((G s) *ᵥ v)
          rw [hGT s] at h
          exact h.symm
        rw [hswap2, hGsv, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
          ← mul_assoc, ← sq]
      · rw [Matrix.smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul, hvunit,
          mul_one]
    have hHv := hHb v
    rw [hvunit, mul_one] at hHv
    have hquadle : v ⬝ᵥ M *ᵥ v ≤ a ^ 2 * (1 + c ^ 2 * (s - s₀) ^ 2) := by
      rw [hquad]
      nlinarith [sq_nonneg (s - s₀)]
    have hquadpos : 0 < v ⬝ᵥ M *ᵥ v := by
      have hvne : v ≠ 0 := by
        intro hv0
        rw [hv0] at hvunit
        simp [dotProduct] at hvunit
      have h := hMps.dotProduct_mulVec_pos (x := v) hvne
      simpa [star_trivial] using h
    have hinv := dot_inv_lower hMps hvunit
    calc (1 + (c * (s - s₀)) ^ 2)⁻¹
        = a ^ 2 * (a ^ 2 * (1 + c ^ 2 * (s - s₀) ^ 2))⁻¹ := by
          rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
          congr 2
          ring
      _ ≤ a ^ 2 * (v ⬝ᵥ M *ᵥ v)⁻¹ := by
          have hle : (a ^ 2 * (1 + c ^ 2 * (s - s₀) ^ 2))⁻¹ ≤ (v ⬝ᵥ M *ᵥ v)⁻¹ := by
            rw [← one_div, ← one_div]
            exact one_div_le_one_div_of_le hquadpos hquadle
          exact mul_le_mul_of_nonneg_left hle (by positivity)
      _ ≤ a ^ 2 * (v ⬝ᵥ M⁻¹ *ᵥ v) :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = v ⬝ᵥ (a ^ 2 • M⁻¹) *ᵥ v := by
          rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
      _ ≤ (a ^ 2 • M⁻¹).trace :=
          trace_ge_dot (hMinvPD.posSemidef.smul (by positivity)) hvunit
  -- continuity of the trace integrand
  have hcG : Continuous G := by
    rw [hGdef]
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hcM : Continuous fun s : ℝ =>
      (G s) * (G s) + a ^ 2 • (1 : Matrix n n ℝ) :=
    (hcG.matrix_mul hcG).add continuous_const
  have hdet0 : ∀ s, ((G s) * (G s) + a ^ 2 • (1 : Matrix n n ℝ)).det ≠ 0 :=
    fun s => (hMpos s).det_pos.ne'
  have hcinv : Continuous fun s : ℝ =>
      ((G s) * (G s) + a ^ 2 • (1 : Matrix n n ℝ))⁻¹ := by
    have hfun : (fun s : ℝ => ((G s) * (G s) + a ^ 2 • (1 : Matrix n n ℝ))⁻¹)
        = fun s => (((G s) * (G s) + a ^ 2 • (1 : Matrix n n ℝ)).det)⁻¹
          • ((G s) * (G s) + a ^ 2 • (1 : Matrix n n ℝ)).adjugate := by
      funext s
      rw [Matrix.inv_def, Ring.inverse_eq_inv]
    rw [hfun]
    exact ((hcM.matrix_det).inv₀ hdet0).smul (hcM.matrix_adjugate)
  have hcont : Continuous fun s : ℝ =>
      (a ^ 2 • ((G s) * (G s) + a ^ 2 • (1 : Matrix n n ℝ))⁻¹).trace :=
    (hcinv.const_smul (a ^ 2)).matrix_trace
  have hker_cont : Continuous fun s : ℝ => (1 + (c * (s - s₀)) ^ 2)⁻¹ := by
    refine Continuous.inv₀ ?_ fun s => by positivity
    exact continuous_const.add ((continuous_const.mul
      (continuous_id.sub continuous_const)).pow 2)
  have hmono := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (by norm_num : (0:ℝ) ≤ 1)
    (hker_cont.intervalIntegrable 0 1) (hcont.intervalIntegrable 0 1)
    fun s _ => hpoint s
  calc Real.arctan c / c
      ≤ (Real.arctan (c * (1 - s₀)) - Real.arctan (c * (0 - s₀))) / c :=
        cauchy_integral_lower hc h0 h1
    _ = ∫ s in (0:ℝ)..1, (1 + (c * (s - s₀)) ^ 2)⁻¹ :=
        (integral_cauchy_kernel c s₀ hc).symm
    _ ≤ _ := hmono

end SoftSource
end NCG
