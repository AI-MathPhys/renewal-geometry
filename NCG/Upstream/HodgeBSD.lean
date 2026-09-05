/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Hodge cycle observability and the BSD jet-nullity dictionary
  (`thm:Hodge-master`, `thm:BSD-jet-master`, flagship)

* `hodge_cycle_observability` — for the cycle-class matrix
  `𝒵 : ℂ^m → H` on the finite-dimensional Hodge sector, the chain
  of equivalences: the classes span `H` ⟺ `𝒵` is surjective ⟺ the
  Gram block `𝒵𝒵ᴴ` is positive definite ⟺ `𝒵𝒵ᴴ ⪰ c·1` for some
  `c > 0` (spectral-gap form, via the smallest eigenvalue);
* `jetMatrix` / `jet_kernel_characterization` / `jet_nullity` /
  `jet_nullity_degenerate` — the truncated-multiplication jet
  matrix of an analytic germ of vanishing order `r` has kernel
  `{c : c_j = 0 for j < m - r}` and nullity `min r m`;
* `gram_kernel_eq` — `ker (MᴴM) = ker M`, so the Hermitian jet
  block `𝕁 = MᴴM` has the same nullity.

The Hodge conjecture content (that the algebraic classes span) and
the BSD moment identification are the declared external inputs;
these results are the exact linear-algebra dictionary used by the
master statements.
-/

namespace NCG

open Matrix Unitary

open scoped ComplexOrder

/-- `thm:Hodge-master` (dictionary): span ⟺ surjectivity ⟺ Gram
positive-definiteness ⟺ uniform spectral gap. -/
theorem hodge_cycle_observability {d m : Type*} [Finite d]
    [Fintype m] [DecidableEq d] (A : Matrix d m ℂ) :
    (Submodule.span ℂ (Set.range A.col) = ⊤
        ↔ Function.Surjective A.mulVec)
      ∧ (Function.Surjective A.mulVec ↔ (A * Aᴴ).PosDef)
      ∧ ((A * Aᴴ).PosDef
        ↔ ∃ c : ℝ, 0 < c ∧ (A * Aᴴ - (c : ℂ) • 1).PosSemidef) := by
  haveI := Fintype.ofFinite d
  refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · -- span of the columns = range of `mulVec`
    rw [← Matrix.range_mulVecLin, LinearMap.range_eq_top]
    constructor
    · intro h z
      obtain ⟨w, hw⟩ := h z
      exact ⟨w, by rwa [Matrix.mulVecLin_apply] at hw⟩
    · intro h z
      obtain ⟨w, hw⟩ := h z
      exact ⟨w, by rwa [Matrix.mulVecLin_apply]⟩
  · -- surjective ⇒ positive definite Gram block
    intro hsurj
    refine Matrix.PosDef.of_dotProduct_mulVec_pos
      (Matrix.isHermitian_mul_conjTranspose_self A) ?_
    intro x hx
    have hform : star x ⬝ᵥ ((A * Aᴴ) *ᵥ x)
        = star (Aᴴ *ᵥ x) ⬝ᵥ (Aᴴ *ᵥ x) := by
      rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose,
        ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    rw [hform, Matrix.dotProduct_star_self_pos_iff]
    intro hker
    have hrow : star x ᵥ* A = 0 := by
      have hstar := congrArg star hker
      rwa [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose,
        star_zero] at hstar
    obtain ⟨w, hw⟩ := hsurj x
    have hself : star x ⬝ᵥ x = 0 := by
      nth_rewrite 2 [← hw]
      rw [Matrix.dotProduct_mulVec, hrow, zero_dotProduct]
    exact hx (dotProduct_star_self_eq_zero.mp hself)
  · -- positive definite ⇒ surjective, via the inverse Gram block
    intro hPD z
    have hdet : IsUnit (A * Aᴴ).det :=
      isUnit_iff_ne_zero.mpr hPD.det_pos.ne'
    refine ⟨Aᴴ *ᵥ ((A * Aᴴ)⁻¹ *ᵥ z), ?_⟩
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  · -- positive definite ⇒ spectral gap at the smallest eigenvalue
    intro hPD
    rcases isEmpty_or_nonempty d with hd | hd
    · refine ⟨1, one_pos,
        Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_⟩
      · ext i j
        exact isEmptyElim i
      · intro x
        simp [dotProduct]
    · set lam := hPD.1.eigenvalues with hlam
      set c : ℝ := Finset.univ.inf' Finset.univ_nonempty lam
        with hcdef
      obtain ⟨i0, -, hi0⟩ :=
        Finset.exists_mem_eq_inf' Finset.univ_nonempty lam
      have hc : 0 < c := by
        rw [hcdef, hi0]
        exact hPD.eigenvalues_pos i0
      refine ⟨c, hc, ?_⟩
      have hkey : A * Aᴴ - (c : ℂ) • 1
          = conjStarAlgAut ℂ _ hPD.1.eigenvectorUnitary
              (Matrix.diagonal (RCLike.ofReal ∘ lam)
                - (c : ℂ) • 1) := by
        rw [map_sub, map_smul, map_one, ← hPD.1.spectral_theorem]
      rw [hkey]
      have hdiag : Matrix.diagonal (RCLike.ofReal ∘ lam)
          - (c : ℂ) • (1 : Matrix d d ℂ)
          = Matrix.diagonal (fun i => ((lam i - c : ℝ) : ℂ)) := by
        ext i j
        by_cases hij : i = j
        · subst hij
          simp [Matrix.diagonal_apply_eq, Matrix.one_apply_eq,
            Complex.ofReal_sub]
        · simp [Matrix.diagonal_apply_ne _ hij,
            Matrix.one_apply_ne hij]
      rw [hdiag, conjStarAlgAut_apply,
        Matrix.star_eq_conjTranspose]
      exact (Matrix.posSemidef_diagonal_iff.mpr fun i =>
        Complex.zero_le_real.mpr (sub_nonneg.mpr
          (Finset.inf'_le _ (Finset.mem_univ i)))
        ).mul_mul_conjTranspose_same _
  · -- spectral gap ⇒ positive definite
    rintro ⟨c, hc, hPSD⟩
    refine Matrix.PosDef.of_dotProduct_mulVec_pos
      (Matrix.isHermitian_mul_conjTranspose_self A) ?_
    intro x hx
    have h1 := hPSD.dotProduct_mulVec_nonneg x
    have hsub : (A * Aᴴ - (c : ℂ) • 1) *ᵥ x
        = (A * Aᴴ) *ᵥ x - (c : ℂ) • x := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec]
    rw [hsub, dotProduct_sub, dotProduct_smul,
      smul_eq_mul] at h1
    have hxpos : 0 < star x ⬝ᵥ x :=
      dotProduct_star_self_pos_iff.mpr hx
    rw [RCLike.nonneg_iff] at h1
    rw [RCLike.pos_iff] at hxpos ⊢
    obtain ⟨hS, hSim⟩ := hxpos
    obtain ⟨hre, him⟩ := h1
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      RCLike.re_to_complex,
      RCLike.im_to_complex] at hre him hS hSim ⊢
    rw [hSim] at him
    constructor
    · nlinarith
    · linarith

/-- The order-`m` jet (truncated multiplication) matrix of the
germ with Taylor coefficients `F`. -/
def jetMatrix (F : ℕ → ℂ) (m : ℕ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun k j =>
    if (j : ℕ) ≤ (k : ℕ) then F ((k : ℕ) - (j : ℕ)) else 0

/-- `thm:BSD-jet-master` (kernel): for a germ of exact vanishing
order `r ≤ m`, the jet kernel is the coordinate slab
`{c : c_j = 0 for j < m - r}`. -/
theorem jet_kernel_characterization (F : ℕ → ℂ) {m r : ℕ}
    (hrm : r ≤ m) (hlow : ∀ i, i < r → F i = 0) (hne : F r ≠ 0)
    (c : Fin m → ℂ) :
    (jetMatrix F m) *ᵥ c = 0
      ↔ ∀ j : Fin m, (j : ℕ) < m - r → c j = 0 := by
  constructor
  · intro h
    have key : ∀ N : ℕ, ∀ j : Fin m, (j : ℕ) = N
        → (j : ℕ) < m - r → c j = 0 := by
      intro N
      induction N using Nat.strong_induction_on with
      | _ N IH =>
        intro j hjN hj
        have hk : (j : ℕ) + r < m := by omega
        have hrow : (∑ i : Fin m,
            jetMatrix F m ⟨(j : ℕ) + r, hk⟩ i * c i) = 0 := by
          have hc := congrFun h ⟨(j : ℕ) + r, hk⟩
          simpa [Matrix.mulVec, dotProduct] using hc
        have hsingle : (∑ i : Fin m,
            jetMatrix F m ⟨(j : ℕ) + r, hk⟩ i * c i)
            = jetMatrix F m ⟨(j : ℕ) + r, hk⟩ j * c j := by
          apply Finset.sum_eq_single
          · intro i _ hij
            have hine : (i : ℕ) ≠ (j : ℕ) :=
              fun hh => hij (Fin.ext hh)
            rcases Nat.lt_or_ge (i : ℕ) (j : ℕ) with hlt | hge
            · rw [IH (i : ℕ) (by omega) i rfl (by omega),
                mul_zero]
            · have hgt : (j : ℕ) < (i : ℕ) := by omega
              simp only [jetMatrix, Matrix.of_apply]
              by_cases hle : (i : ℕ) ≤ (j : ℕ) + r
              · rw [if_pos hle,
                  hlow ((j : ℕ) + r - (i : ℕ)) (by omega),
                  zero_mul]
              · rw [if_neg hle, zero_mul]
          · intro hmem
            exact absurd (Finset.mem_univ j) hmem
        rw [hsingle] at hrow
        have hFr : jetMatrix F m ⟨(j : ℕ) + r, hk⟩ j = F r := by
          simp only [jetMatrix, Matrix.of_apply]
          rw [if_pos (by omega : (j : ℕ) ≤ (j : ℕ) + r)]
          congr 1
          omega
        rw [hFr] at hrow
        exact (mul_eq_zero.mp hrow).resolve_left hne
    exact fun j hj => key (j : ℕ) j rfl hj
  · intro hc
    funext k
    have hklt : (k : ℕ) < m := k.isLt
    have hsum : (∑ i : Fin m, jetMatrix F m k i * c i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hilt : (i : ℕ) < m := i.isLt
      by_cases hle : (i : ℕ) ≤ (k : ℕ)
      · by_cases hiz : (i : ℕ) < m - r
        · rw [hc i hiz, mul_zero]
        · simp only [jetMatrix, Matrix.of_apply]
          rw [if_pos hle,
            hlow ((k : ℕ) - (i : ℕ)) (by omega), zero_mul]
      · simp only [jetMatrix, Matrix.of_apply]
        rw [if_neg hle, zero_mul]
    simpa [Matrix.mulVec, dotProduct] using hsum

/-- `thm:BSD-jet-master` (nullity): the jet matrix of a germ of
exact order `r ≤ m` has nullity `min r m = r`. -/
theorem jet_nullity (F : ℕ → ℂ) {m r : ℕ}
    (hrm : r ≤ m) (hlow : ∀ i, i < r → F i = 0) (hne : F r ≠ 0) :
    Module.finrank ℂ (LinearMap.ker (jetMatrix F m).mulVecLin)
      = min r m := by
  have hchar : ∀ cv : Fin m → ℂ,
      cv ∈ LinearMap.ker (jetMatrix F m).mulVecLin
        ↔ ∀ j : Fin m, (j : ℕ) < m - r → cv j = 0 := by
    intro cv
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact jet_kernel_characterization F hrm hlow hne cv
  let e : (LinearMap.ker (jetMatrix F m).mulVecLin)
      ≃ₗ[ℂ] (Fin r → ℂ) :=
    { toFun := fun a i => a.val ⟨m - r + (i : ℕ), by
        have := i.isLt
        omega⟩
      map_add' := fun a b => rfl
      map_smul' := fun t a => rfl
      invFun := fun v => ⟨fun j =>
          if hjr : (j : ℕ) < m - r then 0
          else v ⟨(j : ℕ) - (m - r), by
            have := j.isLt
            omega⟩, by
        refine (hchar _).mpr ?_
        intro j hj
        rw [dif_pos hj]⟩
      left_inv := fun a => by
        apply Subtype.ext
        funext j
        dsimp only
        by_cases hjr : (j : ℕ) < m - r
        · rw [dif_pos hjr]
          exact ((hchar a.val).mp a.property j hjr).symm
        · rw [dif_neg hjr]
          apply congrArg
          apply Fin.ext
          change m - r + ((j : ℕ) - (m - r)) = (j : ℕ)
          omega
      right_inv := fun v => by
        funext i
        dsimp only
        rw [dif_neg (by omega : ¬ (m - r + (i : ℕ) < m - r))]
        congr 1
        apply Fin.ext
        change (m - r + (i : ℕ)) - (m - r) = (i : ℕ)
        omega }
  rw [LinearEquiv.finrank_eq e, Module.finrank_fin_fun]
  omega

/-- `thm:BSD-jet-master` (degenerate window): if the vanishing
order reaches the window size, the jet matrix is zero and the
nullity saturates at `min r m = m`. -/
theorem jet_nullity_degenerate (F : ℕ → ℂ) {m r : ℕ}
    (hmr : m ≤ r) (hlow : ∀ i, i < r → F i = 0) :
    jetMatrix F m = 0
      ∧ Module.finrank ℂ
          (LinearMap.ker (jetMatrix F m).mulVecLin) = min r m := by
  have hzero : jetMatrix F m = 0 := by
    ext k i
    simp only [jetMatrix, Matrix.of_apply, Matrix.zero_apply]
    by_cases hle : (i : ℕ) ≤ (k : ℕ)
    · rw [if_pos hle]
      exact hlow _ (by have := k.isLt; omega)
    · rw [if_neg hle]
  refine ⟨hzero, ?_⟩
  rw [hzero, Matrix.mulVecLin_zero, LinearMap.ker_zero,
    finrank_top, Module.finrank_fin_fun]
  omega

/-- `thm:BSD-jet-master` (Hermitian block): `ker (MᴴM) = ker M`,
so the Hermitian jet block `𝕁 = MᴴM` has the same nullity as the
jet matrix. -/
theorem gram_kernel_eq {p q : Type*} [Fintype p] [Fintype q]
    (M : Matrix p q ℂ) (x : q → ℂ) :
    (Mᴴ * M) *ᵥ x = 0 ↔ M *ᵥ x = 0 := by
  constructor
  · intro h
    have hdot : star (M *ᵥ x) ⬝ᵥ (M *ᵥ x) = 0 := by
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
        Matrix.mulVec_mulVec, h, dotProduct_zero]
    exact dotProduct_star_self_eq_zero.mp hdot
  · intro h
    rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

end NCG
