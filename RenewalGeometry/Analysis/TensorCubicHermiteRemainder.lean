/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.TwoPointHermiteInterpolation
import RenewalGeometry.DiscreteAnalysis.CubicHermiteStability

/-!
# Exact-reference remainder of the tensor-product cubic Hermite interpolant
  (`thm:supp-gowdy-full-curvature`: "the exact-reference cubic Hermite remainder is
  `O(h^{4-k})` through derivative order `k = 2`"; emergent-spacetime supplement)

For the cubic Hermite basis `H₀, H₁, G₀, G₁` of `CubicHermiteStability` and a smooth function
`φ : ℝ × ℝ → ℝ`, let `Iφ` be the tensor-product cubic Hermite interpolant on the cell
`[x₀, x₀+h] × [y₀, y₀+h]` built from the exact corner records
`(φ, ∂ₓφ, ∂_yφ, ∂ₓ∂_yφ)` (`CubicHermite.interp`).  With partial derivatives
`dP F z = DF(z)(1,0)`, `dQ F z = DF(z)(0,1)`:

* `herm`, `herm_zero_eq_polyCurve`, `iteratedDeriv_herm`, `abs_iteratedDeriv_sub_herm_le`
  (**one-dimensional remainder on the unit interval**): the basis form
  `g(0)H₀ + g(1)H₁ + g'(0)G₀ + g'(1)G₁` is the two-point Hermite cubic of
  `TwoPointHermiteInterpolation`, hence `|g^{(j)} - (Hg)^{(j)}| ≤ (1 + hermiteConst 1 j) M` on
  `[0,1]` for `j ≤ 2`, `M ≥ sup |g⁗|`.
* `dP`, `dQ`, the section lemmas `iteratedDeriv_section_p/q` and the **Schwarz commutation**
  `dQ_dP`, `iterate_dP_iterate_dQ_comm` for smooth functions.
* `unit_remainder` (**unit cell**): if all partials `dP^a dQ^b F` with `4 ≤ a + b ≤ 6` are
  bounded by `M` on `[0,1]²`, then for `i + j ≤ 2`
  `|dP^i dQ^j F - ∂_p^i ∂_q^j (IF)| ≤ hermRemConst · M` on `[0,1]²`, where `∂_p^i ∂_q^j (IF)` is
  the tensor of the differentiated basis (`CubicHermite.hasDerivAt_interp_*`).  The proof splits
  `F - IF = (F - I_q F) + (I_q F - I_p I_q F)` and applies the one-dimensional remainder to
  sections, so no stability estimate of the interpolant is needed.
* `cell_remainder` (**physical cell of size `h ≤ 1`**): with records
  `f = φ, u = ∂ₓφ, v = ∂_yφ, w = ∂ₓ∂_yφ` at the corners and
  `M ≥ |dP^a dQ^b φ|` (`4 ≤ a + b ≤ 6`) on the cell,
  `|dP^i dQ^j φ(x₀+hp, y₀+hq) - h^{-(i+j)} ∂_p^i∂_q^j interp h f u v w (p,q)| ≤ C M h^{4-i-j}`
  for `i + j ≤ 2`, `(p,q) ∈ [0,1]²`: the exact-reference remainder `O(h^{4-k})`, `k ≤ 2`.
-/

open Set
open scoped BigOperators ContDiff

namespace RenewalGeometry.CubicHermiteRemainder

open CubicHermite TwoPointHermite

noncomputable section

/-! ### The one-dimensional unit Hermite cubic -/

/-- The `j`-th derivative of the value basis (`j = 0, 1, 2`; zero beyond, unused). -/
def BH : ℕ → Fin 2 → ℝ → ℝ
  | 0 => basisH
  | 1 => basisHD
  | 2 => basisHDD
  | _ => fun _ _ => 0

/-- The `j`-th derivative of the slope basis. -/
def BG : ℕ → Fin 2 → ℝ → ℝ
  | 0 => basisG
  | 1 => basisGD
  | 2 => basisGDD
  | _ => fun _ _ => 0

/-- The `j`-th derivative of the unit Hermite cubic of `g`:
`g(0)H₀⁽ʲ⁾ + g(1)H₁⁽ʲ⁾ + g'(0)G₀⁽ʲ⁾ + g'(1)G₁⁽ʲ⁾`. -/
def herm (j : ℕ) (g : ℝ → ℝ) (q : ℝ) : ℝ :=
  g 0 * BH j 0 q + g 1 * BH j 1 q + deriv g 0 * BG j 0 q + deriv g 1 * BG j 1 q

theorem hasDerivAt_herm (j : ℕ) (hj : j ≤ 1) (g : ℝ → ℝ) (q : ℝ) :
    HasDerivAt (herm j g) (herm (j + 1) g q) q := by
  interval_cases j
  · have hH := fun a => hasDerivAt_cubic (hCoef a) q
    have hG := fun a => hasDerivAt_cubic (gCoef a) q
    have := ((((hH 0).const_mul (g 0)).add ((hH 1).const_mul (g 1))).add
      ((hG 0).const_mul (deriv g 0))).add ((hG 1).const_mul (deriv g 1))
    exact this
  · have hH := fun a => hasDerivAt_cubicD (hCoef a) q
    have hG := fun a => hasDerivAt_cubicD (gCoef a) q
    have := ((((hH 0).const_mul (g 0)).add ((hH 1).const_mul (g 1))).add
      ((hG 0).const_mul (deriv g 0))).add ((hG 1).const_mul (deriv g 1))
    exact this

theorem iteratedDeriv_herm (g : ℝ → ℝ) {j : ℕ} (hj : j ≤ 2) :
    iteratedDeriv j (herm 0 g) = herm j g := by
  induction j with
  | zero => rw [iteratedDeriv_zero]
  | succ j ih =>
    rw [iteratedDeriv_succ, ih (by omega)]
    funext q
    exact (hasDerivAt_herm j (by omega) g q).deriv

/-- The coefficient vector of the unit Hermite cubic in the monomial basis. -/
def hermCoeffs (g : ℝ → ℝ) : Fin 4 → ℝ :=
  ![g 0, deriv g 0, -3 * g 0 + 3 * g 1 - 2 * deriv g 0 - deriv g 1,
    2 * g 0 - 2 * g 1 + deriv g 0 + deriv g 1]

theorem polyCurve_hermCoeffs (g : ℝ → ℝ) : polyCurve (hermCoeffs g) = herm 0 g := by
  funext q
  simp only [polyCurve, Fin.sum_univ_four, hermCoeffs, herm, BH, BG]
  simp [basisH, basisG, cubic, hCoef, gCoef]
  ring

/-- The basis form is the two-point Hermite cubic of `TwoPointHermiteInterpolation` on `[0,1]`. -/
theorem herm_zero_eq_polyCurve (g : ℝ → ℝ) :
    herm 0 g = polyCurve (hermiteInterpCoeffs 1 g 1) := by
  rw [← polyCurve_hermCoeffs]
  congr 1
  apply eq_of_jets_eq (k := 1)
  funext r
  have hP : jets (hermiteInterpCoeffs 1 g 1) r = iteratedDeriv r.2 g ((r.1 : ℕ) : ℝ) := by
    have := iteratedDeriv_hermiteInterp (k := 1) g (one_ne_zero) r.1 r.2
    have e : ((r.1 : ℕ) : ℝ) * 1 = ((r.1 : ℕ) : ℝ) := mul_one _
    rw [e, iteratedDeriv_polyCurve] at this
    exact this
  rw [hP]
  obtain ⟨e, i⟩ := r
  fin_cases e <;> fin_cases i <;>
    simp [jets, polyCurveDeriv, Fin.sum_univ_four, hermCoeffs, iteratedDeriv_one] <;> ring

/-- **One-dimensional cubic Hermite remainder on `[0,1]`**: for `g ∈ C⁴` with `|g⁗| ≤ M` on
`[0,1]` and `j ≤ 2`, `|g⁽ʲ⁾(t) - (Hg)⁽ʲ⁾(t)| ≤ (1 + hermiteConst 1 j) M`. -/
theorem abs_iteratedDeriv_sub_herm_le (g : ℝ → ℝ) (hg : ContDiff ℝ 4 g) {M : ℝ}
    (hM : ∀ t ∈ Icc (0 : ℝ) 1, |iteratedDeriv 4 g t| ≤ M) {j : ℕ} (hj : j ≤ 2) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    |iteratedDeriv j g t - herm j g t| ≤ (1 + hermiteConst 1 j) * M := by
  have h := norm_iteratedDeriv_sub_hermiteInterp_le (k := 1) g (hg.of_le (by norm_num))
    (τ := 1) (M := M) one_pos (fun s hs => by rw [Real.norm_eq_abs]; exact hM s hs)
    (j := j) (by omega) ht
  rw [← herm_zero_eq_polyCurve, iteratedDeriv_herm g hj, one_pow, mul_one,
    Real.norm_eq_abs] at h
  exact h

/-! ### Basis derivative bounds -/

theorem abs_BH_le {j : ℕ} (hj : j ≤ 2) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (a : Fin 2) :
    |BH j a q| ≤ 6 := by
  interval_cases j
  · exact (abs_basisH_le hq a).trans (by norm_num)
  · exact (abs_basisHD_le hq a).trans (by norm_num)
  · exact abs_basisHDD_le hq a

theorem abs_BG_le {j : ℕ} (hj : j ≤ 2) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (a : Fin 2) :
    |BG j a q| ≤ 6 := by
  interval_cases j
  · exact (abs_basisG_le hq a).trans (by norm_num)
  · exact (abs_basisGD_le hq a).trans (by norm_num)
  · exact (abs_basisGDD_le hq a).trans (by norm_num)

/-! ### Partial derivatives on `ℝ × ℝ` -/

/-- The partial derivative `∂_p F (z) = DF(z)(1, 0)`. -/
def dP (F : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun z => fderiv ℝ F z (1, 0)

/-- The partial derivative `∂_q F (z) = DF(z)(0, 1)`. -/
def dQ (F : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun z => fderiv ℝ F z (0, 1)

theorem contDiff_dP {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (dP F) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem contDiff_dQ {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (dQ F) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem contDiff_iterate_dP {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (a : ℕ) :
    ContDiff ℝ ∞ (dP^[a] F) := by
  induction a with
  | zero => exact hF
  | succ a ih => rw [Function.iterate_succ_apply']; exact contDiff_dP ih

theorem contDiff_iterate_dQ {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (b : ℕ) :
    ContDiff ℝ ∞ (dQ^[b] F) := by
  induction b with
  | zero => exact hF
  | succ b ih => rw [Function.iterate_succ_apply']; exact contDiff_dQ ih

theorem hasDerivAt_section_p {F : ℝ × ℝ → ℝ} (hF : Differentiable ℝ F) (p q : ℝ) :
    HasDerivAt (fun p => F (p, q)) (dP F (p, q)) p := by
  have h1 : HasDerivAt (fun p : ℝ => (p, q)) ((1 : ℝ), (0 : ℝ)) p :=
    (hasDerivAt_id p).prodMk (hasDerivAt_const p q)
  exact (hF (p, q)).hasFDerivAt.comp_hasDerivAt p h1

theorem hasDerivAt_section_q {F : ℝ × ℝ → ℝ} (hF : Differentiable ℝ F) (p q : ℝ) :
    HasDerivAt (fun q => F (p, q)) (dQ F (p, q)) q := by
  have h1 : HasDerivAt (fun q : ℝ => (p, q)) ((0 : ℝ), (1 : ℝ)) q :=
    (hasDerivAt_const q p).prodMk (hasDerivAt_id q)
  exact (hF (p, q)).hasFDerivAt.comp_hasDerivAt q h1

theorem iteratedDeriv_section_p {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (a : ℕ) (q : ℝ) :
    iteratedDeriv a (fun p => F (p, q)) = fun p => (dP^[a] F) (p, q) := by
  induction a with
  | zero => rw [iteratedDeriv_zero]; rfl
  | succ a ih =>
    rw [iteratedDeriv_succ, ih]
    funext p
    rw [Function.iterate_succ_apply']
    exact (hasDerivAt_section_p ((contDiff_iterate_dP hF a).differentiable (by simp)) p q).deriv

theorem iteratedDeriv_section_q {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (b : ℕ) (p : ℝ) :
    iteratedDeriv b (fun q => F (p, q)) = fun q => (dQ^[b] F) (p, q) := by
  induction b with
  | zero => rw [iteratedDeriv_zero]; rfl
  | succ b ih =>
    rw [iteratedDeriv_succ, ih]
    funext q
    rw [Function.iterate_succ_apply']
    exact (hasDerivAt_section_q ((contDiff_iterate_dQ hF b).differentiable (by simp)) p q).deriv

theorem deriv_section_p {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (p q : ℝ) :
    deriv (fun p => F (p, q)) p = dP F (p, q) :=
  (hasDerivAt_section_p (hF.differentiable (by simp)) p q).deriv

theorem deriv_section_q {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (p q : ℝ) :
    deriv (fun q => F (p, q)) q = dQ F (p, q) :=
  (hasDerivAt_section_q (hF.differentiable (by simp)) p q).deriv

theorem contDiff_section_p {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (q : ℝ) :
    ContDiff ℝ ∞ (fun p => F (p, q)) :=
  hF.comp (contDiff_id.prodMk contDiff_const)

theorem contDiff_section_q {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (p : ℝ) :
    ContDiff ℝ ∞ (fun q => F (p, q)) :=
  hF.comp (contDiff_const.prodMk contDiff_id)

/-- **Schwarz**: `∂_q ∂_p F = ∂_p ∂_q F` for smooth `F`. -/
theorem dQ_dP {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) : dQ (dP F) = dP (dQ F) := by
  funext z
  have hs := (hF.contDiffAt (x := z)).isSymmSndFDerivAt
    (by rw [minSmoothness_of_isRCLikeNormedField]; norm_cast)
  have hd : DifferentiableAt ℝ (fderiv ℝ F) z :=
    ((hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) z
  show fderiv ℝ (fun y => fderiv ℝ F y (1, 0)) z (0, 1) =
    fderiv ℝ (fun y => fderiv ℝ F y (0, 1)) z (1, 0)
  rw [fderiv_clm_apply hd (differentiableAt_const _), fderiv_clm_apply hd (differentiableAt_const _)]
  simpa using hs (0, 1) (1, 0)

theorem dQ_iterate_dP {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (a : ℕ) :
    dQ (dP^[a] F) = dP^[a] (dQ F) := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', dQ_dP
      (contDiff_iterate_dP hF a), ih]

theorem iterate_dQ_iterate_dP {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (a b : ℕ) :
    dQ^[b] (dP^[a] F) = dP^[a] (dQ^[b] F) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      dQ_iterate_dP (contDiff_iterate_dQ hF b)]

/-! ### The unit cell -/

/-- Corner value records `F(a, b)` on the unit cell. -/
def fR (F : ℝ × ℝ → ℝ) : Fin 2 → Fin 2 → ℝ := fun a b => F (((a : ℕ) : ℝ), ((b : ℕ) : ℝ))
/-- Corner `p`-derivative records. -/
def uR (F : ℝ × ℝ → ℝ) : Fin 2 → Fin 2 → ℝ := fun a b => dP F (((a : ℕ) : ℝ), ((b : ℕ) : ℝ))
/-- Corner `q`-derivative records. -/
def vR (F : ℝ × ℝ → ℝ) : Fin 2 → Fin 2 → ℝ := fun a b => dQ F (((a : ℕ) : ℝ), ((b : ℕ) : ℝ))
/-- Corner mixed-derivative records. -/
def wR (F : ℝ × ℝ → ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun a b => dP (dQ F) (((a : ℕ) : ℝ), ((b : ℕ) : ℝ))

/-- The remainder constant `25 (1 + Σ_{k ≤ 2} hermiteConst 1 k)`. -/
def hermRemConst : ℝ := 25 * (1 + hermiteConst 1 0 + hermiteConst 1 1 + hermiteConst 1 2)

theorem one_add_hermiteConst_le {k : ℕ} (hk : k ≤ 2) :
    1 + hermiteConst 1 k ≤ 1 + hermiteConst 1 0 + hermiteConst 1 1 + hermiteConst 1 2 := by
  have h0 := hermiteConst_nonneg 1 0
  have h1 := hermiteConst_nonneg 1 1
  have h2 := hermiteConst_nonneg 1 2
  interval_cases k <;> linarith

/-- **Exact-reference remainder of the tensor cubic Hermite interpolant on the unit cell.**  If
`F` is smooth and every partial `dP^a dQ^b F` with `4 ≤ a + b ≤ 6` is bounded by `M` on `[0,1]²`,
then for `i + j ≤ 2` and `(p, q) ∈ [0,1]²` the derivative `dP^i dQ^j F` differs from the
corresponding derivative of the interpolant (the tensor of the differentiated basis, see
`CubicHermite.hasDerivAt_interp_p` etc.) by at most `hermRemConst · M`. -/
theorem unit_remainder {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {M : ℝ}
    (hM : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ∀ a b : ℕ, 4 ≤ a + b → a + b ≤ 6 →
      |(dP^[a] (dQ^[b] F)) z| ≤ M)
    {i j : ℕ} (hij : i + j ≤ 2) {p q : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1) :
    |(dP^[i] (dQ^[j] F)) (p, q) - tensor 1 (fR F) (uR F) (vR F) (wR F) (fun a => BH i a p)
        (fun a => BG i a p) (fun b => BH j b q) (fun b => BG j b q)| ≤ hermRemConst * M := by
  have hi : i ≤ 2 := by omega
  have hj : j ≤ 2 := by omega
  have hM0 : 0 ≤ M := (abs_nonneg _).trans
    (hM (0, 0) ⟨⟨le_refl _, zero_le_one⟩, ⟨le_refl _, zero_le_one⟩⟩ 4 0 (by norm_num) (by norm_num))
  set Fi := dP^[i] F with hFi
  have hFis : ContDiff ℝ ∞ Fi := contDiff_iterate_dP hF i
  -- Step A: the `q`-remainder of the section `q ↦ Fi(p, q)`
  set g : ℝ → ℝ := fun q => Fi (p, q) with hg
  have hgs : ContDiff ℝ ∞ g := contDiff_section_q hFis p
  have hgM : ∀ t ∈ Icc (0 : ℝ) 1, |iteratedDeriv 4 g t| ≤ M := by
    intro t ht
    rw [hg, iteratedDeriv_section_q hFis 4 p, hFi, iterate_dQ_iterate_dP hF]
    exact hM (p, t) ⟨hp, ht⟩ i 4 (by omega) (by omega)
  have hA := abs_iteratedDeriv_sub_herm_le g (hgs.of_le (by norm_cast)) hgM hj hq
  have eA1 : iteratedDeriv j g q = (dP^[i] (dQ^[j] F)) (p, q) := by
    rw [hg, iteratedDeriv_section_q hFis j p, hFi, iterate_dQ_iterate_dP hF]
  have hdg : ∀ t, deriv g t = (dP^[i] (dQ F)) (p, t) := by
    intro t
    rw [hg, deriv_section_q hFis, hFi]
    have := congrFun (iterate_dQ_iterate_dP hF i 1) (p, t)
    simpa using this
  -- Step B: the `p`-remainders of the sections `p ↦ F(p, b)` and `p ↦ dQ F(p, b)`
  have hB : ∀ (G : ℝ × ℝ → ℝ), ContDiff ℝ ∞ G → ∀ b : ℝ, (∀ t ∈ Icc (0 : ℝ) 1,
      |(dP^[4] G) (t, b)| ≤ M) →
      |(dP^[i] G) (p, b) - (G (0, b) * BH i 0 p + G (1, b) * BH i 1 p +
        dP G (0, b) * BG i 0 p + dP G (1, b) * BG i 1 p)| ≤ (1 + hermiteConst 1 i) * M := by
    intro G hG b hGM
    have hs := contDiff_section_p hG b
    have h := abs_iteratedDeriv_sub_herm_le (fun p => G (p, b)) (hs.of_le (by norm_cast))
      (fun t ht => by rw [iteratedDeriv_section_p hG]; exact hGM t ht) hi hp
    rw [iteratedDeriv_section_p hG] at h
    simp only [herm, deriv_section_p hG] at h
    exact h
  have h0m : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  have h1m : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl _⟩
  have hBF : ∀ b : ℝ, b ∈ Icc (0 : ℝ) 1 → _ := fun b hb => hB F hF b (fun t ht => by
    simpa using hM (t, b) ⟨ht, hb⟩ 4 0 (by norm_num) (by norm_num))
  have hBQ : ∀ b : ℝ, b ∈ Icc (0 : ℝ) 1 → _ := fun b hb => hB (dQ F) (contDiff_dQ hF) b
    (fun t ht => by simpa using hM (t, b) ⟨ht, hb⟩ 4 1 (by norm_num) (by norm_num))
  have t20 := hBF 0 h0m
  have t21 := hBF 1 h1m
  have t30 := hBQ 0 h0m
  have t31 := hBQ 1 h1m
  set R2a := (dP^[i] F) (p, 0) - (F (0, 0) * BH i 0 p + F (1, 0) * BH i 1 p +
        dP F (0, 0) * BG i 0 p + dP F (1, 0) * BG i 1 p)
  set R2b := (dP^[i] F) (p, 1) - (F (0, 1) * BH i 0 p + F (1, 1) * BH i 1 p +
        dP F (0, 1) * BG i 0 p + dP F (1, 1) * BG i 1 p)
  set R3a := (dP^[i] (dQ F)) (p, 0) - (dQ F (0, 0) * BH i 0 p + dQ F (1, 0) * BH i 1 p +
        dP (dQ F) (0, 0) * BG i 0 p + dP (dQ F) (1, 0) * BG i 1 p)
  set R3b := (dP^[i] (dQ F)) (p, 1) - (dQ F (0, 1) * BH i 0 p + dQ F (1, 1) * BH i 1 p +
        dP (dQ F) (0, 1) * BG i 0 p + dP (dQ F) (1, 1) * BG i 1 p)
  set R1 := iteratedDeriv j g q - herm j g q
  have hherm : herm j g q = (dP^[i] F) (p, 0) * BH j 0 q + (dP^[i] F) (p, 1) * BH j 1 q +
      (dP^[i] (dQ F)) (p, 0) * BG j 0 q + (dP^[i] (dQ F)) (p, 1) * BG j 1 q := by
    unfold herm
    rw [hdg 0, hdg 1]
  have hten : tensor 1 (fR F) (uR F) (vR F) (wR F) (fun a => BH i a p) (fun a => BG i a p)
      (fun b => BH j b q) (fun b => BG j b q) =
      F (0, 0) * BH i 0 p * BH j 0 q + F (0, 1) * BH i 0 p * BH j 1 q +
        F (1, 0) * BH i 1 p * BH j 0 q + F (1, 1) * BH i 1 p * BH j 1 q +
      (dP F (0, 0) * BG i 0 p * BH j 0 q + dP F (0, 1) * BG i 0 p * BH j 1 q +
        dP F (1, 0) * BG i 1 p * BH j 0 q + dP F (1, 1) * BG i 1 p * BH j 1 q) +
      (dQ F (0, 0) * BH i 0 p * BG j 0 q + dQ F (0, 1) * BH i 0 p * BG j 1 q +
        dQ F (1, 0) * BH i 1 p * BG j 0 q + dQ F (1, 1) * BH i 1 p * BG j 1 q) +
      (dP (dQ F) (0, 0) * BG i 0 p * BG j 0 q + dP (dQ F) (0, 1) * BG i 0 p * BG j 1 q +
        dP (dQ F) (1, 0) * BG i 1 p * BG j 0 q + dP (dQ F) (1, 1) * BG i 1 p * BG j 1 q) := by
    simp [tensor, fR, uR, vR, wR, Fin.sum_univ_two]
    ring
  have hdecomp : (dP^[i] (dQ^[j] F)) (p, q) - tensor 1 (fR F) (uR F) (vR F) (wR F)
      (fun a => BH i a p) (fun a => BG i a p) (fun b => BH j b q) (fun b => BG j b q) =
      R1 + (BH j 0 q * R2a + BH j 1 q * R2b) + (BG j 0 q * R3a + BG j 1 q * R3b) := by
    rw [hten]
    simp only [R1, R2a, R2b, R3a, R3b, eA1, hherm]
    ring
  rw [hdecomp]
  have hR1 : |R1| ≤ (1 + hermiteConst 1 j) * M := hA
  set c := hermiteConst 1 i
  have hb : ∀ (x y : ℝ), |x| ≤ 6 → |y| ≤ (1 + c) * M → |x * y| ≤ 6 * ((1 + c) * M) :=
    fun x y hx hy => by rw [abs_mul]; exact mul_le_mul hx hy (abs_nonneg _) (by norm_num)
  have u1 := hb _ _ (abs_BH_le hj hq 0) t20
  have u2 := hb _ _ (abs_BH_le hj hq 1) t21
  have u3 := hb _ _ (abs_BG_le hj hq 0) t30
  have u4 := hb _ _ (abs_BG_le hj hq 1) t31
  have s1 := abs_add_le (BH j 0 q * R2a) (BH j 1 q * R2b)
  have s2 := abs_add_le (BG j 0 q * R3a) (BG j 1 q * R3b)
  have s3 := abs_add_le (R1 + (BH j 0 q * R2a + BH j 1 q * R2b))
    (BG j 0 q * R3a + BG j 1 q * R3b)
  have s4 := abs_add_le R1 (BH j 0 q * R2a + BH j 1 q * R2b)
  have hci := one_add_hermiteConst_le hi
  have hcj := one_add_hermiteConst_le hj
  have hcM : (1 + c) * M ≤ (1 + hermiteConst 1 0 + hermiteConst 1 1 + hermiteConst 1 2) * M :=
    mul_le_mul_of_nonneg_right hci hM0
  have hcjM : (1 + hermiteConst 1 j) * M ≤
      (1 + hermiteConst 1 0 + hermiteConst 1 1 + hermiteConst 1 2) * M :=
    mul_le_mul_of_nonneg_right hcj hM0
  unfold hermRemConst
  nlinarith

/-! ### Scaling to a physical cell -/

/-- The affine chart `(p, q) ↦ (x₀ + h p, y₀ + h q)` of the cell `[x₀, x₀+h] × [y₀, y₀+h]`. -/
def cellMap (x₀ y₀ h : ℝ) (z : ℝ × ℝ) : ℝ × ℝ := (x₀ + h * z.1, y₀ + h * z.2)

theorem hasFDerivAt_cellMap (x₀ y₀ h : ℝ) (z : ℝ × ℝ) :
    HasFDerivAt (cellMap x₀ y₀ h) (h • ContinuousLinearMap.id ℝ (ℝ × ℝ)) z := by
  have e : cellMap x₀ y₀ h = fun z => (x₀, y₀) + h • z := by
    funext w; ext <;> simp [cellMap]
  rw [e]
  exact ((hasFDerivAt_id z).const_smul h).const_add (x₀, y₀)

theorem contDiff_cellMap (x₀ y₀ h : ℝ) : ContDiff ℝ ∞ (cellMap x₀ y₀ h) := by
  unfold cellMap
  exact (contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk
    (contDiff_const.add (contDiff_const.mul contDiff_snd))

theorem dP_scale {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (x₀ y₀ h c : ℝ) :
    dP (fun z => c * ψ (cellMap x₀ y₀ h z)) = fun z => c * h * dP ψ (cellMap x₀ y₀ h z) := by
  funext z
  have hd : HasFDerivAt (fun z => c * ψ (cellMap x₀ y₀ h z))
      (c • (fderiv ℝ ψ (cellMap x₀ y₀ h z)).comp (h • ContinuousLinearMap.id ℝ (ℝ × ℝ))) z :=
    (((hψ.differentiable (by simp)) _).hasFDerivAt.comp z (hasFDerivAt_cellMap x₀ y₀ h z)).const_mul c
  unfold dP
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul]
  rw [show h • ((1 : ℝ), (0 : ℝ)) = h • ((1 : ℝ), (0 : ℝ)) from rfl, map_smul, smul_eq_mul]
  ring

theorem dQ_scale {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (x₀ y₀ h c : ℝ) :
    dQ (fun z => c * ψ (cellMap x₀ y₀ h z)) = fun z => c * h * dQ ψ (cellMap x₀ y₀ h z) := by
  funext z
  have hd : HasFDerivAt (fun z => c * ψ (cellMap x₀ y₀ h z))
      (c • (fderiv ℝ ψ (cellMap x₀ y₀ h z)).comp (h • ContinuousLinearMap.id ℝ (ℝ × ℝ))) z :=
    (((hψ.differentiable (by simp)) _).hasFDerivAt.comp z (hasFDerivAt_cellMap x₀ y₀ h z)).const_mul c
  unfold dQ
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul]
  rw [map_smul, smul_eq_mul]
  ring

theorem iterate_dQ_scale {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (x₀ y₀ h c : ℝ) (b : ℕ) :
    dQ^[b] (fun z => c * ψ (cellMap x₀ y₀ h z)) =
      fun z => c * h ^ b * (dQ^[b] ψ) (cellMap x₀ y₀ h z) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Function.iterate_succ_apply', ih, dQ_scale (contDiff_iterate_dQ hψ b),
      Function.iterate_succ_apply']
    funext z; ring

theorem iterate_dP_scale {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (x₀ y₀ h c : ℝ) (a : ℕ) :
    dP^[a] (fun z => c * ψ (cellMap x₀ y₀ h z)) =
      fun z => c * h ^ a * (dP^[a] ψ) (cellMap x₀ y₀ h z) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Function.iterate_succ_apply', ih, dP_scale (contDiff_iterate_dP hψ a),
      Function.iterate_succ_apply']
    funext z; ring

/-- `dP^a dQ^b (φ ∘ cellMap) = h^{a+b} (dP^a dQ^b φ) ∘ cellMap`. -/
theorem iterate_dP_dQ_comp_cellMap {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (x₀ y₀ h : ℝ)
    (a b : ℕ) (z : ℝ × ℝ) :
    (dP^[a] (dQ^[b] (fun z => φ (cellMap x₀ y₀ h z)))) z =
      h ^ (a + b) * (dP^[a] (dQ^[b] φ)) (cellMap x₀ y₀ h z) := by
  have e0 : (fun z => φ (cellMap x₀ y₀ h z)) = fun z => 1 * φ (cellMap x₀ y₀ h z) := by
    funext w; ring
  rw [e0, iterate_dQ_scale hφ, iterate_dP_scale (contDiff_iterate_dQ hφ b)]
  ring

/-- Physical corner value records `φ(x₀ + h a, y₀ + h b)`. -/
def cellF (φ : ℝ × ℝ → ℝ) (x₀ y₀ h : ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun a b => φ (cellMap x₀ y₀ h (((a : ℕ) : ℝ), ((b : ℕ) : ℝ)))
/-- Physical corner records of `∂ₓφ`. -/
def cellU (φ : ℝ × ℝ → ℝ) (x₀ y₀ h : ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun a b => dP φ (cellMap x₀ y₀ h (((a : ℕ) : ℝ), ((b : ℕ) : ℝ)))
/-- Physical corner records of `∂_yφ`. -/
def cellV (φ : ℝ × ℝ → ℝ) (x₀ y₀ h : ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun a b => dQ φ (cellMap x₀ y₀ h (((a : ℕ) : ℝ), ((b : ℕ) : ℝ)))
/-- Physical corner records of `∂ₓ∂_yφ`. -/
def cellW (φ : ℝ × ℝ → ℝ) (x₀ y₀ h : ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun a b => dP (dQ φ) (cellMap x₀ y₀ h (((a : ℕ) : ℝ), ((b : ℕ) : ℝ)))

theorem tensor_scale (h : ℝ) (f u v w : Fin 2 → Fin 2 → ℝ) (Hp Gp Hq Gq : Fin 2 → ℝ) :
    tensor 1 f (fun a b => h * u a b) (fun a b => h * v a b) (fun a b => h ^ 2 * w a b)
      Hp Gp Hq Gq = tensor h f u v w Hp Gp Hq Gq := by
  simp only [tensor, Fin.sum_univ_two]
  ring

/-- **Exact-reference remainder of the tensor cubic Hermite readout on a physical cell**
(`O(h^{4-k})` for `k ≤ 2`).  Let `φ` be smooth, `0 < h ≤ 1`, and let `M` bound every partial
`dP^a dQ^b φ` with `4 ≤ a + b ≤ 6` on `[x₀, x₀+h] × [y₀, y₀+h]`.  With the exact corner records
`f = φ, u = ∂ₓφ, v = ∂_yφ, w = ∂ₓ∂_yφ`, for `i + j ≤ 2` and `(p, q) ∈ [0,1]²`:
`|h^{i+j} ∂ₓ^i∂_y^j φ(x₀+hp, y₀+hq) - ∂_p^i∂_q^j interp h f u v w (p, q)| ≤ hermRemConst · M h⁴`. -/
theorem cell_remainder {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {x₀ y₀ h M : ℝ} (hh : 0 < h)
    (hh1 : h ≤ 1)
    (hM : ∀ x ∈ Icc x₀ (x₀ + h), ∀ y ∈ Icc y₀ (y₀ + h), ∀ a b : ℕ, 4 ≤ a + b → a + b ≤ 6 →
      |(dP^[a] (dQ^[b] φ)) (x, y)| ≤ M)
    {i j : ℕ} (hij : i + j ≤ 2) {p q : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1) :
    |h ^ (i + j) * (dP^[i] (dQ^[j] φ)) (x₀ + h * p, y₀ + h * q) -
        tensor h (cellF φ x₀ y₀ h) (cellU φ x₀ y₀ h) (cellV φ x₀ y₀ h) (cellW φ x₀ y₀ h)
          (fun a => BH i a p) (fun a => BG i a p) (fun b => BH j b q) (fun b => BG j b q)| ≤
      hermRemConst * M * h ^ 4 := by
  set F := fun z => φ (cellMap x₀ y₀ h z) with hFdef
  have hF : ContDiff ℝ ∞ F := hφ.comp (contDiff_cellMap x₀ y₀ h)
  have hmem : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, (cellMap x₀ y₀ h z).1 ∈ Icc x₀ (x₀ + h) ∧
      (cellMap x₀ y₀ h z).2 ∈ Icc y₀ (y₀ + h) := by
    rintro ⟨s, t⟩ ⟨⟨hs0, hs1⟩, ⟨ht0, ht1⟩⟩
    simp only [cellMap]
    refine ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩
  have hFM : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ∀ a b : ℕ, 4 ≤ a + b → a + b ≤ 6 →
      |(dP^[a] (dQ^[b] F)) z| ≤ h ^ 4 * M := by
    intro z hz a b h4 h6
    rw [hFdef, iterate_dP_dQ_comp_cellMap hφ, abs_mul, abs_of_pos (pow_pos hh _)]
    have hb := hM _ (hmem z hz).1 _ (hmem z hz).2 a b h4 h6
    have hM0 : 0 ≤ M := (abs_nonneg _).trans hb
    have hpow : h ^ (a + b) ≤ h ^ 4 := pow_le_pow_of_le_one hh.le hh1 h4
    calc h ^ (a + b) * |(dP^[a] (dQ^[b] φ)) (cellMap x₀ y₀ h z)| ≤ h ^ (a + b) * M :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ h ^ 4 * M := mul_le_mul_of_nonneg_right hpow hM0
  have hU := unit_remainder hF hFM hij hp hq
  have hlhs : (dP^[i] (dQ^[j] F)) (p, q) =
      h ^ (i + j) * (dP^[i] (dQ^[j] φ)) (x₀ + h * p, y₀ + h * q) := by
    rw [hFdef, iterate_dP_dQ_comp_cellMap hφ]; rfl
  have hrec : tensor 1 (fR F) (uR F) (vR F) (wR F) (fun a => BH i a p) (fun a => BG i a p)
      (fun b => BH j b q) (fun b => BG j b q) =
      tensor h (cellF φ x₀ y₀ h) (cellU φ x₀ y₀ h) (cellV φ x₀ y₀ h) (cellW φ x₀ y₀ h)
        (fun a => BH i a p) (fun a => BG i a p) (fun b => BH j b q) (fun b => BG j b q) := by
    have e1 : uR F = fun a b => h * cellU φ x₀ y₀ h a b := by
      funext a b
      have := iterate_dP_dQ_comp_cellMap hφ x₀ y₀ h 1 0 (((a : ℕ) : ℝ), ((b : ℕ) : ℝ))
      simpa [uR, cellU, hFdef] using this
    have e2 : vR F = fun a b => h * cellV φ x₀ y₀ h a b := by
      funext a b
      have := iterate_dP_dQ_comp_cellMap hφ x₀ y₀ h 0 1 (((a : ℕ) : ℝ), ((b : ℕ) : ℝ))
      simpa [vR, cellV, hFdef] using this
    have e3 : wR F = fun a b => h ^ 2 * cellW φ x₀ y₀ h a b := by
      funext a b
      have := iterate_dP_dQ_comp_cellMap hφ x₀ y₀ h 1 1 (((a : ℕ) : ℝ), ((b : ℕ) : ℝ))
      simpa [wR, cellW, hFdef] using this
    rw [e1, e2, e3, tensor_scale]
    rfl
  rw [hlhs, hrec] at hU
  calc _ ≤ hermRemConst * (h ^ 4 * M) := hU
    _ = hermRemConst * M * h ^ 4 := by ring

/-- **The readout remainder in physical scaling**: under the hypotheses of `cell_remainder`,
`|∂ₓ^i∂_y^j φ(x₀+hp, y₀+hq) - h^{-(i+j)} ∂_p^i∂_q^j interp h f u v w (p, q)|
  ≤ hermRemConst · M · h^{4-(i+j)}`; `h^{-(i+j)} ∂_p^i∂_q^j interp` is the `(i, j)` physical
derivative of the readout `(x, y) ↦ interp h f u v w ((x-x₀)/h, (y-y₀)/h)`. -/
theorem cell_remainder_scaled {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {x₀ y₀ h M : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1)
    (hM : ∀ x ∈ Icc x₀ (x₀ + h), ∀ y ∈ Icc y₀ (y₀ + h), ∀ a b : ℕ, 4 ≤ a + b → a + b ≤ 6 →
      |(dP^[a] (dQ^[b] φ)) (x, y)| ≤ M)
    {i j : ℕ} (hij : i + j ≤ 2) {p q : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1) :
    |(dP^[i] (dQ^[j] φ)) (x₀ + h * p, y₀ + h * q) -
        tensor h (cellF φ x₀ y₀ h) (cellU φ x₀ y₀ h) (cellV φ x₀ y₀ h) (cellW φ x₀ y₀ h)
          (fun a => BH i a p) (fun a => BG i a p) (fun b => BH j b q) (fun b => BG j b q) /
          h ^ (i + j)| ≤
      hermRemConst * M * h ^ (4 - (i + j)) := by
  have h1 := cell_remainder hφ hh hh1 hM hij hp hq
  have hpos : 0 < h ^ (i + j) := pow_pos hh _
  have e : (dP^[i] (dQ^[j] φ)) (x₀ + h * p, y₀ + h * q) -
      tensor h (cellF φ x₀ y₀ h) (cellU φ x₀ y₀ h) (cellV φ x₀ y₀ h) (cellW φ x₀ y₀ h)
          (fun a => BH i a p) (fun a => BG i a p) (fun b => BH j b q) (fun b => BG j b q) /
          h ^ (i + j) =
      (h ^ (i + j) * (dP^[i] (dQ^[j] φ)) (x₀ + h * p, y₀ + h * q) -
        tensor h (cellF φ x₀ y₀ h) (cellU φ x₀ y₀ h) (cellV φ x₀ y₀ h) (cellW φ x₀ y₀ h)
          (fun a => BH i a p) (fun a => BG i a p) (fun b => BH j b q) (fun b => BG j b q)) /
        h ^ (i + j) := by field_simp
  rw [e, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  have hp4 : h ^ 4 = h ^ (4 - (i + j)) * h ^ (i + j) := by
    rw [← pow_add]; congr 1; omega
  rw [hp4] at h1
  linarith

end

end RenewalGeometry.CubicHermiteRemainder
