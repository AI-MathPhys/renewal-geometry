/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.CellQuadratureEstimate
import RenewalGeometry.Gravity.DeSitterExactLinkDefects

/-!
# Palatini–cosmological first variation and its midpoint quadrature on the de Sitter slab
(`thm:supp-finite-defects`, Palatini part of `eq:supp-finite-defect-bound`;
emergent-spacetime manuscript)

The manuscript lets `δS(e, ω)` be the continuum Palatini–cosmological first variation and
`δS_h(e_h, U_h)` its midpoint quadrature on the cells of `K_h`, and its proof uses that the
first variation "is a finite sum of products of coframe, curvature, and test-field
coefficients".  We encode this as follows.

* Densities `eq:main-phv-densities`: `L_Palatini = ½ ε_{IJKL} eᴵ ∧ eᴶ ∧ R^{KL}`,
  `L_vol = (1/4!) ε_{IJKL} eᴵ ∧ eᴶ ∧ eᴷ ∧ eᴸ`; the Palatini–cosmological action is
  `S = c_P ∫ L_Palatini + c_V ∫ L_vol` (arbitrary real coefficients).
* Its first variation in Euler–Lagrange (bulk) form, i.e. after the integration by parts that
  removes derivatives of the test fields, as the manuscript's proof requires:
  `δS[v, w] = ∫ c_P ε_{IJKL} vᴵ ∧ eᴶ ∧ R^{KL} + (c_V/6) ε_{IJKL} vᴵ ∧ eᴶ ∧ eᴷ ∧ eᴸ
              − c_P ε_{IJKL} Tᴵ ∧ eᴶ ∧ w^{KL}`
  for a coframe variation `vᴵ` and a connection variation `w^{KL}` (`δ_ω ½ε e e R =
  ½ ε e e ∧ D w ≃ −½ ε D(e∧e) ∧ w = −ε T ∧ e ∧ w`).  Four-forms are evaluated on the coordinate
  frame `(∂_t, ∂₁, ∂₂, ∂₃)` (`firstVariationDensity`, `wedge4`, `wedge112`, `wedge211`).
* `firstVariation`: `δS` on a region `S` (Lebesgue integral); `quadratureVariation`: the
  one-point (midpoint) quadrature `δS_h = ∑_c |c| ρ(F_h(c), v(x_c))` on a finite measurable cell
  decomposition with quadrature points `x_c` and cell coefficients `F_h(c)`.
* `dsComp`: the de Sitter / flat Cartan data of `Gravity/DeSitterExactLinkDefects.lean` in
  components; faithfulness check `firstVariationDensity_desitter_eq_zero`: with the tuned
  cosmological coefficient `c_V = −6 c_P H²` (`Λ = 3H²`, `eq:supp-desitter-einstein`) the de
  Sitter data are stationary (the density vanishes identically, for every test value).

Main results:

* `abs_firstVariationDensity_sub_le`: the density is locally Lipschitz in all coefficients.
* `abs_quadratureVariation_sub_firstVariation_le`: on the slab `[−T, T] × D` (`D` any finite
  measure spatial fundamental domain), for every finite measurable cell decomposition whose
  points lie within `κh ≤ 1` of their quadrature point, every cell writer whose coefficients are
  within `ε ≤ 1` of the continuum coefficients at the quadrature point, and every unit test
  field (`|v|, |w| ≤ 1`, `1`-Lipschitz components, a superset of the `C¹` unit ball, see
  `isUnitTest_of_contDiff`), `|δS_h[v] − δS[v]| ≤ L_T ((D_T + 1) κh + ε) |[−T,T] × D|`.
  The midpoint quadrature itself is `ε = 0` (`palatini_midpoint_slab_le`).
* `palatini_flat_eq_zero`: for the flat regulator (`H = 0`, `c_V = 0`) both sides vanish.
* `holComp`, `holComp_close`, `palatini_holonomyWriter_slab_le`: the finite holonomy writer
  (curvature coefficients `−|p|⁻¹ log U_{∂p}` of the exact-link holonomies of the coordinate faces
  centred at the quadrature point, torsion coefficients from their developed-edge closures) is
  `C_T h`-accurate, so the quadrature built from the regulator data `(e_h, U_h)` also has
  `O_T(h)` error.
* `summable_palatiniConst_diagonal`: the slab constants are summable along `h_n = 2^{−n²}`,
  `T_n = n`.
* `finiteDefects_slab`, `finiteDefects_full_diagonal`, `finiteDefects_flat_full`: the complete
  `eq:supp-finite-defect-bound` (curvature, torsion and Palatini parts) with
  `C_T = 2 C_T^{Cartan} + C_T^P`, its diagonal summability, and the flat case.

Disclosures: the first variation is taken in Euler–Lagrange (bulk) form, boundary terms of the
integration by parts are not included; the coefficients `(c_P, c_V)` are arbitrary (with the
tuned value `c_V = −6 c_P H²` both sides vanish identically); four-forms are integrated against
coordinate Lebesgue measure on `[−T, T] × D` (orientation `dt ∧ dx¹ ∧ dx² ∧ dx³`); cells are any
finite measurable decomposition of the slab with quadrature points within `κh` (the product cells
of `K_h` with their midpoints are a special case).
-/

namespace RenewalGeometry.DeSitterExactLink.Palatini

open MeasureTheory Set _root_.Matrix

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-! ### Index conventions, Levi-Civita symbol, coordinate frame -/

/-- Reference ordering `0, 1, 2, 3` of the internal / coordinate index set `Idx`. -/
def refIdx : Fin 4 ≃ Idx := finSuccEquiv 3

open Classical in
/-- Levi-Civita symbol `ε_{IJKL}` with `ε_{0123} = 1`. -/
noncomputable def levi (I J K L : Idx) : ℝ :=
  if h : Function.Bijective (![I, J, K, L] : Fin 4 → Idx) then
    ((Equiv.Perm.sign ((Equiv.ofBijective _ h).trans refIdx.symm) : ℤ) : ℝ)
  else 0

theorem abs_levi_le (I J K L : Idx) : |levi I J K L| ≤ 1 := by
  unfold levi
  split_ifs with hb
  · rcases Int.units_eq_one_or
      (Equiv.Perm.sign ((Equiv.ofBijective _ hb).trans refIdx.symm)) with h | h <;> simp [h]
  · simp

/-- Coordinate frame `∂_t, ∂₁, ∂₂, ∂₃` of `ℝ × ℝ³`. -/
noncomputable def cvec : Idx → TVec
  | none => (1, 0)
  | some a => (0, Pi.single a 1)

theorem norm_cvec_le (μ : Idx) : ‖cvec μ‖ ≤ 1 := by
  cases μ with
  | none => simp [cvec]
  | some a =>
    simp only [cvec, Prod.norm_def, norm_zero]
    refine max_le zero_le_one ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun b => ?_)
    by_cases hb : b = a
    · subst hb; simp
    · simp [Pi.single_apply, hb]

theorem abs_cvec_fst_le (μ : Idx) : |(cvec μ).1| ≤ 1 :=
  (norm_fst_le (cvec μ)).trans (norm_cvec_le μ)

theorem norm_cvec_snd_le (μ : Idx) : ‖(cvec μ).2‖ ≤ 1 :=
  (norm_snd_le (cvec μ)).trans (norm_cvec_le μ)

/-! ### Component data and wedge evaluations -/

/-- Cartan coefficients at a point in the coordinate frame: `e I μ = eᴵ(∂_μ)`,
`R K L μ ν = R^{KL}(∂_μ, ∂_ν)` (both internal indices up), `T I μ ν = Tᴵ(∂_μ, ∂_ν)`. -/
structure CartanComp where
  /-- coframe components `eᴵ_μ` -/
  e : Idx → Idx → ℝ
  /-- curvature components `R^{KL}_{μν}` -/
  R : Idx → Idx → Idx → Idx → ℝ
  /-- torsion components `Tᴵ_{μν}` -/
  T : Idx → Idx → Idx → ℝ

/-- Test values at a point: coframe variation `vᴵ_μ` and connection variation `w^{KL}_μ`. -/
structure TestVal where
  /-- coframe variation `vᴵ_μ` -/
  v : Idx → Idx → ℝ
  /-- connection variation `w^{KL}_μ` -/
  w : Idx → Idx → Idx → ℝ

/-- `(a ∧ b ∧ c ∧ d)(∂_t, ∂₁, ∂₂, ∂₃)` for one-forms `a, b, c, d`. -/
noncomputable def wedge4 (a b c d : Idx → ℝ) : ℝ :=
  ∑ σ : Equiv.Perm Idx, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
    (a (σ (refIdx 0)) * b (σ (refIdx 1)) * c (σ (refIdx 2)) * d (σ (refIdx 3)))

/-- `(a ∧ b ∧ g)(∂_t, ∂₁, ∂₂, ∂₃)` for one-forms `a, b` and a two-form `g`. -/
noncomputable def wedge112 (a b : Idx → ℝ) (g : Idx → Idx → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ σ : Equiv.Perm Idx, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
    (a (σ (refIdx 0)) * b (σ (refIdx 1)) * g (σ (refIdx 2)) (σ (refIdx 3)))

/-- `(g ∧ a ∧ b)(∂_t, ∂₁, ∂₂, ∂₃)` for a two-form `g` and one-forms `a, b`. -/
noncomputable def wedge211 (g : Idx → Idx → ℝ) (a b : Idx → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ σ : Equiv.Perm Idx, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
    (g (σ (refIdx 0)) (σ (refIdx 1)) * a (σ (refIdx 2)) * b (σ (refIdx 3)))

/-- **Palatini–cosmological first-variation density** (Euler–Lagrange form) of
`S = c_P ∫ ½ ε eeR + c_V ∫ (1/4!) ε eeee`, evaluated on the coordinate frame:
`c_P ε vᴵ∧eᴶ∧R^{KL} + (c_V/6) ε vᴵ∧eᴶ∧eᴷ∧eᴸ − c_P ε Tᴵ∧eᴶ∧w^{KL}`. -/
noncomputable def firstVariationDensity (cP cV : ℝ) (F : CartanComp) (u : TestVal) : ℝ :=
  ∑ I : Idx, ∑ J : Idx, ∑ K : Idx, ∑ L : Idx, levi I J K L *
    (cP * wedge112 (u.v I) (F.e J) (F.R K L) + cV / 6 * wedge4 (u.v I) (F.e J) (F.e K) (F.e L)
      - cP * wedge211 (F.T I) (F.e J) (u.w K L))

/-! ### Elementary product bounds -/

theorem card_perm_idx : Fintype.card (Equiv.Perm Idx) = 24 := by
  rw [Fintype.card_perm, Fintype.card_option, Fintype.card_fin]; rfl

theorem abs_sum_perm_le (f : Equiv.Perm Idx → ℝ) {M : ℝ} (hf : ∀ σ, |f σ| ≤ M) :
    |∑ σ : Equiv.Perm Idx, ((Equiv.Perm.sign σ : ℤ) : ℝ) * f σ| ≤ 24 * M := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm Idx)),
      |((Equiv.Perm.sign σ : ℤ) : ℝ) * f σ| ≤ M := fun σ _ => by
    rw [abs_mul]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h, hf σ]
  refine (Finset.sum_le_card_nsmul _ _ _ this).trans ?_
  rw [Finset.card_univ, card_perm_idx]; simp

theorem abs_mul3_sub_le {a b c a' b' c' B d : ℝ} (hB : 0 ≤ B)
    (ha : |a| ≤ B) (hb : |b| ≤ B) (hb' : |b'| ≤ B) (hc' : |c'| ≤ B)
    (hda : |a - a'| ≤ d) (hdb : |b - b'| ≤ d) (hdc : |c - c'| ≤ d) (hc : |c| ≤ B)
    (ha' : |a'| ≤ B) :
    |a * b * c - a' * b' * c'| ≤ 3 * B ^ 2 * d := by
  have e : a * b * c - a' * b' * c' = (a - a') * b * c + a' * (b - b') * c + a' * b' * (c - c') := by
    ring
  have hd : 0 ≤ d := (abs_nonneg _).trans hda
  rw [e]
  have t1 : |(a - a') * b * c| ≤ d * B * B := by
    rw [abs_mul, abs_mul]; gcongr
  have t2 : |a' * (b - b') * c| ≤ B * d * B := by
    rw [abs_mul, abs_mul]; gcongr
  have t3 : |a' * b' * (c - c')| ≤ B * B * d := by
    rw [abs_mul, abs_mul]; gcongr
  calc _ ≤ |(a - a') * b * c| + |a' * (b - b') * c| + |a' * b' * (c - c')| :=
        abs_add_three _ _ _
    _ ≤ d * B * B + B * d * B + B * B * d := add_le_add (add_le_add t1 t2) t3
    _ = 3 * B ^ 2 * d := by ring

theorem abs_mul4_sub_le {a b c f a' b' c' f' B d : ℝ} (hB : 0 ≤ B)
    (ha : |a| ≤ B) (hb : |b| ≤ B) (hc : |c| ≤ B) (hf : |f| ≤ B)
    (ha' : |a'| ≤ B) (hb' : |b'| ≤ B) (hc' : |c'| ≤ B) (hf' : |f'| ≤ B)
    (hda : |a - a'| ≤ d) (hdb : |b - b'| ≤ d) (hdc : |c - c'| ≤ d) (hdf : |f - f'| ≤ d) :
    |a * b * c * f - a' * b' * c' * f'| ≤ 4 * B ^ 3 * d := by
  have e : a * b * c * f - a' * b' * c' * f' = (a * b * c - a' * b' * c') * f
      + a' * b' * c' * (f - f') := by ring
  have h3 := abs_mul3_sub_le hB ha hb hb' hc' hda hdb hdc hc ha'
  have hd : 0 ≤ d := (abs_nonneg _).trans hda
  rw [e]
  have t1 : |(a * b * c - a' * b' * c') * f| ≤ 3 * B ^ 2 * d * B := by
    rw [abs_mul]; gcongr
  have t2 : |a' * b' * c' * (f - f')| ≤ B * B * B * d := by
    rw [abs_mul, abs_mul, abs_mul]; gcongr
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ 3 * B ^ 2 * d * B + B * B * B * d := add_le_add t1 t2
    _ = 4 * B ^ 3 * d := by ring

/-! ### Lipschitz bound of the density -/

/-- All coefficients of `F` are bounded by `B`. -/
def CompBound (B : ℝ) (F : CartanComp) : Prop :=
  (∀ I μ, |F.e I μ| ≤ B) ∧ (∀ K L μ ν, |F.R K L μ ν| ≤ B) ∧ (∀ I μ ν, |F.T I μ ν| ≤ B)

/-- All coefficients of `F` and `F'` differ by at most `d`. -/
def CompClose (d : ℝ) (F F' : CartanComp) : Prop :=
  (∀ I μ, |F.e I μ - F'.e I μ| ≤ d) ∧ (∀ K L μ ν, |F.R K L μ ν - F'.R K L μ ν| ≤ d) ∧
    (∀ I μ ν, |F.T I μ ν - F'.T I μ ν| ≤ d)

/-- All test values are bounded by `B`. -/
def TestBound (B : ℝ) (u : TestVal) : Prop :=
  (∀ I μ, |u.v I μ| ≤ B) ∧ (∀ K L μ, |u.w K L μ| ≤ B)

/-- All test values differ by at most `d`. -/
def TestClose (d : ℝ) (u u' : TestVal) : Prop :=
  (∀ I μ, |u.v I μ - u'.v I μ| ≤ d) ∧ (∀ K L μ, |u.w K L μ - u'.w K L μ| ≤ d)

theorem sum_perm_sub (f g : Equiv.Perm Idx → ℝ) :
    ∑ σ : Equiv.Perm Idx, ((Equiv.Perm.sign σ : ℤ) : ℝ) * f σ
      - ∑ σ : Equiv.Perm Idx, ((Equiv.Perm.sign σ : ℤ) : ℝ) * g σ
      = ∑ σ : Equiv.Perm Idx, ((Equiv.Perm.sign σ : ℤ) : ℝ) * (f σ - g σ) := by
  rw [← Finset.sum_sub_distrib]; simp only [mul_sub]

theorem abs_wedge4_sub_le {a b c f a' b' c' f' : Idx → ℝ} {B d : ℝ} (hB : 0 ≤ B)
    (ha : ∀ μ, |a μ| ≤ B) (hb : ∀ μ, |b μ| ≤ B) (hc : ∀ μ, |c μ| ≤ B) (hf : ∀ μ, |f μ| ≤ B)
    (ha' : ∀ μ, |a' μ| ≤ B) (hb' : ∀ μ, |b' μ| ≤ B) (hc' : ∀ μ, |c' μ| ≤ B)
    (hf' : ∀ μ, |f' μ| ≤ B)
    (hda : ∀ μ, |a μ - a' μ| ≤ d) (hdb : ∀ μ, |b μ - b' μ| ≤ d) (hdc : ∀ μ, |c μ - c' μ| ≤ d)
    (hdf : ∀ μ, |f μ - f' μ| ≤ d) :
    |wedge4 a b c f - wedge4 a' b' c' f'| ≤ 96 * B ^ 3 * d := by
  unfold wedge4
  rw [sum_perm_sub]
  have := abs_sum_perm_le _ fun σ => abs_mul4_sub_le hB (ha _) (hb _) (hc _) (hf _) (ha' _)
    (hb' _) (hc' _) (hf' _) (hda (σ (refIdx 0))) (hdb (σ (refIdx 1))) (hdc (σ (refIdx 2)))
    (hdf (σ (refIdx 3)))
  linarith

theorem abs_wedge112_sub_le {a b a' b' : Idx → ℝ} {g g' : Idx → Idx → ℝ} {B d : ℝ} (hB : 0 ≤ B)
    (ha : ∀ μ, |a μ| ≤ B) (hb : ∀ μ, |b μ| ≤ B) (hg : ∀ μ ν, |g μ ν| ≤ B)
    (ha' : ∀ μ, |a' μ| ≤ B) (hb' : ∀ μ, |b' μ| ≤ B) (hg' : ∀ μ ν, |g' μ ν| ≤ B)
    (hda : ∀ μ, |a μ - a' μ| ≤ d) (hdb : ∀ μ, |b μ - b' μ| ≤ d)
    (hdg : ∀ μ ν, |g μ ν - g' μ ν| ≤ d) :
    |wedge112 a b g - wedge112 a' b' g'| ≤ 12 * (3 * B ^ 2 * d) := by
  unfold wedge112
  rw [← mul_sub, sum_perm_sub, abs_mul]
  have := abs_sum_perm_le _ fun σ => abs_mul3_sub_le hB (ha _) (hb _) (hb' _) (hg' _ _)
    (hda (σ (refIdx 0))) (hdb (σ (refIdx 1))) (hdg (σ (refIdx 2)) (σ (refIdx 3))) (hg _ _)
    (ha' _)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  linarith

theorem abs_wedge211_sub_le {a b a' b' : Idx → ℝ} {g g' : Idx → Idx → ℝ} {B d : ℝ} (hB : 0 ≤ B)
    (ha : ∀ μ, |a μ| ≤ B) (hb : ∀ μ, |b μ| ≤ B) (hg : ∀ μ ν, |g μ ν| ≤ B)
    (ha' : ∀ μ, |a' μ| ≤ B) (hb' : ∀ μ, |b' μ| ≤ B) (hg' : ∀ μ ν, |g' μ ν| ≤ B)
    (hda : ∀ μ, |a μ - a' μ| ≤ d) (hdb : ∀ μ, |b μ - b' μ| ≤ d)
    (hdg : ∀ μ ν, |g μ ν - g' μ ν| ≤ d) :
    |wedge211 g a b - wedge211 g' a' b'| ≤ 12 * (3 * B ^ 2 * d) := by
  unfold wedge211
  rw [← mul_sub, sum_perm_sub, abs_mul]
  have := abs_sum_perm_le _ fun σ => abs_mul3_sub_le hB (hg _ _) (ha _) (ha' _) (hb' _)
    (hdg (σ (refIdx 0)) (σ (refIdx 1))) (hda (σ (refIdx 2))) (hdb (σ (refIdx 3))) (hb _)
    (hg' _ _)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  linarith

theorem abs_sum_idx4_le (f : Idx → Idx → Idx → Idx → ℝ) {M : ℝ}
    (hf : ∀ I J K L, |f I J K L| ≤ M) :
    |∑ I : Idx, ∑ J : Idx, ∑ K : Idx, ∑ L : Idx, f I J K L| ≤ 256 * M := by
  have hc : Fintype.card Idx = 4 := by rw [Fintype.card_option, Fintype.card_fin]
  have step : ∀ (g : Idx → ℝ) (N : ℝ), (∀ I, |g I| ≤ N) → |∑ I : Idx, g I| ≤ 4 * N :=
    fun g N hg => by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_card_nsmul _ _ N fun I _ => hg I).trans ?_
      rw [Finset.card_univ, hc]; simp
  have := step _ _ fun I => step _ _ fun J => step _ _ fun K => step _ _ fun L => hf I J K L
  linarith

/-- Lipschitz constant of the first-variation density on coefficients bounded by `B`. -/
noncomputable def densityLip (cP cV B : ℝ) : ℝ := 256 * (72 * |cP| * B ^ 2 + 16 * |cV| * B ^ 3)

theorem densityLip_nonneg (cP cV : ℝ) {B : ℝ} (hB : 0 ≤ B) : 0 ≤ densityLip cP cV B := by
  unfold densityLip; positivity

theorem abs_term_sub_le (cP cV : ℝ) {x112 x4 x211 y112 y4 y211 B d : ℝ}
    (h1 : |x112 - y112| ≤ 12 * (3 * B ^ 2 * d)) (h2 : |x4 - y4| ≤ 96 * B ^ 3 * d)
    (h3 : |x211 - y211| ≤ 12 * (3 * B ^ 2 * d)) :
    |(cP * x112 + cV / 6 * x4 - cP * x211) - (cP * y112 + cV / 6 * y4 - cP * y211)|
      ≤ 72 * |cP| * B ^ 2 * d + 16 * |cV| * B ^ 3 * d := by
  have e : (cP * x112 + cV / 6 * x4 - cP * x211) - (cP * y112 + cV / 6 * y4 - cP * y211)
      = cP * (x112 - y112) + cV / 6 * (x4 - y4) - cP * (x211 - y211) := by ring
  rw [e]
  have k1 := abs_sub (cP * (x112 - y112) + cV / 6 * (x4 - y4)) (cP * (x211 - y211))
  have k2 := abs_add_le (cP * (x112 - y112)) (cV / 6 * (x4 - y4))
  have hcP := abs_nonneg cP
  have hcV := abs_nonneg cV
  have m1 : |cP * (x112 - y112)| ≤ |cP| * (12 * (3 * B ^ 2 * d)) := by
    rw [abs_mul]; gcongr
  have m2 : |cV / 6 * (x4 - y4)| ≤ |cV| / 6 * (96 * B ^ 3 * d) := by
    rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 6)]; gcongr
  have m3 : |cP * (x211 - y211)| ≤ |cP| * (12 * (3 * B ^ 2 * d)) := by
    rw [abs_mul]; gcongr
  nlinarith

/-- **The first-variation density is locally Lipschitz** in the Cartan coefficients and the
test values: for coefficients and test values bounded by `B` and differing by at most `d`,
`|ρ(F, u) − ρ(F', u')| ≤ densityLip c_P c_V B · d`. -/
theorem abs_firstVariationDensity_sub_le (cP cV : ℝ) {F F' : CartanComp} {u u' : TestVal}
    {B d : ℝ} (hB : 0 ≤ B) (hF : CompBound B F) (hF' : CompBound B F') (hu : TestBound B u)
    (hu' : TestBound B u') (hFF : CompClose d F F') (huu : TestClose d u u') :
    |firstVariationDensity cP cV F u - firstVariationDensity cP cV F' u'|
      ≤ densityLip cP cV B * d := by
  obtain ⟨hFe, hFR, hFT⟩ := hF
  obtain ⟨hFe', hFR', hFT'⟩ := hF'
  obtain ⟨hv, hw⟩ := hu
  obtain ⟨hv', hw'⟩ := hu'
  obtain ⟨hde, hdR, hdT⟩ := hFF
  obtain ⟨hdv, hdw⟩ := huu
  unfold firstVariationDensity
  simp only [← Finset.sum_sub_distrib, ← mul_sub]
  have := abs_sum_idx4_le _ (M := 72 * |cP| * B ^ 2 * d + 16 * |cV| * B ^ 3 * d)
    fun I J K L => by
      rw [abs_mul]
      have h1 := abs_wedge112_sub_le hB (hv I) (hFe J) (hFR K L) (hv' I) (hFe' J) (hFR' K L)
        (hdv I) (hde J) (hdR K L)
      have h2 := abs_wedge4_sub_le hB (hv I) (hFe J) (hFe K) (hFe L) (hv' I) (hFe' J) (hFe' K)
        (hFe' L) (hdv I) (hde J) (hde K) (hde L)
      have h3 := abs_wedge211_sub_le hB (hFe J) (fun μ => hw K L μ) (hFT I) (hFe' J)
        (fun μ => hw' K L μ) (hFT' I) (hde J) (fun μ => hdw K L μ) (hdT I)
      have hX := abs_term_sub_le cP cV h1 h2 h3
      calc |levi I J K L| * _ ≤ 1 * (72 * |cP| * B ^ 2 * d + 16 * |cV| * B ^ 3 * d) :=
            mul_le_mul (abs_levi_le I J K L) hX (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
  calc _ ≤ 256 * (72 * |cP| * B ^ 2 * d + 16 * |cV| * B ^ 3 * d) := this
    _ = densityLip cP cV B * d := by unfold densityLip; ring

/-! ### The de Sitter / flat Cartan data in components -/

/-- The Cartan coefficients of the de Sitter (`H ≠ 0`) or flat (`H = 0`) regulator at time `t`
in the coordinate frame: `eᴵ_μ = ϑᴵ(∂_μ)`, `R^{KL}_{μν} = Ωᴷ_L(∂_μ, ∂_ν) η_{LL}` (index raised
with `η`), and the torsion `Tᴵ_{μν} = (dϑ + ω ∧ ϑ)ᴵ(∂_μ, ∂_ν)` computed from the coframe and the
connection by Cartan's first structure equation. -/
noncomputable def dsComp (H t : ℝ) : CartanComp where
  e I μ := coframe H t (cvec μ) I
  R K L μ ν := curvature H t (cvec μ) (cvec ν) K L * eta L L
  T I μ ν := (cvec μ).1 * deriv (fun s => coframe H s (cvec ν) I) t
      - (cvec ν).1 * deriv (fun s => coframe H s (cvec μ) I) t
      + ((connection H t (cvec μ)) *ᵥ (coframe H t (cvec ν))) I
      - ((connection H t (cvec ν)) *ᵥ (coframe H t (cvec μ))) I

/-- The torsion of the encoded data vanishes (`torsion_free`). -/
theorem dsComp_T (H t : ℝ) (I μ ν : Idx) : (dsComp H t).T I μ ν = 0 :=
  torsion_free H t (cvec μ) (cvec ν) I

theorem eta_mul_self (L : Idx) : eta L L * eta L L = 1 := by
  cases L <;> simp [eta]

/-- `R^{KL} = H² eᴷ ∧ eᴸ` for the encoded data (`eq:supp-desitter-curvature` with the second
index raised). -/
theorem dsComp_R (H t : ℝ) (K L μ ν : Idx) :
    (dsComp H t).R K L μ ν = H ^ 2 * ((dsComp H t).e K μ * (dsComp H t).e L ν
      - (dsComp H t).e K ν * (dsComp H t).e L μ) := by
  simp only [dsComp]
  rw [curvature_eq_desitter]
  have := eta_mul_self L
  linear_combination (H ^ 2 * (coframe H t (cvec μ) K * coframe H t (cvec ν) L
    - coframe H t (cvec ν) K * coframe H t (cvec μ) L)) * this

/-- Reindexing by the transposition of the last two slots flips the sign. -/
theorem sum_perm_swap23 (F : Equiv.Perm Idx → ℝ) :
    ∑ σ : Equiv.Perm Idx, ((Equiv.Perm.sign σ : ℤ) : ℝ)
        * F (σ * Equiv.swap (refIdx 2) (refIdx 3))
      = -∑ σ : Equiv.Perm Idx, ((Equiv.Perm.sign σ : ℤ) : ℝ) * F σ := by
  set τ := Equiv.swap (refIdx 2) (refIdx 3)
  have hτ : Equiv.Perm.sign τ = -1 :=
    Equiv.Perm.sign_swap (refIdx.injective.ne (by decide))
  have key := Equiv.sum_comp (Equiv.mulRight τ)
    (fun ρ => ((Equiv.Perm.sign (ρ * τ⁻¹) : ℤ) : ℝ) * F ρ)
  simp only [Equiv.coe_mulRight, mul_inv_cancel_right] at key
  rw [key, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, hτ]
  push_cast; ring

/-- `(a ∧ b ∧ (c ∧ d))(∂) = (a ∧ b ∧ c ∧ d)(∂)` with `(c ∧ d)(μ, ν) = c μ d ν − c ν d μ`. -/
theorem wedge112_wedge (a b c d : Idx → ℝ) :
    wedge112 a b (fun μ ν => c μ * d ν - c ν * d μ) = wedge4 a b c d := by
  have h0 : Equiv.swap (refIdx 2) (refIdx 3) (refIdx 0) = refIdx 0 :=
    Equiv.swap_apply_of_ne_of_ne (refIdx.injective.ne (by decide))
      (refIdx.injective.ne (by decide))
  have h1 : Equiv.swap (refIdx 2) (refIdx 3) (refIdx 1) = refIdx 1 :=
    Equiv.swap_apply_of_ne_of_ne (refIdx.injective.ne (by decide))
      (refIdx.injective.ne (by decide))
  have h2 : Equiv.swap (refIdx 2) (refIdx 3) (refIdx 2) = refIdx 3 := Equiv.swap_apply_left _ _
  have h3 : Equiv.swap (refIdx 2) (refIdx 3) (refIdx 3) = refIdx 2 := Equiv.swap_apply_right _ _
  have hs := sum_perm_swap23 fun ρ =>
    a (ρ (refIdx 0)) * b (ρ (refIdx 1)) * c (ρ (refIdx 2)) * d (ρ (refIdx 3))
  simp only [Equiv.Perm.mul_apply, h0, h1, h2, h3] at hs
  unfold wedge112 wedge4
  have e : ∀ σ : Equiv.Perm Idx, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
      (a (σ (refIdx 0)) * b (σ (refIdx 1)) *
        (c (σ (refIdx 2)) * d (σ (refIdx 3)) - c (σ (refIdx 3)) * d (σ (refIdx 2))))
      = ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          (a (σ (refIdx 0)) * b (σ (refIdx 1)) * c (σ (refIdx 2)) * d (σ (refIdx 3)))
        - ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          (a (σ (refIdx 0)) * b (σ (refIdx 1)) * c (σ (refIdx 3)) * d (σ (refIdx 2))) :=
    fun σ => by ring
  simp only [e, Finset.sum_sub_distrib, hs]
  ring

theorem wedge112_smul (a b : Idx → ℝ) (r : ℝ) (g : Idx → Idx → ℝ) :
    wedge112 a b (fun μ ν => r * g μ ν) = r * wedge112 a b g := by
  unfold wedge112
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => by ring

theorem wedge211_zero (a b : Idx → ℝ) : wedge211 (fun _ _ => 0) a b = 0 := by
  simp [wedge211]

/-- **Faithfulness check: de Sitter is stationary.**  With the cosmological coefficient tuned to
`c_V = −6 c_P H²` (i.e. `Λ = 3H²`, `G + Λ g = 0`, `eq:supp-desitter-einstein`) the
first-variation density of the encoded de Sitter data vanishes for every test value. -/
theorem firstVariationDensity_desitter_eq_zero (cP H t : ℝ) (u : TestVal) :
    firstVariationDensity cP (-6 * cP * H ^ 2) (dsComp H t) u = 0 := by
  unfold firstVariationDensity
  refine Finset.sum_eq_zero fun I _ => Finset.sum_eq_zero fun J _ =>
    Finset.sum_eq_zero fun K _ => Finset.sum_eq_zero fun L _ => ?_
  have hR : (dsComp H t).R K L = fun μ ν => H ^ 2 * ((dsComp H t).e K μ * (dsComp H t).e L ν
      - (dsComp H t).e K ν * (dsComp H t).e L μ) := by
    funext μ ν; exact dsComp_R H t K L μ ν
  have hT : (dsComp H t).T I = fun _ _ => 0 := by
    funext μ ν; exact dsComp_T H t I μ ν
  rw [hR, hT, wedge112_smul, wedge112_wedge, wedge211_zero]
  ring

/-- Sanity check: the Levi-Civita symbol is normalized, `ε_{0123} = 1` (so the encoded densities
are not identically zero). -/
theorem levi_ref : levi none (some 0) (some 1) (some 2) = 1 := by
  have hb : Function.Bijective (![none, some 0, some 1, some 2] : Fin 4 → Idx) := by
    have : (![none, some 0, some 1, some 2] : Fin 4 → Idx) = refIdx := by
      funext k; fin_cases k <;> rfl
    rw [this]; exact refIdx.bijective
  have hp : (Equiv.ofBijective _ hb).trans refIdx.symm = 1 := by
    ext k
    simp only [Equiv.trans_apply, Equiv.ofBijective_apply, Equiv.Perm.coe_one, id_eq]
    fin_cases k <;> rfl
  unfold levi
  rw [dite_cond_eq_true (eq_true hb), hp]
  simp

/-! ### Slab bounds for the de Sitter coefficients -/

theorem abs_exp_sub_exp_le {x y M : ℝ} (hx : x ≤ M) (hy : y ≤ M) :
    |Real.exp x - Real.exp y| ≤ Real.exp M * |x - y| := by
  have key : ∀ a b : ℝ, b ≤ a → a ≤ M → Real.exp a - Real.exp b ≤ Real.exp M * (a - b) := by
    intro a b hba haM
    have h1 := Real.add_one_le_exp (b - a)
    have h2 : Real.exp (b - a) * Real.exp a = Real.exp b := by rw [← Real.exp_add]; ring_nf
    have h3 : Real.exp a ≤ Real.exp M := Real.exp_le_exp.2 haM
    have h4 := Real.exp_pos a
    nlinarith
  rcases le_total y x with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 h)), abs_of_nonneg (sub_nonneg.2 h)]
    exact key x y h hx
  · rw [abs_of_nonpos (sub_nonpos.2 (Real.exp_le_exp.2 h)), abs_of_nonpos (sub_nonpos.2 h)]
    have := key y x h hy
    linarith

/-- Coefficient bound / Lipschitz constant of the de Sitter data on the slab `|t| ≤ T + 1`:
`42 B_T³` with `B_T = (|H| + 1) e^{|H|(T+1)}` (`slabScale`). -/
noncomputable def dsConst (H T : ℝ) : ℝ := 42 * slabScale H T ^ 3

theorem norm_curvX_le (V W : TVec) (hV : |V.1| ≤ 1) (hW : |W.1| ≤ 1) (hV2 : ‖V.2‖ ≤ 1)
    (hW2 : ‖W.2‖ ≤ 1) : ‖V.1 • boost W.2 - W.1 • boost V.2‖ ≤ 6 := by
  have h1 : ‖boost W.2‖ ≤ 3 := (norm_boost_le _).trans (by linarith)
  have h2 : ‖boost V.2‖ ≤ 3 := (norm_boost_le _).trans (by linarith)
  calc _ ≤ ‖V.1 • boost W.2‖ + ‖W.1 • boost V.2‖ := norm_sub_le _ _
    _ = |V.1| * ‖boost W.2‖ + |W.1| * ‖boost V.2‖ := by rw [norm_smul, norm_smul]; rfl
    _ ≤ 1 * 3 + 1 * 3 := by gcongr
    _ = 6 := by norm_num

theorem norm_curvY_le (V W : TVec) (hV2 : ‖V.2‖ ≤ 1) (hW2 : ‖W.2‖ ≤ 1) :
    ‖boost V.2 * boost W.2 - boost W.2 * boost V.2‖ ≤ 18 := by
  have h1 : ‖boost W.2‖ ≤ 3 := (norm_boost_le _).trans (by linarith)
  have h2 : ‖boost V.2‖ ≤ 3 := (norm_boost_le _).trans (by linarith)
  calc _ ≤ ‖boost V.2 * boost W.2‖ + ‖boost W.2 * boost V.2‖ := norm_sub_le _ _
    _ ≤ ‖boost V.2‖ * ‖boost W.2‖ + ‖boost W.2‖ * ‖boost V.2‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ 3 * 3 + 3 * 3 := by gcongr
    _ = 18 := by norm_num

theorem curvature_sub (H t s : ℝ) (V W : TVec) :
    curvature H t V W - curvature H s V W
      = (H ^ 2 * (Real.exp (H * t) - Real.exp (H * s))) • (V.1 • boost W.2 - W.1 • boost V.2)
        + (H ^ 2 * (Real.exp (2 * H * t) - Real.exp (2 * H * s)))
          • (boost V.2 * boost W.2 - boost W.2 * boost V.2) := by
  simp only [curvature]; module

theorem abs_entry_le_norm (M : Gen) (K L : Idx) : |M K L| ≤ ‖M‖ := by
  have h1 : ‖M K L‖₊ ≤ ∑ j, ‖M K j‖₊ :=
    Finset.single_le_sum (f := fun j => ‖M K j‖₊) (fun _ _ => by positivity) (Finset.mem_univ L)
  have h2 : ∑ j, ‖M K j‖₊ ≤ (Finset.univ : Finset Idx).sup fun i => ∑ j, ‖M i j‖₊ :=
    Finset.le_sup (f := fun i => ∑ j, ‖M i j‖₊) (Finset.mem_univ K)
  have h3 : ‖M K L‖₊ ≤ ‖M‖₊ := by rw [Matrix.linfty_opNNNorm_def]; exact h1.trans h2
  have := NNReal.coe_le_coe.2 h3
  simpa [Real.norm_eq_abs] using this

theorem abs_eta_diag (L : Idx) : |eta L L| = 1 := by
  cases L <;> simp [eta]

/-- Elementary slab facts: with `E = e^{|H|(T+1)}` and `B = (|H|+1)E`, for `|t| ≤ T + 1`. -/
theorem slab_facts (H T t : ℝ) (ht : |t| ≤ T + 1) :
    Real.exp (H * t) ≤ Real.exp (|H| * (T + 1)) ∧
      Real.exp (2 * H * t) ≤ Real.exp (|H| * (T + 1)) ^ 2 ∧
      slabScale H T = (|H| + 1) * Real.exp (|H| * (T + 1)) ∧
      1 ≤ Real.exp (|H| * (T + 1)) := by
  have hT : 0 ≤ T + 1 := (abs_nonneg t).trans ht
  have h1 : H * t ≤ |H| * (T + 1) :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left ht (abs_nonneg H))
  refine ⟨Real.exp_le_exp.2 h1, ?_, rfl, Real.one_le_exp (by positivity)⟩
  rw [← Real.exp_nat_mul]
  exact Real.exp_le_exp.2 (by push_cast; linarith)

theorem dsComp_bound (H T t : ℝ) (ht : |t| ≤ T + 1) : CompBound (dsConst H T) (dsComp H t) := by
  obtain ⟨hE1, hE2, hB, hE⟩ := slab_facts H T t ht
  set E := Real.exp (|H| * (T + 1))
  set B := slabScale H T
  have hH := abs_nonneg H
  have hB1 : 1 ≤ B := by rw [hB]; nlinarith
  have hEB : E ≤ B := by rw [hB]; nlinarith
  have hB2 : B ≤ B ^ 3 := by simpa using pow_le_pow_right₀ hB1 (by norm_num : 1 ≤ 3)
  have hexp := Real.exp_pos (H * t)
  have hexp2 := Real.exp_pos (2 * H * t)
  refine ⟨fun I μ => ?_, fun K L μ ν => ?_, fun I μ ν => ?_⟩
  · simp only [dsComp, coframe]
    cases I with
    | none =>
      simp only [Option.elim]
      have := abs_cvec_fst_le μ
      unfold dsConst; nlinarith
    | some a =>
      simp only [Option.elim]
      have hx : |(cvec μ).2 a| ≤ 1 := (norm_le_pi_norm (cvec μ).2 a).trans (norm_cvec_snd_le μ)
      rw [abs_mul, abs_of_pos hexp]
      have : Real.exp (H * t) * |(cvec μ).2 a| ≤ E * 1 := mul_le_mul hE1 hx (abs_nonneg _) (by linarith)
      unfold dsConst; nlinarith
  · simp only [dsComp]
    rw [abs_mul, abs_eta_diag, mul_one]
    refine (abs_entry_le_norm _ K L).trans ?_
    have hX := norm_curvX_le (cvec μ) (cvec ν) (abs_cvec_fst_le μ) (abs_cvec_fst_le ν)
      (norm_cvec_snd_le μ) (norm_cvec_snd_le ν)
    have hY := norm_curvY_le (cvec μ) (cvec ν) (norm_cvec_snd_le μ) (norm_cvec_snd_le ν)
    have hc : ‖curvature H t (cvec μ) (cvec ν)‖ ≤ H ^ 2 * Real.exp (H * t) * 6
        + H ^ 2 * Real.exp (2 * H * t) * 18 := by
      simp only [curvature]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]; gcongr
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]; gcongr
    refine hc.trans ?_
    have hH2 : H ^ 2 = |H| ^ 2 := (sq_abs H).symm
    rw [hH2]
    have k1 : |H| ^ 2 * Real.exp (H * t) ≤ B ^ 2 := by
      rw [hB]
      have : |H| ^ 2 * Real.exp (H * t) ≤ (|H| + 1) ^ 2 * E ^ 2 := by
        have : Real.exp (H * t) ≤ E ^ 2 := hE1.trans (by nlinarith)
        have h' : |H| ^ 2 ≤ (|H| + 1) ^ 2 := by nlinarith
        exact mul_le_mul h' this hexp.le (by positivity)
      nlinarith
    have k2 : |H| ^ 2 * Real.exp (2 * H * t) ≤ B ^ 2 := by
      rw [hB]
      have h' : |H| ^ 2 ≤ (|H| + 1) ^ 2 := by nlinarith
      have : |H| ^ 2 * Real.exp (2 * H * t) ≤ (|H| + 1) ^ 2 * E ^ 2 :=
        mul_le_mul h' hE2 hexp2.le (by positivity)
      nlinarith
    have hB23 : B ^ 2 ≤ B ^ 3 := by nlinarith
    unfold dsConst; nlinarith
  · rw [dsComp_T, abs_zero]; unfold dsConst; positivity

theorem dsComp_close (H T t s : ℝ) (ht : |t| ≤ T + 1) (hs : |s| ≤ T + 1) :
    CompClose (dsConst H T * |t - s|) (dsComp H t) (dsComp H s) := by
  obtain ⟨hE1, hE2, hB, hE⟩ := slab_facts H T t ht
  obtain ⟨hE1', hE2', -, -⟩ := slab_facts H T s hs
  set E := Real.exp (|H| * (T + 1))
  set B := slabScale H T
  have hH := abs_nonneg H
  have hB1 : 1 ≤ B := by rw [hB]; nlinarith
  have hts := abs_nonneg (t - s)
  have hM1 : H * t ≤ |H| * (T + 1) :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left ht (abs_nonneg H))
  have hM1' : H * s ≤ |H| * (T + 1) :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hs (abs_nonneg H))
  -- `|e^{Ht} − e^{Hs}| ≤ E |H| |t − s|`
  have hd1 : |Real.exp (H * t) - Real.exp (H * s)| ≤ E * (|H| * |t - s|) := by
    have := abs_exp_sub_exp_le hM1 hM1'
    rwa [← mul_sub, abs_mul] at this
  -- `|e^{2Ht} − e^{2Hs}| ≤ E² 2|H| |t − s|`
  have hd2 : |Real.exp (2 * H * t) - Real.exp (2 * H * s)| ≤ E ^ 2 * (2 * |H| * |t - s|) := by
    have h2 : 2 * H * t ≤ 2 * (|H| * (T + 1)) := by linarith
    have h2' : 2 * H * s ≤ 2 * (|H| * (T + 1)) := by linarith
    have := abs_exp_sub_exp_le h2 h2'
    have e1 : Real.exp (2 * (|H| * (T + 1))) = E ^ 2 := by
      rw [← Real.exp_nat_mul]; push_cast; ring_nf
    have e2 : 2 * H * t - 2 * H * s = (2 * H) * (t - s) := by ring
    rw [e1, e2, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at this
    linarith
  have hEB : E ≤ B := by rw [hB]; nlinarith
  have hHB : |H| * E ≤ B := by rw [hB]; nlinarith
  refine ⟨fun I μ => ?_, fun K L μ ν => ?_, fun I μ ν => ?_⟩
  · simp only [dsComp, coframe]
    cases I with
    | none => simp only [Option.elim, sub_self, abs_zero]; unfold dsConst; positivity
    | some a =>
      simp only [Option.elim]
      have hx : |(cvec μ).2 a| ≤ 1 := (norm_le_pi_norm (cvec μ).2 a).trans (norm_cvec_snd_le μ)
      rw [← sub_mul, abs_mul]
      have : |Real.exp (H * t) - Real.exp (H * s)| * |(cvec μ).2 a| ≤ E * (|H| * |t - s|) * 1 :=
        mul_le_mul hd1 hx (abs_nonneg _) (by positivity)
      have hB3 : B ≤ 42 * B ^ 3 := by
        have := pow_le_pow_right₀ hB1 (by norm_num : 1 ≤ 3); simp at this; linarith
      unfold dsConst
      nlinarith
  · simp only [dsComp]
    rw [← sub_mul, abs_mul, abs_eta_diag, mul_one, ← Matrix.sub_apply]
    refine (abs_entry_le_norm _ K L).trans ?_
    rw [curvature_sub]
    have hX := norm_curvX_le (cvec μ) (cvec ν) (abs_cvec_fst_le μ) (abs_cvec_fst_le ν)
      (norm_cvec_snd_le μ) (norm_cvec_snd_le ν)
    have hY := norm_curvY_le (cvec μ) (cvec ν) (norm_cvec_snd_le μ) (norm_cvec_snd_le ν)
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (sq_nonneg H)]
    have hH2 : H ^ 2 = |H| ^ 2 := (sq_abs H).symm
    rw [hH2]
    have t1 : |H| ^ 2 * |Real.exp (H * t) - Real.exp (H * s)|
          * ‖(cvec μ).1 • boost (cvec ν).2 - (cvec ν).1 • boost (cvec μ).2‖
        ≤ |H| ^ 2 * (E * (|H| * |t - s|)) * 6 := by gcongr
    have t2 : |H| ^ 2 * |Real.exp (2 * H * t) - Real.exp (2 * H * s)|
          * ‖boost (cvec μ).2 * boost (cvec ν).2 - boost (cvec ν).2 * boost (cvec μ).2‖
        ≤ |H| ^ 2 * (E ^ 2 * (2 * |H| * |t - s|)) * 18 := by gcongr
    have k : |H| ^ 3 * E ^ 2 ≤ B ^ 3 := by
      have : |H| * E ≤ B := hHB
      have hE' : 1 ≤ E := hE
      calc |H| ^ 3 * E ^ 2 ≤ (|H| * E) ^ 3 := by
            have : E ^ 2 ≤ E ^ 3 := by nlinarith
            calc |H| ^ 3 * E ^ 2 ≤ |H| ^ 3 * E ^ 3 := by gcongr
              _ = (|H| * E) ^ 3 := by ring
        _ ≤ B ^ 3 := by gcongr
    have k' : |H| ^ 3 * E ≤ B ^ 3 := by
      have : |H| ^ 3 * E ≤ |H| ^ 3 * E ^ 2 := by
        have : E ≤ E ^ 2 := by nlinarith
        gcongr
      linarith
    unfold dsConst
    nlinarith
  · rw [dsComp_T, dsComp_T, sub_self, abs_zero]; unfold dsConst; positivity

/-! ### Closeness bookkeeping -/

theorem CompClose.trans {d d' : ℝ} {F G G' : CartanComp} (h1 : CompClose d F G)
    (h2 : CompClose d' G G') : CompClose (d + d') F G' := by
  obtain ⟨a1, b1, c1⟩ := h1
  obtain ⟨a2, b2, c2⟩ := h2
  refine ⟨fun I μ => ?_, fun K L μ ν => ?_, fun I μ ν => ?_⟩
  · have := abs_sub_le (F.e I μ) (G.e I μ) (G'.e I μ); linarith [a1 I μ, a2 I μ]
  · have := abs_sub_le (F.R K L μ ν) (G.R K L μ ν) (G'.R K L μ ν)
    linarith [b1 K L μ ν, b2 K L μ ν]
  · have := abs_sub_le (F.T I μ ν) (G.T I μ ν) (G'.T I μ ν); linarith [c1 I μ ν, c2 I μ ν]

theorem CompClose.mono {d d' : ℝ} {F G : CartanComp} (h : CompClose d F G) (hd : d ≤ d') :
    CompClose d' F G := by
  obtain ⟨a, b, c⟩ := h
  exact ⟨fun I μ => (a I μ).trans hd, fun K L μ ν => (b K L μ ν).trans hd,
    fun I μ ν => (c I μ ν).trans hd⟩

theorem CompBound.of_close {B d : ℝ} {F G : CartanComp} (hF : CompBound B F)
    (h : CompClose d F G) : CompBound (B + d) G := by
  obtain ⟨a, b, c⟩ := hF
  obtain ⟨a', b', c'⟩ := h
  refine ⟨fun I μ => ?_, fun K L μ ν => ?_, fun I μ ν => ?_⟩
  · have := abs_sub_abs_le_abs_sub (G.e I μ) (F.e I μ)
    rw [abs_sub_comm] at this; linarith [a I μ, a' I μ]
  · have := abs_sub_abs_le_abs_sub (G.R K L μ ν) (F.R K L μ ν)
    rw [abs_sub_comm] at this; linarith [b K L μ ν, b' K L μ ν]
  · have := abs_sub_abs_le_abs_sub (G.T I μ ν) (F.T I μ ν)
    rw [abs_sub_comm] at this; linarith [c I μ ν, c' I μ ν]

theorem CompBound.mono {B B' : ℝ} {F : CartanComp} (h : CompBound B F) (hB : B ≤ B') :
    CompBound B' F := by
  obtain ⟨a, b, c⟩ := h
  exact ⟨fun I μ => (a I μ).trans hB, fun K L μ ν => (b K L μ ν).trans hB,
    fun I μ ν => (c I μ ν).trans hB⟩

/-! ### Test fields, slab, cell decompositions -/

/-- **Unit test fields**: all components bounded by `1` and `1`-Lipschitz (for the max norm on
`ℝ × ℝ³`).  This contains the `C¹` unit ball (`isUnitTest_of_contDiff`). -/
def IsUnitTest (u : TVec → TestVal) : Prop :=
  (∀ y, TestBound 1 (u y)) ∧ (∀ I μ, LipschitzWith 1 fun y => (u y).v I μ) ∧
    (∀ K L μ, LipschitzWith 1 fun y => (u y).w K L μ)

/-- Every test field with `C¹` norm at most one (`|v| ≤ 1`, `‖Dv‖ ≤ 1` componentwise) is a unit
test field. -/
theorem isUnitTest_of_contDiff (u : TVec → TestVal)
    (hv : ∀ I μ, Differentiable ℝ (fun y => (u y).v I μ) ∧
      ∀ y, |(u y).v I μ| ≤ 1 ∧ ‖fderiv ℝ (fun y => (u y).v I μ) y‖ ≤ 1)
    (hw : ∀ K L μ, Differentiable ℝ (fun y => (u y).w K L μ) ∧
      ∀ y, |(u y).w K L μ| ≤ 1 ∧ ‖fderiv ℝ (fun y => (u y).w K L μ) y‖ ≤ 1) :
    IsUnitTest u := by
  refine ⟨fun y => ⟨fun I μ => ((hv I μ).2 y).1, fun K L μ => ((hw K L μ).2 y).1⟩,
    fun I μ => ?_, fun K L μ => ?_⟩
  · refine lipschitzWith_of_nnnorm_fderiv_le (hv I μ).1 fun y => ?_
    have := ((hv I μ).2 y).2
    exact_mod_cast this
  · refine lipschitzWith_of_nnnorm_fderiv_le (hw K L μ).1 fun y => ?_
    have := ((hw K L μ).2 y).2
    exact_mod_cast this

theorem IsUnitTest.close {u : TVec → TestVal} (hu : IsUnitTest u) (y x : TVec) :
    TestClose (dist y x) (u y) (u x) := by
  obtain ⟨-, hv, hw⟩ := hu
  refine ⟨fun I μ => ?_, fun K L μ => ?_⟩
  · have := (hv I μ).dist_le_mul y x
    simpa [Real.dist_eq] using this
  · have := (hw K L μ).dist_le_mul y x
    simpa [Real.dist_eq] using this

theorem TestClose.mono {d d' : ℝ} {u u' : TestVal} (h : TestClose d u u') (hd : d ≤ d') :
    TestClose d' u u' :=
  ⟨fun I μ => (h.1 I μ).trans hd, fun K L μ => (h.2 K L μ).trans hd⟩

theorem TestBound.mono {B B' : ℝ} {u : TestVal} (h : TestBound B u) (hB : B ≤ B') :
    TestBound B' u :=
  ⟨fun I μ => (h.1 I μ).trans hB, fun K L μ => (h.2 K L μ).trans hB⟩

/-- The compact time slab `[−T, T] × D` over a spatial fundamental domain `D ⊆ ℝ³`. -/
def slab (T : ℝ) (D : Set (Fin 3 → ℝ)) : Set TVec := Icc (-T) T ×ˢ D

theorem volume_slab (T : ℝ) (hT : 0 ≤ T) (D : Set (Fin 3 → ℝ)) :
    volume (slab T D) = ENNReal.ofReal (2 * T) * volume D := by
  rw [slab, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
  congr 2; ring

theorem volume_slab_lt_top (T : ℝ) (hT : 0 ≤ T) {D : Set (Fin 3 → ℝ)} (hD : volume D < ⊤) :
    volume (slab T D) < ⊤ := by
  rw [volume_slab T hT]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hD

theorem volume_real_slab (T : ℝ) (hT : 0 ≤ T) (D : Set (Fin 3 → ℝ)) :
    volume.real (slab T D) = 2 * T * volume.real D := by
  simp only [Measure.real, volume_slab T hT, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 2 * T)]

/-- A finite measurable **cell decomposition** of a region `S` of mesh `δ`: pairwise disjoint
measurable cells covering `S`, each with a quadrature point within `δ` of all its points (e.g. the
cell midpoint of the product complex `K_h`, `δ = κ h`). -/
structure CellDecomp (ι : Type*) (S : Set TVec) (δ : ℝ) where
  /-- the (finite) set of cells -/
  cells : Finset ι
  /-- the cells -/
  cell : ι → Set TVec
  /-- the quadrature points -/
  point : ι → TVec
  meas : ∀ i ∈ cells, MeasurableSet (cell i)
  disj : Set.Pairwise (↑cells) (Function.onFun Disjoint cell)
  cover : ⋃ i ∈ cells, cell i = S
  near : ∀ i ∈ cells, ∀ y ∈ cell i, dist y (point i) ≤ δ

theorem CellDecomp.subset {ι : Type*} {S : Set TVec} {δ : ℝ} (P : CellDecomp ι S δ) {i : ι}
    (hi : i ∈ P.cells) : P.cell i ⊆ S := by
  exact (Set.subset_biUnion_of_mem (u := P.cell) hi).trans P.cover.subset

/-- The continuum first variation `δS[v] = ∫_S ρ(F(y), v(y)) dy`. -/
noncomputable def firstVariation (cP cV : ℝ) (F : TVec → CartanComp) (u : TVec → TestVal)
    (S : Set TVec) : ℝ :=
  ∫ y in S, firstVariationDensity cP cV (F y) (u y)

/-- The one-point (midpoint) quadrature `δS_h[v] = ∑_c |c| ρ(F_h(c), v(x_c))` with cell
coefficients `F_h(c)` (the cell writer). -/
noncomputable def quadratureVariation {ι : Type*} {S : Set TVec} {δ : ℝ} (cP cV : ℝ)
    (P : CellDecomp ι S δ) (Fh : ι → CartanComp) (u : TVec → TestVal) : ℝ :=
  ∑ i ∈ P.cells, volume.real (P.cell i) * firstVariationDensity cP cV (Fh i) (u (P.point i))

/-! ### Continuity of the de Sitter density -/

theorem continuous_firstVariationDensity {X : Type*} [TopologicalSpace X] (cP cV : ℝ)
    (F : X → CartanComp) (u : X → TestVal) (he : ∀ I μ, Continuous fun y => (F y).e I μ)
    (hR : ∀ K L μ ν, Continuous fun y => (F y).R K L μ ν)
    (hT : ∀ I μ ν, Continuous fun y => (F y).T I μ ν)
    (hv : ∀ I μ, Continuous fun y => (u y).v I μ)
    (hw : ∀ K L μ, Continuous fun y => (u y).w K L μ) :
    Continuous fun y => firstVariationDensity cP cV (F y) (u y) := by
  unfold firstVariationDensity wedge112 wedge4 wedge211
  refine continuous_finsetSum _ fun I _ => continuous_finsetSum _ fun J _ =>
    continuous_finsetSum _ fun K _ => continuous_finsetSum _ fun L _ => ?_
  refine continuous_const.mul (((continuous_const.mul (continuous_const.mul
    (continuous_finsetSum _ fun σ _ => continuous_const.mul ?_))).add
    (continuous_const.mul (continuous_finsetSum _ fun σ _ => continuous_const.mul ?_))).sub
    (continuous_const.mul (continuous_const.mul
    (continuous_finsetSum _ fun σ _ => continuous_const.mul ?_))))
  · exact ((hv _ _).mul (he _ _)).mul (hR _ _ _ _)
  · exact (((hv _ _).mul (he _ _)).mul (he _ _)).mul (he _ _)
  · exact ((hT _ _ _).mul (he _ _)).mul (hw _ _ _)

theorem continuous_dsComp_e (H : ℝ) (I μ : Idx) :
    Continuous fun y : TVec => (dsComp H y.1).e I μ := by
  simp only [dsComp, coframe]
  cases I with
  | none => exact continuous_const
  | some a => simp only [Option.elim]; fun_prop

theorem continuous_dsComp_R (H : ℝ) (K L μ ν : Idx) :
    Continuous fun y : TVec => (dsComp H y.1).R K L μ ν := by
  simp only [dsComp, curvature, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  fun_prop

theorem continuous_dsComp_T (H : ℝ) (I μ ν : Idx) :
    Continuous fun y : TVec => (dsComp H y.1).T I μ ν := by
  simp only [dsComp_T]; exact continuous_const

/-! ### The Palatini part of `eq:supp-finite-defect-bound` -/

/-- **Midpoint-quadrature consistency of the Palatini–cosmological first variation on a de Sitter
slab** (Palatini part of `eq:supp-finite-defect-bound`).  Let `D ⊆ ℝ³` be a measurable spatial
fundamental domain of finite volume, `T ≥ 0`, and `P` a finite measurable cell decomposition of
the slab `[−T, T] × D` whose points lie within `κh ≤ 1` of their quadrature point.  For every
cell writer `F_h` whose coefficients are within `ε ≤ 1` of the continuum de Sitter coefficients
at the quadrature point (`ε = 0`: the literal midpoint rule), every Palatini–cosmological
coefficient pair `(c_P, c_V)` and every unit test field,
`|δS_h[v] − δS[v]| ≤ L_T ((D_T + 1) κh + ε) |[−T,T] × D|`, with `D_T = 42 B_T³`,
`L_T = densityLip c_P c_V (D_T + 1)`; the constant is independent of `h` and of the
decomposition. -/
theorem abs_quadratureVariation_sub_firstVariation_le {ι : Type*} (H cP cV T κ h ε : ℝ)
    (hT : 0 ≤ T) (hκh0 : 0 ≤ κ * h) (hκh : κ * h ≤ 1) (hε0 : 0 ≤ ε) (hε : ε ≤ 1)
    {D : Set (Fin 3 → ℝ)} (hDfin : volume D < ⊤) (P : CellDecomp ι (slab T D) (κ * h))
    (Fh : ι → CartanComp)
    (hFh : ∀ i ∈ P.cells, (P.cell i).Nonempty → CompClose ε (dsComp H (P.point i).1) (Fh i))
    (u : TVec → TestVal) (hu : IsUnitTest u) :
    |quadratureVariation cP cV P Fh u - firstVariation cP cV (fun y => dsComp H y.1) u (slab T D)|
      ≤ densityLip cP cV (dsConst H T + 1) * ((dsConst H T + 1) * (κ * h) + ε)
        * volume.real (slab T D) := by
  set B' := dsConst H T + 1
  have hD0 : 0 ≤ dsConst H T := by unfold dsConst; have := one_le_slabScale H T hT; positivity
  have hB'0 : 0 ≤ B' := by positivity
  set η := densityLip cP cV B' * (B' * (κ * h) + ε)
  set f : TVec → ℝ := fun y => firstVariationDensity cP cV (dsComp H y.1) (u y)
  set q : ι → ℝ := fun i => firstVariationDensity cP cV (Fh i) (u (P.point i))
  -- per-cell estimate
  have hη : ∀ i ∈ P.cells, ∀ y ∈ P.cell i, |f y - q i| ≤ η := by
    intro i hi y hy
    have hyS := P.subset hi hy
    have hyt : |y.1| ≤ T := abs_le.2 ⟨hyS.1.1, hyS.1.2⟩
    have hdist := P.near i hi y hy
    have hdt : |y.1 - (P.point i).1| ≤ κ * h := by
      have := le_max_left (dist y.1 (P.point i).1) (dist y.2 (P.point i).2)
      rw [← Prod.dist_eq, Real.dist_eq] at this
      exact this.trans hdist
    have hxt : |(P.point i).1| ≤ T + 1 := by
      have := abs_sub_abs_le_abs_sub (P.point i).1 y.1
      rw [abs_sub_comm] at this; linarith
    have hyt' : |y.1| ≤ T + 1 := by linarith
    have hclose1 := dsComp_close H T y.1 (P.point i).1 hyt' hxt
    have hclose : CompClose (dsConst H T * (κ * h) + ε) (dsComp H y.1) (Fh i) :=
      (hclose1.mono (mul_le_mul_of_nonneg_left hdt hD0)).trans (hFh i hi ⟨y, hy⟩)
    have hbd1 : CompBound B' (dsComp H y.1) :=
      (dsComp_bound H T y.1 hyt').mono (by linarith)
    have hbd2 : CompBound B' (Fh i) :=
      ((dsComp_bound H T _ hxt).of_close (hFh i hi ⟨y, hy⟩)).mono (by linarith)
    have htu1 : TestBound B' (u y) := (hu.1 y).mono (by linarith)
    have htu2 : TestBound B' (u (P.point i)) := (hu.1 _).mono (by linarith)
    have hd : dsConst H T * (κ * h) + ε ≤ B' * (κ * h) + ε := by
      have : dsConst H T * (κ * h) ≤ B' * (κ * h) :=
        mul_le_mul_of_nonneg_right (by linarith) hκh0
      linarith
    have htc : TestClose (B' * (κ * h) + ε) (u y) (u (P.point i)) :=
      (hu.close y (P.point i)).mono (by nlinarith)
    exact abs_firstVariationDensity_sub_le cP cV hB'0 hbd1 hbd2 htu1 htu2 (hclose.mono hd) htc
  have hfin : ∀ i ∈ P.cells, volume (P.cell i) < ⊤ := fun i hi =>
    (measure_mono (P.subset hi)).trans_lt (volume_slab_lt_top T hT hDfin)
  have hcont : Continuous f := continuous_firstVariationDensity cP cV _ u
    (continuous_dsComp_e H) (continuous_dsComp_R H) (continuous_dsComp_T H)
    (fun I μ => (hu.2.1 I μ).continuous) (fun K L μ => (hu.2.2 K L μ).continuous)
  have hint : ∀ i ∈ P.cells, IntegrableOn f (P.cell i) volume := fun i hi =>
    Measure.integrableOn_of_bounded (hfin i hi).ne hcont.aestronglyMeasurable (M := |q i| + η)
      ((ae_restrict_iff' (P.meas i hi)).2 (Filter.Eventually.of_forall fun y hy => by
        have := hη i hi y hy
        have h2 := abs_sub_abs_le_abs_sub (f y) (q i)
        rw [Real.norm_eq_abs]; linarith))
  have key := CellQuadrature.abs_sum_sub_setIntegral_le volume P.cells P.cell P.meas P.disj
    hfin f hint q η hη
  rw [P.cover] at key
  exact key

/-- **Literal midpoint quadrature** (`ε = 0`): `|δS_h[v] − δS[v]| ≤ C_T h` with
`C_T = L_T (D_T + 1) κ · 2T |D|`. -/
theorem palatini_midpoint_slab_le {ι : Type*} (H cP cV T κ h : ℝ) (hT : 0 ≤ T)
    (hκh0 : 0 ≤ κ * h) (hκh : κ * h ≤ 1) {D : Set (Fin 3 → ℝ)} (hDfin : volume D < ⊤)
    (P : CellDecomp ι (slab T D) (κ * h)) (u : TVec → TestVal) (hu : IsUnitTest u) :
    |quadratureVariation cP cV P (fun i => dsComp H (P.point i).1) u
        - firstVariation cP cV (fun y => dsComp H y.1) u (slab T D)|
      ≤ densityLip cP cV (dsConst H T + 1) * (dsConst H T + 1) * κ * (2 * T * volume.real D)
        * h := by
  have hc : ∀ i ∈ P.cells, (P.cell i).Nonempty →
      CompClose 0 (dsComp H (P.point i).1) (dsComp H (P.point i).1) :=
    fun i _ _ => ⟨fun _ _ => by simp, fun _ _ _ _ => by simp, fun _ _ _ => by simp⟩
  have := abs_quadratureVariation_sub_firstVariation_le H cP cV T κ h 0 hT hκh0 hκh le_rfl
    zero_le_one hDfin P _ hc u hu
  rw [volume_real_slab T hT] at this
  refine this.trans (le_of_eq ?_)
  ring

/-- **Stationary regulators**: with the cosmological coefficient tuned to the regulator,
`c_V = −6 c_P H²` (`Λ = 3H²`; `c_V = 0` for the flat regulator `H = 0`), both the continuum
first variation and its midpoint quadrature vanish identically. -/
theorem palatini_tuned_eq_zero {ι : Type*} (H cP : ℝ) {S : Set TVec} {δ : ℝ}
    (P : CellDecomp ι S δ) (u : TVec → TestVal) :
    firstVariation cP (-6 * cP * H ^ 2) (fun y => dsComp H y.1) u S = 0 ∧
      quadratureVariation cP (-6 * cP * H ^ 2) P (fun i => dsComp H (P.point i).1) u = 0 := by
  constructor
  · simp only [firstVariation, firstVariationDensity_desitter_eq_zero, integral_zero]
  · simp only [quadratureVariation, firstVariationDensity_desitter_eq_zero, mul_zero,
      Finset.sum_const_zero]

/-- **Flat regulator**: for `H = 0` (and the flat cosmological coefficient `c_V = 0`) the
Palatini part of `eq:supp-finite-defect-bound` is zero. -/
theorem palatini_flat_eq_zero {ι : Type*} (cP : ℝ) {S : Set TVec} {δ : ℝ}
    (P : CellDecomp ι S δ) (u : TVec → TestVal) :
    quadratureVariation cP 0 P (fun i => dsComp 0 (P.point i).1) u
      - firstVariation cP 0 (fun y => dsComp 0 y.1) u S = 0 := by
  have h := palatini_tuned_eq_zero 0 cP P u
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h
  rw [h.1, h.2, sub_zero]

/-! ### Slab constants, diagonal summability, and the full defect bound -/

/-- The Palatini slab constant `C_T^P = L_T (D_T + 1) κ · 2T |D|` of `palatini_midpoint_slab_le`. -/
noncomputable def palatiniConst (H cP cV κ vD T : ℝ) : ℝ :=
  densityLip cP cV (dsConst H T + 1) * (dsConst H T + 1) * κ * (2 * T * vD)

theorem palatiniConst_nonneg (H cP cV κ vD T : ℝ) (hκ : 0 ≤ κ) (hvD : 0 ≤ vD) (hT : 0 ≤ T) :
    0 ≤ palatiniConst H cP cV κ vD T := by
  have hD0 : 0 ≤ dsConst H T := by unfold dsConst; have := one_le_slabScale H T hT; positivity
  unfold palatiniConst
  have := densityLip_nonneg cP cV (by linarith : 0 ≤ dsConst H T + 1)
  positivity

/-- At most exponential growth: `C_n^P ≤ K e^{(12|H| + 1) n}`. -/
theorem palatiniConst_le_exp (H cP cV κ vD : ℝ) (hκ : 0 ≤ κ) (hvD : 0 ≤ vD) (n : ℕ) :
    palatiniConst H cP cV κ vD n ≤
      (256 * (72 * |cP| + 16 * |cV|) * 43 ^ 4 * (|H| + 1) ^ 12 * Real.exp (12 * |H|)
        * (2 * κ * vD)) * Real.exp ((12 * |H| + 1) * n) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set S := slabScale H n with hSdef
  have hS1 : 1 ≤ S := one_le_slabScale H n hn
  set B' := dsConst H n + 1
  have hB'1 : 1 ≤ B' := by
    have : 0 ≤ dsConst H n := by unfold dsConst; positivity
    linarith
  have hB'S : B' ≤ 43 * S ^ 3 := by
    have : 1 ≤ S ^ 3 := one_le_pow₀ hS1
    simp only [B', dsConst]; linarith
  have hdL : densityLip cP cV B' ≤ 256 * (72 * |cP| + 16 * |cV|) * B' ^ 3 := by
    unfold densityLip
    have h23 : B' ^ 2 ≤ B' ^ 3 := pow_le_pow_right₀ hB'1 (by norm_num)
    have := abs_nonneg cP
    have := abs_nonneg cV
    nlinarith
  have hS12 : S ^ 12 = (|H| + 1) ^ 12 * Real.exp (12 * |H|) * Real.exp (12 * |H| * n) := by
    rw [hSdef, slabScale, mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    congr 2; push_cast; ring
  have hnexp : (n : ℝ) ≤ Real.exp n := by have := Real.add_one_le_exp (n : ℝ); linarith
  have hA : 0 ≤ 256 * (72 * |cP| + 16 * |cV|) := by positivity
  calc palatiniConst H cP cV κ vD n
      = densityLip cP cV B' * B' * (2 * κ * vD) * n := by unfold palatiniConst; ring
    _ ≤ 256 * (72 * |cP| + 16 * |cV|) * B' ^ 3 * B' * (2 * κ * vD) * n := by gcongr
    _ = 256 * (72 * |cP| + 16 * |cV|) * B' ^ 4 * (2 * κ * vD) * n := by ring
    _ ≤ 256 * (72 * |cP| + 16 * |cV|) * (43 * S ^ 3) ^ 4 * (2 * κ * vD) * Real.exp n := by
        gcongr
    _ = 256 * (72 * |cP| + 16 * |cV|) * 43 ^ 4 * S ^ 12 * (2 * κ * vD) * Real.exp n := by ring
    _ = _ := by
        rw [hS12, show (12 * |H| + 1) * (n : ℝ) = 12 * |H| * n + n by ring, Real.exp_add]
        ring

/-- The Palatini slab constants are summable along the diagonal exhaustion `h_n = 2^{−n²}`,
`T_n = n` (`eq:supp-defect-summability`, Palatini part). -/
theorem summable_palatiniConst_diagonal (H cP cV κ vD : ℝ) (hκ : 0 ≤ κ) (hvD : 0 ≤ vD) :
    Summable fun n : ℕ =>
      palatiniConst H cP cV κ vD n * RelationalDeSitterBranch.diagonalMesh n := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg
      (palatiniConst_nonneg H cP cV κ vD n hκ hvD (Nat.cast_nonneg n))
      (RelationalDeSitterBranch.diagonalMesh_pos n).le) (fun n => ?_)
    ((summable_exp_mul_diagonalMesh (12 * |H| + 1)).mul_left
      (256 * (72 * |cP| + 16 * |cV|) * 43 ^ 4 * (|H| + 1) ^ 12 * Real.exp (12 * |H|)
        * (2 * κ * vD)))
  have := palatiniConst_le_exp H cP cV κ vD hκ hvD n
  have hp := (RelationalDeSitterBranch.diagonalMesh_pos n).le
  calc palatiniConst H cP cV κ vD n * RelationalDeSitterBranch.diagonalMesh n
      ≤ ((256 * (72 * |cP| + 16 * |cV|) * 43 ^ 4 * (|H| + 1) ^ 12 * Real.exp (12 * |H|)
        * (2 * κ * vD)) * Real.exp ((12 * |H| + 1) * n))
          * RelationalDeSitterBranch.diagonalMesh n := mul_le_mul_of_nonneg_right this hp
    _ = _ := by ring

/-- The full constant `C_T = 2 C_T^{Cartan} + C_T^P` of `eq:supp-finite-defect-bound`. -/
noncomputable def finiteDefectConst (H cP cV κ vD T : ℝ) : ℝ :=
  2 * slabConst H κ T + palatiniConst H cP cV κ vD T

/-- **`thm:supp-finite-defects`, `eq:supp-finite-defect-bound` on a compact slab** (de Sitter
regulator with Hubble rate `H`; `H = 0` is the flat regulator).  For `T ≥ 0`, `κ ≥ 1`,
`0 < h ≤ h_T`, a finite-volume spatial domain `D`, every finite measurable cell decomposition `P`
of `[−T, T] × D` of mesh `κh` with midpoint quadrature, every unit test field `v`, every time
`|t| ≤ T`, and every shape-regular face `p` of the product complex at time `t` (closed spatial
polygons, edge × time-step rectangles):
`‖𝔯_p‖ + ‖𝔱_p‖ + |δS_h[v] − δS[v]| ≤ C_T h`, `C_T = finiteDefectConst`. -/
theorem finiteDefects_slab {ι : Type*} (H cP cV κ T : ℝ) (hκ : 1 ≤ κ) (hT : 0 ≤ T) {h : ℝ}
    (hh0 : 0 < h) (hh : h ≤ slabMesh H κ T) {D : Set (Fin 3 → ℝ)} (hDfin : volume D < ⊤)
    (P : CellDecomp ι (slab T D) (κ * h)) (u : TVec → TestVal) (hu : IsUnitTest u) {t : ℝ}
    (ht : |t| ≤ T) :
    let δ := |quadratureVariation cP cV P (fun i => dsComp H (P.point i).1) u
        - firstVariation cP cV (fun y => dsComp H y.1) u (slab T D)|
    (∀ (us : List (Fin 3 → ℝ)) (x xm : Fin 3 → ℝ) (area : ℝ), us.sum = 0 →
        (us.map fun u => ‖u‖).sum ≤ κ * h → ‖xm - x‖ ≤ κ * h → h ^ 2 / κ ≤ area →
        ‖curvatureDefect H t t (us.map spatialVec) area‖
          + ‖torsionDefect H t x t xm (us.map spatialVec) area‖ + δ
          ≤ finiteDefectConst H cP cV κ (volume.real D) T * h) ∧
    (∀ (w x : Fin 3 → ℝ) (area : ℝ), ‖w‖ ≤ κ * h → h ^ 2 / κ ≤ area →
        ‖curvatureDefect H t (t + h / 2) (mixedLoop h w) area‖
          + ‖torsionDefect H t x (t + h / 2) (x + (1 / 2 : ℝ) • w) (mixedLoop h w) area‖ + δ
          ≤ finiteDefectConst H cP cV κ (volume.real D) T * h) := by
  intro δ
  obtain ⟨c1, c2⟩ := curvatureDefect_slab_le H κ T hκ hT hh0 hh ht
  obtain ⟨t1, t2⟩ := torsionDefect_slab_le H κ T hκ hT hh0 hh ht
  have hB1 : 1 ≤ slabScale H T := one_le_slabScale H T hT
  have hκh : κ * h ≤ 1 := by
    have h24 : 0 < 24 * κ * slabScale H T := by positivity
    have := hh
    rw [slabMesh, le_div_iff₀ h24] at this
    nlinarith
  have hP : δ ≤ palatiniConst H cP cV κ (volume.real D) T * h := by
    have := palatini_midpoint_slab_le H cP cV T κ h hT (by positivity) hκh hDfin P u hu
    simpa [palatiniConst] using this
  refine ⟨fun us x xm area h0 hus hxm harea => ?_, fun w x area hw harea => ?_⟩
  · have := add_le_add (c1 us area h0 hus harea) (t1 us x xm area h0 hus hxm harea)
    unfold finiteDefectConst; linarith
  · have := add_le_add (c2 w area hw harea) (t2 w x area hw harea)
    unfold finiteDefectConst; linarith

/-- **`thm:supp-finite-defects`, diagonal exhaustion** (`eq:supp-diagonal-exhaustion`,
`eq:supp-defect-summability`): with `h_n = 2^{−n²}`, `T_n = n`, the full constants satisfy
`∑ₙ C_{T_n} h_n < ∞`, and `h_n ≤ h_{T_n}` for all large `n`, so `finiteDefects_slab` applies
along the exhaustion. -/
theorem finiteDefects_full_diagonal (H cP cV κ vD : ℝ) (hκ : 1 ≤ κ) (hvD : 0 ≤ vD) :
    Summable (fun n : ℕ =>
        finiteDefectConst H cP cV κ vD n * RelationalDeSitterBranch.diagonalMesh n) ∧
      ∃ N : ℕ, ∀ n ≥ N, RelationalDeSitterBranch.diagonalMesh n ≤ slabMesh H κ n := by
  obtain ⟨hs, hN⟩ := diagonal_exhaustion H κ hκ
  refine ⟨?_, hN⟩
  have h2 := (hs.mul_left 2).add (summable_palatiniConst_diagonal H cP cV κ vD (by linarith) hvD)
  refine h2.congr fun n => ?_
  unfold finiteDefectConst; ring

/-- **`thm:supp-finite-defects`, flat regulator**: all curvature and torsion defects of closed
loops and the Palatini quadrature defect (flat cosmological coefficient `c_V = 0`) vanish. -/
theorem finiteDefects_flat_full {ι : Type*} (cP t tm : ℝ) (x xm : Fin 3 → ℝ) (Vs : List TVec)
    (area : ℝ) (hclosed : Vs.sum = 0) {S : Set TVec} {δ : ℝ} (P : CellDecomp ι S δ)
    (u : TVec → TestVal) :
    curvatureDefect 0 t tm Vs area = 0 ∧ torsionDefect 0 t x tm xm Vs area = 0 ∧
      quadratureVariation cP 0 P (fun i => dsComp 0 (P.point i).1) u
        - firstVariation cP 0 (fun y => dsComp 0 y.1) u S = 0 :=
  ⟨(finiteDefects_flat t tm x xm Vs area hclosed).1,
    (finiteDefects_flat t tm x xm Vs area hclosed).2, palatini_flat_eq_zero cP P u⟩

/-! ### Non-vacuity -/

/-- The zero test field is a unit test field. -/
theorem isUnitTest_zero : IsUnitTest fun _ => ⟨fun _ _ => 0, fun _ _ _ => 0⟩ :=
  ⟨fun _ => ⟨fun _ _ => by simp, fun _ _ _ => by simp⟩,
    fun _ _ => (LipschitzWith.const 0).weaken zero_le_one,
    fun _ _ _ => (LipschitzWith.const 0).weaken zero_le_one⟩

/-- A smooth non-constant unit test field: `v⁰_0(t, x) = (sin t)/2`, all other components zero. -/
theorem isUnitTest_sin : IsUnitTest fun y =>
    ⟨fun I μ => if I = none ∧ μ = none then Real.sin y.1 / 2 else 0, fun _ _ _ => 0⟩ := by
  refine ⟨fun y => ⟨fun I μ => ?_, fun _ _ _ => by simp⟩, fun I μ => ?_,
    fun _ _ _ => (LipschitzWith.const 0).weaken zero_le_one⟩
  · dsimp only
    split_ifs
    · rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have := Real.abs_sin_le_one y.1
      linarith
    · simp
  · dsimp only
    by_cases hIμ : I = none ∧ μ = none
    · simp only [hIμ, and_self, ite_true]
      refine LipschitzWith.of_dist_le_mul fun y z => ?_
      rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have h1 := Real.abs_sin_sub_sin_le y.1 z.1
      have h2 : |y.1 - z.1| ≤ dist y z := by
        have := le_max_left (dist y.1 z.1) (dist y.2 z.2)
        rwa [← Prod.dist_eq, Real.dist_eq] at this
      have h3 := dist_nonneg (x := y) (y := z)
      simp only [NNReal.coe_one, one_mul]
      linarith
    · simp only [hIμ, ite_false]; exact (LipschitzWith.const 0).weaken zero_le_one

/-- Non-vacuity of the cell-decomposition hypothesis: the slab `[−h/2, h/2] × [0, h]³` is a single
cell of mesh `h` with quadrature point its midpoint. -/
noncomputable example (h : ℝ) (hh : 0 < h) :
    CellDecomp Unit (slab (h / 2) (Set.pi Set.univ fun _ => Icc 0 h)) (1 * h) where
  cells := {()}
  cell _ := slab (h / 2) (Set.pi Set.univ fun _ => Icc 0 h)
  point _ := (0, fun _ => h / 2)
  meas _ _ := measurableSet_Icc.prod (MeasurableSet.univ_pi fun _ => measurableSet_Icc)
  disj := by simp
  cover := by simp [Set.iUnion_const]
  near := by
    intro _ _ y hy
    obtain ⟨⟨h1, h2⟩, h3⟩ := hy
    rw [Prod.dist_eq, one_mul]
    refine max_le ?_ ?_
    · rw [Real.dist_eq, sub_zero, abs_le]; constructor <;> linarith
    · refine (dist_pi_le_iff hh.le).2 fun a => ?_
      obtain ⟨ha1, ha2⟩ := h3 a (Set.mem_univ a)
      rw [Real.dist_eq, abs_le]; constructor <;> linarith

/-! ### The finite holonomy writer

The cell writer built from the regulator data `(e_h, U_h)` themselves: in each coordinate plane
through the quadrature point `x_c = (t, x)` take the coordinate square of side `h` centred at
`x_c` (a closed spatial square at time `t`, or an edge × time-step rectangle from time `t − h/2`
to `t + h/2`), and read the curvature coefficient off its exact-link holonomy,
`R_h(∂_μ, ∂_ν) = −|p|⁻¹ log U_{∂p}`, and the torsion coefficient off its covariant developed-edge
closure `𝔱_p` (reference point `x_c`, the face midpoint).  The coframe is sampled at `x_c`. -/

/-- Unit coordinate vector `e_a` of `ℝ³`. -/
noncomputable def unitVec (a : Fin 3) : Fin 3 → ℝ := Pi.single a 1

theorem norm_unitVec (a : Fin 3) : ‖unitVec a‖ = 1 := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun b => ?_
    by_cases hb : b = a
    · subst hb; simp [unitVec]
    · simp [unitVec, hb]
  · have := norm_le_pi_norm (unitVec a) a
    simpa [unitVec] using this

theorem cvec_some (a : Fin 3) : cvec (some a) = (0, unitVec a) := rfl

/-- Edge vectors of the spatial coordinate square of side `h` in the `(a, b)` plane. -/
noncomputable def sqLoop (h : ℝ) (a b : Fin 3) : List (Fin 3 → ℝ) :=
  [h • unitVec a, h • unitVec b, -(h • unitVec a), -(h • unitVec b)]

theorem sqLoop_sum (h : ℝ) (a b : Fin 3) : (sqLoop h a b).sum = 0 := by
  simp [sqLoop]

theorem sqLoop_norm_sum (h : ℝ) (hh : 0 ≤ h) (a b : Fin 3) :
    ((sqLoop h a b).map fun u => ‖u‖).sum = 4 * h := by
  simp [sqLoop, norm_smul, norm_unitVec, abs_of_nonneg hh]; ring

theorem curvature_antisymm (H t : ℝ) (V W : TVec) :
    curvature H t V W = -curvature H t W V := by
  simp only [curvature]; module

theorem curvature_self (H t : ℝ) (V : TVec) : curvature H t V V = 0 := by
  have := curvature_antisymm H t V V
  have h2 : (2 : ℝ) • curvature H t V V = 0 := by rw [two_smul]; nth_rw 1 [this]; simp
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

theorem areaCurvature_sq (H t h : ℝ) (a b : Fin 3) :
    areaCurvature H t ((sqLoop h a b).map spatialVec)
      = (h ^ 2) • curvature H t (cvec (some a)) (cvec (some b)) := by
  ext K L
  simp only [sqLoop, List.map_cons, List.map_nil, areaCurvature, List.sum_cons, List.sum_nil,
    cvec_some]
  cases K <;> cases L <;>
    simp [curvature, Matrix.mul_apply, Fintype.sum_option, unitVec, Pi.single_apply] <;>
    split_ifs <;> subst_vars <;> first | ring1 | (simp_all; done) | (simp_all; ring1)

theorem areaCurvature_mixed_unit (H tm h : ℝ) (a : Fin 3) :
    areaCurvature H tm (mixedLoop h (h • unitVec a))
      = (h ^ 2) • curvature H tm (cvec (some a)) (cvec none) := by
  rw [areaCurvature_mixed]
  ext K L
  cases K <;> cases L <;>
    simp [curvature, cvec, Matrix.mul_apply, Fintype.sum_option, unitVec, Pi.single_apply] <;>
    split_ifs <;> simp <;> ring

/-- The holonomy curvature writer `R_h(∂_μ, ∂_ν) = −|p|⁻¹ log U_{∂p}` (as a mixed `Ωᴬ_B`
matrix) on the coordinate faces of side `h` centred at time `t`. -/
noncomputable def holR (H h t : ℝ) : Idx → Idx → Gen
  | some a, some b => if a = b then 0 else
      -(h ^ 2)⁻¹ • LogBCH.logOnePlus (loopHolonomy H t ((sqLoop h a b).map spatialVec) - 1)
  | some a, none =>
      -(h ^ 2)⁻¹ • LogBCH.logOnePlus (loopHolonomy H (t - h / 2) (mixedLoop h (h • unitVec a)) - 1)
  | none, some a =>
      (h ^ 2)⁻¹ • LogBCH.logOnePlus (loopHolonomy H (t - h / 2) (mixedLoop h (h • unitVec a)) - 1)
  | none, none => 0

/-- The developed-edge torsion writer: the normalized torsion defect `𝔱_p` of the coordinate
face of side `h` centred at `(t, x)` (reference point the face midpoint). -/
noncomputable def holT (H h t : ℝ) (x : Fin 3 → ℝ) : Idx → Idx → (Idx → ℝ)
  | some a, some b => if a = b then 0 else
      torsionDefect H t (x - (1 / 2 : ℝ) • (h • unitVec a + h • unitVec b)) t x
        ((sqLoop h a b).map spatialVec) (h ^ 2)
  | some a, none =>
      torsionDefect H (t - h / 2) (x - (1 / 2 : ℝ) • (h • unitVec a)) (t - h / 2 + h / 2)
        (x - (1 / 2 : ℝ) • (h • unitVec a) + (1 / 2 : ℝ) • (h • unitVec a))
        (mixedLoop h (h • unitVec a)) (h ^ 2)
  | none, some a =>
      -torsionDefect H (t - h / 2) (x - (1 / 2 : ℝ) • (h • unitVec a)) (t - h / 2 + h / 2)
        (x - (1 / 2 : ℝ) • (h • unitVec a) + (1 / 2 : ℝ) • (h • unitVec a))
        (mixedLoop h (h • unitVec a)) (h ^ 2)
  | none, none => 0

/-- The **finite holonomy writer** `F_h(c)` at the quadrature point `(t, x)`. -/
noncomputable def holComp (H h t : ℝ) (x : Fin 3 → ℝ) : CartanComp where
  e := (dsComp H t).e
  R K L μ ν := holR H h t μ ν K L * eta L L
  T I μ ν := holT H h t x μ ν I

theorem curvatureDefect_eq (H tb tm area : ℝ) (Vs : List TVec) (harea : area ≠ 0) {C : Gen}
    (hC : areaCurvature H tm Vs = area • C) :
    -area⁻¹ • LogBCH.logOnePlus (loopHolonomy H tb Vs - 1) - C
      = -curvatureDefect H tb tm Vs area := by
  rw [curvatureDefect, hC, smul_add, smul_smul, inv_mul_cancel₀ harea, one_smul, neg_smul]
  abel

/-- The holonomy writer is `C_T h`-accurate: every coefficient of `R_h` and `T_h` is within
`slabConst H κ T' · h` of the continuum coefficient at the quadrature point, for `κ ≥ 4`,
`0 < h ≤ h_{T'}` and `|t| + 1 ≤ T'`. -/
theorem holComp_close (H κ T' : ℝ) (hκ : 4 ≤ κ) (hT' : 0 ≤ T') {h : ℝ} (hh0 : 0 < h)
    (hh : h ≤ slabMesh H κ T') {t : ℝ} (ht : |t| + 1 ≤ T') (x : Fin 3 → ℝ) :
    CompClose (slabConst H κ T' * h) (dsComp H t) (holComp H h t x) := by
  have hκ1 : 1 ≤ κ := by linarith
  have hκ0 : 0 < κ := by linarith
  have hB1 := one_le_slabScale H T' hT'
  have hh1 : h ≤ 1 := by
    have h24 : 0 < 24 * κ * slabScale H T' := by positivity
    have := hh
    rw [slabMesh, le_div_iff₀ h24] at this
    nlinarith
  have htT : |t| ≤ T' := by linarith [abs_nonneg t]
  have htT2 : |t - h / 2| ≤ T' := by
    have := abs_sub (t) (h / 2)
    rw [abs_of_pos (by positivity : 0 < h / 2)] at this
    linarith
  obtain ⟨cs, -⟩ := curvatureDefect_slab_le H κ T' hκ1 hT' hh0 hh htT
  obtain ⟨-, cm⟩ := curvatureDefect_slab_le H κ T' hκ1 hT' hh0 hh htT2
  obtain ⟨ts, -⟩ := torsionDefect_slab_le H κ T' hκ1 hT' hh0 hh htT
  obtain ⟨-, tm⟩ := torsionDefect_slab_le H κ T' hκ1 hT' hh0 hh htT2
  have hC0 : 0 ≤ slabConst H κ T' * h := by unfold slabConst; positivity
  have harea : h ^ 2 / κ ≤ h ^ 2 := div_le_self (by positivity) hκ1
  have hh2 : h ^ 2 ≠ 0 := by positivity
  have hua : ∀ a : Fin 3, ‖h • unitVec a‖ ≤ κ * h := fun a => by
    rw [norm_smul, norm_unitVec, Real.norm_eq_abs, abs_of_pos hh0, mul_one]; nlinarith
  have hsq : ∀ a b : Fin 3, ((sqLoop h a b).map fun u => ‖u‖).sum ≤ κ * h := fun a b => by
    rw [sqLoop_norm_sum h hh0.le]; nlinarith
  have hmid : t - h / 2 + h / 2 = t := by ring
  -- curvature: matrix-level accuracy
  have hR : ∀ μ ν : Idx, ‖curvature H t (cvec μ) (cvec ν) - holR H h t μ ν‖
      ≤ slabConst H κ T' * h := by
    intro μ ν
    cases μ with
    | none =>
      cases ν with
      | none => simp [holR, curvature_self, hC0]
      | some a =>
        have hc := cm (h • unitVec a) (h ^ 2) (hua a) harea
        have e := curvatureDefect_eq H (t - h / 2) (t - h / 2 + h / 2) (h ^ 2)
          (mixedLoop h (h • unitVec a)) hh2 (areaCurvature_mixed_unit H _ h a)
        rw [hmid] at e
        simp only [holR]
        rw [curvature_antisymm]
        have : -curvature H t (cvec (some a)) (cvec none) - (h ^ 2)⁻¹ • LogBCH.logOnePlus
            (loopHolonomy H (t - h / 2) (mixedLoop h (h • unitVec a)) - 1)
            = -(h ^ 2)⁻¹ • LogBCH.logOnePlus
              (loopHolonomy H (t - h / 2) (mixedLoop h (h • unitVec a)) - 1)
              - curvature H t (cvec (some a)) (cvec none) := by
          rw [neg_smul]; abel
        rw [this, e, norm_neg]
        rw [hmid] at hc; exact hc
    | some a =>
      cases ν with
      | none =>
        have hc := cm (h • unitVec a) (h ^ 2) (hua a) harea
        have e := curvatureDefect_eq H (t - h / 2) (t - h / 2 + h / 2) (h ^ 2)
          (mixedLoop h (h • unitVec a)) hh2 (areaCurvature_mixed_unit H _ h a)
        simp only [holR]
        rw [hmid] at e hc
        rw [← norm_neg, neg_sub, e, norm_neg]; exact hc
      | some b =>
        by_cases hab : a = b
        · subst hab; simp [holR, curvature_self, hC0]
        · have hc := cs (sqLoop h a b) (h ^ 2) (sqLoop_sum h a b) (hsq a b) harea
          have e := curvatureDefect_eq H t t (h ^ 2) ((sqLoop h a b).map spatialVec) hh2
            (areaCurvature_sq H t h a b)
          simp only [holR, hab, if_false]
          rw [← norm_neg, neg_sub, e, norm_neg]; exact hc
  -- torsion: vector-level accuracy
  have hT : ∀ μ ν : Idx, ‖holT H h t x μ ν‖ ≤ slabConst H κ T' * h := by
    intro μ ν
    cases μ with
    | none =>
      cases ν with
      | none => simp [holT, hC0]
      | some a =>
        simp only [holT, norm_neg]
        exact tm (h • unitVec a) _ (h ^ 2) (hua a) harea
    | some a =>
      cases ν with
      | none => exact tm (h • unitVec a) _ (h ^ 2) (hua a) harea
      | some b =>
        by_cases hab : a = b
        · subst hab; simp [holT, hC0]
        · simp only [holT, hab, if_false]
          refine ts (sqLoop h a b) _ x (h ^ 2) (sqLoop_sum h a b) (hsq a b) ?_ harea
          rw [sub_sub_cancel, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
          have := norm_add_le (h • unitVec a) (h • unitVec b)
          nlinarith [hua a, hua b]
  refine ⟨fun I μ => by simp [holComp, hC0], fun K L μ ν => ?_, fun I μ ν => ?_⟩
  · simp only [dsComp, holComp]
    rw [← sub_mul, abs_mul, abs_eta_diag, mul_one, ← Matrix.sub_apply]
    exact (abs_entry_le_norm _ K L).trans (hR μ ν)
  · rw [dsComp_T, zero_sub, abs_neg]
    simp only [holComp]
    exact (norm_le_pi_norm (holT H h t x μ ν) I).trans (hT μ ν)

/-- **Palatini part with the finite holonomy writer**: replacing the curvature and torsion
coefficients at each quadrature point by the exact-link face holonomies and developed-edge
closures of the coordinate faces through it (`holComp`) still gives
`|δS_h[v] − δS[v]| ≤ L_T ((D_T + 1) κh + C_{T+2} h) |[−T, T] × D|`, for `κ ≥ 4`,
`0 < h ≤ h_{T+2}` and `C_{T+2} h ≤ 1`. -/
theorem palatini_holonomyWriter_slab_le {ι : Type*} (H cP cV T κ h : ℝ) (hT : 0 ≤ T)
    (hκ : 4 ≤ κ) (hh0 : 0 < h) (hh : h ≤ slabMesh H κ (T + 2))
    (hC : slabConst H κ (T + 2) * h ≤ 1) {D : Set (Fin 3 → ℝ)} (hDfin : volume D < ⊤)
    (P : CellDecomp ι (slab T D) (κ * h)) (u : TVec → TestVal) (hu : IsUnitTest u) :
    |quadratureVariation cP cV P (fun i => holComp H h (P.point i).1 (P.point i).2) u
        - firstVariation cP cV (fun y => dsComp H y.1) u (slab T D)|
      ≤ densityLip cP cV (dsConst H T + 1)
          * ((dsConst H T + 1) * (κ * h) + slabConst H κ (T + 2) * h)
          * volume.real (slab T D) := by
  have hB1 := one_le_slabScale H (T + 2) (by linarith)
  have hκh : κ * h ≤ 1 := by
    have h24 : 0 < 24 * κ * slabScale H (T + 2) := by positivity
    have := hh
    rw [slabMesh, le_div_iff₀ h24] at this
    nlinarith
  have hC0 : 0 ≤ slabConst H κ (T + 2) * h := by unfold slabConst; positivity
  refine abs_quadratureVariation_sub_firstVariation_le H cP cV T κ h _ hT (by positivity) hκh hC0
    hC hDfin P _ (fun i hi hne => ?_) u hu
  obtain ⟨y, hy⟩ := hne
  have hyS := P.subset hi hy
  have hyt : |y.1| ≤ T := abs_le.2 ⟨hyS.1.1, hyS.1.2⟩
  have hdt : |y.1 - (P.point i).1| ≤ κ * h := by
    have := le_max_left (dist y.1 (P.point i).1) (dist y.2 (P.point i).2)
    rw [← Prod.dist_eq, Real.dist_eq] at this
    exact this.trans (P.near i hi y hy)
  have hxt : |(P.point i).1| + 1 ≤ T + 2 := by
    have := abs_sub_abs_le_abs_sub (P.point i).1 y.1
    rw [abs_sub_comm] at this; linarith
  exact holComp_close H κ (T + 2) hκ (by linarith) hh0 hh hxt _

end RenewalGeometry.DeSitterExactLink.Palatini
