/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.SMDescentYukawaBlocksExact

/-!
# Exact determinant normalization and semisimple remainder: the group-algebraic core
  (`prop:native-determinant-split`, Einstein–SM action closure)

The exact finite group algebra behind `prop:native-determinant-split`, in
`G_SM = S(U(3) × U(2))` (`SMGaugeGroup`) on an arbitrary lattice (`shift : X → D → X`).

* `centralElem t = e^{tZ_c} = (e^{-it/3} I₃, e^{it/2} I₂)`, `Z_c = (-i/3 I₃, i/2 I₂)`:
  a central one-parameter subgroup (`centralElem_add`, `centralElem_comm`) with
  `χ(e^{tZ_c}) = e^{it}` (`smChi_centralElem`) and `exp(s Z_c) = e^{sZ_c}`
  (`exp_Zc_fst`, `exp_Zc_snd`, matrix exponential).
* `zSix = e^{2πZ_c} = (e^{-2πi/3} I₃, -I₂)` lies in `G_ss` and `z₆⁶ = 1`
  (`zSix_components`, `zSix_mem_ss_pow_six`); `e^{(t+2πk)Z_c} = z₆^k e^{tZ_c}`.
* `splitLinks` is `V = e^{-h a Z_c} U^{e^{tZ_c}}` (`eq:determinant-exact-split`):
  `χ(V) = 1` from the Abelian normalization (`smChi_splitLinks`), the exact plaquette relation
  `P_{U'} = e^{h(d_h a)hZ_c} P_V` (`plaq_split`), `Ad V = Ad U'` (`ad_splitLinks`,
  `ad_matrix_splitLinks`), and the lift change by central `G_ss` site gauges
  (`splitLinks_lift_change`).
* `ℓ_c`, `Π_ss` (`eq:determinant-projections`): `ℓ_c(Z_c) = 1`, `Π_ss` idempotent and
  linear; a logarithm `L` of `P_{U'}` with `ℓ_c(L) = h²f` gives the logarithm `Π_ss L` of
  `P_V` (`exp_piSS`), unique on any injectivity chart (`chartLog_piSS`); entrywise
  `‖Π_ss L‖ ≤ 2‖L‖` (`piSS_entry_le`).
* `native_determinant_split_core` assembles these.

Not formalised here (inputs of the proposition taken as hypotheses): the construction of
`s_h, a_h` and `d_h a_h = f_h` (`prop:periodic-determinant-normalization`), the eventual
admissibility of the logarithms and `f_h = ℓ_c(𝔽_h)` (`lem:determinant-screen-flux`;
`det exp = exp tr` is not in Mathlib), and the rooted-certificate invariance
(`prop:rooted-gauge-certificate`).
-/

open Matrix

namespace RenewalGeometry

namespace DeterminantSplit

open SMDescentYukawa

noncomputable section

/-! ### The central one-parameter subgroup `t ↦ e^{t Z_c}` -/

/-- `e^{t Z_c} = (e^{-it/3} I₃, e^{it/2} I₂) ∈ S(U(3) × U(2))`, `Z_c = (-i/3 I₃, i/2 I₂)`. -/
def centralElem (t : ℝ) : SMGaugeGroup :=
  ⟨(phaseUnitary (Fin 3) (Circle.exp (-t / 3)), phaseUnitary (Fin 2) (Circle.exp (t / 2))), by
    apply Subtype.ext
    change ((Circle.exp (-t / 3) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)).det *
      ((Circle.exp (t / 2) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = 1
    rw [Matrix.det_smul, Matrix.det_smul, Matrix.det_one, Matrix.det_one, Fintype.card_fin,
      Fintype.card_fin, mul_one, mul_one, Circle.coe_exp, Circle.coe_exp, ← Complex.exp_nat_mul,
      ← Complex.exp_nat_mul, ← Complex.exp_add]
    convert Complex.exp_zero using 2
    push_cast
    ring⟩

theorem centralElem_U3 (t : ℝ) :
    smU3 (centralElem t) = (Complex.exp (-(t / 3) * Complex.I)) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  simp only [smU3_apply, centralElem, phaseUnitary_val, Circle.coe_exp]
  congr 2
  push_cast
  ring

theorem centralElem_U2 (t : ℝ) :
    smU2 (centralElem t) = (Complex.exp ((t / 2) * Complex.I)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp only [smU2_apply, centralElem, phaseUnitary_val, Circle.coe_exp]
  congr 2
  push_cast
  ring

theorem smGauge_ext {y y' : SMGaugeGroup} (h3 : smU3 y = smU3 y') (h2 : smU2 y = smU2 y') :
    y = y' :=
  Subtype.ext (Prod.ext (Subtype.ext h3) (Subtype.ext h2))

theorem centralElem_add (s t : ℝ) : centralElem (s + t) = centralElem s * centralElem t := by
  apply smGauge_ext
  · rw [map_mul, centralElem_U3, centralElem_U3, centralElem_U3, smul_mul_smul_comm, one_mul,
      ← Complex.exp_add]
    congr 2
    push_cast
    ring
  · rw [map_mul, centralElem_U2, centralElem_U2, centralElem_U2, smul_mul_smul_comm, one_mul,
      ← Complex.exp_add]
    congr 2
    push_cast
    ring

theorem centralElem_zero : centralElem 0 = 1 := by
  apply smGauge_ext
  · rw [centralElem_U3, map_one]; simp
  · rw [centralElem_U2, map_one]; simp

theorem centralElem_neg (t : ℝ) : (centralElem t)⁻¹ = centralElem (-t) := by
  rw [inv_eq_iff_mul_eq_one, ← centralElem_add, show t + -t = 0 by ring, centralElem_zero]

/-- `e^{t Z_c}` is central in `G_SM`. -/
theorem centralElem_comm (t : ℝ) (y : SMGaugeGroup) : centralElem t * y = y * centralElem t := by
  apply smGauge_ext
  · rw [map_mul, map_mul, centralElem_U3, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  · rw [map_mul, map_mul, centralElem_U2, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]

/-- `χ(e^{t Z_c}) = e^{it}` (`eq:determinant-character`). -/
theorem smChi_centralElem (t : ℝ) : smChi (centralElem t) = Complex.exp (t * Complex.I) := by
  rw [smChi_apply, centralElem_U2, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one,
    ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The central one-parameter subgroup as a homomorphism `ℝ → G_SM`. -/
def centralHom : Multiplicative ℝ →* SMGaugeGroup :=
  MonoidHom.mk' (fun s => centralElem s.toAdd) (fun s t => centralElem_add _ _)

theorem centralElem_zsmul (k : ℤ) (s : ℝ) : centralElem (k * s) = (centralElem s) ^ k := by
  have := map_zpow centralHom (Multiplicative.ofAdd s) k
  simpa [centralHom, ← ofAdd_zsmul, zsmul_eq_mul] using this

/-! ### `z₆ = e^{2π Z_c}` (`eq:determinant-central-six`) -/

/-- `z₆ = e^{2π Z_c}`. -/
def zSix : SMGaugeGroup := centralElem (2 * Real.pi)

theorem zSix_components :
    smU3 zSix = Complex.exp (-(2 * Real.pi * Complex.I / 3)) • (1 : Matrix (Fin 3) (Fin 3) ℂ) ∧
      smU2 zSix = -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  refine ⟨?_, ?_⟩
  · rw [zSix, centralElem_U3]
    congr 2
    push_cast
    ring
  · rw [zSix, centralElem_U2]
    have : Complex.exp (((2 * Real.pi : ℝ) : ℂ) / 2 * Complex.I) = -1 := by
      rw [show ((2 * Real.pi : ℝ) : ℂ) / 2 * Complex.I = Real.pi * Complex.I by push_cast; ring,
        Complex.exp_pi_mul_I]
    rw [this, neg_one_smul]

/-- `z₆ ∈ G_ss = ker χ` and `z₆⁶ = 1`. -/
theorem zSix_mem_ss_pow_six : smChi zSix = 1 ∧ zSix ^ 6 = 1 := by
  refine ⟨?_, ?_⟩
  · rw [zSix, smChi_centralElem]
    have : ((2 * Real.pi : ℝ) : ℂ) * Complex.I = 2 * Real.pi * Complex.I := by push_cast; ring
    rw [this, Complex.exp_two_pi_mul_I]
  · have h6 : zSix ^ 6 = centralElem (((6 : ℤ) : ℝ) * (2 * Real.pi)) := by
      rw [centralElem_zsmul, zSix]
      exact (zpow_natCast _ 6).symm
    rw [h6]
    apply smGauge_ext
    · rw [centralElem_U3, map_one]
      have : Complex.exp (-(((((6 : ℤ) : ℝ) * (2 * Real.pi) : ℝ) : ℂ) / 3) * Complex.I) = 1 := by
        rw [show -(((((6 : ℤ) : ℝ) * (2 * Real.pi) : ℝ) : ℂ) / 3) * Complex.I =
          ((-2 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
        exact Complex.exp_int_mul_two_pi_mul_I (-2)
      rw [this, one_smul]
    · rw [centralElem_U2, map_one]
      have : Complex.exp ((((((6 : ℤ) : ℝ) * (2 * Real.pi) : ℝ) : ℂ) / 2) * Complex.I) = 1 := by
        rw [show (((((6 : ℤ) : ℝ) * (2 * Real.pi) : ℝ) : ℂ) / 2) * Complex.I =
          ((3 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
        exact Complex.exp_int_mul_two_pi_mul_I 3
      rw [this, one_smul]

/-! ### Links, gauge transforms and plaquettes on a finite lattice -/

section Lattice

variable {X D : Type*} (shift : X → D → X)

/-- Site gauge transform `U^g_μ(x) = g(x) U_μ(x) g(x + h e_μ)⁻¹`. -/
def gaugeTr (g : X → SMGaugeGroup) (U : X → D → SMGaugeGroup) (x : X) (μ : D) : SMGaugeGroup :=
  g x * U x μ * (g (shift x μ))⁻¹

/-- Oriented plaquette `U_μ(x) U_ν(x+μ) U_μ(x+ν)⁻¹ U_ν(x)⁻¹`. -/
def plaq (U : X → D → SMGaugeGroup) (x : X) (μ ν : D) : SMGaugeGroup :=
  U x μ * U (shift x μ) ν * (U (shift x ν) μ)⁻¹ * (U x ν)⁻¹

/-- The construction `eq:determinant-exact-split`: `g_h = e^{t_h Z_c}`, `U' = U^{g_h}`,
`V_μ = e^{-h a_μ Z_c} U'_μ`. -/
def splitLinks (h : ℝ) (t : X → ℝ) (a : X → D → ℝ) (U : X → D → SMGaugeGroup) (x : X)
    (μ : D) : SMGaugeGroup :=
  centralElem (-(h * a x μ)) * gaugeTr shift (fun x => centralElem (t x)) U x μ

/-- Discrete curl `h (d_h a)_{μν}(x) = a_μ(x) + a_ν(x+μ) - a_μ(x+ν) - a_ν(x)`. -/
def curl (a : X → D → ℝ) (x : X) (μ ν : D) : ℝ :=
  a x μ + a (shift x μ) ν - a (shift x ν) μ - a x ν

theorem central_move (s : ℝ) (y z : SMGaugeGroup) :
    y * (centralElem s * z) = centralElem s * (y * z) := by
  rw [← mul_assoc, ← centralElem_comm, mul_assoc]

/-- A plaquette of centrally rescaled links. -/
theorem plaq_central (α β γ δ : ℝ) (u₁ u₂ u₃ u₄ : SMGaugeGroup) :
    (centralElem α * u₁) * (centralElem β * u₂) * (centralElem γ * u₃)⁻¹ *
        (centralElem δ * u₄)⁻¹ =
      centralElem (α + β - γ - δ) * (u₁ * u₂ * u₃⁻¹ * u₄⁻¹) := by
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, centralElem_neg, centralElem_neg]
  simp only [mul_assoc]
  rw [← centralElem_comm (-δ) u₄⁻¹, central_move (-γ) u₃⁻¹, central_move (-δ) u₃⁻¹,
    central_move (-γ) u₂, central_move (-δ) u₂, central_move β u₁, central_move (-γ) u₁,
    central_move (-δ) u₁, show α + β - γ - δ = α + (β + (-γ + -δ)) by ring]
  simp only [← mul_assoc, ← centralElem_add]

/-- **`V_h ∈ G_ss` exactly.**  If the determinant links are normalized,
`e^{i t(x)} χ(U_μ(x)) e^{-i t(x+μ)} = e^{i h a_μ(x)}` (the conclusion
`u^{s_h} = e^{i h a_h}` of `prop:periodic-determinant-normalization` with `s_h = e^{i t_h}`),
then `χ(V_μ(x)) = 1`. -/
theorem smChi_splitLinks (h : ℝ) (t : X → ℝ) (a : X → D → ℝ) (U : X → D → SMGaugeGroup)
    (hN : ∀ x μ, Complex.exp (t x * Complex.I) * smChi (U x μ) *
      Complex.exp (-(t (shift x μ) * Complex.I)) = Complex.exp (h * a x μ * Complex.I))
    (x : X) (μ : D) : smChi (splitLinks shift h t a U x μ) = 1 := by
  simp only [splitLinks, gaugeTr, map_mul, map_inv, smChi_centralElem]
  rw [← Complex.exp_neg, hN x μ, ← Complex.exp_add]
  convert Complex.exp_zero using 2
  push_cast
  ring

/-- `χ = 1` forces both determinants to be one: `V ∈ SU(3) × SU(2)`. -/
theorem det_eq_one_of_smChi (y : SMGaugeGroup) (hy : smChi y = 1) :
    (smU3 y).det = 1 ∧ (smU2 y).det = 1 := by
  have hprod : (smU3 y).det * (smU2 y).det = 1 := by
    have h := congrArg Subtype.val y.2
    simpa [determinantProductHom, unitaryDetHom] using h
  rw [smChi_apply] at hy
  rw [hy, mul_one] at hprod
  exact ⟨hprod, hy⟩

/-- **Exact plaquette relation** `P_{U',μν} = e^{h (d_h a)_{μν} h Z_c} P_{V,μν}`; with
`d_h a_h = f_h` (from `prop:periodic-determinant-normalization`) this is
`P_{U'} = e^{h² f Z_c} P_V`. -/
theorem plaq_split (h : ℝ) (t : X → ℝ) (a : X → D → ℝ) (U : X → D → SMGaugeGroup)
    (x : X) (μ ν : D) :
    plaq shift (gaugeTr shift (fun x => centralElem (t x)) U) x μ ν =
      centralElem (h * curl shift a x μ ν) * plaq shift (splitLinks shift h t a U) x μ ν := by
  unfold plaq splitLinks
  rw [plaq_central, ← mul_assoc, ← centralElem_add]
  have : h * curl shift a x μ ν + (-(h * a x μ) + -(h * a (shift x μ) ν) -
      -(h * a (shift x ν) μ) - -(h * a x ν)) = 0 := by
    unfold curl; ring
  rw [this, centralElem_zero, one_mul]

/-- **Adjoint Wilson transport**: `Ad(V_μ(x)) = Ad(U'_μ(x))` on `G_SM`. -/
theorem ad_splitLinks (h : ℝ) (t : X → ℝ) (a : X → D → ℝ) (U : X → D → SMGaugeGroup)
    (x : X) (μ : D) (w : SMGaugeGroup) :
    splitLinks shift h t a U x μ * w * (splitLinks shift h t a U x μ)⁻¹ =
      gaugeTr shift (fun x => centralElem (t x)) U x μ * w *
        (gaugeTr shift (fun x => centralElem (t x)) U x μ)⁻¹ := by
  unfold splitLinks
  set u := gaugeTr shift (fun x => centralElem (t x)) U x μ
  set c := centralElem (-(h * a x μ))
  rw [_root_.mul_inv_rev, show c * u * w * (u⁻¹ * c⁻¹) = c * (u * w * u⁻¹) * c⁻¹ by group,
    centralElem_comm, mul_assoc, mul_inv_cancel, mul_one]

/-- **Adjoint Wilson transport on the Lie algebra**: conjugation of colour and weak matrices
by `V` and by `U'` agree. -/
theorem ad_matrix_splitLinks (h : ℝ) (t : X → ℝ) (a : X → D → ℝ)
    (U : X → D → SMGaugeGroup) (x : X) (μ : D) (M₃ : Matrix (Fin 3) (Fin 3) ℂ)
    (M₂ : Matrix (Fin 2) (Fin 2) ℂ) :
    smU3 (splitLinks shift h t a U x μ) * M₃ * smU3 (splitLinks shift h t a U x μ)⁻¹ =
        smU3 (gaugeTr shift (fun x => centralElem (t x)) U x μ) * M₃ *
          smU3 (gaugeTr shift (fun x => centralElem (t x)) U x μ)⁻¹ ∧
      smU2 (splitLinks shift h t a U x μ) * M₂ * smU2 (splitLinks shift h t a U x μ)⁻¹ =
        smU2 (gaugeTr shift (fun x => centralElem (t x)) U x μ) * M₂ *
          smU2 (gaugeTr shift (fun x => centralElem (t x)) U x μ)⁻¹ := by
  set u := gaugeTr shift (fun x => centralElem (t x)) U x μ
  set s := -(h * a x μ)
  have hV : splitLinks shift h t a U x μ = centralElem s * u := rfl
  have hinv : (centralElem s * u)⁻¹ = u⁻¹ * centralElem (-s) := by
    rw [_root_.mul_inv_rev, centralElem_neg]
  rw [hV, hinv]
  have p3 : Complex.exp (-((s : ℂ) / 3) * Complex.I) *
      Complex.exp (-(((-s : ℝ) : ℂ) / 3) * Complex.I) = 1 := by
    rw [← Complex.exp_add]; convert Complex.exp_zero using 2; push_cast; ring
  have p2 : Complex.exp ((s : ℂ) / 2 * Complex.I) *
      Complex.exp (((-s : ℝ) : ℂ) / 2 * Complex.I) = 1 := by
    rw [← Complex.exp_add]; convert Complex.exp_zero using 2; push_cast; ring
  constructor
  · rw [map_mul, map_mul, centralElem_U3, centralElem_U3]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul,
      mul_comm (Complex.exp (-(((-s : ℝ) : ℂ) / 3) * Complex.I)), p3, one_smul]
  · rw [map_mul, map_mul, centralElem_U2, centralElem_U2]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul,
      mul_comm (Complex.exp (((-s : ℝ) : ℂ) / 2 * Complex.I)), p2, one_smul]

/-- **Change of site lifts.**  Replacing `t(x)` by `t(x) + 2π k(x)` changes `V` by the
central `G_ss` site gauge `z₆^{k(x)}`. -/
theorem central_conj (α β : ℝ) (u : SMGaugeGroup) :
    centralElem α * u * (centralElem β)⁻¹ = centralElem (α - β) * u := by
  rw [centralElem_neg, mul_assoc, ← centralElem_comm, ← mul_assoc, ← centralElem_add,
    sub_eq_add_neg]

/-- **Change of site lifts.**  Replacing `t(x)` by `t(x) + 2π k(x)` changes `V` by the
central `G_ss` site gauge `z₆^{k(x)}`. -/
theorem splitLinks_lift_change (h : ℝ) (t : X → ℝ) (k : X → ℤ) (a : X → D → ℝ)
    (U : X → D → SMGaugeGroup) (x : X) (μ : D) :
    splitLinks shift h (fun x => t x + 2 * Real.pi * k x) a U x μ =
      gaugeTr shift (fun x => zSix ^ k x) (splitLinks shift h t a U) x μ := by
  show centralElem (-(h * a x μ)) * (centralElem (t x + 2 * Real.pi * k x) * U x μ *
      (centralElem (t (shift x μ) + 2 * Real.pi * k (shift x μ)))⁻¹) =
    zSix ^ k x * (centralElem (-(h * a x μ)) * (centralElem (t x) * U x μ *
      (centralElem (t (shift x μ)))⁻¹)) * (zSix ^ k (shift x μ))⁻¹
  rw [zSix, ← centralElem_zsmul, ← centralElem_zsmul]
  simp only [central_conj]
  simp only [← mul_assoc, ← centralElem_add]
  congr 2
  ring

end Lattice

/-! ### The Lie-algebra projections and the logarithm clause -/

section LieAlgebra

/-- A Lie-algebra pair `(X₃, X₂)` of `𝔤_SM`. -/
abbrev LiePair := Matrix (Fin 3) (Fin 3) ℂ × Matrix (Fin 2) (Fin 2) ℂ

/-- `Z_c = (-i/3 I₃, i/2 I₂)`. -/
def Zc : LiePair := (-(Complex.I / 3) • 1, (Complex.I / 2) • 1)

/-- `ℓ_c(X) = (1/i) tr X₂` (`eq:determinant-projections`). -/
def ellC (X : LiePair) : ℂ := (Matrix.trace X.2) / Complex.I

/-- `Π_ss X = X - Z_c ℓ_c(X)`. -/
def piSS (X : LiePair) : LiePair := (X.1 - ellC X • Zc.1, X.2 - ellC X • Zc.2)

theorem ellC_Zc : ellC Zc = 1 := by
  simp [ellC, Zc, Matrix.trace_smul]

theorem ellC_piSS (X : LiePair) : ellC (piSS X) = 0 := by
  have h : ellC (piSS X) = ellC X - ellC X * ellC Zc := by
    simp only [ellC, piSS, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
    ring
  rw [h, ellC_Zc, mul_one, sub_self]

theorem piSS_piSS (X : LiePair) : piSS (piSS X) = piSS X := by
  unfold piSS
  rw [show ellC (X.1 - ellC X • Zc.1, X.2 - ellC X • Zc.2) = 0 from ellC_piSS X]
  simp

theorem piSS_smul (c : ℂ) (X : LiePair) : piSS (c • X) = c • piSS X := by
  have h : ellC (c • X) = c * ellC X := by
    simp only [ellC, Prod.smul_snd, Matrix.trace_smul, smul_eq_mul]
    ring
  simp only [piSS, h, Prod.smul_fst, Prod.smul_snd]
  refine Prod.ext ?_ ?_ <;> simp [smul_sub, smul_smul]

/-- `exp(s Z_c)` is the central element `e^{s Z_c}` (colour factor). -/
theorem exp_Zc_fst (s : ℝ) : NormedSpace.exp ((s : ℂ) • Zc.1) = smU3 (centralElem s) := by
  have hd : (s : ℂ) • Zc.1 = Matrix.diagonal (fun _ => -((s : ℂ) / 3) * Complex.I) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [Zc]; ring
    · simp [Zc, hij]
  rw [hd, Matrix.exp_diagonal, centralElem_U3, Pi.exp_def]
  ext i j
  by_cases hij : i = j
  · subst hij; simp [← Complex.exp_eq_exp_ℂ]
  · simp [hij]

/-- `exp(s Z_c)` is the central element `e^{s Z_c}` (weak factor). -/
theorem exp_Zc_snd (s : ℝ) : NormedSpace.exp ((s : ℂ) • Zc.2) = smU2 (centralElem s) := by
  have hd : (s : ℂ) • Zc.2 = Matrix.diagonal (fun _ => ((s : ℂ) / 2) * Complex.I) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [Zc]; ring
    · simp [Zc, hij]
  rw [hd, Matrix.exp_diagonal, centralElem_U2, Pi.exp_def]
  ext i j
  by_cases hij : i = j
  · subst hij; simp [← Complex.exp_eq_exp_ℂ]
  · simp [hij]

/-- **Logarithm clause.**  Let `X` be a logarithm of the full plaquette `P_{U'}`
(`exp X₃ = (P_{U'})₃`, `exp X₂ = (P_{U'})₂`) whose determinant part is the principal
determinant argument, `ℓ_c(X) = h² f` (the identity `f_h = ℓ_c(𝔽_h)` of
`lem:determinant-screen-flux`), and let `P_{U'} = e^{h²f Z_c} P_V`.  Then `Π_ss X` is a
logarithm of `P_V`. -/
theorem exp_piSS (X : LiePair) (PU PV : SMGaugeGroup) (φ : ℝ)
    (h3 : NormedSpace.exp X.1 = smU3 PU) (h2 : NormedSpace.exp X.2 = smU2 PU)
    (hl : ellC X = φ) (hP : PU = centralElem φ * PV) :
    NormedSpace.exp (piSS X).1 = smU3 PV ∧ NormedSpace.exp (piSS X).2 = smU2 PV := by
  have hPV : PV = PU * centralElem (-φ) := by
    rw [hP, centralElem_comm, mul_assoc, ← centralElem_add, add_neg_cancel, centralElem_zero,
      mul_one]
  have e1 : (piSS X).1 = X.1 + ((-φ : ℝ) : ℂ) • Zc.1 := by
    simp only [piSS, hl]; push_cast; rw [neg_smul, sub_eq_add_neg]
  have e2 : (piSS X).2 = X.2 + ((-φ : ℝ) : ℂ) • Zc.2 := by
    simp only [piSS, hl]; push_cast; rw [neg_smul, sub_eq_add_neg]
  have c1 : Commute X.1 (((-φ : ℝ) : ℂ) • Zc.1) := by
    simp only [Zc, smul_smul]
    exact (Commute.one_right X.1).smul_right _
  have c2 : Commute X.2 (((-φ : ℝ) : ℂ) • Zc.2) := by
    simp only [Zc, smul_smul]
    exact (Commute.one_right X.2).smul_right _
  rw [e1, e2, Matrix.exp_add_of_commute _ _ c1, Matrix.exp_add_of_commute _ _ c2, h3, h2,
    exp_Zc_fst, exp_Zc_snd, hPV, map_mul, map_mul]
  exact ⟨rfl, rfl⟩

/-- **`eq:determinant-semisimple-curvature`** on an admissible logarithm chart: if the
pair-exponential is injective on a chart `Ω` containing `X` (a logarithm of `P_{U'}` as in
`exp_piSS`) and `Π_ss X`, then the chart logarithm of `P_V` is `Π_ss X`, i.e.
`F_h(V) = Π_ss F_h(U')` after division by `h²`. -/
theorem chartLog_piSS (Ω : Set LiePair)
    (hinj : ∀ Y ∈ Ω, ∀ Y' ∈ Ω, NormedSpace.exp Y.1 = NormedSpace.exp Y'.1 →
      NormedSpace.exp Y.2 = NormedSpace.exp Y'.2 → Y = Y')
    (X : LiePair) (PU PV : SMGaugeGroup) (φ : ℝ)
    (h3 : NormedSpace.exp X.1 = smU3 PU) (h2 : NormedSpace.exp X.2 = smU2 PU)
    (hl : ellC X = φ) (hP : PU = centralElem φ * PV) (hX : piSS X ∈ Ω)
    (Y : LiePair) (hY : Y ∈ Ω) (hY3 : NormedSpace.exp Y.1 = smU3 PV)
    (hY2 : NormedSpace.exp Y.2 = smU2 PV) : Y = piSS X := by
  obtain ⟨e3, e2⟩ := exp_piSS X PU PV φ h3 h2 hl hP
  exact hinj Y hY (piSS X) hX (hY3.trans e3.symm) (hY2.trans e2.symm)

/-- **Inherited semisimple screen**: entrywise, `‖Π_ss X‖ ≤ 2 ‖X‖`. -/
theorem piSS_entry_le (X : LiePair) (c : ℝ)
    (h3 : ∀ i j, ‖X.1 i j‖ ≤ c) (h2 : ∀ i j, ‖X.2 i j‖ ≤ c) :
    (∀ i j, ‖(piSS X).1 i j‖ ≤ 2 * c) ∧ (∀ i j, ‖(piSS X).2 i j‖ ≤ 2 * c) := by
  have hc : 0 ≤ c := (norm_nonneg _).trans (h2 0 0)
  have hl : ‖ellC X‖ ≤ 2 * c := by
    simp only [ellC, norm_div, Complex.norm_I, div_one, Matrix.trace, Matrix.diag,
      Fin.sum_univ_two]
    linarith [norm_add_le (X.2 0 0) (X.2 1 1), h2 0 0, h2 1 1]
  have hZ1 : ∀ i j, ‖Zc.1 i j‖ ≤ 1 / 2 := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp [Zc, Complex.norm_I]; norm_num
    · simp [Zc, hij]
  have hZ2 : ∀ i j, ‖Zc.2 i j‖ ≤ 1 / 2 := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp [Zc, Complex.norm_I]
    · simp [Zc, hij]
  constructor
  · intro i j
    simp only [piSS, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    nlinarith [h3 i j, hZ1 i j, hl, norm_nonneg (ellC X), norm_nonneg (Zc.1 i j)]
  · intro i j
    simp only [piSS, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    nlinarith [h2 i j, hZ2 i j, hl, norm_nonneg (ellC X), norm_nonneg (Zc.2 i j)]

end LieAlgebra

/-! ### Assembly of the exact group-algebraic content -/

section Assembly

variable {X D : Type*} (shift : X → D → X)

/-- **`prop:native-determinant-split`, exact group-algebraic content.**  Let `U` be
`G_SM`-links on a lattice, `t` real site lifts and `a` a real potential with
* (normalization, from `prop:periodic-determinant-normalization`)
  `e^{it(x)} χ(U_μ(x)) e^{-it(x+μ)} = e^{i h a_μ(x)}` and `h² f = h (d_h a)` on plaquettes;
* (admissible logarithms, from `lem:determinant-screen-flux`) logarithms `L_{μν}(x)` of the
  full plaquettes of `U' = U^{e^{tZ_c}}` lying in a chart `Ω` on which the exponential is
  injective, with `ℓ_c(L) = h² f` and `Π_ss L ∈ Ω`.
Then, for `V = e^{-h a Z_c} U'`:
1. `χ(V_μ(x)) = 1`, i.e. `V ∈ G_ss = SU(3) × SU(2)` exactly;
2. `P_{U'} = e^{h² f Z_c} P_V` on every plaquette;
3. every logarithm of `P_V` in the chart equals `Π_ss L` (so `F_h(V) = Π_ss F_h(U')`);
4. `Ad(V) = Ad(U')`;
5. changing the lifts by `2π k(x)` changes `V` by the central `G_ss` site gauge `z₆^{k(x)}`,
   with `z₆ = e^{2πZ_c} = (e^{-2πi/3} I₃, -I₂) ∈ G_ss`, `z₆⁶ = 1`. -/
theorem native_determinant_split_core (h : ℝ) (t : X → ℝ) (a : X → D → ℝ)
    (U : X → D → SMGaugeGroup) (f : X → D → D → ℝ)
    (hN : ∀ x μ, Complex.exp (t x * Complex.I) * smChi (U x μ) *
      Complex.exp (-(t (shift x μ) * Complex.I)) = Complex.exp (h * a x μ * Complex.I))
    (hcurl : ∀ x μ ν, h * curl shift a x μ ν = h ^ 2 * f x μ ν)
    (Ω : Set LiePair)
    (hinj : ∀ Y ∈ Ω, ∀ Y' ∈ Ω, NormedSpace.exp Y.1 = NormedSpace.exp Y'.1 →
      NormedSpace.exp Y.2 = NormedSpace.exp Y'.2 → Y = Y')
    (L : X → D → D → LiePair)
    (hL3 : ∀ x μ ν, NormedSpace.exp (L x μ ν).1 =
      smU3 (plaq shift (gaugeTr shift (fun x => centralElem (t x)) U) x μ ν))
    (hL2 : ∀ x μ ν, NormedSpace.exp (L x μ ν).2 =
      smU2 (plaq shift (gaugeTr shift (fun x => centralElem (t x)) U) x μ ν))
    (hLc : ∀ x μ ν, ellC (L x μ ν) = (h ^ 2 * f x μ ν : ℝ))
    (hΩ : ∀ x μ ν, piSS (L x μ ν) ∈ Ω) :
    (∀ x μ, smChi (splitLinks shift h t a U x μ) = 1 ∧
      (smU3 (splitLinks shift h t a U x μ)).det = 1 ∧
      (smU2 (splitLinks shift h t a U x μ)).det = 1) ∧
    (∀ x μ ν, plaq shift (gaugeTr shift (fun x => centralElem (t x)) U) x μ ν =
      centralElem (h ^ 2 * f x μ ν) * plaq shift (splitLinks shift h t a U) x μ ν) ∧
    (∀ x μ ν, ∀ Y ∈ Ω, NormedSpace.exp Y.1 = smU3 (plaq shift (splitLinks shift h t a U) x μ ν) →
      NormedSpace.exp Y.2 = smU2 (plaq shift (splitLinks shift h t a U) x μ ν) →
      Y = piSS (L x μ ν)) ∧
    (∀ x μ w, splitLinks shift h t a U x μ * w * (splitLinks shift h t a U x μ)⁻¹ =
      gaugeTr shift (fun x => centralElem (t x)) U x μ * w *
        (gaugeTr shift (fun x => centralElem (t x)) U x μ)⁻¹) ∧
    (∀ (k : X → ℤ) x μ, splitLinks shift h (fun x => t x + 2 * Real.pi * k x) a U x μ =
      gaugeTr shift (fun x => zSix ^ k x) (splitLinks shift h t a U) x μ) ∧
    (smChi zSix = 1 ∧ zSix ^ 6 = 1) := by
  have hplaq : ∀ x μ ν, plaq shift (gaugeTr shift (fun x => centralElem (t x)) U) x μ ν =
      centralElem (h ^ 2 * f x μ ν) * plaq shift (splitLinks shift h t a U) x μ ν := by
    intro x μ ν
    rw [plaq_split, hcurl]
  refine ⟨fun x μ => ?_, hplaq, fun x μ ν Y hY hY3 hY2 => ?_,
    fun x μ w => ad_splitLinks shift h t a U x μ w,
    fun k x μ => splitLinks_lift_change shift h t k a U x μ, zSix_mem_ss_pow_six⟩
  · have hχ := smChi_splitLinks shift h t a U hN x μ
    exact ⟨hχ, det_eq_one_of_smChi _ hχ⟩
  · exact chartLog_piSS Ω hinj (L x μ ν) _ _ (h ^ 2 * f x μ ν) (hL3 x μ ν) (hL2 x μ ν)
      (hLc x μ ν) (hplaq x μ ν) (hΩ x μ ν) Y hY hY3 hY2

end Assembly

end

end DeterminantSplit

end RenewalGeometry
