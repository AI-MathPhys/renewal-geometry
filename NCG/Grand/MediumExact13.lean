/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.GRHZeroMode
import NCG.Grand.SharpChainCentralBankExact

/-!
# Medium-exact batch 13

Exact closures of the fidelity-audit gaps for the MEDIUM records

* `thm:GRH-integrated-zero-mode` — the operator clause: the predictable mixed
  energy of the assembled packet is bounded by the zero-mode compression
  `‖Z* P₀ Z‖` of the phase source through the projection onto the fixed space
  of the accepted contraction, together with the complex-Gram router
  dispersion identity and the square-root-scale bridge estimate;
* `thm:GRH-sharp-chain-central-bank` — the operator-level central boundary
  bank: the central loading Gram `𝔸_cen = ∑ b_j V_j* T_j* T_j V_j ⪰ 0` built
  from actual isometries and boundary reads, its sharp source floor
  `κ_cen = λ_min/β_m` with a genuinely defined spectral floor, and the
  dilution bound GRH.18 in the labelled `ℓ²` direct sum with the sharp-source
  norm `√β_m ‖g‖` *proved* from the isometry property (not hypothesised).

Further records of the batch are appended in later sections of this file.
-/

open Finset

namespace NCG
namespace MediumExact13

/-! ## `thm:GRH-integrated-zero-mode`: the operator clause

The manuscript packet: a finite accepted energy partition with complete
total–phase Grams has the boxed router dispersion (proved over any complex
inner-product space of phase sources); on the physical Hilbert carrier the
packet is represented by a contraction `T`, an accepted total source `s` with
`T* s = s`, and a phase source `Z`; with the common source normalization the
predictable mixed energy `D^pred = |⟪s, Z g⟫|²` is bounded by
`‖Z* P₀ Z‖` where `P₀` projects onto `ker (1 - T)`; a subpower estimate for
`‖Z* P₀ Z‖` then forces the square-root-scale upper bound `|B| ≤ √(A‖Z*P₀Z‖)`
of the hard-edge GRH bridge. -/

section ZeroMode

open scoped InnerProductSpace ComplexConjugate

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The boxed router dispersion of `thm:GRH-integrated-zero-mode` over a
complex inner-product space of phase Grams:
`∑ⱼ ‖bⱼ‖²/aⱼ − ‖∑b‖²/∑a = ∑ⱼ aⱼ‖bⱼ/aⱼ − K‖²` with the pooled router
`K = (∑a)⁻¹ ∑b`. -/
theorem router_dispersion_complex {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℝ) (b : ι → V) (ha : ∀ j, 0 < a j) :
    ∑ j, ‖b j‖ ^ 2 / a j - ‖∑ j, b j‖ ^ 2 / (∑ j, a j)
      = ∑ j, a j * ‖((a j : ℝ) : ℂ)⁻¹ • b j
          - (((∑ i, a i : ℝ) : ℂ))⁻¹ • ∑ i, b i‖ ^ 2 := by
  have hA : 0 < ∑ j, a j := Finset.sum_pos (fun j _ => ha j) univ_nonempty
  set K : V := (((∑ i, a i : ℝ) : ℂ))⁻¹ • ∑ i, b i with hK
  have hterm : ∀ j, a j * ‖((a j : ℝ) : ℂ)⁻¹ • b j - K‖ ^ 2
      = ‖b j‖ ^ 2 / a j - 2 * RCLike.re (⟪b j, K⟫_ℂ) + a j * ‖K‖ ^ 2 := by
    intro j
    have hj := ha j
    have hexp := norm_sub_sq (𝕜 := ℂ) (((a j : ℝ) : ℂ)⁻¹ • b j) K
    have h1 : ‖((a j : ℝ) : ℂ)⁻¹ • b j‖ ^ 2 = ‖b j‖ ^ 2 / (a j) ^ 2 := by
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hj, mul_pow, inv_pow]
      field_simp
    have h2 : RCLike.re (⟪((a j : ℝ) : ℂ)⁻¹ • b j, K⟫_ℂ)
        = (a j)⁻¹ * RCLike.re (⟪b j, K⟫_ℂ) := by
      rw [inner_smul_left, ← Complex.ofReal_inv, Complex.conj_ofReal]
      simp [Complex.ofReal_mul_re]
    rw [hexp, h1, h2]
    field_simp
    ring
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hre : ∑ j, 2 * RCLike.re (⟪b j, K⟫_ℂ)
      = 2 * RCLike.re (⟪∑ i, b i, K⟫_ℂ) := by
    rw [sum_inner, map_sum, Finset.mul_sum]
  have hIK : RCLike.re (⟪∑ i, b i, K⟫_ℂ)
      = ‖∑ i, b i‖ ^ 2 / (∑ i, a i) := by
    rw [hK, inner_smul_right, inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    rw [← Complex.ofReal_inv, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    rw [Complex.ofReal_re, inv_mul_eq_div]
  have hK2 : ‖K‖ ^ 2 = ‖∑ i, b i‖ ^ 2 / (∑ i, a i) ^ 2 := by
    rw [hK, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hA, mul_pow, inv_pow]
    field_simp
  rw [hre, hIK, hK2]
  field_simp
  ring

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

/-- The zero-mode space `ker (1 - T)` of the accepted contraction. -/
noncomputable abbrev fixedSpace (T : E →L[ℂ] E) : Submodule ℂ E :=
  LinearMap.ker ((1 : E →L[ℂ] E) - T)

/-- A source co-fixed by a contraction is fixed: `T* s = s` and `‖T‖ ≤ 1`
force `T s = s`, so the accepted total source lies in the zero-mode space. -/
theorem fixed_of_adjoint_fixed {T : E →L[ℂ] E} (hT : ‖T‖ ≤ 1) {s : E}
    (hfix : ContinuousLinearMap.adjoint T s = s) : T s = s := by
  have hinner : ⟪s, T s⟫_ℂ = (⟪s, s⟫_ℂ) := by
    rw [← ContinuousLinearMap.adjoint_inner_left, hfix]
  have hre : RCLike.re (⟪T s, s⟫_ℂ) = ‖s‖ ^ 2 := by
    rw [← inner_conj_symm, hinner, inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    simp
  have hnorm : ‖T s‖ ≤ ‖s‖ := by
    calc ‖T s‖ ≤ ‖T‖ * ‖s‖ := T.le_opNorm s
      _ ≤ 1 * ‖s‖ := by
          have := norm_nonneg s
          nlinarith
      _ = ‖s‖ := one_mul _
  have hsq := norm_sub_sq (𝕜 := ℂ) (T s) s
  rw [hre] at hsq
  have hz : ‖T s - s‖ = 0 := by
    have h0 : 0 ≤ ‖T s - s‖ := norm_nonneg _
    have h1 : ‖T s - s‖ ^ 2 ≤ 0 := by nlinarith [norm_nonneg (T s)]
    nlinarith
  have := norm_eq_zero.mp hz
  linarith [sub_eq_zero.mp this]

/-- **The operator clause of `thm:GRH-integrated-zero-mode`** — the boxed
predictable mixed-energy bound `D_X^pred ≤ ‖Z* P₀ Z‖`.

After the common source normalization (`‖s‖ = 1`, `‖g‖ = 1`), the predictable
mixed energy `D^pred = |⟪s, Z g⟫|²` of the phase source `Z` against the
accepted total source `s` (co-fixed by the contraction, `T* s = s`) is
bounded by the norm of the zero-mode compression `Z* P₀ Z`, where `P₀` is
the orthogonal projection onto `ker (1 - T)`. -/
theorem zero_mode_pred_bound (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1)
    (Z : F →L[ℂ] E) (s : E) (hfix : ContinuousLinearMap.adjoint T s = s)
    (hs : ‖s‖ = 1) (g : F) (hg : ‖g‖ = 1) :
    ‖(⟪s, Z g⟫_ℂ)‖ ^ 2
      ≤ ‖ContinuousLinearMap.adjoint Z ∘L
          ((fixedSpace T).starProjection ∘L Z)‖ := by
  set P : E →L[ℂ] E := (fixedSpace T).starProjection with hP
  have hker : s ∈ fixedSpace T := by
    have hTs := fixed_of_adjoint_fixed hT hfix
    simp [fixedSpace, LinearMap.mem_ker, ContinuousLinearMap.sub_apply, hTs]
  have hPs : P s = s := Submodule.starProjection_eq_self_iff.mpr hker
  have hswap : ⟪s, Z g⟫_ℂ = ⟪s, P (Z g)⟫_ℂ := by
    conv_lhs => rw [← hPs]
    exact Submodule.inner_starProjection_left_eq_right _ s (Z g)
  have hidem : P (P (Z g)) = P (Z g) := by
    have h := (fixedSpace T).isIdempotentElem_starProjection
    calc P (P (Z g)) = (P * P) (Z g) := rfl
      _ = P (Z g) := by rw [h.eq]
  have hPnorm : ‖P (Z g)‖ ^ 2 = RCLike.re (⟪Z g, P (Z g)⟫_ℂ) := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
    congr 1
    calc ⟪P (Z g), P (Z g)⟫_ℂ = ⟪Z g, P (P (Z g))⟫_ℂ :=
        Submodule.inner_starProjection_left_eq_right _ _ _
      _ = ⟪Z g, P (Z g)⟫_ℂ := by rw [hidem]
  have hadj : ⟪Z g, P (Z g)⟫_ℂ
      = ⟪g, (ContinuousLinearMap.adjoint Z ∘L (P ∘L Z)) g⟫_ℂ := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right]
  have hcauchy : ‖(⟪s, Z g⟫_ℂ)‖ ≤ ‖P (Z g)‖ := by
    rw [hswap]
    calc ‖(⟪s, P (Z g)⟫_ℂ)‖ ≤ ‖s‖ * ‖P (Z g)‖ := norm_inner_le_norm _ _
      _ = ‖P (Z g)‖ := by rw [hs, one_mul]
  set W := ContinuousLinearMap.adjoint Z ∘L (P ∘L Z) with hW
  have hWbound : RCLike.re (⟪g, W g⟫_ℂ) ≤ ‖W‖ := by
    calc RCLike.re (⟪g, W g⟫_ℂ) ≤ ‖(⟪g, W g⟫_ℂ)‖ := RCLike.re_le_norm _
      _ ≤ ‖g‖ * ‖W g‖ := norm_inner_le_norm _ _
      _ = ‖W g‖ := by rw [hg, one_mul]
      _ ≤ ‖W‖ * ‖g‖ := W.le_opNorm g
      _ = ‖W‖ := by rw [hg, mul_one]
  calc ‖(⟪s, Z g⟫_ℂ)‖ ^ 2 ≤ ‖P (Z g)‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hcauchy 2
    _ = RCLike.re (⟪Z g, P (Z g)⟫_ℂ) := hPnorm
    _ = RCLike.re (⟪g, W g⟫_ℂ) := by rw [hadj]
    _ ≤ ‖W‖ := hWbound

/-- The hard-edge bridge estimate closing `thm:GRH-integrated-zero-mode`:
whenever the predictable mixed energy `B²/A` is bounded by the zero-mode
compression norm `W` (with `A = X^{1+o(1)}` the accepted total energy and
`W = X^{o(1)}` the regulator estimate), the completed Euler endpoint obeys
the square-root-scale upper bound `|B| ≤ √(A·W)`. -/
theorem sqrt_scale_bridge (A B W : ℝ) (hA : 0 < A)
    (hbound : B ^ 2 / A ≤ W) : |B| ≤ Real.sqrt (A * W) := by
  have hB2 : B ^ 2 ≤ A * W := by
    rw [div_le_iff₀ hA] at hbound
    linarith
  calc |B| = Real.sqrt (B ^ 2) := (Real.sqrt_sq_eq_abs B).symm
    _ ≤ Real.sqrt (A * W) := Real.sqrt_le_sqrt hB2

/-- **`thm:GRH-integrated-zero-mode`, assembled**: the boxed router
dispersion with its nonnegativity (the short of the assembled complete Gram
is not the sum of the pointwise shorts), the boxed operator bound
`D^pred ≤ ‖Z* P₀ Z‖`, and the square-root-scale bridge estimate. -/
theorem grh_integrated_zero_mode_exact {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℝ) (b : ι → V) (ha : ∀ j, 0 < a j)
    (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1) (Z : F →L[ℂ] E) (s : E)
    (hfix : ContinuousLinearMap.adjoint T s = s) (hs : ‖s‖ = 1)
    (g : F) (hg : ‖g‖ = 1) :
    (∑ j, ‖b j‖ ^ 2 / a j - ‖∑ j, b j‖ ^ 2 / (∑ j, a j)
        = ∑ j, a j * ‖((a j : ℝ) : ℂ)⁻¹ • b j
            - (((∑ i, a i : ℝ) : ℂ))⁻¹ • ∑ i, b i‖ ^ 2)
    ∧ 0 ≤ ∑ j, ‖b j‖ ^ 2 / a j - ‖∑ j, b j‖ ^ 2 / (∑ j, a j)
    ∧ ‖(⟪s, Z g⟫_ℂ)‖ ^ 2
        ≤ ‖ContinuousLinearMap.adjoint Z ∘L
            ((fixedSpace T).starProjection ∘L Z)‖
    ∧ ∀ A B W : ℝ, 0 < A → B ^ 2 / A ≤ W → |B| ≤ Real.sqrt (A * W) := by
  refine ⟨router_dispersion_complex a b ha, ?_,
    zero_mode_pred_bound T hT Z s hfix hs g hg,
    fun A B W hA hb => sqrt_scale_bridge A B W hA hb⟩
  rw [router_dispersion_complex a b ha]
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (ha j).le (sq_nonneg _)

end ZeroMode

/-! ## `thm:GRH-sharp-chain-central-bank`: the operator-level bank

GRH.15 is the proved `NCG.SharpChain.central_mass`; here the remaining
clauses GRH.16–GRH.18 are closed at the operator level: the central loading
Gram is assembled from actual isometries `V_j : E → E_j` and boundary reads
`T_j : E_j → 𝒴_j`, its positivity and quadratic form are proved, the sharp
source floor uses a genuinely defined spectral floor (the infimum of the
Rayleigh quotients), and the GRH.18 dilution bound lives in the labelled
`ℓ²` direct sum with the sharp-source central mass `β_m ‖g‖²` proved from
the isometry property. -/

section SharpChainOp

open scoped InnerProductSpace

/-- The sine-profile boundary weight `b_{m,j} = |u_j|²` of the translation
chain. -/
noncomputable def bWeight (m : ℕ) (j : Fin m) : ℝ :=
  2 / ((m : ℝ) + 1) * Real.sin (((j.val : ℝ) + 1) * Real.pi / ((m : ℝ) + 1)) ^ 2

/-- `b_{m,j}` is the square of the sine-profile amplitude
`u_j = √(2/(m+1)) sin((j+1)π/(m+1))`. -/
theorem bWeight_eq_sq (m : ℕ) (j : Fin m) :
    bWeight m j = (Real.sqrt (2 / ((m : ℝ) + 1))
      * Real.sin (((j.val : ℝ) + 1) * Real.pi / ((m : ℝ) + 1))) ^ 2 := by
  rw [mul_pow, Real.sq_sqrt (by positivity), bWeight]

theorem bWeight_nonneg (m : ℕ) (j : Fin m) : 0 ≤ bWeight m j := by
  rw [bWeight_eq_sq]
  exact sq_nonneg _

/-- The central boundary mass `β_m = ∑_{j ∈ 𝒥_m} b_{m,j}`. -/
noncomputable def betaMass (m : ℕ) : ℝ :=
  ∑ j ∈ SharpChain.centralSet m, bWeight m j

theorem betaMass_nonneg (m : ℕ) : 0 ≤ betaMass m :=
  Finset.sum_nonneg fun j _ => bWeight_nonneg m j

/-- **GRH.15**: `β_m ≥ 1/3` (the proved `NCG.SharpChain.central_mass`). -/
theorem betaMass_ge (m : ℕ) (hm : 1 ≤ m) : (1 : ℝ) / 3 ≤ betaMass m := by
  simpa [betaMass, bWeight] using SharpChain.central_mass m hm

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]
  {Ej : Fin m → Type*} [∀ j, NormedAddCommGroup (Ej j)]
  [∀ j, InnerProductSpace ℂ (Ej j)]
  {Yj : Fin m → Type*} [∀ j, NormedAddCommGroup (Yj j)]
  [∀ j, InnerProductSpace ℂ (Yj j)] [∀ j, FiniteDimensional ℂ (Yj j)]

/-- The boundary-labelled arithmetic read through row `j`: the actual read
`T_j` composed with the isometric carrier `V_j`. -/
noncomputable def rowRead (V : ∀ j, E →ₗᵢ[ℂ] Ej j)
    (T : ∀ j, Ej j →L[ℂ] Yj j) (j : Fin m) : E →L[ℂ] Yj j :=
  (T j).comp (V j).toContinuousLinearMap

/-- **GRH.16, the central loading Gram**
`𝔸_cen = ∑_{j ∈ 𝒥_m} b_{m,j} V_j* T_j* T_j V_j`. -/
noncomputable def centralGram (V : ∀ j, E →ₗᵢ[ℂ] Ej j)
    (T : ∀ j, Ej j →L[ℂ] Yj j) : E →L[ℂ] E :=
  ∑ j ∈ SharpChain.centralSet m, ((bWeight m j : ℝ) : ℂ) •
    (ContinuousLinearMap.adjoint (rowRead V T j) ∘L rowRead V T j)

/-- The quadratic form of the central loading Gram is the weighted central
boundary energy `∑_{j ∈ 𝒥_m} b_{m,j} ‖T_j V_j g‖²`. -/
theorem centralGram_inner (V : ∀ j, E →ₗᵢ[ℂ] Ej j)
    (T : ∀ j, Ej j →L[ℂ] Yj j) (g : E) :
    RCLike.re (⟪g, centralGram V T g⟫_ℂ)
      = ∑ j ∈ SharpChain.centralSet m,
          bWeight m j * ‖rowRead V T j g‖ ^ 2 := by
  have happ : centralGram V T g = ∑ j ∈ SharpChain.centralSet m,
      ((bWeight m j : ℝ) : ℂ) •
        (ContinuousLinearMap.adjoint (rowRead V T j)) (rowRead V T j g) := by
    rw [centralGram, ContinuousLinearMap.sum_apply]
    exact Finset.sum_congr rfl fun j _ => rfl
  rw [happ, inner_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_right, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- **GRH.16**: the central loading Gram is a positive operator. -/
theorem centralGram_isPositive (V : ∀ j, E →ₗᵢ[ℂ] Ej j)
    (T : ∀ j, Ej j →L[ℂ] Yj j) : (centralGram V T).IsPositive := by
  constructor
  · rw [ContinuousLinearMap.isSelfAdjoint_iff']
    rw [centralGram, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.adjoint_smul, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint, Complex.conj_ofReal]
  · intro x
    rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    have h : RCLike.re (⟪centralGram V T x, x⟫_ℂ)
        = RCLike.re (⟪x, centralGram V T x⟫_ℂ) := by
      rw [← inner_conj_symm]
      simp
    rw [h, centralGram_inner]
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (bWeight_nonneg m j) (sq_nonneg _)

/-- The spectral floor of an operator: the infimum of its Rayleigh values on
the unit sphere.  For the (self-adjoint, positive) central Gram this is its
least eigenvalue `λ_min(𝔸_cen)`. -/
noncomputable def spectralFloor (A : E →L[ℂ] E) : ℝ :=
  sInf ((fun g => RCLike.re (⟪g, A g⟫_ℂ)) '' {g : E | ‖g‖ = 1})

/-- The spectral floor really floors every Rayleigh quotient:
`λ_min ‖g‖² ≤ re ⟪g, A g⟫`. -/
theorem spectralFloor_le [Nontrivial E] (A : E →L[ℂ] E) (g : E) :
    spectralFloor A * ‖g‖ ^ 2 ≤ RCLike.re (⟪g, A g⟫_ℂ) := by
  have hbdd : BddBelow ((fun g => RCLike.re (⟪g, A g⟫_ℂ)) '' {g : E | ‖g‖ = 1}) := by
    refine ⟨-‖A‖, ?_⟩
    rintro r ⟨u, hu, rfl⟩
    have h1 : ‖(⟪u, A u⟫_ℂ)‖ ≤ ‖A‖ := by
      calc ‖(⟪u, A u⟫_ℂ)‖ ≤ ‖u‖ * ‖A u‖ := norm_inner_le_norm _ _
        _ ≤ ‖u‖ * (‖A‖ * ‖u‖) :=
            mul_le_mul_of_nonneg_left (A.le_opNorm u) (norm_nonneg u)
        _ = ‖A‖ := by rw [Set.mem_setOf_eq] at hu; rw [hu]; ring
    have h2 := abs_le.mp (RCLike.abs_re_le_norm (⟪u, A u⟫_ℂ))
    linarith [h2.1, h1]
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  · have hgn : (0 : ℝ) < ‖g‖ := norm_pos_iff.mpr hg
    set u : E := ((‖g‖⁻¹ : ℝ) : ℂ) • g with hu
    have hun : ‖u‖ = 1 := by
      rw [hu, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hgn), inv_mul_cancel₀ hgn.ne']
    have hval : RCLike.re (⟪u, A u⟫_ℂ)
        = ‖g‖⁻¹ ^ 2 * RCLike.re (⟪g, A g⟫_ℂ) := by
      rw [hu, map_smul, inner_smul_left, inner_smul_right,
        Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul]
      rw [show (‖g‖⁻¹ * ‖g‖⁻¹ : ℝ) = ‖g‖⁻¹ ^ 2 by ring]
      simp [Complex.ofReal_mul_re]
    have hmem : RCLike.re (⟪u, A u⟫_ℂ)
        ∈ (fun g => RCLike.re (⟪g, A g⟫_ℂ)) '' {g : E | ‖g‖ = 1} :=
      ⟨u, hun, rfl⟩
    have hinf := csInf_le hbdd hmem
    rw [hval] at hinf
    have h3 : spectralFloor A * ‖g‖ ^ 2
        ≤ ‖g‖⁻¹ ^ 2 * RCLike.re (⟪g, A g⟫_ℂ) * ‖g‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_right hinf (sq_nonneg _)
    calc spectralFloor A * ‖g‖ ^ 2
        ≤ ‖g‖⁻¹ ^ 2 * RCLike.re (⟪g, A g⟫_ℂ) * ‖g‖ ^ 2 := h3
      _ = RCLike.re (⟪g, A g⟫_ℂ) := by
          field_simp

/-- **GRH.17**: the sharp source floor `κ_cen = λ_min(𝔸_cen)/β_m` rescales
the `β_m`-normalized bank: `κ_cen · (β_m ‖g‖²) ≤ re ⟪g, 𝔸_cen g⟫`. -/
theorem central_floor_exact [Nontrivial E] (V : ∀ j, E →ₗᵢ[ℂ] Ej j)
    (T : ∀ j, Ej j →L[ℂ] Yj j) (hβ : 0 < betaMass m) (g : E) :
    spectralFloor (centralGram V T) / betaMass m * (betaMass m * ‖g‖ ^ 2)
      ≤ RCLike.re (⟪g, centralGram V T g⟫_ℂ) := by
  have h := spectralFloor_le (centralGram V T) g
  calc spectralFloor (centralGram V T) / betaMass m * (betaMass m * ‖g‖ ^ 2)
      = spectralFloor (centralGram V T) * ‖g‖ ^ 2 := by
        field_simp
    _ ≤ RCLike.re (⟪g, centralGram V T g⟫_ℂ) := h

/-! ### GRH.18: the dilution bound in the labelled direct sum -/

/-- The sharp source of `g` in the labelled `ℓ²` direct sum:
row `j` carries `√b_{m,j} · V_j g`. -/
noncomputable def sharpSource (V : ∀ j, E →ₗᵢ[ℂ] Ej j) (g : E) :
    PiLp 2 Ej :=
  WithLp.toLp 2 fun j => ((Real.sqrt (bWeight m j) : ℝ) : ℂ) • V j g

/-- The central boundary mass of a labelled source. -/
noncomputable def centralMassOf (y : PiLp 2 Ej) : ℝ :=
  ∑ j ∈ SharpChain.centralSet m, ‖y j‖ ^ 2

theorem centralMassOf_nonneg (y : PiLp 2 Ej) : 0 ≤ centralMassOf y :=
  Finset.sum_nonneg fun j _ => sq_nonneg _

/-- The central boundary mass of the sharp source is exactly `β_m ‖g‖²`
(proved from the isometry property of the carriers, not hypothesised). -/
theorem sharpSource_centralMass (V : ∀ j, E →ₗᵢ[ℂ] Ej j) (g : E) :
    centralMassOf (sharpSource V g) = betaMass m * ‖g‖ ^ 2 := by
  rw [centralMassOf, betaMass, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have happ : (sharpSource V g) j
      = ((Real.sqrt (bWeight m j) : ℝ) : ℂ) • V j g := rfl
  rw [happ, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), (V j).norm_map, mul_pow,
    Real.sq_sqrt (bWeight_nonneg m j)]

/-- The square root of the central mass is `1`-Lipschitz for the `ℓ²`
direct-sum distance. -/
theorem sqrt_centralMass_lipschitz (y z : PiLp 2 Ej) :
    Real.sqrt (centralMassOf y) - Real.sqrt (centralMassOf z)
      ≤ ‖y - z‖ := by
  classical
  have hyz : ∀ w : PiLp 2 Ej, Real.sqrt (centralMassOf w) ≤ ‖w‖ := by
    intro w
    rw [PiLp.norm_eq_of_L2]
    refine Real.sqrt_le_sqrt ?_
    rw [centralMassOf]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun i _ _ => sq_nonneg _
  -- triangle inequality for the central seminorm
  have htri : Real.sqrt (centralMassOf y)
      ≤ Real.sqrt (centralMassOf z) + Real.sqrt (centralMassOf (y - z)) := by
    -- interpret the central mass as a `ℓ²` norm over the central subtype
    set R : PiLp 2 Ej → PiLp 2 (fun j : {j // j ∈ SharpChain.centralSet m} => Ej j.val) :=
      fun w => WithLp.toLp 2 fun j => w j.val with hR
    have hnorm : ∀ w : PiLp 2 Ej, ‖R w‖ = Real.sqrt (centralMassOf w) := by
      intro w
      rw [PiLp.norm_eq_of_L2, centralMassOf, ← Finset.sum_coe_sort]
      rfl
    have hadd : R y = R z + R (y - z) := by
      apply WithLp.ofLp_injective
      funext j
      show y j.val = z j.val + (y - z) j.val
      simp
    have h := norm_add_le (R z) (R (y - z))
    rw [← hadd, hnorm, hnorm, hnorm] at h
    exact h
  have hsub : Real.sqrt (centralMassOf (y - z)) ≤ ‖y - z‖ := hyz (y - z)
  linarith

/-- **GRH.18**: an actual source `ε`-close in the labelled direct sum to the
sharp source of `g` keeps central boundary mass at least
`(√β_m ‖g‖ − ε)₊²` — sharp-chain softness cannot be diluted over
arbitrarily many boundary times. -/
theorem central_mass_lower_exact (V : ∀ j, E →ₗᵢ[ℂ] Ej j) (g : E)
    (y : PiLp 2 Ej) (ε : ℝ)
    (hclose : ‖y - sharpSource V g‖ ≤ ε) :
    max 0 (Real.sqrt (betaMass m) * ‖g‖ - ε) ^ 2 ≤ centralMassOf y := by
  have hsharp : Real.sqrt (centralMassOf (sharpSource V g))
      = Real.sqrt (betaMass m) * ‖g‖ := by
    rw [sharpSource_centralMass, Real.sqrt_mul (betaMass_nonneg m),
      Real.sqrt_sq (norm_nonneg g)]
  have hlip := sqrt_centralMass_lipschitz (sharpSource V g) y
  rw [hsharp, norm_sub_rev] at hlip
  have hlow : Real.sqrt (betaMass m) * ‖g‖ - ε
      ≤ Real.sqrt (centralMassOf y) := by linarith
  rcases le_or_gt (Real.sqrt (betaMass m) * ‖g‖ - ε) 0 with hle | hgt
  · rw [max_eq_left hle]
    simpa using centralMassOf_nonneg y
  · rw [max_eq_right hgt.le]
    calc (Real.sqrt (betaMass m) * ‖g‖ - ε) ^ 2
        ≤ Real.sqrt (centralMassOf y) ^ 2 :=
          pow_le_pow_left₀ hgt.le hlow 2
      _ = centralMassOf y :=
          Real.sq_sqrt (centralMassOf_nonneg y)

/-- **`thm:GRH-sharp-chain-central-bank`, assembled**: GRH.15 (`β_m ≥ 1/3`
with `b_{m,j} = |u_j|²`), GRH.16 (the operator central Gram is positive with
the weighted boundary-energy quadratic form), GRH.17 (the sharp source floor
`λ_min/β_m` refloors the `β_m`-normalized bank), and GRH.18 (the dilution
bound in the labelled direct sum, with the sharp-source mass proved from the
isometries). -/
theorem grh_sharp_chain_central_bank_exact [Nontrivial E] (hm : 1 ≤ m)
    (V : ∀ j, E →ₗᵢ[ℂ] Ej j) (T : ∀ j, Ej j →L[ℂ] Yj j) :
    ((1 : ℝ) / 3 ≤ betaMass m
      ∧ ∀ j, bWeight m j = (Real.sqrt (2 / ((m : ℝ) + 1))
          * Real.sin (((j.val : ℝ) + 1) * Real.pi / ((m : ℝ) + 1))) ^ 2)
    ∧ (centralGram V T).IsPositive
    ∧ (∀ g : E, RCLike.re (⟪g, centralGram V T g⟫_ℂ)
        = ∑ j ∈ SharpChain.centralSet m, bWeight m j * ‖rowRead V T j g‖ ^ 2)
    ∧ (∀ g : E,
        spectralFloor (centralGram V T) / betaMass m
            * (betaMass m * ‖g‖ ^ 2)
          ≤ RCLike.re (⟪g, centralGram V T g⟫_ℂ))
    ∧ ∀ (g : E) (y : PiLp 2 Ej) (ε : ℝ), ‖y - sharpSource V g‖ ≤ ε →
        max 0 (Real.sqrt (betaMass m) * ‖g‖ - ε) ^ 2 ≤ centralMassOf y := by
  have hβ : 0 < betaMass m := lt_of_lt_of_le (by norm_num) (betaMass_ge m hm)
  exact ⟨⟨betaMass_ge m hm, bWeight_eq_sq m⟩,
    centralGram_isPositive V T,
    centralGram_inner V T,
    fun g => central_floor_exact V T hβ g,
    fun g y ε hc => central_mass_lower_exact V g y ε hc⟩

end SharpChainOp

end MediumExact13
end NCG
