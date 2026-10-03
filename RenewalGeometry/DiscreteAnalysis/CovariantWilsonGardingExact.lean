/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.DiscreteAnalysis.VariableWilsonGardingExact

/-!
# The covariant (spin-link) Wilson operator: Gårding estimate, self-adjointness, grading

Paper `predictive_spectral_geometry`, label `thm:supp-general-Wilson-ellipticity`, for the
operator of `eq:supp-general-Wilson` *with spin links*:
`D̃^W_h = ½ Σ_j (M_{ĉ^j} P^Ω_j + P^Ω_j M_{ĉ^j}) + ϖ Γ_⊥ W^Ω_h`, built from the covariant shifts
`T^Ω_j u(x) = U_j(x) u(x + e_j)` and their adjoints `(T^Ω_j)^* u(x) = U_j(x - e_j)^* u(x - e_j)`
(`covShift`, `covShiftAdj`, exactly as `CovariantWilsonCoreConsistency.covShift`, here on the
periodic lattice torus `(ℤ/nℤ)^d`), `P^Ω_j = (T^Ω_j - (T^Ω_j)^*)/(2ih)` and
`W^Ω_h = (2h)⁻¹ Σ_j (2 - T^Ω_j - (T^Ω_j)^*)` (`eq:supp-covariant-differences`).

* `covVarWilson_sub_varWilson`, `norm_eucl_covVarWilson_sub_varWilson_le`: if the links satisfy
  `‖U_j(x) - I‖ ≤ C_U h` (the paper's "`T^Ω_{j,h} - S_{j,h} = O(h)` in operator norm"), then
  `‖(D̃^Ω - D̃^S) u‖ ≤ d C_U (B + |ϖ| G) ‖u‖`, uniformly in `h`; the adjoint links are controlled
  by `euclNormSq_conjTranspose_mulVec_le` (no separate hypothesis).
* `linkBound_of_connection`: a link that is the parallel transport to second order,
  `U_j(x) = I + h Ω_j(x) + O(h²)` with bounded connection coefficients, satisfies the link
  bound with `C_U = C_2 + B_Ω` for `h ≤ 1`.
* `covariant_garding` (**`eq:supp-general-Garding` for the covariant operator**):
  `‖u‖²_{1,h} ≤ C (‖D̃^Ω u‖²_h + ‖u‖²_h)` with the explicit `h`-independent constant
  `covariantGardingConstant`; `covariant_garding_norm` is the unsquared form
  `‖u‖_{1,h} ≤ √C (‖D̃^Ω u‖_h + ‖u‖_h)`.
* `covVarWilson_symmetric`: with Hermitian coefficients, Hermitian `Γ_⊥` commuting with the
  links, the covariant operator is symmetric for the grid inner product (self-adjointness).
* `matMul_covVarWilson` (**grading clause**): a Hermitian `γ̂` anticommuting with every
  `ĉ^j(x)` and with `Γ_⊥` and commuting with the links anticommutes with `D̃^Ω`.
* The fixed doubled Clifford convention `eq:supp-doubled-clifford`:
  `ĉ^j = c^j ⊗ σ₁`, `Γ_⊥ = I ⊗ σ₂`, `γ̂ = I ⊗ σ₃`, links `U ⊗ I` (`doubled`, on `ℂ^{M·2}` via
  `finProdFinEquiv`).  `doubled_cliffordData` derives `DoubledCliffordData` from the undoubled
  Clifford relations, and `doubled_grading` derives the grading clause
  `γ̂ D̃^Ω = -D̃^Ω γ̂` for the paper's `γ̂ = I ⊗ σ₃`; `doubled_symmetric` the self-adjointness.
-/

open Finset Matrix ZMod ComplexConjugate
open RenewalGeometry.LatticeTorusPlancherel RenewalGeometry.FrozenWilsonGarding
open RenewalGeometry.VariableWilsonGarding

set_option linter.unusedSectionVars false

namespace RenewalGeometry.CovariantWilsonGarding

variable {d n N : ℕ} [NeZero n]

/-! ### Matrix bounds in Euclidean form -/

theorem euclNormSq_eq_norm_sq (v : Fin N → ℂ) :
    euclNormSq v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N))‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  rfl

/-- An operator bound for `A` gives the same bound for `Aᴴ`. -/
theorem euclNormSq_conjTranspose_mulVec_le (A : Matrix (Fin N) (Fin N) ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ w, euclNormSq (A *ᵥ w) ≤ C ^ 2 * euclNormSq w) (w : Fin N → ℂ) :
    euclNormSq (Aᴴ *ᵥ w) ≤ C ^ 2 * euclNormSq w := by
  set T := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin N) A
  have hT : ‖T‖ ≤ C := by
    refine ContinuousLinearMap.opNorm_le_bound _ hC fun x => ?_
    have h1 := hA (WithLp.ofLp x)
    rw [euclNormSq_eq_norm_sq, euclNormSq_eq_norm_sq, WithLp.toLp_ofLp] at h1
    have h2 : ‖T x‖ ^ 2 ≤ (C * ‖x‖) ^ 2 := by
      rw [mul_pow]
      have : T x = WithLp.toLp 2 (A *ᵥ WithLp.ofLp x) := rfl
      rw [this]
      exact h1
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  have hT' : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin N) Aᴴ‖ ≤ C := by
    rw [← Matrix.star_eq_conjTranspose, map_star, ContinuousLinearMap.star_eq_adjoint,
      LinearIsometryEquiv.norm_map]
    exact hT
  have h3 := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin N) Aᴴ).le_opNorm (WithLp.toLp 2 w)
  have h4 : ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin N) Aᴴ) (WithLp.toLp 2 w)‖ ≤
      C * ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin N))‖ :=
    h3.trans (mul_le_mul_of_nonneg_right hT' (norm_nonneg _))
  rw [euclNormSq_eq_norm_sq, euclNormSq_eq_norm_sq, ← mul_pow]
  rw [Matrix.toEuclideanCLM_toLp] at h4
  exact pow_le_pow_left₀ (norm_nonneg _) h4 2

/-! ### The covariant operators on the torus -/

/-- Spin links on the torus: `U j x` is the transport on the edge `x → x + e_j`. -/
abbrev TorusLinks (d n N : ℕ) := Fin d → Grid d n → Matrix (Fin N) (Fin N) ℂ

/-- The covariant shift `T^Ω_j u(x) = U_j(x) u(x + e_j)`. -/
def covShift (U : TorusLinks d n N) (j : Fin d) (u : TorusSection d n N) : TorusSection d n N :=
  fun x => U j x *ᵥ u (x + Pi.single j 1)

/-- The adjoint covariant shift `(T^Ω_j)^* u(x) = U_j(x - e_j)^* u(x - e_j)`. -/
def covShiftAdj (U : TorusLinks d n N) (j : Fin d) (u : TorusSection d n N) :
    TorusSection d n N :=
  fun x => (U j (x - Pi.single j 1))ᴴ *ᵥ u (x - Pi.single j 1)

/-- The covariant symmetric difference `P^Ω_j = (T^Ω_j - (T^Ω_j)^*)/(2ih)`. -/
noncomputable def covSymmetricDifference (h : ℝ) (U : TorusLinks d n N) (j : Fin d)
    (u : TorusSection d n N) : TorusSection d n N :=
  fun x => (2 * Complex.I * (h : ℂ))⁻¹ • (covShift U j u x - covShiftAdj U j u x)

/-- The covariant Wilson term `W^Ω = (2h)⁻¹ Σ_j (2 - T^Ω_j - (T^Ω_j)^*)`. -/
noncomputable def covWilsonTerm (h : ℝ) (U : TorusLinks d n N) (u : TorusSection d n N) :
    TorusSection d n N :=
  fun x => (2 * (h : ℂ))⁻¹ • ∑ j, ((2 : ℂ) • u x - covShift U j u x - covShiftAdj U j u x)

/-- **The covariant doubled Wilson operator of `eq:supp-general-Wilson`** on the torus:
`½ Σ_j (M_{ĉ^j} P^Ω_j + P^Ω_j M_{ĉ^j}) + ϖ Γ_⊥ W^Ω`. -/
noncomputable def covVarWilson (h ϖ : ℝ) (c : CoefficientField d n N) (U : TorusLinks d n N)
    (Γ : Matrix (Fin N) (Fin N) ℂ) (u : TorusSection d n N) : TorusSection d n N :=
  (2 : ℂ)⁻¹ • (∑ j, (varMul (coeff c j) (covSymmetricDifference h U j u) +
      covSymmetricDifference h U j (varMul (coeff c j) u))) +
    (ϖ : ℂ) • matMul Γ (covWilsonTerm h U u)

theorem covSymmetricDifference_one (h : ℝ) (j : Fin d) (u : TorusSection d n N) :
    covSymmetricDifference h (fun _ _ => 1) j u = symmetricDifference h j u := by
  funext x
  simp [covSymmetricDifference, symmetricDifference, covShift, covShiftAdj, shift, shiftAdj]

theorem covWilsonTerm_one (h : ℝ) (u : TorusSection d n N) :
    covWilsonTerm h (fun _ _ => 1) u = wilsonTerm h u := by
  funext x
  simp [covWilsonTerm, wilsonTerm, covShift, covShiftAdj, shift, shiftAdj]

/-- With trivial links the covariant operator is the ordinary one. -/
theorem covVarWilson_one (h ϖ : ℝ) (c : CoefficientField d n N) (Γ : Matrix (Fin N) (Fin N) ℂ)
    (u : TorusSection d n N) :
    covVarWilson h ϖ c (fun _ _ => 1) Γ u = varWilson h ϖ c Γ u := by
  simp only [covVarWilson, varWilson, covSymmetricDifference_one, covWilsonTerm_one]

/-! ### Link corrections -/

/-- `P^Ω_j - P_j = (2ih)⁻¹ [ (U_j - I) S_j - S_j^* (U_j^* - I) ]`. -/
noncomputable def linkCorrection (h : ℝ) (U : TorusLinks d n N) (j : Fin d)
    (u : TorusSection d n N) : TorusSection d n N :=
  (2 * Complex.I * (h : ℂ))⁻¹ • (varMul (fun x => U j x - 1) (shift j u) -
    shiftAdj j (varMul (fun x => (U j x)ᴴ - 1) u))

/-- `W^Ω - W = -(2h)⁻¹ Σ_j [ (U_j - I) S_j + S_j^* (U_j^* - I) ]`. -/
noncomputable def wilsonLinkCorrection (h : ℝ) (U : TorusLinks d n N) (u : TorusSection d n N) :
    TorusSection d n N :=
  (2 * (h : ℂ))⁻¹ • ∑ j, (-(varMul (fun x => U j x - 1) (shift j u)) -
    shiftAdj j (varMul (fun x => (U j x)ᴴ - 1) u))

theorem covSymmetricDifference_eq (h : ℝ) (U : TorusLinks d n N) (j : Fin d)
    (u : TorusSection d n N) :
    covSymmetricDifference h U j u = symmetricDifference h j u + linkCorrection h U j u := by
  funext x
  simp only [covSymmetricDifference, symmetricDifference, linkCorrection, covShift, covShiftAdj,
    shift, shiftAdj, varMul, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Matrix.sub_mulVec,
    Matrix.one_mulVec]
  rw [← smul_add]
  congr 1
  abel

theorem covWilsonTerm_eq (h : ℝ) (U : TorusLinks d n N) (u : TorusSection d n N) :
    covWilsonTerm h U u = wilsonTerm h u + wilsonLinkCorrection h U u := by
  funext x
  simp only [covWilsonTerm, wilsonTerm, wilsonLinkCorrection, covShift, covShiftAdj,
    shift, shiftAdj, varMul, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply,
    Finset.sum_apply, Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [← smul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  abel

/-- The operator difference `D̃^Ω - D̃`. -/
noncomputable def linkDifference (h ϖ : ℝ) (c : CoefficientField d n N) (U : TorusLinks d n N)
    (Γ : Matrix (Fin N) (Fin N) ℂ) (u : TorusSection d n N) : TorusSection d n N :=
  (2 : ℂ)⁻¹ • (∑ j, (varMul (coeff c j) (linkCorrection h U j u) +
      linkCorrection h U j (varMul (coeff c j) u))) +
    (ϖ : ℂ) • matMul Γ (wilsonLinkCorrection h U u)

theorem matMul_add' (Γ : Matrix (Fin N) (Fin N) ℂ) (u v : TorusSection d n N) :
    matMul Γ (u + v) = matMul Γ u + matMul Γ v := by
  funext x; simp [matMul, Matrix.mulVec_add]

theorem covVarWilson_sub_varWilson (h ϖ : ℝ) (c : CoefficientField d n N) (U : TorusLinks d n N)
    (Γ : Matrix (Fin N) (Fin N) ℂ) (u : TorusSection d n N) :
    covVarWilson h ϖ c U Γ u = varWilson h ϖ c Γ u + linkDifference h ϖ c U Γ u := by
  simp only [covVarWilson, varWilson, linkDifference, covSymmetricDifference_eq,
    covWilsonTerm_eq, varMul_add, matMul_add', smul_add, Finset.sum_add_distrib]
  abel

/-! ### Bounds -/

/-- The link hypothesis `‖U_j(x) - I‖ ≤ C_U h` (operator norm on `ℂ^N`). -/
def LinkBound (h : ℝ) (U : TorusLinks d n N) (CU : ℝ) : Prop :=
  ∀ (j : Fin d) (x : Grid d n) (w : Fin N → ℂ),
    euclNormSq ((U j x - 1) *ᵥ w) ≤ (CU * h) ^ 2 * euclNormSq w

theorem LinkBound.adjoint {h CU : ℝ} {U : TorusLinks d n N} (hU : LinkBound h U CU)
    (hCU : 0 ≤ CU) (hh : 0 ≤ h) (j : Fin d) (x : Grid d n) (w : Fin N → ℂ) :
    euclNormSq (((U j x)ᴴ - 1) *ᵥ w) ≤ (CU * h) ^ 2 * euclNormSq w := by
  have : (U j x)ᴴ - 1 = (U j x - 1)ᴴ := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
  rw [this]
  exact euclNormSq_conjTranspose_mulVec_le _ (by positivity) (hU j x) w

theorem norm_eucl_linkCorrection_le (h : ℝ) (hh : 0 < h) {U : TorusLinks d n N} {CU : ℝ}
    (hCU : 0 ≤ CU) (hU : LinkBound h U CU) (j : Fin d) (u : TorusSection d n N) :
    ‖eucl (linkCorrection h U j u)‖ ≤ CU * ‖eucl u‖ := by
  unfold linkCorrection
  rw [eucl_smul, norm_smul, VariableWilsonGarding.norm_inv_two_I_mul h hh, eucl_sub]
  have h1 : ‖eucl (varMul (fun x => U j x - 1) (shift j u))‖ ≤ CU * h * ‖eucl u‖ := by
    calc _ ≤ CU * h * ‖eucl (shift j u)‖ :=
          norm_eucl_varMul_le _ (by positivity) (fun x w => hU j x w) _
      _ = CU * h * ‖eucl u‖ := by rw [norm_eucl_shift]
  have h2 : ‖eucl (shiftAdj j (varMul (fun x => (U j x)ᴴ - 1) u))‖ ≤ CU * h * ‖eucl u‖ := by
    rw [norm_eucl_shiftAdj]
    exact norm_eucl_varMul_le _ (by positivity) (fun x w => hU.adjoint hCU hh.le j x w) _
  calc (2 * h)⁻¹ * ‖eucl (varMul (fun x => U j x - 1) (shift j u)) -
        eucl (shiftAdj j (varMul (fun x => (U j x)ᴴ - 1) u))‖
      ≤ (2 * h)⁻¹ * (CU * h * ‖eucl u‖ + CU * h * ‖eucl u‖) := by
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add h1 h2)
    _ = CU * ‖eucl u‖ := by field_simp; ring

theorem norm_eucl_wilsonLinkCorrection_le (h : ℝ) (hh : 0 < h) {U : TorusLinks d n N} {CU : ℝ}
    (hCU : 0 ≤ CU) (hU : LinkBound h U CU) (u : TorusSection d n N) :
    ‖eucl (wilsonLinkCorrection h U u)‖ ≤ d * CU * ‖eucl u‖ := by
  unfold wilsonLinkCorrection
  rw [eucl_smul, norm_smul, VariableWilsonGarding.norm_inv_two_mul h hh, eucl_sum]
  have hj : ∀ j : Fin d, ‖eucl (-(varMul (fun x => U j x - 1) (shift j u)) -
      shiftAdj j (varMul (fun x => (U j x)ᴴ - 1) u))‖ ≤ 2 * (CU * h * ‖eucl u‖) := by
    intro j
    rw [eucl_sub, eucl_neg]
    have h1 : ‖eucl (varMul (fun x => U j x - 1) (shift j u))‖ ≤ CU * h * ‖eucl u‖ := by
      calc _ ≤ CU * h * ‖eucl (shift j u)‖ :=
            norm_eucl_varMul_le _ (by positivity) (fun x w => hU j x w) _
        _ = CU * h * ‖eucl u‖ := by rw [norm_eucl_shift]
    have h2 : ‖eucl (shiftAdj j (varMul (fun x => (U j x)ᴴ - 1) u))‖ ≤ CU * h * ‖eucl u‖ := by
      rw [norm_eucl_shiftAdj]
      exact norm_eucl_varMul_le _ (by positivity) (fun x w => hU.adjoint hCU hh.le j x w) _
    calc _ ≤ ‖-eucl (varMul (fun x => U j x - 1) (shift j u))‖ +
          ‖eucl (shiftAdj j (varMul (fun x => (U j x)ᴴ - 1) u))‖ := norm_sub_le _ _
      _ ≤ _ := by rw [norm_neg]; linarith
  calc (2 * h)⁻¹ * ‖∑ j, eucl (-(varMul (fun x => U j x - 1) (shift j u)) -
        shiftAdj j (varMul (fun x => (U j x)ᴴ - 1) u))‖
      ≤ (2 * h)⁻¹ * ∑ _j : Fin d, 2 * (CU * h * ‖eucl u‖) := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hj j)
    _ = d * CU * ‖eucl u‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

/-- **`‖(D̃^Ω - D̃^S) u‖ ≤ d C_U (B + |ϖ| G) ‖u‖`**, uniformly in `h`. -/
theorem norm_eucl_linkDifference_le (h ϖ : ℝ) (hh : 0 < h) (c : CoefficientField d n N)
    (U : TorusLinks d n N) (Γ : Matrix (Fin N) (Fin N) ℂ) {B G CU : ℝ} (hB : 0 ≤ B)
    (hG : 0 ≤ G) (hCU : 0 ≤ CU) (hU : LinkBound h U CU)
    (hc : ∀ x j w, euclNormSq (c x j *ᵥ w) ≤ B ^ 2 * euclNormSq w)
    (hΓb : ∀ w, euclNormSq (Γ *ᵥ w) ≤ G ^ 2 * euclNormSq w) (u : TorusSection d n N) :
    ‖eucl (linkDifference h ϖ c U Γ u)‖ ≤ d * CU * (B + |ϖ| * G) * ‖eucl u‖ := by
  unfold linkDifference
  rw [eucl_add, eucl_smul, eucl_smul, eucl_sum]
  have hj : ∀ j : Fin d, ‖eucl (varMul (coeff c j) (linkCorrection h U j u) +
      linkCorrection h U j (varMul (coeff c j) u))‖ ≤ 2 * (B * CU * ‖eucl u‖) := by
    intro j
    rw [eucl_add]
    have h1 : ‖eucl (varMul (coeff c j) (linkCorrection h U j u))‖ ≤ B * (CU * ‖eucl u‖) :=
      (norm_eucl_varMul_le _ hB (fun x w => hc x j w) _).trans
        (mul_le_mul_of_nonneg_left (norm_eucl_linkCorrection_le h hh hCU hU j u) hB)
    have h2 : ‖eucl (linkCorrection h U j (varMul (coeff c j) u))‖ ≤ CU * (B * ‖eucl u‖) :=
      (norm_eucl_linkCorrection_le h hh hCU hU j _).trans
        (mul_le_mul_of_nonneg_left (norm_eucl_varMul_le _ hB (fun x w => hc x j w) _) hCU)
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ _ := add_le_add h1 h2
      _ = _ := by ring
  have hW : ‖eucl (matMul Γ (wilsonLinkCorrection h U u))‖ ≤ G * (d * CU * ‖eucl u‖) := by
    rw [← varMul_const]
    exact (norm_eucl_varMul_le _ hG (fun _ w => hΓb w) _).trans
      (mul_le_mul_of_nonneg_left (norm_eucl_wilsonLinkCorrection_le h hh hCU hU u) hG)
  calc ‖(2 : ℂ)⁻¹ • ∑ j, eucl (varMul (coeff c j) (linkCorrection h U j u) +
        linkCorrection h U j (varMul (coeff c j) u)) +
        (ϖ : ℂ) • eucl (matMul Γ (wilsonLinkCorrection h U u))‖
      ≤ (2 : ℝ)⁻¹ * ∑ _j : Fin d, 2 * (B * CU * ‖eucl u‖) + |ϖ| * (G * (d * CU * ‖eucl u‖)) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_smul, VariableWilsonGarding.norm_inv_two]
          gcongr
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hj j)
        · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
          gcongr
    _ = d * CU * (B + |ϖ| * G) * ‖eucl u‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ### The covariant Gårding estimate -/

/-- The explicit constant of the covariant estimate: the ordinary constant `gardingConstant`
enlarged by the link perturbation `d C_U (B + |ϖ| G)`. -/
noncomputable def covariantGardingConstant (d m : ℕ) (lam ϖ K L B G CU : ℝ) : ℝ :=
  gardingConstant d m lam ϖ K L B G * (2 + 2 * (d * CU * (B + |ϖ| * G)) ^ 2)

/-- **`eq:supp-general-Garding` for the covariant operator with spin links
(`thm:supp-general-Wilson-ellipticity`).**  Under the hypotheses of `variable_garding`
(partition of unity `Σ_α χ_α² = 1` with cutoff gradients `≤ h K`, coefficient bounds `B`,
Lipschitz constant `L`, modulus of continuity `ω` absorbed by the frozen estimate at uniformly
elliptic Hermitian frozen data) and links with `‖U_j(x) - I‖ ≤ C_U h`,
`‖u‖²_{1,h} ≤ C (‖D̃^Ω u‖²_h + ‖u‖²_h)` with `C = covariantGardingConstant`, independent of `h`
and `n`. -/
theorem covariant_garding (h ϖ lam Lam : ℝ) (hh : 0 < h) (hlam : 0 < lam) (hϖ : ϖ ≠ 0)
    (hLam : 0 ≤ Lam) (c : CoefficientField d n N) (U : TorusLinks d n N)
    (Γ : Matrix (Fin N) (Fin N) ℂ) (hΓ : Γᴴ = Γ)
    {m : ℕ} (χ : Fin m → Grid d n → ℝ) (hpart : ∀ x, ∑ α, χ α x ^ 2 = 1)
    (x₀ : Fin m → Grid d n) (hell : ∀ α, UniformlyElliptic (c (x₀ α)) Γ lam Lam)
    {ω K L B G CU : ℝ} (hω : 0 ≤ ω) (hK : 0 ≤ K) (hL : 0 ≤ L) (hB : 0 ≤ B) (hG : 0 ≤ G)
    (hCU : 0 ≤ CU)
    (hgrad : ∀ α (j : Fin d) x, |χ α (x + Pi.single j 1) - χ α x| ≤ h * K)
    (hc : ∀ x j w, euclNormSq (c x j *ᵥ w) ≤ B ^ 2 * euclNormSq w)
    (hΓb : ∀ w, euclNormSq (Γ *ᵥ w) ≤ G ^ 2 * euclNormSq w)
    (hfreeze : ∀ α (j : Fin d) x, NearSupport (χ α) j x →
      ∀ w, euclNormSq ((c x j - c (x₀ α) j) *ᵥ w) ≤ ω ^ 2 * euclNormSq w)
    (hLip : ∀ (j : Fin d) x w,
      euclNormSq ((c (x + Pi.single j 1) j - c x j) *ᵥ w) ≤ (h * L) ^ 2 * euclNormSq w)
    (habs : 4 * d * ω ^ 2 * frozenConstant lam ϖ ≤ 1) (hU : LinkBound h U CU)
    (u : TorusSection d n N) :
    h1NormSq h u ≤ covariantGardingConstant d m lam ϖ K L B G CU *
      (gridNormSq h (covVarWilson h ϖ c U Γ u) + gridNormSq h u) := by
  have hS := variable_garding h ϖ lam Lam hh hlam hϖ hLam c Γ hΓ χ hpart x₀ hell hω hK hL hB hG
    hgrad hc hΓb hfreeze hLip habs u
  set E := d * CU * (B + |ϖ| * G) with hE
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hdiff := norm_eucl_linkDifference_le h ϖ hh c U Γ hB hG hCU hU hc hΓb u
  rw [← hE] at hdiff
  have hrel : varWilson h ϖ c Γ u = covVarWilson h ϖ c U Γ u - linkDifference h ϖ c U Γ u := by
    rw [covVarWilson_sub_varWilson]; abel
  have hnorm : ‖eucl (varWilson h ϖ c Γ u)‖ ≤
      ‖eucl (covVarWilson h ϖ c U Γ u)‖ + E * ‖eucl u‖ := by
    rw [hrel, eucl_sub]
    exact (norm_sub_le _ _).trans (add_le_add le_rfl hdiff)
  have hsq : ‖eucl (varWilson h ϖ c Γ u)‖ ^ 2 ≤
      2 * ‖eucl (covVarWilson h ϖ c U Γ u)‖ ^ 2 + 2 * E ^ 2 * ‖eucl u‖ ^ 2 := by
    have h0 : 0 ≤ ‖eucl (varWilson h ϖ c Γ u)‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖eucl (covVarWilson h ϖ c U Γ u)‖ - E * ‖eucl u‖)]
  have hgC : 0 ≤ gardingConstant d m lam ϖ K L B G := by
    unfold gardingConstant commutatorConstant
    have := frozenConstant_nonneg lam ϖ
    positivity
  have hhd : 0 ≤ h ^ d := by positivity
  simp only [gridNormSq_eq_norm_eucl_sq] at hS ⊢
  unfold covariantGardingConstant
  rw [← hE]
  have hX : 0 ≤ ‖eucl (covVarWilson h ϖ c U Γ u)‖ ^ 2 := by positivity
  have hY : 0 ≤ ‖eucl u‖ ^ 2 := by positivity
  calc h1NormSq h u ≤ gardingConstant d m lam ϖ K L B G *
        (h ^ d * ‖eucl (varWilson h ϖ c Γ u)‖ ^ 2 + h ^ d * ‖eucl u‖ ^ 2) := hS
    _ ≤ gardingConstant d m lam ϖ K L B G *
        (h ^ d * (2 * ‖eucl (covVarWilson h ϖ c U Γ u)‖ ^ 2 + 2 * E ^ 2 * ‖eucl u‖ ^ 2) +
          h ^ d * ‖eucl u‖ ^ 2) := by gcongr
    _ ≤ gardingConstant d m lam ϖ K L B G * (2 + 2 * E ^ 2) *
        (h ^ d * ‖eucl (covVarWilson h ϖ c U Γ u)‖ ^ 2 + h ^ d * ‖eucl u‖ ^ 2) := by
        rw [mul_assoc (gardingConstant d m lam ϖ K L B G)]
        apply mul_le_mul_of_nonneg_left _ hgC
        have hE2 : 0 ≤ E ^ 2 := sq_nonneg E
        nlinarith [mul_nonneg hhd hX, mul_nonneg hhd hY, mul_nonneg (mul_nonneg hhd hY) hE2,
          mul_nonneg (mul_nonneg hhd hX) hE2]

/-- The unsquared form `‖u‖_{1,h} ≤ √C (‖D u‖_h + ‖u‖_h)` from the squared one. -/
theorem sqrt_h1NormSq_le_of_le {h C : ℝ} {D u : TorusSection d n N}
    (hle : h1NormSq h u ≤ C * (gridNormSq h D + gridNormSq h u)) (hh : 0 ≤ h) :
    Real.sqrt (h1NormSq h u) ≤
      Real.sqrt C * (Real.sqrt (gridNormSq h D) + Real.sqrt (gridNormSq h u)) := by
  have ha : 0 ≤ gridNormSq h D := by
    rw [gridNormSq_eq_norm_eucl_sq]; positivity
  have hb : 0 ≤ gridNormSq h u := by
    rw [gridNormSq_eq_norm_eucl_sq]; positivity
  calc Real.sqrt (h1NormSq h u) ≤ Real.sqrt (C * (gridNormSq h D + gridNormSq h u)) :=
        Real.sqrt_le_sqrt hle
    _ = Real.sqrt C * Real.sqrt (gridNormSq h D + gridNormSq h u) := by
        by_cases hC : 0 ≤ C
        · exact Real.sqrt_mul hC _
        · rw [not_le] at hC
          rw [Real.sqrt_eq_zero_of_nonpos (by nlinarith), Real.sqrt_eq_zero_of_nonpos hC.le,
            zero_mul]
    _ ≤ Real.sqrt C * (Real.sqrt (gridNormSq h D) + Real.sqrt (gridNormSq h u)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        rw [Real.sqrt_le_left (by positivity)]
        nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg (gridNormSq h D),
          Real.sqrt_nonneg (gridNormSq h u),
          mul_nonneg (Real.sqrt_nonneg (gridNormSq h D)) (Real.sqrt_nonneg (gridNormSq h u))]

/-- **`eq:supp-general-Garding`, unsquared, covariant operator:**
`‖u‖_{1,h} ≤ √C (‖D̃^Ω u‖_h + ‖u‖_h)`. -/
theorem covariant_garding_norm (h ϖ lam Lam : ℝ) (hh : 0 < h) (hlam : 0 < lam) (hϖ : ϖ ≠ 0)
    (hLam : 0 ≤ Lam) (c : CoefficientField d n N) (U : TorusLinks d n N)
    (Γ : Matrix (Fin N) (Fin N) ℂ) (hΓ : Γᴴ = Γ)
    {m : ℕ} (χ : Fin m → Grid d n → ℝ) (hpart : ∀ x, ∑ α, χ α x ^ 2 = 1)
    (x₀ : Fin m → Grid d n) (hell : ∀ α, UniformlyElliptic (c (x₀ α)) Γ lam Lam)
    {ω K L B G CU : ℝ} (hω : 0 ≤ ω) (hK : 0 ≤ K) (hL : 0 ≤ L) (hB : 0 ≤ B) (hG : 0 ≤ G)
    (hCU : 0 ≤ CU)
    (hgrad : ∀ α (j : Fin d) x, |χ α (x + Pi.single j 1) - χ α x| ≤ h * K)
    (hc : ∀ x j w, euclNormSq (c x j *ᵥ w) ≤ B ^ 2 * euclNormSq w)
    (hΓb : ∀ w, euclNormSq (Γ *ᵥ w) ≤ G ^ 2 * euclNormSq w)
    (hfreeze : ∀ α (j : Fin d) x, NearSupport (χ α) j x →
      ∀ w, euclNormSq ((c x j - c (x₀ α) j) *ᵥ w) ≤ ω ^ 2 * euclNormSq w)
    (hLip : ∀ (j : Fin d) x w,
      euclNormSq ((c (x + Pi.single j 1) j - c x j) *ᵥ w) ≤ (h * L) ^ 2 * euclNormSq w)
    (habs : 4 * d * ω ^ 2 * frozenConstant lam ϖ ≤ 1) (hU : LinkBound h U CU)
    (u : TorusSection d n N) :
    Real.sqrt (h1NormSq h u) ≤ Real.sqrt (covariantGardingConstant d m lam ϖ K L B G CU) *
      (Real.sqrt (gridNormSq h (covVarWilson h ϖ c U Γ u)) + Real.sqrt (gridNormSq h u)) :=
  sqrt_h1NormSq_le_of_le (covariant_garding h ϖ lam Lam hh hlam hϖ hLam c U Γ hΓ χ hpart x₀ hell
    hω hK hL hB hG hCU hgrad hc hΓb hfreeze hLip habs hU u) hh.le

/-- **Links from a smooth spin connection.**  If `U_j(x) = I + h Ω_j(x) + O(h²)` (constant `C₂`)
with `‖Ω_j(x)‖ ≤ B_Ω`, then `‖U_j(x) - I‖ ≤ (C₂ + B_Ω) h` for `0 ≤ h ≤ 1`: the paper's
"`T^Ω_{j,h} - S_{j,h} = O(h)` in a smooth spin frame". -/
theorem linkBound_of_connection {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) (U : TorusLinks d n N)
    (Ω : Fin d → Grid d n → Matrix (Fin N) (Fin N) ℂ) {C₂ BΩ : ℝ} (hC₂ : 0 ≤ C₂) (hBΩ : 0 ≤ BΩ)
    (hexp : ∀ j x w, euclNormSq ((U j x - 1 - (h : ℂ) • Ω j x) *ᵥ w) ≤
      (C₂ * h ^ 2) ^ 2 * euclNormSq w)
    (hΩ : ∀ j x w, euclNormSq (Ω j x *ᵥ w) ≤ BΩ ^ 2 * euclNormSq w) :
    LinkBound h U (C₂ + BΩ) := by
  intro j x w
  have h1 := hexp j x w
  have h2 := hΩ j x w
  rw [euclNormSq_eq_norm_sq, euclNormSq_eq_norm_sq] at h1 h2 ⊢
  set W : EuclideanSpace ℂ (Fin N) := WithLp.toLp 2 w
  have n1 : ‖(WithLp.toLp 2 ((U j x - 1 - (h : ℂ) • Ω j x) *ᵥ w) : EuclideanSpace ℂ (Fin N))‖ ≤
      C₂ * h ^ 2 * ‖W‖ := by
    rw [← mul_pow] at h1
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h1
  have n2 : ‖(WithLp.toLp 2 (Ω j x *ᵥ w) : EuclideanSpace ℂ (Fin N))‖ ≤ BΩ * ‖W‖ := by
    rw [← mul_pow] at h2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  have hsplit : (WithLp.toLp 2 ((U j x - 1) *ᵥ w) : EuclideanSpace ℂ (Fin N)) =
      WithLp.toLp 2 ((U j x - 1 - (h : ℂ) • Ω j x) *ᵥ w) +
        (h : ℂ) • (WithLp.toLp 2 (Ω j x *ᵥ w) : EuclideanSpace ℂ (Fin N)) := by
    rw [← WithLp.toLp_smul, ← WithLp.toLp_add, Matrix.sub_mulVec (U j x - 1),
      Matrix.smul_mulVec, sub_add_cancel]
  have hfin : ‖(WithLp.toLp 2 ((U j x - 1) *ᵥ w) : EuclideanSpace ℂ (Fin N))‖ ≤
      (C₂ + BΩ) * h * ‖W‖ := by
    rw [hsplit]
    have hW : 0 ≤ ‖W‖ := norm_nonneg _
    have hh2 : h ^ 2 ≤ h := by nlinarith
    calc _ ≤ ‖(WithLp.toLp 2 ((U j x - 1 - (h : ℂ) • Ω j x) *ᵥ w) : EuclideanSpace ℂ (Fin N))‖ +
          ‖(h : ℂ) • (WithLp.toLp 2 (Ω j x *ᵥ w) : EuclideanSpace ℂ (Fin N))‖ := norm_add_le _ _
      _ ≤ C₂ * h ^ 2 * ‖W‖ + h * (BΩ * ‖W‖) := by
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh]
          gcongr
      _ ≤ (C₂ + BΩ) * h * ‖W‖ := by
          nlinarith [mul_le_mul_of_nonneg_left hh2 (mul_nonneg hC₂ hW)]
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hfin 2

/-! ### Self-adjointness of the covariant operator -/

/-- The grid inner product is conjugate-symmetric. -/
theorem gridInner_conj (u v : TorusSection d n N) : gridInner u v = star (gridInner v u) := by
  simp only [gridInner, star_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.star_dotProduct]

/-- `(T^Ω_j)^*` is the adjoint of `T^Ω_j` for the grid inner product. -/
theorem gridInner_covShift (U : TorusLinks d n N) (j : Fin d) (u v : TorusSection d n N) :
    gridInner (covShift U j u) v = gridInner u (covShiftAdj U j v) := by
  simp only [gridInner, covShift, covShiftAdj]
  have hb : Function.Bijective (fun x : Grid d n => x + Pi.single j (1 : ZMod n)) :=
    (Equiv.addRight (Pi.single j (1 : ZMod n) : Grid d n)).bijective
  have := hb.sum_comp (fun y => star (u y) ⬝ᵥ ((U j (y - Pi.single j 1))ᴴ *ᵥ
    v (y - Pi.single j 1)))
  simp only [add_sub_cancel_right] at this
  rw [← this]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]

theorem gridInner_covShiftAdj (U : TorusLinks d n N) (j : Fin d) (u v : TorusSection d n N) :
    gridInner (covShiftAdj U j u) v = gridInner u (covShift U j v) := by
  rw [gridInner_conj, ← gridInner_covShift, ← gridInner_conj]

/-- `P^Ω_j` is symmetric. -/
theorem gridInner_covSymmetricDifference (h : ℝ) (U : TorusLinks d n N) (j : Fin d)
    (u v : TorusSection d n N) :
    gridInner (covSymmetricDifference h U j u) v =
      gridInner u (covSymmetricDifference h U j v) := by
  have hl : covSymmetricDifference h U j u =
      (2 * Complex.I * (h : ℂ))⁻¹ • (covShift U j u - covShiftAdj U j u) := by funext x; rfl
  have hr : covSymmetricDifference h U j v =
      (2 * Complex.I * (h : ℂ))⁻¹ • (covShift U j v - covShiftAdj U j v) := by funext x; rfl
  rw [hl, hr, gridInner_smul_left, gridInner_smul_right, conj_inv_two_I_mul, gridInner_sub_left,
    gridInner_sub_right, gridInner_covShift, gridInner_covShiftAdj]
  ring

/-- `W^Ω` is symmetric. -/
theorem gridInner_covWilsonTerm (h : ℝ) (U : TorusLinks d n N) (u v : TorusSection d n N) :
    gridInner (covWilsonTerm h U u) v = gridInner u (covWilsonTerm h U v) := by
  have hl : covWilsonTerm h U u =
      (2 * (h : ℂ))⁻¹ • ∑ j, ((2 : ℂ) • u - covShift U j u - covShiftAdj U j u) := by
    funext x; simp [covWilsonTerm, Finset.sum_apply]
  have hr : covWilsonTerm h U v =
      (2 * (h : ℂ))⁻¹ • ∑ j, ((2 : ℂ) • v - covShift U j v - covShiftAdj U j v) := by
    funext x; simp [covWilsonTerm, Finset.sum_apply]
  have hstar : star ((2 * (h : ℂ))⁻¹) = (2 * (h : ℂ))⁻¹ := by
    simp [Complex.conj_ofReal]
  rw [hl, hr, gridInner_smul_left, gridInner_smul_right, hstar, gridInner_sum_left,
    gridInner_sum_right]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gridInner_sub_left, gridInner_sub_left, gridInner_sub_right, gridInner_sub_right,
    gridInner_smul_left, gridInner_smul_right, gridInner_covShift, gridInner_covShiftAdj]
  have h2 : star (2 : ℂ) = 2 := by simp
  rw [h2]
  ring

/-- A constant matrix commuting with every link (hence, if Hermitian, with every adjoint link)
commutes with the covariant shifts. -/
theorem matMul_covShift (M : Matrix (Fin N) (Fin N) ℂ) (U : TorusLinks d n N)
    (hM : ∀ j x, M * U j x = U j x * M) (j : Fin d) (v : TorusSection d n N) :
    matMul M (covShift U j v) = covShift U j (matMul M v) := by
  funext x
  simp only [matMul, covShift, Matrix.mulVec_mulVec, hM]

theorem matMul_covShiftAdj (M : Matrix (Fin N) (Fin N) ℂ) (U : TorusLinks d n N)
    (hM : ∀ j x, M * (U j x)ᴴ = (U j x)ᴴ * M) (j : Fin d) (v : TorusSection d n N) :
    matMul M (covShiftAdj U j v) = covShiftAdj U j (matMul M v) := by
  funext x
  simp only [matMul, covShiftAdj, Matrix.mulVec_mulVec, hM]

/-- A Hermitian matrix commuting with `U` commutes with `Uᴴ`. -/
theorem comm_conjTranspose_of_comm {M A : Matrix (Fin N) (Fin N) ℂ} (hMh : Mᴴ = M)
    (hMA : M * A = A * M) : M * Aᴴ = Aᴴ * M := by
  have := congrArg Matrix.conjTranspose hMA
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hMh] at this
  exact this.symm

theorem matMul_covSymmetricDifference (h : ℝ) (M : Matrix (Fin N) (Fin N) ℂ)
    (U : TorusLinks d n N) (hM : ∀ j x, M * U j x = U j x * M)
    (hM' : ∀ j x, M * (U j x)ᴴ = (U j x)ᴴ * M) (j : Fin d) (v : TorusSection d n N) :
    matMul M (covSymmetricDifference h U j v) = covSymmetricDifference h U j (matMul M v) := by
  have e1 := congrFun (matMul_covShift M U hM j v)
  have e2 := congrFun (matMul_covShiftAdj M U hM' j v)
  funext x
  have e1x := e1 x
  have e2x := e2 x
  simp only [matMul] at e1x e2x
  simp only [matMul, covSymmetricDifference, Matrix.mulVec_smul, Matrix.mulVec_sub, e1x, e2x]

theorem matMul_covWilsonTerm (h : ℝ) (M : Matrix (Fin N) (Fin N) ℂ)
    (U : TorusLinks d n N) (hM : ∀ j x, M * U j x = U j x * M)
    (hM' : ∀ j x, M * (U j x)ᴴ = (U j x)ᴴ * M) (v : TorusSection d n N) :
    matMul M (covWilsonTerm h U v) = covWilsonTerm h U (matMul M v) := by
  have h1 := fun j => congrFun (matMul_covShift M U hM j v)
  have h2 := fun j => congrFun (matMul_covShiftAdj M U hM' j v)
  funext x
  simp only [matMul, covWilsonTerm, Matrix.mulVec_smul, Matrix.mulVec_sum, Matrix.mulVec_sub]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 := h1 j x
  have e2 := h2 j x
  simp only [matMul] at e1 e2
  rw [e1, e2]

/-- **Self-adjointness** (`thm:supp-general-Wilson-ellipticity`): with Hermitian coefficients
`ĉ^j(x)` and a Hermitian `Γ_⊥` commuting with the links, the covariant operator `D̃^Ω` is
symmetric for the grid inner product. -/
theorem covVarWilson_symmetric (h ϖ : ℝ) (c : CoefficientField d n N) (U : TorusLinks d n N)
    (Γ : Matrix (Fin N) (Fin N) ℂ) (hc : ∀ x j, (c x j)ᴴ = c x j) (hΓ : Γᴴ = Γ)
    (hΓU : ∀ j x, Γ * U j x = U j x * Γ) (u v : TorusSection d n N) :
    gridInner (covVarWilson h ϖ c U Γ u) v = gridInner u (covVarWilson h ϖ c U Γ v) := by
  have hΓU' : ∀ j x, Γ * (U j x)ᴴ = (U j x)ᴴ * Γ := fun j x =>
    comm_conjTranspose_of_comm hΓ (hΓU j x)
  have hstar2 : star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by simp
  have hstarϖ : star ((ϖ : ℝ) : ℂ) = (ϖ : ℂ) := Complex.conj_ofReal ϖ
  simp only [covVarWilson, gridInner_add_left, gridInner_add_right, gridInner_smul_left,
    gridInner_smul_right, hstar2, hstarϖ, gridInner_sum_left, gridInner_sum_right]
  congr 2
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [gridInner_varMul (coeff c j) (fun x => hc x j), gridInner_covSymmetricDifference,
      gridInner_covSymmetricDifference, gridInner_varMul (coeff c j) (fun x => hc x j), add_comm]
  · rw [← varMul_const, gridInner_varMul (fun _ => Γ) (fun _ => hΓ), gridInner_covWilsonTerm,
      varMul_const, matMul_covWilsonTerm h Γ U hΓU hΓU']

/-! ### The grading clause -/

theorem matMul_add'' (M : Matrix (Fin N) (Fin N) ℂ) (u v : TorusSection d n N) :
    matMul M (u + v) = matMul M u + matMul M v := matMul_add' M u v

theorem matMul_smul' (M : Matrix (Fin N) (Fin N) ℂ) (a : ℂ) (v : TorusSection d n N) :
    matMul M (a • v) = a • matMul M v := by
  funext x; simp [matMul, Matrix.mulVec_smul]

theorem matMul_neg' (M : Matrix (Fin N) (Fin N) ℂ) (v : TorusSection d n N) :
    matMul M (-v) = -matMul M v := by
  funext x; simp [matMul, Matrix.mulVec_neg]

theorem matMul_sum' {ι : Type*} (M : Matrix (Fin N) (Fin N) ℂ) (s : Finset ι)
    (f : ι → TorusSection d n N) : matMul M (∑ i ∈ s, f i) = ∑ i ∈ s, matMul M (f i) := by
  funext x; simp [matMul, Matrix.mulVec_sum, Finset.sum_apply]

theorem covSymmetricDifference_neg (h : ℝ) (U : TorusLinks d n N) (j : Fin d)
    (v : TorusSection d n N) :
    covSymmetricDifference h U j (-v) = -covSymmetricDifference h U j v := by
  funext x
  simp only [covSymmetricDifference, covShift, covShiftAdj, Pi.neg_apply, Matrix.mulVec_neg]
  rw [← smul_neg]
  congr 1
  abel

theorem varMul_matMul_of_anticomm (c : Grid d n → Matrix (Fin N) (Fin N) ℂ)
    (γ : Matrix (Fin N) (Fin N) ℂ) (hc : ∀ x, c x * γ = -(γ * c x)) (v : TorusSection d n N) :
    varMul c (matMul γ v) = -matMul γ (varMul c v) := by
  funext x
  simp only [varMul, matMul, Pi.neg_apply, Matrix.mulVec_mulVec, hc x, Matrix.neg_mulVec]

theorem matMul_matMul_of_anticomm (Γ γ : Matrix (Fin N) (Fin N) ℂ) (hΓ : Γ * γ = -(γ * Γ))
    (v : TorusSection d n N) : matMul Γ (matMul γ v) = -matMul γ (matMul Γ v) := by
  funext x
  simp only [matMul, Pi.neg_apply, Matrix.mulVec_mulVec, hΓ, Matrix.neg_mulVec]

/-- **Grading clause** (`thm:supp-general-Wilson-ellipticity`): a Hermitian `γ̂` anticommuting
with every `ĉ^j(x)` and with `Γ_⊥` and commuting with every link anticommutes with the covariant
operator: `D̃^Ω γ̂ = -γ̂ D̃^Ω`. -/
theorem covVarWilson_matMul (h ϖ : ℝ) (c : CoefficientField d n N) (U : TorusLinks d n N)
    (Γ γ : Matrix (Fin N) (Fin N) ℂ) (hγ : γᴴ = γ) (hcγ : ∀ x j, c x j * γ = -(γ * c x j))
    (hΓγ : Γ * γ = -(γ * Γ)) (hUγ : ∀ j x, γ * U j x = U j x * γ) (u : TorusSection d n N) :
    covVarWilson h ϖ c U Γ (matMul γ u) = -matMul γ (covVarWilson h ϖ c U Γ u) := by
  have hUγ' : ∀ j x, γ * (U j x)ᴴ = (U j x)ᴴ * γ := fun j x =>
    comm_conjTranspose_of_comm hγ (hUγ j x)
  have hP : ∀ j v, covSymmetricDifference h U j (matMul γ v) =
      matMul γ (covSymmetricDifference h U j v) := fun j v =>
    (matMul_covSymmetricDifference h γ U hUγ hUγ' j v).symm
  have hW : ∀ v, covWilsonTerm h U (matMul γ v) = matMul γ (covWilsonTerm h U v) := fun v =>
    (matMul_covWilsonTerm h γ U hUγ hUγ' v).symm
  have hC : ∀ j v, varMul (coeff c j) (matMul γ v) = -matMul γ (varMul (coeff c j) v) :=
    fun j v => varMul_matMul_of_anticomm (coeff c j) γ (fun x => hcγ x j) v
  simp only [covVarWilson, hP, hC, covSymmetricDifference_neg, hW,
    matMul_matMul_of_anticomm Γ γ hΓγ, matMul_add', matMul_smul', matMul_sum']
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, smul_add, smul_neg]
  abel

/-! ### The fixed doubled Clifford convention `eq:supp-doubled-clifford` -/

/-- `A ⊗ P` on `ℂ^M ⊗ ℂ² ≅ ℂ^{M·2}`. -/
def dbl {M : ℕ} (A : Matrix (Fin M) (Fin M) ℂ) (P : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin (M * 2)) (Fin (M * 2)) ℂ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.kroneckerMap (· * ·) A P)

/-- The Pauli matrices. -/
def σ₁ : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def σ₂ : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def σ₃ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem σ₁_mul_σ₁ : σ₁ * σ₁ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σ₁, Matrix.mul_apply, Fin.sum_univ_two]
theorem σ₂_mul_σ₂ : σ₂ * σ₂ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σ₂, Matrix.mul_apply, Fin.sum_univ_two]
theorem σ₂_mul_σ₁_add : σ₂ * σ₁ + σ₁ * σ₂ = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σ₁, σ₂]
theorem σ₁_mul_σ₃ : σ₁ * σ₃ = -(σ₃ * σ₁) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σ₁, σ₃, Matrix.mul_apply, Fin.sum_univ_two]
theorem σ₂_mul_σ₃ : σ₂ * σ₃ = -(σ₃ * σ₂) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σ₂, σ₃, Matrix.mul_apply, Fin.sum_univ_two]
theorem σ₁_conjTranspose : σ₁ᴴ = σ₁ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σ₁]
theorem σ₂_conjTranspose : σ₂ᴴ = σ₂ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σ₂]
theorem σ₃_conjTranspose : σ₃ᴴ = σ₃ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σ₃]

section doubled

variable {M : ℕ}

theorem dbl_mul (A B : Matrix (Fin M) (Fin M) ℂ) (P Q : Matrix (Fin 2) (Fin 2) ℂ) :
    dbl A P * dbl B Q = dbl (A * B) (P * Q) := by
  unfold dbl
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul]

theorem dbl_conjTranspose (A : Matrix (Fin M) (Fin M) ℂ) (P : Matrix (Fin 2) (Fin 2) ℂ) :
    (dbl A P)ᴴ = dbl Aᴴ Pᴴ := by
  unfold dbl
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
    Matrix.conjTranspose_kronecker]

theorem dbl_neg_right (A : Matrix (Fin M) (Fin M) ℂ) (P : Matrix (Fin 2) (Fin 2) ℂ) :
    dbl A (-P) = -dbl A P := by
  ext i j; simp [dbl]

theorem dbl_add_left (A B : Matrix (Fin M) (Fin M) ℂ) (P : Matrix (Fin 2) (Fin 2) ℂ) :
    dbl (A + B) P = dbl A P + dbl B P := by
  ext i j; simp [dbl, Matrix.kroneckerMap_apply, add_mul]

theorem dbl_add_right (A : Matrix (Fin M) (Fin M) ℂ) (P Q : Matrix (Fin 2) (Fin 2) ℂ) :
    dbl A (P + Q) = dbl A P + dbl A Q := by
  ext i j; simp [dbl, Matrix.kroneckerMap_apply, mul_add]

theorem dbl_smul_left (a : ℂ) (A : Matrix (Fin M) (Fin M) ℂ) (P : Matrix (Fin 2) (Fin 2) ℂ) :
    dbl (a • A) P = a • dbl A P := by
  ext i j; simp [dbl, Matrix.kroneckerMap_apply, mul_assoc]

theorem dbl_zero_right (A : Matrix (Fin M) (Fin M) ℂ) : dbl A 0 = 0 := by
  ext i j; simp [dbl, Matrix.kroneckerMap_apply]

theorem dbl_one_one : dbl (1 : Matrix (Fin M) (Fin M) ℂ) 1 = 1 := by
  unfold dbl
  rw [Matrix.one_kronecker_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

/-- The doubled Clifford coefficients `ĉ^j = c^j ⊗ σ₁`. -/
def doubledCoeff (c₀ : Grid d n → Fin d → Matrix (Fin M) (Fin M) ℂ) :
    CoefficientField d n (M * 2) := fun x j => dbl (c₀ x j) σ₁

/-- The normal Clifford generator `Γ_⊥ = I ⊗ σ₂`. -/
def doubledNormal : Matrix (Fin (M * 2)) (Fin (M * 2)) ℂ := dbl 1 σ₂

/-- The grading `γ̂ = I ⊗ σ₃`. -/
def doubledGrading : Matrix (Fin (M * 2)) (Fin (M * 2)) ℂ := dbl 1 σ₃

/-- The spin links act on the spin factor: `U ⊗ I`. -/
def doubledLinks (V : Fin d → Grid d n → Matrix (Fin M) (Fin M) ℂ) : TorusLinks d n (M * 2) :=
  fun j x => dbl (V j x) 1

/-- **The doubled Clifford relations.**  If the undoubled coefficients satisfy
`c^j c^k + c^k c^j = 2 g^{jk} I` (`eq:supp-clifford-coeff`), the doubled data
`ĉ^j = c^j ⊗ σ₁`, `Γ_⊥ = I ⊗ σ₂` satisfy `DoubledCliffordData` (the hypothesis of the frozen
symbol theorem `eq:supp-general-frozen-square` and of the Gårding estimate). -/
theorem doubled_cliffordData (c₀ : Fin d → Matrix (Fin M) (Fin M) ℂ)
    (g : Matrix (Fin d) (Fin d) ℝ)
    (hc : ∀ j k, c₀ j * c₀ k + c₀ k * c₀ j =
      ((2 * g j k : ℝ) : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)) :
    FrozenWilsonSymbol.DoubledCliffordData (fun j => dbl (c₀ j) σ₁) (dbl 1 σ₂) g where
  anticomm j k := by
    rw [dbl_mul, dbl_mul, σ₁_mul_σ₁, ← dbl_add_left, hc j k, dbl_smul_left, dbl_one_one]
  normal_anticomm j := by
    rw [dbl_mul, dbl_mul, Matrix.one_mul, Matrix.mul_one, ← dbl_add_right, σ₂_mul_σ₁_add,
      dbl_zero_right]
  normal_sq := by rw [dbl_mul, Matrix.one_mul, σ₂_mul_σ₂, dbl_one_one]

/-- **The fixed doubled Clifford convention supplies the grading.**  For the doubled data of
`eq:supp-doubled-clifford` (coefficients `c^j ⊗ σ₁`, `Γ_⊥ = I ⊗ σ₂`, links `U ⊗ I`) the grading
`γ̂ = I ⊗ σ₃` anticommutes with the covariant Wilson operator, for arbitrary undoubled
coefficients and links. -/
theorem doubled_grading (h ϖ : ℝ) (c₀ : Grid d n → Fin d → Matrix (Fin M) (Fin M) ℂ)
    (V : Fin d → Grid d n → Matrix (Fin M) (Fin M) ℂ) (u : TorusSection d n (M * 2)) :
    covVarWilson h ϖ (doubledCoeff c₀) (doubledLinks V) doubledNormal (matMul doubledGrading u) =
      -matMul doubledGrading (covVarWilson h ϖ (doubledCoeff c₀) (doubledLinks V) doubledNormal u)
      := by
  apply covVarWilson_matMul
  · rw [doubledGrading, dbl_conjTranspose, Matrix.conjTranspose_one, σ₃_conjTranspose]
  · intro x j
    rw [doubledCoeff, doubledGrading, dbl_mul, dbl_mul, Matrix.mul_one, Matrix.one_mul,
      σ₁_mul_σ₃, dbl_neg_right]
  · rw [doubledNormal, doubledGrading, dbl_mul, dbl_mul, σ₂_mul_σ₃, dbl_neg_right]
  · intro j x
    rw [doubledLinks, doubledGrading, dbl_mul, dbl_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul]

/-- **Self-adjointness in the doubled convention**: Hermitian undoubled coefficients give a
symmetric covariant operator (for arbitrary links). -/
theorem doubled_symmetric (h ϖ : ℝ) (c₀ : Grid d n → Fin d → Matrix (Fin M) (Fin M) ℂ)
    (hc₀ : ∀ x j, (c₀ x j)ᴴ = c₀ x j) (V : Fin d → Grid d n → Matrix (Fin M) (Fin M) ℂ)
    (u v : TorusSection d n (M * 2)) :
    gridInner (covVarWilson h ϖ (doubledCoeff c₀) (doubledLinks V) doubledNormal u) v =
      gridInner u (covVarWilson h ϖ (doubledCoeff c₀) (doubledLinks V) doubledNormal v) := by
  apply covVarWilson_symmetric
  · intro x j
    rw [doubledCoeff, dbl_conjTranspose, hc₀, σ₁_conjTranspose]
  · rw [doubledNormal, dbl_conjTranspose, Matrix.conjTranspose_one, σ₂_conjTranspose]
  · intro j x
    rw [doubledNormal, doubledLinks, dbl_mul, dbl_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul]

/-! ### Non-vacuity of the covariant Gårding hypotheses -/

theorem euclNormSq_eq_re_dotProduct (v : Fin N → ℂ) : euclNormSq v = (star v ⬝ᵥ v).re := by
  simp only [euclNormSq, dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast

/-- A unitary matrix preserves `euclNormSq`. -/
theorem euclNormSq_mulVec_of_unitary (A : Matrix (Fin N) (Fin N) ℂ) (hA : Aᴴ * A = 1)
    (w : Fin N → ℂ) : euclNormSq (A *ᵥ w) = euclNormSq w := by
  rw [euclNormSq_eq_re_dotProduct, euclNormSq_eq_re_dotProduct, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]

theorem dbl_one_σ₁_unitary : (dbl (1 : Matrix (Fin 1) (Fin 1) ℂ) σ₁)ᴴ * dbl 1 σ₁ = 1 := by
  rw [dbl_conjTranspose, Matrix.conjTranspose_one, σ₁_conjTranspose, dbl_mul, Matrix.one_mul,
    σ₁_mul_σ₁, dbl_one_one]

theorem dbl_one_σ₂_unitary : (dbl (1 : Matrix (Fin 1) (Fin 1) ℂ) σ₂)ᴴ * dbl 1 σ₂ = 1 := by
  rw [dbl_conjTranspose, Matrix.conjTranspose_one, σ₂_conjTranspose, dbl_mul, Matrix.one_mul,
    σ₂_mul_σ₂, dbl_one_one]

/-- **Non-vacuity of `covariant_garding`**: on the one-dimensional torus `ℤ/nℤ` with the doubled
module `ℂ^{1·2}`, the coefficient `ĉ = 1 ⊗ σ₁`, `Γ_⊥ = 1 ⊗ σ₂`, the non-trivial (non-identity)
links `U = (1 + i h) I` and a single patch, every hypothesis is discharged and the estimate
holds. -/
theorem covariant_garding_nonvacuous (n : ℕ) [NeZero n] (h : ℝ) (hh : 0 < h)
    (u : TorusSection 1 n (1 * 2)) :
    h1NormSq h u ≤ covariantGardingConstant 1 1 1 1 0 0 1 1 1 *
      (gridNormSq h (covVarWilson h 1 (fun _ _ => dbl 1 σ₁)
        (fun _ _ => ((1 : ℂ) + (h : ℂ) * Complex.I) • 1) (dbl 1 σ₂) u) + gridNormSq h u) := by
  have hcl := doubled_cliffordData (d := 1) (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ)) 1
    (fun j k => by
      rw [Subsingleton.elim j k, Matrix.one_apply_eq, Matrix.one_mul]
      push_cast
      rw [mul_one, two_smul])
  refine covariant_garding (d := 1) h 1 1 1 hh one_pos one_ne_zero zero_le_one
    (fun _ _ => dbl 1 σ₁) (fun _ _ => ((1 : ℂ) + (h : ℂ) * Complex.I) • 1) (dbl 1 σ₂)
    (by rw [dbl_conjTranspose, Matrix.conjTranspose_one, σ₂_conjTranspose])
    (m := 1) (fun _ _ => 1) (fun _ => by simp) (fun _ => 0) (fun _ => ?_)
    (ω := 0) (K := 0) (L := 0) (B := 1) (G := 1) (CU := 1) le_rfl le_rfl le_rfl zero_le_one
    zero_le_one zero_le_one (fun _ _ _ => by simp) (fun _ _ w => ?_) (fun w => ?_)
    (fun _ _ _ _ w => by simp [euclNormSq]) (fun _ _ w => by simp [euclNormSq])
    (by simp) (fun _ _ w => ?_) u
  · refine ⟨fun _ => by rw [dbl_conjTranspose, Matrix.conjTranspose_one, σ₁_conjTranspose],
      1, hcl, fun ξ => by simp [sq], fun ξ => by simp [sq]⟩
  · rw [euclNormSq_mulVec_of_unitary _ dbl_one_σ₁_unitary]; simp
  · rw [euclNormSq_mulVec_of_unitary _ dbl_one_σ₂_unitary]; simp
  · have : ((1 : ℂ) + (h : ℂ) * Complex.I) • (1 : Matrix (Fin (1 * 2)) (Fin (1 * 2)) ℂ) - 1 =
        ((h : ℂ) * Complex.I) • 1 := by
      rw [add_smul, one_smul, add_sub_cancel_left]
    rw [this, Matrix.smul_mulVec, Matrix.one_mulVec, euclNormSq_smul, norm_mul, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
    ring_nf
    exact le_rfl

end doubled

end RenewalGeometry.CovariantWilsonGarding
