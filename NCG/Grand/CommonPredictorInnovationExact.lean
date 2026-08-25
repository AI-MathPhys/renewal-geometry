/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The common-predictor innovation comparison

Exact formalization for `thm:common-predictor-innovation`.

* `StrictlyCausal` / `resolvent`: a strictly causal block operator `P` on a finite
  time-ordered carrier is nilpotent (`pow_eq_zero_of_strictlyCausal`), so
  `L = (I - P)⁻¹` exists (`one_sub_mul_resolvent`);
* `common_predictor_innovation`: on the product Gaussian space carrying independent
  centered innovations `V ~ N(0, D_G)` and `B ~ N(0, D_B)`, the processes `Y = LV`
  and `X = L(V+B)` satisfy the same causal predictor recursion
  `Z - PZ = innovation`, their covariance matrices are **computed** as
  `Cov(Y) = L D_G Lᵀ` and `Cov(X) = L (D_G + D_B) Lᵀ` (via genuine measure-theoretic
  covariances of the multivariate Gaussian), and `Cov(Y) ⪯ Cov(X)` in Loewner order;
* `innovation_difference_posSemidef`: conversely, for any joint causal realization
  with uncorrelated innovation increment, the difference of the innovation
  covariances is positive semidefinite — the exact converse clause.
-/

open Finset MeasureTheory ProbabilityTheory Matrix

namespace NCG
namespace PredictorInnovation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The strictly causal operator layer -/

/-- A block operator is strictly causal for the time grading `t` when outputs load
only strictly earlier inputs. -/
def StrictlyCausal (t : ι → ℕ) (P : Matrix ι ι ℝ) : Prop :=
  ∀ i j, t i ≤ t j → P i j = 0

theorem pow_entry_eq_zero {t : ι → ℕ} {P : Matrix ι ι ℝ} (hP : StrictlyCausal t P) :
    ∀ (k : ℕ) (i j : ι), t i < t j + k → (P ^ k) i j = 0 := by
  intro k
  induction k with
  | zero =>
    intro i j hij
    have hne : i ≠ j := by
      intro h
      rw [h] at hij
      omega
    rw [pow_zero]
    exact Matrix.one_apply_ne hne
  | succ k ih =>
    intro i j hij
    rw [pow_succ', Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : t i ≤ t l
    · rw [hP i l hl, zero_mul]
    · rw [ih l j (by omega), mul_zero]

theorem pow_eq_zero_of_strictlyCausal {t : ι → ℕ} {P : Matrix ι ι ℝ}
    (hP : StrictlyCausal t P) (n : ℕ) (hn : ∀ i, t i < n) : P ^ n = 0 := by
  ext i j
  rw [Matrix.zero_apply]
  exact pow_entry_eq_zero hP n i j (by have := hn i; omega)

theorem isNilpotent_of_strictlyCausal {t : ι → ℕ} {P : Matrix ι ι ℝ}
    (hP : StrictlyCausal t P) : IsNilpotent P :=
  ⟨(Finset.univ.sup t) + 1,
    pow_eq_zero_of_strictlyCausal hP _ fun i =>
      Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))⟩

/-- The causal resolvent `L = (I - P)⁻¹`. -/
noncomputable def resolvent (P : Matrix ι ι ℝ) : Matrix ι ι ℝ := (1 - P)⁻¹

theorem one_sub_mul_resolvent {t : ι → ℕ} {P : Matrix ι ι ℝ}
    (hP : StrictlyCausal t P) : (1 - P) * resolvent P = 1 := by
  have hu : IsUnit (1 - P) := (isNilpotent_of_strictlyCausal hP).isUnit_one_sub
  exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu)

/-- The innovation recursion `(Lu)_i - (P·Lu)_i = u_i` from the left inverse. -/
theorem recursion_of_left_inverse {P L : Matrix ι ι ℝ} (hinv : (1 - P) * L = 1)
    (u : ι → ℝ) (i : ι) :
    (∑ j, L i j * u j) - ∑ j, P i j * ∑ l, L j l * u l = u i := by
  have h1 : ∑ j, P i j * ∑ l, L j l * u l = ∑ l, (P * L) i l * u l := by
    simp_rw [Finset.mul_sum, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by ring
  rw [h1, ← Finset.sum_sub_distrib]
  have h2 : ∀ l, L i l * u l - (P * L) i l * u l
      = (1 : Matrix ι ι ℝ) i l * u l := by
    intro l
    have hentry : (L - P * L) i l = (1 : Matrix ι ι ℝ) i l := by
      rw [show L - P * L = (1 - P) * L by rw [Matrix.sub_mul, Matrix.one_mul], hinv]
    rw [Matrix.sub_apply] at hentry
    rw [← hentry]
    ring
  rw [Finset.sum_congr rfl fun l _ => h2 l]
  simp [Matrix.one_apply, ite_mul]

/-! ### Covariance bilinearity for finite linear combinations -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

omit [DecidableEq ι] in
theorem memLp_comb (c : ι → ℝ) (Z : ι → Ω → ℝ) (hZ : ∀ j, MemLp (Z j) 2 μ) :
    MemLp (fun ω => ∑ j, c j * Z j ω) 2 μ := by
  have he : (fun ω => ∑ j, c j * Z j ω) = ∑ j, fun ω => c j * Z j ω := by
    funext ω
    rw [Finset.sum_apply]
  rw [he]
  exact memLp_finsetSum' _ fun j _ => (hZ j).const_mul (c j)

omit [DecidableEq ι] in
theorem covariance_vec_comb [IsFiniteMeasure μ] (x y : ι → ℝ) (Z W : ι → Ω → ℝ)
    (hZ : ∀ j, MemLp (Z j) 2 μ) (hW : ∀ j, MemLp (W j) 2 μ) :
    cov[fun ω => ∑ j, x j * Z j ω, fun ω => ∑ l, y l * W l ω; μ]
      = ∑ j, ∑ l, x j * (y l * cov[Z j, W l; μ]) := by
  rw [covariance_fun_sum_left (fun j => (hZ j).const_mul (x j))
    (memLp_comb y W hW)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [covariance_fun_sum_right (fun l => (hW l).const_mul (y l))
    ((hZ j).const_mul (x j))]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [covariance_const_mul_left, covariance_const_mul_right]

omit [DecidableEq ι] in
theorem covariance_matrix_comb [IsFiniteMeasure μ] (L M : Matrix ι ι ℝ)
    (Z W : ι → Ω → ℝ) (hZ : ∀ j, MemLp (Z j) 2 μ) (hW : ∀ j, MemLp (W j) 2 μ)
    (i k : ι) :
    cov[fun ω => ∑ j, L i j * Z j ω, fun ω => ∑ l, M k l * W l ω; μ]
      = ∑ j, ∑ l, L i j * (M k l * cov[Z j, W l; μ]) :=
  covariance_vec_comb (L i) (M k) Z W hZ hW

omit [DecidableEq ι] in
/-- The covariance matrix of any square-integrable family is positive
semidefinite. -/
theorem covMatrix_posSemidef [IsFiniteMeasure μ] (Z : ι → Ω → ℝ)
    (hZ : ∀ i, MemLp (Z i) 2 μ) :
    (Matrix.of fun i j => cov[Z i, Z j; μ]).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · rw [Matrix.IsHermitian]
    ext i j
    rw [Matrix.conjTranspose_apply]
    simp only [Matrix.of_apply, star_trivial]
    exact covariance_comm _ _
  · intro x
    have hstar : star x = x := funext fun i => star_trivial _
    have hexp : star x ⬝ᵥ ((Matrix.of fun i j => cov[Z i, Z j; μ]) *ᵥ x)
        = cov[fun ω => ∑ j, x j * Z j ω, fun ω => ∑ l, x l * Z l ω; μ] := by
      rw [hstar, covariance_vec_comb x x Z Z hZ hZ]
      simp_rw [dotProduct, Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
      simp only [Matrix.of_apply]
      ring
    rw [hexp, covariance_self (memLp_comb x Z hZ).aestronglyMeasurable.aemeasurable]
    exact variance_nonneg _ _

/-! ### The product Gaussian realization -/

variable {DG DB : Matrix ι ι ℝ}

/-- The joint law of the two independent centered innovation processes. -/
noncomputable def jointLaw (DG DB : Matrix ι ι ℝ) :
    Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :=
  (multivariateGaussian 0 DG).prod (multivariateGaussian 0 DB)

instance : IsProbabilityMeasure (jointLaw DG DB) := by
  unfold jointLaw
  infer_instance

/-- The private innovation coordinate. -/
def evalFst (i : ι) : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι → ℝ := fun ω => ω.1 i

/-- The disturbance innovation coordinate. -/
def evalSnd (i : ι) : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι → ℝ := fun ω => ω.2 i

/-- The reference process `Y = LV`. -/
noncomputable def procY (L : Matrix ι ι ℝ) (i : ι) :
    EuclideanSpace ℝ ι × EuclideanSpace ℝ ι → ℝ := fun ω => ∑ j, L i j * ω.1 j

/-- The loaded process `X = L(V + B)`. -/
noncomputable def procX (L : Matrix ι ι ℝ) (i : ι) :
    EuclideanSpace ℝ ι × EuclideanSpace ℝ ι → ℝ :=
  fun ω => ∑ j, L i j * (ω.1 j + ω.2 j)

theorem memLp_eval_mvGaussian {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (i : ι) :
    MemLp (fun x : EuclideanSpace ℝ ι => x i) 2 (multivariateGaussian 0 S) :=
  (memLp_id_gaussianReal' 2 (by norm_num)).comp_measurePreserving
    (measurePreserving_eval_multivariateGaussian hS)

theorem memLp_evalFst (hG : DG.PosSemidef) (_hB : DB.PosSemidef) (i : ι) :
    MemLp (evalFst i) 2 (jointLaw DG DB) :=
  (memLp_eval_mvGaussian hG i).comp_fst (multivariateGaussian 0 DB)

theorem memLp_evalSnd (_hG : DG.PosSemidef) (hB : DB.PosSemidef) (i : ι) :
    MemLp (evalSnd i) 2 (jointLaw DG DB) :=
  (memLp_eval_mvGaussian hB i).comp_snd (multivariateGaussian 0 DG)

theorem cov_evalFst (hG : DG.PosSemidef) (_hB : DB.PosSemidef) (i j : ι) :
    cov[evalFst i, evalFst j; jointLaw DG DB] = DG i j := by
  have hmap : (jointLaw DG DB).map Prod.fst = multivariateGaussian 0 DG := by
    rw [jointLaw, Measure.map_fst_prod, measure_univ, one_smul]
  have hcm := covariance_map (μ := jointLaw DG DB) (Z := Prod.fst)
    (X := fun x : EuclideanSpace ℝ ι => x i)
    (Y := fun x : EuclideanSpace ℝ ι => x j)
    ((by fun_prop : Measurable (fun x : EuclideanSpace ℝ ι => x i)).aestronglyMeasurable)
    ((by fun_prop : Measurable (fun x : EuclideanSpace ℝ ι => x j)).aestronglyMeasurable)
    measurable_fst.aemeasurable
  rw [hmap, covariance_eval_multivariateGaussian hG] at hcm
  exact hcm.symm

theorem cov_evalSnd (_hG : DG.PosSemidef) (hB : DB.PosSemidef) (i j : ι) :
    cov[evalSnd i, evalSnd j; jointLaw DG DB] = DB i j := by
  have hmap : (jointLaw DG DB).map Prod.snd = multivariateGaussian 0 DB := by
    rw [jointLaw, Measure.map_snd_prod, measure_univ, one_smul]
  have hcm := covariance_map (μ := jointLaw DG DB) (Z := Prod.snd)
    (X := fun x : EuclideanSpace ℝ ι => x i)
    (Y := fun x : EuclideanSpace ℝ ι => x j)
    ((by fun_prop : Measurable (fun x : EuclideanSpace ℝ ι => x i)).aestronglyMeasurable)
    ((by fun_prop : Measurable (fun x : EuclideanSpace ℝ ι => x j)).aestronglyMeasurable)
    measurable_snd.aemeasurable
  rw [hmap, covariance_eval_multivariateGaussian hB] at hcm
  exact hcm.symm

theorem cov_fst_snd (hG : DG.PosSemidef) (hB : DB.PosSemidef) (i j : ι) :
    cov[evalFst i, evalSnd j; jointLaw DG DB] = 0 :=
  covariance_fst_snd_prod (memLp_eval_mvGaussian hG i) (memLp_eval_mvGaussian hB j)

theorem cov_snd_fst (hG : DG.PosSemidef) (hB : DB.PosSemidef) (i j : ι) :
    cov[evalSnd i, evalFst j; jointLaw DG DB] = 0 := by
  rw [covariance_comm]
  exact cov_fst_snd hG hB j i

/-- The summed innovation `V + B` has covariance `D_G + D_B`. -/
theorem cov_sum_innovation (hG : DG.PosSemidef) (hB : DB.PosSemidef) (i j : ι) :
    cov[fun ω => evalFst i ω + evalSnd i ω,
      fun ω => evalFst j ω + evalSnd j ω; jointLaw DG DB] = DG i j + DB i j := by
  have h0 : ∀ k : ι, (fun ω => evalFst k ω + evalSnd k ω) = evalFst k + evalSnd k :=
    fun k => rfl
  rw [h0 i, h0 j,
    covariance_add_left (memLp_evalFst hG hB i) (memLp_evalSnd hG hB i)
      ((memLp_evalFst hG hB j).add (memLp_evalSnd hG hB j)),
    covariance_add_right (memLp_evalFst hG hB i) (memLp_evalFst hG hB j)
      (memLp_evalSnd hG hB j),
    covariance_add_right (memLp_evalSnd hG hB i) (memLp_evalFst hG hB j)
      (memLp_evalSnd hG hB j),
    cov_evalFst hG hB, cov_fst_snd hG hB, cov_snd_fst hG hB, cov_evalSnd hG hB]
  ring

/-- **Boxed covariance, reference process**: `Cov(Y) = L D_G Lᵀ`. -/
theorem cov_procY (hG : DG.PosSemidef) (hB : DB.PosSemidef)
    (L : Matrix ι ι ℝ) (i k : ι) :
    cov[procY L i, procY L k; jointLaw DG DB] = (L * DG * L.transpose) i k := by
  have h := covariance_matrix_comb (μ := jointLaw DG DB) L L evalFst evalFst
    (memLp_evalFst hG hB) (memLp_evalFst hG hB) i k
  calc cov[procY L i, procY L k; jointLaw DG DB]
      = ∑ j, ∑ l, L i j * (L k l * cov[evalFst j, evalFst l; jointLaw DG DB]) := h
    _ = ∑ j, ∑ l, L i j * (L k l * DG j l) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
        rw [cov_evalFst hG hB]
    _ = (L * DG * L.transpose) i k := by
        simp_rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
        ring

/-- **Boxed covariance, loaded process**: `Cov(X) = L (D_G + D_B) Lᵀ`. -/
theorem cov_procX (hG : DG.PosSemidef) (hB : DB.PosSemidef)
    (L : Matrix ι ι ℝ) (i k : ι) :
    cov[procX L i, procX L k; jointLaw DG DB]
      = (L * (DG + DB) * L.transpose) i k := by
  have hmem : ∀ j, MemLp (fun ω => evalFst j ω + evalSnd j ω) 2 (jointLaw DG DB) :=
    fun j => (memLp_evalFst hG hB j).add (memLp_evalSnd hG hB j)
  have h := covariance_matrix_comb (μ := jointLaw DG DB) L L
    (fun j ω => evalFst j ω + evalSnd j ω) (fun j ω => evalFst j ω + evalSnd j ω)
    hmem hmem i k
  calc cov[procX L i, procX L k; jointLaw DG DB]
      = ∑ j, ∑ l, L i j * (L k l * cov[fun ω => evalFst j ω + evalSnd j ω,
          fun ω => evalFst l ω + evalSnd l ω; jointLaw DG DB]) := h
    _ = ∑ j, ∑ l, L i j * (L k l * (DG j l + DB j l)) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
        rw [cov_sum_innovation hG hB]
    _ = (L * (DG + DB) * L.transpose) i k := by
        simp_rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul,
          Matrix.add_apply]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
        ring

/-! ### The bundle -/

/-- **Bundle for `thm:common-predictor-innovation`**: on the joint Gaussian carrier,
`Y = LV` and `X = L(V+B)` share the causal predictor recursion `Z - PZ = innovation`,
their covariances are `L D_G Lᵀ` and `L (D_G + D_B) Lᵀ`, and `Cov(Y) ⪯ Cov(X)`. -/
theorem common_predictor_innovation {t : ι → ℕ} {P : Matrix ι ι ℝ}
    (hP : StrictlyCausal t P) (hG : DG.PosSemidef) (hB : DB.PosSemidef) :
    (∀ i ω, procY (resolvent P) i ω
        - ∑ j, P i j * procY (resolvent P) j ω = ω.1 i) ∧
    (∀ i ω, procX (resolvent P) i ω
        - ∑ j, P i j * procX (resolvent P) j ω = ω.1 i + ω.2 i) ∧
    (∀ i k, cov[procY (resolvent P) i, procY (resolvent P) k; jointLaw DG DB]
        = (resolvent P * DG * (resolvent P).transpose) i k) ∧
    (∀ i k, cov[procX (resolvent P) i, procX (resolvent P) k; jointLaw DG DB]
        = (resolvent P * (DG + DB) * (resolvent P).transpose) i k) ∧
    (resolvent P * (DG + DB) * (resolvent P).transpose
      - resolvent P * DG * (resolvent P).transpose).PosSemidef := by
  have hinv := one_sub_mul_resolvent hP
  refine ⟨fun i ω => recursion_of_left_inverse hinv (fun j => ω.1 j) i,
    fun i ω => recursion_of_left_inverse hinv (fun j => ω.1 j + ω.2 j) i,
    cov_procY hG hB (resolvent P), cov_procX hG hB (resolvent P), ?_⟩
  have hdiff : resolvent P * (DG + DB) * (resolvent P).transpose
      - resolvent P * DG * (resolvent P).transpose
      = resolvent P * DB * (resolvent P).transpose := by
    noncomm_ring
  have hct : (resolvent P).conjTranspose = (resolvent P).transpose := by
    ext i j
    rw [Matrix.conjTranspose_apply, star_trivial]
    rfl
  rw [hdiff, ← hct]
  exact hB.mul_mul_conjTranspose_same (resolvent P)

omit [DecidableEq ι] in
/-- **Converse clause**: any joint causal realization with uncorrelated innovation
increment forces the difference of innovation covariances to be positive
semidefinite. -/
theorem innovation_difference_posSemidef [IsFiniteMeasure μ]
    (V B : ι → Ω → ℝ) (hV : ∀ i, MemLp (V i) 2 μ) (hB : ∀ i, MemLp (B i) 2 μ)
    (hcross : ∀ i j, cov[V i, B j; μ] = 0)
    (DY DX : Matrix ι ι ℝ)
    (hDY : ∀ i j, cov[V i, V j; μ] = DY i j)
    (hDX : ∀ i j, cov[fun ω => V i ω + B i ω, fun ω => V j ω + B j ω; μ] = DX i j) :
    (DX - DY).PosSemidef := by
  have h0 : ∀ k : ι, (fun ω => V k ω + B k ω) = V k + B k := fun k => rfl
  have hkey : ∀ i j, DX i j - DY i j = cov[B i, B j; μ] := by
    intro i j
    have hx := hDX i j
    rw [h0 i, h0 j,
      covariance_add_left (hV i) (hB i) ((hV j).add (hB j)),
      covariance_add_right (hV i) (hV j) (hB j),
      covariance_add_right (hB i) (hV j) (hB j),
      hcross i j, hDY i j] at hx
    have h2 : cov[B i, V j; μ] = 0 := by
      rw [covariance_comm]
      exact hcross j i
    rw [h2] at hx
    linarith
  have he : DX - DY = Matrix.of fun i j => cov[B i, B j; μ] := by
    ext i j
    rw [Matrix.sub_apply]
    exact hkey i j
  rw [he]
  exact covMatrix_posSemidef B hB

end PredictorInnovation
end NCG
