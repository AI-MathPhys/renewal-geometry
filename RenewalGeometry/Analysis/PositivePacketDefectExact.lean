/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.MonotoneDefectRemovalExact

/-!
# Covariance measure of a weak quadratic packet
  (`lem:positive-packet-defect`, Einstein–SM action closure)

Setting: a compact metric space `K` (the compact domain with its boundary) with a
Borel measure `V₀` (the reference volume), and the fibre `E = ℝ^r`
(`EuclideanSpace ℝ (Fin r)`): the bundle with its positive fibre metric written in
an orthonormal frame (the paper works in a finite atlas; complex packets enter
through realification).  Packets are elements `Y_h ∈ L²(K; ℝ^r)` (`Lp _ 2 V₀`), and
weak convergence `Y_h ⇀ Y` is convergence of every continuous linear functional
(`WeakTendsto`).

Matrix-valued Radon measures on `K` are encoded by the Riesz identification as
continuous linear functionals on the coefficient space `C(K, ℝ^{r×r})`
(`Fin r → Fin r → ℝ`, sup norm): the pairing `∫ P : d𝖰 = Σ_{ab} ∫ P_{ab} d𝖰_{ab}`.
Thus

* `quadCLM Z` is the measure `Z ⊗ Z dV₀`,
  `P ↦ ∫ Σ_{ab} Z_a P_{ab} Z_b dV₀` (`quadCLM_apply_eq`, `inner_matAct`);
* `PosSemidef 𝖰` means `𝖰(P) ≥ 0` for every coefficient field with
  `ξᵀ P(x) ξ ≥ 0` (a positive-semidefinite matrix measure), `IsSymm 𝖰` means
  `𝖰(Pᵀ) = 𝖰(P)`;
* `traceMeasure 𝖰 = tr 𝖰` is the scalar measure `φ ↦ 𝖰(φ I)`;
* `B : 𝖰` (contraction with a continuous coefficient field `B`) is the scalar
  measure `φ ↦ 𝖰(φ B)` (`smulField`).

Results:

* `exists_packetDefect` — after extraction, `Y_h ⊗ Y_h dV₀ ⇀* Y ⊗ Y dV₀ + 𝖰_Y`
  (`IsPacketDefect`), by the sequential Banach–Alaoglu theorem in the dual of the
  separable space `C(K, ℝ^{r×r})` and the uniform `L²` bound (Banach–Steinhaus).
* `posSemidef`, `isSymm` — `𝖰_Y` is positive semidefinite and symmetric (the
  paper's argument: expand `∫ (Y_h - Y)ᵀ P (Y_h - Y) ≥ 0` and pass the cross terms
  by weak convergence).
* `tendsto_trace`, `traceMeasure_nonneg` — `|Y_h|² dV₀ ⇀* |Y|² dV₀ + μ_Y`,
  `μ_Y = tr 𝖰_Y ≥ 0`.
* `abs_contraction_le` — `|B : 𝖰_Y| ≤ C_B μ_Y` with `C_B = sup_x ‖B(x)‖_op`, tested
  on `φ ≥ 0`.
* `traceMeasure_eq_zero_iff`, `eq_zero_iff_tendsto` —
  `eq:positive-defect-equivalence`: `μ_Y = 0 ↔ 𝖰_Y = 0 ↔ Y_h → Y` in `L²`.
* `tendsto_contraction` — `eq:defect-contraction`: for `B_h → B` uniformly,
  `B_h(Y_h, Y_h) dV₀ ⇀* B(Y, Y) dV₀ + B : 𝖰_Y`.
* `positive_packet_defect` — everything bundled for the extracted subsequence.
-/

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

namespace RenewalGeometry

namespace PositivePacketDefect

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
variable {V₀ : Measure K}

/-! ## Multiplication by a continuous operator field on `L²` -/

section MulField

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem memLp_mulField (P : C(K, E →L[ℝ] E)) (W : Lp E 2 V₀) :
    MemLp (fun x => P x (W x)) 2 V₀ := by
  refine MemLp.of_le_mul (c := ‖P‖) (Lp.memLp W) ?_ (Eventually.of_forall fun x => ?_)
  · exact Continuous.comp_aestronglyMeasurable₂ (g := fun (A : E →L[ℝ] E) (v : E) => A v)
      (continuous_fst.clm_apply continuous_snd) P.continuous.aestronglyMeasurable
      (Lp.aestronglyMeasurable W)
  · exact ((P x).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (P.norm_coe_le_norm x) (norm_nonneg _))

/-- Multiplication `W ↦ P W` of an `L²` section by a continuous operator field. -/
noncomputable def mulField (P : C(K, E →L[ℝ] E)) (W : Lp E 2 V₀) : Lp E 2 V₀ :=
  (memLp_mulField P W).toLp _

theorem coeFn_mulField (P : C(K, E →L[ℝ] E)) (W : Lp E 2 V₀) :
    mulField P W =ᵐ[V₀] fun x => P x (W x) :=
  MemLp.coeFn_toLp _

theorem mulField_sub_right (P : C(K, E →L[ℝ] E)) (W W' : Lp E 2 V₀) :
    mulField P (W - W') = mulField P W - mulField P W' := by
  apply Lp.ext
  filter_upwards [coeFn_mulField P (W - W'), coeFn_mulField P W, coeFn_mulField P W',
    Lp.coeFn_sub W W', Lp.coeFn_sub (mulField P W) (mulField P W')] with x h1 h2 h3 h4 h5
  rw [h1, h5, Pi.sub_apply, h2, h3, h4, Pi.sub_apply, map_sub]

theorem mulField_add_left (P P' : C(K, E →L[ℝ] E)) (W : Lp E 2 V₀) :
    mulField (P + P') W = mulField P W + mulField P' W := by
  apply Lp.ext
  filter_upwards [coeFn_mulField (P + P') W, coeFn_mulField P W, coeFn_mulField P' W,
    Lp.coeFn_add (mulField P W) (mulField P' W)] with x h1 h2 h3 h4
  rw [h1, h4, Pi.add_apply, h2, h3]
  simp

theorem mulField_smul_left (c : ℝ) (P : C(K, E →L[ℝ] E)) (W : Lp E 2 V₀) :
    mulField (c • P) W = c • mulField P W := by
  apply Lp.ext
  filter_upwards [coeFn_mulField (c • P) W, coeFn_mulField P W,
    Lp.coeFn_smul c (mulField P W)] with x h1 h2 h3
  rw [h1, h3, Pi.smul_apply, h2]
  simp

theorem norm_mulField_le (P : C(K, E →L[ℝ] E)) (W : Lp E 2 V₀) :
    ‖mulField P W‖ ≤ ‖P‖ * ‖W‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [coeFn_mulField P W] with x hx
  rw [hx]
  exact ((P x).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (P.norm_coe_le_norm x) (norm_nonneg _))

theorem inner_mulField_eq_integral (P : C(K, E →L[ℝ] E)) (Z W : Lp E 2 V₀) :
    ⟪Z, mulField P W⟫ = ∫ x, ⟪Z x, P x (W x)⟫ ∂V₀ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_mulField P W] with x hx
  rw [hx]

end MulField

/-! ## Matrix coefficient fields acting on `ℝ^r` -/

variable {r : ℕ}

/-- The matrix `A` acting on `ℝ^r` (linear map). -/
noncomputable def matLin (A : Fin r → Fin r → ℝ) :
    EuclideanSpace ℝ (Fin r) →ₗ[ℝ] EuclideanSpace ℝ (Fin r) where
  toFun w := WithLp.toLp 2 (fun a => ∑ b, A a b * w b)
  map_add' v w := by ext a; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    ext a; simp [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring

/-- `A ↦ (w ↦ A w)`, continuous linear in the matrix. -/
noncomputable def matAct :
    (Fin r → Fin r → ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin r)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => LinearMap.toContinuousLinearMap (matLin A)
      map_add' := fun A B => by ext w a; simp [matLin, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c A => by ext w a; simp [matLin, Finset.mul_sum, mul_assoc] }

theorem matAct_apply_apply (A : Fin r → Fin r → ℝ) (w : EuclideanSpace ℝ (Fin r)) (a : Fin r) :
    matAct A w a = ∑ b, A a b * w b := rfl

/-- `⟪z, A w⟫ = Σ_{ab} z_a A_{ab} w_b`. -/
theorem inner_matAct (A : Fin r → Fin r → ℝ) (z w : EuclideanSpace ℝ (Fin r)) :
    ⟪z, matAct A w⟫ = ∑ a, ∑ b, z a * A a b * w b := by
  simp only [PiLp.inner_apply, matAct_apply_apply, RCLike.inner_apply, conj_trivial]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- The identity matrix. -/
def idMat : Fin r → Fin r → ℝ := fun a b => if a = b then 1 else 0

theorem matAct_idMat (w : EuclideanSpace ℝ (Fin r)) : matAct (idMat (r := r)) w = w := by
  ext a
  rw [matAct_apply_apply]
  simp [idMat]

theorem inner_matAct_transpose (A : Fin r → Fin r → ℝ) (z w : EuclideanSpace ℝ (Fin r)) :
    ⟪z, matAct A w⟫ = ⟪w, matAct (fun a b => A b a) z⟫ := by
  rw [inner_matAct, inner_matAct, Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- The operator field `x ↦ P(x)` acting on `ℝ^r`. -/
noncomputable def opField (P : C(K, Fin r → Fin r → ℝ)) :
    C(K, EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin r)) :=
  ⟨fun x => matAct (P x), matAct.continuous.comp P.continuous⟩

theorem opField_apply (P : C(K, Fin r → Fin r → ℝ)) (x : K) : opField P x = matAct (P x) := rfl

theorem norm_opField_le (P : C(K, Fin r → Fin r → ℝ)) :
    ‖opField P‖ ≤ ‖(matAct : (Fin r → Fin r → ℝ) →L[ℝ] _)‖ * ‖P‖ := by
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun x => ?_
  rw [opField_apply]
  exact (matAct.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (P.norm_coe_le_norm x) (norm_nonneg _))

theorem opField_add (P P' : C(K, Fin r → Fin r → ℝ)) :
    opField (P + P') = opField P + opField P' := by
  ext x : 1; simp [opField_apply]

theorem opField_smul (c : ℝ) (P : C(K, Fin r → Fin r → ℝ)) :
    opField (c • P) = c • opField P := by
  ext x : 1; simp [opField_apply]

/-- The transposed coefficient field `x ↦ P(x)ᵀ`. -/
def transField (P : C(K, Fin r → Fin r → ℝ)) : C(K, Fin r → Fin r → ℝ) :=
  ⟨fun x a b => P x b a, by fun_prop⟩

theorem transField_apply (P : C(K, Fin r → Fin r → ℝ)) (x : K) (a b : Fin r) :
    transField P x a b = P x b a := rfl

theorem transField_transField (P : C(K, Fin r → Fin r → ℝ)) : transField (transField P) = P := by
  ext x a b; rfl

theorem inner_mulField_trans (P : C(K, Fin r → Fin r → ℝ))
    (Z W : Lp (EuclideanSpace ℝ (Fin r)) 2 V₀) :
    ⟪Z, mulField (opField P) W⟫ = ⟪mulField (opField (transField P)) Z, W⟫ := by
  rw [inner_mulField_eq_integral, real_inner_comm, inner_mulField_eq_integral]
  congr 1
  funext x
  rw [opField_apply, opField_apply, inner_matAct_transpose]
  rfl

/-! ## The quadratic measure `Z ⊗ Z dV₀` as a functional on coefficient fields -/

theorem abs_inner_mulField_opField_le (Z : Lp (EuclideanSpace ℝ (Fin r)) 2 V₀)
    (P : C(K, Fin r → Fin r → ℝ)) :
    |⟪Z, mulField (opField P) Z⟫| ≤
      ‖Z‖ * ‖Z‖ * ‖(matAct : (Fin r → Fin r → ℝ) →L[ℝ] _)‖ * ‖P‖ := by
  calc |⟪Z, mulField (opField P) Z⟫| ≤ ‖Z‖ * ‖mulField (opField P) Z‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ ‖Z‖ * (‖opField P‖ * ‖Z‖) :=
        mul_le_mul_of_nonneg_left (norm_mulField_le _ Z) (norm_nonneg _)
    _ ≤ ‖Z‖ * ((‖(matAct : (Fin r → Fin r → ℝ) →L[ℝ] _)‖ * ‖P‖) * ‖Z‖) := by
        gcongr; exact norm_opField_le P
    _ = ‖Z‖ * ‖Z‖ * ‖(matAct : (Fin r → Fin r → ℝ) →L[ℝ] _)‖ * ‖P‖ := by ring

/-- The matrix-valued measure `Z ⊗ Z dV₀`, as the functional
`P ↦ ∫ Zᵀ P Z dV₀` on `C(K, ℝ^{r×r})` (`lem:positive-packet-defect`). -/
noncomputable def quadCLM (Z : Lp (EuclideanSpace ℝ (Fin r)) 2 V₀) :
    StrongDual ℝ C(K, Fin r → Fin r → ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun P => ⟪Z, mulField (opField P) Z⟫
      map_add' := fun P P' => by rw [opField_add, mulField_add_left, inner_add_right]
      map_smul' := fun c P => by
        rw [opField_smul, mulField_smul_left, real_inner_smul_right]; rfl }
    (‖Z‖ * ‖Z‖ * ‖(matAct : (Fin r → Fin r → ℝ) →L[ℝ] _)‖) fun P => by
      rw [Real.norm_eq_abs]
      exact abs_inner_mulField_opField_le Z P

theorem quadCLM_apply (Z : Lp (EuclideanSpace ℝ (Fin r)) 2 V₀) (P : C(K, Fin r → Fin r → ℝ)) :
    quadCLM Z P = ⟪Z, mulField (opField P) Z⟫ := rfl

theorem abs_quadCLM_le (Z : Lp (EuclideanSpace ℝ (Fin r)) 2 V₀) (P : C(K, Fin r → Fin r → ℝ)) :
    |quadCLM Z P| ≤ ‖Z‖ * ‖Z‖ * ‖(matAct : (Fin r → Fin r → ℝ) →L[ℝ] _)‖ * ‖P‖ :=
  abs_inner_mulField_opField_le Z P

/-- `∫ P : (Z ⊗ Z) dV₀ = ∫ ⟪Z, P Z⟫ dV₀ = ∫ Σ_{ab} Z_a P_{ab} Z_b dV₀`. -/
theorem quadCLM_apply_eq (Z : Lp (EuclideanSpace ℝ (Fin r)) 2 V₀)
    (P : C(K, Fin r → Fin r → ℝ)) :
    quadCLM Z P = ∫ x, ⟪Z x, matAct (P x) (Z x)⟫ ∂V₀ :=
  inner_mulField_eq_integral _ Z Z

theorem norm_quadCLM_le (Z : Lp (EuclideanSpace ℝ (Fin r)) 2 V₀) :
    ‖quadCLM (K := K) Z‖ ≤ ‖Z‖ * ‖Z‖ * ‖(matAct : (Fin r → Fin r → ℝ) →L[ℝ] _)‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

theorem quadCLM_transField (Z : Lp (EuclideanSpace ℝ (Fin r)) 2 V₀)
    (P : C(K, Fin r → Fin r → ℝ)) : quadCLM Z (transField P) = quadCLM Z P := by
  rw [quadCLM_apply, inner_mulField_trans, transField_transField, real_inner_comm, quadCLM_apply]

/-- The coefficient field `x ↦ φ(x) B(x)`. -/
def smulField (φ : C(K, ℝ)) (B : C(K, Fin r → Fin r → ℝ)) : C(K, Fin r → Fin r → ℝ) :=
  ⟨fun x => φ x • B x, φ.continuous.smul B.continuous⟩

theorem smulField_apply (φ : C(K, ℝ)) (B : C(K, Fin r → Fin r → ℝ)) (x : K) :
    smulField φ B x = φ x • B x := rfl

/-- The scalar field `x ↦ φ(x) I`. -/
def idField (φ : C(K, ℝ)) : C(K, Fin r → Fin r → ℝ) :=
  smulField φ (ContinuousMap.const K idMat)

theorem idField_apply (φ : C(K, ℝ)) (x : K) :
    (idField φ : C(K, Fin r → Fin r → ℝ)) x = φ x • idMat := rfl

theorem norm_smulField_le (φ : C(K, ℝ)) (B : C(K, Fin r → Fin r → ℝ)) :
    ‖smulField φ B‖ ≤ ‖φ‖ * ‖B‖ := by
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun x => ?_
  rw [smulField_apply, norm_smul]
  exact mul_le_mul (φ.norm_coe_le_norm x) (B.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _)

/-- `B ↦ φ B` as a continuous linear map of coefficient fields. -/
noncomputable def smulFieldCLM (φ : C(K, ℝ)) :
    C(K, Fin r → Fin r → ℝ) →L[ℝ] C(K, Fin r → Fin r → ℝ) :=
  LinearMap.mkContinuous
    { toFun := smulField φ
      map_add' := fun B B' => by ext x a b; simp [smulField_apply, mul_add]
      map_smul' := fun c B => by ext x a b; simp [smulField_apply]; ring }
    ‖φ‖ (norm_smulField_le φ)

/-- `φ ↦ φ I` as a continuous linear map. -/
noncomputable def idCLM : C(K, ℝ) →L[ℝ] C(K, Fin r → Fin r → ℝ) :=
  LinearMap.mkContinuous
    { toFun := idField
      map_add' := fun φ φ' => by ext x a b; simp [idField_apply, add_mul]
      map_smul' := fun c φ => by ext x a b; simp [idField_apply, mul_assoc] }
    ‖(ContinuousMap.const K (idMat (r := r)))‖ fun φ => by
      refine (norm_smulField_le _ _).trans ?_
      rw [mul_comm]

/-- The trace measure `tr 𝖰 : φ ↦ 𝖰(φ I)`. -/
noncomputable def traceMeasure (Q : StrongDual ℝ C(K, Fin r → Fin r → ℝ)) :
    StrongDual ℝ C(K, ℝ) :=
  Q.comp idCLM

theorem traceMeasure_apply (Q : StrongDual ℝ C(K, Fin r → Fin r → ℝ)) (φ : C(K, ℝ)) :
    traceMeasure Q φ = Q (idField φ) := by
  simp only [traceMeasure, ContinuousLinearMap.comp_apply]
  rfl

theorem opField_idField_apply (φ : C(K, ℝ)) (x : K) (y : EuclideanSpace ℝ (Fin r)) :
    opField (idField φ) x y = φ x • y := by
  rw [opField_apply, idField_apply, map_smul, ContinuousLinearMap.smul_apply, matAct_idMat]

theorem quadCLM_idField (Z : Lp (EuclideanSpace ℝ (Fin r)) 2 V₀) (φ : C(K, ℝ)) :
    quadCLM Z (idField φ) = ∫ x, φ x * ‖Z x‖ ^ 2 ∂V₀ := by
  rw [quadCLM_apply, inner_mulField_eq_integral]
  congr 1
  funext x
  rw [opField_idField_apply, real_inner_smul_right, real_inner_self_eq_norm_sq]

theorem quadCLM_idField_one (Z : Lp (EuclideanSpace ℝ (Fin r)) 2 V₀) :
    quadCLM Z (idField (1 : C(K, ℝ))) = ‖Z‖ ^ 2 := by
  have : mulField (opField (idField (1 : C(K, ℝ)))) Z = Z := by
    apply Lp.ext
    filter_upwards [coeFn_mulField (opField (idField (1 : C(K, ℝ)))) Z] with x hx
    rw [hx, opField_idField_apply]
    simp
  rw [quadCLM_apply, this, real_inner_self_eq_norm_sq]

/-! ## Positive semidefinite matrix-valued measures and the defect -/

/-- Positive semidefiniteness of a matrix-valued measure: `∫ P : d𝖰 ≥ 0` whenever
`ξᵀ P(x) ξ ≥ 0` for all `x, ξ`. -/
def PosSemidef (Q : StrongDual ℝ C(K, Fin r → Fin r → ℝ)) : Prop :=
  ∀ P : C(K, Fin r → Fin r → ℝ), (∀ x y, 0 ≤ ⟪y, matAct (P x) y⟫) → 0 ≤ Q P

/-- Symmetry of a matrix-valued measure: `𝖰(Pᵀ) = 𝖰(P)`. -/
def IsSymm (Q : StrongDual ℝ C(K, Fin r → Fin r → ℝ)) : Prop :=
  ∀ P : C(K, Fin r → Fin r → ℝ), Q (transField P) = Q P

/-- The defect relation `Y_h ⊗ Y_h dV₀ ⇀* Y ⊗ Y dV₀ + 𝖰` (`eq:positive-packet-defect`),
tested against every continuous coefficient field. -/
def IsPacketDefect (Y : ℕ → Lp (EuclideanSpace ℝ (Fin r)) 2 V₀)
    (Y₀ : Lp (EuclideanSpace ℝ (Fin r)) 2 V₀) (Q : StrongDual ℝ C(K, Fin r → Fin r → ℝ)) :
    Prop :=
  ∀ P, Tendsto (fun h => quadCLM (Y h) P) atTop (𝓝 (quadCLM Y₀ P + Q P))

/-- Weak convergence in `L²(K; ℝ^r)`. -/
def WeakTendsto (Y : ℕ → Lp (EuclideanSpace ℝ (Fin r)) 2 V₀)
    (Y₀ : Lp (EuclideanSpace ℝ (Fin r)) 2 V₀) : Prop :=
  ∀ φ : StrongDual ℝ (Lp (EuclideanSpace ℝ (Fin r)) 2 V₀),
    Tendsto (fun h => φ (Y h)) atTop (𝓝 (φ Y₀))

variable {Y : ℕ → Lp (EuclideanSpace ℝ (Fin r)) 2 V₀} {Y₀ : Lp (EuclideanSpace ℝ (Fin r)) 2 V₀}
variable {Q : StrongDual ℝ C(K, Fin r → Fin r → ℝ)}

theorem WeakTendsto.comp (hY : WeakTendsto Y Y₀) {σ : ℕ → ℕ} (hσ : StrictMono σ) :
    WeakTendsto (Y ∘ σ) Y₀ :=
  fun φ => (hY φ).comp hσ.tendsto_atTop

theorem WeakTendsto.inner_left (hY : WeakTendsto Y Y₀) (W : Lp (EuclideanSpace ℝ (Fin r)) 2 V₀) :
    Tendsto (fun h => ⟪W, Y h⟫) atTop (𝓝 ⟪W, Y₀⟫) := by
  simpa [innerSL_apply_apply] using hY (innerSL ℝ W)

theorem WeakTendsto.inner_right (hY : WeakTendsto Y Y₀)
    (W : Lp (EuclideanSpace ℝ (Fin r)) 2 V₀) :
    Tendsto (fun h => ⟪Y h, W⟫) atTop (𝓝 ⟪Y₀, W⟫) := by
  simpa [real_inner_comm] using hY.inner_left W

/-- `lem:positive-packet-defect`, extraction: a weakly convergent packet has a subsequence
and a matrix-valued measure `𝖰` with `Y_h ⊗ Y_h dV₀ ⇀* Y ⊗ Y dV₀ + 𝖰`. -/
theorem exists_packetDefect (hY : WeakTendsto Y Y₀) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ Q : StrongDual ℝ C(K, Fin r → Fin r → ℝ),
      IsPacketDefect (Y ∘ σ) Y₀ Q := by
  obtain ⟨C, hC⟩ := MonotoneDefectRemoval.norm_bounded_of_weak_tendsto Y Y₀ hY
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  set M := ‖(matAct : (Fin r → Fin r → ℝ) →L[ℝ] _)‖
  let ℓ : ℕ → WeakDual ℝ C(K, Fin r → Fin r → ℝ) :=
    fun h => StrongDual.toWeakDual (quadCLM (Y h))
  set ρ : ℝ := 1 / (C * C * M + 1)
  have hM0 : 0 ≤ M := norm_nonneg (matAct : (Fin r → Fin r → ℝ) →L[ℝ] _)
  have hden : 0 < C * C * M + 1 := by positivity
  have hρ : 0 < ρ := by positivity
  have hmem : ∀ h, ℓ h ∈ WeakDual.polar ℝ (Metric.ball (0 : C(K, Fin r → Fin r → ℝ)) ρ) := by
    intro h
    rw [WeakDual.polar_def]
    intro P hP
    rw [mem_ball_zero_iff] at hP
    change ‖quadCLM (Y h) P‖ ≤ 1
    rw [Real.norm_eq_abs]
    refine (abs_quadCLM_le (Y h) P).trans ?_
    have h1 : ‖Y h‖ * ‖Y h‖ * M ≤ C * C * M := by
      gcongr
      · exact hC h
      · exact hC h
    calc ‖Y h‖ * ‖Y h‖ * M * ‖P‖ ≤ C * C * M * ρ := by
          gcongr
      _ ≤ (C * C * M + 1) * ρ := by gcongr; linarith
      _ = 1 := by simp only [ρ]; field_simp
  obtain ⟨L, -, σ, hσ, hlim⟩ :=
    WeakDual.isSeqCompact_polar ℝ C(K, Fin r → Fin r → ℝ) (Metric.ball_mem_nhds (0 : C(K, Fin r → Fin r → ℝ)) hρ) hmem
  refine ⟨σ, hσ, WeakDual.toStrongDual L - quadCLM Y₀, fun P => ?_⟩
  have := ((WeakDual.eval_continuous P).tendsto L).comp hlim
  have e : quadCLM Y₀ P + (WeakDual.toStrongDual L - quadCLM Y₀) P = L P := by
    rw [ContinuousLinearMap.sub_apply, add_sub_cancel]
    rfl
  rw [e]
  exact this

/-- `lem:positive-packet-defect`: the defect `𝖰_Y` is positive semidefinite. -/
theorem posSemidef (hY : WeakTendsto Y Y₀) (hQ : IsPacketDefect Y Y₀ Q) : PosSemidef Q := by
  intro P hP
  set A := opField P
  set At := opField (transField P)
  have hnn : ∀ h, 0 ≤ ⟪Y h - Y₀, mulField A (Y h - Y₀)⟫ := by
    intro h
    rw [inner_mulField_eq_integral]
    exact integral_nonneg fun x => hP x _
  have hexp : ∀ h, ⟪Y h - Y₀, mulField A (Y h - Y₀)⟫ =
      quadCLM (Y h) P - ⟪Y h, mulField A Y₀⟫ - ⟪mulField At Y₀, Y h⟫ + quadCLM Y₀ P := by
    intro h
    rw [mulField_sub_right, inner_sub_left, inner_sub_right, inner_sub_right,
      inner_mulField_trans P Y₀ (Y h), quadCLM_apply, quadCLM_apply]
    ring
  have h1 := hY.inner_right (mulField A Y₀)
  have h2 := hY.inner_left (mulField At Y₀)
  have hlim : Tendsto (fun h => ⟪Y h - Y₀, mulField A (Y h - Y₀)⟫) atTop
      (𝓝 ((quadCLM Y₀ P + Q P) - ⟪Y₀, mulField A Y₀⟫ - ⟪mulField At Y₀, Y₀⟫ +
        quadCLM Y₀ P)) := by
    simp_rw [hexp]
    exact (((hQ P).sub h1).sub h2).add_const _
  have hge := ge_of_tendsto' hlim hnn
  have e1 : ⟪mulField At Y₀, Y₀⟫ = quadCLM Y₀ P := by
    rw [← inner_mulField_trans, quadCLM_apply]
  have e2 : ⟪Y₀, mulField A Y₀⟫ = quadCLM Y₀ P := rfl
  rw [e1, e2] at hge
  linarith

/-- `lem:positive-packet-defect`: the defect is symmetric. -/
theorem isSymm (hQ : IsPacketDefect Y Y₀ Q) : IsSymm Q := by
  intro P
  have h1 := hQ (transField P)
  simp_rw [quadCLM_transField] at h1
  have := tendsto_nhds_unique h1 (hQ P)
  linarith

/-- `lem:positive-packet-defect`: `|Y_h|² dV₀ ⇀* |Y|² dV₀ + μ_Y` with `μ_Y = tr 𝖰_Y`. -/
theorem tendsto_trace (hQ : IsPacketDefect Y Y₀ Q) (φ : C(K, ℝ)) :
    Tendsto (fun h => ∫ x, φ x * ‖Y h x‖ ^ 2 ∂V₀) atTop
      (𝓝 (∫ x, φ x * ‖Y₀ x‖ ^ 2 ∂V₀ + traceMeasure Q φ)) := by
  have := hQ (idField φ)
  simp_rw [quadCLM_idField] at this
  rw [traceMeasure_apply]
  exact this

/-- `lem:positive-packet-defect`: `μ_Y = tr 𝖰_Y ≥ 0`. -/
theorem traceMeasure_nonneg (hpos : PosSemidef Q) {φ : C(K, ℝ)} (hφ : ∀ x, 0 ≤ φ x) :
    0 ≤ traceMeasure Q φ := by
  rw [traceMeasure_apply]
  refine hpos _ fun x y => ?_
  rw [← opField_apply, opField_idField_apply, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  exact mul_nonneg (hφ x) (sq_nonneg _)

/-- `eq:defect-contraction`, domination: `|B : 𝖰| ≤ C_B μ` with
`C_B = sup_x ‖B(x)‖_op = ‖opField B‖`, tested on nonnegative continuous functions. -/
theorem abs_contraction_le (hpos : PosSemidef Q) (B : C(K, Fin r → Fin r → ℝ)) {φ : C(K, ℝ)}
    (hφ : ∀ x, 0 ≤ φ x) : |Q (smulField φ B)| ≤ ‖opField B‖ * traceMeasure Q φ := by
  set c := ‖opField B‖
  have hB : ∀ x y, |⟪y, matAct (B x) y⟫| ≤ c * ‖y‖ ^ 2 := by
    intro x y
    calc |⟪y, matAct (B x) y⟫| ≤ ‖y‖ * ‖matAct (B x) y‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖y‖ * (c * ‖y‖) := by
          gcongr
          exact ((matAct (B x)).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right ((opField B).norm_coe_le_norm x) (norm_nonneg _))
      _ = c * ‖y‖ ^ 2 := by ring
  have key : ∀ s : ℝ, s = 1 ∨ s = -1 →
      0 ≤ c * traceMeasure Q φ + s * Q (smulField φ B) := by
    intro s hs
    have hP := hpos (c • idField φ + s • smulField φ B) fun x y => by
      have e : matAct ((c • idField φ + s • smulField φ B : C(K, Fin r → Fin r → ℝ)) x) y =
          (c * φ x) • y + (s * φ x) • matAct (B x) y := by
        rw [ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.smul_apply, map_add,
          map_smul, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.smul_apply, ← opField_apply, opField_idField_apply,
          smulField_apply, map_smul, ContinuousLinearMap.smul_apply, smul_smul, smul_smul]
      rw [e, inner_add_right, real_inner_smul_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq]
      have h1 := abs_le.1 (hB x y)
      have h2 := hφ x
      have h3 : 0 ≤ ‖y‖ ^ 2 := sq_nonneg _
      rcases hs with rfl | rfl
      · nlinarith [mul_nonneg h2 (by linarith [h1.1] : 0 ≤ c * ‖y‖ ^ 2 + ⟪y, matAct (B x) y⟫)]
      · nlinarith [mul_nonneg h2 (by linarith [h1.2] : 0 ≤ c * ‖y‖ ^ 2 - ⟪y, matAct (B x) y⟫)]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← traceMeasure_apply] at hP
    exact hP
  have k1 := key 1 (Or.inl rfl)
  have k2 := key (-1) (Or.inr rfl)
  rw [abs_le]
  constructor <;> linarith

/-- Every coefficient field is dominated by the total trace mass:
`|𝖰(P)| ≤ ‖P‖_op,∞ μ(1)`. -/
theorem abs_apply_le (hpos : PosSemidef Q) (P : C(K, Fin r → Fin r → ℝ)) :
    |Q P| ≤ ‖opField P‖ * traceMeasure Q 1 := by
  have h := abs_contraction_le hpos P (φ := 1) fun _ => zero_le_one
  have : smulField (1 : C(K, ℝ)) P = P := by ext x a b; simp [smulField_apply]
  rwa [this] at h

/-- `eq:positive-defect-equivalence`, first equivalence: `μ_Y = 0 ↔ 𝖰_Y = 0`. -/
theorem traceMeasure_eq_zero_iff (hpos : PosSemidef Q) : traceMeasure Q = 0 ↔ Q = 0 := by
  constructor
  · intro h
    ext P
    have := abs_apply_le hpos P
    rw [h, ContinuousLinearMap.zero_apply, mul_zero] at this
    simpa using abs_nonpos_iff.1 this
  · intro h
    rw [h]
    rfl

/-- `eq:positive-defect-equivalence`, second equivalence: `𝖰_Y = 0 ↔ Y_h → Y` in `L²`. -/
theorem eq_zero_iff_tendsto (hY : WeakTendsto Y Y₀) (hQ : IsPacketDefect Y Y₀ Q) :
    Q = 0 ↔ Tendsto (fun h => ‖Y h - Y₀‖) atTop (𝓝 0) := by
  have hpos := posSemidef hY hQ
  have hnorm := hQ (idField 1)
  simp_rw [quadCLM_idField_one] at hnorm
  constructor
  · intro h0
    rw [h0, ContinuousLinearMap.zero_apply, add_zero] at hnorm
    have hsq : Tendsto (fun h => ‖Y h - Y₀‖ ^ 2) atTop (𝓝 0) := by
      have hexp : ∀ h, ‖Y h - Y₀‖ ^ 2 = ‖Y h‖ ^ 2 - 2 * ⟪Y h, Y₀⟫ + ‖Y₀‖ ^ 2 :=
        fun h => norm_sub_sq_real _ _
      simp_rw [hexp]
      have h1 := hY.inner_right Y₀
      rw [real_inner_self_eq_norm_sq] at h1
      have := ((hnorm.sub (h1.const_mul 2)).add_const (‖Y₀‖ ^ 2))
      convert this using 2
      ring
    exact MonotoneDefectRemoval.tendsto_zero_of_pow_tendsto_zero _ (fun _ => norm_nonneg _)
      two_ne_zero hsq
  · intro hs
    have hconv : Tendsto Y atTop (𝓝 Y₀) := tendsto_iff_norm_sub_tendsto_zero.2 hs
    have h2 : Tendsto (fun h => ‖Y h‖ ^ 2) atTop (𝓝 (‖Y₀‖ ^ 2)) :=
      (hconv.norm).pow 2
    have h3 := tendsto_nhds_unique hnorm h2
    have htr : traceMeasure Q 1 = 0 := by
      rw [traceMeasure_apply]; linarith
    ext P
    have := abs_apply_le hpos P
    rw [htr, mul_zero] at this
    simpa using abs_nonpos_iff.1 this

/-- Convergence of the quadratic functionals along strongly convergent coefficient fields. -/
theorem tendsto_quadCLM_of_tendsto (hY : WeakTendsto Y Y₀) (hQ : IsPacketDefect Y Y₀ Q)
    {P : ℕ → C(K, Fin r → Fin r → ℝ)} {P₀ : C(K, Fin r → Fin r → ℝ)}
    (hP : Tendsto P atTop (𝓝 P₀)) :
    Tendsto (fun h => quadCLM (Y h) (P h)) atTop (𝓝 (quadCLM Y₀ P₀ + Q P₀)) := by
  obtain ⟨C, hC⟩ := MonotoneDefectRemoval.norm_bounded_of_weak_tendsto Y Y₀ hY
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  set M := ‖(matAct : (Fin r → Fin r → ℝ) →L[ℝ] _)‖
  have hsmall : Tendsto (fun h => quadCLM (Y h) (P h - P₀)) atTop (𝓝 0) := by
    have hd : Tendsto (fun h => ‖P h - P₀‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 hP
    refine squeeze_zero_norm (fun h => ?_) (by simpa using hd.const_mul (C * C * M))
    rw [Real.norm_eq_abs]
    refine (abs_quadCLM_le (Y h) (P h - P₀)).trans ?_
    gcongr
    · exact hC h
    · exact hC h
  have hsum := hsmall.add (hQ P₀)
  rw [zero_add] at hsum
  refine hsum.congr fun h => ?_
  rw [← map_add, sub_add_cancel]

/-- `eq:defect-contraction`: for coefficient fields `B_h → B` uniformly,
`B_h(Y_h, Y_h) dV₀ ⇀* B(Y, Y) dV₀ + B : 𝖰_Y`, tested against every `φ ∈ C(K)`. -/
theorem tendsto_contraction (hY : WeakTendsto Y Y₀) (hQ : IsPacketDefect Y Y₀ Q)
    {B : ℕ → C(K, Fin r → Fin r → ℝ)} {B₀ : C(K, Fin r → Fin r → ℝ)}
    (hB : Tendsto B atTop (𝓝 B₀)) (φ : C(K, ℝ)) :
    Tendsto (fun h => quadCLM (Y h) (smulField φ (B h))) atTop
      (𝓝 (quadCLM Y₀ (smulField φ B₀) + Q (smulField φ B₀))) :=
  tendsto_quadCLM_of_tendsto hY hQ (((smulFieldCLM φ).continuous.tendsto B₀).comp hB)

/-- `lem:positive-packet-defect`, bundled: for `Y_h ⇀ Y` weakly in `L²(K; ℝ^r)` there are a
subsequence and a matrix-valued measure `𝖰_Y` with `Y_h ⊗ Y_h dV₀ ⇀* Y ⊗ Y dV₀ + 𝖰_Y`,
`𝖰_Y` symmetric positive semidefinite, `|Y_h|² dV₀ ⇀* |Y|² dV₀ + μ_Y`,
`μ_Y = tr 𝖰_Y ≥ 0`, `μ_Y = 0 ↔ 𝖰_Y = 0 ↔ Y_h → Y` in `L²` along the subsequence, and for
`B_h → B` uniformly `B_h(Y_h, Y_h) dV₀ ⇀* B(Y, Y) dV₀ + B : 𝖰_Y` with
`|B : 𝖰_Y| ≤ C_B μ_Y`. -/
theorem positive_packet_defect (hY : WeakTendsto Y Y₀) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ Q : StrongDual ℝ C(K, Fin r → Fin r → ℝ),
      IsPacketDefect (Y ∘ σ) Y₀ Q ∧ PosSemidef Q ∧ IsSymm Q ∧
      (∀ φ : C(K, ℝ), Tendsto (fun h => ∫ x, φ x * ‖Y (σ h) x‖ ^ 2 ∂V₀) atTop
        (𝓝 (∫ x, φ x * ‖Y₀ x‖ ^ 2 ∂V₀ + traceMeasure Q φ))) ∧
      (∀ φ : C(K, ℝ), (∀ x, 0 ≤ φ x) → 0 ≤ traceMeasure Q φ) ∧
      (traceMeasure Q = 0 ↔ Q = 0) ∧
      (Q = 0 ↔ Tendsto (fun h => ‖Y (σ h) - Y₀‖) atTop (𝓝 0)) ∧
      (∀ (B : ℕ → C(K, Fin r → Fin r → ℝ)) (B₀ : C(K, Fin r → Fin r → ℝ)),
        Tendsto B atTop (𝓝 B₀) → ∀ φ : C(K, ℝ),
          Tendsto (fun h => quadCLM (Y (σ h)) (smulField φ (B h))) atTop
            (𝓝 (quadCLM Y₀ (smulField φ B₀) + Q (smulField φ B₀)))) ∧
      (∀ (B : C(K, Fin r → Fin r → ℝ)) (φ : C(K, ℝ)), (∀ x, 0 ≤ φ x) →
        |Q (smulField φ B)| ≤ ‖opField B‖ * traceMeasure Q φ) := by
  obtain ⟨σ, hσ, Q, hQ⟩ := exists_packetDefect hY
  have hYσ := hY.comp hσ
  have hpos := posSemidef hYσ hQ
  exact ⟨σ, hσ, Q, hQ, hpos, isSymm hQ, tendsto_trace hQ,
    fun φ hφ => traceMeasure_nonneg hpos hφ, traceMeasure_eq_zero_iff hpos,
    eq_zero_iff_tendsto hYσ hQ, fun B B₀ hB φ => tendsto_contraction hYσ hQ hB φ,
    fun B φ hφ => abs_contraction_le hpos B hφ⟩

end PositivePacketDefect

end RenewalGeometry
