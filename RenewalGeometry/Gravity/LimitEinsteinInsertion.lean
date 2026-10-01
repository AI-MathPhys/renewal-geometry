/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.DistributionalFirstBianchi
import RenewalGeometry.Gravity.PalatiniEinsteinVariationAlgebra

/-!
# Einstein insertion for limiting coframes and connections, and Levi-Civita uniqueness
  (Holst-inert and Einstein-identification steps of `thm:supp-renewal-palatini`,
  `eq:supp-einstein-insertion`; emergent-spacetime manuscript, supplement)

This file connects the analytic Bianchi passage (`Gravity/DistributionalFirstBianchi.lean`)
with the pointwise Palatini–Holst–volume algebra (`Gravity/PalatiniEinsteinVariationAlgebra.lean`)
for `so(1,3)`-type connections acting on `ℝ⁴` by matrix multiplication.

* `matAct`: the matrix action `M ↦ (v ↦ M v)` as a continuous bilinear map (with the
  `L^∞`-operator norm on matrices), multiplicative;
* `satisfiesFirstBianchi_of_bianchiForm_eq_zero`: the vanishing three-form `(R ∧ e)` of the
  matrix-valued (mixed-index) curvature is the algebraic first Bianchi identity of
  `PalatiniEinsteinAlgebra` for the raised curvature `R^{KL} = R^K{}_M η^{ML}`;
* `classifiedMetricVariation_eq_einstein`: at a point with `det e > 0`, internal antisymmetry
  and the first Bianchi identity, the classified coframe variation along an inverse-metric test
  is `β √(-g) k^{γb}(G + Λ g)_{bγ}`;
* `integral_classifiedMetricVariation_of_approx`: **Einstein insertion for the limit.**  If the
  limiting coframe/connection pair is the weak–strong limit of `C¹` pairs with `L²`-vanishing
  torsion (the hypotheses of `isDistributionalBianchi_of_approx`), the limiting coframe is
  oriented and the internal curvature antisymmetric almost everywhere, then on every compact
  `K ⊆ Ω` the integrated classified metric first variation equals
  `β ∫_K √(-g) k^{γb} (G_{bγ} + Λ g_{bγ})`, `Λ = -λ/(2β)`: the Holst variation drops out by the
  first Bianchi identity and the Palatini and volume variations give the Einstein and
  cosmological insertions of `eq:supp-einstein-insertion`;
* `leviCivita_difference_eq_zero`: **algebraic uniqueness of the torsion-free metric-compatible
  connection**: two connections compatible with a symmetric nondegenerate `η` and with the same
  torsion for an invertible coframe coincide (pointwise; hence almost everywhere for limits).

Disclosed rendering: `G` is the Einstein tensor of the coordinate curvature
`𝓡^{αβ}_{ρσ} = E^α_K E^β_L R^{KL}_{ρσ}` of the torsion-free metric-compatible (by
`leviCivita_difference_eq_zero`, the unique such) connection; its agreement with the classical
Riemann tensor of `g = eᵀ η e` for `C²` coframes is the classical tetrad computation, not
formalised here.
-/

open MeasureTheory Filter Topology TopologicalSpace
open scoped NNReal Distributions

noncomputable section

namespace RenewalGeometry.LimitEinsteinInsertion

open DistributionalBianchi PalatiniEinsteinAlgebra DistributionalTorsion DistributionalCurvature

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The matrix action `M ↦ (v ↦ M v)` of `4 × 4` matrices on `ℝ⁴`. -/
def matAct : Matrix (Fin 4) (Fin 4) ℝ →L[ℝ] (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : ((Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)) ≃ₗ[ℝ] _).toLinearMap ∘ₗ
      Matrix.mulVecBilin ℝ ℝ)

theorem matAct_apply (M : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℝ) :
    matAct M v = M.mulVec v := by
  simp [matAct]

theorem matAct_zero_apply (v : Fin 4 → ℝ) : matAct 0 v = 0 := by
  rw [matAct_apply]; simp

theorem matAct_mul (x y : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℝ) :
    matAct (x * y) v = matAct x (matAct y v) := by
  simp [matAct_apply, Matrix.mulVec_mulVec]

/-! ### From the mixed-index three-form to the algebraic first Bianchi identity -/

/-- The internal curvature with both indices raised, `R^{KL}_{ρσ} = R^K{}_{M ρσ} η^{ML}`,
from a matrix-valued (mixed-index) curvature two-form `Rm ρ σ = R^·{}_{·ρσ}`. -/
def raisedCurvature (Rm : Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℝ) :
    Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun K L ρ σ => ∑ M, Rm ρ σ K M * minkowski M L

/-- The coframe matrix `e^I_μ` of a coframe given by its one-form components `e_μ ∈ ℝ⁴`. -/
def coframeMatrix (e : Fin 4 → (Fin 4 → ℝ)) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun I μ => e μ I

theorem minkowski_mul_self : minkowski * minkowski = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [minkowski, Matrix.mul_apply, Fin.sum_univ_four,
    Matrix.one_apply]

theorem bianchiTerm_raised (Rm : Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℝ)
    (e : Fin 4 → (Fin 4 → ℝ)) (K ν ρ σ : Fin 4) :
    bianchiTerm minkowski (coframeMatrix e) (raisedCurvature Rm) K ν ρ σ =
      (matAct (Rm ρ σ) (e ν)) K := by
  have hmm : ∀ M J, ∑ L, minkowski M L * minkowski L J = if M = J then 1 else 0 := by
    intro M J
    have := congrFun (congrFun minkowski_mul_self M) J
    rw [Matrix.mul_apply] at this
    rw [this, Matrix.one_apply]
  rw [matAct_apply]
  simp only [bianchiTerm, raisedCurvature, coordCurvature, coframeMatrix, Matrix.of_apply,
    Matrix.mulVec, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun M _ => ?_
  have : ∀ L, Rm ρ σ K M * minkowski M L * ∑ J, minkowski L J * e ν J =
      ∑ J, Rm ρ σ K M * (minkowski M L * minkowski L J) * e ν J := by
    intro L; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun J _ => ?_; ring
  simp only [this]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, ← Finset.mul_sum, hmm]
  simp

/-- The vanishing Bianchi three-form of the matrix-valued curvature is the algebraic first
Bianchi identity of the raised curvature. -/
theorem satisfiesFirstBianchi_of_bianchiForm_eq_zero
    (Rm : Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℝ) (e : Fin 4 → (Fin 4 → ℝ))
    (h : ∀ a b c, matAct (Rm a b) (e c) + matAct (Rm b c) (e a) + matAct (Rm c a) (e b) = 0) :
    SatisfiesFirstBianchi minkowski (coframeMatrix e) (raisedCurvature Rm) := by
  intro K ν ρ σ
  simp only [bianchiTerm_raised]
  have := congrFun (h ρ σ ν) K
  simpa [add_assoc] using this

/-! ### The classified metric variation and its Einstein form -/

/-- The first variation of `α L_H + β L_P + λ L_vol` along the inverse-metric test lift
`δe = e H`, `H = -½ k g` (curvature held fixed). -/
def classifiedMetricVariation (α β lam : ℝ) (η e k : Matrix (Fin 4) (Fin 4) ℝ)
    (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) : ℝ :=
  α * holstVariation η e (e * metricTestGenerator η e k) R +
    β * palatiniVariation e (e * metricTestGenerator η e k) R +
    lam * (e.det * Matrix.trace (e⁻¹ * (e * metricTestGenerator η e k)))

/-- The Einstein insertion density `β √(-g) k^{γb} (G_{bγ} + Λ g_{bγ})`, `Λ = -λ/(2β)`. -/
def einsteinInsertionDensity (β lam : ℝ) (e k : Matrix (Fin 4) (Fin 4) ℝ)
    (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) : ℝ :=
  β * Real.sqrt (-(coframeMetric minkowski e).det) *
    ∑ γ, ∑ b, k γ b * (einsteinOf (coframeMetric minkowski e) (coordCurvature e R) b γ +
      (-lam / (2 * β)) * coframeMetric minkowski e b γ)

theorem classifiedMetricVariation_eq_einstein (e k : Matrix (Fin 4) (Fin 4) ℝ)
    (hdet : 0 < e.det) (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hR1 : ∀ K L ρ σ, R L K ρ σ = -R K L ρ σ) (hR2 : ∀ K L ρ σ, R K L σ ρ = -R K L ρ σ)
    (hB : SatisfiesFirstBianchi minkowski e R) (α β lam : ℝ) (hβ : β ≠ 0) :
    classifiedMetricVariation α β lam minkowski e k R = einsteinInsertionDensity β lam e k R := by
  set δ := e * metricTestGenerator minkowski e k
  have h1 := (((hasDerivAt_holstDensity minkowski e δ R).const_mul α).add
    ((hasDerivAt_palatiniDensity e δ R).const_mul β)).add
    ((hasDerivAt_volumeDensity e δ hdet.ne').const_mul lam)
  have h2 := hasDerivAt_classifiedDensity_einstein e k hdet R hR1 hR2 hB α β lam hβ
  exact h1.unique h2

/-- **Einstein insertion for the limit pair.**  Let `(e_n, ω_n)` be `C¹` coframes and
`4 × 4`-matrix connections on `Ω ⊆ ℝ⁴` with `e_n → e` strongly in `L²_loc(Ω)`, `ω_n` bounded in
`L²_loc(Ω)`, torsions tending to zero strongly in `L²_loc(Ω)`, and curvatures bounded in
`L²_loc(Ω)` and weakly convergent to `R ∈ L²_loc(Ω)` (the hypotheses of
`isDistributionalBianchi_of_approx`).  Suppose the limiting coframe is oriented and the raised
curvature `R^{KL}` antisymmetric in both pairs almost everywhere on `Ω` (metric compatibility).
Then for every compact `K ⊆ Ω`, every inverse-metric test field `k` and `β ≠ 0`,
`∫_K δ(α L_H + β L_P + λ L_vol)[k] = ∫_K β √(-g) k^{γb}(G + Λ g)_{bγ}`. -/
theorem integral_classifiedMetricVariation_of_approx {Ω : Opens (Fin 4 → ℝ)}
    {e : ℕ → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
    {ω : ℕ → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    (he1 : ∀ n a, ContDiff ℝ 1 (e n a)) (hω1 : ∀ n a, ContDiff ℝ 1 (ω n a))
    {e' : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
    {R' : Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    (he : L2LocTendsto Ω e e') (hωb : L2LocBounded Ω ω)
    (hT : L2LocNull Ω fun n (ab : Fin 4 × Fin 4) =>
      classicalTorsion matAct (e n) (ω n) ab.1 ab.2)
    (hRb : L2LocBounded Ω fun n (ab : Fin 4 × Fin 4) => classicalCurvature (ω n) ab.1 ab.2)
    (hRw : WeakActTendsto matAct Ω (fun n => classicalCurvature (ω n)) R')
    (hR' : ∀ a b (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
      MemLp (R' a b) 2 (volume.restrict C))
    (hdet : ∀ᵐ x, x ∈ Ω → 0 < (coframeMatrix fun μ => e' μ x).det)
    (hanti1 : ∀ᵐ x, x ∈ Ω → ∀ K L ρ σ,
      raisedCurvature (fun ρ σ => R' ρ σ x) L K ρ σ = -raisedCurvature (fun ρ σ => R' ρ σ x) K L ρ σ)
    (hanti2 : ∀ᵐ x, x ∈ Ω → ∀ K L ρ σ,
      raisedCurvature (fun ρ σ => R' ρ σ x) K L σ ρ = -raisedCurvature (fun ρ σ => R' ρ σ x) K L ρ σ)
    (K : Set (Fin 4 → ℝ)) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (k : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (α β lam : ℝ) (hβ : β ≠ 0) :
    ∫ x in K, classifiedMetricVariation α β lam minkowski (coframeMatrix fun μ => e' μ x) (k x)
        (raisedCurvature fun ρ σ => R' ρ σ x) =
      ∫ x in K, einsteinInsertionDensity β lam (coframeMatrix fun μ => e' μ x) (k x)
        (raisedCurvature fun ρ σ => R' ρ σ x) := by
  have hB := isDistributionalBianchi_of_approx matAct matAct_mul he1 hω1 he hωb hT hRb hRw hR'
  have hae : ∀ a b c, ∀ᵐ x, x ∈ Ω → bianchiForm matAct R' e' a b c x = 0 := fun a b c =>
    ae_bianchi_of_isDistributionalBianchi matAct hR' he.memLp_lim hB a b c
  have hall : ∀ᵐ x, x ∈ Ω → ∀ a b c, bianchiForm matAct R' e' a b c x = 0 := by
    have : ∀ᵐ x, ∀ a b c : Fin 4, x ∈ Ω → bianchiForm matAct R' e' a b c x = 0 := by
      simp only [ae_all_iff]; exact hae
    filter_upwards [this] with x hx hxΩ a b c using hx a b c hxΩ
  refine setIntegral_congr_ae hK.isClosed.measurableSet ?_
  filter_upwards [hall, hdet, hanti1, hanti2] with x h1 h2 h3 h4 hxK
  have hxΩ := hKΩ hxK
  exact classifiedMetricVariation_eq_einstein _ _ (h2 hxΩ) _ (h3 hxΩ) (h4 hxΩ)
    (satisfiesFirstBianchi_of_bianchiForm_eq_zero _ _ fun a b c => h1 hxΩ a b c) α β lam hβ


/-! ### Algebraic uniqueness of the torsion-free metric-compatible connection -/

/-- **Uniqueness of the Levi-Civita connection (algebraic core).**  Let `η` be symmetric and
nondegenerate and `e` an invertible coframe.  If the difference `A^I{}_{Ja}` of two connections
is metric compatible (`η_{IK} A^K{}_{Ja}` antisymmetric in `I, J`) and the two connections have
the same torsion for `e` (`A^I{}_{Ja} e^J_b - A^I{}_{Jb} e^J_a = 0`), then `A = 0`.  Hence a
torsion-free metric-compatible connection is unique (it is the Levi-Civita spin connection). -/
theorem leviCivita_difference_eq_zero {n : ℕ} (η e : Matrix (Fin n) (Fin n) ℝ)
    (hηdet : η.det ≠ 0) (hdet : e.det ≠ 0) (A : Fin n → Fin n → Fin n → ℝ)
    (hcompat : ∀ I J a, ∑ K, η I K * A K J a = -∑ K, η J K * A K I a)
    (htors : ∀ I a b, ∑ J, (A I J a * e J b - A I J b * e J a) = 0) : A = 0 := by
  set E := e⁻¹
  have hEe : E * e = 1 := Matrix.nonsing_inv_mul e (isUnit_iff_ne_zero.mpr hdet)
  -- frame components `B K J P = A^K{}_{J a} E^a_P`
  set M : Fin n → Matrix (Fin n) (Fin n) ℝ := fun K => Matrix.of fun J a => A K J a
  set B : Fin n → Matrix (Fin n) (Fin n) ℝ := fun K => M K * E
  have hBsym : ∀ K, (B K).transpose = B K := by
    intro K
    set N := (M K).transpose * e
    have hN : N.transpose = N := by
      ext a b
      have := htors K b a
      rw [Finset.sum_sub_distrib, sub_eq_zero] at this
      simp only [N, Matrix.transpose_apply, Matrix.mul_apply, M, Matrix.of_apply]
      exact this
    have h1 : (B K).transpose = E.transpose * N * E := by
      simp only [B, N, Matrix.transpose_mul, Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv e (isUnit_iff_ne_zero.mpr hdet), Matrix.mul_one]
    rw [h1]
    calc E.transpose * N * E = (E.transpose * N * E).transpose := by
          rw [Matrix.transpose_mul, Matrix.transpose_mul, hN, Matrix.transpose_transpose,
            Matrix.mul_assoc]
      _ = B K := by rw [← h1, Matrix.transpose_transpose]
  -- lowered components `C I J P = η_{IK} B K J P`
  set C : Fin n → Fin n → Fin n → ℝ := fun I J P => ∑ K, η I K * B K J P
  have hCsym : ∀ I J P, C I J P = C I P J := by
    intro I J P
    simp only [C]
    refine Finset.sum_congr rfl fun K _ => ?_
    have h := congrFun (congrFun (hBsym K) P) J
    rw [Matrix.transpose_apply] at h
    rw [h]
  have hCform : ∀ I J P, C I J P = ∑ a, (∑ K, η I K * A K J a) * E a P := by
    intro I J P
    simp only [C, B, Matrix.mul_apply, M, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun K _ => ?_
    ring
  have hCanti : ∀ I J P, C I J P = -C J I P := by
    intro I J P
    rw [hCform, hCform, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hcompat I J a]; ring
  have hC0 : ∀ I J P, C I J P = 0 := by
    intro I J P
    have h : C I J P = -C I J P := by
      calc C I J P = -C J I P := hCanti I J P
        _ = -C J P I := by rw [hCsym J I P]
        _ = C P J I := by rw [hCanti J P I, neg_neg]
        _ = C P I J := hCsym P J I
        _ = -C I P J := hCanti P I J
        _ = -C I J P := by rw [hCsym I P J]
    linarith
  -- `η` is invertible, so `B = 0`
  have hB0 : ∀ K J P, B K J P = 0 := by
    intro K J P
    have hv : η.mulVec (fun K => B K J P) = 0 := by
      ext I; simpa [Matrix.mulVec, dotProduct, C] using hC0 I J P
    have : (fun K => B K J P) = 0 := by
      have h := congrArg (fun v => η⁻¹.mulVec v) hv
      simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul η (isUnit_iff_ne_zero.mpr hηdet)]
        using h
    exact congrFun this K
  -- and `A = B e = 0`
  funext K J a
  have hM : M K = B K * e := by simp only [B, Matrix.mul_assoc, hEe, Matrix.mul_one]
  have : B K = 0 := by ext J P; exact hB0 K J P
  have h := congrFun (congrFun hM J) a
  simp only [this, Matrix.zero_mul, M, Matrix.of_apply] at h
  simpa using h


/-- **Uniqueness of the torsion-free metric-compatible limit connection.**  Two `L²_loc`
matrix connections that are both torsion-free in distributions for the same `L²_loc` coframe and
both `η`-compatible (Minkowski `η`) almost everywhere coincide almost everywhere wherever the
coframe is nondegenerate.  In particular the torsion-free limit connection of
`thm:supp-renewal-palatini` is the (unique) Levi-Civita spin connection of its coframe. -/
theorem ae_eq_of_isTorsionFree {Ω : Opens (Fin 4 → ℝ)} {e : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
    {ω ω' : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    (he : ∀ c (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω → MemLp (e c) 2 (volume.restrict C))
    (hω : ∀ a (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω → MemLp (ω a) 2 (volume.restrict C))
    (hω' : ∀ a (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
      MemLp (ω' a) 2 (volume.restrict C))
    (hT : IsTorsionFree matAct Ω e ω) (hT' : IsTorsionFree matAct Ω e ω')
    (hdet : ∀ᵐ x, x ∈ Ω → (coframeMatrix fun μ => e μ x).det ≠ 0)
    (hc : ∀ᵐ x, x ∈ Ω → ∀ a I J,
      ∑ K, minkowski I K * ω a x K J = -∑ K, minkowski J K * ω a x K I)
    (hc' : ∀ᵐ x, x ∈ Ω → ∀ a I J,
      ∑ K, minkowski I K * ω' a x K J = -∑ K, minkowski J K * ω' a x K I) :
    ∀ᵐ x, x ∈ Ω → ∀ a, ω a x = ω' a x := by
  set D : Fin 4 → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ) := fun a b x =>
    matAct (ω a x - ω' a x) (e b x) - matAct (ω b x - ω' b x) (e a x) with hD
  -- integrability of the four products on compacts
  have hi : ∀ (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω → ∀ (ψ : (Fin 4 → ℝ) → ℝ) (M0 : ℝ),
      Continuous ψ → (∀ x, ‖ψ x‖ ≤ M0) →
      ∀ (w : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ),
      (∀ a, MemLp (w a) 2 (volume.restrict C)) → ∀ a b,
      Integrable (fun x => ψ x • matAct (w a x) (e b x)) (volume.restrict C) := by
    intro C hC hCΩ ψ M0 hψ hM0 w hw a b
    have : IsFiniteMeasure (volume.restrict C) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hC.measure_lt_top⟩
    exact integrable_smul_bilin matAct hψ.aestronglyMeasurable hM0 (hw a) (he b C hC hCΩ)
  have hDsplit : ∀ a b x, D a b x = (matAct (ω a x) (e b x) - matAct (ω' a x) (e b x)) -
      (matAct (ω b x) (e a x) - matAct (ω' b x) (e a x)) := by
    intro a b x; simp only [hD, map_sub, ContinuousLinearMap.sub_apply]
  -- `∫ φ D = 0` for every test function
  have hzero : ∀ a b (φ : 𝓓(Ω, ℝ)), ∫ x, φ x • D a b x = 0 := by
    intro a b φ
    set C := tsupport (φ : (Fin 4 → ℝ) → ℝ)
    have hC : IsCompact C := φ.hasCompactSupport
    have hCΩ : C ⊆ Ω := φ.tsupport_subset
    have hz0 : ∀ x, x ∉ C → φ x = 0 := fun x hx => test_eq_zero_off φ hx
    obtain ⟨M0, hM0⟩ := exists_bound_of_eq_zero_off φ.continuous hC hz0
    have i1 := hi C hC hCΩ φ M0 φ.continuous hM0 ω (fun a => hω a C hC hCΩ)
    have i2 := hi C hC hCΩ φ M0 φ.continuous hM0 ω' (fun a => hω' a C hC hCΩ)
    have h := hT φ a b
    have h' := hT' φ a b
    unfold torsionPairing at h h'
    simp only [integral_test_eq_setIntegral hz0] at h h' ⊢
    have hsub : (∫ x in C, φ x • matAct (ω a x) (e b x)) - (∫ x in C, φ x • matAct (ω b x) (e a x)) -
        ((∫ x in C, φ x • matAct (ω' a x) (e b x)) - ∫ x in C, φ x • matAct (ω' b x) (e a x)) = 0 := by
      have := congrArg₂ (· - ·) h h'
      simp only [sub_zero] at this
      rw [← this]; abel
    rw [← integral_sub (i1 a b) (i1 b a), ← integral_sub (i2 a b) (i2 b a),
      ← integral_sub ((i1 a b).sub' (i1 b a)) ((i2 a b).sub' (i2 b a))] at hsub
    rw [← hsub]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hDsplit, smul_sub]
    abel
  -- the pointwise conclusion
  have hloc : ∀ a b, LocallyIntegrableOn (D a b) Ω := by
    intro a b
    rw [locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed]
    intro K hKΩ hK
    have i1 := hi K hK hKΩ (fun _ => 1) 1 continuous_const (fun _ => by simp) ω
      (fun a => hω a K hK hKΩ)
    have i2 := hi K hK hKΩ (fun _ => 1) 1 continuous_const (fun _ => by simp) ω'
      (fun a => hω' a K hK hKΩ)
    simp only [one_smul] at i1 i2
    refine (((i1 a b).sub' (i2 a b)).sub' ((i1 b a).sub' (i2 b a))).congr ?_
    exact Eventually.of_forall fun x => (hDsplit a b x).symm
  have hae : ∀ a b, ∀ᵐ x, x ∈ Ω → D a b x = 0 := fun a b =>
    Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hloc a b) fun g hg hgc hgs =>
      hzero a b ⟨g, hg, hgc, hgs⟩
  have hall : ∀ᵐ x, x ∈ Ω → ∀ a b, D a b x = 0 := by
    have : ∀ᵐ x, ∀ a b : Fin 4, x ∈ Ω → D a b x = 0 := by
      simp only [ae_all_iff]; exact hae
    filter_upwards [this] with x hx hxΩ a b using hx a b hxΩ
  filter_upwards [hall, hdet, hc, hc'] with x h1 h2 h3 h4 hxΩ
  have hA := leviCivita_difference_eq_zero minkowski (coframeMatrix fun μ => e μ x)
    (by rw [det_minkowski]; norm_num) (h2 hxΩ) (fun I J a => (ω a x - ω' a x) I J)
    (fun I J a => by
      simp only [Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]
      rw [h3 hxΩ a I J, h4 hxΩ a I J]; ring)
    (fun I a b => by
      have := congrFun (h1 hxΩ a b) I
      simp only [hD, matAct_apply, Pi.sub_apply, Matrix.mulVec, dotProduct, Pi.zero_apply]
        at this
      simp only [coframeMatrix, Matrix.of_apply, Finset.sum_sub_distrib]
      linarith)
  intro a
  ext I J
  have := congrFun (congrFun (congrFun hA I) J) a
  simp only [Matrix.sub_apply, Pi.zero_apply] at this
  linarith


theorem coframeMatrix_basis : coframeMatrix (fun μ => (Pi.single μ 1 : Fin 4 → ℝ)) = 1 := by
  ext I μ
  simp [coframeMatrix, Pi.single_apply, Matrix.one_apply]

/-- Non-vacuity of the pointwise hypotheses of `integral_classifiedMetricVariation_of_approx`
(the approximation packet is checked in `DistributionalFirstBianchi`): the constant basis
coframe is oriented, and the zero curvature has the internal antisymmetries and satisfies the
first Bianchi identity. -/
example : 0 < (coframeMatrix fun μ => (Pi.single μ 1 : Fin 4 → ℝ)).det ∧
    (∀ K L ρ σ, raisedCurvature (fun _ _ => 0) L K ρ σ =
      -raisedCurvature (fun _ _ => 0) K L ρ σ) ∧
    SatisfiesFirstBianchi minkowski (coframeMatrix fun μ => (Pi.single μ 1 : Fin 4 → ℝ))
      (raisedCurvature fun _ _ => 0) := by
  refine ⟨by rw [coframeMatrix_basis]; simp, fun _ _ _ _ => by simp [raisedCurvature], ?_⟩
  intro K ν ρ σ
  simp [bianchiTerm, raisedCurvature]

end RenewalGeometry.LimitEinsteinInsertion
