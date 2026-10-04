/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.PathOrderedExponential
import RenewalGeometry.Analysis.LipschitzRiemannSumError
import RenewalGeometry.GaugeTheory.WilsonTransportConsistency

/-!
# Covariant cell-average quadrature (`lem:covariant-quadrature`)

Einstein–Standard-Model action-closure manuscript, "Equivariant consistency of the explicit
local action".  Let `𝔻 = d + ω` be a metric connection on a trivialised bundle with fibre a
real Hilbert space `V` over the chart `[0,1]^d` (the manuscript's `d = 4`; `V` = the finite
direct sum of coframe, adjoint, Higgs and spinor test fibres, finite-dimensional), i.e.
`ω : ℝ^d → L(ℝ^d, End V)` with skew-adjoint values (`IsMetric`).  On the uniform grid of mesh
`h = 1/M` with cells `C_x = x + [0,h)^d`, fix for every node `x` and every `y ∈ C_x` a path
`γ_{x,y} : [0,1] → ℝ^d` from `y` to `x` of length `≤ ℓ` (`ℓ = Ch`) and let `P_{x←y}` be the
parallel transport of `𝔻` along it (`P' = -ω(γ)(γ') P`, `P(0) = 1`).  The covariant test
average is `(Q_h v)(x) = h^{-d} ∫_{C_x} P_{x←y} v(y) dy` (`cellAverage`).

* `inner_transport_apply_apply` / `norm_transport_apply`: metric compatibility makes every
  transport an isometry.
* `abs_inner_covariant_ftc` (**covariant fundamental theorem of calculus**): for a section `X`
  with `‖𝔻X‖ ≤ B` along the path, `|⟪X(x), P_{x←y} w⟫ - ⟪X(y), w⟫| ≤ B ℓ ‖w‖`.
* `abs_covariant_quadrature_sub_le` (**`eq:covariant-quadrature`**):
  `|h^d Σ_x ⟪X(x), (Q_h v)(x)⟫ - ∫ ⟪X, v⟫| ≤ ℓ B ‖v‖_{L¹}` (so `≤ C h ‖𝔻X‖_∞ ‖v‖_1` for paths of
  length `≤ Ch`).
* `norm_cellAverage_le` (`‖Q_h v‖_{∞,h} ≤ ‖v‖_∞`) and `cellAverage_sq_sum_le`
  (`‖Q_h v‖_{2,h} ≤ ‖v‖_2`, Jensen / Cauchy–Schwarz on each cell).
* Equivariance under unitary changes of frame: `isTransport_gaugeTransform` (endpoint
  transformation `P ↦ g(γ(t)) P g(γ(0))⁻¹` of parallel transport under
  `ω ↦ g ω g⁻¹ - (dg) g⁻¹`), `cellAverage_gaugeTransform` (`Q'_h(g v) = g Q_h v`) and
  `inner_cellAverage_gaugeTransform` (both sides of `eq:covariant-quadrature` are invariant).
* `exists_transport_of_le` (gluing): parallel transports of a continuous bounded coefficient
  exist on every segment (not only short ones).
* `straight` paths: `γ_{x,y}(t) = y + t(x - y)`, of length `‖x - y‖ < h`; for a Lipschitz
  metric connection the transports exist (`exists_straightTransport`) and depend continuously on
  `y` (`continuousOn_straightTransport`), so the measurability hypothesis of the general lemma is
  automatic: `abs_covariant_quadrature_straight_sub_le` is the lemma for this concrete path family,
  with constant `C = 1` (sup norm).

Renderings (disclosed): the buffered chart is the unit cube (any coordinate box is an affine
image); the bundle is trivialised on the chart, as in the manuscript's fixed local frames; all
lengths and operator norms use the sup norm of `ℝ^d` (other norms change `C` by a dimensional
factor); "a fixed family of paths" is a family `γ_{x,y}` with a measurable transport field
`y ↦ P_{x←y}` (automatic for the straight family).
-/

open MeasureTheory Set Filter Topology Finset
open scoped NNReal InnerProductSpace

noncomputable section

namespace RenewalGeometry.CovariantQuadrature

open PathOrderedExp UnitCubeRiemannSum LipschitzRiemannSum

/-! ### Gluing: transports exist on every segment -/

section Gluing

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Two transports on adjacent segments glue to a transport. -/
theorem IsTransport.glue {ω : ℝ → 𝔸} {a c b : ℝ} {U W : ℝ → 𝔸} (hac : a ≤ c) (hcb : c ≤ b)
    (hU : IsTransport ω a c U) (hW : IsTransport ω c b W) (hc : W c = U c) :
    IsTransport ω a b (fun t => if t ≤ c then U t else W t) := by
  intro t ht
  have hval : (fun t => if t ≤ c then U t else W t) t =
      if t ≤ c then U t else W t := rfl
  have hunion : Icc a b = Icc a c ∪ Icc c b := (Icc_union_Icc_eq_Icc hac hcb).symm
  rw [hunion]
  apply HasDerivWithinAt.union
  · by_cases htc : t ≤ c
    · have h1 := hU t ⟨ht.1, htc⟩
      refine h1.congr_of_mem (fun s hs => by simp [hs.2]) ⟨ht.1, htc⟩ |>.congr_deriv ?_
      simp [htc]
    · have : t ∉ closure (Icc a c) := by
        rw [closure_Icc]; exact fun h => htc h.2
      exact HasFDerivWithinAt.of_notMem_closure this
  · by_cases htc : c ≤ t
    · have h1 := hW t ⟨htc, ht.2⟩
      have heq : ∀ s ∈ Icc c b, (if s ≤ c then U s else W s) = W s := by
        intro s hs
        by_cases hsc : s ≤ c
        · have : s = c := le_antisymm hsc hs.1
          subst this; simp [hc]
        · simp [hsc]
      refine (h1.congr_of_mem heq ⟨htc, ht.2⟩).congr_deriv ?_
      change _ = -(ω t * (if t ≤ c then U t else W t))
      rw [heq t ⟨htc, ht.2⟩]
    · have : t ∉ closure (Icc c b) := by
        rw [closure_Icc]; exact fun h => htc h.1
      exact HasFDerivWithinAt.of_notMem_closure this

/-- **Transports exist on every segment**: for `ω` continuous on `[a,b]` with `‖ω‖ ≤ K`, every
initial value `U₀` has a transport on `[a,b]` (gluing short Picard–Lindelöf pieces). -/
theorem exists_transport_of_le {ω : ℝ → 𝔸} {a b K : ℝ} (hab : a ≤ b)
    (hω : ContinuousOn ω (Icc a b)) (hK : ∀ t ∈ Icc a b, ‖ω t‖ ≤ K) (U₀ : 𝔸) :
    ∃ U : ℝ → 𝔸, U a = U₀ ∧ IsTransport ω a b U := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK a ⟨le_rfl, hab⟩)
  set δ : ℝ := 1 / (2 * (K + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hKδ : K * δ ≤ 1 / 2 := by
    rw [hδ, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have key : ∀ n : ℕ, ∀ a', a ≤ a' → a' ≤ b → b - a' ≤ n * δ → ∀ U₀ : 𝔸,
      ∃ U : ℝ → 𝔸, U a' = U₀ ∧ IsTransport ω a' b U := by
    intro n
    induction n with
    | zero =>
      intro a' ha' hab' hn U₀
      have hb : b = a' := by simp at hn; linarith
      subst hb
      exact exists_transport le_rfl (hω.mono (Icc_subset_Icc ha' le_rfl))
        (fun t ht => hK t ⟨ha'.trans ht.1, ht.2⟩) (by norm_num) U₀
    | succ n ih =>
      intro a' ha' hab' hn U₀
      by_cases hshort : b - a' ≤ δ
      · exact exists_transport hab' (hω.mono (Icc_subset_Icc ha' le_rfl))
          (fun t ht => hK t ⟨ha'.trans ht.1, ht.2⟩)
          ((mul_le_mul_of_nonneg_left hshort hK0).trans hKδ) U₀
      · push Not at hshort
        set c := a' + δ
        have hac : a' ≤ c := by linarith
        have hcb : c ≤ b := by linarith
        obtain ⟨U, hU0, hU⟩ := exists_transport hac (hω.mono (Icc_subset_Icc ha' hcb))
          (fun t ht => hK t ⟨ha'.trans ht.1, ht.2.trans hcb⟩)
          (by rw [show c - a' = δ by ring]; exact hKδ) U₀
        obtain ⟨W, hW0, hW⟩ := ih c (ha'.trans hac) hcb (by push_cast at hn; linarith) (U c)
        refine ⟨fun t => if t ≤ c then U t else W t, by simp [hac, hU0],
          IsTransport.glue hac hcb hU hW hW0⟩
  obtain ⟨n, hn⟩ := exists_nat_ge ((b - a) / δ)
  exact key n a le_rfl hab (by rwa [div_le_iff₀ hδpos] at hn) U₀

end Gluing

/-! ### Metric connections, covariant derivative, isometric transport -/

variable {d : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- A connection one-form on the trivialised bundle `ℝ^d × V`: `ω x u ∈ End V` is the
connection matrix in direction `u` at `x`, `𝔻_u = ∂_u + ω(u)`. -/
abbrev Connection (d : ℕ) (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] :=
  (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] (V →L[ℝ] V)

/-- Metric compatibility: every `ω x u` is skew-adjoint. -/
def IsMetric (ω : Connection d V) : Prop :=
  ∀ x u (a b : V), ⟪ω x u a, b⟫_ℝ = -⟪a, ω x u b⟫_ℝ

/-- The covariant derivative `𝔻X(x) = dX(x) + ω(x)(·) X(x) : ℝ^d →L V`. -/
def covDeriv (ω : Connection d V) (X : (Fin d → ℝ) → V) (x : Fin d → ℝ) :
    (Fin d → ℝ) →L[ℝ] V :=
  fderiv ℝ X x + (ContinuousLinearMap.apply ℝ V (X x)).comp (ω x)

omit [CompleteSpace V] in
theorem covDeriv_apply (ω : Connection d V) (X : (Fin d → ℝ) → V) (x u : Fin d → ℝ) :
    covDeriv ω X x u = fderiv ℝ X x u + ω x u (X x) := rfl

omit [CompleteSpace V] in
/-- Transports of a skew-adjoint coefficient preserve inner products. -/
theorem inner_transport_apply_apply {c : ℝ → (V →L[ℝ] V)} {P : ℝ → (V →L[ℝ] V)}
    (hP : IsTransport c 0 1 P) (hP0 : P 0 = 1)
    (hskew : ∀ t ∈ Icc (0 : ℝ) 1, ∀ a b : V, ⟪c t a, b⟫_ℝ = -⟪a, c t b⟫_ℝ) (a b : V) :
    ∀ t ∈ Icc (0 : ℝ) 1, ⟪P t a, P t b⟫_ℝ = ⟪a, b⟫_ℝ := by
  have hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun t => ⟪P t a, P t b⟫_ℝ) 0 (Icc 0 1) t := by
    intro t ht
    have ha := (hP t ht).clm_apply (hasDerivWithinAt_const t (Icc 0 1) a)
    have hb := (hP t ht).clm_apply (hasDerivWithinAt_const t (Icc 0 1) b)
    have := ha.inner ℝ hb
    refine this.congr_deriv ?_
    simp only [map_zero, add_zero, neg_apply, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_apply, inner_neg_left, inner_neg_right]
    rw [hskew t ht]
    ring
  intro t ht
  have := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hd
    (fun _ _ => by simp : ∀ x ∈ Icc (0 : ℝ) 1, ‖(0 : ℝ)‖ ≤ 0) ⟨le_rfl, zero_le_one⟩ ht
  simp only [zero_mul, norm_le_zero_iff, sub_eq_zero] at this
  rw [this, hP0]
  rfl

omit [CompleteSpace V] in
/-- Transports of a skew-adjoint coefficient are isometries. -/
theorem norm_transport_apply {c : ℝ → (V →L[ℝ] V)} {P : ℝ → (V →L[ℝ] V)}
    (hP : IsTransport c 0 1 P) (hP0 : P 0 = 1)
    (hskew : ∀ t ∈ Icc (0 : ℝ) 1, ∀ a b : V, ⟪c t a, b⟫_ℝ = -⟪a, c t b⟫_ℝ) (a : V)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ‖P t a‖ = ‖a‖ := by
  have := inner_transport_apply_apply hP hP0 hskew a a t ht
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at this
  have h := congrArg Real.sqrt this
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h

omit [CompleteSpace V] in
theorem opNorm_transport_le {c : ℝ → (V →L[ℝ] V)} {P : ℝ → (V →L[ℝ] V)}
    (hP : IsTransport c 0 1 P) (hP0 : P 0 = 1)
    (hskew : ∀ t ∈ Icc (0 : ℝ) 1, ∀ a b : V, ⟪c t a, b⟫_ℝ = -⟪a, c t b⟫_ℝ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ‖P t‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => by
    rw [norm_transport_apply hP hP0 hskew a ht, one_mul]

omit [CompleteSpace V] in
/-- The path coefficient `t ↦ ω(γ t)(γ' t)` of a metric connection is skew-adjoint. -/
theorem skew_pathCoeff {ω : Connection d V} (hω : IsMetric ω) (γ γ' : ℝ → Fin d → ℝ) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ a b : V, ⟪ω (γ t) (γ' t) a, b⟫_ℝ = -⟪a, ω (γ t) (γ' t) b⟫_ℝ :=
  fun _ _ a b => hω _ _ a b

omit [CompleteSpace V] in
/-- **Covariant fundamental theorem of calculus.**  If `P` is the parallel transport of the
metric connection `ω` along a path `γ` from `γ 0` to `γ 1` with speed `‖γ'‖ ≤ ℓ`, and the section
`X` has covariant derivative `‖𝔻X‖ ≤ B` along `γ`, then for every fibre vector `w`
`|⟪X(γ 1), P(1) w⟫ - ⟪X(γ 0), w⟫| ≤ B ℓ ‖w‖`, i.e. `‖P_{γ0←γ1} X(γ 1) - X(γ 0)‖ ≤ B ℓ`. -/
theorem abs_inner_covariant_ftc {ω : Connection d V} (hω : IsMetric ω) {X : (Fin d → ℝ) → V}
    {γ γ' : ℝ → Fin d → ℝ} {P : ℝ → (V →L[ℝ] V)}
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt γ (γ' t) (Icc 0 1) t)
    (hX : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ X (γ t))
    (hP : IsTransport (fun t => ω (γ t) (γ' t)) 0 1 P) (hP0 : P 0 = 1) {B ℓ : ℝ}
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, ‖covDeriv ω X (γ t)‖ ≤ B)
    (hℓ : ∀ t ∈ Icc (0 : ℝ) 1, ‖γ' t‖ ≤ ℓ) (w : V) :
    |⟪X (γ 1), P 1 w⟫_ℝ - ⟪X (γ 0), w⟫_ℝ| ≤ B * ℓ * ‖w‖ := by
  have hskew := skew_pathCoeff hω γ γ'
  have hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun t => ⟪X (γ t), P t w⟫_ℝ)
      ⟪covDeriv ω X (γ t) (γ' t), P t w⟫_ℝ (Icc 0 1) t := by
    intro t ht
    have h1 : HasDerivWithinAt (X ∘ γ) (fderiv ℝ X (γ t) (γ' t)) (Icc 0 1) t :=
      (hX t ht).hasFDerivAt.comp_hasDerivWithinAt t (hγ t ht)
    have h2 := (hP t ht).clm_apply (hasDerivWithinAt_const t (Icc 0 1) w)
    have := h1.inner ℝ h2
    refine this.congr_deriv ?_
    simp only [Function.comp_apply, map_zero, add_zero, neg_apply,
      ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, inner_neg_right,
      covDeriv_apply, inner_add_left]
    rw [hskew t ht]
    ring
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖⟪covDeriv ω X (γ t) (γ' t), P t w⟫_ℝ‖ ≤ B * ℓ * ‖w‖ := by
    intro t ht
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [norm_transport_apply hP hP0 hskew w ht]
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB t ht)
    gcongr
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hB t ht) (hℓ t ht) (norm_nonneg _) hB0)
  have := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hd hbound
    ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
  simp only [Real.norm_eq_abs, sub_zero, abs_one, mul_one, hP0] at this
  simpa using this

/-! ### The covariant cell average and the quadrature estimate -/

/-- **The covariant test average** `(Q_h v)(x_k) = h^{-d} ∫_{C_k} P_{x_k←y} v(y) dy`
(`eq:covariant-test-average`), `h = 1/M`, `P k y = P_{x_k←y}`. -/
def cellAverage {M : ℕ} (P : (Fin d → Fin M) → (Fin d → ℝ) → (V →L[ℝ] V))
    (v : (Fin d → ℝ) → V) (k : Fin d → Fin M) : V :=
  ((M : ℝ) ^ d) • ∫ y in cell M k, P k y (v y)

omit [CompleteSpace V] in
/-- Integrability of the transported test on a cell. -/
theorem integrableOn_transport_apply {M : ℕ} (hM : 0 < M)
    {P : (Fin d → Fin M) → (Fin d → ℝ) → (V →L[ℝ] V)} {v : (Fin d → ℝ) → V}
    (hv : IntegrableOn v (Icc (0 : Fin d → ℝ) 1)) (k : Fin d → Fin M)
    (hPm : AEStronglyMeasurable (P k) (volume.restrict (cell M k)))
    (hPn : ∀ y ∈ cell M k, ‖P k y‖ ≤ 1) :
    IntegrableOn (fun y => P k y (v y)) (cell M k) := by
  have hvk : IntegrableOn v (cell M k) := hv.mono_set (cell_subset_Icc hM k)
  refine Integrable.mono' hvk.norm ?_ ?_
  · exact (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂ hPm
      hvk.aestronglyMeasurable)
  · refine (ae_restrict_iff' (measurableSet_cell M k)).2 (Eventually.of_forall fun y hy => ?_)
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (by simpa using mul_le_mul_of_nonneg_right (hPn y hy) (norm_nonneg (v y)))

/-- The weighted node pairing equals the cell integral: `h^d ⟪X(x_k), (Q_h v)(x_k)⟫ =
∫_{C_k} ⟪X(x_k), P_{x_k←y} v(y)⟫ dy`. -/
theorem cellVolume_mul_inner_cellAverage {M : ℕ} (hM : 0 < M)
    {P : (Fin d → Fin M) → (Fin d → ℝ) → (V →L[ℝ] V)} {v : (Fin d → ℝ) → V}
    (k : Fin d → Fin M) (hint : IntegrableOn (fun y => P k y (v y)) (cell M k)) (z : V) :
    (1 / (M : ℝ)) ^ d * ⟪z, cellAverage P v k⟫_ℝ = ∫ y in cell M k, ⟪z, P k y (v y)⟫_ℝ := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  rw [integral_inner hint z, cellAverage, inner_smul_right, ← mul_assoc, ← mul_pow,
    one_div_mul_cancel hM'.ne', one_pow, one_mul]

/-- **`eq:covariant-quadrature`.**  For a metric connection `ω`, paths `γ_{k,y}` from `y ∈ C_k`
to the node `x_k` with speed `≤ ℓ`, the parallel transports `P_{k,y}` along them (with a
measurable transport field `y ↦ P_{x_k←y}`), a section `X` continuous on the cube,
differentiable along the paths with `‖𝔻X‖ ≤ B` there, and an integrable test `v`:
`|h^d Σ_k ⟪X(x_k), (Q_h v)(x_k)⟫ - ∫_{[0,1]^d} ⟪X, v⟫| ≤ ℓ B ‖v‖_{L¹}`. -/
theorem abs_covariant_quadrature_sub_le {M : ℕ} (hM : 0 < M) {ω : Connection d V}
    (hω : IsMetric ω) {X : (Fin d → ℝ) → V} (hXc : ContinuousOn X (Icc 0 1))
    {v : (Fin d → ℝ) → V} (hv : IntegrableOn v (Icc (0 : Fin d → ℝ) 1))
    {γ γ' : (Fin d → Fin M) → (Fin d → ℝ) → ℝ → Fin d → ℝ}
    {P : (Fin d → Fin M) → (Fin d → ℝ) → ℝ → (V →L[ℝ] V)} {B ℓ : ℝ}
    (hγ0 : ∀ k, ∀ y ∈ cell M k, γ k y 0 = y) (hγ1 : ∀ k, ∀ y ∈ cell M k, γ k y 1 = gridPoint M k)
    (hγ : ∀ k, ∀ y ∈ cell M k, ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (γ k y) (γ' k y t) (Icc 0 1) t)
    (hℓ : ∀ k, ∀ y ∈ cell M k, ∀ t ∈ Icc (0 : ℝ) 1, ‖γ' k y t‖ ≤ ℓ)
    (hX : ∀ k, ∀ y ∈ cell M k, ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ X (γ k y t))
    (hB : ∀ k, ∀ y ∈ cell M k, ∀ t ∈ Icc (0 : ℝ) 1, ‖covDeriv ω X (γ k y t)‖ ≤ B)
    (hP : ∀ k, ∀ y ∈ cell M k, IsTransport (fun t => ω (γ k y t) (γ' k y t)) 0 1 (P k y))
    (hP0 : ∀ k, ∀ y ∈ cell M k, P k y 0 = 1)
    (hPm : ∀ k, AEStronglyMeasurable (fun y => P k y 1) (volume.restrict (cell M k))) :
    |(1 / (M : ℝ)) ^ d * ∑ k : Fin d → Fin M, ⟪X (gridPoint M k),
        cellAverage (fun k y => P k y 1) v k⟫_ℝ - ∫ y in Icc (0 : Fin d → ℝ) 1, ⟪X y, v y⟫_ℝ| ≤
      ℓ * B * ∫ y in Icc (0 : Fin d → ℝ) 1, ‖v y‖ := by
  have hPn : ∀ k, ∀ y ∈ cell M k, ‖P k y 1‖ ≤ 1 := fun k y hy =>
    opNorm_transport_le (hP k y hy) (hP0 k y hy) (skew_pathCoeff hω _ _) ⟨zero_le_one, le_rfl⟩
  have hint : ∀ k, IntegrableOn (fun y => P k y 1 (v y)) (cell M k) := fun k =>
    integrableOn_transport_apply (P := fun k y => P k y 1) hM hv k (hPm k) (hPn k)
  -- integrability of `⟪X, v⟫` on the cube
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : Fin d → ℝ)) (b := 1)).exists_bound_of_continuousOn hXc
  have hXv : IntegrableOn (fun y => ⟪X y, v y⟫_ℝ) (Icc (0 : Fin d → ℝ) 1) := by
    refine Integrable.mono' (hv.norm.const_mul C) ?_ ?_
    · exact (hXc.aestronglyMeasurable measurableSet_Icc).inner hv.aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun y hy => ?_)
      rw [Real.norm_eq_abs]
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (hC y hy) (norm_nonneg _))
  rw [Finset.mul_sum, setIntegral_Icc_eq_sum_cell_of_integrableOn hM _ hXv,
    setIntegral_Icc_eq_sum_cell_of_integrableOn hM _ hv.norm, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [cellVolume_mul_inner_cellAverage hM k (hint k),
    ← integral_sub ((hint k).const_inner _) (hXv.mono_set (cell_subset_Icc hM k)),
    ← Real.norm_eq_abs, ← integral_const_mul]
  refine norm_integral_le_of_norm_le
    ((IntegrableOn.mono_set hv.norm (cell_subset_Icc hM k)).const_mul _) ?_
  refine (ae_restrict_iff' (measurableSet_cell M k)).2 (Eventually.of_forall fun y hy => ?_)
  rw [Real.norm_eq_abs]
  have := abs_inner_covariant_ftc hω (hγ k y hy) (hX k y hy) (hP k y hy) (hP0 k y hy)
    (hB k y hy) (hℓ k y hy) (v y)
  rw [hγ1 k y hy, hγ0 k y hy] at this
  refine this.trans (le_of_eq ?_)
  ring

omit [CompleteSpace V] in
/-- **Sup bound** `‖Q_h v‖_{∞,h} ≤ ‖v‖_∞`: if `‖v‖ ≤ m` on the cell, then `‖(Q_h v)(x_k)‖ ≤ m`. -/
theorem norm_cellAverage_le {M : ℕ} (hM : 0 < M)
    {P : (Fin d → Fin M) → (Fin d → ℝ) → (V →L[ℝ] V)} {v : (Fin d → ℝ) → V}
    (k : Fin d → Fin M) (hPn : ∀ y ∈ cell M k, ∀ a : V, ‖P k y a‖ = ‖a‖) {m : ℝ}
    (hm : ∀ y ∈ cell M k, ‖v y‖ ≤ m) : ‖cellAverage P v k‖ ≤ m := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  rw [cellAverage, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have := norm_setIntegral_le_of_norm_le_const (volume_cell_lt_top hM k)
    (fun y hy => (hPn y hy (v y)).trans_le (hm y hy) : ∀ y ∈ cell M k, ‖P k y (v y)‖ ≤ m)
  rw [volume_real_cell hM k] at this
  calc (M : ℝ) ^ d * ‖∫ y in cell M k, P k y (v y)‖ ≤ (M : ℝ) ^ d * (m * (1 / (M : ℝ)) ^ d) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = m := by
        rw [mul_comm m, ← mul_assoc, ← mul_pow, mul_one_div_cancel hM'.ne', one_pow, one_mul]

/-- Cauchy–Schwarz on a set of finite positive measure: `(∫_s f)² ≤ μ(s) ∫_s f²`. -/
theorem sq_setIntegral_le_mul {s : Set (Fin d → ℝ)} (hs : volume s < ⊤) {f : (Fin d → ℝ) → ℝ}
    (hf : IntegrableOn f s) (hf2 : IntegrableOn (fun y => f y ^ 2) s) :
    (∫ y in s, f y) ^ 2 ≤ volume.real s * ∫ y in s, f y ^ 2 := by
  rcases eq_or_lt_of_le (measureReal_nonneg : 0 ≤ volume.real s) with h0 | hpos
  · have hz : volume s = 0 := by
      rw [measureReal_def, eq_comm, ENNReal.toReal_eq_zero_iff] at h0
      exact h0.resolve_right hs.ne
    simp [Measure.restrict_eq_zero.2 hz]
  · set a := (∫ y in s, f y) / volume.real s
    have hconst : IntegrableOn (fun _ : Fin d → ℝ => (1 : ℝ)) s := integrableOn_const hs.ne
    have hnn : 0 ≤ ∫ y in s, (f y - a) ^ 2 := integral_nonneg fun y => sq_nonneg _
    have hexp : ∫ y in s, (f y - a) ^ 2 =
        (∫ y in s, f y ^ 2) - 2 * a * (∫ y in s, f y) + a ^ 2 * volume.real s := by
      have e : (fun y => (f y - a) ^ 2) = fun y => f y ^ 2 - 2 * a * f y + a ^ 2 * 1 := by
        funext y; ring
      have i1 : IntegrableOn (fun y => f y ^ 2 - 2 * a * f y) s := hf2.sub (hf.const_mul _)
      have i2 : IntegrableOn (fun _ : Fin d → ℝ => a ^ 2 * 1) s := hconst.const_mul _
      rw [e, integral_add i1 i2,
        integral_sub hf2 (hf.const_mul _), integral_const_mul, integral_const_mul,
        setIntegral_const, smul_eq_mul, mul_one]
    rw [hexp] at hnn
    have ha : a * volume.real s = ∫ y in s, f y := div_mul_cancel₀ _ hpos.ne'
    have : (∫ y in s, f y) ^ 2 = a * (∫ y in s, f y) * volume.real s := by
      rw [← ha]; ring
    nlinarith

omit [CompleteSpace V] in
/-- **`L²` bound** `‖Q_h v‖_{2,h} ≤ ‖v‖_2`: `h^d Σ_k ‖(Q_h v)(x_k)‖² ≤ ∫_{[0,1]^d} ‖v‖²`. -/
theorem cellAverage_sq_sum_le {M : ℕ} (hM : 0 < M)
    {P : (Fin d → Fin M) → (Fin d → ℝ) → (V →L[ℝ] V)} {v : (Fin d → ℝ) → V}
    (hv : IntegrableOn v (Icc (0 : Fin d → ℝ) 1))
    (hv2 : IntegrableOn (fun y => ‖v y‖ ^ 2) (Icc (0 : Fin d → ℝ) 1))
    (hPm : ∀ k, AEStronglyMeasurable (P k) (volume.restrict (cell M k)))
    (hPn : ∀ k, ∀ y ∈ cell M k, ∀ a : V, ‖P k y a‖ = ‖a‖) :
    (1 / (M : ℝ)) ^ d * ∑ k : Fin d → Fin M, ‖cellAverage P v k‖ ^ 2 ≤
      ∫ y in Icc (0 : Fin d → ℝ) 1, ‖v y‖ ^ 2 := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  rw [setIntegral_Icc_eq_sum_cell_of_integrableOn hM _ hv2, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have hPn' : ∀ y ∈ cell M k, ‖P k y‖ ≤ 1 := fun y hy =>
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => by rw [hPn k y hy, one_mul]
  have hint := integrableOn_transport_apply hM hv k (hPm k) hPn'
  have hvk : IntegrableOn v (cell M k) := hv.mono_set (cell_subset_Icc hM k)
  have h1 : ‖∫ y in cell M k, P k y (v y)‖ ≤ ∫ y in cell M k, ‖v y‖ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq (setIntegral_congr_fun
      (measurableSet_cell M k) fun y hy => hPn k y hy (v y)))
  have h2 := sq_setIntegral_le_mul (volume_cell_lt_top hM k) hvk.norm
    (hv2.mono_set (cell_subset_Icc hM k))
  rw [volume_real_cell hM k] at h2
  have hnn : 0 ≤ ‖∫ y in cell M k, P k y (v y)‖ := norm_nonneg _
  rw [cellAverage, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_pow]
  calc (1 / (M : ℝ)) ^ d * (((M : ℝ) ^ d) ^ 2 * ‖∫ y in cell M k, P k y (v y)‖ ^ 2)
      ≤ (1 / (M : ℝ)) ^ d * (((M : ℝ) ^ d) ^ 2 * (∫ y in cell M k, ‖v y‖) ^ 2) := by
        gcongr
    _ ≤ (1 / (M : ℝ)) ^ d * (((M : ℝ) ^ d) ^ 2 *
          ((1 / (M : ℝ)) ^ d * ∫ y in cell M k, ‖v y‖ ^ 2)) := by gcongr
    _ = ∫ y in cell M k, ‖v y‖ ^ 2 := by
        have : (1 / (M : ℝ)) ^ d * (M : ℝ) ^ d = 1 := by
          rw [← mul_pow, one_div_mul_cancel hM'.ne', one_pow]
        calc (1 / (M : ℝ)) ^ d * (((M : ℝ) ^ d) ^ 2 *
              ((1 / (M : ℝ)) ^ d * ∫ y in cell M k, ‖v y‖ ^ 2))
            = ((1 / (M : ℝ)) ^ d * (M : ℝ) ^ d) * ((1 / (M : ℝ)) ^ d * (M : ℝ) ^ d) *
                ∫ y in cell M k, ‖v y‖ ^ 2 := by ring
          _ = _ := by rw [this, one_mul, one_mul]

/-! ### Equivariance under unitary changes of frame -/

/-- The gauge-transformed connection `ω^g(x)(u) = g(x) ω(x)(u) g(x)⁻¹ - (dg(x) u) g(x)⁻¹` for
a frame change `g : ℝ^d → O(V)` (`G x` a linear isometry equivalence, `g = G` as a map into
`End V` with derivative `dg`). -/
def gaugeCoeff (ω : Connection d V) (G : (Fin d → ℝ) → (V ≃ₗᵢ[ℝ] V))
    (dg : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] (V →L[ℝ] V)) (x u : Fin d → ℝ) : V →L[ℝ] V :=
  (G x).toContinuousLinearEquiv.toContinuousLinearMap * ω x u *
      (G x).symm.toContinuousLinearEquiv.toContinuousLinearMap -
    dg x u * (G x).symm.toContinuousLinearEquiv.toContinuousLinearMap

omit [CompleteSpace V] in
/-- **Endpoint transformation of parallel transport**: if `P` is the transport of `ω` along `γ`,
then `t ↦ g(γ t) P(t) g(γ 0)⁻¹` is the transport of the gauge-transformed connection along `γ`
(for a differentiable frame change `g` with derivative `dg`). -/
theorem isTransport_gaugeTransform {ω : Connection d V} {G : (Fin d → ℝ) → (V ≃ₗᵢ[ℝ] V)}
    {dg : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] (V →L[ℝ] V)}
    (hG : ∀ x, HasFDerivAt (fun y => (G y).toContinuousLinearEquiv.toContinuousLinearMap) (dg x) x)
    {γ γ' : ℝ → Fin d → ℝ} (hγ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt γ (γ' t) (Icc 0 1) t)
    {P : ℝ → (V →L[ℝ] V)} (hP : IsTransport (fun t => ω (γ t) (γ' t)) 0 1 P) :
    IsTransport (fun t => gaugeCoeff ω G dg (γ t) (γ' t)) 0 1
      (fun t => (G (γ t)).toContinuousLinearEquiv.toContinuousLinearMap * P t *
        (G (γ 0)).symm.toContinuousLinearEquiv.toContinuousLinearMap) := by
  intro t ht
  set g : (Fin d → ℝ) → (V →L[ℝ] V) := fun y => (G y).toContinuousLinearEquiv.toContinuousLinearMap
  set g0inv := (G (γ 0)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have h1 : HasDerivWithinAt (g ∘ γ) (dg (γ t) (γ' t)) (Icc 0 1) t :=
    (hG (γ t)).comp_hasDerivWithinAt t (hγ t ht)
  have h2 := (h1.mul (hP t ht)).mul_const g0inv
  refine h2.congr_deriv ?_
  have hinv : (G (γ t)).symm.toContinuousLinearEquiv.toContinuousLinearMap * g (γ t) = 1 := by
    ext a; simp [g]
  simp only [Function.comp_apply, gaugeCoeff]
  calc (dg (γ t) (γ' t) * P t + g (γ t) * -(ω (γ t) (γ' t) * P t)) * g0inv
      = -((g (γ t) * ω (γ t) (γ' t) * 1 - dg (γ t) (γ' t) * 1) * P t * g0inv) := by noncomm_ring
    _ = _ := by rw [← hinv]; simp only [g]; noncomm_ring

/-- **Equivariance of the cell average**: if the transports transform by their endpoints,
`P'_{x←y} = g(x) P_{x←y} g(y)⁻¹`, then `Q'_h(g v)(x_k) = g(x_k) (Q_h v)(x_k)`. -/
theorem cellAverage_gaugeTransform {M : ℕ}
    {P : (Fin d → Fin M) → (Fin d → ℝ) → (V →L[ℝ] V)} {v : (Fin d → ℝ) → V}
    (G : (Fin d → ℝ) → (V ≃ₗᵢ[ℝ] V)) (k : Fin d → Fin M)
    (hint : IntegrableOn (fun y => P k y (v y)) (cell M k)) :
    cellAverage (fun k y => (G (gridPoint M k)).toContinuousLinearEquiv.toContinuousLinearMap *
        P k y * (G y).symm.toContinuousLinearEquiv.toContinuousLinearMap) (fun y => G y (v y)) k =
      G (gridPoint M k) (cellAverage P v k) := by
  have e : ∀ y, ((G (gridPoint M k)).toContinuousLinearEquiv.toContinuousLinearMap * P k y *
      (G y).symm.toContinuousLinearEquiv.toContinuousLinearMap) (G y (v y)) =
      (G (gridPoint M k)).toContinuousLinearEquiv.toContinuousLinearMap (P k y (v y)) := by
    intro y; simp
  simp only [cellAverage, e]
  rw [ContinuousLinearMap.integral_comp_comm _ hint, LinearIsometryEquiv.map_smul]
  rfl

/-- **Invariance of the quadrature pairing**: under a unitary change of frame
`X ↦ gX`, `v ↦ gv`, `P ↦ g P g⁻¹`, both the node pairing `⟪X(x_k), (Q_h v)(x_k)⟫` and the
continuum density `⟪X, v⟫` are unchanged, so `eq:covariant-quadrature` is frame-equivariant. -/
theorem inner_cellAverage_gaugeTransform {M : ℕ}
    {P : (Fin d → Fin M) → (Fin d → ℝ) → (V →L[ℝ] V)} {v X : (Fin d → ℝ) → V}
    (G : (Fin d → ℝ) → (V ≃ₗᵢ[ℝ] V)) (k : Fin d → Fin M)
    (hint : IntegrableOn (fun y => P k y (v y)) (cell M k)) :
    ⟪G (gridPoint M k) (X (gridPoint M k)),
        cellAverage (fun k y => (G (gridPoint M k)).toContinuousLinearEquiv.toContinuousLinearMap *
          P k y * (G y).symm.toContinuousLinearEquiv.toContinuousLinearMap)
          (fun y => G y (v y)) k⟫_ℝ = ⟪X (gridPoint M k), cellAverage P v k⟫_ℝ ∧
      ∀ y, ⟪G y (X y), G y (v y)⟫_ℝ = ⟪X y, v y⟫_ℝ := by
  refine ⟨?_, fun y => LinearIsometryEquiv.inner_map_map _ _ _⟩
  rw [cellAverage_gaugeTransform G k hint, LinearIsometryEquiv.inner_map_map]

/-! ### The straight-segment path family -/

variable [Nontrivial V]

/-- The straight path `γ_{x,y}(t) = y + t (x - y)` from `y` to `x`. -/
def straightPath (x y : Fin d → ℝ) (t : ℝ) : Fin d → ℝ := y + t • (x - y)

open Classical in
/-- The parallel transport along the straight path from `y` to `x` (a chosen transport of the
path coefficient `t ↦ ω(y + t(x - y))(x - y)` with `P(0) = 1`; it exists and is unique for
continuous bounded `ω`, see `exists_straightTransport`, `transport_unique`). -/
def straightTransport (ω : Connection d V) (x y : Fin d → ℝ) : ℝ → (V →L[ℝ] V) :=
  if h : ∃ U : ℝ → (V →L[ℝ] V), U 0 = 1 ∧
      IsTransport (fun t => ω (straightPath x y t) (x - y)) 0 1 U then h.choose
  else fun _ => 1

theorem straightPath_mem {x y : Fin d → ℝ} (hx : x ∈ Icc (0 : Fin d → ℝ) 1)
    (hy : y ∈ Icc (0 : Fin d → ℝ) 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    straightPath x y t ∈ Icc (0 : Fin d → ℝ) 1 :=
  (convex_Icc (0 : Fin d → ℝ) 1).add_smul_sub_mem hy hx ht

theorem hasDerivWithinAt_straightPath (x y : Fin d → ℝ) (t : ℝ) :
    HasDerivWithinAt (straightPath x y) (x - y) (Icc 0 1) t := by
  have := ((hasDerivAt_id t).smul_const (x - y)).const_add y
  rw [one_smul] at this
  exact this.hasDerivWithinAt

/-- Existence of the straight transports for a continuous bounded connection on the cube. -/
theorem exists_straightTransport {ω : Connection d V} {K : ℝ}
    (hωc : ContinuousOn ω (Icc 0 1)) (hωK : ∀ z ∈ Icc (0 : Fin d → ℝ) 1, ‖ω z‖ ≤ K)
    {x y : Fin d → ℝ} (hx : x ∈ Icc (0 : Fin d → ℝ) 1) (hy : y ∈ Icc (0 : Fin d → ℝ) 1) :
    straightTransport ω x y 0 = 1 ∧
      IsTransport (fun t => ω (straightPath x y t) (x - y)) 0 1 (straightTransport ω x y) := by
  have hex : ∃ U : ℝ → (V →L[ℝ] V), U 0 = 1 ∧
      IsTransport (fun t => ω (straightPath x y t) (x - y)) 0 1 U := by
    have hpc : ContinuousOn (straightPath x y) (Icc 0 1) := by
      unfold straightPath; fun_prop
    have hc : ContinuousOn (fun t => ω (straightPath x y t) (x - y)) (Icc 0 1) :=
      (hωc.comp hpc fun t ht => straightPath_mem hx hy ht).clm_apply continuousOn_const
    exact exists_transport_of_le zero_le_one hc
      (fun t ht => (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hωK _ (straightPath_mem hx hy ht)) (norm_nonneg _))) 1
  rw [straightTransport, dite_eq_left hex]
  exact hex.choose_spec

/-- The straight transports are isometries. -/
theorem norm_straightTransport_apply {ω : Connection d V} (hω : IsMetric ω) {K : ℝ}
    (hωc : ContinuousOn ω (Icc 0 1)) (hωK : ∀ z ∈ Icc (0 : Fin d → ℝ) 1, ‖ω z‖ ≤ K)
    {x y : Fin d → ℝ} (hx : x ∈ Icc (0 : Fin d → ℝ) 1) (hy : y ∈ Icc (0 : Fin d → ℝ) 1) (a : V) :
    ‖straightTransport ω x y 1 a‖ = ‖a‖ :=
  let h := exists_straightTransport hωc hωK hx hy
  norm_transport_apply h.2 h.1 (skew_pathCoeff hω _ _) a ⟨zero_le_one, le_rfl⟩

/-- **Lipschitz dependence of the straight transports on the initial point** (Grönwall comparison
of the path coefficients): for `y, y'` in the cube and `‖x - y‖, ‖x - y'‖ ≤ 1`,
`‖P_{x←y} - P_{x←y'}‖ ≤ (L + K) e^{2K} ‖y - y'‖`. -/
theorem norm_straightTransport_sub_le {ω : Connection d V} {K L : ℝ≥0}
    (hωK : ∀ z ∈ Icc (0 : Fin d → ℝ) 1, ‖ω z‖ ≤ K) (hωL : LipschitzOnWith L ω (Icc 0 1))
    {x y y₂ : Fin d → ℝ} (hx : x ∈ Icc (0 : Fin d → ℝ) 1) (hy : y ∈ Icc (0 : Fin d → ℝ) 1)
    (hy₂ : y₂ ∈ Icc (0 : Fin d → ℝ) 1) (hxy : ‖x - y‖ ≤ 1) (hxy₂ : ‖x - y₂‖ ≤ 1) :
    ‖straightTransport ω x y 1 - straightTransport ω x y₂ 1‖ ≤
      ((L : ℝ) + K) * Real.exp (2 * K) * ‖y - y₂‖ := by
  have hωc : ContinuousOn ω (Icc 0 1) := hωL.continuousOn
  obtain ⟨h0, hT⟩ := exists_straightTransport hωc hωK hx hy
  obtain ⟨h0₂, hT₂⟩ := exists_straightTransport hωc hωK hx hy₂
  have hcoef : ∀ z w : Fin d → ℝ, z ∈ Icc (0 : Fin d → ℝ) 1 → ‖w‖ ≤ 1 → ‖ω z w‖ ≤ K := by
    intro z w hz hw
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    calc ‖ω z‖ * ‖w‖ ≤ K * 1 := mul_le_mul (hωK z hz) hw (norm_nonneg _) K.coe_nonneg
      _ = K := mul_one _
  have hδ : ∀ t ∈ Icc (0 : ℝ) 1, ‖ω (straightPath x y t) (x - y) -
      ω (straightPath x y₂ t) (x - y₂)‖ ≤ ((L : ℝ) + K) * ‖y - y₂‖ := by
    intro t ht
    have hp := straightPath_mem hx hy ht
    have hp₂ := straightPath_mem hx hy₂ ht
    have hpp : ‖straightPath x y t - straightPath x y₂ t‖ ≤ ‖y - y₂‖ := by
      have e : straightPath x y t - straightPath x y₂ t = (1 - t) • (y - y₂) := by
        simp only [straightPath, smul_sub, sub_smul, one_smul]; abel
      rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
      exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [ht.1])
    have e2 : ω (straightPath x y t) (x - y) - ω (straightPath x y₂ t) (x - y₂) =
        (ω (straightPath x y t) - ω (straightPath x y₂ t)) (x - y) +
          ω (straightPath x y₂ t) (y₂ - y) := by
      simp only [sub_apply, map_sub]; abel
    rw [e2]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(ω (straightPath x y t) - ω (straightPath x y₂ t)) (x - y)‖ ≤ L * ‖y - y₂‖ := by
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      have hl := hωL.norm_sub_le hp hp₂
      calc ‖ω (straightPath x y t) - ω (straightPath x y₂ t)‖ * ‖x - y‖
          ≤ (L * ‖y - y₂‖) * 1 :=
            mul_le_mul (hl.trans (mul_le_mul_of_nonneg_left hpp L.coe_nonneg)) hxy
              (norm_nonneg _) (by positivity)
        _ = L * ‖y - y₂‖ := mul_one _
    have h2 : ‖ω (straightPath x y₂ t) (y₂ - y)‖ ≤ K * ‖y - y₂‖ := by
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      rw [norm_sub_rev y₂ y]
      exact mul_le_mul_of_nonneg_right (hωK _ hp₂) (norm_nonneg _)
    linarith
  have hcmp := norm_transport_sub_transport_le (K := K)
    (fun t ht => hcoef _ _ (straightPath_mem hx hy ht) hxy)
    (fun t ht => hcoef _ _ (straightPath_mem hx hy₂ ht) hxy₂) hδ hT hT₂ (by rw [h0, h0₂])
    1 ⟨zero_le_one, le_rfl⟩
  simp only [h0, norm_one, one_mul, sub_zero, mul_one] at hcmp
  refine hcmp.trans ((WilsonTransport.gronwallBound_zero_le K.coe_nonneg (by positivity)
    zero_le_one).trans (le_of_eq ?_))
  simp only [mul_one]
  rw [two_mul, Real.exp_add]
  ring

/-- The straight transport field `y ↦ P_{x_k←y}` is Lipschitz, hence measurable, on each cell. -/
theorem aestronglyMeasurable_straightTransport {M : ℕ} (hM : 0 < M) {ω : Connection d V}
    {K L : ℝ≥0} (hωK : ∀ z ∈ Icc (0 : Fin d → ℝ) 1, ‖ω z‖ ≤ K)
    (hωL : LipschitzOnWith L ω (Icc 0 1)) (k : Fin d → Fin M) :
    AEStronglyMeasurable (fun y => straightTransport ω (gridPoint M k) y 1)
      (volume.restrict (cell M k)) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hlen1 : ∀ y ∈ cell M k, ‖gridPoint M k - y‖ ≤ 1 := fun y hy => by
    rw [norm_sub_rev, ← dist_eq_norm]
    exact (dist_lt_of_mem_cell hM k hy).le.trans (by rw [div_le_one hM']; exact_mod_cast hM)
  have hlip : LipschitzOnWith (((L : ℝ) + K) * Real.exp (2 * K)).toNNReal
      (fun y => straightTransport ω (gridPoint M k) y 1) (cell M k) := by
    refine LipschitzOnWith.of_dist_le_mul fun y hy y₂ hy₂ => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
    exact norm_straightTransport_sub_le hωK hωL (gridPoint_mem_Icc hM k)
      (cell_subset_Icc hM k hy) (cell_subset_Icc hM k hy₂) (hlen1 y hy) (hlen1 y₂ hy₂)
  exact hlip.continuousOn.aestronglyMeasurable (measurableSet_cell M k)

/-- **`lem:covariant-quadrature` for the straight path family**: for a metric connection that is
bounded (`‖ω‖ ≤ K`) and Lipschitz on the cube, a section `X` differentiable on the cube with
`‖𝔻X‖ ≤ B` there, and an integrable test `v`, the covariant cell average along straight
segments (length `‖x_k - y‖ < h = 1/M`) satisfies
`|h^d Σ_k ⟪X(x_k), (Q_h v)(x_k)⟫ - ∫_{[0,1]^d} ⟪X, v⟫| ≤ h B ‖v‖_{L¹}`. -/
theorem abs_covariant_quadrature_straight_sub_le {M : ℕ} (hM : 0 < M) {ω : Connection d V}
    (hω : IsMetric ω) {K L : ℝ≥0} (hωK : ∀ z ∈ Icc (0 : Fin d → ℝ) 1, ‖ω z‖ ≤ K)
    (hωL : LipschitzOnWith L ω (Icc 0 1)) {X : (Fin d → ℝ) → V}
    (hX : ∀ z ∈ Icc (0 : Fin d → ℝ) 1, DifferentiableAt ℝ X z) {B : ℝ}
    (hB : ∀ z ∈ Icc (0 : Fin d → ℝ) 1, ‖covDeriv ω X z‖ ≤ B)
    {v : (Fin d → ℝ) → V} (hv : IntegrableOn v (Icc (0 : Fin d → ℝ) 1)) :
    |(1 / (M : ℝ)) ^ d * ∑ k : Fin d → Fin M, ⟪X (gridPoint M k),
        cellAverage (fun k y => straightTransport ω (gridPoint M k) y 1) v k⟫_ℝ -
        ∫ y in Icc (0 : Fin d → ℝ) 1, ⟪X y, v y⟫_ℝ| ≤
      (1 / (M : ℝ)) * B * ∫ y in Icc (0 : Fin d → ℝ) 1, ‖v y‖ := by
  have hωc : ContinuousOn ω (Icc 0 1) := hωL.continuousOn
  have hxk := gridPoint_mem_Icc (d := d) hM
  have hyk : ∀ k : Fin d → Fin M, ∀ y ∈ cell M k, y ∈ Icc (0 : Fin d → ℝ) 1 := fun k y hy =>
    cell_subset_Icc hM k hy
  have hlen : ∀ k : Fin d → Fin M, ∀ y ∈ cell M k, ‖gridPoint M k - y‖ ≤ 1 / M :=
    fun k y hy => by
    rw [norm_sub_rev, ← dist_eq_norm]; exact (dist_lt_of_mem_cell hM k hy).le
  have hXc : ContinuousOn X (Icc 0 1) := fun z hz => (hX z hz).continuousAt.continuousWithinAt
  exact abs_covariant_quadrature_sub_le hM hω hXc hv
    (γ := fun k y => straightPath (gridPoint M k) y) (γ' := fun k y _ => gridPoint M k - y)
    (P := fun k y => straightTransport ω (gridPoint M k) y)
    (fun k y _ => by simp [straightPath]) (fun k y _ => by simp [straightPath])
    (fun k y _ t _ => hasDerivWithinAt_straightPath _ _ t) (fun k y hy _ _ => hlen k y hy)
    (fun k y hy t ht => hX _ (straightPath_mem (hxk k) (hyk k y hy) ht))
    (fun k y hy t ht => hB _ (straightPath_mem (hxk k) (hyk k y hy) ht))
    (fun k y hy => (exists_straightTransport hωc hωK (hxk k) (hyk k y hy)).2)
    (fun k y hy => (exists_straightTransport hωc hωK (hxk k) (hyk k y hy)).1)
    (fun k => aestronglyMeasurable_straightTransport hM hωK hωL k)

/-- The norm estimates of `lem:covariant-quadrature` for the straight family:
`‖Q_h v‖_{∞,h} ≤ ‖v‖_∞` and `‖Q_h v‖_{2,h} ≤ ‖v‖_2`. -/
theorem straight_cellAverage_norm_bounds {M : ℕ} (hM : 0 < M) {ω : Connection d V}
    (hω : IsMetric ω) {K L : ℝ≥0} (hωK : ∀ z ∈ Icc (0 : Fin d → ℝ) 1, ‖ω z‖ ≤ K)
    (hωL : LipschitzOnWith L ω (Icc 0 1)) {v : (Fin d → ℝ) → V}
    (hv : IntegrableOn v (Icc (0 : Fin d → ℝ) 1)) :
    (∀ m : ℝ, (∀ y ∈ Icc (0 : Fin d → ℝ) 1, ‖v y‖ ≤ m) → ∀ k : Fin d → Fin M,
      ‖cellAverage (fun k y => straightTransport ω (gridPoint M k) y 1) v k‖ ≤ m) ∧
    (IntegrableOn (fun y => ‖v y‖ ^ 2) (Icc (0 : Fin d → ℝ) 1) →
      (1 / (M : ℝ)) ^ d * ∑ k : Fin d → Fin M,
        ‖cellAverage (fun k y => straightTransport ω (gridPoint M k) y 1) v k‖ ^ 2 ≤
        ∫ y in Icc (0 : Fin d → ℝ) 1, ‖v y‖ ^ 2) := by
  have hωc : ContinuousOn ω (Icc 0 1) := hωL.continuousOn
  have hxk := gridPoint_mem_Icc (d := d) hM
  have hyk : ∀ k : Fin d → Fin M, ∀ y ∈ cell M k, y ∈ Icc (0 : Fin d → ℝ) 1 := fun k y hy =>
    cell_subset_Icc hM k hy
  have hiso : ∀ k : Fin d → Fin M, ∀ y ∈ cell M k, ∀ a : V,
      ‖straightTransport ω (gridPoint M k) y 1 a‖ = ‖a‖ := fun k y hy a =>
    norm_straightTransport_apply hω hωc hωK (hxk k) (hyk k y hy) a
  exact ⟨fun m hm k => norm_cellAverage_le hM k (hiso k) fun y hy => hm y (hyk k y hy),
    fun hv2 => cellAverage_sq_sum_le hM hv hv2
      (fun k => aestronglyMeasurable_straightTransport hM hωK hωL k) hiso⟩

/-- Non-vacuity: the flat connection `ω = 0` on the trivial line bundle `V = ℝ` is metric,
bounded by `0` and `0`-Lipschitz, so `abs_covariant_quadrature_straight_sub_le` applies
(with `P_{x←y} = 1` it reduces to the scalar first-order quadrature estimate). -/
example : IsMetric (0 : Connection 4 ℝ) ∧ (∀ z ∈ Icc (0 : Fin 4 → ℝ) 1,
    ‖(0 : Connection 4 ℝ) z‖ ≤ ((0 : ℝ≥0) : ℝ)) ∧
    LipschitzOnWith 0 (0 : Connection 4 ℝ) (Icc 0 1) :=
  ⟨fun _ _ _ _ => by simp, fun _ _ => by
    rw [NNReal.coe_zero]; exact (norm_zero (E := (Fin 4 → ℝ) →L[ℝ] (ℝ →L[ℝ] ℝ))).le,
    (LipschitzWith.const' (0 : (Fin 4 → ℝ) →L[ℝ] (ℝ →L[ℝ] ℝ))).lipschitzOnWith⟩

end RenewalGeometry.CovariantQuadrature
