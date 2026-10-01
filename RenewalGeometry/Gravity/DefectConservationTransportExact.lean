/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Covariant conservation under a strong connection limit
  (`lem:defect-conservation-transport`, Einstein–SM action closure)

Setting: a compact chart `K ⊆ ℝ^n` (`Fin n → ℝ`), metric component fields
`g_h, g : ℝ^n → Mat_n(ℝ)` of class `C¹`, a `C¹` vector field `X`, and
covariant tensor densities `𝖳_{h,μν}`, `𝖳_{μν}` given as finite signed Radon
measures on `K`, i.e. (Riesz identification) continuous linear functionals on
`C(K, ℝ)`; the dual norm is the total variation `|𝖳|(K)` and weak-* convergence
is convergence against every continuous function on `K`.

* `symCovDeriv` / `christoffel` — the coordinate formula
  `∇^{(μ}X^{ν)} = ½(g^{μα}∇_αX^ν + g^{να}∇_αX^μ)`,
  `∇_αX^ν = ∂_αX^ν + Γ^ν_{αβ}X^β`,
  `Γ^ν_{αβ} = ½ g^{νλ}(∂_αg_{λβ} + ∂_βg_{λα} - ∂_λg_{αβ})`, written over any
  commutative `ℝ`-algebra; `covSym g X` is this formula in the ring `C(K, ℝ)`
  (inverse metric = inverse matrix over `C(K, ℝ)`), and `covSym_apply` shows that
  it evaluates at every point of `K` to the same formula with `(g x)⁻¹` and the
  real partial derivatives.
* `tendsto_covSym` — `C¹` convergence `g_h → g` on `K` with `g` nondegenerate on
  `K` gives `∇_{g_h}^{(μ}X^{ν)} → ∇_g^{(μ}X^{ν)}` uniformly on `K` (the key step
  of the paper's proof: inversion is continuous at the unit `det g` of the
  Banach algebra `C(K, ℝ)`).
* `defect_conservation_transport` — if `𝖳_h` are uniformly bounded and
  converge weakly-* to `𝖳`, and `∫ ∇_{g_h}^{(μ}X^{ν)} d𝖳_{h,μν} → 0`
  (`eq:defect-conservation-tested`), then `∫ ∇_g^{(μ}X^{ν)} d𝖳_{μν} = 0`.
* `defect_conservation_split` — if `𝖳 = T(z) dV_g + 𝔖` and the regular part has
  the identity, so does `𝔖`.

Renderings disclosed: the measures are encoded as elements of `C(K,ℝ)^*`
(Riesz–Markov identification of finite signed Radon measures on the compact
chart); the metrics are `C¹` maps defined on `ℝ^n` (only their values and first
partials on `K` enter); the limit metric is nondegenerate on `K` (part of being
a metric; it is what the paper's uniform inverse bounds give in the limit) — the
uniform inverse bounds on `g_h` themselves are not needed; symmetry of `𝖳` and
compact support of `X` are not needed (the identity is proved per `C¹` field).
-/

namespace RenewalGeometry

namespace DefectConservationTransport

open Filter Topology

section Algebra

variable {n : ℕ} {R : Type*} [CommRing R] [Algebra ℝ R]

/-- Christoffel symbols `Γ^ν_{αβ} = ½ g^{νλ}(∂_α g_{λβ} + ∂_β g_{λα} - ∂_λ g_{αβ})`
from an inverse metric `Ginv` and first partials `D k i j = ∂_k g_{ij}`
(`lem:defect-conservation-transport`). -/
noncomputable def christoffel (Ginv : Matrix (Fin n) (Fin n) R) (D : Fin n → Matrix (Fin n) (Fin n) R)
    (ν α β : Fin n) : R :=
  (1 / 2 : ℝ) • ∑ l, Ginv ν l * (D α l β + D β l α - D l α β)

/-- Symmetrized contravariant covariant derivative
`∇^{(μ}X^{ν)} = ½(g^{μα}(∂_αX^ν + Γ^ν_{αβ}X^β) + g^{να}(∂_αX^μ + Γ^μ_{αβ}X^β))`,
with `dX α ν = ∂_α X^ν` (`lem:defect-conservation-transport`). -/
noncomputable def symCovDeriv (Ginv : Matrix (Fin n) (Fin n) R) (D : Fin n → Matrix (Fin n) (Fin n) R)
    (X : Fin n → R) (dX : Fin n → Fin n → R) (μ ν : Fin n) : R :=
  (1 / 2 : ℝ) • ∑ a, (Ginv μ a * (dX a ν + ∑ b, christoffel Ginv D ν a b * X b) +
    Ginv ν a * (dX a μ + ∑ b, christoffel Ginv D μ a b * X b))

theorem map_christoffel {S : Type*} [CommRing S] [Algebra ℝ S] (φ : R →ₐ[ℝ] S)
    (Ginv : Matrix (Fin n) (Fin n) R) (D : Fin n → Matrix (Fin n) (Fin n) R) (ν α β : Fin n) :
    φ (christoffel Ginv D ν α β) =
      christoffel (Ginv.map φ) (fun k => (D k).map φ) ν α β := by
  simp [christoffel, map_sum, map_mul, map_sub, map_add, map_smul]

theorem map_symCovDeriv {S : Type*} [CommRing S] [Algebra ℝ S] (φ : R →ₐ[ℝ] S)
    (Ginv : Matrix (Fin n) (Fin n) R) (D : Fin n → Matrix (Fin n) (Fin n) R)
    (X : Fin n → R) (dX : Fin n → Fin n → R) (μ ν : Fin n) :
    φ (symCovDeriv Ginv D X dX μ ν) =
      symCovDeriv (Ginv.map φ) (fun k => (D k).map φ) (fun i => φ (X i))
        (fun a i => φ (dX a i)) μ ν := by
  simp only [symCovDeriv, map_smul, map_sum, map_add, map_mul, map_christoffel]
  rfl

variable [TopologicalSpace R] [IsTopologicalRing R] [ContinuousConstSMul ℝ R]

/-- Entrywise convergence of inverse metrics and first partials gives convergence of
`∇^{(μ}X^{ν)}`. -/
theorem tendsto_symCovDeriv {ι : Type*} {l : Filter ι}
    {Gh : ι → Matrix (Fin n) (Fin n) R} {G : Matrix (Fin n) (Fin n) R}
    {Dh : ι → Fin n → Matrix (Fin n) (Fin n) R} {D : Fin n → Matrix (Fin n) (Fin n) R}
    (hG : ∀ i j, Tendsto (fun h => Gh h i j) l (𝓝 (G i j)))
    (hD : ∀ k i j, Tendsto (fun h => Dh h k i j) l (𝓝 (D k i j)))
    (X : Fin n → R) (dX : Fin n → Fin n → R) (μ ν : Fin n) :
    Tendsto (fun h => symCovDeriv (Gh h) (Dh h) X dX μ ν) l
      (𝓝 (symCovDeriv G D X dX μ ν)) := by
  have hΓ : ∀ ν a b, Tendsto (fun h => christoffel (Gh h) (Dh h) ν a b) l
      (𝓝 (christoffel G D ν a b)) := by
    intro ν a b
    unfold christoffel
    refine Tendsto.const_smul (tendsto_finsetSum _ fun c _ => ?_) _
    exact (hG _ _).mul (((hD _ _ _).add (hD _ _ _)).sub (hD _ _ _))
  unfold symCovDeriv
  refine Tendsto.const_smul (tendsto_finsetSum _ fun a _ => ?_) _
  exact ((hG _ _).mul (tendsto_const_nhds.add (tendsto_finsetSum _ fun b _ =>
    (hΓ _ _ _).mul tendsto_const_nhds))).add ((hG _ _).mul (tendsto_const_nhds.add
      (tendsto_finsetSum _ fun b _ => (hΓ _ _ _).mul tendsto_const_nhds)))

end Algebra

section InverseLimit

variable {n : ℕ} {R : Type*} [NormedCommRing R] [CompleteSpace R]

/-- In a complete normed commutative ring, matrix inversion is continuous at a matrix
with unit determinant (entrywise form). -/
theorem tendsto_inv_entry {ι : Type*} {l : Filter ι}
    {Gh : ι → Matrix (Fin n) (Fin n) R} {G : Matrix (Fin n) (Fin n) R}
    (hG : ∀ i j, Tendsto (fun h => Gh h i j) l (𝓝 (G i j))) (hdet : IsUnit G.det)
    (i j : Fin n) : Tendsto (fun h => (Gh h)⁻¹ i j) l (𝓝 (G⁻¹ i j)) := by
  have hM : Tendsto Gh l (𝓝 G) :=
    tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun b => hG a b
  have hdetT : Tendsto (fun h => (Gh h).det) l (𝓝 G.det) :=
    ((continuous_id.matrix_det).tendsto G).comp hM
  have hadjT : Tendsto (fun h => (Gh h).adjugate) l (𝓝 G.adjugate) :=
    ((continuous_id.matrix_adjugate).tendsto G).comp hM
  have hinvT : Tendsto (fun h => Ring.inverse (Gh h).det) l (𝓝 (Ring.inverse G.det)) := by
    have := NormedRing.inverse_continuousAt hdet.unit
    rw [IsUnit.unit_spec] at this
    exact this.tendsto.comp hdetT
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
  exact hinvT.mul ((continuous_apply j).tendsto _ |>.comp
    ((continuous_apply i).tendsto _ |>.comp hadjT))

end InverseLimit

section Chart

variable {n : ℕ} {K : Set (Fin n → ℝ)}

/-- Restriction of a function on `ℝ^n` to the chart `K` as a continuous map (zero if the
restriction is not continuous; only used for continuous functions). -/
noncomputable def restr (K : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : C(K, ℝ) := by
  classical
  exact if h : Continuous (fun x : K => f x) then ⟨fun x => f x, h⟩ else 0

theorem restr_apply {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) (x : K) :
    restr K f x = f x := by
  have hc : Continuous (fun x : K => f x) := hf.comp continuous_subtype_val
  simp [restr, hc]

/-- Coordinate partial derivative `∂_k f`. -/
noncomputable def pd (k : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single k 1)

theorem continuous_pd {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (k : Fin n) :
    Continuous (pd k f) :=
  (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- The metric components restricted to the chart, as a matrix over `C(K, ℝ)`. -/
noncomputable def metricMat (K : Set (Fin n → ℝ)) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) C(K, ℝ) :=
  fun i j => restr K fun x => g x i j

/-- The first partials `∂_k g_{ij}` restricted to the chart. -/
noncomputable def metricDer (K : Set (Fin n → ℝ)) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) :
    Fin n → Matrix (Fin n) (Fin n) C(K, ℝ) :=
  fun k i j => restr K (pd k fun x => g x i j)

/-- `∇_g^{(μ}X^{ν)}` on the chart `K`, as an element of `C(K, ℝ)`
(`lem:defect-conservation-transport`). -/
noncomputable def covSym (K : Set (Fin n → ℝ)) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (X : (Fin n → ℝ) → Fin n → ℝ) (μ ν : Fin n) : C(K, ℝ) :=
  symCovDeriv (metricMat K g)⁻¹ (metricDer K g) (fun i => restr K fun x => X x i)
    (fun a i => restr K (pd a fun x => X x i)) μ ν

theorem metricMat_map_eval {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hg : ∀ i j, Continuous fun x => g x i j) (x : K) :
    (metricMat K g).map (ContinuousMap.evalAlgHom ℝ ℝ x) = g x := by
  ext i j
  simp [metricMat, restr_apply (hg i j)]

theorem isUnit_det_metricMat {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hg : ∀ i j, Continuous fun x => g x i j) (hdet : ∀ x ∈ K, (g x).det ≠ 0) :
    IsUnit (metricMat K g).det := by
  rw [ContinuousMap.isUnit_iff_forall_ne_zero]
  intro x
  have := (ContinuousMap.evalAlgHom ℝ ℝ x).toRingHom.map_det (metricMat K g)
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ContinuousMap.evalAlgHom_apply] at this
  rw [this]
  have hm : ((ContinuousMap.evalAlgHom ℝ ℝ x : C(K, ℝ) →ₐ[ℝ] ℝ) : C(K, ℝ) →+* ℝ).mapMatrix
      (metricMat K g) = g x := by
    ext i j
    simp [metricMat, restr_apply (hg i j)]
  rw [hm]
  exact hdet x x.2

/-- Pointwise, the inverse metric over `C(K, ℝ)` is the inverse matrix `(g x)⁻¹`. -/
theorem inv_metricMat_map_eval {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hg : ∀ i j, Continuous fun x => g x i j) (hdet : ∀ x ∈ K, (g x).det ≠ 0) (x : K) :
    ((metricMat K g)⁻¹).map (ContinuousMap.evalAlgHom ℝ ℝ x) = (g x)⁻¹ := by
  have hu := isUnit_det_metricMat hg hdet
  have h1 : metricMat K g * (metricMat K g)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have h2 : (metricMat K g * (metricMat K g)⁻¹).map (ContinuousMap.evalAlgHom ℝ ℝ x) =
      (1 : Matrix (Fin n) (Fin n) C(K, ℝ)).map (ContinuousMap.evalAlgHom ℝ ℝ x) := by
    rw [h1]
  rw [Matrix.map_mul, metricMat_map_eval hg x, Matrix.map_one _ (map_zero _) (map_one _)] at h2
  exact (Matrix.inv_eq_right_inv h2).symm

/-- `covSym` is the coordinate formula for `∇_g^{(μ}X^{ν)}` at every point of `K`:
the same formula over `ℝ` with the inverse matrix `(g x)⁻¹` and the real partial
derivatives `∂_k g_{ij}(x)`, `∂_α X^ν(x)`. -/
theorem covSym_apply {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hg : ∀ i j, ContDiff ℝ 1 fun x => g x i j) (hdet : ∀ x ∈ K, (g x).det ≠ 0)
    {X : (Fin n → ℝ) → Fin n → ℝ} (hX : ∀ i, ContDiff ℝ 1 fun x => X x i)
    (μ ν : Fin n) (x : K) :
    covSym K g X μ ν x =
      symCovDeriv (g x)⁻¹ (fun k i j => pd k (fun y => g y i j) x) (fun i => X x i)
        (fun a i => pd a (fun y => X y i) x) μ ν := by
  have h := map_symCovDeriv (ContinuousMap.evalAlgHom ℝ ℝ x) (metricMat K g)⁻¹
    (metricDer K g) (fun i => restr K fun x => X x i)
    (fun a i => restr K (pd a fun x => X x i)) μ ν
  simp only [ContinuousMap.evalAlgHom_apply] at h
  rw [covSym, h, inv_metricMat_map_eval (fun i j => (hg i j).continuous) hdet x]
  congr 1
  · funext k
    ext i j
    simp [metricDer, restr_apply (continuous_pd (hg i j) k)]
  · funext i
    simp [restr_apply (hX i).continuous]
  · funext a i
    simp [restr_apply (continuous_pd (hX i) a)]

variable [CompactSpace K]

theorem tendsto_restr {F : ℕ → (Fin n → ℝ) → ℝ} {f : (Fin n → ℝ) → ℝ}
    (hF : ∀ h, Continuous (F h)) (hf : Continuous f)
    (hu : TendstoUniformlyOn F f atTop K) :
    Tendsto (fun h => restr K (F h)) atTop (𝓝 (restr K f)) := by
  rw [ContinuousMap.tendsto_iff_tendstoUniformly]
  have e1 : (fun h (x : K) => restr K (F h) x) = fun h (x : K) => F h x := by
    funext h x; exact restr_apply (hF h) x
  have e2 : (⇑(restr K f)) = fun x : K => f x := by
    funext x; exact restr_apply hf x
  rw [e1, e2]
  exact (tendstoUniformlyOn_iff_tendstoUniformly_comp_coe).1 hu

/-- `lem:defect-conservation-transport`, key step: `C¹` convergence of the metrics on the
compact chart (with nondegenerate limit) gives uniform convergence on `K` of
`∇_{g_h}^{(μ}X^{ν)}` to `∇_g^{(μ}X^{ν)}`. -/
theorem tendsto_covSym {g : ℕ → (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    {g₀ : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hg : ∀ h i j, ContDiff ℝ 1 fun x => g h x i j) (hg₀ : ∀ i j, ContDiff ℝ 1 fun x => g₀ x i j)
    (hdet : ∀ x ∈ K, (g₀ x).det ≠ 0)
    (hC0 : ∀ i j, TendstoUniformlyOn (fun h x => g h x i j) (fun x => g₀ x i j) atTop K)
    (hC1 : ∀ k i j, TendstoUniformlyOn (fun h => pd k fun x => g h x i j)
      (pd k fun x => g₀ x i j) atTop K)
    (X : (Fin n → ℝ) → Fin n → ℝ) (μ ν : Fin n) :
    Tendsto (fun h => covSym K (g h) X μ ν) atTop (𝓝 (covSym K g₀ X μ ν)) := by
  have hG : ∀ i j, Tendsto (fun h => metricMat K (g h) i j) atTop (𝓝 (metricMat K g₀ i j)) :=
    fun i j => tendsto_restr (fun h => (hg h i j).continuous) (hg₀ i j).continuous (hC0 i j)
  have hD : ∀ k i j, Tendsto (fun h => metricDer K (g h) k i j) atTop
      (𝓝 (metricDer K g₀ k i j)) :=
    fun k i j => tendsto_restr (fun h => continuous_pd (hg h i j) k)
      (continuous_pd (hg₀ i j) k) (hC1 k i j)
  have hu := isUnit_det_metricMat (fun i j => (hg₀ i j).continuous) hdet
  exact tendsto_symCovDeriv (tendsto_inv_entry hG hu) hD _ _ μ ν

/-- Uniformly bounded, weakly-* convergent functionals applied to strongly convergent
arguments converge. -/
theorem tendsto_apply_of_bounded_weakStar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} {l : Filter ι} {T : ι → E →L[ℝ] ℝ} {T₀ : E →L[ℝ] ℝ} {C : ℝ}
    (hT : ∀ i, ‖T i‖ ≤ C) (hw : ∀ φ, Tendsto (fun i => T i φ) l (𝓝 (T₀ φ)))
    {B : ι → E} {B₀ : E} (hB : Tendsto B l (𝓝 B₀)) :
    Tendsto (fun i => T i (B i)) l (𝓝 (T₀ B₀)) := by
  have h1 : Tendsto (fun i => T i (B i - B₀)) l (𝓝 0) := by
    refine squeeze_zero_norm (fun i => ((T i).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hT i) (norm_nonneg _))) ?_
    have : Tendsto (fun i => ‖B i - B₀‖) l (𝓝 0) := by
      simpa using (hB.sub_const B₀).norm
    simpa using this.const_mul C
  have h2 := h1.add (hw B₀)
  simp only [map_sub, sub_add_cancel, zero_add] at h2
  exact h2

/-- `lem:defect-conservation-transport`: let `g_h → g` in `C¹` on the compact chart `K`
(limit nondegenerate on `K`), let the tensor densities `𝖳_{h,μν}` be uniformly bounded
Radon measures (functionals on `C(K)` of norm `≤ C`) converging weakly-* to `𝖳_{μν}`, and
let `X` be a `C¹` vector field with
`∫ ∇_{g_h}^{(μ}X^{ν)} d𝖳_{h,μν} → 0` (`eq:defect-conservation-tested`).
Then `∫ ∇_g^{(μ}X^{ν)} d𝖳_{μν} = 0`. -/
theorem defect_conservation_transport {g : ℕ → (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    {g₀ : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hg : ∀ h i j, ContDiff ℝ 1 fun x => g h x i j) (hg₀ : ∀ i j, ContDiff ℝ 1 fun x => g₀ x i j)
    (hdet : ∀ x ∈ K, (g₀ x).det ≠ 0)
    (hC0 : ∀ i j, TendstoUniformlyOn (fun h x => g h x i j) (fun x => g₀ x i j) atTop K)
    (hC1 : ∀ k i j, TendstoUniformlyOn (fun h => pd k fun x => g h x i j)
      (pd k fun x => g₀ x i j) atTop K)
    (T : ℕ → Fin n → Fin n → C(K, ℝ) →L[ℝ] ℝ) (T₀ : Fin n → Fin n → C(K, ℝ) →L[ℝ] ℝ)
    {C : ℝ} (hT : ∀ h μ ν, ‖T h μ ν‖ ≤ C)
    (hw : ∀ μ ν φ, Tendsto (fun h => T h μ ν φ) atTop (𝓝 (T₀ μ ν φ)))
    (X : (Fin n → ℝ) → Fin n → ℝ)
    (htest : Tendsto (fun h => ∑ μ, ∑ ν, T h μ ν (covSym K (g h) X μ ν)) atTop (𝓝 0)) :
    ∑ μ, ∑ ν, T₀ μ ν (covSym K g₀ X μ ν) = 0 := by
  have hlim : Tendsto (fun h => ∑ μ, ∑ ν, T h μ ν (covSym K (g h) X μ ν)) atTop
      (𝓝 (∑ μ, ∑ ν, T₀ μ ν (covSym K g₀ X μ ν))) :=
    tendsto_finsetSum _ fun μ _ => tendsto_finsetSum _ fun ν _ =>
      tendsto_apply_of_bounded_weakStar (fun h => hT h μ ν) (hw μ ν)
        (tendsto_covSym hg hg₀ hdet hC0 hC1 X μ ν)
  exact tendsto_nhds_unique hlim htest

omit [CompactSpace K] in
/-- `lem:defect-conservation-transport`, splitting clause: if `𝖳 = T(z) dV_g + 𝔖` and
the regular part satisfies the identity, then so does `𝔖`. -/
theorem defect_conservation_split (g₀ : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (X : (Fin n → ℝ) → Fin n → ℝ) (T₀ Treg S : Fin n → Fin n → C(K, ℝ) →L[ℝ] ℝ)
    (hsplit : ∀ μ ν, T₀ μ ν = Treg μ ν + S μ ν)
    (hT : ∑ μ, ∑ ν, T₀ μ ν (covSym K g₀ X μ ν) = 0)
    (hreg : ∑ μ, ∑ ν, Treg μ ν (covSym K g₀ X μ ν) = 0) :
    ∑ μ, ∑ ν, S μ ν (covSym K g₀ X μ ν) = 0 := by
  simp only [hsplit, FunLike.coe_add, Pi.add_apply, Finset.sum_add_distrib, hreg,
    zero_add] at hT
  exact hT

end Chart

end DefectConservationTransport

end RenewalGeometry
