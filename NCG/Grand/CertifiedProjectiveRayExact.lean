/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperationalConeExact
import NCG.Topology.Brouwer.FixedPoint

/-!
# Operational projective map, residual certification, and coordinate covariance

Machinery for `thm:SM-certified-projective-ray`.  On the compact convex base
`ℬ = {x ∈ 𝒦 : ν(x) = 1}` of the operational cone, a leading map
`ℱ(x) = b + 𝒬(x,x) - K₁ x` (RG.13) mapping the base into the pointed cone normalizes to the
projective map `𝒯(x) = ℱ(x)/ν(ℱ(x))` (RG.14, `rayMap`).

* (RG.15) a fixed point `a ∈ ℬ` of `𝒯` satisfies `ℱ(a) = β a` with `β = ν(ℱ(a)) > 0`
  (`fixed_eigen`); unconditional existence for continuous `ℱ` follows from the bundled cubical
  Sperner proof of Brouwer's theorem (`exists_fixed_of_continuous`), while the `q`-contractive
  branch also has a direct iterative proof (`exists_fixed_of_contractive`);
* uniqueness on the contractive branch (`fixed_unique_of_contractive`);
* (RG.16) the a-posteriori residual bound `‖â - a‖ ≤ ‖â - 𝒯(â)‖ / (1 - q)`
  (`residual_bound`);
* (RG.17) the certified scalar Read: `|ℓ(â) - ℓ(a)| ≤ ‖ℓ|_{ker ν}‖ ‖â - 𝒯(â)‖ / (1 - q)`
  (`read_bound`);
* (RG.18) coordinate covariance: an invertible transport conjugating the packet carries fixed
  points and scalar Reads exactly (`rayMap_equivariant`, `read_transport`).
-/

open Matrix ContinuousLinearMap
open scoped Topology

namespace NCG
namespace ProjectiveRay

open NCG.OperationalCone

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F]
  {ι : Type*} [Fintype ι] {n : ι → Type*} [∀ j, Fintype (n j)]

variable (R : E →ₗ[ℝ] F) (L : ∀ j, E →ₗ[ℝ] Matrix (n j) (n j) ℝ)
  (W : ∀ j, Matrix (n j) (n j) ℝ)

/-- (RG.14) the normalized projective map `𝒯(x) = ℱ(x)/ν(ℱ(x))`. -/
noncomputable def rayMap (Φ : E → E) (x : E) : E := (calib L W (Φ x))⁻¹ • Φ x

section Basic

variable (hW : ∀ j, (W j).PosDef) (Φ : E → E)
  (hΦ : ∀ x ∈ base R L W, Φ x ∈ cone R L)
  (hΦ0 : ∀ x ∈ base R L W, ¬ ∀ j, L j (Φ x) = 0)

include hW hΦ hΦ0

omit [FiniteDimensional ℝ E] in
theorem calib_pos_of_mem {x : E} (hx : x ∈ base R L W) : 0 < calib L W (Φ x) :=
  calib_pos R L W hW (hΦ x hx) (hΦ0 x hx)

omit [FiniteDimensional ℝ E] in
/-- The projective map preserves the base. -/
theorem rayMap_mem_base {x : E} (hx : x ∈ base R L W) : rayMap L W Φ x ∈ base R L W := by
  have hc := calib_pos_of_mem R L W hW Φ hΦ hΦ0 hx
  refine ⟨cone_smul R L (hΦ x hx) (inv_nonneg.mpr hc.le), ?_⟩
  rw [rayMap, calib_smul, inv_mul_cancel₀ hc.ne']

omit [FiniteDimensional ℝ E] in
/-- **(RG.15)**: a fixed point of the projective map is an eigenray of the leading map with
positive eigenvalue `β = ν(ℱ(a))`. -/
theorem fixed_eigen {a : E} (ha : a ∈ base R L W) (hfix : rayMap L W Φ a = a) :
    Φ a = calib L W (Φ a) • a ∧ 0 < calib L W (Φ a) := by
  have hc := calib_pos_of_mem R L W hW Φ hΦ hΦ0 ha
  refine ⟨?_, hc⟩
  have h := congrArg (fun v => calib L W (Φ a) • v) hfix
  simp only [rayMap, smul_smul, mul_inv_cancel₀ hc.ne', one_smul] at h
  exact h

end Basic

/-! ### The unconditional Brouwer branch -/

section Brouwer

variable (hW : ∀ j, (W j).PosDef) (Φ : E → E)
  (hΦ : ∀ x ∈ base R L W, Φ x ∈ cone R L)
  (hΦ0 : ∀ x ∈ base R L W, ¬ ∀ j, L j (Φ x) = 0)

include hW hΦ hΦ0

/-- Continuity of normalization by the strictly positive calibration on the physical base. -/
theorem continuousOn_rayMap (hΦc : ContinuousOn Φ (base R L W)) :
    ContinuousOn (rayMap L W Φ) (base R L W) := by
  have hcal : ContinuousOn (fun x => calib L W (Φ x)) (base R L W) :=
    (continuous_calib L W).comp_continuousOn hΦc
  have hinv : ContinuousOn (fun x => (calib L W (Φ x))⁻¹) (base R L W) :=
    hcal.inv₀ fun x hx => (calib_pos_of_mem R L W hW Φ hΦ hΦ0 hx).ne'
  exact hinv.smul hΦc

/-- The normalized projective map as a continuous self-map of the compact convex base. -/
noncomputable def continuousRayMap (hΦc : ContinuousOn Φ (base R L W)) :
    C(base R L W, base R L W) where
  toFun x := ⟨rayMap L W Φ x, rayMap_mem_base R L W hW Φ hΦ hΦ0 x.property⟩
  continuous_toFun := Continuous.subtype_mk
    (continuousOn_rayMap R L W hW Φ hΦ hΦ0 hΦc).restrict _

/-- **(RG.15), unconditional branch**: Brouwer's theorem supplies a fixed projective ray for
every continuous cone-preserving leading map on a nonempty compact physical base. -/
theorem exists_fixed_of_continuous
    (hpointed : ∀ x ∈ LinearMap.ker R, (∀ j, L j x = 0) → x = 0)
    (hne : (base R L W).Nonempty) (hΦc : ContinuousOn Φ (base R L W)) :
    ∃ a ∈ base R L W, rayMap L W Φ a = a := by
  obtain ⟨a, ha⟩ := brouwer_fixed_point (base R L W) (base_convex R L W)
    (base_isCompact R L W hW hpointed) hne (continuousRayMap R L W hW Φ hΦ hΦ0 hΦc)
  refine ⟨a, a.property, ?_⟩
  exact congrArg Subtype.val ha

end Brouwer

/-! ### The contractive branch -/

section Contractive

variable (hW : ∀ j, (W j).PosDef) (Φ : E → E) {q : ℝ}
  (hq0 : 0 ≤ q) (hq1 : q < 1)
  (hΦ : ∀ x ∈ base R L W, Φ x ∈ cone R L)
  (hΦ0 : ∀ x ∈ base R L W, ¬ ∀ j, L j (Φ x) = 0)
  (hLip : ∀ x ∈ base R L W, ∀ y ∈ base R L W,
    dist (rayMap L W Φ x) (rayMap L W Φ y) ≤ q * dist x y)

include hq0 hq1 hLip

omit [FiniteDimensional ℝ E] hq0 in
/-- Uniqueness of the projective ray on the contractive branch. -/
theorem fixed_unique_of_contractive {a a' : E} (ha : a ∈ base R L W) (ha' : a' ∈ base R L W)
    (hfa : rayMap L W Φ a = a) (hfa' : rayMap L W Φ a' = a') : a = a' := by
  have h := hLip a ha a' ha'
  rw [hfa, hfa'] at h
  have : (1 - q) * dist a a' ≤ 0 := by linarith
  have hd : dist a a' ≤ 0 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  exact dist_le_zero.mp hd

include hW hΦ hΦ0

/-- Existence of the projective ray on the contractive branch (Banach iteration on the compact
base). -/
theorem exists_fixed_of_contractive (hne : (base R L W).Nonempty) :
    ∃ a ∈ base R L W, rayMap L W Φ a = a := by
  classical
  obtain ⟨x₀, hx₀⟩ := hne
  set T : E → E := rayMap L W Φ with hT
  set u : ℕ → E := fun k => T^[k] x₀ with hu
  have humem : ∀ k, u k ∈ base R L W := by
    intro k
    induction k with
    | zero => simpa [hu] using hx₀
    | succ k ih =>
      have : u (k + 1) = T (u k) := by
        simp [hu, Function.iterate_succ_apply']
      rw [this]
      exact rayMap_mem_base R L W hW Φ hΦ hΦ0 ih
  have hstep : ∀ k, u (k + 1) = T (u k) := by
    intro k
    simp [hu, Function.iterate_succ_apply']
  have hgeom : ∀ k, dist (u k) (u (k + 1)) ≤ dist (u 0) (u 1) * q ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 := hLip (u k) (humem k) (u (k + 1)) (humem (k + 1))
      rw [← hstep k, ← hstep (k + 1)] at h1
      calc dist (u (k + 1)) (u (k + 2)) ≤ q * dist (u k) (u (k + 1)) := h1
        _ ≤ q * (dist (u 0) (u 1) * q ^ k) := by
            exact mul_le_mul_of_nonneg_left ih hq0
        _ = dist (u 0) (u 1) * q ^ (k + 1) := by ring
  have hcauchy : CauchySeq u := cauchySeq_of_le_geometric q (dist (u 0) (u 1)) hq1 hgeom
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hamem : a ∈ base R L W :=
    (isClosed_base R L W).mem_of_tendsto ha (Filter.Eventually.of_forall humem)
  refine ⟨a, hamem, ?_⟩
  have hTa : Filter.Tendsto (fun k => T (u k)) Filter.atTop (𝓝 (T a)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    rw [Metric.tendsto_atTop] at ha
    obtain ⟨N, hN⟩ := ha ε hε
    refine ⟨N, fun k hk => ?_⟩
    calc dist (T (u k)) (T a) ≤ q * dist (u k) a := hLip (u k) (humem k) a hamem
      _ ≤ 1 * dist (u k) a := mul_le_mul_of_nonneg_right hq1.le dist_nonneg
      _ = dist (u k) a := one_mul _
      _ < ε := hN k hk
  have hTa' : Filter.Tendsto (fun k => u (k + 1)) Filter.atTop (𝓝 a) :=
    ha.comp (Filter.tendsto_add_atTop_nat 1)
  have : Filter.Tendsto (fun k => T (u k)) Filter.atTop (𝓝 a) := by
    refine hTa'.congr fun k => ?_
    rw [hstep k]
  exact tendsto_nhds_unique hTa this

omit [FiniteDimensional ℝ E] hW hΦ hΦ0 hq0 in
/-- **(RG.16)**: the a-posteriori residual bound
`‖â - a‖ ≤ ‖â - 𝒯(â)‖ / (1 - q)`. -/
theorem residual_bound {a ahat : E} (ha : a ∈ base R L W) (hahat : ahat ∈ base R L W)
    (hfa : rayMap L W Φ a = a) :
    ‖ahat - a‖ ≤ ‖ahat - rayMap L W Φ ahat‖ / (1 - q) := by
  have h1 : dist ahat a ≤ dist ahat (rayMap L W Φ ahat) + dist (rayMap L W Φ ahat) a :=
    dist_triangle _ _ _
  have h2 : dist (rayMap L W Φ ahat) a ≤ q * dist ahat a := by
    have := hLip ahat hahat a ha
    rwa [hfa] at this
  have h3 : (1 - q) * dist ahat a ≤ dist ahat (rayMap L W Φ ahat) := by linarith
  rw [dist_eq_norm, dist_eq_norm] at h3
  rw [le_div_iff₀ (by linarith)]
  linarith

end Contractive

/-! ### (RG.17): the certified scalar Read -/

/-- The calibration as a continuous linear functional. -/
noncomputable def calibL : E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := calib L W
      map_add' := calib_add L W
      map_smul' := fun c x => by simp [calib_smul L W c x] }

theorem calibL_apply (x : E) : calibL L W x = calib L W x := rfl

omit [FiniteDimensional ℝ E] in
theorem calib_sub (x y : E) : calib L W (x - y) = calib L W x - calib L W y := by
  have h1 : calib L W ((-1 : ℝ) • y) = -calib L W y := by
    rw [calib_smul]
    ring
  rw [sub_eq_add_neg, sub_eq_add_neg, calib_add, ← h1, neg_one_smul]

/-- Membership of base differences in the calibration kernel. -/
theorem sub_mem_ker_calibL {x y : E} (hx : x ∈ base R L W) (hy : y ∈ base R L W) :
    x - y ∈ LinearMap.ker (calibL L W : E →ₗ[ℝ] ℝ) := by
  rw [LinearMap.mem_ker]
  change calibL L W (x - y) = 0
  rw [calibL_apply, calib_sub, hx.2, hy.2, sub_self]

/-- **(RG.17)**: the physical scalar Read is certified through the kernel-restricted dual norm
and the residual bound. -/
theorem read_bound (ℓ : E →L[ℝ] ℝ) {q : ℝ} (hq1 : q < 1) (Φ : E → E)
    (hLip : ∀ x ∈ base R L W, ∀ y ∈ base R L W,
      dist (rayMap L W Φ x) (rayMap L W Φ y) ≤ q * dist x y)
    {a ahat : E} (ha : a ∈ base R L W) (hahat : ahat ∈ base R L W)
    (hfa : rayMap L W Φ a = a) :
    |ℓ ahat - ℓ a|
      ≤ ‖ℓ.comp (LinearMap.ker (calibL L W : E →ₗ[ℝ] ℝ)).subtypeL‖
        * (‖ahat - rayMap L W Φ ahat‖ / (1 - q)) := by
  have hker := sub_mem_ker_calibL R L W hahat ha
  have h1 : |ℓ ahat - ℓ a|
      = ‖ℓ.comp (LinearMap.ker (calibL L W : E →ₗ[ℝ] ℝ)).subtypeL ⟨ahat - a, hker⟩‖ := by
    change |ℓ ahat - ℓ a| = ‖ℓ (ahat - a)‖
    rw [map_sub, Real.norm_eq_abs]
  have h2 : ‖ℓ.comp (LinearMap.ker (calibL L W : E →ₗ[ℝ] ℝ)).subtypeL ⟨ahat - a, hker⟩‖
      ≤ ‖ℓ.comp (LinearMap.ker (calibL L W : E →ₗ[ℝ] ℝ)).subtypeL‖ * ‖ahat - a‖ :=
    (ℓ.comp (LinearMap.ker (calibL L W : E →ₗ[ℝ] ℝ)).subtypeL).le_opNorm _
  have h3 : ‖ahat - a‖ ≤ ‖ahat - rayMap L W Φ ahat‖ / (1 - q) :=
    residual_bound R L W Φ hq1 hLip ha hahat hfa
  rw [h1]
  refine h2.trans ?_
  exact mul_le_mul_of_nonneg_left h3 (by positivity)

/-! ### (RG.18): coordinate covariance -/

variable {E' F' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [AddCommGroup F'] [Module ℝ F']

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- **(RG.18)**: an invertible packet transport conjugates the projective map, so fixed rays and
scalar Reads transport exactly. -/
theorem rayMap_equivariant {n' : ι → Type*} [∀ j, Fintype (n' j)]
    (L' : ∀ j, E' →ₗ[ℝ] Matrix (n' j) (n' j) ℝ) (W' : ∀ j, Matrix (n' j) (n' j) ℝ)
    (A : E ≃L[ℝ] E') (Φ : E → E) (Φ' : E' → E')
    (hcal : ∀ x : E, calib L' W' (A x) = calib L W x)
    (hΦ' : ∀ x : E, Φ' (A x) = A (Φ x)) (x : E) :
    rayMap L' W' Φ' (A x) = A (rayMap L W Φ x) := by
  rw [rayMap, rayMap, hΦ' x, hcal (Φ x), map_smul]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
theorem fixed_transport {n' : ι → Type*} [∀ j, Fintype (n' j)]
    (L' : ∀ j, E' →ₗ[ℝ] Matrix (n' j) (n' j) ℝ) (W' : ∀ j, Matrix (n' j) (n' j) ℝ)
    (A : E ≃L[ℝ] E') (Φ : E → E) (Φ' : E' → E')
    (hcal : ∀ x : E, calib L' W' (A x) = calib L W x)
    (hΦ' : ∀ x : E, Φ' (A x) = A (Φ x)) {a : E} (hfa : rayMap L W Φ a = a) :
    rayMap L' W' Φ' (A a) = A a := by
  rw [rayMap_equivariant L W L' W' A Φ Φ' hcal hΦ' a, hfa]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- The transported scalar Read of the transported ray is unchanged. -/
theorem read_transport (A : E ≃L[ℝ] E') (ℓ : E →L[ℝ] ℝ) (ℓ' : E' →L[ℝ] ℝ)
    (hℓ : ∀ x : E, ℓ' (A x) = ℓ x) (a : E) : ℓ' (A a) = ℓ a := hℓ a

/-- **`thm:SM-certified-projective-ray`** (fixed-point existence on the non-contractive branch
is Brouwer's theorem, entering only through the hypotheses of `fixed_eigen`): the projective map
preserves the base; (RG.15) fixed points are positive eigenrays; on the `q`-contractive branch
existence, uniqueness, (RG.16) the residual bound and (RG.17) the certified scalar Read. -/
theorem sm_certified_projective_ray (hW : ∀ j, (W j).PosDef) (Φ : E → E)
    (hΦ : ∀ x ∈ base R L W, Φ x ∈ cone R L)
    (hΦ0 : ∀ x ∈ base R L W, ¬ ∀ j, L j (Φ x) = 0) :
    (∀ x ∈ base R L W, rayMap L W Φ x ∈ base R L W) ∧
      (∀ a ∈ base R L W, rayMap L W Φ a = a →
        Φ a = calib L W (Φ a) • a ∧ 0 < calib L W (Φ a)) ∧
      ∀ {q : ℝ}, 0 ≤ q → q < 1 →
        (∀ x ∈ base R L W, ∀ y ∈ base R L W,
          dist (rayMap L W Φ x) (rayMap L W Φ y) ≤ q * dist x y) →
        ((base R L W).Nonempty → ∃ a ∈ base R L W, rayMap L W Φ a = a) ∧
        (∀ a ∈ base R L W, ∀ a' ∈ base R L W,
          rayMap L W Φ a = a → rayMap L W Φ a' = a' → a = a') ∧
        ∀ a ∈ base R L W, ∀ ahat ∈ base R L W, rayMap L W Φ a = a →
          ‖ahat - a‖ ≤ ‖ahat - rayMap L W Φ ahat‖ / (1 - q) ∧
          ∀ ℓ : E →L[ℝ] ℝ, |ℓ ahat - ℓ a|
            ≤ ‖ℓ.comp (LinearMap.ker (calibL L W : E →ₗ[ℝ] ℝ)).subtypeL‖
              * (‖ahat - rayMap L W Φ ahat‖ / (1 - q)) :=
  ⟨fun _ hx => rayMap_mem_base R L W hW Φ hΦ hΦ0 hx,
    fun _ ha hfix => fixed_eigen R L W hW Φ hΦ hΦ0 ha hfix,
    fun hq0 hq1 hLip =>
      ⟨fun hne => exists_fixed_of_contractive R L W hW Φ hq0 hq1 hΦ hΦ0 hLip hne,
        fun _ ha _ ha' hfa hfa' =>
          fixed_unique_of_contractive R L W Φ hq1 hLip ha ha' hfa hfa',
        fun _ ha _ hahat hfa => ⟨residual_bound R L W Φ hq1 hLip ha hahat hfa,
          fun ℓ => read_bound R L W ℓ hq1 Φ hLip ha hahat hfa⟩⟩⟩

/-- **`thm:SM-certified-projective-ray`**, including the unconditional (RG.15) clause: on a
nonempty pointed compact base, every continuous cone-preserving leading map has a positive
eigenray.  The remaining preservation, contractive uniqueness, residual certification, scalar
Read, and covariance clauses are supplied by `sm_certified_projective_ray` and the transport
theorems above. -/
theorem sm_certified_projective_ray_with_brouwer
    (hW : ∀ j, (W j).PosDef)
    (hpointed : ∀ x ∈ LinearMap.ker R, (∀ j, L j x = 0) → x = 0)
    (hne : (base R L W).Nonempty) (Φ : E → E)
    (hΦ : ∀ x ∈ base R L W, Φ x ∈ cone R L)
    (hΦ0 : ∀ x ∈ base R L W, ¬ ∀ j, L j (Φ x) = 0)
    (hΦc : ContinuousOn Φ (base R L W)) :
    (∃ a ∈ base R L W, rayMap L W Φ a = a ∧
      Φ a = calib L W (Φ a) • a ∧ 0 < calib L W (Φ a)) ∧
      ((∀ x ∈ base R L W, rayMap L W Φ x ∈ base R L W) ∧
      (∀ a ∈ base R L W, rayMap L W Φ a = a →
        Φ a = calib L W (Φ a) • a ∧ 0 < calib L W (Φ a))) := by
  obtain ⟨a, ha, hfix⟩ :=
    exists_fixed_of_continuous R L W hW Φ hΦ hΦ0 hpointed hne hΦc
  have heigen := fixed_eigen R L W hW Φ hΦ hΦ0 ha hfix
  exact ⟨⟨a, ha, hfix, heigen⟩,
    (sm_certified_projective_ray R L W hW Φ hΦ hΦ0).1,
    (sm_certified_projective_ray R L W hW Φ hΦ hΦ0).2.1⟩

end ProjectiveRay
end NCG
