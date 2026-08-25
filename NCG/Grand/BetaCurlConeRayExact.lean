/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CertifiedProjectiveRayExact

/-!
# Variational–circulating marginal tensor and cone ray

Machinery for `thm:SM-beta-curl-cone-ray`.  On a real inner product space with a symmetric
quadratic tensor `𝒬`:

* (RG.10) the metric-orthogonal decomposition `𝒬 = 𝒬_var + 𝒬_circ`: the variational part is the
  full symmetrization of `⟨𝒬(u,v), w⟩` — the gradient tensor of the cubic potential
  `Φ(x) = ⅓⟨x, 𝒬(x,x)⟩` (`hasDerivAt_cubic`) — the circulation is radial-free,
  `⟨x, 𝒬_circ(x,x)⟩ = 0` (`inner_circ_self`), and the decomposition is unique
  (`decomposition_unique`);
* (RG.11) the circulation is exactly the beta-form curl
  `⟨h, 𝒬_circ(u,v)⟩ = ⅙(Ω_v(u,h) + Ω_u(v,h))` (`inner_circ_eq_curl`), where `Ω` is the
  exterior derivative of the beta one-form `α_x(h) = ⟨h, 𝒬(x,x)⟩` (`hasDerivAt_beta`);
* (RG.12) for a variational cone candidate `a` with dual slack `s` (`𝒬_var(a,a) = β a - s`),
  the complete-ray condition on the tangent space `h ⊥ a` is the tangent-curl identity
  `⅓ Ω_a(a,h) = ⟨h, s⟩` (`ray_iff_tangent_curl`);
* the projective cone-ray existence (contractive branch) and uniqueness clauses are
  `NCG.ProjectiveRay.sm_certified_projective_ray` applied to `Φ(x) = 𝒬(x,x)`
  (`quadratic_cone_ray`).
-/

open scoped RealInnerProductSpace InnerProduct

namespace NCG
namespace BetaCurl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (Q : E →L[ℝ] E →L[ℝ] E)

/-- The symmetrized trilinear form `S(u,v,w) = ⅓(⟨𝒬(u,v),w⟩ + ⟨𝒬(v,w),u⟩ + ⟨𝒬(w,u),v⟩)`. -/
noncomputable def symForm (u v w : E) : ℝ :=
  (⟪Q u v, w⟫ + ⟪Q v w, u⟫ + ⟪Q w u, v⟫) / 3

/-- (RG.10) the variational part `𝒬_var`, with `⟨𝒬_var(u,v), w⟩ = S(u,v,w)`. -/
noncomputable def Qvar (u v : E) : E :=
  (3 : ℝ)⁻¹ • (Q u v + ((Q v)†) u + ((ContinuousLinearMap.flip Q u)†) v)

/-- (RG.10) the circulating part `𝒬_circ = 𝒬 - 𝒬_var`. -/
noncomputable def Qcirc (u v : E) : E := Q u v - Qvar Q u v

theorem inner_Qvar (u v w : E) : ⟪Qvar Q u v, w⟫ = symForm Q u v w := by
  rw [Qvar, real_inner_smul_left, inner_add_left, inner_add_left,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.flip_apply, symForm,
    real_inner_comm u (Q v w), real_inner_comm v (Q w u)]
  ring

theorem Qvar_add_Qcirc (u v : E) : Qvar Q u v + Qcirc Q u v = Q u v := by
  rw [Qcirc]
  abel

/-- **(RG.10)**: the circulation is radial-free. -/
theorem inner_circ_self (x : E) : ⟪Qcirc Q x x, x⟫ = 0 := by
  rw [Qcirc, inner_sub_left, inner_Qvar, symForm]
  ring

/-- **(RG.10)**: the variational part is the gradient tensor of the cubic potential
`Φ(x) = ⅓⟨x, 𝒬(x,x)⟩`: along every line, `∂_t Φ(x + t h)|₀ = ⟨𝒬_var(x,x), h⟩`. -/
theorem hasDerivAt_cubic (x h : E) :
    HasDerivAt (fun t : ℝ => ⟪Q (x + t • h) (x + t • h), x + t • h⟫ / 3)
      ⟪Qvar Q x x, h⟫ 0 := by
  set a₀ : ℝ := ⟪Q x x, x⟫ with ha₀
  set a₁ : ℝ := ⟪Q x x, h⟫ + ⟪Q x h, x⟫ + ⟪Q h x, x⟫ with ha₁
  set a₂ : ℝ := ⟪Q x h, h⟫ + ⟪Q h x, h⟫ + ⟪Q h h, x⟫ with ha₂
  set a₃ : ℝ := ⟪Q h h, h⟫ with ha₃
  have hfe : ∀ t : ℝ, ⟪Q (x + t • h) (x + t • h), x + t • h⟫ / 3
      = (a₀ + a₁ * t + a₂ * t ^ 2 + a₃ * t ^ 3) / 3 := by
    intro t
    simp only [map_add, map_smul, _root_.add_apply, _root_.smul_apply,
      inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      ha₀, ha₁, ha₂, ha₃]
    ring
  have hpoly : HasDerivAt (fun t : ℝ => (a₀ + a₁ * t + a₂ * t ^ 2 + a₃ * t ^ 3) / 3)
      (a₁ / 3) 0 := by
    have h := ((((hasDerivAt_const (0 : ℝ) a₀).add
      ((hasDerivAt_id (0 : ℝ)).const_mul a₁)).add
      ((hasDerivAt_pow 2 (0 : ℝ)).const_mul a₂)).add
      ((hasDerivAt_pow 3 (0 : ℝ)).const_mul a₃)).div_const 3
    exact h.congr_deriv (by norm_num)
  have hval : a₁ / 3 = ⟪Qvar Q x x, h⟫ := by
    rw [inner_Qvar, symForm, ha₁, real_inner_comm x (Q x h), real_inner_comm x (Q h x)]
  rw [← hval]
  exact hpoly.congr_of_eventuallyEq (Filter.Eventually.of_forall hfe)

/-! ### Uniqueness of the decomposition -/

section Unique

variable (Q₂ : E →L[ℝ] E →L[ℝ] E)

omit [CompleteSpace E] in
/-- Polarization step: a symmetric radial-free tensor kills `2⟨𝒬₂(u,v),u⟩ + ⟨𝒬₂(u,u),v⟩`. -/
theorem circ_first_slot (hs2 : ∀ u v, Q₂ u v = Q₂ v u) (hcirc : ∀ x, ⟪Q₂ x x, x⟫ = 0)
    (u v : E) : 2 * ⟪Q₂ u v, u⟫ + ⟪Q₂ u u, v⟫ = 0 := by
  have hexp : ∀ t : ℝ, 0 = (2 * ⟪Q₂ u v, u⟫ + ⟪Q₂ u u, v⟫) * t
      + (2 * ⟪Q₂ u v, v⟫ + ⟪Q₂ v v, u⟫) * t ^ 2 := by
    intro t
    have h := hcirc (u + t • v)
    simp only [map_add, map_smul, _root_.add_apply,
      _root_.smul_apply, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right] at h
    rw [hcirc u, hcirc v] at h
    have hs : ⟪Q₂ v u, u⟫ = ⟪Q₂ u v, u⟫ := by rw [hs2 v u]
    have hs' : ⟪Q₂ v u, v⟫ = ⟪Q₂ u v, v⟫ := by rw [hs2 v u]
    rw [hs, hs'] at h
    linear_combination -h
  have h1 := hexp 1
  have h2 := hexp (-1)
  nlinarith [h1, h2]

omit [CompleteSpace E] in
/-- The cyclic sum of a symmetric radial-free tensor vanishes. -/
theorem circ_cyclic (hs2 : ∀ u v, Q₂ u v = Q₂ v u) (hcirc : ∀ x, ⟪Q₂ x x, x⟫ = 0)
    (a b v : E) : ⟪Q₂ a b, v⟫ + ⟪Q₂ b v, a⟫ + ⟪Q₂ v a, b⟫ = 0 := by
  have h := circ_first_slot Q₂ hs2 hcirc (a + b) v
  have ha := circ_first_slot Q₂ hs2 hcirc a v
  have hb := circ_first_slot Q₂ hs2 hcirc b v
  simp only [map_add, _root_.add_apply, inner_add_left, inner_add_right] at h
  have hsab : ⟪Q₂ b a, v⟫ = ⟪Q₂ a b, v⟫ := by rw [hs2 b a]
  have hsav : ⟪Q₂ a v, b⟫ = ⟪Q₂ v a, b⟫ := by rw [hs2 a v]
  rw [hsab] at h
  rw [← hsav]
  linear_combination (h - ha - hb) / 2

/-- **(RG.10) uniqueness**: a decomposition of `𝒬` into a cyclically symmetric part and a
symmetric radial-free part is the variational–circulating decomposition. -/
theorem decomposition_unique (Q₁ : E →L[ℝ] E →L[ℝ] E)
    (hQ12 : ∀ u v, Q u v = Q₁ u v + Q₂ u v)
    (hcyc1 : ∀ u v w, ⟪Q₁ u v, w⟫ = ⟪Q₁ v w, u⟫)
    (hs2 : ∀ u v, Q₂ u v = Q₂ v u) (hcirc : ∀ x, ⟪Q₂ x x, x⟫ = 0) (u v : E) :
    Q₁ u v = Qvar Q u v ∧ Q₂ u v = Qcirc Q u v := by
  have hmain : Q₁ u v = Qvar Q u v := by
    refine ext_inner_right ℝ fun w => ?_
    rw [inner_Qvar, symForm, hQ12 u v, hQ12 v w, hQ12 w u]
    simp only [inner_add_left]
    have hc := circ_cyclic Q₂ hs2 hcirc u v w
    have h1 : ⟪Q₁ v w, u⟫ = ⟪Q₁ u v, w⟫ := (hcyc1 u v w).symm
    have h2 : ⟪Q₁ w u, v⟫ = ⟪Q₁ u v, w⟫ := by rw [hcyc1 w u v]
    rw [h1, h2]
    linarith [hc]
  refine ⟨hmain, ?_⟩
  have h := hQ12 u v
  rw [hmain] at h
  rw [Qcirc, h]
  abel

end Unique

/-! ### (RG.11): the beta-form curl -/

/-- The beta-form curl `Ω_x(u,h) = ∂_u α_x(h) - ∂_h α_x(u)` of `α_x(h) = ⟨h, 𝒬(x,x)⟩`. -/
noncomputable def Omega (x u h : E) : ℝ := 2 * ⟪h, Q u x⟫ - 2 * ⟪u, Q h x⟫

variable (hsym : ∀ u v, Q u v = Q v u)
include hsym

omit [CompleteSpace E] in
/-- The directional derivative of the beta one-form: `∂_t α_{x+tu}(h)|₀ = 2⟨h, 𝒬(u,x)⟩`, so
`Ω` is its exterior derivative. -/
theorem hasDerivAt_beta (x u h : E) :
    HasDerivAt (fun t : ℝ => ⟪h, Q (x + t • u) (x + t • u)⟫) (2 * ⟪h, Q u x⟫) 0 := by
  set b₀ : ℝ := ⟪h, Q x x⟫ with hb₀
  set b₁ : ℝ := ⟪h, Q x u⟫ + ⟪h, Q u x⟫ with hb₁
  set b₂ : ℝ := ⟪h, Q u u⟫ with hb₂
  have hfe : ∀ t : ℝ, ⟪h, Q (x + t • u) (x + t • u)⟫ = b₀ + b₁ * t + b₂ * t ^ 2 := by
    intro t
    simp only [map_add, map_smul, _root_.add_apply, _root_.smul_apply,
      inner_add_right, real_inner_smul_right, hb₀, hb₁, hb₂]
    ring
  have hpoly : HasDerivAt (fun t : ℝ => b₀ + b₁ * t + b₂ * t ^ 2) b₁ 0 := by
    have h := (((hasDerivAt_const (0 : ℝ) b₀).add
      ((hasDerivAt_id (0 : ℝ)).const_mul b₁)).add
      ((hasDerivAt_pow 2 (0 : ℝ)).const_mul b₂))
    exact h.congr_deriv (by norm_num)
  have hval : b₁ = 2 * ⟪h, Q u x⟫ := by
    rw [hb₁, hsym x u]
    ring
  rw [← hval]
  exact hpoly.congr_of_eventuallyEq (Filter.Eventually.of_forall hfe)

/-- **(RG.11)**: the circulation is exactly the beta-form curl,
`⟨h, 𝒬_circ(u,v)⟩ = ⅙(Ω_v(u,h) + Ω_u(v,h))`. -/
theorem inner_circ_eq_curl (u v h : E) :
    ⟪Qcirc Q u v, h⟫ = (Omega Q v u h + Omega Q u v h) / 6 := by
  rw [Qcirc, inner_sub_left, inner_Qvar, symForm, Omega, Omega, hsym v u, hsym h v, hsym h u]
  have c1 : ⟪h, Q u v⟫ = ⟪Q u v, h⟫ := real_inner_comm (Q u v) h
  have c2 : ⟪u, Q v h⟫ = ⟪Q v h, u⟫ := real_inner_comm (Q v h) u
  have c3 : ⟪v, Q u h⟫ = ⟪Q u h, v⟫ := real_inner_comm (Q u h) v
  rw [c1, c2, c3]
  ring

/-- **(RG.12)**: for a variational cone candidate `a` with dual slack `s`
(`𝒬_var(a,a) = β a - s`), the complete-ray condition on the tangent space `h ⊥ a` is the
tangent-curl identity `⅓ Ω_a(a,h) = ⟨h, s⟩`. -/
theorem ray_iff_tangent_curl (a s : E) (β : ℝ) (hKKT : Qvar Q a a = β • a - s) (h : E)
    (hperp : ⟪h, a⟫ = 0) :
    ⟪Q a a, h⟫ = 0 ↔ Omega Q a a h / 3 = ⟪h, s⟫ := by
  have hsplit : ⟪Q a a, h⟫ = ⟪Qvar Q a a, h⟫ + ⟪Qcirc Q a a, h⟫ := by
    rw [Qcirc, inner_sub_left]
    ring
  have hcurl : ⟪Qcirc Q a a, h⟫ = Omega Q a a h / 3 := by
    rw [inner_circ_eq_curl Q hsym a a h]
    ring
  have hvar : ⟪Qvar Q a a, h⟫ = -⟪s, h⟫ := by
    rw [hKKT, inner_sub_left, real_inner_smul_left, ← real_inner_comm a h, hperp]
    ring
  rw [hsplit, hcurl, hvar, real_inner_comm h s]
  constructor
  · intro h0
    linarith
  · intro h0
    linarith

end BetaCurl

/-! ### The quadratic cone ray -/

namespace BetaCurl

open Matrix NCG.OperationalCone NCG.ProjectiveRay

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [AddCommGroup F] [Module ℝ F]
  {ι : Type*} [Fintype ι] {n : ι → Type*} [∀ j, Fintype (n j)]

omit [CompleteSpace E] in
/-- The projective cone-ray clauses of the theorem, for the normalized quadratic shell
`𝒯(x) = 𝒬(x,x)/ν(𝒬(x,x))`: the base is preserved, fixed points are positive eigenrays, and on
the strictly contractive branch the ray exists and is unique. -/
theorem quadratic_cone_ray (R : E →ₗ[ℝ] F) (L : ∀ j, E →ₗ[ℝ] Matrix (n j) (n j) ℝ)
    (W : ∀ j, Matrix (n j) (n j) ℝ) (hW : ∀ j, (W j).PosDef) (Q : E →L[ℝ] E →L[ℝ] E)
    (hQ : ∀ x ∈ base R L W, Q x x ∈ cone R L)
    (hQ0 : ∀ x ∈ base R L W, ¬ ∀ j, L j (Q x x) = 0) :
    (∀ x ∈ base R L W, rayMap L W (fun x => Q x x) x ∈ base R L W) ∧
      (∀ a ∈ base R L W, rayMap L W (fun x => Q x x) a = a →
        Q a a = calib L W (Q a a) • a ∧ 0 < calib L W (Q a a)) ∧
      ∀ {q : ℝ}, 0 ≤ q → q < 1 →
        (∀ x ∈ base R L W, ∀ y ∈ base R L W,
          dist (rayMap L W (fun x => Q x x) x) (rayMap L W (fun x => Q x x) y)
            ≤ q * dist x y) →
        ((base R L W).Nonempty → ∃ a ∈ base R L W, rayMap L W (fun x => Q x x) a = a) ∧
        ∀ a ∈ base R L W, ∀ a' ∈ base R L W, rayMap L W (fun x => Q x x) a = a →
          rayMap L W (fun x => Q x x) a' = a' → a = a' := by
  obtain ⟨h1, h2, h3⟩ := sm_certified_projective_ray R L W hW (fun x => Q x x) hQ hQ0
  exact ⟨h1, h2, fun hq0 hq1 hLip => ⟨(h3 hq0 hq1 hLip).1, (h3 hq0 hq1 hLip).2.1⟩⟩

end BetaCurl
end NCG
