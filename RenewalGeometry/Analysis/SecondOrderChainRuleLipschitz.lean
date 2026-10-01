/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Second-order chain rule and jet errors of compositions
  (infrastructure for `thm:supp-gowdy-full-curvature`, `eq:supp-gowdy-full-curvature`: "the
  metric estimates follow by differentiating this smooth composition twice"; emergent-spacetime
  supplement)

For a map `Γ : F → G` which is `C³` on an open set `V` and maps `A, B : E → F` of class `C²`:

* `hasFDerivAt_fderiv_comp` (**second-order chain rule**): where `A z ∈ V`,
  `D²(Γ ∘ A)(z) w = D²Γ(A z)(DA(z) w) ∘ DA(z) + DΓ(A z) ∘ D²A(z) w`.
* `comp_jet_sub_le` (**jet errors of a composition**): for every compact convex `K ⊆ V` there is
  `C ≥ 0` such that, whenever `A z, B z ∈ K` and `‖DA z‖, ‖DB z‖, ‖D²B z‖ ≤ M`,
  `‖Γ(A z) - Γ(B z)‖ ≤ C δ₀`, `‖D(Γ∘A) z - D(Γ∘B) z‖ ≤ C (1+M) (δ₀ + δ₁)` and
  `‖D²(Γ∘A) z - D²(Γ∘B) z‖ ≤ C (1+M)² (δ₀ + δ₁ + δ₂)`, with `δ_k = ‖D^k A z - D^k B z‖`.
  The jets of `Γ ∘ A` are also bounded (`comp_jet_norm_le`).
* `fderiv_fderiv_clm_comp`: second derivatives commute with continuous linear maps (used to read
  components).
* `norm_clm_prod_le`, `norm_bilin_prod_le`: operator norms on `ℝ × ℝ` are bounded by the values
  on the two coordinate vectors.
-/

open Set Filter Topology

namespace RenewalGeometry.SecondOrderChainRule

noncomputable section

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The second derivative of `Γ ∘ A` at `z`, assembled from the jets of `Γ` and `A`. -/
def secondComp (Γ : F → G) (A : E → F) (z : E) : E →L[ℝ] E →L[ℝ] G :=
  (ContinuousLinearMap.compL ℝ E F G (fderiv ℝ Γ (A z))).comp (fderiv ℝ (fderiv ℝ A) z) +
    ((ContinuousLinearMap.compL ℝ E F G).flip (fderiv ℝ A z)).comp
      ((fderiv ℝ (fderiv ℝ Γ) (A z)).comp (fderiv ℝ A z))

theorem secondComp_apply (Γ : F → G) (A : E → F) (z w : E) :
    secondComp Γ A z w =
      (fderiv ℝ Γ (A z)).comp (fderiv ℝ (fderiv ℝ A) z w) +
        (fderiv ℝ (fderiv ℝ Γ) (A z) (fderiv ℝ A z w)).comp (fderiv ℝ A z) := rfl

/-- **Second-order chain rule.** -/
theorem hasFDerivAt_fderiv_comp {Γ : F → G} {V : Set F} (hV : IsOpen V) (hΓ : ContDiffOn ℝ 2 Γ V)
    {A : E → F} (hA : ContDiff ℝ 2 A) {z : E} (hz : A z ∈ V) :
    HasFDerivAt (fderiv ℝ (fun y => Γ (A y))) (secondComp Γ A z) z := by
  have hAc : Continuous A := hA.continuous
  have hev : ∀ᶠ y in 𝓝 z, A y ∈ V := hAc.continuousAt.preimage_mem_nhds (hV.mem_nhds hz)
  have heq : (fun y => (fderiv ℝ Γ (A y)).comp (fderiv ℝ A y)) =ᶠ[𝓝 z]
      fderiv ℝ (fun y => Γ (A y)) := by
    filter_upwards [hev] with y hy
    have hΓy : DifferentiableAt ℝ Γ (A y) :=
      ((hΓ.contDiffAt (hV.mem_nhds hy)).differentiableAt (by norm_num))
    exact (fderiv_comp y hΓy (hA.differentiable (by norm_num) y)).symm
  have hdΓ : ContDiffOn ℝ 1 (fderiv ℝ Γ) V := hΓ.fderiv_of_isOpen hV (by norm_num)
  have hc : HasFDerivAt (fun y => fderiv ℝ Γ (A y))
      ((fderiv ℝ (fderiv ℝ Γ) (A z)).comp (fderiv ℝ A z)) z :=
    (((hdΓ.contDiffAt (hV.mem_nhds hz)).differentiableAt (by norm_num)).hasFDerivAt).comp z
      ((hA.differentiable (by norm_num)) z).hasFDerivAt
  have hdA : ContDiff ℝ 1 (fderiv ℝ A) := hA.fderiv_right (by norm_num)
  have hd : HasFDerivAt (fderiv ℝ A) (fderiv ℝ (fderiv ℝ A) z) z :=
    ((hdA.differentiable (by norm_num)) z).hasFDerivAt
  exact (hc.clm_comp hd).congr_of_eventuallyEq heq.symm

theorem fderiv_fderiv_comp {Γ : F → G} {V : Set F} (hV : IsOpen V) (hΓ : ContDiffOn ℝ 2 Γ V)
    {A : E → F} (hA : ContDiff ℝ 2 A) {z : E} (hz : A z ∈ V) :
    fderiv ℝ (fderiv ℝ (fun y => Γ (A y))) z = secondComp Γ A z :=
  (hasFDerivAt_fderiv_comp hV hΓ hA hz).fderiv

theorem fderiv_comp_eq {Γ : F → G} {V : Set F} (hV : IsOpen V) (hΓ : ContDiffOn ℝ 2 Γ V)
    {A : E → F} (hA : ContDiff ℝ 2 A) {z : E} (hz : A z ∈ V) :
    fderiv ℝ (fun y => Γ (A y)) z = (fderiv ℝ Γ (A z)).comp (fderiv ℝ A z) :=
  fderiv_comp z ((hΓ.contDiffAt (hV.mem_nhds hz)).differentiableAt (by norm_num))
    (hA.differentiable (by norm_num) z)

/-- Second derivatives commute with a continuous linear map. -/
theorem fderiv_fderiv_clm_comp (L : F →L[ℝ] G) {f : E → F} (hf : ContDiff ℝ 2 f) (z v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => L (f y))) z v w = L (fderiv ℝ (fderiv ℝ f) z v w) := by
  have h1 : fderiv ℝ (fun y => L (f y)) = fun y => (ContinuousLinearMap.compL ℝ E F G L)
      (fderiv ℝ f y) := by
    funext y
    exact (L.hasFDerivAt.comp y ((hf.differentiable (by norm_num)) y).hasFDerivAt).fderiv
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have h2 := ((ContinuousLinearMap.compL ℝ E F G L).hasFDerivAt.comp z
    ((hdf.differentiable (by norm_num)) z).hasFDerivAt)
  rw [h1]
  have h3 : fderiv ℝ (fun y => (ContinuousLinearMap.compL ℝ E F G L) (fderiv ℝ f y)) z =
      (ContinuousLinearMap.compL ℝ E F G L).comp (fderiv ℝ (fderiv ℝ f) z) := h2.fderiv
  rw [h3]
  rfl

/-- First derivatives commute with a continuous linear map. -/
theorem fderiv_clm_comp' (L : F →L[ℝ] G) {f : E → F} (hf : DifferentiableAt ℝ f z) (v : E) :
    fderiv ℝ (fun y => L (f y)) z v = L (fderiv ℝ f z v) := by
  have h3 : fderiv ℝ (fun y => L (f y)) z = L.comp (fderiv ℝ f z) :=
    (L.hasFDerivAt.comp z hf.hasFDerivAt).fderiv
  rw [h3]
  rfl

/-! ### Operator norms on `ℝ × ℝ` -/

theorem norm_clm_prod_le (L : ℝ × ℝ →L[ℝ] G) : ‖L‖ ≤ ‖L (1, 0)‖ + ‖L (0, 1)‖ := by
  refine L.opNorm_le_bound (by positivity) fun v => ?_
  have e : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  have h1 : |v.1| ≤ ‖v‖ := by
    have := norm_fst_le v; rwa [Real.norm_eq_abs] at this
  have h2 : |v.2| ≤ ‖v‖ := by
    have := norm_snd_le v; rwa [Real.norm_eq_abs] at this
  rw [e, map_add, map_smul, map_smul]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have : ‖v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ))‖ = ‖v‖ := by rw [← e]
  rw [this]
  nlinarith [norm_nonneg (L (1, 0)), norm_nonneg (L (0, 1)),
    mul_le_mul_of_nonneg_right h1 (norm_nonneg (L (1, 0))),
    mul_le_mul_of_nonneg_right h2 (norm_nonneg (L (0, 1)))]

theorem norm_bilin_prod_le (T : ℝ × ℝ →L[ℝ] ℝ × ℝ →L[ℝ] G) :
    ‖T‖ ≤ ‖T (1, 0) (1, 0)‖ + ‖T (1, 0) (0, 1)‖ + ‖T (0, 1) (1, 0)‖ + ‖T (0, 1) (0, 1)‖ := by
  refine (norm_clm_prod_le T).trans ?_
  have := norm_clm_prod_le (T (1, 0))
  have := norm_clm_prod_le (T (0, 1))
  linarith

/-! ### Jet errors of a composition -/

theorem norm_secondComp_sub_le {Γ : F → G} {A B : E → F} {z : E} {L₁ L₂ M₁ M₂ M δ₀ δ₁ δ₂ : ℝ}
    (hM : 0 ≤ M) (hM₁ : ‖fderiv ℝ Γ (A z)‖ ≤ M₁) (hM₂ : ‖fderiv ℝ (fderiv ℝ Γ) (B z)‖ ≤ M₂)
    (hL₁ : ‖fderiv ℝ Γ (A z) - fderiv ℝ Γ (B z)‖ ≤ L₁ * δ₀)
    (hL₂ : ‖fderiv ℝ (fderiv ℝ Γ) (A z) - fderiv ℝ (fderiv ℝ Γ) (B z)‖ ≤ L₂ * δ₀)
    (hδ₀ : 0 ≤ δ₀) (hL₁0 : 0 ≤ L₁) (hL₂0 : 0 ≤ L₂)
    (hA1 : ‖fderiv ℝ A z‖ ≤ M) (hB1 : ‖fderiv ℝ B z‖ ≤ M) (hB2 : ‖fderiv ℝ (fderiv ℝ B) z‖ ≤ M)
    (hδ₁ : ‖fderiv ℝ A z - fderiv ℝ B z‖ ≤ δ₁)
    (hδ₂ : ‖fderiv ℝ (fderiv ℝ A) z - fderiv ℝ (fderiv ℝ B) z‖ ≤ δ₂) :
    ‖secondComp Γ A z - secondComp Γ B z‖ ≤
      (L₂ * M ^ 2 + L₁ * M) * δ₀ + 2 * M₂ * M * δ₁ + M₁ * δ₂ := by
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg (fderiv ℝ Γ (A z))).trans hM₁
  have hM₂0 : 0 ≤ M₂ := (norm_nonneg (fderiv ℝ (fderiv ℝ Γ) (B z))).trans hM₂
  have hδ₁0 : 0 ≤ δ₁ := (norm_nonneg _).trans hδ₁
  have hδ₂0 : 0 ≤ δ₂ :=
    (norm_nonneg (fderiv ℝ (fderiv ℝ A) z - fderiv ℝ (fderiv ℝ B) z)).trans hδ₂
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  set a := fderiv ℝ Γ (A z)
  set b := fderiv ℝ Γ (B z)
  set a2 := fderiv ℝ (fderiv ℝ Γ) (A z)
  set b2 := fderiv ℝ (fderiv ℝ Γ) (B z)
  set DA := fderiv ℝ A z
  set DB := fderiv ℝ B z
  set D2A := fderiv ℝ (fderiv ℝ A) z
  set D2B := fderiv ℝ (fderiv ℝ B) z
  have e : (secondComp Γ A z - secondComp Γ B z) w =
      a.comp ((D2A - D2B) w) + (a - b).comp (D2B w) +
        (((a2 - b2) (DA w)).comp DA + (b2 ((DA - DB) w)).comp DA + (b2 (DB w)).comp (DA - DB)) := by
    rw [ContinuousLinearMap.sub_apply, secondComp_apply, secondComp_apply]
    ext x
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.comp_apply, map_sub]
    abel
  rw [e]
  have hw := norm_nonneg w
  have t1 : ‖a.comp ((D2A - D2B) w)‖ ≤ M₁ * (δ₂ * ‖w‖) :=
    (a.opNorm_comp_le _).trans (mul_le_mul hM₁ (((D2A - D2B).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right hδ₂ hw)) (norm_nonneg _) hM₁0)
  have t2 : ‖(a - b).comp (D2B w)‖ ≤ L₁ * δ₀ * (M * ‖w‖) :=
    ((a - b).opNorm_comp_le _).trans (mul_le_mul hL₁ ((D2B.le_opNorm w).trans
      (mul_le_mul_of_nonneg_right hB2 hw)) (norm_nonneg _) (by positivity))
  have t3 : ‖((a2 - b2) (DA w)).comp DA‖ ≤ L₂ * δ₀ * (M * ‖w‖) * M := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul ?_ hA1 (norm_nonneg _)
      (by positivity))
    refine ((a2 - b2).le_opNorm _).trans (mul_le_mul hL₂ ?_ (norm_nonneg _) (by positivity))
    exact (DA.le_opNorm w).trans (mul_le_mul_of_nonneg_right hA1 hw)
  have t4 : ‖(b2 ((DA - DB) w)).comp DA‖ ≤ M₂ * (δ₁ * ‖w‖) * M := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul ?_ hA1 (norm_nonneg _)
      (by positivity))
    refine (b2.le_opNorm _).trans (mul_le_mul hM₂ ?_ (norm_nonneg _) hM₂0)
    exact ((DA - DB).le_opNorm w).trans (mul_le_mul_of_nonneg_right hδ₁ hw)
  have t5 : ‖(b2 (DB w)).comp (DA - DB)‖ ≤ M₂ * (M * ‖w‖) * δ₁ := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul ?_ hδ₁ (norm_nonneg _)
      (by positivity))
    refine (b2.le_opNorm _).trans (mul_le_mul hM₂ ?_ (norm_nonneg _) hM₂0)
    exact (DB.le_opNorm w).trans (mul_le_mul_of_nonneg_right hB1 hw)
  have n1 := norm_add_le (a.comp ((D2A - D2B) w)) ((a - b).comp (D2B w))
  have n2 := norm_add_le (a.comp ((D2A - D2B) w) + (a - b).comp (D2B w))
    (((a2 - b2) (DA w)).comp DA + (b2 ((DA - DB) w)).comp DA + (b2 (DB w)).comp (DA - DB))
  have n3 := norm_add_le (((a2 - b2) (DA w)).comp DA + (b2 ((DA - DB) w)).comp DA)
    ((b2 (DB w)).comp (DA - DB))
  have n4 := norm_add_le (((a2 - b2) (DA w)).comp DA) ((b2 ((DA - DB) w)).comp DA)
  nlinarith

/-- **Jet errors of a composition.**  If `Γ` is `C³` on the open set `V` and `K ⊆ V` is compact
and convex, there is `C ≥ 0` such that for `C²` maps `A, B` with `A z, B z ∈ K` and
`‖DA z‖, ‖DB z‖, ‖D²B z‖ ≤ M`:
`‖Γ(A z) - Γ(B z)‖ ≤ C ‖A z - B z‖`,
`‖D(Γ∘A) z - D(Γ∘B) z‖ ≤ C (1 + M) (‖A z - B z‖ + ‖DA z - DB z‖)`,
`‖D²(Γ∘A) z - D²(Γ∘B) z‖ ≤ C (1 + M)² (‖A z - B z‖ + ‖DA z - DB z‖ + ‖D²A z - D²B z‖)`. -/
theorem comp_jet_sub_le {Γ : F → G} {V K : Set F} (hV : IsOpen V) (hΓ : ContDiffOn ℝ 3 Γ V)
    (hKV : K ⊆ V) (hKc : IsCompact K) (hKx : Convex ℝ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A B : E → F), ContDiff ℝ 2 A → ContDiff ℝ 2 B → ∀ z : E,
      A z ∈ K → B z ∈ K → ∀ M : ℝ, 0 ≤ M → ‖fderiv ℝ A z‖ ≤ M → ‖fderiv ℝ B z‖ ≤ M →
        ‖fderiv ℝ (fderiv ℝ B) z‖ ≤ M →
        ‖Γ (A z) - Γ (B z)‖ ≤ C * ‖A z - B z‖ ∧
        ‖fderiv ℝ (fun y => Γ (A y)) z - fderiv ℝ (fun y => Γ (B y)) z‖ ≤
          C * (1 + M) * (‖A z - B z‖ + ‖fderiv ℝ A z - fderiv ℝ B z‖) ∧
        ‖fderiv ℝ (fderiv ℝ (fun y => Γ (A y))) z - fderiv ℝ (fderiv ℝ (fun y => Γ (B y))) z‖ ≤
          C * (1 + M) ^ 2 * (‖A z - B z‖ + ‖fderiv ℝ A z - fderiv ℝ B z‖ +
            ‖fderiv ℝ (fderiv ℝ A) z - fderiv ℝ (fderiv ℝ B) z‖) := by
  have hd1 : ContDiffOn ℝ 2 (fderiv ℝ Γ) V := hΓ.fderiv_of_isOpen hV (by norm_num)
  have hd2 : ContDiffOn ℝ 1 (fderiv ℝ (fderiv ℝ Γ)) V := hd1.fderiv_of_isOpen hV (by norm_num)
  obtain ⟨L₀, hL₀⟩ := (hΓ.mono hKV).exists_lipschitzOnWith (by norm_num) hKx hKc
  obtain ⟨L₁, hL₁⟩ := (hd1.mono hKV).exists_lipschitzOnWith (by norm_num) hKx hKc
  obtain ⟨L₂, hL₂⟩ := (hd2.mono hKV).exists_lipschitzOnWith (by norm_num) hKx hKc
  obtain ⟨M₁, hM₁⟩ := hKc.exists_bound_of_continuousOn (hd1.continuousOn.mono hKV)
  obtain ⟨M₂, hM₂⟩ := hKc.exists_bound_of_continuousOn (f := fderiv ℝ (fderiv ℝ Γ)) (hd2.continuousOn.mono hKV)
  set C := (L₀ : ℝ) + L₁ + L₂ + 2 * |M₁| + 2 * |M₂| with hC
  have hL₀0 := L₀.2
  have hL₁0 := L₁.2
  have hL₂0 := L₂.2
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C, hC0, fun A B hA hB z hAz hBz M hM hA1 hB1 hB2 => ?_⟩
  have hΓ2 : ContDiffOn ℝ 2 Γ V := hΓ.of_le (by norm_num)
  set δ₀ := ‖A z - B z‖
  set δ₁ := ‖fderiv ℝ A z - fderiv ℝ B z‖
  set δ₂ := ‖fderiv ℝ (fderiv ℝ A) z - fderiv ℝ (fderiv ℝ B) z‖
  have hδ₀ : 0 ≤ δ₀ := norm_nonneg _
  have hδ₁ : 0 ≤ δ₁ := norm_nonneg _
  have hδ₂ : 0 ≤ δ₂ := norm_nonneg (fderiv ℝ (fderiv ℝ A) z - fderiv ℝ (fderiv ℝ B) z)
  have l0 : ‖Γ (A z) - Γ (B z)‖ ≤ L₀ * δ₀ := by
    have := hL₀.dist_le_mul _ hAz _ hBz; rwa [dist_eq_norm, dist_eq_norm] at this
  have l1 : ‖fderiv ℝ Γ (A z) - fderiv ℝ Γ (B z)‖ ≤ L₁ * δ₀ := by
    have := hL₁.dist_le_mul _ hAz _ hBz; rwa [dist_eq_norm, dist_eq_norm] at this
  have l2 : ‖fderiv ℝ (fderiv ℝ Γ) (A z) - fderiv ℝ (fderiv ℝ Γ) (B z)‖ ≤ L₂ * δ₀ := by
    have := hL₂.dist_le_mul _ hAz _ hBz; rwa [dist_eq_norm, dist_eq_norm] at this
  have m1 : ‖fderiv ℝ Γ (A z)‖ ≤ |M₁| := (hM₁ _ hAz).trans (le_abs_self _)
  have m1' : ‖fderiv ℝ Γ (B z)‖ ≤ |M₁| := (hM₁ _ hBz).trans (le_abs_self _)
  have m2 : ‖fderiv ℝ (fderiv ℝ Γ) (B z)‖ ≤ |M₂| := (hM₂ _ hBz).trans (le_abs_self _)
  have hM1 : 0 ≤ |M₁| := abs_nonneg _
  have hM2 : 0 ≤ |M₂| := abs_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · refine l0.trans (mul_le_mul_of_nonneg_right ?_ hδ₀)
    rw [hC]; linarith
  · rw [fderiv_comp_eq hV hΓ2 hA (hKV hAz), fderiv_comp_eq hV hΓ2 hB (hKV hBz)]
    have e : (fderiv ℝ Γ (A z)).comp (fderiv ℝ A z) - (fderiv ℝ Γ (B z)).comp (fderiv ℝ B z) =
        (fderiv ℝ Γ (A z)).comp (fderiv ℝ A z - fderiv ℝ B z) +
          (fderiv ℝ Γ (A z) - fderiv ℝ Γ (B z)).comp (fderiv ℝ B z) := by
      ext x; simp
    rw [e]
    have t1 := ((fderiv ℝ Γ (A z)).opNorm_comp_le (fderiv ℝ A z - fderiv ℝ B z)).trans
      (mul_le_mul m1 (le_refl δ₁) hδ₁ hM1)
    have t2 := ((fderiv ℝ Γ (A z) - fderiv ℝ Γ (B z)).opNorm_comp_le (fderiv ℝ B z)).trans
      (mul_le_mul l1 hB1 (norm_nonneg _) (by positivity))
    refine (norm_add_le _ _).trans ((add_le_add t1 t2).trans ?_)
    have hc1 : |M₁| ≤ C := by rw [hC]; linarith
    have hc2 : (L₁ : ℝ) ≤ C := by rw [hC]; linarith
    nlinarith [mul_le_mul_of_nonneg_right hc1 hδ₁, mul_le_mul_of_nonneg_right hc2
      (mul_nonneg hδ₀ hM), mul_nonneg hC0 hδ₀, mul_nonneg hC0 hδ₁, mul_nonneg (mul_nonneg hC0 hM) hδ₁]
  · rw [fderiv_fderiv_comp hV hΓ2 hA (hKV hAz), fderiv_fderiv_comp hV hΓ2 hB (hKV hBz)]
    have hS := norm_secondComp_sub_le (Γ := Γ) (A := A) (B := B) (z := z) hM m1 m2 l1 l2 hδ₀
      hL₁0 hL₂0 hA1 hB1 hB2 (le_refl δ₁) (le_refl δ₂)
    refine hS.trans ?_
    have hc1 : |M₁| ≤ C := by rw [hC]; linarith
    have hc2 : (L₁ : ℝ) ≤ C := by rw [hC]; linarith
    have hc3 : (L₂ : ℝ) ≤ C := by rw [hC]; linarith
    have hc4 : 2 * |M₂| ≤ C := by rw [hC]; linarith
    have hMM : M ^ 2 + M ≤ (1 + M) ^ 2 := by nlinarith
    have hM1' : M ≤ (1 + M) ^ 2 := by nlinarith
    have h1' : (1 : ℝ) ≤ (1 + M) ^ 2 := by nlinarith
    have a1 : (L₂ * M ^ 2 + L₁ * M) * δ₀ ≤ C * (1 + M) ^ 2 * δ₀ := by
      have : (L₂ : ℝ) * M ^ 2 + L₁ * M ≤ C * (1 + M) ^ 2 :=
        calc (L₂ : ℝ) * M ^ 2 + L₁ * M ≤ C * M ^ 2 + C * M :=
              add_le_add (mul_le_mul_of_nonneg_right hc3 (sq_nonneg M))
                (mul_le_mul_of_nonneg_right hc2 hM)
          _ = C * (M ^ 2 + M) := by ring
          _ ≤ C * (1 + M) ^ 2 := mul_le_mul_of_nonneg_left hMM hC0
      exact mul_le_mul_of_nonneg_right this hδ₀
    have a2 : 2 * |M₂| * M * δ₁ ≤ C * (1 + M) ^ 2 * δ₁ := by
      have : 2 * |M₂| * M ≤ C * (1 + M) ^ 2 :=
        (mul_le_mul_of_nonneg_right hc4 hM).trans (mul_le_mul_of_nonneg_left hM1' hC0)
      exact mul_le_mul_of_nonneg_right this hδ₁
    have a3 : |M₁| * δ₂ ≤ C * (1 + M) ^ 2 * δ₂ := by
      have : |M₁| ≤ C * (1 + M) ^ 2 := by
        calc |M₁| ≤ C * 1 := by rw [mul_one]; exact hc1
          _ ≤ C * (1 + M) ^ 2 := mul_le_mul_of_nonneg_left h1' hC0
      exact mul_le_mul_of_nonneg_right this hδ₂
    have e : C * (1 + M) ^ 2 * (δ₀ + δ₁ + δ₂) =
        C * (1 + M) ^ 2 * δ₀ + C * (1 + M) ^ 2 * δ₁ + C * (1 + M) ^ 2 * δ₂ := by ring
    rw [e]
    linarith

/-- **Bounds on the jets of a composition**: with the constants of `comp_jet_sub_le`'s setting, the
value, first and second derivative of `Γ ∘ B` are bounded in terms of `M`. -/
theorem comp_jet_norm_le {Γ : F → G} {V K : Set F} (hV : IsOpen V) (hΓ : ContDiffOn ℝ 3 Γ V)
    (hKV : K ⊆ V) (hKc : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : E → F), ContDiff ℝ 2 B → ∀ z : E, B z ∈ K → ∀ M : ℝ, 0 ≤ M →
      ‖fderiv ℝ B z‖ ≤ M → ‖fderiv ℝ (fderiv ℝ B) z‖ ≤ M →
        ‖Γ (B z)‖ ≤ C ∧ ‖fderiv ℝ (fun y => Γ (B y)) z‖ ≤ C * (1 + M) ^ 2 ∧
        ‖fderiv ℝ (fderiv ℝ (fun y => Γ (B y))) z‖ ≤ C * (1 + M) ^ 2 := by
  have hd1 : ContDiffOn ℝ 2 (fderiv ℝ Γ) V := hΓ.fderiv_of_isOpen hV (by norm_num)
  have hd2 : ContDiffOn ℝ 1 (fderiv ℝ (fderiv ℝ Γ)) V := hd1.fderiv_of_isOpen hV (by norm_num)
  obtain ⟨M₀, hM₀⟩ := hKc.exists_bound_of_continuousOn (hΓ.continuousOn.mono hKV)
  obtain ⟨M₁, hM₁⟩ := hKc.exists_bound_of_continuousOn (hd1.continuousOn.mono hKV)
  obtain ⟨M₂, hM₂⟩ := hKc.exists_bound_of_continuousOn (f := fderiv ℝ (fderiv ℝ Γ)) (hd2.continuousOn.mono hKV)
  refine ⟨|M₀| + |M₁| + |M₂|, by positivity, fun B hB z hBz M hM hB1 hB2 => ?_⟩
  have hΓ2 : ContDiffOn ℝ 2 Γ V := hΓ.of_le (by norm_num)
  have m0 := (hM₀ _ hBz).trans (le_abs_self _)
  have m1 := (hM₁ _ hBz).trans (le_abs_self _)
  have m2 := (hM₂ _ hBz).trans (le_abs_self _)
  have hM0' := abs_nonneg M₀
  have hM1' := abs_nonneg M₁
  have hM2' := abs_nonneg M₂
  have h1' : (1 : ℝ) ≤ (1 + M) ^ 2 := by nlinarith
  have hM1'' : M ≤ (1 + M) ^ 2 := by nlinarith
  have hMM : M ^ 2 + M ≤ (1 + M) ^ 2 := by nlinarith
  refine ⟨by linarith, ?_, ?_⟩
  · rw [fderiv_comp_eq hV hΓ2 hB (hKV hBz)]
    refine ((fderiv ℝ Γ (B z)).opNorm_comp_le _).trans ?_
    have := mul_le_mul m1 hB1 (norm_nonneg _) hM1'
    nlinarith [mul_le_mul_of_nonneg_left hM1'' (by positivity : (0 : ℝ) ≤ |M₀| + |M₁| + |M₂|)]
  · rw [fderiv_fderiv_comp hV hΓ2 hB (hKV hBz)]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
    rw [secondComp_apply]
    have hw := norm_nonneg w
    have t1 : ‖(fderiv ℝ Γ (B z)).comp (fderiv ℝ (fderiv ℝ B) z w)‖ ≤ |M₁| * (M * ‖w‖) :=
      ((fderiv ℝ Γ (B z)).opNorm_comp_le _).trans (mul_le_mul m1
        (((fderiv ℝ (fderiv ℝ B) z).le_opNorm w).trans (mul_le_mul_of_nonneg_right hB2 hw))
        (norm_nonneg _) hM1')
    have t2 : ‖(fderiv ℝ (fderiv ℝ Γ) (B z) (fderiv ℝ B z w)).comp (fderiv ℝ B z)‖ ≤
        |M₂| * (M * ‖w‖) * M := by
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul ?_ hB1 (norm_nonneg _)
        (by positivity))
      exact ((fderiv ℝ (fderiv ℝ Γ) (B z)).le_opNorm _).trans (mul_le_mul m2
        (((fderiv ℝ B z).le_opNorm w).trans (mul_le_mul_of_nonneg_right hB1 hw)) (norm_nonneg _)
        hM2')
    refine (norm_add_le _ _).trans ((add_le_add t1 t2).trans ?_)
    have e1 : |M₁| * (M * ‖w‖) + |M₂| * (M * ‖w‖) * M = (|M₁| * M + |M₂| * M ^ 2) * ‖w‖ := by ring
    rw [e1]
    refine mul_le_mul_of_nonneg_right ?_ hw
    nlinarith [mul_le_mul_of_nonneg_left hM1'' hM1', mul_le_mul_of_nonneg_left hMM hM2',
      mul_nonneg hM0' (sq_nonneg (1 + M)), sq_nonneg M, mul_nonneg hM2' hM]

end

end RenewalGeometry.SecondOrderChainRule
