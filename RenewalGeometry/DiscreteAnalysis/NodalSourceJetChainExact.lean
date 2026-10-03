/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.NodalSourceTransferExact

/-!
# The `O(hK³)` clause of the nodal source transfer
  (`lem:nodal-source-transfer`, `eq:growing-derivatives`, `eq:nodal-source-transfer`;
  Einstein–Standard-Model action-closure manuscript)

`RenewalGeometry.DiscreteAnalysis.NodalSourceTransferExact` proves the transfer estimate
`‖f‖_{L²(Q)} ≤ √2 ‖𝖲_h f‖_{0,h;Q'} + √2 |Q'|^{1/2} h ‖∂f‖_{L^∞(Q')}`.  This file derives the
last clause of the lemma — *for the complete physical Euler density of a field satisfying
`eq:growing-derivatives`, the last term is `O(hK³)`* — from the paper's assumptions instead of
assuming the derivative bound.

## Model of the Euler density

The bosonic Euler density has differential degree at most two (the Dirac density at most one),
so it is a function of the second jet: `𝓔₀(y)(x) = F(j²y(x))`, where
`j²y(x) = (y(x), Dy(x), D²y(x))` (`jet2`, valued in `Jet2`) and `F` is `C¹` on an open set `U`
containing a compact jet chart `𝒦` in which the jet of the field stays (the fixed coefficient
chart).  The field `y` is `C³` near every point of the buffered slab `Q'` and satisfies the
growing-derivative bounds of `eq:growing-derivatives` for `1 ≤ |α| ≤ 3`, literally on the
coordinate partial derivatives:
`‖∂_{α₁} ⋯ ∂_{αₙ} y(x)‖ = ‖Dⁿy(x)(e_{α₁}, …, e_{αₙ})‖ ≤ C Kⁿ`.

## Results

* `norm_le_card_pow_mul_of_basis` — a continuous `n`-linear map on `(ℝ^d, sup)` with all
  coordinate values `‖f(e_{α₁},…,e_{αₙ})‖ ≤ B` has `‖f‖ ≤ dⁿ B` (partial-derivative bounds
  control the Fréchet norm).
* `hasFDerivAt_jet2`, `norm_jet2Deriv_le` — chain rule for the jet map and
  `‖D(j²y)(x)‖ ≤ max(‖Dy‖, ‖D²y‖, ‖D³y‖) ≤ d³ C K³` for `K ≥ 1`.
* `euler_density_derivative_bound` — there is `M ≥ 0`, depending only on `F` and the chart `𝒦`
  (not on `y`, `h`, `K`), such that `‖D(F ∘ j²y)(x)‖ ≤ M d³ C K³` on `Q'`.
* `eLpNorm_euler_density_le_nodalNorm` — **`lem:nodal-source-transfer` with its `O(hK³)` clause**:
  `‖F ∘ j²y‖_{L²(Q)} ≤ √2 ‖𝖲_h(F ∘ j²y)‖_{0,h;Q'} + √2 |Q'|^{1/2} · M d³ C · h K³`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace RenewalGeometry

namespace NodalSourceTransfer

variable {d : ℕ}
variable {Fy : Type*} [NormedAddCommGroup Fy] [NormedSpace ℝ Fy]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-! ### Partial derivatives control the Fréchet norm -/

/-- A continuous `n`-linear map on `(ℝ^d, sup norm)` whose values on all tuples of coordinate
vectors are bounded by `B ≥ 0` has operator norm at most `dⁿ B`. -/
theorem norm_le_card_pow_mul_of_basis {n : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin d → ℝ) Fy) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ α : Fin n → Fin d, ‖f (fun i => Pi.single (α i) (1 : ℝ))‖ ≤ B) :
    ‖f‖ ≤ (d : ℝ) ^ n * B := by
  classical
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
  have hm : m = fun i => ∑ k, m i k • (Pi.single k (1 : ℝ) : Fin d → ℝ) := by
    funext i
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hexp : f m = ∑ r : Fin n → Fin d,
      (∏ i, m i (r i)) • f (fun i => Pi.single (r i) (1 : ℝ)) := by
    conv_lhs => rw [hm]
    rw [ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    exact f.map_smul_univ (fun i => m i (r i)) (fun i => Pi.single (r i) (1 : ℝ))
  rw [hexp]
  calc ‖∑ r : Fin n → Fin d, (∏ i, m i (r i)) • f (fun i => Pi.single (r i) (1 : ℝ))‖
      ≤ ∑ r : Fin n → Fin d, ‖(∏ i, m i (r i)) • f (fun i => Pi.single (r i) (1 : ℝ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _r : Fin n → Fin d, (∏ i, ‖m i‖) * B := by
        refine Finset.sum_le_sum fun r _ => ?_
        rw [norm_smul, norm_prod]
        refine mul_le_mul (Finset.prod_le_prod (fun i _ => norm_nonneg _)
          fun i _ => norm_le_pi_norm (m i) (r i)) (h r) (norm_nonneg _)
          (Finset.prod_nonneg fun i _ => norm_nonneg _)
    _ = (d : ℝ) ^ n * B * ∏ i, ‖m i‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-! ### The second jet and its derivative -/

/-- The second-jet space `J² = Fy × L¹(ℝ^d; Fy) × L²(ℝ^d; Fy)`. -/
abbrev Jet2 (d : ℕ) (Fy : Type*) [NormedAddCommGroup Fy] [NormedSpace ℝ Fy] :=
  ContinuousMultilinearMap ℝ (fun _ : Fin 0 => Fin d → ℝ) Fy ×
    ContinuousMultilinearMap ℝ (fun _ : Fin 1 => Fin d → ℝ) Fy ×
      ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Fin d → ℝ) Fy

/-- The second jet `j²y(x) = (y(x), Dy(x), D²y(x))` of a field. -/
noncomputable def jet2 (y : (Fin d → ℝ) → Fy) (x : Fin d → ℝ) : Jet2 d Fy :=
  (iteratedFDeriv ℝ 0 y x, iteratedFDeriv ℝ 1 y x, iteratedFDeriv ℝ 2 y x)

/-- The derivative of the jet map, `D(j²y)(x) = (D(D⁰y), D(D¹y), D(D²y))`. -/
noncomputable def jet2Deriv (y : (Fin d → ℝ) → Fy) (x : Fin d → ℝ) :
    (Fin d → ℝ) →L[ℝ] Jet2 d Fy :=
  (fderiv ℝ (iteratedFDeriv ℝ 0 y) x).prod
    ((fderiv ℝ (iteratedFDeriv ℝ 1 y) x).prod (fderiv ℝ (iteratedFDeriv ℝ 2 y) x))

/-- Chain rule for the jet map of a `C³` field. -/
theorem hasFDerivAt_jet2 {y : (Fin d → ℝ) → Fy} {x : Fin d → ℝ} (hy : ContDiffAt ℝ 3 y x) :
    HasFDerivAt (jet2 y) (jet2Deriv y x) x := by
  have h0 := (hy.differentiableAt_iteratedFDeriv (m := 0) (by norm_num)).hasFDerivAt
  have h1 := (hy.differentiableAt_iteratedFDeriv (m := 1) (by norm_num)).hasFDerivAt
  have h2 := (hy.differentiableAt_iteratedFDeriv (m := 2) (by norm_num)).hasFDerivAt
  exact h0.prodMk (h1.prodMk h2)

/-- `‖D(j²y)(x)‖ ≤ max(‖Dy(x)‖, ‖D²y(x)‖, ‖D³y(x)‖)`. -/
theorem norm_jet2Deriv_le (y : (Fin d → ℝ) → Fy) (x : Fin d → ℝ) {L : ℝ}
    (h1 : ‖iteratedFDeriv ℝ 1 y x‖ ≤ L) (h2 : ‖iteratedFDeriv ℝ 2 y x‖ ≤ L)
    (h3 : ‖iteratedFDeriv ℝ 3 y x‖ ≤ L) : ‖jet2Deriv y x‖ ≤ L := by
  unfold jet2Deriv
  rw [ContinuousLinearMap.opNorm_prod, norm_prod_le_iff, ContinuousLinearMap.opNorm_prod,
    norm_prod_le_iff]
  simp only
  rw [norm_fderiv_iteratedFDeriv, norm_fderiv_iteratedFDeriv, norm_fderiv_iteratedFDeriv]
  exact ⟨h1, h2, h3⟩

/-- `eq:growing-derivatives` for `1 ≤ n ≤ 3` (coordinate partial derivatives) gives
`‖D(j²y)(x)‖ ≤ d³ C K³` for `K ≥ 1`. -/
theorem norm_jet2Deriv_le_growing (y : (Fin d → ℝ) → Fy) (x : Fin d → ℝ) {C K : ℝ}
    (hC : 0 ≤ C) (hK : 1 ≤ K)
    (hgrow : ∀ n, 1 ≤ n → n ≤ 3 → ∀ α : Fin n → Fin d,
      ‖iteratedFDeriv ℝ n y x (fun i => Pi.single (α i) (1 : ℝ))‖ ≤ C * K ^ n) :
    ‖jet2Deriv y x‖ ≤ (d : ℝ) ^ 3 * C * K ^ 3 := by
  have hK0 : 0 ≤ K := by linarith
  have hn : ∀ n, 1 ≤ n → n ≤ 3 → ‖iteratedFDeriv ℝ n y x‖ ≤ (d : ℝ) ^ 3 * C * K ^ 3 := by
    intro n hn1 hn3
    have hb := norm_le_card_pow_mul_of_basis (iteratedFDeriv ℝ n y x)
      (by positivity : 0 ≤ C * K ^ n) (hgrow n hn1 hn3)
    refine hb.trans ?_
    have hKn : K ^ n ≤ K ^ 3 := pow_le_pow_right₀ hK hn3
    have hdn : (d : ℝ) ^ n ≤ (d : ℝ) ^ 3 := by
      rcases Nat.eq_zero_or_pos d with hd | hd
      · subst hd
        simp [zero_pow (by omega : n ≠ 0)]
      · exact pow_le_pow_right₀ (by exact_mod_cast hd) hn3
    calc (d : ℝ) ^ n * (C * K ^ n) ≤ (d : ℝ) ^ 3 * (C * K ^ 3) := by
          gcongr
      _ = (d : ℝ) ^ 3 * C * K ^ 3 := by ring
  exact norm_jet2Deriv_le y x (hn 1 le_rfl (by norm_num)) (hn 2 (by norm_num) (by norm_num))
    (hn 3 (by norm_num) le_rfl)

/-! ### The Euler density `F ∘ j²y` -/

/-- **Derivative bound for the Euler density.**  Let `F` be `C¹` on an open set `U` of the jet
space containing a compact jet chart `𝒦`.  There is `M ≥ 0`, depending only on `F` and `𝒦`,
such that for every field `y` which is `C³` near the buffered slab `Q'`, has its second jet in
`𝒦` on `Q'` and satisfies the growing-derivative bounds `eq:growing-derivatives`
(`‖∂^α y‖ ≤ C K^{|α|}`, `1 ≤ |α| ≤ 3`, `K ≥ 1`), the density `𝓔₀ = F ∘ j²y` is differentiable on
`Q'` with `‖D𝓔₀(x)‖ ≤ M d³ C K³`. -/
theorem euler_density_derivative_bound (F : Jet2 d Fy → G) {U 𝒦 : Set (Jet2 d Fy)}
    (hU : IsOpen U) (h𝒦 : IsCompact 𝒦) (h𝒦U : 𝒦 ⊆ U) (hF : ContDiffOn ℝ 1 F U) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (Q' : Set (Fin d → ℝ)) (y : (Fin d → ℝ) → Fy) (C K : ℝ),
      0 ≤ C → 1 ≤ K →
      (∀ x ∈ Q', ContDiffAt ℝ 3 y x) → (∀ x ∈ Q', jet2 y x ∈ 𝒦) →
      (∀ x ∈ Q', ∀ n, 1 ≤ n → n ≤ 3 → ∀ α : Fin n → Fin d,
        ‖iteratedFDeriv ℝ n y x (fun i => Pi.single (α i) (1 : ℝ))‖ ≤ C * K ^ n) →
      ∀ x ∈ Q', HasFDerivAt (F ∘ jet2 y) ((fderiv ℝ F (jet2 y x)).comp (jet2Deriv y x)) x ∧
        ‖(fderiv ℝ F (jet2 y x)).comp (jet2Deriv y x)‖ ≤ M * (d : ℝ) ^ 3 * C * K ^ 3 := by
  have hcont : ContinuousOn (fun p => fderiv ℝ F p) 𝒦 :=
    (hF.continuousOn_fderiv_of_isOpen hU le_rfl).mono h𝒦U
  obtain ⟨M₀, hM₀'⟩ := h𝒦.exists_bound_of_continuousOn
    (ContinuousOn.norm (f := fun p => fderiv ℝ F p) hcont)
  have hM₀ : ∀ p ∈ 𝒦, ‖fderiv ℝ F p‖ ≤ M₀ := fun p hp => by
    simpa using hM₀' p hp
  refine ⟨max M₀ 0, le_max_right _ _, ?_⟩
  intro Q' y C K hC hK hy hjet hgrow x hx
  have hFdiff : DifferentiableAt ℝ F (jet2 y x) :=
    (hF.contDiffAt (hU.mem_nhds (h𝒦U (hjet x hx)))).differentiableAt (by norm_num)
  refine ⟨hFdiff.hasFDerivAt.comp x (hasFDerivAt_jet2 (hy x hx)), ?_⟩
  have hJ := norm_jet2Deriv_le_growing y x hC hK (hgrow x hx)
  have hM : ‖fderiv ℝ F (jet2 y x)‖ ≤ max M₀ 0 := (hM₀ _ (hjet x hx)).trans (le_max_left _ _)
  calc ‖(fderiv ℝ F (jet2 y x)).comp (jet2Deriv y x)‖
      ≤ ‖fderiv ℝ F (jet2 y x)‖ * ‖jet2Deriv y x‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ max M₀ 0 * ((d : ℝ) ^ 3 * C * K ^ 3) :=
        mul_le_mul hM hJ (ContinuousLinearMap.opNorm_nonneg _) (le_max_right _ _)
    _ = max M₀ 0 * (d : ℝ) ^ 3 * C * K ^ 3 := by ring

/-- **`lem:nodal-source-transfer`, including the `O(hK³)` clause.**  For the Euler density
`𝓔₀ = F ∘ j²y` of `euler_density_derivative_bound` (with `F` `C¹` near a compact jet chart) and a
field satisfying `eq:growing-derivatives` on the buffered slab `Q'` (`K ≥ 1`), if every cell of
`h ℤ^d` meeting `Q` lies in `Q'`, then
`‖𝓔₀‖_{L²(Q)} ≤ √2 ‖𝖲_h 𝓔₀‖_{0,h;Q'} + √2 |Q'|^{1/2} · (M d³ C) · h K³`,
with `M` depending only on `F` and the chart. -/
theorem eLpNorm_euler_density_le_nodalNorm (F : Jet2 d Fy → G) {U 𝒦 : Set (Jet2 d Fy)}
    (hU : IsOpen U) (h𝒦 : IsCompact 𝒦) (h𝒦U : 𝒦 ⊆ U) (hF : ContDiffOn ℝ 1 F U) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (Q Q' : Set (Fin d → ℝ)) (y : (Fin d → ℝ) → Fy) (C K h : ℝ),
      0 < h → 0 ≤ C → 1 ≤ K →
      (∀ k, (cell h k ∩ Q).Nonempty → cell h k ⊆ Q') →
      (∀ x ∈ Q', ContDiffAt ℝ 3 y x) → (∀ x ∈ Q', jet2 y x ∈ 𝒦) →
      (∀ x ∈ Q', ∀ n, 1 ≤ n → n ≤ 3 → ∀ α : Fin n → Fin d,
        ‖iteratedFDeriv ℝ n y x (fun i => Pi.single (α i) (1 : ℝ))‖ ≤ C * K ^ n) →
      eLpNorm (F ∘ jet2 y) 2 (volume.restrict Q) ≤
        (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) * nodalMassSq h Q' (F ∘ jet2 y) ^ (1 / 2 : ℝ) +
          (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) * volume Q' ^ (1 / 2 : ℝ) *
            ENNReal.ofReal ((M * (d : ℝ) ^ 3 * C) * h * K ^ 3) := by
  obtain ⟨M, hM0, hM⟩ := euler_density_derivative_bound F hU h𝒦 h𝒦U hF
  refine ⟨M, hM0, ?_⟩
  intro Q Q' y C K h hh hC hK hbuf hy hjet hgrow
  have hder := hM Q' y C K hC hK hy hjet hgrow
  refine eLpNorm_le_nodalNorm_growing (CE := M * (d : ℝ) ^ 3 * C) hh hbuf
    (f' := fun x => (fderiv ℝ F (jet2 y x)).comp (jet2Deriv y x))
    (fun x hx => (hder x hx).1.hasFDerivWithinAt) (fun x hx => ?_)
  have := (hder x hx).2
  calc ‖(fderiv ℝ F (jet2 y x)).comp (jet2Deriv y x)‖ ≤ M * (d : ℝ) ^ 3 * C * K ^ 3 := this
    _ = M * (d : ℝ) ^ 3 * C * K ^ 3 := rfl

end NodalSourceTransfer

end RenewalGeometry
