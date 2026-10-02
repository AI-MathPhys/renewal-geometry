/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.PeriodicGridTimeDifferentiatedConsistency

/-!
# Time-differentiated interpolation estimates of every order
  (`lem:supp-open-interpolation`, last assertion; emergent-spacetime manuscript, supplement)

`DiscreteAnalysis/PeriodicGridTimeDifferentiatedConsistency.lean` differentiates the five estimates
of `lem:supp-open-interpolation` once in time.  Here we treat **every order `k`**.  A grid history
with `k` controlled time derivatives is encoded by its jet `v : ℕ → ℝ → …`, `v 0 = u_h`, with
`∂_t v_i = v_{i+1}` (`i < k`) on an open time set `O` (`IsJet`); `iteratedDeriv` jets of a `C^k`
history are an instance (`isJet_iteratedDeriv`).

* `iteratedDeriv_eq_of_chain`: a general principle — if `G_0, G_1, …` satisfy `∂_t G_j = G_{j+1}`
  on an open set, then `∂_t^j G_0 = G_j` there.
* Sampling and differences (linear errors): `∂_t^k` of the error is the same error of the `k`-th
  derivative (`sampling_error_iteratedDeriv`, `sampling_stable_iteratedDeriv`,
  `difference_consistency_{Dp,Dm,D0}_iteratedDeriv`).
* `product_consistency_iteratedDeriv` (**general Leibniz rule**): `∂_t^k[𝓘_h(u w) - 𝓘_h u 𝓘_h w]` is
  `Σ_i C(k,i) [𝓘_h(u^{(i)} w^{(k-i)}) - 𝓘_h u^{(i)} 𝓘_h w^{(k-i)}]`, and
  `‖·‖_{H^r} ≤ C h Σ_i C(k,i) ‖u^{(i)}‖_{r+1,h} ‖w^{(k-i)}‖_{r+1,h}`.
* `jetMap A k` (**Faà di Bruno jet map**): `Φ_0(z_0) = A(z_0)`,
  `Φ_{k+1}(z_0,…,z_{k+1}) = DΦ_k(z_0,…,z_k)(z_1,…,z_{k+1})`, so that
  `∂_t^k A(γ(t)) = Φ_k(γ, γ', …, γ^{(k)})` (`iteratedDeriv_comp_eq_jetMap`).  It is analytic on
  `{z_0 ∈ ball}` (`analyticOnNhd_jetMap`) and weighted homogeneous,
  `Φ_k(z_0, λz_1, …, λ^k z_k) = λ^k Φ_k(z)` (`jetMap_scale`).
* `composition_consistency_iteratedDeriv`: for `A` analytic at the constant base point `c`, on the
  small chart (`Σ_j ‖u_j(s) - c_j‖_{r+1,h} ≤ δ` for `s ∈ O`), the `k`-th time derivative of
  `y ↦ 𝓘_h A(u_h)(y) - A(𝓘_h u_h)(y)` is the composition error of the analytic jet map `Φ_k` on the
  grid jet, and
  `‖∂_t^k[𝓘_h A(u_h) - A(𝓘_h u_h)]‖²_{H^r} ≤ C h² (Σ_{i=1}^k ‖u^{(i)}‖_{r+1,h}^{1/i})^{2k}`
  with **no smallness assumption on the time derivatives** (each `u^{(i)}` enters with its
  Faà di Bruno weight `i`; for `k = 1` this is `composition_consistency_deriv`).

In every case one spatial order is spent on each controlled time derivative exactly through the
grid `H^{r+1}` norms of the time derivatives appearing on the right.
-/

open Finset ComplexConjugate UnitAddTorus
open scoped BigOperators Real Topology

namespace RenewalGeometry.PeriodicGridSobolev

namespace HigherTimeConsistency

open LatticeTorusPlancherel Sampling RenewalGeometry.PeriodicGridSobolev.Composition
  RenewalGeometry.PeriodicGridSobolev.TimeConsistency

set_option linter.unusedSectionVars false

noncomputable section

/-! ### Iterated derivatives from derivative chains -/

/-- If `∂_t G_j = G_{j+1}` on an open set `O` for `j < k`, then `∂_t^j G_0 = G_j` on `O`, `j ≤ k`. -/
theorem iteratedDeriv_eq_of_chain {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {O : Set ℝ} (hO : IsOpen O) (G : ℕ → ℝ → F) (k : ℕ)
    (hG : ∀ j < k, ∀ s ∈ O, HasDerivAt (G j) (G (j + 1) s) s) :
    ∀ j ≤ k, ∀ s ∈ O, iteratedDeriv j (G 0) s = G j s := by
  intro j
  induction j with
  | zero => intro _ s _; simp
  | succ j ih =>
    intro hj s hs
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv j (G 0) =ᶠ[𝓝 s] G j :=
      Filter.eventually_of_mem (hO.mem_nhds hs) fun s' hs' => ih (by omega) s' hs'
    rw [heq.deriv_eq]
    exact (hG j (by omega) s hs).deriv

/-- A jet of a history with `k` controlled time derivatives on `O`: `∂_t v_i = v_{i+1}`, `i < k`. -/
def IsJet {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (O : Set ℝ) (k : ℕ)
    (v : ℕ → ℝ → F) : Prop :=
  ∀ i < k, ∀ s ∈ O, HasDerivAt (v i) (v (i + 1) s) s

/-- The `iteratedDeriv` jet of a `C^k` history is a jet. -/
theorem isJet_iteratedDeriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
    {u : ℝ → F} (hu : ContDiff ℝ k u) (O : Set ℝ) :
    IsJet O k (fun i => iteratedDeriv i u) := by
  intro i hi s _
  have hd := (hu.differentiable_iteratedDeriv i (by exact_mod_cast hi)) s
  show HasDerivAt (iteratedDeriv i u) (iteratedDeriv (i + 1) u s) s
  rw [iteratedDeriv_succ]
  exact hd.hasDerivAt

/-- A jet stays a jet under a continuous linear map applied pointwise. -/
theorem IsJet.map {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] {O : Set ℝ} {k : ℕ} {v : ℕ → ℝ → F} (hv : IsJet O k v) (L : F →L[ℝ] G) :
    IsJet O k (fun i s => L (v i s)) :=
  fun i hi s hs => L.hasFDerivAt.comp_hasDerivAt s (hv i hi s hs)

/-! ### Linear errors: sampling and differences -/

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

variable {N : ℕ} [NeZero N]

/-- **Order-`k` time-differentiated sampling estimate** (`eq:supp-open-sampling-estimate`, with
the `h^j`, `H^{r+j}` refinement): for a continuum history with `k` controlled time derivatives on
an open time set `O`, `∂_t^k(𝒫_h f - f) = 𝒫_h f^{(k)} - f^{(k)}`, with
`‖·‖²_{H^r} ≤ C h^{2j} ‖f^{(k)}‖²_{H^{r+j}}` (`C` independent of `h`, `k` and the history). -/
theorem sampling_error_iteratedDeriv (r j : ℕ) (hrj : 2 ≤ r + j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (k : ℕ) {O : Set ℝ}, IsOpen O →
      ∀ (f : ℕ → ℝ → C(UnitAddTorus (Fin 3), ℂ)), IsJet O k f → ∀ t ∈ O,
      iteratedDeriv k (fun s => projL N (f 0 s) - f 0 s) t = projL N (f k t) - f k t ∧
      (Summable (fun n => trigWeight (r + j) n * ‖mFourierCoeff ⇑(f k t) n‖ ^ 2) →
        trigSobSq r ⇑(projL N (f k t) - f k t) ≤
          C * (((N : ℝ) ^ 2) ^ j)⁻¹ * trigSobSq (r + j) ⇑(f k t)) := by
  obtain ⟨C, hC, hE⟩ := sampling_error r j hrj
  refine ⟨C, hC, fun N _ k O hO f hf t ht => ⟨?_, fun hs => (hE N (f k t) hs).2⟩⟩
  exact iteratedDeriv_eq_of_chain hO (fun i s => projL N (f i s) - f i s) k
    (fun i hi s hs => (hasDerivAt_proj (hf i hi s hs)).sub (hf i hi s hs)) k le_rfl t ht

/-- **Order-`k` time-differentiated sampling stability**: `∂_t^k 𝒫_h f = 𝒫_h f^{(k)}` and
`‖𝒫_h f^{(k)}‖²_{H^r} ≤ C ‖f^{(k)}‖²_{H^r}` (`r ≥ 2`). -/
theorem sampling_stable_iteratedDeriv (r : ℕ) (hr : 2 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (k : ℕ) {O : Set ℝ}, IsOpen O →
      ∀ (f : ℕ → ℝ → C(UnitAddTorus (Fin 3), ℂ)), IsJet O k f → ∀ t ∈ O,
      iteratedDeriv k (fun s => projL N (f 0 s)) t = projL N (f k t) ∧
      (Summable (fun n => trigWeight r n * ‖mFourierCoeff ⇑(f k t) n‖ ^ 2) →
        trigSobSq r ⇑(projL N (f k t)) ≤ C * trigSobSq r ⇑(f k t)) := by
  obtain ⟨C, hC, hE⟩ := sampling_stable r hr
  refine ⟨C, hC, fun N _ k O hO f hf t ht => ⟨?_, fun hs => (hE N (f k t) hs).2⟩⟩
  exact iteratedDeriv_eq_of_chain hO (fun i s => projL N (f i s)) k
    (fun i hi s hs => hasDerivAt_proj (hf i hi s hs)) k le_rfl t ht

/-- **Order-`k` time-differentiated difference consistency** for `D_i⁺`:
`∂_t^k(𝓘_h D_i⁺ u_h - ∂_i 𝓘_h u_h) = 𝓘_h D_i⁺ u_h^{(k)} - ∂_i 𝓘_h u_h^{(k)}`, bounded by
`(π²/4)^{r+2} h² ‖u_h^{(k)}‖²_{r+2,h}`. -/
theorem difference_consistency_Dp_iteratedDeriv (r : ℕ) (i : Fin 3) (k : ℕ) {O : Set ℝ}
    (hO : IsOpen O) {v : ℕ → ℝ → Grid N → ℂ} (hv : IsJet O k v) {t : ℝ} (ht : t ∈ O) :
    iteratedDeriv k (fun s => interp (Dp i (v 0 s)) - interp (specD i (v 0 s))) t =
      interp (Dp i (v k t)) - interp (specD i (v k t)) ∧
    trigSobSq r ⇑(interp (Dp i (v k t)) - interp (specD i (v k t))) ≤
      ((π ^ 2 / 4) ^ (r + 2) * (((N : ℝ) ^ 2)⁻¹)) * sobSq (r + 2) (v k t) :=
  ⟨iteratedDeriv_eq_of_chain hO (fun l s => interp (Dp i (v l s)) - interp (specD i (v l s))) k
    (fun l hl s hs => ((difference_consistency_Dp_deriv r i (hv l hl s hs)).1)) k le_rfl t ht,
    difference_consistency_Dp r i _⟩

/-- **Order-`k` time-differentiated difference consistency** for `D_i⁻`. -/
theorem difference_consistency_Dm_iteratedDeriv (r : ℕ) (i : Fin 3) (k : ℕ) {O : Set ℝ}
    (hO : IsOpen O) {v : ℕ → ℝ → Grid N → ℂ} (hv : IsJet O k v) {t : ℝ} (ht : t ∈ O) :
    iteratedDeriv k (fun s => interp (Dm i (v 0 s)) - interp (specD i (v 0 s))) t =
      interp (Dm i (v k t)) - interp (specD i (v k t)) ∧
    trigSobSq r ⇑(interp (Dm i (v k t)) - interp (specD i (v k t))) ≤
      ((π ^ 2 / 4) ^ (r + 2) * (((N : ℝ) ^ 2)⁻¹)) * sobSq (r + 2) (v k t) :=
  ⟨iteratedDeriv_eq_of_chain hO (fun l s => interp (Dm i (v l s)) - interp (specD i (v l s))) k
    (fun l hl s hs => ((difference_consistency_Dm_deriv r i (hv l hl s hs)).1)) k le_rfl t ht,
    difference_consistency_Dm r i _⟩

/-- **Order-`k` time-differentiated difference consistency** for `D_i⁰`. -/
theorem difference_consistency_D0_iteratedDeriv (r : ℕ) (i : Fin 3) (k : ℕ) {O : Set ℝ}
    (hO : IsOpen O) {v : ℕ → ℝ → Grid N → ℂ} (hv : IsJet O k v) {t : ℝ} (ht : t ∈ O) :
    iteratedDeriv k (fun s => interp (D0 i (v 0 s)) - interp (specD i (v 0 s))) t =
      interp (D0 i (v k t)) - interp (specD i (v k t)) ∧
    trigSobSq r ⇑(interp (D0 i (v k t)) - interp (specD i (v k t))) ≤
      ((π ^ 2 / 4) ^ (r + 2) * (((N : ℝ) ^ 2)⁻¹)) * sobSq (r + 2) (v k t) :=
  ⟨iteratedDeriv_eq_of_chain hO (fun l s => interp (D0 i (v l s)) - interp (specD i (v l s))) k
    (fun l hl s hs => ((difference_consistency_D0_deriv r i (hv l hl s hs)).1)) k le_rfl t ht,
    difference_consistency_D0 r i _⟩

/-! ### Products: the general Leibniz rule -/

/-- The product error `𝓘_h(u w) - (𝓘_h u)(𝓘_h w)`. -/
def productError (u w : Grid N → ℂ) : C(UnitAddTorus (Fin 3), ℂ) :=
  interp (u * w) - interp u * interp w

theorem hasDerivAt_productError {u w : ℝ → Grid N → ℂ} {u' w' : Grid N → ℂ} {t : ℝ}
    (hu : HasDerivAt u u' t) (hw : HasDerivAt w w' t) :
    HasDerivAt (fun s => productError (u s) (w s))
      (productError u' (w t) + productError (u t) w') t := by
  have h1 : HasDerivAt (fun s => interp (u s * w s)) (interp (u' * w t + u t * w')) t :=
    hasDerivAt_interp (hu.mul hw)
  have h2 := (hasDerivAt_interp hu).mul (hasDerivAt_interp hw)
  have h3 := h1.sub h2
  rw [interp_add] at h3
  unfold productError
  exact h3.congr_deriv (by abel)

theorem natCast_mul_eq_smul (n : ℕ) (F : C(UnitAddTorus (Fin 3), ℂ)) :
    (n : C(UnitAddTorus (Fin 3), ℂ)) * F = (n : ℂ) • F := by
  ext y; simp

/-- The Leibniz sum `Σ_{i ≤ j} C(j,i) [𝓘_h(v_i w_{j-i}) - 𝓘_h v_i 𝓘_h w_{j-i}]`. -/
def leibnizError (v w : ℕ → ℝ → Grid N → ℂ) (j : ℕ) (s : ℝ) : C(UnitAddTorus (Fin 3), ℂ) :=
  ∑ i ∈ range (j + 1), ((j.choose i : ℕ) : C(UnitAddTorus (Fin 3), ℂ)) *
    productError (v i s) (w (j - i) s)

theorem hasDerivAt_leibnizError {k : ℕ} {O : Set ℝ} {v w : ℕ → ℝ → Grid N → ℂ}
    (hv : IsJet O k v) (hw : IsJet O k w) {j : ℕ} (hj : j < k) {s : ℝ} (hs : s ∈ O) :
    HasDerivAt (leibnizError v w j) (leibnizError v w (j + 1) s) s := by
  have hterm : ∀ i ∈ range (j + 1), HasDerivAt
      (fun s => ((j.choose i : ℕ) : C(UnitAddTorus (Fin 3), ℂ)) * productError (v i s) (w (j - i) s))
      (((j.choose i : ℕ) : C(UnitAddTorus (Fin 3), ℂ)) *
        (productError (v (i + 1) s) (w (j - i) s) + productError (v i s) (w (j + 1 - i) s))) s := by
    intro i hi
    have hi' : i ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have h := hasDerivAt_productError (hv i (by omega) s hs) (hw (j - i) (by omega) s hs)
    rw [show j - i + 1 = j + 1 - i by omega] at h
    exact h.const_mul _
  have hsum := HasDerivAt.fun_sum hterm
  refine hsum.congr_deriv ?_
  unfold leibnizError
  rw [sum_choose_succ_mul (fun a b => productError (v a s) (w b s)) j]
  simp only [mul_add, sum_add_distrib]
  rw [add_comm]

/-- `sn` form of `product_consistency`: `‖𝓘_h(u w) - 𝓘_h u 𝓘_h w‖_{H^r} ≤ √C h ‖u‖_{r+1,h}‖w‖_{r+1,h}`. -/
theorem sn_productError_le (r : ℕ) (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (u w : Grid N → ℂ),
      sn r ⇑(productError u w) ≤ C * (N : ℝ)⁻¹ * (sobNorm (r + 1) u * sobNorm (r + 1) w) := by
  obtain ⟨C, hC, hP⟩ := product_consistency r hr
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, fun N _ u w => ?_⟩
  unfold sn productError
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  calc Real.sqrt (trigSobSq r ⇑(interp (u * w) - interp u * interp w))
      ≤ Real.sqrt (C * ((N : ℝ) ^ 2)⁻¹ * sobSq (r + 1) u * sobSq (r + 1) w) :=
        Real.sqrt_le_sqrt (hP N u w)
    _ = Real.sqrt C * (N : ℝ)⁻¹ * (sobNorm (r + 1) u * sobNorm (r + 1) w) := by
        rw [← sobNorm_sq, ← sobNorm_sq, ← inv_pow,
          show C * ((N : ℝ)⁻¹) ^ 2 * sobNorm (r + 1) u ^ 2 * sobNorm (r + 1) w ^ 2 =
            C * ((N : ℝ)⁻¹ * (sobNorm (r + 1) u * sobNorm (r + 1) w)) ^ 2 by ring,
          Real.sqrt_mul hC, Real.sqrt_sq (by
            have := Real.sqrt_nonneg (sobSq (r + 1) u)
            have := Real.sqrt_nonneg (sobSq (r + 1) w)
            unfold sobNorm; positivity)]
        ring

/-- **Order-`k` time-differentiated product consistency** (`eq:supp-open-product-consistency`,
general Leibniz rule).  For grid histories `u_h = v_0`, `w_h = w_0` with `k` controlled time
derivatives on an open time set `O` and `r ≥ 1`, at every `t ∈ O`
`∂_t^k[𝓘_h(u_h w_h) - (𝓘_h u_h)(𝓘_h w_h)] = Σ_{i ≤ k} C(k,i) [𝓘_h(u^{(i)} w^{(k-i)}) - 𝓘_h u^{(i)} 𝓘_h w^{(k-i)}]`
in `C(𝕋³)`, and with a mesh-independent `C` (independent of `k` and of the histories)
`‖∂_t^k[…]‖_{H^r} ≤ C h Σ_{i ≤ k} C(k,i) ‖u^{(i)}‖_{r+1,h} ‖w^{(k-i)}‖_{r+1,h}`. -/
theorem product_consistency_iteratedDeriv (r : ℕ) (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (k : ℕ) {O : Set ℝ}, IsOpen O →
      ∀ (v w : ℕ → ℝ → Grid N → ℂ), IsJet O k v → IsJet O k w → ∀ t ∈ O,
      iteratedDeriv k (fun s => interp (v 0 s * w 0 s) - interp (v 0 s) * interp (w 0 s)) t =
        ∑ i ∈ range (k + 1), ((k.choose i : ℕ) : C(UnitAddTorus (Fin 3), ℂ)) *
          (interp (v i t * w (k - i) t) - interp (v i t) * interp (w (k - i) t)) ∧
      sn r ⇑(∑ i ∈ range (k + 1), ((k.choose i : ℕ) : C(UnitAddTorus (Fin 3), ℂ)) *
          (interp (v i t * w (k - i) t) - interp (v i t) * interp (w (k - i) t))) ≤
        C * (N : ℝ)⁻¹ * ∑ i ∈ range (k + 1),
          (k.choose i : ℝ) * (sobNorm (r + 1) (v i t) * sobNorm (r + 1) (w (k - i) t)) := by
  obtain ⟨C, hC, hP⟩ := sn_productError_le r hr
  refine ⟨C, hC, fun N _ k O hO v w hv hw t ht => ⟨?_, ?_⟩⟩
  · have h := iteratedDeriv_eq_of_chain hO (leibnizError v w) k
      (fun j hj s hs => hasDerivAt_leibnizError hv hw hj hs) k le_rfl t ht
    have h0 : leibnizError v w 0 = fun s => interp (v 0 s * w 0 s) - interp (v 0 s) * interp (w 0 s) := by
      funext s; simp [leibnizError, productError]
    rw [h0] at h
    exact h
  · have hTP : ∀ i, IsTP (((k.choose i : ℕ) : C(UnitAddTorus (Fin 3), ℂ)) *
        (interp (v i t * w (k - i) t) - interp (v i t) * interp (w (k - i) t))) := fun i => by
      rw [natCast_mul_eq_smul]; exact (isTP_productError _ _).smul _
    refine (sn_sum_le r (range (k + 1)) hTP).2.trans ?_
    rw [mul_sum]
    refine sum_le_sum fun i _ => ?_
    rw [natCast_mul_eq_smul, sn_smul, Complex.norm_natCast]
    have := hP N (v i t) (w (k - i) t)
    unfold productError at this
    calc (k.choose i : ℝ) * sn r ⇑(interp (v i t * w (k - i) t) - interp (v i t) * interp (w (k - i) t))
        ≤ (k.choose i : ℝ) * (C * (N : ℝ)⁻¹ *
            (sobNorm (r + 1) (v i t) * sobNorm (r + 1) (w (k - i) t))) := by gcongr
      _ = _ := by ring

/-! ### Compositions: the Faà di Bruno jet map -/

section Jet

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **Faà di Bruno jet map** of `A : ℂ^ι → ℂ`: `Φ_0(z_0) = A(z_0)` and
`Φ_{k+1}(z_0, …, z_{k+1}) = DΦ_k(z_0, …, z_k)(z_1, …, z_{k+1})`; a jet is a map
`Fin (k+1) × ι → ℂ`, `(i, l) ↦ z_i(l)`.  Along a curve, `∂_t^k A(γ) = Φ_k(γ, γ', …, γ^{(k)})`. -/
def jetMap (A : (ι → ℂ) → ℂ) : (k : ℕ) → (Fin (k + 1) × ι → ℂ) → ℂ
  | 0 => fun z => A (fun l => z (0, l))
  | k + 1 => fun z => fderiv ℂ (jetMap A k) (fun q => z (q.1.castSucc, q.2))
      (fun q => z (q.1.succ, q.2))

/-- The position `z_0` of a jet. -/
def jetPos (k : ℕ) : (Fin (k + 1) × ι → ℂ) →L[ℂ] (ι → ℂ) :=
  ContinuousLinearMap.pi fun l => ContinuousLinearMap.proj ((0 : Fin (k + 1)), l)

/-- The truncation `(z_0, …, z_k)` of a jet of order `k + 1`. -/
def jetInit (k : ℕ) : (Fin (k + 2) × ι → ℂ) →L[ℂ] (Fin (k + 1) × ι → ℂ) :=
  ContinuousLinearMap.pi fun q => ContinuousLinearMap.proj (q.1.castSucc, q.2)

/-- The shift `(z_1, …, z_{k+1})` of a jet of order `k + 1`. -/
def jetTail (k : ℕ) : (Fin (k + 2) × ι → ℂ) →L[ℂ] (Fin (k + 1) × ι → ℂ) :=
  ContinuousLinearMap.pi fun q => ContinuousLinearMap.proj (q.1.succ, q.2)

theorem jetMap_succ (A : (ι → ℂ) → ℂ) (k : ℕ) (z : Fin (k + 2) × ι → ℂ) :
    jetMap A (k + 1) z = fderiv ℂ (jetMap A k) (jetInit k z) (jetTail k z) := rfl

/-- `Φ_k` is analytic wherever the position `z_0` lies in a set on which `A` is analytic. -/
theorem analyticOnNhd_jetMap {A : (ι → ℂ) → ℂ} {B : Set (ι → ℂ)} (hA : AnalyticOnNhd ℂ A B) :
    ∀ k : ℕ, AnalyticOnNhd ℂ (jetMap A k) (jetPos k ⁻¹' B) := by
  intro k
  induction k with
  | zero =>
    intro z hz
    exact (hA _ hz).comp ((jetPos 0).analyticAt z)
  | succ k ih =>
    intro z hz
    have hinit : jetInit k z ∈ jetPos k ⁻¹' B := by
      have : jetPos k (jetInit k z) = jetPos (k + 1) z := by
        funext l; rfl
      simpa [Set.mem_preimage, this] using hz
    have hg : AnalyticAt ℂ (fun z => fderiv ℂ (jetMap A k) (jetInit k z)) z :=
      (ih.fderiv _ hinit).comp ((jetInit k).analyticAt z)
    have hpair : AnalyticAt ℂ (fun z => (jetTail k z, fderiv ℂ (jetMap A k) (jetInit k z))) z :=
      ((jetTail k).analyticAt z).prod hg
    have := ((ContinuousLinearMap.apply ℂ ℂ : (Fin (k + 1) × ι → ℂ) →L[ℂ]
      ((Fin (k + 1) × ι → ℂ) →L[ℂ] ℂ) →L[ℂ] ℂ).analyticAt_bilinear _).comp hpair
    exact this

/-- The weighted scaling `(z_i)_i ↦ (λ^i z_i)_i` of jets, as a continuous linear equivalence. -/
def jetScale (k : ℕ) (lam : ℂ) (hlam : lam ≠ 0) :
    (Fin (k + 1) × ι → ℂ) ≃L[ℂ] (Fin (k + 1) × ι → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun z q => lam ^ (q.1 : ℕ) * z q
      invFun := fun z q => (lam ^ (q.1 : ℕ))⁻¹ * z q
      map_add' := fun z w => by funext q; simp [mul_add]
      map_smul' := fun a z => by funext q; simp; ring
      left_inv := fun z => by funext q; simp [pow_ne_zero _ hlam]
      right_inv := fun z => by funext q; simp [pow_ne_zero _ hlam] }

theorem jetScale_apply (k : ℕ) (lam : ℂ) (hlam : lam ≠ 0) (z : Fin (k + 1) × ι → ℂ) :
    jetScale k lam hlam z = fun q => lam ^ (q.1 : ℕ) * z q := rfl

/-- **Weighted homogeneity** of the jet map: `Φ_k(z_0, λ z_1, …, λ^k z_k) = λ^k Φ_k(z)`. -/
theorem jetMap_scale (A : (ι → ℂ) → ℂ) :
    ∀ (k : ℕ) (lam : ℂ), lam ≠ 0 → ∀ z : Fin (k + 1) × ι → ℂ,
      jetMap A k (fun q => lam ^ (q.1 : ℕ) * z q) = lam ^ k * jetMap A k z := by
  intro k
  induction k with
  | zero =>
    intro lam _ z
    simp [jetMap]
  | succ k ih =>
    intro lam hlam z
    -- differentiate the inductive identity `Φ_k ∘ S_λ = λ^k Φ_k`
    have hfun : (jetMap A k) ∘ (jetScale k lam hlam) = lam ^ k • jetMap A k := by
      funext w
      simp only [Function.comp_apply, jetScale_apply, Pi.smul_apply, smul_eq_mul]
      exact ih lam hlam w
    have hD : ∀ w v, fderiv ℂ (jetMap A k) (jetScale k lam hlam w) (jetScale k lam hlam v) =
        lam ^ k * fderiv ℂ (jetMap A k) w v := by
      intro w v
      have h1 := (jetScale k lam hlam).comp_right_fderiv (f := jetMap A k) (x := w)
      rw [hfun, fderiv_const_smul_field] at h1
      have h2 := congrArg (fun L => L v) h1
      simp only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
        Function.comp_apply] at h2
      exact h2.symm
    rw [jetMap_succ, jetMap_succ]
    have hi : jetInit k (fun q => lam ^ (q.1 : ℕ) * z q) = jetScale k lam hlam (jetInit k z) := by
      funext q; simp [jetInit, jetScale_apply]
    have ht : jetTail k (fun q => lam ^ (q.1 : ℕ) * z q) =
        lam • jetScale k lam hlam (jetTail k z) := by
      funext q; simp [jetTail, jetScale_apply, pow_succ]; ring
    rw [hi, ht, map_smul, hD, smul_eq_mul, pow_succ]
    ring

/-- **Chain rule along jets**: if `∂_t e_i = e_{i+1}` (`i ≤ k`) at `s` and the position `e_0(s)`
lies in a set where `A` is analytic, then
`∂_t Φ_k(e_0, …, e_k) = Φ_{k+1}(e_0, …, e_{k+1})` at `s`. -/
theorem hasDerivAt_jetMap {A : (ι → ℂ) → ℂ} {B : Set (ι → ℂ)} (hA : AnalyticOnNhd ℂ A B)
    {k : ℕ} (e : ℕ → ℝ → ι → ℂ) {s : ℝ} (he : ∀ i ≤ k, HasDerivAt (e i) (e (i + 1) s) s)
    (hB : e 0 s ∈ B) :
    HasDerivAt (fun s => jetMap A k (fun q => e q.1 s q.2))
      (jetMap A (k + 1) (fun q => e q.1 s q.2)) s := by
  have hJ : HasDerivAt (fun s => fun q : Fin (k + 1) × ι => e q.1 s q.2)
      (fun q => e (q.1 + 1) s q.2) s :=
    hasDerivAt_pi.mpr fun q => hasDerivAt_pi.mp (he q.1 (Nat.lt_succ_iff.mp q.1.2)) q.2
  have hmem : (fun q : Fin (k + 1) × ι => e q.1 s q.2) ∈ jetPos k ⁻¹' B := by
    simpa [Set.mem_preimage, jetPos] using hB
  have hF := (((analyticOnNhd_jetMap hA k) _ hmem).differentiableAt.hasFDerivAt.restrictScalars
    ℝ).comp_hasDerivAt s hJ
  refine hF.congr_deriv ?_
  simp only [ContinuousLinearMap.coe_restrictScalars']
  rw [jetMap_succ]
  congr 1

/-- Real scaling lemma behind the Faà di Bruno weights: if `λ^{2k} X ≤ M` for every `λ > 0` with
`Σ_{i<k} λ^{i+1} σ_{i+1} ≤ δ'/2`, then `X ≤ M η^{-2k} (Σ_{i=1}^k σ_i^{1/i})^{2k}` whenever
`0 < η ≤ 1` and `k η ≤ δ'/2`. -/
theorem jet_scaling_bound {k : ℕ} {X M δ' η : ℝ} {σ : ℕ → ℝ} (hX0 : 0 ≤ X) (hM0 : 0 ≤ M)
    (hσ0 : ∀ i, 0 ≤ σ i) (hη : 0 < η) (hη1 : η ≤ 1) (hkη : (k : ℝ) * η ≤ δ' / 2)
    (hscale : ∀ lam : ℝ, 0 < lam →
      ∑ i ∈ range k, lam ^ (i + 1) * σ (i + 1) ≤ δ' / 2 → lam ^ (2 * k) * X ≤ M) :
    X ≤ M / η ^ (2 * k) * (∑ i ∈ Icc 1 k, σ i ^ ((i : ℝ)⁻¹)) ^ (2 * k) := by
  set S := ∑ i ∈ Icc 1 k, σ i ^ ((i : ℝ)⁻¹) with hSdef
  have hS0 : 0 ≤ S := sum_nonneg fun i _ => Real.rpow_nonneg (hσ0 i) _
  have hσS : ∀ i ∈ range k, σ (i + 1) ≤ S ^ (i + 1) := by
    intro i hi
    have hmem : i + 1 ∈ Icc 1 k := by
      rw [mem_Icc]; have := mem_range.mp hi; omega
    have h1 : σ (i + 1) ^ (((i + 1 : ℕ) : ℝ)⁻¹) ≤ S :=
      single_le_sum (f := fun i => σ i ^ ((i : ℝ)⁻¹))
        (fun i _ => Real.rpow_nonneg (hσ0 i) _) hmem
    calc σ (i + 1) = (σ (i + 1) ^ (((i + 1 : ℕ) : ℝ)⁻¹)) ^ (i + 1) :=
          (Real.rpow_inv_natCast_pow (hσ0 _) (Nat.succ_ne_zero i)).symm
      _ ≤ S ^ (i + 1) := pow_le_pow_left₀ (Real.rpow_nonneg (hσ0 _) _) h1 _
  clear_value S
  rcases hS0.lt_or_eq with hS | hS
  · -- `S > 0`: scale by `λ = η / S`
    have hlam : 0 < η / S := div_pos hη hS
    have hsum : ∑ i ∈ range k, (η / S) ^ (i + 1) * σ (i + 1) ≤ δ' / 2 := by
      have hle : ∀ i ∈ range k, (η / S) ^ (i + 1) * σ (i + 1) ≤ η := by
        intro i hi
        calc (η / S) ^ (i + 1) * σ (i + 1) ≤ (η / S) ^ (i + 1) * S ^ (i + 1) :=
              mul_le_mul_of_nonneg_left (hσS i hi) (pow_nonneg hlam.le _)
          _ = η ^ (i + 1) := by rw [← mul_pow, div_mul_cancel₀ _ hS.ne']
          _ ≤ η := pow_le_of_le_one hη.le hη1 (Nat.succ_ne_zero i)
      calc ∑ i ∈ range k, (η / S) ^ (i + 1) * σ (i + 1) ≤ ∑ i ∈ range k, η := sum_le_sum hle
        _ = k * η := by simp
        _ ≤ δ' / 2 := hkη
    have h := hscale (η / S) hlam hsum
    have hpos : 0 < (η / S) ^ (2 * k) := pow_pos hlam _
    have hX : X ≤ M / (η / S) ^ (2 * k) := by
      rw [le_div_iff₀ hpos, mul_comm]; exact h
    refine hX.trans (le_of_eq ?_)
    have hηk : η ^ (2 * k) ≠ 0 := pow_ne_zero _ hη.ne'
    have hSk : S ^ (2 * k) ≠ 0 := pow_ne_zero _ hS.ne'
    rw [div_pow]
    field_simp
  · -- `S = 0`: every time derivative vanishes, every scaling is admissible
    have hσz : ∀ i ∈ range k, σ (i + 1) = 0 := by
      intro i hi
      have := hσS i hi
      rw [← hS, zero_pow (Nat.succ_ne_zero i)] at this
      exact le_antisymm this (hσ0 _)
    have hsum0 : ∀ lam : ℝ, ∑ i ∈ range k, lam ^ (i + 1) * σ (i + 1) = 0 := fun lam =>
      sum_eq_zero fun i hi => by rw [hσz i hi, mul_zero]
    have hδ' : 0 ≤ δ' / 2 := le_trans (mul_nonneg (Nat.cast_nonneg k) hη.le) hkη
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      have h := hscale 1 one_pos (by rw [hsum0]; exact hδ')
      simp only [one_pow, one_mul] at h
      simpa using h
    · have hX : X ≤ 0 := by
        by_contra hneg
        replace hneg := not_le.mp hneg
        have hMX : 0 ≤ M / X := div_nonneg hM0 hneg.le
        have hlam1 : 1 ≤ M / X + 1 := by linarith
        have h := hscale (M / X + 1) (by linarith) (by rw [hsum0]; exact hδ')
        have h2 : (M / X + 1) * X ≤ (M / X + 1) ^ (2 * k) * X := by
          refine mul_le_mul_of_nonneg_right ?_ hX0
          calc M / X + 1 = (M / X + 1) ^ 1 := (pow_one _).symm
            _ ≤ (M / X + 1) ^ (2 * k) := pow_le_pow_right₀ hlam1 (by omega)
        have h3 : (M / X + 1) * X = M + X := by field_simp
        linarith
      rw [← hS, zero_pow (by omega), mul_zero]
      linarith

/-- **Order-`k` time-differentiated analytic composition consistency**
(`eq:supp-open-composition-consistency`, differentiated `k` times in time).  Let `A : ℂ^ι → ℂ` be
analytic at the constant base point `c` (power series on a ball), `r ≥ 1` and `k ∈ ℕ`.  There are
mesh-independent `δ > 0, C` such that for every grid history `u_h = v_0 : ℝ → (ι → Grid N → ℂ)`
with `k` controlled time derivatives `v_1, …, v_k` on an open time set `O` (`IsJet`) whose position
stays in the small chart `Σ_j ‖v_0(s)_j - c_j‖_{r+1,h} ≤ δ` (`s ∈ O`), at every `t ∈ O`:
* at every point `y` of the torus,
  `∂_t^k [𝓘_h A(u_h)(y) - A(𝓘_h u_h)(y)] = 𝓘_h[Φ_k(u_h, …, u_h^{(k)})](y) - Φ_k(𝓘_h u_h, …, 𝓘_h u_h^{(k)})(y)`
  with `Φ_k = jetMap A k` the Faà di Bruno jet map (ordinary chain rule), and
* `‖∂_t^k[…]‖²_{H^r} ≤ C h² (Σ_{i=1}^k ‖u_h^{(i)}‖_{r+1,h}^{1/i})^{2k}`, where
  `‖u^{(i)}‖_{r+1,h} = Σ_j ‖v_i(t)_j‖_{r+1,h}`; no smallness of the time derivatives is assumed
  (each enters with its Faà di Bruno weight `i`, by the weighted homogeneity `jetMap_scale`). -/
theorem composition_consistency_iteratedDeriv (r : ℕ) (hr : 1 ≤ r) {A : (ι → ℂ) → ℂ}
    {p : FormalMultilinearSeries ℂ (ι → ℂ) ℂ} {c : ι → ℂ} {R : ENNReal}
    (hA : HasFPowerSeriesOnBall A p c R) (k : ℕ) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] {O : Set ℝ}, IsOpen O →
      ∀ (v : ℕ → ℝ → ι → Grid N → ℂ), IsJet O k v →
      (∀ s ∈ O, ∑ j, sobNorm (r + 1) (v 0 s j - fun _ => c j) ≤ δ) → ∀ t ∈ O,
      (∀ y, iteratedDeriv k
          (fun s => interp (fun x => A (fun j => v 0 s j x)) y - A (fun j => interp (v 0 s j) y)) t =
        interp (fun x => jetMap A k (fun q => v q.1 t q.2 x)) y -
          jetMap A k (fun q => interp (v q.1 t q.2) y)) ∧
      trigSobSq r (fun y => interp (fun x => jetMap A k (fun q => v q.1 t q.2 x)) y -
          jetMap A k (fun q => interp (v q.1 t q.2) y)) ≤
        C * ((N : ℝ) ^ 2)⁻¹ *
          (∑ i ∈ Icc 1 k, (∑ j, sobNorm (r + 1) (v i t j)) ^ ((i : ℝ)⁻¹)) ^ (2 * k) := by
  classical
  set B : Set (ι → ℂ) := Metric.eball c R
  have hAB : AnalyticOnNhd ℂ A B := hA.analyticOnNhd
  -- the jet map is analytic at the base jet `(c, 0, …, 0)`
  set b : Fin (k + 1) × ι → ℂ := fun q => if (q.1 : ℕ) = 0 then c q.2 else 0 with hbdef
  have hbmem : b ∈ jetPos k ⁻¹' B := by
    have : jetPos k b = c := by funext l; simp [jetPos, b]
    rw [Set.mem_preimage, this]
    exact Metric.mem_eball_self hA.r_pos
  obtain ⟨p', R', hΦ⟩ := analyticOnNhd_jetMap hAB k b hbmem
  obtain ⟨δ', hδ', C', hC', hcomp⟩ := composition_consistency (ι := Fin (k + 1) × ι) r hr hΦ
  obtain ⟨ρ, hρ0, hρR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hA.r_pos
  have hρ : (0 : ℝ) < ρ := NNReal.coe_pos.mpr (ENNReal.coe_pos.mp hρ0)
  set K : ℝ := Real.sqrt cEmb * (π / 2) ^ (r + 1) with hKdef
  have hK0 : 0 ≤ K := by positivity
  set δ : ℝ := min (δ' / 2) (ρ / (2 * (K + 1)))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  set η : ℝ := min 1 (δ' / (2 * (k + 1)))
  have hη : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  refine ⟨δ, hδ, C' * δ' ^ 2 / η ^ (2 * k), by positivity,
    fun N _ O hO v hv hchart t ht => ⟨fun y => ?_, ?_⟩⟩
  · -- the derivative identity, by the chain lemma along the jets
    have hball : ∀ s ∈ O, ∀ z : ι → ℂ,
        (∀ j, ∃ y, z j - c j = interp (v 0 s j - fun _ => c j) y) → z ∈ B := by
      intro s hs z hz
      have hKσ : K * ∑ j, sobNorm (r + 1) (v 0 s j - fun _ => c j) ≤ ρ / 2 := by
        have h1 : ∑ j, sobNorm (r + 1) (v 0 s j - fun _ => c j) ≤ ρ / (2 * (K + 1)) :=
          (hchart s hs).trans (min_le_right _ _)
        have h2 : K * ∑ j, sobNorm (r + 1) (v 0 s j - fun _ => c j) ≤
            (K + 1) * (ρ / (2 * (K + 1))) :=
          mul_le_mul (by linarith) h1 (sum_nonneg fun j _ => Real.sqrt_nonneg _) (by linarith)
        have h3 : (K + 1) * (ρ / (2 * (K + 1))) = ρ / 2 := by field_simp
        linarith
      have := norm_sub_le_of_chart r hr (fun j => v 0 s j - fun _ => c j) z c hz
      exact mem_eball_of_norm_le hρR (this.trans hKσ)
    set G : ℕ → ℝ → ℂ := fun m s => interp (fun x => jetMap A m (fun q => v q.1 s q.2 x)) y -
      jetMap A m (fun q => interp (v q.1 s q.2) y) with hGdef
    have hchain : ∀ m < k, ∀ s ∈ O, HasDerivAt (G m) (G (m + 1) s) s := by
      intro m hm s hs
      have hvi : ∀ i ≤ m, ∀ l, HasDerivAt (fun s => v i s l) (v (i + 1) s l) s :=
        fun i hi l => hasDerivAt_pi.mp (hv i (by omega) s hs) l
      -- grid term
      have hg : HasDerivAt (fun s => fun x => jetMap A m (fun q => v q.1 s q.2 x))
          (fun x => jetMap A (m + 1) (fun q => v q.1 s q.2 x)) s := by
        refine hasDerivAt_pi.mpr fun x => ?_
        refine hasDerivAt_jetMap hAB (k := m) (fun i s l => v i s l x) (fun i hi => ?_) ?_
        · exact hasDerivAt_pi.mpr fun l => hasDerivAt_pi.mp (hvi i hi l) x
        · exact hball s hs _ fun j =>
            ⟨samplePt x, by rw [interp_sub_const_apply, interp_sample]⟩
      have hF1 := ((ContinuousMap.evalCLM ℝ y).hasFDerivAt).comp_hasDerivAt s
        (hasDerivAt_interp hg)
      -- interpolant term
      have hF2 : HasDerivAt (fun s => jetMap A m (fun q => interp (v q.1 s q.2) y))
          (jetMap A (m + 1) (fun q => interp (v q.1 s q.2) y)) s := by
        refine hasDerivAt_jetMap hAB (k := m) (fun i s l => interp (v i s l) y)
          (fun i hi => ?_) ?_
        · refine hasDerivAt_pi.mpr fun l => ?_
          have := ((ContinuousMap.evalCLM ℝ y : C(UnitAddTorus (Fin 3), ℂ) →L[ℝ] ℂ).hasFDerivAt
            ).comp_hasDerivAt s (hasDerivAt_interp (hvi i hi l))
          exact this
        · exact hball s hs _ fun j => ⟨y, by rw [interp_sub_const_apply]⟩
      exact hF1.sub hF2
    have h := iteratedDeriv_eq_of_chain hO G k hchain k le_rfl t ht
    have h0 : G 0 = fun s => interp (fun x => A (fun j => v 0 s j x)) y -
        A (fun j => interp (v 0 s j) y) := by
      funext s; simp [hGdef, jetMap]
    rw [h0] at h
    exact h
  · -- the bound, by scaling the jet
    set Φ := jetMap A k
    set D : UnitAddTorus (Fin 3) → ℂ := fun y =>
      interp (fun x => Φ (fun q => v q.1 t q.2 x)) y - Φ (fun q => interp (v q.1 t q.2) y)
      with hDdef
    set a := ∑ j, sobNorm (r + 1) (v 0 t j - fun _ => c j)
    set σ : ℕ → ℝ := fun i => ∑ j, sobNorm (r + 1) (v i t j) with hσdef
    have hσ0 : ∀ i, 0 ≤ σ i := fun i => sum_nonneg fun j _ => Real.sqrt_nonneg _
    have ha0 : 0 ≤ a := sum_nonneg fun j _ => Real.sqrt_nonneg _
    have ha : a ≤ δ' / 2 := (hchart t ht).trans (min_le_left _ _)
    set X := trigSobSq r D
    have hX0 : 0 ≤ X := trigSobSq_nonneg' r D
    set M : ℝ := C' * ((N : ℝ) ^ 2)⁻¹ * δ' ^ 2
    have hM0 : 0 ≤ M := mul_nonneg (mul_nonneg hC' (inv_nonneg.mpr (sq_nonneg _))) (sq_nonneg _)
    have hscale : ∀ lam : ℝ, 0 < lam →
        ∑ i ∈ range k, lam ^ (i + 1) * σ (i + 1) ≤ δ' / 2 → lam ^ (2 * k) * X ≤ M := by
      intro lam hlam hsum
      have hlamC : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
      set U : Fin (k + 1) × ι → Grid N → ℂ := fun q => ((lam : ℂ) ^ (q.1 : ℕ)) • v q.1 t q.2
      have hterm : ∀ i : Fin (k + 1), ∑ l, sobNorm (r + 1) (U (i, l) - fun _ => b (i, l)) =
          if (i : ℕ) = 0 then a else lam ^ (i : ℕ) * σ i := by
        intro i
        by_cases hi : (i : ℕ) = 0
        · simp only [hi, ite_true, U, b, pow_zero, one_smul, a]
        · simp only [hi, ite_false, U, b, σ, mul_sum]
          refine sum_congr rfl fun l _ => ?_
          rw [show ((lam : ℂ) ^ (i : ℕ) • v i t l - fun _ => (0 : ℂ)) =
              ((lam : ℂ) ^ (i : ℕ)) • v i t l by funext x; simp,
            Moser.sobNorm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam]
      have hdev : ∑ q, sobNorm (r + 1) (U q - fun _ => b q) =
          a + ∑ i ∈ range k, lam ^ (i + 1) * σ (i + 1) := by
        rw [Fintype.sum_prod_type]
        simp only [hterm]
        rw [Fin.sum_univ_eq_sum_range (fun i => if i = 0 then a else lam ^ i * σ i) (k + 1),
          sum_range_succ']
        simp only [Nat.succ_ne_zero, ite_false, ite_true]
        ring
      have hdevle : a + ∑ i ∈ range k, lam ^ (i + 1) * σ (i + 1) ≤ δ' := by linarith
      have hb := hcomp N U (by rw [hdev]; exact hdevle)
      rw [hdev] at hb
      have hfun : (fun y => interp (fun x => Φ (fun q => U q x)) y -
          Φ (fun q => interp (U q) y)) = fun y => ((lam : ℂ) ^ k) * D y := by
        funext y
        have e1 : (fun x => Φ (fun q => U q x)) =
            ((lam : ℂ) ^ k) • fun x => Φ (fun q => v q.1 t q.2 x) := by
          funext x
          simp only [U, Pi.smul_apply, smul_eq_mul]
          exact jetMap_scale A k (lam : ℂ) hlamC (fun q => v q.1 t q.2 x)
        have e2 : Φ (fun q => interp (U q) y) =
            ((lam : ℂ) ^ k) * Φ (fun q => interp (v q.1 t q.2) y) := by
          simp only [U, interp_smul, ContinuousMap.smul_apply, smul_eq_mul]
          exact jetMap_scale A k (lam : ℂ) hlamC (fun q => interp (v q.1 t q.2) y)
        rw [e1, e2, interp_smul, hDdef]
        simp only [ContinuousMap.smul_apply, smul_eq_mul]
        ring
      rw [hfun, trigSobSq_const_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hlam, ← pow_mul, mul_comm k 2] at hb
      refine hb.trans ?_
      have : (a + ∑ i ∈ range k, lam ^ (i + 1) * σ (i + 1)) ^ 2 ≤ δ' ^ 2 :=
        pow_le_pow_left₀ (add_nonneg ha0 (sum_nonneg fun i _ =>
          mul_nonneg (pow_nonneg hlam.le _) (hσ0 _))) hdevle 2
      calc C' * ((N : ℝ) ^ 2)⁻¹ * (a + ∑ i ∈ range k, lam ^ (i + 1) * σ (i + 1)) ^ 2
          ≤ C' * ((N : ℝ) ^ 2)⁻¹ * δ' ^ 2 := by gcongr
        _ = M := rfl
    have hkη : (k : ℝ) * η ≤ δ' / 2 := by
      have h1 : η ≤ δ' / (2 * (k + 1)) := min_le_right _ _
      have h2 : (k : ℝ) * η ≤ k * (δ' / (2 * (k + 1))) :=
        mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg k)
      have h3 : (k : ℝ) * (δ' / (2 * (k + 1))) ≤ δ' / 2 := by
        have hk1 : (0 : ℝ) < 2 * (k + 1) := by positivity
        rw [mul_div_assoc', div_le_div_iff₀ hk1 two_pos]
        nlinarith
      linarith
    have := jet_scaling_bound hX0 hM0 hσ0 hη hη1 hkη hscale
    refine this.trans (le_of_eq ?_)
    simp only [M]
    ring

/-- Non-vacuity: the constant jet `(c, 0, 0, …)` is a jet on every open set (and lies in every
chart); every analytic `A` (e.g. a constant) has a power series on a ball. -/
example (N : ℕ) [NeZero N] (k : ℕ) (c : ι → ℂ) :
    IsJet Set.univ k (fun i (_ : ℝ) => if i = 0 then (fun j (_ : Grid N) => c j) else 0) := by
  intro i _ s _
  by_cases hi : i = 0
  · subst hi; simpa using hasDerivAt_const s (fun j (_ : Grid N) => c j)
  · simpa [hi] using hasDerivAt_const s (0 : ι → Grid N → ℂ)


end Jet

end

end HigherTimeConsistency

end RenewalGeometry.PeriodicGridSobolev
