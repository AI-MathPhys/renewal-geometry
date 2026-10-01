/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.PeriodicGridMoserComposition
import RenewalGeometry.Analysis.IteratedDerivBounds

/-!
# The grid Sobolev spaces `H^r_h` as normed spaces, and smooth pointwise compositions
  (infrastructure for `lem:supp-open-local-jets`; emergent-spacetime manuscript)

On the periodic grid `(ℤ/N)³` (mesh `h = 1/N`):

* `GridH N r`: the real arrays `(ℤ/N)³ → ℝ` with the grid Sobolev norm
  `‖u‖ = ‖u‖_{r,h} = (Σ_{|α| ≤ r} ‖D^α u‖_h²)^{1/2}` (`sobNorm`) as a genuine finite-dimensional
  normed space (`GridH.norm_def`), so that Fréchet derivatives and their operator norms on
  `H^r_h` are Mathlib's.
* `GridH.abs_apply_le`: `|u(x)| ≤ √K ‖u‖_{r,h}` for `r ≥ 2` (uniform discrete embedding).
* `GridH.incl` (`H^{r'}_h → H^r_h`, `r ≤ r'`, norm `≤ 1`), `GridH.up` (**inverse inequality**
  `‖u‖_{r+1,h} ≤ C_r h^{-1} ‖u‖_{r,h}` with `C_r = 2 √#{|α| ≤ r+1}`, from the bounded frequency
  cube: `h‖D_i⁺w‖_h ≤ 2‖w‖_h`), `GridH.mulL` (the product, bilinear with norm `≤ A_r`, `r ≥ 2`).
* `GridH.pointwise A c`: the array map `u ↦ (x ↦ A(c + u(x)))` on `ι`-component arrays, and
  `GridH.pointwise_derivBound` (**uniform derivative bounds for analytic compositions**): for
  `A` analytic at `c`, `r ≥ 2` and every `K`, there are `δ > 0` and `C`, independent of `N`, such
  that `u ↦ A(c + u)` is `C^∞` on the `δ`-ball of `(H^r_h)^ι` with
  `‖D^k (A(c + ·))(u)‖_{(H^r_h)^k → H^r_h} ≤ C` for all `k ≤ K`.  The `k`-th derivative is the
  pointwise array `x ↦ D^k A(c + u(x))[Y₁(x), …, Y_k(x)]` (`GridH.iteratedFDeriv_pointwise_apply`)
  and the bound is the discrete Moser estimate for the analytic coefficients
  `w ↦ D^k A(c + w)[e_{ρ₁}, …, e_{ρ_k}]` combined with the product algebra.
-/

open Finset Filter Topology Set
open scoped BigOperators ContDiff

namespace RenewalGeometry.PeriodicGridSobolev

open LatticeTorusPlancherel IteratedDerivBounds

noncomputable section

set_option linter.unusedSectionVars false

/-! ### Auxiliary grid facts -/

section Aux

variable {N : ℕ} [NeZero N]

theorem gridNorm_S_eq (i : Fin 3) (w : Grid N → ℂ) : gridNorm (S i w) = gridNorm w := by
  unfold gridNorm
  rw [gridNormSq_of_unimodular (isMult_S i) (fun k => norm_chi i k)]

/-- `h ‖D_i⁺ w‖_h ≤ 2 ‖w‖_h`. -/
theorem gridNorm_Dp_le_mesh (i : Fin 3) (w : Grid N → ℂ) :
    gridNorm (Dp i w) ≤ 2 * N * gridNorm w := by
  have e : Dp i w = (N : ℂ) • (S i w - w) := by simp [Dp]
  rw [e, gridNorm_smul, Complex.norm_natCast]
  have h1 := gridNorm_sub_le (S i w) w
  rw [gridNorm_S_eq] at h1
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

theorem Dα_single (i : Fin 3) : Dα (N := N) (Pi.single i 1) = Dp i := by
  fin_cases i <;> simp [Dα]

theorem Dα_const_of_ne {α : Fin 3 → ℕ} (hα : α ≠ 0) (a : ℂ) :
    Dα (N := N) α (fun _ => a) = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
    by_contra h; push_neg at h; exact hα (funext h)
  have hsplit : α = Pi.single i 1 + (α - Pi.single i 1) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp; omega
    · simp [Pi.single_apply, hj]
  rw [hsplit, Dα_add]
  -- `D^β` of a constant is a constant multiple, and `D_i⁺` kills constants
  have hconst : ∀ (β : Fin 3 → ℕ), ∃ b : ℂ, Dα (N := N) β (fun _ => a) = fun _ => b := by
    intro β
    have key : ∀ (T : Module.End ℂ (Grid N → ℂ)) (n : ℕ),
        (∀ b : ℂ, ∃ b' : ℂ, T (fun _ => b) = fun _ => b') →
        ∀ b : ℂ, ∃ b' : ℂ, (T ^ n) (fun _ => b) = fun _ => b' := by
      intro T n hT
      induction n with
      | zero => intro b; exact ⟨b, rfl⟩
      | succ n ih =>
        intro b
        obtain ⟨b1, hb1⟩ := ih b
        obtain ⟨b2, hb2⟩ := hT b1
        exact ⟨b2, by rw [pow_succ', Module.End.mul_apply, hb1, hb2]⟩
    have hDp : ∀ j : Fin 3, ∀ b : ℂ, ∃ b' : ℂ, Dp (N := N) j (fun _ => b) = fun _ => b' :=
      fun j b => ⟨0, by funext x; rw [Dp_apply]; simp⟩
    obtain ⟨b2, h2⟩ := key (Dp 2) (β 2) (hDp 2) a
    obtain ⟨b1, h1⟩ := key (Dp 1) (β 1) (hDp 1) b2
    obtain ⟨b0, h0⟩ := key (Dp 0) (β 0) (hDp 0) b1
    exact ⟨b0, by simp only [Dα, Module.End.mul_apply, h2, h1, h0]⟩
  obtain ⟨b, hb⟩ := hconst (α - Pi.single i 1)
  rw [hb, Dα_single]
  funext x; rw [Dp_apply]; simp

/-- `‖1‖_{r,h} = 1`. -/
theorem sobNorm_const (r : ℕ) (a : ℂ) : sobNorm (N := N) r (fun _ => a) = ‖a‖ := by
  have hsq : sobSq (N := N) r (fun _ => a) = ‖a‖ ^ 2 := by
    unfold sobSq
    rw [← sum_erase_add _ _ (mem_multiIndices.mpr (show deg (0 : Fin 3 → ℕ) ≤ r by simp [deg]))]
    rw [sum_eq_zero fun α hα => by
      rw [Dα_const_of_ne (ne_of_mem_erase hα)]
      simp [gridNormSq]]
    rw [zero_add, Dα_zero, Module.End.one_apply, gridNormSq]
    have hN : ((N : ℝ) ^ 3) ≠ 0 := by
      have : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
      positivity
    rw [sum_const, card_univ]
    simp only [nsmul_eq_mul]
    have hc : (Fintype.card (Grid N) : ℝ) = (N : ℝ) ^ 3 := by
      simp [Grid, LatticeTorusPlancherel.Grid, Fintype.card_fun, ZMod.card]
    rw [hc, ← mul_assoc, inv_mul_cancel₀ hN, one_mul]
  rw [sobNorm, hsq, Real.sqrt_sq (norm_nonneg _)]

theorem card_grid : (Fintype.card (Grid N) : ℝ) = (N : ℝ) ^ 3 := by
  simp [Grid, LatticeTorusPlancherel.Grid, Fintype.card_fun, ZMod.card]

/-- The number of multi-indices of degree `≤ r`. -/
def numMultiIndices (r : ℕ) : ℝ := (multiIndices r).card

/-- **Inverse inequality**, squared form: `‖u‖²_{r+1,h} ≤ 4 #{|α| ≤ r+1} N² ‖u‖²_{r,h}`. -/
theorem sobSq_succ_le_inverse (r : ℕ) (u : Grid N → ℂ) :
    sobSq (r + 1) u ≤ 4 * numMultiIndices (r + 1) * (N : ℝ) ^ 2 * sobSq r u := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hterm : ∀ α ∈ multiIndices (r + 1), gridNormSq (Dα α u) ≤ 4 * (N : ℝ) ^ 2 * sobSq r u := by
    intro α hα
    by_cases h0 : α = 0
    · subst h0
      rw [Dα_zero, Module.End.one_apply, ← sobSq_zero]
      have := sobSq_mono (Nat.zero_le r) u
      have h4 : (1 : ℝ) ≤ 4 * (N : ℝ) ^ 2 := by nlinarith
      nlinarith [sobSq_nonneg r u]
    · obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
        by_contra h; push_neg at h; exact h0 (funext h)
      set α' := α - Pi.single i 1
      have hsplit : α = Pi.single i 1 + α' := by
        funext j
        by_cases hj : j = i
        · subst hj; simp [α']; omega
        · simp [α', Pi.single_apply, hj]
      have hdeg : deg α' ≤ r := by
        have h1 := mem_multiIndices.mp hα
        have h2 : deg α = 1 + deg α' := by
          rw [hsplit, deg_add]; congr 1; fin_cases i <;> simp [deg]
        omega
      rw [hsplit, Dα_add, Dα_single, ← gridNorm_sq]
      have h1 := gridNorm_Dp_le_mesh i (Dα α' u)
      have h2 : gridNorm (Dα α' u) ^ 2 ≤ sobSq r u := by
        rw [gridNorm_sq]; exact gridNormSq_Dα_le_sobSq hdeg u
      have h3 : gridNorm (Dp i (Dα α' u)) ^ 2 ≤ (2 * N * gridNorm (Dα α' u)) ^ 2 :=
        pow_le_pow_left₀ (gridNorm_nonneg _) h1 2
      nlinarith [gridNorm_nonneg (Dα α' u)]
  unfold sobSq
  calc ∑ α ∈ multiIndices (r + 1), gridNormSq (Dα α u)
      ≤ ∑ _α ∈ multiIndices (r + 1), 4 * (N : ℝ) ^ 2 * sobSq r u := sum_le_sum hterm
    _ = 4 * numMultiIndices (r + 1) * (N : ℝ) ^ 2 * sobSq r u := by
        rw [sum_const, nsmul_eq_mul, numMultiIndices]; unfold sobSq; ring

/-- The inverse-inequality constant `2 √#{|α| ≤ r+1}`. -/
def invConst (r : ℕ) : ℝ := 2 * Real.sqrt (numMultiIndices (r + 1))

theorem invConst_nonneg (r : ℕ) : 0 ≤ invConst r := by unfold invConst; positivity

/-- **Inverse inequality** `‖u‖_{r+1,h} ≤ C_r h^{-1} ‖u‖_{r,h}`. -/
theorem sobNorm_succ_le_inverse (r : ℕ) (u : Grid N → ℂ) :
    sobNorm (r + 1) u ≤ invConst r * N * sobNorm r u := by
  have h := sobSq_succ_le_inverse r u
  have hnm : 0 ≤ numMultiIndices (r + 1) := Nat.cast_nonneg _
  unfold sobNorm
  have e : invConst r * N * Real.sqrt (sobSq r u) =
      Real.sqrt (4 * numMultiIndices (r + 1) * (N : ℝ) ^ 2 * sobSq r u) := by
    rw [invConst, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_mul (by positivity), Real.sqrt_sq (Nat.cast_nonneg N),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [e]
  exact Real.sqrt_le_sqrt h

end Aux

/-! ### The normed space `H^r_h` -/

/-- **The grid Sobolev space** `H^r_h`: real arrays on `(ℤ/N)³` with the norm `‖u‖_{r,h}`. -/
def GridH (N r : ℕ) : Type := Grid N → ℝ

namespace GridH

variable {N : ℕ} [NeZero N] {r : ℕ}

instance : AddCommGroup (GridH N r) := inferInstanceAs (AddCommGroup (Grid N → ℝ))
instance : Module ℝ (GridH N r) := inferInstanceAs (Module ℝ (Grid N → ℝ))

/-- The underlying array. -/
def val (u : GridH N r) : Grid N → ℝ := u

/-- An array as an element of `H^r_h`. -/
def mk (f : Grid N → ℝ) : GridH N r := f

@[simp] theorem val_mk (f : Grid N → ℝ) : val (mk (r := r) f) = f := rfl
@[simp] theorem mk_val (u : GridH N r) : mk (val u) = u := rfl
@[simp] theorem val_add (u w : GridH N r) : val (u + w) = val u + val w := rfl
@[simp] theorem val_sub (u w : GridH N r) : val (u - w) = val u - val w := rfl
@[simp] theorem val_neg (u : GridH N r) : val (-u) = -val u := rfl
@[simp] theorem val_smul (c : ℝ) (u : GridH N r) : val (c • u) = c • val u := rfl
@[simp] theorem val_zero : val (0 : GridH N r) = 0 := rfl
theorem val_sum {ι : Type*} (s : Finset ι) (f : ι → GridH N r) :
    val (∑ i ∈ s, f i) = ∑ i ∈ s, val (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, val_add, ih]

theorem ext {u w : GridH N r} (h : ∀ x, val u x = val w x) : u = w := funext h

/-- The complexified array. -/
def cxv (u : GridH N r) : Grid N → ℂ := fun x => ((val u x : ℝ) : ℂ)

theorem cxv_add (u w : GridH N r) : cxv (u + w) = cxv u + cxv w := by
  funext x; simp [cxv]

theorem cxv_smul (c : ℝ) (u : GridH N r) : cxv (c • u) = (c : ℂ) • cxv u := by
  funext x; simp [cxv]

instance : Norm (GridH N r) := ⟨fun u => sobNorm r (cxv u)⟩

theorem norm_def (u : GridH N r) : ‖u‖ = sobNorm r (cxv u) := rfl

theorem core : NormedSpace.Core ℝ (GridH N r) where
  norm_nonneg u := Moser.sobNorm_nonneg r _
  norm_smul c u := by
    rw [norm_def, norm_def, cxv_smul, Moser.sobNorm_smul, Complex.norm_real]
  norm_triangle u w := by
    rw [norm_def, norm_def, norm_def, cxv_add]; exact Moser.sobNorm_add_le r _ _
  norm_eq_zero_iff u := by
    constructor
    · intro h
      rw [norm_def, sobNorm, Real.sqrt_eq_zero (sobSq_nonneg _ _)] at h
      have h0 : gridNormSq (cxv u) = 0 := by
        have h1 := sobSq_mono (Nat.zero_le r) (cxv u)
        rw [sobSq_zero] at h1
        exact le_antisymm (h ▸ h1) (gridNormSq_nonneg _)
      unfold gridNormSq at h0
      have hN : ((N : ℝ) ^ 3)⁻¹ ≠ 0 := by
        have : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
        positivity
      have hs := (mul_eq_zero.mp h0).resolve_left hN
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)] at hs
      funext x
      have := hs x (mem_univ x)
      have h2 : val u x = 0 := by simpa [cxv] using this
      exact h2
    · rintro rfl
      rw [norm_def]
      have : cxv (0 : GridH N r) = 0 := by funext x; simp [cxv]
      rw [this, Moser.sobNorm_zero]

instance : NormedAddCommGroup (GridH N r) := NormedAddCommGroup.ofCore core
instance : NormedSpace ℝ (GridH N r) := NormedSpace.ofCore core
instance : FiniteDimensional ℝ (GridH N r) := inferInstanceAs (FiniteDimensional ℝ (Grid N → ℝ))

/-- The identification `H^r_h ≃ (ℤ/N)³ → ℝ` (continuous: finite dimension). -/
def toFunLin : GridH N r ≃ₗ[ℝ] (Grid N → ℝ) where
  toFun := val
  invFun := mk
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The identification `H^r_h ≃ (ℤ/N)³ → ℝ` (continuous: finite dimension). -/
def toFunL : GridH N r ≃L[ℝ] (Grid N → ℝ) := toFunLin.toContinuousLinearEquiv

@[simp] theorem toFunL_apply (u : GridH N r) : toFunL u = val u := rfl
@[simp] theorem toFunL_symm_apply (f : Grid N → ℝ) : toFunL.symm f = mk (r := r) f := rfl

/-- `|u(x)| ≤ √K ‖u‖_{r,h}` for `r ≥ 2`. -/
theorem abs_apply_le (hr : 2 ≤ r) (u : GridH N r) (x : Grid N) :
    |val u x| ≤ Real.sqrt Kprod * ‖u‖ := by
  have h := Moser.norm_le_sobNorm_two (cxv u) x
  have h2 := Moser.sobNorm_mono hr (cxv u)
  simp only [cxv, Complex.norm_real, Real.norm_eq_abs] at h
  exact h.trans (mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _))

/-- A linear map of arrays which is bounded for the grid norms, as a continuous linear map. -/
def ofBound {r' : ℕ} (T : (Grid N → ℝ) →ₗ[ℝ] (Grid N → ℝ)) (C : ℝ)
    (h : ∀ u : GridH N r', ‖(mk (r := r) (T (val u)) : GridH N r)‖ ≤ C * ‖u‖) :
    GridH N r' →L[ℝ] GridH N r :=
  LinearMap.mkContinuous
    { toFun := fun u => mk (T (val u))
      map_add' := fun u w => ext fun x => by simp
      map_smul' := fun c u => ext fun x => by simp } C h

@[simp] theorem ofBound_val {r' : ℕ} (T : (Grid N → ℝ) →ₗ[ℝ] (Grid N → ℝ)) (C : ℝ) (h)
    (u : GridH N r') : val (ofBound (r := r) T C h u) = T (val u) := rfl

theorem norm_ofBound_le {r' : ℕ} (T : (Grid N → ℝ) →ₗ[ℝ] (Grid N → ℝ)) {C : ℝ} (hC : 0 ≤ C) (h) :
    ‖ofBound (r := r) (r' := r') T C h‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

/-- The inclusion `H^{r'}_h → H^r_h` for `r ≤ r'` (norm `≤ 1`). -/
def incl {r' : ℕ} (hrr : r ≤ r') : GridH N r' →L[ℝ] GridH N r :=
  ofBound LinearMap.id 1 fun u => by
    simp only [LinearMap.id_apply, mk_val, one_mul]
    exact Moser.sobNorm_mono hrr _

@[simp] theorem incl_val {r' : ℕ} (hrr : r ≤ r') (u : GridH N r') : val (incl hrr u) = val u := rfl

theorem norm_incl_le {r' : ℕ} (hrr : r ≤ r') : ‖incl (N := N) hrr‖ ≤ 1 :=
  norm_ofBound_le _ zero_le_one _

/-- The **inverse inequality** as a map `H^r_h → H^{r+1}_h` of norm `≤ C_r N`. -/
def up (r : ℕ) : GridH N r →L[ℝ] GridH N (r + 1) :=
  ofBound LinearMap.id (invConst r * N) fun u => by
    simp only [LinearMap.id_apply, mk_val]
    exact sobNorm_succ_le_inverse r _

@[simp] theorem up_val (u : GridH N r) : val (up r u) = val u := rfl

theorem norm_up_le (r : ℕ) : ‖up (N := N) r‖ ≤ invConst r * N :=
  norm_ofBound_le _ (by have := invConst_nonneg r; positivity) _

/-- Pointwise product of arrays. -/
def mulLin : (Grid N → ℝ) →ₗ[ℝ] (Grid N → ℝ) →ₗ[ℝ] (Grid N → ℝ) :=
  LinearMap.mk₂ ℝ (fun f g => f * g) (fun a b c => add_mul a b c) (fun c a b => smul_mul_assoc c a b)
    (fun a b c => mul_add a b c) (fun c a b => mul_smul_comm c a b)

theorem cxv_mul (u w : GridH N r) :
    cxv (mk (r := r) (val u * val w)) = cxv u * cxv w := by
  funext x; simp [cxv, Pi.mul_apply]

/-- **The product** `H^r_h × H^r_h → H^r_h` (`r ≥ 2`), bilinear with norm `≤ A_r`. -/
def mulL (hr : 2 ≤ r) : GridH N r →L[ℝ] GridH N r →L[ℝ] GridH N r :=
  LinearMap.mkContinuous₂
    { toFun := fun u =>
        { toFun := fun w => mk (val u * val w)
          map_add' := fun w w' => ext fun x => by simp [mul_add]
          map_smul' := fun c w => ext fun x => by simp }
      map_add' := fun u u' => by
        refine LinearMap.ext fun w => ext fun x => ?_
        simp [add_mul]
      map_smul' := fun c u => by
        refine LinearMap.ext fun w => ext fun x => ?_
        simp }
    (Moser.algConst r) fun u w => by
      show sobNorm r (cxv (mk (r := r) (val u * val w))) ≤ _
      rw [cxv_mul]
      exact Moser.sobNorm_mul_le r hr _ _

@[simp] theorem mulL_val (hr : 2 ≤ r) (u w : GridH N r) :
    val (mulL hr u w) = val u * val w := rfl

theorem norm_mulL_le (hr : 2 ≤ r) : ‖mulL (N := N) hr‖ ≤ Moser.algConst r :=
  LinearMap.mkContinuous₂_norm_le _ (Moser.algConst_pos r).le _

/-! ### Pointwise compositions -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Evaluation of an `ι`-component array at a site. -/
def evalAt (x : Grid N) : (ι → GridH N r) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun i => (ContinuousLinearMap.proj x).comp
    ((toFunL (N := N) (r := r) : GridH N r →L[ℝ] (Grid N → ℝ)).comp (ContinuousLinearMap.proj i))

@[simp] theorem evalAt_apply (x : Grid N) (u : ι → GridH N r) (i : ι) :
    evalAt x u i = val (u i) x := rfl

theorem norm_evalAt_le (hr : 2 ≤ r) (x : Grid N) (u : ι → GridH N r) :
    ‖evalAt x u‖ ≤ Real.sqrt Kprod * ‖u‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  rw [evalAt_apply, Real.norm_eq_abs]
  exact (abs_apply_le hr (u i) x).trans
    (mul_le_mul_of_nonneg_left (norm_le_pi_norm u i) (Real.sqrt_nonneg _))

/-- The pointwise composition `u ↦ (x ↦ A(c + u(x)))` on `ι`-component arrays. -/
def pointwise (A : (ι → ℝ) → ℝ) (c : ι → ℝ) (u : ι → GridH N r) : GridH N r :=
  mk fun x => A (c + evalAt x u)

theorem pointwise_eq (A : (ι → ℝ) → ℝ) (c : ι → ℝ) :
    (pointwise (N := N) (r := r) A c) =
      fun u => (toFunL (r := r)).symm (fun x => A (c + evalAt x u)) := rfl

/-- The coordinate size `Σ_j ‖u_j‖` is controlled by the sup norm. -/
theorem coordSum_le (u : ι → GridH N r) :
    Moser.coordSum r (Pi.basisFun ℝ ι) (fun x j => val (u j) x) ≤ Fintype.card ι * ‖u‖ := by
  unfold Moser.coordSum
  have : ∀ j, sobNorm r (Moser.coordArr (Pi.basisFun ℝ ι) (fun x j => val (u j) x) j) = ‖u j‖ := by
    intro j; rfl
  simp only [this]
  calc ∑ j, ‖u j‖ ≤ ∑ _j : ι, ‖u‖ := sum_le_sum fun j _ => norm_le_pi_norm u j
    _ = Fintype.card ι * ‖u‖ := by simp

/-- **The derivatives of a pointwise composition are pointwise**: on an open set `V` on which
`g` is smooth, `D^k(u ↦ g ∘ u)(u)[Y](x) = D^k g(u(x))[Y(x)]`. -/
theorem iteratedFDeriv_pointwise_apply {g : (ι → ℝ) → ℝ} {V : Set (ι → ℝ)}
    (hg : ContDiffOn ℝ ∞ g V) (hV : IsOpen V) {u : ι → GridH N r} (hu : ∀ x, evalAt x u ∈ V)
    (k : ℕ) (Y : Fin k → (ι → GridH N r)) (x : Grid N) :
    val (iteratedFDeriv ℝ k (fun u : ι → GridH N r => (toFunL (r := r)).symm
      (fun y => g (evalAt y u))) u Y) x = iteratedFDeriv ℝ k g (evalAt x u) (fun m => evalAt x (Y m)) := by
  set Ψ : (ι → GridH N r) → (Grid N → ℝ) := fun u y => g (evalAt y u)
  have hΨ : ContDiffAt ℝ ∞ Ψ u := by
    refine contDiffAt_pi.2 fun y => ?_
    have h1 : ContDiffAt ℝ ∞ g (evalAt y u) := hg.contDiffAt (hV.mem_nhds (hu y))
    exact h1.comp u (evalAt (N := N) (r := r) (ι := ι) y).contDiff.contDiffAt
  have e1 : (fun u : ι → GridH N r => (toFunL (r := r)).symm (fun y => g (evalAt y u))) =
      (toFunL (N := N) (r := r)).symm ∘ Ψ := rfl
  rw [e1, ContinuousLinearEquiv.iteratedFDeriv_comp_left]
  have e2 : val (((toFunL (N := N) (r := r)).symm : (Grid N → ℝ) →L[ℝ] GridH N r).compContinuousMultilinearMap
      (iteratedFDeriv ℝ k Ψ u) Y) x = (ContinuousLinearMap.proj x : (Grid N → ℝ) →L[ℝ] ℝ)
        (iteratedFDeriv ℝ k Ψ u Y) := rfl
  rw [e2]
  have h := congrArg (fun L => L Y)
    ((ContinuousLinearMap.proj x : (Grid N → ℝ) →L[ℝ] ℝ).iteratedFDeriv_comp_left hΨ
      (i := k) (by exact_mod_cast le_top))
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply] at h
  rw [← h]
  have e3 : ((ContinuousLinearMap.proj x : (Grid N → ℝ) →L[ℝ] ℝ) ∘ Ψ) =
      fun w => g (evalAt x w) := rfl
  rw [e3, DerivBound.iteratedFDeriv_comp_clm hg hV (evalAt x) (hu x) k]
  rfl

/-- Local uniformization over a finite family (minimum of radii, sum of constants). -/
theorem uniformize' {κ : Type*} [Fintype κ] (P : κ → ℝ → ℝ → Prop)
    (hmono : ∀ i δ δ' C C', 0 < δ' → δ' ≤ δ → C ≤ C' → P i δ C → P i δ' C')
    (h : ∀ i, ∃ δ > 0, ∃ C ≥ 0, P i δ C) : ∃ δ > 0, ∃ C ≥ 0, ∀ i, P i δ C := by
  classical
  choose δf hδ Cf hC hP using h
  set T : Finset ℝ := insert 1 (univ.image δf)
  have hT : T.Nonempty := insert_nonempty _ _
  have hpos : 0 < T.min' hT := by
    rw [Finset.lt_min'_iff]
    intro y hy
    rcases mem_insert.mp hy with rfl | hy
    · exact one_pos
    · obtain ⟨i, -, rfl⟩ := mem_image.mp hy; exact hδ i
  refine ⟨T.min' hT, hpos, ∑ i, Cf i, sum_nonneg fun i _ => hC i, fun i => ?_⟩
  refine hmono i (δf i) _ (Cf i) _ hpos (T.min'_le _ (mem_insert_of_mem (mem_image_of_mem _
    (mem_univ i)))) (single_le_sum (fun j _ => hC j) (mem_univ i)) (hP i)

/-- Arrays of the form `x ↦ a(u(x))` with `a` analytic at `0` are bounded in `H^r_h` uniformly in
the mesh on a small ball. -/
theorem sobNorm_analytic_bounded (hr : 2 ≤ r) {a : (ι → ℝ) → ℝ} (ha : AnalyticAt ℝ a 0) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (u : ι → GridH N r), ‖u‖ ≤ δ →
      sobNorm r (fun x => ((a (evalAt x u) : ℝ) : ℂ)) ≤ C := by
  obtain ⟨δ, hδ, C, hC, h⟩ := Moser.moser_analyticAt_order r hr (Pi.basisFun ℝ ι) (c := 0) ha 1
    le_rfl (fun _ _ n h1 h2 => absurd h2 (by omega))
  refine ⟨δ / (Fintype.card ι + 1), by positivity, ‖a 0‖ + C * δ, by positivity, ?_⟩
  intro N _ u hu
  have hcs : Moser.coordSum r (Pi.basisFun ℝ ι) (fun x j => val (u j) x) ≤ δ := by
    refine (coordSum_le u).trans ?_
    have hc : (Fintype.card ι : ℝ) ≤ Fintype.card ι + 1 := by linarith
    calc (Fintype.card ι : ℝ) * ‖u‖ ≤ (Fintype.card ι + 1) * (δ / (Fintype.card ι + 1)) :=
          mul_le_mul hc hu (norm_nonneg _) (by positivity)
      _ = δ := by field_simp
  have hm := h N (fun x j => val (u j) x) hcs
  have e : (fun x => ((a (evalAt x u) : ℝ) : ℂ)) =
      (fun x => ((a (0 + fun j => val (u j) x) - a 0 : ℝ) : ℂ)) + fun _ => ((a 0 : ℝ) : ℂ) := by
    funext x; simp only [Pi.add_apply, zero_add]; push_cast; ring_nf; rfl
  rw [e]
  refine (Moser.sobNorm_add_le r _ _).trans ?_
  rw [sobNorm_const, Complex.norm_real, pow_one] at *
  have h3 : C * Moser.coordSum r (Pi.basisFun ℝ ι) (fun x j => val (u j) x) ≤ C * δ :=
    mul_le_mul_of_nonneg_left hcs hC
  linarith

/-- The coefficient bound used in `pointwise_derivBound`. -/
def CoefBound (r : ℕ) (g : (ι → ℝ) → ℝ) (k : ℕ) (ρ : Fin k → ι) (δ C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (u : ι → GridH N r), ‖u‖ ≤ δ →
    sobNorm r (fun x => ((iteratedFDeriv ℝ k g (evalAt x u) (fun m => Pi.single (ρ m) 1) : ℝ) : ℂ))
      ≤ C

theorem CoefBound.mono {g : (ι → ℝ) → ℝ} {k : ℕ} {ρ : Fin k → ι} {δ δ' C C' : ℝ}
    (h : CoefBound r g k ρ δ C) (hδ : δ' ≤ δ) (hC : C ≤ C') : CoefBound r g k ρ δ' C' :=
  fun N _ u hu => (h N u (hu.trans hδ)).trans hC

theorem coefBound_fixed (hr : 2 ≤ r) {g : (ι → ℝ) → ℝ} (k : ℕ)
    (ha : ∀ ρ : Fin k → ι, AnalyticAt ℝ
      (fun w : ι → ℝ => iteratedFDeriv ℝ k g w (fun m => Pi.single (ρ m) 1)) 0) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ ρ : Fin k → ι, CoefBound r g k ρ δ C := by
  have h : ∀ ρ : Fin k → ι, ∃ δ > 0, ∃ C ≥ 0, CoefBound r g k ρ δ C := by
    intro ρ
    obtain ⟨δ, hδ, C, hC, hb⟩ := sobNorm_analytic_bounded (r := r) hr (ha ρ)
    refine ⟨δ, hδ, C, hC, ?_⟩
    intro N _ u hu
    exact hb N u hu
  exact uniformize' (fun ρ δ C => CoefBound r g k ρ δ C)
    (fun _ _ _ _ _ _ hδ hC h => h.mono hδ hC) h

theorem coefBound_uniform (hr : 2 ≤ r) {g : (ι → ℝ) → ℝ}
    (ha : ∀ (k : ℕ) (ρ : Fin k → ι), AnalyticAt ℝ
      (fun w : ι → ℝ => iteratedFDeriv ℝ k g w (fun m => Pi.single (ρ m) 1)) 0) (K : ℕ) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ k ≤ K, ∀ ρ : Fin k → ι, CoefBound r g k ρ δ C := by
  obtain ⟨δ, hδ, C, hC, h⟩ := uniformize' (κ := Fin (K + 1))
    (fun k δ C => ∀ ρ : Fin (k : ℕ) → ι, CoefBound r g k ρ δ C)
    (fun _ _ _ _ _ _ hδ hC h ρ => (h ρ).mono hδ hC)
    (fun k => coefBound_fixed hr (k : ℕ) (ha k))
  exact ⟨δ, hδ, C, hC, fun k hk ρ => h ⟨k, Nat.lt_succ_of_le hk⟩ ρ⟩

set_option maxHeartbeats 1000000 in
/-- **Uniform derivative bounds for analytic pointwise compositions.**  Let `A` be analytic at
`c`, `r ≥ 2` and `K ∈ ℕ`.  There are `δ > 0` and `C ≥ 0`, independent of the mesh, such that for
every `N` the map `u ↦ (x ↦ A(c + u(x)))` on `(H^r_h)^ι` satisfies
`DerivBound _ (ball 0 δ) K C`: it is `C^∞` there and `‖D^k‖ ≤ C` for `k ≤ K`. -/
theorem pointwise_derivBound (hr : 2 ≤ r) {A : (ι → ℝ) → ℝ} {c : ι → ℝ} (hA : AnalyticAt ℝ A c)
    (K : ℕ) : ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N],
      DerivBound (pointwise (N := N) (r := r) A c) (Metric.ball 0 δ) K C := by
  -- `g = A(c + ·)` is analytic on a ball `V` around `0`
  have hg0 : AnalyticAt ℝ (fun w : ι → ℝ => A (c + w)) 0 := by
    have : AnalyticAt ℝ (fun w : ι → ℝ => c + w) 0 := by fun_prop
    exact hA.comp_of_eq this (by simp)
  obtain ⟨R0, hR0, hgV⟩ := hg0.exists_ball_analyticOnNhd
  set g : (ι → ℝ) → ℝ := fun w => A (c + w)
  set V : Set (ι → ℝ) := Metric.ball 0 R0
  have hV : IsOpen V := Metric.isOpen_ball
  have hgC : ContDiffOn ℝ ∞ g V :=
    (hgV.contDiffOn_of_completeSpace).of_le (by exact_mod_cast le_top)
  -- analytic coefficients `a_{k,ρ}(w) = D^k g(w)[e_{ρ}]`
  have ha : ∀ (k : ℕ) (ρ : Fin k → ι), AnalyticAt ℝ
      (fun w : ι → ℝ => iteratedFDeriv ℝ k g w (fun m => Pi.single (ρ m) 1)) 0 := by
    intro k ρ
    have h1 : AnalyticAt ℝ (iteratedFDeriv ℝ k g) 0 :=
      hgV.iteratedFDeriv k 0 (Metric.mem_ball_self hR0)
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => ι → ℝ) ℝ
      (fun m => Pi.single (ρ m) 1)).analyticAt _ |>.comp h1
  -- uniform bounds over `k ≤ K` and `ρ`
  obtain ⟨δ1, hδ1, C1, hC1, hcoef⟩ := coefBound_uniform (r := r) hr ha K
  set δ := min δ1 (R0 / (Real.sqrt Kprod + 1)) with hδdef
  have hδ : 0 < δ := lt_min hδ1 (by positivity)
  refine ⟨δ / 2, by positivity, ((Fintype.card ι : ℝ) + 1) ^ K * Moser.algConst r ^ K * C1,
    mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (Moser.algConst_pos r).le _)) hC1, ?_⟩
  intro N _
  have hmaps : ∀ u : ι → GridH N r, u ∈ Metric.ball 0 (δ / 2) → ∀ x, evalAt x u ∈ V := by
    intro u hu x
    have hu' : ‖u‖ < δ / 2 := by simpa using hu
    show evalAt x u ∈ Metric.ball 0 R0
    rw [Metric.mem_ball, dist_zero_right]
    have h1 := norm_evalAt_le hr x u
    have h2 : δ ≤ R0 / (Real.sqrt Kprod + 1) := min_le_right _ _
    have hK := Real.sqrt_nonneg Kprod
    have h3 : Real.sqrt Kprod * ‖u‖ ≤ Real.sqrt Kprod * (δ / 2) :=
      mul_le_mul_of_nonneg_left hu'.le hK
    have h4 : Real.sqrt Kprod * (δ / 2) < R0 := by
      have : (Real.sqrt Kprod + 1) * δ ≤ R0 := by
        rw [le_div_iff₀ (by positivity)] at h2; linarith
      nlinarith
    linarith
  refine ⟨?_, fun u hu k hk => ?_⟩
  · -- smoothness
    rw [pointwise_eq]
    intro u hu
    refine (ContDiffAt.contDiffWithinAt ?_)
    have hΨ : ContDiffAt ℝ ∞ (fun u : ι → GridH N r => fun y => g (evalAt y u)) u := by
      refine contDiffAt_pi.2 fun y => ?_
      exact (hgC.contDiffAt (hV.mem_nhds (hmaps u hu y))).comp u
        (evalAt (N := N) (r := r) (ι := ι) y).contDiff.contDiffAt
    exact (toFunL (N := N) (r := r)).symm.contDiff.contDiffAt.comp u hΨ
  · -- bounds
    have hu' : ‖u‖ ≤ δ1 := by
      have : ‖u‖ < δ / 2 := by simpa using hu
      have h2 : δ ≤ δ1 := min_le_left _ _
      linarith
    refine ContinuousMultilinearMap.opNorm_le_bound
      (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (Moser.algConst_pos r).le _)) hC1)
      fun Y => ?_
    rw [pointwise_eq, norm_def]
    -- the derivative array, expanded in coordinates
    have hval : cxv (iteratedFDeriv ℝ k (fun u : ι → GridH N r =>
        (toFunL (r := r)).symm (fun y => g (evalAt y u))) u Y) =
        ∑ ρ : Fin k → ι, (fun x => ((iteratedFDeriv ℝ k g (evalAt x u)
          (fun m => Pi.single (ρ m) 1) : ℝ) : ℂ)) * ∏ m, cxv (Y m (ρ m)) := by
      funext x
      simp only [cxv]
      rw [iteratedFDeriv_pointwise_apply hgC hV (hmaps u hu) k Y x,
        Moser.multilinear_eq (Pi.basisFun ℝ ι)]
      simp only [Finset.sum_apply, Pi.mul_apply, Finset.prod_apply, Pi.basisFun_repr,
        Pi.basisFun_apply, evalAt_apply]
      push_cast
      refine sum_congr rfl fun ρ _ => ?_
      simp only [cxv]
      ring
    rw [hval]
    refine (Moser.sobNorm_sum_le r _ _).trans ?_
    have hterm : ∀ ρ : Fin k → ι, sobNorm r ((fun x => ((iteratedFDeriv ℝ k g (evalAt x u)
        (fun m => Pi.single (ρ m) 1) : ℝ) : ℂ)) * ∏ m, cxv (Y m (ρ m))) ≤
        Moser.algConst r ^ k * C1 * ∏ m, ‖Y m‖ := by
      intro ρ
      have hc := hcoef k hk ρ N u hu'
      -- product of `k + 1` arrays
      have hp := Moser.sobNorm_prod_le r hr k (Fin.cons (fun x => ((iteratedFDeriv ℝ k g
        (evalAt x u) (fun m => Pi.single (ρ m) 1) : ℝ) : ℂ)) fun m => cxv (Y m (ρ m)))
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ] at hp
      simp only [Fin.cons_zero, Fin.cons_succ] at hp
      refine hp.trans ?_
      have hY : ∏ m, sobNorm r (cxv (Y m (ρ m))) ≤ ∏ m, ‖Y m‖ :=
        prod_le_prod (fun _ _ => Moser.sobNorm_nonneg _ _) fun m _ => norm_le_pi_norm (Y m) (ρ m)
      have hA := Moser.algConst_pos r
      have h0 : 0 ≤ ∏ m, sobNorm r (cxv (Y m (ρ m))) := prod_nonneg fun _ _ => Moser.sobNorm_nonneg _ _
      calc Moser.algConst r ^ k * (sobNorm r (fun x => ((iteratedFDeriv ℝ k g (evalAt x u)
            (fun m => Pi.single (ρ m) 1) : ℝ) : ℂ)) * ∏ m, sobNorm r (cxv (Y m (ρ m))))
          ≤ Moser.algConst r ^ k * (C1 * ∏ m, ‖Y m‖) := by
            gcongr
        _ = Moser.algConst r ^ k * C1 * ∏ m, ‖Y m‖ := by ring
    refine (sum_le_sum fun ρ _ => hterm ρ).trans ?_
    rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
    have hY0 : 0 ≤ ∏ m, ‖Y m‖ := prod_nonneg fun _ _ => norm_nonneg _
    have hA1 : 1 ≤ Moser.algConst r := Moser.one_le_algConst r
    have hcard : (1 : ℝ) ≤ Fintype.card ι + 1 := by linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ Fintype.card ι)]
    have hpow : ((Fintype.card ι ^ k : ℕ) : ℝ) * Moser.algConst r ^ k ≤
        ((Fintype.card ι : ℝ) + 1) ^ K * Moser.algConst r ^ K := by
      push_cast
      have h1 : (Fintype.card ι : ℝ) ^ k ≤ ((Fintype.card ι : ℝ) + 1) ^ K :=
        (pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) k).trans (pow_le_pow_right₀ hcard hk)
      exact mul_le_mul h1 (pow_le_pow_right₀ hA1 hk) (by positivity) (by positivity)
    calc ((Fintype.card ι ^ k : ℕ) : ℝ) * (Moser.algConst r ^ k * C1 * ∏ m, ‖Y m‖)
        = (((Fintype.card ι ^ k : ℕ) : ℝ) * Moser.algConst r ^ k) * C1 * ∏ m, ‖Y m‖ := by ring
      _ ≤ (((Fintype.card ι : ℝ) + 1) ^ K * Moser.algConst r ^ K) * C1 * ∏ m, ‖Y m‖ := by
          gcongr
      _ = _ := by ring

end GridH

end

end RenewalGeometry.PeriodicGridSobolev
