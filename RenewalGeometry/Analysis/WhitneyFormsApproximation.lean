/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.WhitneyFormsGeneralDegree

/-!
# Approximation by Whitney forms and strong convergence of the projections (`lem:Whitney`)

Einstein–Standard-Model action-closure manuscript, `lem:Whitney` ("Commuting reconstruction and
positive comparison norm"), last sentence: *orthogonal projections `P_h^k` onto the Whitney ranges
converge strongly to the identity on `L²` `k`-forms*; proof as in the paper: "smooth forms are
approximated by their Whitney interpolants in `L²` (Taylor expansion on each cell and shape-regular
scaling); density of smooth forms and `‖P_h^k‖ ≤ 1` give strong convergence".  Built on
`WhitneyFormsGeneralDegree.lean` (Whitney forms of every degree, de Rham map, `R_h W_h = I`,
cellwise `d W_h = W_h d_h`, global mesh `WhitneyMesh`).

* `homog_edges`, `form_expand`, `sum_form_det`, `inner_sum`, `sum_edges_det`: multilinear algebra
  of a constant form in the barycentric frame (`Σ_m dλ_m(v)(v_m - x) = v`,
  `Σ_m λ_m(x)(v_m - x) = 0`, homogenisation `β(u₁-u₀, …) = Σ_l (-1)^l β(u ∘ succAbove l)`).
* **`W_R_const`: reproduction of constant forms**, `W_T R_T β = β` for every constant `k`-form `β`
  (at every point, in every degree).
* `norm_wedgeL_le`, `lam_mem_Icc`, `norm_whit_le`, `norm_W_le`, `abs_R_le`: cellwise bounds.
* **`norm_W_R_sub_le`: the local approximation estimate** `‖W_T R_T α - α‖ ≤ |ι|^{k+1} (L D)^k ω`
  on the simplex, `L ≥ ‖dλ_m‖`, `D ≥` edge lengths, `ω` the oscillation of `α` on the cell (the
  modulus of continuity in place of `h ‖∇α‖_∞`, so it applies to every continuous form);
  `norm_WG_RG_sub_le`: the same on the open cells of a `WhitneyMesh`.
* **`whitney_interpolant_tendsto_uniform` / `whitney_interpolant_tendsto_L2`**: on a sequence of
  meshes of a compact region `K` (cells cover `K` and lie in `K`), with mesh size `h_j → 0` and
  shape regularity `‖dλ_m‖ · |v_p - v_{p'}| ≤ σ` (`diam T · max|∇λ| ≤ σ`, equivalent up to the
  factors `1/2`, `n+1` to the classical `diam T/ρ_T ≤ σ'` since `1/ρ_T = Σ_m |∇λ_m|`),
  `W_h R_h α → α` uniformly a.e. on `K` and in `L²(K)` for every continuous (in particular every
  smooth) form `α` (`ae_mem_interior`: cell boundaries are null).
* `FormSpace`, `toForm`: the fibre `Λ^k` with the reference Hilbert norm
  `|α|² = Σ_q α(e_{q₀}, …, e_{q_{k-1}})²` in a fixed orthonormal frame (`= k! |α|²_{Λ^k}`, a constant
  multiple, hence the same orthogonal projections); `L²(K; Λ^k) = Lp (FormSpace E k) 2`.
* `whitneyMap`, `whitneyRange`: `W_h : C_h^k → L²(K; Λ^k)` and its (finite-dimensional, closed)
  range; `mem_whitneyRange_iff`: the range is the range on alternating (oriented) cochains
  (`W_altPart`: `W c = W (Alt c)`).
* `tendsto_starProjection_of_approx` (Hilbert-space lemma) and **`whitney_projection_tendsto`**:
  `P_{h_j}^k f → f` in `L²(K; Λ^k)` for every `f` (bounded continuous forms are dense,
  `‖f - P_h f‖ ≤ ‖f - W_h R_h α‖`).  Non-vacuity: the one-cell mesh of the zero-dimensional space.

Not covered (disclosed): the distributional (global weak) form of `d W_h = W_h d_h` across the
faces of the mesh; the paper's proof establishes the identity by differentiating the barycentric
formula cellwise (`WhitneyGen.WhitneyMesh.extDeriv_WG`, on the open cells, a full-measure set),
and the global weak form additionally needs Stokes' theorem on simplices and the pairing of
interior faces of the triangulation, neither of which is available.
-/

open MeasureTheory Set Finset Filter Topology
open scoped ENNReal NNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace RenewalGeometry
namespace WhitneyApprox

open WhitneyLow WhitneyGen

/-! ### Alternating maps: subtracting the first argument from the others -/

section AltAlgebra

variable {M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]

/-- For an alternating map, subtracting the `0`-th argument from all the others does not change
the value. -/
theorem alt_map_cons_sub {n : ℕ} (A : M [⋀^Fin (n + 1)]→ₗ[ℝ] N) (w : Fin (n + 1) → M) :
    A (Fin.cons (w 0) fun q => w q.succ - w 0) = A w := by
  classical
  have key : ∀ S : Finset (Fin n), A (Fin.cons (w 0) fun q => if q ∈ S then w q.succ - w 0
      else w q.succ) = A w := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      congr 1
      ext m
      refine Fin.cases ?_ (fun q => ?_) m <;> simp
    | insert q S hq ih =>
      have hupd : (Fin.cons (w 0) fun q' => if q' ∈ insert q S then w q'.succ - w 0
          else w q'.succ : Fin (n + 1) → M) = Function.update (Fin.cons (w 0) fun q' =>
            if q' ∈ S then w q'.succ - w 0 else w q'.succ) q.succ (w q.succ - w 0) := by
        ext m
        refine Fin.cases ?_ (fun q' => ?_) m
        · simp [Function.update_of_ne (Fin.succ_ne_zero q).symm]
        · by_cases hq' : q' = q
          · subst hq'; simp
          · rw [Function.update_of_ne (fun h => hq' (Fin.succ_injective _ h))]
            simp [hq']
      have hself : (Function.update (Fin.cons (w 0) fun q' =>
            if q' ∈ S then w q'.succ - w 0 else w q'.succ : Fin (n + 1) → M) q.succ (w q.succ))
          = Fin.cons (w 0) fun q' => if q' ∈ S then w q'.succ - w 0 else w q'.succ := by
        ext m
        refine Fin.cases ?_ (fun q' => ?_) m
        · simp [Function.update_of_ne (Fin.succ_ne_zero q).symm]
        · by_cases hq' : q' = q
          · subst hq'; simp [hq]
          · rw [Function.update_of_ne (fun h => hq' (Fin.succ_injective _ h))]
      rw [hupd, A.map_update_sub, hself, ih]
      have h0 : A (Function.update (Fin.cons (w 0) fun q' =>
            if q' ∈ S then w q'.succ - w 0 else w q'.succ : Fin (n + 1) → M) q.succ (w 0)) = 0 :=
        A.map_update_self _ (Fin.succ_ne_zero q)
      rw [h0, sub_zero]
  simpa using key Finset.univ

end AltAlgebra

/-! ### Homogenisation of a constant form on the edges of a face -/

section Homog

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Homogenisation identity**: `β(u₁ - u₀, …, u_k - u₀) = Σ_l (-1)^l β(u₀, …, û_l, …, u_k)`. -/
theorem homog_edges {k : ℕ} (β : E [⋀^Fin k]→L[ℝ] ℝ) (u : Fin (k + 1) → E) :
    β (fun q => u q.succ - u 0) = ∑ l : Fin (k + 1), (-1 : ℝ) ^ (l : ℕ) * β (u ∘ l.succAbove) := by
  set f : (ℝ × E) →ₗ[ℝ] (ℝ × E) [⋀^Fin k]→ₗ[ℝ] ℝ :=
    (LinearMap.fst ℝ ℝ E).smulRight (β.toAlternatingMap.compLinearMap (LinearMap.snd ℝ ℝ E))
  set A := AlternatingMap.alternatizeUncurryFin f
  have hA : ∀ w : Fin (k + 1) → ℝ × E, A w = ∑ l : Fin (k + 1),
      (-1 : ℝ) ^ (l : ℕ) * ((w l).1 * β (fun q => (w (l.succAbove q)).2)) := by
    intro w
    rw [AlternatingMap.alternatizeUncurryFin_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [f, Fin.removeNth, zsmul_eq_mul]
  set w : Fin (k + 1) → ℝ × E := fun m => (1, u m)
  have h1 : A w = ∑ l : Fin (k + 1), (-1 : ℝ) ^ (l : ℕ) * β (u ∘ l.succAbove) := by
    rw [hA]
    simp [w, Function.comp_def]
  have h2 : A (Fin.cons (w 0) fun q => w q.succ - w 0) = β (fun q => u q.succ - u 0) := by
    rw [hA, Fin.sum_univ_succ, Finset.sum_eq_zero (fun l _ => by simp [w])]
    simp [w]
  rw [← h2, alt_map_cons_sub, h1]

end Homog

/-! ### Reproduction of constant forms -/

section Reproduction

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (b : AffineBasis ι ℝ E)

/-- `Σ_m dλ_m(v) (v_m - x) = v`. -/
theorem sum_dlam_smul_sub (x v : E) : ∑ m, dlam b m v • (b m - x) = v := by
  have h1 := b.linear_combination_coord_eq_self (x + v)
  have h0 := b.linear_combination_coord_eq_self x
  have hl : ∀ m, b.coord m (x + v) = b.coord m x + dlam b m v := fun m => lam_add b m x v
  simp only [hl, add_smul, Finset.sum_add_distrib] at h1
  rw [h0] at h1
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, sum_dlam, zero_smul, sub_zero]
  linear_combination (norm := module) h1

/-- `Σ_m λ_m(x) (v_m - x) = 0`. -/
theorem sum_lam_smul_sub (x : E) : ∑ m, lam b m x • (b m - x) = 0 := by
  have h0 := b.linear_combination_coord_eq_self x
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, sum_lam, one_smul]
  rw [show ∑ m, lam b m x • b m = x from h0, sub_self]

/-- Multilinear expansion of a form in the barycentric frame. -/
theorem form_expand {k : ℕ} (β : E [⋀^Fin k]→L[ℝ] ℝ) (x : E) (v : Fin k → E) :
    ∑ j : Fin k → ι, (∏ q, dlam b (j q) (v q)) * β (fun q => b (j q) - x) = β v := by
  conv_rhs => rw [show v = fun q => ∑ m, dlam b m (v q) • (b m - x) from
    funext fun q => (sum_dlam_smul_sub b x (v q)).symm]
  have hs := β.toContinuousMultilinearMap.map_sum (fun q m => dlam b m (v q) • (b m - x))
  change _ = β.toContinuousMultilinearMap _
  rw [hs]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

/-- The differential matrix of a `k`-tuple of vertices on `k` vectors. -/
def dMatK {k : ℕ} (i : Fin k → ι) (v : Fin k → E) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun p q => dlam b (i p) (v q)

/-- `Σ_j β(v_j - x) det(dλ_{j_p}(v_q)) = k! β(v)`. -/
theorem sum_form_det {k : ℕ} (β : E [⋀^Fin k]→L[ℝ] ℝ) (x : E) (v : Fin k → E) :
    ∑ j : Fin k → ι, β (fun q => b (j q) - x) * (dMatK b j v).det = k.factorial * β v := by
  simp only [Matrix.det_apply, dMatK, Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  have key : ∀ σ : Equiv.Perm (Fin k), ∑ j : Fin k → ι, β (fun q => b (j q) - x) *
      (Equiv.Perm.sign σ • ∏ q, dlam b (j (σ q)) (v q)) = β v := by
    intro σ
    let e : (Fin k → ι) ≃ (Fin k → ι) := σ.symm.arrowCongr (Equiv.refl ι)
    have he : ∀ j, e j = j ∘ σ := fun j => by
      funext q; simp [e, Equiv.arrowCongr_apply]
    rw [← form_expand b β x v]
    refine Fintype.sum_equiv e _ _ fun j => ?_
    rw [he]
    have hperm : β (fun q => b (j q) - x) =
        (Equiv.Perm.sign σ⁻¹ : ℝ) * β (fun q => b ((j ∘ σ) q) - x) := by
      have := β.toAlternatingMap.map_perm (fun q => b ((j ∘ σ) q) - x) σ⁻¹
      have hc : (fun q => b ((j ∘ σ) q) - x) ∘ ⇑σ⁻¹ = fun q => b (j q) - x := by
        funext q; simp
      rw [hc] at this
      change β _ = _ • β _ at this
      rw [this, Units.smul_def, zsmul_eq_mul]
    rw [hperm, Units.smul_def, zsmul_eq_mul, Equiv.Perm.sign_inv]
    have hε : ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign σ : ℤ) : ℝ) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    simp only [Function.comp_apply]
    linear_combination ((∏ q, dlam b (j (σ q)) (v q)) * β fun q => b (j (σ q)) - x) * hε
  rw [Finset.sum_congr rfl fun σ _ => key σ, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

/-- The de Rham map of a constant form: `R β (a) = β(edges a) / k!`. -/
theorem R_const {k : ℕ} (β : E [⋀^Fin k]→L[ℝ] ℝ) (a : Fin (k + 1) → ι) :
    R b k (fun _ => β) a = 1 / (k.factorial : ℝ) * β (edges b a) := by
  rw [R, setIntegral_const, measureReal_def, volume_stdSimp, ENNReal.toReal_ofReal (by positivity),
    smul_eq_mul]

/-- The inner sums of the reproduction identity: summing over the vertex inserted at slot `j`. -/
theorem inner_sum {k : ℕ} (β : E [⋀^Fin k]→L[ℝ] ℝ) (x : E) (v : Fin k → E) (l j : Fin (k + 1)) :
    ∑ i : Fin (k + 1) → ι, lam b (i j) x * β (fun q => b (i (l.succAbove q)) - x) *
      (dMatK b (i ∘ j.succAbove) v).det = if l = j then (k.factorial : ℝ) * β v else 0 := by
  set G : (Fin (k + 1) → ι) → ℝ := fun i => lam b (i j) x *
    β (fun q => b (i (l.succAbove q)) - x) * (dMatK b (i ∘ j.succAbove) v).det with hG
  have hre := Fintype.sum_equiv (Fin.insertNthEquiv (fun _ => ι) j)
    (fun p => G (Fin.insertNthEquiv (fun _ => ι) j p)) G (fun p => rfl)
  have hc : ∀ (m : ι) (i' : Fin k → ι),
      (Fin.insertNthEquiv (fun _ => ι) j (m, i') : Fin (k + 1) → ι) ∘ j.succAbove = i' :=
    fun m i' => by funext q; simp
  rw [← hre, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [hG, hc]
  simp only [Fin.insertNthEquiv_apply, Fin.insertNth_apply_same]
  split_ifs with hlj
  · subst hlj
    simp only [Fin.insertNth_apply_succAbove]
    have : ∀ i' : Fin k → ι, ∑ m, lam b m x * β (fun q => b (i' q) - x) * (dMatK b i' v).det =
        β (fun q => b (i' q) - x) * (dMatK b i' v).det := by
      intro i'
      rw [← Finset.sum_mul, ← Finset.sum_mul, sum_lam, one_mul]
    rw [Finset.sum_congr rfl fun i' _ => this i', sum_form_det]
  · refine Finset.sum_eq_zero fun i' _ => ?_
    rcases isEmpty_or_nonempty ι with hι | ⟨⟨m₀⟩⟩
    · simp
    obtain ⟨p, hp⟩ := Fin.exists_succAbove_eq (Ne.symm hlj)
    set G : Fin k → E := fun q => b (Fin.insertNth (α := fun _ => ι) j m₀ i' (l.succAbove q)) - x
    have hF : ∀ m, (fun q => b (Fin.insertNth (α := fun _ => ι) j m i' (l.succAbove q)) - x) =
        Function.update G p (b m - x) := by
      intro m
      funext q
      by_cases hq : q = p
      · subst hq; simp [hp]
      · rw [Function.update_of_ne hq]
        have hne : l.succAbove q ≠ j := fun h => hq (l.succAbove_right_injective (h.trans hp.symm))
        obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq hne
        simp only [G, ← hr, Fin.insertNth_apply_succAbove]
    simp only [hF]
    have hsum : ∑ m, lam b m x * β (Function.update G p (b m - x)) = 0 := by
      have h1 : ∀ m, lam b m x * β (Function.update G p (b m - x)) =
          β (Function.update G p (lam b m x • (b m - x))) := by
        intro m; rw [ContinuousAlternatingMap.map_update_smul, smul_eq_mul]
      simp only [h1]
      have h2 := β.toAlternatingMap.map_update_sum Finset.univ p (fun m => lam b m x • (b m - x)) G
      change β _ = ∑ m, β _ at h2
      rw [← h2, sum_lam_smul_sub, ContinuousAlternatingMap.map_update_zero]
    rw [← Finset.sum_mul, hsum, zero_mul]

theorem det_baryMat_expand {k : ℕ} (i : Fin (k + 1) → ι) (x : E) (v : Fin k → E) :
    (baryMat b i x v).det = ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) * lam b (i j) x *
      (dMatK b (i ∘ j.succAbove) v).det := by
  rw [Matrix.det_succ_column_zero]
  rfl

/-- `Σ_i β(edges i) det(baryMat i x v) = (k+1)! β(v)`. -/
theorem sum_edges_det {k : ℕ} (β : E [⋀^Fin k]→L[ℝ] ℝ) (x : E) (v : Fin k → E) :
    ∑ i : Fin (k + 1) → ι, β (edges b i) * (baryMat b i x v).det =
      ((k + 1).factorial : ℝ) * β v := by
  have he : ∀ i : Fin (k + 1) → ι, β (edges b i) = ∑ l : Fin (k + 1),
      (-1 : ℝ) ^ (l : ℕ) * β (fun q => b (i (l.succAbove q)) - x) := by
    intro i
    have : edges b i = fun q => (b (i q.succ) - x) - (b (i 0) - x) := by
      funext q; simp [edges]
    rw [this]
    exact homog_edges β (fun m => b (i m) - x)
  simp only [he, det_baryMat_expand, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  have : ∀ l : Fin (k + 1), ∑ i : Fin (k + 1) → ι, ∑ j : Fin (k + 1),
      (-1 : ℝ) ^ (l : ℕ) * β (fun q => b (i (l.succAbove q)) - x) *
        ((-1 : ℝ) ^ (j : ℕ) * lam b (i j) x * (dMatK b (i ∘ j.succAbove) v).det) =
      (-1 : ℝ) ^ (l : ℕ) * ((-1 : ℝ) ^ (l : ℕ) * ((k.factorial : ℝ) * β v)) := by
    intro l
    rw [Finset.sum_comm]
    have h2 : ∀ j : Fin (k + 1), ∑ i : Fin (k + 1) → ι,
        (-1 : ℝ) ^ (l : ℕ) * β (fun q => b (i (l.succAbove q)) - x) *
          ((-1 : ℝ) ^ (j : ℕ) * lam b (i j) x * (dMatK b (i ∘ j.succAbove) v).det) =
        (-1 : ℝ) ^ (l : ℕ) * ((-1 : ℝ) ^ (j : ℕ) *
          (if l = j then (k.factorial : ℝ) * β v else 0)) := by
      intro j
      rw [← inner_sum b β x v l j, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [Finset.sum_congr rfl fun j _ => h2 j]
    simp
  rw [Finset.sum_congr rfl fun l _ => this l]
  have h1 : ∀ l : Fin (k + 1), (-1 : ℝ) ^ (l : ℕ) * ((-1 : ℝ) ^ (l : ℕ) * ((k.factorial : ℝ) * β v))
      = (k.factorial : ℝ) * β v := by
    intro l
    rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]; norm_num
  rw [Finset.sum_congr rfl fun l _ => h1 l, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.factorial_succ]
  push_cast; ring

/-- **Reproduction of constant forms**: `W_T R_T β = β` for every constant `k`-form `β`, at every
point. -/
theorem W_R_const {k : ℕ} (β : E [⋀^Fin k]→L[ℝ] ℝ) (x : E) :
    W b k (R b k fun _ => β) x = β := by
  ext v
  rw [W_apply]
  simp only [R_const]
  have : ∑ i : Fin (k + 1) → ι, 1 / (k.factorial : ℝ) * β (edges b i) *
      ((k.factorial : ℝ) * (baryMat b i x v).det) =
      ∑ i : Fin (k + 1) → ι, β (edges b i) * (baryMat b i x v).det := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (k.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  rw [this, sum_edges_det]
  have : ((k + 1).factorial : ℝ) ≠ 0 := by positivity
  field_simp

end Reproduction

/-! ### Norm bounds and the local approximation estimate -/

section Local

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (b : AffineBasis ι ℝ E)

/-- `‖f₀ ∧ ⋯ ∧ f_{m-1}‖ ≤ m! ∏ ‖f_p‖`. -/
theorem norm_wedgeL_le {m : ℕ} (f : Fin m → E →L[ℝ] ℝ) :
    ‖wedgeL f‖ ≤ m.factorial * ∏ p, ‖f p‖ := by
  refine ContinuousAlternatingMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [wedgeL_apply, Matrix.det_apply, Real.norm_eq_abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hσ : ∀ σ : Equiv.Perm (Fin m), |Equiv.Perm.sign σ • ∏ i, (Matrix.of fun p q => f p (v q)) (σ i) i|
      ≤ (∏ p, ‖f p‖) * ∏ i, ‖v i‖ := by
    intro σ
    rw [Units.smul_def, zsmul_eq_mul, abs_mul]
    have h1 : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    rw [h1, one_mul, Finset.abs_prod]
    calc ∏ i, |(Matrix.of fun p q => f p (v q)) (σ i) i| ≤ ∏ i, (‖f (σ i)‖ * ‖v i‖) :=
          Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => by
            simpa [Real.norm_eq_abs] using (f (σ i)).le_opNorm (v i)
      _ = (∏ p, ‖f p‖) * ∏ i, ‖v i‖ := by
          rw [Finset.prod_mul_distrib, Equiv.prod_comp σ (fun p => ‖f p‖)]
  calc ∑ σ : Equiv.Perm (Fin m), |Equiv.Perm.sign σ • ∏ i, (Matrix.of fun p q => f p (v q)) (σ i) i|
      ≤ ∑ _σ : Equiv.Perm (Fin m), (∏ p, ‖f p‖) * ∏ i, ‖v i‖ := Finset.sum_le_sum fun σ _ => hσ σ
    _ = (m.factorial * ∏ p, ‖f p‖) * ∏ i, ‖v i‖ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- Barycentric coordinates take values in `[0, 1]` on the closed simplex. -/
theorem lam_mem_Icc {x : E} (hx : x ∈ simplex b) (m : ι) : lam b m x ∈ Icc (0 : ℝ) 1 := by
  have hconv : Convex ℝ {y : E | lam b m y ∈ Icc (0 : ℝ) 1} :=
    (convex_Icc (0 : ℝ) 1).affine_preimage (b.coord m)
  have hsub : Set.range b ⊆ {y : E | lam b m y ∈ Icc (0 : ℝ) 1} := by
    rintro _ ⟨j, rfl⟩
    simp only [mem_ofPred_eq, lam_vertex, δ]
    split_ifs <;> norm_num
  exact convexHull_min hsub hconv hx

/-- `‖w_i(x)‖ ≤ k! (k+1) k! L^k` on the simplex if `‖dλ_m‖ ≤ L`. -/
theorem norm_whit_le {k : ℕ} (i : Fin (k + 1) → ι) {x : E} (hx : x ∈ simplex b) {L : ℝ}
    (hL : ∀ m, ‖dlam b m‖ ≤ L) :
    ‖whit b k i x‖ ≤ k.factorial * ((k + 1) * (k.factorial * L ^ k)) := by
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL (i 0))
  rw [whit, norm_smul, Real.norm_natCast]
  gcongr
  refine (norm_sum_le _ _).trans ?_
  have hj : ∀ j : Fin (k + 1), ‖((-1 : ℝ) ^ (j : ℕ) * lam b (i j) x) •
      wedgeL (fun p => dlam b (i (j.succAbove p)))‖ ≤ k.factorial * L ^ k := by
    intro j
    rw [norm_smul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs]
    have hl := lam_mem_Icc b hx (i j)
    rw [abs_of_nonneg hl.1]
    calc lam b (i j) x * ‖wedgeL fun p => dlam b (i (j.succAbove p))‖
        ≤ 1 * (k.factorial * ∏ p, ‖dlam b (i (j.succAbove p))‖) :=
          mul_le_mul hl.2 (norm_wedgeL_le _) (norm_nonneg _) zero_le_one
      _ ≤ 1 * (k.factorial * L ^ k) := by
          gcongr
          calc ∏ p, ‖dlam b (i (j.succAbove p))‖ ≤ ∏ _p : Fin k, L :=
                Finset.prod_le_prod (fun p _ => norm_nonneg _) fun p _ => hL _
            _ = L ^ k := by simp
      _ = k.factorial * L ^ k := one_mul _
  calc ∑ j : Fin (k + 1), ‖((-1 : ℝ) ^ (j : ℕ) * lam b (i j) x) •
        wedgeL (fun p => dlam b (i (j.succAbove p)))‖ ≤ ∑ _j : Fin (k + 1), k.factorial * L ^ k :=
        Finset.sum_le_sum fun j _ => hj j
    _ = (k + 1) * (k.factorial * L ^ k) := by simp

/-- `‖W c(x)‖ ≤ |ι|^{k+1} k! L^k max|c|` on the simplex. -/
theorem norm_W_le {k : ℕ} {c : (Fin (k + 1) → ι) → ℝ} {x : E} (hx : x ∈ simplex b) {L Mc : ℝ}
    (hL : ∀ m, ‖dlam b m‖ ≤ L) (hc : ∀ i, |c i| ≤ Mc) :
    ‖W b k c x‖ ≤ (Fintype.card ι : ℝ) ^ (k + 1) * k.factorial * L ^ k * Mc := by
  rw [W, norm_smul]
  have hk : (0 : ℝ) < ((k + 1).factorial : ℝ) := by positivity
  have hterm : ∀ i : Fin (k + 1) → ι, ‖c i • whit b k i x‖ ≤
      Mc * (k.factorial * ((k + 1) * (k.factorial * L ^ k))) := by
    intro i
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hc i) (norm_whit_le b i hx hL) (norm_nonneg _)
      ((abs_nonneg _).trans (hc i))
  calc ‖(1 / ((k + 1).factorial : ℝ))‖ * ‖∑ i, c i • whit b k i x‖
      ≤ (1 / ((k + 1).factorial : ℝ)) * ∑ _i : Fin (k + 1) → ι,
          Mc * (k.factorial * ((k + 1) * (k.factorial * L ^ k))) := by
        rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hterm i)
    _ = (Fintype.card ι : ℝ) ^ (k + 1) * k.factorial * L ^ k * Mc := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
          Nat.factorial_succ]
        push_cast
        field_simp

theorem isCompact_stdSimp (k : ℕ) : IsCompact (stdSimp k) := by
  have hcl : IsClosed (stdSimp k) := by
    have h1 : IsClosed {t : Fin k → ℝ | ∀ q, 0 ≤ t q} := by
      rw [ofPred_forall]
      exact isClosed_iInter fun q => isClosed_le continuous_const (continuous_apply q)
    have h2 : IsClosed {t : Fin k → ℝ | ∑ q, t q ≤ 1} :=
      isClosed_le (continuous_finsetSum _ fun q _ => continuous_apply q) continuous_const
    exact h1.inter h2
  refine (isCompact_univ_pi fun _ => isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset hcl
    fun t ht => ?_
  intro q _
  refine ⟨ht.1 q, ?_⟩
  have := Finset.single_le_sum (fun q _ => ht.1 q) (Finset.mem_univ q)
  linarith [ht.2]

theorem norm_edges_le {k : ℕ} (a : Fin (k + 1) → ι) {D : ℝ} (hD : ∀ p p', ‖b p - b p'‖ ≤ D)
    (q : Fin k) : ‖edges b a q‖ ≤ D := hD _ _

/-- The de Rham map of a form bounded by `Mγ` on the simplex: `|R γ(a)| ≤ Mγ D^k / k!`. -/
theorem abs_R_le {k : ℕ} (γ : E → E [⋀^Fin k]→L[ℝ] ℝ) {Mγ D : ℝ}
    (hγ : ∀ y ∈ simplex b, ‖γ y‖ ≤ Mγ) (hD : ∀ p p', ‖b p - b p'‖ ≤ D) (a : Fin (k + 1) → ι) :
    |R b k γ a| ≤ 1 / (k.factorial : ℝ) * (Mγ * D ^ k) := by
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD (a 0) (a 0))
  rw [R, ← Real.norm_eq_abs]
  have hvol : volume (stdSimp k) < ⊤ := by rw [volume_stdSimp]; exact ENNReal.ofReal_lt_top
  refine (norm_setIntegral_le_of_norm_le_const hvol (C := Mγ * D ^ k) fun t ht => ?_).trans ?_
  · refine ((γ (faceMap b a t)).le_opNorm _).trans ?_
    have hM := hγ _ (faceMap_mem b a ht)
    have hprod : ∏ q, ‖edges b a q‖ ≤ D ^ k := by
      calc ∏ q, ‖edges b a q‖ ≤ ∏ _q : Fin k, D :=
            Finset.prod_le_prod (fun q _ => norm_nonneg _) fun q _ => norm_edges_le b a hD q
        _ = D ^ k := by simp
    exact mul_le_mul hM hprod (by positivity) ((norm_nonneg _).trans hM)
  · rw [measureReal_def, volume_stdSimp, ENNReal.toReal_ofReal (by positivity)]
    linarith

/-- Linearity of the Whitney reconstruction in the cochain. -/
theorem W_sub {k : ℕ} (c c' : (Fin (k + 1) → ι) → ℝ) (x : E) :
    W b k (c - c') x = W b k c x - W b k c' x := by
  ext v
  rw [ContinuousAlternatingMap.sub_apply, W_apply, W_apply, W_apply]
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, mul_sub]

theorem integrableOn_face {k : ℕ} {α : E → E [⋀^Fin k]→L[ℝ] ℝ}
    (hα : ContinuousOn α (simplex b)) (a : Fin (k + 1) → ι) :
    IntegrableOn (fun t => α (faceMap b a t) (edges b a)) (stdSimp k) := by
  refine ContinuousOn.integrableOn_compact (isCompact_stdSimp k) ?_
  have hface : Continuous (faceMap b a) := by
    unfold faceMap
    fun_prop
  have h1 : ContinuousOn (fun t => α (faceMap b a t)) (stdSimp k) :=
    hα.comp hface.continuousOn fun t ht => faceMap_mem b a ht
  exact (continuous_eval_const (edges b a)).comp_continuousOn h1

/-- Linearity of the de Rham map on continuous forms. -/
theorem R_sub {k : ℕ} {α α' : E → E [⋀^Fin k]→L[ℝ] ℝ} (hα : ContinuousOn α (simplex b))
    (hα' : ContinuousOn α' (simplex b)) :
    R b k (fun y => α y - α' y) = R b k α - R b k α' := by
  funext a
  simp only [R, Pi.sub_apply, ContinuousAlternatingMap.sub_apply]
  exact integral_sub (integrableOn_face b hα a) (integrableOn_face b hα' a)

/-- **Local approximation estimate on one simplex**: if `‖dλ_m‖ ≤ L`, the edges have length
`≤ D`, and `α` oscillates by at most `ω` on the simplex, then
`‖W_T R_T α(x) - α(x)‖ ≤ |ι|^{k+1} (L D)^k ω` at every point `x` of the simplex (Taylor estimate
of `lem:Whitney`, with the modulus of continuity in place of `h ‖∇α‖_∞`). -/
theorem norm_W_R_sub_le {k : ℕ} {α : E → E [⋀^Fin k]→L[ℝ] ℝ} (hα : ContinuousOn α (simplex b))
    {L D ω : ℝ} (hL : ∀ m, ‖dlam b m‖ ≤ L) (hD : ∀ p p', ‖b p - b p'‖ ≤ D)
    (hω : ∀ y ∈ simplex b, ∀ z ∈ simplex b, ‖α y - α z‖ ≤ ω) {x : E} (hx : x ∈ simplex b) :
    ‖W b k (R b k α) x - α x‖ ≤ (Fintype.card ι : ℝ) ^ (k + 1) * (L * D) ^ k * ω := by
  set β := α x with hβ
  have hrep : β = W b k (R b k fun _ => β) x := (W_R_const b β x).symm
  have hsub : R b k α - R b k (fun _ => β) = R b k (fun y => α y - β) :=
    (R_sub b hα continuousOn_const).symm
  rw [show W b k (R b k α) x - β = W b k (R b k α) x - W b k (R b k fun _ => β) x by
    rw [← hrep], ← W_sub, hsub]
  have hγ : ∀ y ∈ simplex b, ‖α y - β‖ ≤ ω := fun y hy => hω y hy x hx
  have hc : ∀ a, |R b k (fun y => α y - β) a| ≤ 1 / (k.factorial : ℝ) * (ω * D ^ k) :=
    abs_R_le b _ hγ hD
  refine (norm_W_le b hx hL hc).trans (le_of_eq ?_)
  have : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

end Local

/-! ### The global mesh: cellwise estimate and linearity -/

section MeshEstimate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}

namespace WhitneyMeshAux

open WhitneyMesh

theorem cellCoch_RG (M : WhitneyMesh E n) {k : ℕ} (T : M.Cell) (α : E → E [⋀^Fin k]→L[ℝ] ℝ) :
    M.cellCoch T (M.RG α) = R (M.basis T) k α :=
  funext fun i => M.RG_eq_R T α i

/-- **Cellwise approximation estimate on a mesh**: on the open cell `T`,
`‖W_h R_h α(x) - α(x)‖ ≤ (n+1)^{k+1} (L D)^k ω`. -/
theorem norm_WG_RG_sub_le (M : WhitneyMesh E n) {k : ℕ} {α : E → E [⋀^Fin k]→L[ℝ] ℝ}
    {T : M.Cell} (hα : ContinuousOn α (simplex (M.basis T))) {L D ω : ℝ}
    (hL : ∀ m, ‖dlam (M.basis T) m‖ ≤ L) (hD : ∀ p p', ‖M.basis T p - M.basis T p'‖ ≤ D)
    (hω : ∀ y ∈ simplex (M.basis T), ∀ z ∈ simplex (M.basis T), ‖α y - α z‖ ≤ ω) {x : E}
    (hx : x ∈ interior (simplex (M.basis T))) :
    ‖M.WG (M.RG α) x - α x‖ ≤ ((n : ℝ) + 1) ^ (k + 1) * (L * D) ^ k * ω := by
  rw [M.WG_eq_of_mem _ hx]
  unfold WCell
  rw [cellCoch_RG]
  have := norm_W_R_sub_le (M.basis T) hα hL hD hω (interior_subset hx)
  simpa using this

theorem W_add {ι : Type*} [Fintype ι] [DecidableEq ι] (b : AffineBasis ι ℝ E) {k : ℕ}
    (c c' : (Fin (k + 1) → ι) → ℝ) (x : E) : W b k (c + c') x = W b k c x + W b k c' x := by
  ext v
  rw [ContinuousAlternatingMap.add_apply, W_apply, W_apply, W_apply]
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

theorem W_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (b : AffineBasis ι ℝ E) {k : ℕ}
    (r : ℝ) (c : (Fin (k + 1) → ι) → ℝ) (x : E) : W b k (r • c) x = r • W b k c x := by
  ext v
  rw [ContinuousAlternatingMap.smul_apply, W_apply, W_apply, smul_eq_mul, Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem WG_add (M : WhitneyMesh E n) {k : ℕ} (c c' : (Fin (k + 1) → M.V) → ℝ) (x : E) :
    M.WG (c + c') x = M.WG c x + M.WG c' x := by
  simp only [WG, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases hx : x ∈ interior (simplex (M.basis T))
  · simp only [Set.indicator_of_mem hx, WCell]
    exact W_add (M.basis T) _ _ x
  · simp [Set.indicator_of_notMem hx]

theorem WG_smul (M : WhitneyMesh E n) {k : ℕ} (r : ℝ) (c : (Fin (k + 1) → M.V) → ℝ) (x : E) :
    M.WG (r • c) x = r • M.WG c x := by
  simp only [WG, Finset.smul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases hx : x ∈ interior (simplex (M.basis T))
  · simp only [Set.indicator_of_mem hx, WCell]
    exact W_smul (M.basis T) r _ x
  · simp [Set.indicator_of_notMem hx]

/-- The global Whitney reconstruction is bounded. -/
theorem exists_bound_WG (M : WhitneyMesh E n) {k : ℕ} (c : (Fin (k + 1) → M.V) → ℝ) :
    ∃ B : ℝ, ∀ x, ‖M.WG c x‖ ≤ B := by
  have h : ∀ T : M.Cell, ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ simplex (M.basis T), ‖M.WCell T c y‖ ≤ B := by
    intro T
    obtain ⟨B, hB⟩ := (isCompact_simplex (M.basis T)).exists_bound_of_continuousOn
      (continuous_W (M.basis T) k (M.cellCoch T c)).continuousOn
    exact ⟨max B 0, le_max_right _ _, fun y hy => (hB y hy).trans (le_max_left _ _)⟩
  choose B hB0 hB using h
  refine ⟨∑ T, B T, fun x => (norm_sum_le _ _).trans (Finset.sum_le_sum fun T _ => ?_)⟩
  by_cases hx : x ∈ interior (simplex (M.basis T))
  · rw [Set.indicator_of_mem hx]; exact hB T x (interior_subset hx)
  · rw [Set.indicator_of_notMem hx, norm_zero]; exact hB0 T

theorem aestronglyMeasurable_WG (μ : Measure E)
    (M : WhitneyMesh E n) {k : ℕ} (c : (Fin (k + 1) → M.V) → ℝ) :
    AEStronglyMeasurable (M.WG c) μ := by
  have : M.WG c = fun x => ∑ T, (interior (simplex (M.basis T))).indicator
      (fun y => M.WCell T c y) x := rfl
  rw [this]
  refine Finset.aestronglyMeasurable_fun_sum _ fun T _ => ?_
  exact ((continuous_W (M.basis T) k (M.cellCoch T c)).aestronglyMeasurable).indicator
    isOpen_interior.measurableSet

/-- Almost every point of a region covered by the closed cells lies in an open cell (cell
boundaries are null sets). -/
theorem ae_mem_interior (μ : Measure E) [μ.IsAddHaarMeasure]
    (M : WhitneyMesh E n) {K : Set E} (hKm : MeasurableSet K)
    (hcover : K ⊆ ⋃ T, simplex (M.basis T)) :
    ∀ᵐ x ∂(μ.restrict K), ∃ T, x ∈ interior (simplex (M.basis T)) := by
  have hnull : μ (⋃ T, frontier (simplex (M.basis T))) = 0 :=
    measure_iUnion_null fun T => (convex_convexHull ℝ _).addHaar_frontier μ
  rw [ae_restrict_iff' hKm]
  refine measure_mono_null (fun x hx => ?_) hnull
  have hx' : ¬ (x ∈ K → ∃ T, x ∈ interior (simplex (M.basis T))) := hx
  push Not at hx'
  obtain ⟨hxK, hno⟩ := hx'
  obtain ⟨T, hT⟩ := mem_iUnion.mp (hcover hxK)
  exact mem_iUnion.mpr ⟨T, subset_closure hT, hno T⟩

end WhitneyMeshAux

end MeshEstimate

/-! ### Strong convergence of the Whitney interpolants -/

section Interpolant

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}

open WhitneyMesh WhitneyMeshAux

/-- **`W_h R_h α → α` uniformly on the covered region** (up to the null set of cell boundaries),
for a continuous form `α` on a shape-regular family of simplicial meshes of a compact region `K`
with mesh size `h_j → 0`.  Shape regularity is rendered as `‖dλ_m‖ · |v_p - v_{p'}| ≤ σ` on every
cell (equivalently `diam T · max_m |∇λ_m| ≤ σ`; since `1/ρ_T = Σ_m |∇λ_m|` this is equivalent, up to
the factors `1/2` and `n+1`, to the classical bound `diam T / ρ_T ≤ σ'` on the inradius). -/
theorem whitney_interpolant_tendsto_uniform (μ : Measure E) [μ.IsAddHaarMeasure] {k : ℕ}
    {K : Set E} (hK : IsCompact K) (M : ℕ → WhitneyMesh E n)
    (hcover : ∀ j, K ⊆ ⋃ T, simplex ((M j).basis T))
    (hsub : ∀ j T, simplex ((M j).basis T) ⊆ K) {h : ℕ → ℝ} (hh : Tendsto h atTop (𝓝 0))
    (hdiam : ∀ j T, ∀ y ∈ simplex ((M j).basis T), ∀ z ∈ simplex ((M j).basis T), dist y z ≤ h j)
    {σ : ℝ} (hshape : ∀ j T, ∃ L D : ℝ, (∀ m, ‖dlam ((M j).basis T) m‖ ≤ L) ∧
      (∀ p p', ‖(M j).basis T p - (M j).basis T p'‖ ≤ D) ∧ L * D ≤ σ)
    {α : E → E [⋀^Fin k]→L[ℝ] ℝ} (hα : Continuous α) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ᵐ x ∂(μ.restrict K), ‖(M j).WG ((M j).RG α) x - α x‖ ≤ ε := by
  set Cst : ℝ := ((n : ℝ) + 1) ^ (k + 1) * (max σ 0) ^ k + 1
  have hCst : 0 < Cst := by positivity
  obtain ⟨δ, hδ, hunif⟩ := Metric.uniformContinuousOn_iff_le.mp
    (hK.uniformContinuousOn_of_continuous hα.continuousOn) (ε / Cst) (by positivity)
  filter_upwards [hh.eventually (gt_mem_nhds hδ)] with j hj
  filter_upwards [ae_mem_interior μ (M j) hK.isClosed.measurableSet (hcover j)] with x hx
  obtain ⟨T, hxT⟩ := hx
  obtain ⟨L, D, hL, hD, hLD⟩ := hshape j T
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0 0)
  have hω : ∀ y ∈ simplex ((M j).basis T), ∀ z ∈ simplex ((M j).basis T),
      ‖α y - α z‖ ≤ ε / Cst := fun y hy z hz => by
    rw [← dist_eq_norm]
    exact hunif y (hsub j T hy) z (hsub j T hz) ((hdiam j T y hy z hz).trans hj.le)
  refine (norm_WG_RG_sub_le (M j) hα.continuousOn hL hD hω hxT).trans ?_
  have hpow : (L * D) ^ k ≤ (max σ 0) ^ k :=
    pow_le_pow_left₀ (mul_nonneg hL0 hD0) (hLD.trans (le_max_left _ _)) k
  calc ((n : ℝ) + 1) ^ (k + 1) * (L * D) ^ k * (ε / Cst)
      ≤ ((n : ℝ) + 1) ^ (k + 1) * (max σ 0) ^ k * (ε / Cst) := by gcongr
    _ ≤ Cst * (ε / Cst) := by gcongr; linarith
    _ = ε := by field_simp

/-- **`W_h R_h α → α` in `L²(K)`** for every continuous `k`-form `α` (in particular every smooth
one) on a shape-regular family of meshes of `K` with `h → 0` (`L²` of the operator norm). -/
theorem whitney_interpolant_tendsto_L2 (μ : Measure E) [μ.IsAddHaarMeasure] {k : ℕ}
    {K : Set E} (hK : IsCompact K) (M : ℕ → WhitneyMesh E n)
    (hcover : ∀ j, K ⊆ ⋃ T, simplex ((M j).basis T))
    (hsub : ∀ j T, simplex ((M j).basis T) ⊆ K) {h : ℕ → ℝ} (hh : Tendsto h atTop (𝓝 0))
    (hdiam : ∀ j T, ∀ y ∈ simplex ((M j).basis T), ∀ z ∈ simplex ((M j).basis T), dist y z ≤ h j)
    {σ : ℝ} (hshape : ∀ j T, ∃ L D : ℝ, (∀ m, ‖dlam ((M j).basis T) m‖ ≤ L) ∧
      (∀ p p', ‖(M j).basis T p - (M j).basis T p'‖ ≤ D) ∧ L * D ≤ σ)
    {α : E → E [⋀^Fin k]→L[ℝ] ℝ} (hα : Continuous α) :
    Tendsto (fun j => eLpNorm (fun x => (M j).WG ((M j).RG α) x - α x) 2 (μ.restrict K))
      atTop (𝓝 0) := by
  have hfin : μ.restrict K Set.univ ≠ ⊤ := by
    rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top.ne
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεt
  · exact Eventually.of_forall fun _ => le_top
  set A : ℝ≥0∞ := μ.restrict K Set.univ ^ (ENNReal.toReal 2)⁻¹
  have hAt : A ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hfin
  set η : ℝ := ε.toReal / (A.toReal + 1) with hη_def
  have hη : 0 < η := div_pos (ENNReal.toReal_pos hε.ne' hεt) (by positivity)
  filter_upwards [whitney_interpolant_tendsto_uniform μ hK M hcover hsub hh hdiam hshape hα hη]
    with j hj
  refine (eLpNorm_le_of_ae_bound hj).trans ?_
  have h1 : A * ENNReal.ofReal η = ENNReal.ofReal (A.toReal * η) := by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hAt]
  rw [h1]
  refine (ENNReal.ofReal_le_ofReal (?_ : A.toReal * η ≤ ε.toReal)).trans
    (ENNReal.ofReal_toReal_le)
  have hA0 : 0 ≤ A.toReal := ENNReal.toReal_nonneg
  calc A.toReal * η ≤ (A.toReal + 1) * η := by gcongr; linarith
    _ = ε.toReal := by rw [hη_def]; field_simp

end Interpolant

/-! ### Orthogonal projections in a Hilbert space -/

section Projection

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **Strong convergence of orthogonal projections from approximability**: if every vector is,
up to `ε`, eventually approximable from the subspaces `S_j`, then `P_{S_j} f → f`
(best approximation: `‖f - P_j f‖ ≤ ‖f - g‖` for `g ∈ S_j`). -/
theorem tendsto_starProjection_of_approx (S : ℕ → Submodule ℝ H)
    [∀ j, (S j).HasOrthogonalProjection] (f : H)
    (happrox : ∀ ε > 0, ∃ g : ℕ → H, (∀ j, g j ∈ S j) ∧ ∀ᶠ j in atTop, ‖f - g j‖ ≤ ε) :
    Tendsto (fun j => (S j).starProjection f) atTop (𝓝 f) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hg, hev⟩ := happrox (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun j hj => ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  have hmin : ‖f - (S j).starProjection f‖ ≤ ‖f - g j‖ := by
    rw [Submodule.starProjection_minimal]
    exact ciInf_le ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩ (⟨g j, hg j⟩ : S j)
  linarith [hN j hj]

end Projection

/-! ### The Hilbert space of `L²` `k`-forms and the Whitney subspaces -/

section FormSpace

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The components of a `k`-form in the fixed orthonormal reference frame `(e_i)`:
`α ↦ (α(e_{q₀}, …, e_{q_{k-1}}))_q`. -/
def formEmb (k : ℕ) :
    (E [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin k → Fin (Module.finrank ℝ E)) where
  toFun α := WithLp.toLp 2 fun q => α fun p => stdOrthonormalBasis ℝ E (q p)
  map_add' α β := by ext q; simp
  map_smul' c α := by ext q; simp

theorem formEmb_injective (k : ℕ) : Function.Injective (formEmb E k) := by
  intro α β h
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  refine Module.Basis.ext_alternating (stdOrthonormalBasis ℝ E).toBasis fun v _ => ?_
  have := congrArg (fun z : EuclideanSpace ℝ (Fin k → Fin (Module.finrank ℝ E)) => z v) h
  simpa [formEmb, OrthonormalBasis.coe_toBasis] using this

/-- **The fibre of `k`-forms with the reference Hilbert norm**: the range of the component map, a
finite-dimensional inner product space; `|α|² = Σ_q α(e_q)² = k! |α|²_{Λ^k}` (a constant multiple
of the standard `Λ^k` norm, hence the same orthogonal projections). -/
abbrev FormSpace (k : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin k → Fin (Module.finrank ℝ E))) :=
  LinearMap.range (formEmb E k)

/-- The identification of `k`-forms with `FormSpace`. -/
def toForm (k : ℕ) : (E [⋀^Fin k]→L[ℝ] ℝ) ≃ₗ[ℝ] FormSpace E k :=
  LinearEquiv.ofInjective _ (formEmb_injective E k)

variable {E}

theorem norm_toForm_le {k : ℕ} (α : E [⋀^Fin k]→L[ℝ] ℝ) :
    ‖toForm E k α‖ ≤ Real.sqrt (Fintype.card (Fin k → Fin (Module.finrank ℝ E))) * ‖α‖ := by
  have hco : ((toForm E k α : FormSpace E k) : EuclideanSpace ℝ _) = formEmb E k α := rfl
  rw [← Submodule.norm_coe, hco, EuclideanSpace.norm_eq]
  have hq : ∀ q : Fin k → Fin (Module.finrank ℝ E), ‖(formEmb E k α) q‖ ≤ ‖α‖ := by
    intro q
    simp only [formEmb, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply]
    refine (α.le_opNorm _).trans (le_of_eq ?_)
    simp [(stdOrthonormalBasis ℝ E).orthonormal.1]
  calc Real.sqrt (∑ q, ‖(formEmb E k α) q‖ ^ 2)
      ≤ Real.sqrt (∑ _q : Fin k → Fin (Module.finrank ℝ E), ‖α‖ ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum fun q _ =>
          pow_le_pow_left₀ (norm_nonneg _) (hq q) 2)
    _ = Real.sqrt (Fintype.card (Fin k → Fin (Module.finrank ℝ E))) * ‖α‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.sqrt_mul (by positivity),
          Real.sqrt_sq (norm_nonneg _)]

theorem continuous_toForm (k : ℕ) : Continuous (toForm E k) :=
  AddMonoidHomClass.continuous_of_bound (toForm E k) _ fun α => norm_toForm_le α

theorem continuous_toForm_symm (k : ℕ) : Continuous (toForm E k).symm :=
  (toForm E k).symm.toLinearMap.continuous_of_finiteDimensional

end FormSpace

/-! ### The Whitney subspaces of `L²(K; Λ^k)` and strong convergence of their projections -/

section WhitneyRange

set_option synthInstance.maxHeartbeats 400000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n k : ℕ} (μ : Measure E) [μ.IsAddHaarMeasure] {K : Set E}
  (hK : IsCompact K)

open WhitneyMesh WhitneyMeshAux

/-- The global Whitney reconstruction of a cochain, as a `FormSpace`-valued function. -/
def whitneyFun (M : WhitneyMesh E n) (c : (Fin (k + 1) → M.V) → ℝ) : E → FormSpace E k :=
  fun x => toForm E k (M.WG c x)

include hK in
theorem memLp_whitneyFun (M : WhitneyMesh E n) (c : (Fin (k + 1) → M.V) → ℝ) :
    MemLp (whitneyFun M c) 2 (μ.restrict K) := by
  have : IsFiniteMeasure (μ.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  obtain ⟨B, hB⟩ := exists_bound_WG M c
  refine MemLp.of_bound ((continuous_toForm k).comp_aestronglyMeasurable
    (aestronglyMeasurable_WG _ M c))
    (Real.sqrt (Fintype.card (Fin k → Fin (Module.finrank ℝ E))) * B)
    (ae_of_all _ fun x => (norm_toForm_le _).trans ?_)
  gcongr
  exact hB x

/-- The Whitney reconstruction `W_h c` as an element of `L²(K; Λ^k)`. -/
def whitneyLp (M : WhitneyMesh E n) (c : (Fin (k + 1) → M.V) → ℝ) :
    Lp (FormSpace E k) 2 (μ.restrict K) :=
  (memLp_whitneyFun μ hK M c).toLp _

/-- `W_h : C_h^k → L²(K; Λ^k)` as a linear map. -/
def whitneyMap (M : WhitneyMesh E n) :
    ((Fin (k + 1) → M.V) → ℝ) →ₗ[ℝ] Lp (FormSpace E k) 2 (μ.restrict K) where
  toFun c := whitneyLp μ hK M c
  map_add' c c' := by
    simp only [whitneyLp]
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (ae_of_all _ fun x => by
      simp [whitneyFun, WG_add, map_add])
  map_smul' r c := by
    simp only [whitneyLp, RingHom.id_apply]
    rw [← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (ae_of_all _ fun x => by
      simp [whitneyFun, WG_smul, map_smul])

/-- **The finite-element range of `W_h`** in `L²(K; Λ^k)`. -/
def whitneyRange (M : WhitneyMesh E n) : Submodule ℝ (Lp (FormSpace E k) 2 (μ.restrict K)) :=
  LinearMap.range (whitneyMap μ hK M)

instance (M : WhitneyMesh E n) : FiniteDimensional ℝ (whitneyRange (k := k) μ hK M) :=
  LinearMap.finiteDimensional_range _

instance (M : WhitneyMesh E n) :
    Submodule.HasOrthogonalProjection (𝕜 := ℝ) (E := Lp (FormSpace E k) 2 (μ.restrict K))
      (whitneyRange (k := k) μ hK M) :=
  haveI := FiniteDimensional.complete ℝ (whitneyRange (k := k) μ hK M)
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- **`lem:Whitney`, strong convergence of the projections**: on a shape-regular family of
simplicial meshes of the compact region `K` with mesh size `h_j → 0`, the orthogonal projections
`P_h^k` of `L²(K; Λ^k)` onto the Whitney ranges converge strongly to the identity:
`P_{h_j}^k f → f` for every `L²` `k`-form `f`.  (Proof: bounded continuous forms are dense, their
Whitney interpolants `W_h R_h α` converge in `L²` (`whitney_interpolant_tendsto_L2`), and
`‖f - P_h f‖ ≤ ‖f - W_h R_h α‖`.) -/
theorem whitney_projection_tendsto (M : ℕ → WhitneyMesh E n)
    (hcover : ∀ j, K ⊆ ⋃ T, simplex ((M j).basis T))
    (hsub : ∀ j T, simplex ((M j).basis T) ⊆ K) {h : ℕ → ℝ} (hh : Tendsto h atTop (𝓝 0))
    (hdiam : ∀ j T, ∀ y ∈ simplex ((M j).basis T), ∀ z ∈ simplex ((M j).basis T), dist y z ≤ h j)
    {σ : ℝ} (hshape : ∀ j T, ∃ L D : ℝ, (∀ m, ‖dlam ((M j).basis T) m‖ ≤ L) ∧
      (∀ p p', ‖(M j).basis T p - (M j).basis T p'‖ ≤ D) ∧ L * D ≤ σ)
    (f : Lp (FormSpace E k) 2 (μ.restrict K)) :
    Tendsto (fun j => Submodule.starProjection (𝕜 := ℝ) (E := Lp (FormSpace E k) 2 (μ.restrict K))
      (whitneyRange μ hK (M j)) f) atTop
      (𝓝 f) := by
  have : IsFiniteMeasure (μ.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  refine tendsto_starProjection_of_approx _ f fun ε hε => ?_
  obtain ⟨G, hG, hGmem⟩ := (Lp.memLp f).exists_boundedContinuous_eLpNorm_sub_le
    (by norm_num) (ε := ENNReal.ofReal (ε / 2)) (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  set α : E → E [⋀^Fin k]→L[ℝ] ℝ := fun x => (toForm E k).symm (G x)
  have hα : Continuous α := (continuous_toForm_symm k).comp G.continuous
  set Cf : ℝ := Real.sqrt (Fintype.card (Fin k → Fin (Module.finrank ℝ E)))
  have hCf : 0 ≤ Cf := Real.sqrt_nonneg _
  refine ⟨fun j => whitneyLp μ hK (M j) ((M j).RG α), fun j => ⟨_, rfl⟩, ?_⟩
  have hL2 := whitney_interpolant_tendsto_L2 μ hK M hcover hsub hh hdiam hshape hα
  have hev := (ENNReal.tendsto_nhds_zero.mp hL2) (ENNReal.ofReal (ε / 2 / (Cf + 1)))
    (ENNReal.ofReal_pos.mpr (by positivity))
  filter_upwards [hev] with j hj
  have h1 : ‖f - hGmem.toLp G‖ ≤ ε / 2 := by
    have : ‖f - hGmem.toLp G‖ = (eLpNorm (⇑f - ⇑G) 2 (μ.restrict K)).toReal := by
      conv_lhs => rw [← Lp.toLp_coeFn f (Lp.memLp f)]
      rw [← MemLp.toLp_sub, Lp.norm_toLp]
    rw [this]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hG
  have h2 : ‖hGmem.toLp G - whitneyLp μ hK (M j) ((M j).RG α)‖ ≤ ε / 2 := by
    rw [whitneyLp, ← MemLp.toLp_sub, Lp.norm_toLp]
    have hpt : ∀ x, ‖(⇑G - whitneyFun (M j) ((M j).RG α)) x‖ ≤
        Cf * ‖(M j).WG ((M j).RG α) x - α x‖ := by
      intro x
      have hGx : G x = toForm E k (α x) := ((toForm E k).apply_symm_apply (G x)).symm
      simp only [Pi.sub_apply, whitneyFun, hGx, ← map_sub]
      exact (norm_toForm_le _).trans (le_of_eq (by rw [norm_sub_rev]))
    have hle := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (ae_of_all _ hpt) 2 (μ := μ.restrict K)
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) (hle.trans ?_)
    calc ENNReal.ofReal Cf * eLpNorm (fun x => (M j).WG ((M j).RG α) x - α x) 2 (μ.restrict K)
        ≤ ENNReal.ofReal Cf * ENNReal.ofReal (ε / 2 / (Cf + 1)) := by gcongr
      _ = ENNReal.ofReal (Cf * (ε / 2 / (Cf + 1))) := (ENNReal.ofReal_mul hCf).symm
      _ ≤ ENNReal.ofReal (ε / 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [mul_div_assoc']
          rw [div_le_iff₀ (by positivity)]
          nlinarith
  calc ‖f - whitneyLp μ hK (M j) ((M j).RG α)‖
      ≤ ‖f - hGmem.toLp G‖ + ‖hGmem.toLp G - whitneyLp μ hK (M j) ((M j).RG α)‖ :=
        norm_sub_le_norm_sub_add_norm_sub f (hGmem.toLp G) _
    _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
    _ = ε := by ring

end WhitneyRange

/-! ### The Whitney range is the range on alternating cochains -/

section Alternation

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (b : AffineBasis ι ℝ E)

/-- The alternating part of a cochain, `(Alt c)_i = (1/(k+1)!) Σ_σ sign σ c_{i∘σ}`. -/
def altPart {κ : Type*} {k : ℕ} (c : (Fin (k + 1) → κ) → ℝ) : (Fin (k + 1) → κ) → ℝ :=
  fun i => 1 / ((k + 1).factorial : ℝ) * ∑ σ : Equiv.Perm (Fin (k + 1)),
    (Equiv.Perm.sign σ : ℝ) * c (i ∘ σ)

theorem sign_mul_self_real {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign σ : ℤ) : ℝ) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

theorem altPart_isAlt {κ : Type*} {k : ℕ} (c : (Fin (k + 1) → κ) → ℝ)
    (τ : Equiv.Perm (Fin (k + 1))) (i : Fin (k + 1) → κ) :
    altPart c (i ∘ τ) = (Equiv.Perm.sign τ : ℝ) * altPart c i := by
  have hsum : ∑ σ : Equiv.Perm (Fin (k + 1)), (Equiv.Perm.sign σ : ℝ) * c ((i ∘ τ) ∘ σ) =
      ∑ σ : Equiv.Perm (Fin (k + 1)), (Equiv.Perm.sign τ : ℝ) *
        ((Equiv.Perm.sign σ : ℝ) * c (i ∘ σ)) := by
    refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => ?_
    have hc : (i ∘ τ) ∘ σ = i ∘ ⇑(Equiv.mulLeft τ σ) := by
      funext q; simp
    have hs : (Equiv.Perm.sign (Equiv.mulLeft τ σ) : ℝ) =
        (Equiv.Perm.sign τ : ℝ) * (Equiv.Perm.sign σ : ℝ) := by
      simp [Equiv.Perm.sign_mul]
    rw [hc, hs]
    linear_combination (-(((Equiv.Perm.sign σ : ℤ) : ℝ) * c (i ∘ ⇑((Equiv.mulLeft τ) σ)))) *
      sign_mul_self_real τ
  simp only [altPart]
  rw [hsum, ← Finset.mul_sum]
  ring

theorem det_baryMat_perm {k : ℕ} (i : Fin (k + 1) → ι) (σ : Equiv.Perm (Fin (k + 1))) (x : E)
    (v : Fin k → E) :
    (baryMat b (i ∘ σ) x v).det = (Equiv.Perm.sign σ : ℝ) * (baryMat b i x v).det := by
  rw [← Matrix.det_permute]
  rfl

/-- **The Whitney reconstruction only sees the alternating part of a cochain**:
`W c = W (Alt c)`. -/
theorem sum_altPart_mul {κ : Type*} [Fintype κ] {k : ℕ} (c D : (Fin (k + 1) → κ) → ℝ)
    (hD : ∀ i (σ : Equiv.Perm (Fin (k + 1))), D (i ∘ σ) = (Equiv.Perm.sign σ : ℝ) * D i) :
    ∑ i, altPart c i * D i = ∑ i, c i * D i := by
  have key : ∀ σ : Equiv.Perm (Fin (k + 1)),
      ∑ i, (Equiv.Perm.sign σ : ℝ) * c (i ∘ σ) * D i = ∑ i, c i * D i := by
    intro σ
    let e : (Fin (k + 1) → κ) ≃ (Fin (k + 1) → κ) := σ.symm.arrowCongr (Equiv.refl κ)
    have he : ∀ i, e i = i ∘ σ := fun i => by funext q; simp [e, Equiv.arrowCongr_apply]
    refine Fintype.sum_equiv e _ _ fun i => ?_
    rw [he, hD]
    ring
  have h1 : ∀ i, altPart c i * D i = 1 / ((k + 1).factorial : ℝ) *
      ∑ σ : Equiv.Perm (Fin (k + 1)), (Equiv.Perm.sign σ : ℝ) * c (i ∘ σ) * D i := by
    intro i
    simp only [altPart, mul_assoc, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun i _ => h1 i, ← Finset.mul_sum, Finset.sum_comm,
    Finset.sum_congr rfl fun σ _ => key σ, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  have : ((k + 1).factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- **The Whitney reconstruction only sees the alternating part of a cochain**:
`W c = W (Alt c)`. -/
theorem W_altPart {k : ℕ} (c : (Fin (k + 1) → ι) → ℝ) (x : E) :
    W b k (altPart c) x = W b k c x := by
  ext v
  rw [W_apply, W_apply, sum_altPart_mul c (fun i => (k.factorial : ℝ) * (baryMat b i x v).det)
    fun i σ => by rw [det_baryMat_perm]; ring]

end Alternation

section AltRange

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n k : ℕ}

open WhitneyMesh

theorem WG_altPart (M : WhitneyMesh E n) (c : (Fin (k + 1) → M.V) → ℝ) :
    M.WG (altPart c) = M.WG c := by
  funext x
  simp only [WG]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases hx : x ∈ interior (simplex (M.basis T))
  · simp only [Set.indicator_of_mem hx, WCell]
    exact W_altPart (M.basis T) (M.cellCoch T c) x
  · simp [Set.indicator_of_notMem hx]

theorem isAltG_altPart (M : WhitneyMesh E n) (c : (Fin (k + 1) → M.V) → ℝ) :
    M.IsAltG (altPart c) := fun σ a => altPart_isAlt c σ a

variable (μ : Measure E) [μ.IsAddHaarMeasure] {K : Set E} (hK : IsCompact K)

/-- **The Whitney range is the range of `W_h` on alternating (oriented) cochains**: every
element of `whitneyRange` is `W_h c` for an alternating cochain `c` (`c = Alt c'`). -/
theorem mem_whitneyRange_iff (M : WhitneyMesh E n) (g : Lp (FormSpace E k) 2 (μ.restrict K)) :
    g ∈ whitneyRange μ hK M ↔ ∃ c, M.IsAltG c ∧ whitneyMap μ hK M c = g := by
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨altPart c, isAltG_altPart M c, ?_⟩
    simp only [whitneyMap, LinearMap.coe_mk, AddHom.coe_mk, whitneyLp]
    exact MemLp.toLp_congr _ _ (ae_of_all _ fun x => by simp only [whitneyFun, WG_altPart])
  · rintro ⟨c, -, rfl⟩
    exact ⟨c, rfl⟩

end AltRange

/-! ### Non-vacuity -/

section NonVacuity

/-- The zero-dimensional model space. -/
abbrev E0 := EuclideanSpace ℝ (Fin 0)

instance : Subsingleton E0 := by
  constructor
  intro x y
  ext i
  exact i.elim0

/-- The one-point simplex of the zero-dimensional space. -/
def pointBasis : AffineBasis (Fin 1) ℝ E0 where
  toFun := fun _ => 0
  ind' := affineIndependent_of_subsingleton ℝ _
  tot' := by
    refine eq_top_iff.mpr fun x _ => ?_
    have : x = 0 := Subsingleton.elim _ _
    subst this
    exact subset_affineSpan ℝ _ ⟨0, rfl⟩

/-- The one-cell mesh of the zero-dimensional space. -/
def pointMesh : WhitneyMesh E0 0 where
  V := Unit
  pos := fun _ => 0
  Cell := Unit
  vert := fun _ _ => ()
  vert_injective := fun _ p q _ => Fin.ext (by have := p.isLt; have := q.isLt; omega)
  basis := fun _ => pointBasis
  basis_apply := fun _ _ => rfl
  shared_face := fun _ _ => by
    have h1 : simplex pointBasis = {0} := by
      ext x
      simp only [Set.mem_singleton_iff]
      exact ⟨fun _ => Subsingleton.elim _ _, fun hx => hx ▸ subset_convexHull ℝ _ ⟨0, rfl⟩⟩
    rw [h1, Set.inter_self]
    have h2 : (fun _ : Unit => (0 : E0)) '' (Set.range (fun _ : Fin 1 => ()) ∩
        Set.range (fun _ : Fin 1 => ())) = {0} := by
      ext x
      constructor
      · rintro ⟨_, _, h⟩; exact h.symm
      · intro hx
        exact ⟨(), ⟨⟨0, rfl⟩, ⟨0, rfl⟩⟩, (Set.mem_singleton_iff.mp hx).symm⟩
    rw [h2, convexHull_singleton]
  interior_disjoint := fun T T' h => absurd (Subsingleton.elim T T') h

/-- **Non-vacuity of `whitney_projection_tendsto`**: the hypothesis packet (compact region, covering
meshes, mesh size `h_j → 0`, shape regularity) is satisfied by the constant one-cell mesh of the
zero-dimensional space, so the theorem applies (here in degree `0`). -/
example (μ : Measure E0) [μ.IsAddHaarMeasure]
    (f : Lp (FormSpace E0 0) 2 (μ.restrict {0})) :
    Tendsto (fun _j : ℕ => Submodule.starProjection (𝕜 := ℝ)
      (E := Lp (FormSpace E0 0) 2 (μ.restrict {0}))
      (whitneyRange μ isCompact_singleton pointMesh) f) atTop (𝓝 f) := by
  have hS : simplex pointBasis = {0} := by
    ext x
    simp only [Set.mem_singleton_iff]
    exact ⟨fun _ => Subsingleton.elim _ _, fun hx => hx ▸ subset_convexHull ℝ _ ⟨0, rfl⟩⟩
  refine whitney_projection_tendsto (k := 0) μ isCompact_singleton (fun _ => pointMesh)
    (fun _ => ?_) (fun _ _ => ?_) (h := fun _ => 0) tendsto_const_nhds (fun _ _ y _ z _ => ?_)
    (σ := 0) (fun _ _ => ⟨‖dlam pointBasis 0‖, 0, fun m => ?_, fun _ _ => ?_, by simp⟩) f
  · intro x hx
    exact Set.mem_iUnion.mpr ⟨(), by
      show x ∈ simplex pointBasis
      rw [hS]; exact hx⟩
  · show simplex pointBasis ⊆ {0}
    rw [hS]
  · rw [Subsingleton.elim y z, dist_self]
  · rw [show m = 0 from Fin.ext (by have := m.isLt; omega)]
    exact le_rfl
  · exact le_of_eq (norm_eq_zero.mpr (Subsingleton.elim _ _))

end NonVacuity

end WhitneyApprox
end RenewalGeometry
