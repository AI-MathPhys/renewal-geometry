/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Source-shorted occurrence Laplacian and Thomson correction

Exact encoding of `thm:accepted-occurrence-Laplacian` (AO.9–AO.13) on a finite edge set
`E` with source/target maps `src tgt : E → X` and a positive reference weight `R`.

Functions on edges carry the inner product `⟨h, k⟩ = ∑ h k / R`; `rowSum = A` and
`colSum = B` are the source and target marginal maps, `rowAdj = A^*`, `colAdj = B^*`
their weighted adjoints, `ν = A R`, `ρ = B R`, `Q(x, ·) = R(x, ·)/ν(x)`.

* `laplacian_apply` / `laplacian_matrix` (AO.9): `𝓛 u = B P_s B^* u = ρ u - Qᵀ diag(ν) Q u`;
* `laplacian_quad` (AO.10): `⟨u, 𝓛 u⟩ = ∑_x ν(x) Var_{Q(x,·)}(u)` (hence `𝓛 ⪰ 0`);
* `corrector_feasible` / `pythagoras` / `energy_eq` / `eq_corrector_of_min`
  (AO.11–AO.12): for `𝓛 u = d`, `h_* = R [u(y) - (Qu)(x)]` is the unique minimum-norm
  solution of `A h = 0`, `B h = d`, with `‖h_*‖² = ⟨d, u⟩`;
* `solvable_iff` (AO.11): the constraints are solvable exactly when `d ∈ Ran 𝓛`;
* `occupation_pos` / `occupation_rowSum` / `occupation_colSum` / `kl_bounds` /
  `occupationDefect_le` (AO.13): under leverage `ϑ ≤ 1/2`, `π = R + h_*` is a positive
  coupling with marginals `ν` and `𝓔/3 ≤ D_KL(π ‖ R) ≤ 𝓔`, so the occupation defect is at
  most `𝓔`;
* `ker_iff_const_on_rows`: `ker 𝓛` consists of the functions constant on every row
  support (hence on the components of the target-overlap graph).
-/

open Finset
open scoped InnerProductSpace

namespace NCG
namespace AcceptedOccurrenceLaplacian

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

variable {X E : Type*} [Fintype X] [Fintype E] [DecidableEq X]
variable (src tgt : E → X) (R : E → ℝ)

/-! ### Weighted inner product, marginal maps and adjoints -/

/-- `⟨h, k⟩_{R⁻¹} = ∑ h k / R`. -/
def wip (h k : E → ℝ) : ℝ := ∑ e, h e * k e / R e

/-- The source marginal `A h (x) = ∑_{e : src e = x} h e`. -/
def rowSum (h : E → ℝ) (x : X) : ℝ := ∑ e, if src e = x then h e else 0

/-- The target marginal `B h (y) = ∑_{e : tgt e = y} h e`. -/
def colSum (h : E → ℝ) (y : X) : ℝ := ∑ e, if tgt e = y then h e else 0

/-- `A^* f = R · (f ∘ src)`. -/
def rowAdj (f : X → ℝ) : E → ℝ := fun e => R e * f (src e)

/-- `B^* g = R · (g ∘ tgt)`. -/
def colAdj (g : X → ℝ) : E → ℝ := fun e => R e * g (tgt e)

/-- `ν = A R`. -/
def nu (x : X) : ℝ := rowSum src R x

/-- `ρ = B R`. -/
def rho (y : X) : ℝ := colSum tgt R y

/-- `(Q u)(x) = ∑_{e : src e = x} R e u(tgt e) / ν(x)`. -/
noncomputable def Qu (u : X → ℝ) (x : X) : ℝ :=
  (∑ e, if src e = x then R e * u (tgt e) else 0) / nu src R x

theorem sum_mul_rowSum (g : X → ℝ) (h : E → ℝ) :
    ∑ x, g x * rowSum src h x = ∑ e, g (src e) * h e := by
  unfold rowSum
  simp only [mul_sum, mul_ite, mul_zero]
  rw [sum_comm]
  simp

theorem sum_mul_colSum (g : X → ℝ) (h : E → ℝ) :
    ∑ y, g y * colSum tgt h y = ∑ e, g (tgt e) * h e := by
  unfold colSum
  simp only [mul_sum, mul_ite, mul_zero]
  rw [sum_comm]
  simp

theorem sum_rowSum (h : E → ℝ) : ∑ x, rowSum src h x = ∑ e, h e := by
  have := sum_mul_rowSum src (fun _ => (1 : ℝ)) h
  simpa using this

theorem sum_colSum (h : E → ℝ) : ∑ y, colSum tgt h y = ∑ e, h e := by
  have := sum_mul_colSum tgt (fun _ => (1 : ℝ)) h
  simpa using this

/-- Fibrewise summation over sources. -/
theorem sum_sum_ite_src (F : E → X → ℝ) :
    ∑ x, ∑ e, (if src e = x then F e x else 0) = ∑ e, F e (src e) := by
  rw [sum_comm]
  simp

theorem rowSum_sub (h k : E → ℝ) (x : X) :
    rowSum src (h - k) x = rowSum src h x - rowSum src k x := by
  unfold rowSum; rw [← sum_sub_distrib]; refine sum_congr rfl fun e _ => ?_; split_ifs <;> simp

theorem colSum_sub (h k : E → ℝ) (y : X) :
    colSum tgt (h - k) y = colSum tgt h y - colSum tgt k y := by
  unfold colSum; rw [← sum_sub_distrib]; refine sum_congr rfl fun e _ => ?_; split_ifs <;> simp

theorem rowSum_add (h k : E → ℝ) (x : X) :
    rowSum src (h + k) x = rowSum src h x + rowSum src k x := by
  unfold rowSum; rw [← sum_add_distrib]; refine sum_congr rfl fun e _ => ?_; split_ifs <;> simp

theorem colSum_add (h k : E → ℝ) (y : X) :
    colSum tgt (h + k) y = colSum tgt h y + colSum tgt k y := by
  unfold colSum; rw [← sum_add_distrib]; refine sum_congr rfl fun e _ => ?_; split_ifs <;> simp

variable {R}

theorem wip_rowAdj (hR : ∀ e, 0 < R e) (f : X → ℝ) (h : E → ℝ) :
    wip R (rowAdj src R f) h = ∑ x, f x * rowSum src h x := by
  rw [sum_mul_rowSum]
  unfold wip rowAdj
  refine sum_congr rfl fun e _ => ?_
  field_simp [(hR e).ne']

theorem wip_colAdj (hR : ∀ e, 0 < R e) (g : X → ℝ) (h : E → ℝ) :
    wip R (colAdj tgt R g) h = ∑ y, g y * colSum tgt h y := by
  rw [sum_mul_colSum]
  unfold wip colAdj
  refine sum_congr rfl fun e _ => ?_
  field_simp [(hR e).ne']

theorem wip_comm (h k : E → ℝ) : wip R h k = wip R k h := by
  unfold wip; refine sum_congr rfl fun e _ => ?_; ring

theorem wip_sub_left (h k l : E → ℝ) : wip R (h - k) l = wip R h l - wip R k l := by
  unfold wip; rw [← sum_sub_distrib]; refine sum_congr rfl fun e _ => ?_; simp [sub_mul, sub_div]

theorem wip_add_left (h k l : E → ℝ) : wip R (h + k) l = wip R h l + wip R k l := by
  unfold wip; rw [← sum_add_distrib]; refine sum_congr rfl fun e _ => ?_; simp [add_mul, add_div]

theorem wip_self_nonneg (hR : ∀ e, 0 < R e) (h : E → ℝ) : 0 ≤ wip R h h :=
  sum_nonneg fun e _ => div_nonneg (mul_self_nonneg _) (hR e).le

theorem wip_self_eq_zero (hR : ∀ e, 0 < R e) (h : E → ℝ) (h0 : wip R h h = 0) : h = 0 := by
  unfold wip at h0
  rw [sum_eq_zero_iff_of_nonneg (fun e _ => div_nonneg (mul_self_nonneg _) (hR e).le)] at h0
  funext e
  have := h0 e (mem_univ e)
  rw [div_eq_zero_iff] at this
  rcases this with h1 | h1
  · exact mul_self_eq_zero.mp h1
  · exact absurd h1 (hR e).ne'

/-- `A A^* = diag ν`. -/
theorem rowSum_rowAdj (f : X → ℝ) (x : X) : rowSum src (rowAdj src R f) x = nu src R x * f x := by
  simp only [nu, rowSum, rowAdj]
  rw [sum_mul]
  refine sum_congr rfl fun e _ => ?_
  split_ifs with h
  · rw [h]
  · simp

/-- `B B^* = diag ρ`. -/
theorem colSum_colAdj (g : X → ℝ) (y : X) : colSum tgt (colAdj tgt R g) y = rho tgt R y * g y := by
  simp only [rho, colSum, colAdj]
  rw [sum_mul]
  refine sum_congr rfl fun e _ => ?_
  split_ifs with h
  · rw [h]
  · simp

theorem nu_pos_of_src (hR : ∀ e, 0 < R e) (e : E) : 0 < nu src R (src e) := by
  unfold nu rowSum
  calc (0 : ℝ) < R e := hR e
    _ = (if src e = src e then R e else 0) := by simp
    _ ≤ ∑ e', (if src e' = src e then R e' else 0) :=
      single_le_sum (f := fun e' => if src e' = src e then R e' else 0)
        (fun e' _ => by split_ifs <;> first | exact (hR e').le | exact le_rfl) (mem_univ e)

/-- `∑_{e : src e = x} R e u(tgt e) = ν(x) (Qu)(x)` whenever `x` carries an edge. -/
theorem sum_src_eq_nu_mul_Qu (hR : ∀ e, 0 < R e) (u : X → ℝ) (x : X) :
    (∑ e, if src e = x then R e * u (tgt e) else 0) = nu src R x * Qu src tgt R u x := by
  unfold Qu
  by_cases hx : nu src R x = 0
  · rw [hx, zero_mul]
    refine sum_eq_zero fun e _ => ?_
    split_ifs with h
    · exfalso
      have := nu_pos_of_src src hR e
      rw [h, hx] at this
      exact lt_irrefl _ this
    · rfl
  · rw [mul_div_cancel₀ _ hx]

/-! ### The source projection and the Laplacian -/

variable (R)

/-- `P_s h = h - A^* diag(ν)⁻¹ A h`. -/
noncomputable def sourceProj (h : E → ℝ) : E → ℝ :=
  fun e => h e - R e * (rowSum src h (src e) / nu src R (src e))

/-- The Thomson corrector `h_*(x, y) = R(x, y) [u(y) - (Qu)(x)]` (AO.12). -/
noncomputable def corrector (u : X → ℝ) : E → ℝ :=
  fun e => R e * (u (tgt e) - Qu src tgt R u (src e))

/-- The source-shorted occurrence Laplacian `𝓛 = B P_s B^*`. -/
noncomputable def laplacian (u : X → ℝ) : X → ℝ :=
  colSum tgt (sourceProj src R (colAdj tgt R u))

variable {R}

/-- `P_s B^* u = h_*`. -/
theorem sourceProj_colAdj (u : X → ℝ) :
    sourceProj src R (colAdj tgt R u) = corrector src tgt R u := by
  funext e
  unfold sourceProj corrector colAdj rowSum Qu
  ring

theorem laplacian_eq (u : X → ℝ) : laplacian src tgt R u = colSum tgt (corrector src tgt R u) := by
  unfold laplacian
  rw [sourceProj_colAdj]

/-- `P_s` fixes the source-balanced currents. -/
theorem sourceProj_of_rowSum_zero (h : E → ℝ) (hA : ∀ x, rowSum src h x = 0) :
    sourceProj src R h = h := by
  funext e
  unfold sourceProj
  rw [hA, zero_div, mul_zero, sub_zero]

/-- `P_s` is self-adjoint for the weighted inner product. -/
theorem wip_sourceProj (hR : ∀ e, 0 < R e) (h k : E → ℝ) :
    wip R (sourceProj src R h) k = wip R h (sourceProj src R k) := by
  have key : ∀ h k : E → ℝ, wip R (sourceProj src R h) k
      = wip R h k - ∑ x, rowSum src h x * rowSum src k x / nu src R x := by
    intro h k
    have e1 : ∀ e, (h e - R e * (rowSum src h (src e) / nu src R (src e))) * k e / R e
        = h e * k e / R e - rowSum src h (src e) / nu src R (src e) * k e := by
      intro e
      have hb := (nu_pos_of_src src hR e).ne'
      have hR' := (hR e).ne'
      field_simp
    unfold wip sourceProj
    simp only [e1, sum_sub_distrib]
    congr 1
    have hf : ∑ e, rowSum src h (src e) / nu src R (src e) * k e
        = ∑ x, ∑ e, if src e = x then rowSum src h x / nu src R x * k e else 0 :=
      (sum_sum_ite_src src fun e x => rowSum src h x / nu src R x * k e).symm
    rw [hf]
    refine sum_congr rfl fun x _ => ?_
    rw [mul_div_right_comm]
    unfold rowSum
    rw [mul_sum]
    refine sum_congr rfl fun e _ => ?_
    split_ifs <;> simp
  rw [key h k, wip_comm h (sourceProj src R k), key k h, wip_comm k h]
  congr 1
  refine sum_congr rfl fun x _ => ?_
  ring

/-- `A h_* = 0` (`A P_s = 0`). -/
theorem rowSum_corrector (hR : ∀ e, 0 < R e) (u : X → ℝ) (x : X) :
    rowSum src (corrector src tgt R u) x = 0 := by
  unfold rowSum corrector
  have key : ∑ e, (if src e = x then R e * (u (tgt e) - Qu src tgt R u (src e)) else 0)
      = (∑ e, if src e = x then R e * u (tgt e) else 0) - Qu src tgt R u x * nu src R x := by
    unfold nu rowSum
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun e _ => ?_
    split_ifs with h
    · rw [h]; ring
    · simp
  rw [key, sum_src_eq_nu_mul_Qu src tgt hR, mul_comm, sub_self]


/-- **(AO.9, edge form)**: `𝓛 u (y) = ρ(y) u(y) - ∑_{e : tgt e = y} R e (Qu)(src e)`. -/
theorem laplacian_apply (u : X → ℝ) (y : X) :
    laplacian src tgt R u y
      = rho tgt R y * u y - ∑ e, (if tgt e = y then R e * Qu src tgt R u (src e) else 0) := by
  rw [laplacian_eq]
  unfold colSum corrector rho colSum
  rw [sum_mul, ← sum_sub_distrib]
  refine sum_congr rfl fun e _ => ?_
  split_ifs with h
  · rw [h]; ring
  · simp

variable (R) in
/-- The transition matrix `Q(x, y) = ∑_{e : x → y} R e / ν(x)`. -/
def Qmat (x y : X) : ℝ :=
  (∑ e, if src e = x ∧ tgt e = y then R e else 0) / nu src R x

/-- **(AO.9, matrix form)**: `𝓛 = diag(ρ) - Qᵀ diag(ν) Q`. -/
theorem laplacian_matrix (hR : ∀ e, 0 < R e) (u : X → ℝ) (y : X) :
    laplacian src tgt R u y
      = rho tgt R y * u y - ∑ x, Qmat src tgt R x y * nu src R x * Qu src tgt R u x := by
  rw [laplacian_apply]
  congr 1
  have hf : ∑ e, (if tgt e = y then R e * Qu src tgt R u (src e) else 0)
      = ∑ x, ∑ e, if src e = x then (if tgt e = y then R e * Qu src tgt R u x else 0) else 0 := by
    rw [sum_sum_ite_src src fun e x => if tgt e = y then R e * Qu src tgt R u x else 0]
  rw [hf]
  refine sum_congr rfl fun x _ => ?_
  unfold Qmat
  by_cases hx : nu src R x = 0
  · rw [hx, div_zero, zero_mul, zero_mul]
    refine sum_eq_zero fun e _ => ?_
    split_ifs with h1 h2
    · exfalso
      have := nu_pos_of_src src hR e
      rw [h1, hx] at this
      exact lt_irrefl _ this
    · rfl
    · rfl
  · rw [div_mul_cancel₀ _ hx, sum_mul]
    refine sum_congr rfl fun e _ => ?_
    by_cases h1 : src e = x <;> by_cases h2 : tgt e = y <;> simp [h1, h2]

/-- The symmetric bilinear form of the Laplacian through the corrector. -/
theorem sum_mul_laplacian (hR : ∀ e, 0 < R e) (u v : X → ℝ) :
    ∑ y, v y * laplacian src tgt R u y
      = ∑ e, R e * (u (tgt e) - Qu src tgt R u (src e)) * (v (tgt e) - Qu src tgt R v (src e)) := by
  rw [laplacian_eq, sum_mul_colSum]
  have h0 : ∑ e, Qu src tgt R v (src e) * corrector src tgt R u e = 0 := by
    rw [← sum_mul_rowSum]
    simp [rowSum_corrector src tgt hR]
  have : ∑ e, v (tgt e) * corrector src tgt R u e
      = ∑ e, (v (tgt e) - Qu src tgt R v (src e)) * corrector src tgt R u e
        + ∑ e, Qu src tgt R v (src e) * corrector src tgt R u e := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun e _ => ?_
    ring
  rw [this, h0, add_zero]
  refine sum_congr rfl fun e _ => ?_
  unfold corrector
  ring

/-- **(AO.10)**: `⟨u, 𝓛 u⟩ = ∑_x ν(x) Var_{Q(x,·)}(u)`, the row-variance form. -/
theorem laplacian_quad (hR : ∀ e, 0 < R e) (u : X → ℝ) :
    ∑ y, u y * laplacian src tgt R u y
      = ∑ x, ∑ e, (if src e = x then R e * (u (tgt e) - Qu src tgt R u x) ^ 2 else 0) := by
  rw [sum_mul_laplacian src tgt hR,
    sum_sum_ite_src src fun e x => R e * (u (tgt e) - Qu src tgt R u x) ^ 2]
  all_goals (refine sum_congr rfl fun e _ => ?_; ring)

/-- `𝓛 ⪰ 0`. -/
theorem laplacian_quad_nonneg (hR : ∀ e, 0 < R e) (u : X → ℝ) :
    0 ≤ ∑ y, u y * laplacian src tgt R u y := by
  rw [laplacian_quad src tgt hR]
  refine sum_nonneg fun x _ => sum_nonneg fun e _ => ?_
  split_ifs
  · exact mul_nonneg (hR e).le (sq_nonneg _)
  · exact le_rfl

/-- The Laplacian is symmetric. -/
theorem laplacian_symm (hR : ∀ e, 0 < R e) (u v : X → ℝ) :
    ∑ y, v y * laplacian src tgt R u y = ∑ y, u y * laplacian src tgt R v y := by
  rw [sum_mul_laplacian src tgt hR, sum_mul_laplacian src tgt hR]
  refine sum_congr rfl fun e _ => ?_
  ring

/-! ### Minimum-norm correction (AO.11–AO.12) -/

/-- The occurrence constraints `A h = 0`, `B h = d`. -/
def Feasible (d : X → ℝ) (h : E → ℝ) : Prop :=
  (∀ x, rowSum src h x = 0) ∧ ∀ y, colSum tgt h y = d y

/-- **(AO.12)**: `h_* = P_s B^* u` is feasible when `𝓛 u = d`. -/
theorem corrector_feasible (hR : ∀ e, 0 < R e) {u d : X → ℝ} (hL : laplacian src tgt R u = d) :
    Feasible src tgt d (corrector src tgt R u) :=
  ⟨rowSum_corrector src tgt hR u, fun y => by rw [← hL, laplacian_eq]⟩

theorem wip_corrector (hR : ∀ e, 0 < R e) (k : E → ℝ) (u : X → ℝ) :
    wip R k (corrector src tgt R u)
      = ∑ y, u y * colSum tgt k y - ∑ x, Qu src tgt R u x * rowSum src k x := by
  rw [sum_mul_colSum, sum_mul_rowSum, ← sum_sub_distrib]
  unfold wip corrector
  refine sum_congr rfl fun e _ => ?_
  field_simp [(hR e).ne']

/-- **Pythagoras**: any feasible `h` decomposes as `h_* ⊕ (h - h_*)` orthogonally. -/
theorem pythagoras (hR : ∀ e, 0 < R e) {u d : X → ℝ} (hL : laplacian src tgt R u = d)
    {h : E → ℝ} (hf : Feasible src tgt d h) :
    wip R h h = wip R (corrector src tgt R u) (corrector src tgt R u)
      + wip R (h - corrector src tgt R u) (h - corrector src tgt R u) := by
  have hf' := corrector_feasible src tgt hR hL
  have hcross : wip R (h - corrector src tgt R u) (corrector src tgt R u) = 0 := by
    rw [wip_corrector src tgt hR]
    have h1 : ∀ y, colSum tgt (h - corrector src tgt R u) y = 0 := fun y => by
      rw [colSum_sub, hf.2 y, hf'.2 y, sub_self]
    have h2 : ∀ x, rowSum src (h - corrector src tgt R u) x = 0 := fun x => by
      rw [rowSum_sub, hf.1 x, hf'.1 x, sub_self]
    simp [h1, h2]
  have hadd_right : ∀ l h k : E → ℝ, wip R l (h + k) = wip R l h + wip R l k := fun l h k => by
    rw [wip_comm, wip_add_left, wip_comm h l, wip_comm k l]
  set c := corrector src tgt R u with hc
  have e : h = c + (h - c) := by abel
  have this : wip R h h = wip R (c + (h - c)) (c + (h - c)) := by rw [← e]
  rw [this, wip_add_left, hadd_right, hadd_right, hcross, wip_comm c (h - c), hcross]
  ring

/-- **(AO.11)**: `‖h_*‖² = ⟨d, u⟩`. -/
theorem energy_eq (hR : ∀ e, 0 < R e) {u d : X → ℝ} (hL : laplacian src tgt R u = d) :
    wip R (corrector src tgt R u) (corrector src tgt R u) = ∑ y, d y * u y := by
  rw [wip_corrector src tgt hR]
  have := corrector_feasible src tgt hR hL
  simp only [this.1, mul_zero, sum_const_zero, sub_zero, this.2]
  refine sum_congr rfl fun y _ => ?_
  ring

/-- **(AO.11)**: `h_*` minimizes the energy among feasible currents. -/
theorem energy_le (hR : ∀ e, 0 < R e) {u d : X → ℝ} (hL : laplacian src tgt R u = d)
    {h : E → ℝ} (hf : Feasible src tgt d h) :
    wip R (corrector src tgt R u) (corrector src tgt R u) ≤ wip R h h := by
  rw [pythagoras src tgt hR hL hf]
  linarith [wip_self_nonneg hR (h - corrector src tgt R u)]

/-- **(AO.12)**: the minimum-norm correction is unique. -/
theorem eq_corrector_of_min (hR : ∀ e, 0 < R e) {u d : X → ℝ}
    (hL : laplacian src tgt R u = d) {h : E → ℝ} (hf : Feasible src tgt d h)
    (hmin : wip R h h ≤ wip R (corrector src tgt R u) (corrector src tgt R u)) :
    h = corrector src tgt R u := by
  have hp := pythagoras src tgt hR hL hf
  have h0 : wip R (h - corrector src tgt R u) (h - corrector src tgt R u) = 0 := by
    linarith [wip_self_nonneg hR (h - corrector src tgt R u)]
  have := wip_self_eq_zero hR _ h0
  exact sub_eq_zero.mp this

/-! ### Solvability: `d ∈ Ran 𝓛` -/

theorem Qu_add (u v : X → ℝ) (x : X) :
    Qu src tgt R (u + v) x = Qu src tgt R u x + Qu src tgt R v x := by
  unfold Qu
  rw [← add_div, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun e _ => ?_
  split_ifs <;> simp [mul_add]

theorem Qu_smul (c : ℝ) (u : X → ℝ) (x : X) :
    Qu src tgt R (c • u) x = c * Qu src tgt R u x := by
  unfold Qu
  rw [mul_div_assoc', mul_sum]
  congr 1
  refine sum_congr rfl fun e _ => ?_
  split_ifs <;> simp; ring

theorem laplacian_add (u v : X → ℝ) :
    laplacian src tgt R (u + v) = laplacian src tgt R u + laplacian src tgt R v := by
  funext y
  rw [laplacian_eq, laplacian_eq, laplacian_eq, Pi.add_apply, ← colSum_add]
  congr 1
  funext e
  simp only [corrector, Pi.add_apply, Qu_add]
  ring

theorem laplacian_smul (c : ℝ) (u : X → ℝ) :
    laplacian src tgt R (c • u) = c • laplacian src tgt R u := by
  funext y
  rw [laplacian_eq, laplacian_eq, Pi.smul_apply, smul_eq_mul]
  unfold colSum
  rw [mul_sum]
  refine sum_congr rfl fun e _ => ?_
  simp only [corrector, Pi.smul_apply, smul_eq_mul, Qu_smul]
  split_ifs <;> ring

variable (R) in
/-- The Laplacian as a linear map. -/
def laplacianL : (X → ℝ) →ₗ[ℝ] (X → ℝ) where
  toFun := laplacian src tgt R
  map_add' := laplacian_add src tgt
  map_smul' := laplacian_smul src tgt

/-- A feasible current makes `d` orthogonal to `ker 𝓛`. -/
theorem sum_mul_eq_zero_of_feasible (hR : ∀ e, 0 < R e) {d : X → ℝ} {h : E → ℝ}
    (hf : Feasible src tgt d h) {w : X → ℝ} (hw : laplacian src tgt R w = 0) :
    ∑ y, w y * d y = 0 := by
  have hq : ∑ y, w y * laplacian src tgt R w y = 0 := by rw [hw]; simp
  rw [laplacian_quad src tgt hR] at hq
  -- every row variance term vanishes: `h_* (w) = 0`
  have hcorr : corrector src tgt R w = 0 := by
    have hsum := hq
    rw [sum_sum_ite_src src fun e x => R e * (w (tgt e) - Qu src tgt R w x) ^ 2] at hsum
    rw [sum_eq_zero_iff_of_nonneg (fun e _ => mul_nonneg (hR e).le (sq_nonneg _))] at hsum
    funext e
    have := hsum e (mem_univ e)
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 (hR e).ne'
    · unfold corrector
      rw [pow_eq_zero_iff (by norm_num) |>.mp h1, mul_zero]
      rfl
  calc ∑ y, w y * d y = ∑ y, w y * colSum tgt h y := by simp [hf.2]
    _ = wip R (colAdj tgt R w) h := (wip_colAdj tgt hR w h).symm
    _ = wip R (colAdj tgt R w) (sourceProj src R h) := by
        rw [sourceProj_of_rowSum_zero src h hf.1]
    _ = wip R (sourceProj src R (colAdj tgt R w)) h := (wip_sourceProj src hR _ _).symm
    _ = 0 := by rw [sourceProj_colAdj, hcorr]; simp [wip]

/-- **(AO.11)**: the constraints `A h = 0`, `B h = d` are solvable exactly when `d ∈ Ran 𝓛`. -/
theorem solvable_iff (hR : ∀ e, 0 < R e) (d : X → ℝ) :
    (∃ h : E → ℝ, Feasible src tgt d h) ↔ ∃ u : X → ℝ, laplacian src tgt R u = d := by
  constructor
  · rintro ⟨h, hf⟩
    -- orthogonal decomposition of `d` against the range of `𝓛`
    let K : Submodule ℝ (EuclideanSpace ℝ X) :=
      (LinearMap.range (laplacianL src tgt R)).map (WithLp.linearEquiv 2 ℝ (X → ℝ)).symm.toLinearMap
    obtain ⟨y, hy, z, hz, hdz⟩ := K.exists_add_mem_mem_orthogonal (WithLp.toLp 2 d)
    have hzL : ∀ u : X → ℝ, ∑ i, laplacian src tgt R u i * (WithLp.ofLp z) i = 0 := by
      intro u
      have hmem : WithLp.toLp 2 (laplacian src tgt R u) ∈ K :=
        Submodule.mem_map.mpr ⟨laplacian src tgt R u, LinearMap.mem_range_self _ u, rfl⟩
      have := Submodule.inner_right_of_mem_orthogonal hmem hz
      rw [EuclideanSpace.inner_eq_star_dotProduct] at this
      simpa [dotProduct, mul_comm] using this
    -- `z` is in the kernel
    have hzker : laplacian src tgt R (WithLp.ofLp z) = 0 := by
      have hq : ∑ i, (WithLp.ofLp z) i * laplacian src tgt R (WithLp.ofLp z) i = 0 := by
        have := hzL (WithLp.ofLp z)
        rw [← this]
        refine sum_congr rfl fun i _ => ?_
        ring
      rw [laplacian_quad src tgt hR,
        sum_sum_ite_src src fun e x =>
          R e * ((WithLp.ofLp z) (tgt e) - Qu src tgt R (WithLp.ofLp z) x) ^ 2,
        sum_eq_zero_iff_of_nonneg (fun e _ => mul_nonneg (hR e).le (sq_nonneg _))] at hq
      rw [laplacian_eq]
      funext i
      unfold colSum
      refine sum_eq_zero fun e _ => ?_
      have := hq e (mem_univ e)
      rcases mul_eq_zero.mp this with h1 | h1
      · exact absurd h1 (hR e).ne'
      · unfold corrector
        rw [pow_eq_zero_iff (by norm_num) |>.mp h1, mul_zero]
        simp
    -- hence `⟨z, d⟩ = 0`, but `⟨z, d⟩ = ‖z‖²`
    have h1 := sum_mul_eq_zero_of_feasible src tgt hR hf hzker
    have hzy : ⟪y, z⟫_ℝ = 0 := Submodule.inner_right_of_mem_orthogonal hy hz
    have hzz : ⟪z, z⟫_ℝ = 0 := by
      have h2 : ⟪z, WithLp.toLp 2 d⟫_ℝ = 0 := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        simpa [dotProduct, mul_comm] using h1
      rw [hdz, inner_add_right, real_inner_comm y z, hzy, zero_add] at h2
      exact h2
    have hz0 : z = 0 := inner_self_eq_zero.mp hzz
    rw [hz0, add_zero] at hdz
    rw [← hdz] at hy
    obtain ⟨u, hu, hud⟩ := Submodule.mem_map.mp hy
    obtain ⟨u', rfl⟩ := LinearMap.mem_range.mp hu
    refine ⟨u', ?_⟩
    have := congrArg (WithLp.ofLp) hud
    simpa [laplacianL] using this
  · rintro ⟨u, hu⟩
    exact ⟨_, corrector_feasible src tgt hR hu⟩

/-! ### The kernel: functions constant on row supports -/

theorem corrector_eq_zero_iff (hR : ∀ e, 0 < R e) (u : X → ℝ) :
    corrector src tgt R u = 0 ↔ ∀ e, u (tgt e) = Qu src tgt R u (src e) := by
  constructor
  · intro h e
    have := congrFun h e
    simp only [corrector, Pi.zero_apply, mul_eq_zero] at this
    rcases this with h1 | h1
    · exact absurd h1 (hR e).ne'
    · exact sub_eq_zero.mp h1
  · intro h
    funext e
    simp [corrector, h e]

theorem laplacian_eq_zero_iff (hR : ∀ e, 0 < R e) (u : X → ℝ) :
    laplacian src tgt R u = 0 ↔ corrector src tgt R u = 0 := by
  constructor
  · intro h0
    have hq : ∑ y, u y * laplacian src tgt R u y = 0 := by rw [h0]; simp
    rw [laplacian_quad src tgt hR,
      sum_sum_ite_src src fun e x => R e * (u (tgt e) - Qu src tgt R u x) ^ 2,
      sum_eq_zero_iff_of_nonneg (fun e _ => mul_nonneg (hR e).le (sq_nonneg _))] at hq
    funext e
    have := hq e (mem_univ e)
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 (hR e).ne'
    · simp [corrector, (pow_eq_zero_iff two_ne_zero).mp h1]
  · intro h0
    rw [laplacian_eq, h0]
    funext y
    simp [colSum]

/-- **Kernel**: `𝓛 u = 0` exactly when `u` is constant on every row support (hence on the
connected components of the target-overlap graph generated by common row supports). -/
theorem ker_iff_const_on_rows (hR : ∀ e, 0 < R e) (u : X → ℝ) :
    laplacian src tgt R u = 0 ↔ ∀ e e', src e = src e' → u (tgt e) = u (tgt e') := by
  rw [laplacian_eq_zero_iff src tgt hR, corrector_eq_zero_iff src tgt hR]
  constructor
  · intro h e e' hee'
    rw [h e, h e', hee']
  · intro h e
    have hsum : (∑ e', if src e' = src e then R e' * u (tgt e') else 0)
        = u (tgt e) * nu src R (src e) := by
      unfold nu rowSum
      rw [mul_sum]
      refine sum_congr rfl fun e' _ => ?_
      split_ifs with h'
      · rw [h e' e h']; ring
      · simp
    unfold Qu
    rw [hsum, mul_div_cancel_right₀ _ (nu_pos_of_src src hR e).ne']

/-! ### AO.13: positivity, marginals and entropy bounds -/

/-- The scalar bounds `t²/3 ≤ (1 + t) log(1 + t) - t ≤ t²` for `|t| ≤ 1/2`. -/
theorem scalar_bounds {t : ℝ} (ht : |t| ≤ 1 / 2) :
    t ^ 2 / 3 ≤ (1 + t) * Real.log (1 + t) - t ∧ (1 + t) * Real.log (1 + t) - t ≤ t ^ 2 := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp ht
  have hpos : 0 < 1 + t := by linarith
  constructor
  · -- `g s = (1+s) log(1+s) - s - s²/3` is nonnegative on `[-1/2, 1/2]`
    set g : ℝ → ℝ := fun s => (1 + s) * Real.log (1 + s) - s - s ^ 2 / 3 with hg
    set g' : ℝ → ℝ := fun s => Real.log (1 + s) - 2 / 3 * s with hg'
    have hdg : ∀ s, -1 < s → HasDerivAt g (g' s) s := by
      intro s hs
      have h1 : (1 + s) ≠ 0 := by linarith
      have hl := ((hasDerivAt_id s).const_add 1).log h1
      have := (((hasDerivAt_id s).const_add 1).mul hl).sub (hasDerivAt_id s) |>.sub
        ((hasDerivAt_pow 2 s).div_const 3)
      refine this.congr_deriv ?_
      simp only [hg', id]
      field_simp
      ring
    have hdg' : ∀ s, -1 < s → HasDerivAt g' (1 / (1 + s) - 2 / 3) s := by
      intro s hs
      have h1 : (1 + s) ≠ 0 := by linarith
      have hl := ((hasDerivAt_id s).const_add 1).log h1
      have := hl.sub ((hasDerivAt_id s).const_mul (2 / 3))
      refine this.congr_deriv ?_
      simp only [id]
      ring
    have hg'mono : MonotoneOn g' (Set.Icc (-1 / 2) (1 / 2)) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
      · intro x hx
        exact (hdg' x (by linarith [hx.1])).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        exact (hdg' x (by linarith [hx.1])).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        rw [(hdg' x (by linarith [hx.1])).deriv]
        have h1 : 0 < 1 + x := by linarith [hx.1]
        have : 2 / 3 ≤ 1 / (1 + x) := by
          rw [le_div_iff₀ h1]; linarith [hx.2]
        linarith
    have hg'0 : g' 0 = 0 := by simp [hg']
    have hg0 : g 0 = 0 := by simp [hg]
    have hge : 0 ≤ g t := by
      rcases le_or_gt 0 t with h0 | h0
      · -- monotone on `[0, 1/2]`
        have hmono : MonotoneOn g (Set.Icc 0 (1 / 2)) := by
          refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
          · intro x hx
            exact (hdg x (by linarith [hx.1])).continuousAt.continuousWithinAt
          · intro x hx
            rw [interior_Icc] at hx
            exact (hdg x (by linarith [hx.1])).differentiableAt.differentiableWithinAt
          · intro x hx
            rw [interior_Icc] at hx
            rw [(hdg x (by linarith [hx.1])).deriv, ← hg'0]
            exact hg'mono ⟨by norm_num, by norm_num⟩ ⟨by linarith [hx.1], hx.2.le⟩ hx.1.le
        have := hmono ⟨le_rfl, by norm_num⟩ ⟨h0, hhi⟩ h0
        rwa [hg0] at this
      · -- antitone on `[-1/2, 0]`
        have hanti : AntitoneOn g (Set.Icc (-1 / 2) 0) := by
          refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?_ ?_ ?_
          · intro x hx
            exact (hdg x (by linarith [hx.1])).continuousAt.continuousWithinAt
          · intro x hx
            rw [interior_Icc] at hx
            exact (hdg x (by linarith [hx.1])).differentiableAt.differentiableWithinAt
          · intro x hx
            rw [interior_Icc] at hx
            rw [(hdg x (by linarith [hx.1])).deriv, ← hg'0]
            exact hg'mono ⟨hx.1.le, by linarith [hx.2]⟩ ⟨by norm_num, by norm_num⟩ hx.2.le
        have := hanti ⟨by linarith, h0.le⟩ ⟨by norm_num, le_rfl⟩ h0.le
        rwa [hg0] at this
    simp only [hg] at hge
    linarith
  · have hlog := Real.log_le_sub_one_of_pos hpos
    have : (1 + t) * Real.log (1 + t) ≤ (1 + t) * t := by
      have := mul_le_mul_of_nonneg_left hlog hpos.le
      simpa using this
    nlinarith

variable (R) in
/-- The linearized occupation `π^lin = R + h_*`. -/
def occupation (u : X → ℝ) : E → ℝ := fun e => R e + corrector src tgt R u e

variable (R) in
/-- The leverage bound `ϑ_occ = max |u(y) - (Qu)(x)| ≤ 1/2`. -/
def Leverage (u : X → ℝ) : Prop := ∀ e, |u (tgt e) - Qu src tgt R u (src e)| ≤ 1 / 2

theorem occupation_eq (u : X → ℝ) (e : E) :
    occupation src tgt R u e = R e * (1 + (u (tgt e) - Qu src tgt R u (src e))) := by
  unfold occupation corrector; ring

/-- **(AO.13)**: under the leverage bound, `π^lin` is positive. -/
theorem occupation_pos (hR : ∀ e, 0 < R e) {u : X → ℝ} (hlev : Leverage src tgt R u) (e : E) :
    0 < occupation src tgt R u e := by
  rw [occupation_eq]
  have := (abs_le.mp (hlev e)).1
  have h1 : 0 < 1 + (u (tgt e) - Qu src tgt R u (src e)) := by linarith
  exact mul_pos (hR e) h1

/-- **(AO.13)**: `π^lin` has source marginal `ν`. -/
theorem occupation_rowSum (hR : ∀ e, 0 < R e) (u : X → ℝ) (x : X) :
    rowSum src (occupation src tgt R u) x = nu src R x := by
  have : occupation src tgt R u = R + corrector src tgt R u := rfl
  rw [this, rowSum_add, rowSum_corrector src tgt hR, add_zero]
  rfl

/-- **(AO.13)**: with `d = ν - ρ`, `π^lin` has target marginal `ν`. -/
theorem occupation_colSum {u : X → ℝ}
    (hL : laplacian src tgt R u = fun y => nu src R y - rho tgt R y) (y : X) :
    colSum tgt (occupation src tgt R u) y = nu src R y := by
  have hc : colSum tgt (corrector src tgt R u) y = nu src R y - rho tgt R y := by
    rw [← laplacian_eq, hL]
  have : occupation src tgt R u = R + corrector src tgt R u := rfl
  rw [this, colSum_add, hc]
  unfold rho
  ring

variable (R) in
/-- The relative entropy `D_KL(π ‖ R) = ∑ π log(π / R)`. -/
def klDiv (π : E → ℝ) : ℝ := ∑ e, π e * Real.log (π e / R e)

variable (R) in
/-- The occupation energy `𝓔_occ = ‖h_*‖²_{R⁻¹}`. -/
def energy (u : X → ℝ) : ℝ := wip R (corrector src tgt R u) (corrector src tgt R u)

theorem energy_eq_sum (hR : ∀ e, 0 < R e) (u : X → ℝ) :
    energy src tgt R u = ∑ e, R e * (u (tgt e) - Qu src tgt R u (src e)) ^ 2 := by
  unfold energy wip corrector
  refine sum_congr rfl fun e _ => ?_
  field_simp [(hR e).ne']

theorem sum_corrector_eq_zero {u : X → ℝ}
    (hL : laplacian src tgt R u = fun y => nu src R y - rho tgt R y) :
    ∑ e, corrector src tgt R u e = 0 := by
  rw [← sum_colSum tgt, ← laplacian_eq, hL, sum_sub_distrib]
  unfold nu rho
  rw [sum_rowSum, sum_colSum, sub_self]

/-- **(AO.13)**: `𝓔_occ / 3 ≤ D_KL(π^lin ‖ R) ≤ 𝓔_occ`. -/
theorem kl_bounds (hR : ∀ e, 0 < R e) {u : X → ℝ} (hlev : Leverage src tgt R u)
    (hL : laplacian src tgt R u = fun y => nu src R y - rho tgt R y) :
    energy src tgt R u / 3 ≤ klDiv R (occupation src tgt R u) ∧
      klDiv R (occupation src tgt R u) ≤ energy src tgt R u := by
  have hterm : ∀ e, occupation src tgt R u e * Real.log (occupation src tgt R u e / R e)
      = R e * ((1 + (u (tgt e) - Qu src tgt R u (src e)))
          * Real.log (1 + (u (tgt e) - Qu src tgt R u (src e)))
          - (u (tgt e) - Qu src tgt R u (src e))) + corrector src tgt R u e := by
    intro e
    have hR' := (hR e).ne'
    rw [occupation_eq]
    have : R e * (1 + (u (tgt e) - Qu src tgt R u (src e))) / R e
        = 1 + (u (tgt e) - Qu src tgt R u (src e)) := by
      rw [mul_div_cancel_left₀ _ hR']
    rw [this]
    unfold corrector
    ring
  have hkl : klDiv R (occupation src tgt R u)
      = ∑ e, R e * ((1 + (u (tgt e) - Qu src tgt R u (src e)))
          * Real.log (1 + (u (tgt e) - Qu src tgt R u (src e)))
          - (u (tgt e) - Qu src tgt R u (src e))) := by
    unfold klDiv
    simp_rw [hterm]
    rw [sum_add_distrib, sum_corrector_eq_zero src tgt hL, add_zero]
  rw [hkl, energy_eq_sum src tgt hR]
  constructor
  · rw [sum_div]
    refine sum_le_sum fun e _ => ?_
    have := (scalar_bounds (hlev e)).1
    calc R e * (u (tgt e) - Qu src tgt R u (src e)) ^ 2 / 3
        = R e * ((u (tgt e) - Qu src tgt R u (src e)) ^ 2 / 3) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this (hR e).le
  · refine sum_le_sum fun e _ => ?_
    exact mul_le_mul_of_nonneg_left (scalar_bounds (hlev e)).2 (hR e).le

variable (R) in
/-- Positive couplings with both marginals `ν`. -/
def IsCoupling (π : E → ℝ) : Prop :=
  (∀ e, 0 < π e) ∧ (∀ x, rowSum src π x = nu src R x) ∧ ∀ y, colSum tgt π y = nu src R y

variable (R) in
/-- The occupation defect `𝔇_occ = inf D_KL(π ‖ R)` over positive couplings. -/
def occupationDefect : ℝ := sInf (klDiv R '' {π | IsCoupling src tgt R π})

theorem klDiv_nonneg_of_coupling (hR : ∀ e, 0 < R e) {π : E → ℝ}
    (hπ : IsCoupling src tgt R π) : 0 ≤ klDiv R π := by
  have hsum : ∑ e, π e = ∑ e, R e := by
    rw [← sum_rowSum src π, ← sum_rowSum src R]
    exact sum_congr rfl fun x _ => hπ.2.1 x
  have hterm : ∀ e, π e - R e ≤ π e * Real.log (π e / R e) := by
    intro e
    have hπe := hπ.1 e
    have hRe := hR e
    have hlog := Real.log_le_sub_one_of_pos (div_pos hRe hπe)
    have hinv : Real.log (π e / R e) = -Real.log (R e / π e) := by
      rw [← Real.log_inv, inv_div]
    rw [hinv]
    have : π e * (R e / π e - 1) = R e - π e := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hlog hπe.le]
  unfold klDiv
  calc (0 : ℝ) = ∑ e, (π e - R e) := by rw [sum_sub_distrib, hsum, sub_self]
    _ ≤ _ := sum_le_sum fun e _ => hterm e

/-- **(AO.13)**: `𝔇_occ ≤ 𝓔_occ`. -/
theorem occupationDefect_le (hR : ∀ e, 0 < R e) {u : X → ℝ} (hlev : Leverage src tgt R u)
    (hL : laplacian src tgt R u = fun y => nu src R y - rho tgt R y) :
    occupationDefect src tgt R ≤ energy src tgt R u := by
  refine le_trans (csInf_le ?_ ?_) (kl_bounds src tgt hR hlev hL).2
  · refine ⟨0, ?_⟩
    rintro r ⟨π, hπ, rfl⟩
    exact klDiv_nonneg_of_coupling src tgt hR hπ
  · exact ⟨occupation src tgt R u,
      ⟨occupation_pos src tgt hR hlev, occupation_rowSum src tgt hR u,
        occupation_colSum src tgt hL⟩, rfl⟩

end

end AcceptedOccurrenceLaplacian
end NCG
