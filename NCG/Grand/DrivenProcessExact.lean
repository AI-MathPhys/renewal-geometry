/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Perron–Doob driven process and entropy-optimal control

Machinery for `thm:accepted-driven-process`.  On a finite state space `S` with a Markov
generator `L` (Metzler, zero row sums), a protected state reward `v` and jump reward `g`, the
tilted matrix is `B_k(u,w) = L(u,w) e^{k g(u,w)}` (`u ≠ w`), `B_k(u,u) = L(u,u) + k v(u)`.  Given
a positive Perron pair `B_k r = ψ r`, `ℓ B_k = ψ ℓ`, `ℓ ⬝ r = 1` and `D = diag r`:

* `L_k^dr = D⁻¹ B_k D - ψ I` is a Markov generator with the same off-diagonal support as `L`
  (`driven_isGenerator`, `driven_pos_iff`);
* its stationary law is `π = ℓ ⊙ r` (`vecMul_driven`, `sum_stationary`);
* the tilt of the driven generator by `q` is `D⁻¹ B_{k+q} D - ψ(k) I`, so a Perron pair of
  `B_{k+q}` transports to a positive eigenpair of the driven tilt with eigenvalue
  `ψ(k+q) - ψ(k)` (`tilt_driven`, `driven_tilt_eigen`);
* for every stationary controlled generator `K` with invariant law `ν`, absolutely continuous
  with respect to `L`, `ℋ(ν,K‖L) - k j(ν,K) + ψ = ℋ(ν,K‖L_k^dr) ≥ 0` (`control_identity`,
  `entropyRate_nonneg`).
-/

open Matrix Finset
open scoped BigOperators

namespace NCG
namespace DrivenProcess

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- A finite Markov generator: Metzler with zero row sums. -/
structure IsGenerator (L : Matrix S S ℝ) : Prop where
  offDiag_nonneg : ∀ u w, u ≠ w → 0 ≤ L u w
  row_sum : ∀ u, ∑ w, L u w = 0

/-- The tilted matrix `B_k`. -/
noncomputable def tilt (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ) (k : ℝ) :
    Matrix S S ℝ :=
  fun u w => if u = w then L u u + k * v u else L u w * Real.exp (k * g u w)

omit [Fintype S] in
theorem tilt_apply_ne (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ) (k : ℝ) {u w : S}
    (h : u ≠ w) : tilt L v g k u w = L u w * Real.exp (k * g u w) := by
  simp [tilt, h]

omit [Fintype S] in
theorem tilt_apply_self (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ) (k : ℝ) (u : S) :
    tilt L v g k u u = L u u + k * v u := by
  simp [tilt]

/-- The Doob-transformed driven generator `L_k^dr = D⁻¹ B D - ψ I` with `D = diag r`. -/
noncomputable def driven (B : Matrix S S ℝ) (r : S → ℝ) (ψ : ℝ) : Matrix S S ℝ :=
  diagonal (fun u => (r u)⁻¹) * B * diagonal r - ψ • (1 : Matrix S S ℝ)

theorem driven_apply (B : Matrix S S ℝ) (r : S → ℝ) (ψ : ℝ) (u w : S) :
    driven B r ψ u w = (r u)⁻¹ * B u w * r w - (if u = w then ψ else 0) := by
  simp [driven, diagonal_mul, mul_diagonal, Matrix.one_apply]

theorem driven_apply_ne (B : Matrix S S ℝ) (r : S → ℝ) (ψ : ℝ) {u w : S} (h : u ≠ w) :
    driven B r ψ u w = (r u)⁻¹ * B u w * r w := by
  rw [driven_apply, if_neg h, sub_zero]

theorem driven_apply_self (B : Matrix S S ℝ) (r : S → ℝ) (ψ : ℝ) (u : S) :
    driven B r ψ u u = (r u)⁻¹ * B u u * r u - ψ := by
  rw [driven_apply, if_pos rfl]

section Perron

variable (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ) (k : ℝ) (r ℓ : S → ℝ) (ψ : ℝ)

/-- The driven generator `L_k^dr` built from the Perron vector of `B_k`. -/
noncomputable def drivenGen : Matrix S S ℝ := driven (tilt L v g k) r ψ

/-- **Markov generator**: for a positive right Perron vector `B_k r = ψ r`, the driven matrix is
Metzler with zero row sums. -/
theorem driven_isGenerator (hL : IsGenerator L) (hr : ∀ u, 0 < r u)
    (hright : (tilt L v g k) *ᵥ r = ψ • r) : IsGenerator (drivenGen L v g k r ψ) where
  offDiag_nonneg := by
    intro u w huw
    rw [drivenGen, driven_apply_ne _ _ _ huw, tilt_apply_ne _ _ _ _ huw]
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (hr u).le)
      (mul_nonneg (hL.offDiag_nonneg u w huw) (Real.exp_pos _).le)) (hr w).le
  row_sum := by
    intro u
    have h := congrFun hright u
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    simp only [drivenGen, driven_apply, Finset.sum_sub_distrib, Finset.sum_ite_eq, mem_univ,
      if_true]
    have : ∑ w, (r u)⁻¹ * tilt L v g k u w * r w = (r u)⁻¹ * ∑ w, tilt L v g k u w * r w := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => by ring
    rw [this, h]
    field_simp [(hr u).ne']
    ring

/-- The driven generator has the same off-diagonal support as `L` (hence the same
irreducibility). -/
theorem driven_pos_iff (hL : IsGenerator L) (hr : ∀ u, 0 < r u) {u w : S} (huw : u ≠ w) :
    0 < drivenGen L v g k r ψ u w ↔ 0 < L u w := by
  rw [drivenGen, driven_apply_ne _ _ _ huw, tilt_apply_ne _ _ _ _ huw]
  constructor
  · intro h
    rcases (hL.offDiag_nonneg u w huw).lt_or_eq with h' | h'
    · exact h'
    · rw [← h'] at h
      simp at h
  · intro h
    exact mul_pos (mul_pos (inv_pos.mpr (hr u)) (mul_pos h (Real.exp_pos _))) (hr w)

/-- The stationary law `π = ℓ ⊙ r`. -/
noncomputable def stationary : S → ℝ := fun u => ℓ u * r u

/-- **Stationarity**: `π L_k^dr = 0` for the left Perron vector `ℓ B_k = ψ ℓ`. -/
theorem vecMul_driven (hr : ∀ u, 0 < r u) (hleft : ℓ ᵥ* (tilt L v g k) = ψ • ℓ) :
    (stationary r ℓ) ᵥ* drivenGen L v g k r ψ = 0 := by
  funext w
  have h := congrFun hleft w
  simp only [vecMul, dotProduct, Pi.smul_apply, smul_eq_mul] at h
  simp only [vecMul, dotProduct, drivenGen, driven_apply, stationary, Pi.zero_apply,
    mul_sub, Finset.sum_sub_distrib]
  have h1 : ∑ u, ℓ u * r u * ((r u)⁻¹ * tilt L v g k u w * r w)
      = (∑ u, ℓ u * tilt L v g k u w) * r w := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    field_simp [(hr u).ne']
  have h2 : ∑ u, ℓ u * r u * (if u = w then ψ else 0) = ℓ w * r w * ψ := by
    simp [Finset.sum_ite_eq']
  rw [h1, h2, h]
  ring

omit [Fintype S] [DecidableEq S] in
theorem stationary_nonneg (hr : ∀ u, 0 < r u) (hℓ : ∀ u, 0 < ℓ u) (u : S) :
    0 < stationary r ℓ u := mul_pos (hℓ u) (hr u)

omit [DecidableEq S] in
theorem sum_stationary (hnorm : ∑ u, ℓ u * r u = 1) : ∑ u, stationary r ℓ u = 1 := hnorm

/-! ### The driven tilt -/

/-- **Tilt shift**: tilting the driven generator by `q` is `D⁻¹ B_{k+q} D - ψ(k) I`. -/
theorem tilt_driven (hr : ∀ u, 0 < r u) (q : ℝ) :
    tilt (drivenGen L v g k r ψ) v g q = driven (tilt L v g (k + q)) r ψ := by
  ext u w
  by_cases huw : u = w
  · subst huw
    rw [tilt_apply_self, drivenGen, driven_apply_self, driven_apply_self, tilt_apply_self,
      tilt_apply_self]
    field_simp [(hr u).ne']
    ring
  · rw [tilt_apply_ne _ _ _ _ huw, drivenGen, driven_apply_ne _ _ _ huw,
      driven_apply_ne _ _ _ huw, tilt_apply_ne _ _ _ _ huw, tilt_apply_ne _ _ _ _ huw,
      add_mul, Real.exp_add]
    ring

/-- **Driven SCGF**: a Perron pair `(r', ℓ', ψ')` of `B_{k+q}` transports to the positive
eigenpair `(D⁻¹ r', ℓ' D)` of the driven tilt with eigenvalue `ψ(k+q) - ψ(k)`. -/
theorem driven_tilt_eigen (hr : ∀ u, 0 < r u) (q : ℝ) (r' ℓ' : S → ℝ) (ψ' : ℝ)
    (hright' : (tilt L v g (k + q)) *ᵥ r' = ψ' • r')
    (hleft' : ℓ' ᵥ* (tilt L v g (k + q)) = ψ' • ℓ') :
    (tilt (drivenGen L v g k r ψ) v g q) *ᵥ (fun u => (r u)⁻¹ * r' u)
        = (ψ' - ψ) • (fun u => (r u)⁻¹ * r' u) ∧
      (fun u => ℓ' u * r u) ᵥ* (tilt (drivenGen L v g k r ψ) v g q)
        = (ψ' - ψ) • (fun u => ℓ' u * r u) := by
  rw [tilt_driven L v g k r ψ hr]
  constructor
  · funext u
    have h := congrFun hright' u
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h ⊢
    simp only [driven_apply, sub_mul, Finset.sum_sub_distrib]
    have h1 : ∑ w, (r u)⁻¹ * tilt L v g (k + q) u w * r w * ((r w)⁻¹ * r' w)
        = (r u)⁻¹ * ∑ w, tilt L v g (k + q) u w * r' w := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      field_simp [(hr w).ne']
    have h2 : ∑ w, (if u = w then ψ else 0) * ((r w)⁻¹ * r' w) = ψ * ((r u)⁻¹ * r' u) := by
      simp [Finset.sum_ite_eq]
    rw [h1, h2, h]
    ring
  · funext w
    have h := congrFun hleft' w
    simp only [vecMul, dotProduct, Pi.smul_apply, smul_eq_mul] at h ⊢
    simp only [driven_apply, mul_sub, Finset.sum_sub_distrib]
    have h1 : ∑ u, ℓ' u * r u * ((r u)⁻¹ * tilt L v g (k + q) u w * r w)
        = (∑ u, ℓ' u * tilt L v g (k + q) u w) * r w := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun u _ => ?_
      field_simp [(hr u).ne']
    have h2 : ∑ u, ℓ' u * r u * (if u = w then ψ else 0) = ℓ' w * r w * ψ := by
      simp [Finset.sum_ite_eq']
    rw [h1, h2, h]
    ring

end Perron

/-! ### Entropy-optimal control -/

/-- `Φ(a, b) = a log(a/b) - a + b`. -/
noncomputable def Phi (a b : ℝ) : ℝ := a * Real.log (a / b) - a + b

theorem Phi_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : b = 0 → a = 0) : 0 ≤ Phi a b := by
  rcases hb.lt_or_eq with hb' | hb'
  · rcases ha.lt_or_eq with ha' | ha'
    · have h := Real.log_le_sub_one_of_pos (div_pos hb' ha')
      rw [Real.log_div hb'.ne' ha'.ne'] at h
      unfold Phi
      rw [Real.log_div ha'.ne' hb'.ne']
      have : a * (Real.log a - Real.log b) ≥ a - b := by
        have h2 : Real.log a - Real.log b ≥ 1 - b / a := by linarith
        calc a * (Real.log a - Real.log b) ≥ a * (1 - b / a) :=
              mul_le_mul_of_nonneg_left h2 ha'.le
          _ = a - b := by field_simp
      linarith
    · rw [← ha']
      unfold Phi
      rw [zero_mul, sub_zero, zero_add]
      exact hb
  · rw [← hb', hab hb'.symm]
    simp [Phi]

/-- The relative entropy rate `ℋ(ν, K ‖ L) = ∑ᵤ ν(u) ∑_{w ≠ u} Φ(K(u,w), L(u,w))`. -/
noncomputable def entropyRate (ν : S → ℝ) (K L : Matrix S S ℝ) : ℝ :=
  ∑ u, ν u * ∑ w ∈ univ.erase u, Phi (K u w) (L u w)

/-- The stationary reward rate `j(ν, K) = ∑ᵤ ν(u) (v(u) + ∑_{w ≠ u} K(u,w) g(u,w))`. -/
noncomputable def rewardRate (ν : S → ℝ) (K : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ) : ℝ :=
  ∑ u, ν u * (v u + ∑ w ∈ univ.erase u, K u w * g u w)

theorem entropyRate_nonneg (ν : S → ℝ) (K L : Matrix S S ℝ) (hν : ∀ u, 0 ≤ ν u)
    (hK : ∀ u w, u ≠ w → 0 ≤ K u w) (hL : ∀ u w, u ≠ w → 0 ≤ L u w)
    (hKL : ∀ u w, u ≠ w → L u w = 0 → K u w = 0) : 0 ≤ entropyRate ν K L :=
  Finset.sum_nonneg fun u _ => mul_nonneg (hν u) (Finset.sum_nonneg fun w hw =>
    Phi_nonneg (hK u w (Finset.ne_of_mem_erase hw).symm) (hL u w (Finset.ne_of_mem_erase hw).symm)
      (hKL u w (Finset.ne_of_mem_erase hw).symm))

variable (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ) (k : ℝ) (r : S → ℝ) (ψ : ℝ)

/-- Termwise change of `Φ` under the Doob transform, for `u ≠ w`. -/
theorem Phi_driven (hL : IsGenerator L) (hr : ∀ u, 0 < r u) (K : Matrix S S ℝ)
    (hK : ∀ u w, u ≠ w → 0 ≤ K u w) (hKL : ∀ u w, u ≠ w → L u w = 0 → K u w = 0) {u w : S}
    (huw : u ≠ w) :
    Phi (K u w) (drivenGen L v g k r ψ u w)
      = Phi (K u w) (L u w) - K u w * (k * g u w + Real.log (r w) - Real.log (r u))
        + (drivenGen L v g k r ψ u w - L u w) := by
  rw [drivenGen, driven_apply_ne _ _ _ huw, tilt_apply_ne _ _ _ _ huw]
  rcases (hL.offDiag_nonneg u w huw).lt_or_eq with hLpos | hL0
  · rcases (hK u w huw).lt_or_eq with hKpos | hK0
    · unfold Phi
      have hd : 0 < (r u)⁻¹ * (L u w * Real.exp (k * g u w)) * r w :=
        mul_pos (mul_pos (inv_pos.mpr (hr u)) (mul_pos hLpos (Real.exp_pos _))) (hr w)
      rw [Real.log_div hKpos.ne' hd.ne', Real.log_div hKpos.ne' hLpos.ne', Real.log_mul
        (mul_pos (inv_pos.mpr (hr u)) (mul_pos hLpos (Real.exp_pos _))).ne' (hr w).ne',
        Real.log_mul (inv_pos.mpr (hr u)).ne' (mul_pos hLpos (Real.exp_pos _)).ne',
        Real.log_mul hLpos.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_inv]
      ring
    · rw [← hK0]
      simp [Phi]
  · have hK0 : K u w = 0 := hKL u w huw hL0.symm
    rw [← hL0, hK0]
    simp [Phi]

/-- **Entropy-optimal control**: for a stationary controlled generator `K` with invariant law
`ν`, `ℋ(ν,K‖L) - k j(ν,K) + ψ = ℋ(ν,K‖L_k^dr)`. -/
theorem control_identity (hL : IsGenerator L) (hr : ∀ u, 0 < r u)
    (hright : (tilt L v g k) *ᵥ r = ψ • r) (K : Matrix S S ℝ) (hKgen : IsGenerator K)
    (hKL : ∀ u w, u ≠ w → L u w = 0 → K u w = 0) (ν : S → ℝ) (hν1 : ∑ u, ν u = 1)
    (hstat : ν ᵥ* K = 0) :
    entropyRate ν K L - k * rewardRate ν K v g + ψ
      = entropyRate ν K (drivenGen L v g k r ψ) := by
  have hdr := driven_isGenerator L v g k r ψ hL hr hright
  -- termwise expansion
  have hterm : ∀ u, ∑ w ∈ univ.erase u, Phi (K u w) (drivenGen L v g k r ψ u w)
      = ∑ w ∈ univ.erase u, Phi (K u w) (L u w)
        - k * ∑ w ∈ univ.erase u, K u w * g u w
        - ∑ w ∈ univ.erase u, K u w * (Real.log (r w) - Real.log (r u))
        + (∑ w ∈ univ.erase u, drivenGen L v g k r ψ u w - ∑ w ∈ univ.erase u, L u w) := by
    intro u
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [Phi_driven L v g k r ψ hL hr K hKgen.offDiag_nonneg hKL (Finset.ne_of_mem_erase hw).symm]
    ring
  -- off-diagonal row sums of generators
  have hrow : ∀ (M : Matrix S S ℝ), IsGenerator M → ∀ u, ∑ w ∈ univ.erase u, M u w = -M u u := by
    intro M hM u
    have := hM.row_sum u
    rw [← Finset.add_sum_erase _ _ (mem_univ u)] at this
    linarith
  have hdiag : ∀ u, drivenGen L v g k r ψ u u - L u u = k * v u - ψ := by
    intro u
    rw [drivenGen, driven_apply_self, tilt_apply_self]
    field_simp [(hr u).ne']
    ring
  -- the log term vanishes by stationarity and zero row sums
  have hlog : ∑ u, ν u * ∑ w ∈ univ.erase u, K u w * (Real.log (r w) - Real.log (r u)) = 0 := by
    have e : ∀ u, ∑ w ∈ univ.erase u, K u w * (Real.log (r w) - Real.log (r u))
        = ∑ w, K u w * (Real.log (r w) - Real.log (r u)) := by
      intro u
      rw [← Finset.add_sum_erase _ _ (mem_univ u), sub_self, mul_zero, zero_add]
    simp only [e]
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    have h1 : ∑ u, ∑ w, ν u * (K u w * Real.log (r w)) = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun w _ => ?_
      have := congrFun hstat w
      simp only [vecMul, dotProduct, Pi.zero_apply] at this
      calc ∑ u, ν u * (K u w * Real.log (r w)) = (∑ u, ν u * K u w) * Real.log (r w) := by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun u _ => by ring
        _ = 0 := by rw [this, zero_mul]
    have h2 : ∑ u, ∑ w, ν u * (K u w * Real.log (r u)) = 0 := by
      refine Finset.sum_eq_zero fun u _ => ?_
      calc ∑ w, ν u * (K u w * Real.log (r u)) = ν u * Real.log (r u) * ∑ w, K u w := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun w _ => by ring
        _ = 0 := by rw [hKgen.row_sum, mul_zero]
    rw [h1, h2, sub_zero]
  -- assemble
  simp only [entropyRate, rewardRate, hterm]
  have hu : ∀ u, ν u * (∑ w ∈ univ.erase u, Phi (K u w) (L u w)
      - k * ∑ w ∈ univ.erase u, K u w * g u w
      - ∑ w ∈ univ.erase u, K u w * (Real.log (r w) - Real.log (r u))
      + (∑ w ∈ univ.erase u, drivenGen L v g k r ψ u w - ∑ w ∈ univ.erase u, L u w))
      = ν u * ∑ w ∈ univ.erase u, Phi (K u w) (L u w)
        - k * (ν u * ∑ w ∈ univ.erase u, K u w * g u w)
        - ν u * ∑ w ∈ univ.erase u, K u w * (Real.log (r w) - Real.log (r u))
        + (ν u * ψ - k * (ν u * v u)) := by
    intro u
    rw [hrow _ hdr u, hrow _ hL u]
    have e : -drivenGen L v g k r ψ u u - -L u u = ψ - k * v u := by linarith [hdiag u]
    rw [e]
    ring
  rw [Finset.sum_congr rfl fun u _ => hu u]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hlog,
    ← Finset.sum_mul, hν1, one_mul]
  simp only [mul_add, Finset.sum_add_distrib]
  ring

/-- **`thm:accepted-driven-process`** (finite algebraic content): for a positive Perron pair of
`B_k`, the driven matrix `L_k^dr = D⁻¹ B_k D - ψ I` is a Markov generator with the support of
`L`, `π = ℓ ⊙ r` is stationary and normalized, the driven tilt is `D⁻¹ B_{k+q} D - ψ(k) I`
with transported Perron pairs of eigenvalue `ψ(k+q) - ψ(k)`, and the entropy-optimal control
identity holds with nonnegative right-hand side. -/
theorem accepted_driven_process (hL : IsGenerator L) (ℓ : S → ℝ) (hr : ∀ u, 0 < r u)
    (hℓ : ∀ u, 0 < ℓ u) (hright : (tilt L v g k) *ᵥ r = ψ • r)
    (hleft : ℓ ᵥ* (tilt L v g k) = ψ • ℓ) (hnorm : ∑ u, ℓ u * r u = 1) :
    IsGenerator (drivenGen L v g k r ψ) ∧
      (∀ u w, u ≠ w → (0 < drivenGen L v g k r ψ u w ↔ 0 < L u w)) ∧
      (stationary r ℓ) ᵥ* drivenGen L v g k r ψ = 0 ∧
      (∀ u, 0 < stationary r ℓ u) ∧ ∑ u, stationary r ℓ u = 1 ∧
      (∀ q, tilt (drivenGen L v g k r ψ) v g q = driven (tilt L v g (k + q)) r ψ) ∧
      (∀ q (r' ℓ' : S → ℝ) (ψ' : ℝ), (tilt L v g (k + q)) *ᵥ r' = ψ' • r' →
        ℓ' ᵥ* (tilt L v g (k + q)) = ψ' • ℓ' →
        (tilt (drivenGen L v g k r ψ) v g q) *ᵥ (fun u => (r u)⁻¹ * r' u)
            = (ψ' - ψ) • (fun u => (r u)⁻¹ * r' u) ∧
          (fun u => ℓ' u * r u) ᵥ* (tilt (drivenGen L v g k r ψ) v g q)
            = (ψ' - ψ) • (fun u => ℓ' u * r u)) ∧
      ∀ (K : Matrix S S ℝ), IsGenerator K → (∀ u w, u ≠ w → L u w = 0 → K u w = 0) →
        ∀ ν : S → ℝ, (∀ u, 0 ≤ ν u) → ∑ u, ν u = 1 → ν ᵥ* K = 0 →
          entropyRate ν K L - k * rewardRate ν K v g + ψ
              = entropyRate ν K (drivenGen L v g k r ψ) ∧
            0 ≤ entropyRate ν K (drivenGen L v g k r ψ) :=
  ⟨driven_isGenerator L v g k r ψ hL hr hright,
    fun _ _ huw => driven_pos_iff L v g k r ψ hL hr huw,
    vecMul_driven L v g k r ℓ ψ hr hleft, stationary_nonneg r ℓ hr hℓ, sum_stationary r ℓ hnorm,
    fun q => tilt_driven L v g k r ψ hr q,
    fun q r' ℓ' ψ' h1 h2 => driven_tilt_eigen L v g k r ψ hr q r' ℓ' ψ' h1 h2,
    fun K hK hKL ν hν hν1 hstat =>
      ⟨control_identity L v g k r ψ hL hr hright K hK hKL ν hν1 hstat,
        entropyRate_nonneg ν K _ hν hK.offDiag_nonneg
          (driven_isGenerator L v g k r ψ hL hr hright).offDiag_nonneg
          fun u w huw h0 => hKL u w huw (by
            by_contra hne
            have hpos : 0 < L u w := lt_of_le_of_ne (hL.offDiag_nonneg u w huw) (Ne.symm hne)
            have := (driven_pos_iff L v g k r ψ hL hr huw).mpr hpos
            rw [h0] at this
            exact lt_irrefl _ this)⟩⟩

end DrivenProcess
end NCG
